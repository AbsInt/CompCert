module B=Bitmap
module E = Errormsg

open Cil
open Pretty

let debug = false
    
(* Globalsread, Globalswritten should be closed under call graph *)

module StringOrder = 
  struct
    type t = string
    let compare s1 s2 = 
      if s1 = s2 then 0 else
      if s1 < s2 then -1 else 1
  end
  
module StringSet = Set.Make (StringOrder)

module IntOrder = 
  struct
    type t = int
    let compare i1 i2 = 
      if i1 = i2 then 0 else
      if i1 < i2 then -1 else 1
  end
  
module IntSet = Set.Make (IntOrder)


type cfgInfo = {
    name: string; (* The function name *)
    start   : int;          
    size    : int;    
    blocks: cfgBlock array; (** Dominating blocks must come first *)
    successors: int list array; (* block indices *)
    predecessors: int list array;   
    mutable nrRegs: int;
    mutable regToVarinfo: varinfo array; (** Map register IDs to varinfo *)
  } 

(** A block corresponds to a statement *)
and cfgBlock = { 
    bstmt: Cil.stmt; 

    (* We abstract the statement as a list of def/use instructions *)
    instrlist: instruction list;
    mutable livevars: (reg * int) list;  
    (** For each variable ID that is live at the start of the block, the 
     * block whose definition reaches this point. If that block is the same 
     * as the current one, then the variable is a phi variable *)
    mutable reachable: bool;
  }
  
and instruction = (reg list * reg list) 
  (* lhs variables, variables on rhs.  *)


and reg = int

type idomInfo = int array  (* immediate dominator *)

and dfInfo = (int list) array  (* dominance frontier *)

and oneSccInfo = {
    nodes: int list;
    headers: int list;
    backEdges: (int*int) list;
  } 

and sccInfo = oneSccInfo list 

(* Muchnick's Domin_Fast, 7.16 *)

let compute_idom (flowgraph: cfgInfo): idomInfo = 
  let start = flowgraph.start in
  let size  = flowgraph.size in
  let successors = flowgraph.successors in
  let predecessors = flowgraph.predecessors in 
  let n0 = size in (* a new node (not in the flowgraph) *)
  let idom = Array.make size (-1) in (* Make an array of immediate dominators  *)
  let nnodes  = size + 1 in
  let nodeSet = B.init nnodes (fun i -> true) in
  
  let ndfs     = Array.create nnodes 0 in (* mapping from depth-first 
                                         * number to nodes. DForder 
                                         * starts at 1, with 0 used as 
                                         * an invalid entry  *)
  let parent   = Array.create nnodes 0 in (* the parent in depth-first 
                                         * spanning tree  *) 

      (* A semidominator of w is the node v with the minimal DForder such 
       * that there is a path from v to w containing only nodes with the 
       * DForder larger than w.  *)
  let sdno     = Array.create nnodes 0 in (* depth-first number of 
                                         * semidominator  *)
  
                                        (* The set of nodes whose 
                                           * semidominator is ndfs(i) *)
  let bucket   = Array.init nnodes (fun _ -> B.cloneEmpty nodeSet) in
  
       (* The functions link and eval maintain a forest within the 
          * depth-first spanning tree. Ancestor is n0 is the node is a root in 
          * the forest. Label(v) is the node in the ancestor chain with the 
          * smallest depth-first number of its semidominator. Child and Size 
          * are used to keep the trees in the forest balanced  *)
  let ancestor = Array.create nnodes 0 in 
  let label    = Array.create nnodes 0 in
  let child    = Array.create nnodes 0 in
  let size     = Array.create nnodes 0 in
  
  
  let n = ref 0 in                  (* depth-first scan and numbering. 
                                       * Initialize data structures. *)
  ancestor.(n0) <- n0;
  label.(n0)    <- n0;
  let rec depthFirstSearchDom v =
    incr n;
  sdno.(v) <- !n;
    ndfs.(!n) <- v; label.(v) <- v;
    ancestor.(v) <- n0;             (* All nodes are roots initially *)
    child.(v) <- n0; size.(v) <- 1;
    List.iter 
      (fun w ->
	if sdno.(w) = 0 then begin 
          parent.(w) <- v; depthFirstSearchDom w 
	end)
      successors.(v);
  in
       (* Determine the ancestor of v whose semidominator has the the minimal 
          * DFnumber. In the process, compress the paths in the forest.  *)
  let eval v =
    let rec compress v =
      if ancestor.(ancestor.(v)) <> n0 then
	begin
	  compress ancestor.(v);
	  if sdno.(label.(ancestor.(v))) < sdno.(label.(v)) then
	    label.(v) <- label.(ancestor.(v));
	  ancestor.(v) <- ancestor.(ancestor.(v))
      end
    in
    if ancestor.(v) = n0 then label.(v)
    else begin
      compress v;
      if sdno.(label.(ancestor.(v))) >= sdno.(label.(v)) then
	label.(v)
      else label.(ancestor.(v))
    end
  in
  
  let link v w =
    let s = ref w in
    while sdno.(label.(w)) < sdno.(label.(child.(!s))) do
      if size.(!s) + size.(child.(child.(!s))) >= 2* size.(child.(!s)) then
	(ancestor.(child.(!s)) <- !s;
	 child.(!s) <- child.(child.(!s)))
      else
	(size.(child.(!s)) <- size.(!s);
	 ancestor.(!s) <- child.(!s); s := child.(!s));
    done;
    label.(!s) <- label.(w);
    size.(v) <- size.(v) + size.(w);
    if size.(v) < 2 * size.(w) then begin
      let tmp = !s in
      s :=  child.(v);
      child.(v) <- tmp;
    end;
    while !s <> n0 do
      ancestor.(!s) <- v;
      s := child.(!s);
    done;
  in
      (* Start now *)
  depthFirstSearchDom start;
  for i = !n downto 2 do
    let w = ndfs.(i) in
    List.iter (fun v ->
      let u = eval v in
      if sdno.(u) < sdno.(w) then sdno.(w) <- sdno.(u);)
      predecessors.(w);
    B.set bucket.(ndfs.(sdno.(w))) w true;
    link parent.(w) w;
    while not (B.empty bucket.(parent.(w))) do
      let v =
	match B.toList bucket.(parent.(w)) with
	  x :: _ -> x
	| [] -> ignore(print_string "Error in dominfast");0 in
      B.set bucket.(parent.(w)) v false;
      let u = eval v in
      idom.(v) <- if sdno.(u) < sdno.(v) then u else parent.(w);
    done;
  done;
  
  for i=2 to !n do
    let w = ndfs.(i) in
    if idom.(w) <> ndfs.(sdno.(w)) then begin 
      let newDom = idom.(idom.(w)) in
      idom.(w) <- newDom;
    end
  done;
  idom
    
    
    
    
    
let dominance_frontier (flowgraph: cfgInfo) : dfInfo = 
  let idom = compute_idom flowgraph in
  let size = flowgraph.size in
  let children = Array.create size [] in 
  for i = 0 to size - 1 do
    if (idom.(i) != -1) then children.(idom.(i)) <- i :: children.(idom.(i));
  done; 

  let size  = flowgraph.size in
  let start  = flowgraph.start in
  let successors = flowgraph.successors in
  
  let df = Array.create size [] in
                                        (* Compute the dominance frontier  *)
  
  let bottom = Array.make size true in  (* bottom of the dominator tree *)
  for i = 0 to size - 1 do 
    if (i != start) && idom.(i) <> -1 then bottom.(idom.(i)) <- false; 
  done;

  let processed = Array.make size false in (* to record the nodes added to work_list *) 
  let workList = ref ([]) in (* to iterate in a bottom-up traversal of the dominator tree *)
  for i = 0 to size - 1 do 
    if (bottom.(i)) then workList := i :: !workList; 
  done;
  while (!workList != []) do
    let x = List.hd !workList in
    let update y = if idom.(y) <> x then df.(x) <- y::df.(x) in
                                        (* compute local component *)
    
(* We use whichPred instead of whichSucc because ultimately this info is 
 * needed by control dependence dag which is constructed from REVERSE 
 * dominance frontier *)
    List.iter (fun succ -> update succ) successors.(x);
                                        (* add on up component *)
    List.iter (fun z -> List.iter (fun y  -> update y) df.(z)) children.(x);
    processed.(x) <- true;
    workList := List.tl !workList;
    if (x != start) then begin
      let i = idom.(x) in
      if i <> -1 && 
         (List.for_all (fun child -> processed.(child)) children.(i)) then workList := i :: !workList; 
    end;
  done;
  df
    
    
(* Computes for each register, the set of nodes that need a phi definition 
 * for the register *)
    
let add_phi_functions_info (flowgraph: cfgInfo) : unit = 
  let df = dominance_frontier flowgraph in
  let size  = flowgraph.size in
  let nrRegs = flowgraph.nrRegs in 
  

  let defs = Array.init size (fun i -> B.init nrRegs (fun j -> false)) in 
  for i = 0 to size-1 do 
    List.iter 
      (fun (lhs,rhs) ->
        List.iter (fun (r: reg) -> B.set defs.(i) r true) lhs;
      ) 
      flowgraph.blocks.(i).instrlist
  done;
  let iterCount = ref 0 in
  let hasAlready = Array.create size 0 in 
  let work = Array.create size 0 in 
  let w = ref ([]) in 
  let dfPlus = Array.init nrRegs (
    fun i -> 
      let defIn = B.make size in
      for j = 0 to size - 1 do 
	if B.get defs.(j) i then B.set defIn j true
      done;
      let res = ref [] in 
      incr iterCount;
      B.iter (fun x -> work.(x) <- !iterCount; w := x :: !w;) defIn;
      while (!w != []) do 
	let x = List.hd !w in
	w := List.tl !w;
	List.iter (fun y -> 
	  if (hasAlready.(y) < !iterCount) then begin
	    res := y :: !res;
	    hasAlready.(y) <- !iterCount;
	    if (work.(y) < !iterCount) then begin
	      work.(y) <- !iterCount;
	      w := y :: !w;
	    end;
	  end;
		  ) df.(x)
      done;
      (* res := List.filter (fun blkId -> B.get liveIn.(blkId) i) !res; *)
      !res
   ) in
  let result = Array.create size ([]) in
  for i = 0 to nrRegs - 1 do
    List.iter (fun node -> result.(node) <- i::result.(node);) dfPlus.(i) 
  done;
(* result contains for each node, the list of variables that need phi 
 * definition *)
  for i = 0 to size-1 do
    flowgraph.blocks.(i).livevars <- 
      List.map (fun r -> (r, i)) result.(i);
  done
    
  
    
(* add dominating definitions info *)
    
let add_dom_def_info (f: cfgInfo): unit = 
  let blocks = f.blocks in
  let start = f.start in
  let size = f.size in
  let nrRegs = f.nrRegs in

  let idom = compute_idom f in
  let children = Array.create size [] in 
  for i = 0 to size - 1 do
    if (idom.(i) != -1) then children.(idom.(i)) <- i :: children.(idom.(i));
  done; 
  
  if debug then begin
    ignore (E.log "Immediate dominators\n");
    for i = 0 to size - 1 do 
      ignore (E.log " block %d: idom=%d, children=%a\n"
                i idom.(i)
                (docList num) children.(i));
    done
  end;

  (* For each variable, maintain a stack of blocks that define it. When you 
   * process a block, the top of the stack is the closest dominator that 
   * defines the variable *)
  let s = Array.make nrRegs ([start]) in 
  
  (* Search top-down in the idom tree *)
  let rec search (x: int): unit = (* x is a graph node *)
    (* Push the current block for the phi variables *)
    List.iter 
      (fun ((r: reg), dr) -> 
        if x = dr then s.(r) <- x::s.(r)) 
      blocks.(x).livevars;

    (* Clear livevars *)
    blocks.(x).livevars <- [];
    
    (* Compute livevars *)
    for i = 0 to nrRegs-1 do
      match s.(i) with 
      | [] -> assert false
      | fst :: _ -> 
          blocks.(x).livevars <- (i, fst) :: blocks.(x).livevars
    done;


    (* Update s for the children *)
    List.iter 
      (fun (lhs,rhs) ->
	List.iter (fun (lreg: reg) -> s.(lreg) <- x::s.(lreg) ) lhs; 
      ) 
      blocks.(x).instrlist;
    
        
    (* Go and do the children *)
    List.iter search children.(x);
    
    (* Then we pop x, whenever it is on top of a stack *)
    Array.iteri 
      (fun i istack -> 
        let rec dropX = function
            [] -> []
          |  x' :: rest when x = x' -> dropX rest
          | l -> l
        in
        s.(i) <- dropX istack)
      s;
  in
  search(start)
  
   

let prune_cfg (f: cfgInfo): cfgInfo = 
 let size = f.size in 
 if size = 0 then f else
 let reachable = Array.make size false in
 let worklist = ref([f.start]) in
 while (!worklist != []) do 
   let h = List.hd !worklist in
   worklist := List.tl !worklist;
   reachable.(h) <- true;
   List.iter (fun s -> if (reachable.(s) = false) then worklist := s::!worklist; 
	     ) f.successors.(h);
 done;
(*
 let dummyblock = {  bstmt = mkEmptyStmt ();
                     instrlist = [];
                     livevars = [] } 
 in
*)
 let successors = Array.init size (fun i -> List.filter (fun s -> reachable.(s)) f.successors.(i)) in
 let predecessors = Array.init size (fun i -> List.filter (fun s -> reachable.(s)) f.predecessors.(i)) in
 Array.iteri (fun i b -> b.reachable <- reachable.(i)) f.blocks;
 let result: cfgInfo = 
        { name = f.name;
          start = f.start;
          size = f.size;
          successors = successors;
          predecessors = predecessors;
          blocks = f.blocks;
          nrRegs = f.nrRegs;
          regToVarinfo = f.regToVarinfo;
        }
 in
 result
 
 
let add_ssa_info (f: cfgInfo): unit = 
  let f = prune_cfg f in
  let d_reg () (r: int) = 
    dprintf "%s(%d)" f.regToVarinfo.(r).vname r
  in
  if debug then begin
    ignore (E.log "Doing SSA for %s. Initial data:\n" f.name);
    Array.iteri (fun i b -> 
      ignore (E.log " block %d:\n    succs=@[%a@]\n    preds=@[%a@]\n   instr=@[%a@]\n"
                i
                (docList num) f.successors.(i)
                (docList num) f.predecessors.(i)
                (docList ~sep:line (fun (lhs, rhs) -> 
                  dprintf "%a := @[%a@]"
                    (docList (d_reg ())) lhs (docList (d_reg ())) rhs))
                b.instrlist))
      f.blocks;
  end;

  add_phi_functions_info f;
  add_dom_def_info f;

  if debug then begin
    ignore (E.log "After SSA\n");
    Array.iter (fun b -> 
      ignore (E.log " block %d livevars: @[%a@]\n" 
                b.bstmt.sid 
                (docList (fun (i, fst) -> 
                  dprintf "%a def at %d" d_reg i fst))
                b.livevars))
      f.blocks;
  end


let set2list s = 
  let result = ref([]) in
  IntSet.iter (fun element -> result := element::!result) s;
  !result




let preorderDAG (nrNodes: int) (successors: (int list) array): int list = 
  let processed = Array.make nrNodes false in
  let revResult = ref ([]) in
  let predecessorsSet = Array.make nrNodes (IntSet.empty) in
  for i = 0 to nrNodes -1 do 
    List.iter (fun s -> predecessorsSet.(s) <- IntSet.add i predecessorsSet.(s)) successors.(i);
  done;
  let predecessors = Array.init nrNodes (fun i -> set2list predecessorsSet.(i)) in
  let workList = ref([]) in
  for i = 0 to nrNodes - 1 do
    if (predecessors.(i) = []) then workList := i::!workList;
  done;
  while (!workList != []) do
    let x = List.hd !workList in
    workList := List.tl !workList;
    revResult := x::!revResult;
    processed.(x) <- true;
    List.iter (fun s -> 
      if (List.for_all (fun p -> processed.(p)) predecessors.(s)) then
	workList := s::!workList;
	      ) successors.(x);
  done;
  List.rev !revResult


(* Muchnick Fig 7.12 *) 
(* takes an SCC description as an input and returns prepares the appropriate SCC *)
let preorder (nrNodes: int) (successors: (int list) array) (r: int): oneSccInfo = 
  if debug then begin
    ignore (E.log "Inside preorder \n");
    for i = 0 to nrNodes - 1 do 
      ignore (E.log "succ(%d) = %a" i (docList (fun i -> num i)) successors.(i)); 
    done;
  end;
  let i = ref(0) in
  let j = ref(0) in 
  let pre = Array.make nrNodes (-1) in
  let post = Array.make nrNodes (-1) in
  let visit = Array.make nrNodes (false) in
  let backEdges = ref ([]) in
  let headers = ref(IntSet.empty) in
  let rec depth_first_search_pp (x:int) =      
    visit.(x) <- true; 
    pre.(x) <- !j;
    incr j;
    List.iter (fun (y:int) -> 
      if (not visit.(y)) then
	(depth_first_search_pp y)
      else 
	if (post.(y) = -1) then begin
          backEdges := (x,y)::!backEdges;
	  headers := IntSet.add y !headers;
	end;
	      ) successors.(x);
    post.(x) <- !i;
    incr i;
  in
  depth_first_search_pp r;
  let nodes = Array.make nrNodes (-1) in
  for y = 0 to nrNodes - 1 do
    if (pre.(y) != -1) then nodes.(pre.(y)) <- y;
  done;
  let nodeList = List.filter (fun i -> (i != -1)) (Array.to_list nodes) in
  let result = { headers = set2list !headers; backEdges = !backEdges; nodes = nodeList; } in
  result
    

exception Finished


let strong_components (f: cfgInfo) (debug: bool) = 
  let size = f.size in
  let parent = Array.make size (-1) in
  let color = Array.make size (-1) in
  let finish = Array.make size (-1) in
  let root = Array.make size (-1) in

(* returns a list of SCC. Each SCC is a tuple of SCC root and SCC nodes *) 
  let dfs (successors: (int list) array) (order: int array) = 
    let time = ref(-1) in
    let rec dfs_visit u = 
      color.(u) <- 1;
      incr time; 
      (* d.(u) <- time; *)
      List.iter (fun v ->
	if color.(v) = 0 then (parent.(v) <- u; dfs_visit v) 
		) successors.(u);
      color.(u) <- 2;
      incr time;
      finish.(u) <- !time
    in
    for u = 0 to size - 1 do
      color.(u) <- 0; (* white = 0, gray = 1, black = 2 *)
      parent.(u) <- -1; (* nil = -1 *)
      root.(u) <- 0; (* Is u a root? *)
    done;
    time := 0;
    Array.iter (fun u -> 
      if (color.(u) = 0) then begin 
	root.(u) <- 1;
	dfs_visit u;
      end;
	       ) order;
  in

  let simpleOrder = Array.init size (fun i -> i) in
  dfs f.successors simpleOrder;
  Array.sort (fun i j -> if (finish.(i) > finish.(j)) then -1 else 1) simpleOrder;
  
  dfs f.predecessors simpleOrder;
(* SCCs have been computed. (The trees represented by non-null parent edges 
 * represent the SCCS. We call the black nodes as the roots). Now put the 
 * result in the ouput format *)
  let allScc = ref([]) in
  for u = 0 to size - 1 do 
    if root.(u) = 1 then begin
      let sccNodes = ref(IntSet.empty) in
      let workList = ref([u]) in
      while (!workList != []) do 
	let h=List.hd !workList in
	workList := List.tl !workList;
	sccNodes := IntSet.add h !sccNodes;
	List.iter (fun s -> if parent.(s)=h then workList := s::!workList;) f.predecessors.(h);
      done;
      allScc := (u,!sccNodes)::!allScc;
      if (debug) then begin
	ignore (E.log "Got an SCC with root %d and nodes %a" u (docList num) (set2list !sccNodes)); 
      end;
    end;
  done;
  !allScc
      
 
let stronglyConnectedComponents (f: cfgInfo) (debug: bool): sccInfo = 
  let size = f.size in
  if (debug) then begin
    ignore (E.log "size = %d\n" size);
    for i = 0 to size - 1 do 
      ignore (E.log "Successors(%d): %a\n" i (docList (fun n -> num n)) f.successors.(i));
    done;
  end;

  let allScc = strong_components f debug in
  let all_sccArray = Array.of_list allScc in

  if (debug) then begin 
    ignore (E.log "Computed SCCs\n");
    for i = 0 to (Array.length all_sccArray) - 1 do
      ignore(E.log "SCC #%d: " i);
      let (_,sccNodes) = all_sccArray.(i) in
      IntSet.iter (fun i -> ignore(E.log "%d, " i)) sccNodes;
      ignore(E.log "\n");
    done;
  end;
  

  (* Construct sccId: Node -> Scc Id *)
  let sccId = Array.make size (-1) in
  Array.iteri (fun i (r,sccNodes) -> 
    IntSet.iter (fun n -> sccId.(n) <- i) sccNodes; 
	      ) all_sccArray;
  
  if (debug) then begin 
    ignore (E.log "\nComputed SCC IDs: ");
    for i = 0 to size - 1 do 
      ignore (E.log "SCCID(%d) = %d " i sccId.(i));
    done;
  end;
  

  (* Construct sccCFG *)
  let nrScc = Array.length all_sccArray in
  let successors = Array.make nrScc [] in
  for x = 0 to nrScc - 1 do
    successors.(x) <- 
      let s = ref(IntSet.empty) in 
      IntSet.iter (fun y ->
	List.iter (fun z -> 
	  let sy = sccId.(y) in
	  let sz = sccId.(z) in
	  if (not(sy = sz)) then begin 
	    s := IntSet.add sz !s;
	  end
		  ) f.successors.(y) 
		  ) (snd all_sccArray.(x));
      set2list !s
  done;
 
  if (debug) then begin 
    ignore (E.log "\nComputed SCC CFG, which should be a DAG:");
    ignore (E.log "nrSccs = %d " nrScc);
    for i = 0 to nrScc - 1 do  
      ignore (E.log "successors(%d) = [%a] " i (docList (fun j -> num j)) successors.(i));
    done;
  end;
  

  (* Order SCCs. The graph is a DAG here *)
  let sccorder = preorderDAG nrScc successors in

  if (debug) then begin 
    ignore (E.log "\nComputed SCC Preorder: ");
    ignore (E.log "Nodes in Preorder = [%a]" (docList (fun i -> num i)) sccorder);
  end;
  
  (* Order nodes of each SCC. The graph is a SCC here.*)
  let scclist = List.map (fun i -> 
    let successors = Array.create size [] in
    for j = 0 to size - 1 do 
      successors.(j) <- List.filter (fun x -> IntSet.mem x (snd all_sccArray.(i))) f.successors.(j);
    done;
    preorder f.size successors (fst all_sccArray.(i))  
	   ) sccorder in
  if (debug) then begin 
    ignore (E.log "Computed Preorder for Nodes of each SCC\n");
    List.iter (fun scc -> 
      ignore (E.log "BackEdges = %a \n" 
                (docList (fun (src,dest) -> dprintf "(%d,%d)" src dest))
                scc.backEdges);) 
      scclist;
  end;
  scclist




    
    
    
	
    
