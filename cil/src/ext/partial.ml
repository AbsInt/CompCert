(* See copyright notice at the end of the file *)
(*****************************************************************************
 * Partial Evaluation & Constant Folding
 *
 * Soundness Assumptions:
 * (1) Whole program analysis. You may call functions that are not defined
 *     (e.g., library functions) but they may not call back. 
 * (2) An undefined function may not return the address of a function whose
 *     address is not already taken in the code I can see. 
 * (3) A function pointer call may only call a function that has its
 *     address visibly taken in the code I can see. 
 *
 * (More assumptions in the comments below)
 *****************************************************************************)
open Cil
open Pretty

(*****************************************************************************
 * A generic signature for Alias Analysis information. Used to compute the
 * call graph and do symbolic execution. 
 ****************************************************************************)
module type AliasInfo =
  sig
    val can_have_the_same_value : Cil.exp -> Cil.exp -> bool
    val resolve_function_pointer : Cil.exp -> (Cil.fundec list)
  end

(*****************************************************************************
 * A generic signature for Symbolic Execution execution algorithms. Such
 * algorithms are used below to perform constant folding and dead-code
 * elimination. You write a "basic-block" symex algorithm, we'll make it
 * a whole-program CFG-pruner. 
 ****************************************************************************)
module type Symex = 
  sig
    type t (* the type of a symex algorithm state object *)
    val empty : t                           (* all values unknown *)
    val equal : t -> t -> bool              (* are these the same? *)
    val assign : t -> Cil.lval -> Cil.exp  -> (Cil.exp * t) 
      (* incorporate an assignment, return the RHS *)
    val unassign : t -> Cil.lval -> t 
      (* lose all information about the given lvalue: assume an 
       * unknown external value has been assigned to it *)
    val assembly : t -> Cil.instr -> t      (* handle ASM *)
    val assume : t -> Cil.exp -> t          (* incorporate an assumption *) 
    val evaluate : t -> Cil.exp -> Cil.exp  (* symbolic evaluation *)
    val join : (t list) -> t                (* join a bunch of states *) 
    val call : t -> Cil.fundec -> (Cil.exp list) -> (Cil.exp list * t)
      (* we are calling the given function with the given actuals *)
    val return : t -> Cil.fundec -> t
      (* we are returning from the given function *)
    val call_to_unknown_function : t -> t 
      (* throw away information that may have been changed *) 
    val debug : t -> unit
  end

(*****************************************************************************
 * A generic signature for whole-progam call graphs. 
 ****************************************************************************)
module type CallGraph =
  sig 
    type t (* the type of a call graph *)
    val compute : Cil.file -> t (* file for which we compute the graph *)
    val can_call : t -> Cil.fundec -> (Cil.fundec list)
    val can_be_called_by : t -> Cil.fundec -> (Cil.fundec list)
    val fundec_of_varinfo : t -> Cil.varinfo -> Cil.fundec
  end

(*****************************************************************************
 * My cheap-o Alias Analysis. Assume all expressions can have the same 
 * value and any function with its address taken can be the target of
 * any function pointer. 
 *
 * Soundness Assumptions:
 * (1) Someone must call "find_all_functions_With_address_taken" before the
 *     results are valid. This is already done in the code below.
 ****************************************************************************)
let all_functions_with_address_taken = ref [] 
let find_all_functions_with_address_taken (f : Cil.file) =
  iterGlobals f (fun g -> match g with
    GFun(fd,_) -> if fd.svar.vaddrof then
      all_functions_with_address_taken := fd :: 
      !all_functions_with_address_taken
  | _ -> ())  

module EasyAlias =
  struct
    let can_have_the_same_value e1 e2 = true
    let resolve_function_pointer e1 = !all_functions_with_address_taken
  end

(*****************************************************************************
 * My particular method for computing the Call Graph. 
 ****************************************************************************)
module EasyCallGraph = functor (A : AliasInfo) -> 
  struct
    type callGraphNode = {
              fd        : Cil.fundec ;
      mutable calledBy  : Cil.fundec list ;
      mutable calls     : Cil.fundec list ;
    } 
    type t = (Cil.varinfo, callGraphNode) Hashtbl.t 

    let cgCreateNode cg fundec =
      let newnode = { fd = fundec ; calledBy = [] ; calls = [] } in
      Hashtbl.add cg fundec.svar newnode

    let cgFindNode cg svar = Hashtbl.find cg svar 

    let cgAddEdge cg caller callee = 
      try 
        let n1 = cgFindNode cg caller in
        let n2 = cgFindNode cg callee in
        n1.calls <- n2.fd :: n1.calls ;
        n1.calledBy <- n1.fd :: n1.calledBy 
      with _ -> () 

    class callGraphVisitor cg = object
      inherit nopCilVisitor 
      val the_fun = ref None  

      method vinst i = 
        let _ = match i with
          Call(_,Lval(Var(callee),NoOffset),_,_) -> begin
            (* known function call *)
            match !the_fun with
              None -> failwith "callGraphVisitor: call outside of any function"
            | Some(enclosing) -> cgAddEdge cg enclosing callee
          end
        | Call(_,e,_,_) -> begin 
            (* unknown function call *)
            match !the_fun with
              None -> failwith "callGraphVisitor: call outside of any function"
            | Some(enclosing) -> let lst = A.resolve_function_pointer e in 
                List.iter (fun possible_target_fd ->
                  cgAddEdge cg enclosing possible_target_fd.svar) lst
          end
        | _ -> () 
        in SkipChildren 

      method vfunc f = the_fun := Some(f.svar) ; DoChildren
    end 

    let compute (f : Cil.file) = 
      let cg = Hashtbl.create 511 in 
      iterGlobals f (fun g -> match g with
          GFun(fd,_) -> cgCreateNode cg fd 
        | _ -> ()
      ) ; 
      visitCilFileSameGlobals (new callGraphVisitor cg) f ;
      cg

    let can_call cg fd =
      let n = cgFindNode cg fd.svar in n.calls
    let can_be_called_by cg fd =
      let n = cgFindNode cg fd.svar in n.calledBy
    let fundec_of_varinfo cg vi = 
      let n = cgFindNode cg vi in n.fd 
  end (* END OF: module EasyCallGraph *)

(*****************************************************************************
 * Necula's Constant Folding Strategem (re-written to be applicative) 
 *
 * Soundness Assumptions:
 * (1) Inline assembly does not affect constant folding. 
 ****************************************************************************)
module OrderedInt = 
  struct 
    type t = int
    let compare = compare
  end
module IntMap = Map.Make(OrderedInt) 

module NeculaFolding = functor (A : AliasInfo) ->
  struct
    (* Register file. Maps identifiers of local variables to expressions.
     * We also remember if the expression depends on memory or depends on
     * variables that depend on memory *)
    type reg = {
      rvi : varinfo ;
      rval : exp ;
      rmem : bool
    } 
    type t = reg IntMap.t 
    let empty = IntMap.empty 
    let equal t1 t2 = (compare t1 t2 = 0) (* use OCAML here *)
    let dependsOnMem = ref false
    (* Rewrite an expression based on the current register file *)
    class rewriteExpClass (regFile : t) = object
      inherit nopCilVisitor
      method vexpr = function
        | Lval (Var v, NoOffset) -> begin
            try
              let defined = (IntMap.find v.vid regFile) in
              if (defined.rmem) then dependsOnMem := true;
              (match defined.rval with
              | Const(x) -> ChangeTo (defined.rval)
              | _ -> DoChildren)
            with Not_found -> DoChildren
          end
        | Lval (Mem _, _) -> dependsOnMem := true; DoChildren
        | _ -> DoChildren
    end
    (* Rewrite an expression and return the new expression along with an 
     * indication of whether it depends on memory *)
    let rewriteExp r (e: exp) : exp * bool = 
      dependsOnMem := false;
      let e' = constFold true (visitCilExpr (new rewriteExpClass r) e) in
      e', !dependsOnMem
    let eval r e = 
      let new_e, depends = rewriteExp r e in
      new_e

    let setMemory regFile = 
      (* Get a list of all mappings that depend on memory *)
      let depids = ref [] in
      IntMap.iter (fun id v -> if v.rmem then depids := id :: !depids) regFile;
      (* And remove them from the register file *)
      List.fold_left (fun acc id -> IntMap.remove id acc) regFile !depids

    let setRegister regFile (v: varinfo) ((e,b): exp * bool) = 
      IntMap.add v.vid { rvi = v ; rval = e ; rmem = b; } regFile 

    let resetRegister regFile (id: int) =
      IntMap.remove id regFile 

    class findLval lv contains = object
      inherit nopCilVisitor 
      method vlval l = 
        if l = lv then 
          (contains := true ; SkipChildren)
        else
          DoChildren
    end 

    let removeMappingsThatDependOn regFile l =
      (* Get a list of all mappings that depend on l *)
      let depids = ref [] in
      IntMap.iter (fun id reg -> 
        let found = ref false in 
        ignore (visitCilExpr (new findLval l found) reg.rval) ;
        if !found then 
          depids := id :: !depids
      )  regFile ; 
      (* And remove them from the register file *)
      List.fold_left (fun acc id -> IntMap.remove id acc) regFile !depids

    let assign r l e = 
      let (newe,b) = rewriteExp r e in
      let r' = match l with
        (Var v, NoOffset) -> 
            let r'' = setRegister r v (newe,b) in 
            removeMappingsThatDependOn r'' l 
      | (Mem _, _) -> setMemory r
      | _ -> r 
      in newe, r' 

    let unassign r l = 
      let r' = match l with
        (Var v, NoOffset) -> 
            let r'' = resetRegister r v.vid in
            removeMappingsThatDependOn r'' l 
      | (Mem _, _) -> setMemory r
      | _ -> r 
      in r' 

    let assembly r i = r (* no-op in Necula-world *)
    let assume r e = r (* no-op in Necula-world *)

    let evaluate r e = 
      let (newe,_) = rewriteExp r e in
      newe

    (* Join two symex states *)  
    let join2 (r1 : t) (r2 : t) = 
      let keep = ref [] in 
      IntMap.iter (fun id reg -> 
        try 
          let reg' = IntMap.find id r2 in
          if reg'.rval = reg.rval && reg'.rmem = reg.rmem then 
            keep := (id,reg) :: !keep 
        with _ -> ()
      ) r1 ;
      List.fold_left (fun acc (id,v) ->
        IntMap.add id v acc) (IntMap.empty) !keep

    let join (lst : t list) = match lst with
        [] -> failwith "empty list"
    | r :: tl -> List.fold_left 
                  (fun (acc : t) (elt : t) -> join2 acc elt) r tl 

    let call r fd el = 
      let new_arg_list = ref [] in 
      let final_r = List.fold_left2 (fun r vi e -> 
        let newe, r' = assign r ((Var(vi),NoOffset)) e in
        new_arg_list := newe :: !new_arg_list ;
        r'
      ) r fd.sformals el in
      (List.rev !new_arg_list), final_r

    let return r fd =
      let regFile = 
        List.fold_left (fun r vi -> IntMap.remove vi.vid r) r fd.sformals
      in 
      (* Get a list of all globals *)
      let depids = ref [] in
      IntMap.iter (fun vid reg -> 
        if reg.rvi.vglob || reg.rvi.vaddrof then depids := vid :: !depids 
      )  regFile ; 
      (* And remove them from the register file *)
      List.fold_left (fun acc id -> IntMap.remove id acc) regFile !depids


    let call_to_unknown_function r =
      setMemory r 

    let debug r = 
      IntMap.iter (fun key reg -> 
        ignore (Pretty.printf "%s <- %a (%b)@!" reg.rvi.vname d_exp reg.rval reg.rmem)
      ) r 
  end (* END OF: NeculaFolding *)

(*****************************************************************************
 * A transformation to make every function call end its statement. So
 * { x=1; Foo(); y=1; } 
 * becomes at least:
 * { { x=1; Foo(); }
 *   { y=1; } }
 * But probably more like:
 * { { x=1; } { Foo(); } { y=1; } }
 ****************************************************************************)
let rec contains_call il = match il with
    [] -> false
  | Call(_) :: tl -> true
  | _ :: tl -> contains_call tl 

class callBBVisitor = object
  inherit nopCilVisitor 

  method vstmt s =
    match s.skind with
      Instr(il) when contains_call il -> begin
        let list_of_stmts = List.map (fun one_inst -> 
          mkStmtOneInstr one_inst) il in
        let block = mkBlock list_of_stmts in
        ChangeDoChildrenPost(s, (fun _ -> 
          s.skind <- Block(block) ;
          s))
      end
    | _ -> DoChildren

  method vvdec _ = SkipChildren
  method vexpr _ = SkipChildren
  method vlval _ = SkipChildren
  method vtype _ = SkipChildren
end 

let calls_end_basic_blocks f =
  let thisVisitor = new callBBVisitor in
  visitCilFileSameGlobals thisVisitor f  

(*****************************************************************************
 * A transformation that gives each variable a unique identifier. 
 ****************************************************************************)
class vidVisitor = object
  inherit nopCilVisitor 
  val count = ref 0 

  method vvdec vi = 
    vi.vid <- !count ;
    incr count ; SkipChildren
end 

let globally_unique_vids f =
  let thisVisitor = new vidVisitor in
  visitCilFileSameGlobals thisVisitor f  

(*****************************************************************************
 * The Weimeric Partial Evaluation Data-Flow Engine
 *
 * This functor performs flow-sensitive, context-insensitive whole-program
 * data-flow analysis with an eye toward partial evaluation and constant
 * folding. 
 *
 * Toposort the whole-program inter-procedural CFG to compute
 *  (1) the number of actual predecessors for each statement
 *  (2) the global toposort ordering
 *
 * Perform standard data-flow analysis (joins, etc) on the ICFG until you
 * hit a fixed point. If this changed the structure of the ICFG (by
 * removing an IF-branch or an empty function call), redo the whole thing.
 *
 * Soundness Assumptions:
 * (1) A "call instruction" is the last thing in its statement.
 *       Use "calls_end_basic_blocks" to get this. cil/src/main.ml does
 *       this when you pass --makeCFG.
 * (2) All variables have globally unique identifiers. 
 *       Use "globally_unique_vids" to get this. cil/src/main.ml does 
 *       this when you pass --makeCFG. 
 * (3) This may not be a strict soundness requirement, but I wrote this
 *       assuming that the input file has all switch/break/continue
 *       statements removed. 
 ****************************************************************************)
module MakePartial =
  functor (S : Symex) -> 
  functor (C : CallGraph) -> 
  functor (A : AliasInfo) -> 
  struct

    let debug = false 

    (* We keep this information about every statement. Ideally this should
     * be put in the stmt itself, but CIL doesn't give us space. *)
    type sinfo = { (* statement info *)
              incoming_state : (int, S.t) Hashtbl.t ;
              (* mapping from stmt.sid to Symex.state *)
              reachable_preds : (int, bool) Hashtbl.t ; 
              (* basically a set of all of the stmt.sids that can really
               * reach this statement *)
      mutable last_used_state : S.t option ;
              (* When we last did the Post() of this statement, what
               * incoming state did we use? If our new incoming state is
               * the same, we don't have to do it again. *)
      mutable priority : int ; 
              (* Whole-program toposort priority. High means "do me first".
               * The first stmt in "main()" will have the highest priority.
               *)
    } 
    let sinfo_ht = Hashtbl.create 511 
    let clear_sinfo () = Hashtbl.clear sinfo_ht 

    (* We construct sinfo nodes lazily: if you ask for one that isn't
     * there, we build it. *)
    let get_sinfo stmt = 
      try
        Hashtbl.find sinfo_ht stmt.sid
      with _ ->
        let new_sinfo = { incoming_state = Hashtbl.create 3 ;
                          reachable_preds = Hashtbl.create 3 ; 
                          last_used_state = None ; 
                          priority = (-1) ; } in
        Hashtbl.add sinfo_ht stmt.sid new_sinfo ;
        new_sinfo 

    (* Topological Sort is a DFS in which you assign a priority right as 
     * you finished visiting the children. While we're there we compute
     * the actual number of unique predecessors for each statement. The CIL
     * information may be out of date because we keep changing the CFG by
     * removing IFs and whatnot. *)
    let toposort_counter = ref 1  
    let add_edge s1 s2 =
      let si2 = get_sinfo s2 in
      Hashtbl.replace si2.reachable_preds s1.sid true 

    let rec toposort c stmt = 
      let si = get_sinfo stmt in 
      if si.priority >= 0 then
        () (* already visited! *)
      else begin
        si.priority <- 0 ; (* currently visiting *)
        (* handle function calls in this basic block *) 
        (match stmt.skind with
          (Instr(il)) -> 
            List.iter (fun i -> 
              let fd_list = match i with
                Call(_,Lval(Var(vi),NoOffset),_,_) -> 
                  begin 
                    try 
                      let fd = C.fundec_of_varinfo c vi in
                      [fd] 
                    with e -> [] (* calling external function *)
                  end 
              | Call(_,e,_,_) -> 
                  A.resolve_function_pointer e 
              | _ -> []
              in 
              List.iter (fun fd -> 
                if List.length fd.sbody.bstmts > 0 then 
                  let fun_stmt = List.hd fd.sbody.bstmts in 
                  add_edge stmt fun_stmt ; 
                  toposort c fun_stmt 
              ) fd_list 
            ) il 
        | _ -> ()); 
        List.iter (fun succ -> 
          add_edge stmt succ ; toposort c succ) stmt.succs ;
        si.priority <- !toposort_counter ;
        incr toposort_counter 
      end

    (* we set this to true whenever we eliminate an IF or otherwise 
     * change the CFG *)
    let changed_cfg = ref false 

    (* Partially evaluate / constant fold a statement. Basically this just
     * asks the Symex algorithm to evaluate the RHS in the current state
     * and then compute a new state that incorporates the assignment. 
     *
     * However, we have special handling for ifs and calls. If we can
     * evaluate an if predicate to a constant, we remove the if. 
     *
     * If we are going to make a call to a function with an empty body, we
     * remove the function call. *)
    let partial_stmt c state stmt handle_funcall = 
      let result = match stmt.skind with
        Instr(il) -> 
          let state = ref state in 
          let new_il = List.map (fun i -> 
            if debug then begin 
              ignore (Pretty.printf "Instr %a@!" d_instr i )
            end ;
            match i with
            | Set(l,e,loc) -> 
                let e', state' = S.assign !state l e in
                state := state' ;
                [Set(l,e',loc)]
            | Call(lo,(Lval(Var(vi),NoOffset)),al,loc) -> 
                let result = begin
                  try 
                    let fd = C.fundec_of_varinfo c vi in
                    begin 
                    match fd.sbody.bstmts with
                      [] -> [] (* no point in making this call *)
                    | hd :: tl -> 
                        let al', state' = S.call !state fd al in
                        handle_funcall stmt hd state' ;
                        let state'' = S.return state' fd in 
                        state := state'' ;
                        [Call(lo,(Lval(Var(vi),NoOffset)),al',loc)]
                    end
                  with e ->
                    let state'' = S.call_to_unknown_function !state in
                    let al' = List.map (S.evaluate !state) al in 
                    state := state'' ; 
                    [Call(lo,(Lval(Var(vi),NoOffset)),al',loc)]
                end in 
                (* handle return value *)
                begin 
                  match lo with
                    Some(lv) -> state := S.unassign !state lv 
                  | _ -> () 
                end ;
                result
            | Call(lo,f,al,loc) -> 
                let al' = List.map (S.evaluate !state) al in 
                state := S.call_to_unknown_function !state ;
                (match lo with
                  Some(lv) -> state := S.unassign !state lv
                | None -> ()) ;
                [Call(lo,f,al',loc)]
            | Asm(_) -> state := S.assembly !state i ; [i] 
          ) il in
          stmt.skind <- Instr(List.flatten new_il) ;
          if debug then begin 
            ignore (Pretty.printf "New Stmt is %a@!" d_stmt stmt) ; 
          end ;
          !state

      | If(e,b1,b2,loc) -> 
          let e' = S.evaluate state e in 
          (* Pretty.printf "%a evals to %a\n" d_exp e d_exp e' ; *)

          (* helper function to remove an IF branch *)
          let remove b remains = begin 
            changed_cfg := true ; 
            (match b.bstmts with
            | [] -> ()
            | hd :: tl -> 
              stmt.succs <- List.filter (fun succ -> succ.sid <> hd.sid)
                stmt.succs 
            ) 
          end in 

          if (e' = one) then begin
            if b2.bstmts = [] && b2.battrs = [] then begin
              stmt.skind <- Block(b1) ;
              match b1.bstmts with
                [] -> failwith "partial: completely empty if" 
              | hd :: tl -> stmt.succs <- [hd]
            end else 
              stmt.skind <- Block( 
              { bstmts = 
                [ mkStmt (Block(b1)) ;
                  mkStmt (If(zero,b2,{bstmts=[];battrs=[];},loc)) ] ;
                battrs = [] } ) ;
            remove b2 b1 ;
            state
          end else if (e' = zero) then begin
            if b1.bstmts = [] && b1.battrs = [] then begin
              stmt.skind <- Block(b2) ;
              match b2.bstmts with
                [] -> failwith "partial: completely empty if" 
              | hd :: tl -> stmt.succs <- [hd]
            end else 
            stmt.skind <- Block(
            { bstmts = 
              [ mkStmt (Block(b2)) ;
                mkStmt (If(zero,b1,{bstmts=[];battrs=[];},loc)) ] ;
              battrs = [] } ) ;
            remove b1 b2 ; 
            state
          end else begin
            stmt.skind <- If(e',b1,b2,loc) ;
            state
          end 

      | Return(Some(e),loc) ->
          let e' = S.evaluate state e in 
          stmt.skind <- Return(Some(e'),loc) ;
          state

      | Block(b) ->
          if debug && List.length stmt.succs > 1 then begin
            ignore (Pretty.printf "(%a) has successors [%a]@!"
              d_stmt stmt 
              (docList ~sep:(chr '@') (d_stmt ()))
              stmt.succs)
          end ;
          state

      | _ -> state
    in result

    (* 
     * This is the main conceptual entry-point for the partial evaluation 
     * data-flow functor.
     *)
    let dataflow (file : Cil.file)         (* whole program *)
                 (c : C.t)                 (* control-flow graph *)
                 (initial_state : S.t)     (* any assumptions? *)
                 (initial_stmt : Cil.stmt) (* entry point *) 
    = begin
      (* count the total number of statements in the program *)
      let num_stmts = ref 1 in
      iterGlobals file (fun g -> match g with
        GFun(fd,_) -> begin
          match fd.smaxstmtid with
            Some(i) -> if i > !num_stmts then num_stmts := i 
          | None -> () 
          end
      | _ -> () 
      ) ;
      (if debug then 
      Printf.printf "Dataflow: at most %d statements in program\n" !num_stmts); 

      (* create a priority queue in which to store statements *) 
      let worklist = Heap.create !num_stmts in

      let finished = ref false in
      let passes = ref 0 in

      (* add something to the work queue *)
      let enqueue caller callee state = begin
        let si = get_sinfo callee in 
        Hashtbl.replace si.incoming_state caller.sid state ;
        Heap.insert worklist si.priority callee
      end in 

      (* we will be finished when we complete a round of data-flow that
       * does not change the ICFG *)
      while not !finished do 
        clear_sinfo () ; 
        incr passes ; 

        (* we must recompute the ordering and the predecessor information
         * because we may have changed it by removing IFs *)
        (if debug then Printf.printf "Dataflow: Topological Sorting & Reachability\n" );
        toposort c initial_stmt ;  

        let initial_si = get_sinfo initial_stmt in
        Heap.insert worklist initial_si.priority initial_stmt ;

        while not (Heap.is_empty worklist) do
          let (p,s) = Heap.extract_max worklist in 
          if debug then begin 
            ignore (Pretty.printf "Working on stmt %d (%a) %a@!" 
              s.sid 
              (docList ~sep:(chr ',' ++ break) (fun s -> dprintf "%d" s.sid))
              s.succs
              d_stmt s) ; 
            flush stdout ;
          end ; 
          let si = get_sinfo s in 

          (* Even though this stmt is on the worklist, we may not have
           * to do anything with it if the join of all of the incoming
           * states is the same as the last state we used here. *) 
          let must_recompute, incoming_state = 
            begin
              let list_of_incoming_states = ref [] in
              Hashtbl.iter (fun true_pred_sid b -> 
                let this_pred_state =
                  try
                    Hashtbl.find si.incoming_state true_pred_sid
                  with _ -> 
                    (* this occurs when we're evaluating a statement and we
                     * have not yet evaluated all of its predecessors (the
                     * first time we look at a loop head, say). We must be
                     * conservative. We'll come back later with better
                     * information (as we work toward the fix-point). *) 
                    S.empty 
                in
                if debug then begin 
                  Printf.printf " Incoming State from %d\n" true_pred_sid ;
                  S.debug this_pred_state ; 
                  flush stdout ; 
                end ; 
                list_of_incoming_states := this_pred_state ::
                  !list_of_incoming_states 
              ) si.reachable_preds ; 
              let merged_incoming_state = 
                if !list_of_incoming_states = [] then
                  (* this occurs when we're looking at the first statement
                   * in "main" -- it has no preds *) 
                  initial_state
                else 
                  S.join !list_of_incoming_states 
              in
              if debug then begin 
                Printf.printf " Merged State:\n" ;
                S.debug merged_incoming_state ; 
                flush stdout ; 
              end ;
              let must_recompute = match si.last_used_state with
                None -> true
              | Some(last) -> not (S.equal merged_incoming_state last)
              in must_recompute, merged_incoming_state 
            end 
          in 
          if must_recompute then begin
            si.last_used_state <- Some(incoming_state) ; 
            let outgoing_state = 
              (* partially evaluate and optimize the statement *) 
              partial_stmt c incoming_state s enqueue in
            let fresh_succs = s.succs in 
            (* touch every successor so that we will reconsider it *)
            List.iter (fun succ ->
              enqueue s succ outgoing_state 
            ) fresh_succs ;
          end else begin
            if debug then begin 
              Printf.printf "No need to recompute.\n" 
            end 
          end
        done ;
        (if debug then Printf.printf "Dataflow: Pass %d Complete\n" !passes) ;
        if !changed_cfg then begin
          (if debug then Printf.printf "Dataflow: Restarting (CFG Changed)\n") ;
          changed_cfg := false 
        end else 
          finished := true 
      done ;
      (if debug then Printf.printf "Dataflow: Completed (%d passes)\n" !passes) 

    end 
    
  let simplify file c fd (assumptions : (Cil.lval * Cil.exp) list) =
    let starting_state = List.fold_left (fun s (l,e) ->
      let e',s' = S.assign s l e in 
      s'
    ) S.empty assumptions in 
    dataflow file c starting_state (List.hd fd.sbody.bstmts)

  end


(* 
 * Currently our partial-eval optimizer is built out of basically nothing.  
 * The alias analysis is fake, the call grpah is cheap, and we're using
 * George's old basic-block symex. Still, it works. 
 *)
(* Don't you love Functor application? *)
module BasicCallGraph = EasyCallGraph(EasyAlias)
module BasicSymex = NeculaFolding(EasyAlias)
module BasicPartial = MakePartial(BasicSymex)(BasicCallGraph)(EasyAlias)

(*
 * A very easy entry-point to partial evaluation/symbolic execution.
 * You pass the Cil file and a list of assumptions (lvalue, exp pairs that 
 * should be treated as assignments that occur before the program starts). 
 *
 * We partially evaluate and optimize starting from "main". The Cil.file
 * is modified in place. 
 *)
let partial (f : Cil.file) (assumptions : (Cil.lval * Cil.exp) list) =
  try 
    find_all_functions_with_address_taken f ;
    let c = BasicCallGraph.compute f in 
    try 
      iterGlobals f (fun g -> match g with
        GFun(fd,_) when fd.svar.vname = "main" -> 
          BasicPartial.simplify f c fd assumptions 
      | _ -> ()) ;
    with e -> begin
      Printf.printf "Error in DataFlow: %s\n" (Printexc.to_string e) ;
      raise e
    end 
  with e -> begin
      Printf.printf "Error in Partial: %s\n" (Printexc.to_string e) ;
      raise e
    end 

let feature : featureDescr = 
  { fd_name = "partial";
    fd_enabled = Cilutil.doPartial;
    fd_description = "interprocedural partial evaluation and constant folding" ;
    fd_extraopt = [];
    fd_doit = (function (f: file) -> 
      if not !Cilutil.makeCFG then begin
        Errormsg.s (Errormsg.error "--dopartial: you must also specify --domakeCFG\n")
      end ; 
      partial f [] ) ;
    fd_post_check = false;
  } 

(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)
