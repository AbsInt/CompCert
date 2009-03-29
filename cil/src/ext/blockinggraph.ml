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
open Cil
open Pretty
module E = Errormsg

let debug = false

let fingerprintAll = true


type blockkind =
    NoBlock
  | BlockTrans
  | BlockPoint
  | EndPoint

(* For each function we have a node *)
type node =
{
  nodeid: int;
  name: string;
  mutable scanned: bool;
  mutable expand: bool;
  mutable fptr: bool;
  mutable stacksize: int;
  mutable fds: fundec option;
  mutable bkind: blockkind;
  mutable origkind: blockkind;
  mutable preds: node list;
  mutable succs: node list;
  mutable predstmts: (stmt * node) list;
}

type blockpt =
{
  id: int;
  point: stmt;
  callfun: string;
  infun: string;
  mutable leadsto: blockpt list;
}


(* Fresh ids for each node. *)
let curNodeNum : int ref = ref 0
let getFreshNodeNum () : int =
  let num = !curNodeNum in
  incr curNodeNum;
  num

(* Initialize a node. *)
let newNode (name: string) (fptr: bool) (mangle: bool) : node =
  let id = getFreshNodeNum () in
  { nodeid = id; name = if mangle then name ^ (string_of_int id) else name;
    scanned = false; expand = false;
    fptr = fptr; stacksize = 0; fds = None;
    bkind = NoBlock; origkind = NoBlock;
    preds = []; succs = []; predstmts = []; }


(* My type signature ignores attributes and function pointers. *)
let myTypeSig (t: typ) : typsig =
  let rec removeFunPtrs (ts: typsig) : typsig =
    match ts with
      TSPtr (TSFun _, a) ->
        TSPtr (TSBase voidType, a)
    | TSPtr (base, a) ->
        TSPtr (removeFunPtrs base, a)
    | TSArray (base, e, a) ->
        TSArray (removeFunPtrs base, e, a)
    | TSFun (ret, args, v, a) ->
        TSFun (removeFunPtrs ret, List.map removeFunPtrs args, v, a)
    | _ -> ts
  in
  removeFunPtrs (typeSigWithAttrs (fun _ -> []) t)


(* We add a dummy function whose name is "@@functionPointer@@" that is called 
 * at all invocations of function pointers and itself calls all functions 
 * whose address is taken.  *)
let functionPointerName = "@@functionPointer@@"

(* We map names to nodes *)
let functionNodes: (string, node) Hashtbl.t = Hashtbl.create 113 
let getFunctionNode (n: string) : node = 
  Util.memoize 
    functionNodes
    n
    (fun _ -> newNode n false false)

(* We map types to nodes for function pointers *)
let functionPtrNodes: (typsig, node) Hashtbl.t = Hashtbl.create 113
let getFunctionPtrNode (t: typ) : node =
  Util.memoize
    functionPtrNodes
    (myTypeSig t)
    (fun _ -> newNode functionPointerName true true)

let startNode: node = newNode "@@startNode@@" true false


(*
(** Dump the function call graph. *)
let dumpFunctionCallGraph (start: node) = 
  Hashtbl.iter (fun _ x -> x.scanned <- false) functionNodes;
  let rec dumpOneNode (ind: int) (n: node) : unit = 
    output_string !E.logChannel "\n";
    for i = 0 to ind do 
      output_string !E.logChannel "  "
    done;
    output_string !E.logChannel (n.name ^ " ");
    begin
      match n.bkind with
        NoBlock -> ()
      | BlockTrans -> output_string !E.logChannel " <blocks>"
      | BlockPoint -> output_string !E.logChannel " <blockpt>"
      | EndPoint -> output_string !E.logChannel " <endpt>"
    end;
    if n.scanned then (* Already dumped *)
      output_string !E.logChannel " <rec> "
    else begin
      n.scanned <- true;
      List.iter (fun n -> if n.bkind <> EndPoint then dumpOneNode (ind + 1) n)
                n.succs
    end
  in
  dumpOneNode 0 start;
  output_string !E.logChannel "\n\n"
*)

let dumpFunctionCallGraphToFile () = 
  let channel = open_out "graph" in
  let dumpNode _ (n: node) : unit =
    let first = ref true in
    let dumpSucc (n: node) : unit =
      if !first then
        first := false
      else
        output_string channel ",";
      output_string channel n.name
    in
    output_string channel (string_of_int n.nodeid);
    output_string channel ":";
    output_string channel (string_of_int n.stacksize);
    output_string channel ":";
    if n.fds = None && not n.fptr then
      output_string channel "x";
    output_string channel ":";
    output_string channel n.name;
    output_string channel ":";
    List.iter dumpSucc n.succs;
    output_string channel "\n";
  in
  dumpNode () startNode;
  Hashtbl.iter dumpNode functionNodes;
  Hashtbl.iter dumpNode functionPtrNodes;
  close_out channel
  

let addCall (callerNode: node) (calleeNode: node) (sopt: stmt option) =
  if not (List.exists (fun n -> n.name = calleeNode.name)
                      callerNode.succs) then begin
    if debug then
      ignore (E.log "found call from %s to %s\n"
                    callerNode.name calleeNode.name);
    callerNode.succs <- calleeNode :: callerNode.succs;
    calleeNode.preds <- callerNode :: calleeNode.preds;
  end;
  match sopt with
    Some s ->
      if not (List.exists (fun (s', _) -> s' = s) calleeNode.predstmts) then
        calleeNode.predstmts <- (s, callerNode) :: calleeNode.predstmts
  | None -> ()


class findCallsVisitor (host: node) : cilVisitor = object
  inherit nopCilVisitor

  val mutable curStmt : stmt ref = ref (mkEmptyStmt ())

  method vstmt s =
    curStmt := s;
    DoChildren

  method vinst i =
    match i with
    | Call(_,Lval(Var(vi),NoOffset),args,l) -> 
        addCall host (getFunctionNode vi.vname) (Some !curStmt);
        SkipChildren

    | Call(_,e,_,l) -> (* Calling a function pointer *)
        addCall host (getFunctionPtrNode (typeOf e)) (Some !curStmt);
        SkipChildren

    | _ -> SkipChildren (* No calls in other instructions *)

  (* There are no calls in expressions and types *)          
  method vexpr e = SkipChildren
  method vtype t = SkipChildren

end


let endPt = { id = 0; point = mkEmptyStmt (); callfun = "end"; infun = "end";
              leadsto = []; }

(* These values will be initialized for real in makeBlockingGraph. *)
let curId : int ref = ref 1
let startName : string ref = ref ""
let blockingPoints : blockpt list ref = ref []
let blockingPointsNew : blockpt Queue.t = Queue.create ()
let blockingPointsHash : (int, blockpt) Hashtbl.t = Hashtbl.create 113

let getFreshNum () : int =
  let num = !curId in
  curId := !curId + 1;
  num

let getBlockPt (s: stmt) (cfun: string) (ifun: string) : blockpt =
  try
    Hashtbl.find blockingPointsHash s.sid
  with Not_found ->
    let num = getFreshNum () in
    let bpt = { id = num; point = s; callfun = cfun; infun = ifun;
                leadsto = []; } in
    Hashtbl.add blockingPointsHash s.sid bpt;
    blockingPoints := bpt :: !blockingPoints;
    Queue.add bpt blockingPointsNew;
    bpt


type action =
    Process of stmt * node
  | Next of stmt * node
  | Return of node

let getStmtNode (s: stmt) : node option =
  match s.skind with
    Instr instrs -> begin
      let len = List.length instrs in
      if len > 0 then
        match List.nth instrs (len - 1) with
          Call (_, Lval (Var vi, NoOffset), args, _) -> 
            Some (getFunctionNode vi.vname)
        | Call (_, e, _, _) -> (* Calling a function pointer *)
            Some (getFunctionPtrNode (typeOf e))
        | _ ->
            None
      else
        None
      end
  | _ -> None

let addBlockingPointEdge (bptFrom: blockpt) (bptTo: blockpt) : unit =
  if not (List.exists (fun bpt -> bpt = bptTo) bptFrom.leadsto) then
    bptFrom.leadsto <- bptTo :: bptFrom.leadsto

let findBlockingPointEdges (bpt: blockpt) : unit =
  let seenStmts = Hashtbl.create 117 in
  let worklist = Queue.create () in
  Queue.add (Next (bpt.point, getFunctionNode bpt.infun)) worklist;
  while Queue.length worklist > 0 do
    let act = Queue.take worklist in
    match act with
      Process (curStmt, curNode) -> begin
        Hashtbl.add seenStmts curStmt.sid ();
        match getStmtNode curStmt with
          Some node -> begin
            if debug then
              ignore (E.log "processing node %s\n" node.name);
            match node.bkind with
              NoBlock ->
                Queue.add (Next (curStmt, curNode)) worklist
            | BlockTrans -> begin
                let processFundec (fd: fundec) : unit =
                  let s = List.hd fd.sbody.bstmts in
                  if not (Hashtbl.mem seenStmts s.sid) then
                    let n = getFunctionNode fd.svar.vname in
                    Queue.add (Process (s, n)) worklist
                in
                match node.fds with
                  Some fd ->
                    processFundec fd
                | None ->
                    List.iter
                      (fun n ->
                         match n.fds with
                           Some fd -> processFundec fd
                         | None -> E.s (bug "expected fundec"))
                      node.succs
              end
            | BlockPoint ->
                addBlockingPointEdge bpt
                  (getBlockPt curStmt node.name curNode.name)
            | EndPoint ->
                addBlockingPointEdge bpt endPt
          end
        | _ ->
            Queue.add (Next (curStmt, curNode)) worklist
      end
    | Next (curStmt, curNode) -> begin
        match curStmt.Cil.succs with
          [] ->
            if debug then
              ignore (E.log "hit end of %s\n" curNode.name);
            Queue.add (Return curNode) worklist
        | _ ->
            List.iter (fun s ->
                         if not (Hashtbl.mem seenStmts s.sid) then
                           Queue.add (Process (s, curNode)) worklist)
                      curStmt.Cil.succs
      end
    | Return curNode when curNode.bkind = NoBlock ->
        ()
    | Return curNode when curNode.name = !startName ->
        addBlockingPointEdge bpt endPt
    | Return curNode ->
        List.iter (fun (s, n) -> if n.bkind <> NoBlock then
                                   Queue.add (Next (s, n)) worklist)
                  curNode.predstmts;
        List.iter (fun n -> if n.fptr then
                               Queue.add (Return n) worklist)
                  curNode.preds
  done

let markYieldPoints (n: node) : unit =
  let rec markNode (n: node) : unit =
    if n.bkind = NoBlock then
      match n.origkind with
        BlockTrans ->
          if n.expand || n.fptr then begin
            n.bkind <- BlockTrans;
            List.iter markNode n.succs
          end else begin
            n.bkind <- BlockPoint
          end
      | _ ->
          n.bkind <- n.origkind
  in
  Hashtbl.iter (fun _ n -> n.bkind <- NoBlock) functionNodes;
  Hashtbl.iter (fun _ n -> n.bkind <- NoBlock) functionPtrNodes;
  markNode n

let makeBlockingGraph (start: node) =
  let startStmt =
    match start.fds with
      Some fd -> List.hd fd.sbody.bstmts
    | None -> E.s (bug "expected fundec")
  in
  curId := 1;
  startName := start.name;
  blockingPoints := [endPt];
  Queue.clear blockingPointsNew;
  Hashtbl.clear blockingPointsHash;
  ignore (getBlockPt startStmt start.name start.name);
  while Queue.length blockingPointsNew > 0 do
    let bpt = Queue.take blockingPointsNew in
    findBlockingPointEdges bpt;
  done

let dumpBlockingGraph () =
  List.iter
    (fun bpt ->
       if bpt.id < 2 then begin
         ignore (E.log "bpt %d (%s): " bpt.id bpt.callfun)
       end else begin
         ignore (E.log "bpt %d (%s in %s): " bpt.id bpt.callfun bpt.infun)
       end;
       List.iter (fun bpt -> ignore (E.log "%d " bpt.id)) bpt.leadsto;
       ignore (E.log "\n"))
    !blockingPoints;
  ignore (E.log "\n")

let beforeFun =
  makeGlobalVar "before_bg_node"
                (TFun (voidType, Some [("node_idx", intType, []);
                                       ("num_edges", intType, [])],
                       false, []))

let initFun =
  makeGlobalVar "init_blocking_graph"
                (TFun (voidType, Some [("num_nodes", intType, [])],
                       false, []))

let fingerprintVar =
  let vi = makeGlobalVar "stack_fingerprint" intType in
  vi.vstorage <- Extern;
  vi

let startNodeAddrs =
  let vi = makeGlobalVar "start_node_addrs" (TPtr (voidPtrType, [])) in
  vi.vstorage <- Extern;
  vi

let startNodeStacks =
  let vi = makeGlobalVar "start_node_stacks" (TPtr (intType, [])) in
  vi.vstorage <- Extern;
  vi

let startNodeAddrsArray =
  makeGlobalVar "start_node_addrs_array" (TArray (voidPtrType, None, [])) 

let startNodeStacksArray =
  makeGlobalVar "start_node_stacks_array" (TArray (intType, None, [])) 

let insertInstr (newInstr: instr) (s: stmt) : unit =
  match s.skind with
    Instr instrs ->
      let rec insert (instrs: instr list) : instr list =
        match instrs with
          [] -> E.s (bug "instr list does not end with call\n")
        | [Call _] -> newInstr :: instrs
        | i :: rest -> i :: (insert rest)
      in
      s.skind <- Instr (insert instrs)
  | _ ->
      E.s (bug "instr stmt expected\n")

let instrumentBlockingPoints () =
  List.iter
    (fun bpt ->
       if bpt.id > 1 then
       let arg1 = integer bpt.id in
       let arg2 = integer (List.length bpt.leadsto) in
       let call = Call (None, Lval (var beforeFun),
                        [arg1; arg2], locUnknown) in
       insertInstr call bpt.point;
       addCall (getFunctionNode bpt.infun)
               (getFunctionNode beforeFun.vname) None)
    !blockingPoints


let startNodes : node list ref = ref []

let makeAndDumpBlockingGraphs () : unit =
  if List.length !startNodes > 1 then
    E.s (unimp "We can't handle more than one start node right now.\n");
  List.iter
    (fun n ->
       markYieldPoints n;
       (*dumpFunctionCallGraph n;*)
       makeBlockingGraph n;
       dumpBlockingGraph ();
       instrumentBlockingPoints ())
    !startNodes


let pragmas : (string, int) Hashtbl.t = Hashtbl.create 13

let gatherPragmas (f: file) : unit =
  List.iter
    (function
       GPragma (Attr ("stacksize", [AStr s; AInt n]), _) ->
         Hashtbl.add pragmas s n
     | _ -> ())
    f.globals


let blockingNodes : node list ref = ref []

let markBlockingFunctions () : unit =
  let rec markFunction (n: node) : unit =
    if debug then
      ignore (E.log "marking %s\n" n.name);
    if n.origkind = NoBlock then begin
      n.origkind <- BlockTrans;
      List.iter markFunction n.preds;
    end
  in
  List.iter (fun n -> List.iter markFunction n.preds) !blockingNodes

let hasFunctionTypeAttribute (n: string) (t: typ) : bool = 
  let _, _, _, a = splitFunctionType t in 
  hasAttribute n a

let markVar (vi: varinfo) : unit =
  let node = getFunctionNode vi.vname in
  if node.origkind = NoBlock then begin
    if hasAttribute "yield" vi.vattr then begin
      node.origkind <- BlockPoint;
      blockingNodes := node :: !blockingNodes;
    end else if hasFunctionTypeAttribute "noreturn" vi.vtype then begin
      node.origkind <- EndPoint;
    end else if hasAttribute "expand" vi.vattr then begin
      node.expand <- true;
    end
  end;
  begin
    try
      node.stacksize <- Hashtbl.find pragmas node.name
    with Not_found -> begin
      match filterAttributes "stacksize" vi.vattr with
        (Attr (_, [AInt n])) :: _ when n > node.stacksize ->
          node.stacksize <- n
      | _ -> ()
    end
  end

let makeFunctionCallGraph (f: Cil.file) : unit = 
  Hashtbl.clear functionNodes;
  (* Scan the file and construct the control-flow graph *)
  List.iter
    (function
        GFun(fdec, _) -> 
          let curNode = getFunctionNode fdec.svar.vname in
          if fdec.svar.vaddrof then begin
            addCall (getFunctionPtrNode fdec.svar.vtype)
                    curNode None;
          end;
          if hasAttribute "start" fdec.svar.vattr then begin
            startNodes := curNode :: !startNodes;
          end;
          markVar fdec.svar;
          curNode.fds <- Some fdec;
          let vis = new findCallsVisitor curNode in
          ignore (visitCilBlock vis fdec.sbody)

      | GVarDecl(vi, _) when isFunctionType vi.vtype ->
          (* TODO: what if we take the addr of an extern? *)
          markVar vi

      | _ -> ())
    f.globals

let makeStartNodeLinks () : unit =
  addCall startNode (getFunctionNode "main") None;
  List.iter (fun n -> addCall startNode n None) !startNodes

let funType (ret_t: typ) (args: (string * typ) list) = 
  TFun(ret_t, 
      Some (List.map (fun (n,t) -> (n, t, [])) args),
      false, [])

class instrumentClass = object
  inherit nopCilVisitor

  val mutable curNode : node ref = ref (getFunctionNode "main")
  val mutable seenRet : bool ref = ref false

  val mutable funId : int ref = ref 0

  method vfunc (fdec: fundec) : fundec visitAction = begin
    (* Remember the current function. *)
    curNode := getFunctionNode fdec.svar.vname;
    seenRet := false;
    funId := Random.bits ();
    (* Add useful locals. *)
    ignore (makeLocalVar fdec "savesp" voidPtrType);
    ignore (makeLocalVar fdec "savechunk" voidPtrType);
    ignore (makeLocalVar fdec "savebottom" voidPtrType);
    (* Add macro for function entry when we're done. *)
    let addEntryNode (fdec: fundec) : fundec =
      if not !seenRet then E.s (bug "didn't find a return statement");
      let node = getFunctionNode fdec.svar.vname in
      if fingerprintAll || node.origkind <> NoBlock then begin
        let fingerprintSet =
          Set (var fingerprintVar, BinOp (BXor, Lval (var fingerprintVar),
                                          integer !funId, intType),
               locUnknown)
        in
        fdec.sbody.bstmts <- mkStmtOneInstr fingerprintSet :: fdec.sbody.bstmts
      end;
      let nodeFun = emptyFunction ("NODE_CALL_"^(string_of_int node.nodeid)) in
      let nodeCall = Call (None, Lval (var nodeFun.svar), [], locUnknown) in
      nodeFun.svar.vtype <- funType voidType [];
      nodeFun.svar.vstorage <- Static;
      fdec.sbody.bstmts <- mkStmtOneInstr nodeCall :: fdec.sbody.bstmts;
      fdec
    in
    ChangeDoChildrenPost (fdec, addEntryNode)
  end

  method vstmt (s: stmt) : stmt visitAction = begin
    begin
      match s.skind with
        Instr instrs -> begin
          let instrumentNode (callNode: node) : unit =
            (* Make calls to macros. *)
            let suffix = "_" ^ (string_of_int !curNode.nodeid) ^
                         "_" ^ (string_of_int callNode.nodeid)
            in
            let beforeFun = emptyFunction ("BEFORE_CALL" ^ suffix) in
            let beforeCall = Call (None, Lval (var beforeFun.svar),
                                   [], locUnknown) in
            beforeFun.svar.vtype <- funType voidType [];
            beforeFun.svar.vstorage <- Static;
            let afterFun = emptyFunction ("AFTER_CALL" ^ suffix) in
            let afterCall = Call (None, Lval (var afterFun.svar),
                                  [], locUnknown) in
            afterFun.svar.vtype <- funType voidType [];
            afterFun.svar.vstorage <- Static;
            (* Insert instrumentation around call site. *)
            let rec addCalls (is: instr list) : instr list =
              match is with
                [call] -> [beforeCall; call; afterCall]
              | cur :: rest -> cur :: addCalls rest
              | [] -> E.s (bug "expected list of non-zero length")
            in
            s.skind <- Instr (addCalls instrs)
          in
          (* If there's a call site here, instrument it. *)
          let len = List.length instrs in
          if len > 0 then begin
            match List.nth instrs (len - 1) with
              Call (_, Lval (Var vi, NoOffset), _, _) ->
              (*
                if (try String.sub vi.vname 0 10 <> "NODE_CALL_"
                    with Invalid_argument _ -> true) then
*)
                  instrumentNode (getFunctionNode vi.vname)
            | Call (_, e, _, _) -> (* Calling a function pointer *)
                instrumentNode (getFunctionPtrNode (typeOf e))
            | _ -> ()
          end;
          DoChildren
        end
      | Cil.Return _ -> begin
          if !seenRet then E.s (bug "found multiple returns");
          seenRet := true;
          if fingerprintAll || !curNode.origkind <> NoBlock then begin
            let fingerprintSet =
              Set (var fingerprintVar, BinOp (BXor, Lval (var fingerprintVar),
                                              integer !funId, intType),
                   locUnknown)
            in
            s.skind <- Block (mkBlock [mkStmtOneInstr fingerprintSet;
                                       mkStmt s.skind]);
          end;
          SkipChildren
        end
      | _ -> DoChildren
    end
  end
end

let makeStartNodeTable (globs: global list) : global list =
  if List.length !startNodes = 0 then
    globs
  else
    let addrInitInfo = { init = None } in
    let stackInitInfo = { init = None } in
    let rec processNode (nodes: node list) (i: int) =
      match nodes with
        node :: rest ->
          let curGlobs, addrInit, stackInit = processNode rest (i + 1) in
          let fd =
            match node.fds with
              Some fd -> fd
            | None -> E.s (bug "expected fundec")
          in
          let stack =
            makeGlobalVar ("NODE_STACK_" ^ (string_of_int node.nodeid)) intType
          in
          GVarDecl (fd.svar, locUnknown) :: curGlobs,
          ((Index (integer i, NoOffset), SingleInit (mkAddrOf (var fd.svar))) ::
           addrInit),
          ((Index (integer i, NoOffset), SingleInit (Lval (var stack))) ::
           stackInit)
      | [] -> (GVarDecl (startNodeAddrs, locUnknown) ::
               GVarDecl (startNodeStacks, locUnknown) ::
               GVar (startNodeAddrsArray, addrInitInfo, locUnknown) ::
               GVar (startNodeStacksArray, stackInitInfo, locUnknown) ::
               []),
              [Index (integer i, NoOffset), SingleInit zero],
              [Index (integer i, NoOffset), SingleInit zero]
    in
    let newGlobs, addrInit, stackInit = processNode !startNodes 0 in
    addrInitInfo.init <-
      Some (CompoundInit (TArray (voidPtrType, None, []), addrInit));
    stackInitInfo.init <-
      Some (CompoundInit (TArray (intType, None, []), stackInit));
    let file = { fileName = "startnode.h"; globals = newGlobs;
                 globinit = None; globinitcalled = false; } in
    let channel = open_out file.fileName in
    dumpFile defaultCilPrinter channel file;
    close_out channel;
    GText ("#include \"" ^ file.fileName ^ "\"") :: globs

let instrumentProgram (f: file) : unit =
  (* Add function prototypes. *)
  f.globals <- makeStartNodeTable f.globals;
  f.globals <- GText ("#include \"stack.h\"") ::
               GVarDecl (initFun, locUnknown) ::
               GVarDecl (beforeFun, locUnknown) ::
               GVarDecl (fingerprintVar, locUnknown) ::
               f.globals;
  (* Add instrumentation to call sites. *)
  visitCilFile ((new instrumentClass) :> cilVisitor) f;
  (* Force creation of this node. *)
  ignore (getFunctionNode beforeFun.vname);
  (* Add initialization call to main(). *)
  let mainNode = getFunctionNode "main" in
  match mainNode.fds with
    Some fdec ->
      let arg1 = integer (List.length !blockingPoints) in
      let initInstr = Call (None, Lval (var initFun), [arg1], locUnknown) in
      let addrsInstr =
        Set (var startNodeAddrs, StartOf (var startNodeAddrsArray),
             locUnknown)
      in
      let stacksInstr =
        Set (var startNodeStacks, StartOf (var startNodeStacksArray),
             locUnknown)
      in
      let newStmt =
        if List.length !startNodes = 0 then
          mkStmtOneInstr initInstr
        else
          mkStmt (Instr [addrsInstr; stacksInstr; initInstr])
      in
      fdec.sbody.bstmts <- newStmt :: fdec.sbody.bstmts;
      addCall mainNode (getFunctionNode initFun.vname) None
  | None ->
      E.s (bug "expected main fundec")



let feature : featureDescr = 
  { fd_name = "FCG";
    fd_enabled = ref false;
    fd_description = "computing and printing a static call graph";
    fd_extraopt = [];
    fd_doit = 
    (function (f : file) ->
      Random.init 0; (* Use the same seed so that results are predictable. *)
      gatherPragmas f;
      makeFunctionCallGraph f;
      makeStartNodeLinks ();
      markBlockingFunctions ();
      (* makeAndDumpBlockingGraphs (); *)
      instrumentProgram f;
      dumpFunctionCallGraphToFile ());
    fd_post_check = true;
  } 
