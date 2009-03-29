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
module H = Hashtbl
open Cil
open Pretty
module E = Errormsg

let debug = false


(* For each function we have a node *)
type node = { name: string;
              mutable scanned: bool;
              mutable mustcheck: bool;
              mutable succs: node list }
(* We map names to nodes *)
let functionNodes: (string, node) H.t = H.create 113 
let getFunctionNode (n: string) : node = 
  Util.memoize 
    functionNodes
    n
    (fun _ -> { name = n; mustcheck = false; scanned = false; succs = [] })

(** Dump the function call graph. Assume that there is a main *)
let dumpGraph = true
let dumpFunctionCallGraph () = 
  H.iter (fun _ x -> x.scanned <- false) functionNodes;
  let rec dumpOneNode (ind: int) (n: node) : unit = 
    output_string !E.logChannel "\n";
    for i = 0 to ind do 
      output_string !E.logChannel "  "
    done;
    output_string !E.logChannel (n.name ^ " ");
    if n.scanned then (* Already dumped *)
      output_string !E.logChannel " <rec> "
    else begin
      n.scanned <- true;
      List.iter (dumpOneNode (ind + 1)) n.succs
    end
  in
  try
    let main = H.find functionNodes "main" in
    dumpOneNode 0 main
  with Not_found -> begin
    ignore (E.log 
              "I would like to dump the function graph but there is no main");
  end
  
(* We add a dummy function whose name is "@@functionPointer@@" that is called 
 * at all invocations of function pointers and itself calls all functions 
 * whose address is taken.  *)
let functionPointerName = "@@functionPointer@@"

let checkSomeFunctions = ref false

let init () = 
  H.clear functionNodes;
  checkSomeFunctions := false


let addCall (caller: string) (callee: string) = 
  let callerNode = getFunctionNode caller in
  let calleeNode = getFunctionNode callee in
  if not (List.exists (fun n -> n.name = callee) callerNode.succs) then begin
    if debug then
      ignore (E.log "found call from %s to %s\n" caller callee);
    callerNode.succs <- calleeNode :: callerNode.succs;
  end;
  ()


class findCallsVisitor (host: string) : cilVisitor = object
  inherit nopCilVisitor

  method vinst i =
    match i with
    | Call(_,Lval(Var(vi),NoOffset),_,l) -> 
        addCall host vi.vname;
        SkipChildren

    | Call(_,e,_,l) -> (* Calling a function pointer *)
        addCall host functionPointerName;
        SkipChildren

    | _ -> SkipChildren (* No calls in other instructions *)

  (* There are no calls in expressions and types *)          
  method vexpr e = SkipChildren
  method vtype t = SkipChildren

end

(* Now detect the cycles in the call graph. Do a depth first search of the 
 * graph (stack is the list of nodes already visited in the current path). 
 * Return true if we have found a cycle. *)
let rec breakCycles (stack: node list) (n: node) : bool = 
  if n.scanned then (* We have already scanned this node. There are no cycles 
                     * going through this node *)
    false
  else if n.mustcheck then 
    (* We are reaching a node that we already know we much check. Return with 
     * no new cycles. *)
    false
  else if List.memq n stack then begin
    (* We have found a cycle. Mark the node n to be checked and return *)
    if debug then
      ignore (E.log "Will place an overflow check in %s\n" n.name);
    checkSomeFunctions := true;
    n.mustcheck <- true;
    n.scanned <- true;
    true
  end else begin
    let res = List.exists (fun nd -> breakCycles (n :: stack) nd) n.succs in
    n.scanned <- true;
    if res && n.mustcheck then 
      false
    else
      res
  end
let findCheckPlacement () = 
  H.iter (fun _ nd -> 
    if nd.name <> functionPointerName 
       && not nd.scanned && not nd.mustcheck then begin
         ignore (breakCycles [] nd)
       end)
    functionNodes

let makeFunctionCallGraph (f: Cil.file) : unit = 
  init ();
  (* Scan the file and construct the control-flow graph *)
  List.iter
    (function
        GFun(fdec, _) -> 
          if fdec.svar.vaddrof then 
            addCall functionPointerName fdec.svar.vname;
          let vis = new findCallsVisitor fdec.svar.vname in
          ignore (visitCilBlock vis fdec.sbody)

      | _ -> ())
    f.globals

let makeAndDumpFunctionCallGraph (f: file) = 
  makeFunctionCallGraph f;
  dumpFunctionCallGraph ()


let addCheck (f: Cil.file) : unit = 
  makeFunctionCallGraph f;
  findCheckPlacement ();
  if !checkSomeFunctions then begin
    (* Add a declaration for the stack threshhold variable. The program is 
     * stopped when the stack top is less than this value. *)
    let stackThreshholdVar = makeGlobalVar "___stack_threshhold" !upointType in
    stackThreshholdVar.vstorage <- Extern;
    (* And the initialization function *)
    let computeStackThreshhold = 
      makeGlobalVar "___compute_stack_threshhold" 
        (TFun(!upointType, Some [], false, [])) in
    computeStackThreshhold.vstorage <- Extern;
    (* And the failure function *)
    let stackOverflow = 
      makeGlobalVar "___stack_overflow" 
        (TFun(voidType, Some [], false, [])) in
    stackOverflow.vstorage <- Extern;
    f.globals <- 
       GVar(stackThreshholdVar, {init=None}, locUnknown) ::
       GVarDecl(computeStackThreshhold, locUnknown) ::
       GVarDecl(stackOverflow, locUnknown) :: f.globals;
    (* Now scan and instrument each function definition *)
    List.iter
      (function 
          GFun(fdec, l) -> 
            (* If this is main we must introduce the initialization of the 
             * bottomOfStack *)
            let nd = getFunctionNode fdec.svar.vname in
            if fdec.svar.vname = "main" then begin
              if nd.mustcheck then 
                E.s (E.error "The \"main\" function is recursive!!");
              let loc = makeLocalVar fdec "__a_local" intType in
              loc.vaddrof <- true;
              fdec.sbody <- 
                 mkBlock
                   [ mkStmtOneInstr
                       (Call (Some(var stackThreshholdVar), 
                              Lval(var computeStackThreshhold), [], l));
                     mkStmt (Block fdec.sbody) ]
            end else if nd.mustcheck then begin
              let loc = makeLocalVar fdec "__a_local" intType in
              loc.vaddrof <- true;
              fdec.sbody <- 
                 mkBlock
                   [ mkStmt
                       (If(BinOp(Le, 
                                 CastE(!upointType, AddrOf (var loc)),
                                 Lval(var stackThreshholdVar), intType),
                           mkBlock [mkStmtOneInstr
                                  (Call(None, Lval(var stackOverflow),
                                        [], l))],
                           mkBlock [],
                           l));
                     mkStmt (Block fdec.sbody) ]
            end else
              ()

        | _ -> ())
      f.globals;
    ()
  end




