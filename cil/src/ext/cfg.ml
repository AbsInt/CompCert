(* MODIF: Loop constructor replaced by 3 constructors: While, DoWhile, For. *)

(*
 *
 * Copyright (c) 2001-2003, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 *  Simon Goldsmith     <sfg@cs.berkeley.edu>
 *  S.P Rahul, Aman Bhargava
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

(* Authors: Aman Bhargava, S. P. Rahul *)
(* sfg: this stuff was stolen from optim.ml - the code to print the cfg as
   a dot graph is mine *)

open Pretty
open Cil
module E=Errormsg

(* entry points: cfgFun, printCfgChannel, printCfgFilename *)

(* known issues:
 * -sucessors of if somehow end up with two edges each 
 *)

(*------------------------------------------------------------*)
(* Notes regarding CFG computation:
   1) Initially only succs and preds are computed. sid's are filled in
      later, in whatever order is suitable (e.g. for forward problems, reverse
      depth-first postorder).
   2) If a stmt (return, break or continue) has no successors, then
      function return must follow.
      No predecessors means it is the start of the function
   3) We use the fact that initially all the succs and preds are assigned []
*)

(* Fill in the CFG info for the stmts in a block
   next = succ of the last stmt in this block
   break = succ of any Break in this block
   cont  = succ of any Continue in this block
   None means the succ is the function return. It does not mean the break/cont
   is invalid. We assume the validity has already been checked.
*)
(* At the end of CFG computation, 
   - numNodes = total number of CFG nodes 
   - length(nodeList) = numNodes
*)

let numNodes = ref 0 (* number of nodes in the CFG *)
let nodeList : stmt list ref = ref [] (* All the nodes in a flat list *) (* ab: Added to change dfs from quadratic to linear *)
let start_id = ref 0 (* for unique ids across many functions *)

(* entry point *)

(** Compute a control flow graph for fd.  Stmts in fd have preds and succs
  filled in *)
let rec cfgFun (fd : fundec): int = 
  begin
    numNodes := !start_id;
    nodeList := [];

    cfgBlock fd.sbody None None None;
    !numNodes - !start_id
  end


and cfgStmts (ss: stmt list) 
                 (next:stmt option) (break:stmt option) (cont:stmt option) =
  match ss with
    [] -> ();
  | [s] -> cfgStmt s next break cont
  | hd::tl ->
      cfgStmt hd (Some (List.hd tl))  break cont;
      cfgStmts tl next break cont

and cfgBlock  (blk: block) 
              (next:stmt option) (break:stmt option) (cont:stmt option) = 
   cfgStmts blk.bstmts next break cont

(* Fill in the CFG info for a stmt
   Meaning of next, break, cont should be clear from earlier comment
*)
and cfgStmt (s: stmt) (next:stmt option) (break:stmt option) (cont:stmt option) =
  incr numNodes;
  s.sid <- !numNodes;
  nodeList := s :: !nodeList; (* Future traversals can be made in linear time. e.g.  *)
  if s.succs <> [] then
    E.s (bug "CFG must be cleared before being computed!");
  let addSucc (n: stmt) =
    if not (List.memq n s.succs) then
      s.succs <- n::s.succs;
    if not (List.memq s n.preds) then
      n.preds <- s::n.preds
  in
  let addOptionSucc (n: stmt option) =
    match n with
      None -> ()
    | Some n' -> addSucc n'
  in
  let addBlockSucc (b: block) =
    match b.bstmts with
      [] -> addOptionSucc next
    | hd::_ -> addSucc hd
  in
  match s.skind with
    Instr _  -> addOptionSucc next
  | Return _  -> ()
  | Goto (p,_) -> addSucc !p
  | Break _ -> addOptionSucc break
  | Continue _ -> addOptionSucc cont
  | If (_, blk1, blk2, _) ->
      (* The succs of If is [true branch;false branch] *)
      addBlockSucc blk2;
      addBlockSucc blk1;
      cfgBlock blk1 next break cont;
      cfgBlock blk2 next break cont
  | Block b -> 
      addBlockSucc b;
      cfgBlock b next break cont
  | Switch(_,blk,l,_) -> 
      List.iter addSucc (List.rev l); (* Add successors in order *)
      (* sfg: if there's no default, need to connect s->next *)
      if not (List.exists 
                (fun stmt -> List.exists 
                   (function Default _ -> true | _ -> false)
                   stmt.labels) 
                l) 
      then 
        addOptionSucc next;
      cfgBlock blk next next cont
(*
  | Loop(blk,_,_,_) ->
*)
  | While(_,blk,_)
  | DoWhile(_,blk,_)
  | For(_,_,_,blk,_) ->
      addBlockSucc blk;
      cfgBlock blk (Some s) next (Some s)
      (* Since all loops have terminating condition true, we don't put
         any direct successor to stmt following the loop *)
  | TryExcept _ | TryFinally _ -> 
      E.s (E.unimp "try/except/finally")

(*------------------------------------------------------------*)

(**************************************************************)
(* do something for all stmts in a fundec *)

let rec forallStmts (todo) (fd : fundec) = 
  begin
    fasBlock todo fd.sbody;
  end

and fasBlock (todo) (b : block) =
  List.iter (fasStmt todo) b.bstmts

and fasStmt (todo) (s : stmt) =
  begin
    ignore(todo s);
    match s.skind with
      | Block b -> fasBlock todo b
      | If (_, tb, fb, _) -> (fasBlock todo tb; fasBlock todo fb)
      | Switch (_, b, _, _) -> fasBlock todo b
(*
      | Loop (b, _, _, _) -> fasBlock todo b
*)
      | While (_, b, _) -> fasBlock todo b
      | DoWhile (_, b, _) -> fasBlock todo b
      | For (_, _, _, b, _) -> fasBlock todo b
      | (Return _ | Break _ | Continue _ | Goto _ | Instr _) -> ()
      | TryExcept _ | TryFinally _ -> E.s (E.unimp "try/except/finally")
  end
;;

(**************************************************************)
(* printing the control flow graph - you have to compute it first *)

let d_cfgnodename () (s : stmt) =
  dprintf "%d" s.sid

let d_cfgnodelabel () (s : stmt) =
  let label = 
  begin
    match s.skind with
      | If (e, _, _, _)  -> "if" (*sprint ~width:999 (dprintf "if %a" d_exp e)*)
(*
      | Loop _ -> "loop"
*)
      | While _ -> "while"
      | DoWhile _ -> "dowhile"
      | For _ -> "for"
      | Break _ -> "break"
      | Continue _ -> "continue"
      | Goto _ -> "goto"
      | Instr _ -> "instr"
      | Switch _ -> "switch"
      | Block _ -> "block"
      | Return _ -> "return"
      | TryExcept _ -> "try-except"
      | TryFinally _ -> "try-finally"
  end in
    dprintf "%d: %s" s.sid label

let d_cfgedge (src) () (dest) =
  dprintf "%a -> %a"
    d_cfgnodename src
    d_cfgnodename dest

let d_cfgnode () (s : stmt) =
    dprintf "%a [label=\"%a\"]\n\t%a" 
    d_cfgnodename s
    d_cfgnodelabel s
    (d_list "\n\t" (d_cfgedge s)) s.succs

(**********************************************************************)
(* entry points *)

(** print control flow graph (in dot form) for fundec to channel *)
let printCfgChannel (chan : out_channel) (fd : fundec) =
  let pnode (s:stmt) = fprintf chan "%a\n" d_cfgnode s in
    begin
      ignore (fprintf chan "digraph CFG_%s {\n" fd.svar.vname);
      forallStmts pnode fd;
      ignore(fprintf chan  "}\n");
    end

(** Print control flow graph (in dot form) for fundec to file *)
let printCfgFilename (filename : string) (fd : fundec) =
  let chan = open_out filename in
    begin
      printCfgChannel chan fd;
      close_out chan;
    end


;;

(**********************************************************************)

let clearCFGinfo (fd : fundec) =
  let clear s =
    s.sid <- -1;
    s.succs <- [];
    s.preds <- [];
  in
  forallStmts clear fd

let clearFileCFG (f : file) =
  iterGlobals f (fun g ->
    match g with GFun(fd,_) ->
      clearCFGinfo fd
    | _ -> ())

let computeFileCFG (f : file) =
  iterGlobals f (fun g ->
    match g with GFun(fd,_) ->
      numNodes := cfgFun fd;
      start_id := !start_id + !numNodes
    | _ -> ())
