(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* A simple control flow analysis for C statements.
   Main purpose: emit warnings for _Noreturn functions. *)

open C
open Cutil

(* Statements are abstracted as "flow transformers":
   functions from possible inputs to possible outcomes.
   Possible inputs are:
   - start normally at the beginning of the statement
   - start at a "case" or "default" label because of an enclosing switch
   Possible outputs are:
   - terminate normally and fall through
   - terminate early on "break"
   - terminate early on "continue"
   - terminate early on "return"
*)

type flow = bool -> (* start normally at beginning of statement *)
            bool -> (* start at "case"/"default" label *)
            int
(* Outputs are encoded as bit masks in an integer *)

let _None = 0
let _Fallthrough = 1
let _Break = 2
let _Continue = 4
let _Return = 8
let can flag out = out land flag <> 0
let add flag out = out lor flag
let remove flag out = out land (lnot flag)
let join out1 out2 = out1 lor out2

(* Some elementary flows *)
  
let normal   : flow = fun i is -> if i then _Fallthrough else _None
let break    : flow = fun i is -> if i then _Break else _None
let continue : flow = fun i is -> if i then _Continue else _None
let return   : flow = fun i is -> if i then _Return else _None
let noflow   : flow = fun i is -> _None
  
(* Some flow transformers *)

(* Sequential composition *)

let seq (s1: flow) (s2: flow) : flow = fun i is ->
  let o1 = s1 i is in
  let o2 = s2 (can _Fallthrough o1) is in
  join (remove _Fallthrough o1) o2

(* Nondeterministic choice *)
  
let either (s1: flow) (s2: flow) : flow = fun i is ->
  join (s1 i is) (s2 i is)

(* If-then-else, with special cases for conditions that are always true
   or always false. *)

let resolve_test env e =
  match Ceval.integer_expr env e with
  | None -> None
  | Some n -> Some (n <> 0L)

let if_ env e (s1: flow) (s2: flow) : flow =
  match resolve_test env e with
  | Some true -> s1
  | Some false -> s2
  | None -> either s1 s2

(* Convert "continue" into "fallthrough".  Typically applied to a loop body. *)

let catch_continue (s: flow) : flow = fun i is ->
  let o = s i is in
  if can _Continue o then add _Fallthrough (remove _Continue o) else o

(* Convert "continue" into "fallthrough".  Typically applied to a loop. *)

let catch_break (s: flow) : flow = fun i is ->
  let o = s i is in
  if can _Break o then add _Fallthrough (remove _Break o) else o

(* For goto-labeled statements we assume they can always be entered normally. *)

let label (s: flow) : flow = fun i is -> s true is

(* For "case" and "default" labeled statements, we assume they can be entered
   normally as soon as the nearest enclosing "switch" can be entered normally. *)
   
let case (s: flow) : flow = fun i is -> s is is

let switch (s: flow) : flow = fun i is -> s false i

(* This is the flow for an infinite loop with body [s].  
   There is no fallthrough exit, but all other exits from [s] are preserved. *)

let loop (s: flow) : flow = fun i is ->
  let o = s i is in
  if (not i) && can _Fallthrough o then
    (* Corner case: on the first iteration, [s] was not entered normally,
       but it exits by fallthrough.  Then on the next iteration [s] is
       entered normally.  So, we need to recompute the flow of [s]
       assuming it is entered normally. *)
     s true is
   else
     (* In all other cases, iterating [s] once more does not produce new
        exits that we did not compute on the first iteration.  Just remove
        the fallthrough exit. *)
     remove _Fallthrough o

(* This is the main analysis function.  Given a C statement [s] it returns
   a flow that overapproximates the behavior of [s]. *)

let rec outcomes env s : flow =
  match s.sdesc with
  | Sskip ->
      normal
  | Sdo {edesc = ECall(fn, args)} ->
      if find_custom_attributes ["noreturn"; "__noreturn__"]
                                (attributes_of_type env fn.etyp) = []
      then normal else noflow
  | Sdo e ->
      normal
  | Sseq(s1, s2) ->
      seq (outcomes env s1) (outcomes env s2)
  | Sif(e, s1, s2) ->
      if_ env e (outcomes env s1) (outcomes env s2)
  | Swhile(e, s) ->
      catch_break (
        loop (
          if_ env e
             (catch_continue (outcomes env s)) (* e is true: execute body [s] *)
             break))                           (* e is false: exit loop *)
  | Sdowhile(s, e) ->
      catch_break (
        loop (
          seq (catch_continue (outcomes env s)) (* do the body *)
              (if_ env e normal break)))        (* then continue or break *)
  | Sfor(s1, e, s2, s3) ->
      seq (outcomes env s1)              (* initialization, runs once *)
          (catch_break (
            loop (
              if_ env e                  (* e is true: do body, do next *)
                (seq (catch_continue (outcomes env s2)) (outcomes env s3))
                break)))                 (* e is false: exit loop *)
  | Sbreak ->
      break
  | Scontinue ->
      continue
  | Sswitch(e, s) ->
      catch_break (switch (outcomes env s))
  | Slabeled(Slabel _, s) ->
      label (outcomes env s)
  | Slabeled((Scase _ | Sdefault), s) ->
      case (outcomes env s)
  | Sgoto _ ->
      noflow
  | Sreturn opte ->
      return
  | Sblock sl ->
      outcomes_block env sl
  | Sdecl dcl ->
      normal
  | Sasm _ ->
      normal

and outcomes_block env sl =
  match sl with
  | [] ->
      normal
  | s1 :: sl ->
      seq (outcomes env s1) (outcomes_block env sl)

(* This is the entry point in this module.  Given the body of a function,
   estimate if and how this function can return. *)

let function_returns env body =
  let o = outcomes env body true false in
  (* First boolean is: function can return
     Second boolean is: function can return by fall-through *)
  (can _Fallthrough o || can _Return o, can _Fallthrough o)
