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
   Main purpose: emit warnings for non-void functions that fall through,
   and for _Noreturn functions that can return. *)

open C
open Cutil

module StringSet = Set.Make(String)

(* Functions declared noreturn by the standard *)
let std_noreturn_functions =
   ["longjmp";"exit";"_exit";"abort";"_Exit";"quick_exit";"thrd_exit"]

(* Statements are abstracted as "flow transformers":
   functions from possible inputs to possible outcomes.
   Possible inputs are:
   - start normally at the beginning of the statement
   - start at a "case" or "default" label because of an enclosing switch
   - start at a named label because of a "goto"
   Possible outputs are:
   - terminate normally and fall through
   - terminate early on "break"
   - terminate early on "continue"
   - terminate early on "return"
   - terminate early on "goto" to a label
*)

type flow = inflow -> outflow

and inflow = {
  inormal: bool;           (* start normally at beginning of statement *)
  iswitch: bool;           (* start at any "case" or "default" label *)
  igoto: StringSet.t;      (* start at one of the goto labels in the set *)
}

and outflow = {
  onormal: bool;           (* terminates normally by falling through *)
  obreak: bool;            (* terminates early by "break" *)
  ocontinue: bool;         (* terminates early by "continue" *)
  oreturn: bool;           (* terminates early by "return" *)
  ogoto: StringSet.t       (* terminates early by "goto" *)
                           (* to one of the labels in the set *)
}

(* The l.u.b. of two out flows *)

let join o1 o2 =
  { onormal = o1.onormal || o2.onormal;
    obreak = o1.obreak || o2.obreak;
    ocontinue = o1.ocontinue || o2.ocontinue;
    oreturn = o1.oreturn || o2.oreturn;
    ogoto = StringSet.union o1.ogoto o2.ogoto }

(* Some elementary flows *)
  
let normal : flow = fun i ->
  { onormal = i.inormal;
    obreak = false; ocontinue = false; oreturn = false;
    ogoto = StringSet.empty }

let break : flow = fun i ->
  { obreak = i.inormal;
    onormal = false; ocontinue = false; oreturn = false;
    ogoto = StringSet.empty }

let continue : flow = fun i ->
  { ocontinue = i.inormal;
    onormal = false; obreak = false; oreturn = false;
    ogoto = StringSet.empty }

let return : flow = fun i ->
  { oreturn = i.inormal;
    onormal = false; obreak = false; ocontinue = false;
    ogoto = StringSet.empty }

let goto lbl : flow = fun i ->
  { onormal = false; obreak = false; ocontinue = false; oreturn = false;
    ogoto = if i.inormal then StringSet.singleton lbl else StringSet.empty }

let noflow : flow = fun i ->
  { onormal = false; obreak = false; ocontinue = false; oreturn = false;
    ogoto = StringSet.empty }
  
(* Some flow transformers *)

(* Sequential composition *)

let seq (s1: flow) (s2: flow) : flow = fun i ->
  let o1 = s1 i in
  let o2 = s2 {i with inormal = o1.onormal} in
  { onormal = o2.onormal;
    obreak = o1.obreak || o2.obreak;
    ocontinue = o1.ocontinue || o2.ocontinue;
    oreturn = o1.oreturn || o2.oreturn;
    ogoto = StringSet.union o1.ogoto o2.ogoto }

(* Nondeterministic choice *)
  
let either (s1: flow) (s2: flow) : flow = fun i ->
  join (s1 i) (s2 i)

(* If-then-else, with special cases for conditions that are always true
   or always false. *)

let resolve_test env e =
  match Ceval.integer_expr env e with
  | None -> None
  | Some n -> Some (n <> 0L)
  | exception Env.Error _ -> None (* Any error due to local types should be ignored *)

let if_ env e (s1: flow) (s2: flow) : flow =
  match resolve_test env e with
  | Some true -> s1
  | Some false -> s2
  | None -> either s1 s2

(* Convert "continue" into "fallthrough".  Typically applied to a loop body. *)

let catch_continue (s: flow) : flow = fun i ->
  let o = s i in
  { o with onormal = o.onormal || o.ocontinue; ocontinue = false}

(* Convert "break" into "fallthrough".  Typically applied to a loop. *)

let catch_break (s: flow) : flow = fun i ->
  let o = s i in
  { o with onormal = o.onormal || o.obreak; obreak = false}

(* Statements labeled with a goto label *)

let label lbl (s: flow) : flow = fun i ->
  s { i with inormal = i.inormal || StringSet.mem lbl i.igoto }

(* For "case" and "default" labeled statements, we assume they can be
   entered normally as soon as the nearest enclosing "switch" can be
   entered normally. *)
   
let case (s: flow) : flow = fun i ->
  s { i with inormal = i.inormal || i.iswitch }

let switch (s: flow) : flow = fun i ->
  s { i with inormal = false; iswitch = i.inormal }
  
(* This is the flow for an infinite loop with body [s].  
   There is no fallthrough exit, but all other exits from [s] are preserved. *)

let loop (s: flow) : flow = fun i ->
  let o = s i in
  if o.onormal && not i.inormal then
    (* Corner case: on the first iteration, [s] was not entered normally,
       but it exits by fallthrough.  Then on the next iteration [s] is
       entered normally.  So, we need to recompute the flow of [s]
       assuming it is entered normally. *)
     s { i with inormal = true}
   else
     (* In all other cases, iterating [s] once more does not produce new
        exits that we did not compute on the first iteration.  Just remove
        the fallthrough exit. *)
     { o with onormal = false }

(* Detect the presence of a 'default' case reachable from an enclosing
   'switch' *)

let rec contains_default s =
  match s.sdesc with
  | Sskip -> false
  | Sdo _ -> false
  | Sseq(s1, s2) -> contains_default s1 || contains_default s2
  | Sif(e, s1, s2) -> contains_default s1 || contains_default s2
  | Swhile(e, s) -> contains_default s
  | Sdowhile(s, e) -> contains_default s
  | Sfor(s1, e, s2, s3) ->
      contains_default s1 || contains_default s2 || contains_default s3
  | Sbreak -> false
  | Scontinue -> false
  | Sswitch(e, s) -> false
     (* the default that could appear inside the switch
        cannot be reached by the enclosing switch *)
  | Slabeled(Sdefault, s) -> true
  | Slabeled(_, s) -> contains_default s
  | Sgoto lbl -> false
  | Sreturn opte -> false
  | Sblock sl -> List.exists contains_default sl
  | Sdecl dcl -> false
  | Sasm _ -> false


(* This is the main analysis function.  Given a C statement [s] it returns
   a flow that overapproximates the behavior of [s]. *)

let rec outcomes env s : flow =
  match s.sdesc with
  | Sskip ->
      normal
  | Sdo {edesc = ECall(fn, args)} ->
    let returns = find_custom_attributes ["noreturn"; "__noreturn__"]
        (attributes_of_type env fn.etyp) = [] in
    let std_noreturn = List.exists (is_call_to_fun fn) std_noreturn_functions in
    if returns && not std_noreturn then normal else noflow
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
      let fl = catch_break (switch (outcomes env s)) in
      if contains_default s then fl else either normal fl
      (* if there is no 'default' case, the switch can fall through *)
  | Slabeled(Slabel lbl, s) ->
      label lbl (outcomes env s)
  | Slabeled((Scase _ | Sdefault), s) ->
      case (outcomes env s)
  | Sgoto lbl ->
      goto lbl
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
  (* Iterate [outcomes] until all gotos are accounted for *)
  let rec fixpoint i =
    let o = outcomes env body i in
    if StringSet.subset o.ogoto i.igoto
    then o
    else fixpoint { i with igoto = StringSet.union i.igoto o.ogoto } in
  let o =
    fixpoint { inormal = true; iswitch = false; igoto = StringSet.empty } in
  (* First boolean is: function can return
     Second boolean is: function can return by fall-through *)
  (o.onormal || o.oreturn, o.onormal)
