(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Elimination of unreferenced static definitions *)

Require Import FSets.
Require Import Coqlib.
Require Import Ordered.
Require Import Maps.
Require Import Iteration.
Require Import AST.
Require Import Errors.
Require Import Op.
Require Import Registers.
Require Import RTL.

Local Open Scope string_scope.

(** * Determination of global identifiers that are referenced *)

(** The working set *)

Module IS := FSetAVL.Make(OrderedPositive).

Record workset := mk_workset {
  w_seen :> IS.t;
  w_todo: list ident
}.

Definition add_workset (id: ident) (w: workset) : workset :=
  if IS.mem id w.(w_seen)
  then w
  else {| w_seen := IS.add id w.(w_seen); w_todo := id :: w.(w_todo) |}.

Fixpoint addlist_workset (l: list ident) (w: workset) : workset :=
  match l with
  | nil => w
  | id :: l' => addlist_workset l' (add_workset id w)
  end.

(** Global symbols referenced in a function or variable definition *)

Definition ref_instruction (i: instruction) : list ident :=
  match i with
  | Inop _ => nil
  | Iop op _ _ _ => globals_operation op
  | Iload _ addr _ _ _ => globals_addressing addr
  | Istore _ addr _ _ _ => globals_addressing addr
  | Icall _ (inl r) _ _ _ => nil
  | Icall _ (inr id) _ _ _ => id :: nil
  | Itailcall _ (inl r) _ => nil
  | Itailcall _ (inr id) _ => id :: nil
  | Ibuiltin _ args _ _ => globals_of_builtin_args args
  | Icond cond _ _ _ => nil
  | Ijumptable _ _ => nil
  | Ireturn _ => nil
  end.

Definition add_ref_instruction (w: workset) (pc: node) (i: instruction) : workset :=
  addlist_workset (ref_instruction i) w.

Definition add_ref_function (f: function) (w: workset): workset :=
  PTree.fold add_ref_instruction f.(fn_code) w.

Definition add_ref_init_data (w: workset) (i: init_data) : workset :=
  match i with
  | Init_addrof id _ => add_workset id w
  | _ => w
  end.

Definition add_ref_globvar (gv: globvar unit) (w: workset): workset :=
  List.fold_left add_ref_init_data gv.(gvar_init) w.

Definition prog_map : Type := PTree.t (globdef fundef unit).

Definition add_ref_definition (pm: prog_map) (id: ident) (w: workset): workset :=
  match pm!id with
  | None => w
  | Some (Gfun (Internal f)) => add_ref_function f w
  | Some (Gfun (External ef)) => w
  | Some (Gvar gv) => add_ref_globvar gv w
  end.

(** Traversal of the dependency graph. *)

Definition iter_step (pm: prog_map) (w: workset) : IS.t + workset :=
  match w.(w_todo) with
  | nil =>
      inl _ w.(w_seen)
  | id :: rem =>
      inr _ (add_ref_definition pm id {| w_seen := w.(w_seen); w_todo := rem |})
  end.

Definition initial_workset (p: program): workset :=
  add_workset p.(prog_main)
    (List.fold_left (fun w id => add_workset id w)
                    p.(prog_public)
                    {| w_seen := IS.empty; w_todo := nil |}).

Definition add_def_prog_map (pm: prog_map) (id_df: ident * globdef fundef unit) : prog_map :=
  PTree.set (fst id_df) (snd id_df) pm.

Definition program_map (p: program) : prog_map :=
  List.fold_left add_def_prog_map p.(prog_defs) (PTree.empty _).

Definition used_globals (p: program) : option IS.t :=
  let pm := program_map p in
  PrimIter.iterate _ _ (iter_step pm) (initial_workset p).

(** * Elimination of unreferenced global definitions *)

(** We also eliminate multiple definitions of the same global name, keeping ony
  the last definition (in program definition order). *)

Fixpoint filter_globdefs (used: IS.t) (accu defs: list (ident * globdef fundef unit)) :=
  match defs with
  | nil => accu
  | (id, gd) :: defs' =>
      if IS.mem id used
      then filter_globdefs (IS.remove id used) ((id, gd) :: accu) defs'
      else filter_globdefs used accu defs'
  end.

Definition transform_program (p: program) : res program :=
  match used_globals p with
  | None => Error (msg "Unusedglob: analysis failed")
  | Some used =>
      OK {| prog_defs := filter_globdefs used nil (List.rev p.(prog_defs));
            prog_public := p.(prog_public);
            prog_main := p.(prog_main) |}
  end.

