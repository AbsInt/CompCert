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

(** Typing rules for Linear. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Import LTL.
Require Import Linear.

(** The typing rules for Linear enforce several properties useful for
  the proof of the [Stacking] pass:
- for each instruction, the type of the result register or slot
  agrees with the type of values produced by the instruction;
- correctness conditions on the offsets of stack slots
  accessed through [Lgetstack] and [Lsetstack] Linear instructions.
*)

(** The rules are presented as boolean-valued functions so that we
  get an executable type-checker for free. *)

Section WT_INSTR.

Variable funct: function.

Definition slot_valid (sl: slot) (ofs: Z) (ty: typ): bool :=
  match sl with
  | Local => zle 0 ofs
  | Outgoing => zle 0 ofs
  | Incoming => In_dec Loc.eq (S Incoming ofs ty) (loc_parameters funct.(fn_sig))
  end &&
  match ty with
  | Tint | Tfloat => true
  | Tlong => false
  end.

Definition slot_writable (sl: slot) : bool :=
  match sl with
  | Local => true
  | Outgoing => true
  | Incoming => false
  end.

Definition loc_valid (l: loc) : bool :=
  match l with
  | R r => true
  | S Local ofs ty => slot_valid Local ofs ty
  | S _ _ _ => false
  end.

Definition wt_instr (i: instruction) : bool :=
  match i with
  | Lgetstack sl ofs ty r =>
      typ_eq ty (mreg_type r) && slot_valid sl ofs ty
  | Lsetstack r sl ofs ty =>
      typ_eq ty (mreg_type r) && slot_valid sl ofs ty && slot_writable sl
  | Lop op args res =>
      match is_move_operation op args with
      | Some arg =>
          typ_eq (mreg_type arg) (mreg_type res)
      | None => 
          let (targs, tres) := type_of_operation op in
          typ_eq (mreg_type res) tres
      end
  | Lload chunk addr args dst =>
      typ_eq (mreg_type dst) (type_of_chunk chunk)
  | Ltailcall sg ros =>
      zeq (size_arguments sg) 0
  | Lbuiltin ef args res =>
      list_typ_eq (map mreg_type res) (proj_sig_res' (ef_sig ef))
  | Lannot ef args =>
      forallb loc_valid args
  | _ =>
      true
  end.

End WT_INSTR.

Definition wt_code (f: function) (c: code) : bool :=
  forallb (wt_instr f) c.

Definition wt_function (f: function) : bool :=
  wt_code f f.(fn_code).

(** Typing the run-time state.  These definitions are used in [Stackingproof]. *)

Require Import Values.

Definition wt_locset (ls: locset) : Prop :=
  forall l, Val.has_type (ls l) (Loc.type l).

Lemma wt_setloc:
  forall ls l v,
  Val.has_type v (Loc.type l) -> wt_locset ls -> wt_locset (Locmap.set l v ls).
Proof.
  intros; red; intros.
  unfold Locmap.set. 
  destruct (Loc.eq l l0). congruence.
  destruct (Loc.diff_dec l l0). auto. red. auto.
Qed.

Lemma wt_setlocs:
  forall ll vl ls,
  Val.has_type_list vl (map Loc.type ll) -> wt_locset ls -> wt_locset (Locmap.setlist ll vl ls).
Proof.
  induction ll; destruct vl; simpl; intuition. 
  apply IHll; auto. apply wt_setloc; auto.
Qed.

Lemma wt_undef_regs:
  forall rs ls, wt_locset ls -> wt_locset (undef_regs rs ls).
Proof.
  induction rs; simpl; intros. auto. apply wt_setloc; auto. red; auto.
Qed.

Lemma wt_call_regs:
  forall ls, wt_locset ls -> wt_locset (call_regs ls).
Proof.
  intros; red; intros. unfold call_regs. destruct l. auto.
  destruct sl.
  red; auto.
  change (Loc.type (S Incoming pos ty)) with (Loc.type (S Outgoing pos ty)). auto.
  red; auto.
Qed.

Lemma wt_return_regs:
  forall caller callee,
  wt_locset caller -> wt_locset callee -> wt_locset (return_regs caller callee).
Proof.
  intros; red; intros.
  unfold return_regs. destruct l; auto.
  destruct (in_dec mreg_eq r destroyed_at_call); auto.
Qed.

Lemma wt_init:
  wt_locset (Locmap.init Vundef).
Proof.
  red; intros. unfold Locmap.init. red; auto.
Qed.

Lemma wt_setlist_result:
  forall sg v rs,
  Val.has_type v (proj_sig_res sg) ->
  wt_locset rs ->
  wt_locset (Locmap.setlist (map R (loc_result sg)) (encode_long (sig_res sg) v) rs).
Proof.
  unfold loc_result, encode_long, proj_sig_res; intros.
  destruct (sig_res sg) as [[] | ]; simpl.
  apply wt_setloc; auto.
  apply wt_setloc; auto.
  destruct v; simpl in H; try contradiction;
  simpl; apply wt_setloc; auto; apply wt_setloc; auto.
  apply wt_setloc; auto.
Qed.

