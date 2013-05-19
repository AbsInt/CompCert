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
  | Tint | Tfloat | Tsingle => true
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
      subtype ty (mreg_type r) && slot_valid sl ofs ty
  | Lsetstack r sl ofs ty =>
      slot_valid sl ofs ty && slot_writable sl
  | Lop op args res =>
      match is_move_operation op args with
      | Some arg =>
          subtype (mreg_type arg) (mreg_type res)
      | None => 
          let (targs, tres) := type_of_operation op in
          subtype tres (mreg_type res)
      end
  | Lload chunk addr args dst =>
      subtype (type_of_chunk chunk) (mreg_type dst)
  | Ltailcall sg ros =>
      zeq (size_arguments sg) 0
  | Lbuiltin ef args res =>
      subtype_list (proj_sig_res' (ef_sig ef)) (map mreg_type res) 
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

Lemma wt_setreg:
  forall ls r v,
  Val.has_type v (mreg_type r) -> wt_locset ls -> wt_locset (Locmap.set (R r) v ls).
Proof.
  intros; red; intros.
  unfold Locmap.set. 
  destruct (Loc.eq (R r) l).
  subst l; auto.
  destruct (Loc.diff_dec (R r) l). auto. red. auto.
Qed.

Lemma wt_setstack:
  forall ls sl ofs ty v,
  wt_locset ls -> wt_locset (Locmap.set (S sl ofs ty) v ls).
Proof.
  intros; red; intros.
  unfold Locmap.set. 
  destruct (Loc.eq (S sl ofs ty) l).
  subst l. simpl. 
  generalize (Val.load_result_type (chunk_of_type ty) v). 
  replace (type_of_chunk (chunk_of_type ty)) with ty. auto.
  destruct ty; reflexivity.
  destruct (Loc.diff_dec (S sl ofs ty) l). auto. red. auto.
Qed.

Lemma wt_undef_regs:
  forall rs ls, wt_locset ls -> wt_locset (undef_regs rs ls).
Proof.
  induction rs; simpl; intros. auto. apply wt_setreg; auto. red; auto.
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
- apply wt_setreg; auto.
- apply wt_setreg; auto.
- destruct v; simpl in H; try contradiction;
  simpl; apply wt_setreg; auto; apply wt_setreg; auto.
- apply wt_setreg; auto. apply Val.has_subtype with Tsingle; auto. 
- apply wt_setreg; auto.
Qed.

