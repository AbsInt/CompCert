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

(** Predictor for return addresses in generated PPC code.

    The [return_address_offset] predicate defined here is used in the
    concrete semantics for Mach (module [Machconcr]) to determine the
    return addresses that are stored in activation records. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Asm.
Require Import Asmgen.

(** The ``code tail'' of an instruction list [c] is the list of instructions
  starting at PC [pos]. *)

Inductive code_tail: Z -> code -> code -> Prop :=
  | code_tail_0: forall c,
      code_tail 0 c c
  | code_tail_S: forall pos i c1 c2,
      code_tail pos c1 c2 ->
      code_tail (pos + 1) (i :: c1) c2.

Lemma code_tail_pos:
  forall pos c1 c2, code_tail pos c1 c2 -> pos >= 0.
Proof.
  induction 1. omega. omega.
Qed.

(** Consider a Mach function [f] and a sequence [c] of Mach instructions
  representing the Mach code that remains to be executed after a
  function call returns.  The predicate [return_address_offset f c ofs]
  holds if [ofs] is the integer offset of the PPC instruction
  following the call in the PPC code obtained by translating the
  code of [f]. Graphically:
<<
     Mach function f    |--------- Mcall ---------|
         Mach code c    |                |--------|
                        |                 \        \
                        |                  \        \
                        |                   \        \
     PPC code           |                    |--------|
     PPC function       |--------------- Pbl ---------|

                        <-------- ofs ------->
>>
*)

Inductive return_address_offset: Mach.function -> Mach.code -> int -> Prop :=
  | return_address_offset_intro:
      forall c f ofs,
      code_tail ofs (transl_function f) (transl_code f c) ->
      return_address_offset f c (Int.repr ofs).

(** We now show that such an offset always exists if the Mach code [c]
  is a suffix of [f.(fn_code)].  This holds because the translation
  from Mach to PPC is compositional: each Mach instruction becomes
  zero, one or several PPC instructions, but the order of instructions
  is preserved. *)

Lemma is_tail_code_tail:
  forall c1 c2, is_tail c1 c2 -> exists ofs, code_tail ofs c2 c1.
Proof.
  induction 1. exists 0; constructor.
  destruct IHis_tail as [ofs CT]. exists (ofs + 1); constructor; auto.
Qed.

Hint Resolve is_tail_refl: ppcretaddr.

Ltac IsTail :=
  auto with ppcretaddr;
  match goal with
  | [ |- is_tail _ (_ :: _) ] => constructor; IsTail
  | [ |- is_tail _ (match ?x with true => _ | false => _ end) ] => destruct x; IsTail
  | [ |- is_tail _ (match ?x with left _ => _ | right _ => _ end) ] => destruct x; IsTail
  | [ |- is_tail _ (match ?x with nil => _ | _ :: _ => _ end) ] => destruct x; IsTail
  | [ |- is_tail _ (match ?x with Tint => _ | Tfloat => _ end) ] => destruct x; IsTail
  | [ |- is_tail _ (?f _ _ _ _ _ _ ?k) ] => apply is_tail_trans with k; IsTail
  | [ |- is_tail _ (?f _ _ _ _ _ ?k) ] => apply is_tail_trans with k; IsTail
  | [ |- is_tail _ (?f _ _ _ _ ?k) ] => apply is_tail_trans with k; IsTail
  | [ |- is_tail _ (?f _ _ _ ?k) ] => apply is_tail_trans with k; IsTail
  | [ |- is_tail _ (?f _ _ ?k) ] => apply is_tail_trans with k; IsTail
  | _ => idtac
  end.

Lemma loadimm_tail:
  forall r n k, is_tail k (loadimm r n k).
Proof. unfold loadimm; intros; IsTail. Qed.
Hint Resolve loadimm_tail: ppcretaddr.

Lemma addimm_tail:
  forall r1 r2 n k, is_tail k (addimm r1 r2 n k).
Proof. unfold addimm; intros; IsTail. Qed.
Hint Resolve addimm_tail: ppcretaddr.

Lemma andimm_tail:
  forall r1 r2 n k, is_tail k (andimm r1 r2 n k).
Proof. unfold andimm; intros; IsTail. Qed.
Hint Resolve andimm_tail: ppcretaddr.

Lemma makeimm_tail:
  forall f r1 r2 n k, is_tail k (makeimm f r1 r2 n k).
Proof. unfold makeimm; intros; IsTail. Qed.
Hint Resolve makeimm_tail: ppcretaddr.

Lemma transl_cond_tail:
  forall cond args k, is_tail k (transl_cond cond args k).
Proof. unfold transl_cond; intros; destruct cond; IsTail. Qed.
Hint Resolve transl_cond_tail: ppcretaddr.

Lemma transl_op_tail:
  forall op args r k, is_tail k (transl_op op args r k).
Proof. unfold transl_op; intros; destruct op; IsTail. Qed.
Hint Resolve transl_op_tail: ppcretaddr.

Lemma transl_load_store_tail:
  forall mk1 mk2 is_immed addr args k,
  is_tail k (transl_load_store mk1 mk2 is_immed addr args k).
Proof. unfold transl_load_store; intros; destruct addr; IsTail.
       destruct mk2; IsTail. destruct mk2; IsTail. Qed.
Hint Resolve transl_load_store_tail: ppcretaddr.

Lemma transl_load_store_int_tail:
  forall mk is_immed rd addr args k,
  is_tail k (transl_load_store_int mk is_immed rd addr args k).
Proof. unfold transl_load_store_int; intros; IsTail. Qed.
Hint Resolve transl_load_store_int_tail: ppcretaddr.

Lemma transl_load_store_float_tail:
  forall mk is_immed rd addr args k,
  is_tail k (transl_load_store_float mk is_immed rd addr args k).
Proof. unfold transl_load_store_float; intros; IsTail. Qed.
Hint Resolve transl_load_store_float_tail: ppcretaddr.

Lemma loadind_int_tail:
  forall base ofs dst k, is_tail k (loadind_int base ofs dst k).
Proof. unfold loadind_int; intros; IsTail. Qed.
Hint Resolve loadind_int_tail: ppcretaddr.

Lemma loadind_tail:
  forall base ofs ty dst k, is_tail k (loadind base ofs ty dst k).
Proof. unfold loadind, loadind_float; intros; IsTail. Qed.
Hint Resolve loadind_tail: ppcretaddr.

Lemma storeind_int_tail:
  forall src base ofs k, is_tail k (storeind_int src base ofs k).
Proof. unfold storeind_int; intros; IsTail. Qed.
Hint Resolve storeind_int_tail: ppcretaddr.

Lemma storeind_tail:
  forall src base ofs ty k, is_tail k (storeind src base ofs ty k).
Proof. unfold storeind, storeind_float; intros; IsTail. Qed.
Hint Resolve storeind_tail: ppcretaddr.

Lemma transl_instr_tail:
  forall f i k, is_tail k (transl_instr f i k).
Proof.
  unfold transl_instr; intros; destruct i; IsTail.
  destruct m; IsTail.
  destruct m; IsTail.
  destruct s0; IsTail.
  destruct s0; IsTail.
Qed.
Hint Resolve transl_instr_tail: ppcretaddr.

Lemma transl_code_tail: 
  forall f c1 c2, is_tail c1 c2 -> is_tail (transl_code f c1) (transl_code f c2).
Proof.
  induction 1; simpl. constructor. eapply is_tail_trans; eauto with ppcretaddr.
Qed.

Lemma return_address_exists:
  forall f c, is_tail c f.(fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. assert (is_tail (transl_code f c) (transl_function f)).
  unfold transl_function. IsTail. apply transl_code_tail; auto.
  destruct (is_tail_code_tail _ _ H0) as [ofs A].
  exists (Int.repr ofs). constructor. auto.
Qed.

 
