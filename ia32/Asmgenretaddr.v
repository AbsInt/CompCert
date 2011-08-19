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

(** Predictor for return addresses in generated IA32 code.

    The [return_address_offset] predicate defined here is used in the
    semantics for Mach (module [Machsem]) to determine the
    return addresses that are stored in activation records. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Errors.
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
  following the call in the Asm code obtained by translating the
  code of [f]. Graphically:
<<
     Mach function f    |--------- Mcall ---------|
         Mach code c    |                |--------|
                        |                 \        \
                        |                  \        \
                        |                   \        \
     Asm code           |                    |--------|
     Asm function       |------------- Pcall ---------|

                        <-------- ofs ------->
>>
*)

Inductive return_address_offset: Mach.function -> Mach.code -> int -> Prop :=
  | return_address_offset_intro:
      forall f c ofs,
      (forall tf tc,
       transf_function f = OK tf ->
       transl_code f c false = OK tc ->
       code_tail ofs tf tc) ->
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
  eauto with ppcretaddr;
  match goal with
  | [ |- is_tail _ (_ :: _) ] => constructor; IsTail
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: OK _ = OK _ |- _ ] => inv H; IsTail
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H; IsTail
  | [ H: (if ?x then _ else _) = OK _ |- _ ] => destruct x; IsTail
  | [ H: match ?x with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct x; IsTail
  | _ => idtac
  end.

Lemma mk_mov_tail:
  forall rd rs k c, mk_mov rd rs k = OK c -> is_tail k c.
Proof.
  unfold mk_mov; intros. destruct rd; IsTail; destruct rs; IsTail.
Qed.

Lemma mk_shift_tail:
  forall si r1 r2 k c, mk_shift si r1 r2 k = OK c -> is_tail k c.
Proof.
  unfold mk_shift; intros; IsTail.
Qed.

Lemma mk_mov2_tail:
  forall r1 r2 r3 r4 k, is_tail k (mk_mov2 r1 r2 r3 r4 k).
Proof.
  unfold mk_mov2; intros.
  destruct (ireg_eq r1 r2). IsTail.
  destruct (ireg_eq r3 r4). IsTail.
  destruct (ireg_eq r3 r2); IsTail.
  destruct (ireg_eq r1 r4); IsTail.
Qed.

Lemma mk_div_tail:
  forall di r1 r2 k c, mk_div di r1 r2 k = OK c -> is_tail k c.
Proof.
  unfold mk_div; intros; IsTail.
  eapply is_tail_trans. 2: eapply mk_mov2_tail. IsTail.
Qed.

Lemma mk_mod_tail:
  forall di r1 r2 k c, mk_mod di r1 r2 k = OK c -> is_tail k c.
Proof.
  unfold mk_mod; intros; IsTail.
  eapply is_tail_trans. 2: eapply mk_mov2_tail. IsTail.
Qed.

Lemma mk_shrximm_tail:
  forall r n k c, mk_shrximm r n k = OK c -> is_tail k c.
Proof.
  unfold mk_shrximm; intros; IsTail.
Qed.

Lemma mk_intconv_tail:
  forall mk rd rs k c, mk_intconv mk rd rs k = OK c -> is_tail k c.
Proof.
  unfold mk_intconv; intros; IsTail.
Qed.

Lemma mk_smallstore_tail:
  forall sto addr rs k c, mk_smallstore sto addr rs k = OK c -> is_tail k c.
Proof.
  unfold mk_smallstore; intros; IsTail.
Qed.

Lemma loadind_tail:
  forall base ofs ty dst k c, loadind base ofs ty dst k = OK c -> is_tail k c.
Proof.
  unfold loadind; intros. destruct ty; IsTail. destruct (preg_of dst); IsTail.
Qed.

Lemma storeind_tail:
  forall src base ofs ty k c, storeind src base ofs ty k = OK c -> is_tail k c.
Proof.
  unfold storeind; intros. destruct ty; IsTail. destruct (preg_of src); IsTail.
Qed.

Lemma mk_setcc_tail:
  forall cond rd k, is_tail k (mk_setcc cond rd k).
Proof.
  unfold mk_setcc; intros. destruct cond.
  IsTail.
  destruct (ireg_eq rd EDX); IsTail.
  destruct (ireg_eq rd EDX); IsTail.
Qed.

Lemma mk_jcc_tail:
  forall cond lbl k, is_tail k (mk_jcc cond lbl k).
Proof.
  unfold mk_jcc; intros. destruct cond; IsTail.
Qed.

Hint Resolve mk_mov_tail mk_shift_tail mk_div_tail mk_mod_tail mk_shrximm_tail
             mk_intconv_tail mk_smallstore_tail loadind_tail storeind_tail
             mk_setcc_tail mk_jcc_tail : ppcretaddr.

Lemma transl_cond_tail:
  forall cond args k c, transl_cond cond args k = OK c -> is_tail k c.
Proof.
  unfold transl_cond; intros. destruct cond; IsTail; destruct (Int.eq_dec i Int.zero); IsTail.
Qed.

Lemma transl_op_tail:
  forall op args res k c, transl_op op args res k = OK c -> is_tail k c.
Proof.
  unfold transl_op; intros. destruct op; IsTail. 
  eapply is_tail_trans. 2: eapply transl_cond_tail; eauto. IsTail.
Qed.

Lemma transl_load_tail:
  forall chunk addr args dest k c, transl_load chunk addr args dest k = OK c -> is_tail k c.
Proof.
  unfold transl_load; intros. IsTail. destruct chunk; IsTail. 
Qed.

Lemma transl_store_tail:
  forall chunk addr args src k c, transl_store chunk addr args src k = OK c -> is_tail k c.
Proof.
  unfold transl_store; intros. IsTail. destruct chunk; IsTail. 
Qed.

Lemma transl_instr_tail:
  forall f i ep k c, transl_instr f i ep k = OK c -> is_tail k c.
Proof.
  unfold transl_instr; intros. destruct i; IsTail.
  eapply is_tail_trans; eapply loadind_tail; eauto.
  eapply transl_op_tail; eauto.
  eapply transl_load_tail; eauto.
  eapply transl_store_tail; eauto.
  destruct s0; IsTail.
  destruct s0; IsTail.
  eapply is_tail_trans. 2: eapply transl_cond_tail; eauto. IsTail.
Qed.

Lemma transl_code_tail: 
  forall f c1 c2, is_tail c1 c2 ->
  forall tc2 ep2, transl_code f c2 ep2 = OK tc2 ->
  exists tc1, exists ep1, transl_code f c1 ep1 = OK tc1 /\ is_tail tc1 tc2.
Proof.
  induction 1; simpl; intros.
  exists tc2; exists ep2; split; auto with coqlib.
  monadInv H0. exploit IHis_tail; eauto. intros [tc1 [ep1 [A B]]].
  exists tc1; exists ep1; split. auto. 
  apply is_tail_trans with x. auto. eapply transl_instr_tail; eauto.
Qed.

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros.
  caseEq (transf_function f). intros tf TF.
  assert (exists tc1, transl_code f (fn_code f) true = OK tc1 /\ is_tail tc1 tf).
    monadInv TF.
    destruct (zlt (list_length_z x) Int.max_unsigned); monadInv EQ0.
    econstructor; eauto with coqlib.
  destruct H0 as [tc2 [A B]].
  exploit transl_code_tail; eauto. intros [tc1 [ep [C D]]].
Opaque transl_instr.
  monadInv C.
  assert (is_tail x tf).
    apply is_tail_trans with tc2; auto.
    apply is_tail_trans with tc1; auto.
    eapply transl_instr_tail; eauto.
  exploit is_tail_code_tail. eexact H0. intros [ofs C].
  exists (Int.repr ofs). constructor; intros. congruence. 
  intros. exists (Int.repr 0). constructor; intros; congruence.
Qed.

 
