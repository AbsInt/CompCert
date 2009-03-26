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

(** The whole compiler and its proof of semantic preservation *)

(** Libraries. *)
Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import AST.
Require Import Values.
Require Import Smallstep.
(** Languages (syntax and semantics). *)
Require Csyntax.
Require Csem.
Require Csharpminor.
Require Cminor.
Require CminorSel.
Require RTL.
Require LTL.
Require LTLin.
Require Linear.
Require Mach.
Require Asm.
(** Translation passes. *)
Require Cshmgen.
Require Cminorgen.
Require Selection.
Require RTLgen.
Require Tailcall.
Require Constprop.
Require CSE.
Require Allocation.
Require Tunneling.
Require Linearize.
Require Reload.
Require Stacking.
Require Asmgen.
(** Type systems. *)
Require Ctyping.
Require RTLtyping.
Require LTLtyping.
Require LTLintyping.
Require Lineartyping.
Require Machtyping.
(** Proofs of semantic preservation and typing preservation. *)
Require Cshmgenproof3.
Require Cminorgenproof.
Require Selectionproof.
Require RTLgenproof.
Require Tailcallproof.
Require Constpropproof.
Require CSEproof.
Require Allocproof.
Require Alloctyping.
Require Tunnelingproof.
Require Tunnelingtyping.
Require Linearizeproof.
Require Linearizetyping.
Require Reloadproof.
Require Reloadtyping.
Require Stackingproof.
Require Stackingtyping.
Require Machabstr2concr.
Require Asmgenproof.

Open Local Scope string_scope.

(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Set) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Set)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

(** We define three translation functions for whole programs: one
  starting with a C program, one with a Cminor program, one with an
  RTL program.  The three translations produce Asm programs ready for
  pretty-printing and assembling.

  There are two ways to compose the compiler passes.  The first
  translates every function from the Cminor program from Cminor to
  RTL, then to LTL, etc, all the way to Asm, and iterates this
  transformation for every function.  The second translates the whole
  Cminor program to a RTL program, then to an LTL program, etc. 
  Between Cminor and Asm, we follow the first approach because it has
  lower memory requirements.  The translation from Clight to Asm
  follows the second approach.
  
  The translation of an RTL function to an Asm function is as follows. *)

Definition transf_rtl_fundef (f: RTL.fundef) : res Asm.fundef :=
   OK f
   @@ Tailcall.transf_fundef
   @@ Constprop.transf_fundef
   @@ CSE.transf_fundef
  @@@ Allocation.transf_fundef
   @@ Tunneling.tunnel_fundef
  @@@ Linearize.transf_fundef
   @@ Reload.transf_fundef
  @@@ Stacking.transf_fundef
  @@@ Asmgen.transf_fundef.

(* Here is the translation of a Cminor function to an Asm function. *)

Definition transf_cminor_fundef (f: Cminor.fundef) : res Asm.fundef :=
  OK f
   @@ Selection.sel_fundef
  @@@ RTLgen.transl_fundef
  @@@ transf_rtl_fundef.

(** The corresponding translations for whole program follow. *)

Definition transf_rtl_program (p: RTL.program) : res Asm.program :=
  transform_partial_program transf_rtl_fundef p.

Definition transf_cminor_program (p: Cminor.program) : res Asm.program :=
  transform_partial_program transf_cminor_fundef p.

Definition transf_c_program (p: Csyntax.program) : res Asm.program :=
  match Ctyping.typecheck_program p with
  | false =>
      Error (msg "Ctyping: type error")
  | true =>
      OK p 
      @@@ Cshmgen.transl_program
      @@@ Cminorgen.transl_program
      @@@ transf_cminor_program
  end.

(** The following lemmas help reason over compositions of passes. *)

Lemma map_partial_compose:
  forall (X A B C: Set)
         (ctx: X -> errmsg)
         (f1: A -> res B) (f2: B -> res C)
         (pa: list (X * A)) (pc: list (X * C)),
  map_partial ctx (fun f => f1 f @@@ f2) pa = OK pc ->
  exists pb, map_partial ctx f1 pa = OK pb /\ map_partial ctx f2 pb = OK pc.
Proof.
  induction pa; simpl.
  intros. inv H. econstructor; eauto.
  intro pc. destruct a as [x a].
  caseEq (f1 a); simpl; try congruence. intros b F1.
  caseEq (f2 b); simpl; try congruence. intros c F2 EQ.
  monadInv EQ. exploit IHpa; eauto. intros [pb [P Q]]. 
  rewrite P; simpl.
  exists ((x, b) :: pb); split. auto. simpl. rewrite F2. rewrite Q. auto. 
Qed.

Lemma transform_partial_program_compose:
  forall (A B C V: Set)
         (f1: A -> res B) (f2: B -> res C)
         (pa: program A V) (pc: program C V),
  transform_partial_program (fun f => f1 f @@@ f2) pa = OK pc ->
  exists pb, transform_partial_program f1 pa = OK pb /\
             transform_partial_program f2 pb = OK pc.
Proof.
  intros. monadInv H. 
  exploit map_partial_compose; eauto. intros [xb [P Q]].
  exists (mkprogram xb (prog_main pa) (prog_vars pa)); split.
  unfold transform_partial_program. rewrite P; auto. 
  unfold transform_partial_program. simpl. rewrite Q; auto.
Qed.

Lemma transform_program_partial_program:
  forall (A B V: Set) (f: A -> B) (p: program A V) (tp: program B V),
  transform_partial_program (fun x => OK (f x)) p = OK tp ->
  transform_program f p = tp.
Proof.
  intros until tp. unfold transform_partial_program. 
  rewrite map_partial_total. simpl. intros. inv H. auto. 
Qed.

Lemma transform_program_compose:
  forall (A B C V: Set)
         (f1: A -> res B) (f2: B -> C)
         (pa: program A V) (pc: program C V),
  transform_partial_program (fun f => f1 f @@ f2) pa = OK pc ->
  exists pb, transform_partial_program f1 pa = OK pb /\
             transform_program f2 pb = pc.
Proof.
  intros. 
  replace (fun f : A => f1 f @@ f2)
     with (fun f : A => f1 f @@@ (fun x => OK (f2 x))) in H.
  exploit transform_partial_program_compose; eauto.
  intros [pb [X Y]]. exists pb; split. auto. 
  apply transform_program_partial_program. auto. 
  apply extensionality; intro. destruct(f1 x); auto. 
Qed.

Lemma transform_partial_program_identity:
  forall (A V: Set) (pa pb: program A V),
  transform_partial_program (@OK A) pa = OK pb ->
  pa = pb.
Proof.
  intros until pb. unfold transform_partial_program. 
  replace (@OK A) with (fun b => @OK A b).
  rewrite map_partial_identity. simpl. destruct pa; simpl; congruence.
  apply extensionality; auto. 
Qed.

(** * Semantic preservation *)

(** We prove that the [transf_program] translations preserve semantics.
  The proof composes the semantic preservation results for each pass.
  This establishes the correctness of the whole compiler! *)

Theorem transf_rtl_program_correct:
  forall p tp beh,
  transf_rtl_program p = OK tp ->
  RTL.exec_program p beh ->
  Asm.exec_program tp beh.
Proof.
  intros. unfold transf_rtl_program, transf_rtl_fundef in H.
  destruct (transform_partial_program_compose _ _ _ _ _ _ _ _ H) as [p7 [H7 P7]].
  clear H.
  destruct (transform_partial_program_compose _ _ _ _ _ _ _ _ H7) as [p6 [H6 P6]].
  clear H7.
  destruct (transform_partial_program_compose _ _ _ _ _ _ _ _ H6) as [p5 [H5 P5]].
  clear H6. generalize (transform_program_partial_program _ _ _ _ _ _ P5). clear P5. intro P5.
  destruct (transform_partial_program_compose _ _ _ _ _ _ _ _ H5) as [p4 [H4 P4]].
  clear H5.
  destruct (transform_partial_program_compose _ _ _ _ _ _ _ _ H4) as [p3 [H3 P3]].
  clear H4. generalize (transform_program_partial_program _ _ _ _ _ _ P3). clear P3. intro P3.
  destruct (transform_partial_program_compose _ _ _ _ _ _ _ _ H3) as [p2 [H2 P2]].
  clear H3.
  destruct (transform_program_compose _ _ _ _ _ _ _ _ H2) as [p1 [H1 P1]].
  clear H2.
  destruct (transform_program_compose _ _ _ _ _ _ _ _ H1) as [p0 [H00 P0]].
  clear H1.
  destruct (transform_program_compose _ _ _ _ _ _ _ _ H00) as [p00 [H000 P00]].
  clear H00.
  generalize (transform_partial_program_identity _ _ _ _ H000). clear H000. intro. subst p00.

  assert (WT3 : LTLtyping.wt_program p3).
    apply Alloctyping.program_typing_preserved with p2. auto.
  assert (WT4 : LTLtyping.wt_program p4).
    subst p4. apply Tunnelingtyping.program_typing_preserved. auto.
  assert (WT5 : LTLintyping.wt_program p5).
    apply Linearizetyping.program_typing_preserved with p4. auto. auto.
  assert (WT6 : Lineartyping.wt_program p6).
    subst p6. apply Reloadtyping.program_typing_preserved. auto.
  assert (WT7: Machtyping.wt_program p7).
    apply Stackingtyping.program_typing_preserved with p6. auto. auto.

  apply Asmgenproof.transf_program_correct with p7; auto.
  apply Machabstr2concr.exec_program_equiv; auto.
  apply Stackingproof.transf_program_correct with p6; auto.
  subst p6; apply Reloadproof.transf_program_correct; auto.
  apply Linearizeproof.transf_program_correct with p4; auto.
  subst p4; apply Tunnelingproof.transf_program_correct. 
  apply Allocproof.transf_program_correct with p2; auto.
  subst p2; apply CSEproof.transf_program_correct.
  subst p1; apply Constpropproof.transf_program_correct.
  subst p0; apply Tailcallproof.transf_program_correct.
  auto.
Qed.

Theorem transf_cminor_program_correct:
  forall p tp beh,
  transf_cminor_program p = OK tp ->
  Cminor.exec_program p beh ->
  Asm.exec_program tp beh.
Proof.
  intros. unfold transf_cminor_program, transf_cminor_fundef in H.
  destruct (transform_partial_program_compose _ _ _ _ _ _ _ _ H) as [p3 [H3 P3]].
  clear H.
  destruct (transform_partial_program_compose _ _ _ _ _ _ _ _ H3) as [p2 [H2 P2]].
  clear H3.
  destruct (transform_program_compose _ _ _ _ _ _ _ _ H2) as [p1 [H1 P1]].
  generalize (transform_partial_program_identity _ _ _ _ H1). clear H1. intro. subst p1.
  apply transf_rtl_program_correct with p3. auto.
  apply RTLgenproof.transf_program_correct with p2; auto.
  rewrite <- P1. apply Selectionproof.transf_program_correct; auto.
Qed.

Theorem transf_c_program_correct:
  forall p tp beh,
  transf_c_program p = OK tp ->
  Csem.exec_program p beh ->
  Asm.exec_program tp beh.
Proof.
  intros until beh; unfold transf_c_program; simpl.
  caseEq (Ctyping.typecheck_program p); try congruence; intro.
  caseEq (Cshmgen.transl_program p); simpl; try congruence; intros p1 EQ1.
  caseEq (Cminorgen.transl_program p1); simpl; try congruence; intros p2 EQ2. 
  intros EQ3 SEM.
  eapply transf_cminor_program_correct; eauto.
  eapply Cminorgenproof.transl_program_correct; eauto. 
  eapply Cshmgenproof3.transl_program_correct; eauto.
  apply Ctyping.typecheck_program_correct; auto.
Qed.
