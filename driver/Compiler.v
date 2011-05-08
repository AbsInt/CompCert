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
Require Import Axioms.
Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import AST.
Require Import Values.
Require Import Smallstep.
(** Languages (syntax and semantics). *)
Require Csyntax.
Require Csem.
Require Cstrategy.
Require Clight.
Require Csharpminor.
Require Cminor.
Require CminorSel.
Require RTL.
Require LTL.
Require LTLin.
Require Linear.
Require Mach.
Require Machsem.
Require Asm.
(** Translation passes. *)
Require Initializers.
Require SimplExpr.
Require Cshmgen.
Require Cminorgen.
Require Selection.
Require RTLgen.
Require Tailcall.
Require CastOptim.
Require Constprop.
Require CSE.
Require Allocation.
Require Tunneling.
Require Linearize.
Require CleanupLabels.
Require Reload.
Require Stacking.
Require Asmgen.
(** Type systems. *)
Require RTLtyping.
Require LTLtyping.
Require LTLintyping.
Require Lineartyping.
Require Machtyping.
(** Proofs of semantic preservation and typing preservation. *)
Require SimplExprproof.
Require Cshmgenproof.
Require Cminorgenproof.
Require Selectionproof.
Require RTLgenproof.
Require Tailcallproof.
Require CastOptimproof.
Require Constpropproof.
Require CSEproof.
Require Allocproof.
Require Alloctyping.
Require Tunnelingproof.
Require Tunnelingtyping.
Require Linearizeproof.
Require Linearizetyping.
Require CleanupLabelsproof.
Require CleanupLabelstyping.
Require Reloadproof.
Require Reloadtyping.
Require Stackingproof.
Require Stackingtyping.
Require Asmgenproof.
(** Pretty-printers (defined in Caml). *)
Parameter print_Csyntax: Csyntax.program -> unit.
Parameter print_Clight: Clight.program -> unit.
Parameter print_Cminor: Cminor.program -> unit.
Parameter print_RTL: RTL.fundef -> unit.
Parameter print_RTL_tailcall: RTL.fundef -> unit.
Parameter print_RTL_castopt: RTL.fundef -> unit.
Parameter print_RTL_constprop: RTL.fundef -> unit.
Parameter print_RTL_cse: RTL.fundef -> unit.
Parameter print_LTLin: LTLin.fundef -> unit.

Open Local Scope string_scope.

(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  match printer prog with tt => prog end.

(** We define three translation functions for whole programs: one
  starting with a C program, one with a Cminor program, one with an
  RTL program.  The three translations produce Asm programs ready for
  pretty-printing and assembling.

  There are two ways to compose the compiler passes.  The first
  translates every function from the Cminor program from Cminor to
  RTL, then to LTL, etc, all the way to Asm, and iterates this
  transformation for every function.  The second translates the whole
  Cminor program to a RTL program, then to an LTL program, etc. 
  Between CminorSel and Asm, we follow the first approach because it has
  lower memory requirements.  The translation from Clight to Asm
  follows the second approach.
  
  The translation of an RTL function to an Asm function is as follows. *)

Definition transf_rtl_fundef (f: RTL.fundef) : res Asm.fundef :=
   OK f
   @@ print print_RTL
   @@ Tailcall.transf_fundef
   @@ print print_RTL_tailcall
   @@ CastOptim.transf_fundef
   @@ print print_RTL_castopt
   @@ Constprop.transf_fundef
   @@ print print_RTL_constprop
   @@ CSE.transf_fundef
   @@ print print_RTL_cse
  @@@ Allocation.transf_fundef
   @@ Tunneling.tunnel_fundef
  @@@ Linearize.transf_fundef
   @@ CleanupLabels.transf_fundef
   @@ print print_LTLin
   @@ Reload.transf_fundef
  @@@ Stacking.transf_fundef
  @@@ Asmgen.transf_fundef.

(* Here is the translation of a CminorSel function to an Asm function. *)

Definition transf_cminorsel_fundef (f: CminorSel.fundef) : res Asm.fundef :=
  OK f
  @@@ RTLgen.transl_fundef
  @@@ transf_rtl_fundef.

(** The corresponding translations for whole program follow. *)

Definition transf_rtl_program (p: RTL.program) : res Asm.program :=
  transform_partial_program transf_rtl_fundef p.

Definition transf_cminor_program (p: Cminor.program) : res Asm.program :=
   OK p
   @@ print print_Cminor
   @@ Selection.sel_program
  @@@ transform_partial_program transf_cminorsel_fundef.

Definition transf_c_program (p: Csyntax.program) : res Asm.program :=
  OK p 
   @@ print print_Csyntax
  @@@ SimplExpr.transl_program
   @@ print print_Clight
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program
  @@@ transf_cminor_program.

(** Force [Initializers] to be extracted as well. *)

Definition transl_init := Initializers.transl_init.

(** The following lemmas help reason over compositions of passes. *)

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. destruct (printer prog); auto. 
Qed.

Lemma map_partial_compose:
  forall (X A B C: Type)
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
  forall (A B C V: Type)
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
  forall (A B V: Type) (f: A -> B) (p: program A V) (tp: program B V),
  transform_partial_program (fun x => OK (f x)) p = OK tp ->
  transform_program f p = tp.
Proof.
  intros until tp. unfold transform_partial_program. 
  rewrite map_partial_total. simpl. intros. inv H. auto. 
Qed.

Lemma transform_program_compose:
  forall (A B C V: Type)
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
  forall (A V: Type) (pa pb: program A V),
  transform_partial_program (@OK A) pa = OK pb ->
  pa = pb.
Proof.
  intros until pb. unfold transform_partial_program. 
  replace (@OK A) with (fun b => @OK A b).
  rewrite map_partial_identity. simpl. destruct pa; simpl; congruence.
  apply extensionality; auto. 
Qed.

Lemma transform_program_print_identity:
  forall (A V: Type) (p: program A V) (f: A -> unit),
  transform_program (print f) p = p.
Proof.
  intros until f. unfold transform_program, transf_program. 
  destruct p; simpl; f_equal. 
  transitivity (map (fun x => x) prog_funct). 
  apply list_map_exten; intros. destruct x; simpl. rewrite print_identity. auto.
  apply list_map_identity.
Qed.

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit), 
  x @@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto. 
Qed.

(** * Semantic preservation *)

(** We prove that the [transf_program] translations preserve semantics.
  The proof composes the semantic preservation results for each pass.
  This establishes the correctness of the whole compiler! *)

Ltac TransfProgInv :=
  match goal with
  | [ H: transform_partial_program (fun f => _ @@@ _) _ = OK _ |- _ ] =>
      let p := fresh "p" in let X := fresh "X" in let P := fresh "P" in
      destruct (transform_partial_program_compose _ _ _ _ _ _ _ _ H) as [p [X P]];
      clear H
  | [ H: transform_partial_program (fun f => _ @@ _) _ = OK _ |- _ ] =>
      let p := fresh "p" in let X := fresh "X" in let P := fresh "P" in
      destruct (transform_program_compose _ _ _ _ _ _ _ _ H) as [p [X P]];
      clear H
  end.

Theorem transf_rtl_program_correct:
  forall p tp beh,
  transf_rtl_program p = OK tp ->
  not_wrong beh ->
  RTL.exec_program p beh ->
  Asm.exec_program tp beh.
Proof.
  intros. unfold transf_rtl_program, transf_rtl_fundef in H.
  repeat TransfProgInv. 
  repeat rewrite transform_program_print_identity in *. subst. 
  exploit transform_partial_program_identity; eauto. intro EQ. subst.

  generalize Alloctyping.program_typing_preserved
             Tunnelingtyping.program_typing_preserved
             Linearizetyping.program_typing_preserved
             CleanupLabelstyping.program_typing_preserved
             Reloadtyping.program_typing_preserved
             Stackingtyping.program_typing_preserved; intros.

  eapply Asmgenproof.transf_program_correct; eauto 6.
  eapply Stackingproof.transf_program_correct; eauto 6.
  eapply Reloadproof.transf_program_correct; eauto.
  eapply CleanupLabelsproof.transf_program_correct; eauto.
  eapply Linearizeproof.transf_program_correct; eauto.
  eapply Tunnelingproof.transf_program_correct; eauto.
  eapply Allocproof.transf_program_correct; eauto.
  eapply CSEproof.transf_program_correct; eauto.
  eapply Constpropproof.transf_program_correct; eauto.
  eapply CastOptimproof.transf_program_correct; eauto.
  eapply Tailcallproof.transf_program_correct; eauto.
Qed.

Theorem transf_cminor_program_correct:
  forall p tp beh,
  transf_cminor_program p = OK tp ->
  not_wrong beh ->
  Cminor.exec_program p beh ->
  Asm.exec_program tp beh.
Proof.
  intros. unfold transf_cminor_program, transf_cminorsel_fundef in H.
  simpl in H. repeat TransfProgInv.
  eapply transf_rtl_program_correct; eauto.
  eapply RTLgenproof.transf_program_correct; eauto.
  eapply Selectionproof.transf_program_correct; eauto.
  rewrite print_identity. auto.
Qed.

Theorem transf_c_program_correct:
  forall p tp beh,
  transf_c_program p = OK tp ->
  not_wrong beh ->
  Cstrategy.exec_program p beh ->
  Asm.exec_program tp beh.
Proof.
  intros until beh; unfold transf_c_program; simpl.
  rewrite print_identity.
  caseEq (SimplExpr.transl_program p); simpl; try congruence; intros p0 EQ0.
  rewrite print_identity.
  caseEq (Cshmgen.transl_program p0); simpl; try congruence; intros p1 EQ1.
  caseEq (Cminorgen.transl_program p1); simpl; try congruence; intros p2 EQ2.
  intros EQ3 NOTW SEM.
  eapply transf_cminor_program_correct; eauto.
  eapply Cminorgenproof.transl_program_correct; eauto. 
  eapply Cshmgenproof.transl_program_correct; eauto.
  eapply SimplExprproof.transl_program_correct; eauto.
Qed.
