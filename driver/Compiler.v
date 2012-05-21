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
Require Cexec.
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
Require Inlining.
Require Renumber.
Require Constprop.
Require CSE.
Require Allocation.
Require Tunneling.
Require Linearize.
Require CleanupLabels.
Require Reload.
Require RRE.
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
Require Inliningproof.
Require Renumberproof.
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
Require RREproof.
Require RREtyping.
Require Stackingproof.
Require Stackingtyping.
Require Asmgenproof.

(** Pretty-printers (defined in Caml). *)
Parameter print_Clight: Clight.program -> unit.
Parameter print_Cminor: Cminor.program -> unit.
Parameter print_RTL: RTL.program -> unit.
Parameter print_RTL_tailcall: RTL.program -> unit.
Parameter print_RTL_inline: RTL.program -> unit.
Parameter print_RTL_constprop: RTL.program -> unit.
Parameter print_RTL_cse: RTL.program -> unit.
Parameter print_LTLin: LTLin.program -> unit.
Parameter print_Mach: Mach.program -> unit.

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
  let unused := printer prog in prog.

(** We define three translation functions for whole programs: one
  starting with a C program, one with a Cminor program, one with an
  RTL program.  The three translations produce Asm programs ready for
  pretty-printing and assembling. *)

Definition transf_rtl_program (f: RTL.program) : res Asm.program :=
   OK f
   @@ print print_RTL
   @@ Tailcall.transf_program
   @@ print print_RTL_tailcall
  @@@ Inlining.transf_program
   @@ Renumber.transf_program
   @@ print print_RTL_inline
   @@ Constprop.transf_program
   @@ Renumber.transf_program
   @@ print print_RTL_constprop
  @@@ CSE.transf_program
   @@ print print_RTL_cse
  @@@ Allocation.transf_program
   @@ Tunneling.tunnel_program
  @@@ Linearize.transf_program
   @@ CleanupLabels.transf_program
   @@ print print_LTLin
   @@ Reload.transf_program
   @@ RRE.transf_program
  @@@ Stacking.transf_program
   @@ print print_Mach
  @@@ Asmgen.transf_program.

Definition transf_cminor_program (p: Cminor.program) : res Asm.program :=
   OK p
   @@ print print_Cminor
   @@ Selection.sel_program
  @@@ RTLgen.transl_program
  @@@ transf_rtl_program.

Definition transf_clight_program (p: Clight.program) : res Asm.program :=
  OK p 
   @@ print print_Clight
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program
  @@@ transf_cminor_program.

Definition transf_c_program (p: Csyntax.program) : res Asm.program :=
  OK p 
  @@@ SimplExpr.transl_program
  @@@ transf_clight_program.

(** Force [Initializers] and [Cexec] to be extracted as well. *)

Definition transl_init := Initializers.transl_init.
Definition cexec_do_step := Cexec.do_step.

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
  { pb | map_partial ctx f1 pa = OK pb /\ map_partial ctx f2 pb = OK pc }.
Proof.
  induction pa; simpl.
  intros. inv H. econstructor; eauto.
  intro pc. destruct a as [x a].
  destruct (f1 a) as [] _eqn; simpl; try congruence.
  destruct (f2 b) as [] _eqn; simpl; try congruence.
  destruct (map_partial ctx (fun f => f1 f @@@ f2) pa) as [] _eqn; simpl; try congruence.
  intros. inv H.
  destruct (IHpa l) as [pb [P Q]]; auto.
  rewrite P; simpl.
  econstructor; split. eauto. simpl. rewrite Heqr0. rewrite Q. auto.
Qed.

Lemma transform_partial_program_compose:
  forall (A B C V: Type)
         (f1: A -> res B) (f2: B -> res C)
         (pa: program A V) (pc: program C V),
  transform_partial_program (fun f => f1 f @@@ f2) pa = OK pc ->
  { pb | transform_partial_program f1 pa = OK pb /\
         transform_partial_program f2 pb = OK pc }.
Proof.
  intros. unfold transform_partial_program in H. 
  destruct (map_partial prefix_name (fun f : A => f1 f @@@ f2) (prog_funct pa)) as [] _eqn;
  simpl in H; inv H.
  destruct (map_partial_compose _ _ _ _ _ _ _ _ _ Heqr) as [xb [P Q]].
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
  { pb | transform_partial_program f1 pa = OK pb /\
         transform_program f2 pb = pc }.
Proof.
  intros. 
  replace (fun f : A => f1 f @@ f2)
     with (fun f : A => f1 f @@@ (fun x => OK (f2 x))) in H.
  destruct (transform_partial_program_compose _ _ _ _ _ _ _  _ H) as [pb [X Y]].
  exists pb; split. auto. 
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

(** We prove that the [transf_program] translations preserve semantics
  by constructing the following simulations:
- Forward simulations from [Cstrategy] / [Cminor] / [RTL] to [Asm]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Asm]).
- Backward simulation from [Csem] to [Asm]
  (composition of two backward simulations).

These results establish the correctness of the whole compiler! *)

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
  forall p tp,
  transf_rtl_program p = OK tp ->
  forward_simulation (RTL.semantics p) (Asm.semantics tp)
  * backward_simulation (RTL.semantics p) (Asm.semantics tp).
Proof.
  intros.
  assert (F: forward_simulation (RTL.semantics p) (Asm.semantics tp)).
  unfold transf_rtl_program in H.
  repeat rewrite compose_print_identity in H.
  simpl in H.
  set (p1 := Tailcall.transf_program p) in *.
  destruct (Inlining.transf_program p1) as [p11|]_eqn; simpl in H; try discriminate.
  set (p12 := Renumber.transf_program p11) in *.
  set (p2 := Constprop.transf_program p12) in *.
  set (p21 := Renumber.transf_program p2) in *.
  destruct (CSE.transf_program p21) as [p3|]_eqn; simpl in H; try discriminate.
  destruct (Allocation.transf_program p3) as [p4|]_eqn; simpl in H; try discriminate.
  set (p5 := Tunneling.tunnel_program p4) in *.
  destruct (Linearize.transf_program p5) as [p6|]_eqn; simpl in H; try discriminate.
  set (p7 := CleanupLabels.transf_program p6) in *.
  set (p8 := Reload.transf_program p7) in *.
  set (p9 := RRE.transf_program p8) in *.
  destruct (Stacking.transf_program p9) as [p10|]_eqn; simpl in H; try discriminate.

  assert(TY1: LTLtyping.wt_program p5).
    eapply Tunnelingtyping.program_typing_preserved. 
    eapply Alloctyping.program_typing_preserved; eauto.
  assert(TY2: LTLintyping.wt_program p7).
    eapply CleanupLabelstyping.program_typing_preserved.
    eapply Linearizetyping.program_typing_preserved; eauto.
  assert(TY3: Lineartyping.wt_program p9).
    eapply RREtyping.program_typing_preserved.
    eapply Reloadtyping.program_typing_preserved; eauto.
  assert(TY4: Machtyping.wt_program p10).
    eapply Stackingtyping.program_typing_preserved; eauto.

  eapply compose_forward_simulation. apply Tailcallproof.transf_program_correct. 
  eapply compose_forward_simulation. apply Inliningproof.transf_program_correct. eassumption.
  eapply compose_forward_simulation. apply Renumberproof.transf_program_correct. 
  eapply compose_forward_simulation. apply Constpropproof.transf_program_correct. 
  eapply compose_forward_simulation. apply Renumberproof.transf_program_correct. 
  eapply compose_forward_simulation. apply CSEproof.transf_program_correct. eassumption.
  eapply compose_forward_simulation. apply Allocproof.transf_program_correct. eassumption.
  eapply compose_forward_simulation. apply Tunnelingproof.transf_program_correct.
  eapply compose_forward_simulation. apply Linearizeproof.transf_program_correct. eassumption. eauto. 
  eapply compose_forward_simulation. apply CleanupLabelsproof.transf_program_correct. 
  eapply compose_forward_simulation. apply Reloadproof.transf_program_correct. eauto.
  eapply compose_forward_simulation. apply RREproof.transf_program_correct. eauto.
  eapply compose_forward_simulation. apply Stackingproof.transf_program_correct. eassumption. eauto.
  apply Asmgenproof.transf_program_correct; eauto.
  split. auto. 
  apply forward_to_backward_simulation. auto. 
  apply RTL.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem transf_cminor_program_correct:
  forall p tp,
  transf_cminor_program p = OK tp ->
  forward_simulation (Cminor.semantics p) (Asm.semantics tp)
  * backward_simulation (Cminor.semantics p) (Asm.semantics tp).
Proof.
  intros.
  assert (F: forward_simulation (Cminor.semantics p) (Asm.semantics tp)).
  unfold transf_cminor_program in H.
  repeat rewrite compose_print_identity in H.
  simpl in H. 
  set (p1 := Selection.sel_program p) in *.
  destruct (RTLgen.transl_program p1) as [p2|]_eqn; simpl in H; try discriminate.
  eapply compose_forward_simulation. apply Selectionproof.transf_program_correct.
  eapply compose_forward_simulation. apply RTLgenproof.transf_program_correct. eassumption.
  exact (fst (transf_rtl_program_correct _ _ H)).

  split. auto. 
  apply forward_to_backward_simulation. auto. 
  apply Cminor.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem transf_clight_program_correct:
  forall p tp,
  transf_clight_program p = OK tp ->
  forward_simulation (Clight.semantics p) (Asm.semantics tp)
  * backward_simulation (Clight.semantics p) (Asm.semantics tp).
Proof.
  intros. 
  assert (F: forward_simulation (Clight.semantics p) (Asm.semantics tp)).
  revert H; unfold transf_clight_program; simpl.
  rewrite print_identity.
  caseEq (Cshmgen.transl_program p); simpl; try congruence; intros p1 EQ1.
  caseEq (Cminorgen.transl_program p1); simpl; try congruence; intros p2 EQ2.
  intros EQ3.
  eapply compose_forward_simulation. apply Cshmgenproof.transl_program_correct. eauto.
  eapply compose_forward_simulation. apply Cminorgenproof.transl_program_correct. eauto.
  exact (fst (transf_cminor_program_correct _ _ EQ3)). 

  split. auto. 
  apply forward_to_backward_simulation. auto. 
  apply Clight.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem transf_cstrategy_program_correct:
  forall p tp,
  transf_c_program p = OK tp ->
  forward_simulation (Cstrategy.semantics p) (Asm.semantics tp)
  * backward_simulation (atomic (Cstrategy.semantics p)) (Asm.semantics tp).
Proof.
  intros.
  assert (F: forward_simulation (Cstrategy.semantics p) (Asm.semantics tp)).
  revert H; unfold transf_c_program; simpl.
  caseEq (SimplExpr.transl_program p); simpl; try congruence; intros p0 EQ0.
  intros EQ1.
  eapply compose_forward_simulation. apply SimplExprproof.transl_program_correct. eauto.
  exact (fst (transf_clight_program_correct _ _ EQ1)). 

  split. auto. 
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces. eapply Asm.semantics_determinate.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem transf_c_program_correct:
  forall p tp,
  transf_c_program p = OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  intros. 
  apply compose_backward_simulation with (atomic (Cstrategy.semantics p)).
  eapply sd_traces; eapply Asm.semantics_determinate.
  apply factor_backward_simulation. 
  apply Cstrategy.strategy_simulation.
  apply Csem.semantics_single_events.
  eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  exact (snd (transf_cstrategy_program_correct _ _ H)).
Qed.
