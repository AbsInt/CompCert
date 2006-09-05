(** The compiler back-end and its proof of semantic preservation *)

(** Libraries. *)
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Values.
(** Languages (syntax and semantics). *)
Require Csyntax.
Require Csem.
Require Csharpminor.
Require Cminor.
Require RTL.
Require LTL.
Require Linear.
Require Mach.
Require PPC.
(** Translation passes. *)
Require Cshmgen.
Require Cminorgen.
Require RTLgen.
Require Constprop.
Require CSE.
Require Allocation.
Require Tunneling.
Require Linearize.
Require Stacking.
Require PPCgen.
(** Type systems. *)
Require Ctyping.
Require RTLtyping.
Require LTLtyping.
Require Lineartyping.
Require Machtyping.
(** Proofs of semantic preservation and typing preservation. *)
Require Cshmgenproof3.
Require Cminorgenproof.
Require RTLgenproof.
Require Constpropproof.
Require CSEproof.
Require Allocproof.
Require Alloctyping.
Require Tunnelingproof.
Require Tunnelingtyping.
Require Linearizeproof.
Require Linearizetyping.
Require Stackingproof.
Require Stackingtyping.
Require Machabstr2mach.
Require PPCgenproof.

(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Set) (x: option A) (f: A -> B) : option B :=
  match x with None => None | Some x1 => Some (f x1) end.

Definition apply_partial (A B: Set)
                         (x: option A) (f: A -> option B) : option B :=
  match x with None => None | Some x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

(** We define two translation functions for whole programs: one starting with
  a C program, the other with a Cminor program.  Both
  translations produce PPC programs ready for pretty-printing and
  assembling.  

  There are two ways to compose the compiler passes.  The first translates
  every function from the Cminor program from Cminor to RTL, then to LTL, etc,
  all the way to PPC, and iterates this transformation for every function.
  The second translates the whole Cminor program to a RTL program, then to
  an LTL program, etc.  We follow the first approach because it has lower
  memory requirements.
  
  The translation of a Cminor function to a PPC function is as follows. *)

Definition transf_cminor_fundef (f: Cminor.fundef) : option PPC.fundef :=
  Some f
  @@@ RTLgen.transl_fundef
   @@ Constprop.transf_fundef
   @@ CSE.transf_fundef
  @@@ Allocation.transf_fundef
   @@ Tunneling.tunnel_fundef
   @@ Linearize.transf_fundef
  @@@ Stacking.transf_fundef
  @@@ PPCgen.transf_fundef.

(** The corresponding translations for whole program follow. *)

Definition transf_cminor_program (p: Cminor.program) : option PPC.program :=
  transform_partial_program transf_cminor_fundef p.

Definition transf_c_program (p: Csyntax.program) : option PPC.program :=
  match Ctyping.typecheck_program p with
  | false => None
  | true =>
      Some p 
      @@@ Cshmgen.transl_program
      @@@ Cminorgen.transl_program
      @@@ transf_cminor_program
  end.

(** * Equivalence with whole program transformations *)

(** To prove semantic preservation for the whole compiler, it is easier to reason
  over the second way to compose the compiler pass: the one that translate
  whole programs through each compiler pass.  We now define this second translation
  and prove that it produces the same PPC programs as the first translation. *)

Definition transf_cminor_program2 (p: Cminor.program) : option PPC.program :=
  Some p
  @@@ RTLgen.transl_program
   @@ Constprop.transf_program
   @@ CSE.transf_program
  @@@ Allocation.transf_program
   @@ Tunneling.tunnel_program
   @@ Linearize.transf_program
  @@@ Stacking.transf_program
  @@@ PPCgen.transf_program.

Lemma map_partial_compose:
  forall (X A B C: Set)
         (f1: A -> option B) (f2: B -> option C)
         (p: list (X * A)),
  map_partial f1 p @@@ map_partial f2 =
  map_partial (fun f => f1 f @@@ f2) p.
Proof.
  induction p. simpl. auto.
  simpl. destruct a. destruct (f1 a). 
  simpl. simpl in IHp. destruct (map_partial f1 p).
  simpl. simpl in IHp. destruct (f2 b).
  destruct (map_partial f2 l). 
  rewrite <- IHp. auto.
  rewrite <- IHp. auto.
  auto.
  simpl. rewrite <- IHp. simpl. destruct (f2 b); auto.
  simpl. auto.
Qed.

(*
Lemma transform_partial_program2_compose:
  forall (A B C V W X: Set)
         (f1: A -> option B) (g1: V -> option W)
         (f2: B -> option C) (g2: W -> option X)
         (p: program A V),
  transform_partial_program2 f1 g1 p @@@
                  (fun p' => transform_partial_program2 f2 g2 p') =
  transform_partial_program2 (fun x => f1 x @@@ f2) (fun x => g1 x @@@ g2) p.
Proof.
  unfold transform_partial_program2; intros.
  rewrite <- map_partial_compose; simpl.
  rewrite <- map_partial_compose; simpl.
  destruct (map_partial f1 (prog_funct p)); simpl; auto.
  destruct (map_partial g1 (prog_vars p)); simpl; auto.
  destruct (map_partial f2 l); auto.
Qed.

Lemma transform_program_partial2_partial:
  forall (A B V: Set) (f: A -> option B) (p: program A V),
  transform_partial_program f p =
  transform_partial_program2 f (fun x => Some x) p.
Proof.
  intros. unfold transform_partial_program, transform_partial_program2.
  rewrite map_partial_identity. auto.
Qed.

Lemma apply_partial_transf_program:
  forall (A B V: Set) (f: A -> option B) (x: option (program A V)),
  x @@@ (fun p => transform_partial_program f p) =
  x @@@ (fun p => transform_partial_program2 f (fun x => Some x) p).
Proof.
  intros. unfold apply_partial. 
  destruct x. apply transform_program_partial2_partial. auto.
Qed.
*)
Lemma transform_partial_program_compose:
  forall (A B C V: Set)
         (f1: A -> option B) (f2: B -> option C)
         (p: program A V),
  transform_partial_program f1 p @@@
                       (fun p' => transform_partial_program f2 p') =
  transform_partial_program (fun f => f1 f @@@ f2) p.
Proof.
  unfold transform_partial_program; intros.
  rewrite <- map_partial_compose. simpl. 
  destruct (map_partial f1 (prog_funct p)); simpl.
  auto. auto. 
Qed.

Lemma transform_program_partial_total:
  forall (A B V: Set) (f: A -> B) (p: program A V),
  Some (transform_program f p) =
    transform_partial_program (fun x => Some (f x)) p.
Proof.
  intros. unfold transform_program, transform_partial_program.
  rewrite map_partial_total. auto. 
Qed.

Lemma apply_total_transf_program:
  forall (A B V: Set) (f: A -> B) (x: option (program A V)),
  x @@ (fun p => transform_program f p) =
  x @@@ (fun p => transform_partial_program (fun x => Some (f x)) p).
Proof.
  intros. unfold apply_total, apply_partial. 
  destruct x. apply transform_program_partial_total. auto.
Qed.

Lemma transf_cminor_program_equiv:
  forall p, transf_cminor_program2 p = transf_cminor_program p.
Proof.
  intro. unfold transf_cminor_program, transf_cminor_program2, transf_cminor_fundef.
  simpl. 
  unfold RTLgen.transl_program,
         Constprop.transf_program, RTL.program.
  rewrite apply_total_transf_program.  
  rewrite transform_partial_program_compose.
  unfold CSE.transf_program, RTL.program.
  rewrite apply_total_transf_program.
  rewrite transform_partial_program_compose.
  unfold Allocation.transf_program,
         LTL.program, RTL.program. 
  rewrite transform_partial_program_compose.
  unfold Tunneling.tunnel_program, LTL.program.
  rewrite apply_total_transf_program.
  rewrite transform_partial_program_compose.
  unfold Linearize.transf_program, LTL.program, Linear.program.
  rewrite apply_total_transf_program. 
  rewrite transform_partial_program_compose.
  unfold Stacking.transf_program, Linear.program, Mach.program.
  rewrite transform_partial_program_compose.
  unfold PPCgen.transf_program, Mach.program, PPC.program.
  rewrite transform_partial_program_compose.
  reflexivity.
Qed.

(*
Lemma transf_csharpminor_program_equiv:
  forall p, transf_csharpminor_program2 p = transf_csharpminor_program p.
Proof.
  intros. 
  unfold transf_csharpminor_program2, transf_csharpminor_program, transf_csharpminor_fundef.
  simpl. 
  replace transf_cminor_program2 with transf_cminor_program.
  unfold transf_cminor_program, Cminorgen.transl_program, Cminor.program, PPC.program.
  rewrite apply_partial_transf_program.
  rewrite transform_partial_program2_compose.
  reflexivity.
  symmetry. apply extensionality. exact transf_cminor_program_equiv.
Qed.
*)

(** * Semantic preservation *)

(** We prove that the [transf_program] translations preserve semantics.  The proof
  composes the semantic preservation results for each pass.
  This establishes the correctness of the whole compiler! *)

Theorem transf_cminor_program_correct:
  forall p tp t n,
  transf_cminor_program p = Some tp ->
  Cminor.exec_program p t (Vint n) ->
  PPC.exec_program tp t (Vint n).
Proof.
  intros until n.
  rewrite <- transf_cminor_program_equiv.
  unfold transf_cminor_program2.
  simpl. caseEq (RTLgen.transl_program p). intros p1 EQ1. 
  simpl. set (p2 := CSE.transf_program (Constprop.transf_program p1)).
  caseEq (Allocation.transf_program p2). intros p3 EQ3.
  simpl. set (p4 := Tunneling.tunnel_program p3).
  set (p5 := Linearize.transf_program p4).
  caseEq (Stacking.transf_program p5). intros p6 EQ6.
  simpl. intros EQTP EXEC.
  assert (WT3 : LTLtyping.wt_program p3).
    apply Alloctyping.program_typing_preserved with p2. auto.
  assert (WT4 : LTLtyping.wt_program p4).
    unfold p4. apply Tunnelingtyping.program_typing_preserved. auto.
  assert (WT5 : Lineartyping.wt_program p5).
    unfold p5. apply Linearizetyping.program_typing_preserved. auto.
  assert (WT6: Machtyping.wt_program p6).
    apply Stackingtyping.program_typing_preserved with p5. auto. auto.
  apply PPCgenproof.transf_program_correct with p6; auto.
  apply Machabstr2mach.exec_program_equiv; auto.
  apply Stackingproof.transl_program_correct with p5; auto.
  unfold p5; apply Linearizeproof.transf_program_correct. 
  unfold p4; apply Tunnelingproof.transf_program_correct. 
  apply Allocproof.transl_program_correct with p2; auto.
  unfold p2; apply CSEproof.transf_program_correct;
  apply Constpropproof.transf_program_correct.
  apply RTLgenproof.transl_program_correct with p; auto.
  simpl; intros; discriminate.
  simpl; intros; discriminate.
  simpl; intros; discriminate.
Qed.

Theorem transf_c_program_correct:
  forall p tp t n,
  transf_c_program p = Some tp ->
  Csem.exec_program p t (Vint n) ->
  PPC.exec_program tp t (Vint n).
Proof.
  intros until n; unfold transf_c_program; simpl.
  caseEq (Ctyping.typecheck_program p); try congruence; intro.
  caseEq (Cshmgen.transl_program p); simpl; try congruence; intros p1 EQ1.
  caseEq (Cminorgen.transl_program p1); simpl; try congruence; intros p2 EQ2. 
  intros EQ3 SEM.
  eapply transf_cminor_program_correct; eauto.
  eapply Cminorgenproof.transl_program_correct; eauto. 
  eapply Cshmgenproof3.transl_program_correct; eauto.
  apply Ctyping.typecheck_program_correct; auto.
Qed.
