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
Require Import String.
Require Import Coqlib Errors.
Require Import AST Linking Smallstep ExposedSmallstep2.
(** Languages (syntax and semantics). *)
Require Ctypes Csyntax Csem Cstrategy Cexec.
Require Clight.
Require Csharpminor.
Require Cminor.
Require CminorSel.
Require RTL.
Require LTL.
Require Linear.
Require Mach.
Require Asm.
(** Translation passes. *)
Require Initializers.
Require SimplExpr.
Require SimplLocals.
Require Cshmgen.
Require Cminorgen.
Require Selection.
Require RTLgen.
Require Tailcall.
Require Inlining.
Require Renumber.
Require Constprop.
Require CSE.
Require Deadcode. 
Require Unusedglob.
Require Allocation.
Require Tunneling.
Require Linearize.
Require CleanupLabels.
Require Debugvar.
Require Stacking.
Require Asmgen.
(** Proofs of semantic preservation. *)
Require SimplExprproof.
(*Require SimplLocalsproof.*)
Require Cshmgenproof.
Require Cminorgenproof.
Require Selectionproof.
Require RTLgenproof.
Require Tailcallproof.
(*Require Inliningproof.*)
Require Renumberproof.
Require Constpropproof.
Require CSEproof.
Require Deadcodeproof.
(*Require Unusedglobproof.*)
Require Allocproof.
Require Tunnelingproof.
Require Linearizeproof.
Require CleanupLabelsproof.
Require Debugvarproof.
Require Stackingproof_temp.
(*Require Stackingproof.*)
Require Asmgenproof.
(** Command-line flags. *)
Require Import Compopts.

(** Pretty-printers (defined in Caml). *)
Parameter print_Clight: Clight.program -> unit.
Parameter print_Cminor: Cminor.program -> unit.
Parameter print_RTL: Z -> RTL.program -> unit.
Parameter print_LTL: LTL.program -> unit.
Parameter print_Mach: Mach.program -> unit.

Local Open Scope string_scope.

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

Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.

Definition total_if {A: Type}
          (flag: unit -> bool) (f: A -> A) (prog: A) : A :=
  if flag tt then f prog else prog.

Definition partial_if {A: Type}
          (flag: unit -> bool) (f: A -> res A) (prog: A) : res A :=
  if flag tt then f prog else OK prog.

(** We define three translation functions for whole programs: one
  starting with a C program, one with a Cminor program, one with an
  RTL program.  The three translations produce Asm programs ready for
  pretty-printing and assembling. *)

Definition simpl_transf_rtl_program (f: RTL.program) : res Asm.program:=
  OK f
   @@ print (print_RTL 0)
   @@ total_if Compopts.optim_tailcalls (time "Tail calls" Tailcall.transf_program)
   @@ print (print_RTL 2)
   @@ time "Renumbering" Renumber.transf_program
   @@ print (print_RTL 3)
   @@ total_if Compopts.optim_constprop (time "Constant propagation" Constprop.transf_program)
   @@ print (print_RTL 4)
   @@ total_if Compopts.optim_constprop (time "Renumbering" Renumber.transf_program)
   @@ print (print_RTL 5)
  @@@ partial_if Compopts.optim_CSE (time "CSE" CSE.transf_program)(*
   @@ print (print_RTL 6)
  @@@ partial_if Compopts.optim_redundancy (time "Redundancy elimination" Deadcode.transf_program) *)(*
   @@ print (print_RTL 7)
  @@@ time "Unused globals" Unusedglob.transform_program*)
   @@ print (print_RTL 8)
  @@@ time "Register allocation" Allocation.transf_program
   @@ print print_LTL
   @@ time "Branch tunneling" Tunneling.tunnel_program
  @@@ time "CFG linearization" Linearize.transf_program
   @@ time "Label cleanup" CleanupLabels.transf_program
  @@@ partial_if Compopts.debug (time "Debugging info for local variables" Debugvar.transf_program)
  @@@ time "Mach generation" Stacking.transf_program
   @@ print print_Mach
  @@@ time "Asm generation" Asmgen.transf_program.

Definition simpl_transf_cminor_program (p: Cminor.program) : res Asm.program :=
   OK p
   @@ print print_Cminor
  @@@ time "Instruction selection" Selection.sel_program
  @@@ time "RTL generation" RTLgen.transl_program
  @@@ simpl_transf_rtl_program.

Definition simpl_transf_clight_program (p: Clight.program) : res Asm.program :=
  OK p
   @@ print print_Clight
  @@@ time "C#minor generation" Cshmgen.transl_program
  @@@ time "Cminor generation" Cminorgen.transl_program
  @@@ simpl_transf_cminor_program.

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

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit),
  x @@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto.
Qed.

(** * Relational specification of compilation *)

Definition match_if {A: Type} (flag: unit -> bool) (R: A -> A -> Prop): A -> A -> Prop :=
  if flag tt then R else eq.

Lemma total_if_match:
  forall (A: Type) (flag: unit -> bool) (f: A -> A) (rel: A -> A -> Prop) (prog: A),
  (forall p, rel p (f p)) ->
  match_if flag rel prog (total_if flag f prog).
Proof.
  intros. unfold match_if, total_if. destruct (flag tt); auto.
Qed.

Lemma partial_if_match:
  forall (A: Type) (flag: unit -> bool) (f: A -> res A) (rel: A -> A -> Prop) (prog tprog: A),
  (forall p tp, f p = OK tp -> rel p tp) ->
  partial_if flag f prog = OK tprog ->
  match_if flag rel prog tprog.
Proof.
  intros. unfold match_if, partial_if in *. destruct (flag tt). auto. congruence.
Qed.

Instance TransfIfLink {A: Type} {LA: Linker A}
                      (flag: unit -> bool) (transf: A -> A -> Prop) (TL: TransfLink transf)
                      : TransfLink (match_if flag transf).
Proof.
  unfold match_if. destruct (flag tt).
- auto.
- red; intros. subst tp1 tp2. exists p; auto.
Qed.

(** This is the list of compilation passes of CompCert in relational style.
  Each pass is characterized by a [match_prog] relation between its
  input code and its output code.  The [mkpass] and [:::] combinators,
  defined in module [Linking], ensure that the passes are composable
  (the output language of a pass is the input language of the next pass)
  and that they commute with linking (property [TransfLink], inferred
  by the type class mechanism of Coq). *)

Local Open Scope linking_scope.

Axiom Stackingproof_match_prog: Linear.program -> Mach.program -> Prop.

Definition Simpl_CompCert's_passes :=
   mkpass Cshmgenproof.match_prog
  ::: mkpass Cminorgenproof.match_prog
  ::: mkpass Selectionproof.match_prog
  ::: mkpass RTLgenproof.match_prog
  ::: mkpass (match_if Compopts.optim_tailcalls Tailcallproof.match_prog)
  ::: mkpass Renumberproof.match_prog
  ::: mkpass (match_if Compopts.optim_constprop Constpropproof.match_prog)
  ::: mkpass (match_if Compopts.optim_constprop Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.optim_CSE CSEproof.match_prog)
  ::: mkpass Allocproof.match_prog
  ::: mkpass Tunnelingproof.match_prog
  ::: mkpass Linearizeproof.match_prog
  ::: mkpass CleanupLabelsproof.match_prog
  ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
  ::: mkpass Stackingproof_temp.match_prog
  ::: mkpass Asmgenproof.match_prog
  ::: pass_nil _.


(** Composing the [match_prog] relations above, we obtain the relation
  between CompCert C sources and Asm code that characterize CompCert's
  compilation. *)

Definition simpl_match_prog: Clight.program -> Asm.program -> Prop :=
  pass_match (compose_passes Simpl_CompCert's_passes).

(** The [transf_c_program] function, when successful, produces
  assembly code that is in the [match_prog] relation with the source C program. *)

Theorem transf_clight_program_match:
  forall p tp,
  simpl_transf_clight_program p = OK tp ->
  simpl_match_prog p tp.
Proof.
  intros p tp T.
  unfold simpl_transf_clight_program, time in T.
  rewrite ! compose_print_identity in T. simpl in T.
  destruct (Cshmgen.transl_program p) as [p3|e] eqn:P3; simpl in T; try discriminate.
  destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
  unfold simpl_transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold simpl_transf_rtl_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  set (p7 := total_if optim_tailcalls Tailcall.transf_program p6) in *.
  set (p8 := Renumber.transf_program p7) in *.
  set (p9 := total_if optim_constprop Constprop.transf_program p8) in *.
  set (p10 := total_if optim_constprop Renumber.transf_program p9) in *.
  destruct (partial_if optim_CSE CSE.transf_program p10) as [p11|e] eqn:P11; simpl in T; try discriminate.
  destruct (Allocation.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
  set (p13 := Tunneling.tunnel_program p12) in *.
  destruct (Linearize.transf_program p13) as [p14|e] eqn:P14; simpl in T; try discriminate.
  set (p15 := CleanupLabels.transf_program p14) in *.
  destruct (partial_if debug Debugvar.transf_program p15) as [p16|e] eqn:P16; simpl in T; try discriminate.
  destruct (Stacking.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
  unfold simpl_match_prog; simpl. 
  exists p3; split. apply Cshmgenproof.transf_program_match; auto.
  exists p4; split. apply Cminorgenproof.transf_program_match; auto.
  exists p5; split. apply Selectionproof.transf_program_match; auto.
  exists p6; split. apply RTLgenproof.transf_program_match; auto.
  exists p7; split. apply total_if_match. apply Tailcallproof.transf_program_match.
  exists p8; split. apply Renumberproof.transf_program_match; auto.
  exists p9; split. apply total_if_match. apply Constpropproof.transf_program_match.
  exists p10; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p11; split. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
  exists p12; split. apply Allocproof.transf_program_match; auto.
  exists p13; split. apply Tunnelingproof.transf_program_match.
  exists p14; split. apply Linearizeproof.transf_program_match; auto.
  exists p15; split. apply CleanupLabelsproof.transf_program_match; auto.
  exists p16; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
  exists p17; split. apply Stackingproof_temp.transf_program_match; auto.
  exists tp; split. apply Asmgenproof.transf_program_match; auto. 
  reflexivity.
Qed.

(** * Semantic preservation *)

(** We now prove that the whole CompCert compiler (as characterized by the
  [match_prog] relation) preserves semantics by constructing 
  the following simulations:
- Forward simulations from [Cstrategy] to [Asm]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Asm]).
- Backward simulation from [Csem] to [Asm]
  (composition of two backward simulations).
*)

Remark forward_simulation_identity:
  forall sem, forward_simulation sem sem.
Proof.
  intros. apply forward_simulation_step with (fun s1 s2 => s2 = s1); intros.
- auto.
- exists s1; auto.
- subst s2; auto.
- subst s2. exists s1'; auto.
Qed.

Remark forward_injection_identity:
  forall sem get_mem, forward_injection sem sem get_mem get_mem.
Proof.
  intros. econstructor.
Admitted.

Remark forward_extension_identity:
  forall sem get_mem, forward_extension sem sem get_mem get_mem.
Proof.
  intros. econstructor.
Admitted.

Lemma match_if_simulation:
  forall (A: Type) (sem: A -> semantics) (flag: unit -> bool) (transf: A -> A -> Prop) (prog tprog: A),
  match_if flag transf prog tprog ->
  (forall p tp, transf p tp -> forward_simulation (sem p) (sem tp)) ->
  forward_simulation (sem prog) (sem tprog).
Proof.
  intros. unfold match_if in *. destruct (flag tt). eauto. subst. apply forward_simulation_identity.
Qed.

Lemma exposed_match_if_injection:
  forall (A: Type) (sem: A -> semantics)(get_mem: forall p, state (sem p) -> Memory.Mem.mem ) (flag: unit -> bool) (transf: A -> A -> Prop) (prog tprog: A),
  match_if flag transf prog tprog ->
  (forall p tp, transf p tp -> forward_injection (sem p) (sem tp) (get_mem p) (get_mem tp)) ->
  forward_injection (sem prog) (sem tprog) (get_mem prog) (get_mem tprog).
Proof.
  intros. unfold match_if in *. destruct (flag tt). eauto. subst.
  apply forward_injection_identity.
Qed.

Lemma exposed_match_if_extension:
  forall (A: Type) (sem: A -> semantics)(get_mem: forall p, state (sem p) -> Memory.Mem.mem ) (flag: unit -> bool) (transf: A -> A -> Prop) (prog tprog: A),
  match_if flag transf prog tprog ->
  (forall p tp, transf p tp -> forward_extension (sem p) (sem tp) (get_mem p) (get_mem tp)) ->
  forward_extension (sem prog) (sem tprog) (get_mem prog) (get_mem tprog).
Proof.
  intros. unfold match_if in *. destruct (flag tt). eauto. subst.
  apply forward_extension_identity.
Qed.

Theorem simpl_clight_semantic_preservation:
  forall p tp,
  simpl_match_prog p tp ->
  fsim_injection (Clight.semantics2 p) (Asm.semantics tp) Clight.get_mem Asm.get_mem.
Proof.
  intros p tp M. unfold simpl_match_prog, pass_match in M; simpl in M.
Ltac DestructM' :=
  match goal with
    [ H: exists p, _ /\ _ |- _ ] => 
      let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
      destruct H as (p & M & MM); clear H
  end.
  repeat DestructM'. subst tp.
   eapply extension_injection_composition.
    eapply Cshmgenproof.exposed_transl_program_correct; eassumption.
  eapply injection_injection_composition.
    eapply Cminorgenproof.exposed_transl_program_correct; eassumption.
  eapply extension_injection_composition.
    eapply Selectionproof.exposed_transl_program_correct; eassumption.
  eapply extension_injection_composition.
    eapply RTLgenproof.exposed_transl_program_correct; eassumption.
  eapply extension_injection_composition with (L2:=RTL.semantics p5).
    eapply (exposed_match_if_extension _ RTL.semantics ( fun _ => RTL.get_mem)); eauto.
    eexact Tailcallproof.exposed_transl_program_correct. 
  eapply extension_injection_composition.
    eapply Renumberproof.exposed_transl_program_correct; eassumption.
  eapply extension_injection_composition.
    eapply (exposed_match_if_extension _ RTL.semantics ( fun _ => RTL.get_mem)); eauto.
    exact Constpropproof.exposed_transl_program_correct.
  eapply extension_injection_composition.
    eapply (exposed_match_if_extension _ RTL.semantics ( fun _ => RTL.get_mem)); eauto.
    exact Renumberproof.exposed_transl_program_correct.
  eapply extension_injection_composition.
    eapply (exposed_match_if_extension _ RTL.semantics ( fun _ => RTL.get_mem)); eauto.
    exact CSEproof.exposed_transl_program_correct.
  eapply extension_injection_composition.
    eapply Allocproof.exposed_transl_program_correct; eassumption.
  eapply extension_injection_composition.
    eapply Tunnelingproof.exposed_transl_program_correct; eassumption.
  eapply extension_injection_composition.
    eapply Linearizeproof.exposed_transl_program_correct; eassumption.
  eapply extension_injection_composition.
    eapply CleanupLabelsproof.exposed_transl_program_correct; eassumption.
  eapply extension_injection_composition.
    eapply (exposed_match_if_extension _ Linear.semantics ( fun _ => Linear.get_mem)); eauto.
    exact Debugvarproof.exposed_transl_program_correct.
  eapply injection_extension_composition.
    Axiom Stackingproof_exposed_transl_program_correct:
      forall prog return_address_offset tprog,
        forall (return_address_offset_exists:
             forall f sg ros c,
               is_tail (Mach.Mcall sg ros :: c) (Mach.fn_code f) ->
               exists ofs, return_address_offset f c ofs),
       Stackingproof_temp.match_prog prog tprog->
       forward_injection (Linear.semantics prog)
                         (Mach.semantics return_address_offset tprog)
                         Linear.get_mem Mach.get_mem.
    eapply Stackingproof_exposed_transl_program_correct with (return_address_offset:= Asmgenproof0.return_address_offset).
    exact Asmgenproof.return_address_exists.
    eassumption.
    eapply Asmgenproof.exposed_transf_program_correct; eassumption.
  
Qed.


(** * Correctness of the CompCert compiler *)

(** Combining the results above, we obtain semantic preservation for two
  usage scenarios of CompCert: compilation of a single monolithic program,
  and separate compilation of multiple source files followed by linking.

  In the monolithic case, we have a whole C program [p] that is
  compiled in one run of CompCert to a whole Asm program [tp].
  Then, [tp] preserves the semantics of [p], in the sense that there
  exists a backward simulation of the dynamic semantics of [p]
  by the dynamic semantics of [tp]. *)

Theorem transf_clight_program_correct:
  forall p tp,
  simpl_transf_clight_program p = OK tp  ->
  forward_injection (Clight.semantics2 p) (Asm.semantics tp) Clight.get_mem Asm.get_mem.
Proof.
  intros. apply simpl_clight_semantic_preservation.
  apply transf_clight_program_match; auto.
Qed.
