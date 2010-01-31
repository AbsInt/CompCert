(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Representation of observable events and execution traces. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.

(** The observable behaviour of programs is stated in terms of
  input/output events, which can also be thought of as system calls 
  to the operating system.  An event is generated each time an
  external function (see module AST) is invoked.  The event records
  the name of the external function, the arguments to the function
  invocation provided by the program, and the return value provided by
  the outside world (e.g. the operating system).  Arguments and values
  are either integers or floating-point numbers.  We currently do not
  allow pointers to be exchanged between the program and the outside
  world. *)

Inductive eventval: Type :=
  | EVint: int -> eventval
  | EVfloat: float -> eventval.

Record event : Type := mkevent {
  ev_name: ident;
  ev_args: list eventval;
  ev_res: eventval
}.

(** The dynamic semantics for programs collect traces of events.
  Traces are of two kinds: finite (type [trace]) or infinite (type [traceinf]). *)

Definition trace := list event.

Definition E0 : trace := nil.

Definition Eextcall
             (name: ident) (args: list eventval) (res: eventval) : trace :=
  mkevent name args res :: nil.

Definition Eapp (t1 t2: trace) : trace := t1 ++ t2.

CoInductive traceinf : Type :=
  | Econsinf: event -> traceinf -> traceinf.

Fixpoint Eappinf (t: trace) (T: traceinf) {struct t} : traceinf :=
  match t with
  | nil => T
  | ev :: t' => Econsinf ev (Eappinf t' T)
  end.

(** Concatenation of traces is written [**] in the finite case
  or [***] in the infinite case. *)

Infix "**" := Eapp (at level 60, right associativity).
Infix "***" := Eappinf (at level 60, right associativity).

Lemma E0_left: forall t, E0 ** t = t.
Proof. auto. Qed.

Lemma E0_right: forall t, t ** E0 = t.
Proof. intros. unfold E0, Eapp. rewrite <- app_nil_end. auto. Qed.

Lemma Eapp_assoc: forall t1 t2 t3, (t1 ** t2) ** t3 = t1 ** (t2 ** t3).
Proof. intros. unfold Eapp, trace. apply app_ass. Qed.

Lemma Eapp_E0_inv: forall t1 t2, t1 ** t2 = E0 -> t1 = E0 /\ t2 = E0.
Proof (@app_eq_nil event).
  
Lemma E0_left_inf: forall T, E0 *** T = T.
Proof. auto. Qed.

Lemma Eappinf_assoc: forall t1 t2 T, (t1 ** t2) *** T = t1 *** (t2 *** T).
Proof.
  induction t1; intros; simpl. auto. decEq; auto.
Qed.

Hint Rewrite E0_left E0_right Eapp_assoc
             E0_left_inf Eappinf_assoc: trace_rewrite.

Opaque trace E0 Eextcall Eapp Eappinf.

(** The following [traceEq] tactic proves equalities between traces
  or infinite traces. *)

Ltac substTraceHyp :=
  match goal with
  | [ H: (@eq trace ?x ?y) |- _ ] =>
       subst x || clear H
  end.

Ltac decomposeTraceEq :=
  match goal with
  | [ |- (_ ** _) = (_ ** _) ] =>
      apply (f_equal2 Eapp); auto; decomposeTraceEq
  | _ =>
      auto
  end.

Ltac traceEq := 
  repeat substTraceHyp; autorewrite with trace_rewrite; decomposeTraceEq.

(** The predicate [event_match ef vargs t vres] expresses that
  the event [t] is generated when invoking external function [ef]
  with arguments [vargs], and obtaining [vres] as a return value
  from the operating system. *)

Inductive eventval_match: eventval -> typ -> val -> Prop :=
  | ev_match_int:
      forall i, eventval_match (EVint i) Tint (Vint i)
  | ev_match_float:
      forall f, eventval_match (EVfloat f) Tfloat (Vfloat f).

Inductive eventval_list_match: list eventval -> list typ -> list val -> Prop :=
  | evl_match_nil:
      eventval_list_match nil nil nil
  | evl_match_cons:
      forall ev1 evl ty1 tyl v1 vl,
      eventval_match ev1 ty1 v1 ->
      eventval_list_match evl tyl vl ->
      eventval_list_match (ev1::evl) (ty1::tyl) (v1::vl).

Inductive event_match:
         external_function -> list val -> trace -> val -> Prop :=
  event_match_intro:
    forall ef vargs vres eargs eres,
    eventval_list_match eargs (sig_args ef.(ef_sig)) vargs ->
    eventval_match eres (proj_sig_res ef.(ef_sig)) vres ->
    event_match ef vargs (Eextcall ef.(ef_id) eargs eres) vres.

(** The following section shows that [event_match] is stable under
  relocation of pointer values, as performed by memory injections
  (see module [Mem]). *)

Require Import Mem.

Section EVENT_MATCH_INJECT.

Variable f: meminj.

Remark eventval_match_inject:
  forall ev ty v1,  eventval_match ev ty v1 ->
  forall v2, val_inject f v1 v2 ->
  eventval_match ev ty v2.
Proof.
  induction 1; intros; inversion H; constructor.
Qed.

Remark eventval_list_match_inject:
  forall evl tyl vl1,  eventval_list_match evl tyl vl1 ->
  forall vl2, val_list_inject f vl1 vl2 ->
  eventval_list_match evl tyl vl2.
Proof.
  induction 1; intros.
  inversion H; constructor. 
  inversion H1; constructor. 
  eapply eventval_match_inject; eauto.
  eauto.
Qed.

Lemma event_match_inject:
  forall ef args1 t res args2,
  event_match ef args1 t res ->
  val_list_inject f args1 args2 ->
  event_match ef args2 t res /\ val_inject f res res.
Proof.
  intros. inversion H; subst. 
  split. constructor. eapply eventval_list_match_inject; eauto. auto.
  inversion H2; constructor.
Qed.

End EVENT_MATCH_INJECT.

(** The following section shows that [event_match] is stable under
  replacement of [Vundef] values by more defined values. *)

Section EVENT_MATCH_LESSDEF.

Remark eventval_match_lessdef:
  forall ev ty v1,  eventval_match ev ty v1 ->
  forall v2, Val.lessdef v1 v2 ->
  eventval_match ev ty v2.
Proof.
  induction 1; intros; inv H; constructor.
Qed.

Remark eventval_list_match_moredef:
  forall evl tyl vl1, eventval_list_match evl tyl vl1 ->
  forall vl2, Val.lessdef_list vl1 vl2 ->
  eventval_list_match evl tyl vl2.
Proof.
  induction 1; intros.
  inversion H; constructor. 
  inversion H1; constructor. 
  eapply eventval_match_lessdef; eauto.
  eauto.
Qed.

Lemma event_match_lessdef:
  forall ef args1 t res1 args2,
  event_match ef args1 t res1 ->
  Val.lessdef_list args1 args2 ->
  exists res2, event_match ef args2 t res2 /\ Val.lessdef res1 res2.
Proof.
  intros. inversion H; subst. exists res1; split. 
  constructor. eapply eventval_list_match_moredef; eauto. auto.
  auto.
Qed.

End EVENT_MATCH_LESSDEF.

(** Bisimilarity between infinite traces. *)

CoInductive traceinf_sim: traceinf -> traceinf -> Prop :=
  | traceinf_sim_cons: forall e T1 T2,
      traceinf_sim T1 T2 ->
      traceinf_sim (Econsinf e T1) (Econsinf e T2).

Lemma traceinf_sim_refl:
  forall T, traceinf_sim T T.
Proof.
  cofix COINDHYP; intros.
  destruct T. constructor. apply COINDHYP.
Qed.
 
Lemma traceinf_sim_sym:
  forall T1 T2, traceinf_sim T1 T2 -> traceinf_sim T2 T1.
Proof.
  cofix COINDHYP; intros. inv H; constructor; auto.
Qed.

Lemma traceinf_sim_trans:
  forall T1 T2 T3, 
  traceinf_sim T1 T2 -> traceinf_sim T2 T3 -> traceinf_sim T1 T3.
Proof.
  cofix COINDHYP;intros. inv H; inv H0; constructor; eauto.
Qed.

(** The "is prefix of" relation between a finite and an infinite trace. *)

Inductive traceinf_prefix: trace -> traceinf -> Prop :=
  | traceinf_prefix_nil: forall T,
      traceinf_prefix nil T
  | traceinf_prefix_cons: forall e t1 T2,
      traceinf_prefix t1 T2 ->
      traceinf_prefix (e :: t1) (Econsinf e T2).

Lemma traceinf_prefix_app:
  forall t1 T2 t,
  traceinf_prefix t1 T2 ->
  traceinf_prefix (t ** t1) (t *** T2).
Proof.
  induction t; simpl; intros. auto.
  change ((a :: t) ** t1) with (a :: (t ** t1)).
  change ((a :: t) *** T2) with (Econsinf a (t *** T2)).
  constructor. auto.
Qed.

(** An alternate presentation of infinite traces as
  infinite concatenations of nonempty finite traces. *)

CoInductive traceinf': Type :=
  | Econsinf': forall (t: trace) (T: traceinf'), t <> E0 -> traceinf'.

Program Definition split_traceinf' (t: trace) (T: traceinf') (NE: t <> E0): event * traceinf' :=
  match t with
  | nil => _
  | e :: nil => (e, T)
  | e :: t' => (e, Econsinf' t' T _)
  end.
Next Obligation.
  elimtype False. elim NE. auto. 
Qed.
Next Obligation.
  red; intro. elim (H e). rewrite H0. auto. 
Qed.

CoFixpoint traceinf_of_traceinf' (T': traceinf') : traceinf :=
  match T' with
  | Econsinf' t T'' NOTEMPTY =>
      let (e, tl) := split_traceinf' t T'' NOTEMPTY in
      Econsinf e (traceinf_of_traceinf' tl)
  end.

Remark unroll_traceinf':
  forall T, T = match T with Econsinf' t T' NE => Econsinf' t T' NE end.
Proof.
  intros. destruct T; auto.
Qed.

Remark unroll_traceinf:
  forall T, T = match T with Econsinf t T' => Econsinf t T' end.
Proof.
  intros. destruct T; auto.
Qed.

Lemma traceinf_traceinf'_app:
  forall t T NE,
  traceinf_of_traceinf' (Econsinf' t T NE) = t *** traceinf_of_traceinf' T.
Proof.
  induction t.
  intros. elim NE. auto.
  intros. simpl.   
  rewrite (unroll_traceinf (traceinf_of_traceinf' (Econsinf' (a :: t) T NE))).
  simpl. destruct t. auto.
Transparent Eappinf.
  simpl. f_equal. apply IHt. 
Qed.
