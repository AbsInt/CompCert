(** Representation of (traces of) observable events. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.

Inductive eventval: Set :=
  | EVint: int -> eventval
  | EVfloat: float -> eventval.

Parameter trace: Set.
Parameter E0: trace.
Parameter Eextcall: ident -> list eventval -> eventval -> trace.
Parameter Eapp: trace -> trace -> trace.

Infix "**" := Eapp (at level 60, right associativity).

Axiom E0_left: forall t, E0 ** t = t.
Axiom E0_right: forall t, t ** E0 = t.
Axiom Eapp_assoc: forall t1 t2 t3, (t1 ** t2) ** t3 = t1 ** (t2 ** t3).

Hint Rewrite E0_left E0_right Eapp_assoc: trace_rewrite.

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
