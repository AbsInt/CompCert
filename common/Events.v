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

Inductive eventval: Set :=
  | EVint: int -> eventval
  | EVfloat: float -> eventval.

Record event : Set := mkevent {
  ev_name: ident;
  ev_args: list eventval;
  ev_res: eventval
}.

(** The dynamic semantics for programs collect traces of events.
  Traces are of two kinds: finite (type [trace]) 
  or infinite (type [traceinf]). *)

Definition trace := list event.

Definition E0 : trace := nil.

Definition Eextcall
             (name: ident) (args: list eventval) (res: eventval) : trace :=
  mkevent name args res :: nil.

Definition Eapp (t1 t2: trace) : trace := t1 ++ t2.

CoInductive traceinf : Set :=
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

Lemma Eappinf_assoc: forall t1 t2 T, (t1 ** t2) *** T = t1 *** (t2 *** T).
Proof.
  induction t1; intros; simpl. auto. decEq; auto.
Qed.

Hint Rewrite E0_left E0_right Eapp_assoc: trace_rewrite.

Opaque trace E0 Eextcall Eapp.

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
