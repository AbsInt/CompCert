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

(** A deterministic evaluation strategy for C. *)

Require Import Coq.Program.Equality.
Require Import Axioms.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Determinism.
Require Import Csyntax.
Require Import Csem.

Section STRATEGY.

Variable ge: genv.

(** * Definition of the strategy *)

(** We now formalize a particular strategy for reducing expressions which
  is the one implemented by the CompCert compiler.  It evaluates effectful
  subexpressions first, in leftmost-innermost order, then finishes 
  with the evaluation of the remaining simple expression. *)

(** Simple expressions are defined as follows. *)

Fixpoint simple (a: expr) : Prop :=
  match a with
  | Eloc _ _ _ => True
  | Evar _ _ => True
  | Ederef r _ => simple r
  | Efield l1 _ _ => simple l1
  | Eval _ _ => True
  | Evalof l _ => simple l
  | Eaddrof l _ => simple l
  | Eunop _ r1 _ => simple r1
  | Ebinop _ r1 r2 _ => simple r1 /\ simple r2
  | Ecast r1 _ => simple r1
  | Econdition _ _ _ _ => False
  | Esizeof _ _ => True
  | Eassign _ _ _ => False
  | Eassignop _ _ _ _ _ => False
  | Epostincr _ _ _ => False
  | Ecomma _ _ _ => False
  | Ecall _ _ _ => False
  | Eparen _ _ => False
  end.

Fixpoint simplelist (rl: exprlist) : Prop :=
  match rl with Enil => True | Econs r rl' => simple r /\ simplelist rl' end.

(** Simple expressions have interesting properties: their evaluations always
  terminate, are deterministic, and preserve the memory state.
  We seize this opportunity to define a big-step semantics for simple
  expressions. *)

Section SIMPLE_EXPRS.

Variable e: env.
Variable m: mem.

Inductive eval_simple_lvalue: expr -> block -> int -> Prop :=
  | esl_loc: forall b ofs ty,
      eval_simple_lvalue (Eloc b ofs ty) b ofs
  | esl_var_local: forall x ty b,
      e!x = Some(b, ty) ->
      eval_simple_lvalue (Evar x ty) b Int.zero
  | esl_var_global: forall x ty b,
      e!x = None ->
      Genv.find_symbol ge x = Some b ->
      type_of_global ge b = Some ty ->
      eval_simple_lvalue (Evar x ty) b Int.zero
  | esl_deref: forall r ty b ofs,
      eval_simple_rvalue r (Vptr b ofs) ->
      eval_simple_lvalue (Ederef r ty) b ofs
  | esl_field_struct: forall l f ty b ofs id fList delta,
      eval_simple_lvalue l b ofs ->
      typeof l = Tstruct id fList -> field_offset f fList = OK delta ->
      eval_simple_lvalue (Efield l f ty) b (Int.add ofs (Int.repr delta))
  | esl_field_union: forall l f ty b ofs id fList,
      eval_simple_lvalue l b ofs ->
      typeof l = Tunion id fList ->
      eval_simple_lvalue (Efield l f ty) b ofs

with eval_simple_rvalue: expr -> val -> Prop :=
  | esr_val: forall v ty,
      eval_simple_rvalue (Eval v ty) v
  | esr_rvalof: forall b ofs l ty v,
      eval_simple_lvalue l b ofs ->
      ty = typeof l ->
      load_value_of_type ty m b ofs = Some v ->
      eval_simple_rvalue (Evalof l ty) v
  | esr_addrof: forall b ofs l ty,
      eval_simple_lvalue l b ofs ->
      eval_simple_rvalue (Eaddrof l ty) (Vptr b ofs)
  | esr_unop: forall op r1 ty v1 v,
      eval_simple_rvalue r1 v1 ->
      sem_unary_operation op v1 (typeof r1) = Some v ->
      eval_simple_rvalue (Eunop op r1 ty) v
  | esr_binop: forall op r1 r2 ty v1 v2 v,
      eval_simple_rvalue r1 v1 -> eval_simple_rvalue r2 v2 ->
      sem_binary_operation op v1 (typeof r1) v2 (typeof r2) m = Some v ->
      eval_simple_rvalue (Ebinop op r1 r2 ty) v
  | esr_cast: forall ty r1 v1 v,
      eval_simple_rvalue r1 v1 ->
      cast v1 (typeof r1) ty v ->
      eval_simple_rvalue (Ecast r1 ty) v
  | esr_sizeof: forall ty1 ty,
      eval_simple_rvalue (Esizeof ty1 ty) (Vint (Int.repr (sizeof ty1))).

Inductive eval_simple_list: exprlist -> typelist -> list val -> Prop :=
  | esrl_nil:
      eval_simple_list Enil Tnil nil
  | esrl_cons: forall r rl ty tyl v vl v',
      eval_simple_rvalue r v' -> cast v' (typeof r) ty v ->
      eval_simple_list rl tyl vl ->
      eval_simple_list (Econs r rl) (Tcons ty tyl) (v :: vl).

Scheme eval_simple_rvalue_ind2 := Minimality for eval_simple_rvalue Sort Prop
  with eval_simple_lvalue_ind2 := Minimality for eval_simple_lvalue Sort Prop.
Combined Scheme eval_simple_rvalue_lvalue_ind from eval_simple_rvalue_ind2, eval_simple_lvalue_ind2.

End SIMPLE_EXPRS.

(** Left reduction contexts. These contexts allow reducing to the right
  of a binary operator only if the left subexpression is simple. *)

Inductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
  | lctx_top: forall k,
      leftcontext k k (fun x => x)
  | lctx_deref: forall k C ty,
      leftcontext k RV C -> leftcontext k LV (fun x => Ederef (C x) ty)
  | lctx_field: forall k C f ty,
      leftcontext k LV C -> leftcontext k LV (fun x => Efield (C x) f ty)
  | lctx_rvalof: forall k C ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Evalof (C x) ty)
  | lctx_addrof: forall k C ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Eaddrof (C x) ty)
  | lctx_unop: forall k C op ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Eunop op (C x) ty)
  | lctx_binop_left: forall k C op e2 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Ebinop op (C x) e2 ty)
  | lctx_binop_right: forall k C op e1 ty,
      simple e1 -> leftcontext k RV C ->
      leftcontext k RV (fun x => Ebinop op e1 (C x) ty)
  | lctx_cast: forall k C ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Ecast (C x) ty)
  | lctx_condition: forall k C r2 r3 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Econdition (C x) r2 r3 ty)
  | lctx_assign_left: forall k C e2 ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Eassign (C x) e2 ty)
  | lctx_assign_right: forall k C e1 ty,
      simple e1 -> leftcontext k RV C ->
      leftcontext k RV (fun x => Eassign e1 (C x) ty)
  | lctx_assignop_left: forall k C op e2 tyres ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Eassignop op (C x) e2 tyres ty)
  | lctx_assignop_right: forall k C op e1 tyres ty,
      simple e1 -> leftcontext k RV C ->
      leftcontext k RV (fun x => Eassignop op e1 (C x) tyres ty)
  | lctx_postincr: forall k C id ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Epostincr id (C x) ty)
  | lctx_call_left: forall k C el ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Ecall (C x) el ty)
  | lctx_call_right: forall k C e1 ty,
      simple e1 -> leftcontextlist k C ->
      leftcontext k RV (fun x => Ecall e1 (C x) ty)
  | lctx_comma: forall k C e2 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Ecomma (C x) e2 ty)
  | lctx_paren: forall k C ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Eparen (C x) ty)

with leftcontextlist: kind -> (expr -> exprlist) -> Prop :=
  | lctx_list_head: forall k C el,
      leftcontext k RV C -> leftcontextlist k (fun x => Econs (C x) el)
  | lctx_list_tail: forall k C e1,
      simple e1 -> leftcontextlist k C ->
      leftcontextlist k (fun x => Econs e1 (C x)).

Lemma leftcontext_context:
  forall k1 k2 C, leftcontext k1 k2 C -> context k1 k2 C
with leftcontextlist_contextlist:
  forall k C, leftcontextlist k C -> contextlist k C.
Proof.
  induction 1; constructor; auto.
  induction 1; constructor; auto.
Qed.

Hint Resolve leftcontext_context.

(** Strategy for reducing expressions. We reduce the leftmost innermost
  non-simple subexpression, evaluating its arguments (which are necessarily
  simple expressions) with the big-step semantics.
  If there are none, the whole expression is simple and is evaluated in
  one big step. *)

Inductive estep: state -> trace -> state -> Prop :=

  | step_expr: forall f r k e m v ty,
      eval_simple_rvalue e m r v ->
      match r with Eval _ _ => False | _ => True end ->
      ty = typeof r ->
      estep (ExprState f r k e m)
         E0 (ExprState f (Eval v ty) k e m)

  | step_condition_true: forall f C r1 r2 r3 ty k e m v,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r1 v ->
      is_true v (typeof r1) ->
      typeof r2 = ty ->
      estep (ExprState f (C (Econdition r1 r2 r3 ty)) k e m)
         E0 (ExprState f (C (Eparen r2 ty)) k e m)

  | step_condition_false: forall f C r1 r2 r3 ty k e m v,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r1 v ->
      is_false v (typeof r1) ->
      typeof r3 = ty ->
      estep (ExprState f (C (Econdition r1 r2 r3 ty)) k e m)
         E0 (ExprState f (C (Eparen r3 ty)) k e m)

  | step_assign: forall f C l r ty k e m b ofs v v' m',
      leftcontext RV RV C ->
      eval_simple_lvalue e m l b ofs ->
      eval_simple_rvalue e m r v ->
      cast v (typeof r) (typeof l) v' ->
      store_value_of_type (typeof l) m b ofs v' = Some m' ->
      ty = typeof l ->
      estep (ExprState f (C (Eassign l r ty)) k e m)
         E0 (ExprState f (C (Eval v' ty)) k e m')

  | step_assignop: forall f C op l r tyres ty k e m b ofs v1 v2 v3 v4 m',
      leftcontext RV RV C ->
      eval_simple_lvalue e m l b ofs ->
      load_value_of_type (typeof l) m b ofs = Some v1 ->
      eval_simple_rvalue e m r v2 ->
      sem_binary_operation op v1 (typeof l) v2 (typeof r) m = Some v3 ->
      cast v3 tyres (typeof l) v4 ->
      store_value_of_type (typeof l) m b ofs v4 = Some m' ->
      ty = typeof l ->
      estep (ExprState f (C (Eassignop op l r tyres ty)) k e m)
         E0 (ExprState f (C (Eval v4 ty)) k e m')

  | step_postincr: forall f C id l ty k e m b ofs v1 v2 v3 m',
      leftcontext RV RV C ->
      eval_simple_lvalue e m l b ofs ->
      load_value_of_type ty m b ofs = Some v1 ->
      sem_incrdecr id v1 ty = Some v2 ->
      cast v2 (typeconv ty) ty v3 ->
      store_value_of_type ty m b ofs v3 = Some m' ->
      ty = typeof l ->
      estep (ExprState f (C (Epostincr id l ty)) k e m)
         E0 (ExprState f (C (Eval v1 ty)) k e m')

  | step_comma: forall f C r1 r2 ty k e m v,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r1 v ->
      ty = typeof r2 ->
      estep (ExprState f (C (Ecomma r1 r2 ty)) k e m)
         E0 (ExprState f (C r2) k e m)

  | step_paren: forall f C r ty k e m v,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r v ->
      ty = typeof r ->
      estep (ExprState f (C (Eparen r ty)) k e m)
         E0 (ExprState f (C (Eval v ty)) k e m)

  | step_call: forall f C rf rargs ty k e m targs tres vf vargs fd,
      leftcontext RV RV C ->
      typeof rf = Tfunction targs tres ->
      eval_simple_rvalue e m rf vf ->
      eval_simple_list e m rargs targs vargs ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction targs tres ->
      estep (ExprState f (C (Ecall rf rargs ty)) k e m)
         E0 (Callstate fd vargs (Kcall f e C ty k) m).

Definition step (S: state) (t: trace) (S': state) : Prop :=
  estep S t S' \/ sstep ge S t S'.

(** * Safe executions. *)

(** A C program is safe (in the nondeterministic strategy) 
  if it cannot get stuck.  The definition is parameterized by
  an external world (cf. file [Determinism]) to constrain the behavior
  of external functions. *)

Inductive immsafe: world -> state -> Prop :=
  | immsafe_final: forall w s r,
      final_state s r ->
      immsafe w s
  | immsafe_step: forall w s t s' w',
      Csem.step ge s t s' -> possible_trace w t w' ->
      immsafe w s.

Definition safe (w: world) (s: Csem.state) : Prop :=
  forall t s' w', star Csem.step ge s t s' -> possible_trace w t w' -> immsafe w' s'.

Lemma safe_steps:
  forall w s t s' w',
  safe w s -> star Csem.step ge s t s' -> possible_trace w t w' -> safe w' s'.
Proof.
  intros; red; intros. 
  eapply H. eapply star_trans; eauto. eapply possible_trace_app; eauto.
Qed.

Lemma safe_imm:
  forall w s, safe w s -> immsafe w s.
Proof.
  intros. eapply H. apply star_refl. constructor.
Qed.

Lemma not_stuck_val:
  forall e v ty m,
  not_stuck ge e (Eval v ty) m.
Proof.
  intros; red; intros. inv H; try congruence. subst e'. constructor.
Qed.

Lemma safe_not_stuck:
  forall w f a k e m,
  safe w (ExprState f a k e m) ->
  not_stuck ge e a m.
Proof.
  intros. exploit safe_imm; eauto; intro IS; inv IS. 
  inv H0.
  inv H0. inv H2; auto; apply not_stuck_val. inv H2; apply not_stuck_val.
Qed.

Lemma safe_not_imm_stuck:
  forall k C w f a K e m,
  safe w (ExprState f (C a) K e m) ->
  context k RV C ->
  not_imm_stuck ge e k a m.
Proof.
  intros. exploit safe_not_stuck; eauto.
Qed.

(** Simple, non-stuck expressions are well-formed with respect to
    l-values and r-values. *)

Lemma context_compose:
  forall k2 k3 C2, context k2 k3 C2 ->
  forall k1 C1, context k1 k2 C1 ->
  context k1 k3 (fun x => C2(C1 x))
with contextlist_compose:
  forall k2 C2, contextlist k2 C2 ->
  forall k1 C1, context k1 k2 C1 ->
  contextlist k1 (fun x => C2(C1 x)).
Proof.
  induction 1; intros; try (constructor; eauto).
  replace (fun x => C1 x) with C1. auto. apply extensionality; auto.
  induction 1; intros; constructor; eauto.
Qed.

Definition expr_kind (a: expr) : kind :=
  match a with
  | Eloc _ _ _ => LV
  | Evar _ _ => LV
  | Ederef _ _ => LV
  | Efield _ _ _ => LV
  | _ => RV
  end.

Lemma lred_kind:
  forall e a m a' m', lred ge e a m a' m' -> expr_kind a = LV.
Proof.
  induction 1; auto.
Qed.

Lemma rred_kind:
  forall a m a' m', rred a m a' m' -> expr_kind a = RV.
Proof.
  induction 1; auto.
Qed.

Lemma callred_kind:
  forall a fd args ty, callred ge a fd args ty -> expr_kind a = RV.
Proof.
  induction 1; auto.
Qed.

Lemma context_kind:
  forall a from to C, context from to C -> expr_kind a = from -> expr_kind (C a) = to.
Proof.
  induction 1; intros; simpl; auto.
Qed.

Lemma not_imm_stuck_kind:
  forall e k a m, not_imm_stuck ge e k a m -> expr_kind a = k.
Proof.
  induction 1.
  auto.
  auto.
  eapply context_kind; eauto. eapply lred_kind; eauto.
  eapply context_kind; eauto. eapply rred_kind; eauto.
  eapply context_kind; eauto. eapply callred_kind; eauto.
Qed.

Lemma safe_expr_kind:
  forall from C w f a k e m,
  context from RV C ->
  safe w (ExprState f (C a) k e m) ->
  expr_kind a = from.
Proof.
  intros. eapply not_imm_stuck_kind. eapply safe_not_imm_stuck; eauto.
Qed.

(** Painful inversion lemmas on particular states that are not stuck. *)

Section INVERSION_LEMMAS.

Variable e: env.

Fixpoint exprlist_all_values (rl: exprlist) : Prop :=
  match rl with
  | Enil => True
  | Econs (Eval v ty) rl' => exprlist_all_values rl'
  | Econs _ _ => False
  end.

Definition invert_expr_prop (a: expr) (m: mem) : Prop :=
  match a with
  | Eloc b ofs ty => False
  | Evar x ty =>
      exists b,
      e!x = Some(b, ty)
      \/ (e!x = None /\ Genv.find_symbol ge x = Some b /\ type_of_global ge b = Some ty)
  | Ederef (Eval v ty1) ty =>
      exists b, exists ofs, v = Vptr b ofs
  | Efield (Eloc b ofs ty1) f ty =>
      match ty1 with
      | Tstruct _ fList => exists delta, field_offset f fList = Errors.OK delta
      | Tunion _ _ => True
      | _ => False
      end
  | Eval v ty => False
  | Evalof (Eloc b ofs ty') ty =>
      ty' = ty /\ exists v, load_value_of_type ty m b ofs = Some v
  | Eunop op (Eval v1 ty1) ty =>
      exists v, sem_unary_operation op v1 ty1 = Some v
  | Ebinop op (Eval v1 ty1) (Eval v2 ty2) ty =>
      exists v, sem_binary_operation op v1 ty1 v2 ty2 m = Some v
  | Ecast (Eval v1 ty1) ty =>
      exists v, cast v1 ty1 ty v
  | Econdition (Eval v1 ty1) r1 r2 ty =>
      ((is_true v1 ty1 /\ typeof r1 = ty) \/ (is_false v1 ty1 /\ typeof r2 = ty))
  | Eassign (Eloc b ofs ty1) (Eval v2 ty2) ty =>
      exists v, exists m',
      ty = ty1 /\ cast v2 ty2 ty1 v /\ store_value_of_type ty1 m b ofs v = Some m'
  | Eassignop op (Eloc b ofs ty1) (Eval v2 ty2) tyres ty =>
      exists v1, exists v, exists v', exists m',
      ty = ty1 
      /\ load_value_of_type ty1 m b ofs = Some v1
      /\ sem_binary_operation op v1 ty1 v2 ty2 m = Some v
      /\ cast v tyres ty1 v'
      /\ store_value_of_type ty1 m b ofs v' = Some m'
  | Epostincr id (Eloc b ofs ty1) ty =>
      exists v1, exists v2, exists v3, exists m',
      ty = ty1
      /\ load_value_of_type ty m b ofs = Some v1
      /\ sem_incrdecr id v1 ty = Some v2
      /\ cast v2 (typeconv ty) ty v3
      /\ store_value_of_type ty m b ofs v3 = Some m'
  | Ecomma (Eval v ty1) r2 ty =>
      typeof r2 = ty
  | Eparen (Eval v ty1) ty =>
      ty = ty1
  | Ecall (Eval vf tyf) rargs ty =>
      exprlist_all_values rargs ->
      exists tyargs, exists tyres, exists fd, exists vl,
         tyf = Tfunction tyargs tyres
      /\ Genv.find_funct ge vf = Some fd
      /\ cast_arguments rargs tyargs vl
      /\ type_of_fundef fd = Tfunction tyargs tyres
  | _ => True
  end.

Lemma lred_invert:
  forall l m l' m', lred ge e l m l' m' -> invert_expr_prop l m.
Proof.
  induction 1; red; auto.
  exists b; auto.
  exists b; auto.
  exists b; exists ofs; auto.
  exists delta; auto.
Qed.

Lemma rred_invert:
  forall r m r' m', rred r m r' m' -> invert_expr_prop r m.
Proof.
  induction 1; red; auto.
  split; auto; exists v; auto.
  exists v; auto.
  exists v; auto.
  exists v; auto.
  exists v; exists m'; auto.
  exists v1; exists v; exists v'; exists m'; auto.
  exists v1; exists v2; exists v3; exists m'; auto.
  destruct r; auto.
Qed.

Lemma callred_invert:
  forall r fd args ty m,
  callred ge r fd args ty ->
  invert_expr_prop r m.
Proof.
  intros. inv H. simpl.
  intros. exists tyargs; exists tyres; exists fd; exists args; auto.
Qed.

Scheme context_ind2 := Minimality for context Sort Prop
  with contextlist_ind2 := Minimality for contextlist Sort Prop.
Combined Scheme context_contextlist_ind from context_ind2, contextlist_ind2.

Lemma invert_expr_context:
  (forall from to C, context from to C ->
   forall a m,
   invert_expr_prop a m ->
   invert_expr_prop (C a) m)
/\(forall from C, contextlist from C ->
  forall a m,
  invert_expr_prop a m ->
  ~exprlist_all_values (C a)).
Proof.
  apply context_contextlist_ind; intros; try (exploit H0; [eauto|intros]).
  auto.
  simpl. destruct (C a); auto. contradiction.
  simpl. destruct (C a); auto. contradiction. 
  simpl. destruct (C a); auto. contradiction. 
  simpl. auto.
  simpl. destruct (C a); auto. contradiction. 
  simpl. destruct (C a); auto. contradiction. 
  simpl.
    destruct e1; auto. destruct (C a); auto. contradiction.
  simpl. destruct (C a); auto. contradiction.
  simpl. destruct (C a); auto. contradiction.
  simpl. destruct (C a); auto. contradiction.
  simpl.
    destruct e1; auto. destruct (C a); auto. contradiction.
  simpl. destruct (C a); auto. contradiction.
  simpl.
    destruct e1; auto. destruct (C a); auto. contradiction.
  simpl. destruct (C a); auto. contradiction.
  simpl. destruct (C a); auto. contradiction.
  simpl. destruct e1; auto. intros. elim (H0 a m); auto.   
  simpl. destruct (C a); auto. contradiction. 
  simpl. destruct (C a); auto. contradiction.
  simpl. red; intros. destruct (C a); auto. 
  simpl; red; intros. destruct e1; auto. elim (H0 a m); auto. 
Qed.

Lemma not_imm_stuck_inv:
  forall k a m,
  not_imm_stuck ge e k a m ->
  match a with
  | Eloc _ _ _ => True
  | Eval _ _ => True
  | _ => invert_expr_prop a m
  end.
Proof.
  destruct invert_expr_context as [A B].
  intros. inv H. 
  auto.
  auto.
  assert (invert_expr_prop (C e0) m).
    eapply A; eauto. eapply lred_invert; eauto.
  red in H. destruct (C e0); auto; contradiction.
  assert (invert_expr_prop (C e0) m).
    eapply A; eauto. eapply rred_invert; eauto.
  red in H. destruct (C e0); auto; contradiction.
  assert (invert_expr_prop (C e0) m).
    eapply A; eauto. eapply callred_invert; eauto.
  red in H. destruct (C e0); auto; contradiction.
Qed.

End INVERSION_LEMMAS.

(** * Correctness of the strategy. *)

Section SIMPLE_EVAL.

Variable f: function.
Variable k: cont.
Variable e: env.
Variable m: mem.
Variable w: world.

Lemma simple_eval:
  forall a from C,
  simple a -> context from RV C -> safe w (ExprState f (C a) k e m) ->
  match from with
  | LV =>
     exists b, exists ofs,
        eval_simple_lvalue e m a b ofs
     /\ star Csem.step ge (ExprState f (C a) k e m)
                       E0 (ExprState f (C (Eloc b ofs (typeof a))) k e m)
  | RV =>
     exists v,
        eval_simple_rvalue e m a v
     /\ star Csem.step ge (ExprState f (C a) k e m)
                       E0 (ExprState f (C (Eval v (typeof a))) k e m)
  end.
Proof.
  induction a; intros from C S CTX SAFE;
  generalize (safe_expr_kind _ _ _ _ _ _ _ _ CTX SAFE); intro K; subst;
  simpl in S; try contradiction; simpl.
(* val *)
  exists v; split. constructor. apply star_refl.
(* var *)
  exploit not_imm_stuck_inv. eapply safe_not_imm_stuck; eauto.
  simpl. intros [b A].
  exists b; exists Int.zero; split.
  intuition. apply esl_var_local; auto. apply esl_var_global; auto.
  apply star_one. left; apply step_lred.
  intuition. apply red_var_local; auto. apply red_var_global; auto. 
  eapply safe_not_stuck; eauto. auto.
(* field *)
  set (C1 := fun x => Efield x f0 ty).
  set (C2 := fun x => C(C1 x)).
  exploit (IHa LV C2); auto. eapply context_compose; eauto. repeat constructor.
  unfold C2, C1; intros [b [ofs [A B]]].
  exploit not_imm_stuck_inv.
    eapply safe_not_imm_stuck. eapply safe_steps; eauto. constructor. eauto.
  simpl. 
  case_eq (typeof a); intros; try contradiction.
  destruct H0 as [delta EQ]. 
  exists b; econstructor; split.
  eapply esl_field_struct; eauto.
  eapply star_right. eauto. left; apply step_lred.
  rewrite H. constructor; auto.
  eapply safe_not_stuck. eapply safe_steps; eauto. constructor. auto.
  traceEq.
  exists b; exists ofs; split.
  eapply esl_field_union; eauto.
  eapply star_right. eauto. left; apply step_lred.
  rewrite H. constructor; auto.
  eapply safe_not_stuck. eapply safe_steps; eauto. constructor. auto.
  traceEq.
(* valof *)
  set (C1 := fun x => Evalof x ty).
  set (C2 := fun x => C(C1 x)).
  exploit (IHa LV C2); auto. eapply context_compose; eauto. repeat constructor.
  unfold C2, C1; intros [b [ofs [A B]]].
  exploit not_imm_stuck_inv.
    eapply safe_not_imm_stuck. eapply safe_steps; eauto. constructor. eauto. 
  simpl. intros [D [v E]].
  exists v; split.
  econstructor; eauto.
  eapply star_right. eauto. left; apply step_rred.
  simpl. rewrite D. constructor. auto. 
  eapply safe_not_stuck. eapply safe_steps; eauto. constructor. auto.
  traceEq.
(* deref *)
  set (C1 := fun x => Ederef x ty).
  set (C2 := fun x => C(C1 x)).
  exploit (IHa RV C2); auto. eapply context_compose; eauto. repeat constructor.
  unfold C2, C1; intros [v1 [A B]].
  exploit not_imm_stuck_inv.
    eapply safe_not_imm_stuck. eapply safe_steps; eauto. constructor. eauto.
  simpl. intros [b [ofs D]]. subst v1. 
  exists b; exists ofs; split.
  econstructor; eauto. 
  eapply star_right. eauto. left; apply step_lred.
  simpl. constructor.
  eapply safe_not_stuck. eapply safe_steps; eauto. constructor. auto.
  traceEq.
(* addrof *)
  set (C1 := fun x => Eaddrof x ty).
  set (C2 := fun x => C(C1 x)).
  exploit (IHa LV C2); auto. eapply context_compose; eauto. repeat constructor.
  unfold C2, C1; intros [b [ofs [A B]]].
  exists (Vptr b ofs); split.
  econstructor; eauto.
  eapply star_right. eauto. left; apply step_rred.
  simpl. constructor. 
  eapply safe_not_stuck. eapply safe_steps; eauto. constructor. auto.
  traceEq.
(* unop *)
  set (C1 := fun x => Eunop op x ty).
  set (C2 := fun x => C(C1 x)).
  exploit (IHa RV C2); auto. eapply context_compose; eauto. repeat constructor.
  unfold C2, C1; intros [v1 [A B]].
  exploit not_imm_stuck_inv.
    eapply safe_not_imm_stuck. eapply safe_steps; eauto. constructor. eauto.
  simpl. intros [v E].
  exists v; split.
  econstructor; eauto.
  eapply star_right. eauto. left; apply step_rred.
  simpl. constructor. auto. 
  eapply safe_not_stuck. eapply safe_steps; eauto. constructor. auto.
  traceEq.
(* binop *)
  set (C1 := fun x => Ebinop op x a2 ty).
  set (C2 := fun x => C(C1 x)).
  exploit (IHa1 RV C2). tauto. eapply context_compose; eauto. repeat constructor. auto.
  unfold C2, C1; intros [v1 [A B]].
  assert (safe w (ExprState f (C (Ebinop op (Eval v1 (typeof a1)) a2 ty)) k e m)).
    eapply safe_steps; eauto. constructor.
  set (C3 := fun x => Ebinop op (Eval v1 (typeof a1)) x ty).
  set (C4 := fun x => C(C3 x)).
  exploit (IHa2 RV C4). tauto. eapply context_compose; eauto. repeat constructor. auto.
  unfold C4, C3; intros [v2 [D E]].
  assert (safe w (ExprState f (C (Ebinop op (Eval v1 (typeof a1)) (Eval v2 (typeof a2)) ty)) k e m)).
    eapply safe_steps; eauto. constructor.
  exploit not_imm_stuck_inv.
    eapply safe_not_imm_stuck. eexact H0. eauto. 
  simpl. intros [v F].
  exists v; split.
  econstructor; eauto.
  eapply star_right. eapply star_trans; eauto. left; apply step_rred.
  simpl. constructor. auto. 
  eapply safe_not_stuck. eauto.
  auto.
  traceEq.
(* cast *)
  set (C1 := fun x => Ecast x ty).
  set (C2 := fun x => C(C1 x)).
  exploit (IHa RV C2); auto. eapply context_compose; eauto. repeat constructor.
  unfold C2, C1; intros [v1 [A B]].
  exploit not_imm_stuck_inv.
    eapply safe_not_imm_stuck. eapply safe_steps; eauto. constructor. eauto.
  simpl. intros [v E].
  exists v; split.
  econstructor; eauto.
  eapply star_right. eauto. left; apply step_rred.
  simpl. constructor. auto. 
  eapply safe_not_stuck. eapply safe_steps; eauto. constructor. auto.
  traceEq.
(* sizeof *)
  econstructor; split. constructor. 
  apply star_one. left; apply step_rred. constructor. 
  eapply safe_not_stuck; eauto.
  auto.
(* loc *)
  exploit not_imm_stuck_inv. eapply safe_not_imm_stuck; eauto.
  simpl. intros.
  exists b; exists ofs; split. constructor. apply star_refl.
Qed.

Lemma simple_eval_r:
   forall r C, 
   simple r -> context RV RV C -> safe w (ExprState f (C r) k e m) ->
   exists v,
      eval_simple_rvalue e m r v
   /\ star Csem.step ge (ExprState f (C r) k e m)
                     E0 (ExprState f (C (Eval v (typeof r))) k e m).
Proof.
  intros. apply (simple_eval r RV); auto.
Qed.

Lemma simple_eval_l:
   forall l C,
   simple l -> context LV RV C -> safe w (ExprState f (C l) k e m) ->
   exists b, exists ofs,
      eval_simple_lvalue e m l b ofs
   /\ star Csem.step ge (ExprState f (C l) k e m)
                     E0 (ExprState f (C (Eloc b ofs (typeof l))) k e m).
Proof.
  intros. apply (simple_eval l LV); auto.
Qed.

Fixpoint rval_list (vl: list val) (rl: exprlist) : exprlist :=
  match vl, rl with
  | v1 :: vl', Econs r1 rl' => Econs (Eval v1 (typeof r1)) (rval_list vl' rl')
  | _, _ => Enil
  end.

Inductive eval_simple_list': exprlist -> list val -> Prop :=
  | esrl'_nil:
      eval_simple_list' Enil nil
  | esrl'_cons: forall r rl v vl,
      eval_simple_rvalue e m r v ->
      eval_simple_list' rl vl ->
      eval_simple_list' (Econs r rl) (v :: vl).

Fixpoint exprlist_app (rl1 rl2: exprlist) : exprlist :=
  match rl1 with
  | Enil => rl2
  | Econs r1 rl1' => Econs r1 (exprlist_app rl1' rl2)
  end.

Lemma exprlist_app_assoc:
  forall rl2 rl3 rl1,
  exprlist_app (exprlist_app rl1 rl2) rl3 =
  exprlist_app rl1 (exprlist_app rl2 rl3).
Proof.
  induction rl1; auto. simpl. congruence. 
Qed.

Inductive contextlist' : (exprlist -> expr) -> Prop :=
  | contextlist'_intro: forall r1 rl0 ty C,
      context RV RV C ->
      contextlist' (fun rl => C (Ecall r1 (exprlist_app rl0 rl) ty)).

Lemma exprlist_app_context:
  forall rl1 rl2,
  contextlist RV (fun x => exprlist_app rl1 (Econs x rl2)).
Proof.
  induction rl1; simpl; intros. 
  apply ctx_list_head. constructor.
  apply ctx_list_tail. auto. 
Qed.

Lemma contextlist'_head:
  forall rl C,
  contextlist' C ->
  context RV RV (fun x => C (Econs x rl)).
Proof.
  intros. inv H. 
  set (C' := fun x => Ecall r1 (exprlist_app rl0 (Econs x rl)) ty).
  assert (context RV RV C'). constructor. apply exprlist_app_context.
  change (context RV RV (fun x => C0 (C' x))). 
  eapply context_compose; eauto.
Qed.

Lemma contextlist'_tail:
  forall r1 C,
  contextlist' C ->
  contextlist' (fun x => C (Econs r1 x)).
Proof.
  intros. inv H. 
  replace (fun x => C0 (Ecall r0 (exprlist_app rl0 (Econs r1 x)) ty))
     with (fun x => C0 (Ecall r0 (exprlist_app (exprlist_app rl0 (Econs r1 Enil)) x) ty)).
  constructor. auto. 
  apply extensionality; intros. f_equal. f_equal. apply exprlist_app_assoc.
Qed.

Lemma simple_eval_rlist:
  forall rl C,
  simplelist rl ->
  contextlist' C ->
  safe w (ExprState f (C rl) k e m) ->
  exists vl,
  eval_simple_list' rl vl
  /\ star Csem.step ge (ExprState f (C rl) k e m)
                       E0 (ExprState f (C (rval_list vl rl)) k e m).
Proof.
  induction rl; intros. 
  econstructor; split. constructor. simpl. apply star_refl.
  simpl in H; destruct H.
  set (C1 := fun x => C (Econs x rl)). 
  exploit (simple_eval_r r1 C1). auto. apply contextlist'_head. auto. auto.
  unfold C1; intros [v [X Y]].
  assert (safe w (ExprState f (C (Econs (Eval v (typeof r1)) rl)) k e m)).
    eapply safe_steps; eauto. constructor.
  set (C2 := fun x => C (Econs (Eval v (typeof r1)) x)). 
  destruct (IHrl C2) as [vl [U V]]. auto. apply contextlist'_tail. auto. auto.
  unfold C2 in V.
  exists (v :: vl); split. constructor; auto.
  simpl. eapply star_trans; eauto.
Qed.

Lemma rval_list_all_values:
  forall vl rl, exprlist_all_values (rval_list vl rl).
Proof.
  induction vl; simpl; intros. auto. 
  destruct rl; simpl; auto.
Qed.

Lemma can_eval_simple_list:
  forall rl vl,
  eval_simple_list' rl vl ->
  forall tyl vl',
  cast_arguments (rval_list vl rl) tyl vl' ->
  eval_simple_list e m rl tyl vl'.
Proof.
  induction 1; simpl; intros. 
  inv H. constructor.
  inv H1. econstructor; eauto. 
Qed.

End SIMPLE_EVAL.

(** Decomposition *)

Section DECOMPOSITION.

Variable f: function.
Variable k: cont.
Variable e: env.
Variable m: mem.
Variable w: world.

Definition simple_side_effect (r: expr) : Prop :=
  match r with
  | Econdition r1 r2 r3 ty => simple r1
  | Eassign l1 r2 _ => simple l1 /\ simple r2
  | Eassignop _ l1 r2 _ _ => simple l1 /\ simple r2
  | Epostincr _ l1 _ => simple l1
  | Ecomma r1 r2 _ => simple r1
  | Ecall r1 rl _ => simple r1 /\ simplelist rl
  | Eparen r1 _ => simple r1
  | _ => False
  end.

Scheme expr_ind2 := Induction for expr Sort Prop
  with exprlist_ind2 := Induction for exprlist Sort Prop.
Combined Scheme expr_expr_list_ind from expr_ind2, exprlist_ind2.

Lemma decompose_expr:
  (forall a from C,
   context from RV C -> safe w (ExprState f (C a) k e m) ->
       simple a
    \/ exists C', exists a', simple_side_effect a' /\ leftcontext RV from C' /\ a = C' a')
/\(forall rl C,
   contextlist' C -> safe w (ExprState f (C rl) k e m) ->
       simplelist rl
    \/ exists C', exists a', simple_side_effect a' /\ leftcontextlist RV C' /\ rl = C' a').
Proof.
  apply expr_expr_list_ind; intros; simpl; auto.
(* field *)
  exploit safe_expr_kind; eauto; simpl; intros. subst.
  destruct (H LV (fun x => C (Efield x f0 ty))) as [A | [C' [a' [A [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto.
  auto.
  right; exists (fun x => Efield (C' x) f0 ty); exists a'.
  split. auto. split. constructor; auto. rewrite D; auto.
(* rvalof *)
  exploit safe_expr_kind; eauto; simpl; intros. subst.
  destruct (H LV (fun x => C (Evalof x ty))) as [A | [C' [a' [A [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto.
  auto.
  right; exists (fun x => Evalof (C' x) ty); exists a'.
  split. auto. split. constructor; auto. rewrite D; auto.
(* deref *)
  exploit safe_expr_kind; eauto; simpl; intros. subst.
  subst. destruct (H RV (fun x => C (Ederef x ty))) as [A | [C' [a' [A [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto.
  auto.
  right; exists (fun x => Ederef (C' x) ty); exists a'.
  split. auto. split. constructor; auto. rewrite D; auto.
(* addrof *)
  exploit safe_expr_kind; eauto; simpl; intros. subst.
  destruct (H LV (fun x => C (Eaddrof x ty))) as [A | [C' [a' [A [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto.
  auto.
  right; exists (fun x => Eaddrof (C' x) ty); exists a'.
  split. auto. split. constructor; auto. rewrite D; auto.
(* unop *)
  exploit safe_expr_kind; eauto; simpl; intros. subst.
  destruct (H RV (fun x => C (Eunop op x ty))) as [A | [C' [a' [A [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto.
  auto.
  right; exists (fun x => Eunop op (C' x) ty); exists a'.
  split. auto. split. constructor; auto. rewrite D; auto.
(* binop *)
  exploit safe_expr_kind; eauto; simpl; intros. subst.
  destruct (H RV (fun x => C (Ebinop op x r2 ty))) as [A | [C' [a' [A [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto.
  destruct (H0 RV (fun x => C (Ebinop op r1 x ty))) as [A' | [C' [a' [A' [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto.
  auto.
  right; exists (fun x => Ebinop op r1 (C' x) ty); exists a'. 
  split. auto. split. constructor; auto. rewrite D; auto.
  right; exists (fun x => Ebinop op (C' x) r2 ty); exists a'. 
  split. auto. split. constructor; auto. rewrite D; auto.
(* cast *)
  exploit safe_expr_kind; eauto; simpl; intros. subst.
  destruct (H RV (fun x => C (Ecast x ty))) as [A | [C' [a' [A [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto.
  auto.
  right; exists (fun x => Ecast (C' x) ty); exists a'.
  split. auto. split. constructor; auto. rewrite D; auto.
(* condition *)
  exploit safe_expr_kind; eauto; simpl; intros. subst.
  destruct (H RV (fun x => C(Econdition x r2 r3 ty))) as [A | [C' [a' [A [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto.
  right. exists (fun x => x); exists (Econdition r1 r2 r3 ty).
  split. red; auto. split. constructor. auto.
  right; exists (fun x => Econdition (C' x) r2 r3 ty); exists a'. 
  split. auto. split. constructor; auto. rewrite D; auto.
(* assign *)
  exploit safe_expr_kind; eauto; simpl; intros. subst.
  destruct (H LV (fun x => C (Eassign x r ty))) as [A | [C' [a' [A [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto.
  destruct (H0 RV (fun x => C (Eassign l x ty))) as [A' | [C' [a' [A' [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto.
  right. exists (fun x => x); exists (Eassign l r ty).
  split. red; auto. split. constructor. auto.
  right; exists (fun x => Eassign l (C' x) ty); exists a'. 
  split. auto. split. constructor; auto. rewrite D; auto.
  right; exists (fun x => Eassign (C' x) r ty); exists a'. 
  split. auto. split. constructor; auto. rewrite D; auto.
(* assignop *)
  exploit safe_expr_kind; eauto; simpl; intros. subst.
  destruct (H LV (fun x => C (Eassignop op x r tyres ty))) as [A | [C' [a' [A [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto.
  destruct (H0 RV (fun x => C (Eassignop op l x tyres ty))) as [A' | [C' [a' [A' [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto.
  right. exists (fun x => x); exists (Eassignop op l r tyres ty).
  split. red; auto. split. constructor. auto.
  right; exists (fun x => Eassignop op l (C' x) tyres ty); exists a'. 
  split. auto. split. constructor; auto. rewrite D; auto.
  right; exists (fun x => Eassignop op (C' x) r tyres ty); exists a'. 
  split. auto. split. constructor; auto. rewrite D; auto.
(* postincr *)
  exploit safe_expr_kind; eauto; simpl; intros. subst.
  destruct (H LV (fun x => C(Epostincr id x ty))) as [A | [C' [a' [A [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto. 
  right. exists (fun x => x); exists (Epostincr id l ty).
  split. red; auto. split. constructor. auto.
  right; exists (fun x => Epostincr id (C' x) ty); exists a'. 
  split. auto. split. econstructor; eauto. rewrite D; auto.
(* comma *)
  exploit safe_expr_kind; eauto; simpl; intros. subst.
  destruct (H RV (fun x => C(Ecomma x r2 ty))) as [A | [C' [a' [A [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto. 
  right. exists (fun x => x); exists (Ecomma r1 r2 ty).
  split. red; auto. split. constructor. auto.
  right; exists (fun x => Ecomma (C' x) r2 ty); exists a'. 
  split. auto. split. econstructor; eauto. rewrite D; auto.
(* call *)
  exploit safe_expr_kind; eauto; simpl; intros. subst.
  destruct (H RV (fun x => C (Ecall x rargs ty))) as [A | [C' [a' [A [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto.
  destruct (H0 (fun x => C (Ecall r1 x ty))) as [A' | [C' [a' [A' [B D]]]]].
    eapply contextlist'_intro with (C := C) (rl0 := Enil). auto. auto.
  right. exists (fun x => x); exists (Ecall r1 rargs ty).
  split. red; auto. split. constructor. auto.
  right; exists (fun x => Ecall r1 (C' x) ty); exists a'. 
  split. auto. split. constructor; auto. rewrite D; auto.
  right; exists (fun x => Ecall (C' x) rargs ty); exists a'.
  split. auto. split. constructor; auto. rewrite D; auto.
(* rparen *)
  exploit safe_expr_kind; eauto; simpl; intros. subst.
  destruct (H RV (fun x => C (Eparen x ty))) as [A | [C' [a' [A [B D]]]]].
    eapply context_compose; eauto. repeat constructor. auto.
  right. exists (fun x => x); exists (Eparen r ty).
  split. red; auto. split. constructor. auto.
  right; exists (fun x => Eparen (C' x) ty); exists a'. 
  split. auto. split. econstructor; eauto. rewrite D; auto.
(* cons *)
  destruct (H RV (fun x => C (Econs x rl))) as [A | [C' [a' [A [B D]]]]].
    eapply contextlist'_head; eauto. auto.
  destruct (H0 (fun x => C (Econs r1 x))) as [A' | [C' [a' [A' [B D]]]]].
    eapply contextlist'_tail; eauto. auto. 
  auto.
  right; exists (fun x => Econs r1 (C' x)); exists a'. 
  split. auto. split. constructor; auto. rewrite D; auto.
  right; exists (fun x => Econs (C' x) rl); exists a'. 
  split. auto. split. constructor; auto. rewrite D; auto.
Qed.

Lemma decompose_topexpr:
  forall a,
  safe w (ExprState f a k e m) ->
       simple a
    \/ exists C, exists a', simple_side_effect a' /\ leftcontext RV RV C /\ a = C a'.
Proof.
  intros. eapply (proj1 decompose_expr). apply ctx_top. auto.
Qed.

End DECOMPOSITION.

(** Simulation for expressions. *)

Lemma can_estep:
  forall w f a k e m,
  safe w (ExprState f a k e m) ->
  match a with Eval _ _ => False | _ => True end ->
  exists S,
     estep (ExprState f a k e m) E0 S
  /\ plus Csem.step ge (ExprState f a k e m) E0 S.
Proof.
  intros. destruct (decompose_topexpr f k e m w a H) as [A | [C [b [P [Q R]]]]].
(* expr *)
  exploit (simple_eval_r f k e m w a (fun x => x)); auto. constructor.
  intros [v [S T]].
  econstructor; split. 
  eapply step_expr; eauto.
  inversion T. rewrite H2 in H0. contradiction. econstructor; eauto. 
(* side effect *)
  clear H0. subst a. red in P. destruct b; try contradiction. 
(* condition *)
  set (C1 := fun x => Econdition x b2 b3 ty).
  exploit (simple_eval_r f k e m w b1 (fun x => C(C1 x))). auto. 
    eapply context_compose; eauto. repeat constructor. auto. 
  unfold C1; intros [v [A B]].
  exploit not_imm_stuck_inv.
    eapply safe_not_imm_stuck. eapply safe_steps; eauto. constructor. eauto.
  simpl. intros [[X Y] | [X Y]].
  econstructor; split. eapply step_condition_true; eauto.
  eapply plus_right. eauto. left; eapply step_rred. constructor; auto.
  eapply safe_not_stuck. eapply safe_steps; eauto. constructor. apply leftcontext_context; auto.
  traceEq.
  econstructor; split. eapply step_condition_false; eauto.
  eapply plus_right. eauto. left; eapply step_rred. constructor; auto.
  eapply safe_not_stuck. eapply safe_steps; eauto. constructor. apply leftcontext_context; auto.
  traceEq.
(* assign *)
  destruct P.
  set (C1 := fun x => Eassign x b2 ty).
  exploit (simple_eval_l f k e m w b1 (fun x => C(C1 x))). auto. 
    eapply context_compose; eauto. repeat constructor. auto. 
  unfold C1; intros [blk [ofs [A B]]].
  assert (S1: safe w (ExprState f (C (Eassign (Eloc blk ofs (typeof b1)) b2 ty)) k e m)).
    eapply safe_steps; eauto. constructor.
  set (C2 := fun x => Eassign (Eloc blk ofs (typeof b1)) x ty).
  exploit (simple_eval_r f k e m w b2 (fun x => C(C2 x))). auto. 
    eapply context_compose; eauto. repeat constructor. auto. 
  unfold C2; intros [v [E F]].
  assert (S2: safe w (ExprState f
         (C (Eassign (Eloc blk ofs (typeof b1)) (Eval v (typeof b2)) ty)) k e
         m)).
    eapply safe_steps; eauto. constructor.
  exploit not_imm_stuck_inv. eapply safe_not_imm_stuck. eexact S2. eauto. 
  simpl. intros [v' [m' [X [Y Z]]]].
  econstructor; split.
  eapply step_assign with (C := C); eauto.
  eapply star_plus_trans. eapply star_trans; eauto. 
  apply plus_one. left. apply step_rred. rewrite X. econstructor; eauto. 
  eapply safe_not_stuck; eauto. apply leftcontext_context; auto.
  traceEq.
(* assignop *)
  destruct P.
  set (C1 := fun x => Eassignop op x b2 tyres ty).
  exploit (simple_eval_l f k e m w b1 (fun x => C(C1 x))). auto. 
    eapply context_compose; eauto. repeat constructor. auto. 
  unfold C1; intros [blk [ofs [A B]]].
  assert (S1: safe w (ExprState f (C (Eassignop op (Eloc blk ofs (typeof b1)) b2 tyres ty)) k e m)).
    eapply safe_steps; eauto. constructor.
  set (C2 := fun x => Eassignop op (Eloc blk ofs (typeof b1)) x tyres ty).
  exploit (simple_eval_r f k e m w b2 (fun x => C(C2 x))). auto. 
    eapply context_compose; eauto. repeat constructor. auto. 
  unfold C2; intros [v [E F]].
  assert (S2: safe w (ExprState f
         (C
            (Eassignop op (Eloc blk ofs (typeof b1)) (Eval v (typeof b2))
               tyres ty)) k e m)).
    eapply safe_steps; eauto. constructor.
  exploit not_imm_stuck_inv. eapply safe_not_imm_stuck. eexact S2. eauto. 
  simpl. intros [v1 [v2 [v3 [m' [U [V [W [X Y]]]]]]]].
  econstructor; split.
  eapply step_assignop with (C := C); eauto.
  eapply star_plus_trans. eapply star_trans; eauto. 
  apply plus_one. left. apply step_rred. rewrite U. econstructor; eauto.
  eapply safe_not_stuck; eauto. apply leftcontext_context; auto.
  traceEq.
(* postincr *)
  set (C1 := fun x => Epostincr id x ty).
  exploit (simple_eval_l f k e m w b (fun x => C(C1 x))). auto. 
    eapply context_compose; eauto. repeat constructor. auto. 
  unfold C1; intros [blk [ofs [A B]]].
  assert (S1: safe w (ExprState f (C (Epostincr id (Eloc blk ofs (typeof b)) ty)) k e m)).
    eapply safe_steps; eauto. constructor.
  exploit not_imm_stuck_inv. eapply safe_not_imm_stuck. eexact S1. eauto. 
  simpl. intros [v1 [v2 [v3 [m' [U [V [W [X Y]]]]]]]].
  econstructor; split.
  eapply step_postincr with (C := C); eauto.
  eapply star_plus_trans. eauto. 
  apply plus_one. left. apply step_rred. subst ty. econstructor; eauto.
  eapply safe_not_stuck; eauto. apply leftcontext_context; auto.
  traceEq.
(* comma *)
  set (C1 := fun x => Ecomma x b2 ty).
  exploit (simple_eval_r f k e m w b1 (fun x => C(C1 x))). auto. 
    eapply context_compose; eauto. repeat constructor. auto. 
  unfold C1; intros [v1 [A B]].
  assert (S1: safe w (ExprState f (C (Ecomma (Eval v1 (typeof b1)) b2 ty)) k e m)).
    eapply safe_steps; eauto. constructor.
  exploit not_imm_stuck_inv. eapply safe_not_imm_stuck. eexact S1. eauto. 
  simpl. intro X.
  econstructor; split.
  eapply step_comma with (C := C); eauto.
  eapply star_plus_trans. eauto. 
  apply plus_one. left. apply step_rred. subst ty. econstructor; eauto.
  eapply safe_not_stuck; eauto. apply leftcontext_context; auto.
  traceEq.
(* call *)
  destruct P.
  set (C1 := fun x => Ecall x rargs ty).
  exploit (simple_eval_r f k e m w b (fun x => C(C1 x))). auto. 
    eapply context_compose; eauto. repeat constructor. auto. 
  unfold C1; intros [vf [A B]].
  assert (S1: safe w (ExprState f (C (Ecall (Eval vf (typeof b)) rargs ty)) k e m)).
    eapply safe_steps; eauto. constructor.
  exploit (simple_eval_rlist f k e m w rargs (fun x => C(Ecall (Eval vf (typeof b)) x ty))).
    auto. eapply contextlist'_intro with (rl0 := Enil). auto. auto.
  intros [vl [E F]].
  assert (S2: safe w (ExprState f (C (Ecall (Eval vf (typeof b)) (rval_list vl rargs) ty))
         k e m)).
    eapply safe_steps; eauto. constructor.
  exploit not_imm_stuck_inv. eapply safe_not_imm_stuck. eexact S2. eauto. 
  simpl. intros X.
  destruct X as [tyargs [tyres [fd [vl' [U [V [W X]]]]]]].
  apply rval_list_all_values.
  econstructor; split.
  eapply step_call with (C := C); eauto. eapply can_eval_simple_list; eauto.
  eapply plus_right. eapply star_trans; eauto. 
  left. econstructor. rewrite U. econstructor; eauto. 
  eapply safe_not_stuck; eauto. apply leftcontext_context; auto.
  traceEq.
(* rparen *)
  set (C1 := fun x => Eparen x ty).
  exploit (simple_eval_r f k e m w b (fun x => C(C1 x))). auto. 
    eapply context_compose; eauto. repeat constructor. auto. 
  unfold C1; intros [v [A B]].
  assert (S1: safe w (ExprState f (C (Eparen (Eval v (typeof b)) ty)) k e m)).
    eapply safe_steps; eauto. constructor.
  exploit not_imm_stuck_inv. eapply safe_not_imm_stuck. eexact S1. eauto. 
  simpl. intros EQ. subst ty.
  econstructor; split.
  eapply step_paren with (C := C); eauto.
  eapply star_plus_trans. eauto. 
  apply plus_one. left. apply step_rred. econstructor; eauto.
  eapply safe_not_stuck; eauto. apply leftcontext_context; auto.
  traceEq.
Qed.

(** The main simulation result. *)

Theorem strategy_simulation:
  forall w S,
  safe w S ->
     (exists r, final_state S r)
  \/ (exists t, exists S', exists w',
         step S t S'
      /\ plus Csem.step ge S t S'
      /\ possible_trace w t w').
Proof.
  intros. exploit safe_imm; eauto. intros IS; inv IS.
(* terminated *)
  left; exists r; auto.
  destruct H0.
(* expression step *)
  inv H0. 
  (* lred *)
  exploit can_estep; eauto. inv H4; auto. 
  intros [S [A B]]. right. exists E0; exists S; exists w. 
  split. left; auto. split. auto. constructor.
  (* rred *)
  exploit can_estep; eauto. inv H4; auto. inv H2; auto. 
  intros [S [A B]]. right. exists E0; exists S; exists w. 
  split. left; auto. split. auto. constructor.
  (* callred *)
  exploit can_estep; eauto. inv H4; auto. inv H2; auto. 
  intros [S [A B]]. right. exists E0; exists S; exists w. 
  split. left; auto. split. auto. constructor.
(* other step *)
  right. exists t; exists s'; exists w'.
  split. right. auto. 
  split. apply plus_one. right. auto. 
  auto.
Qed.

End STRATEGY.

(** * Whole-program behaviors *)

Definition exec_program (p: program) (beh: program_behavior) : Prop :=
  program_behaves step (initial_state p) final_state (Genv.globalenv p) beh.

Definition safeprog (p: program) (w: world) : Prop :=
  (exists s, initial_state p s)
  /\ (forall s, initial_state p s -> safe (Genv.globalenv p) w s).

(** We now show the existence of a safe behavior for the strategy,
  which is also an acceptable behavior for the nondeterministic semantics. *)

Section BEHAVIOR.

Variable prog: program.
Variable initial_world: world.

(** We define a transition semantics that combines 
- one strategy step;
- one or several nondeterministic steps;
- the state of the external world.
*)

Local Open Scope pair_scope.

Definition comb_state := (state * world)%type.

Definition comb_step (ge: genv) (s: comb_state) (t: trace) (s': comb_state) : Prop :=
  (step ge s#1 t s'#1 /\ plus Csem.step ge s#1 t s'#1)
  /\ possible_trace s#2 t s'#2.

Definition comb_initial_state (s: comb_state) : Prop :=
  initial_state prog s#1 /\ s#2 = initial_world.

Definition comb_final_state (s: comb_state) (r: int) : Prop :=
  final_state s#1 r.

Definition comb_program_behaves (beh: program_behavior) : Prop :=
  program_behaves comb_step comb_initial_state comb_final_state (Genv.globalenv prog) beh.

(** If the source program is safe, the combined semantics cannot go wrong. *)

Remark proj_star_comb_step:
  forall ge s t s',
  star comb_step ge s t s' ->
  star Csem.step ge s#1 t s'#1 /\ possible_trace s#2 t s'#2.
Proof.
  induction 1. split; constructor.
  destruct H as [[A B] C]. destruct IHstar. 
  split. eapply star_trans. apply plus_star; eauto. eauto. auto. 
  subst t. eapply possible_trace_app; eauto.
Qed.

Lemma comb_behavior_not_wrong:
  forall beh,
  safeprog prog initial_world -> comb_program_behaves beh -> not_wrong beh.
Proof.
  intros. destruct H. inv H0; simpl; auto.
(* Goes wrong after some steps *)
  destruct H2. exploit proj_star_comb_step; eauto. intros [A B].
  assert (C: safe (Genv.globalenv prog) s'#2 s'#1).
    eapply safe_steps. apply H1. eauto. eauto. congruence.
  exploit strategy_simulation. eexact C. 
  intros [[r P] | [t' [s'' [w'' [P [Q R]]]]]].
  elim (H5 r). auto. 
  elim (H4 t' (s'', w'')). red. auto. 
(* Goes initiall wrong *)
  destruct H as [s A]. elim (H2 (s, initial_world)). red; auto. 
Qed.

(** Any non-wrong behavior of the combined semantics is a behavior 
  for the nondeterministic semantics. *)

Lemma proj1_comb_behavior:
  forall beh,
  not_wrong beh ->
  comb_program_behaves beh ->
  Csem.exec_program prog beh.
Proof.
  intros. red in H0. red.
  eapply simulation_plus_preservation with
    (match_states := fun (S1: comb_state) (S2: state) => S2 = S1#1); eauto.
  intros. destruct H1. exists (st1#1); auto.
  intros. red in H2. congruence.
  intros. destruct H1 as [[A B] D]. subst st2. exists (st1'#1); auto.
Qed.

(** Likewise, any non-wrong behavior of the combined semantics is a behavior 
  for the strategy. *)

Lemma proj2_comb_behavior:
  forall beh,
  not_wrong beh ->
  comb_program_behaves beh ->
  exec_program prog beh.
Proof.
  intros. red in H0. red.
  eapply simulation_step_preservation with
    (match_states := fun (S1: comb_state) (S2: state) => S2 = S1#1); eauto.
  intros. destruct H1. exists (st1#1); auto.
  intros. red in H2. congruence.
  intros. destruct H1 as [[A B] D]. subst st2. exists (st1'#1); auto.
Qed.

(** Finally, any behavior of the combined semantics is possible in the
  initial world. *)

Lemma possible_comb_behavior:
  forall beh,
  comb_program_behaves beh ->
  possible_behavior initial_world beh.
Proof.
  intros. 
  apply (project_behaviors_trace _ _
    (fun ge s t s' => step ge s t s' /\ plus Csem.step ge s t s')
    (initial_state prog)
    final_state
    initial_world (Genv.globalenv prog)).
  exact H. 
Qed.

(** It follows that a safe C program has a non-wrong behavior that
  follows the strategy. *)

Theorem strategy_behavior:
  safeprog prog initial_world ->
  exists beh, not_wrong beh 
           /\ Csem.exec_program prog beh
           /\ exec_program prog beh
           /\ possible_behavior initial_world beh.
Proof.
  intros.
  assert (exists beh, comb_program_behaves beh).
    unfold comb_program_behaves. apply program_behaves_exists. 
  destruct H0 as [beh CPB].
  assert (not_wrong beh). eapply comb_behavior_not_wrong; eauto. 
  exists beh. split. auto.
  split. apply proj1_comb_behavior; auto.
  split. apply proj2_comb_behavior; auto.
  apply possible_comb_behavior; auto.
Qed.

End BEHAVIOR.

(** * A big-step semantics implementing the reduction strategy. *)

Section BIGSTEP.

Variable ge: genv.

(** The execution of a statement produces an ``outcome'', indicating
  how the execution terminated: either normally or prematurely
  through the execution of a [break], [continue] or [return] statement. *)

Inductive outcome: Type :=
   | Out_break: outcome                 (**r terminated by [break] *)
   | Out_continue: outcome              (**r terminated by [continue] *)
   | Out_normal: outcome                (**r terminated normally *)
   | Out_return: option (val * type) -> outcome. (**r terminated by [return] *)

Inductive out_normal_or_continue : outcome -> Prop :=
  | Out_normal_or_continue_N: out_normal_or_continue Out_normal
  | Out_normal_or_continue_C: out_normal_or_continue Out_continue.

Inductive out_break_or_return : outcome -> outcome -> Prop :=
  | Out_break_or_return_B: out_break_or_return Out_break Out_normal
  | Out_break_or_return_R: forall ov,
      out_break_or_return (Out_return ov) (Out_return ov).

Definition outcome_switch (out: outcome) : outcome :=
  match out with
  | Out_break => Out_normal
  | o => o
  end.

Definition outcome_result_value (out: outcome) (t: type) (v: val) : Prop :=
  match out, t with
  | Out_normal, Tvoid => v = Vundef
  | Out_return None, Tvoid => v = Vundef
  | Out_return (Some (v', ty')), ty => ty <> Tvoid /\ cast v' ty' ty v
  | _, _ => False
  end. 

(** [eval_expression ge e m1 a t m2 a'] describes the evaluation of the
  complex expression e.  [v] is the resulting value, [m2] the final
  memory state, and [t] the trace of input/output events performed
  during this evaluation.  *)

Inductive eval_expression: env -> mem -> expr -> trace -> mem -> val -> Prop :=
  | eval_expression_intro: forall e m a t m' a' v,
      eval_expr e m RV a t m' a' -> eval_simple_rvalue ge e m' a' v ->
      eval_expression e m a t m' v

with eval_expr: env -> mem -> kind -> expr -> trace -> mem -> expr -> Prop :=
  | eval_val: forall e m v ty,
      eval_expr e m RV (Eval v ty) E0 m (Eval v ty)
  | eval_var: forall e m x ty,
      eval_expr e m LV (Evar x ty) E0 m (Evar x ty)
  | eval_field: forall e m a t m' a' f ty,
      eval_expr e m LV a t m' a' ->
      eval_expr e m LV (Efield a f ty) t m' (Efield a' f ty)
  | eval_valof: forall e m a t m' a' ty,
      eval_expr e m LV a t m' a' ->
      eval_expr e m RV (Evalof a ty) t m' (Evalof a' ty)
  | eval_deref: forall e m a t m' a' ty,
      eval_expr e m RV a t m' a' ->
      eval_expr e m LV (Ederef a ty) t m' (Ederef a' ty)
  | eval_addrof: forall e m a t m' a' ty,
      eval_expr e m LV a t m' a' ->
      eval_expr e m RV (Eaddrof a ty) t m' (Eaddrof a' ty)
  | eval_unop: forall e m a t m' a' op ty,
      eval_expr e m RV a t m' a' ->
      eval_expr e m RV (Eunop op a ty) t m' (Eunop op a' ty)
  | eval_binop: forall e m a1 t1 m' a1' a2 t2 m'' a2' op ty,
      eval_expr e m RV a1 t1 m' a1' -> eval_expr e m' RV a2 t2 m'' a2' ->
      eval_expr e m RV (Ebinop op a1 a2 ty) (t1 ** t2) m'' (Ebinop op a1' a2' ty)
  | eval_cast: forall e m a t m' a' ty,
      eval_expr e m RV a t m' a' ->
      eval_expr e m RV (Ecast a ty) t m' (Ecast a' ty)
  | eval_condition_true: forall e m a1 a2 a3 ty t1 m' a1' v1 t2 m'' a2' v,
      eval_expr e m RV a1 t1 m' a1' -> eval_simple_rvalue ge e m' a1' v1 -> is_true v1 (typeof a1) ->
      eval_expr e m' RV a2 t2 m'' a2' -> eval_simple_rvalue ge e m'' a2' v ->
      ty = typeof a2 ->
      eval_expr e m RV (Econdition a1 a2 a3 ty) (t1**t2) m'' (Eval v ty)
  | eval_condition_false: forall e m a1 a2 a3 ty t1 m' a1' v1 t2 m'' a3' v,
      eval_expr e m RV a1 t1 m' a1' -> eval_simple_rvalue ge e m' a1' v1 -> is_false v1 (typeof a1) ->
      eval_expr e m' RV a3 t2 m'' a3' -> eval_simple_rvalue ge e m'' a3' v ->
      ty = typeof a3 ->
      eval_expr e m RV (Econdition a1 a2 a3 ty) (t1**t2) m'' (Eval v ty)
  | eval_sizeof: forall e m ty' ty,
      eval_expr e m RV (Esizeof ty' ty) E0 m (Esizeof ty' ty)
  | eval_assign: forall e m l r ty t1 m1 l' t2 m2 r' b ofs v v' m3,
      eval_expr e m LV l t1 m1 l' -> eval_expr e m1 RV r t2 m2 r' ->
      eval_simple_lvalue ge e m2 l' b ofs ->
      eval_simple_rvalue ge e m2 r' v ->
      cast v (typeof r) (typeof l) v' ->
      store_value_of_type (typeof l) m2 b ofs v' = Some m3 ->
      ty = typeof l ->
      eval_expr e m RV (Eassign l r ty) (t1**t2) m3 (Eval v' ty)
  | eval_assignop: forall e m op l r tyres ty t1 m1 l' t2 m2 r' b ofs
                          v1 v2 v3 v4 m3,
      eval_expr e m LV l t1 m1 l' -> eval_expr e m1 RV r t2 m2 r' ->
      eval_simple_lvalue ge e m2 l' b ofs ->
      load_value_of_type (typeof l) m2 b ofs = Some v1 ->
      eval_simple_rvalue ge e m2 r' v2 ->
      sem_binary_operation op v1 (typeof l) v2 (typeof r) m2 = Some v3 ->
      cast v3 tyres (typeof l) v4 ->
      store_value_of_type (typeof l) m2 b ofs v4 = Some m3 ->
      ty = typeof l ->
      eval_expr e m RV (Eassignop op l r tyres ty) (t1**t2) m3 (Eval v4 ty)
  | eval_postincr: forall e m id l ty t m1 l' b ofs v1 v2 v3 m2,
      eval_expr e m LV l t m1 l' ->
      eval_simple_lvalue ge e m1 l' b ofs ->
      load_value_of_type ty m1 b ofs = Some v1 ->
      sem_incrdecr id v1 ty = Some v2 ->
      cast v2 (typeconv ty) ty v3 ->
      store_value_of_type ty m1 b ofs v3 = Some m2 ->
      ty = typeof l ->
      eval_expr e m RV (Epostincr id l ty) t m2 (Eval v1 ty)
  | eval_comma: forall e m r1 r2 ty t1 m1 r1' v1 t2 m2 r2',
      eval_expr e m RV r1 t1 m1 r1' ->
      eval_simple_rvalue ge e m1 r1' v1 ->
      eval_expr e m1 RV r2 t2 m2 r2' ->
      ty = typeof r2 ->
      eval_expr e m RV (Ecomma r1 r2 ty) (t1**t2) m2 r2'
  | eval_call: forall e m rf rargs ty t1 m1 rf' t2 m2 rargs' vf vargs
                      targs tres fd t3 m3 vres,
      eval_expr e m RV rf t1 m1 rf' -> eval_exprlist e m1 rargs t2 m2 rargs' ->
      eval_simple_rvalue ge e m2 rf' vf ->
      eval_simple_list ge e m2 rargs' targs vargs ->
      typeof rf = Tfunction targs tres ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction targs tres ->
      eval_funcall m2 fd vargs t3 m3 vres ->
      eval_expr e m RV (Ecall rf rargs ty) (t1**t2**t3) m3 (Eval vres ty)

with eval_exprlist: env -> mem -> exprlist -> trace -> mem -> exprlist -> Prop :=
  | eval_nil: forall e m,
      eval_exprlist e m Enil E0 m Enil
  | eval_cons: forall e m a1 al t1 m1 a1' t2 m2 al',
      eval_expr e m RV a1 t1 m1 a1' -> eval_exprlist e m1 al t2 m2 al' ->
      eval_exprlist e m (Econs a1 al) (t1**t2) m2 (Econs a1' al')

(** [exec_stmt ge e m1 s t m2 out] describes the execution of 
  the statement [s].  [out] is the outcome for this execution.
  [m1] is the initial memory state, [m2] the final memory state.
  [t] is the trace of input/output events performed during this
  evaluation. *)

with exec_stmt: env -> mem -> statement -> trace -> mem -> outcome -> Prop :=
  | exec_Sskip:   forall e m,
      exec_stmt e m Sskip
               E0 m Out_normal
  | exec_Sdo:     forall e m a t m' v,
      eval_expression e m a t m' v ->
      exec_stmt e m (Sdo a)
                t m' Out_normal
  | exec_Sseq_1:   forall e m s1 s2 t1 m1 t2 m2 out,
      exec_stmt e m s1 t1 m1 Out_normal ->
      exec_stmt e m1 s2 t2 m2 out ->
      exec_stmt e m (Ssequence s1 s2)
                (t1 ** t2) m2 out
  | exec_Sseq_2:   forall e m s1 s2 t1 m1 out,
      exec_stmt e m s1 t1 m1 out ->
      out <> Out_normal ->
      exec_stmt e m (Ssequence s1 s2)
                t1 m1 out
  | exec_Sifthenelse_true: forall e m a s1 s2 t1 m1 v1 t2 m2 out,
      eval_expression e m a t1 m1 v1 ->
      is_true v1 (typeof a) ->
      exec_stmt e m1 s1 t2 m2 out ->
      exec_stmt e m (Sifthenelse a s1 s2)
                (t1**t2) m2 out
  | exec_Sifthenelse_false: forall e m a s1 s2 t1 m1 v1 t2 m2 out,
      eval_expression e m a t1 m1 v1 ->
      is_false v1 (typeof a) ->
      exec_stmt e m1 s2 t2 m2 out ->
      exec_stmt e m (Sifthenelse a s1 s2)
                (t1**t2) m2 out
  | exec_Sreturn_none:   forall e m,
      exec_stmt e m (Sreturn None)
               E0 m (Out_return None)
  | exec_Sreturn_some: forall e m a t m' v,
      eval_expression e m a t m' v ->
      exec_stmt e m (Sreturn (Some a))
                t m' (Out_return (Some(v, typeof a)))
  | exec_Sbreak:   forall e m,
      exec_stmt e m Sbreak
               E0 m Out_break
  | exec_Scontinue:   forall e m,
      exec_stmt e m Scontinue
               E0 m Out_continue
  | exec_Swhile_false: forall e m a s t m' v,
      eval_expression e m a t m' v ->
      is_false v (typeof a) ->
      exec_stmt e m (Swhile a s)
                t m' Out_normal
  | exec_Swhile_stop: forall e m a s t1 m1 v t2 m2 out' out,
      eval_expression e m a t1 m1 v ->
      is_true v (typeof a) ->
      exec_stmt e m1 s t2 m2 out' ->
      out_break_or_return out' out ->
      exec_stmt e m (Swhile a s)
                (t1**t2) m2 out
  | exec_Swhile_loop: forall e m a s t1 m1 v t2 m2 out1 t3 m3 out,
      eval_expression e m a t1 m1 v ->
      is_true v (typeof a) ->
      exec_stmt e m1 s t2 m2 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e m2 (Swhile a s) t3 m3 out ->
      exec_stmt e m (Swhile a s)
                (t1 ** t2 ** t3) m3 out
  | exec_Sdowhile_false: forall e m s a t1 m1 out1 t2 m2 v,
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      eval_expression e m1 a t2 m2 v ->
      is_false v (typeof a) ->
      exec_stmt e m (Sdowhile a s)
                (t1 ** t2) m2 Out_normal
  | exec_Sdowhile_stop: forall e m s a t m1 out1 out,
      exec_stmt e m s t m1 out1 ->
      out_break_or_return out1 out ->
      exec_stmt e m (Sdowhile a s)
                t m1 out
  | exec_Sdowhile_loop: forall e m s a t1 m1 out1 t2 m2 v t3 m3 out,
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      eval_expression e m1 a t2 m2 v ->
      is_true v (typeof a) ->
      exec_stmt e m2 (Sdowhile a s) t3 m3 out ->
      exec_stmt e m (Sdowhile a s) 
                (t1 ** t2 ** t3) m3 out
  | exec_Sfor_start: forall e m s a1 a2 a3 out m1 m2 t1 t2,
      exec_stmt e m a1 t1 m1 Out_normal ->
      exec_stmt e m1 (Sfor Sskip a2 a3 s) t2 m2 out ->
      exec_stmt e m (Sfor a1 a2 a3 s) 
                (t1 ** t2) m2 out
  | exec_Sfor_false: forall e m s a2 a3 t m' v,
      eval_expression e m a2 t m' v ->
      is_false v (typeof a2) ->
      exec_stmt e m (Sfor Sskip a2 a3 s)
                t m' Out_normal
  | exec_Sfor_stop: forall e m s a2 a3 t1 m1 v t2 m2 out1 out,
      eval_expression e m a2 t1 m1 v ->
      is_true v (typeof a2) ->
      exec_stmt e m1 s t2 m2 out1 ->
      out_break_or_return out1 out ->
      exec_stmt e m (Sfor Sskip a2 a3 s)
                (t1 ** t2) m2 out
  | exec_Sfor_loop: forall e m s a2 a3 t1 m1 v t2 m2 out1 t3 m3 t4 m4 out,
      eval_expression e m a2 t1 m1 v ->
      is_true v (typeof a2) ->
      exec_stmt e m1 s t2 m2 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e m2 a3 t3 m3 Out_normal ->
      exec_stmt e m3 (Sfor Sskip a2 a3 s) t4 m4 out ->
      exec_stmt e m (Sfor Sskip a2 a3 s)
                (t1 ** t2 ** t3 ** t4) m4 out
  | exec_Sswitch:   forall e m a sl t1 m1 n t2 m2 out,
      eval_expression e m a t1 m1 (Vint n) ->
      exec_stmt e m1 (seq_of_labeled_statement (select_switch n sl)) t2 m2 out ->
      exec_stmt e m (Sswitch a sl)
                (t1 ** t2) m2 (outcome_switch out)

(** [eval_funcall m1 fd args t m2 res] describes the invocation of
  function [fd] with arguments [args].  [res] is the value returned
  by the call.  *)

with eval_funcall: mem -> fundef -> list val -> trace -> mem -> val -> Prop :=
  | eval_funcall_internal: forall m f vargs t e m1 m2 m3 out vres m4,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      alloc_variables empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters e m1 f.(fn_params) vargs m2 ->
      exec_stmt e m2 f.(fn_body) t m3 out ->
      outcome_result_value out f.(fn_return) vres ->
      Mem.free_list m3 (blocks_of_env e) = Some m4 ->
      eval_funcall m (Internal f) vargs t m4 vres
  | eval_funcall_external: forall m ef targs tres vargs t vres m',
      external_call ef ge vargs m t vres m' ->
      eval_funcall m (External ef targs tres) vargs t m' vres.

Scheme eval_expression_ind5 := Minimality for eval_expression Sort Prop
  with eval_expr_ind5 := Minimality for eval_expr Sort Prop
  with eval_exprlist_ind5 := Minimality for eval_exprlist Sort Prop
  with exec_stmt_ind5 := Minimality for exec_stmt Sort Prop
  with eval_funcall_ind5 := Minimality for eval_funcall Sort Prop.

Combined Scheme bigstep_induction from
        eval_expression_ind5,  eval_expr_ind5,  eval_exprlist_ind5,
        exec_stmt_ind5, eval_funcall_ind5.

(** [evalinf_expr ge e m1 K a T] denotes the fact that expression [a]
  diverges in initial state [m1].  [T] is the trace of input/output
  events performed during this evaluation.  *)

CoInductive evalinf_expr: env -> mem -> kind -> expr -> traceinf -> Prop :=
  | evalinf_field: forall e m a t f ty,
      evalinf_expr e m LV a t ->
      evalinf_expr e m LV (Efield a f ty) t
  | evalinf_valof: forall e m a t ty,
      evalinf_expr e m LV a t ->
      evalinf_expr e m RV (Evalof a ty) t
  | evalinf_deref: forall e m a t ty,
      evalinf_expr e m RV a t ->
      evalinf_expr e m LV (Ederef a ty) t
  | evalinf_addrof: forall e m a t ty,
      evalinf_expr e m LV a t ->
      evalinf_expr e m RV (Eaddrof a ty) t
  | evalinf_unop: forall e m a t op ty,
      evalinf_expr e m RV a t ->
      evalinf_expr e m RV (Eunop op a ty) t
  | evalinf_binop_left: forall e m a1 t1 a2 op ty,
      evalinf_expr e m RV a1 t1 ->
      evalinf_expr e m RV (Ebinop op a1 a2 ty) t1
  | evalinf_binop_right: forall e m a1 t1 m' a1' a2 t2 op ty,
      eval_expr e m RV a1 t1 m' a1' -> evalinf_expr e m' RV a2 t2 ->
      evalinf_expr e m RV (Ebinop op a1 a2 ty) (t1 *** t2)
  | evalinf_cast: forall e m a t ty,
      evalinf_expr e m RV a t ->
      evalinf_expr e m RV (Ecast a ty) t
  | evalinf_condition: forall e m a1 a2 a3 ty t1,
      evalinf_expr e m RV a1 t1 ->
      evalinf_expr e m RV (Econdition a1 a2 a3 ty) t1
  | evalinf_condition_true: forall e m a1 a2 a3 ty t1 m' a1' v1 t2,
      eval_expr e m RV a1 t1 m' a1' -> eval_simple_rvalue ge e m' a1' v1 -> is_true v1 (typeof a1) ->
      evalinf_expr e m' RV a2 t2 ->
      ty = typeof a2 ->
      evalinf_expr e m RV (Econdition a1 a2 a3 ty) (t1***t2)
  | evalinf_condition_false: forall e m a1 a2 a3 ty t1 m' a1' v1 t2,
      eval_expr e m RV a1 t1 m' a1' -> eval_simple_rvalue ge e m' a1' v1 -> is_false v1 (typeof a1) ->
      evalinf_expr e m' RV a3 t2 ->
      ty = typeof a3 ->
      evalinf_expr e m RV (Econdition a1 a2 a3 ty) (t1***t2)
  | evalinf_assign_left: forall e m a1 t1 a2 ty,
      evalinf_expr e m LV a1 t1 ->
      evalinf_expr e m RV (Eassign a1 a2 ty) t1
  | evalinf_assign_right: forall e m a1 t1 m' a1' a2 t2 ty,
      eval_expr e m LV a1 t1 m' a1' -> evalinf_expr e m' RV a2 t2 ->
      evalinf_expr e m RV (Eassign a1 a2 ty) (t1 *** t2)
  | evalinf_assignop_left: forall e m a1 t1 a2 op tyres ty,
      evalinf_expr e m LV a1 t1 ->
      evalinf_expr e m RV (Eassignop op a1 a2 tyres ty) t1
  | evalinf_assignop_right: forall e m a1 t1 m' a1' a2 t2 op tyres ty,
      eval_expr e m LV a1 t1 m' a1' -> evalinf_expr e m' RV a2 t2 ->
      evalinf_expr e m RV (Eassignop op a1 a2 tyres ty) (t1 *** t2)
  | evalinf_postincr: forall e m a t id ty,
      evalinf_expr e m LV a t ->
      evalinf_expr e m RV (Epostincr id a ty) t
  | evalinf_comma_left: forall e m a1 t1 a2 ty,
      evalinf_expr e m RV a1 t1 ->
      evalinf_expr e m RV (Ecomma a1 a2 ty) t1
  | evalinf_comma_right: forall e m a1 t1 m1 a1' v1 a2 t2 ty,
      eval_expr e m RV a1 t1 m1 a1' -> eval_simple_rvalue ge e m1 a1' v1 ->
      ty = typeof a2 ->
      evalinf_expr e m1 RV a2 t2 ->
      evalinf_expr e m RV (Ecomma a1 a2 ty) (t1 *** t2)
  | evalinf_call_left: forall e m a1 t1 a2 ty,
      evalinf_expr e m RV a1 t1 ->
      evalinf_expr e m RV (Ecall a1 a2 ty) t1
  | evalinf_call_right: forall e m a1 t1 m1 a1' a2 t2 ty,
      eval_expr e m RV a1 t1 m1 a1' -> 
      evalinf_exprlist e m1 a2 t2 ->
      evalinf_expr e m RV (Ecall a1 a2 ty) (t1 *** t2)
  | evalinf_call: forall e m rf rargs ty t1 m1 rf' t2 m2 rargs' vf vargs
                      targs tres fd t3,
      eval_expr e m RV rf t1 m1 rf' -> eval_exprlist e m1 rargs t2 m2 rargs' ->
      eval_simple_rvalue ge e m2 rf' vf ->
      eval_simple_list ge e m2 rargs' targs vargs ->
      typeof rf = Tfunction targs tres ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction targs tres ->
      evalinf_funcall m2 fd vargs t3 ->
      evalinf_expr e m RV (Ecall rf rargs ty) (t1***t2***t3)

with evalinf_exprlist: env -> mem -> exprlist -> traceinf -> Prop :=
  | evalinf_cons_left: forall e m a1 al t1,
      evalinf_expr e m RV a1 t1 ->
      evalinf_exprlist e m (Econs a1 al) t1
  | evalinf_cons_right: forall e m a1 al t1 m1 a1' t2,
      eval_expr e m RV a1 t1 m1 a1' -> evalinf_exprlist e m1 al t2 ->
      evalinf_exprlist e m (Econs a1 al) (t1***t2)

(** [execinf_stmt ge e m1 s t] describes the diverging execution of 
  the statement [s].  *)

with execinf_stmt: env -> mem -> statement -> traceinf -> Prop :=
  | execinf_Sdo:     forall e m a t,
      evalinf_expr e m RV a t ->
      execinf_stmt e m (Sdo a) t
  | execinf_Sseq_1:   forall e m s1 s2 t1,
      execinf_stmt e m s1 t1 ->
      execinf_stmt e m (Ssequence s1 s2) t1
  | execinf_Sseq_2:   forall e m s1 s2 t1 m1 t2,
      exec_stmt e m s1 t1 m1 Out_normal ->
      execinf_stmt e m1 s2 t2 ->
      execinf_stmt e m (Ssequence s1 s2) (t1***t2)
  | execinf_Sifthenelse_test: forall e m a s1 s2 t1,
      evalinf_expr e m RV a t1 ->
      execinf_stmt e m (Sifthenelse a s1 s2) t1
  | execinf_Sifthenelse_true: forall e m a s1 s2 t1 m1 v1 t2,
      eval_expression e m a t1 m1 v1 ->
      is_true v1 (typeof a) ->
      execinf_stmt e m1 s1 t2 ->
      execinf_stmt e m (Sifthenelse a s1 s2) (t1***t2)
  | execinf_Sifthenelse_false: forall e m a s1 s2 t1 m1 v1 t2,
      eval_expression e m a t1 m1 v1 ->
      is_false v1 (typeof a) ->
      execinf_stmt e m1 s2 t2 ->
      execinf_stmt e m (Sifthenelse a s1 s2) (t1***t2)
  | execinf_Sreturn_some: forall e m a t,
      evalinf_expr e m RV a t ->
      execinf_stmt e m (Sreturn (Some a)) t
  | execinf_Swhile_test: forall e m a s t1,
      evalinf_expr e m RV a t1 ->
      execinf_stmt e m (Swhile a s) t1
  | execinf_Swhile_body: forall e m a s t1 m1 v t2,
      eval_expression e m a t1 m1 v ->
      is_true v (typeof a) ->
      execinf_stmt e m1 s t2 ->
      execinf_stmt e m (Swhile a s) (t1***t2)
  | execinf_Swhile_loop: forall e m a s t1 m1 v t2 m2 out1 t3,
      eval_expression e m a t1 m1 v ->
      is_true v (typeof a) ->
      exec_stmt e m1 s t2 m2 out1 ->
      out_normal_or_continue out1 ->
      execinf_stmt e m2 (Swhile a s) t3 ->
      execinf_stmt e m (Swhile a s) (t1***t2***t3)
  | execinf_Sdowhile_body: forall e m s a t1,
      execinf_stmt e m s t1 ->
      execinf_stmt e m (Sdowhile a s) t1
  | execinf_Sdowhile_test: forall e m s a t1 m1 out1 t2,
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      evalinf_expr e m1 RV a t2 ->
      execinf_stmt e m (Sdowhile a s) (t1***t2)
  | execinf_Sdowhile_loop: forall e m s a t1 m1 out1 t2 m2 v t3,
      exec_stmt e m s t1 m1 out1 ->
      out_normal_or_continue out1 ->
      eval_expression e m1 a t2 m2 v ->
      is_true v (typeof a) ->
      execinf_stmt e m2 (Sdowhile a s) t3 ->
      execinf_stmt e m (Sdowhile a s) (t1***t2***t3)
  | execinf_Sfor_start_1: forall e m s a1 a2 a3 t1,
      execinf_stmt e m a1 t1 ->
      execinf_stmt e m (Sfor a1 a2 a3 s) t1
  | execinf_Sfor_start_2: forall e m s a1 a2 a3 m1 t1 t2,
      exec_stmt e m a1 t1 m1 Out_normal -> a1 <> Sskip ->
      execinf_stmt e m1 (Sfor Sskip a2 a3 s) t2 ->
      execinf_stmt e m (Sfor a1 a2 a3 s) (t1***t2)
  | execinf_Sfor_test: forall e m s a2 a3 t,
      evalinf_expr e m RV a2 t ->
      execinf_stmt e m (Sfor Sskip a2 a3 s) t
  | execinf_Sfor_body: forall e m s a2 a3 t1 m1 v t2,
      eval_expression e m a2 t1 m1 v ->
      is_true v (typeof a2) ->
      execinf_stmt e m1 s t2 ->
      execinf_stmt e m (Sfor Sskip a2 a3 s) (t1***t2)
  | execinf_Sfor_next: forall e m s a2 a3 t1 m1 v t2 m2 out1 t3,
      eval_expression e m a2 t1 m1 v ->
      is_true v (typeof a2) ->
      exec_stmt e m1 s t2 m2 out1 ->
      out_normal_or_continue out1 ->
      execinf_stmt e m2 a3 t3 ->
      execinf_stmt e m (Sfor Sskip a2 a3 s) (t1***t2***t3)
  | execinf_Sfor_loop: forall e m s a2 a3 t1 m1 v t2 m2 out1 t3 m3 t4,
      eval_expression e m a2 t1 m1 v ->
      is_true v (typeof a2) ->
      exec_stmt e m1 s t2 m2 out1 ->
      out_normal_or_continue out1 ->
      exec_stmt e m2 a3 t3 m3 Out_normal ->
      execinf_stmt e m3 (Sfor Sskip a2 a3 s) t4 ->
      execinf_stmt e m (Sfor Sskip a2 a3 s) (t1***t2***t3***t4)
  | execinf_Sswitch_expr:   forall e m a sl t1,
      evalinf_expr e m RV a t1 ->
      execinf_stmt e m (Sswitch a sl) t1
  | execinf_Sswitch_body:   forall e m a sl t1 m1 n t2,
      eval_expression e m a t1 m1 (Vint n) ->
      execinf_stmt e m1 (seq_of_labeled_statement (select_switch n sl)) t2 ->
      execinf_stmt e m (Sswitch a sl) (t1***t2)

(** [evalinf_funcall m1 fd args t m2 res] describes a diverging
  invocation of function [fd] with arguments [args].  *)

with evalinf_funcall: mem -> fundef -> list val -> traceinf -> Prop :=
  | evalinf_funcall_internal: forall m f vargs t e m1 m2,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      alloc_variables empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters e m1 f.(fn_params) vargs m2 ->
      execinf_stmt e m2 f.(fn_body) t ->
      evalinf_funcall m (Internal f) vargs t.

(** ** Implication from big-step semantics to transition semantics *)

Inductive outcome_state_match
       (e: env) (m: mem) (f: function) (k: cont): outcome -> state -> Prop :=
  | osm_normal:
      outcome_state_match e m f k Out_normal (State f Sskip k e m)
  | osm_break:
      outcome_state_match e m f k Out_break (State f Sbreak k e m)
  | osm_continue:
      outcome_state_match e m f k Out_continue (State f Scontinue k e m)
  | osm_return_none: forall k',
      call_cont k' = call_cont k ->
      outcome_state_match e m f k 
        (Out_return None) (State f (Sreturn None) k' e m)
  | osm_return_some: forall v ty k',
      call_cont k' = call_cont k ->
      outcome_state_match e m f k
        (Out_return (Some (v, ty))) (ExprState f (Eval v ty) (Kreturn k') e m).

Lemma is_call_cont_call_cont:
  forall k, is_call_cont k -> call_cont k = k.
Proof.
  destruct k; simpl; intros; contradiction || auto.
Qed.

Lemma leftcontext_compose:
  forall k2 k3 C2, leftcontext k2 k3 C2 ->
  forall k1 C1, leftcontext k1 k2 C1 ->
  leftcontext k1 k3 (fun x => C2(C1 x))
with leftcontextlist_compose:
  forall k2 C2, leftcontextlist k2 C2 ->
  forall k1 C1, leftcontext k1 k2 C1 ->
  leftcontextlist k1 (fun x => C2(C1 x)).
Proof.
  induction 1; intros; try (constructor; eauto).
  replace (fun x => C1 x) with C1. auto. apply extensionality; auto.
  induction 1; intros; constructor; eauto.
Qed.

Lemma exprlist_app_leftcontext:
  forall rl1 rl2,
  simplelist rl1 -> leftcontextlist RV (fun x => exprlist_app rl1 (Econs x rl2)).
Proof.
  induction rl1; simpl; intros. 
  apply lctx_list_head. constructor.
  destruct H. apply lctx_list_tail. auto. auto. 
Qed.

Lemma exprlist_app_simple:
  forall rl1 rl2, simplelist rl1 -> simplelist rl2 -> simplelist (exprlist_app rl1 rl2).
Proof.
  induction rl1; simpl; intros. auto. destruct H; auto. 
Qed.

Lemma bigstep_to_steps:
  (forall e m a t m' v,
   eval_expression e m a t m' v ->
   forall f k,
   star step ge (ExprState f a k e m) t (ExprState f (Eval v (typeof a)) k e m'))
/\(forall e m K a t m' a',
   eval_expr e m K a t m' a' ->
   forall C f k, leftcontext K RV C ->
   simple a' /\ typeof a' = typeof a /\
   star step ge (ExprState f (C a) k e m) t (ExprState f (C a') k e m'))
/\(forall e m al t m' al',
   eval_exprlist e m al t m' al' ->
   forall a1 al2 ty C f k, leftcontext RV RV C -> simple a1 -> simplelist al2 ->
   simplelist al' /\
   star step ge (ExprState f (C (Ecall a1 (exprlist_app al2 al) ty)) k e m)
              t (ExprState f (C (Ecall a1 (exprlist_app al2 al') ty)) k e m'))
/\(forall e m s t m' out,
   exec_stmt e m s t m' out ->
   forall f k,
(*
   match out with
   | Out_return None => fn_return f = Tvoid
   | Out_return (Some(v, ty)) => fn_return f <> Tvoid
   | _ => True
   end ->
*)
   exists S,
   star step ge (State f s k e m) t S /\ outcome_state_match e m' f k out S)
/\(forall m fd args t m' res,
   eval_funcall m fd args t m' res ->
   forall k,
   is_call_cont k ->
   star step ge (Callstate fd args k m) t (Returnstate res k m')).
Proof.
  apply bigstep_induction; intros.
(* expression, general *)
  exploit (H0 (fun x => x) f k). constructor. intros [A [B C]].
  assert (match a' with Eval _ _ => False | _ => True end ->
          star step ge (ExprState f a k e m) t (ExprState f (Eval v (typeof a)) k e m')).
   intro. eapply star_right. eauto. left. eapply step_expr; eauto. traceEq. 
  destruct a'; auto.
  simpl in B. rewrite B in C. inv H1. auto. 

(* val *)
  simpl; intuition. apply star_refl.
(* var *)
  simpl; intuition. apply star_refl.
(* field *)
  exploit (H0 (fun x => C(Efield x f ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition; eauto. 
(* valof *)
  exploit (H0 (fun x => C(Evalof x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition; eauto. 
(* deref *)
  exploit (H0 (fun x => C(Ederef x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition; eauto.
(* addrof *)
  exploit (H0 (fun x => C(Eaddrof x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition; eauto.
(* unop *)
  exploit (H0 (fun x => C(Eunop op x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition; eauto.
(* binop *)
  exploit (H0 (fun x => C(Ebinop op x a2 ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  exploit (H2 (fun x => C(Ebinop op a1' x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. auto. intros [E [F G]].
  simpl; intuition. eapply star_trans; eauto. 
(* cast *)
  exploit (H0 (fun x => C(Ecast x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition; eauto.
(* condition *)
  exploit (H0 (fun x => C(Econdition x a2 a3 ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  exploit (H4 (fun x => C(Eparen x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [E [F G]].
  simpl; intuition.
  eapply star_trans. eexact D.
  eapply star_left. left; eapply step_condition_true; eauto. congruence.
  eapply star_right. eexact G. left; eapply step_paren; eauto.  congruence. 
  reflexivity. reflexivity. traceEq.
(* condition false *)
  exploit (H0 (fun x => C(Econdition x a2 a3 ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  exploit (H4 (fun x => C(Eparen x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [E [F G]].
  simpl; intuition.
  eapply star_trans. eexact D.
  eapply star_left. left; eapply step_condition_false; eauto. congruence.
  eapply star_right. eexact G. left; eapply step_paren; eauto.  congruence. 
  reflexivity. reflexivity. traceEq.
(* sizeof *)
  simpl; intuition. apply star_refl.
(* assign *)
  exploit (H0 (fun x => C(Eassign x r ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  exploit (H2 (fun x => C(Eassign l' x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. auto. intros [E [F G]].
  simpl; intuition.
  eapply star_trans. eexact D. 
  eapply star_right. eexact G.
  left. eapply step_assign; eauto. congruence. congruence. congruence. 
  reflexivity. traceEq.
(* assignop *)
  exploit (H0 (fun x => C(Eassignop op x r tyres ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  exploit (H2 (fun x => C(Eassignop op l' x tyres ty))).
    eapply leftcontext_compose; eauto. repeat constructor. auto. intros [E [F G]].
  simpl; intuition.
  eapply star_trans. eexact D. 
  eapply star_right. eexact G.
  left. eapply step_assignop; eauto.
  rewrite B; eauto. rewrite B; rewrite F; eauto. congruence. congruence. congruence.
  reflexivity. traceEq.
(* postincr *)
  exploit (H0 (fun x => C(Epostincr id x ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  simpl; intuition.
  eapply star_right. eexact D. 
  left. eapply step_postincr; eauto. congruence. 
  traceEq.
(* comma *)
  exploit (H0 (fun x => C(Ecomma x r2 ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  exploit (H3 C). auto. intros [E [F G]].
  simpl; intuition. congruence.
  eapply star_trans. eexact D.
  eapply star_left. left; eapply step_comma; eauto. 
  eexact G.
  reflexivity. traceEq.
(* call *)
  exploit (H0 (fun x => C(Ecall x rargs ty))).
    eapply leftcontext_compose; eauto. repeat constructor. intros [A [B D]].
  exploit (H2 rf' Enil ty C); eauto. red; auto. intros [E F].
  simpl; intuition. 
  eapply star_trans. eexact D.
  eapply star_trans. eexact F. 
  eapply star_left. left; eapply step_call; eauto. congruence. 
  eapply star_right. eapply H9. red; auto. 
  right; constructor. 
  reflexivity. reflexivity. reflexivity. traceEq.
(* nil *)
  simpl; intuition. apply star_refl.
(* cons *)
  exploit (H0 (fun x => C(Ecall a0 (exprlist_app al2 (Econs x al)) ty))).
    eapply leftcontext_compose; eauto. repeat constructor. auto.
    apply exprlist_app_leftcontext; auto. intros [A [B D]].
  exploit (H2 a0 (exprlist_app al2 (Econs a1' Enil))); eauto.
  apply exprlist_app_simple; auto. simpl. auto. 
  repeat rewrite exprlist_app_assoc. simpl.  
  intros [E F].

  simpl; intuition. 
  eapply star_trans; eauto.

(* skip *)
  econstructor; split. apply star_refl. constructor.

(* do *)
  econstructor; split. 
  eapply star_left. right; constructor. 
  eapply star_right. apply H0. right; constructor.
  reflexivity. traceEq.
  constructor.

(* sequence 2 *)
  destruct (H0 f (Kseq s2 k)) as [S1 [A1 B1]]; auto. inv B1.
  destruct (H2 f k) as [S2 [A2 B2]]; auto.
  econstructor; split.
  eapply star_left. right; econstructor.
  eapply star_trans. eexact A1. 
  eapply star_left. right; constructor. eexact A2.
  reflexivity. reflexivity. traceEq.
  auto.

(* sequence 1 *)
  destruct (H0 f (Kseq s2 k)) as [S1 [A1 B1]]; auto.
  set (S2 :=
    match out with
    | Out_break => State f Sbreak k e m1
    | Out_continue => State f Scontinue k e m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. right; econstructor.
  eapply star_trans. eexact A1.
  unfold S2; inv B1.
    congruence.
    apply star_one. right; apply step_break_seq.
    apply star_one. right; apply step_continue_seq.
    apply star_refl.
    apply star_refl.
  reflexivity. traceEq.
  unfold S2; inv B1; congruence || econstructor; eauto.

(* ifthenelse true *)
  destruct (H3 f k) as [S1 [A1 B1]]; auto.
  exists S1; split.
  eapply star_left. right; apply step_ifthenelse.
  eapply star_trans. eapply H0.
  eapply star_left. right; eapply step_ifthenelse_true; eauto.
  eexact A1. 
  reflexivity. reflexivity. traceEq.
  auto.

(* ifthenelse false *)
  destruct (H3 f k) as [S1 [A1 B1]]; auto.
  exists S1; split.
  eapply star_left. right; apply step_ifthenelse.
  eapply star_trans. eapply H0.
  eapply star_left. right; eapply step_ifthenelse_false; eauto.
  eexact A1. 
  reflexivity. reflexivity. traceEq.
  auto.

(* return none *)
  econstructor; split. apply star_refl. constructor. auto.

(* return some *)
  econstructor; split.
  eapply star_left. right; apply step_return_1.
  eapply H0. traceEq.
  econstructor; eauto. 

(* break *)
  econstructor; split. apply star_refl. constructor.

(* continue *)
  econstructor; split. apply star_refl. constructor.

(* while false *)
  econstructor; split.
  eapply star_left. right; apply step_while.
  eapply star_right. apply H0. right; eapply step_while_false; eauto. 
  reflexivity. traceEq.
  constructor.

(* while stop *)
  destruct (H3 f (Kwhile2 a s k)) as [S1 [A1 B1]].
  set (S2 :=
    match out' with
    | Out_break => State f Sskip k e m2
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. right; apply step_while.
  eapply star_trans. apply H0.
  eapply star_left. right; eapply step_while_true; eauto.
  eapply star_trans. eexact A1.
  unfold S2. inversion H4; subst.
  inv B1. apply star_one. right; constructor.    
  apply star_refl.
  reflexivity. reflexivity. reflexivity. traceEq.
  unfold S2. inversion H4; subst. constructor. inv B1; econstructor; eauto.

(* while loop *)
  destruct (H3 f (Kwhile2 a s k)) as [S1 [A1 B1]].
  destruct (H6 f k) as [S2 [A2 B2]]; auto.
  exists S2; split.
  eapply star_left. right; apply step_while.
  eapply star_trans. apply H0.
  eapply star_left. right; eapply step_while_true; eauto.
  eapply star_trans. eexact A1.
  eapply star_left.
  inv H4; inv B1; right; apply step_skip_or_continue_while; auto.
  eexact A2.
  reflexivity. reflexivity. reflexivity. reflexivity. traceEq.
  auto.

(* dowhile false *)
  destruct (H0 f (Kdowhile1 a s k)) as [S1 [A1 B1]].
  exists (State f Sskip k e m2); split.
  eapply star_left. right; constructor.
  eapply star_trans. eexact A1.
  eapply star_left.
  inv H1; inv B1; right; eapply step_skip_or_continue_dowhile; eauto.
  eapply star_right. apply H3. 
  right; eapply step_dowhile_false; eauto. 
  reflexivity. reflexivity. reflexivity. traceEq. 
  constructor.

(* dowhile stop *)
  destruct (H0 f (Kdowhile1 a s k)) as [S1 [A1 B1]].
  set (S2 :=
    match out1 with
    | Out_break => State f Sskip k e m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. right; apply step_dowhile. 
  eapply star_trans. eexact A1.
  unfold S2. inversion H1; subst.
  inv B1. apply star_one. right; constructor.
  apply star_refl.
  reflexivity. traceEq.
  unfold S2. inversion H1; subst. constructor. inv B1; econstructor; eauto.

(* dowhile loop *)
  destruct (H0 f (Kdowhile1 a s k)) as [S1 [A1 B1]].
  destruct (H6 f k) as [S2 [A2 B2]]; auto.
  exists S2; split.
  eapply star_left. right; constructor.
  eapply star_trans. eexact A1.
  eapply star_left.
  inv H1; inv B1; right; eapply step_skip_or_continue_dowhile; eauto.
  eapply star_trans. apply H3.
  eapply star_left. right; eapply step_dowhile_true; eauto.
  eexact A2.
  reflexivity. reflexivity. reflexivity. reflexivity. traceEq.
  auto.

(* for start *)
  assert (a1 = Sskip \/ a1 <> Sskip). destruct a1; auto; right; congruence. 
  destruct H3.
  subst a1. inv H. apply H2; auto.
  destruct (H0 f (Kseq (Sfor Sskip a2 a3 s) k)) as [S1 [A1 B1]]; auto. inv B1.
  destruct (H2 f k) as [S2 [A2 B2]]; auto.
  exists S2; split.
  eapply star_left. right; apply step_for_start; auto.   
  eapply star_trans. eexact A1.
  eapply star_left. right; constructor. eexact A2.
  reflexivity. reflexivity. traceEq.
  auto.

(* for false *)
  econstructor; split.
  eapply star_left. right; apply step_for. 
  eapply star_right. apply H0. right; eapply step_for_false; eauto. 
  reflexivity. traceEq.
  constructor.

(* for stop *)
  destruct (H3 f (Kfor3 a2 a3 s k)) as [S1 [A1 B1]].
  set (S2 :=
    match out1 with
    | Out_break => State f Sskip k e m2
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. right; apply step_for. 
  eapply star_trans. apply H0. 
  eapply star_left. right; eapply step_for_true; eauto.
  eapply star_trans. eexact A1. 
  unfold S2. inversion H4; subst.
  inv B1. apply star_one. right; constructor. 
  apply star_refl.
  reflexivity. reflexivity. reflexivity. traceEq.
  unfold S2. inversion H4; subst. constructor. inv B1; econstructor; eauto.

(* for loop *)
  destruct (H3 f (Kfor3 a2 a3 s k)) as [S1 [A1 B1]].
  destruct (H6 f (Kfor4 a2 a3 s k)) as [S2 [A2 B2]]; auto. inv B2.
  destruct (H8 f k) as [S3 [A3 B3]]; auto.
  exists S3; split.
  eapply star_left. right; apply step_for. 
  eapply star_trans. apply H0. 
  eapply star_left. right; eapply step_for_true; eauto.
  eapply star_trans. eexact A1.
  eapply star_trans with (s2 := State f a3 (Kfor4 a2 a3 s k) e m2).
  inv H4; inv B1.
  apply star_one. right; constructor; auto. 
  apply star_one. right; constructor; auto. 
  eapply star_trans. eexact A2. 
  eapply star_left. right; constructor.
  eexact A3.
  reflexivity. reflexivity. reflexivity. reflexivity.
  reflexivity. reflexivity. traceEq.
  auto.

(* switch *)
  destruct (H2 f (Kswitch2 k)) as [S1 [A1 B1]].
  set (S2 :=
    match out with
    | Out_normal => State f Sskip k e m2
    | Out_break => State f Sskip k e m2
    | Out_continue => State f Scontinue k e m2
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. right; eapply step_switch.
  eapply star_trans. apply H0. 
  eapply star_left. right; eapply step_expr_switch.
  eapply star_trans. eexact A1. 
  unfold S2; inv B1.
    apply star_one. right; constructor. auto. 
    apply star_one. right; constructor. auto. 
    apply star_one. right; constructor. 
    apply star_refl.
    apply star_refl.
  reflexivity. reflexivity. reflexivity. traceEq.
  unfold S2. inv B1; simpl; econstructor; eauto.

(* call internal *)
  destruct (H3 f k) as [S1 [A1 B1]].
  eapply star_left. right; eapply step_internal_function; eauto.
  eapply star_right. eexact A1. 
  inv B1; simpl in H4; try contradiction.
  (* Out_normal *)
  assert (fn_return f = Tvoid /\ vres = Vundef).
    destruct (fn_return f); auto || contradiction.
  destruct H7. subst vres. right; apply step_skip_call; auto.
  (* Out_return None *)
  assert (fn_return f = Tvoid /\ vres = Vundef).
    destruct (fn_return f); auto || contradiction.
  destruct H8. subst vres.
  rewrite <- (is_call_cont_call_cont k H6). rewrite <- H7.
  right; apply step_return_0; auto.
  (* Out_return Some *)
  destruct H4.
  rewrite <- (is_call_cont_call_cont k H6). rewrite <- H7.
  right; eapply step_return_2; eauto.
  reflexivity. traceEq.

(* call external *)
  apply star_one. right; apply step_external_function; auto. 
Qed.

Lemma eval_expression_to_steps:
   forall e m a t m' v,
   eval_expression e m a t m' v ->
   forall f k,
   star step ge (ExprState f a k e m) t (ExprState f (Eval v (typeof a)) k e m').
Proof (proj1 bigstep_to_steps).

Lemma eval_expr_to_steps:
   forall e m K a t m' a',
   eval_expr e m K a t m' a' ->
   forall C f k, leftcontext K RV C ->
   simple a' /\ typeof a' = typeof a /\
   star step ge (ExprState f (C a) k e m) t (ExprState f (C a') k e m').
Proof (proj1 (proj2 bigstep_to_steps)).

Lemma eval_exprlist_to_steps:
   forall e m al t m' al',
   eval_exprlist e m al t m' al' ->
   forall a1 al2 ty C f k, leftcontext RV RV C -> simple a1 -> simplelist al2 ->
   simplelist al' /\
   star step ge (ExprState f (C (Ecall a1 (exprlist_app al2 al) ty)) k e m)
              t (ExprState f (C (Ecall a1 (exprlist_app al2 al') ty)) k e m').
Proof (proj1 (proj2 (proj2 bigstep_to_steps))).

Lemma exec_stmt_to_steps:
   forall e m s t m' out,
   exec_stmt e m s t m' out ->
   forall f k,
   exists S,
   star step ge (State f s k e m) t S /\ outcome_state_match e m' f k out S.
Proof (proj1 (proj2 (proj2 (proj2 bigstep_to_steps)))).

Lemma eval_funcall_to_steps:
  forall m fd args t m' res,
  eval_funcall m fd args t m' res ->
  forall k,
  is_call_cont k ->
  star step ge (Callstate fd args k m) t (Returnstate res k m').
Proof (proj2 (proj2 (proj2 (proj2 bigstep_to_steps)))).

Fixpoint esize (a: expr) : nat :=
  match a with
  | Eloc _ _ _ => 1%nat
  | Evar _ _ => 1%nat
  | Ederef r1 _ => S(esize r1)
  | Efield l1 _ _ => S(esize l1)
  | Eval _ _ => O
  | Evalof l1 _ => S(esize l1)
  | Eaddrof l1 _ => S(esize l1)
  | Eunop _ r1 _ => S(esize r1)
  | Ebinop _ r1 r2 _ => S(esize r1 + esize r2)%nat
  | Ecast r1 _ => S(esize r1)
  | Econdition r1 _ _ _ => S(esize r1)
  | Esizeof _ _ => 1%nat
  | Eassign l1 r2 _ => S(esize l1 + esize r2)%nat
  | Eassignop _ l1 r2 _ _ => S(esize l1 + esize r2)%nat
  | Epostincr _ l1 _ => S(esize l1)
  | Ecomma r1 r2 _ => S(esize r1 + esize r2)%nat
  | Ecall r1 rl2 _ => S(esize r1 + esizelist rl2)%nat
  | Eparen r1 _ => S(esize r1)
  end

with esizelist (el: exprlist) : nat :=
  match el with
  | Enil => O
  | Econs r1 rl2 => S(esize r1 + esizelist rl2)%nat
  end.

Lemma leftcontext_size:
  forall from to C,
  leftcontext from to C ->
  forall e1 e2,
  (esize e1 < esize e2)%nat ->
  (esize (C e1) < esize (C e2))%nat
with leftcontextlist_size:
  forall from C,
  leftcontextlist from C ->
  forall e1 e2,
  (esize e1 < esize e2)%nat ->
  (esizelist (C e1) < esizelist (C e2))%nat.
Proof.
  induction 1; intros; simpl; auto with arith. exploit leftcontextlist_size; eauto. auto with arith.
  induction 1; intros; simpl; auto with arith. exploit leftcontext_size; eauto. auto with arith.
Qed.

Lemma evalinf_funcall_steps:
  forall m fd args t k,
  evalinf_funcall m fd args t ->
  forever_N step lt ge O (Callstate fd args k m) t.
Proof.
  cofix COF.

  assert (COS: 
    forall e m s t f k,
    execinf_stmt e m s t ->
    forever_N step lt ge O (State f s k e m) t).
  cofix COS.

  assert (COE:
    forall e m K a t C f k,
    evalinf_expr e m K a t ->
    leftcontext K RV C ->
    forever_N step lt ge (esize a) (ExprState f (C a) k e m) t).
  cofix COE.

  assert (COEL:
    forall e m a t C f k a1 al ty,
    evalinf_exprlist e m a t ->
    leftcontext RV RV C -> simple a1 -> simplelist al ->
    forever_N step lt ge (esizelist a)
                   (ExprState f (C (Ecall a1 (exprlist_app al a) ty)) k e m) t).
  cofix COEL.
  intros. inv H.
(* cons left *)
  eapply forever_N_star with (a2 := (esize a0)). apply star_refl. simpl; omega. 
  eapply COE with (C := fun x => C(Ecall a1 (exprlist_app al (Econs x al0)) ty)).
  eauto. eapply leftcontext_compose; eauto. constructor. auto. 
  apply exprlist_app_leftcontext; auto. traceEq.
(* cons right *) 
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H3 
             (fun x => C(Ecall a1 (exprlist_app al (Econs x al0)) ty)) f k)
  as [P [Q R]]. 
  eapply leftcontext_compose; eauto. repeat constructor. auto. 
  apply exprlist_app_leftcontext; auto. 
  eapply forever_N_star with (a2 := (esizelist al0)).
  eexact R. simpl; omega.
  change (Econs a1' al0) with (exprlist_app (Econs a1' Enil) al0).
  rewrite <- exprlist_app_assoc.  
  eapply COEL. eauto. auto. auto. 
  apply exprlist_app_simple. auto. simpl; auto. traceEq.

  intros. inv H.
(* field *)
  eapply forever_N_star with (a2 := (esize a0)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Efield x f0 ty)). eauto. 
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* valof *)
  eapply forever_N_star with (a2 := (esize a0)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Evalof x ty)). eauto. 
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* deref *)
  eapply forever_N_star with (a2 := (esize a0)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Ederef x ty)). eauto. 
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* addrof *)
  eapply forever_N_star with (a2 := (esize a0)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Eaddrof x ty)). eauto. 
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* unop *)
  eapply forever_N_star with (a2 := (esize a0)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Eunop op x ty)). eauto. 
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* binop left *)
  eapply forever_N_star with (a2 := (esize a1)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Ebinop op x a2 ty)). eauto. 
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* binop right *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Ebinop op x a2 ty)) f k)
  as [P [Q R]]. 
  eapply leftcontext_compose; eauto. repeat constructor.
  eapply forever_N_star with (a2 := (esize a2)). eexact R. simpl; omega.
  eapply COE with (C := fun x => C(Ebinop op a1' x ty)). eauto. 
  eapply leftcontext_compose; eauto. repeat constructor. auto. traceEq.
(* cast *)
  eapply forever_N_star with (a2 := (esize a0)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Ecast x ty)). eauto. 
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* condition top *)
  eapply forever_N_star with (a2 := (esize a1)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Econdition x a2 a3 ty)). eauto. 
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* condition true *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Econdition x a2 a3 (typeof a2))) f k)
  as [P [Q R]]. 
  eapply leftcontext_compose; eauto. repeat constructor.
  eapply forever_N_plus. eapply plus_right. eexact R. 
  left; eapply step_condition_true; eauto. congruence. 
  reflexivity. 
  eapply COE with (C := fun x => (C (Eparen x (typeof a2)))). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* condition false *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Econdition x a2 a3 (typeof a3))) f k)
  as [P [Q R]]. 
  eapply leftcontext_compose; eauto. repeat constructor.
  eapply forever_N_plus. eapply plus_right. eexact R. 
  left; eapply step_condition_false; eauto. congruence. 
  reflexivity. 
  eapply COE with (C := fun x => (C (Eparen x (typeof a3)))). eauto.
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* assign left *)
  eapply forever_N_star with (a2 := (esize a1)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Eassign x a2 ty)). eauto. 
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* assign right *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Eassign x a2 ty)) f k)
  as [P [Q R]]. 
  eapply leftcontext_compose; eauto. repeat constructor.
  eapply forever_N_star with (a2 := (esize a2)). eexact R. simpl; omega.
  eapply COE with (C := fun x => C(Eassign a1' x ty)). eauto. 
  eapply leftcontext_compose; eauto. repeat constructor. auto. traceEq.
(* assignop left *)
  eapply forever_N_star with (a2 := (esize a1)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Eassignop op x a2 tyres ty)). eauto. 
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* assignop right *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Eassignop op x a2 tyres ty)) f k)
  as [P [Q R]]. 
  eapply leftcontext_compose; eauto. repeat constructor.
  eapply forever_N_star with (a2 := (esize a2)). eexact R. simpl; omega.
  eapply COE with (C := fun x => C(Eassignop op a1' x tyres ty)). eauto. 
  eapply leftcontext_compose; eauto. repeat constructor. auto. traceEq.
(* postincr *)
  eapply forever_N_star with (a2 := (esize a0)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Epostincr id x ty)). eauto. 
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* comma left *)
  eapply forever_N_star with (a2 := (esize a1)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Ecomma x a2 ty)). eauto. 
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* comma right *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Ecomma x a2 (typeof a2))) f k)
  as [P [Q R]]. 
  eapply leftcontext_compose; eauto. repeat constructor.
  eapply forever_N_plus. eapply plus_right. eexact R. 
  left; eapply step_comma; eauto. reflexivity.  
  eapply COE with (C := C); eauto. traceEq.
(* call left *)
  eapply forever_N_star with (a2 := (esize a1)). apply star_refl. simpl; omega.
  eapply COE with (C := fun x => C(Ecall x a2 ty)). eauto. 
  eapply leftcontext_compose; eauto. repeat constructor. traceEq.
(* call right *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Ecall x a2 ty)) f k)
  as [P [Q R]]. 
  eapply leftcontext_compose; eauto. repeat constructor.
  eapply forever_N_star with (a2 := (esizelist a2)). eexact R. simpl; omega.
  eapply COEL with (al := Enil). eauto. auto. auto. red; auto. traceEq.
(* call *)
  destruct (eval_expr_to_steps _ _ _ _ _ _ _ H1 (fun x => C(Ecall x rargs ty)) f k)
  as [P [Q R]]. 
  eapply leftcontext_compose; eauto. repeat constructor.
  destruct (eval_exprlist_to_steps _ _ _ _ _ _ H2 rf' Enil ty C f k)
  as [S T]. auto. auto. simpl; auto.
  eapply forever_N_plus. eapply plus_right.
  eapply star_trans. eexact R. eexact T. reflexivity.
  simpl. left; eapply step_call; eauto. congruence. reflexivity. 
  apply COF. eauto. traceEq. 

(* statements *)
  intros. inv H.
(* do *)
  eapply forever_N_plus. apply plus_one; right; constructor. 
  eapply COE with (C := fun x => x); eauto. constructor. traceEq.
(* seq 1 *)
  eapply forever_N_plus. apply plus_one; right; constructor. 
  eapply COS; eauto. traceEq.
(* seq 2 *)
  destruct (exec_stmt_to_steps _ _ _ _ _ _ H0 f (Kseq s2 k)) as [S1 [A1 B1]]; auto. inv B1.
  eapply forever_N_plus. 
  eapply plus_left. right; constructor. 
  eapply star_right. eauto. right; constructor.
  reflexivity. reflexivity. 
  eapply COS; eauto. traceEq.
(* if test *)
  eapply forever_N_plus. apply plus_one; right; constructor. 
  eapply COE with (C := fun x => x); eauto. constructor. traceEq.
(* if true *)
  eapply forever_N_plus.
  eapply plus_left. right; constructor.
  eapply star_right. eapply eval_expression_to_steps; eauto.
  right. apply step_ifthenelse_true. auto. 
  reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* if false *)
  eapply forever_N_plus.
  eapply plus_left. right; constructor.
  eapply star_right. eapply eval_expression_to_steps; eauto.
  right. apply step_ifthenelse_false. auto. 
  reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* return some *)
  eapply forever_N_plus. apply plus_one; right; constructor.
  eapply COE with (C := fun x => x); eauto. constructor. traceEq.
(* while test *)
  eapply forever_N_plus. apply plus_one; right; constructor.
  eapply COE with (C := fun x => x); eauto. constructor. traceEq.
(* while body *)
  eapply forever_N_plus.
  eapply plus_left. right; constructor. 
  eapply star_right. eapply eval_expression_to_steps; eauto.
  right; apply step_while_true; auto.
  reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* while loop *)
  destruct (exec_stmt_to_steps _ _ _ _ _ _ H2 f (Kwhile2 a s0 k)) as [S1 [A1 B1]]; auto.
  eapply forever_N_plus.
  eapply plus_left. right; constructor. 
  eapply star_trans. eapply eval_expression_to_steps; eauto.
  eapply star_left. right; apply step_while_true; auto.
  eapply star_trans. eexact A1. 
  inv H3; inv B1; apply star_one; right; apply step_skip_or_continue_while; auto.
  reflexivity. reflexivity. reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* dowhile body *)
  eapply forever_N_plus. apply plus_one; right; constructor.
  eapply COS; eauto. traceEq.
(* dowhile test *)
  destruct (exec_stmt_to_steps _ _ _ _ _ _ H0 f (Kdowhile1 a s0 k)) as [S1 [A1 B1]]; auto.
  eapply forever_N_plus.
  eapply plus_left. right; constructor. 
  eapply star_trans. eexact A1.
  eapply star_one. right. inv H1; inv B1; apply step_skip_or_continue_dowhile; auto.
  reflexivity. reflexivity.
  eapply COE with (C := fun x => x); eauto. constructor. traceEq.
(* dowhile loop *)
  destruct (exec_stmt_to_steps _ _ _ _ _ _ H0 f (Kdowhile1 a s0 k)) as [S1 [A1 B1]]; auto.
  eapply forever_N_plus.
  eapply plus_left. right; constructor. 
  eapply star_trans. eexact A1.
  eapply star_left. right. inv H1; inv B1; apply step_skip_or_continue_dowhile; auto.
  eapply star_right. eapply eval_expression_to_steps; eauto.
  right; apply step_dowhile_true; auto.
  reflexivity. reflexivity. reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* for start 1 *)
  assert (a1 <> Sskip). red; intros; subst a1; inv H0.
  eapply forever_N_plus. apply plus_one. right. constructor. auto.
  eapply COS; eauto. traceEq.
(* for start 2 *)
  destruct (exec_stmt_to_steps _ _ _ _ _ _ H0 f (Kseq (Sfor Sskip a2 a3 s0) k)) as [S1 [A1 B1]]; auto. inv B1.
  eapply forever_N_plus.
  eapply plus_left. right; constructor. auto. 
  eapply star_trans. eexact A1.
  apply star_one. right; constructor. 
  reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* for test *)
  eapply forever_N_plus. apply plus_one; right; apply step_for.
  eapply COE with (C := fun x => x); eauto. constructor. traceEq.
(* for body *)
  eapply forever_N_plus.
  eapply plus_left. right; apply step_for.
  eapply star_right. eapply eval_expression_to_steps; eauto.
  right; apply step_for_true; auto.
  reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* for next *)
  destruct (exec_stmt_to_steps _ _ _ _ _ _ H2 f (Kfor3 a2 a3 s0 k)) as [S1 [A1 B1]]; auto.
  eapply forever_N_plus.
  eapply plus_left. right; apply step_for.
  eapply star_trans. eapply eval_expression_to_steps; eauto.
  eapply star_left. right; apply step_for_true; auto.
  eapply star_trans. eexact A1. 
  inv H3; inv B1; apply star_one; right; apply step_skip_or_continue_for3; auto.
  reflexivity. reflexivity. reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* for loop *)
  destruct (exec_stmt_to_steps _ _ _ _ _ _ H2 f (Kfor3 a2 a3 s0 k)) as [S1 [A1 B1]]; auto.
  destruct (exec_stmt_to_steps _ _ _ _ _ _ H4 f (Kfor4 a2 a3 s0 k)) as [S2 [A2 B2]]; auto. inv B2.
  eapply forever_N_plus.
  eapply plus_left. right; apply step_for.
  eapply star_trans. eapply eval_expression_to_steps; eauto.
  eapply star_left. right; apply step_for_true; auto.
  eapply star_trans. eexact A1.
  eapply star_left.
  inv H3; inv B1; right; apply step_skip_or_continue_for3; auto.
  eapply star_right. eexact A2. 
  right; constructor.
  reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity.
  eapply COS; eauto. traceEq.
(* switch expr *)
  eapply forever_N_plus. apply plus_one; right; constructor.
  eapply COE with (C := fun x => x); eauto. constructor. traceEq.
(* switch body *)
  eapply forever_N_plus.
  eapply plus_left. right; constructor. 
  eapply star_right. eapply eval_expression_to_steps; eauto. 
  right; constructor. 
  reflexivity. reflexivity. 
  eapply COS; eauto. traceEq. 

(* funcalls *)
  intros. inv H.
  eapply forever_N_plus. apply plus_one. right; econstructor; eauto. 
  eapply COS; eauto. traceEq.
Qed.

End BIGSTEP.

(** ** Whole-program behaviors, big-step style. *)

Inductive bigstep_program_terminates (p: program): trace -> int -> Prop :=
  | bigstep_program_terminates_intro: forall b f m0 m1 t r,
      let ge := Genv.globalenv p in 
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil (Tint I32 Signed) ->
      eval_funcall ge m0 f nil t m1 (Vint r) ->
      bigstep_program_terminates p t r.

Inductive bigstep_program_diverges (p: program): traceinf -> Prop :=
  | bigstep_program_diverges_intro: forall b f m0 t,
      let ge := Genv.globalenv p in 
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil (Tint I32 Signed) ->
      evalinf_funcall ge m0 f nil t ->
      bigstep_program_diverges p t.

Theorem bigstep_program_terminates_exec:
  forall prog t r,
  bigstep_program_terminates prog t r -> exec_program prog (Terminates t r).
Proof.
  intros. inv H. 
  econstructor.
  econstructor; eauto.
  apply eval_funcall_to_steps. eauto. red; auto. 
  econstructor.
Qed.

Theorem bigstep_program_diverges_exec:
  forall prog T,
  bigstep_program_diverges prog T ->
  exec_program prog (Reacts T) \/
  exists t, exec_program prog (Diverges t) /\ traceinf_prefix t T.
Proof.
  intros. inv H.
  set (st := Callstate f nil Kstop m0).
  assert (forever step ge st T). 
    eapply forever_N_forever with (order := lt).
    apply lt_wf. 
    eapply evalinf_funcall_steps; eauto. 
  destruct (forever_silent_or_reactive _ _ _ _ _ _ H)
  as [A | [t [s' [T' [B [C D]]]]]]. 
  left. econstructor. econstructor; eauto. eauto.
  right. exists t. split.
  econstructor. econstructor; eauto. eauto. auto. 
  subst T. rewrite <- (E0_right t) at 1. apply traceinf_prefix_app. constructor.
Qed.

