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

(* A solver for unification constraints. *)

Require Import Recdef Coqlib Maps Errors.

Local Open Scope nat_scope.
Local Open Scope error_monad_scope.

(** This module provides a solver for sets of unification constraints of the
  following kinds: [T(x) = base-type] or [T(x) = T(y)].
  The unknowns are the types [T(x)] of every identifier [x]. *)

(** The interface for base types. *)

Module Type TYPE_ALGEBRA.

Parameter t: Type.
Parameter eq: forall (x y: t), {x=y} + {x<>y}.
Parameter default: t.

End TYPE_ALGEBRA.

(** The constraint solver. *)

Module UniSolver (T: TYPE_ALGEBRA).

(* The current set of constraints is represented by a record with two components:
- [te_typ]: a partial map from variables to types
- [te_equ]: a list of pairs [(x,y)] of variables, indicating that
  the type of [x] must be equal to the type of [y].
*)

Definition constraint : Type := (positive * positive)%type.

Record typenv : Type := Typenv {
  te_typ: PTree.t T.t;       (**r mapping var -> typ *)
  te_equ: list constraint    (**r additional equality constraints *)
}.

Definition initial : typenv := {| te_typ := PTree.empty _; te_equ := nil |}.

(** Add the constraint [T(x) = ty]. *)

Definition set (e: typenv) (x: positive) (ty: T.t) : res typenv :=
  match e.(te_typ)!x with
  | None =>
      OK {| te_typ := PTree.set x ty e.(te_typ);
            te_equ := e.(te_equ) |}
  | Some ty' =>
      if T.eq ty ty'
      then OK e
      else Error (MSG "bad definition/use of variable " :: POS x :: nil)
  end.

Fixpoint set_list (e: typenv) (rl: list positive) (tyl: list T.t) {struct rl}: res typenv :=
  match rl, tyl with
  | nil, nil => OK e
  | r1::rs, ty1::tys => do e1 <- set e r1 ty1; set_list e1 rs tys
  | _, _ => Error (msg "arity mismatch")
  end.

(** Add the constraint [T(x) = T(y)].
    The boolean result is [true] if the types of [x] or [y] could be
    made more precise.  Otherwise, [te_typ] does not change and
    [false] is returned. *)

Definition move (e: typenv) (r1 r2: positive) : res (bool * typenv) :=
  if peq r1 r2 then OK (false, e) else
  match e.(te_typ)!r1, e.(te_typ)!r2 with
  | None, None =>
      OK (false, {| te_typ := e.(te_typ); te_equ := (r1, r2) :: e.(te_equ) |})
  | Some ty1, None =>
      OK (true, {| te_typ := PTree.set r2 ty1 e.(te_typ); te_equ := e.(te_equ) |})
  | None, Some ty2 =>
      OK (true, {| te_typ := PTree.set r1 ty2 e.(te_typ); te_equ := e.(te_equ) |})
  | Some ty1, Some ty2 =>
      if T.eq ty1 ty2
      then OK (false, e)
      else Error(MSG "ill-typed move from " :: POS r1 :: MSG " to " :: POS r2 :: nil)
  end.

(** Solve the remaining subtyping constraints by iteration. *)

Fixpoint solve_rec (e: typenv) (changed: bool) (q: list constraint) : res (typenv * bool) :=
  match q with
  | nil =>
      OK (e, changed)
  | (r1, r2) :: q' =>
      do (changed1, e1) <- move e r1 r2; solve_rec e1 (changed || changed1) q'
  end.

(** Measuring the state *)

Lemma move_shape:
  forall e r1 r2 changed e',
  move e r1 r2 = OK (changed, e') ->
  (e'.(te_equ) = e.(te_equ) \/ e'.(te_equ) = (r1, r2) :: e.(te_equ))
  /\ (changed = true -> e'.(te_equ) = e.(te_equ)).
Proof.
  unfold move; intros.
  destruct (peq r1 r2). inv H. auto.
  destruct e.(te_typ)!r1 as [ty1|]; destruct e.(te_typ)!r2 as [ty2|]; inv H; simpl.
  destruct (T.eq ty1 ty2); inv H1. auto.
  auto.
  auto.
  split. auto. intros. discriminate.
Qed.

Lemma length_move:
  forall e r1 r2 changed e',
  move e r1 r2 = OK (changed, e') ->
  length e'.(te_equ) + (if changed then 1 else 0) <= S(length e.(te_equ)).
Proof.
  unfold move; intros.
  destruct (peq r1 r2). inv H. omega.
  destruct e.(te_typ)!r1 as [ty1|]; destruct e.(te_typ)!r2 as [ty2|]; inv H; simpl.
  destruct (T.eq ty1 ty2); inv H1. omega.
  omega.
  omega.
  omega.
Qed.

Lemma length_solve_rec:
  forall q e ch e' ch',
  solve_rec e ch q = OK (e', ch') ->
  length e'.(te_equ) + (if ch' && negb ch then 1 else 0) <= length e.(te_equ) + length q.
Proof.
  induction q; simpl; intros.
- inv H. replace (ch' && negb ch') with false. omega. destruct ch'; auto.
- destruct a as [r1 r2]; monadInv H. rename x0 into e0. rename x into ch0.
  exploit IHq; eauto. intros A.
  exploit length_move; eauto. intros B.
  set (X := (if ch' && negb (ch || ch0) then 1 else 0)) in *.
  set (Y := (if ch0 then 1 else 0)) in *.
  set (Z := (if ch' && negb ch then 1 else 0)) in *.
  cut (Z <= X + Y). intros. omega.
  unfold X, Y, Z. destruct ch'; destruct ch; destruct ch0; simpl; auto.
Qed.

Definition weight_typenv (e: typenv) : nat := length e.(te_equ).


(** Iterative solving of the remaining constraints *)

Function solve_constraints (e: typenv) {measure weight_typenv e}: res typenv :=
  match solve_rec {| te_typ := e.(te_typ); te_equ := nil |} false e.(te_equ) with
  | OK(e', false) => OK e                   (**r no more changes, fixpoint reached *)
  | OK(e', true)  => solve_constraints e'   (**r one more iteration *)
  | Error msg => Error msg
  end.
Proof.
  intros. exploit length_solve_rec; eauto. simpl. intros.
  unfold weight_typenv. omega.
Qed.

Definition typassign := positive -> T.t.

Definition makeassign (e: typenv) : typassign :=
  fun x => match e.(te_typ)!x with Some ty => ty | None => T.default end.

Definition solve (e: typenv) : res typassign :=
  do e' <- solve_constraints e; OK(makeassign e').

(** What it means to be a solution *)

Definition satisf (te: typassign) (e: typenv) : Prop :=
   (forall x ty, e.(te_typ)!x = Some ty -> te x = ty)
/\ (forall x y, In (x, y) e.(te_equ) -> te x = te y).

Lemma satisf_initial: forall te, satisf te initial.
Proof.
  unfold initial; intros; split; simpl; intros.
  rewrite PTree.gempty in H; discriminate.
  contradiction.
Qed.

(** Soundness proof *)

Lemma set_incr:
  forall te x ty e e', set e x ty = OK e' -> satisf te e' -> satisf te e.
Proof.
  unfold set; intros. destruct (te_typ e)!x as [ty'|] eqn:E.
- destruct (T.eq ty ty'); inv H. auto.
- inv H. destruct H0 as [A B]; simpl in *. red; split; intros; auto.
  apply A. rewrite PTree.gso by congruence. auto.
Qed.

Hint Resolve set_incr: ty.

Lemma set_sound:
  forall te x ty e e', set e x ty = OK e' -> satisf te e' -> te x = ty.
Proof.
  unfold set; intros. destruct H0 as [P Q].
  destruct (te_typ e)!x as [ty'|] eqn:E.
- destruct (T.eq ty ty'); inv H. eauto.
- inv H. simpl in P. apply P. apply PTree.gss.
Qed.

Lemma set_list_incr:
  forall te xl tyl e e', set_list e xl tyl = OK e' -> satisf te e' -> satisf te e.
Proof.
  induction xl; destruct tyl; simpl; intros; monadInv H; eauto with ty.
Qed.

Hint Resolve set_list_incr: ty.

Lemma set_list_sound:
  forall te xl tyl e e', set_list e xl tyl = OK e' -> satisf te e' -> map te xl = tyl.
Proof.
  induction xl; destruct tyl; simpl; intros; monadInv H.
  auto.
  f_equal. eapply set_sound; eauto with ty. eauto.
Qed.

Lemma move_incr:
  forall te e r1 r2 e' changed,
  move e r1 r2 = OK(changed, e') -> satisf te e' -> satisf te e.
Proof.
  unfold move; intros. destruct H0 as [P Q].
  destruct (peq r1 r2). inv H; split; auto.
  destruct (te_typ e)!r1 as [ty1|] eqn:E1;
  destruct (te_typ e)!r2 as [ty2|] eqn:E2.
- destruct (T.eq ty1 ty2); inv H. split; auto.
- inv H; simpl in *; split; auto. intros. apply P.
  rewrite PTree.gso by congruence. auto.
- inv H; simpl in *; split; auto. intros. apply P.
  rewrite PTree.gso by congruence. auto.
- inv H; simpl in *; split; auto.
Qed.

Hint Resolve move_incr: ty.

Lemma move_sound:
  forall te e r1 r2 e' changed,
  move e r1 r2 = OK(changed, e') -> satisf te e' -> te r1 = te r2.
Proof.
  unfold move; intros. destruct H0 as [P Q].
  destruct (peq r1 r2). congruence.
  destruct (te_typ e)!r1 as [ty1|] eqn:E1;
  destruct (te_typ e)!r2 as [ty2|] eqn:E2.
- destruct (T.eq ty1 ty2); inv H. erewrite ! P by eauto. auto.
- inv H; simpl in *. rewrite (P r1 ty1). rewrite (P r2 ty1). auto.
  apply PTree.gss. rewrite PTree.gso by congruence. auto.
- inv H; simpl in *. rewrite (P r1 ty2). rewrite (P r2 ty2). auto.
  rewrite PTree.gso by congruence. auto. apply PTree.gss.
- inv H; simpl in *. apply Q; auto.
Qed.

Lemma solve_rec_incr:
  forall te q e changed e' changed',
  solve_rec e changed q = OK(e', changed') -> satisf te e' -> satisf te e.
Proof.
  induction q; simpl; intros.
- inv H. auto.
- destruct a as [r1 r2]; monadInv H. eauto with ty.
Qed.

Lemma solve_rec_sound:
  forall te r1 r2 q e changed e' changed',
  solve_rec e changed q = OK(e', changed') -> In (r1, r2) q -> satisf te e' ->
  te r1 = te r2.
Proof.
  induction q; simpl; intros.
- contradiction.
- destruct a as [r3 r4]; monadInv H. destruct H0.
  + inv H. eapply move_sound; eauto. eapply solve_rec_incr; eauto.
  + eapply IHq; eauto with ty.
Qed.

Lemma move_false:
  forall e r1 r2 e',
  move e r1 r2 = OK(false, e') ->
  te_typ e' = te_typ e /\ makeassign e r1 = makeassign e r2.
Proof.
  unfold move; intros.
  destruct (peq r1 r2). inv H. split; auto.
  unfold makeassign;
  destruct (te_typ e)!r1 as [ty1|] eqn:E1;
  destruct (te_typ e)!r2 as [ty2|] eqn:E2.
- destruct (T.eq ty1 ty2); inv H. auto.
- discriminate.
- discriminate.
- inv H. split; auto.
Qed.

Lemma solve_rec_false:
  forall r1 r2 q e changed e',
  solve_rec e changed q = OK(e', false) ->
  changed = false /\
  (In (r1, r2) q -> makeassign e r1 = makeassign e r2).
Proof.
  induction q; simpl; intros.
- inv H. tauto.
- destruct a as [r3 r4]; monadInv H.
  exploit IHq; eauto. intros [P Q].
  destruct changed; try discriminate. destruct x; try discriminate.
  exploit move_false; eauto. intros [U V].
  split. auto. intros [A|A]. inv A. auto. exploit Q; auto.
  unfold makeassign; rewrite U; auto.
Qed.

Lemma solve_constraints_incr:
  forall te e e', solve_constraints e = OK e' -> satisf te e' -> satisf te e.
Proof.
  intros te e; functional induction (solve_constraints e); intros.
- inv H. auto.
- exploit solve_rec_incr; eauto. intros [A B].
  split; auto. intros; eapply solve_rec_sound; eauto.
- discriminate.
Qed.

Lemma solve_constraints_sound:
  forall e e', solve_constraints e = OK e' -> satisf (makeassign e') e'.
Proof.
  intros e0; functional induction (solve_constraints e0); intros.
- inv H. split; intros.
  unfold makeassign; rewrite H. split; auto with ty.
  exploit solve_rec_false. eauto. intros [A B]. eapply B; eauto.
- eauto.
- discriminate.
Qed.

Theorem solve_sound:
  forall e te, solve e = OK te -> satisf te e.
Proof.
  unfold solve; intros. monadInv H.
  eapply solve_constraints_incr. eauto. eapply solve_constraints_sound; eauto.
Qed.

(** Completeness proof *)

Lemma set_complete:
  forall te e x ty,
  satisf te e -> te x = ty -> exists e', set e x ty = OK e' /\ satisf te e'.
Proof.
  unfold set; intros. generalize H; intros [P Q].
  destruct (te_typ e)!x as [ty1|] eqn:E.
- replace ty1 with ty. rewrite dec_eq_true. exists e; auto.
  exploit P; eauto. congruence.
- econstructor; split; eauto. split; simpl; intros; auto.
  rewrite PTree.gsspec in H1. destruct (peq x0 x). congruence. eauto.
Qed.

Lemma set_list_complete:
  forall te xl tyl e,
  satisf te e -> map te xl = tyl ->
  exists e', set_list e xl tyl = OK e' /\ satisf te e'.
Proof.
  induction xl; intros; inv H0; simpl.
  econstructor; eauto.
  exploit (set_complete te e a (te a)); auto. intros (e1 & P & Q).
  exploit (IHxl (map te xl) e1); auto. intros (e2 & U & V).
  exists e2; split; auto. rewrite P; auto.
Qed.

Lemma move_complete:
  forall te e r1 r2,
  satisf te e -> te r1 = te r2 ->
  exists changed e', move e r1 r2 = OK(changed, e') /\ satisf te e'.
Proof.
  unfold move; intros. elim H; intros P Q.
  assert (Q': forall x y, In (x, y) ((r1, r2) :: te_equ e) -> te x = te y).
  { intros. destruct H1; auto. congruence. }
  destruct (peq r1 r2). econstructor; econstructor; eauto.
  destruct (te_typ e)!r1 as [ty1|] eqn:E1;
  destruct (te_typ e)!r2 as [ty2|] eqn:E2.
- replace ty2 with ty1. rewrite dec_eq_true. econstructor; econstructor; eauto.
  exploit (P r1); eauto. exploit (P r2); eauto. congruence.
- econstructor; econstructor; split; eauto.
  split; simpl; intros; auto. rewrite PTree.gsspec in H1. destruct (peq x r2).
  inv H1. rewrite <- H0. eauto.
  eauto.
- econstructor; econstructor; split; eauto.
  split; simpl; intros; auto. rewrite PTree.gsspec in H1. destruct (peq x r1).
  inv H1. rewrite H0. eauto.
  eauto.
- econstructor; econstructor; split; eauto.
  split; eauto.
Qed.

Lemma solve_rec_complete:
  forall te q e changed,
  satisf te e ->
  (forall r1 r2, In (r1, r2) q -> te r1 = te r2) ->
  exists e' changed', solve_rec e changed q = OK(e', changed') /\ satisf te e'.
Proof.
  induction q; simpl; intros.
- econstructor; econstructor; eauto.
- destruct a as [r1 r2].
  exploit (move_complete te e r1 r2); auto. intros (changed1 & e1 & A & B).
  exploit (IHq e1 (changed || changed1)); auto. intros (e' & changed' & C & D).
  exists e'; exists changed'. rewrite A; simpl; rewrite C; auto.
Qed.

Lemma solve_constraints_complete:
  forall te e, satisf te e -> exists e', solve_constraints e = OK e' /\ satisf te e'.
Proof.
  intros te e. functional induction (solve_constraints e); intros.
- exists e; auto.
- exploit (solve_rec_complete te (te_equ e) {| te_typ := te_typ e; te_equ := nil |} false).
  destruct H; split; auto. simpl; tauto.
  destruct H; auto.
  intros (e1 & changed1 & P & Q).
  apply IHr. congruence.
- exploit (solve_rec_complete te (te_equ e) {| te_typ := te_typ e; te_equ := nil |} false).
  destruct H; split; auto. simpl; tauto.
  destruct H; auto.
  intros (e1 & changed1 & P & Q).
  congruence.
Qed.

Lemma solve_complete:
  forall te e, satisf te e -> exists te', solve e = OK te'.
Proof.
  intros. unfold solve.
  destruct (solve_constraints_complete te e H) as (e' & P & Q).
  econstructor. rewrite P. simpl. eauto.
Qed.

End UniSolver.

