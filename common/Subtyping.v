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

(* A solver for subtyping constraints. *)

Require Import Recdef Coqlib Maps Errors.

Local Open Scope nat_scope.
Local Open Scope error_monad_scope.

(** This module provides a solver for sets of subtyping constraints of the
  following kinds: [base-type <: T(x)] or [T(x) <: base-type] or [T(x) <: T(y)].
  The unknowns are the types [T(x)] of every identifier [x]. *)

(** The interface for base types and the subtyping relation. *)

Module Type TYPE_ALGEBRA.

(** Type expressions *)

Parameter t: Type.
Parameter eq: forall (x y: t), {x=y} + {x<>y}.
Parameter default: t.

(** Subtyping *)

Parameter sub: t -> t -> Prop.
Axiom sub_refl: forall x, sub x x.
Axiom sub_trans: forall x y z, sub x y -> sub y z -> sub x z.
Parameter sub_dec: forall x y, {sub x y} + {~sub x y}.

(** Least upper bounds. [lub x y] is specified only when [x] and [y] have
  a common supertype; it can be arbitrary otherwise. *)

Parameter lub: t -> t -> t.
Axiom lub_left: forall x y z, sub x z -> sub y z -> sub x (lub x y).
Axiom lub_right: forall x y z, sub x z -> sub y z -> sub y (lub x y).
Axiom lub_min: forall x y z, sub x z -> sub y z -> sub (lub x y) z.

(** Greater lower bounds. [glb x y] is specified only when [x] and [y] have
  a common subtype; it can be arbitrary otherwise.*)

Parameter glb: t -> t -> t.
Axiom glb_left: forall x y z, sub z x -> sub z y -> sub (glb x y) x.
Axiom glb_right: forall x y z, sub z x -> sub z y -> sub (glb x y) y.
Axiom glb_max: forall x y z, sub z x -> sub z y -> sub z (glb x y).

(** Low and high bounds for a given type. *)
Parameter low_bound: t -> t.
Parameter high_bound: t -> t.
Axiom low_bound_sub: forall t, sub (low_bound t) t.
Axiom low_bound_minorant: forall x y, sub x y -> sub (low_bound y) x.
Axiom high_bound_sub: forall t, sub t (high_bound t).
Axiom high_bound_majorant: forall x y, sub x y -> sub y (high_bound x).

(** Measure over types *)

Parameter weight: t -> nat.
Parameter max_weight: nat.
Axiom weight_range: forall t, weight t <= max_weight.
Axiom weight_sub: forall x y, sub x y -> weight x <= weight y.
Axiom weight_sub_strict: forall x y, sub x y -> x <> y -> weight x < weight y.

End TYPE_ALGEBRA.

(** The constraint solver. *)

Module SubSolver (T: TYPE_ALGEBRA).

(* The current set of constraints is represented by a record with two components:
- [te_typ]: a partial map from variables to pairs [tlo, thi]
  of types, representing the low and high bounds for this variable.
- [te_sub]: a list of pairs [(x,y)] of variables, indicating that
  the type of [x] must be a subtype of the type of [y].
*)

Inductive bounds : Type := B (lo: T.t) (hi: T.t) (SUB: T.sub lo hi).

Definition constraint : Type := (positive * positive)%type.

Record typenv : Type := Typenv {
  te_typ: PTree.t bounds;    (**r mapping var -> low & high bounds *)
  te_sub: list constraint    (**r additional subtyping constraints *)
}.

Definition initial : typenv := {| te_typ := PTree.empty _; te_sub := nil |}.

(** Add the constraint [ty <: T(x)]. *)

Definition type_def (e: typenv) (x: positive) (ty: T.t) : res typenv :=
  match e.(te_typ)!x with
  | None =>
      let b := B ty (T.high_bound ty) (T.high_bound_sub ty) in
      OK {| te_typ := PTree.set x b e.(te_typ);
            te_sub := e.(te_sub) |}
  | Some(B lo hi s1) =>
      match T.sub_dec ty hi with
      | left s2 =>
          let lo' := T.lub lo ty in
          if T.eq lo lo' then OK e else
            let b := B lo' hi (T.lub_min lo ty hi s1 s2) in
            OK {| te_typ := PTree.set x b e.(te_typ);
                  te_sub := e.(te_sub) |}
      | right _ =>
          Error (MSG "bad definition of variable " :: POS x :: nil)
      end
  end.

Fixpoint type_defs (e: typenv) (rl: list positive) (tyl: list T.t) {struct rl}: res typenv :=
  match rl, tyl with
  | nil, nil => OK e
  | r1::rs, ty1::tys => do e1 <- type_def e r1 ty1; type_defs e1 rs tys
  | _, _ => Error (msg "arity mismatch")
  end.

(** Add the constraint [T(x) <: ty]. *)

Definition type_use (e: typenv) (x: positive) (ty: T.t) : res typenv :=
  match e.(te_typ)!x with
  | None =>
      let b := B (T.low_bound ty) ty (T.low_bound_sub ty) in
      OK {| te_typ := PTree.set x b e.(te_typ);
            te_sub := e.(te_sub) |}
  | Some(B lo hi s1) =>
      match T.sub_dec lo ty with
      | left s2 =>
          let hi' := T.glb hi ty in
          if T.eq hi hi' then OK e else
            let b := B lo hi' (T.glb_max hi ty lo s1 s2) in
            OK {| te_typ := PTree.set x b e.(te_typ);
                  te_sub := e.(te_sub) |}
      | right _ =>
          Error (MSG "bad use of variable " :: POS x :: nil)
      end
  end.

Fixpoint type_uses (e: typenv) (rl: list positive) (tyl: list T.t) {struct rl}: res typenv :=
  match rl, tyl with
  | nil, nil => OK e
  | r1::rs, ty1::tys => do e1 <- type_use e r1 ty1; type_uses e1 rs tys
  | _, _ => Error (msg "arity mismatch")
  end.

(** Add the constraint [T(x) <: T(y)].
    The boolean result is [true] if the types of [r1] and [r2] could be
    made more precise.  Otherwise, [te_typ] does not change and
    [false] is returned. *)

Definition type_move (e: typenv) (r1 r2: positive) : res (bool * typenv) :=
  if peq r1 r2 then OK (false, e) else
  match e.(te_typ)!r1, e.(te_typ)!r2 with
  | None, None =>
      OK (false, {| te_typ := e.(te_typ); te_sub := (r1, r2) :: e.(te_sub) |})
  | Some(B lo1 hi1 s1), None =>
      let b2 := B lo1 (T.high_bound lo1) (T.high_bound_sub lo1) in
      OK (true, {| te_typ := PTree.set r2 b2 e.(te_typ);
                   te_sub := if T.sub_dec hi1 lo1 then e.(te_sub)
                             else (r1, r2) :: e.(te_sub) |})
  | None, Some(B lo2 hi2 s2) =>
      let b1 := B (T.low_bound hi2) hi2 (T.low_bound_sub hi2) in
      OK (true, {| te_typ := PTree.set r1 b1 e.(te_typ);
                   te_sub := if T.sub_dec hi2 lo2 then e.(te_sub)
                             else (r1, r2) :: e.(te_sub) |})
  | Some(B lo1 hi1 s1), Some(B lo2 hi2 s2) =>
      if T.sub_dec hi1 lo2 then
        (* The constraint is always true, don't record it *)
        OK (false, e)
      else match T.sub_dec lo1 hi2 with
      | left s =>
          (* Tighten the bounds on [r1] and [r2] when possible and record
             the constraint. *)
          let lo2' := T.lub lo1 lo2 in
          let hi1' := T.glb hi1 hi2 in
          let b1 := B lo1 hi1' (T.glb_max hi1 hi2 lo1 s1 s) in
          let b2 := B lo2' hi2 (T.lub_min lo1 lo2 hi2 s s2) in
          if T.eq lo2 lo2' then
            if T.eq hi1 hi1' then
              OK (false, {| te_typ := e.(te_typ);
                            te_sub := (r1, r2) :: e.(te_sub) |})
            else
              OK (true, {| te_typ := PTree.set r1 b1 e.(te_typ);
                           te_sub := (r1, r2) :: e.(te_sub) |})
          else
            if T.eq hi1 hi1' then
              OK (true, {| te_typ := PTree.set r2 b2 e.(te_typ);
                           te_sub := (r1, r2) :: e.(te_sub) |})
            else
              OK (true, {| te_typ := PTree.set r2 b2 (PTree.set r1 b1 e.(te_typ));
                           te_sub := (r1, r2) :: e.(te_sub) |})
      | right _ =>
          Error(MSG "ill-typed move from " :: POS r1 :: MSG " to " :: POS r2 :: nil)
      end
  end.

(** Solve the remaining subtyping constraints by iteration. *)

Fixpoint solve_rec (e: typenv) (changed: bool) (q: list constraint) : res (typenv * bool) :=
  match q with
  | nil =>
      OK (e, changed)
  | (r1, r2) :: q' =>
      do (changed1, e1) <- type_move e r1 r2; solve_rec e1 (changed || changed1) q'
  end.

(** Measuring the state *)

Definition weight_bounds (ob: option bounds) : nat :=
  match ob with None => T.max_weight + 1 | Some(B lo hi s) => T.weight hi - T.weight lo end.

Lemma weight_bounds_1:
  forall lo hi s, weight_bounds (Some (B lo hi s)) < weight_bounds None.
Proof.
  intros; simpl. generalize (T.weight_range hi); omega.
Qed.

Lemma weight_bounds_2:
  forall lo1 hi1 s1 lo2 hi2 s2,
  T.sub lo2 lo1 -> T.sub hi1 hi2 -> lo1 <> lo2 \/ hi1 <> hi2 ->
  weight_bounds (Some (B lo1 hi1 s1)) < weight_bounds (Some (B lo2 hi2 s2)).
Proof.
  intros; simpl.
  generalize (T.weight_sub _ _ s1) (T.weight_sub _ _ s2) (T.weight_sub _ _ H) (T.weight_sub _ _ H0); intros.
  destruct H1.
  assert (T.weight lo2 < T.weight lo1) by (apply T.weight_sub_strict; auto). omega.
  assert (T.weight hi1 < T.weight hi2) by (apply T.weight_sub_strict; auto). omega.
Qed.

Hint Resolve T.sub_refl: ty.

Lemma weight_type_move:
  forall e r1 r2 changed e',
  type_move e r1 r2 = OK(changed, e') ->
  (e'.(te_sub) = e.(te_sub) \/ e'.(te_sub) = (r1, r2) :: e.(te_sub))
  /\ (forall r, weight_bounds e'.(te_typ)!r <= weight_bounds e.(te_typ)!r)
  /\ (changed = true ->
        weight_bounds e'.(te_typ)!r1 + weight_bounds e'.(te_typ)!r2
        < weight_bounds e.(te_typ)!r1 + weight_bounds e.(te_typ)!r2).
Proof.
  unfold type_move; intros.
  destruct (peq r1 r2).
  inv H. split; auto. split; intros. omega. discriminate.
  destruct (te_typ e)!r1 as [[lo1 hi1 s1]|] eqn:E1;
  destruct (te_typ e)!r2 as [[lo2 hi2 s2]|] eqn:E2.
- destruct (T.sub_dec hi1 lo2).
  inv H. split; auto. split; intros. omega. discriminate.
  destruct (T.sub_dec lo1 hi2); try discriminate.
  set (lo2' := T.lub lo1 lo2) in *.
  set (hi1' := T.glb hi1 hi2) in *.
  assert (S1': T.sub hi1' hi1) by (eapply T.glb_left; eauto).
  assert (S2': T.sub lo2 lo2') by (eapply T.lub_right; eauto).
  set (b1 := B lo1 hi1' (T.glb_max hi1 hi2 lo1 s1 s)) in *.
  set (b2 := B lo2' hi2 (T.lub_min lo1 lo2 hi2 s s2)) in *.
Local Opaque weight_bounds.
  destruct (T.eq lo2 lo2'); destruct (T.eq hi1 hi1'); inversion H; clear H; subst changed e'; simpl.
+ split; auto. split; intros. omega. discriminate.
+ assert (weight_bounds (Some b1) < weight_bounds (Some (B lo1 hi1 s1)))
  by (apply weight_bounds_2; auto with ty).
  split; auto. split; intros.
  rewrite PTree.gsspec. destruct (peq r r1). subst r. rewrite E1. omega. omega.
  rewrite PTree.gss. rewrite PTree.gso by auto. rewrite E2. omega.
+ assert (weight_bounds (Some b2) < weight_bounds (Some (B lo2 hi2 s2)))
  by (apply weight_bounds_2; auto with ty).
  split; auto. split; intros.
  rewrite PTree.gsspec. destruct (peq r r2). subst r. rewrite E2. omega. omega.
  rewrite PTree.gss. rewrite PTree.gso by auto. rewrite E1. omega.
+ assert (weight_bounds (Some b1) < weight_bounds (Some (B lo1 hi1 s1)))
  by (apply weight_bounds_2; auto with ty).
  assert (weight_bounds (Some b2) < weight_bounds (Some (B lo2 hi2 s2)))
  by (apply weight_bounds_2; auto with ty).
  split; auto. split; intros.
  rewrite ! PTree.gsspec.
  destruct (peq r r2). subst r. rewrite E2. omega.
  destruct (peq r r1). subst r. rewrite E1. omega.
  omega.
  rewrite PTree.gss. rewrite PTree.gso by auto. rewrite PTree.gss. omega.

- set (b2 := B lo1 (T.high_bound lo1) (T.high_bound_sub lo1)) in *.
  assert (weight_bounds (Some b2) < weight_bounds None) by (apply weight_bounds_1).
  inv H; simpl.
  split. destruct (T.sub_dec hi1 lo1); auto.
  split; intros.
  rewrite PTree.gsspec. destruct (peq r r2). subst r; rewrite E2; omega. omega.
  rewrite PTree.gss. rewrite PTree.gso by auto. rewrite E1. omega.

- set (b1 := B (T.low_bound hi2) hi2 (T.low_bound_sub hi2)) in *.
  assert (weight_bounds (Some b1) < weight_bounds None) by (apply weight_bounds_1).
  inv H; simpl.
  split. destruct (T.sub_dec hi2 lo2); auto.
  split; intros.
  rewrite PTree.gsspec. destruct (peq r r1). subst r; rewrite E1; omega. omega.
  rewrite PTree.gss. rewrite PTree.gso by auto. rewrite E2. omega.

- inv H. split; auto. simpl; split; intros. omega. congruence.
Qed.

Definition weight_constraints (b: PTree.t bounds) (cstr: list constraint) : nat :=
  List.fold_right (fun xy n => n + weight_bounds b!(fst xy) + weight_bounds b!(snd xy)) 0 cstr.

Remark weight_constraints_tighter:
  forall b1 b2, (forall r, weight_bounds b1!r <= weight_bounds b2!r) ->
  forall q, weight_constraints b1 q <= weight_constraints b2 q.
Proof.
  induction q; simpl. omega. generalize (H (fst a)) (H (snd a)); omega.
Qed.

Lemma weight_solve_rec:
  forall q e changed e' changed',
  solve_rec e changed q = OK(e', changed') ->
  (forall r, weight_bounds e'.(te_typ)!r <= weight_bounds e.(te_typ)!r) /\
  weight_constraints e'.(te_typ) e'.(te_sub) + (if changed' && negb changed then 1 else 0)
     <= weight_constraints e.(te_typ) e.(te_sub) + weight_constraints e.(te_typ) q.
Proof.
  induction q; simpl; intros.
- inv H. split. intros; omega. replace (changed' && negb changed') with false.
  omega. destruct changed'; auto.
- destruct a as [r1 r2]; monadInv H; simpl.
  rename x into changed1. rename x0 into e1.
  exploit weight_type_move; eauto. intros [A [B C]].
  exploit IHq; eauto. intros [D E].
  split. intros. eapply le_trans. eapply D. eapply B.
  assert (P: weight_constraints (te_typ e1) (te_sub e) <=
             weight_constraints (te_typ e) (te_sub e))
  by (apply weight_constraints_tighter; auto).
  assert (Q: weight_constraints (te_typ e1) (te_sub e1) <=
             weight_constraints (te_typ e1) (te_sub e) +
             weight_bounds (te_typ e1)!r1 + weight_bounds (te_typ e1)!r2).
  { destruct A as [Q|Q]; rewrite Q. omega. simpl. omega. }
  assert (R: weight_constraints (te_typ e1) q <= weight_constraints (te_typ e) q)
  by (apply weight_constraints_tighter; auto).
  set (ch1 := if changed' && negb (changed || changed1) then 1 else 0) in *.
  set (ch2 := if changed' && negb changed then 1 else 0) in *.
  destruct changed1.
  assert (ch2 <= ch1 + 1).
  { unfold ch2, ch1. rewrite orb_true_r. simpl. rewrite andb_false_r.
    destruct (changed' && negb changed); omega. }
  exploit C; eauto. omega.
  assert (ch2 <= ch1).
  { unfold ch2, ch1. rewrite orb_false_r. omega. }
  generalize (B r1) (B r2); omega.
Qed.

Definition weight_typenv (e: typenv) : nat :=
  weight_constraints e.(te_typ) e.(te_sub).

(** Iterative solving of the remaining constraints *)

Function solve_constraints (e: typenv) {measure weight_typenv e}: res typenv :=
  match solve_rec {| te_typ := e.(te_typ); te_sub := nil |} false e.(te_sub) with
  | OK(e', false) => OK e                   (**r no more changes, fixpoint reached *)
  | OK(e', true)  => solve_constraints e'   (**r one more iteration *)
  | Error msg => Error msg
  end.
Proof.
  intros. exploit weight_solve_rec; eauto. simpl. intros [A B].
  unfold weight_typenv. omega.
Qed.

Definition typassign := positive -> T.t.

Definition makeassign (e: typenv) : typassign :=
  fun x => match e.(te_typ)!x with Some(B lo hi s) => lo | None => T.default end.

Definition solve (e: typenv) : res typassign :=
  do e' <- solve_constraints e; OK(makeassign e').

(** What it means to be a solution *)

Definition satisf (te: typassign) (e: typenv) : Prop :=
   (forall x lo hi s, e.(te_typ)!x = Some(B lo hi s) -> T.sub lo (te x) /\ T.sub (te x) hi)
/\ (forall x y, In (x, y) e.(te_sub) -> T.sub (te x) (te y)).

Lemma satisf_initial: forall te, satisf te initial.
Proof.
  unfold initial; intros; split; simpl; intros.
  rewrite PTree.gempty in H; discriminate.
  contradiction.
Qed.

(** Soundness proof *)

Lemma type_def_incr:
  forall te x ty e e', type_def e x ty = OK e' -> satisf te e' -> satisf te e.
Proof.
  unfold type_def; intros. destruct (te_typ e)!x as [[lo hi s1]|] eqn:E.
- destruct (T.sub_dec ty hi); try discriminate.
  destruct (T.eq lo (T.lub lo ty)); monadInv H.
  subst e'; auto.
  destruct H0 as [P Q]; split; auto; intros.
  destruct (peq x x0).
  + subst x0. rewrite E in H; inv H.
    exploit (P x); simpl. rewrite PTree.gss; eauto. intuition.
    apply T.sub_trans with (T.lub lo0 ty); auto. eapply T.lub_left; eauto.
  + eapply P; simpl. rewrite PTree.gso; eauto.
- inv H. destruct H0 as [P Q]; split; auto; intros.
  eapply P; simpl. rewrite PTree.gso; eauto. congruence.
Qed.

Hint Resolve type_def_incr: ty.

Lemma type_def_sound:
  forall te x ty e e', type_def e x ty = OK e' -> satisf te e' -> T.sub ty (te x).
Proof.
  unfold type_def; intros. destruct H0 as [P Q].
  destruct (te_typ e)!x as [[lo hi s1]|] eqn:E.
- destruct (T.sub_dec ty hi); try discriminate.
  destruct (T.eq lo (T.lub lo ty)); monadInv H.
  + subst e'. apply T.sub_trans with lo.
    rewrite e0. eapply T.lub_right; eauto. eapply P; eauto.
  + apply T.sub_trans with (T.lub lo ty).
    eapply T.lub_right; eauto.
    eapply (P x). simpl. rewrite PTree.gss; eauto.
- inv H. eapply (P x); simpl. rewrite PTree.gss; eauto.
Qed.

Lemma type_defs_incr:
  forall te xl tyl e e', type_defs e xl tyl = OK e' -> satisf te e' -> satisf te e.
Proof.
  induction xl; destruct tyl; simpl; intros; monadInv H; eauto with ty.
Qed.

Hint Resolve type_defs_incr: ty.

Lemma type_defs_sound:
  forall te xl tyl e e', type_defs e xl tyl = OK e' -> satisf te e' -> list_forall2 T.sub tyl (map te xl).
Proof.
  induction xl; destruct tyl; simpl; intros; monadInv H.
  constructor.
  constructor; eauto. eapply type_def_sound; eauto with ty.
Qed.

Lemma type_use_incr:
  forall te x ty e e', type_use e x ty = OK e' -> satisf te e' -> satisf te e.
Proof.
  unfold type_use; intros. destruct (te_typ e)!x as [[lo hi s1]|] eqn:E.
- destruct (T.sub_dec lo ty); try discriminate.
  destruct (T.eq hi (T.glb hi ty)); monadInv H.
  subst e'; auto.
  destruct H0 as [P Q]; split; auto; intros.
  destruct (peq x x0).
  + subst x0. rewrite E in H; inv H.
    exploit (P x); simpl. rewrite PTree.gss; eauto. intuition.
    apply T.sub_trans with (T.glb hi0 ty); auto. eapply T.glb_left; eauto.
  + eapply P; simpl. rewrite PTree.gso; eauto.
- inv H. destruct H0 as [P Q]; split; auto; intros.
  eapply P; simpl. rewrite PTree.gso; eauto. congruence.
Qed.

Hint Resolve type_use_incr: ty.

Lemma type_use_sound:
  forall te x ty e e', type_use e x ty = OK e' -> satisf te e' -> T.sub (te x) ty.
Proof.
  unfold type_use; intros. destruct H0 as [P Q].
  destruct (te_typ e)!x as [[lo hi s1]|] eqn:E.
- destruct (T.sub_dec lo ty); try discriminate.
  destruct (T.eq hi (T.glb hi ty)); monadInv H.
  + subst e'. apply T.sub_trans with hi.
    eapply P; eauto. rewrite e0. eapply T.glb_right; eauto.
  + apply T.sub_trans with (T.glb hi ty).
    eapply (P x). simpl. rewrite PTree.gss; eauto.
    eapply T.glb_right; eauto.
- inv H. eapply (P x); simpl. rewrite PTree.gss; eauto.
Qed.

Lemma type_uses_incr:
  forall te xl tyl e e', type_uses e xl tyl = OK e' -> satisf te e' -> satisf te e.
Proof.
  induction xl; destruct tyl; simpl; intros; monadInv H; eauto with ty.
Qed.

Hint Resolve type_uses_incr: ty.

Lemma type_uses_sound:
  forall te xl tyl e e', type_uses e xl tyl = OK e' -> satisf te e' -> list_forall2 T.sub (map te xl) tyl.
Proof.
  induction xl; destruct tyl; simpl; intros; monadInv H.
  constructor.
  constructor; eauto. eapply type_use_sound; eauto with ty.
Qed.

Lemma type_move_incr:
  forall te e r1 r2 e' changed,
  type_move e r1 r2 = OK(changed, e') -> satisf te e' -> satisf te e.
Proof.
  unfold type_move; intros. destruct H0 as [P Q].
  destruct (peq r1 r2). inv H; split; auto.
  destruct (te_typ e)!r1 as [[lo1 hi1 s1]|] eqn:E1;
  destruct (te_typ e)!r2 as [[lo2 hi2 s2]|] eqn:E2.
- destruct (T.sub_dec hi1 lo2). inv H; split; auto.
  destruct (T.sub_dec lo1 hi2); try discriminate.
  set (lo := T.lub lo1 lo2) in *. set (hi := T.glb hi1 hi2) in *.
  destruct (T.eq lo2 lo); destruct (T.eq hi1 hi); monadInv H; simpl in *.
  + subst e'; simpl in *. split; auto.
  + subst e'; simpl in *. split; auto. intros. destruct (peq x r1).
    subst x.
    rewrite E1 in H. injection H; intros; subst lo0 hi0.
    exploit (P r1). rewrite PTree.gss; eauto. intuition.
    apply T.sub_trans with (T.glb hi1 hi2); auto. eapply T.glb_left; eauto.
    eapply P. rewrite PTree.gso; eauto.
  + subst e'; simpl in *. split; auto. intros. destruct (peq x r2).
    subst x.
    rewrite E2 in H. injection H; intros; subst lo0 hi0.
    exploit (P r2). rewrite PTree.gss; eauto. intuition.
    apply T.sub_trans with (T.lub lo1 lo2); auto. eapply T.lub_right; eauto.
    eapply P. rewrite PTree.gso; eauto.
  + split; auto. intros.
    destruct (peq x r1). subst x.
    rewrite E1 in H. injection H; intros; subst lo0 hi0.
    exploit (P r1). rewrite PTree.gso; eauto. rewrite PTree.gss; eauto. intuition.
    apply T.sub_trans with (T.glb hi1 hi2); auto. eapply T.glb_left; eauto.
    destruct (peq x r2). subst x.
    rewrite E2 in H. injection H; intros; subst lo0 hi0.
    exploit (P r2). rewrite PTree.gss; eauto. intuition.
    apply T.sub_trans with (T.lub lo1 lo2); auto. eapply T.lub_right; eauto.
    eapply P. rewrite ! PTree.gso; eauto.
- inv H; simpl in *. split; intros.
  eapply P. rewrite PTree.gso; eauto. congruence.
  apply Q.   destruct (T.sub_dec hi1 lo1); auto with coqlib.
- inv H; simpl in *. split; intros.
  eapply P. rewrite PTree.gso; eauto. congruence.
  apply Q.   destruct (T.sub_dec hi2 lo2); auto with coqlib.
- inv H; simpl in *. split; auto.
Qed.

Hint Resolve type_move_incr: ty.

Lemma type_move_sound:
  forall te e r1 r2 e' changed,
  type_move e r1 r2 = OK(changed, e') -> satisf te e' -> T.sub (te r1) (te r2).
Proof.
  unfold type_move; intros. destruct H0 as [P Q].
  destruct (peq r1 r2). subst r2. apply T.sub_refl.
  destruct (te_typ e)!r1 as [[lo1 hi1 s1]|] eqn:E1;
  destruct (te_typ e)!r2 as [[lo2 hi2 s2]|] eqn:E2.
- destruct (T.sub_dec hi1 lo2).
  inv H. apply T.sub_trans with hi1. eapply P; eauto. apply T.sub_trans with lo2; auto. eapply P; eauto.
  destruct (T.sub_dec lo1 hi2); try discriminate.
  set (lo := T.lub lo1 lo2) in *. set (hi := T.glb hi1 hi2) in *.
  destruct (T.eq lo2 lo); destruct (T.eq hi1 hi); monadInv H; simpl in *.
  + subst e'; simpl in *. apply Q; auto.
  + subst e'; simpl in *. apply Q; auto.
  + subst e'; simpl in *. apply Q; auto.
  + apply Q; auto.
- inv H; simpl in *. destruct (T.sub_dec hi1 lo1).
  + apply T.sub_trans with hi1. eapply P; eauto. rewrite PTree.gso; eauto.
    apply T.sub_trans with lo1; auto. eapply P. rewrite PTree.gss; eauto.
  + auto with coqlib.
- inv H; simpl in *. destruct (T.sub_dec hi2 lo2).
  + apply T.sub_trans with hi2. eapply P. rewrite PTree.gss; eauto.
    apply T.sub_trans with lo2; auto. eapply P. rewrite PTree.gso; eauto.
  + auto with coqlib.
- inv H. simpl in Q; auto.
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
  T.sub (te r1) (te r2).
Proof.
  induction q; simpl; intros.
- contradiction.
- destruct a as [r3 r4]; monadInv H. destruct H0.
  + inv H. eapply type_move_sound; eauto. eapply solve_rec_incr; eauto.
  + eapply IHq; eauto with ty.
Qed.

Lemma type_move_false:
  forall e r1 r2 e',
  type_move e r1 r2 = OK(false, e') ->
  te_typ e' = te_typ e /\ T.sub (makeassign e r1) (makeassign e r2).
Proof.
  unfold type_move; intros.
  destruct (peq r1 r2). inv H. split; auto. apply T.sub_refl.
  unfold makeassign;
  destruct (te_typ e)!r1 as [[lo1 hi1 s1]|] eqn:E1;
  destruct (te_typ e)!r2 as [[lo2 hi2 s2]|] eqn:E2.
- destruct (T.sub_dec hi1 lo2).
  inv H. split; auto. eapply T.sub_trans; eauto.
  destruct (T.sub_dec lo1 hi2); try discriminate.
  set (lo := T.lub lo1 lo2) in *. set (hi := T.glb hi1 hi2) in *.
  destruct (T.eq lo2 lo); destruct (T.eq hi1 hi); try discriminate.
  monadInv H. split; auto. rewrite e0. unfold lo. eapply T.lub_left; eauto.
- discriminate.
- discriminate.
- inv H. split; auto. apply T.sub_refl.
Qed.

Lemma solve_rec_false:
  forall r1 r2 q e changed e',
  solve_rec e changed q = OK(e', false) ->
  changed = false /\
  (In (r1, r2) q -> T.sub (makeassign e r1) (makeassign e r2)).
Proof.
  induction q; simpl; intros.
- inv H. tauto.
- destruct a as [r3 r4]; monadInv H.
  exploit IHq; eauto. intros [P Q].
  destruct changed; try discriminate. destruct x; try discriminate.
  exploit type_move_false; eauto. intros [U V].
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

Lemma type_def_complete:
  forall te e x ty,
  satisf te e -> T.sub ty (te x) -> exists e', type_def e x ty = OK e' /\ satisf te e'.
Proof.
  unfold type_def; intros. destruct H as [P Q].
  destruct (te_typ e)!x as [[lo hi s1]|] eqn:E.
- destruct (T.sub_dec ty hi).
  destruct (T.eq lo (T.lub lo ty)).
  exists e; split; auto. split; auto.
  econstructor; split; eauto. split; simpl; auto; intros.
  rewrite PTree.gsspec in H. destruct (peq x0 x).
  inv H. exploit P; eauto. intuition. eapply T.lub_min; eauto.
  eapply P; eauto.
  elim n. apply T.sub_trans with (te x); auto. eapply P; eauto.
- econstructor; split; eauto. split; simpl; auto; intros.
  rewrite PTree.gsspec in H. destruct (peq x0 x).
  inv H. split; auto. apply T.high_bound_majorant; auto.
  eapply P; eauto.
Qed.

Lemma type_defs_complete:
  forall te xl tyl e,
  satisf te e -> list_forall2 T.sub tyl (map te xl) ->
  exists e', type_defs e xl tyl = OK e' /\ satisf te e'.
Proof.
  induction xl; intros; inv H0; simpl.
  econstructor; eauto.
  exploit (type_def_complete te e a a1); auto. intros (e1 & P & Q).
  exploit (IHxl al e1); auto. intros (e2 & U & V).
  exists e2; split; auto. rewrite P; auto.
Qed.

Lemma type_use_complete:
  forall te e x ty,
  satisf te e -> T.sub (te x) ty -> exists e', type_use e x ty = OK e' /\ satisf te e'.
Proof.
  unfold type_use; intros. destruct H as [P Q].
  destruct (te_typ e)!x as [[lo hi s1]|] eqn:E.
- destruct (T.sub_dec lo ty).
  destruct (T.eq hi (T.glb hi ty)).
  exists e; split; auto. split; auto.
  econstructor; split; eauto. split; simpl; auto; intros.
  rewrite PTree.gsspec in H. destruct (peq x0 x).
  inv H. exploit P; eauto. intuition. eapply T.glb_max; eauto.
  eapply P; eauto.
  elim n. apply T.sub_trans with (te x); auto. eapply P; eauto.
- econstructor; split; eauto. split; simpl; auto; intros.
  rewrite PTree.gsspec in H. destruct (peq x0 x).
  inv H. split; auto. apply T.low_bound_minorant; auto.
  eapply P; eauto.
Qed.

Lemma type_uses_complete:
  forall te xl tyl e,
  satisf te e -> list_forall2 T.sub (map te xl) tyl ->
  exists e', type_uses e xl tyl = OK e' /\ satisf te e'.
Proof.
  induction xl; intros; inv H0; simpl.
  econstructor; eauto.
  exploit (type_use_complete te e a b1); auto. intros (e1 & P & Q).
  exploit (IHxl bl e1); auto. intros (e2 & U & V).
  exists e2; split; auto. rewrite P; auto.
Qed.

Lemma type_move_complete:
  forall te e r1 r2,
  satisf te e -> T.sub (te r1) (te r2) ->
  exists changed e', type_move e r1 r2 = OK(changed, e') /\ satisf te e'.
Proof.
  unfold type_move; intros. elim H; intros P Q.
  assert (Q': forall x y, In (x, y) ((r1, r2) :: te_sub e) -> T.sub (te x) (te y)).
  { intros. destruct H1; auto. congruence. }
  destruct (peq r1 r2). econstructor; econstructor; eauto.
  destruct (te_typ e)!r1 as [[lo1 hi1 s1]|] eqn:E1;
  destruct (te_typ e)!r2 as [[lo2 hi2 s2]|] eqn:E2.
- exploit (P r1); eauto. intros [L1 U1].
  exploit (P r2); eauto. intros [L2 U2].
  destruct (T.sub_dec hi1 lo2). econstructor; econstructor; eauto.
  destruct (T.sub_dec lo1 hi2).
  destruct (T.eq lo2 (T.lub lo1 lo2)); destruct (T.eq hi1 (T.glb hi1 hi2));
  econstructor; econstructor; split; eauto; split; auto; simpl; intros.
  + rewrite PTree.gsspec in H1. destruct (peq x r1).
    clear e0. inv H1. split; auto.
    apply T.glb_max. auto. apply T.sub_trans with (te r2); auto.
    eapply P; eauto.
  + rewrite PTree.gsspec in H1. destruct (peq x r2).
    clear e0. inv H1. split; auto.
    apply T.lub_min. apply T.sub_trans with (te r1); auto. auto.
    eapply P; eauto.
  + rewrite ! PTree.gsspec in H1. destruct (peq x r2).
    inv H1. split; auto. apply T.lub_min; auto. apply T.sub_trans with (te r1); auto.
    destruct (peq x r1).
    inv H1. split; auto. apply T.glb_max; auto. apply T.sub_trans with (te r2); auto.
    eapply P; eauto.
  + elim n1. apply T.sub_trans with (te r1); auto.
    apply T.sub_trans with (te r2); auto.
- econstructor; econstructor; split; eauto; split.
  + simpl; intros. rewrite PTree.gsspec in H1. destruct (peq x r2).
    inv H1. exploit P; eauto. intuition.
    apply T.sub_trans with (te r1); auto.
    apply T.high_bound_majorant. apply T.sub_trans with (te r1); auto.
    eapply P; eauto.
  + destruct (T.sub_dec hi1 lo1); auto.
- econstructor; econstructor; split; eauto; split.
  + simpl; intros. rewrite PTree.gsspec in H1. destruct (peq x r1).
    inv H1. exploit P; eauto. intuition.
    apply T.low_bound_minorant. apply T.sub_trans with (te r2); auto.
    apply T.sub_trans with (te r2); auto.
    eapply P; eauto.
  + destruct (T.sub_dec hi2 lo2); auto.
- econstructor; econstructor; split; eauto; split; auto.
Qed.

Lemma solve_rec_complete:
  forall te q e changed,
  satisf te e ->
  (forall r1 r2, In (r1, r2) q -> T.sub (te r1) (te r2)) ->
  exists e' changed', solve_rec e changed q = OK(e', changed') /\ satisf te e'.
Proof.
  induction q; simpl; intros.
- econstructor; econstructor; eauto.
- destruct a as [r1 r2].
  exploit (type_move_complete te e r1 r2); auto. intros (changed1 & e1 & A & B).
  exploit (IHq e1 (changed || changed1)); auto. intros (e' & changed' & C & D).
  exists e'; exists changed'. rewrite A; simpl; rewrite C; auto.
Qed.

Lemma solve_constraints_complete:
  forall te e, satisf te e -> exists e', solve_constraints e = OK e' /\ satisf te e'.
Proof.
  intros te e. functional induction (solve_constraints e); intros.
- exists e; auto.
- exploit (solve_rec_complete te (te_sub e) {| te_typ := te_typ e; te_sub := nil |} false).
  destruct H; split; auto. simpl; tauto.
  destruct H; auto.
  intros (e1 & changed1 & P & Q).
  apply IHr. congruence.
- exploit (solve_rec_complete te (te_sub e) {| te_typ := te_typ e; te_sub := nil |} false).
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

End SubSolver.

