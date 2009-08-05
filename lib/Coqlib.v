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

(** This file collects a number of definitions and theorems that are
    used throughout the development.  It complements the Coq standard
    library. *)

Require Export ZArith.
Require Export Znumtheory.
Require Export List.
Require Export Bool.
Require Import Wf_nat.

(** * Logical axioms *)

(** We use two logical axioms that are not provable in Coq but consistent
  with the logic: function extensionality and proof irrelevance.
  These are used in the memory model to show that two memory states
  that have identical contents are equal. *)

Axiom extensionality:
  forall (A B: Type) (f g : A -> B),
  (forall x, f x = g x) -> f = g.

Axiom proof_irrelevance:
  forall (P: Prop) (p1 p2: P), p1 = p2.

(** * Useful tactics *)

Ltac inv H := inversion H; clear H; subst.

Ltac predSpec pred predspec x y :=
  generalize (predspec x y); case (pred x y); intro.

Ltac caseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

Ltac destructEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; destruct name; intro.

Ltac decEq :=
  match goal with
  | [ |- _ = _ ] => f_equal
  | [ |- (?X ?A <> ?X ?B) ] =>
      cut (A <> B); [intro; congruence | try discriminate]
  end.

Ltac byContradiction :=
  cut False; [contradiction|idtac].

Ltac omegaContradiction :=
  cut False; [contradiction|omega].

Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. auto. Qed.

Ltac exploit x :=
    refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _) _)
 || refine (modusponens _ _ (x _ _) _)
 || refine (modusponens _ _ (x _) _).

(** * Definitions and theorems over the type [positive] *)

Definition peq (x y: positive): {x = y} + {x <> y}.
Proof.
  intros. caseEq (Pcompare x y Eq).
  intro. left. apply Pcompare_Eq_eq; auto.
  intro. right. red. intro. subst y. rewrite (Pcompare_refl x) in H. discriminate.
  intro. right. red. intro. subst y. rewrite (Pcompare_refl x) in H. discriminate.
Qed.

Lemma peq_true:
  forall (A: Type) (x: positive) (a b: A), (if peq x x then a else b) = a.
Proof.
  intros. case (peq x x); intros.
  auto.
  elim n; auto.
Qed.

Lemma peq_false:
  forall (A: Type) (x y: positive) (a b: A), x <> y -> (if peq x y then a else b) = b.
Proof.
  intros. case (peq x y); intros.
  elim H; auto.
  auto.
Qed.  

Definition Plt (x y: positive): Prop := Zlt (Zpos x) (Zpos y).

Lemma Plt_ne:
  forall (x y: positive), Plt x y -> x <> y.
Proof.
  unfold Plt; intros. red; intro. subst y. omega.
Qed.
Hint Resolve Plt_ne: coqlib.

Lemma Plt_trans:
  forall (x y z: positive), Plt x y -> Plt y z -> Plt x z.
Proof.
  unfold Plt; intros; omega.
Qed.

Remark Psucc_Zsucc:
  forall (x: positive), Zpos (Psucc x) = Zsucc (Zpos x).
Proof.
  intros. rewrite Pplus_one_succ_r. 
  reflexivity.
Qed.

Lemma Plt_succ:
  forall (x: positive), Plt x (Psucc x).
Proof.
  intro. unfold Plt. rewrite Psucc_Zsucc. omega.
Qed.
Hint Resolve Plt_succ: coqlib.

Lemma Plt_trans_succ:
  forall (x y: positive), Plt x y -> Plt x (Psucc y).
Proof.
  intros. apply Plt_trans with y. assumption. apply Plt_succ.
Qed.
Hint Resolve Plt_succ: coqlib.

Lemma Plt_succ_inv:
  forall (x y: positive), Plt x (Psucc y) -> Plt x y \/ x = y.
Proof.
  intros x y. unfold Plt. rewrite Psucc_Zsucc. 
  intro. assert (A: (Zpos x < Zpos y)%Z \/ Zpos x = Zpos y). omega.
  elim A; intro. left; auto. right; injection H0; auto.
Qed.

Definition plt (x y: positive) : {Plt x y} + {~ Plt x y}.
Proof.
 intros. unfold Plt. apply Z_lt_dec.
Qed.

Definition Ple (p q: positive) := Zle (Zpos p) (Zpos q).

Lemma Ple_refl: forall (p: positive), Ple p p.
Proof.
  unfold Ple; intros; omega.
Qed.

Lemma Ple_trans: forall (p q r: positive), Ple p q -> Ple q r -> Ple p r.
Proof.
  unfold Ple; intros; omega.
Qed.

Lemma Plt_Ple: forall (p q: positive), Plt p q -> Ple p q.
Proof.
  unfold Plt, Ple; intros; omega.
Qed.

Lemma Ple_succ: forall (p: positive), Ple p (Psucc p).
Proof.
  intros. apply Plt_Ple. apply Plt_succ.
Qed.

Lemma Plt_Ple_trans:
  forall (p q r: positive), Plt p q -> Ple q r -> Plt p r.
Proof.
  unfold Plt, Ple; intros; omega.
Qed.

Lemma Plt_strict: forall p, ~ Plt p p.
Proof.
  unfold Plt; intros. omega.
Qed.

Hint Resolve Ple_refl Plt_Ple Ple_succ Plt_strict: coqlib.

(** Peano recursion over positive numbers. *)

Section POSITIVE_ITERATION.

Lemma Plt_wf: well_founded Plt.
Proof.
  apply well_founded_lt_compat with nat_of_P.
  intros. apply nat_of_P_lt_Lt_compare_morphism. exact H.
Qed.

Variable A: Type.
Variable v1: A.
Variable f: positive -> A -> A.

Lemma Ppred_Plt:
  forall x, x <> xH -> Plt (Ppred x) x.
Proof.
  intros. elim (Psucc_pred x); intro. contradiction.
  set (y := Ppred x) in *. rewrite <- H0. apply Plt_succ.
Qed.

Let iter (x: positive) (P: forall y, Plt y x -> A) : A :=
  match peq x xH with
  | left EQ => v1
  | right NOTEQ => f (Ppred x) (P (Ppred x) (Ppred_Plt x NOTEQ))
  end.

Definition positive_rec : positive -> A :=
  Fix Plt_wf (fun _ => A) iter.

Lemma unroll_positive_rec:
  forall x,
  positive_rec x = iter x (fun y _ => positive_rec y).
Proof.
  unfold positive_rec. apply (Fix_eq Plt_wf (fun _ => A) iter).
  intros. unfold iter. case (peq x 1); intro. auto. decEq. apply H.
Qed.

Lemma positive_rec_base:
  positive_rec 1%positive = v1.
Proof.
  rewrite unroll_positive_rec. unfold iter. case (peq 1 1); intro.
  auto. elim n; auto.
Qed.

Lemma positive_rec_succ:
  forall x, positive_rec (Psucc x) = f x (positive_rec x).
Proof.
  intro. rewrite unroll_positive_rec. unfold iter.
  case (peq (Psucc x) 1); intro.
  destruct x; simpl in e; discriminate.
  rewrite Ppred_succ. auto.
Qed.

Lemma positive_Peano_ind:
  forall (P: positive -> Prop),
  P xH ->
  (forall x, P x -> P (Psucc x)) ->
  forall x, P x.
Proof.
  intros.
  apply (well_founded_ind Plt_wf P).
  intros. 
  case (peq x0 xH); intro.
  subst x0; auto.
  elim (Psucc_pred x0); intro. contradiction. rewrite <- H2.
  apply H0. apply H1. apply Ppred_Plt. auto. 
Qed.

End POSITIVE_ITERATION.

(** * Definitions and theorems over the type [Z] *)

Definition zeq: forall (x y: Z), {x = y} + {x <> y} := Z_eq_dec.

Lemma zeq_true:
  forall (A: Type) (x: Z) (a b: A), (if zeq x x then a else b) = a.
Proof.
  intros. case (zeq x x); intros.
  auto.
  elim n; auto.
Qed.

Lemma zeq_false:
  forall (A: Type) (x y: Z) (a b: A), x <> y -> (if zeq x y then a else b) = b.
Proof.
  intros. case (zeq x y); intros.
  elim H; auto.
  auto.
Qed.  

Open Scope Z_scope.

Definition zlt: forall (x y: Z), {x < y} + {x >= y} := Z_lt_ge_dec.

Lemma zlt_true:
  forall (A: Type) (x y: Z) (a b: A), 
  x < y -> (if zlt x y then a else b) = a.
Proof.
  intros. case (zlt x y); intros.
  auto.
  omegaContradiction.
Qed.

Lemma zlt_false:
  forall (A: Type) (x y: Z) (a b: A), 
  x >= y -> (if zlt x y then a else b) = b.
Proof.
  intros. case (zlt x y); intros.
  omegaContradiction.
  auto.
Qed.

Definition zle: forall (x y: Z), {x <= y} + {x > y} := Z_le_gt_dec.

Lemma zle_true:
  forall (A: Type) (x y: Z) (a b: A), 
  x <= y -> (if zle x y then a else b) = a.
Proof.
  intros. case (zle x y); intros.
  auto.
  omegaContradiction.
Qed.

Lemma zle_false:
  forall (A: Type) (x y: Z) (a b: A), 
  x > y -> (if zle x y then a else b) = b.
Proof.
  intros. case (zle x y); intros.
  omegaContradiction.
  auto.
Qed.

(** Properties of powers of two. *)

Lemma two_power_nat_O : two_power_nat O = 1.
Proof. reflexivity. Qed.

Lemma two_power_nat_pos : forall n : nat, two_power_nat n > 0.
Proof.
  induction n. rewrite two_power_nat_O. omega.
  rewrite two_power_nat_S. omega.
Qed.

Lemma two_p_monotone:
  forall x y, 0 <= x <= y -> two_p x <= two_p y.
Proof.
  intros.
  replace (two_p x) with (two_p x * 1) by omega. 
  replace y with (x + (y - x)) by omega.
  rewrite two_p_is_exp; try omega.
  apply Zmult_le_compat_l.
  assert (two_p (y - x) > 0). apply two_p_gt_ZERO. omega. omega.
  assert (two_p x > 0). apply two_p_gt_ZERO. omega. omega.
Qed.

Lemma two_power_nat_two_p:
  forall x, two_power_nat x = two_p (Z_of_nat x).
Proof.
  induction x. auto. 
  rewrite two_power_nat_S. rewrite inj_S. rewrite two_p_S. omega. omega.
Qed.

(** Properties of [Zmin] and [Zmax] *)

Lemma Zmin_spec:
  forall x y, Zmin x y = if zlt x y then x else y.
Proof.
  intros. case (zlt x y); unfold Zlt, Zge; intros.
  unfold Zmin. rewrite z. auto.
  unfold Zmin. caseEq (x ?= y); intro. 
  apply Zcompare_Eq_eq. auto.
  contradiction.
  reflexivity.
Qed.

Lemma Zmax_spec:
  forall x y, Zmax x y = if zlt y x then x else y.
Proof.
  intros. case (zlt y x); unfold Zlt, Zge; intros.
  unfold Zmax. rewrite <- (Zcompare_antisym y x).
  rewrite z. simpl. auto.
  unfold Zmax. rewrite <- (Zcompare_antisym y x).
  caseEq (y ?= x); intro; simpl.
  symmetry. apply Zcompare_Eq_eq. auto.
  contradiction. reflexivity.
Qed.

Lemma Zmax_bound_l:
  forall x y z, x <= y -> x <= Zmax y z.
Proof.
  intros. generalize (Zmax1 y z). omega.
Qed.
Lemma Zmax_bound_r:
  forall x y z, x <= z -> x <= Zmax y z.
Proof.
  intros. generalize (Zmax2 y z). omega.
Qed.

(** Properties of Euclidean division and modulus. *)

Lemma Zdiv_small:
  forall x y, 0 <= x < y -> x / y = 0.
Proof.
  intros. assert (y > 0). omega. 
  assert (forall a b,
    0 <= a < y ->
    0 <= y * b + a < y ->
    b = 0).
  intros. 
  assert (b = 0 \/ b > 0 \/ (-b) > 0). omega.
  elim H3; intro.
  auto.
  elim H4; intro.
  assert (y * b >= y * 1). apply Zmult_ge_compat_l. omega. omega. 
  omegaContradiction. 
  assert (y * (-b) >= y * 1). apply Zmult_ge_compat_l. omega. omega.
  rewrite <- Zopp_mult_distr_r in H6. omegaContradiction.
  apply H1 with (x mod y). 
  apply Z_mod_lt. auto.
  rewrite <- Z_div_mod_eq. auto. auto.
Qed.

Lemma Zmod_small:
  forall x y, 0 <= x < y -> x mod y = x.
Proof.
  intros. assert (y > 0). omega.
  generalize (Z_div_mod_eq x y H0). 
  rewrite (Zdiv_small x y H). omega.
Qed.

Lemma Zmod_unique:
  forall x y a b,
  x = a * y + b -> 0 <= b < y -> x mod y = b.
Proof.
  intros. subst x. rewrite Zplus_comm. 
  rewrite Z_mod_plus. apply Zmod_small. auto. omega.
Qed.

Lemma Zdiv_unique:
  forall x y a b,
  x = a * y + b -> 0 <= b < y -> x / y = a.
Proof.
  intros. subst x. rewrite Zplus_comm.
  rewrite Z_div_plus. rewrite (Zdiv_small b y H0). omega. omega.
Qed.

Lemma Zdiv_Zdiv:
  forall a b c,
  b > 0 -> c > 0 -> (a / b) / c = a / (b * c).
Proof.
  intros.
  generalize (Z_div_mod_eq a b H). generalize (Z_mod_lt a b H). intros.
  generalize (Z_div_mod_eq (a/b) c H0). generalize (Z_mod_lt (a/b) c H0). intros.
  set (q1 := a / b) in *. set (r1 := a mod b) in *.
  set (q2 := q1 / c) in *. set (r2 := q1 mod c) in *.
  symmetry. apply Zdiv_unique with (r2 * b + r1). 
  rewrite H2. rewrite H4. ring.
  split. 
  assert (0 <= r2 * b). apply Zmult_le_0_compat. omega. omega. omega.
  assert ((r2 + 1) * b <= c * b).
  apply Zmult_le_compat_r. omega. omega. 
  replace ((r2 + 1) * b) with (r2 * b + b) in H5 by ring.
  replace (c * b) with (b * c) in H5 by ring.
  omega.
Qed.

Lemma Zmult_le_compat_l_neg :
  forall n m p:Z, n >= m -> p <= 0 -> p * n <= p * m.
Proof.
  intros.
  assert ((-p) * n >= (-p) * m). apply Zmult_ge_compat_l. auto. omega.
  replace (p * n) with (- ((-p) * n)) by ring.
  replace (p * m) with (- ((-p) * m)) by ring.
  omega.
Qed.

Lemma Zdiv_interval_1:
  forall lo hi a b,
  lo <= 0 -> hi > 0 -> b > 0 ->
  lo * b <= a < hi * b ->
  lo <= a/b < hi.
Proof.
  intros. 
  generalize (Z_div_mod_eq a b H1). generalize (Z_mod_lt a b H1). intros.
  set (q := a/b) in *. set (r := a mod b) in *.
  split.
  assert (lo < (q + 1)).
  apply Zmult_lt_reg_r with b. omega.  
  apply Zle_lt_trans with a. omega. 
  replace ((q + 1) * b) with (b * q + b) by ring.
  omega.
  omega.
  apply Zmult_lt_reg_r with b. omega. 
  replace (q * b) with (b * q) by ring.
  omega.
Qed.

Lemma Zdiv_interval_2:
  forall lo hi a b,
  lo <= a <= hi -> lo <= 0 -> hi > 0 -> b > 0 ->
  lo <= a/b <= hi.
Proof.
  intros.
  assert (lo <= a / b < hi+1).
  apply Zdiv_interval_1. omega. omega. auto.
  assert (lo * b <= lo * 1). apply Zmult_le_compat_l_neg. omega. omega. 
  replace (lo * 1) with lo in H3 by ring.
  assert ((hi + 1) * 1 <= (hi + 1) * b). apply Zmult_le_compat_l. omega. omega.
  replace ((hi + 1) * 1) with (hi + 1) in H4 by ring.
  omega.
  omega.
Qed.

(** Properties of divisibility. *)

Lemma Zdivides_trans:
  forall x y z, (x | y) -> (y | z) -> (x | z).
Proof.
  intros. inv H. inv H0. exists (q0 * q). ring.
Qed.

Definition Zdivide_dec:
  forall (p q: Z), p > 0 -> { (p|q) } + { ~(p|q) }.
Proof.
  intros. destruct (zeq (Zmod q p) 0).
  left. exists (q / p). 
  transitivity (p * (q / p) + (q mod p)). apply Z_div_mod_eq; auto.
  transitivity (p * (q / p)). omega. ring.
  right; red; intros. elim n. apply Z_div_exact_1; auto. 
  inv H0. rewrite Z_div_mult; auto. ring.
Qed.

(** Alignment: [align n amount] returns the smallest multiple of [amount]
  greater than or equal to [n]. *)

Definition align (n: Z) (amount: Z) :=
  ((n + amount - 1) / amount) * amount.

Lemma align_le: forall x y, y > 0 -> x <= align x y.
Proof.
  intros. unfold align. 
  generalize (Z_div_mod_eq (x + y - 1) y H). intro.
  replace ((x + y - 1) / y * y) 
     with ((x + y - 1) - (x + y - 1) mod y).
  generalize (Z_mod_lt (x + y - 1) y H). omega.
  rewrite Zmult_comm. omega.
Qed.

Lemma align_divides: forall x y, y > 0 -> (y | align x y).
Proof.
  intros. unfold align. apply Zdivide_factor_l. 
Qed.

(** * Definitions and theorems on the data types [option], [sum] and [list] *)

Set Implicit Arguments.

(** Mapping a function over an option type. *)

Definition option_map (A B: Type) (f: A -> B) (x: option A) : option B :=
  match x with
  | None => None
  | Some y => Some (f y)
  end.

(** Mapping a function over a sum type. *)

Definition sum_left_map (A B C: Type) (f: A -> B) (x: A + C) : B + C :=
  match x with
  | inl y => inl C (f y)
  | inr z => inr B z
  end.

(** Properties of [List.nth] (n-th element of a list). *)

Hint Resolve in_eq in_cons: coqlib.

Lemma nth_error_in:
  forall (A: Type) (n: nat) (l: list A) (x: A),
  List.nth_error l n = Some x -> In x l.
Proof.
  induction n; simpl.
   destruct l; intros.
    discriminate.
    injection H; intro; subst a. apply in_eq.
   destruct l; intros.
    discriminate.
    apply in_cons. auto.
Qed.
Hint Resolve nth_error_in: coqlib.

Lemma nth_error_nil:
  forall (A: Type) (idx: nat), nth_error (@nil A) idx = None.
Proof.
  induction idx; simpl; intros; reflexivity.
Qed.
Hint Resolve nth_error_nil: coqlib.

(** Properties of [List.incl] (list inclusion). *)

Lemma incl_cons_inv:
  forall (A: Type) (a: A) (b c: list A),
  incl (a :: b) c -> incl b c.
Proof.
  unfold incl; intros. apply H. apply in_cons. auto.
Qed.
Hint Resolve incl_cons_inv: coqlib.

Lemma incl_app_inv_l:
  forall (A: Type) (l1 l2 m: list A),
  incl (l1 ++ l2) m -> incl l1 m.
Proof.
  unfold incl; intros. apply H. apply in_or_app. left; assumption.
Qed.

Lemma incl_app_inv_r:
  forall (A: Type) (l1 l2 m: list A),
  incl (l1 ++ l2) m -> incl l2 m.
Proof.
  unfold incl; intros. apply H. apply in_or_app. right; assumption.
Qed.

Hint Resolve  incl_tl incl_refl incl_app_inv_l incl_app_inv_r: coqlib.

Lemma incl_same_head:
  forall (A: Type) (x: A) (l1 l2: list A),
  incl l1 l2 -> incl (x::l1) (x::l2).
Proof.
  intros; red; simpl; intros. intuition. 
Qed.

(** Properties of [List.map] (mapping a function over a list). *)

Lemma list_map_exten:
  forall (A B: Type) (f f': A -> B) (l: list A),
  (forall x, In x l -> f x = f' x) ->
  List.map f' l = List.map f l.
Proof.
  induction l; simpl; intros.
  reflexivity.
  rewrite <- H. rewrite IHl. reflexivity.
  intros. apply H. tauto.
  tauto.
Qed.

Lemma list_map_compose:
  forall (A B C: Type) (f: A -> B) (g: B -> C) (l: list A),
  List.map g (List.map f l) = List.map (fun x => g(f x)) l.
Proof.
  induction l; simpl. reflexivity. rewrite IHl; reflexivity.
Qed.

Lemma list_map_identity:
  forall (A: Type) (l: list A),
  List.map (fun (x:A) => x) l = l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma list_map_nth:
  forall (A B: Type) (f: A -> B) (l: list A) (n: nat),
  nth_error (List.map f l) n = option_map f (nth_error l n).
Proof.
  induction l; simpl; intros.
  repeat rewrite nth_error_nil. reflexivity.
  destruct n; simpl. reflexivity. auto.
Qed.

Lemma list_length_map:
  forall (A B: Type) (f: A -> B) (l: list A),
  List.length (List.map f l) = List.length l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma list_in_map_inv:
  forall (A B: Type) (f: A -> B) (l: list A) (y: B),
  In y (List.map f l) -> exists x:A, y = f x /\ In x l.
Proof.
  induction l; simpl; intros.
  contradiction.
  elim H; intro. 
  exists a; intuition auto.
  generalize (IHl y H0). intros [x [EQ IN]]. 
  exists x; tauto.
Qed.

Lemma list_append_map:
  forall (A B: Type) (f: A -> B) (l1 l2: list A),
  List.map f (l1 ++ l2) = List.map f l1 ++ List.map f l2.
Proof.
  induction l1; simpl; intros.
  auto. rewrite IHl1. auto.
Qed.

(** Properties of list membership. *)

Lemma in_cns:
  forall (A: Type) (x y: A) (l: list A), In x (y :: l) <-> y = x \/ In x l.
Proof.
  intros. simpl. tauto.
Qed.

Lemma in_app:
  forall (A: Type) (x: A) (l1 l2: list A), In x (l1 ++ l2) <-> In x l1 \/ In x l2.
Proof.
  intros. split; intro. apply in_app_or. auto. apply in_or_app. auto.
Qed.

Lemma list_in_insert:
  forall (A: Type) (x: A) (l1 l2: list A) (y: A),
  In x (l1 ++ l2) -> In x (l1 ++ y :: l2).
Proof.
  intros. apply in_or_app; simpl. elim (in_app_or _ _ _ H); intro; auto.
Qed.

(** [list_disjoint l1 l2] holds iff [l1] and [l2] have no elements 
  in common. *)

Definition list_disjoint (A: Type) (l1 l2: list A) : Prop :=
  forall (x y: A), In x l1 -> In y l2 -> x <> y.

Lemma list_disjoint_cons_left:
  forall (A: Type) (a: A) (l1 l2: list A),
  list_disjoint (a :: l1) l2 -> list_disjoint l1 l2.
Proof.
  unfold list_disjoint; simpl; intros. apply H; tauto. 
Qed.

Lemma list_disjoint_cons_right:
  forall (A: Type) (a: A) (l1 l2: list A),
  list_disjoint l1 (a :: l2) -> list_disjoint l1 l2.
Proof.
  unfold list_disjoint; simpl; intros. apply H; tauto. 
Qed.

Lemma list_disjoint_notin:
  forall (A: Type) (l1 l2: list A) (a: A),
  list_disjoint l1 l2 -> In a l1 -> ~(In a l2).
Proof.
  unfold list_disjoint; intros; red; intros. 
  apply H with a a; auto.
Qed.

Lemma list_disjoint_sym:
  forall (A: Type) (l1 l2: list A),
  list_disjoint l1 l2 -> list_disjoint l2 l1.
Proof.
  unfold list_disjoint; intros. 
  apply sym_not_equal. apply H; auto.
Qed.

Lemma list_disjoint_dec:
  forall (A: Type) (eqA_dec: forall (x y: A), {x=y} + {x<>y}) (l1 l2: list A),
  {list_disjoint l1 l2} + {~list_disjoint l1 l2}.
Proof.
  induction l1; intros.
  left; red; intros. elim H.
  case (In_dec eqA_dec a l2); intro.
  right; red; intro. apply (H a a); auto with coqlib. 
  case (IHl1 l2); intro.
  left; red; intros. elim H; intro. 
    red; intro; subst a y. contradiction.
    apply l; auto.
  right; red; intros. elim n0. eapply list_disjoint_cons_left; eauto.
Defined.

(** [list_equiv l1 l2] holds iff the lists [l1] and [l2] contain the same elements. *)

Definition list_equiv (A : Type) (l1 l2: list A) : Prop :=
  forall x, In x l1 <-> In x l2.

(** [list_norepet l] holds iff the list [l] contains no repetitions,
  i.e. no element occurs twice. *)

Inductive list_norepet (A: Type) : list A -> Prop :=
  | list_norepet_nil:
      list_norepet nil
  | list_norepet_cons:
      forall hd tl,
      ~(In hd tl) -> list_norepet tl -> list_norepet (hd :: tl).

Lemma list_norepet_dec:
  forall (A: Type) (eqA_dec: forall (x y: A), {x=y} + {x<>y}) (l: list A),
  {list_norepet l} + {~list_norepet l}.
Proof.
  induction l.
  left; constructor.
  destruct IHl. 
  case (In_dec eqA_dec a l); intro.
  right. red; intro. inversion H. contradiction. 
  left. constructor; auto.
  right. red; intro. inversion H. contradiction.
Defined.

Lemma list_map_norepet:
  forall (A B: Type) (f: A -> B) (l: list A),
  list_norepet l ->
  (forall x y, In x l -> In y l -> x <> y -> f x <> f y) ->
  list_norepet (List.map f l).
Proof.
  induction 1; simpl; intros.
  constructor.
  constructor.
  red; intro. generalize (list_in_map_inv f _ _ H2).
  intros [x [EQ IN]]. generalize EQ. change (f hd <> f x).
  apply H1. tauto. tauto. 
  red; intro; subst x. contradiction.
  apply IHlist_norepet. intros. apply H1. tauto. tauto. auto.
Qed.

Remark list_norepet_append_commut:
  forall (A: Type) (a b: list A),
  list_norepet (a ++ b) -> list_norepet (b ++ a).
Proof.
  intro A.
  assert (forall (x: A) (b: list A) (a: list A), 
           list_norepet (a ++ b) -> ~(In x a) -> ~(In x b) -> 
           list_norepet (a ++ x :: b)).
    induction a; simpl; intros.
    constructor; auto.
    inversion H. constructor. red; intro.
    elim (in_app_or _ _ _ H6); intro.
    elim H4. apply in_or_app. tauto.
    elim H7; intro. subst a. elim H0. left. auto. 
    elim H4. apply in_or_app. tauto.
    auto.
  induction a; simpl; intros.
  rewrite <- app_nil_end. auto.
  inversion H0. apply H. auto. 
  red; intro; elim H3. apply in_or_app. tauto.
  red; intro; elim H3. apply in_or_app. tauto.
Qed.

Lemma list_norepet_app:
  forall (A: Type) (l1 l2: list A),
  list_norepet (l1 ++ l2) <->
  list_norepet l1 /\ list_norepet l2 /\ list_disjoint l1 l2.
Proof.
  induction l1; simpl; intros; split; intros.
  intuition. constructor. red;simpl;auto.
  tauto.
  inversion H; subst. rewrite IHl1 in H3. rewrite in_app in H2.
  intuition.
  constructor; auto. red; intros. elim H2; intro. congruence. auto. 
  destruct H as [B [C D]]. inversion B; subst. 
  constructor. rewrite in_app. intuition. elim (D a a); auto. apply in_eq. 
  rewrite IHl1. intuition. red; intros. apply D; auto. apply in_cons; auto. 
Qed.

Lemma list_norepet_append:
  forall (A: Type) (l1 l2: list A),
  list_norepet l1 -> list_norepet l2 -> list_disjoint l1 l2 ->
  list_norepet (l1 ++ l2).
Proof.
  generalize list_norepet_app; firstorder.
Qed.

Lemma list_norepet_append_right:
  forall (A: Type) (l1 l2: list A),
  list_norepet (l1 ++ l2) -> list_norepet l2.
Proof.
  generalize list_norepet_app; firstorder.
Qed.

Lemma list_norepet_append_left:
  forall (A: Type) (l1 l2: list A),
  list_norepet (l1 ++ l2) -> list_norepet l1.
Proof.
  generalize list_norepet_app; firstorder.
Qed.

(** [is_tail l1 l2] holds iff [l2] is of the form [l ++ l1] for some [l]. *)

Inductive is_tail (A: Type): list A -> list A -> Prop :=
  | is_tail_refl:
      forall c, is_tail c c
  | is_tail_cons:
      forall i c1 c2, is_tail c1 c2 -> is_tail c1 (i :: c2).

Lemma is_tail_in:
  forall (A: Type) (i: A) c1 c2, is_tail (i :: c1) c2 -> In i c2.
Proof.
  induction c2; simpl; intros.
  inversion H.
  inversion H. tauto. right; auto.
Qed.

Lemma is_tail_cons_left:
  forall (A: Type) (i: A) c1 c2, is_tail (i :: c1) c2 -> is_tail c1 c2.
Proof.
  induction c2; intros; inversion H.
  constructor. constructor. constructor. auto. 
Qed.

Hint Resolve is_tail_refl is_tail_cons is_tail_in is_tail_cons_left: coqlib.

Lemma is_tail_incl:
  forall (A: Type) (l1 l2: list A), is_tail l1 l2 -> incl l1 l2.
Proof.
  induction 1; eauto with coqlib.
Qed.

Lemma is_tail_trans:
  forall (A: Type) (l1 l2: list A),
  is_tail l1 l2 -> forall (l3: list A), is_tail l2 l3 -> is_tail l1 l3.
Proof.
  induction 1; intros. auto. apply IHis_tail. eapply is_tail_cons_left; eauto.
Qed.

(** [list_forall2 P [x1 ... xN] [y1 ... yM] holds iff [N = M] and
  [P xi yi] holds for all [i]. *)

Section FORALL2.

Variable A: Type.
Variable B: Type.
Variable P: A -> B -> Prop.

Inductive list_forall2: list A -> list B -> Prop :=
  | list_forall2_nil:
      list_forall2 nil nil
  | list_forall2_cons:
      forall a1 al b1 bl,
      P a1 b1 ->
      list_forall2 al bl ->
      list_forall2 (a1 :: al) (b1 :: bl).

End FORALL2.

Lemma list_forall2_imply:
  forall (A B: Type) (P1: A -> B -> Prop) (l1: list A) (l2: list B),
  list_forall2 P1 l1 l2 ->
  forall (P2: A -> B -> Prop),
  (forall v1 v2, In v1 l1 -> In v2 l2 -> P1 v1 v2 -> P2 v1 v2) ->
  list_forall2 P2 l1 l2.
Proof.
  induction 1; intros.
  constructor.
  constructor. auto with coqlib. apply IHlist_forall2; auto. 
  intros. auto with coqlib.
Qed.

(** Dropping the first or first two elements of a list. *)

Definition list_drop1 (A: Type) (x: list A) :=
  match x with nil => nil | hd :: tl => tl end.
Definition list_drop2 (A: Type) (x: list A) :=
  match x with nil => nil | hd :: nil => nil | hd1 :: hd2 :: tl => tl end.

Lemma list_drop1_incl:
  forall (A: Type) (x: A) (l: list A), In x (list_drop1 l) -> In x l.
Proof.
  intros. destruct l. elim H. simpl in H. auto with coqlib.
Qed.

Lemma list_drop2_incl:
  forall (A: Type) (x: A) (l: list A), In x (list_drop2 l) -> In x l.
Proof.
  intros. destruct l. elim H. destruct l. elim H.
  simpl in H. auto with coqlib.
Qed.

Lemma list_drop1_norepet:
  forall (A: Type) (l: list A), list_norepet l -> list_norepet (list_drop1 l).
Proof.
  intros. destruct l; simpl. constructor. inversion H. auto.
Qed.

Lemma list_drop2_norepet:
  forall (A: Type) (l: list A), list_norepet l -> list_norepet (list_drop2 l).
Proof.
  intros. destruct l; simpl. constructor.
  destruct l; simpl. constructor. inversion H. inversion H3. auto.
Qed.

Lemma list_map_drop1:
  forall (A B: Type) (f: A -> B) (l: list A), list_drop1 (map f l) = map f (list_drop1 l).
Proof.
  intros; destruct l; reflexivity.
Qed.

Lemma list_map_drop2:
  forall (A B: Type) (f: A -> B) (l: list A), list_drop2 (map f l) = map f (list_drop2 l).
Proof.
  intros; destruct l. reflexivity. destruct l; reflexivity.
Qed.

(** * Definitions and theorems over boolean types *)

Definition proj_sumbool (P Q: Prop) (a: {P} + {Q}) : bool :=
  if a then true else false.

Implicit Arguments proj_sumbool [P Q].

Coercion proj_sumbool: sumbool >-> bool.

Lemma proj_sumbool_true:
  forall (P Q: Prop) (a: {P}+{Q}), proj_sumbool a = true -> P.
Proof.
  intros P Q a. destruct a; simpl. auto. congruence.
Qed.

Section DECIDABLE_EQUALITY.

Variable A: Type.
Variable dec_eq: forall (x y: A), {x=y} + {x<>y}.
Variable B: Type.

Lemma dec_eq_true:
  forall (x: A) (ifso ifnot: B),
  (if dec_eq x x then ifso else ifnot) = ifso.
Proof.
  intros. destruct (dec_eq x x). auto. congruence.
Qed.

Lemma dec_eq_false:
  forall (x y: A) (ifso ifnot: B),
  x <> y -> (if dec_eq x y then ifso else ifnot) = ifnot.
Proof.
  intros. destruct (dec_eq x y). congruence. auto.
Qed.

Lemma dec_eq_sym:
  forall (x y: A) (ifso ifnot: B),
  (if dec_eq x y then ifso else ifnot) =
  (if dec_eq y x then ifso else ifnot).
Proof.
  intros. destruct (dec_eq x y). 
  subst y. rewrite dec_eq_true. auto.
  rewrite dec_eq_false; auto.
Qed.

End DECIDABLE_EQUALITY.
