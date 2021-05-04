(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria Paris            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Additional operations and proofs about binary integers,
    on top of the ZArith standard library. *)

Require Import Psatz Zquot.
Require Import Coqlib.

(** ** Modulo arithmetic *)

(** We define and state properties of equality and arithmetic modulo a
  positive integer. *)

Section EQ_MODULO.

Variable modul: Z.
Hypothesis modul_pos: modul > 0.

Definition eqmod (x y: Z) : Prop := exists k, x = k * modul + y.

Lemma eqmod_refl: forall x, eqmod x x.
Proof.
  intros; red. exists 0. lia.
Qed.

Lemma eqmod_refl2: forall x y, x = y -> eqmod x y.
Proof.
  intros. subst y. apply eqmod_refl.
Qed.

Lemma eqmod_sym: forall x y, eqmod x y -> eqmod y x.
Proof.
  intros x y [k EQ]; red. exists (-k). subst x. ring.
Qed.

Lemma eqmod_trans: forall x y z, eqmod x y -> eqmod y z -> eqmod x z.
Proof.
  intros x y z [k1 EQ1] [k2 EQ2]; red.
  exists (k1 + k2). subst x; subst y. ring.
Qed.

Lemma eqmod_small_eq:
  forall x y, eqmod x y -> 0 <= x < modul -> 0 <= y < modul -> x = y.
Proof.
  intros x y [k EQ] I1 I2.
  generalize (Zdiv_unique _ _ _ _ EQ I2). intro.
  rewrite (Z.div_small x modul I1) in H. subst k. lia.
Qed.

Lemma eqmod_mod_eq:
  forall x y, eqmod x y -> x mod modul = y mod modul.
Proof.
  intros x y [k EQ]. subst x.
  rewrite Z.add_comm. apply Z_mod_plus. auto.
Qed.

Lemma eqmod_mod:
  forall x, eqmod x (x mod modul).
Proof.
  intros; red. exists (x / modul).
  rewrite Z.mul_comm. apply Z_div_mod_eq. auto.
Qed.

Lemma eqmod_add:
  forall a b c d, eqmod a b -> eqmod c d -> eqmod (a + c) (b + d).
Proof.
  intros a b c d [k1 EQ1] [k2 EQ2]; red.
  subst a; subst c. exists (k1 + k2). ring.
Qed.

Lemma eqmod_neg:
  forall x y, eqmod x y -> eqmod (-x) (-y).
Proof.
  intros x y [k EQ]; red. exists (-k). rewrite EQ. ring.
Qed.

Lemma eqmod_sub:
  forall a b c d, eqmod a b -> eqmod c d -> eqmod (a - c) (b - d).
Proof.
  intros a b c d [k1 EQ1] [k2 EQ2]; red.
  subst a; subst c. exists (k1 - k2). ring.
Qed.

Lemma eqmod_mult:
  forall a b c d, eqmod a c -> eqmod b d -> eqmod (a * b) (c * d).
Proof.
  intros a b c d [k1 EQ1] [k2 EQ2]; red.
  subst a; subst b.
  exists (k1 * k2 * modul + c * k2 + k1 * d).
  ring.
Qed.

End EQ_MODULO.

Lemma eqmod_divides:
  forall n m x y, eqmod n x y -> Z.divide m n -> eqmod m x y.
Proof.
  intros. destruct H as [k1 EQ1]. destruct H0 as [k2 EQ2].
  exists (k1*k2). rewrite <- Z.mul_assoc. rewrite <- EQ2. auto.
Qed.

(** ** Fast normalization modulo [2^n] *)

Fixpoint P_mod_two_p (p: positive) (n: nat) {struct n} : Z :=
  match n with
  | O => 0
  | S m =>
      match p with
      | xH => 1
      | xO q => Z.double (P_mod_two_p q m)
      | xI q => Z.succ_double (P_mod_two_p q m)
      end
  end.

Definition Z_mod_two_p (x: Z) (n: nat) : Z :=
  match x with
  | Z0 => 0
  | Zpos p => P_mod_two_p p n
  | Zneg p => let r := P_mod_two_p p n in if zeq r 0 then 0 else two_power_nat n - r
  end.

Lemma P_mod_two_p_range:
  forall n p, 0 <= P_mod_two_p p n < two_power_nat n.
Proof.
  induction n; simpl; intros.
  - rewrite two_power_nat_O. lia.
  - rewrite two_power_nat_S. destruct p.
    + generalize (IHn p). rewrite Z.succ_double_spec. lia.
    + generalize (IHn p). rewrite Z.double_spec. lia.
    + generalize (two_power_nat_pos n). lia.
Qed.

Lemma P_mod_two_p_eq:
  forall n p, P_mod_two_p p n = (Zpos p) mod (two_power_nat n).
Proof.
  assert (forall n p, exists y, Zpos p = y * two_power_nat n + P_mod_two_p p n).
  {
    induction n; simpl; intros.
    - rewrite two_power_nat_O. exists (Zpos p). ring.
    - rewrite two_power_nat_S. destruct p.
      + destruct (IHn p) as [y EQ]. exists y.
        change (Zpos p~1) with (2 * Zpos p + 1). rewrite EQ.
        rewrite Z.succ_double_spec. ring.
      + destruct (IHn p) as [y EQ]. exists y.
        change (Zpos p~0) with (2 * Zpos p). rewrite EQ.
        rewrite (Z.double_spec (P_mod_two_p p n)). ring.
      + exists 0; lia.
  }
  intros.
  destruct (H n p) as [y EQ].
  symmetry. apply Zmod_unique with y. auto. apply P_mod_two_p_range.
Qed.

Lemma Z_mod_two_p_range:
  forall n x, 0 <= Z_mod_two_p x n < two_power_nat n.
Proof.
  intros; unfold Z_mod_two_p. generalize (two_power_nat_pos n); intros.
  destruct x.
  - intuition.
  - apply P_mod_two_p_range.
  - set (r := P_mod_two_p p n).
    assert (0 <= r < two_power_nat n) by apply P_mod_two_p_range.
    destruct (zeq r 0).
    + intuition.
    + Psatz.lia.
Qed.

Lemma Z_mod_two_p_eq:
  forall n x, Z_mod_two_p x n = x mod (two_power_nat n).
Proof.
  intros. unfold Z_mod_two_p. generalize (two_power_nat_pos n); intros.
  destruct x.
  - rewrite Zmod_0_l. auto.
  - apply P_mod_two_p_eq.
  - generalize (P_mod_two_p_range n p) (P_mod_two_p_eq n p). intros A B.
    exploit (Z_div_mod_eq (Zpos p) (two_power_nat n)); auto. intros C.
    set (q := Zpos p / two_power_nat n) in *.
    set (r := P_mod_two_p p n) in *.
    rewrite <- B in C.
    change (Z.neg p) with (- (Z.pos p)). destruct (zeq r 0).
    + symmetry. apply Zmod_unique with (-q). rewrite C; rewrite e. Psatz.lia.
      intuition.
    + symmetry. apply Zmod_unique with (-q - 1). rewrite C. Psatz.lia.
      intuition.
Qed.

(** ** Bit-level operations and properties *)

(** Shift [x] left by one and insert [b] as the low bit of the result. *)

Definition Zshiftin (b: bool) (x: Z) : Z :=
  if b then Z.succ_double x else Z.double x.

Remark Ztestbit_0: forall n, Z.testbit 0 n = false.
Proof Z.testbit_0_l.

Remark Ztestbit_1: forall n, Z.testbit 1 n = zeq n 0.
Proof.
  intros. destruct n; simpl; auto.
Qed.

Remark Ztestbit_m1: forall n, 0 <= n -> Z.testbit (-1) n = true.
Proof.
  intros. destruct n; simpl; auto.
Qed.

Remark Zshiftin_spec:
  forall b x, Zshiftin b x = 2 * x + (if b then 1 else 0).
Proof.
  unfold Zshiftin; intros. destruct b.
  - rewrite Z.succ_double_spec. lia.
  - rewrite Z.double_spec. lia.
Qed.

Remark Zshiftin_inj:
  forall b1 x1 b2 x2,
  Zshiftin b1 x1 = Zshiftin b2 x2 -> b1 = b2 /\ x1 = x2.
Proof.
  intros. rewrite !Zshiftin_spec in H.
  destruct b1; destruct b2.
  split; [auto|lia].
  extlia.
  extlia.
  split; [auto|lia].
Qed.

Remark Zdecomp:
  forall x, x = Zshiftin (Z.odd x) (Z.div2 x).
Proof.
  intros. destruct x; simpl.
  - auto.
  - destruct p; auto.
  - destruct p; auto. simpl. rewrite Pos.pred_double_succ. auto.
Qed.

Remark Ztestbit_shiftin:
  forall b x n,
  0 <= n ->
  Z.testbit (Zshiftin b x) n = if zeq n 0 then b else Z.testbit x (Z.pred n).
Proof.
  intros. rewrite Zshiftin_spec. destruct (zeq n 0).
  - subst n. destruct b.
    + apply Z.testbit_odd_0.
    + rewrite Z.add_0_r. apply Z.testbit_even_0.
  - assert (0 <= Z.pred n) by lia.
    set (n' := Z.pred n) in *.
    replace n with (Z.succ n') by (unfold n'; lia).
    destruct b.
    + apply Z.testbit_odd_succ; auto.
    + rewrite Z.add_0_r. apply Z.testbit_even_succ; auto.
Qed.

Remark Ztestbit_shiftin_base:
  forall b x, Z.testbit (Zshiftin b x) 0 = b.
Proof.
  intros. rewrite Ztestbit_shiftin; reflexivity.
Qed.

Remark Ztestbit_shiftin_succ:
  forall b x n, 0 <= n -> Z.testbit (Zshiftin b x) (Z.succ n) = Z.testbit x n.
Proof.
  intros. rewrite Ztestbit_shiftin. rewrite zeq_false. rewrite Z.pred_succ. auto.
  lia. lia.
Qed.

Lemma Zshiftin_ind:
  forall (P: Z -> Prop),
  P 0 ->
  (forall b x, 0 <= x -> P x -> P (Zshiftin b x)) ->
  forall x, 0 <= x -> P x.
Proof.
  intros. destruct x.
  - auto.
  - induction p.
    + change (P (Zshiftin true (Z.pos p))). auto.
    + change (P (Zshiftin false (Z.pos p))). auto.
    + change (P (Zshiftin true 0)). apply H0. lia. auto.
  - compute in H1. intuition congruence.
Qed.

Lemma Zshiftin_pos_ind:
  forall (P: Z -> Prop),
  P 1 ->
  (forall b x, 0 < x -> P x -> P (Zshiftin b x)) ->
  forall x, 0 < x -> P x.
Proof.
  intros. destruct x; simpl in H1; try discriminate.
  induction p.
    + change (P (Zshiftin true (Z.pos p))). auto.
    + change (P (Zshiftin false (Z.pos p))). auto.
    + auto.
Qed.

(** ** Bit-wise decomposition ([Z.testbit]) *)

Remark Ztestbit_eq:
  forall n x, 0 <= n ->
  Z.testbit x n = if zeq n 0 then Z.odd x else Z.testbit (Z.div2 x) (Z.pred n).
Proof.
  intros. rewrite (Zdecomp x) at 1. apply Ztestbit_shiftin; auto.
Qed.

Remark Ztestbit_base:
  forall x, Z.testbit x 0 = Z.odd x.
Proof.
  intros. rewrite Ztestbit_eq; reflexivity.
Qed.

Remark Ztestbit_succ:
  forall n x, 0 <= n -> Z.testbit x (Z.succ n) = Z.testbit (Z.div2 x) n.
Proof.
  intros. rewrite Ztestbit_eq. rewrite zeq_false. rewrite Z.pred_succ. auto.
  lia. lia.
Qed.

Lemma eqmod_same_bits:
  forall n x y,
  (forall i, 0 <= i < Z.of_nat n -> Z.testbit x i = Z.testbit y i) ->
  eqmod (two_power_nat n) x y.
Proof.
  induction n; intros.
  - change (two_power_nat 0) with 1. exists (x-y); ring.
  - rewrite two_power_nat_S.
    assert (eqmod (two_power_nat n) (Z.div2 x) (Z.div2 y)).
      apply IHn. intros. rewrite <- !Ztestbit_succ. apply H. rewrite Nat2Z.inj_succ; lia.
      lia. lia.
  destruct H0 as [k EQ].
  exists k. rewrite (Zdecomp x). rewrite (Zdecomp y).
  replace (Z.odd y) with (Z.odd x).
  rewrite EQ. rewrite !Zshiftin_spec. ring.
  exploit (H 0). rewrite Nat2Z.inj_succ; lia.
  rewrite !Ztestbit_base. auto.
Qed.

Lemma same_bits_eqmod:
  forall n x y i,
  eqmod (two_power_nat n) x y -> 0 <= i < Z.of_nat n ->
  Z.testbit x i = Z.testbit y i.
Proof.
  induction n; intros.
  - simpl in H0. extlia.
  - rewrite Nat2Z.inj_succ in H0. rewrite two_power_nat_S in H.
    rewrite !(Ztestbit_eq i); intuition.
    destruct H as [k EQ].
    assert (EQ': Zshiftin (Z.odd x) (Z.div2 x) =
                 Zshiftin (Z.odd y) (k * two_power_nat n + Z.div2 y)).
    {
      rewrite (Zdecomp x) in EQ. rewrite (Zdecomp y) in EQ.
      rewrite EQ. rewrite !Zshiftin_spec. ring.
    }
    exploit Zshiftin_inj; eauto. intros [A B].
    destruct (zeq i 0).
    + auto.
    + apply IHn. exists k; auto. lia.
Qed.

Lemma equal_same_bits:
  forall x y,
  (forall i, 0 <= i -> Z.testbit x i = Z.testbit y i) ->
  x = y.
Proof Z.bits_inj'.

Lemma Z_one_complement:
  forall i, 0 <= i ->
  forall x, Z.testbit (-x-1) i = negb (Z.testbit x i).
Proof.
  intros i0 POS0. pattern i0. apply Zlt_0_ind; auto.
  intros i IND POS x.
  rewrite (Zdecomp x). set (y := Z.div2 x).
  replace (- Zshiftin (Z.odd x) y - 1)
     with (Zshiftin (negb (Z.odd x)) (- y - 1)).
  rewrite !Ztestbit_shiftin; auto.
  destruct (zeq i 0). auto. apply IND. lia.
  rewrite !Zshiftin_spec. destruct (Z.odd x); simpl negb; ring.
Qed.

Lemma Ztestbit_above:
  forall n x i,
  0 <= x < two_power_nat n ->
  i >= Z.of_nat n ->
  Z.testbit x i = false.
Proof.
  induction n; intros.
  - change (two_power_nat 0) with 1 in H.
    replace x with 0 by lia.
    apply Z.testbit_0_l.
  - rewrite Nat2Z.inj_succ in H0. rewrite Ztestbit_eq. rewrite zeq_false.
    apply IHn. rewrite two_power_nat_S in H. rewrite (Zdecomp x) in H.
    rewrite Zshiftin_spec in H. destruct (Z.odd x); lia.
    lia. lia. lia.
Qed.

Lemma Ztestbit_above_neg:
  forall n x i,
  -two_power_nat n <= x < 0 ->
  i >= Z.of_nat n ->
  Z.testbit x i = true.
Proof.
  intros. set (y := -x-1).
  assert (Z.testbit y i = false).
    apply Ztestbit_above with n.
    unfold y; lia. auto.
  unfold y in H1. rewrite Z_one_complement in H1.
  change true with (negb false). rewrite <- H1. rewrite negb_involutive; auto.
  lia.
Qed.

Lemma Zsign_bit:
  forall n x,
  0 <= x < two_power_nat (S n) ->
  Z.testbit x (Z.of_nat n) = if zlt x (two_power_nat n) then false else true.
Proof.
  induction n; intros.
  - change (two_power_nat 1) with 2 in H.
    assert (x = 0 \/ x = 1) by lia.
    destruct H0; subst x; reflexivity.
  - rewrite Nat2Z.inj_succ. rewrite Ztestbit_eq. rewrite zeq_false. rewrite Z.pred_succ.
    rewrite IHn. rewrite two_power_nat_S.
    destruct (zlt (Z.div2 x) (two_power_nat n)); rewrite (Zdecomp x); rewrite Zshiftin_spec.
    rewrite zlt_true. auto. destruct (Z.odd x); lia.
    rewrite zlt_false. auto. destruct (Z.odd x); lia.
    rewrite (Zdecomp x) in H; rewrite Zshiftin_spec in H.
    rewrite two_power_nat_S in H. destruct (Z.odd x); lia.
    lia. lia.
Qed.

Lemma Ztestbit_le:
  forall x y,
  0 <= y ->
  (forall i, 0 <= i -> Z.testbit x i = true -> Z.testbit y i = true) ->
  x <= y.
Proof.
  intros x y0 POS0; revert x; pattern y0; apply Zshiftin_ind; auto; intros.
  - replace x with 0. lia. apply equal_same_bits; intros.
    rewrite Ztestbit_0. destruct (Z.testbit x i) as [] eqn:E; auto.
    exploit H; eauto. rewrite Ztestbit_0. auto.
  - assert (Z.div2 x0 <= x).
    { apply H0. intros. exploit (H1 (Z.succ i)).
        lia. rewrite Ztestbit_succ; auto. rewrite Ztestbit_shiftin_succ; auto.
    }
    rewrite (Zdecomp x0). rewrite !Zshiftin_spec.
    destruct (Z.odd x0) as [] eqn:E1; destruct b as [] eqn:E2; try lia.
    exploit (H1 0). lia. rewrite Ztestbit_base; auto.
    rewrite Ztestbit_shiftin_base. congruence.
Qed.

Lemma Ztestbit_mod_two_p:
  forall n x i,
  0 <= n -> 0 <= i ->
  Z.testbit (x mod (two_p n)) i = if zlt i n then Z.testbit x i else false.
Proof.
  intros n0 x i N0POS. revert x i; pattern n0; apply natlike_ind; auto.
  - intros. change (two_p 0) with 1. rewrite Zmod_1_r. rewrite Z.testbit_0_l.
    rewrite zlt_false; auto. lia.
  - intros. rewrite two_p_S; auto.
    replace (x0 mod (2 * two_p x))
       with (Zshiftin (Z.odd x0) (Z.div2 x0 mod two_p x)).
    rewrite Ztestbit_shiftin; auto. rewrite (Ztestbit_eq i x0); auto. destruct (zeq i 0).
    + rewrite zlt_true; auto. lia.
    + rewrite H0. destruct (zlt (Z.pred i) x).
      * rewrite zlt_true; auto. lia.
      * rewrite zlt_false; auto. lia.
      * lia.
    + rewrite (Zdecomp x0) at 3. set (x1 := Z.div2 x0). symmetry.
      apply Zmod_unique with (x1 / two_p x).
      rewrite !Zshiftin_spec. rewrite Z.add_assoc. f_equal.
      transitivity (2 * (two_p x * (x1 / two_p x) + x1 mod two_p x)).
      f_equal. apply Z_div_mod_eq. apply two_p_gt_ZERO; auto.
      ring.
      rewrite Zshiftin_spec. exploit (Z_mod_lt x1 (two_p x)). apply two_p_gt_ZERO; auto.
      destruct (Z.odd x0); lia.
Qed.

Corollary Ztestbit_two_p_m1:
  forall n i, 0 <= n -> 0 <= i ->
  Z.testbit (two_p n - 1) i = if zlt i n then true else false.
Proof.
  intros. replace (two_p n - 1) with ((-1) mod (two_p n)).
  rewrite Ztestbit_mod_two_p; auto. destruct (zlt i n); auto. apply Ztestbit_m1; auto.
  apply Zmod_unique with (-1). ring.
  exploit (two_p_gt_ZERO n). auto. lia.
Qed.

Corollary Ztestbit_neg_two_p:
  forall n i, 0 <= n -> 0 <= i ->
  Z.testbit (- (two_p n)) i = if zlt i n then false else true.
Proof.
  intros. 
  replace (- two_p n) with (- (two_p n - 1) - 1) by lia. 
  rewrite Z_one_complement by auto.
  rewrite Ztestbit_two_p_m1 by auto. 
  destruct (zlt i n); auto.
Qed.

Lemma Z_add_is_or:
  forall i, 0 <= i ->
  forall x y,
  (forall j, 0 <= j <= i -> Z.testbit x j && Z.testbit y j = false) ->
  Z.testbit (x + y) i = Z.testbit x i || Z.testbit y i.
Proof.
  intros i0 POS0. pattern i0. apply Zlt_0_ind; auto.
  intros i IND POS x y EXCL.
  rewrite (Zdecomp x) in *. rewrite (Zdecomp y) in *.
  transitivity (Z.testbit (Zshiftin (Z.odd x || Z.odd y) (Z.div2 x + Z.div2 y)) i).
  - f_equal. rewrite !Zshiftin_spec.
    exploit (EXCL 0). lia. rewrite !Ztestbit_shiftin_base. intros.
Opaque Z.mul.
    destruct (Z.odd x); destruct (Z.odd y); simpl in *; discriminate || ring.
  - rewrite !Ztestbit_shiftin; auto.
    destruct (zeq i 0).
    + auto.
    + apply IND. lia. intros.
      exploit (EXCL (Z.succ j)). lia.
      rewrite !Ztestbit_shiftin_succ. auto.
      lia. lia.
Qed.

(** ** Zero and sign extensions *)

(** In pseudo-code:
<<
    Fixpoint Zzero_ext (n: Z) (x: Z) : Z :=
      if zle n 0 then
        0
      else
        Zshiftin (Z.odd x) (Zzero_ext (Z.pred n) (Z.div2 x)).
    Fixpoint Zsign_ext (n: Z) (x: Z) : Z :=
      if zle n 1 then
        if Z.odd x then -1 else 0
      else
        Zshiftin (Z.odd x) (Zzero_ext (Z.pred n) (Z.div2 x)).
>>
  We encode this [nat]-like recursion using the [Z.iter] iteration
  function, in order to make the [Zzero_ext] and [Zsign_ext]
  functions efficiently executable within Coq.
*)

Definition Zzero_ext (n: Z) (x: Z) : Z :=
  Z.iter n
    (fun rec x => Zshiftin (Z.odd x) (rec (Z.div2 x)))
    (fun x => 0)
    x.

Definition Zsign_ext (n: Z) (x: Z) : Z :=
  Z.iter (Z.pred n)
    (fun rec x => Zshiftin (Z.odd x) (rec (Z.div2 x)))
    (fun x => if Z.odd x && zlt 0 n then -1 else 0)
    x.

Lemma Ziter_base:
  forall (A: Type) n (f: A -> A) x, n <= 0 -> Z.iter n f x = x.
Proof.
  intros. unfold Z.iter. destruct n; auto. compute in H. elim H; auto.
Qed.

Lemma Ziter_succ:
  forall (A: Type) n (f: A -> A) x,
  0 <= n -> Z.iter (Z.succ n) f x = f (Z.iter n f x).
Proof.
  intros. destruct n; simpl.
  - auto.
  - rewrite Pos.add_1_r. apply Pos.iter_succ.
  - compute in H. elim H; auto.
Qed.

Lemma Znatlike_ind:
  forall (P: Z -> Prop),
  (forall n, n <= 0 -> P n) ->
  (forall n, 0 <= n -> P n -> P (Z.succ n)) ->
  forall n, P n.
Proof.
  intros. destruct (zle 0 n).
  apply natlike_ind; auto. apply H; lia.
  apply H. lia.
Qed.

Lemma Zzero_ext_spec:
  forall n x i, 0 <= i ->
  Z.testbit (Zzero_ext n x) i = if zlt i n then Z.testbit x i else false.
Proof.
  unfold Zzero_ext. induction n using Znatlike_ind.
  - intros. rewrite Ziter_base; auto.
    rewrite zlt_false. rewrite Ztestbit_0; auto. lia.
  - intros. rewrite Ziter_succ; auto.
    rewrite Ztestbit_shiftin; auto.
    rewrite (Ztestbit_eq i x); auto.
    destruct (zeq i 0).
    + subst i. rewrite zlt_true; auto. lia.
    + rewrite IHn. destruct (zlt (Z.pred i) n).
      rewrite zlt_true; auto. lia.
      rewrite zlt_false; auto. lia.
      lia.
Qed.

Lemma Zsign_ext_spec:
  forall n x i, 0 <= i ->
  Z.testbit (Zsign_ext n x) i = Z.testbit x (if zlt i n then i else n - 1).
Proof.
  intros n0 x i I0. unfold Zsign_ext. 
  unfold proj_sumbool; destruct (zlt 0 n0) as [N0|N0]; simpl.
- revert x i I0. pattern n0. apply Zlt_lower_bound_ind with (z := 1); [ | lia ].
  unfold Zsign_ext. intros.
  destruct (zeq x 1).
  + subst x; simpl.
    replace (if zlt i 1 then i else 0) with 0.
    rewrite Ztestbit_base.
    destruct (Z.odd x0); [ apply Ztestbit_m1; auto | apply Ztestbit_0 ].
    destruct (zlt i 1); lia.
  + set (x1 := Z.pred x). replace x1 with (Z.succ (Z.pred x1)) by lia.
    rewrite Ziter_succ by (unfold x1; lia). rewrite Ztestbit_shiftin by auto.
    destruct (zeq i 0).
    * subst i. rewrite zlt_true. rewrite Ztestbit_base; auto. lia.
    * rewrite H by (unfold x1; lia).
      unfold x1; destruct (zlt (Z.pred i) (Z.pred x)).
      ** rewrite zlt_true by lia.
         rewrite (Ztestbit_eq i x0) by lia.
         rewrite zeq_false by lia. auto.
      ** rewrite zlt_false by lia.
         rewrite (Ztestbit_eq (x - 1) x0) by lia.
         rewrite zeq_false by lia. auto.
- rewrite Ziter_base by lia. rewrite andb_false_r. 
  rewrite Z.testbit_0_l, Z.testbit_neg_r. auto.
  destruct (zlt i n0); lia.
Qed.

(** [Zzero_ext n x] is [x modulo 2^n] *)

Lemma Zzero_ext_mod:
  forall n x, 0 <= n -> Zzero_ext n x = x mod (two_p n).
Proof.
  intros. apply equal_same_bits; intros.
  rewrite Zzero_ext_spec, Ztestbit_mod_two_p by auto. auto.
Qed.

(** [Zzero_ext n x] is the unique integer congruent to [x] modulo [2^n] in the range [0...2^n-1]. *)

Lemma Zzero_ext_range:
  forall n x, 0 <= n -> 0 <= Zzero_ext n x < two_p n.
Proof.
  intros. rewrite Zzero_ext_mod; auto. apply Z_mod_lt. apply two_p_gt_ZERO. lia.
Qed.

Lemma eqmod_Zzero_ext:
  forall n x, 0 <= n -> eqmod (two_p n) (Zzero_ext n x) x.
Proof.
  intros. rewrite Zzero_ext_mod; auto. apply eqmod_sym. apply eqmod_mod.
  apply two_p_gt_ZERO. lia.
Qed.

(** Relation between [Zsign_ext n x] and (Zzero_ext n x] *)

Lemma Zsign_ext_zero_ext:
  forall n, 0 <= n -> forall x,
  Zsign_ext n x = Zzero_ext n x - (if Z.testbit x (n - 1) then two_p n else 0).
Proof.
  intros. apply equal_same_bits; intros.
  rewrite Zsign_ext_spec by auto.
  destruct (Z.testbit x (n - 1)) eqn:SIGNBIT.
- set (n' := - two_p n). 
  replace (Zzero_ext n x - two_p n) with (Zzero_ext n x + n') by (unfold n'; lia).
  rewrite Z_add_is_or; auto. 
  rewrite Zzero_ext_spec by auto. unfold n'; rewrite Ztestbit_neg_two_p by lia.
  destruct (zlt i n). rewrite orb_false_r; auto. auto.
  intros. rewrite Zzero_ext_spec by lia. unfold n'; rewrite Ztestbit_neg_two_p by lia.
  destruct (zlt j n); auto using andb_false_r.
- replace (Zzero_ext n x - 0) with (Zzero_ext n x) by lia.
  rewrite Zzero_ext_spec by auto.
  destruct (zlt i n); auto.
Qed.

(** [Zsign_ext n x] is the unique integer congruent to [x] modulo [2^n]
    in the range [-2^(n-1)...2^(n-1) - 1]. *)

Lemma Zsign_ext_range:
  forall n x, 0 < n -> -two_p (n-1) <= Zsign_ext n x < two_p (n-1).
Proof.
  intros.
  assert (A: 0 <= Zzero_ext n x < two_p n) by (apply Zzero_ext_range; lia).
  assert (B: Z.testbit (Zzero_ext n x) (n - 1) =
             if zlt (Zzero_ext n x) (two_p (n - 1)) then false else true).
  { set (N := Z.to_nat (n - 1)).
    generalize (Zsign_bit N (Zzero_ext n x)). 
    rewrite ! two_power_nat_two_p.
    rewrite inj_S.  unfold N; rewrite Z2Nat.id by lia.
    intros X; apply X.  replace (Z.succ (n - 1)) with n by lia. exact A. 
  }
  assert (C: two_p n = 2 * two_p (n - 1)).
  { rewrite <- two_p_S by lia. f_equal; lia. }
  rewrite Zzero_ext_spec, zlt_true in B by lia.
  rewrite Zsign_ext_zero_ext by lia. rewrite B.
  destruct (zlt (Zzero_ext n x) (two_p (n - 1))); lia.
Qed.

Lemma eqmod_Zsign_ext:
  forall n x, 0 <= n ->
  eqmod (two_p n) (Zsign_ext n x) x.
Proof.
  intros. rewrite Zsign_ext_zero_ext by auto. 
  apply eqmod_trans with (x - 0). 
  apply eqmod_sub. 
  apply eqmod_Zzero_ext; lia.
  exists (if Z.testbit x (n - 1) then 1 else 0). destruct (Z.testbit x (n - 1)); ring.
  apply eqmod_refl2; lia.
Qed.

(** ** Decomposition of a number as a sum of powers of two. *)

Fixpoint Z_one_bits (n: nat) (x: Z) (i: Z) {struct n}: list Z :=
  match n with
  | O => nil
  | S m =>
      if Z.odd x
      then i :: Z_one_bits m (Z.div2 x) (i+1)
      else Z_one_bits m (Z.div2 x) (i+1)
  end.

Fixpoint powerserie (l: list Z): Z :=
  match l with
  | nil => 0
  | x :: xs => two_p x + powerserie xs
  end.

Lemma Z_one_bits_powerserie:
  forall n x, 0 <= x < two_power_nat n -> x = powerserie (Z_one_bits n x 0).
Proof.
  assert (forall n x i,
    0 <= i ->
    0 <= x < two_power_nat n ->
    x * two_p i = powerserie (Z_one_bits n x i)).
  {
  induction n; intros.
  simpl. rewrite two_power_nat_O in H0.
  assert (x = 0) by lia. subst x. lia.
  rewrite two_power_nat_S in H0. simpl Z_one_bits.
  rewrite (Zdecomp x) in H0. rewrite Zshiftin_spec in H0.
  assert (EQ: Z.div2 x * two_p (i + 1) = powerserie (Z_one_bits n (Z.div2 x) (i + 1))).
    apply IHn. lia.
    destruct (Z.odd x); lia.
  rewrite two_p_is_exp in EQ. change (two_p 1) with 2 in EQ.
  rewrite (Zdecomp x) at 1. rewrite Zshiftin_spec.
  destruct (Z.odd x); simpl powerserie; rewrite <- EQ; ring.
  lia. lia.
  }
  intros. rewrite <- H. change (two_p 0) with 1. lia.
  lia. exact H0.
Qed.

Lemma Z_one_bits_range:
  forall n x i, In i (Z_one_bits n x 0) -> 0 <= i < Z.of_nat n.
Proof.
  assert (forall n x i j,
    In j (Z_one_bits n x i) -> i <= j < i + Z.of_nat n).
  {
  induction n; simpl In.
  tauto.
  intros x i j. rewrite Nat2Z.inj_succ.
  assert (In j (Z_one_bits n (Z.div2 x) (i + 1)) -> i <= j < i + Z.succ (Z.of_nat n)).
    intros. exploit IHn; eauto. lia.
  destruct (Z.odd x); simpl.
  intros [A|B]. subst j. lia. auto.
  auto.
  }
  intros. generalize (H n x 0 i H0). lia.
Qed.

Remark Z_one_bits_zero:
  forall n i, Z_one_bits n 0 i = nil.
Proof.
  induction n; intros; simpl; auto.
Qed.

Remark Z_one_bits_two_p:
  forall n x i,
  0 <= x < Z.of_nat n ->
  Z_one_bits n (two_p x) i = (i + x) :: nil.
Proof.
  induction n; intros; simpl. simpl in H. extlia.
  rewrite Nat2Z.inj_succ in H.
  assert (x = 0 \/ 0 < x) by lia. destruct H0.
  subst x; simpl. decEq. lia. apply Z_one_bits_zero.
  assert (Z.odd (two_p x) = false /\ Z.div2 (two_p x) = two_p (x-1)).
    apply Zshiftin_inj. rewrite <- Zdecomp. rewrite !Zshiftin_spec.
    rewrite <- two_p_S. rewrite Z.add_0_r. f_equal; lia. lia.
  destruct H1 as [A B]; rewrite A; rewrite B.
  rewrite IHn. f_equal; lia. lia.
Qed.

(** ** Recognition of powers of two *)

Fixpoint P_is_power2 (p: positive) : bool :=
  match p with
  | xH => true
  | xO q => P_is_power2 q
  | xI q => false
  end.

Definition Z_is_power2 (x: Z) : option Z :=
  match x with
  | Z0 => None
  | Zpos p => if P_is_power2 p then Some (Z.log2 x) else None
  | Zneg _ => None
  end.

Remark P_is_power2_sound:
  forall p, P_is_power2 p = true -> Z.pos p = two_p (Z.log2 (Z.pos p)).
Proof.
  induction p; simpl P_is_power2; intros.
- discriminate.
- change (Z.pos p~0) with (2 * Z.pos p).  apply IHp in H.
  rewrite Z.log2_double by extlia. rewrite two_p_S.  congruence.
  apply Z.log2_nonneg.
- reflexivity.
Qed.

Lemma Z_is_power2_nonneg:
  forall x i, Z_is_power2 x = Some i -> 0 <= i.
Proof.
  unfold Z_is_power2; intros. destruct x; try discriminate.
  destruct (P_is_power2 p) eqn:P; try discriminate.
  replace i with (Z.log2 (Z.pos p)) by congruence. apply Z.log2_nonneg.
Qed.
 
Lemma Z_is_power2_sound:
  forall x i, Z_is_power2 x = Some i -> x = two_p i /\ i = Z.log2 x.
Proof.
  unfold Z_is_power2; intros. destruct x; try discriminate.
  destruct (P_is_power2 p) eqn:P; try discriminate.
  apply P_is_power2_sound in P. rewrite P; split; congruence.
Qed.

Corollary Z_is_power2_range:
  forall n x i,
  0 <= n -> 0 <= x < two_p n -> Z_is_power2 x = Some i -> 0 <= i < n.
Proof.
  intros.
  assert (x <> 0) by (red; intros; subst x; discriminate).
  apply Z_is_power2_sound in H1. destruct H1 as [P Q]. subst i.
  split. apply Z.log2_nonneg. apply Z.log2_lt_pow2. lia. rewrite <- two_p_equiv; tauto.
Qed.

Lemma Z_is_power2_complete:
  forall i, 0 <= i -> Z_is_power2 (two_p i) = Some i.
Proof.
Opaque Z.log2.
  assert (A: forall x i, Z_is_power2 x = Some i -> Z_is_power2 (2 * x) = Some (Z.succ i)).
  { destruct x; simpl; intros; try discriminate.
    change (2 * Z.pos p) with (Z.pos (xO p)); simpl.
    destruct (P_is_power2 p); inv H. rewrite <- Z.log2_double by extlia. auto.
  }
  induction i using Znatlike_ind; intros.
- replace i with 0 by lia. reflexivity.
- rewrite two_p_S by lia. apply A. apply IHi; lia.
Qed.

Definition Z_is_power2m1 (x: Z) : option Z := Z_is_power2 (Z.succ x).

Lemma Z_is_power2m1_nonneg:
  forall x i, Z_is_power2m1 x = Some i -> 0 <= i.
Proof.
  unfold Z_is_power2m1; intros. eapply Z_is_power2_nonneg; eauto.
Qed.

Lemma Z_is_power2m1_sound:
  forall x i, Z_is_power2m1 x = Some i -> x = two_p i - 1.
Proof.
  unfold Z_is_power2m1; intros. apply Z_is_power2_sound in H. lia.
Qed.

Lemma Z_is_power2m1_complete:
  forall i, 0 <= i -> Z_is_power2m1 (two_p i - 1) = Some i.
Proof.
  intros. unfold Z_is_power2m1. replace (Z.succ (two_p i - 1)) with (two_p i) by lia.
  apply Z_is_power2_complete; auto.
Qed.

Lemma Z_is_power2m1_range:
  forall n x i,
  0 <= n -> 0 <= x < two_p n -> Z_is_power2m1 x = Some i -> 0 <= i <= n.
Proof.
  intros. destruct (zeq x (two_p n - 1)).
- subst x. rewrite Z_is_power2m1_complete in H1 by auto. inv H1; lia.
- unfold Z_is_power2m1 in H1. apply (Z_is_power2_range n (Z.succ x) i) in H1; lia.
Qed.

(** ** Relation between bitwise operations and multiplications / divisions by powers of 2 *)

(** Left shifts and multiplications by powers of 2. *)

Lemma Zshiftl_mul_two_p:
  forall x n, 0 <= n -> Z.shiftl x n = x * two_p n.
Proof.
  intros. destruct n; simpl.
  - lia.
  - pattern p. apply Pos.peano_ind.
    + change (two_power_pos 1) with 2. simpl. ring.
    + intros. rewrite Pos.iter_succ. rewrite H0.
      rewrite Pplus_one_succ_l. rewrite two_power_pos_is_exp.
      change (two_power_pos 1) with 2. ring.
  - compute in H. congruence.
Qed.

(** Right shifts and divisions by powers of 2. *)

Lemma Zshiftr_div_two_p:
  forall x n, 0 <= n -> Z.shiftr x n = x / two_p n.
Proof.
  intros. destruct n; unfold Z.shiftr; simpl.
  - rewrite Zdiv_1_r. auto.
  - pattern p. apply Pos.peano_ind.
    + change (two_power_pos 1) with 2. simpl. apply Zdiv2_div.
    + intros. rewrite Pos.iter_succ. rewrite H0.
      rewrite Pplus_one_succ_l. rewrite two_power_pos_is_exp.
      change (two_power_pos 1) with 2.
      rewrite Zdiv2_div. rewrite Z.mul_comm. apply Zdiv_Zdiv.
      rewrite two_power_pos_nat. apply two_power_nat_pos. lia.
  - compute in H. congruence.
Qed.

(** ** Properties of [shrx] (signed division by a power of 2) *)

Lemma Zquot_Zdiv:
  forall x y,
  y > 0 ->
  Z.quot x y = if zlt x 0 then (x + y - 1) / y else x / y.
Proof.
  intros. destruct (zlt x 0).
  - symmetry. apply Zquot_unique_full with ((x + y - 1) mod y - (y - 1)).
     + red. right; split. lia.
       exploit (Z_mod_lt (x + y - 1) y); auto.
       rewrite Z.abs_eq. lia. lia.
     + transitivity ((y * ((x + y - 1) / y) + (x + y - 1) mod y) - (y-1)).
       rewrite <- Z_div_mod_eq. ring. auto. ring.
  - apply Zquot_Zdiv_pos; lia.
Qed.

Lemma Zdiv_shift:
  forall x y, y > 0 ->
  (x + (y - 1)) / y = x / y + if zeq (Z.modulo x y) 0 then 0 else 1.
Proof.
  intros. generalize (Z_div_mod_eq x y H). generalize (Z_mod_lt x y H).
  set (q := x / y). set (r := x mod y). intros.
  destruct (zeq r 0).
  apply Zdiv_unique with (y - 1). rewrite H1. rewrite e. ring. lia.
  apply Zdiv_unique with (r - 1). rewrite H1. ring. lia.
Qed.

(** ** Size of integers, in bits. *)

Definition Zsize (x: Z) : Z :=
  match x with
  | Zpos p => Zpos (Pos.size p)
  | _ => 0
  end.

Remark Zsize_pos: forall x, 0 <= Zsize x.
Proof.
  destruct x; simpl. lia. compute; intuition congruence. lia.
Qed.

Remark Zsize_pos': forall x, 0 < x -> 0 < Zsize x.
Proof.
  destruct x; simpl; intros; try discriminate. compute; auto.
Qed.

Lemma Zsize_shiftin:
  forall b x, 0 < x -> Zsize (Zshiftin b x) = Z.succ (Zsize x).
Proof.
  intros. destruct x; compute in H; try discriminate.
  destruct b.
  change (Zshiftin true (Zpos p)) with (Zpos (p~1)).
  simpl. f_equal. rewrite Pos.add_1_r; auto.
  change (Zshiftin false (Zpos p)) with (Zpos (p~0)).
  simpl. f_equal. rewrite Pos.add_1_r; auto.
Qed.

Lemma Ztestbit_size_1:
  forall x, 0 < x -> Z.testbit x (Z.pred (Zsize x)) = true.
Proof.
  intros x0 POS0; pattern x0; apply Zshiftin_pos_ind; auto.
  intros. rewrite Zsize_shiftin; auto.
  replace (Z.pred (Z.succ (Zsize x))) with (Z.succ (Z.pred (Zsize x))) by lia.
  rewrite Ztestbit_shiftin_succ. auto. generalize (Zsize_pos' x H); lia.
Qed.

Lemma Ztestbit_size_2:
  forall x, 0 <= x -> forall i, i >= Zsize x -> Z.testbit x i = false.
Proof.
  intros x0 POS0. destruct (zeq x0 0).
  - subst x0; intros. apply Ztestbit_0.
  - pattern x0; apply Zshiftin_pos_ind.
    + simpl. intros. change 1 with (Zshiftin true 0). rewrite Ztestbit_shiftin.
      rewrite zeq_false. apply Ztestbit_0. lia. lia.
    + intros. rewrite Zsize_shiftin in H1; auto.
      generalize (Zsize_pos' _ H); intros.
      rewrite Ztestbit_shiftin. rewrite zeq_false. apply H0. lia.
      lia. lia.
    + lia.
Qed.

Lemma Zsize_interval_1:
  forall x, 0 <= x -> 0 <= x < two_p (Zsize x).
Proof.
  intros.
  assert (x = x mod (two_p (Zsize x))).
    apply equal_same_bits; intros.
    rewrite Ztestbit_mod_two_p; auto.
    destruct (zlt i (Zsize x)). auto. apply Ztestbit_size_2; auto.
    apply Zsize_pos; auto.
  rewrite H0 at 1. rewrite H0 at 3. apply Z_mod_lt. apply two_p_gt_ZERO. apply Zsize_pos; auto.
Qed.

Lemma Zsize_interval_2:
  forall x n, 0 <= n -> 0 <= x < two_p n -> n >= Zsize x.
Proof.
  intros. set (N := Z.to_nat n).
  assert (Z.of_nat N = n) by (apply Z2Nat.id; auto).
  rewrite <- H1 in H0. rewrite <- two_power_nat_two_p in H0.
  destruct (zeq x 0).
  subst x; simpl; lia.
  destruct (zlt n (Zsize x)); auto.
  exploit (Ztestbit_above N x (Z.pred (Zsize x))). auto. lia.
  rewrite Ztestbit_size_1. congruence. lia.
Qed.

Lemma Zsize_monotone:
  forall x y, 0 <= x <= y -> Zsize x <= Zsize y.
Proof.
  intros. apply Z.ge_le. apply Zsize_interval_2. apply Zsize_pos.
  exploit (Zsize_interval_1 y). lia.
  lia.
Qed.

(** ** Bit insertion, bit extraction *)

(** Extract and optionally sign-extend bits [from...from+len-1] of [x] *)
Definition Zextract_u (x: Z) (from: Z) (len: Z) : Z :=
  Zzero_ext len (Z.shiftr x from).

Definition Zextract_s (x: Z) (from: Z) (len: Z) : Z :=
  Zsign_ext len (Z.shiftr x from).

Lemma Zextract_u_spec:
  forall x from len i,
  0 <= from -> 0 <= len -> 0 <= i ->
  Z.testbit (Zextract_u x from len) i =
  if zlt i len then Z.testbit x (from + i) else false.
Proof.
  unfold Zextract_u; intros. rewrite Zzero_ext_spec, Z.shiftr_spec by auto.
  rewrite Z.add_comm. auto.
Qed.

Lemma Zextract_s_spec:
  forall x from len i,
  0 <= from -> 0 < len -> 0 <= i ->
  Z.testbit (Zextract_s x from len) i =
  Z.testbit x (from + (if zlt i len then i else len - 1)).
Proof.
  unfold Zextract_s; intros. rewrite Zsign_ext_spec by auto. rewrite Z.shiftr_spec.
  rewrite Z.add_comm. auto.
  destruct (zlt i len); lia.
Qed.

(** Insert bits [0...len-1] of [y] into bits [to...to+len-1] of [x] *)

Definition Zinsert (x y: Z) (to: Z) (len: Z) : Z :=
  let mask := Z.shiftl (two_p len - 1) to in
  Z.lor (Z.land (Z.shiftl y to) mask) (Z.ldiff x mask).

Lemma Zinsert_spec:
  forall x y to len i,
  0 <= to -> 0 <= len -> 0 <= i ->
  Z.testbit (Zinsert x y to len) i =
    if zle to i && zlt i (to + len)
    then Z.testbit y (i - to)
    else Z.testbit x i.
Proof.
  unfold Zinsert; intros. set (mask := two_p len - 1).
  assert (M: forall j, 0 <= j -> Z.testbit mask j = if zlt j len then true else false).
  { intros; apply Ztestbit_two_p_m1; auto. }
  rewrite Z.lor_spec, Z.land_spec, Z.ldiff_spec by auto. 
  destruct (zle to i).
- rewrite ! Z.shiftl_spec by auto. rewrite ! M by lia. 
  unfold proj_sumbool; destruct (zlt (i - to) len); simpl;
  rewrite andb_true_r, andb_false_r.
+ rewrite zlt_true by lia. apply orb_false_r.
+ rewrite zlt_false by lia; auto.
- rewrite ! Z.shiftl_spec_low by lia. simpl. apply andb_true_r.
Qed.
