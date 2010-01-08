Require Import Arith.
Require Import ZArith.

(* Definition of some facts other arith, for the termination order...
   many uninteresting but necessary lemmas *)

Fixpoint puissance_aux x y res {struct y} : nat :=
match y with
| 0 => res
| S n => puissance_aux x n (x*res)
end.

Definition puissance x y := puissance_aux x y 1.

Lemma dec_base_aux : forall a b c d x,
0 < a ->
a + b +c +d < x ->
a*puissance x 3 + b*puissance x 2 + 
c*x + d > 0.

Proof.
intros a b c d x Ha H.
induction a.
inversion Ha.
unfold puissance;simpl;destruct x.
inversion H.
apply lt_le_trans with (m:=S x * (S x * (S x *1))).
rewrite mult_1_r.
case_eq (S x * (S x * S x)).
intro H0.
inversion H0.
intros n H0.
intuition.
intuition.
Qed.

Lemma inf_diff : forall x y,
x - y > 0 -> x > y.

Proof.
intuition.
Qed.

Lemma plop : forall x y,
y > 0 ->
x <= x*y.

Proof.
induction y;intros.
inversion H.
rewrite mult_succ_r.
intuition.
Qed.

Lemma mult_zero : forall x y,
x*y = 0 -> x = 0 \/ y = 0.

Proof.
intros.
induction x.
left;reflexivity.
induction y.
right;reflexivity.
inversion H.
Qed.

Lemma mult_plop : forall x y z,
x > 0 ->
y < z ->
y*x < z*x.

Proof.
intros x y z H H0.
induction x.
inversion H.
destruct (lt_eq_lt_dec x 0).
destruct s.
inversion l.
do 2 rewrite mult_succ_r.
rewrite e.
do 2 rewrite mult_0_r.
intuition.
generalize (IHx l).
do 2 rewrite mult_succ_r.
intuition.
Qed.

Lemma mult_plop_eq : forall x y z,
x > 0 ->
y <= z ->
y*x <= z*x.

Proof.
intros x y z H H0.
induction x.
inversion H.
destruct (lt_eq_lt_dec x 0).
destruct s.
inversion l.
do 2 rewrite mult_succ_r.
rewrite e.
do 2 rewrite mult_0_r.
intuition.
generalize (IHx l).
do 2 rewrite mult_succ_r.
intuition.
Qed.

Lemma mult_plop_eq2 : forall x y z,
x > 0 ->
y <= z ->
x*y <= x*z.

Proof.
intros x y z H H0.
induction x.
inversion H.
destruct (lt_eq_lt_dec x 0).
destruct s.
inversion l.
do 2 rewrite mult_succ_l.
rewrite e.
do 2 rewrite mult_0_l.
intuition.
generalize (IHx l).
do 2 rewrite mult_succ_l.
intuition.
Qed.

Lemma add_inf : forall x y z,
x <= y -> z+x <= z+y.

Proof.
intuition.
Qed.

Lemma add_hd_eq : forall x y z,
x = y -> z+x = z+y.

Proof.
auto.
Qed.

Lemma add_hd_inf : forall x y z,
x < y -> z+x < z + y.

Proof.
intuition.
Qed.

Lemma dec_base : forall a b c d a' b' c' d' x,
a + b + c + d < x -> x > 0 ->
(a < a' ->
(a *puissance x 3 +b *puissance x 2 + c *x + d < 
  a' *puissance x 3 +b' *puissance x 2 + c' *x + d')).

Proof.
intros a b c d a' b' c' d' x H H0 H1.
unfold puissance;simpl.
rewrite mult_1_r.
apply lt_le_trans with (m := (S a)*x*x*x).
rewrite mult_succ_l.
do 2 rewrite mult_plus_distr_r.
replace (a*(x*(x*x))+b*(x*x)+c*x+d) with (a*x*x*x+(b*x*x+c*x+d)).
apply add_hd_inf.
assert (c*x <= c*x*x).
apply plop.
assumption.
assert (d <= d*x*x).
apply le_trans with (m := d*x).
apply plop.
assumption.
apply plop.
assumption.
apply le_lt_trans with (b*x*x+c*x*x+d*x*x).
intuition.
replace (b*x*x+c*x*x+d*x*x) with ((b+c+d)*x*x).
apply mult_plop.
assumption.
apply mult_plop.
assumption.
intuition.
do 4 rewrite mult_plus_distr_r.
reflexivity.
do 2 rewrite plus_assoc.
replace (a*(x* (x*x))) with (a*x*x*x).
replace (b*(x*x)) with (b*x*x).
reflexivity.
intuition.
replace (x*(x*x)) with (x*x*x).
rewrite mult_assoc.
intuition.
intuition.
apply le_trans with (m := a'*(x*(x*x))).
do 2 rewrite mult_assoc.
intuition.
apply mult_plop_eq.
assumption.
apply mult_plop_eq.
assumption.
apply mult_plop_eq.
assumption.
assumption.
intuition.
Qed.

Lemma dec_base2 : forall a b c a' b' c' x,
a + b + c < x -> x > 0 ->
(a < a' ->
(a *puissance x 2 +b *x+ c < 
  a' *puissance x 2 +b' *x + c')).

Proof.
intros a b c a' b' c' x H H0 H1.
unfold puissance;simpl.
rewrite mult_1_r.
apply lt_le_trans with (m := S a*x*x).
rewrite mult_succ_l.
rewrite mult_plus_distr_r.
rewrite mult_assoc.
rewrite <-plus_assoc.
apply add_hd_inf.
assert (c <= c*x).
apply plop.
assumption.
apply le_lt_trans with (m := b*x+c*x).
intuition.
replace (b*x+c*x) with ((b+c)*x).
apply mult_plop.
assumption.
intuition.
intuition.
apply le_trans with (m := a'*x*x).
apply mult_plop_eq.
assumption.
apply mult_plop_eq.
assumption.
intuition.
rewrite mult_assoc.
intuition.
Qed.

Lemma dec_base3 : forall a b a' b' x,
a + b < x -> x > 0 -> a < a' 
-> (a *x +b <   a' *x + b').

Proof.
intros a b a' b' x H H0 H1.
apply lt_le_trans with (m := S a*x).
rewrite mult_succ_l.
intuition.
assert (S a <= a').
intuition.
apply le_trans with (m:= a'*x).
apply mult_plop_eq;assumption.
intuition.
Qed.

Lemma puiss_aux : forall x y n,
puissance_aux x y n = n*puissance x y.

Proof.
unfold puissance;induction y;simpl.
intuition.
intro n.
rewrite mult_1_r.
rewrite (IHy x).
rewrite (IHy (x*n)).
rewrite mult_assoc.
rewrite (mult_comm x n).
reflexivity.
Qed.

Lemma puiss_step : forall x n,
puissance x (S n) = x*puissance x n.

Proof.
intros.
unfold puissance;simpl.
rewrite puiss_aux;simpl.
intuition.
Qed.

Lemma pos_puiss : forall x y,
x > 0 -> puissance x y > 0.

Proof.
induction y;intros.
unfold puissance;simpl.
intuition.
rewrite puiss_step.
generalize (IHy H);intro H0.
case_eq (x*puissance x y);intros.
generalize (mult_zero _ _ H1);intros.
destruct H2;intuition.
intuition.
Qed.

Lemma incr_puis : forall x y n,
x <= y ->
puissance x n <= puissance y n.

Proof.
induction n;intros;simpl.
intuition.
do 2 rewrite puiss_step.
destruct x.
intuition.
destruct y.
inversion H.
apply le_trans with (m := S x*puissance (S y) n).
apply mult_plop_eq2.
intuition.
apply (IHn H).
apply mult_plop_eq.
apply pos_puiss.
intuition.
assumption.
Qed.

Lemma incr_puis2 : forall x n p,
n <= p ->
x > 0 ->
puissance x n <= puissance x p.

Proof.
induction n;intros.
unfold puissance;simpl.
fold (puissance x p).
generalize (pos_puiss).
intuition.
unfold puissance;simpl.
rewrite mult_1_r.
do 2 rewrite puiss_aux.
rewrite mult_1_l.
generalize (IHn (p-1));intro.
assert (puissance x n <= puissance x (p-1)).
apply H1.
intuition.
assumption.
destruct p.
inversion H.
rewrite puiss_step.
apply mult_plop_eq2.
assumption.
apply IHn.
intuition.
assumption.
Qed.