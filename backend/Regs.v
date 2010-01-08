Require Import Registers.


Definition op_plus (x y : option N) : option N :=
match (x,y) with
|(None,None) => None
|(Some a,Some b) => Some (Nplus a b)
|(Some a,None) => Some a
|(None,Some b) => Some b
end.

Module Regs <: OrderedType.

(* Definition of registers as Pseudo-registers or machine registers *)

Inductive registers : Type :=
|P : reg -> registers
|M : mreg -> registers.

Definition t := registers.

Definition reg_to_Reg := fun r => P r.
Definition mreg_to_Reg := fun r => M r.

Inductive req : t -> t -> Prop :=
|Peq : forall x y, eq x y -> req (P x) (P y)
|Meq : forall x y, eq x y -> req (M x) (M y).

Definition eq := req.

Inductive rlt : t -> t -> Prop :=
|Plt : forall x y, OrderedReg.lt x y -> rlt (P x) (P y)
|Mlt : forall x y, OrderedMreg.lt x y -> rlt (M x) (M y)
|PMlt : forall x y, rlt (M x) (P y).

Definition lt := rlt.

Lemma eq_refl : forall x, eq x x.

Proof.
induction x;constructor;reflexivity.
Qed.

Lemma eq_sym : forall x y, eq x y -> eq y x.

Proof.
induction 1;rewrite H;apply eq_refl.
Qed.

Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.

Proof.
intros x y z H H0.
inversion H;inversion H0;subst.
rewrite H5;apply eq_refl.
inversion H5.
inversion H5.
rewrite H5;apply eq_refl.
Qed.

Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.

Proof.
intros x y z H H0.
inversion H;inversion H0;subst.
inversion H5;subst.
constructor. apply (OrderedReg.lt_trans H1 H4).
inversion H5.
inversion H4.
inversion H5.
inversion H5;subst.
constructor. apply (OrderedMreg.lt_trans _ _ _ H1 H4).
constructor.
constructor.
inversion H4.
constructor.
Qed.

Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.

Proof.
induction 1;intro H0;inversion H0.
elim (OrderedReg.lt_not_eq H H3).
elim (OrderedMreg.lt_not_eq _ _ H H3).
Qed.

Lemma compare : forall x y, Compare lt eq x y.

Proof.
intros x y. 
destruct x;destruct y.
destruct (OrderedReg.compare r r0).
apply LT. constructor. assumption.
apply EQ. constructor. assumption.
apply GT. constructor. assumption.
apply GT. constructor.
apply LT. constructor.
destruct (OrderedMreg.compare m m0).
apply LT. constructor. assumption.
apply EQ. constructor. assumption.
apply GT. constructor. assumption.
Qed.

Lemma eq_dec : forall x y, {eq x y}+{~eq x y}.

Proof.
intros x y.
destruct (compare x y).
right. apply lt_not_eq. assumption.
left. assumption.
right. (cut (~ eq y x)).
intros H H0. elim H. apply eq_sym. assumption.
apply lt_not_eq. assumption.
Qed.

Definition get_type x env :=
match x with
| P y => env y
| M y => mreg_type y
end.

End Regs.