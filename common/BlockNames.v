Require Import DecidableClass.
Require Import Coqlib.
Require Import AST.
Require Import Maps.
Require Import String.

Axiom ident_to_string: ident -> string.
Axiom pos_to_string: positive -> string.

(** * Interface *)

(** This is the interface of the memory block namespace. There should
  be an embedding [glob] of global identifiers into the type of memory
  blocks (which can be inverted with the [ident_of] operation).
  It should also be possible to dynamically allocate block names,
  starting with [init], then by applying [succ] whenever a new block
  name is needed.

  The space of block names must be equipped with a total order
  ([le], [lt]), such that global blocks are considered smaller than
  dynamically allocated blocks, and that dynamic blocks are allocated
  in increasing order.

  Finally, it should be possible to print out a string representation
  for each block name ([to_string]), and there should be an injective
  mapping into [positive], so that we can use an efficient [IMap]
  implementation for block-indexed finite maps. *)

Module Type BlockType <: INDEXED_TYPE.
  Parameter t : Type.
  Parameter eq : forall b1 b2 : t, {b1 = b2} + {b1 <> b2}.

  Parameter glob : ident -> t.  (* block associated to a global identifier *)
  Parameter init : t.           (* initial dynamic block id *)
  Parameter succ : t -> t.
  Parameter ident_of: t -> option ident.
  Parameter to_string: t -> string.

  Parameter lt : t -> t -> Prop.
  Parameter le : t -> t -> Prop.
  Parameter lt_dec : forall b1 b2, {lt b1 b2} + {~ lt b1 b2}.

  Axiom lt_glob_init : forall i, lt (glob i) init.
  Axiom lt_succ : forall b, lt b (succ b).
  Axiom lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Axiom lt_strict : forall b, ~ lt b b.
  Axiom lt_succ_inv: forall x y, lt x (succ y) -> lt x y \/ x = y.
  Axiom lt_le: forall x y, lt x y -> le x y.
  Axiom nlt_le: forall x y, ~ lt y x -> le x y.
  Axiom le_refl: forall b, le b b.
  Axiom le_trans: forall x y z, le x y -> le y z -> le x z.
  Axiom lt_le_trans: forall x y z, lt x y -> le y z -> lt x z.
  Axiom le_lt_trans: forall x y z, le x y -> lt y z -> lt x z.

  Axiom glob_inj: forall i j, glob i = glob j -> i = j.

  Axiom ident_of_glob: forall i, ident_of (glob i) = Some i.
  Axiom ident_of_inv: forall b i, ident_of b = Some i -> b = glob i.

  Parameter index: t -> positive.
  Axiom index_inj: forall (x y: t), index x = index y -> x = y.
End BlockType.

(** * Implementation *)

(** Block names are implemented as the disjoint union of [AST.ident]
  and dynamically allocated [positive]. *)

Module Block : BlockType.
  Inductive t_def :=
    | glob_def : ident -> t_def
    | dyn : positive -> t_def.

  Definition t := t_def.

  Definition eq (b1 b2 : t):
    {b1 = b2} + {b1 <> b2}.
  Proof.
    decide equality.
    apply peq.
    apply peq.
  Defined.

  Definition glob := glob_def.
  Definition init := dyn 1%positive.

  Definition succ (b: t) :=
    match b with
      | glob_def i => glob (Pos.succ i)
      | dyn n => dyn (Pos.succ n)
    end.

  Inductive lt_def : t -> t -> Prop :=
    | glob_dyn_lt i n:
        lt_def (glob i) (dyn n)
    | glob_lt m n:
        Pos.lt m n ->
        lt_def (glob m) (glob n)
    | dyn_lt m n:
        Pos.lt m n ->
        lt_def (dyn m) (dyn n).

  Definition lt := lt_def.

  Definition le b1 b2 :=
    lt b1 b2 \/ b1 = b2.

  Definition lt_dec b1 b2:
    {lt b1 b2} + {~ lt b1 b2}.
  Proof.
    destruct b1 as [i1|n1], b2 as [i2|n2].
    - destruct (plt i1 i2).
      + left. abstract (constructor; eauto).
      + right. abstract (inversion 1; eauto).
    - left. abstract constructor.
    - right. abstract (inversion 1).
    - destruct (plt n1 n2).
      + left. abstract (constructor; eauto).
      + right. abstract (inversion 1; eauto).
  Defined.

  Lemma lt_glob_init i:
    lt (glob i) init.
  Proof.
    constructor.
  Qed.

  Lemma lt_succ b:
    lt b (succ b).
  Proof.
    destruct b; constructor; xomega.
  Qed.

  Lemma lt_trans x y z:
    lt x y -> lt y z -> lt x z.
  Proof.
    intros Hxy Hyz.
    destruct Hyz; inv Hxy; constructor; xomega.
  Qed.

  Lemma lt_strict b:
    ~ lt b b.
  Proof.
    inversion 1; eapply Plt_strict; eauto.
  Qed.

  Lemma lt_succ_inv x y:
    lt x (succ y) -> lt x y \/ x = y.
  Proof.
    destruct y; simpl; inversion 1; subst.
    - destruct (Plt_succ_inv m i) as [H1|H1]; auto.
      left; constructor; auto.
      right; subst; reflexivity.
    - left; constructor.
    - destruct (Plt_succ_inv m p) as [H1|H1]; auto.
      left; constructor; auto.
      right; subst; reflexivity.
  Qed.

  Lemma lt_le x y:
    lt x y -> le x y.
  Proof.
    firstorder.
  Qed.

  Lemma nlt_le x y:
    ~ lt y x -> le x y.
  Proof.
    unfold le.
    destruct x as [i1|n1], y as [i2|n2].
    - destruct (peq i1 i2).
      + right. congruence.
      + left. constructor.
        destruct (plt i1 i2); auto. elim H; constructor; xomega.
    - left. constructor.
    - intro. elim H. constructor.
    - destruct (peq n1 n2).
      + right. congruence.
      + left. constructor.
        destruct (plt n1 n2); auto. elim H; constructor; xomega.
  Qed.

  Lemma le_refl b:
    le b b.
  Proof.
    firstorder.
  Qed.

  Lemma le_trans x y z:
    le x y -> le y z -> le x z.
  Proof.
    unfold le. intros H1 H2.
    destruct H1; try congruence. left.
    destruct H2; try congruence. eauto using lt_trans.
  Qed.

  Lemma lt_le_trans x y z:
    lt x y -> le y z -> lt x z.
  Proof.
    intros Hxy Hyz.
    destruct Hyz; try congruence.
    eapply lt_trans; eauto.
  Qed.

  Lemma le_lt_trans x y z:
    le x y -> lt y z -> lt x z.
  Proof.
    intros Hxy Hyz.
    destruct Hxy; try congruence.
    eapply lt_trans; eauto.
  Qed.

  Definition ident_of b :=
    match b with
      glob_def i => Some i
    | dyn i => None
    end.

  Definition to_string (b: t): string :=
    match b with
    | glob_def i => append "glob:" (ident_to_string i)
    | dyn b => append "dyn:" (pos_to_string b)
    end.

  Lemma ident_of_glob i:
    ident_of (glob i) = Some i.
  Proof.
    reflexivity.
  Qed.

  Lemma ident_of_inv b i:
    ident_of b = Some i -> b = glob i.
  Proof.
    unfold ident_of. destruct b; inversion 1; reflexivity.
  Qed.

  Lemma glob_inj i j:
    glob i = glob j -> i = j.
  Proof.
    inversion 1; auto.
  Qed.

  Definition index (b: t): positive :=
    match b with
    | glob_def i => i~0
    | dyn p => p~1
    end.

  Lemma index_inj (x y: t):
    index x = index y -> x = y.
  Proof.
    destruct x, y; inversion 1; simpl in *; congruence.
  Qed.
End Block.

Module BMap : MAP
    with Definition elt := Block.t
    with Definition elt_eq := Block.eq :=
  IMap Block.

(** * Complements *)

(** ** Properties *)

Lemma Blt_trans_succ b1 b2:
  Block.lt b1 b2 -> Block.lt b1 (Block.succ b2).
Proof.
  intros H.
  eapply Block.lt_trans; eauto.
  apply Block.lt_succ.
Qed.

Lemma Blt_ne x y:
  Block.lt x y -> x <> y.
Proof.
  intros LT EQ; subst; apply Block.lt_strict in LT; auto.
Qed.

(** ** Derived definitions *)

Program Instance Decidable_eq_block (x y: Block.t): Decidable (x = y) :=
  {
    Decidable_witness := if Block.eq x y then true else false;
  }.
Next Obligation.
  destruct Block.eq; firstorder.
Qed.

Definition block_compare (b1 b2: Block.t) :=
  if Block.lt_dec b1 b2
  then (-1)%Z
  else if Block.eq b1 b2
       then 0%Z
       else 1%Z.

(** ** Tactics *)

(** This tactic is used to discharge inequalities involving block names. *)

Hint Resolve
  Block.lt_le_trans
  Block.le_lt_trans
  Block.le_trans
  Block.lt_le
  Blt_ne
  Block.le_refl
  Block.lt_succ
  : blocknames.

Ltac blomega := eauto with blocknames.
