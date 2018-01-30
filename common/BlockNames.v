Require Import Coqlib.
Require Import AST.
Require Import Maps.

(** * Interfaces *)

Module Type BlockType <: EQUALITY_TYPE.
  Parameter t : Type.
  Parameter eq : forall b1 b2 : t, {b1 = b2} + {b1 <> b2}.

  Parameter glob : ident -> t.  (* block associated to a global identifier *)
  Parameter init : t.           (* initial dynamic block id *)
  Parameter succ : t -> t.

  Parameter lt : t -> t -> Prop.
  Parameter lt_dec : forall b1 b2, {lt b1 b2} + {~ lt b1 b2}.

  Axiom lt_glob_init : forall i, lt (glob i) init.
  Axiom lt_succ : forall b, lt b (succ b).
  Axiom lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Axiom lt_strict : forall b, ~ lt b b.
  Axiom lt_succ_inv: forall x y, lt x (succ y) -> lt x y \/ x = y.
End BlockType.

Module Type BMapType (M: BlockType).
  Definition elt := M.t.
  Definition elt_eq := M.eq.
  Parameter t: Type -> Type.
  Parameter init: forall {A}, A -> t A.
  Parameter get: forall {A}, elt -> t A -> A.
  Parameter set: forall {A}, elt -> A -> t A -> t A.
  Axiom gi: forall {A} i (x: A), get i (init x) = x.
  Axiom gss: forall {A} i (x: A) m, get i (set i x m) = x.
  Axiom gso: forall {A} i j (x: A) m, i <> j -> get i (set j x m) = get i m.
  Axiom gsspec:
    forall {A} i j (x: A) m, get i (set j x m) = (if elt_eq i j then x else get i m).
  Axiom gsident:
    forall {A} i j (m: t A), get j (set i (get i m) m) = get j m.
  Parameter map: forall {A B}, (A -> B) -> t A -> t B.
  Axiom gmap:
    forall {A B} (f: A -> B) i m, get i (map f m) = f (get i m).
  Axiom set2:
    forall {A} i (x y: A) m, set i y (set i x m) = set i y m.
End BMapType.

(** * Implementation *)

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
End Block.

Module BMap : BMapType Block := EMap Block.

(** * Properties *)

Lemma Blt_trans_succ b1 b2:
  Block.lt b1 b2 -> Block.lt b1 (Block.succ b2).
Proof.
  intros H.
  eapply Block.lt_trans; eauto.
  apply Block.lt_succ.
Qed.
