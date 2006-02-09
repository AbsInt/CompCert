(** Constructions of semi-lattices. *)

Require Import Coqlib.
Require Import Maps.

(** * Signatures of semi-lattices *)

(** A semi-lattice is a type [t] equipped with a decidable equality [eq],
  a partial order [ge], a smallest element [bot], and an upper
  bound operation [lub].  Note that we do not demand that [lub] computes
  the least upper bound. *)

Module Type SEMILATTICE.

  Variable t: Set.
  Variable eq: forall (x y: t), {x=y} + {x<>y}.
  Variable ge: t -> t -> Prop.
  Hypothesis ge_refl: forall x, ge x x.
  Hypothesis ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Variable bot: t.
  Hypothesis ge_bot: forall x, ge x bot.
  Variable lub: t -> t -> t.
  Hypothesis lub_commut: forall x y, lub x y = lub y x.
  Hypothesis ge_lub_left: forall x y, ge (lub x y) x.

End SEMILATTICE.

(** A semi-lattice ``with top'' is similar, but also has a greatest
  element [top]. *)

Module Type SEMILATTICE_WITH_TOP.

  Variable t: Set.
  Variable eq: forall (x y: t), {x=y} + {x<>y}.
  Variable ge: t -> t -> Prop.
  Hypothesis ge_refl: forall x, ge x x.
  Hypothesis ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Variable bot: t.
  Hypothesis ge_bot: forall x, ge x bot.
  Variable top: t.
  Hypothesis ge_top: forall x, ge top x.
  Variable lub: t -> t -> t.
  Hypothesis lub_commut: forall x y, lub x y = lub y x.
  Hypothesis ge_lub_left: forall x y, ge (lub x y) x.

End SEMILATTICE_WITH_TOP.

(** * Semi-lattice over maps *)

(** Given a semi-lattice with top [L], the following functor implements
  a semi-lattice structure over finite maps from positive numbers to [L.t].
  The default value for these maps is either [L.top] or [L.bot]. *)

Module LPMap(L: SEMILATTICE_WITH_TOP) <: SEMILATTICE_WITH_TOP.

Inductive t_ : Set :=
  | Bot_except: PTree.t L.t -> t_
  | Top_except: PTree.t L.t -> t_.

Definition t: Set := t_.

Lemma eq: forall (x y: t), {x=y} + {x<>y}.
Proof.
  assert (forall m1 m2: PTree.t L.t, {m1=m2} + {m1<>m2}).
  apply PTree.eq. exact L.eq.
  decide equality.
Qed.

Definition get (p: positive) (x: t) : L.t :=
  match x with
  | Bot_except m =>
      match m!p with None => L.bot | Some x => x end
  | Top_except m =>
      match m!p with None => L.top | Some x => x end
  end.

Definition set (p: positive) (v: L.t) (x: t) : t :=
  match x with
  | Bot_except m =>
      Bot_except (PTree.set p v m)
  | Top_except m =>
      Top_except (PTree.set p v m)
  end.

Lemma gss:
  forall p v x,
  get p (set p v x) = v.
Proof.
  intros. destruct x; simpl; rewrite PTree.gss; auto.
Qed.

Lemma gso:
  forall p q v x,
  p <> q -> get p (set q v x) = get p x.
Proof.
  intros. destruct x; simpl; rewrite PTree.gso; auto.
Qed.

Definition ge (x y: t) : Prop :=
  forall p, L.ge (get p x) (get p y).

Lemma ge_refl: forall x, ge x x.
Proof.
  unfold ge; intros. apply L.ge_refl.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge; intros. apply L.ge_trans with (get p y); auto.
Qed.

Definition bot := Bot_except (PTree.empty L.t).

Lemma get_bot: forall p, get p bot = L.bot.
Proof.
  unfold bot; intros; simpl. rewrite PTree.gempty. auto.
Qed.

Lemma ge_bot: forall x, ge x bot.
Proof.
  unfold ge; intros. rewrite get_bot. apply L.ge_bot.
Qed.

Definition top := Top_except (PTree.empty L.t).

Lemma get_top: forall p, get p top = L.top.
Proof.
  unfold top; intros; simpl. rewrite PTree.gempty. auto.
Qed.

Lemma ge_top: forall x, ge top x.
Proof.
  unfold ge; intros. rewrite get_top. apply L.ge_top.
Qed.

Definition lub (x y: t) : t :=
  match x, y with
  | Bot_except m, Bot_except n =>
      Bot_except
        (PTree.combine 
           (fun a b =>
              match a, b with
              | Some u, Some v => Some (L.lub u v)
              | None, _ => b
              | _, None => a
              end)
           m n)
  | Bot_except m, Top_except n =>
      Top_except
        (PTree.combine
           (fun a b =>
              match a, b with
              | Some u, Some v => Some (L.lub u v)
              | None, _ => b
              | _, None => None
              end)
        m n)             
  | Top_except m, Bot_except n =>
      Top_except
        (PTree.combine
           (fun a b =>
              match a, b with
              | Some u, Some v => Some (L.lub u v)
              | None, _ => None
              | _, None => a
              end)
        m n)             
  | Top_except m, Top_except n =>
      Top_except
        (PTree.combine 
           (fun a b =>
              match a, b with
              | Some u, Some v => Some (L.lub u v)
              | _, _ => None
              end)
           m n)
  end.

Lemma lub_commut:
  forall x y, lub x y = lub y x.
Proof.
  destruct x; destruct y; unfold lub; decEq; 
  apply PTree.combine_commut; intros;
  (destruct i; destruct j; auto; decEq; apply L.lub_commut).
Qed.

Lemma ge_lub_left:
  forall x y, ge (lub x y) x.
Proof.
  unfold ge, get, lub; intros; destruct x; destruct y.

  rewrite PTree.gcombine. 
  destruct t0!p. destruct t1!p. apply L.ge_lub_left.
  apply L.ge_refl. destruct t1!p. apply L.ge_bot. apply L.ge_refl.
  auto.

  rewrite PTree.gcombine. 
  destruct t0!p. destruct t1!p. apply L.ge_lub_left.
  apply L.ge_top. destruct t1!p. apply L.ge_bot. apply L.ge_bot.
  auto.

  rewrite PTree.gcombine. 
  destruct t0!p. destruct t1!p. apply L.ge_lub_left.
  apply L.ge_refl. apply L.ge_refl. auto.

  rewrite PTree.gcombine. 
  destruct t0!p. destruct t1!p. apply L.ge_lub_left.
  apply L.ge_top. apply L.ge_refl.
  auto.
Qed.

End LPMap.

(** * Flat semi-lattice *)

(** Given a type with decidable equality [X], the following functor
  returns a semi-lattice structure over [X.t] complemented with
  a top and a bottom element.  The ordering is the flat ordering
  [Bot < Inj x < Top]. *) 

Module LFlat(X: EQUALITY_TYPE) <: SEMILATTICE_WITH_TOP.

Inductive t_ : Set :=
  | Bot: t_
  | Inj: X.t -> t_
  | Top: t_.

Definition t : Set := t_.

Lemma eq: forall (x y: t), {x=y} + {x<>y}.
Proof.
  decide equality. apply X.eq.
Qed.

Definition ge (x y: t) : Prop :=
  match x, y with
  | Top, _ => True
  | _, Bot => True
  | Inj a, Inj b => a = b
  | _, _ => False
  end.

Lemma ge_refl: forall x, ge x x.
Proof.
  unfold ge; destruct x; auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  unfold ge; destruct x; destruct y; try destruct z; intuition.
  transitivity t1; auto.
Qed.

Definition bot: t := Bot.

Lemma ge_bot: forall x, ge x bot.
Proof.
  destruct x; simpl; auto.
Qed.

Definition top: t := Top.

Lemma ge_top: forall x, ge top x.
Proof.
  destruct x; simpl; auto.
Qed.

Definition lub (x y: t) : t :=
  match x, y with
  | Bot, _ => y
  | _, Bot => x
  | Top, _ => Top
  | _, Top => Top
  | Inj a, Inj b => if X.eq a b then Inj a else Top
  end.

Lemma lub_commut: forall x y, lub x y = lub y x.
Proof.
  destruct x; destruct y; simpl; auto.
  case (X.eq t0 t1); case (X.eq t1 t0); intros; congruence.
Qed.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof.
  destruct x; destruct y; simpl; auto.
  case (X.eq t0 t1); simpl; auto.
Qed.

End LFlat.
  
(** * Boolean semi-lattice *)

(** This semi-lattice has only two elements, [bot] and [top], trivially
  ordered. *)

Module LBoolean <: SEMILATTICE_WITH_TOP.

Definition t := bool.

Lemma eq: forall (x y: t), {x=y} + {x<>y}.
Proof. decide equality. Qed.

Definition ge (x y: t) : Prop := x = y \/ x = true.

Lemma ge_refl: forall x, ge x x.
Proof. unfold ge; tauto. Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof. unfold ge; intuition congruence. Qed.

Definition bot := false.

Lemma ge_bot: forall x, ge x bot.
Proof. destruct x; compute; tauto. Qed.

Definition top := true.

Lemma ge_top: forall x, ge top x.
Proof. unfold ge, top; tauto. Qed.

Definition lub (x y: t) := x || y.

Lemma lub_commut: forall x y, lub x y = lub y x.
Proof. intros; unfold lub. apply orb_comm. Qed.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof. destruct x; destruct y; compute; tauto. Qed.

End LBoolean.


