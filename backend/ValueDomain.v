(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import FunInd.
Require Import Zwf Coqlib Maps Integers Floats Lattice.
Require Import Compopts AST.
Require Import Values Memory Globalenvs Events.
Require Import Registers RTL.

(** The abstract domains for value analysis *)

Inductive block_class : Type :=
  | BCinvalid
  | BCglob (id: ident)
  | BCstack
  | BCother.

Definition block_class_eq: forall (x y: block_class), {x=y} + {x<>y}.
Proof. decide equality. apply peq. Defined.

Record block_classification : Type := BC {
  bc_img :> block -> block_class;
  bc_stack: forall b1 b2, bc_img b1 = BCstack -> bc_img b2 = BCstack -> b1 = b2;
  bc_glob: forall b1 b2 id, bc_img b1 = BCglob id -> bc_img b2 = BCglob id -> b1 = b2
}.

Definition bc_below (bc: block_classification) (bound: block) : Prop :=
  forall b, bc b <> BCinvalid -> Plt b bound.

Lemma bc_below_invalid:
  forall b bc bound, ~Plt b bound -> bc_below bc bound -> bc b = BCinvalid.
Proof.
  intros. destruct (block_class_eq (bc b) BCinvalid); auto.
  elim H. apply H0; auto.
Qed.

Hint Extern 2 (_ = _) => congruence : va.
Hint Extern 2 (_ <> _) => congruence : va.
Hint Extern 2 (_ < _) => xomega : va.
Hint Extern 2 (_ <= _) => xomega : va.
Hint Extern 2 (_ > _) => xomega : va.
Hint Extern 2 (_ >= _) => xomega : va.

Section MATCH.

Variable bc: block_classification.

(** * Abstracting the result of conditions (type [option bool]) *)

Inductive abool :=
  | Bnone               (**r always [None] (undefined) *)
  | Just (b: bool)      (**r always [Some b] (defined and known to be [b]) *)
  | Maybe (b: bool)     (**r either [None] or [Some b] (known to be [b] if defined) *)
  | Btop.               (**r unknown, all results are possible *)

Inductive cmatch: option bool -> abool -> Prop :=
  | cmatch_none: cmatch None Bnone
  | cmatch_just: forall b, cmatch (Some b) (Just b)
  | cmatch_maybe_none: forall b, cmatch None (Maybe b)
  | cmatch_maybe_some: forall b, cmatch (Some b) (Maybe b)
  | cmatch_top: forall ob, cmatch ob Btop.

Hint Constructors cmatch : va.

Definition club (x y: abool) : abool :=
  match x, y with
  | Bnone, Bnone => Bnone
  | Bnone, (Just b | Maybe b) => Maybe b
  | (Just b | Maybe b), Bnone => Maybe b
  | Just b1, Just b2 => if eqb b1 b2 then x else Btop
  | Maybe b1, Maybe b2 => if eqb b1 b2 then x else Btop
  | Maybe b1, Just b2 => if eqb b1 b2 then x else Btop
  | Just b1, Maybe b2 => if eqb b1 b2 then y else Btop
  | _, _ => Btop
  end.

Lemma cmatch_lub_l:
  forall ob x y, cmatch ob x -> cmatch ob (club x y).
Proof.
  intros. unfold club; inv H; destruct y; try constructor;
  destruct (eqb b b0) eqn:EQ; try constructor.
  replace b0 with b by (apply eqb_prop; auto). constructor.
Qed.

Lemma cmatch_lub_r:
  forall ob x y, cmatch ob y -> cmatch ob (club x y).
Proof.
  intros. unfold club; inv H; destruct x; try constructor;
  destruct (eqb b0 b) eqn:EQ; try constructor.
  replace b with b0 by (apply eqb_prop; auto). constructor.
  replace b with b0 by (apply eqb_prop; auto). constructor.
  replace b with b0 by (apply eqb_prop; auto). constructor.
Qed.

Definition cnot (x: abool) : abool :=
  match x with
  | Just b => Just (negb b)
  | Maybe b => Maybe (negb b)
  | _ => x
  end.

Lemma cnot_sound:
  forall ob x, cmatch ob x -> cmatch (option_map negb ob) (cnot x).
Proof.
  destruct 1; constructor.
Qed.

(** * Abstracting pointers *)

Inductive aptr : Type :=
  | Pbot                         (**r bottom (empty set of pointers) *)
  | Gl (id: ident) (ofs: ptrofs) (**r pointer into the block for global variable [id] at offset [ofs] *)
  | Glo (id: ident)              (**r pointer anywhere into the block for global [id] *)
  | Glob                         (**r pointer into any global variable *)
  | Stk (ofs: ptrofs)            (**r pointer into the current stack frame at offset [ofs] *)
  | Stack                        (**r pointer anywhere into the current stack frame *)
  | Nonstack                     (**r pointer anywhere but into the current stack frame *)
  | Ptop.                        (**r any valid pointer *)

Definition eq_aptr: forall (p1 p2: aptr), {p1=p2} + {p1<>p2}.
Proof.
  intros. generalize ident_eq, Ptrofs.eq_dec; intros. decide equality.
Defined.

Inductive pmatch (b: block) (ofs: ptrofs): aptr -> Prop :=
  | pmatch_gl: forall id,
      bc b = BCglob id ->
      pmatch b ofs (Gl id ofs)
  | pmatch_glo: forall id,
      bc b = BCglob id ->
      pmatch b ofs (Glo id)
  | pmatch_glob: forall id,
      bc b = BCglob id ->
      pmatch b ofs Glob
  | pmatch_stk:
      bc b = BCstack ->
      pmatch b ofs (Stk ofs)
  | pmatch_stack:
      bc b = BCstack ->
      pmatch b ofs Stack
  | pmatch_nonstack:
      bc b <> BCstack -> bc b <> BCinvalid ->
      pmatch b ofs Nonstack
  | pmatch_top:
      bc b <> BCinvalid ->
      pmatch b ofs Ptop.

Hint Constructors pmatch: va.

Inductive pge: aptr -> aptr -> Prop :=
  | pge_top: forall p, pge Ptop p
  | pge_bot: forall p, pge p Pbot
  | pge_refl: forall p, pge p p
  | pge_glo_gl: forall id ofs, pge (Glo id) (Gl id ofs)
  | pge_glob_gl: forall id ofs, pge Glob (Gl id ofs)
  | pge_glob_glo: forall id, pge Glob (Glo id)
  | pge_ns_gl: forall id ofs, pge Nonstack (Gl id ofs)
  | pge_ns_glo: forall id, pge Nonstack (Glo id)
  | pge_ns_glob: pge Nonstack Glob
  | pge_stack_stk: forall ofs, pge Stack (Stk ofs).

Hint Constructors pge: va.

Lemma pge_trans:
  forall p q, pge p q -> forall r, pge q r -> pge p r.
Proof.
  induction 1; intros r PM; inv PM; auto with va.
Qed.

Lemma pmatch_ge:
  forall b ofs p q, pge p q -> pmatch b ofs q -> pmatch b ofs p.
Proof.
  induction 1; intros PM; inv PM; eauto with va.
Qed.

Lemma pmatch_top': forall b ofs p, pmatch b ofs p -> pmatch b ofs Ptop.
Proof.
  intros. apply pmatch_ge with p; auto with va.
Qed.

Definition plub (p q: aptr) : aptr :=
  match p, q with
  | Pbot, _ => q
  | _, Pbot => p
  | Gl id1 ofs1, Gl id2 ofs2 =>
      if ident_eq id1 id2 then if Ptrofs.eq_dec ofs1 ofs2 then p else Glo id1 else Glob
  | Gl id1 ofs1, Glo id2 =>
      if ident_eq id1 id2 then q else Glob
  | Glo id1, Gl id2 ofs2 =>
      if ident_eq id1 id2 then p else Glob
  | Glo id1, Glo id2 =>
      if ident_eq id1 id2 then p else Glob
  | (Gl _ _ | Glo _ | Glob), Glob => Glob
  | Glob, (Gl _ _ | Glo _) => Glob
  | (Gl _ _ | Glo _ | Glob | Nonstack), Nonstack =>
      Nonstack
  | Nonstack, (Gl _ _ | Glo _ | Glob) =>
      Nonstack
  | Stk ofs1, Stk ofs2 =>
      if Ptrofs.eq_dec ofs1 ofs2 then p else Stack
  | (Stk _ | Stack), Stack =>
      Stack
  | Stack, Stk _ =>
      Stack
  | _, _ => Ptop
  end.

Lemma plub_comm:
  forall p q, plub p q = plub q p.
Proof.
  intros; unfold plub; destruct p; destruct q; auto.
  destruct (ident_eq id id0). subst id0.
  rewrite dec_eq_true.
  destruct (Ptrofs.eq_dec ofs ofs0). subst ofs0. rewrite dec_eq_true. auto.
  rewrite dec_eq_false by auto. auto.
  rewrite dec_eq_false by auto. auto.
  destruct (ident_eq id id0). subst id0.
  rewrite dec_eq_true; auto.
  rewrite dec_eq_false; auto.
  destruct (ident_eq id id0). subst id0.
  rewrite dec_eq_true; auto.
  rewrite dec_eq_false; auto.
  destruct (ident_eq id id0). subst id0.
  rewrite dec_eq_true; auto.
  rewrite dec_eq_false; auto.
  destruct (Ptrofs.eq_dec ofs ofs0). subst ofs0. rewrite dec_eq_true; auto.
  rewrite dec_eq_false; auto.
Qed.

Lemma pge_lub_l:
  forall p q, pge (plub p q) p.
Proof.
  unfold plub; destruct p, q; auto with va.
- destruct (ident_eq id id0).
  destruct (Ptrofs.eq_dec ofs ofs0); subst; constructor.
  constructor.
- destruct (ident_eq id id0); subst; constructor.
- destruct (ident_eq id id0); subst; constructor.
- destruct (ident_eq id id0); subst; constructor.
- destruct (Ptrofs.eq_dec ofs ofs0); subst; constructor.
Qed.

Lemma pge_lub_r:
  forall p q, pge (plub p q) q.
Proof.
  intros. rewrite plub_comm. apply pge_lub_l.
Qed.

Lemma pmatch_lub_l:
  forall b ofs p q, pmatch b ofs p -> pmatch b ofs (plub p q).
Proof.
  intros. eapply pmatch_ge; eauto. apply pge_lub_l.
Qed.

Lemma pmatch_lub_r:
  forall b ofs p q, pmatch b ofs q -> pmatch b ofs (plub p q).
Proof.
  intros. eapply pmatch_ge; eauto. apply pge_lub_r.
Qed.

Lemma plub_least:
  forall r p q, pge r p -> pge r q -> pge r (plub p q).
Proof.
  intros. inv H; inv H0; simpl; try constructor.
- destruct p; constructor.
- unfold plub; destruct q; repeat rewrite dec_eq_true; constructor.
- rewrite dec_eq_true; constructor.
- rewrite dec_eq_true; constructor.
- rewrite dec_eq_true. destruct (Ptrofs.eq_dec ofs ofs0); constructor.
- destruct (ident_eq id id0). destruct (Ptrofs.eq_dec ofs ofs0); constructor. constructor.
- destruct (ident_eq id id0); constructor.
- destruct (ident_eq id id0); constructor.
- destruct (ident_eq id id0); constructor.
- destruct (ident_eq id id0). destruct (Ptrofs.eq_dec ofs ofs0); constructor. constructor.
- destruct (ident_eq id id0); constructor.
- destruct (ident_eq id id0); constructor.
- destruct (ident_eq id id0); constructor.
- destruct (Ptrofs.eq_dec ofs ofs0); constructor.
Qed.

Definition pincl (p q: aptr) : bool :=
  match p, q with
  | Pbot, _ => true
  | Gl id1 ofs1, Gl id2 ofs2 => peq id1 id2 && Ptrofs.eq_dec ofs1 ofs2
  | Gl id1 ofs1, Glo id2 => peq id1 id2
  | Glo id1, Glo id2 => peq id1 id2
  | (Gl _ _ | Glo _ | Glob), Glob => true
  | (Gl _ _ | Glo _ | Glob | Nonstack), Nonstack => true
  | Stk ofs1, Stk ofs2 => Ptrofs.eq_dec ofs1 ofs2
  | Stk ofs1, Stack => true
  | Stack, Stack => true
  | _, Ptop => true
  | _, _ => false
  end.

Lemma pincl_ge: forall p q, pincl p q = true -> pge q p.
Proof.
  unfold pincl; destruct p, q; intros; try discriminate; auto with va;
  InvBooleans; subst; auto with va.
Qed.

Lemma pincl_ge_2: forall p q, pge p q -> pincl q p = true.
Proof.
  destruct 1; simpl; auto.
- destruct p; auto.
- destruct p; simpl; auto; rewrite ! proj_sumbool_is_true; auto.
- rewrite ! proj_sumbool_is_true; auto.
Qed.

Lemma pincl_sound:
  forall b ofs p q,
  pincl p q = true -> pmatch b ofs p -> pmatch b ofs q.
Proof.
  intros. eapply pmatch_ge; eauto. apply pincl_ge; auto.
Qed.

Definition padd (p: aptr) (n: ptrofs) : aptr :=
  match p with
  | Gl id ofs => Gl id (Ptrofs.add ofs n)
  | Stk ofs => Stk (Ptrofs.add ofs n)
  | _ => p
  end.

Lemma padd_sound:
  forall b ofs p delta,
  pmatch b ofs p ->
  pmatch b (Ptrofs.add ofs delta) (padd p delta).
Proof.
  intros. inv H; simpl padd; eauto with va.
Qed.

Definition psub (p: aptr) (n: ptrofs) : aptr :=
  match p with
  | Gl id ofs => Gl id (Ptrofs.sub ofs n)
  | Stk ofs => Stk (Ptrofs.sub ofs n)
  | _ => p
  end.

Lemma psub_sound:
  forall b ofs p delta,
  pmatch b ofs p ->
  pmatch b (Ptrofs.sub ofs delta) (psub p delta).
Proof.
  intros. inv H; simpl psub; eauto with va.
Qed.

Definition poffset (p: aptr) : aptr :=
  match p with
  | Gl id ofs => Glo id
  | Stk ofs => Stack
  | _ => p
  end.

Lemma poffset_sound:
  forall b ofs1 ofs2 p,
  pmatch b ofs1 p ->
  pmatch b ofs2 (poffset p).
Proof.
  intros. inv H; simpl poffset; eauto with va.
Qed.

Definition cmp_different_blocks (c: comparison) : abool :=
  match c with
  | Ceq => Maybe false
  | Cne => Maybe true
  | _   => Bnone
  end.

Lemma cmp_different_blocks_none:
  forall c, cmatch None (cmp_different_blocks c).
Proof.
  intros; destruct c; constructor.
Qed.

Lemma cmp_different_blocks_sound:
  forall c, cmatch (Val.cmp_different_blocks c) (cmp_different_blocks c).
Proof.
  intros; destruct c; constructor.
Qed.

Definition pcmp (c: comparison) (p1 p2: aptr) : abool :=
  match p1, p2 with
  | Pbot, _ | _, Pbot => Bnone
  | Gl id1 ofs1, Gl id2 ofs2 =>
      if peq id1 id2 then Maybe (Ptrofs.cmpu c ofs1 ofs2)
      else cmp_different_blocks c
  | Gl id1 ofs1, Glo id2 =>
      if peq id1 id2 then Btop else cmp_different_blocks c
  | Glo id1, Gl id2 ofs2 =>
      if peq id1 id2 then Btop else cmp_different_blocks c
  | Glo id1, Glo id2 =>
      if peq id1 id2 then Btop else cmp_different_blocks c
  | Stk ofs1, Stk ofs2 => Maybe (Ptrofs.cmpu c ofs1 ofs2)
  | (Gl _ _ | Glo _ | Glob | Nonstack), (Stk _ | Stack) => cmp_different_blocks c
  | (Stk _ | Stack), (Gl _ _ | Glo _ | Glob | Nonstack) => cmp_different_blocks c
  | _, _ => Btop
  end.

Lemma pcmp_sound:
  forall valid c b1 ofs1 p1 b2 ofs2 p2,
  pmatch b1 ofs1 p1 -> pmatch b2 ofs2 p2 ->
  cmatch (Val.cmpu_bool valid c (Vptr b1 ofs1) (Vptr b2 ofs2)) (pcmp c p1 p2).
Proof.
  intros.
  assert (DIFF: b1 <> b2 ->
            cmatch (Val.cmpu_bool valid c (Vptr b1 ofs1) (Vptr b2 ofs2))
                   (cmp_different_blocks c)).
  {
    intros. simpl. rewrite dec_eq_false by assumption.
    destruct Archi.ptr64.
    apply cmp_different_blocks_none.
    destruct (valid b1 (Ptrofs.unsigned ofs1) && valid b2 (Ptrofs.unsigned ofs2)); simpl.
    apply cmp_different_blocks_sound.
    apply cmp_different_blocks_none.
  }
  assert (SAME: b1 = b2 ->
            cmatch (Val.cmpu_bool valid c (Vptr b1 ofs1) (Vptr b2 ofs2))
                   (Maybe (Ptrofs.cmpu c ofs1 ofs2))).
  {
    intros. subst b2. simpl. destruct Archi.ptr64.
    constructor.
    rewrite dec_eq_true.
    destruct ((valid b1 (Ptrofs.unsigned ofs1) || valid b1 (Ptrofs.unsigned ofs1 - 1)) &&
         (valid b1 (Ptrofs.unsigned ofs2) || valid b1 (Ptrofs.unsigned ofs2 - 1))); simpl.
    constructor.
    constructor.
  }
  unfold pcmp; inv H; inv H0; (apply cmatch_top || (apply DIFF; congruence) || idtac).
  - destruct (peq id id0). subst id0. apply SAME. eapply bc_glob; eauto.
    auto with va.
  - destruct (peq id id0); auto with va.
  - destruct (peq id id0); auto with va.
  - destruct (peq id id0); auto with va.
  - apply SAME. eapply bc_stack; eauto.
Qed.

Lemma pcmp_sound_64:
  forall valid c b1 ofs1 p1 b2 ofs2 p2,
  pmatch b1 ofs1 p1 -> pmatch b2 ofs2 p2 ->
  cmatch (Val.cmplu_bool valid c (Vptr b1 ofs1) (Vptr b2 ofs2)) (pcmp c p1 p2).
Proof.
  intros.
  assert (DIFF: b1 <> b2 ->
            cmatch (Val.cmplu_bool valid c (Vptr b1 ofs1) (Vptr b2 ofs2))
                   (cmp_different_blocks c)).
  {
    intros. simpl. rewrite dec_eq_false by assumption.
    destruct Archi.ptr64; simpl.
    destruct (valid b1 (Ptrofs.unsigned ofs1) && valid b2 (Ptrofs.unsigned ofs2)); simpl.
    apply cmp_different_blocks_sound.
    apply cmp_different_blocks_none.
    apply cmp_different_blocks_none.
  }
  assert (SAME: b1 = b2 ->
            cmatch (Val.cmplu_bool valid c (Vptr b1 ofs1) (Vptr b2 ofs2))
                   (Maybe (Ptrofs.cmpu c ofs1 ofs2))).
  {
    intros. subst b2. simpl. destruct Archi.ptr64.
    rewrite dec_eq_true.
    destruct ((valid b1 (Ptrofs.unsigned ofs1) || valid b1 (Ptrofs.unsigned ofs1 - 1)) &&
         (valid b1 (Ptrofs.unsigned ofs2) || valid b1 (Ptrofs.unsigned ofs2 - 1))); simpl.
    constructor.
    constructor.
    constructor.
  }
  unfold pcmp; inv H; inv H0; (apply cmatch_top || (apply DIFF; congruence) || idtac).
  - destruct (peq id id0). subst id0. apply SAME. eapply bc_glob; eauto.
    auto with va.
  - destruct (peq id id0); auto with va.
  - destruct (peq id id0); auto with va.
  - destruct (peq id id0); auto with va.
  - apply SAME. eapply bc_stack; eauto.
Qed.

Lemma pcmp_none:
  forall c p1 p2, cmatch None (pcmp c p1 p2).
Proof.
  intros.
  unfold pcmp; destruct p1; try constructor; destruct p2;
  try (destruct (peq id id0));  try constructor; try (apply cmp_different_blocks_none).
Qed.

Definition pdisjoint (p1: aptr) (sz1: Z) (p2: aptr) (sz2: Z) : bool :=
  match p1, p2 with
  | Pbot, _ => true
  | _, Pbot => true
  | Gl id1 ofs1, Gl id2 ofs2 =>
      if peq id1 id2
      then zle (Ptrofs.unsigned ofs1 + sz1) (Ptrofs.unsigned ofs2)
           || zle (Ptrofs.unsigned ofs2 + sz2) (Ptrofs.unsigned ofs1)
      else true
  | Gl id1 ofs1, Glo id2 => negb(peq id1 id2)
  | Glo id1, Gl id2 ofs2 => negb(peq id1 id2)
  | Glo id1, Glo id2 => negb(peq id1 id2)
  | Stk ofs1, Stk ofs2 =>
      zle (Ptrofs.unsigned ofs1 + sz1) (Ptrofs.unsigned ofs2)
      || zle (Ptrofs.unsigned ofs2 + sz2) (Ptrofs.unsigned ofs1)
  | (Gl _ _ | Glo _ | Glob | Nonstack), (Stk _ | Stack) => true
  | (Stk _ | Stack), (Gl _ _ | Glo _ | Glob | Nonstack) => true
  | _, _ => false
  end.

Lemma pdisjoint_sound:
  forall sz1 b1 ofs1 p1 sz2 b2 ofs2 p2,
  pdisjoint p1 sz1 p2 sz2 = true ->
  pmatch b1 ofs1 p1 -> pmatch b2 ofs2 p2 ->
  b1 <> b2 \/ Ptrofs.unsigned ofs1 + sz1 <= Ptrofs.unsigned ofs2 \/ Ptrofs.unsigned ofs2 + sz2 <= Ptrofs.unsigned ofs1.
Proof.
  intros. inv H0; inv H1; simpl in H; try discriminate; try (left; congruence).
- destruct (peq id id0). subst id0. destruct (orb_true_elim _ _ H); InvBooleans; auto.
  left; congruence.
- destruct (peq id id0); try discriminate. left; congruence.
- destruct (peq id id0); try discriminate. left; congruence.
- destruct (peq id id0); try discriminate. left; congruence.
- destruct (orb_true_elim _ _ H); InvBooleans; auto.
Qed.

(** * Abstracting values *)

Inductive aval : Type :=
  | Vbot                     (**r bottom (empty set of values) *)
  | I (n: int)               (**r exactly [Vint n] *)
  | Uns (p: aptr) (n: Z)     (**r a [n]-bit unsigned integer, or [Vundef] *)
  | Sgn (p: aptr) (n: Z)     (**r a [n]-bit signed integer, or [Vundef] *)
  | L (n: int64)             (**r exactly [Vlong n] *)
  | F (f: float)             (**r exactly [Vfloat f] *)
  | FS (f: float32)          (**r exactly [Vsingle f] *)
  | Ptr (p: aptr)            (**r a pointer from the set [p], or [Vundef] *)
  | Ifptr (p: aptr).         (**r a pointer from the set [p], or a number, or [Vundef] *)

(** The "top" of the value domain is defined as any pointer, or any
    number, or [Vundef]. *)

Definition Vtop := Ifptr Ptop.

(** The [p] parameter (an abstract pointer) to [Uns] and [Sgn] helps keeping
  track of pointers that leak through arithmetic operations such as shifts.
  See the section "Tracking leakage of pointers" below.
  In strict analysis mode, [p] is always [Pbot]. *)

Definition eq_aval: forall (v1 v2: aval), {v1=v2} + {v1<>v2}.
Proof.
  intros. generalize zeq Int.eq_dec Int64.eq_dec Float.eq_dec Float32.eq_dec eq_aptr; intros.
  decide equality.
Defined.

Definition is_uns (n: Z) (i: int) : Prop :=
  forall m, 0 <= m < Int.zwordsize -> m >= n -> Int.testbit i m = false.
Definition is_sgn (n: Z) (i: int) : Prop :=
  forall m, 0 <= m < Int.zwordsize -> m >= n - 1 -> Int.testbit i m = Int.testbit i (Int.zwordsize - 1).

Inductive vmatch : val -> aval -> Prop :=
  | vmatch_i: forall i, vmatch (Vint i) (I i)
  | vmatch_Uns: forall p i n, 0 <= n -> is_uns n i -> vmatch (Vint i) (Uns p n)
  | vmatch_Uns_undef: forall p n, vmatch Vundef (Uns p n)
  | vmatch_Sgn: forall p i n, 0 < n -> is_sgn n i -> vmatch (Vint i) (Sgn p n)
  | vmatch_Sgn_undef: forall p n, vmatch Vundef (Sgn p n)
  | vmatch_l: forall i, vmatch (Vlong i) (L i)
  | vmatch_f: forall f, vmatch (Vfloat f) (F f)
  | vmatch_s: forall f, vmatch (Vsingle f) (FS f)
  | vmatch_ptr: forall b ofs p, pmatch b ofs p -> vmatch (Vptr b ofs) (Ptr p)
  | vmatch_ptr_undef: forall p, vmatch Vundef (Ptr p)
  | vmatch_ifptr_undef: forall p, vmatch Vundef (Ifptr p)
  | vmatch_ifptr_i: forall i p, vmatch (Vint i) (Ifptr p)
  | vmatch_ifptr_l: forall i p, vmatch (Vlong i) (Ifptr p)
  | vmatch_ifptr_f: forall f p, vmatch (Vfloat f) (Ifptr p)
  | vmatch_ifptr_s: forall f p, vmatch (Vsingle f) (Ifptr p)
  | vmatch_ifptr_p: forall b ofs p, pmatch b ofs p -> vmatch (Vptr b ofs) (Ifptr p).

Lemma vmatch_ifptr:
  forall v p,
  (forall b ofs, v = Vptr b ofs -> pmatch b ofs p) ->
  vmatch v (Ifptr p).
Proof.
  intros. destruct v; constructor; auto.
Qed.

Lemma vmatch_top: forall v x, vmatch v x -> vmatch v Vtop.
Proof.
  intros. apply vmatch_ifptr. intros. subst v. inv H; eapply pmatch_top'; eauto.
Qed.

Hint Extern 1 (vmatch _ _) => constructor : va.

(* Some properties about [is_uns] and [is_sgn]. *)

Lemma is_uns_mon: forall n1 n2 i, is_uns n1 i -> n1 <= n2 -> is_uns n2 i.
Proof.
  intros; red; intros. apply H; omega.
Qed.

Lemma is_sgn_mon: forall n1 n2 i, is_sgn n1 i -> n1 <= n2 -> is_sgn n2 i.
Proof.
  intros; red; intros. apply H; omega.
Qed.

Lemma is_uns_sgn: forall n1 n2 i, is_uns n1 i -> n1 < n2 -> is_sgn n2 i.
Proof.
  intros; red; intros. rewrite ! H by omega. auto.
Qed.

Definition usize := Int.size.

Definition ssize (i: int) := Int.size (if Int.lt i Int.zero then Int.not i else i) + 1.

Lemma is_uns_usize:
  forall i, is_uns (usize i) i.
Proof.
  unfold usize; intros; red; intros.
  apply Int.bits_size_2. omega.
Qed.

Lemma is_sgn_ssize:
  forall i, is_sgn (ssize i) i.
Proof.
  unfold ssize; intros; red; intros.
  destruct (Int.lt i Int.zero) eqn:LT.
- rewrite <- (negb_involutive (Int.testbit i m)).
  rewrite <- (negb_involutive (Int.testbit i (Int.zwordsize - 1))).
  f_equal.
  generalize (Int.size_range (Int.not i)); intros RANGE.
  rewrite <- ! Int.bits_not by omega.
  rewrite ! Int.bits_size_2 by omega.
  auto.
- rewrite ! Int.bits_size_2 by omega.
  auto.
Qed.

Lemma is_uns_zero_ext:
  forall n i, is_uns n i <-> Int.zero_ext n i = i.
Proof.
  intros; split; intros.
  Int.bit_solve. destruct (zlt i0 n); auto. symmetry; apply H; auto. omega.
  rewrite <- H. red; intros. rewrite Int.bits_zero_ext by omega. rewrite zlt_false by omega. auto.
Qed.

Lemma is_sgn_sign_ext:
  forall n i, 0 < n -> (is_sgn n i <-> Int.sign_ext n i = i).
Proof.
  intros; split; intros.
  Int.bit_solve. destruct (zlt i0 n); auto.
  transitivity (Int.testbit i (Int.zwordsize - 1)).
  apply H0; omega. symmetry; apply H0; omega.
  rewrite <- H0. red; intros. rewrite ! Int.bits_sign_ext by omega.
  f_equal. transitivity (n-1). destruct (zlt m n); omega.
  destruct (zlt (Int.zwordsize - 1) n); omega.
Qed.

Lemma is_zero_ext_uns:
  forall i n m,
  is_uns m i \/ n <= m -> is_uns m (Int.zero_ext n i).
Proof.
  intros. red; intros. rewrite Int.bits_zero_ext by omega.
  destruct (zlt m0 n); auto. destruct H. apply H; omega. omegaContradiction.
Qed.

Lemma is_zero_ext_sgn:
  forall i n m,
  n < m ->
  is_sgn m (Int.zero_ext n i).
Proof.
  intros. red; intros. rewrite ! Int.bits_zero_ext by omega.
  transitivity false. apply zlt_false; omega.
  symmetry; apply zlt_false; omega.
Qed.

Lemma is_sign_ext_uns:
  forall i n m,
  0 <= m < n ->
  is_uns m i ->
  is_uns m (Int.sign_ext n i).
Proof.
  intros; red; intros. rewrite Int.bits_sign_ext by omega.
  apply H0. destruct (zlt m0 n); omega. destruct (zlt m0 n); omega.
Qed.

Lemma is_sign_ext_sgn:
  forall i n m,
  0 < n -> 0 < m ->
  is_sgn m i \/ n <= m -> is_sgn m (Int.sign_ext n i).
Proof.
  intros. apply is_sgn_sign_ext; auto.
  destruct (zlt m n). destruct H1. apply is_sgn_sign_ext in H1; auto.
  rewrite <- H1. rewrite (Int.sign_ext_widen i) by omega. apply Int.sign_ext_idem; auto.
  omegaContradiction.
  apply Int.sign_ext_widen; omega.
Qed.

Hint Resolve is_uns_mon is_sgn_mon is_uns_sgn is_uns_usize is_sgn_ssize : va.

Lemma is_uns_1:
  forall n, is_uns 1 n -> n = Int.zero \/ n = Int.one.
Proof.
  intros. destruct (Int.testbit n 0) eqn:B0; [right|left]; apply Int.same_bits_eq; intros.
  rewrite Int.bits_one. destruct (zeq i 0). subst i; auto. apply H; omega.
  rewrite Int.bits_zero. destruct (zeq i 0). subst i; auto. apply H; omega.
Qed.

(** Tracking leakage of pointers through arithmetic operations.

In the CompCert semantics, arithmetic operations (e.g. "xor") applied
to pointer values are undefined or produce the [Vundef] result.
So, in strict mode, we can abstract the result values of such operations
as [Ifptr Pbot], namely: [Vundef], or any number, but not a pointer.

In real code, such arithmetic over pointers occurs, so we need to be
more prudent.  The policy we take, inspired by that of GCC, is that
"undefined" arithmetic operations involving pointer arguments can
produce a pointer, but not any pointer: rather, a pointer to the same
block, but possibly with a different offset.  Hence, if the operation
has a pointer to abstract region [p] as argument, the result value
can be a pointer to abstract region [poffset p].  In other words,
the result value is abstracted as [Ifptr (poffset p)].

We encapsulate this reasoning in the following [ntop1] and [ntop2] functions
("numerical top"). *)

Definition provenance (x: aval) : aptr :=
  if va_strict tt then Pbot else
    match x with
    | Ptr p | Ifptr p | Uns p _ | Sgn p _ => poffset p
    | _ => Pbot
    end.

Definition ntop : aval := Ifptr Pbot.

Definition ntop1 (x: aval) : aval := Ifptr (provenance x).

Definition ntop2 (x y: aval) : aval := Ifptr (plub (provenance x) (provenance y)).

(** Smart constructors for [Uns] and [Sgn]. *)

Definition uns (p: aptr) (n: Z) : aval :=
  if zle n 1 then Uns p 1
  else if zle n 7 then Uns p 7
  else if zle n 8 then Uns p 8
  else if zle n 15 then Uns p 15
  else if zle n 16 then Uns p 16
  else Ifptr p.

Definition sgn (p: aptr) (n: Z) : aval :=
  if zle n 8 then Sgn p 8 else if zle n 16 then Sgn p 16 else Ifptr p.

Lemma vmatch_uns':
  forall p i n, is_uns (Z.max 0 n) i -> vmatch (Vint i) (uns p n).
Proof.
  intros.
  assert (A: forall n', n' >= 0 -> n' >= n -> is_uns n' i) by (eauto with va).
  unfold uns.
  destruct (zle n 1). auto with va.
  destruct (zle n 7). auto with va.
  destruct (zle n 8). auto with va.
  destruct (zle n 15). auto with va.
  destruct (zle n 16). auto with va.
  auto with va.
Qed.

Lemma vmatch_uns:
  forall p i n, is_uns n i -> vmatch (Vint i) (uns p n).
Proof.
  intros. apply vmatch_uns'. eauto with va.
Qed.

Lemma vmatch_uns_undef: forall p n, vmatch Vundef (uns p n).
Proof.
  intros. unfold uns.
  destruct (zle n 1). auto with va.
  destruct (zle n 7). auto with va.
  destruct (zle n 8). auto with va.
  destruct (zle n 15). auto with va.
  destruct (zle n 16); auto with va.
Qed.

Lemma vmatch_sgn':
  forall p i n, is_sgn (Z.max 1 n) i -> vmatch (Vint i) (sgn p n).
Proof.
  intros.
  assert (A: forall n', n' >= 1 -> n' >= n -> is_sgn n' i) by (eauto with va).
  unfold sgn.
  destruct (zle n 8). auto with va.
  destruct (zle n 16); auto with va.
Qed.

Lemma vmatch_sgn:
  forall p i n, is_sgn n i -> vmatch (Vint i) (sgn p n).
Proof.
  intros. apply vmatch_sgn'. eauto with va.
Qed.

Lemma vmatch_sgn_undef: forall p n, vmatch Vundef (sgn p n).
Proof.
  intros. unfold sgn.
  destruct (zle n 8). auto with va.
  destruct (zle n 16); auto with va.
Qed.

Hint Resolve vmatch_uns vmatch_uns_undef vmatch_sgn vmatch_sgn_undef : va.

Lemma vmatch_Uns_1:
  forall p v, vmatch v (Uns p 1) -> v = Vundef \/ v = Vint Int.zero \/ v = Vint Int.one.
Proof.
  intros. inv H; auto. right. exploit is_uns_1; eauto. intuition congruence.
Qed.

(** Ordering *)

Inductive vge: aval -> aval -> Prop :=
  | vge_bot: forall v, vge v Vbot
  | vge_i: forall i, vge (I i) (I i)
  | vge_l: forall i, vge (L i) (L i)
  | vge_f: forall f, vge (F f) (F f)
  | vge_s: forall f, vge (FS f) (FS f)
  | vge_uns_i: forall p n i, 0 <= n -> is_uns n i -> vge (Uns p n) (I i)
  | vge_uns_uns: forall p1 n1 p2 n2, n1 >= n2 -> pge p1 p2 -> vge (Uns p1 n1) (Uns p2 n2)
  | vge_sgn_i: forall p n i, 0 < n -> is_sgn n i -> vge (Sgn p n) (I i)
  | vge_sgn_sgn: forall p1 n1 p2 n2, n1 >= n2 -> pge p1 p2 -> vge (Sgn p1 n1) (Sgn p2 n2)
  | vge_sgn_uns: forall p1 n1 p2 n2, n1 > n2 -> pge p1 p2 -> vge (Sgn p1 n1) (Uns p2 n2)
  | vge_p_p: forall p q, pge p q -> vge (Ptr p) (Ptr q)
  | vge_ip_p: forall p q, pge p q -> vge (Ifptr p) (Ptr q)
  | vge_ip_ip: forall p q, pge p q -> vge (Ifptr p) (Ifptr q)
  | vge_ip_i: forall p i, vge (Ifptr p) (I i)
  | vge_ip_l: forall p i, vge (Ifptr p) (L i)
  | vge_ip_f: forall p f, vge (Ifptr p) (F f)
  | vge_ip_s: forall p f, vge (Ifptr p) (FS f)
  | vge_ip_uns: forall p q n, pge p q -> vge (Ifptr p) (Uns q n)
  | vge_ip_sgn: forall p q n, pge p q -> vge (Ifptr p) (Sgn q n).

Hint Constructors vge : va.

Lemma vge_top: forall v, vge Vtop v.
Proof.
  destruct v; constructor; constructor.
Qed.

Hint Resolve vge_top : va.

Lemma vge_refl: forall v, vge v v.
Proof.
  destruct v; auto with va.
Qed.

Lemma vge_trans: forall u v, vge u v -> forall w, vge v w -> vge u w.
Proof.
  induction 1; intros w V; inv V; eauto using pge_trans with va.
Qed.

Lemma vmatch_ge:
  forall v x y, vge x y -> vmatch v y -> vmatch v x.
Proof.
  induction 1; intros V; inv V; eauto using pmatch_ge with va.
Qed.

(** Least upper bound *)

Definition vlub (v w: aval) : aval :=
  match v, w with
  | Vbot, _ => w
  | _, Vbot => v
  | I i1, I i2 =>
      if Int.eq i1 i2 then v else
      if Int.lt i1 Int.zero || Int.lt i2 Int.zero
      then sgn Pbot (Z.max (ssize i1) (ssize i2))
      else uns Pbot (Z.max (usize i1) (usize i2))
  | I i, Uns p n | Uns p n, I i =>
      if Int.lt i Int.zero
      then sgn p (Z.max (ssize i) (n + 1))
      else uns p (Z.max (usize i) n)
  | I i, Sgn p n | Sgn p n, I i =>
      sgn p (Z.max (ssize i) n)
  | I i, (Ptr p | Ifptr p) | (Ptr p | Ifptr p), I i =>
      if va_strict tt || Int.eq i Int.zero then Ifptr p else Vtop
  | Uns p1 n1, Uns p2 n2 => Uns (plub p1 p2) (Z.max n1 n2)
  | Uns p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (Z.max (n1 + 1) n2)
  | Sgn p1 n1, Uns p2 n2 => sgn (plub p1 p2) (Z.max n1 (n2 + 1))
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (Z.max n1 n2)
  | F f1, F f2 =>
      if Float.eq_dec f1 f2 then v else ntop
  | FS f1, FS f2 =>
      if Float32.eq_dec f1 f2 then v else ntop
  | L i1, L i2 =>
      if Int64.eq i1 i2 then v else ntop
  | Ptr p1, Ptr p2 => Ptr(plub p1 p2)
  | Ptr p1, Ifptr p2 => Ifptr(plub p1 p2)
  | Ifptr p1, Ptr p2 => Ifptr(plub p1 p2)
  | Ifptr p1, Ifptr p2 => Ifptr(plub p1 p2)
  | (Ptr p1 | Ifptr p1), (Uns p2 _ | Sgn p2 _) => Ifptr(plub p1 p2)
  | (Uns p1 _ | Sgn p1 _), (Ptr p2 | Ifptr p2) => Ifptr(plub p1 p2)
  | _, (Ptr p | Ifptr p) | (Ptr p | Ifptr p), _ => if va_strict tt then Ifptr p else Vtop
  | _, _ => Vtop
  end.

Lemma vlub_comm:
  forall v w, vlub v w = vlub w v.
Proof.
  intros. unfold vlub; destruct v; destruct w; auto.
- rewrite Int.eq_sym. predSpec Int.eq Int.eq_spec n0 n.
  congruence.
  rewrite orb_comm.
  destruct (Int.lt n0 Int.zero || Int.lt n Int.zero); f_equal; apply Z.max_comm.
- f_equal. apply plub_comm. apply Z.max_comm.
- f_equal. apply plub_comm. apply Z.max_comm.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
- f_equal. apply plub_comm. apply Z.max_comm.
- f_equal. apply plub_comm. apply Z.max_comm.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
- rewrite Int64.eq_sym. predSpec Int64.eq Int64.eq_spec n0 n; congruence.
- rewrite dec_eq_sym. destruct (Float.eq_dec f0 f). congruence. auto.
- rewrite dec_eq_sym. destruct (Float32.eq_dec f0 f). congruence. auto.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
- f_equal; apply plub_comm.
Qed.

Lemma vge_uns_uns': forall p n, vge (uns p n) (Uns p n).
Proof.
  unfold uns; intros.
  destruct (zle n 1). auto with va.
  destruct (zle n 7). auto with va.
  destruct (zle n 8). auto with va.
  destruct (zle n 15). auto with va.
  destruct (zle n 16); auto with va.
Qed.

Lemma vge_uns_i': forall p n i, 0 <= n -> is_uns n i -> vge (uns p n) (I i).
Proof.
  intros. apply vge_trans with (Uns p n). apply vge_uns_uns'. auto with va.
Qed.

Lemma vge_sgn_sgn': forall p n, vge (sgn p n) (Sgn p n).
Proof.
  unfold sgn; intros.
  destruct (zle n 8). auto with va.
  destruct (zle n 16); auto with va.
Qed.

Lemma vge_sgn_i': forall p n i, 0 < n -> is_sgn n i -> vge (sgn p n) (I i).
Proof.
  intros. apply vge_trans with (Sgn p n). apply vge_sgn_sgn'. auto with va.
Qed.

Hint Resolve vge_uns_uns' vge_uns_i' vge_sgn_sgn' vge_sgn_i' : va.

Lemma usize_pos: forall n, 0 <= usize n.
Proof.
  unfold usize; intros. generalize (Int.size_range n); omega.
Qed.

Lemma ssize_pos: forall n, 0 < ssize n.
Proof.
  unfold ssize; intros.
  generalize (Int.size_range (if Int.lt n Int.zero then Int.not n else n)); omega.
Qed.

Lemma vge_lub_l:
  forall x y, vge (vlub x y) x.
Proof.
  assert (IFSTRICT: forall (cond: bool) x1 x2 y, vge x1 y -> vge x2 y -> vge (if cond then x1 else x2) y).
  { destruct cond; auto with va. }
  unfold vlub; destruct x, y; eauto using pge_lub_l with va.
- predSpec Int.eq Int.eq_spec n n0. auto with va.
  destruct (Int.lt n Int.zero || Int.lt n0 Int.zero).
  apply vge_sgn_i'. generalize (ssize_pos n); xomega. eauto with va.
  apply vge_uns_i'. generalize (usize_pos n); xomega. eauto with va.
- destruct (Int.lt n Int.zero).
  apply vge_sgn_i'. generalize (ssize_pos n); xomega. eauto with va.
  apply vge_uns_i'. generalize (usize_pos n); xomega. eauto with va.
- apply vge_sgn_i'. generalize (ssize_pos n); xomega. eauto with va.
- destruct (Int.lt n0 Int.zero).
  eapply vge_trans. apply vge_sgn_sgn'.
  apply vge_trans with (Sgn p (n + 1)); eauto with va.
  eapply vge_trans. apply vge_uns_uns'. eauto with va.
- eapply vge_trans. apply vge_sgn_sgn'.
  apply vge_trans with (Sgn p (n + 1)); eauto using pge_lub_l with va.
- eapply vge_trans. apply vge_sgn_sgn'. eauto with va.
- eapply vge_trans. apply vge_sgn_sgn'. eauto using pge_lub_l with va.
- eapply vge_trans. apply vge_sgn_sgn'. eauto using pge_lub_l with va.
- destruct (Int64.eq n n0); constructor.
- destruct (Float.eq_dec f f0); constructor.
- destruct (Float32.eq_dec f f0); constructor.
Qed.

Lemma vge_lub_r:
  forall x y, vge (vlub x y) y.
Proof.
  intros. rewrite vlub_comm. apply vge_lub_l.
Qed.

Lemma vmatch_lub_l:
  forall v x y, vmatch v x -> vmatch v (vlub x y).
Proof.
  intros. eapply vmatch_ge; eauto. apply vge_lub_l.
Qed.

Lemma vmatch_lub_r:
  forall v x y, vmatch v y -> vmatch v (vlub x y).
Proof.
  intros. rewrite vlub_comm. apply vmatch_lub_l; auto.
Qed.

(** In the CompCert semantics, a memory load or store succeeds only
  if the address is a pointer value.  Hence, in strict mode,
  [aptr_of_aval x] returns [Pbot] (no pointer value) if [x]
  denotes a number or [Vundef].  However, in real code, memory
  addresses are sometimes synthesized from integers, e.g. an absolute
  address for a hardware device.  It is a reasonable assumption
  that these absolute addresses do not point within the stack block,
  however.  Therefore, in relaxed mode, [aptr_of_aval x] returns
  [Nonstack] (any pointer outside the stack) when [x] denotes a number. *)

Definition aptr_of_aval (v: aval) : aptr :=
  match v with
  | Ptr p => p
  | Ifptr p => p
  | _ => if va_strict tt then Pbot else Nonstack
  end.

Lemma match_aptr_of_aval:
  forall b ofs av,
  vmatch (Vptr b ofs) av -> pmatch b ofs (aptr_of_aval av).
Proof.
  unfold aptr_of_aval; intros. inv H; auto.
Qed.

Definition vplub (v: aval) (p: aptr) : aptr :=
  match v with
  | Ptr q => plub q p
  | Ifptr q => plub q p
  | _ => p
  end.

Lemma vmatch_vplub_l:
  forall v x p, vmatch v x -> vmatch v (Ifptr (vplub x p)).
Proof.
  intros. unfold vplub; inv H; auto with va; constructor; eapply pmatch_lub_l; eauto.
Qed.

Lemma pmatch_vplub:
  forall b ofs x p, pmatch b ofs p -> pmatch b ofs (vplub x p).
Proof.
  intros.
  assert (DFL: pmatch b ofs (if va_strict tt then p else Ptop)).
  { destruct (va_strict tt); auto. eapply pmatch_top'; eauto. }
  unfold vplub; destruct x; auto; apply pmatch_lub_r; auto.
Qed.

Lemma vmatch_vplub_r:
  forall v x p, vmatch v (Ifptr p) -> vmatch v (Ifptr (vplub x p)).
Proof.
  intros. apply vmatch_ifptr; intros; subst v. inv H. apply pmatch_vplub; auto.
Qed.

(** Inclusion *)

Definition vpincl (v: aval) (p: aptr) : bool :=
  match v with
  | Ptr q | Ifptr q | Uns q _ | Sgn q _ => pincl q p
  | _ => true
  end.

Lemma vpincl_ge:
  forall x p, vpincl x p = true -> vge (Ifptr p) x.
Proof.
  unfold vpincl; intros. destruct x; constructor; apply pincl_ge; auto.
Qed.

Lemma vpincl_sound:
  forall v x p, vpincl x p = true -> vmatch v x -> vmatch v (Ifptr p).
Proof.
  intros. apply vmatch_ge with x; auto. apply vpincl_ge; auto.
Qed.

Definition vincl (v w: aval) : bool :=
  match v, w with
  | Vbot, _ => true
  | I i, I j => Int.eq_dec i j
  | I i, Uns p n => Int.eq_dec (Int.zero_ext n i) i && zle 0 n
  | I i, Sgn p n => Int.eq_dec (Int.sign_ext n i) i && zlt 0 n
  | Uns p n, Uns q m => zle n m && pincl p q
  | Uns p n, Sgn q m => zlt n m && pincl p q
  | Sgn p n, Sgn q m => zle n m && pincl p q
  | L i, L j => Int64.eq_dec i j
  | F i, F j => Float.eq_dec i j
  | FS i, FS j => Float32.eq_dec i j
  | Ptr p, Ptr q => pincl p q
  | (Ptr p | Ifptr p | Uns p _ | Sgn p _), Ifptr q => pincl p q
  | _, Ifptr _ => true
  | _, _ => false
  end.

Lemma vincl_ge: forall v w, vincl v w = true -> vge w v.
Proof.
  unfold vincl; destruct v; destruct w;
  intros; try discriminate; try InvBooleans; try subst; auto using pincl_ge with va.
- constructor; auto. rewrite is_uns_zero_ext; auto.
- constructor; auto. rewrite is_sgn_sign_ext; auto.
Qed.

(** Loading constants *)

Definition genv_match (ge: genv) : Prop :=
  (forall id b, Genv.find_symbol ge id = Some b <-> bc b = BCglob id)
/\(forall b, Plt b (Genv.genv_next ge) -> bc b <> BCinvalid /\ bc b <> BCstack).

Lemma symbol_address_sound:
  forall ge id ofs,
  genv_match ge ->
  vmatch (Genv.symbol_address ge id ofs) (Ptr (Gl id ofs)).
Proof.
  intros. unfold Genv.symbol_address. destruct (Genv.find_symbol ge id) as [b|] eqn:F.
  constructor. constructor. apply H; auto.
  constructor.
Qed.

Lemma vmatch_ptr_gl:
  forall ge v id ofs,
  genv_match ge ->
  vmatch v (Ptr (Gl id ofs)) ->
  Val.lessdef v (Genv.symbol_address ge id ofs).
Proof.
  intros. unfold Genv.symbol_address. inv H0.
- inv H3. replace (Genv.find_symbol ge id) with (Some b). constructor.
  symmetry. apply H; auto.
- constructor.
Qed.

Lemma vmatch_ptr_stk:
  forall v ofs sp,
  vmatch v (Ptr(Stk ofs)) ->
  bc sp = BCstack ->
  Val.lessdef v (Vptr sp ofs).
Proof.
  intros. inv H.
- inv H3. replace b with sp by (eapply bc_stack; eauto). constructor.
- constructor.
Qed.

(** Generic operations that just do constant propagation. *)

Definition unop_int (sem: int -> int) (x: aval) :=
  match x with I n => I (sem n) | _ => ntop1 x end.

Lemma unop_int_sound:
  forall sem v x,
  vmatch v x ->
  vmatch (match v with Vint i => Vint(sem i) | _ => Vundef end) (unop_int sem x).
Proof.
  intros. unfold unop_int; inv H; auto with va.
Qed.

Definition binop_int (sem: int -> int -> int) (x y: aval) :=
  match x, y with I n, I m => I (sem n m) | _, _ => ntop2 x y end.

Lemma binop_int_sound:
  forall sem v x w y,
  vmatch v x -> vmatch w y ->
  vmatch (match v, w with Vint i, Vint j => Vint(sem i j) | _, _ => Vundef end) (binop_int sem x y).
Proof.
  intros. unfold binop_int; inv H; auto with va; inv H0; auto with va.
Qed.

Definition unop_long (sem: int64 -> int64) (x: aval) :=
  match x with L n => L (sem n) | _ => ntop1 x end.

Lemma unop_long_sound:
  forall sem v x,
  vmatch v x ->
  vmatch (match v with Vlong i => Vlong(sem i) | _ => Vundef end) (unop_long sem x).
Proof.
  intros. unfold unop_long; inv H; auto with va.
Qed.

Definition binop_long (sem: int64 -> int64 -> int64) (x y: aval) :=
  match x, y with L n, L m => L (sem n m) | _, _ => ntop2 x y end.

Lemma binop_long_sound:
  forall sem v x w y,
  vmatch v x -> vmatch w y ->
  vmatch (match v, w with Vlong i, Vlong j => Vlong(sem i j) | _, _ => Vundef end) (binop_long sem x y).
Proof.
  intros. unfold binop_long; inv H; auto with va; inv H0; auto with va.
Qed.

Definition unop_float (sem: float -> float) (x: aval) :=
  match x with F n => F (sem n) | _ => ntop1 x end.

Lemma unop_float_sound:
  forall sem v x,
  vmatch v x ->
  vmatch (match v with Vfloat i => Vfloat(sem i) | _ => Vundef end) (unop_float sem x).
Proof.
  intros. unfold unop_float; inv H; auto with va.
Qed.

Definition binop_float (sem: float -> float -> float) (x y: aval) :=
  match x, y with F n, F m => F (sem n m) | _, _ => ntop2 x y end.

Lemma binop_float_sound:
  forall sem v x w y,
  vmatch v x -> vmatch w y ->
  vmatch (match v, w with Vfloat i, Vfloat j => Vfloat(sem i j) | _, _ => Vundef end) (binop_float sem x y).
Proof.
  intros. unfold binop_float; inv H; auto with va; inv H0; auto with va.
Qed.

Definition unop_single (sem: float32 -> float32) (x: aval) :=
  match x with FS n => FS (sem n) | _ => ntop1 x end.

Lemma unop_single_sound:
  forall sem v x,
  vmatch v x ->
  vmatch (match v with Vsingle i => Vsingle(sem i) | _ => Vundef end) (unop_single sem x).
Proof.
  intros. unfold unop_single; inv H; auto with va.
Qed.

Definition binop_single (sem: float32 -> float32 -> float32) (x y: aval) :=
  match x, y with FS n, FS m => FS (sem n m) | _, _ => ntop2 x y end.

Lemma binop_single_sound:
  forall sem v x w y,
  vmatch v x -> vmatch w y ->
  vmatch (match v, w with Vsingle i, Vsingle j => Vsingle(sem i j) | _, _ => Vundef end) (binop_single sem x y).
Proof.
  intros. unfold binop_single; inv H; auto with va; inv H0; auto with va.
Qed.

(** Logical operations *)

Definition shl (v w: aval) :=
  match w with
  | I amount =>
      if Int.ltu amount Int.iwordsize then
        match v with
        | I i => I (Int.shl i amount)
        | Uns p n => uns p (n + Int.unsigned amount)
        | Sgn p n => sgn p (n + Int.unsigned amount)
        | _ => ntop1 v
        end
      else ntop1 v
  | _ => ntop1 v
  end.

Lemma shl_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.shl v w) (shl x y).
Proof.
  intros.
  assert (DEFAULT: vmatch (Val.shl v w) (ntop1 x)).
  {
    destruct v; destruct w; simpl; try constructor.
    destruct (Int.ltu i0 Int.iwordsize); constructor.
  }
  destruct y; auto. simpl. inv H0. unfold Val.shl.
  destruct (Int.ltu n Int.iwordsize) eqn:LTU; auto.
  exploit Int.ltu_inv; eauto. intros RANGE.
  inv H; auto with va.
- apply vmatch_uns'. red; intros. rewrite Int.bits_shl by omega.
  destruct (zlt m (Int.unsigned n)). auto. apply H1; xomega.
- apply vmatch_sgn'. red; intros. zify.
  rewrite ! Int.bits_shl by omega.
  rewrite ! zlt_false by omega.
  rewrite H1 by omega. symmetry. rewrite H1 by omega. auto.
- destruct v; constructor.
Qed.

Definition shru (v w: aval) :=
  match w with
  | I amount =>
      if Int.ltu amount Int.iwordsize then
        match v with
        | I i => I (Int.shru i amount)
        | Uns p n => uns p (n - Int.unsigned amount)
        | _ => uns (provenance v) (Int.zwordsize - Int.unsigned amount)
        end
      else ntop1 v
  | _ => ntop1 v
  end.

Lemma shru_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.shru v w) (shru x y).
Proof.
  intros.
  assert (DEFAULT: vmatch (Val.shru v w) (ntop1 x)).
  {
    destruct v; destruct w; simpl; try constructor.
    destruct (Int.ltu i0 Int.iwordsize); constructor.
  }
  destruct y; auto. inv H0. unfold shru, Val.shru.
  destruct (Int.ltu n Int.iwordsize) eqn:LTU; auto.
  exploit Int.ltu_inv; eauto. intros RANGE. change (Int.unsigned Int.iwordsize) with Int.zwordsize in RANGE.
  assert (DEFAULT2: forall i, vmatch (Vint (Int.shru i n)) (uns (provenance x) (Int.zwordsize - Int.unsigned n))).
  {
    intros. apply vmatch_uns. red; intros.
    rewrite Int.bits_shru by omega. apply zlt_false. omega.
  }
  inv H; auto with va.
- apply vmatch_uns'. red; intros. zify.
  rewrite Int.bits_shru by omega.
  destruct (zlt (m + Int.unsigned n) Int.zwordsize); auto.
  apply H1; omega.
- destruct v; constructor.
Qed.

Definition shr (v w: aval) :=
  match w with
  | I amount =>
      if Int.ltu amount Int.iwordsize then
        match v with
        | I i => I (Int.shr i amount)
        | Uns p n => sgn p (n + 1 - Int.unsigned amount)
        | Sgn p n => sgn p (n - Int.unsigned amount)
        | _ => sgn (provenance v) (Int.zwordsize - Int.unsigned amount)
        end
      else ntop1 v
  | _ => ntop1 v
  end.

Lemma shr_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.shr v w) (shr x y).
Proof.
  intros.
  assert (DEFAULT: vmatch (Val.shr v w) (ntop1 x)).
  {
    destruct v; destruct w; simpl; try constructor.
    destruct (Int.ltu i0 Int.iwordsize); constructor.
  }
  destruct y; auto. inv H0. unfold shr, Val.shr.
  destruct (Int.ltu n Int.iwordsize) eqn:LTU; auto.
  exploit Int.ltu_inv; eauto. intros RANGE. change (Int.unsigned Int.iwordsize) with Int.zwordsize in RANGE.
  assert (DEFAULT2: forall i, vmatch (Vint (Int.shr i n)) (sgn (provenance x) (Int.zwordsize - Int.unsigned n))).
  {
    intros. apply vmatch_sgn. red; intros.
    rewrite ! Int.bits_shr by omega. f_equal.
    destruct (zlt (m + Int.unsigned n) Int.zwordsize);
    destruct (zlt (Int.zwordsize - 1 + Int.unsigned n) Int.zwordsize);
    omega.
  }
  assert (SGN: forall q i p, is_sgn p i -> 0 < p -> vmatch (Vint (Int.shr i n)) (sgn q (p - Int.unsigned n))).
  {
    intros. apply vmatch_sgn'. red; intros. zify.
    rewrite ! Int.bits_shr by omega.
    transitivity (Int.testbit i (Int.zwordsize - 1)).
    destruct (zlt (m + Int.unsigned n) Int.zwordsize).
    apply H0; omega.
    auto.
    symmetry.
    destruct (zlt (Int.zwordsize - 1 + Int.unsigned n) Int.zwordsize).
    apply H0; omega.
    auto.
  }
  inv H; eauto with va.
- destruct v; constructor.
Qed.

Definition and (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.and i1 i2)
  | I i, Uns p n | Uns p n, I i => uns p (Z.min n (usize i))
  | I i, x | x, I i => uns (provenance x) (usize i)
  | Uns p1 n1, Uns p2 n2 => uns (plub p1 p2) (Z.min n1 n2)
  | Uns p n, _ => uns (plub p (provenance w)) n
  | _, Uns p n => uns (plub (provenance v) p) n
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (Z.max n1 n2)
  | _, _ => ntop2 v w
  end.

Lemma and_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.and v w) (and x y).
Proof.
  assert (UNS_l: forall i j n, is_uns n i -> is_uns n (Int.and i j)).
  {
    intros; red; intros. rewrite Int.bits_and by auto. rewrite (H m) by auto.
    apply andb_false_l.
  }
  assert (UNS_r: forall i j n, is_uns n i -> is_uns n (Int.and j i)).
  {
    intros. rewrite Int.and_commut. eauto.
  }
  assert (UNS: forall i j n m, is_uns n i -> is_uns m j -> is_uns (Z.min n m) (Int.and i j)).
  {
    intros. apply Z.min_case; auto.
  }
  assert (SGN: forall i j n m, is_sgn n i -> is_sgn m j -> is_sgn (Z.max n m) (Int.and i j)).
  {
    intros; red; intros. rewrite ! Int.bits_and by auto with va.
    rewrite H by auto with va. rewrite H0 by auto with va. auto.
  }
  intros. unfold and, Val.and; inv H; eauto with va; inv H0; eauto with va.
Qed.

Definition or (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.or i1 i2)
  | I i, Uns p n | Uns p n, I i => uns p (Z.max n (usize i))
  | Uns p1 n1, Uns p2 n2 => uns (plub p1 p2) (Z.max n1 n2)
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (Z.max n1 n2)
  | _, _ => ntop2 v w
  end.

Lemma or_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.or v w) (or x y).
Proof.
  assert (UNS: forall i j n m, is_uns n i -> is_uns m j -> is_uns (Z.max n m) (Int.or i j)).
  {
    intros; red; intros. rewrite Int.bits_or by auto.
    rewrite H by xomega. rewrite H0 by xomega. auto.
  }
  assert (SGN: forall i j n m, is_sgn n i -> is_sgn m j -> is_sgn (Z.max n m) (Int.or i j)).
  {
    intros; red; intros. rewrite ! Int.bits_or by xomega.
    rewrite H by xomega. rewrite H0 by xomega. auto.
  }
  intros. unfold or, Val.or; inv H; eauto with va; inv H0; eauto with va.
Qed.

Definition xor (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.xor i1 i2)
  | I i, Uns p n | Uns p n, I i => uns p (Z.max n (usize i))
  | Uns p1 n1, Uns p2 n2 => uns (plub p1 p2) (Z.max n1 n2)
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (Z.max n1 n2)
  | _, _ => ntop2 v w
  end.

Lemma xor_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.xor v w) (xor x y).
Proof.
  assert (UNS: forall i j n m, is_uns n i -> is_uns m j -> is_uns (Z.max n m) (Int.xor i j)).
  {
    intros; red; intros. rewrite Int.bits_xor by auto.
    rewrite H by xomega. rewrite H0 by xomega. auto.
  }
  assert (SGN: forall i j n m, is_sgn n i -> is_sgn m j -> is_sgn (Z.max n m) (Int.xor i j)).
  {
    intros; red; intros. rewrite ! Int.bits_xor by xomega.
    rewrite H by xomega. rewrite H0 by xomega. auto.
  }
  intros. unfold xor, Val.xor; inv H; eauto with va; inv H0; eauto with va.
Qed.

Definition notint (v: aval) :=
  match v with
  | I i => I (Int.not i)
  | Uns p n => sgn p (n + 1)
  | Sgn p n => Sgn p n
  | _ => ntop1 v
  end.

Lemma notint_sound:
  forall v x, vmatch v x -> vmatch (Val.notint v) (notint x).
Proof.
  assert (SGN: forall n i, is_sgn n i -> is_sgn n (Int.not i)).
  {
    intros; red; intros. rewrite ! Int.bits_not by omega.
    f_equal. apply H; auto.
  }
  intros. unfold Val.notint, notint; inv H; eauto with va.
Qed.

Definition rol (x y: aval) :=
  match y, x with
  | I j, I i => I(Int.rol i j)
  | I j, Uns p n => uns p (n + Int.unsigned j)
  | I j, Sgn p n => if zlt n Int.zwordsize then sgn p (n + Int.unsigned j) else ntop1 x
  | _, _ => ntop1 x
  end.

Lemma rol_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.rol v w) (rol x y).
Proof.
  intros.
  assert (DEFAULT: forall p, vmatch (Val.rol v w) (Ifptr p)).
  {
    destruct v; destruct w; simpl; constructor.
  }
  unfold rol; destruct y; try apply DEFAULT; auto. inv H0. unfold Val.rol.
  inv H; auto with va.
- apply vmatch_uns. red; intros. rewrite Int.bits_rol by auto.
  generalize (Int.unsigned_range n); intros.
  rewrite Zmod_small by omega.
  apply H1. omega. omega.
- destruct (zlt n0 Int.zwordsize); auto with va.
  apply vmatch_sgn. red; intros. rewrite ! Int.bits_rol by omega.
  generalize (Int.unsigned_range n); intros.
  rewrite ! Zmod_small by omega.
  rewrite H1 by omega. symmetry. rewrite H1 by omega. auto.
- destruct (zlt n0 Int.zwordsize); auto with va.
Qed.

Definition ror (x y: aval) :=
  match y, x with
  | I j, I i => I(Int.ror i j)
  | _, _ => ntop1 x
  end.

Lemma ror_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.ror v w) (ror x y).
Proof.
  intros.
  assert (DEFAULT: forall p, vmatch (Val.ror v w) (Ifptr p)).
  {
    destruct v; destruct w; simpl; constructor.
  }
  unfold ror; destruct y; try apply DEFAULT; auto. inv H0. unfold Val.ror.
  inv H; auto with va.
Qed.

Definition rolm (x: aval) (amount mask: int) :=
  and (rol x (I amount)) (I mask).

Lemma rolm_sound:
  forall v x amount mask,
  vmatch v x -> vmatch (Val.rolm v amount mask) (rolm x amount mask).
Proof.
  intros.
  replace (Val.rolm v amount mask) with (Val.and (Val.rol v (Vint amount)) (Vint mask)).
  apply and_sound. apply rol_sound. auto. constructor. constructor.
  destruct v; auto.
Qed.

(** Integer arithmetic operations *)

Definition neg := unop_int Int.neg.

Lemma neg_sound:
  forall v x, vmatch v x -> vmatch (Val.neg v) (neg x).
Proof (unop_int_sound Int.neg).

Definition add (x y: aval) :=
  match x, y with
  | I i, I j => I (Int.add i j)
  | Ptr p, I i | I i, Ptr p => Ptr (if Archi.ptr64 then poffset p else padd p (Ptrofs.of_int i))
  | Ptr p, _   | _, Ptr p   => Ptr (poffset p)
  | Ifptr p, I i | I i, Ifptr p => Ifptr (if Archi.ptr64 then poffset p else padd p (Ptrofs.of_int i))
  | Ifptr p, Ifptr q => Ifptr (plub (poffset p) (poffset q))
  | Ifptr p, _ | _, Ifptr p => Ifptr (poffset p)
  | _, _ => ntop2 x y
  end.

Lemma add_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.add v w) (add x y).
Proof.
  intros. unfold Val.add, add. destruct Archi.ptr64.
- inv H; inv H0; constructor.
- inv H; inv H0; constructor;
  ((apply padd_sound; assumption) || (eapply poffset_sound; eassumption) || idtac).
  apply pmatch_lub_r. eapply poffset_sound; eauto.
  apply pmatch_lub_l. eapply poffset_sound; eauto.
Qed.

Definition sub (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.sub i1 i2)
  | Ptr p, I i => if Archi.ptr64 then Ifptr (poffset p) else Ptr (psub p (Ptrofs.of_int i))
  | Ptr p, _   => Ifptr (poffset p)
  | Ifptr p, I i => if Archi.ptr64 then Ifptr (plub (poffset p) (provenance w)) else Ifptr (psub p (Ptrofs.of_int i))
  | Ifptr p, _ => Ifptr (plub (poffset p) (provenance w))
  | _, _ => ntop2 v w
  end.

Lemma sub_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.sub v w) (sub x y).
Proof.
  intros. unfold Val.sub, sub. destruct Archi.ptr64.
- inv H; inv H0; eauto with va.
- inv H; inv H0; try (destruct (eq_block b b0)); eauto using psub_sound, poffset_sound, pmatch_lub_l with va.
Qed.

Definition mul := binop_int Int.mul.

Lemma mul_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mul v w) (mul x y).
Proof (binop_int_sound Int.mul).

Definition mulhs := binop_int Int.mulhs.

Lemma mulhs_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mulhs v w) (mulhs x y).
Proof (binop_int_sound Int.mulhs).

Definition mulhu := binop_int Int.mulhu.

Lemma mulhu_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mulhu v w) (mulhu x y).
Proof (binop_int_sound Int.mulhu).

Definition divs (v w: aval) :=
  match w, v with
  | I i2, I i1 =>
      if Int.eq i2 Int.zero
      || Int.eq i1 (Int.repr Int.min_signed) && Int.eq i2 Int.mone
      then if va_strict tt then Vbot else ntop
      else I (Int.divs i1 i2)
  | _, _ => ntop2 v w
  end.

Lemma divs_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.divs v w = Some u -> vmatch u (divs x y).
Proof.
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int.eq i0 Int.zero
         || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone) eqn:E; inv H1.
  inv H; inv H0; auto with va. simpl. rewrite E. constructor.
Qed.

Definition divu (v w: aval) :=
  match w, v with
  | I i2, I i1 =>
      if Int.eq i2 Int.zero
       then if va_strict tt then Vbot else ntop
      else I (Int.divu i1 i2)
  | _, _ => ntop2 v w
  end.

Lemma divu_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.divu v w = Some u -> vmatch u (divu x y).
Proof.
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int.eq i0 Int.zero) eqn:E; inv H1.
  inv H; inv H0; auto with va. simpl. rewrite E. constructor.
Qed.

Definition mods (v w: aval) :=
  match w, v with
  | I i2, I i1 =>
      if Int.eq i2 Int.zero
      || Int.eq i1 (Int.repr Int.min_signed) && Int.eq i2 Int.mone
      then if va_strict tt then Vbot else ntop
      else I (Int.mods i1 i2)
  | _, _ => ntop2 v w
  end.

Lemma mods_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.mods v w = Some u -> vmatch u (mods x y).
Proof.
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int.eq i0 Int.zero
         || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone) eqn:E; inv H1.
  inv H; inv H0; auto with va. simpl. rewrite E. constructor.
Qed.

Definition modu (v w: aval) :=
  match w, v with
  | I i2, I i1 =>
      if Int.eq i2 Int.zero
      then if va_strict tt then Vbot else ntop
      else I (Int.modu i1 i2)
  | I i2, _ => uns (provenance v) (usize i2)
  | _, _ => ntop2 v w
  end.

Lemma modu_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.modu v w = Some u -> vmatch u (modu x y).
Proof.
  assert (UNS: forall i j, j <> Int.zero -> is_uns (usize j) (Int.modu i j)).
  {
    intros. apply is_uns_mon with (usize (Int.modu i j)); auto with va.
    unfold usize, Int.size. apply Int.Zsize_monotone.
    generalize (Int.unsigned_range_2 j); intros RANGE.
    assert (Int.unsigned j <> 0).
    { red; intros; elim H. rewrite <- (Int.repr_unsigned j). rewrite H0. auto. }
    exploit (Z_mod_lt (Int.unsigned i) (Int.unsigned j)). omega. intros MOD.
    unfold Int.modu. rewrite Int.unsigned_repr. omega. omega.
  }
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int.eq i0 Int.zero) eqn:Z; inv H1.
  assert (i0 <> Int.zero) by (generalize (Int.eq_spec i0 Int.zero); rewrite Z; auto).
  unfold modu. inv H; inv H0; auto with va. rewrite Z. constructor.
Qed.

Definition shrx (v w: aval) :=
  match v, w with
  | I i, I j => if Int.ltu j (Int.repr 31) then I(Int.shrx i j) else ntop
  | _, _ => ntop1 v
  end.

Lemma shrx_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.shrx v w = Some u -> vmatch u (shrx x y).
Proof.
  intros.
  destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int.ltu i0 (Int.repr 31)) eqn:LTU; inv H1.
  unfold shrx; inv H; auto with va; inv H0; auto with va.
  rewrite LTU; auto with va.
Qed.

(** 64-bit integer operations *)

Definition shift_long (sem: int64 -> int -> int64) (v w: aval) :=
  match w with
  | I amount =>
      if Int.ltu amount Int64.iwordsize' then
        match v with
        | L i => L (sem i amount)
        | _ => ntop1 v
        end
      else ntop1 v
  | _ => ntop1 v
  end.

Lemma shift_long_sound:
  forall sem v w x y,
  vmatch v x -> vmatch w y ->
  vmatch (match v, w with
          | Vlong i, Vint j => if Int.ltu j Int64.iwordsize'
                               then Vlong (sem i j) else Vundef
          | _, _ => Vundef end)
         (shift_long sem x y).
Proof.
  intros.
  assert (DEFAULT:
    vmatch (match v, w with
            | Vlong i, Vint j => if Int.ltu j Int64.iwordsize'
                                 then Vlong (sem i j) else Vundef
            | _, _ => Vundef end)
           (ntop1 x)).
  { destruct v; try constructor; destruct w; try constructor.
    destruct (Int.ltu i0 Int64.iwordsize'); constructor. }
  unfold shift_long. destruct y; auto.
  destruct (Int.ltu n Int64.iwordsize') eqn:LT; auto.
  destruct x; auto.
  inv H; inv H0. rewrite LT. constructor.
Qed.

Definition shll := shift_long Int64.shl'.

Lemma shll_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.shll v w) (shll x y).
Proof (shift_long_sound Int64.shl').

Definition shrl := shift_long Int64.shr'.

Lemma shrl_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.shrl v w) (shrl x y).
Proof (shift_long_sound Int64.shr').

Definition shrlu := shift_long Int64.shru'.

Lemma shrlu_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.shrlu v w) (shrlu x y).
Proof (shift_long_sound Int64.shru').

Definition andl := binop_long Int64.and.

Lemma andl_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.andl v w) (andl x y).
Proof (binop_long_sound Int64.and).

Definition orl := binop_long Int64.or.

Lemma orl_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.orl v w) (orl x y).
Proof (binop_long_sound Int64.or).

Definition xorl := binop_long Int64.xor.

Lemma xorl_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.xorl v w) (xorl x y).
Proof (binop_long_sound Int64.xor).

Definition notl := unop_long Int64.not.

Lemma notl_sound:
  forall v x, vmatch v x -> vmatch (Val.notl v) (notl x).
Proof (unop_long_sound Int64.not).

Definition rotate_long (sem: int64 -> int64 -> int64) (v w: aval) :=
  match v, w with
  | L i, I amount => L (sem i (Int64.repr (Int.unsigned amount)))
  | _, _ => ntop1 v
  end.

Lemma rotate_long_sound:
  forall sem v w x y,
  vmatch v x -> vmatch w y ->
  vmatch (match v, w with
          | Vlong i, Vint j => Vlong (sem i (Int64.repr (Int.unsigned j)))
          | _, _ => Vundef end)
         (rotate_long sem x y).
Proof.
  intros.
  assert (DEFAULT:
    vmatch (match v, w with
            | Vlong i, Vint j => Vlong (sem i (Int64.repr (Int.unsigned j)))
            | _, _ => Vundef end)
           (ntop1 x)).
  { destruct v; try constructor. destruct w; constructor. }
  unfold rotate_long. destruct x; auto. destruct y; auto. inv H; inv H0. constructor.
Qed.

Definition roll := rotate_long Int64.rol.

Lemma roll_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.roll v w) (roll x y).
Proof (rotate_long_sound Int64.rol).

Definition rorl := rotate_long Int64.ror.

Lemma rorl_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.rorl v w) (rorl x y).
Proof (rotate_long_sound Int64.ror).

Definition negl := unop_long Int64.neg.

Lemma negl_sound:
  forall v x, vmatch v x -> vmatch (Val.negl v) (negl x).
Proof (unop_long_sound Int64.neg).

Definition addl (x y: aval) :=
  match x, y with
  | L i, L j => L (Int64.add i j)
  | Ptr p, L i | L i, Ptr p => Ptr (if Archi.ptr64 then padd p (Ptrofs.of_int64 i) else poffset p)
  | Ptr p, _   | _, Ptr p   => Ptr (poffset p)
  | Ifptr p, L i | L i, Ifptr p => Ifptr (if Archi.ptr64 then padd p (Ptrofs.of_int64 i) else poffset p)
  | Ifptr p, Ifptr q => Ifptr (plub (poffset p) (poffset q))
  | Ifptr p, _ | _, Ifptr p => Ifptr (poffset p)
  | _, _ => ntop2 x y
  end.

Lemma addl_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.addl v w) (addl x y).
Proof.
  intros. unfold Val.addl, addl. destruct Archi.ptr64.
- inv H; inv H0; constructor;
  ((apply padd_sound; assumption) || (eapply poffset_sound; eassumption) || idtac).
  apply pmatch_lub_r. eapply poffset_sound; eauto.
  apply pmatch_lub_l. eapply poffset_sound; eauto.
- inv H; inv H0; constructor.
Qed.

Definition subl (v w: aval) :=
  match v, w with
  | L i1, L i2 => L (Int64.sub i1 i2)
  | Ptr p, L i => if Archi.ptr64 then Ptr (psub p (Ptrofs.of_int64 i)) else Ifptr (poffset p)
  | Ptr p, _   => Ifptr (poffset p)
  | Ifptr p, L i => if Archi.ptr64 then Ifptr (psub p (Ptrofs.of_int64 i)) else Ifptr (plub (poffset p) (provenance w))
  | Ifptr p, _ => Ifptr (plub (poffset p) (provenance w))
  | _, _ => ntop2 v w
  end.

Lemma subl_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.subl v w) (subl x y).
Proof.
  intros. unfold Val.subl, subl. destruct Archi.ptr64.
- inv H; inv H0; try (destruct (eq_block b b0)); eauto using psub_sound, poffset_sound, pmatch_lub_l with va.
- inv H; inv H0; eauto with va.
Qed.

Definition mull := binop_long Int64.mul.

Lemma mull_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mull v w) (mull x y).
Proof (binop_long_sound Int64.mul).

Definition mullhs := binop_long Int64.mulhs.

Lemma mullhs_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mullhs v w) (mullhs x y).
Proof (binop_long_sound Int64.mulhs).

Definition mullhu := binop_long Int64.mulhu.

Lemma mullhu_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mullhu v w) (mullhu x y).
Proof (binop_long_sound Int64.mulhu).

Definition divls (v w: aval) :=
  match w, v with
  | L i2, L i1 =>
      if Int64.eq i2 Int64.zero
      || Int64.eq i1 (Int64.repr Int64.min_signed) && Int64.eq i2 Int64.mone
      then if va_strict tt then Vbot else ntop
      else L (Int64.divs i1 i2)
  | _, _ => ntop2 v w
  end.

Lemma divls_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.divls v w = Some u -> vmatch u (divls x y).
Proof.
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int64.eq i0 Int64.zero
         || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone) eqn:E; inv H1.
  inv H; inv H0; auto with va. simpl. rewrite E. constructor.
Qed.

Definition divlu (v w: aval) :=
  match w, v with
  | L i2, L i1 =>
      if Int64.eq i2 Int64.zero
       then if va_strict tt then Vbot else ntop
      else L (Int64.divu i1 i2)
  | _, _ => ntop2 v w
  end.

Lemma divlu_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.divlu v w = Some u -> vmatch u (divlu x y).
Proof.
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int64.eq i0 Int64.zero) eqn:E; inv H1.
  inv H; inv H0; auto with va. simpl. rewrite E. constructor.
Qed.

Definition modls (v w: aval) :=
  match w, v with
  | L i2, L i1 =>
      if Int64.eq i2 Int64.zero
      || Int64.eq i1 (Int64.repr Int64.min_signed) && Int64.eq i2 Int64.mone
      then if va_strict tt then Vbot else ntop
      else L (Int64.mods i1 i2)
  | _, _ => ntop2 v w
  end.

Lemma modls_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.modls v w = Some u -> vmatch u (modls x y).
Proof.
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int64.eq i0 Int64.zero
         || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone) eqn:E; inv H1.
  inv H; inv H0; auto with va. simpl. rewrite E. constructor.
Qed.

Definition modlu (v w: aval) :=
  match w, v with
  | L i2, L i1 =>
      if Int64.eq i2 Int64.zero
      then if va_strict tt then Vbot else ntop
      else L (Int64.modu i1 i2)
  | _, _ => ntop2 v w
  end.

Lemma modlu_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.modlu v w = Some u -> vmatch u (modlu x y).
Proof.
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int64.eq i0 Int64.zero) eqn:E; inv H1.
  inv H; inv H0; auto with va. simpl. rewrite E. constructor.
Qed.

Definition shrxl (v w: aval) :=
  match v, w with
  | L i, I j => if Int.ltu j (Int.repr 63) then L(Int64.shrx' i j) else ntop
  | _, _ => ntop1 v
  end.

Lemma shrxl_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.shrxl v w = Some u -> vmatch u (shrxl x y).
Proof.
  intros.
  destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int.ltu i0 (Int.repr 63)) eqn:LTU; inv H1.
  unfold shrxl; inv H; auto with va; inv H0; auto with va.
  rewrite LTU; auto with va.
Qed.

Definition rolml (x: aval) (amount: int) (mask: int64) :=
  andl (roll x (I amount)) (L mask).

Lemma rolml_sound:
  forall v x amount mask,
  vmatch v x -> vmatch (Val.rolml v amount mask) (rolml x amount mask).
Proof.
  intros.
  replace (Val.rolml v amount mask) with (Val.andl (Val.roll v (Vint amount)) (Vlong mask)).
  apply andl_sound. apply roll_sound. auto. constructor. constructor.
  destruct v; auto.
Qed.

(** Pointer operations *)

Definition offset_ptr (v: aval) (n: ptrofs) :=
  match v with
  | Ptr p => Ptr (padd p n)
  | Ifptr p => Ifptr (padd p n)
  | _ => ntop1 v
  end.

Lemma offset_ptr_sound:
  forall v x n, vmatch v x -> vmatch (Val.offset_ptr v n) (offset_ptr x n).
Proof.
  intros. unfold Val.offset_ptr, offset_ptr.
  inv H; constructor; apply padd_sound; assumption.
Qed.

(** Floating-point arithmetic operations *)

Definition negf := unop_float Float.neg.

Lemma negf_sound:
  forall v x, vmatch v x -> vmatch (Val.negf v) (negf x).
Proof (unop_float_sound Float.neg).

Definition absf := unop_float Float.abs.

Lemma absf_sound:
  forall v x, vmatch v x -> vmatch (Val.absf v) (absf x).
Proof (unop_float_sound Float.abs).

Definition addf := binop_float Float.add.

Lemma addf_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.addf v w) (addf x y).
Proof (binop_float_sound Float.add).

Definition subf := binop_float Float.sub.

Lemma subf_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.subf v w) (subf x y).
Proof (binop_float_sound Float.sub).

Definition mulf := binop_float Float.mul.

Lemma mulf_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mulf v w) (mulf x y).
Proof (binop_float_sound Float.mul).

Definition divf := binop_float Float.div.

Lemma divf_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.divf v w) (divf x y).
Proof (binop_float_sound Float.div).

Definition negfs := unop_single Float32.neg.

Lemma negfs_sound:
  forall v x, vmatch v x -> vmatch (Val.negfs v) (negfs x).
Proof (unop_single_sound Float32.neg).

Definition absfs := unop_single Float32.abs.

Lemma absfs_sound:
  forall v x, vmatch v x -> vmatch (Val.absfs v) (absfs x).
Proof (unop_single_sound Float32.abs).

Definition addfs := binop_single Float32.add.

Lemma addfs_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.addfs v w) (addfs x y).
Proof (binop_single_sound Float32.add).

Definition subfs := binop_single Float32.sub.

Lemma subfs_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.subfs v w) (subfs x y).
Proof (binop_single_sound Float32.sub).

Definition mulfs := binop_single Float32.mul.

Lemma mulfs_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mulfs v w) (mulfs x y).
Proof (binop_single_sound Float32.mul).

Definition divfs := binop_single Float32.div.

Lemma divfs_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.divfs v w) (divfs x y).
Proof (binop_single_sound Float32.div).

(** Conversions *)

Definition zero_ext (nbits: Z) (v: aval) :=
  match v with
  | I i => I (Int.zero_ext nbits i)
  | Uns p n => uns p (Z.min n nbits)
  | _ => uns (provenance v) nbits
  end.

Lemma zero_ext_sound:
  forall nbits v x, vmatch v x -> vmatch (Val.zero_ext nbits v) (zero_ext nbits x).
Proof.
  assert (DFL: forall nbits i, is_uns nbits (Int.zero_ext nbits i)).
  {
    intros; red; intros. rewrite Int.bits_zero_ext by omega. apply zlt_false; auto.
  }
  intros. inv H; simpl; auto with va. apply vmatch_uns.
  red; intros. zify.
  rewrite Int.bits_zero_ext by omega.
  destruct (zlt m nbits); auto. apply H1; omega.
Qed.

Definition sign_ext (nbits: Z) (v: aval) :=
  match v with
  | I i => I (Int.sign_ext nbits i)
  | Uns p n => if zlt n nbits then Uns p n else sgn p nbits
  | Sgn p n => sgn p (Z.min n nbits)
  | _ => sgn (provenance v) nbits
  end.

Lemma sign_ext_sound:
  forall nbits v x, 0 < nbits -> vmatch v x -> vmatch (Val.sign_ext nbits v) (sign_ext nbits x).
Proof.
  assert (DFL: forall p nbits i, 0 < nbits -> vmatch (Vint (Int.sign_ext nbits i)) (sgn p nbits)).
  {
    intros. apply vmatch_sgn. apply is_sign_ext_sgn; auto with va.
  }
  intros. inv H0; simpl; auto with va.
- destruct (zlt n nbits); eauto with va.
  constructor; auto. eapply is_sign_ext_uns; eauto with va.
- destruct (zlt n nbits); auto with va.
- apply vmatch_sgn. apply is_sign_ext_sgn; auto with va.
  apply Z.min_case; auto with va.
Qed.

Definition longofint (v: aval) :=
  match v with
  | I i => L (Int64.repr (Int.signed i))
  | _ => ntop1 v
  end.

Lemma longofint_sound:
  forall v x, vmatch v x -> vmatch (Val.longofint v) (longofint x).
Proof.
  unfold Val.longofint, longofint; intros; inv H; auto with va.
Qed.

Definition longofintu (v: aval) :=
  match v with
  | I i => L (Int64.repr (Int.unsigned i))
  | _ => ntop1 v
  end.

Lemma longofintu_sound:
  forall v x, vmatch v x -> vmatch (Val.longofintu v) (longofintu x).
Proof.
  unfold Val.longofintu, longofintu; intros; inv H; auto with va.
Qed.

Definition singleoffloat (v: aval) :=
  match v with
  | F f => FS (Float.to_single f)
  | _   => ntop1 v
  end.

Lemma singleoffloat_sound:
  forall v x, vmatch v x -> vmatch (Val.singleoffloat v) (singleoffloat x).
Proof.
  intros.
  assert (DEFAULT: vmatch (Val.singleoffloat v) (ntop1 x)).
  { destruct v; constructor. }
  destruct x; auto. inv H. constructor.
Qed.

Definition floatofsingle (v: aval) :=
  match v with
  | FS f => F (Float.of_single f)
  | _   => ntop1 v
  end.

Lemma floatofsingle_sound:
  forall v x, vmatch v x -> vmatch (Val.floatofsingle v) (floatofsingle x).
Proof.
  intros.
  assert (DEFAULT: vmatch (Val.floatofsingle v) (ntop1 x)).
  { destruct v; constructor. }
  destruct x; auto. inv H. constructor.
Qed.

Definition intoffloat (x: aval) :=
  match x with
  | F f =>
      match Float.to_int f with
      | Some i => I i
      | None => if va_strict tt then Vbot else ntop
      end
  | _ => ntop1 x
  end.

Lemma intoffloat_sound:
  forall v x w, vmatch v x -> Val.intoffloat v = Some w -> vmatch w (intoffloat x).
Proof.
  unfold Val.intoffloat; intros. destruct v; try discriminate.
  destruct (Float.to_int f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor.
Qed.

Definition intuoffloat (x: aval) :=
  match x with
  | F f =>
      match Float.to_intu f with
      | Some i => I i
      | None => if va_strict tt then Vbot else ntop
      end
  | _ => ntop1 x
  end.

Lemma intuoffloat_sound:
  forall v x w, vmatch v x -> Val.intuoffloat v = Some w -> vmatch w (intuoffloat x).
Proof.
  unfold Val.intuoffloat; intros. destruct v; try discriminate.
  destruct (Float.to_intu f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor.
Qed.

Definition floatofint (x: aval) :=
  match x with
  | I i => F(Float.of_int i)
  | _   => ntop1 x
  end.

Lemma floatofint_sound:
  forall v x w, vmatch v x -> Val.floatofint v = Some w -> vmatch w (floatofint x).
Proof.
  unfold Val.floatofint; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.

Definition floatofintu (x: aval) :=
  match x with
  | I i => F(Float.of_intu i)
  | _   => ntop1 x
  end.

Lemma floatofintu_sound:
  forall v x w, vmatch v x -> Val.floatofintu v = Some w -> vmatch w (floatofintu x).
Proof.
  unfold Val.floatofintu; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.

Definition intofsingle (x: aval) :=
  match x with
  | FS f =>
      match Float32.to_int f with
      | Some i => I i
      | None => if va_strict tt then Vbot else ntop
      end
  | _ => ntop1 x
  end.

Lemma intofsingle_sound:
  forall v x w, vmatch v x -> Val.intofsingle v = Some w -> vmatch w (intofsingle x).
Proof.
  unfold Val.intofsingle; intros. destruct v; try discriminate.
  destruct (Float32.to_int f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor.
Qed.

Definition intuofsingle (x: aval) :=
  match x with
  | FS f =>
      match Float32.to_intu f with
      | Some i => I i
      | None => if va_strict tt then Vbot else ntop
      end
  | _ => ntop1 x
  end.

Lemma intuofsingle_sound:
  forall v x w, vmatch v x -> Val.intuofsingle v = Some w -> vmatch w (intuofsingle x).
Proof.
  unfold Val.intuofsingle; intros. destruct v; try discriminate.
  destruct (Float32.to_intu f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor.
Qed.

Definition singleofint (x: aval) :=
  match x with
  | I i => FS(Float32.of_int i)
  | _   => ntop1 x
  end.

Lemma singleofint_sound:
  forall v x w, vmatch v x -> Val.singleofint v = Some w -> vmatch w (singleofint x).
Proof.
  unfold Val.singleofint; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.

Definition singleofintu (x: aval) :=
  match x with
  | I i => FS(Float32.of_intu i)
  | _   => ntop1 x
  end.

Lemma singleofintu_sound:
  forall v x w, vmatch v x -> Val.singleofintu v = Some w -> vmatch w (singleofintu x).
Proof.
  unfold Val.singleofintu; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.

Definition longoffloat (x: aval) :=
  match x with
  | F f =>
      match Float.to_long f with
      | Some i => L i
      | None => if va_strict tt then Vbot else ntop
      end
  | _ => ntop1 x
  end.

Lemma longoffloat_sound:
  forall v x w, vmatch v x -> Val.longoffloat v = Some w -> vmatch w (longoffloat x).
Proof.
  unfold Val.longoffloat; intros. destruct v; try discriminate.
  destruct (Float.to_long f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor.
Qed.

Definition longuoffloat (x: aval) :=
  match x with
  | F f =>
      match Float.to_longu f with
      | Some i => L i
      | None => if va_strict tt then Vbot else ntop
      end
  | _ => ntop1 x
  end.

Lemma longuoffloat_sound:
  forall v x w, vmatch v x -> Val.longuoffloat v = Some w -> vmatch w (longuoffloat x).
Proof.
  unfold Val.longuoffloat; intros. destruct v; try discriminate.
  destruct (Float.to_longu f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor.
Qed.

Definition floatoflong (x: aval) :=
  match x with
  | L i => F(Float.of_long i)
  | _   => ntop1 x
  end.

Lemma floatoflong_sound:
  forall v x w, vmatch v x -> Val.floatoflong v = Some w -> vmatch w (floatoflong x).
Proof.
  unfold Val.floatoflong; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.

Definition floatoflongu (x: aval) :=
  match x with
  | L i => F(Float.of_longu i)
  | _   => ntop1 x
  end.

Lemma floatoflongu_sound:
  forall v x w, vmatch v x -> Val.floatoflongu v = Some w -> vmatch w (floatoflongu x).
Proof.
  unfold Val.floatoflongu; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.

Definition longofsingle (x: aval) :=
  match x with
  | FS f =>
      match Float32.to_long f with
      | Some i => L i
      | None => if va_strict tt then Vbot else ntop
      end
  | _ => ntop1 x
  end.

Lemma longofsingle_sound:
  forall v x w, vmatch v x -> Val.longofsingle v = Some w -> vmatch w (longofsingle x).
Proof.
  unfold Val.longofsingle; intros. destruct v; try discriminate.
  destruct (Float32.to_long f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor.
Qed.

Definition longuofsingle (x: aval) :=
  match x with
  | FS f =>
      match Float32.to_longu f with
      | Some i => L i
      | None => if va_strict tt then Vbot else ntop
      end
  | _ => ntop1 x
  end.

Lemma longuofsingle_sound:
  forall v x w, vmatch v x -> Val.longuofsingle v = Some w -> vmatch w (longuofsingle x).
Proof.
  unfold Val.longuofsingle; intros. destruct v; try discriminate.
  destruct (Float32.to_longu f) as [i|] eqn:E; simpl in H0; inv H0.
  inv H; simpl; auto with va. rewrite E; constructor.
Qed.

Definition singleoflong (x: aval) :=
  match x with
  | L i => FS(Float32.of_long i)
  | _   => ntop1 x
  end.

Lemma singleoflong_sound:
  forall v x w, vmatch v x -> Val.singleoflong v = Some w -> vmatch w (singleoflong x).
Proof.
  unfold Val.singleoflong; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.

Definition singleoflongu (x: aval) :=
  match x with
  | L i => FS(Float32.of_longu i)
  | _   => ntop1 x
  end.

Lemma singleoflongu_sound:
  forall v x w, vmatch v x -> Val.singleoflongu v = Some w -> vmatch w (singleoflongu x).
Proof.
  unfold Val.singleoflongu; intros. destruct v; inv H0.
  inv H; simpl; auto with va.
Qed.

Definition floatofwords (x y: aval) :=
  match x, y with
  | I i, I j => F(Float.from_words i j)
  | _, _     => ntop2 x y
  end.

Lemma floatofwords_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.floatofwords v w) (floatofwords x y).
Proof.
  intros. unfold floatofwords; inv H; simpl; auto with va; inv H0; auto with va.
Qed.

Definition longofwords (x y: aval) :=
  match y, x with
  | I j, I i => L(Int64.ofwords i j)
  | _, _     => ntop2 x y
  end.

Lemma longofwords_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.longofwords v w) (longofwords x y).
Proof.
  intros. unfold longofwords; inv H0; inv H; simpl; auto with va.
Qed.

Definition loword (x: aval) :=
  match x with
  | L i => I(Int64.loword i)
  | _   => ntop1 x
  end.

Lemma loword_sound: forall v x, vmatch v x -> vmatch (Val.loword v) (loword x).
Proof.
  destruct 1; simpl; auto with va.
Qed.

Definition hiword (x: aval) :=
  match x with
  | L i => I(Int64.hiword i)
  | _   => ntop1 x
  end.

Lemma hiword_sound: forall v x, vmatch v x -> vmatch (Val.hiword v) (hiword x).
Proof.
  destruct 1; simpl; auto with va.
Qed.

(** Comparisons and variation intervals *)

Definition cmp_intv (c: comparison) (i: Z * Z) (n: Z) : abool :=
  let (lo, hi) := i in
  match c with
  | Ceq => if zlt n lo || zlt hi n then Maybe false else Btop
  | Cne => Btop
  | Clt => if zlt hi n then Maybe true else if zle n lo then Maybe false else Btop
  | Cle => if zle hi n then Maybe true else if zlt n lo then Maybe false else Btop
  | Cgt => if zlt n lo then Maybe true else if zle hi n then Maybe false else Btop
  | Cge => if zle n lo then Maybe true else if zlt hi n then Maybe false else Btop
  end.

Definition zcmp (c: comparison) (n1 n2: Z) : bool :=
  match c with
  | Ceq => zeq n1 n2
  | Cne => negb (zeq n1 n2)
  | Clt => zlt n1 n2
  | Cle => zle n1 n2
  | Cgt => zlt n2 n1
  | Cge => zle n2 n1
  end.

Lemma zcmp_intv_sound:
  forall c i x n,
  fst i <= x <= snd i ->
  cmatch (Some (zcmp c x n)) (cmp_intv c i n).
Proof.
  intros c [lo hi] x n; simpl; intros R.
  destruct c; unfold zcmp, proj_sumbool.
- (* eq *)
  destruct (zlt n lo). rewrite zeq_false by omega. constructor.
  destruct (zlt hi n). rewrite zeq_false by omega. constructor.
  constructor.
- (* ne *)
  constructor.
- (* lt *)
  destruct (zlt hi n). rewrite zlt_true by omega. constructor.
  destruct (zle n lo). rewrite zlt_false by omega. constructor.
  constructor.
- (* le *)
  destruct (zle hi n). rewrite zle_true by omega. constructor.
  destruct (zlt n lo). rewrite zle_false by omega. constructor.
  constructor.
- (* gt *)
  destruct (zlt n lo). rewrite zlt_true by omega. constructor.
  destruct (zle hi n). rewrite zlt_false by omega. constructor.
  constructor.
- (* ge *)
  destruct (zle n lo). rewrite zle_true by omega. constructor.
  destruct (zlt hi n). rewrite zle_false by omega. constructor.
  constructor.
Qed.

Lemma cmp_intv_None:
  forall c i n, cmatch None (cmp_intv c i n).
Proof.
  unfold cmp_intv; intros. destruct i as [lo hi].
  destruct c.
- (* eq *)
  destruct (zlt n lo). constructor. destruct (zlt hi n); constructor.
- (* ne *)
  constructor.
- (* lt *)
  destruct (zlt hi n). constructor. destruct (zle n lo); constructor.
- (* le *)
  destruct (zle hi n). constructor. destruct (zlt n lo); constructor.
- (* gt *)
  destruct (zlt n lo). constructor. destruct (zle hi n); constructor.
- (* ge *)
  destruct (zle n lo). constructor. destruct (zlt hi n); constructor.
Qed.

Definition uintv (v: aval) : Z * Z :=
  match v with
  | I n => (Int.unsigned n, Int.unsigned n)
  | Uns _ n => if zlt n Int.zwordsize then (0, two_p n - 1) else (0, Int.max_unsigned)
  | _ => (0, Int.max_unsigned)
  end.

Lemma uintv_sound:
  forall n v, vmatch (Vint n) v -> fst (uintv v) <= Int.unsigned n <= snd (uintv v).
Proof.
  intros. inv H; simpl; try (apply Int.unsigned_range_2).
- omega.
- destruct (zlt n0 Int.zwordsize); simpl.
+ rewrite is_uns_zero_ext in H2. rewrite <- H2. rewrite Int.zero_ext_mod by omega.
  exploit (Z_mod_lt (Int.unsigned n) (two_p n0)). apply two_p_gt_ZERO; auto. omega.
+ apply Int.unsigned_range_2.
Qed.

Lemma cmpu_intv_sound:
  forall valid c n1 v1 n2,
  vmatch (Vint n1) v1 ->
  cmatch (Val.cmpu_bool valid c (Vint n1) (Vint n2)) (cmp_intv c (uintv v1) (Int.unsigned n2)).
Proof.
  intros. simpl. replace (Int.cmpu c n1 n2) with (zcmp c (Int.unsigned n1) (Int.unsigned n2)).
  apply zcmp_intv_sound; apply uintv_sound; auto.
  destruct c; simpl; auto.
  unfold Int.ltu. destruct (zle (Int.unsigned n1) (Int.unsigned n2)); [rewrite zlt_false|rewrite zlt_true]; auto; omega.
  unfold Int.ltu. destruct (zle (Int.unsigned n2) (Int.unsigned n1)); [rewrite zlt_false|rewrite zlt_true]; auto; omega.
Qed.

Lemma cmpu_intv_sound_2:
  forall valid c n1 v1 n2,
  vmatch (Vint n1) v1 ->
  cmatch (Val.cmpu_bool valid c (Vint n2) (Vint n1)) (cmp_intv (swap_comparison c) (uintv v1) (Int.unsigned n2)).
Proof.
  intros. rewrite <- Val.swap_cmpu_bool. apply cmpu_intv_sound; auto.
Qed.

Definition sintv (v: aval) : Z * Z :=
  match v with
  | I n => (Int.signed n, Int.signed n)
  | Uns _ n =>
      if zlt n Int.zwordsize then (0, two_p n - 1) else (Int.min_signed, Int.max_signed)
  | Sgn _ n =>
      if zlt n Int.zwordsize
      then (let x := two_p (n-1) in (-x, x-1))
      else (Int.min_signed, Int.max_signed)
  | _ => (Int.min_signed, Int.max_signed)
  end.

Lemma sintv_sound:
  forall n v, vmatch (Vint n) v -> fst (sintv v) <= Int.signed n <= snd (sintv v).
Proof.
  intros. inv H; simpl; try (apply Int.signed_range).
- omega.
- destruct (zlt n0 Int.zwordsize); simpl.
+ rewrite is_uns_zero_ext in H2. rewrite <- H2.
  assert (Int.unsigned (Int.zero_ext n0 n) = Int.unsigned n mod two_p n0) by (apply Int.zero_ext_mod; omega).
  exploit (Z_mod_lt (Int.unsigned n) (two_p n0)). apply two_p_gt_ZERO; auto. intros.
  replace (Int.signed (Int.zero_ext n0 n)) with (Int.unsigned (Int.zero_ext n0 n)).
  rewrite H. omega.
  unfold Int.signed. rewrite zlt_true. auto.
  assert (two_p n0 <= Int.half_modulus).
  { change Int.half_modulus with (two_p (Int.zwordsize - 1)).
    apply two_p_monotone. omega. }
  omega.
+ apply Int.signed_range.
- destruct (zlt n0 (Int.zwordsize)); simpl.
+ rewrite is_sgn_sign_ext in H2 by auto. rewrite <- H2.
  exploit (Int.sign_ext_range n0 n). omega. omega.
+ apply Int.signed_range.
Qed.

Lemma cmp_intv_sound:
  forall c n1 v1 n2,
  vmatch (Vint n1) v1 ->
  cmatch (Val.cmp_bool c (Vint n1) (Vint n2)) (cmp_intv c (sintv v1) (Int.signed n2)).
Proof.
  intros. simpl. replace (Int.cmp c n1 n2) with (zcmp c (Int.signed n1) (Int.signed n2)).
  apply zcmp_intv_sound; apply sintv_sound; auto.
  destruct c; simpl; rewrite ? Int.eq_signed; auto.
  unfold Int.lt. destruct (zle (Int.signed n1) (Int.signed n2)); [rewrite zlt_false|rewrite zlt_true]; auto; omega.
  unfold Int.lt. destruct (zle (Int.signed n2) (Int.signed n1)); [rewrite zlt_false|rewrite zlt_true]; auto; omega.
Qed.

Lemma cmp_intv_sound_2:
  forall c n1 v1 n2,
  vmatch (Vint n1) v1 ->
  cmatch (Val.cmp_bool c (Vint n2) (Vint n1)) (cmp_intv (swap_comparison c) (sintv v1) (Int.signed n2)).
Proof.
  intros. rewrite <- Val.swap_cmp_bool. apply cmp_intv_sound; auto.
Qed.

(** Comparisons *)

Definition cmpu_bool (c: comparison) (v w: aval) : abool :=
  match v, w with
  | I i1, I i2 => Just (Int.cmpu c i1 i2)
  | Ptr _, I i => if Int.eq i Int.zero then cmp_different_blocks c else Btop
  | I i, Ptr _ => if Int.eq i Int.zero then cmp_different_blocks c else Btop
  | Ptr p1, Ptr p2 => pcmp c p1 p2
  | _, I i => club (cmp_intv c (uintv v) (Int.unsigned i)) (cmp_different_blocks c)
  | I i, _ => club (cmp_intv (swap_comparison c) (uintv w) (Int.unsigned i)) (cmp_different_blocks c)
  | _, _ => Btop
  end.

Lemma cmpu_bool_sound:
  forall valid c v w x y, vmatch v x -> vmatch w y -> cmatch (Val.cmpu_bool valid c v w) (cmpu_bool c x y).
Proof.
  intros.
  assert (IP: forall i b ofs,
    cmatch (Val.cmpu_bool valid c (Vint i) (Vptr b ofs)) (cmp_different_blocks c)).
  {
    intros. simpl. destruct Archi.ptr64.
    apply cmp_different_blocks_none.
    destruct (Int.eq i Int.zero && (valid b (Ptrofs.unsigned ofs) || valid b (Ptrofs.unsigned ofs - 1))).
    apply cmp_different_blocks_sound. apply cmp_different_blocks_none.
  }
  assert (PI: forall i b ofs,
    cmatch (Val.cmpu_bool valid c (Vptr b ofs) (Vint i)) (cmp_different_blocks c)).
  {
    intros. simpl. destruct Archi.ptr64.
    apply cmp_different_blocks_none.
    destruct (Int.eq i Int.zero && (valid b (Ptrofs.unsigned ofs) || valid b (Ptrofs.unsigned ofs - 1))).
    apply cmp_different_blocks_sound. apply cmp_different_blocks_none.
  }
  unfold cmpu_bool; inversion H; subst; inversion H0; subst;
  auto using cmatch_top, cmp_different_blocks_none, pcmp_none,
             cmatch_lub_l, cmatch_lub_r, pcmp_sound,
             cmpu_intv_sound, cmpu_intv_sound_2, cmp_intv_None.
- constructor.
- destruct (Int.eq i Int.zero); auto using cmatch_top.
- simpl; destruct (Int.eq i Int.zero); auto using cmatch_top, cmp_different_blocks_none.
- destruct (Int.eq i Int.zero); auto using cmatch_top.
- simpl; destruct (Int.eq i Int.zero); auto using cmatch_top, cmp_different_blocks_none.
Qed.

Definition cmp_bool (c: comparison) (v w: aval) : abool :=
  match v, w with
  | I i1, I i2 => Just (Int.cmp c i1 i2)
  | _, I i => cmp_intv c (sintv v) (Int.signed i)
  | I i, _ => cmp_intv (swap_comparison c) (sintv w) (Int.signed i)
  | _, _ => Btop
  end.

Lemma cmp_bool_sound:
  forall c v w x y, vmatch v x -> vmatch w y -> cmatch (Val.cmp_bool c v w) (cmp_bool c x y).
Proof.
  intros.
  unfold cmp_bool; inversion H; subst; inversion H0; subst;
  auto using cmatch_top, cmp_intv_sound, cmp_intv_sound_2, cmp_intv_None.
- constructor.
Qed.

Definition cmplu_bool (c: comparison) (v w: aval) : abool :=
  match v, w with
  | L i1, L i2 => Just (Int64.cmpu c i1 i2)
  | Ptr _, L i => if Int64.eq i Int64.zero then cmp_different_blocks c else Btop
  | L i, Ptr _ => if Int64.eq i Int64.zero then cmp_different_blocks c else Btop
  | Ptr p1, Ptr p2 => pcmp c p1 p2
  | _, _ => Btop
  end.

Lemma cmplu_bool_sound:
  forall valid c v w x y, vmatch v x -> vmatch w y -> cmatch (Val.cmplu_bool valid c v w) (cmplu_bool c x y).
Proof.
  intros.
  assert (IP: forall i b ofs,
    cmatch (Val.cmplu_bool valid c (Vlong i) (Vptr b ofs)) (cmp_different_blocks c)).
  {
    intros. simpl. destruct Archi.ptr64; simpl.
    destruct (Int64.eq i Int64.zero && (valid b (Ptrofs.unsigned ofs) || valid b (Ptrofs.unsigned ofs - 1))).
    apply cmp_different_blocks_sound. apply cmp_different_blocks_none.
    apply cmp_different_blocks_none.
  }
  assert (PI: forall i b ofs,
    cmatch (Val.cmplu_bool valid c (Vptr b ofs) (Vlong i)) (cmp_different_blocks c)).
  {
    intros. simpl. destruct Archi.ptr64; simpl.
    destruct (Int64.eq i Int64.zero && (valid b (Ptrofs.unsigned ofs) || valid b (Ptrofs.unsigned ofs - 1))).
    apply cmp_different_blocks_sound. apply cmp_different_blocks_none.
    apply cmp_different_blocks_none.
  }
  unfold cmplu_bool; inversion H; subst; inversion H0; subst;
  auto using cmatch_top, cmp_different_blocks_none, pcmp_none,
             cmatch_lub_l, cmatch_lub_r, pcmp_sound_64.
- constructor.
- destruct (Int64.eq i Int64.zero); auto using cmatch_top.
- simpl; destruct (Int64.eq i Int64.zero); auto using cmatch_top, cmp_different_blocks_none.
- destruct (Int64.eq i Int64.zero); auto using cmatch_top.
- simpl; destruct (Int64.eq i Int64.zero); auto using cmatch_top, cmp_different_blocks_none.
Qed.

Definition cmpl_bool (c: comparison) (v w: aval) : abool :=
  match v, w with
  | L i1, L i2 => Just (Int64.cmp c i1 i2)
  | _, _ => Btop
  end.

Lemma cmpl_bool_sound:
  forall c v w x y, vmatch v x -> vmatch w y -> cmatch (Val.cmpl_bool c v w) (cmpl_bool c x y).
Proof.
  intros.
  unfold cmpl_bool; inversion H; subst; inversion H0; subst;
  auto using cmatch_top.
- constructor.
Qed.

Definition cmpf_bool (c: comparison) (v w: aval) : abool :=
  match v, w with
  | F f1, F f2 => Just (Float.cmp c f1 f2)
  | _, _ => Btop
  end.

Lemma cmpf_bool_sound:
  forall c v w x y, vmatch v x -> vmatch w y -> cmatch (Val.cmpf_bool c v w) (cmpf_bool c x y).
Proof.
  intros. inv H; try constructor; inv H0; constructor.
Qed.

Definition cmpfs_bool (c: comparison) (v w: aval) : abool :=
  match v, w with
  | FS f1, FS f2 => Just (Float32.cmp c f1 f2)
  | _, _ => Btop
  end.

Lemma cmpfs_bool_sound:
  forall c v w x y, vmatch v x -> vmatch w y -> cmatch (Val.cmpfs_bool c v w) (cmpfs_bool c x y).
Proof.
  intros. inv H; try constructor; inv H0; constructor.
Qed.

Definition maskzero (x: aval) (mask: int) : abool :=
  match x with
  | I i => Just (Int.eq (Int.and i mask) Int.zero)
  | Uns p n => if Int.eq (Int.zero_ext n mask) Int.zero then Maybe true else Btop
  | _ => Btop
  end.

Lemma maskzero_sound:
  forall mask v x,
  vmatch v x ->
  cmatch (Val.maskzero_bool v mask) (maskzero x mask).
Proof.
  intros. inv H; simpl; auto with va.
  predSpec Int.eq Int.eq_spec (Int.zero_ext n mask) Int.zero; auto with va.
  replace (Int.and i mask) with Int.zero.
  rewrite Int.eq_true. constructor.
  rewrite is_uns_zero_ext in H1. rewrite Int.zero_ext_and in * by auto.
  rewrite <- H1. rewrite Int.and_assoc. rewrite Int.and_commut in H. rewrite H.
  rewrite Int.and_zero; auto.
  destruct (Int.eq (Int.zero_ext n mask) Int.zero); constructor.
Qed.

Definition of_optbool (ab: abool) : aval :=
  match ab with
  | Just b => I (if b then Int.one else Int.zero)
  | _ => Uns Pbot 1
  end.

Lemma of_optbool_sound:
  forall ob ab, cmatch ob ab -> vmatch (Val.of_optbool ob) (of_optbool ab).
Proof.
  intros.
  assert (DEFAULT: vmatch (Val.of_optbool ob) (Uns Pbot 1)).
  {
    destruct ob; simpl; auto with va.
    destruct b; constructor; try omega.
    change 1 with (usize Int.one). apply is_uns_usize.
    red; intros. apply Int.bits_zero.
  }
  inv H; auto. simpl. destruct b; constructor.
Qed.

Definition resolve_branch (ab: abool) : option bool :=
  match ab with
  | Just b => Some b
  | Maybe b => Some b
  | _ => None
  end.

Lemma resolve_branch_sound:
  forall b ab b',
  cmatch (Some b) ab -> resolve_branch ab = Some b' -> b' = b.
Proof.
  intros. inv H; simpl in H0; congruence.
Qed.

(** Normalization at load time *)

Definition vnormalize (chunk: memory_chunk) (v: aval) :=
  match chunk, v with
  | _, Vbot => Vbot
  | Mint8signed, I i => I (Int.sign_ext 8 i)
  | Mint8signed, Uns p n => if zlt n 8 then Uns (provenance v) n else Sgn (provenance v) 8
  | Mint8signed, Sgn p n => Sgn (provenance v) (Z.min n 8)
  | Mint8signed, _ => Sgn (provenance v) 8
  | Mint8unsigned, I i => I (Int.zero_ext 8 i)
  | Mint8unsigned, Uns p n => Uns (provenance v) (Z.min n 8)
  | Mint8unsigned, _ => Uns (provenance v) 8
  | Mint16signed, I i => I (Int.sign_ext 16 i)
  | Mint16signed, Uns p n => if zlt n 16 then Uns (provenance v) n else Sgn (provenance v) 16
  | Mint16signed, Sgn p n => Sgn (provenance v) (Z.min n 16)
  | Mint16signed, _ => Sgn (provenance v) 16
  | Mint16unsigned, I i => I (Int.zero_ext 16 i)
  | Mint16unsigned, Uns p n => Uns (provenance v) (Z.min n 16)
  | Mint16unsigned, _ => Uns (provenance v) 16
  | Mint32, (I _ | Uns _ _ | Sgn _ _ | Ifptr _) => v
  | Mint32, Ptr p => if Archi.ptr64 then Ifptr p else v
  | Mint64, (L _ | Ifptr _) => v
  | Mint64, (Uns p _ | Sgn p _) => Ifptr p
  | Mint64, Ptr p => if Archi.ptr64 then v else Ifptr p
  | Mfloat32, FS f => v
  | Mfloat64, F f => v
  | Many32, (I _ | Uns _ _ | Sgn _ _ | FS _ | Ifptr _) => v
  | Many32, Ptr p => if Archi.ptr64 then Ifptr p else v
  | Many64, _ => v
  | _, _ => Ifptr (provenance v)
  end.

Lemma vnormalize_sound:
  forall chunk v x, vmatch v x -> vmatch (Val.load_result chunk v) (vnormalize chunk x).
Proof.
  unfold Val.load_result, vnormalize; generalize Archi.ptr64; intros ptr64;
  induction 1; destruct chunk; auto with va.
- destruct (zlt n 8); constructor; auto with va.
  apply is_sign_ext_uns; auto.
  apply is_sign_ext_sgn; auto with va.
- constructor. xomega. apply is_zero_ext_uns. apply Z.min_case; auto with va.
- destruct (zlt n 16); constructor; auto with va.
  apply is_sign_ext_uns; auto.
  apply is_sign_ext_sgn; auto with va.
- constructor. xomega. apply is_zero_ext_uns. apply Z.min_case; auto with va.
- destruct (zlt n 8); auto with va.
- destruct (zlt n 16); auto with va.
- constructor. xomega. apply is_sign_ext_sgn; auto with va. apply Z.min_case; auto with va.
- constructor. omega. apply is_zero_ext_uns; auto with va.
- constructor. xomega. apply is_sign_ext_sgn; auto with va. apply Z.min_case; auto with va.
- constructor. omega. apply is_zero_ext_uns; auto with va.
- destruct ptr64; auto with va.
- destruct ptr64; auto with va.
- destruct ptr64; auto with va.
- destruct ptr64; auto with va.
- destruct ptr64; auto with va.
- destruct ptr64; auto with va.
- constructor. omega. apply is_sign_ext_sgn; auto with va.
- constructor. omega. apply is_zero_ext_uns; auto with va.
- constructor. omega. apply is_sign_ext_sgn; auto with va.
- constructor. omega. apply is_zero_ext_uns; auto with va.
- destruct ptr64; auto with va.
- destruct ptr64; auto with va.
- destruct ptr64; auto with va.
Qed.

Lemma vnormalize_cast:
  forall chunk m b ofs v p,
  Mem.load chunk m b ofs = Some v ->
  vmatch v (Ifptr p) ->
  vmatch v (vnormalize chunk (Ifptr p)).
Proof.
  intros. exploit Mem.load_cast; eauto. exploit Mem.load_type; eauto.
  destruct chunk; simpl; intros.
- (* int8signed *)
  rewrite H2. destruct v; simpl; constructor. omega. apply is_sign_ext_sgn; auto with va.
- (* int8unsigned *)
  rewrite H2. destruct v; simpl; constructor. omega. apply is_zero_ext_uns; auto with va.
- (* int16signed *)
  rewrite H2. destruct v; simpl; constructor. omega. apply is_sign_ext_sgn; auto with va.
- (* int16unsigned *)
  rewrite H2. destruct v; simpl; constructor. omega. apply is_zero_ext_uns; auto with va.
- (* int32 *)
  auto.
- (* int64 *)
  auto.
- (* float32 *)
  destruct v; try contradiction; constructor.
- (* float64 *)
  destruct v; try contradiction; constructor.
- (* any32 *)
  destruct Archi.ptr64; auto.
- (* any64 *)
  auto.
Qed.

Remark poffset_monotone:
  forall p q, pge p q -> pge (poffset p) (poffset q).
Proof.
  destruct 1; simpl; auto with va.
Qed.

Remark provenance_monotone:
  forall x y, vge x y -> pge (provenance x) (provenance y).
Proof.
  unfold provenance; intros. destruct (va_strict tt). constructor.
  inv H; auto using poffset_monotone with va.
Qed.

Lemma vnormalize_monotone:
  forall chunk x y,
  vge x y -> vge (vnormalize chunk x) (vnormalize chunk y).
Proof with (auto using provenance_monotone with va).
  intros chunk x y V; unfold vnormalize; generalize Archi.ptr64; intro ptr64; inversion V; subst; destruct chunk eqn:C; simpl...
- destruct (zlt n 8); constructor...
  apply is_sign_ext_uns...
  apply is_sign_ext_sgn...
- constructor... apply is_zero_ext_uns... apply Z.min_case...
- destruct (zlt n 16); constructor...
  apply is_sign_ext_uns...
  apply is_sign_ext_sgn...
- constructor... apply is_zero_ext_uns... apply Z.min_case...
- unfold provenance; destruct (va_strict tt)...
- destruct (zlt n1 8). rewrite zlt_true by omega...
  destruct (zlt n2 8)...
- destruct (zlt n1 16). rewrite zlt_true by omega...
  destruct (zlt n2 16)...
- constructor... apply is_sign_ext_sgn... apply Z.min_case...
- constructor... apply is_zero_ext_uns...
- constructor... apply is_sign_ext_sgn... apply Z.min_case...
- constructor... apply is_zero_ext_uns...
- unfold provenance; destruct (va_strict tt)...
- destruct (zlt n2 8); constructor...
- destruct (zlt n2 16); constructor...
- destruct ptr64...
- destruct ptr64...
- destruct ptr64...
- destruct ptr64...
- destruct ptr64...
- destruct ptr64...
- constructor... apply is_sign_ext_sgn...
- constructor... apply is_zero_ext_uns...
- constructor... apply is_sign_ext_sgn...
- constructor... apply is_zero_ext_uns...
- unfold provenance; destruct (va_strict tt)...
- unfold provenance; destruct (va_strict tt)...
- unfold provenance; destruct (va_strict tt)...
- unfold provenance; destruct (va_strict tt)...
- unfold provenance; destruct (va_strict tt)...
- unfold provenance; destruct (va_strict tt)...
- unfold provenance; destruct (va_strict tt)...
- unfold provenance; destruct (va_strict tt)...
- destruct (zlt n 8)...
- destruct (zlt n 16)...
Qed.

(** Abstracting memory blocks *)

Inductive acontent : Type :=
 | ACval (chunk: memory_chunk) (av: aval).

Definition eq_acontent : forall (c1 c2: acontent), {c1=c2} + {c1<>c2}.
Proof.
  intros. generalize chunk_eq eq_aval. decide equality.
Defined.

Record ablock : Type := ABlock {
  ab_contents: ZTree.t acontent;
  ab_summary: aptr
}.

Local Notation "a ## b" := (ZTree.get b a) (at level 1).

Definition ablock_init (p: aptr) : ablock :=
  {| ab_contents := ZTree.empty _; ab_summary := p |}.

Definition chunk_compat (chunk chunk': memory_chunk) : bool :=
  match chunk, chunk' with
  | (Mint8signed | Mint8unsigned), (Mint8signed | Mint8unsigned) => true
  | (Mint16signed | Mint16unsigned), (Mint16signed | Mint16unsigned) => true
  | Mint32, Mint32 => true
  | Mfloat32, Mfloat32 => true
  | Mint64, Mint64 => true
  | Mfloat64, Mfloat64 => true
  | Many32, Many32 => true
  | Many64, Many64 => true
  | _, _ => false
  end.

Definition ablock_load (chunk: memory_chunk) (ab: ablock) (i: Z) : aval :=
  match ab.(ab_contents)##i with
  | None => vnormalize chunk (Ifptr ab.(ab_summary))
  | Some (ACval chunk' av) =>
      if chunk_compat chunk chunk'
      then vnormalize chunk av
      else vnormalize chunk (Ifptr ab.(ab_summary))
  end.

Definition ablock_load_anywhere (chunk: memory_chunk) (ab: ablock) : aval :=
  vnormalize chunk (Ifptr ab.(ab_summary)).

Function inval_after (lo: Z) (hi: Z) (c: ZTree.t acontent) { wf (Zwf lo) hi } : ZTree.t acontent :=
  if zle lo hi
  then inval_after lo (hi - 1) (ZTree.remove hi c)
  else c.
Proof.
  intros; red; omega.
  apply Zwf_well_founded.
Qed.

Definition inval_if (hi: Z) (lo: Z) (c: ZTree.t acontent) :=
  match c##lo with
  | None => c
  | Some (ACval chunk av) => if zle (lo + size_chunk chunk) hi then c else ZTree.remove lo c
  end.

Function inval_before (hi: Z) (lo: Z) (c: ZTree.t acontent) { wf (Zwf_up hi) lo } : ZTree.t acontent :=
  if zlt lo hi
  then inval_before hi (lo + 1) (inval_if hi lo c)
  else c.
Proof.
  intros; red; omega.
  apply Zwf_up_well_founded.
Qed.

Definition ablock_store (chunk: memory_chunk) (ab: ablock) (i: Z) (av: aval) : ablock :=
  {| ab_contents :=
       ZTree.set i (ACval chunk av)
         (inval_before i (i - 7)
            (inval_after (i + 1) (i + size_chunk chunk - 1) ab.(ab_contents)));
     ab_summary :=
       vplub av ab.(ab_summary) |}.

Definition ablock_store_anywhere (chunk: memory_chunk) (ab: ablock) (av: aval) : ablock :=
  ablock_init (vplub av ab.(ab_summary)).

Definition ablock_loadbytes (ab: ablock) : aptr := ab.(ab_summary).

Definition ablock_storebytes (ab: ablock) (p: aptr) (ofs: Z) (sz: Z) :=
  {| ab_contents :=
       inval_before ofs (ofs - 7)
         (inval_after ofs (ofs + sz - 1) ab.(ab_contents));
     ab_summary :=
       plub p ab.(ab_summary) |}.

Definition ablock_storebytes_anywhere (ab: ablock) (p: aptr) :=
  ablock_init (plub p ab.(ab_summary)).

Definition smatch (m: mem) (b: block) (p: aptr) : Prop :=
  (forall chunk ofs v, Mem.load chunk m b ofs = Some v -> vmatch v (Ifptr p))
/\(forall ofs b' ofs' q i, Mem.loadbytes m b ofs 1 = Some (Fragment (Vptr b' ofs') q i :: nil) -> pmatch b' ofs' p).

Remark loadbytes_load_ext:
  forall b m m',
  (forall ofs n bytes, Mem.loadbytes m' b ofs n = Some bytes -> n >= 0 -> Mem.loadbytes m b ofs n = Some bytes) ->
  forall chunk ofs v, Mem.load chunk m' b ofs = Some v -> Mem.load chunk m b ofs = Some v.
Proof.
  intros. exploit Mem.load_loadbytes; eauto. intros [bytes [A B]].
  exploit Mem.load_valid_access; eauto. intros [C D].
  subst v. apply Mem.loadbytes_load; auto. apply H; auto. generalize (size_chunk_pos chunk); omega.
Qed.

Lemma smatch_ext:
  forall m b p m',
  smatch m b p ->
  (forall ofs n bytes, Mem.loadbytes m' b ofs n = Some bytes -> n >= 0 -> Mem.loadbytes m b ofs n = Some bytes) ->
  smatch m' b p.
Proof.
  intros. destruct H. split; intros.
  eapply H; eauto. eapply loadbytes_load_ext; eauto.
  eapply H1; eauto. apply H0; eauto. omega.
Qed.

Lemma smatch_inv:
  forall m b p m',
  smatch m b p ->
  (forall ofs n, n >= 0 -> Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n) ->
  smatch m' b p.
Proof.
  intros. eapply smatch_ext; eauto.
  intros. rewrite <- H0; eauto.
Qed.

Lemma smatch_ge:
  forall m b p q, smatch m b p -> pge q p -> smatch m b q.
Proof.
  intros. destruct H as [A B]. split; intros.
  apply vmatch_ge with (Ifptr p); eauto with va.
  apply pmatch_ge with p; eauto with va.
Qed.

Lemma In_loadbytes:
  forall m b byte n ofs bytes,
  Mem.loadbytes m b ofs n = Some bytes ->
  In byte bytes ->
  exists ofs', ofs <= ofs' < ofs + n /\ Mem.loadbytes m b ofs' 1 = Some(byte :: nil).
Proof.
  intros until n. pattern n.
  apply well_founded_ind with (R := Zwf 0).
- apply Zwf_well_founded.
- intros sz REC ofs bytes LOAD IN.
  destruct (zle sz 0).
  + rewrite (Mem.loadbytes_empty m b ofs sz) in LOAD by auto.
    inv LOAD. contradiction.
  + exploit (Mem.loadbytes_split m b ofs 1 (sz - 1) bytes).
    replace (1 + (sz - 1)) with sz by omega. auto.
    omega.
    omega.
    intros (bytes1 & bytes2 & LOAD1 & LOAD2 & CONCAT).
    subst bytes.
    exploit Mem.loadbytes_length. eexact LOAD1. change (nat_of_Z 1) with 1%nat. intros LENGTH1.
    rewrite in_app_iff in IN. destruct IN.
  * destruct bytes1; try discriminate. destruct bytes1; try discriminate.
    simpl in H. destruct H; try contradiction. subst m0.
    exists ofs; split. omega. auto.
  * exploit (REC (sz - 1)). red; omega. eexact LOAD2. auto.
    intros (ofs' & A & B).
    exists ofs'; split. omega. auto.
Qed.

Lemma smatch_loadbytes:
  forall m b p b' ofs' q i n ofs bytes,
  Mem.loadbytes m b ofs n = Some bytes ->
  smatch m b p ->
  In (Fragment (Vptr b' ofs') q i) bytes ->
  pmatch b' ofs' p.
Proof.
  intros. exploit In_loadbytes; eauto. intros (ofs1 & A & B).
  eapply H0; eauto.
Qed.

Lemma loadbytes_provenance:
  forall m b ofs' byte n ofs bytes,
  Mem.loadbytes m b ofs n = Some bytes ->
  Mem.loadbytes m b ofs' 1 = Some (byte :: nil) ->
  ofs <= ofs' < ofs + n ->
  In byte bytes.
Proof.
  intros until n. pattern n.
  apply well_founded_ind with (R := Zwf 0).
- apply Zwf_well_founded.
- intros sz REC ofs bytes LOAD LOAD1 IN.
  exploit (Mem.loadbytes_split m b ofs 1 (sz - 1) bytes).
  replace (1 + (sz - 1)) with sz by omega. auto.
  omega.
  omega.
  intros (bytes1 & bytes2 & LOAD3 & LOAD4 & CONCAT). subst bytes. rewrite in_app_iff.
  destruct (zeq ofs ofs').
+ subst ofs'. rewrite LOAD1 in LOAD3; inv LOAD3. left; simpl; auto.
+ right. eapply (REC (sz - 1)). red; omega. eexact LOAD4. auto. omega.
Qed.

Lemma storebytes_provenance:
  forall m b ofs bytes m' b' ofs' b'' ofs'' q i,
  Mem.storebytes m b ofs bytes = Some m' ->
  Mem.loadbytes m' b' ofs' 1 = Some (Fragment (Vptr b'' ofs'') q i :: nil) ->
  In (Fragment (Vptr b'' ofs'') q i) bytes
  \/ Mem.loadbytes m b' ofs' 1 = Some (Fragment (Vptr b'' ofs'') q i :: nil).
Proof.
  intros.
  assert (EITHER:
            (b' <> b \/ ofs' + 1 <= ofs \/ ofs + Z.of_nat (length bytes) <= ofs')
         \/ (b' = b /\ ofs <= ofs' < ofs + Z.of_nat (length bytes))).
  {
    destruct (eq_block b' b); auto.
    destruct (zle (ofs' + 1) ofs); auto.
    destruct (zle (ofs + Z.of_nat (length bytes)) ofs'); auto.
    right. split. auto. omega.
  }
  destruct EITHER as [A | (A & B)].
- right. rewrite <- H0. symmetry. eapply Mem.loadbytes_storebytes_other; eauto. omega.
- subst b'. left.
  eapply loadbytes_provenance; eauto.
  eapply Mem.loadbytes_storebytes_same; eauto.
Qed.

Lemma store_provenance:
  forall chunk m b ofs v m' b' ofs' b'' ofs'' q i,
  Mem.store chunk m b ofs v = Some m' ->
  Mem.loadbytes m' b' ofs' 1 = Some (Fragment (Vptr b'' ofs'') q i :: nil) ->
  v = Vptr b'' ofs'' /\ (chunk = Mint32 \/ chunk = Many32 \/ chunk = Mint64 \/ chunk = Many64)
  \/ Mem.loadbytes m b' ofs' 1 = Some (Fragment (Vptr b'' ofs'') q i :: nil).
Proof.
  intros. exploit storebytes_provenance; eauto. eapply Mem.store_storebytes; eauto.
  intros [A|A]; auto. left.
  generalize (encode_val_shape chunk v). intros ENC; inv ENC.
- split; auto. rewrite <- H1 in A; destruct A.
  + congruence.
  + exploit H5; eauto. intros (j & P & Q); congruence.
- rewrite <- H1 in A; destruct A.
  + congruence.
  + exploit H3; eauto. intros [byte P]; congruence.
- rewrite <- H1 in A; destruct A.
  + congruence.
  + exploit H2; eauto. congruence.
Qed.

Lemma smatch_store:
  forall chunk m b ofs v m' b' p av,
  Mem.store chunk m b ofs v = Some m' ->
  smatch m b' p ->
  vmatch v av ->
  smatch m' b' (vplub av p).
Proof.
  intros. destruct H0 as [A B]. split.
- intros chunk' ofs' v' LOAD. destruct v'; auto with va.
  exploit Mem.load_pointer_store; eauto.
  intros [(P & Q & R & S) | DISJ].
+ subst. apply vmatch_vplub_l. auto.
+ apply vmatch_vplub_r. apply A with (chunk := chunk') (ofs := ofs').
  rewrite <- LOAD. symmetry. eapply Mem.load_store_other; eauto.
- intros. exploit store_provenance; eauto. intros [[P Q] | P].
+ subst.
  assert (V: vmatch (Vptr b'0 ofs') (Ifptr (vplub av p))).
  {
    apply vmatch_vplub_l. auto.
  }
  inv V; auto.
+ apply pmatch_vplub. eapply B; eauto.
Qed.

Lemma smatch_storebytes:
  forall m b ofs bytes m' b' p p',
  Mem.storebytes m b ofs bytes = Some m' ->
  smatch m b' p ->
  (forall b' ofs' q i, In (Fragment (Vptr b' ofs') q i) bytes -> pmatch b' ofs' p') ->
  smatch m' b' (plub p' p).
Proof.
  intros. destruct H0 as [A B]. split.
- intros. apply vmatch_ifptr. intros bx ofsx EQ; subst v.
  exploit Mem.load_loadbytes; eauto. intros (bytes' & P & Q).
  destruct bytes' as [ | byte1' bytes'].
  exploit Mem.loadbytes_length; eauto. intros. destruct chunk; discriminate.
  generalize (decode_val_shape chunk byte1' bytes'). rewrite <- Q.
  intros DEC; inv DEC; try contradiction.
  assert (v = Vptr bx ofsx).
  { destruct H5 as [E|[E|[E|E]]]; rewrite E in H4; destruct v; simpl in H4;
    try congruence; destruct Archi.ptr64; congruence. }
  exploit In_loadbytes; eauto. eauto with coqlib.
  intros (ofs' & X & Y). subst v.
  exploit storebytes_provenance; eauto. intros [Z | Z].
  apply pmatch_lub_l. eauto.
  apply pmatch_lub_r. eauto.
- intros. exploit storebytes_provenance; eauto. intros [Z | Z].
  apply pmatch_lub_l. eauto.
  apply pmatch_lub_r. eauto.
Qed.

Definition bmatch (m: mem) (b: block) (ab: ablock) : Prop :=
  smatch m b ab.(ab_summary) /\
  forall chunk ofs v, Mem.load chunk m b ofs = Some v -> vmatch v (ablock_load chunk ab ofs).

Lemma bmatch_ext:
  forall m b ab m',
  bmatch m b ab ->
  (forall ofs n bytes, Mem.loadbytes m' b ofs n = Some bytes -> n >= 0 -> Mem.loadbytes m b ofs n = Some bytes) ->
  bmatch m' b ab.
Proof.
  intros. destruct H as [A B]. split; intros.
  apply smatch_ext with m; auto.
  eapply B; eauto. eapply loadbytes_load_ext; eauto.
Qed.

Lemma bmatch_inv:
  forall m b ab m',
  bmatch m b ab ->
  (forall ofs n, n >= 0 -> Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n) ->
  bmatch m' b ab.
Proof.
  intros. eapply bmatch_ext; eauto.
  intros. rewrite <- H0; eauto.
Qed.

Lemma ablock_load_sound:
  forall chunk m b ofs v ab,
  Mem.load chunk m b ofs = Some v ->
  bmatch m b ab ->
  vmatch v (ablock_load chunk ab ofs).
Proof.
  intros. destruct H0. eauto.
Qed.

Lemma ablock_load_anywhere_sound:
  forall chunk m b ofs v ab,
  Mem.load chunk m b ofs = Some v ->
  bmatch m b ab ->
  vmatch v (ablock_load_anywhere chunk ab).
Proof.
  intros. destruct H0. destruct H0. unfold ablock_load_anywhere.
  eapply vnormalize_cast; eauto.
Qed.

Lemma ablock_init_sound:
  forall m b p, smatch m b p -> bmatch m b (ablock_init p).
Proof.
  intros; split; auto; intros.
  unfold ablock_load, ablock_init; simpl. rewrite ZTree.gempty.
  eapply vnormalize_cast; eauto. eapply H; eauto.
Qed.

Lemma ablock_store_anywhere_sound:
  forall chunk m b ofs v m' b' ab av,
  Mem.store chunk m b ofs v = Some m' ->
  bmatch m b' ab ->
  vmatch v av ->
  bmatch m' b' (ablock_store_anywhere chunk ab av).
Proof.
  intros. destruct H0 as [A B]. unfold ablock_store_anywhere.
  apply ablock_init_sound. eapply smatch_store; eauto.
Qed.

Remark inval_after_outside:
  forall i lo hi c, i < lo \/ i > hi -> (inval_after lo hi c)##i = c##i.
Proof.
  intros until c. functional induction (inval_after lo hi c); intros.
  rewrite IHt by omega. apply ZTree.gro. unfold ZTree.elt, ZIndexed.t; omega.
  auto.
Qed.

Remark inval_after_contents:
  forall chunk av i lo hi c,
  (inval_after lo hi c)##i = Some (ACval chunk av) ->
  c##i = Some (ACval chunk av) /\ (i < lo \/ i > hi).
Proof.
  intros until c. functional induction (inval_after lo hi c); intros.
  destruct (zeq i hi).
  subst i. rewrite inval_after_outside in H by omega. rewrite ZTree.grs in H. discriminate.
  exploit IHt; eauto. intros [A B]. rewrite ZTree.gro in A by auto. split. auto. omega.
  split. auto. omega.
Qed.

Remark inval_before_outside:
  forall i hi lo c, i < lo \/ i >= hi -> (inval_before hi lo c)##i = c##i.
Proof.
  intros until c. functional induction (inval_before hi lo c); intros.
  rewrite IHt by omega. unfold inval_if. destruct (c##lo) as [[chunk av]|]; auto.
  destruct (zle (lo + size_chunk chunk) hi); auto.
  apply ZTree.gro. unfold ZTree.elt, ZIndexed.t; omega.
  auto.
Qed.

Remark inval_before_contents_1:
  forall i chunk av lo hi c,
  lo <= i < hi -> (inval_before hi lo c)##i = Some(ACval chunk av) ->
  c##i = Some(ACval chunk av) /\ i + size_chunk chunk <= hi.
Proof.
  intros until c. functional induction (inval_before hi lo c); intros.
- destruct (zeq lo i).
+ subst i. rewrite inval_before_outside in H0 by omega.
  unfold inval_if in H0. destruct (c##lo) as [[chunk0 v0]|] eqn:C; try congruence.
  destruct (zle (lo + size_chunk chunk0) hi).
  rewrite C in H0; inv H0. auto.
  rewrite ZTree.grs in H0. congruence.
+ exploit IHt. omega. auto. intros [A B]; split; auto.
  unfold inval_if in A. destruct (c##lo) as [[chunk0 v0]|] eqn:C; auto.
  destruct (zle (lo + size_chunk chunk0) hi); auto.
  rewrite ZTree.gro in A; auto.
- omegaContradiction.
Qed.

Lemma max_size_chunk: forall chunk, size_chunk chunk <= 8.
Proof.
  destruct chunk; simpl; omega.
Qed.

Remark inval_before_contents:
  forall i c chunk' av' j,
  (inval_before i (i - 7) c)##j = Some (ACval chunk' av') ->
  c##j = Some (ACval chunk' av') /\ (j + size_chunk chunk' <= i \/ i <= j).
Proof.
  intros. destruct (zlt j (i - 7)).
  rewrite inval_before_outside in H by omega.
  split. auto. left. generalize (max_size_chunk chunk'); omega.
  destruct (zlt j i).
  exploit inval_before_contents_1; eauto. omega. tauto.
  rewrite inval_before_outside in H by omega.
  split. auto. omega.
Qed.

Lemma ablock_store_contents:
  forall chunk ab i av j chunk' av',
  (ablock_store chunk ab i av).(ab_contents)##j = Some(ACval chunk' av') ->
     (i = j /\ chunk' = chunk /\ av' = av)
  \/ (ab.(ab_contents)##j = Some(ACval chunk' av')
      /\ (j + size_chunk chunk' <= i \/ i + size_chunk chunk <= j)).
Proof.
  unfold ablock_store; simpl; intros.
  destruct (zeq i j).
  subst j. rewrite ZTree.gss in H. inv H; auto.
  right. rewrite ZTree.gso in H by auto.
  exploit inval_before_contents; eauto. intros [A B].
  exploit inval_after_contents; eauto. intros [C D].
  split. auto. omega.
Qed.

Lemma chunk_compat_true:
  forall c c',
  chunk_compat c c' = true ->
  size_chunk c = size_chunk c' /\ align_chunk c <= align_chunk c' /\ type_of_chunk c = type_of_chunk c'.
Proof.
  destruct c, c'; intros; try discriminate; simpl; auto with va.
Qed.

Lemma ablock_store_sound:
  forall chunk m b ofs v m' ab av,
  Mem.store chunk m b ofs v = Some m' ->
  bmatch m b ab ->
  vmatch v av ->
  bmatch m' b (ablock_store chunk ab ofs av).
Proof.
  intros until av; intros STORE BIN VIN. destruct BIN as [BIN1 BIN2]. split.
  eapply smatch_store; eauto.
  intros chunk' ofs' v' LOAD.
  assert (SUMMARY: vmatch v' (vnormalize chunk' (Ifptr (vplub av ab.(ab_summary))))).
  { exploit smatch_store; eauto. intros [A B]. eapply vnormalize_cast; eauto. }
  unfold ablock_load.
  destruct ((ab_contents (ablock_store chunk ab ofs av)) ## ofs') as [[chunk1 av1]|] eqn:C; auto.
  destruct (chunk_compat chunk' chunk1) eqn:COMPAT; auto.
  exploit chunk_compat_true; eauto. intros (U & V & W).
  exploit ablock_store_contents; eauto. intros [(P & Q & R) | (P & Q)].
- (* same offset and compatible chunks *)
  subst.
  assert (v' = Val.load_result chunk' v).
  { exploit Mem.load_store_similar_2; eauto. congruence. }
  subst v'. apply vnormalize_sound; auto.
- (* disjoint load/store *)
  assert (Mem.load chunk' m b ofs' = Some v').
  { rewrite <- LOAD. symmetry. eapply Mem.load_store_other; eauto.
    rewrite U. auto. }
  exploit BIN2; eauto. unfold ablock_load. rewrite P. rewrite COMPAT. auto.
Qed.

Lemma ablock_loadbytes_sound:
  forall m b ab b' ofs' q i n ofs bytes,
  Mem.loadbytes m b ofs n = Some bytes ->
  bmatch m b ab ->
  In (Fragment (Vptr b' ofs') q i) bytes ->
  pmatch b' ofs' (ablock_loadbytes ab).
Proof.
  intros. destruct H0. eapply smatch_loadbytes; eauto.
Qed.

Lemma ablock_storebytes_anywhere_sound:
  forall m b ofs bytes p m' b' ab,
  Mem.storebytes m b ofs bytes = Some m' ->
  (forall b' ofs' q i, In (Fragment (Vptr b' ofs') q i) bytes -> pmatch b' ofs' p) ->
  bmatch m b' ab ->
  bmatch m' b' (ablock_storebytes_anywhere ab p).
Proof.
  intros. destruct H1 as [A B]. apply ablock_init_sound.
  eapply smatch_storebytes; eauto.
Qed.

Lemma ablock_storebytes_contents:
  forall ab p i sz j chunk' av',
  (ablock_storebytes ab p i sz).(ab_contents)##j = Some(ACval chunk' av') ->
  ab.(ab_contents)##j = Some (ACval chunk' av')
  /\ (j + size_chunk chunk' <= i \/ i + Z.max sz 0 <= j).
Proof.
  unfold ablock_storebytes; simpl; intros.
  exploit inval_before_contents; eauto. clear H. intros [A B].
  exploit inval_after_contents; eauto. clear A. intros [C D].
  split. auto. xomega.
Qed.

Lemma ablock_storebytes_sound:
  forall m b ofs bytes m' p ab sz,
  Mem.storebytes m b ofs bytes = Some m' ->
  length bytes = nat_of_Z sz ->
  (forall b' ofs' q i, In (Fragment (Vptr b' ofs') q i) bytes -> pmatch b' ofs' p) ->
  bmatch m b ab ->
  bmatch m' b (ablock_storebytes ab p ofs sz).
Proof.
  intros until sz; intros STORE LENGTH CONTENTS BM. destruct BM as [BM1 BM2]. split.
  eapply smatch_storebytes; eauto.
  intros chunk' ofs' v' LOAD'.
  assert (SUMMARY: vmatch v' (vnormalize chunk' (Ifptr (plub p ab.(ab_summary))))).
  { exploit smatch_storebytes; eauto. intros [A B]. eapply vnormalize_cast; eauto. }
  unfold ablock_load.
  destruct (ab_contents (ablock_storebytes ab p ofs sz))##ofs' as [[chunk av]|] eqn:C; auto.
  destruct (chunk_compat chunk' chunk) eqn:COMPAT; auto.
  exploit chunk_compat_true; eauto. intros (U & V & W).
  exploit ablock_storebytes_contents; eauto. intros [A B].
  assert (Mem.load chunk' m b ofs' = Some v').
  { rewrite <- LOAD'; symmetry. eapply Mem.load_storebytes_other; eauto.
    rewrite U. rewrite LENGTH. rewrite nat_of_Z_max. right; omega. }
  exploit BM2; eauto. unfold ablock_load. rewrite A. rewrite COMPAT. auto.
Qed.

(** Boolean equality *)

Definition bbeq (ab1 ab2: ablock) : bool :=
  eq_aptr ab1.(ab_summary) ab2.(ab_summary) &&
  ZTree.beq (fun c1 c2 => proj_sumbool (eq_acontent c1 c2)) ab1.(ab_contents) ab2.(ab_contents).

Lemma bbeq_load:
  forall ab1 ab2,
  bbeq ab1 ab2 = true ->
  ab1.(ab_summary) = ab2.(ab_summary)
  /\ (forall chunk i, ablock_load chunk ab1 i = ablock_load chunk ab2 i).
Proof.
  unfold bbeq; intros. InvBooleans. split.
- unfold ablock_load_anywhere; intros; congruence.
- assert (A: forall i, ZTree.get i (ab_contents ab1) = ZTree.get i (ab_contents ab2)).
  {
    intros. exploit ZTree.beq_sound; eauto. instantiate (1 := i).
    destruct (ab_contents ab1)##i, (ab_contents ab2)##i; intros; try contradiction.
    InvBooleans; subst; auto.
    auto. }
  intros. unfold ablock_load. rewrite A, H.
  destruct (ab_contents ab2)##i; auto.
Qed.

Lemma bbeq_sound:
  forall ab1 ab2,
  bbeq ab1 ab2 = true ->
  forall m b, bmatch m b ab1 <-> bmatch m b ab2.
Proof.
  intros. exploit bbeq_load; eauto. intros [A B].
  unfold bmatch. rewrite A. intuition. rewrite <- B; eauto. rewrite B; eauto.
Qed.

(** Least upper bound *)

Definition combine_acontents (c1 c2: option acontent) : option acontent :=
  match c1, c2 with
  | Some (ACval chunk1 v1), Some (ACval chunk2 v2) =>
      if chunk_eq chunk1 chunk2 then Some(ACval chunk1 (vlub v1 v2)) else None
  | _, _ =>
      None
  end.

Definition blub (ab1 ab2: ablock) : ablock :=
  {| ab_contents := ZTree.combine combine_acontents ab1.(ab_contents) ab2.(ab_contents);
     ab_summary := plub ab1.(ab_summary) ab2.(ab_summary) |}.

Lemma smatch_lub_l:
  forall m b p q, smatch m b p -> smatch m b (plub p q).
Proof.
  intros. destruct H as [A B]. split; intros.
  change (vmatch v (vlub (Ifptr p) (Ifptr q))). apply vmatch_lub_l. eapply A; eauto.
  apply pmatch_lub_l. eapply B; eauto.
Qed.

Lemma smatch_lub_r:
  forall m b p q, smatch m b q -> smatch m b (plub p q).
Proof.
  intros. destruct H as [A B]. split; intros.
  change (vmatch v (vlub (Ifptr p) (Ifptr q))). apply vmatch_lub_r. eapply A; eauto.
  apply pmatch_lub_r. eapply B; eauto.
Qed.

Lemma bmatch_lub_l:
  forall m b x y, bmatch m b x -> bmatch m b (blub x y).
Proof.
  intros. destruct H as [BM1 BM2]. split; unfold blub; simpl.
- apply smatch_lub_l; auto.
- intros.
  assert (SUMMARY: vmatch v (vnormalize chunk (Ifptr (plub (ab_summary x) (ab_summary y))))
).
  { exploit smatch_lub_l; eauto. instantiate (1 := ab_summary y).
    intros [SUMM _]. eapply vnormalize_cast; eauto. }
  exploit BM2; eauto.
  unfold ablock_load; simpl. rewrite ZTree.gcombine by auto.
  unfold combine_acontents;
  destruct (ab_contents x)##ofs as [[chunkx avx]|], (ab_contents y)##ofs as [[chunky avy]|]; auto.
  destruct (chunk_eq chunkx chunky); auto. subst chunky.
  destruct (chunk_compat chunk chunkx); auto.
  intros. eapply vmatch_ge; eauto. apply vnormalize_monotone. apply vge_lub_l.
Qed.

Lemma bmatch_lub_r:
  forall m b x y, bmatch m b y -> bmatch m b (blub x y).
Proof.
  intros. destruct H as [BM1 BM2]. split; unfold blub; simpl.
- apply smatch_lub_r; auto.
- intros.
  assert (SUMMARY: vmatch v (vnormalize chunk (Ifptr (plub (ab_summary x) (ab_summary y))))
).
  { exploit smatch_lub_r; eauto. instantiate (1 := ab_summary x).
    intros [SUMM _]. eapply vnormalize_cast; eauto. }
  exploit BM2; eauto.
  unfold ablock_load; simpl. rewrite ZTree.gcombine by auto.
  unfold combine_acontents;
  destruct (ab_contents x)##ofs as [[chunkx avx]|], (ab_contents y)##ofs as [[chunky avy]|]; auto.
  destruct (chunk_eq chunkx chunky); auto. subst chunky.
  destruct (chunk_compat chunk chunkx); auto.
  intros. eapply vmatch_ge; eauto. apply vnormalize_monotone. apply vge_lub_r.
Qed.

(** * Abstracting read-only global variables *)

Definition romem := PTree.t ablock.

Definition romatch  (m: mem) (rm: romem) : Prop :=
  forall b id ab,
  bc b = BCglob id ->
  rm!id = Some ab ->
  pge Glob ab.(ab_summary)
  /\ bmatch m b ab
  /\ forall ofs, ~Mem.perm m b ofs Max Writable.

Lemma romatch_store:
  forall chunk m b ofs v m' rm,
  Mem.store chunk m b ofs v = Some m' ->
  romatch m rm ->
  romatch m' rm.
Proof.
  intros; red; intros. exploit H0; eauto. intros (A & B & C). split; auto. split.
- exploit Mem.store_valid_access_3; eauto. intros [P _].
  apply bmatch_inv with m; auto.
+ intros. eapply Mem.loadbytes_store_other; eauto.
  left. red; intros; subst b0. elim (C ofs). apply Mem.perm_cur_max.
  apply P. generalize (size_chunk_pos chunk); omega.
- intros; red; intros; elim (C ofs0). eauto with mem.
Qed.

Lemma romatch_storebytes:
  forall m b ofs bytes m' rm,
  Mem.storebytes m b ofs bytes = Some m' ->
  romatch m rm ->
  romatch m' rm.
Proof.
  intros; red; intros. exploit H0; eauto. intros (A & B & C). split; auto. split.
- apply bmatch_inv with m; auto.
  intros. eapply Mem.loadbytes_storebytes_disjoint; eauto.
  destruct (eq_block b0 b); auto. subst b0. right; red; unfold Intv.In; simpl; red; intros.
  elim (C x). apply Mem.perm_cur_max. eapply Mem.storebytes_range_perm; eauto.
- intros; red; intros; elim (C ofs0). eauto with mem.
Qed.

Lemma romatch_ext:
  forall m rm m',
  romatch m rm ->
  (forall b id ofs n bytes, bc b = BCglob id -> Mem.loadbytes m' b ofs n = Some bytes -> Mem.loadbytes m b ofs n = Some bytes) ->
  (forall b id ofs p, bc b = BCglob id -> Mem.perm m' b ofs Max p -> Mem.perm m b ofs Max p) ->
  romatch m' rm.
Proof.
  intros; red; intros. exploit H; eauto. intros (A & B & C).
  split. auto.
  split. apply bmatch_ext with m; auto. intros. eapply H0; eauto.
  intros; red; intros. elim (C ofs). eapply H1; eauto.
Qed.

Lemma romatch_free:
  forall m b lo hi m' rm,
  Mem.free m b lo hi = Some m' ->
  romatch m rm ->
  romatch m' rm.
Proof.
  intros. apply romatch_ext with m; auto.
  intros. eapply Mem.loadbytes_free_2; eauto.
  intros. eauto with mem.
Qed.

Lemma romatch_alloc:
  forall m b lo hi m' rm,
  Mem.alloc m lo hi = (m', b) ->
  bc_below bc (Mem.nextblock m) ->
  romatch m rm ->
  romatch m' rm.
Proof.
  intros. apply romatch_ext with m; auto.
  intros. rewrite <- H3; symmetry. eapply Mem.loadbytes_alloc_unchanged; eauto.
  apply H0. congruence.
  intros. eapply Mem.perm_alloc_4; eauto. apply Mem.valid_not_valid_diff with m; eauto with mem.
  apply H0. congruence.
Qed.

(** * Abstracting memory states *)

Record amem : Type := AMem {
  am_stack: ablock;
  am_glob: PTree.t ablock;
  am_nonstack: aptr;
  am_top: aptr
}.

Record mmatch (m: mem) (am: amem) : Prop := mk_mem_match {
  mmatch_stack: forall b,
    bc b = BCstack ->
    bmatch m b am.(am_stack);
  mmatch_glob: forall id ab b,
    bc b = BCglob id ->
    am.(am_glob)!id = Some ab ->
    bmatch m b ab;
  mmatch_nonstack: forall b,
    bc b <> BCstack -> bc b <> BCinvalid ->
    smatch m b am.(am_nonstack);
  mmatch_top: forall b,
    bc b <> BCinvalid ->
    smatch m b am.(am_top);
  mmatch_below:
    bc_below bc (Mem.nextblock m)
}.

Definition minit (p: aptr) :=
  {| am_stack := ablock_init p;
     am_glob := PTree.empty _;
     am_nonstack := p;
     am_top := p |}.

Definition mbot := minit Pbot.
Definition mtop := minit Ptop.

Definition load (chunk: memory_chunk) (rm: romem) (m: amem) (p: aptr) : aval :=
  match p with
  | Pbot => if va_strict tt then Vbot else Vtop
  | Gl id ofs =>
      match rm!id with
      | Some ab => ablock_load chunk ab (Ptrofs.unsigned ofs)
      | None =>
          match m.(am_glob)!id with
          | Some ab => ablock_load chunk ab (Ptrofs.unsigned ofs)
          | None => vnormalize chunk (Ifptr m.(am_nonstack))
          end
      end
  | Glo id =>
      match rm!id with
      | Some ab => ablock_load_anywhere chunk ab
      | None =>
          match m.(am_glob)!id with
          | Some ab => ablock_load_anywhere chunk ab
          | None => vnormalize chunk (Ifptr m.(am_nonstack))
          end
      end
  | Stk ofs => ablock_load chunk m.(am_stack) (Ptrofs.unsigned ofs)
  | Stack => ablock_load_anywhere chunk m.(am_stack)
  | Glob | Nonstack => vnormalize chunk (Ifptr m.(am_nonstack))
  | Ptop => vnormalize chunk (Ifptr m.(am_top))
  end.

Definition loadv (chunk: memory_chunk) (rm: romem) (m: amem) (addr: aval) : aval :=
  load chunk rm m (aptr_of_aval addr).

Definition store (chunk: memory_chunk) (m: amem) (p: aptr) (av: aval) : amem :=
  {| am_stack :=
       match p with
       | Stk ofs      => ablock_store chunk m.(am_stack) (Ptrofs.unsigned ofs) av
       | Stack | Ptop => ablock_store_anywhere chunk m.(am_stack) av
       | _ => m.(am_stack)
       end;
     am_glob :=
       match p with
       | Gl id ofs =>
           let ab := match m.(am_glob)!id with Some ab => ab | None => ablock_init m.(am_nonstack) end in
           PTree.set id (ablock_store chunk ab (Ptrofs.unsigned ofs) av) m.(am_glob)
       | Glo id =>
           let ab := match m.(am_glob)!id with Some ab => ab | None => ablock_init m.(am_nonstack) end in
           PTree.set id (ablock_store_anywhere chunk ab av) m.(am_glob)
       | Glob | Nonstack | Ptop => PTree.empty _
       | _ => m.(am_glob)
       end;
     am_nonstack :=
       match p with
       | Gl _ _ | Glo _ | Glob | Nonstack | Ptop => vplub av m.(am_nonstack)
       | _ => m.(am_nonstack)
       end;
     am_top := vplub av m.(am_top)
  |}.

Definition storev (chunk: memory_chunk) (m: amem) (addr: aval) (v: aval): amem :=
  store chunk m (aptr_of_aval addr) v.

Definition loadbytes (m: amem) (rm: romem) (p: aptr) : aptr :=
  match p with
  | Pbot => if va_strict tt then Pbot else Ptop
  | Gl id _ | Glo id =>
      match rm!id with
      | Some ab => ablock_loadbytes ab
      | None =>
          match m.(am_glob)!id with
          | Some ab => ablock_loadbytes ab
          | None => m.(am_nonstack)
          end
      end
  | Stk _ | Stack => ablock_loadbytes m.(am_stack)
  | Glob | Nonstack => m.(am_nonstack)
  | Ptop => m.(am_top)
  end.

Definition storebytes (m: amem) (dst: aptr) (sz: Z) (p: aptr) : amem :=
  {| am_stack :=
       match dst with
       | Stk ofs      => ablock_storebytes m.(am_stack) p (Ptrofs.unsigned ofs) sz
       | Stack | Ptop => ablock_storebytes_anywhere m.(am_stack) p
       | _ => m.(am_stack)
       end;
     am_glob :=
       match dst with
       | Gl id ofs =>
           let ab := match m.(am_glob)!id with Some ab => ab | None => ablock_init m.(am_nonstack) end in
           PTree.set id (ablock_storebytes ab p (Ptrofs.unsigned ofs) sz) m.(am_glob)
       | Glo id =>
           let ab := match m.(am_glob)!id with Some ab => ab | None => ablock_init m.(am_nonstack) end in
           PTree.set id (ablock_storebytes_anywhere ab p) m.(am_glob)
       | Glob | Nonstack | Ptop => PTree.empty _
       | _ => m.(am_glob)
       end;
     am_nonstack :=
       match dst with
       | Gl _ _ | Glo _ | Glob | Nonstack | Ptop => plub p m.(am_nonstack)
       | _ => m.(am_nonstack)
       end;
     am_top := plub p m.(am_top)
  |}.

Theorem load_sound:
  forall chunk m b ofs v rm am p,
  Mem.load chunk m b (Ptrofs.unsigned ofs) = Some v ->
  romatch m rm ->
  mmatch m am ->
  pmatch b ofs p ->
  vmatch v (load chunk rm am p).
Proof.
  intros. unfold load. inv H2.
- (* Gl id ofs *)
  destruct (rm!id) as [ab|] eqn:RM.
  eapply ablock_load_sound; eauto. eapply H0; eauto.
  destruct (am_glob am)!id as [ab|] eqn:AM.
  eapply ablock_load_sound; eauto. eapply mmatch_glob; eauto.
  eapply vnormalize_cast; eauto. eapply mmatch_nonstack; eauto; congruence.
- (* Glo id *)
  destruct (rm!id) as [ab|] eqn:RM.
  eapply ablock_load_anywhere_sound; eauto. eapply H0; eauto.
  destruct (am_glob am)!id as [ab|] eqn:AM.
  eapply ablock_load_anywhere_sound; eauto. eapply mmatch_glob; eauto.
  eapply vnormalize_cast; eauto. eapply mmatch_nonstack; eauto; congruence.
- (* Glob *)
  eapply vnormalize_cast; eauto. eapply mmatch_nonstack; eauto. congruence. congruence.
- (* Stk ofs *)
  eapply ablock_load_sound; eauto. eapply mmatch_stack; eauto.
- (* Stack *)
  eapply ablock_load_anywhere_sound; eauto. eapply mmatch_stack; eauto.
- (* Nonstack *)
  eapply vnormalize_cast; eauto. eapply mmatch_nonstack; eauto.
- (* Top *)
  eapply vnormalize_cast; eauto. eapply mmatch_top; eauto.
Qed.

Theorem loadv_sound:
  forall chunk m addr v rm am aaddr,
  Mem.loadv chunk m addr = Some v ->
  romatch m rm ->
  mmatch m am ->
  vmatch addr aaddr ->
  vmatch v (loadv chunk rm am aaddr).
Proof.
  intros. destruct addr; simpl in H; try discriminate.
  eapply load_sound; eauto. apply match_aptr_of_aval; auto.
Qed.

Theorem store_sound:
  forall chunk m b ofs v m' am p av,
  Mem.store chunk m b (Ptrofs.unsigned ofs) v = Some m' ->
  mmatch m am ->
  pmatch b ofs p ->
  vmatch v av ->
  mmatch m' (store chunk am p av).
Proof.
  intros until av; intros STORE MM PM VM.
  unfold store; constructor; simpl; intros.
- (* Stack *)
  assert (DFL: bc b <> BCstack -> bmatch m' b0 (am_stack am)).
  { intros. apply bmatch_inv with m. eapply mmatch_stack; eauto.
    intros. eapply Mem.loadbytes_store_other; eauto. left; congruence. }
  inv PM; try (apply DFL; congruence).
  + assert (b0 = b) by (eapply bc_stack; eauto). subst b0.
    eapply ablock_store_sound; eauto. eapply mmatch_stack; eauto.
  + assert (b0 = b) by (eapply bc_stack; eauto). subst b0.
    eapply ablock_store_anywhere_sound; eauto. eapply mmatch_stack; eauto.
  + eapply ablock_store_anywhere_sound; eauto. eapply mmatch_stack; eauto.

- (* Globals *)
  rename b0 into b'.
  assert (DFL: bc b <> BCglob id -> (am_glob am)!id = Some ab ->
               bmatch m' b' ab).
  { intros. apply bmatch_inv with m. eapply mmatch_glob; eauto.
    intros. eapply Mem.loadbytes_store_other; eauto. left; congruence. }
  inv PM.
  + rewrite PTree.gsspec in H0. destruct (peq id id0).
    subst id0; inv H0.
    assert (b' = b) by (eapply bc_glob; eauto). subst b'.
    eapply ablock_store_sound; eauto.
    destruct (am_glob am)!id as [ab0|] eqn:GL.
    eapply mmatch_glob; eauto.
    apply ablock_init_sound. eapply mmatch_nonstack; eauto; congruence.
    eapply DFL; eauto. congruence.
  + rewrite PTree.gsspec in H0. destruct (peq id id0).
    subst id0; inv H0.
    assert (b' = b) by (eapply bc_glob; eauto). subst b'.
    eapply ablock_store_anywhere_sound; eauto.
    destruct (am_glob am)!id as [ab0|] eqn:GL.
    eapply mmatch_glob; eauto.
    apply ablock_init_sound. eapply mmatch_nonstack; eauto; congruence.
    eapply DFL; eauto. congruence.
  + rewrite PTree.gempty in H0; congruence.
  + eapply DFL; eauto. congruence.
  + eapply DFL; eauto. congruence.
  + rewrite PTree.gempty in H0; congruence.
  + rewrite PTree.gempty in H0; congruence.

- (* Nonstack *)
  assert (DFL: smatch m' b0 (vplub av (am_nonstack am))).
  { eapply smatch_store; eauto. eapply mmatch_nonstack; eauto. }
  assert (STK: bc b = BCstack -> smatch m' b0 (am_nonstack am)).
  { intros. apply smatch_inv with m. eapply mmatch_nonstack; eauto; congruence.
    intros. eapply Mem.loadbytes_store_other; eauto. left. congruence.
  }
  inv PM; (apply DFL || apply STK; congruence).

- (* Top *)
  eapply smatch_store; eauto. eapply mmatch_top; eauto.

- (* Below *)
  erewrite Mem.nextblock_store by eauto. eapply mmatch_below; eauto.
Qed.

Theorem storev_sound:
  forall chunk m addr v m' am aaddr av,
  Mem.storev chunk m addr v = Some m' ->
  mmatch m am ->
  vmatch addr aaddr ->
  vmatch v av ->
  mmatch m' (storev chunk am aaddr av).
Proof.
  intros. destruct addr; simpl in H; try discriminate.
  eapply store_sound; eauto. apply match_aptr_of_aval; auto.
Qed.

Theorem loadbytes_sound:
  forall m b ofs sz bytes am rm p,
  Mem.loadbytes m b (Ptrofs.unsigned ofs) sz = Some bytes ->
  romatch m rm ->
  mmatch m am ->
  pmatch b ofs p ->
  forall  b' ofs' q i, In (Fragment (Vptr b' ofs') q i) bytes -> pmatch b' ofs' (loadbytes am rm p).
Proof.
  intros. unfold loadbytes; inv H2.
- (* Gl id ofs *)
  destruct (rm!id) as [ab|] eqn:RM.
  exploit H0; eauto. intros (A & B & C). eapply ablock_loadbytes_sound; eauto.
  destruct (am_glob am)!id as [ab|] eqn:GL.
  eapply ablock_loadbytes_sound; eauto. eapply mmatch_glob; eauto.
  eapply smatch_loadbytes; eauto. eapply mmatch_nonstack; eauto with va.
- (* Glo id *)
  destruct (rm!id) as [ab|] eqn:RM.
  exploit H0; eauto. intros (A & B & C). eapply ablock_loadbytes_sound; eauto.
  destruct (am_glob am)!id as [ab|] eqn:GL.
  eapply ablock_loadbytes_sound; eauto. eapply mmatch_glob; eauto.
  eapply smatch_loadbytes; eauto. eapply mmatch_nonstack; eauto with va.
- (* Glob *)
  eapply smatch_loadbytes; eauto. eapply mmatch_nonstack; eauto with va.
- (* Stk ofs *)
  eapply ablock_loadbytes_sound; eauto. eapply mmatch_stack; eauto.
- (* Stack *)
  eapply ablock_loadbytes_sound; eauto. eapply mmatch_stack; eauto.
- (* Nonstack *)
  eapply smatch_loadbytes; eauto. eapply mmatch_nonstack; eauto with va.
- (* Top *)
  eapply smatch_loadbytes; eauto. eapply mmatch_top; eauto with va.
Qed.

Theorem storebytes_sound:
  forall m b ofs bytes m' am p sz q,
  Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
  mmatch m am ->
  pmatch b ofs p ->
  length bytes = nat_of_Z sz ->
  (forall b' ofs' qt i, In (Fragment (Vptr b' ofs') qt i) bytes -> pmatch b' ofs' q) ->
  mmatch m' (storebytes am p sz q).
Proof.
  intros until q; intros STORE MM PM LENGTH BYTES.
  unfold storebytes; constructor; simpl; intros.
- (* Stack *)
  assert (DFL: bc b <> BCstack -> bmatch m' b0 (am_stack am)).
  { intros. apply bmatch_inv with m. eapply mmatch_stack; eauto.
    intros. eapply Mem.loadbytes_storebytes_other; eauto. left; congruence. }
  inv PM; try (apply DFL; congruence).
  + assert (b0 = b) by (eapply bc_stack; eauto). subst b0.
    eapply ablock_storebytes_sound; eauto. eapply mmatch_stack; eauto.
  + assert (b0 = b) by (eapply bc_stack; eauto). subst b0.
    eapply ablock_storebytes_anywhere_sound; eauto. eapply mmatch_stack; eauto.
  + eapply ablock_storebytes_anywhere_sound; eauto. eapply mmatch_stack; eauto.

- (* Globals *)
  rename b0 into b'.
  assert (DFL: bc b <> BCglob id -> (am_glob am)!id = Some ab ->
               bmatch m' b' ab).
  { intros. apply bmatch_inv with m. eapply mmatch_glob; eauto.
    intros. eapply Mem.loadbytes_storebytes_other; eauto. left; congruence. }
  inv PM.
  + rewrite PTree.gsspec in H0. destruct (peq id id0).
    subst id0; inv H0.
    assert (b' = b) by (eapply bc_glob; eauto). subst b'.
    eapply ablock_storebytes_sound; eauto.
    destruct (am_glob am)!id as [ab0|] eqn:GL.
    eapply mmatch_glob; eauto.
    apply ablock_init_sound. eapply mmatch_nonstack; eauto; congruence.
    eapply DFL; eauto. congruence.
  + rewrite PTree.gsspec in H0. destruct (peq id id0).
    subst id0; inv H0.
    assert (b' = b) by (eapply bc_glob; eauto). subst b'.
    eapply ablock_storebytes_anywhere_sound; eauto.
    destruct (am_glob am)!id as [ab0|] eqn:GL.
    eapply mmatch_glob; eauto.
    apply ablock_init_sound. eapply mmatch_nonstack; eauto; congruence.
    eapply DFL; eauto. congruence.
  + rewrite PTree.gempty in H0; congruence.
  + eapply DFL; eauto. congruence.
  + eapply DFL; eauto. congruence.
  + rewrite PTree.gempty in H0; congruence.
  + rewrite PTree.gempty in H0; congruence.

- (* Nonstack *)
  assert (DFL: smatch m' b0 (plub q (am_nonstack am))).
  { eapply smatch_storebytes; eauto. eapply mmatch_nonstack; eauto. }
  assert (STK: bc b = BCstack -> smatch m' b0 (am_nonstack am)).
  { intros. apply smatch_inv with m. eapply mmatch_nonstack; eauto; congruence.
    intros. eapply Mem.loadbytes_storebytes_other; eauto. left. congruence.
  }
  inv PM; (apply DFL || apply STK; congruence).

- (* Top *)
  eapply smatch_storebytes; eauto. eapply mmatch_top; eauto.

- (* Below *)
  erewrite Mem.nextblock_storebytes by eauto. eapply mmatch_below; eauto.
Qed.

Lemma mmatch_ext:
  forall m am m',
  mmatch m am ->
  (forall b ofs n bytes, bc b <> BCinvalid -> n >= 0 -> Mem.loadbytes m' b ofs n = Some bytes -> Mem.loadbytes m b ofs n = Some bytes) ->
  Ple (Mem.nextblock m) (Mem.nextblock m') ->
  mmatch m' am.
Proof.
  intros. inv H. constructor; intros.
- apply bmatch_ext with m; auto with va.
- apply bmatch_ext with m; eauto with va.
- apply smatch_ext with m; auto with va.
- apply smatch_ext with m; auto with va.
- red; intros. exploit mmatch_below0; eauto. xomega.
Qed.

Lemma mmatch_free:
  forall m b lo hi m' am,
  Mem.free m b lo hi = Some m' ->
  mmatch m am ->
  mmatch m' am.
Proof.
  intros. apply mmatch_ext with m; auto.
  intros. eapply Mem.loadbytes_free_2; eauto.
  erewrite <- Mem.nextblock_free by eauto. xomega.
Qed.

Lemma mmatch_top':
  forall m am, mmatch m am -> mmatch m mtop.
Proof.
  intros. constructor; simpl; intros.
- apply ablock_init_sound. apply smatch_ge with (ab_summary (am_stack am)).
  eapply mmatch_stack; eauto. constructor.
- rewrite PTree.gempty in H1; discriminate.
- eapply smatch_ge. eapply mmatch_nonstack; eauto. constructor.
- eapply smatch_ge. eapply mmatch_top; eauto. constructor.
- eapply mmatch_below; eauto.
Qed.

(** Boolean equality *)

Definition mbeq (m1 m2: amem) : bool :=
  eq_aptr m1.(am_top) m2.(am_top)
  && eq_aptr m1.(am_nonstack) m2.(am_nonstack)
  && bbeq m1.(am_stack) m2.(am_stack)
  && PTree.beq bbeq m1.(am_glob) m2.(am_glob).

Lemma mbeq_sound:
  forall m1 m2, mbeq m1 m2 = true -> forall m, mmatch m m1 <-> mmatch m m2.
Proof.
  unfold mbeq; intros. InvBooleans. rewrite PTree.beq_correct in H1.
  split; intros M; inv M; constructor; intros.
- erewrite <- bbeq_sound; eauto.
- specialize (H1 id). rewrite H4 in H1. destruct (am_glob m1)!id eqn:G; try contradiction.
  erewrite <- bbeq_sound; eauto.
- rewrite <- H; eauto.
- rewrite <- H0; eauto.
- auto.
- erewrite bbeq_sound; eauto.
- specialize (H1 id). rewrite H4 in H1. destruct (am_glob m2)!id eqn:G; try contradiction.
  erewrite bbeq_sound; eauto.
- rewrite H; eauto.
- rewrite H0; eauto.
- auto.
Qed.

(** Least upper bound *)

Definition combine_ablock (ob1 ob2: option ablock) : option ablock :=
  match ob1, ob2 with
  | Some b1, Some b2 => Some (blub b1 b2)
  | _, _ => None
  end.

Definition mlub (m1 m2: amem) : amem :=
{| am_stack := blub m1.(am_stack) m2.(am_stack);
   am_glob  := PTree.combine combine_ablock m1.(am_glob) m2.(am_glob);
   am_nonstack := plub m1.(am_nonstack) m2.(am_nonstack);
   am_top := plub m1.(am_top) m2.(am_top) |}.

Lemma mmatch_lub_l:
  forall m x y, mmatch m x -> mmatch m (mlub x y).
Proof.
  intros. inv H. constructor; simpl; intros.
- apply bmatch_lub_l; auto.
- rewrite PTree.gcombine in H0 by auto. unfold combine_ablock in H0.
  destruct (am_glob x)!id as [b1|] eqn:G1;
  destruct (am_glob y)!id as [b2|] eqn:G2;
  inv H0.
  apply bmatch_lub_l; eauto.
- apply smatch_lub_l; auto.
- apply smatch_lub_l; auto.
- auto.
Qed.

Lemma mmatch_lub_r:
  forall m x y, mmatch m y -> mmatch m (mlub x y).
Proof.
  intros. inv H. constructor; simpl; intros.
- apply bmatch_lub_r; auto.
- rewrite PTree.gcombine in H0 by auto. unfold combine_ablock in H0.
  destruct (am_glob x)!id as [b1|] eqn:G1;
  destruct (am_glob y)!id as [b2|] eqn:G2;
  inv H0.
  apply bmatch_lub_r; eauto.
- apply smatch_lub_r; auto.
- apply smatch_lub_r; auto.
- auto.
Qed.

End MATCH.

(** * Monotonicity properties when the block classification changes. *)

Lemma genv_match_exten:
  forall ge (bc1 bc2: block_classification),
  genv_match bc1 ge ->
  (forall b id, bc1 b = BCglob id <-> bc2 b = BCglob id) ->
  (forall b, bc1 b = BCother -> bc2 b = BCother) ->
  genv_match bc2 ge.
Proof.
  intros. destruct H as [A B]. split; intros.
- rewrite <- H0. eauto.
- exploit B; eauto. destruct (bc1 b) eqn:BC1.
  + intuition congruence.
  + rewrite H0 in BC1. intuition congruence.
  + intuition congruence.
  + erewrite H1 by eauto. intuition congruence.
Qed.

Lemma romatch_exten:
  forall (bc1 bc2: block_classification) m rm,
  romatch bc1 m rm ->
  (forall b id, bc2 b = BCglob id <-> bc1 b = BCglob id) ->
  romatch bc2 m rm.
Proof.
  intros; red; intros. rewrite H0 in H1. exploit H; eauto. intros (A & B & C).
  split; auto. split; auto.
  assert (PM: forall b ofs p, pmatch bc1 b ofs p -> pmatch bc1 b ofs (ab_summary ab) -> pmatch bc2 b ofs p).
  {
    intros.
    assert (pmatch bc1 b0 ofs Glob) by (eapply pmatch_ge; eauto).
    inv H5.
    assert (bc2 b0 = BCglob id0) by (rewrite H0; auto).
    inv H3; econstructor; eauto with va.
  }
  assert (VM: forall v x, vmatch bc1 v x -> vmatch bc1 v (Ifptr (ab_summary ab)) -> vmatch bc2 v x).
  {
    intros. inv H3; constructor; auto; inv H4; eapply PM; eauto.
  }
  destruct B as [[B1 B2] B3]. split. split.
- intros. apply VM; eauto.
- intros. apply PM; eauto.
- intros. apply VM; eauto.
Qed.

Definition bc_incr (bc1 bc2: block_classification) : Prop :=
  forall b, bc1 b <> BCinvalid -> bc2 b = bc1 b.

Section MATCH_INCR.

Variables bc1 bc2: block_classification.
Hypothesis INCR: bc_incr bc1 bc2.

Lemma pmatch_incr: forall b ofs p, pmatch bc1 b ofs p -> pmatch bc2 b ofs p.
Proof.
  induction 1;
  assert (bc2 b = bc1 b) by (apply INCR; congruence);
  econstructor; eauto with va. rewrite H0; eauto.
Qed.

Lemma vmatch_incr: forall v x, vmatch bc1 v x -> vmatch bc2 v x.
Proof.
  induction 1; constructor; auto; apply pmatch_incr; auto.
Qed.

Lemma smatch_incr: forall m b p, smatch bc1 m b p -> smatch bc2 m b p.
Proof.
  intros. destruct H as [A B]. split; intros.
  apply vmatch_incr; eauto.
  apply pmatch_incr; eauto.
Qed.

Lemma bmatch_incr: forall m b ab, bmatch bc1 m b ab -> bmatch bc2 m b ab.
Proof.
  intros. destruct H as [B1 B2]. split.
  apply smatch_incr; auto.
  intros. apply vmatch_incr; eauto.
Qed.

End MATCH_INCR.

(** * Matching and memory injections. *)

Definition inj_of_bc (bc: block_classification) : meminj :=
  fun b => match bc b with BCinvalid => None | _ => Some(b, 0) end.

Lemma inj_of_bc_valid:
  forall (bc: block_classification) b, bc b <> BCinvalid -> inj_of_bc bc b = Some(b, 0).
Proof.
  intros. unfold inj_of_bc. destruct (bc b); congruence.
Qed.

Lemma inj_of_bc_inv:
  forall (bc: block_classification) b b' delta,
  inj_of_bc bc b = Some(b', delta) -> bc b <> BCinvalid /\ b' = b /\ delta = 0.
Proof.
  unfold inj_of_bc; intros. destruct (bc b); intuition congruence.
Qed.

Lemma pmatch_inj:
  forall bc b ofs p, pmatch bc b ofs p -> inj_of_bc bc b = Some(b, 0).
Proof.
  intros. apply inj_of_bc_valid. inv H; congruence.
Qed.

Lemma vmatch_inj:
  forall bc v x, vmatch bc v x -> Val.inject (inj_of_bc bc) v v.
Proof.
  induction 1; econstructor.
  eapply pmatch_inj; eauto. rewrite Ptrofs.add_zero; auto.
  eapply pmatch_inj; eauto. rewrite Ptrofs.add_zero; auto.
Qed.

Lemma vmatch_list_inj:
  forall bc vl xl, list_forall2 (vmatch bc) vl xl -> Val.inject_list (inj_of_bc bc) vl vl.
Proof.
  induction 1; constructor. eapply vmatch_inj; eauto. auto.
Qed.

Lemma mmatch_inj:
  forall bc m am, mmatch bc m am -> bc_below bc (Mem.nextblock m) -> Mem.inject (inj_of_bc bc) m m.
Proof.
  intros. constructor. constructor.
- (* perms *)
  intros. exploit inj_of_bc_inv; eauto. intros (A & B & C); subst.
  rewrite Z.add_0_r. auto.
- (* alignment *)
  intros. exploit inj_of_bc_inv; eauto. intros (A & B & C); subst.
  apply Z.divide_0_r.
- (* contents *)
  intros. exploit inj_of_bc_inv; eauto. intros (A & B & C); subst.
  rewrite Z.add_0_r.
  set (mv := ZMap.get ofs (PMap.get b1 (Mem.mem_contents m))).
  assert (Mem.loadbytes m b1 ofs 1 = Some (mv :: nil)).
  {
    Local Transparent Mem.loadbytes.
    unfold Mem.loadbytes. rewrite pred_dec_true. reflexivity.
    red; intros. replace ofs0 with ofs by omega. auto.
  }
  destruct mv; econstructor. destruct v; econstructor.
  apply inj_of_bc_valid.
  assert (PM: pmatch bc b i Ptop).
  { exploit mmatch_top; eauto. intros [P Q].
    eapply pmatch_top'. eapply Q; eauto. }
  inv PM; auto.
  rewrite Ptrofs.add_zero; auto.
- (* free blocks *)
  intros. unfold inj_of_bc. erewrite bc_below_invalid; eauto.
- (* mapped blocks *)
  intros. exploit inj_of_bc_inv; eauto. intros (A & B & C); subst.
  apply H0; auto.
- (* overlap *)
  red; intros.
  exploit inj_of_bc_inv. eexact H2. intros (A1 & B & C); subst.
  exploit inj_of_bc_inv. eexact H3. intros (A2 & B & C); subst.
  auto.
- (* overflow *)
  intros. exploit inj_of_bc_inv; eauto. intros (A & B & C); subst.
  rewrite Z.add_0_r. split. omega. apply Ptrofs.unsigned_range_2.
- (* perm inv *)
  intros. exploit inj_of_bc_inv; eauto. intros (A & B & C); subst.
  rewrite Z.add_0_r in H2. auto.
Qed.

Lemma inj_of_bc_preserves_globals:
  forall bc ge, genv_match bc ge -> meminj_preserves_globals ge (inj_of_bc bc).
Proof.
  intros. destruct H as [A B].
  split. intros. apply inj_of_bc_valid. rewrite A in H. congruence.
  split. intros. apply inj_of_bc_valid. apply B.
    rewrite Genv.find_var_info_iff in H. eapply Genv.genv_defs_range; eauto.
  intros. exploit inj_of_bc_inv; eauto. intros (P & Q & R). auto.
Qed.

Lemma pmatch_inj_top:
  forall bc b b' delta ofs, inj_of_bc bc b = Some(b', delta) -> pmatch bc b ofs Ptop.
Proof.
  intros. exploit inj_of_bc_inv; eauto. intros (A & B & C). constructor; auto.
Qed.

Lemma vmatch_inj_top:
  forall bc v v', Val.inject (inj_of_bc bc) v v' -> vmatch bc v Vtop.
Proof.
  intros. inv H; constructor. eapply pmatch_inj_top; eauto.
Qed.

Lemma mmatch_inj_top:
  forall bc m m', Mem.inject (inj_of_bc bc) m m' -> mmatch bc m mtop.
Proof.
  intros.
  assert (SM: forall b, bc b <> BCinvalid -> smatch bc m b Ptop).
  {
    intros; split; intros.
    - exploit Mem.load_inject. eauto. eauto. apply inj_of_bc_valid; auto.
      intros (v' & A & B). eapply vmatch_inj_top; eauto.
    - exploit Mem.loadbytes_inject. eauto. eauto. apply inj_of_bc_valid; auto.
      intros (bytes' & A & B). inv B. inv H4. inv H8. eapply pmatch_inj_top; eauto.
  }
  constructor; simpl; intros.
  - apply ablock_init_sound. apply SM. congruence.
  - rewrite PTree.gempty in H1; discriminate.
  - apply SM; auto.
  - apply SM; auto.
  - red; intros. eapply Mem.valid_block_inject_1. eapply inj_of_bc_valid; eauto. eauto.
Qed.

(** * Abstracting RTL register environments *)

Module AVal <: SEMILATTICE_WITH_TOP.

  Definition t := aval.
  Definition eq (x y: t) := (x = y).
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).
  Definition beq (x y: t) : bool := proj_sumbool (eq_aval x y).
  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof. unfold beq; intros. InvBooleans. auto. Qed.
  Definition ge := vge.
  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof. unfold eq, ge; intros. subst y. apply vge_refl. Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof. unfold ge; intros. eapply vge_trans; eauto. Qed.
  Definition bot : t := Vbot.
  Lemma ge_bot: forall x, ge x bot.
  Proof. intros. constructor. Qed.
  Definition top : t := Vtop.
  Lemma ge_top: forall x, ge top x.
  Proof. intros. apply vge_top. Qed.
  Definition lub := vlub.
  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof vge_lub_l.
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof vge_lub_r.
End AVal.

Module AE := LPMap(AVal).

Definition aenv := AE.t.

Section MATCHENV.

Variable bc: block_classification.

Definition ematch (e: regset) (ae: aenv) : Prop :=
  forall r, vmatch bc e#r (AE.get r ae).

Lemma ematch_ge:
  forall e ae1 ae2,
  ematch e ae1 -> AE.ge ae2 ae1 -> ematch e ae2.
Proof.
  intros; red; intros. apply vmatch_ge with (AE.get r ae1); auto. apply H0.
Qed.

Lemma ematch_update:
  forall e ae v av r,
  ematch e ae -> vmatch bc v av -> ematch (e#r <- v) (AE.set r av ae).
Proof.
  intros; red; intros. rewrite AE.gsspec. rewrite PMap.gsspec.
  destruct (peq r0 r); auto.
  red; intros. specialize (H xH). subst ae. simpl in H. inv H.
  unfold AVal.eq; red; intros. subst av. inv H0.
Qed.

Fixpoint einit_regs (rl: list reg) : aenv :=
  match rl with
  | r1 :: rs => AE.set r1 (Ifptr Nonstack) (einit_regs rs)
  | nil => AE.top
  end.

Lemma ematch_init:
  forall rl vl,
  (forall v, In v vl -> vmatch bc v (Ifptr Nonstack)) ->
  ematch (init_regs vl rl) (einit_regs rl).
Proof.
  induction rl; simpl; intros.
- red; intros. rewrite Regmap.gi. simpl AE.get. rewrite PTree.gempty.
  constructor.
- destruct vl as [ | v1 vs ].
  + assert (ematch (init_regs nil rl) (einit_regs rl)).
    { apply IHrl. simpl; tauto. }
    replace (init_regs nil rl) with (Regmap.init Vundef) in H0 by (destruct rl; auto).
    red; intros. rewrite AE.gsspec. destruct (peq r a).
    rewrite Regmap.gi. constructor.
    apply H0.
    red; intros EQ; rewrite EQ in H0. specialize (H0 xH). simpl in H0. inv H0.
    unfold AVal.eq, AVal.bot. congruence.
  + assert (ematch (init_regs vs rl) (einit_regs rl)).
    { apply IHrl. eauto with coqlib. }
    red; intros. rewrite Regmap.gsspec. rewrite AE.gsspec. destruct (peq r a).
    auto with coqlib.
    apply H0.
    red; intros EQ; rewrite EQ in H0. specialize (H0 xH). simpl in H0. inv H0.
    unfold AVal.eq, AVal.bot. congruence.
Qed.

Fixpoint eforget (rl: list reg) (ae: aenv) {struct rl} : aenv :=
  match rl with
  | nil => ae
  | r1 :: rs => eforget rs (AE.set r1 Vtop ae)
  end.

Lemma eforget_ge:
  forall rl ae, AE.ge (eforget rl ae) ae.
Proof.
  unfold AE.ge; intros. revert rl ae; induction rl; intros; simpl.
  apply AVal.ge_refl. apply AVal.eq_refl.
  destruct ae. unfold AE.get at 2. apply AVal.ge_bot.
  eapply AVal.ge_trans. apply IHrl. rewrite AE.gsspec.
  destruct (peq p a). apply AVal.ge_top. apply AVal.ge_refl. apply AVal.eq_refl.
  congruence.
  unfold AVal.eq, Vtop, AVal.bot. congruence.
Qed.

Lemma ematch_forget:
  forall e rl ae, ematch e ae -> ematch e (eforget rl ae).
Proof.
  intros. eapply ematch_ge; eauto. apply eforget_ge.
Qed.

End MATCHENV.

Lemma ematch_incr:
  forall bc bc' e ae, ematch bc e ae -> bc_incr bc bc' -> ematch bc' e ae.
Proof.
  intros; red; intros. apply vmatch_incr with bc; auto.
Qed.

(** * Lattice for dataflow analysis *)

Module VA <: SEMILATTICE.

  Inductive t' := Bot | State (ae: aenv) (am: amem).
  Definition t := t'.

  Definition eq (x y: t) :=
    match x, y with
    | Bot, Bot => True
    | State ae1 am1, State ae2 am2 =>
        AE.eq ae1 ae2 /\ forall bc m, mmatch bc m am1 <-> mmatch bc m am2
    | _, _ => False
    end.

  Lemma eq_refl: forall x, eq x x.
  Proof.
    destruct x; simpl. auto. split. apply AE.eq_refl. tauto.
  Qed.
  Lemma eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    destruct x, y; simpl; auto. intros [A B].
    split. apply AE.eq_sym; auto. intros. rewrite B. tauto.
  Qed.
  Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    destruct x, y, z; simpl; try tauto. intros [A B] [C D]; split.
    eapply AE.eq_trans; eauto.
    intros. rewrite B; auto.
  Qed.

  Definition beq (x y: t) : bool :=
    match x, y with
    | Bot, Bot => true
    | State ae1 am1, State ae2 am2 => AE.beq ae1 ae2 && mbeq am1 am2
    | _, _ => false
    end.

  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    destruct x, y; simpl; intros.
    auto.
    congruence.
    congruence.
    InvBooleans; split.
    apply AE.beq_correct; auto.
    intros. apply mbeq_sound; auto.
  Qed.

  Definition ge (x y: t) : Prop :=
    match x, y with
    | _, Bot => True
    | Bot, _ => False
    | State ae1 am1, State ae2 am2 => AE.ge ae1 ae2 /\ forall bc m, mmatch bc m am2 -> mmatch bc m am1
    end.

  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    destruct x, y; simpl; try tauto. intros [A B]; split.
    apply AE.ge_refl; auto.
    intros. rewrite B; auto.
  Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    destruct x, y, z; simpl; try tauto. intros [A B] [C D]; split.
    eapply AE.ge_trans; eauto.
    eauto.
  Qed.

  Definition bot : t := Bot.
  Lemma ge_bot: forall x, ge x bot.
  Proof.
    destruct x; simpl; auto.
  Qed.

  Definition lub (x y: t) : t :=
    match x, y with
    | Bot, _ => y
    | _, Bot => x
    | State ae1 am1, State ae2 am2 => State (AE.lub ae1 ae2) (mlub am1 am2)
    end.

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    destruct x, y.
    apply ge_refl; apply eq_refl.
    simpl. auto.
    apply ge_refl; apply eq_refl.
    simpl. split. apply AE.ge_lub_left. intros; apply mmatch_lub_l; auto.
  Qed.
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    destruct x, y.
    apply ge_refl; apply eq_refl.
    apply ge_refl; apply eq_refl.
    simpl. auto.
    simpl. split. apply AE.ge_lub_right. intros; apply mmatch_lub_r; auto.
  Qed.

End VA.

Hint Constructors cmatch : va.
Hint Constructors pmatch: va.
Hint Constructors vmatch: va.
Hint Resolve cnot_sound symbol_address_sound
       shl_sound shru_sound shr_sound
       and_sound or_sound xor_sound notint_sound
       ror_sound rolm_sound
       neg_sound add_sound sub_sound
       mul_sound mulhs_sound mulhu_sound
       divs_sound divu_sound mods_sound modu_sound shrx_sound
       shll_sound shrl_sound shrlu_sound
       andl_sound orl_sound xorl_sound notl_sound roll_sound rorl_sound
       negl_sound addl_sound subl_sound
       mull_sound mullhs_sound mullhu_sound
       divls_sound divlu_sound modls_sound modlu_sound shrxl_sound
       offset_ptr_sound
       negf_sound absf_sound
       addf_sound subf_sound mulf_sound divf_sound
       negfs_sound absfs_sound
       addfs_sound subfs_sound mulfs_sound divfs_sound
       zero_ext_sound sign_ext_sound longofint_sound longofintu_sound
       singleoffloat_sound floatofsingle_sound
       intoffloat_sound intuoffloat_sound floatofint_sound floatofintu_sound
       intofsingle_sound intuofsingle_sound singleofint_sound singleofintu_sound
       longoffloat_sound longuoffloat_sound floatoflong_sound floatoflongu_sound
       longofsingle_sound longuofsingle_sound singleoflong_sound singleoflongu_sound
       longofwords_sound loword_sound hiword_sound
       cmpu_bool_sound cmp_bool_sound cmplu_bool_sound cmpl_bool_sound
       cmpf_bool_sound cmpfs_bool_sound
       maskzero_sound : va.
