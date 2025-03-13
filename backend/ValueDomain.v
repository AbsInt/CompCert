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
Require Import Zwf Coqlib Maps Zbits Integers Floats Lattice.
Require Import Compopts AST.
Require Import Values Memory Globalenvs Builtins Events.
Require Import Registers RTL.
Require Conventions1.

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

Global Hint Extern 2 (_ = _) => congruence : va.
Global Hint Extern 2 (_ <> _) => congruence : va.
Global Hint Extern 2 (_ < _) => extlia : va.
Global Hint Extern 2 (_ <= _) => extlia : va.
Global Hint Extern 2 (_ > _) => extlia : va.
Global Hint Extern 2 (_ >= _) => extlia : va.

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

Lemma ge_pincl: forall p q, pge p q -> pincl q p = true.
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
  | _   => if va_strict tt then Bnone else Btop
  end.

Lemma cmp_different_blocks_none:
  forall c, cmatch None (cmp_different_blocks c).
Proof.
  unfold cmp_different_blocks. destruct c, (va_strict tt); constructor.
Qed.

Lemma cmp_different_blocks_sound:
  forall c, cmatch (Val.cmp_different_blocks c) (cmp_different_blocks c).
Proof.
  unfold cmp_different_blocks. destruct c, (va_strict tt); constructor.
Qed.

Definition pcmp (c: comparison) (p1 p2: aptr) : abool :=
  match p1, p2 with
  | Pbot, _ | _, Pbot => Bnone
  | Gl id1 ofs1, Gl id2 ofs2 => if peq id1 id2 then Maybe (Ptrofs.cmpu c ofs1 ofs2) else Btop
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
  - apply SAME. eapply bc_stack; eauto.
Qed.

Lemma pcmp_none:
  forall c p1 p2, cmatch None (pcmp c p1 p2).
Proof.
  intros.
  unfold pcmp; destruct p1; try constructor; destruct p2;
  try (destruct (peq id id0));  try constructor; try (apply cmp_different_blocks_none).
Qed.

(** * Abstracting values *)

Inductive aval : Type :=
  | Vbot                     (**r bottom (empty set of values) *)
  | I (n: int)               (**r exactly [Vint n] *)
  | IU (n: int)              (**r [Vint n] or [Vundef] *)
  | Uns (p: aptr) (n: Z)     (**r a [n]-bit unsigned integer, or [Vundef] *)
  | Sgn (p: aptr) (n: Z)     (**r a [n]-bit signed integer, or [Vundef] *)
  | L (n: int64)             (**r exactly [Vlong n] *)
  | F (f: float)             (**r exactly [Vfloat f] *)
  | FS (f: float32)          (**r exactly [Vsingle f] *)
  | Num (p: aptr)            (**r any number, or [Vundef] *)
  | Ptr (p: aptr)            (**r a pointer from the set [p], or [Vundef] *)
  | Ifptr (p: aptr).         (**r a pointer from the set [p], or a number, or [Vundef] *)

(** The "top" of the value domain is defined as any pointer, or any
    number, or [Vundef]. *)

Definition Vtop := Ifptr Ptop.

(** The [p] parameter (an abstract pointer) to [Uns], [Sgn] and [Num] helps keeping
  track of pointers that leak through arithmetic operations such as shifts.
  See the section "Tracking leakage of pointers" below. *)

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
  | vmatch_iu: forall i, vmatch (Vint i) (IU i)
  | vmatch_iu_undef: forall i, vmatch Vundef (IU i)
  | vmatch_Uns: forall p i n, 0 <= n -> is_uns n i -> vmatch (Vint i) (Uns p n)
  | vmatch_Uns_undef: forall p n, vmatch Vundef (Uns p n)
  | vmatch_Sgn: forall p i n, 0 < n -> is_sgn n i -> vmatch (Vint i) (Sgn p n)
  | vmatch_Sgn_undef: forall p n, vmatch Vundef (Sgn p n)
  | vmatch_l: forall i, vmatch (Vlong i) (L i)
  | vmatch_f: forall f, vmatch (Vfloat f) (F f)
  | vmatch_s: forall f, vmatch (Vsingle f) (FS f)
  | vmatch_num_undef: forall p, vmatch Vundef (Num p)
  | vmatch_num_i: forall i p, vmatch (Vint i) (Num p)
  | vmatch_num_l: forall i p, vmatch (Vlong i) (Num p)
  | vmatch_num_f: forall f p, vmatch (Vfloat f) (Num p)
  | vmatch_num_s: forall f p, vmatch (Vsingle f) (Num p)
  | vmatch_ptr: forall b ofs p, pmatch b ofs p -> vmatch (Vptr b ofs) (Ptr p)
  | vmatch_ptr_undef: forall p, vmatch Vundef (Ptr p)
  | vmatch_ifptr_undef: forall p, vmatch Vundef (Ifptr p)
  | vmatch_ifptr_i: forall i p, vmatch (Vint i) (Ifptr p)
  | vmatch_ifptr_l: forall i p, vmatch (Vlong i) (Ifptr p)
  | vmatch_ifptr_f: forall f p, vmatch (Vfloat f) (Ifptr p)
  | vmatch_ifptr_s: forall f p, vmatch (Vsingle f) (Ifptr p)
  | vmatch_ifptr_p: forall b ofs p, pmatch b ofs p -> vmatch (Vptr b ofs) (Ifptr p).

Hint Extern 1 (vmatch _ _) => constructor : va.

Lemma vmatch_num:
  forall v p,
  match v with Vptr _ _ => False | _ => True end ->
  vmatch v (Num p).
Proof.
  intros. destruct v; auto with va; contradiction.
Qed.

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

(** Some properties of [is_uns] and [is_sgn]. *)

Lemma is_uns_mon: forall n1 n2 i, is_uns n1 i -> n1 <= n2 -> is_uns n2 i.
Proof.
  intros; red; intros. apply H; lia.
Qed.

Lemma is_sgn_mon: forall n1 n2 i, is_sgn n1 i -> n1 <= n2 -> is_sgn n2 i.
Proof.
  intros; red; intros. apply H; lia.
Qed.

Lemma is_uns_sgn: forall n1 n2 i, is_uns n1 i -> n1 < n2 -> is_sgn n2 i.
Proof.
  intros; red; intros. rewrite ! H by lia. auto.
Qed.

Definition usize := Int.size.

Definition ssize (i: int) := Int.size (if Int.lt i Int.zero then Int.not i else i) + 1.

Lemma usize_pos: forall n, 0 <= usize n.
Proof.
  unfold usize; intros. generalize (Int.size_range n); lia.
Qed.

Lemma ssize_pos: forall n, 0 < ssize n.
Proof.
  unfold ssize; intros.
  generalize (Int.size_range (if Int.lt n Int.zero then Int.not n else n)); lia.
Qed.

Lemma is_uns_usize:
  forall i, is_uns (usize i) i.
Proof.
  unfold usize; intros; red; intros.
  apply Int.bits_size_2. lia.
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
  rewrite <- ! Int.bits_not by lia.
  rewrite ! Int.bits_size_2 by lia.
  auto.
- rewrite ! Int.bits_size_2 by lia.
  auto.
Qed.

Lemma is_uns_zero_ext:
  forall n i, is_uns n i <-> Int.zero_ext n i = i.
Proof.
  intros; split; intros.
  Int.bit_solve. destruct (zlt i0 n); auto. symmetry; apply H; auto. lia.
  rewrite <- H. red; intros. rewrite Int.bits_zero_ext by lia. rewrite zlt_false by lia. auto.
Qed.

Lemma is_sgn_sign_ext:
  forall n i, 0 < n -> (is_sgn n i <-> Int.sign_ext n i = i).
Proof.
  intros; split; intros.
  Int.bit_solve. destruct (zlt i0 n); auto.
  transitivity (Int.testbit i (Int.zwordsize - 1)).
  apply H0; lia. symmetry; apply H0; lia.
  rewrite <- H0. red; intros. rewrite ! Int.bits_sign_ext by lia.
  f_equal. transitivity (n-1). destruct (zlt m n); lia.
  destruct (zlt (Int.zwordsize - 1) n); lia.
Qed.

Lemma is_zero_ext_uns:
  forall i n m,
  is_uns m i \/ n <= m -> is_uns m (Int.zero_ext n i).
Proof.
  intros. red; intros. rewrite Int.bits_zero_ext by lia.
  destruct (zlt m0 n); auto. destruct H. apply H; lia. extlia.
Qed.

Lemma is_zero_ext_sgn:
  forall i n m,
  n < m ->
  is_sgn m (Int.zero_ext n i).
Proof.
  intros. red; intros. rewrite ! Int.bits_zero_ext by lia.
  transitivity false. apply zlt_false; lia.
  symmetry; apply zlt_false; lia.
Qed.

Lemma is_sign_ext_uns:
  forall i n m,
  0 <= m < n ->
  is_uns m i ->
  is_uns m (Int.sign_ext n i).
Proof.
  intros; red; intros. rewrite Int.bits_sign_ext by lia.
  apply H0. destruct (zlt m0 n); lia. destruct (zlt m0 n); lia.
Qed.

Lemma is_sign_ext_sgn:
  forall i n m,
  0 < n -> 0 < m ->
  is_sgn m i \/ n <= m -> is_sgn m (Int.sign_ext n i).
Proof.
  intros. apply is_sgn_sign_ext; auto.
  destruct (zlt m n). destruct H1. apply is_sgn_sign_ext in H1; auto.
  rewrite <- H1. rewrite (Int.sign_ext_widen i) by lia. apply Int.sign_ext_idem; auto.
  extlia.
  apply Int.sign_ext_widen; lia.
Qed.

Lemma is_uns_wordsize: forall i, is_uns Int.zwordsize i.
Proof.
  intros; red; intros. lia.
Qed.

Lemma is_sgn_wordsize: forall i, is_sgn Int.zwordsize i.
Proof.
  intros; red; intros. f_equal. lia.
Qed.

Hint Resolve is_uns_mon is_sgn_mon is_uns_sgn is_uns_usize is_sgn_ssize
             is_uns_wordsize is_sgn_wordsize usize_pos ssize_pos : va.

Lemma is_uns_0:
  forall n, is_uns 0 n -> n = Int.zero.
Proof.
  intros. apply Int.same_bits_eq; intros.
  rewrite Int.bits_zero. apply H; lia.
Qed.

Lemma is_uns_1:
  forall n, is_uns 1 n -> n = Int.zero \/ n = Int.one.
Proof.
  intros. destruct (Int.testbit n 0) eqn:B0; [right|left]; apply Int.same_bits_eq; intros.
  rewrite Int.bits_one. destruct (zeq i 0). subst i; auto. apply H; lia.
  rewrite Int.bits_zero. destruct (zeq i 0). subst i; auto. apply H; lia.
Qed.

Lemma is_uns_range: forall z n,
  0 <= n -> 0 <= z < two_p n -> is_uns n (Int.repr z).
Proof.
  intros; red; intros. rewrite Int.testbit_repr by auto.
  apply (Zbits_unsigned_range n); auto.
Qed.

Lemma range_is_uns: forall i n,
  0 <= n -> is_uns n i -> 0 <= Int.unsigned i < two_p n.
Proof.
  intros. destruct (zlt n Int.zwordsize).
- apply is_uns_zero_ext in H0; auto.
  rewrite <- H0. rewrite Int.zero_ext_mod by lia.
  auto using Z_mod_lt, two_p_gt_ZERO.
- assert (Int.modulus <= two_p n).
  { rewrite Int.modulus_power. apply two_p_monotone. generalize Int.wordsize_pos; lia. }
  generalize (Int.unsigned_range i). lia.
Qed.

Lemma is_sgn_range: forall z n,
  0 < n -> -(two_p (n - 1)) <= z < two_p (n - 1) -> is_sgn n (Int.repr z).
Proof.
  intros; red; intros. rewrite ! Int.testbit_repr by lia.
  apply (Zbits_signed_range (n - 1)); lia.
Qed.

Lemma range_is_sgn: forall i n,
  0 < n -> is_sgn n i -> -(two_p (n - 1)) <= Int.signed i < two_p (n - 1).
Proof.
  intros. destruct (zlt n Int.zwordsize).
- apply is_sgn_sign_ext in H0; auto. rewrite <- H0. apply Int.sign_ext_range; lia.
- assert (Int.half_modulus <= two_p (n - 1)).
  { rewrite Int.half_modulus_power. apply two_p_monotone. generalize Int.wordsize_pos; lia. }
  generalize (Int.signed_range i). unfold Int.min_signed, Int.max_signed. lia.
Qed.

Definition urange (a: aval) : Z :=
  match a with
  | I n | IU n => usize n
  | Uns p n => n
  | _ => Int.zwordsize
  end.

Definition srange (a: aval) : Z :=
  match a with
  | I n | IU n => ssize n
  | Uns p n => n + 1
  | Sgn p n => n
  | _ => Int.zwordsize
  end.

Lemma urange_sound: forall i a,
  vmatch (Vint i) a -> 0 <= urange a /\ is_uns (urange a) i.
Proof.
  intros. pose proof Int.wordsize_pos. inv H; simpl; auto with va.
Qed.

Lemma srange_sound: forall i a,
  vmatch (Vint i) a -> 0 < srange a /\ is_sgn (srange a) i.
Proof.
  intros. pose proof Int.wordsize_pos. inv H; simpl; eauto with va.
Qed.

(** Tracking leakage of pointers through arithmetic operations.

In the CompCert semantics, arithmetic operations (e.g. "xor") applied
to pointer values are undefined or produce the [Vundef] result.
If we later use the result as the address of a memory access,
the memory access will fail.  Hence, in strict mode, the alias
analysis can ignore these pointers that were transformed by arithmetic
operations.

In real code, arithmetic over pointers occurs, and can produce valid
pointers.  For example, a bitwise "and" can be used to realign a pointer.
Hence, in conservative mode, the alias analysis must track these
pointers that were transformed by arithmetic operations.

This is the purpose of the "provenance" argument [p] to the abstract values
[Num p], [Uns p n], and [Sgn p n].  [p] is an abstract pointer that
over-approximates all the pointer values that may have been used
as integers to produce this numerical value.  If a memory access
is performed at an address that matches [Num p], [Uns p n], or [Sgn p n],
the value analysis considers that the abstract pointer [p] is accessed.
Likewise, if one of these abstract values is joined with a pointer
abstract value [Ptr q] or [Ifptr q], the pointer abstract value
[Ifptr (plub p q)] is produced.

To define the provenance [p] of the result of an arithmetic operation,
we follow the same policy as GCC: "undefined" arithmetic operations
involving pointer arguments can produce a pointer, but not any
pointer, just a pointer to the same block but possibly with a
different offset.  Hence, if the operation has a pointer to abstract
region [p] as argument, the result value can be a pointer to abstract
region [poffset p].

We encapsulate this reasoning in the following [ntop1] and [ntop2] functions
("numerical top"). *)

Definition provenance (x: aval) : aptr :=
  match x with
  | Ptr p | Ifptr p => poffset p
  | Uns p _ | Sgn p _ | Num p => p
  | _ => Pbot
  end.

Definition ntop : aval := Num Pbot.

Definition ntop1 (x: aval) : aval := Num (provenance x).

Definition ntop2 (x y: aval) : aval := Num (plub (provenance x) (provenance y)).

(** Embedded C code often uses integer literals as absolute addresses
for loads and stores, e.g. [ int * device = (int * ) 0x1000; *device = 12; ].
In conservative mode, we analyze these loads and stores as potentially
accessing any memory location except stack blocks, i.e. as a [Nonstack]
access.  

The following functions determine the provenance to use for integer
literals when they are used in a pointer context.  The null pointer
(literal 0) is treated specially: even in conservative mode, accesses
to address 0 are considered illegal. *)

Definition int_provenance (i: int) : aptr :=
  if va_strict tt || Int.eq i Int.zero then Pbot else Nonstack.

Definition long_provenance (i: int64) : aptr :=
  if va_strict tt || Int64.eq i Int64.zero then Pbot else Nonstack.

(** Smart constructors for [Uns] and [Sgn]. *)

Definition uns (p: aptr) (n: Z) : aval :=
  if zle n 0 then IU Int.zero
  else if zle n 1 then Uns p 1
  else if zle n 7 then Uns p 7
  else if zle n 8 then Uns p 8
  else if zle n 15 then Uns p 15
  else if zle n 16 then Uns p 16
  else Num p.

Definition sgn (p: aptr) (n: Z) : aval :=
  if zle n 8 then Sgn p 8 else if zle n 16 then Sgn p 16 else Num p.

Lemma vmatch_uns':
  forall p i n, is_uns (Z.max 0 n) i -> vmatch (Vint i) (uns p n).
Proof.
  intros.
  assert (A: forall n', n' >= 0 -> n' >= n -> is_uns n' i) by (eauto with va).
  unfold uns. repeat destruct zle; auto with va.
  replace (Z.max 0 n) with 0 in H by lia.
  apply is_uns_0 in H.
  subst i; constructor.
Qed.

Lemma vmatch_uns:
  forall p i n, is_uns n i -> vmatch (Vint i) (uns p n).
Proof.
  intros. apply vmatch_uns'. eauto with va.
Qed.

Lemma vmatch_uns_undef: forall p n, vmatch Vundef (uns p n).
Proof.
  intros. unfold uns. repeat destruct zle; auto with va.
Qed.

Lemma vmatch_sgn':
  forall p i n, is_sgn (Z.max 1 n) i -> vmatch (Vint i) (sgn p n).
Proof.
  intros.
  assert (A: forall n', n' >= 1 -> n' >= n -> is_sgn n' i) by (eauto with va).
  unfold sgn. repeat destruct zle; auto with va.
Qed.

Lemma vmatch_sgn:
  forall p i n, is_sgn n i -> vmatch (Vint i) (sgn p n).
Proof.
  intros. apply vmatch_sgn'. eauto with va.
Qed.

Lemma vmatch_sgn_undef: forall p n, vmatch Vundef (sgn p n).
Proof.
  intros. unfold sgn. repeat destruct zle; auto with va.
Qed.

Lemma vmatch_norm_bool_uns: forall v p, vmatch (Val.norm_bool v) (Uns p 1).
Proof.
  intros. destruct (Val.norm_bool_cases v) as [A | [A | A]]; rewrite A; constructor.
  lia. apply is_uns_zero_ext; auto.
  lia. apply is_uns_zero_ext; auto.
Qed.

Hint Resolve vmatch_uns vmatch_uns_undef vmatch_sgn vmatch_sgn_undef vmatch_norm_bool_uns: va.

Lemma vmatch_Uns_1:
  forall p v, vmatch v (Uns p 1) -> v = Vundef \/ v = Vint Int.zero \/ v = Vint Int.one.
Proof.
  intros. inv H; auto. right. exploit is_uns_1; eauto. intuition congruence.
Qed.

Lemma vmatch_Uns_0:
  forall p v, vmatch v (Uns p 0) -> v = Vundef \/ v = Vint Int.zero.
Proof.
  intros. inv H; auto. right. exploit is_uns_0; eauto. intuition congruence.
Qed.


(** Ordering *)

Inductive vge: aval -> aval -> Prop :=
  | vge_bot: forall v, vge v Vbot
  | vge_i: forall i, vge (I i) (I i)
  | vge_l: forall i, vge (L i) (L i)
  | vge_f: forall f, vge (F f) (F f)
  | vge_s: forall f, vge (FS f) (FS f)
  | vge_iu: forall i, vge (IU i) (IU i)
  | vge_iu_i: forall i, vge (IU i) (I i)
  | vge_uns_i: forall p n i, 0 <= n -> is_uns n i -> vge (Uns p n) (I i)
  | vge_uns_iu: forall p n i, 0 <= n -> is_uns n i -> vge (Uns p n) (IU i)
  | vge_uns_uns: forall p1 n1 p2 n2, n1 >= n2 -> pge p1 p2 -> vge (Uns p1 n1) (Uns p2 n2)
  | vge_sgn_i: forall p n i, 0 < n -> is_sgn n i -> vge (Sgn p n) (I i)
  | vge_sgn_iu: forall p n i, 0 < n -> is_sgn n i -> vge (Sgn p n) (IU i)
  | vge_sgn_sgn: forall p1 n1 p2 n2, n1 >= n2 -> pge p1 p2 -> vge (Sgn p1 n1) (Sgn p2 n2)
  | vge_sgn_uns: forall p1 n1 p2 n2, n1 > n2 -> pge p1 p2 -> vge (Sgn p1 n1) (Uns p2 n2)
  | vge_num_i: forall p i, vge (Num p) (I i)
  | vge_num_l: forall p i, vge (Num p) (L i)
  | vge_num_f: forall p f, vge (Num p) (F f)
  | vge_num_s: forall p f, vge (Num p) (FS f)
  | vge_num_iu: forall p i, vge (Num p) (IU i)
  | vge_num_uns: forall p q n, pge p q -> vge (Num p) (Uns q n)
  | vge_num_sgn: forall p q n, pge p q -> vge (Num p) (Sgn q n)
  | vge_num_num: forall p q, pge p q -> vge (Num p) (Num q)
  | vge_p_p: forall p q, pge p q -> vge (Ptr p) (Ptr q)
  | vge_ip_p: forall p q, pge p q -> vge (Ifptr p) (Ptr q)
  | vge_ip_ip: forall p q, pge p q -> vge (Ifptr p) (Ifptr q)
  | vge_ip_i: forall  p i, vge (Ifptr p) (I i)
  | vge_ip_l: forall p i, vge (Ifptr p) (L i)
  | vge_ip_f: forall p f, vge (Ifptr p) (F f)
  | vge_ip_s: forall p f, vge (Ifptr p) (FS f)
  | vge_ip_iu: forall  p i, vge (Ifptr p) (IU i)
  | vge_ip_uns: forall p q n, pge p q -> vge (Ifptr p) (Uns q n)
  | vge_ip_sgn: forall p q n, pge p q -> vge (Ifptr p) (Sgn q n)
  | vge_ip_num: forall p q, pge p q -> vge (Ifptr p) (Num q).

Hint Constructors vge : va.

Lemma vge_top: forall x, vge Vtop x.
Proof.
  unfold Vtop; destruct x; auto with va.
Qed.

Lemma vge_refl: forall x, vge x x.
Proof.
  destruct x; auto with va.
Qed.

Hint Resolve vge_top vge_refl : va.

Lemma vge_trans: forall x y z, vge x y -> vge y z -> vge x z.
Proof.
  intros x y z XY YZ; revert y z YZ x XY.
  destruct 1; intros x V; auto with va; inv V; eauto using pge_trans with va.
Qed.

Lemma vmatch_ge:
  forall v x y, vge x y -> vmatch v y -> vmatch v x.
Proof.
  induction 1; intros V; inv V; eauto using pmatch_ge with va.
Qed.

(** A variant of the [uns] smart constructor that does not produce
    [IU Int.zero], for use in [vlub] below. *)

Definition uns1 (p: aptr) (n: Z) : aval :=
  if zle n 1 then Uns p 1
  else if zle n 7 then Uns p 7
  else if zle n 8 then Uns p 8
  else if zle n 15 then Uns p 15
  else if zle n 16 then Uns p 16
  else Num p.

(** Least upper bound *)

Definition vlub_int (cstr: int -> aval) (i1 i2: int) : aval :=
  if Int.eq i1 i2 then cstr i1 else
  if Int.lt i1 Int.zero || Int.lt i2 Int.zero
  then sgn Pbot (Z.max (ssize i1) (ssize i2))
  else uns1 Pbot (Z.max (usize i1) (usize i2)).

Definition vlub (v w: aval) : aval :=
  match v, w with
  | Vbot, _ => w
  | _, Vbot => v
  | I i1, I i2 => vlub_int I i1 i2
  | I i1, IU i2 | IU i1, I i2 | IU i1, IU i2 => vlub_int IU i1 i2
  | (I i | IU i), Uns p n | Uns p n, (I i | IU i) =>
      if Int.lt i Int.zero
      then sgn p (Z.max (ssize i) (n + 1))
      else uns1 p (Z.max (usize i) n)
  | (I i | IU i), Sgn p n | Sgn p n, (I i | IU i) =>
      sgn p (Z.max (ssize i) n)
  | (I i | IU i), Num p | Num p, (I i | IU i) => Num p
  | (I i | IU i), (Ptr p | Ifptr p) | (Ptr p | Ifptr p), (I i | IU i) => Ifptr (plub p (int_provenance i))
  | (I _ | IU _), (L _ | F _ | FS _) | (L _ | F _ | FS _), (I _ | IU _) => ntop
  | Uns p1 n1, Uns p2 n2 => Uns (plub p1 p2) (Z.max n1 n2)
  | Uns p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (Z.max (n1 + 1) n2)
  | Sgn p1 n1, Uns p2 n2 => sgn (plub p1 p2) (Z.max n1 (n2 + 1))
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (Z.max n1 n2)
  | (Uns p1 _ | Sgn p1 _), Num p2 | Num p1, (Uns p2 _ | Sgn p2 _) => Num (plub p1 p2)
  | (Uns p1 _ | Sgn p1 _), (Ptr p2 | Ifptr p2) | (Ptr p1 | Ifptr p1), (Uns p2 _ | Sgn p2 _) => Ifptr (plub p1 p2)
  | (Uns p _ | Sgn p _), (L _ | F _ | FS _) | (L _ | F _ | FS _), (Uns p _ | Sgn p _) => Num p
  | L i1, L i2 => if Int64.eq i1 i2 then v else ntop
  | L i, Num p | Num p, L i => Num p
  | L i, (Ptr p | Ifptr p) | (Ptr p | Ifptr p), L i => Ifptr (plub p (long_provenance i))
  | L _, (F _ | FS _) | (F _ | FS _), L _ => ntop
  | F f1, F f2 => if Float.eq_dec f1 f2 then v else ntop
  | F _, Num p | Num p, F _ => Num p
  | F _, (Ptr p | Ifptr p) | (Ptr p | Ifptr p), F _ => Ifptr p
  | F _, FS _ | FS _, F _ => ntop
  | FS f1, FS f2 => if Float32.eq_dec f1 f2 then v else ntop
  | FS _, Num p | Num p, FS _ => Num p
  | FS _, (Ptr p | Ifptr p) | (Ptr p | Ifptr p), FS _ => Ifptr p
  | Num p1, Num p2 => Num (plub p1 p2)
  | Num p1, (Ptr p2 | Ifptr p2) | (Ifptr p1 | Ptr p1), Num p2 => Ifptr (plub p1 p2)
  | Ptr p1, Ptr p2 => Ptr(plub p1 p2)
  | Ptr p1, Ifptr p2 | Ifptr p1, Ptr p2 | Ifptr p1, Ifptr p2 => Ifptr(plub p1 p2)
  end.

Lemma vlub_comm:
  forall v w, vlub v w = vlub w v.
Proof.
  assert (INT: forall cstr i j, vlub_int cstr i j = vlub_int cstr j i).
  { intros. unfold vlub_int. rewrite Int.eq_sym, orb_comm.
    predSpec Int.eq Int.eq_spec j i. congruence.
    destruct orb; f_equal; apply Z.max_comm. }
  intros. unfold vlub; destruct v; destruct w; auto; f_equal; auto using Z.max_comm, plub_comm.
- rewrite Int64.eq_sym. predSpec Int64.eq Int64.eq_spec n0 n; congruence.
- rewrite dec_eq_sym. destruct (Float.eq_dec f0 f); congruence.
- rewrite dec_eq_sym. destruct (Float32.eq_dec f0 f); congruence.
Qed.

Lemma vge_uns_uns': forall p n, vge (uns1 p n) (Uns p n).
Proof.
  unfold uns1; intros. repeat (destruct zle); eauto with va.
Qed.

Lemma vge_uns_i': forall p n i, 0 <= n -> is_uns n i -> vge (uns1 p n) (I i).
Proof.
  intros. apply vge_trans with (Uns p n). apply vge_uns_uns'. auto with va.
Qed.

Lemma vge_uns_iu': forall p n i, 0 <= n -> is_uns n i -> vge (uns1 p n) (IU i).
Proof.
  intros. apply vge_trans with (Uns p n). apply vge_uns_uns'. auto with va.
Qed.

Lemma vge_sgn_sgn': forall p n, vge (sgn p n) (Sgn p n).
Proof.
  unfold sgn; intros. repeat (destruct zle); eauto with va.
Qed.

Lemma vge_sgn_i': forall p n i, 0 < n -> is_sgn n i -> vge (sgn p n) (I i).
Proof.
  intros. apply vge_trans with (Sgn p n). apply vge_sgn_sgn'. auto with va.
Qed.

Lemma vge_sgn_iu': forall p n i, 0 < n -> is_sgn n i -> vge (sgn p n) (IU i).
Proof.
  intros. apply vge_trans with (Sgn p n). apply vge_sgn_sgn'. auto with va.
Qed.

Hint Resolve vge_uns_uns' vge_uns_i' vge_uns_iu' vge_sgn_sgn' vge_sgn_i' vge_sgn_iu': va.

Lemma vge_lub_l:
  forall x y, vge (vlub x y) x.
Proof.
  assert (INT: forall i j, vge (vlub_int I i j) (I i)).
  { unfold vlub_int; intros. predSpec Int.eq Int.eq_spec i j. auto with va.
    destruct orb. eauto with va.
    apply vge_sgn_i'. generalize (ssize_pos i); lia. eauto with va.
    apply vge_uns_i'. generalize (usize_pos i); lia. eauto with va. }
  assert (INTU: forall i j, vge (vlub_int IU i j) (IU i)).
  { unfold vlub_int; intros. predSpec Int.eq Int.eq_spec i j. auto with va.
    destruct orb.
    apply vge_sgn_iu'. generalize (ssize_pos i); lia. eauto with va.
    apply vge_uns_iu'. generalize (usize_pos i); lia. eauto with va. }
  unfold vlub, ntop; destruct x, y; eauto using vge_trans, pge_lub_l with va.
- destruct (Int.lt n Int.zero).
  apply vge_sgn_i'. generalize (ssize_pos n); lia. eauto with va.
  apply vge_uns_i'. generalize (usize_pos n); lia. eauto with va.
- apply vge_sgn_i'. generalize (ssize_pos n); lia. eauto with va.
- destruct (Int.lt n Int.zero).
  apply vge_sgn_iu'. generalize (ssize_pos n); lia. eauto with va.
  apply vge_uns_iu'. generalize (usize_pos n); lia. eauto with va.
- apply vge_sgn_iu'. generalize (ssize_pos n); lia. eauto with va.
- destruct (Int.lt n0 Int.zero).
  eapply vge_trans. apply vge_sgn_sgn'.
  apply vge_trans with (Sgn p (n + 1)); eauto with va.
  eapply vge_trans. apply vge_uns_uns'. eauto with va.
- destruct (Int.lt n0 Int.zero).
  eapply vge_trans. apply vge_sgn_sgn'.
  apply vge_trans with (Sgn p (n + 1)); eauto with va.
  eapply vge_trans. apply vge_uns_uns'. eauto with va.
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
  | Ptr p | Ifptr p => p
  | Num p | Uns p _ | Sgn p _ => if va_strict tt then Pbot else p
  | I i => int_provenance i
  | L i => long_provenance i
  | _ => Pbot
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
  | Ptr q | Ifptr q | Num q | Uns q _ | Sgn q _ => pincl q p
  | _ => true
  end.

Lemma vpincl_ge:
  forall x p, vpincl x p = true -> vge (Ifptr p) x.
Proof.
  unfold vpincl; intros. destruct x; eauto using pincl_ge with va. 
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
  | I i, IU j => Int.eq_dec i j
  | IU i, IU j => Int.eq_dec i j
  | (I i | IU i), Uns p n => Int.eq_dec (Int.zero_ext n i) i && zle 0 n
  | (I i | IU i), Sgn p n => Int.eq_dec (Int.sign_ext n i) i && zlt 0 n
  | Uns p n, Uns q m => zle n m && pincl p q
  | Uns p n, Sgn q m => zlt n m && pincl p q
  | Sgn p n, Sgn q m => zle n m && pincl p q
  | L i, L j => Int64.eq_dec i j
  | F i, F j => Float.eq_dec i j
  | FS i, FS j => Float32.eq_dec i j
  | (I _ | IU _ | L _ | F _ | FS _), (Num _ | Ifptr _) => true
  | (Uns p _ | Sgn p _ | Num p), Num q => pincl p q
  | Ptr p, Ptr q => pincl p q
  | (Ptr p | Ifptr p | Num p | Uns p _ | Sgn p _), Ifptr q => pincl p q
  | _, _ => false
  end.

Lemma vincl_ge: forall v w, vincl v w = true -> vge w v.
Proof.
  unfold vincl; destruct v; destruct w;
  intros; try discriminate; try InvBooleans; try subst; eauto using pincl_ge with va.
- constructor; auto. rewrite is_uns_zero_ext; auto.
- constructor; auto. rewrite is_sgn_sign_ext; auto.
- constructor; auto. rewrite is_uns_zero_ext; auto.
- constructor; auto. rewrite is_sgn_sign_ext; auto.
Qed.

Lemma ge_vincl: forall v w, vge v w -> vincl w v = true.
Proof.
  induction 1; simpl; try (apply andb_true_intro; split); auto using ge_pincl, proj_sumbool_is_true.
  all: try (unfold proj_sumbool; rewrite zle_true by lia; auto).
  all: try (unfold proj_sumbool; rewrite zlt_true by lia; auto).
  1,2: apply is_uns_zero_ext in H0; rewrite H0; auto using proj_sumbool_is_true.
  1,2: apply is_sgn_sign_ext in H0; auto; rewrite H0; auto using proj_sumbool_is_true.
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
  match x with I n => I (sem n) | IU n => IU (sem n) | _ => ntop1 x end.

Lemma unop_int_sound:
  forall sem v x,
  vmatch v x ->
  vmatch (match v with Vint i => Vint(sem i) | _ => Vundef end) (unop_int sem x).
Proof.
  intros. unfold unop_int; inv H; auto with va.
Qed.

Definition binop_int (sem: int -> int -> int) (x y: aval) :=
  match x, y with
  | I n, I m => I (sem n m)
  | I n, IU m | IU n, I m | IU n, IU m => IU (sem n m)
  | _, _ => ntop2 x y end.

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
        | IU i => IU (Int.shl i amount)
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
- apply vmatch_uns'. red; intros. rewrite Int.bits_shl by lia.
  destruct (zlt m (Int.unsigned n)). auto. apply H1; extlia.
- apply vmatch_sgn'. red; intros. zify.
  rewrite ! Int.bits_shl by lia.
  rewrite ! zlt_false by lia.
  rewrite H1 by lia. symmetry. rewrite H1 by lia. auto.
- destruct v; constructor.
Qed.

Definition shru (v w: aval) :=
  match w with
  | I amount =>
      if Int.ltu amount Int.iwordsize then
        match v with
        | I i => I (Int.shru i amount)
        | IU i => IU (Int.shru i amount)
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
    rewrite Int.bits_shru by lia. apply zlt_false. lia.
  }
  inv H; auto with va.
- apply vmatch_uns'. red; intros. zify.
  rewrite Int.bits_shru by lia.
  destruct (zlt (m + Int.unsigned n) Int.zwordsize); auto.
  apply H1; lia.
- destruct v; constructor.
Qed.

Definition shr (v w: aval) :=
  match w with
  | I amount =>
      if Int.ltu amount Int.iwordsize then
        match v with
        | I i => I (Int.shr i amount)
        | IU i => IU (Int.shr i amount)
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
    rewrite ! Int.bits_shr by lia. f_equal.
    destruct (zlt (m + Int.unsigned n) Int.zwordsize);
    destruct (zlt (Int.zwordsize - 1 + Int.unsigned n) Int.zwordsize);
    lia.
  }
  assert (SGN: forall q i p, is_sgn p i -> 0 < p -> vmatch (Vint (Int.shr i n)) (sgn q (p - Int.unsigned n))).
  {
    intros. apply vmatch_sgn'. red; intros. zify.
    rewrite ! Int.bits_shr by lia.
    transitivity (Int.testbit i (Int.zwordsize - 1)).
    destruct (zlt (m + Int.unsigned n) Int.zwordsize).
    apply H0; lia.
    auto.
    symmetry.
    destruct (zlt (Int.zwordsize - 1 + Int.unsigned n) Int.zwordsize).
    apply H0; lia.
    auto.
  }
  inv H; eauto with va.
- destruct v; constructor.
Qed.

Definition and (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.and i1 i2)
  | I i1, IU i2 | IU i1, I i2 | IU i1, IU i2 => IU (Int.and i1 i2)
  | (I i | IU i), Uns p n | Uns p n, (I i | IU i) => uns p (Z.min n (usize i))
  | (I i | IU i), x | x, (I i | IU i) => uns (provenance x) (usize i)
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
  | I i1, IU i2 | IU i1, I i2 | IU i1, IU i2 => IU (Int.or i1 i2)
  | (I i | IU i), Uns p n | Uns p n, (I i | IU i) => uns p (Z.max n (usize i))
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
    rewrite H by extlia. rewrite H0 by extlia. auto.
  }
  assert (SGN: forall i j n m, is_sgn n i -> is_sgn m j -> is_sgn (Z.max n m) (Int.or i j)).
  {
    intros; red; intros. rewrite ! Int.bits_or by extlia.
    rewrite H by extlia. rewrite H0 by extlia. auto.
  }
  intros. unfold or, Val.or; inv H; eauto with va; inv H0; eauto with va.
Qed.

Definition xor (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.xor i1 i2)
  | I i1, IU i2 | IU i1, I i2 | IU i1, IU i2 => IU (Int.xor i1 i2)
  | (I i | IU i), Uns p n | Uns p n, (I i | IU i) => uns p (Z.max n (usize i))
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
    rewrite H by extlia. rewrite H0 by extlia. auto.
  }
  assert (SGN: forall i j n m, is_sgn n i -> is_sgn m j -> is_sgn (Z.max n m) (Int.xor i j)).
  {
    intros; red; intros. rewrite ! Int.bits_xor by extlia.
    rewrite H by extlia. rewrite H0 by extlia. auto.
  }
  intros. unfold xor, Val.xor; inv H; eauto with va; inv H0; eauto with va.
Qed.

Definition notint (v: aval) :=
  match v with
  | I i => I (Int.not i)
  | IU i => IU (Int.not i)
  | Uns p n => sgn p (n + 1)
  | Sgn p n => Sgn p n
  | _ => ntop1 v
  end.

Lemma notint_sound:
  forall v x, vmatch v x -> vmatch (Val.notint v) (notint x).
Proof.
  assert (SGN: forall n i, is_sgn n i -> is_sgn n (Int.not i)).
  {
    intros; red; intros. rewrite ! Int.bits_not by lia.
    f_equal. apply H; auto.
  }
  intros. unfold Val.notint, notint; inv H; eauto with va.
Qed.

Definition rol (x y: aval) :=
  match y, x with
  | I j, I i => I(Int.rol i j)
  | I j, IU i => IU(Int.rol i j)
  | I j, Uns p n => uns p (n + Int.unsigned j)
  | I j, Sgn p n => if zlt n Int.zwordsize then sgn p (n + Int.unsigned j) else ntop1 x
  | _, _ => ntop1 x
  end.

Lemma rol_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.rol v w) (rol x y).
Proof.
  intros.
  assert (DEFAULT: forall p, vmatch (Val.rol v w) (Num p)).
  {
    destruct v; destruct w; simpl; constructor.
  }
  unfold rol; destruct y; try apply DEFAULT; auto. inv H0. unfold Val.rol.
  inv H; auto with va.
- apply vmatch_uns. red; intros. rewrite Int.bits_rol by auto.
  generalize (Int.unsigned_range n); intros.
  rewrite Z.mod_small by lia.
  apply H1. lia. lia.
- destruct (zlt n0 Int.zwordsize); auto with va.
  apply vmatch_sgn. red; intros. rewrite ! Int.bits_rol by lia.
  generalize (Int.unsigned_range n); intros.
  rewrite ! Z.mod_small by lia.
  rewrite H1 by lia. symmetry. rewrite H1 by lia. auto.
- destruct (zlt n0 Int.zwordsize); auto with va.
Qed.

Definition ror (x y: aval) :=
  match y, x with
  | I j, I i => I(Int.ror i j)
  | I j, IU i => IU(Int.ror i j)
  | _, _ => ntop1 x
  end.

Lemma ror_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.ror v w) (ror x y).
Proof.
  intros.
  assert (DEFAULT: forall p, vmatch (Val.ror v w) (Num p)).
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

Definition neg (x: aval) :=
  match x with
  | I i => I (Int.neg i)
  | IU i => IU (Int.neg i)
  | Sgn p n => sgn p (n + 1)
  | _ => ntop1 x
  end.

Lemma neg_sound:
  forall v x, vmatch v x -> vmatch (Val.neg v) (neg x).
Proof.
  destruct 1; simpl; eauto with va.
  assert (A: Int.neg i = Int.repr (- Int.signed i)).
  { intros. apply Int.eqm_samerepr. apply eqmod_neg. apply Int.eqm_sym. apply Int.eqm_signed_unsigned. }
  rewrite A.
  exploit range_is_sgn; eauto. intros B.
  apply vmatch_sgn. apply is_sgn_range. lia.
  assert (two_p (n + 1 - 1) = two_p (n - 1) * 2).
  { replace (n + 1 - 1) with ((n - 1) + 1) by lia. apply two_p_is_exp; lia. }
  lia.
Qed.

Definition add (x y: aval) :=
  match x, y with
  | I i, I j => I (Int.add i j)
  | I i, IU j | IU i, I j | IU i, IU j => IU (Int.add i j)
  | (I i | IU i), Uns p n | Uns p n, (I i | IU i) => uns p (Z.max n (usize i) + 1)
  | (I i | IU i), Sgn p n | Sgn p n, (I i | IU i) => sgn p (Z.max n (ssize i) + 1)
  | Uns p1 n1, Uns p2 n2 => uns (plub p1 p2) (Z.max n1 n2 + 1)
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (Z.max n1 n2 + 1)
  | Uns p1 n1, Sgn p2 n2 | Sgn p2 n2, Uns p1 n1 => sgn (plub p1 p2) (Z.max (n1 + 1) n2 + 1)
  | Ptr p, (I i | IU i) | (I i | IU i), Ptr p => Ptr (if Archi.ptr64 then poffset p else padd p (Ptrofs.of_int i))
  | Ptr p, _   | _, Ptr p   => Ptr (poffset p)
  | Ifptr p, (I i | IU i) | (I i | IU i), Ifptr p => Ifptr (if Archi.ptr64 then poffset p else padd p (Ptrofs.of_int i))
  | Ifptr p, Ifptr q => Ifptr (plub (poffset p) (poffset q))
  | Ifptr p, _ | _, Ifptr p => Ifptr (poffset p)
  | _, _ => ntop2 x y
  end.

Lemma add_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.add v w) (add x y).
Proof.
  assert (UNS: forall n i m j,
               0 <= n -> 0 <= m -> is_uns n i -> is_uns m j ->
               is_uns (Z.max n m + 1) (Int.add i j)).
  { intros. apply range_is_uns in H1; auto. apply range_is_uns in H2; auto.
    apply is_uns_range. lia.
    assert (two_p n <= two_p (Z.max n m)) by (apply two_p_monotone; lia).
    assert (two_p m <= two_p (Z.max n m)) by (apply two_p_monotone; lia).
    assert (two_p (Z.max n m + 1) = two_p (Z.max n m) * 2) by (apply two_p_is_exp; lia).
    lia. }
  assert (SGN: forall n i m j,
               0 < n -> 0 < m -> is_sgn n i -> is_sgn m j ->
               is_sgn (Z.max n m + 1) (Int.add i j)).
  { intros. apply range_is_sgn in H1; auto. apply range_is_sgn in H2; auto.
    rewrite Int.add_signed. apply is_sgn_range. lia.
    set (p := Z.max n m - 1).
    assert (two_p (n-1) <= two_p p) by (apply two_p_monotone; lia).
    assert (two_p (m-1) <= two_p p) by (apply two_p_monotone; lia).
    assert (two_p (Z.max n m + 1 - 1) = two_p p * 2).
    { replace (Z.max n m + 1 - 1) with (p + 1) by lia. apply two_p_is_exp; lia. }
    lia. }
  assert (SGN2: forall n i m j,
               0 < n -> 0 < m -> is_sgn n i -> is_sgn m j ->
               is_sgn (Z.max n m + 1) (Int.add j i)).
  { intros. rewrite Z.max_comm; eauto. }
  intros. unfold Val.add, add. destruct Archi.ptr64.
- inv H; inv H0; eauto with va.
- inv H; inv H0; eauto with va; constructor;
  ((apply padd_sound; assumption) || (eapply poffset_sound; eassumption) || idtac).
  apply pmatch_lub_r. eapply poffset_sound; eauto.
  apply pmatch_lub_l. eapply poffset_sound; eauto.
Qed.

Definition sub (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.sub i1 i2)
  | I i1, IU i2 | IU i1, I i2 | IU i1, IU i2 => IU (Int.sub i1 i2)
  | (I i | IU i), Uns p n | Uns p n, (I i | IU i) => sgn p (Z.max (n + 1) (ssize i) + 1)
  | (I i | IU i), Sgn p n | Sgn p n, (I i | IU i) => sgn p (Z.max n (ssize i) + 1)
  | Uns p1 n1, Uns p2 n2 => sgn (plub p1 p2) (Z.max n1 n2 + 1)
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (Z.max n1 n2 + 1)
  | Uns p1 n1, Sgn p2 n2 | Sgn p2 n2, Uns p1 n1 => sgn (plub p1 p2) (Z.max (n1 + 1) n2 + 1)
  | Ptr p, (I i | IU i) => if Archi.ptr64 then Ifptr (poffset p) else Ptr (psub p (Ptrofs.of_int i))
  | Ptr p, _   => Ifptr (poffset p)
  | Ifptr p, (I i | IU i) => if Archi.ptr64 then Ifptr (plub (poffset p) (provenance w)) else Ifptr (psub p (Ptrofs.of_int i))
  | Ifptr p, _ => Ifptr (plub (poffset p) (provenance w))
  | _, _ => ntop2 v w
  end.

Lemma sub_sound:
  forall v w x y, vmatch v x -> vmatch w y -> vmatch (Val.sub v w) (sub x y).
Proof.
  assert (UNS: forall n i m j,
               0 <= n -> 0 <= m -> is_uns n i -> is_uns m j ->
               is_sgn (Z.max n m + 1) (Int.sub i j)).
  { intros. apply range_is_uns in H1; auto. apply range_is_uns in H2; auto.
    apply is_sgn_range. lia.
    assert (two_p n <= two_p (Z.max n m)) by (apply two_p_monotone; lia).
    assert (two_p m <= two_p (Z.max n m)) by (apply two_p_monotone; lia).
    replace (Z.max n m + 1 - 1) with (Z.max n m) by lia.
    lia. }
  assert (SGN: forall n i m j,
               0 < n -> 0 < m -> is_sgn n i -> is_sgn m j ->
               is_sgn (Z.max n m + 1) (Int.sub i j)).
  { intros. apply range_is_sgn in H1; auto. apply range_is_sgn in H2; auto.
    rewrite Int.sub_signed. apply is_sgn_range. lia.
    set (p := Z.max n m - 1).
    assert (two_p (n-1) <= two_p p) by (apply two_p_monotone; lia).
    assert (two_p (m-1) <= two_p p) by (apply two_p_monotone; lia).
    assert (two_p (Z.max n m + 1 - 1) = two_p p * 2).
    { replace (Z.max n m + 1 - 1) with (p + 1) by lia. apply two_p_is_exp; lia. }
    lia. }
  assert (SGN2: forall n i m j,
               0 < n -> 0 < m -> is_sgn n i -> is_sgn m j ->
               is_sgn (Z.max n m + 1) (Int.sub j i)).
  { intros. rewrite Z.max_comm. eauto. }
  intros. unfold Val.sub, sub. destruct Archi.ptr64.
- inv H; inv H0; eauto with va.
- inv H; inv H0; try (destruct (eq_block b b0)); eauto using psub_sound, poffset_sound, pmatch_lub_l with va.
Qed.

Definition mul_base (v w: aval) :=
  match v, w with
  | Uns p n1, (I n2 | IU n2) | (I n2 | IU n2), Uns p n1 => uns p (n1 + usize n2)
  | Uns p1 n1, Uns p2 n2 => uns (plub p1 p2) (n1 + n2)
  | Sgn p n1, (I n2 | IU n2) | (I n2 | IU n2), Sgn p n1 => sgn p (n1 + ssize n2)
  | Sgn p1 n1, Sgn p2 n2 => sgn (plub p1 p2) (n1 + n2)
  | Uns p1 n1, Sgn p2 n2 => sgn (plub p1 p2) ((n1 + 1) + n2)
  | Sgn p1 n1, Uns p2 n2 => sgn (plub p1 p2) (n1 + (n2 + 1))
  | _, _ => ntop2 v w
  end.

Lemma mul_base_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mul v w) (mul_base x y).
Proof.
  intros.
  assert (UNS: forall i1 i2 n1 n2 p,
             0 <= n1 -> is_uns n1 i1 ->
             0 <= n2 -> is_uns n2 i2 ->
             vmatch (Val.mul (Vint i1) (Vint i2)) (uns p (n1 + n2))).
  { intros. apply vmatch_uns. apply is_uns_range. lia.
    apply Zmult_unsigned_range; auto using range_is_uns. }
  assert (SGN: forall i1 i2 n1 n2 p,
             0 < n1 -> is_sgn n1 i1 ->
             0 < n2 -> is_sgn n2 i2 ->
             vmatch (Val.mul (Vint i1) (Vint i2)) (sgn p (n1 + n2))).
  { intros. apply vmatch_sgn. rewrite Int.mul_signed. apply is_sgn_range. lia.
    replace (n1 + n2 - 1) with ((n1 - 1) + (n2 - 1) + 1) by lia.
    apply Zmult_signed_range; auto using range_is_sgn; lia. }
  unfold mul_base.
  inv H; inv H0; eauto with va; rewrite Z.add_comm; eauto with va.
Qed.

Definition mul (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.mul i1 i2)
  | IU i1, I i2 | I i1, IU i2 | IU i1, IU i2 => IU (Int.mul i1 i2)
  | _, _ =>
      if vincl v (Uns Ptop 0) || vincl w (Uns Ptop 0)
      then IU Int.zero
      else mul_base v w
  end.

Lemma mul_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mul v w) (mul x y).
Proof.
  intros.
  assert (vmatch (Val.mul v w)
            (if vincl x (Uns Ptop 0) || vincl y (Uns Ptop 0)
             then IU Int.zero
             else mul_base x y)).
  { destruct orb eqn:INCL; auto using mul_base_sound.
    rewrite orb_true_iff in INCL; destruct INCL;
    exploit vmatch_Uns_0; eauto using vmatch_ge, vincl_ge;
    intros [E|E]; subst; simpl.
    - auto with va.
    - destruct w; auto with va.
    - destruct v; auto with va.
    - destruct v; simpl; rewrite ? Int.mul_zero; auto with va.
  }
  inv H; inv H0; auto with va.
Qed.

Definition mulhs_base (v w: aval) :=
  sgn (plub (provenance v) (provenance w)) (srange v + srange w - Int.zwordsize).

Lemma mulhs_base_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mulhs v w) (mulhs_base x y).
Proof.
  intros. unfold Val.mulhs, mulhs_base; destruct v, w; auto with va.
  rename i0 into j.
  apply srange_sound in H. destruct H as [A1 B1]. apply range_is_sgn in B1; auto.
  apply srange_sound in H0. destruct H0 as [A2 B2]. apply range_is_sgn in B2; auto.
  set (n := srange x) in *. set (m := srange y) in *.
  unfold Int.mulhs. set (a := Int.signed i) in *. set (b := Int.signed j) in *.
  exploit (Zmult_signed_range (n-1) a (m-1) b); auto with va.
  replace (n - 1 + (m - 1) + 1) with (n + m - 1) by lia.
  intros P.
  rewrite Int.modulus_power. change Int.zwordsize with 32. rewrite <- Zshiftr_div_two_p by lia.
  apply vmatch_sgn. red; intros. rewrite ! Int.testbit_repr by lia. rewrite ! Z.shiftr_spec by lia.
  apply (Zbits_signed_range (n + m - 1)); lia.
Qed.

Definition mulhs (v w: aval) :=
  match v, w with
  | I i1, I i2 => I (Int.mulhs i1 i2)
  | IU i1, I i2 | I i1, IU i2 | IU i1, IU i2 => IU (Int.mulhs i1 i2)
  | _, _ =>
      if vincl v (Uns Ptop 0) || vincl w (Uns Ptop 0) then
        IU Int.zero
      else
        mulhs_base v w
  end.

Lemma mulhs_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mulhs v w) (mulhs x y).
Proof.
  intros. unfold mulhs.
  destruct (vincl x (Uns Ptop 0) || vincl y (Uns Ptop 0)) eqn:?; auto with va.
  - rewrite orb_true_iff in Heqb;  destruct Heqb.
    exploit vmatch_Uns_0. eapply vmatch_ge. eapply vincl_ge; eauto. eexact H.
    intros. destruct H2; inv H2; inv H; inv H0; auto with va.
    exploit vmatch_Uns_0. eapply vmatch_ge. eapply vincl_ge; eauto. eexact H0.
    intros. destruct H2; inv H2; inv H; inv H0; simpl; try rewrite Int.mulhs_zero; auto with va.
  - inversion H; inversion H0; subst; eauto using mulhs_base_sound with va.
Qed.

Definition mulhu_base (v w: aval) :=
  uns (plub (provenance v) (provenance w)) (urange v + urange w - Int.zwordsize).

Lemma mulhu_base_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mulhu v w) (mulhu_base x y).
Proof.
  intros. unfold Val.mulhu, mulhu_base; destruct v, w; auto with va.
  apply urange_sound in H. destruct H as [A1 B1]. apply range_is_uns in B1; auto.
  apply urange_sound in H0. destruct H0 as [A2 B2]. apply range_is_uns in B2; auto.
  set (n1 := urange x) in *. set (n2 := urange y) in *.
  unfold Int.mulhu. set (x1 := Int.unsigned i) in *. set (x2 := Int.unsigned i0) in *.
  exploit (Zmult_unsigned_range n1 x1 n2 x2); auto. intros P.
  rewrite Int.modulus_power. change Int.zwordsize with 32. rewrite <- Zshiftr_div_two_p by lia.
  apply vmatch_uns. red; intros. rewrite Int.testbit_repr by auto. rewrite Z.shiftr_spec by lia.
  apply (Zbits_unsigned_range (n1 + n2)); lia.
Qed.

Definition mulhu (v w: aval):=
  match v, w with
  | I i1, I i2 => I (Int.mulhu i1 i2)
  | I i1, IU i2 | IU i1, I i2 | IU i1, IU i2  => IU (Int.mulhu i1 i2)
  | _, _ =>
      if vincl v (Uns Ptop 1) || vincl w (Uns Ptop 1)
      then IU Int.zero
      else mulhu_base v w
  end.

Lemma mulhu_sound:
  forall v x w y, vmatch v x -> vmatch w y -> vmatch (Val.mulhu v w) (mulhu x y).
Proof.
  intros. destruct (vincl x (Uns Ptop 1) || vincl y (Uns Ptop 1)) eqn:?; try eapply mulhu_base_sound; eauto; unfold mulhu; rewrite Heqb.
  - rewrite orb_true_iff in Heqb. destruct Heqb.
    exploit (vmatch_Uns_1 Ptop v). eapply vmatch_ge; eauto. eapply vincl_ge; eauto.
    intros. destruct H2; inv H2. simpl. inv H; destruct y; auto with va.
    simpl. inv H; destruct y; inv H0; auto with va. simpl.
    inv H; destruct y; inv H0; try rewrite Int.mulhu_commut; try rewrite Int.mulhu_one; auto with va.
    exploit (vmatch_Uns_1 Ptop w). eapply vmatch_ge; eauto. eapply vincl_ge; eauto.
    intros. destruct H2; inv H2. inv H; inv H0; simpl; auto with va.
    inv H0; inv H; simpl; auto with va; rewrite Int.mulhu_zero; auto with va.
    inv H0; inv H; simpl; auto with va; rewrite Int.mulhu_one; auto with va.
  - inversion H; inversion H0; subst; eauto using mulhu_base_sound with va.
Qed.

Definition divs (v w: aval) :=
  match w, v with
  | (I i2 | IU i2), (I i1 | IU i1) =>
      if Int.eq i2 Int.zero
      || Int.eq i1 (Int.repr Int.min_signed) && Int.eq i2 Int.mone
      then if va_strict tt then Vbot else ntop
      else I (Int.divs i1 i2)
  | (I i2 | IU i2), _ =>
      if Int.eq i2 Int.zero
      then if va_strict tt then Vbot else ntop
      else sgn (provenance v) (srange v + 1 - Z.log2 (Z.abs (Int.signed i2)))
  | _, _ => ntop2 v w
  end.

Lemma divs_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.divs v w = Some u -> vmatch u (divs x y).
Proof.
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct orb eqn:E; inv H1.
  rename i0 into j.
  assert (E': Int.eq j Int.zero = false). { apply orb_false_elim in E. tauto. }
  assert (Int.signed j <> 0).
  { red; intros. rewrite <- (Int.repr_signed j) in E. rewrite H1 in E. discriminate. }
  set (q := srange x + 1 - Z.log2 (Z.abs (Int.signed j))).
  set (q1 := Z.max 0 ((srange x - 1) + 1 - Z.log2 (Z.abs (Int.signed j)))).
  assert (Z.max 1 q - 1 = q1) by lia.
  assert (vmatch (Vint (Int.divs i j)) (sgn (provenance x) q)).
  { apply srange_sound in H. destruct H as [A B]. apply range_is_sgn in B; auto.
    apply vmatch_sgn'. apply is_sgn_range. lia.
    rewrite ! H2. apply Zdiv_signed_range; auto. lia. }
  unfold divs; inv H; inv H0; auto with va; rewrite ? E, ? E'; auto with va.
Qed.

Definition divu (v w: aval) :=
  match w with
  | I i2 | IU i2 =>
      if Int.eq i2 Int.zero then
        if va_strict tt then Vbot else ntop
      else
        match v with
        | I i1 | IU i1 => I (Int.divu i1 i2)
        | _ => uns (provenance v) (urange v - Z.log2 (Int.unsigned i2))
        end
  | _ => ntop2 v w
  end.

Lemma divu_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.divu v w = Some u -> vmatch u (divu x y).
Proof.
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  rename i0 into j. destruct (Int.eq j Int.zero) eqn:E; inv H1.
  assert (Int.unsigned j <> 0).
  { red; intros. rewrite <- (Int.repr_unsigned j) in E. rewrite H1 in E. discriminate. }
  assert (0 < Int.unsigned j).
  { pose proof (Int.unsigned_range j). lia. } 
  assert (vmatch (Vint (Int.divu i j)) (uns (provenance x) (urange x - Z.log2 (Int.unsigned j)))).
  { apply urange_sound in H. destruct H as [A B]. apply range_is_uns in B; auto.
    apply vmatch_uns'. apply is_uns_range. lia.
    apply Zdiv_unsigned_range; auto. }
  unfold divu; inv H; inv H0; auto with va; rewrite E; auto with va.
Qed.

Definition mods (v w: aval) :=
  match w, v with
  | (I i2 | IU i2), (I i1 | IU i1) =>
      if Int.eq i2 Int.zero
      || Int.eq i1 (Int.repr Int.min_signed) && Int.eq i2 Int.mone
      then if va_strict tt then Vbot else ntop
      else I (Int.mods i1 i2)
  | (I i2 | IU i2), _ => sgn (provenance v) (ssize i2)
  | _, _ => ntop2 v w
  end.

Lemma mods_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.mods v w = Some u -> vmatch u (mods x y).
Proof.
  assert (SGN: forall i j, Int.eq j Int.zero = false -> is_sgn (ssize j) (Int.mods i j)).
  {
    intros. unfold Int.mods.
    pose proof (is_sgn_ssize j). apply range_is_sgn in H0; auto with va.
    set (x := Int.signed i) in *. set (y := Int.signed j) in *.
    assert (y <> 0).
    { unfold y; red; intros. rewrite <- (Int.repr_signed j), H1 in H. discriminate. }
    assert (Z.abs (Z.rem x y) < Z.abs y) by (apply Z.rem_bound_abs; auto).
    apply is_sgn_range. auto with va. lia.
  }
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct orb eqn:E; inv H1.
  assert (E': Int.eq i0 Int.zero = false).  { apply orb_false_elim in E. tauto. }
  unfold mods; inv H; inv H0; auto with va; rewrite ? E; auto with va.
Qed.

Definition modu (v w: aval) :=
  match w, v with
  | (I i2 | IU i2), (I i1| IU i1) =>
      if Int.eq i2 Int.zero
      then if va_strict tt then Vbot else ntop
      else I (Int.modu i1 i2)
  | (I i2 | IU i2), _ => uns (provenance v) (usize i2)
  | _, _ => ntop2 v w
  end.

Lemma modu_sound:
  forall v w u x y, vmatch v x -> vmatch w y -> Val.modu v w = Some u -> vmatch u (modu x y).
Proof.
  assert (UNS: forall i j, j <> Int.zero -> is_uns (usize j) (Int.modu i j)).
  {
    intros. apply is_uns_mon with (usize (Int.modu i j)); auto with va.
    unfold usize, Int.size. apply Zsize_monotone.
    generalize (Int.unsigned_range_2 j); intros RANGE.
    assert (Int.unsigned j <> 0).
    { red; intros; elim H. rewrite <- (Int.repr_unsigned j). rewrite H0. auto. }
    exploit (Z_mod_lt (Int.unsigned i) (Int.unsigned j)). lia. intros MOD.
    unfold Int.modu. rewrite Int.unsigned_repr. lia. lia.
  }
  intros. destruct v; destruct w; try discriminate; simpl in H1.
  destruct (Int.eq i0 Int.zero) eqn:Z; inv H1.
  assert (i0 <> Int.zero) by (generalize (Int.eq_spec i0 Int.zero); rewrite Z; auto).
  unfold modu. inv H; inv H0; auto with va; rewrite Z; constructor.
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
  | IU i => IU (Int.zero_ext nbits i)
  | Uns p n => uns p (Z.min n nbits)
  | _ => uns (provenance v) nbits
  end.

Lemma zero_ext_sound:
  forall nbits v x, vmatch v x -> vmatch (Val.zero_ext nbits v) (zero_ext nbits x).
Proof.
  assert (DFL: forall nbits i, is_uns nbits (Int.zero_ext nbits i)).
  {
    intros; red; intros. rewrite Int.bits_zero_ext by lia. apply zlt_false; auto.
  }
  intros. inv H; simpl; auto with va. apply vmatch_uns.
  red; intros. zify.
  rewrite Int.bits_zero_ext by lia.
  destruct (zlt m nbits); auto. apply H1; lia.
Qed.

Definition sign_ext (nbits: Z) (v: aval) :=
  if zle nbits 0 then Uns (provenance v) 0 else
  match v with
  | I i => I (Int.sign_ext nbits i)
  | IU i => IU (Int.sign_ext nbits i)
  | Uns p n => if zlt n nbits then Uns p n else sgn p nbits
  | Sgn p n => sgn p (Z.min n nbits)
  | _ => sgn (provenance v) nbits
  end.

Lemma sign_ext_sound:
  forall nbits v x, vmatch v x -> vmatch (Val.sign_ext nbits v) (sign_ext nbits x).
Proof.
  assert (DFL: forall p nbits i, 0 < nbits -> vmatch (Vint (Int.sign_ext nbits i)) (sgn p nbits)).
  {
    intros. apply vmatch_sgn. apply is_sign_ext_sgn; auto with va.
  }
  intros. unfold sign_ext. destruct (zle nbits 0).
- destruct v; simpl; auto with va. constructor. lia. 
  rewrite Int.sign_ext_below by auto. red; intros; apply Int.bits_zero.
- inv H; simpl; auto with va.
+ destruct (zlt n nbits); eauto with va.
  constructor; auto. eapply is_sign_ext_uns; eauto with va.
+ destruct (zlt n nbits); auto with va.
+ apply vmatch_sgn. apply is_sign_ext_sgn; auto with va.
  apply Z.min_case; auto with va.
Qed.

Definition zero_ext_l (s: Z) := unop_long (Int64.zero_ext s).

Lemma zero_ext_l_sound:
  forall s v x, vmatch v x -> vmatch (Val.zero_ext_l s v) (zero_ext_l s x).
Proof.
  intros s. exact (unop_long_sound (Int64.zero_ext s)).
Qed.

Definition sign_ext_l (s: Z) := unop_long (Int64.sign_ext s).

Lemma sign_ext_l_sound:
  forall s v x, vmatch v x -> vmatch (Val.sign_ext_l s v) (sign_ext_l s x).
Proof.
  intros s. exact (unop_long_sound (Int64.sign_ext s)).
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
  destruct (zlt n lo). rewrite zeq_false by lia. constructor.
  destruct (zlt hi n). rewrite zeq_false by lia. constructor.
  constructor.
- (* ne *)
  constructor.
- (* lt *)
  destruct (zlt hi n). rewrite zlt_true by lia. constructor.
  destruct (zle n lo). rewrite zlt_false by lia. constructor.
  constructor.
- (* le *)
  destruct (zle hi n). rewrite zle_true by lia. constructor.
  destruct (zlt n lo). rewrite zle_false by lia. constructor.
  constructor.
- (* gt *)
  destruct (zlt n lo). rewrite zlt_true by lia. constructor.
  destruct (zle hi n). rewrite zlt_false by lia. constructor.
  constructor.
- (* ge *)
  destruct (zle n lo). rewrite zle_true by lia. constructor.
  destruct (zlt hi n). rewrite zle_false by lia. constructor.
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

Lemma cmp_intv_different_blocks:
  forall c i n, cmatch (Val.cmp_different_blocks c) (cmp_intv c i n).
Proof.
  intros c [lo hi] n; unfold Val.cmp_different_blocks.
  destruct c; auto using cmp_intv_None; simpl.
- destruct orb; constructor.
- constructor.
Qed.

Lemma cmp_intv_different_blocks_2:
  forall c i n, cmatch (Val.cmp_different_blocks c) (cmp_intv (swap_comparison c) i n).
Proof.
  intros c [lo hi] n; unfold Val.cmp_different_blocks.
  destruct c; auto using cmp_intv_None; simpl.
- destruct orb; constructor.
- constructor.
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
- lia.
- destruct (zlt n0 Int.zwordsize); simpl.
+ rewrite is_uns_zero_ext in H2. rewrite <- H2. rewrite Int.zero_ext_mod by lia.
  exploit (Z_mod_lt (Int.unsigned n) (two_p n0)). apply two_p_gt_ZERO; auto. lia.
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
  unfold Int.ltu. destruct (zle (Int.unsigned n1) (Int.unsigned n2)); [rewrite zlt_false|rewrite zlt_true]; auto; lia.
  unfold Int.ltu. destruct (zle (Int.unsigned n2) (Int.unsigned n1)); [rewrite zlt_false|rewrite zlt_true]; auto; lia.
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
- lia.
- destruct (zlt n0 Int.zwordsize); simpl.
+ rewrite is_uns_zero_ext in H2. rewrite <- H2.
  assert (Int.unsigned (Int.zero_ext n0 n) = Int.unsigned n mod two_p n0) by (apply Int.zero_ext_mod; lia).
  exploit (Z_mod_lt (Int.unsigned n) (two_p n0)). apply two_p_gt_ZERO; auto. intros.
  replace (Int.signed (Int.zero_ext n0 n)) with (Int.unsigned (Int.zero_ext n0 n)).
  rewrite H. lia.
  unfold Int.signed. rewrite zlt_true. auto.
  assert (two_p n0 <= Int.half_modulus).
  { change Int.half_modulus with (two_p (Int.zwordsize - 1)).
    apply two_p_monotone. lia. }
  lia.
+ apply Int.signed_range.
- destruct (zlt n0 (Int.zwordsize)); simpl.
+ rewrite is_sgn_sign_ext in H2 by auto. rewrite <- H2.
  exploit (Int.sign_ext_range n0 n). lia. lia.
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
  unfold Int.lt. destruct (zle (Int.signed n1) (Int.signed n2)); [rewrite zlt_false|rewrite zlt_true]; auto; lia.
  unfold Int.lt. destruct (zle (Int.signed n2) (Int.signed n1)); [rewrite zlt_false|rewrite zlt_true]; auto; lia.
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
  | I i1, IU i2 | IU i1, I i2 | IU i1, IU i2 => Maybe (Int.cmpu c i1 i2)
  | Ptr _, I i => if Int.eq i Int.zero then cmp_different_blocks c else Btop
  | I i, Ptr _ => if Int.eq i Int.zero then cmp_different_blocks c else Btop
  | Ptr p1, Ptr p2 => pcmp c p1 p2
  | _, (I i | IU i) => cmp_intv c (uintv v) (Int.unsigned i)
  | (I i | IU i), _ => cmp_intv (swap_comparison c) (uintv w) (Int.unsigned i)
  | _, _ => Btop
  end.

Lemma cmpu_bool_sound:
  forall valid c v w x y, vmatch v x -> vmatch w y -> cmatch (Val.cmpu_bool valid c v w) (cmpu_bool c x y).
Proof.
  intros.
  assert (IP: forall i b ofs,
    cmatch (Val.cmpu_bool valid c (Vint i) (Vptr b ofs)) (cmp_different_blocks c)).
  {
    intros. simpl. destruct Archi.ptr64; auto using cmp_different_blocks_none.
    destruct andb; auto using cmp_different_blocks_sound, cmp_different_blocks_none.
  }
  assert (PI: forall i b ofs,
    cmatch (Val.cmpu_bool valid c (Vptr b ofs) (Vint i)) (cmp_different_blocks c)).
  {
    intros. simpl. destruct Archi.ptr64; auto using cmp_different_blocks_none.
    destruct andb; auto using cmp_different_blocks_sound, cmp_different_blocks_none.
  }
  assert (IP2: forall i b ofs itv,
    cmatch (Val.cmpu_bool valid c (Vint i) (Vptr b ofs)) (cmp_intv (swap_comparison c) itv (Int.unsigned i))).
  {
    intros. simpl. destruct Archi.ptr64; auto using cmp_intv_None.
    destruct andb; auto using cmp_intv_different_blocks_2, cmp_intv_None.
  }
  assert (PI2: forall i b ofs itv,
    cmatch (Val.cmpu_bool valid c (Vptr b ofs) (Vint i)) (cmp_intv c itv (Int.unsigned i))).
  {
    intros. simpl. destruct Archi.ptr64; auto using cmp_intv_None.
    destruct andb; auto using cmp_intv_different_blocks, cmp_intv_None.
  }
  unfold cmpu_bool; inversion H; subst; inversion H0; subst;
  auto using cmatch_top, cmp_different_blocks_none, pcmp_none, pcmp_sound,
             cmpu_intv_sound, cmpu_intv_sound_2, cmp_intv_None.
- constructor.
- constructor.
- constructor.
- destruct (Int.eq i Int.zero); auto using cmatch_top.
- simpl; destruct (Int.eq i Int.zero); auto using cmatch_top, cmp_different_blocks_none.
- constructor.
- constructor.
- constructor.
- constructor.
- constructor.
- constructor.
- destruct (Int.eq i Int.zero); auto using cmatch_top.
- simpl; destruct (Int.eq i Int.zero); auto using cmatch_top, cmp_different_blocks_none.
Qed.

Definition cmp_bool (c: comparison) (v w: aval) : abool :=
  match v, w with
  | I i1, I i2 => Just (Int.cmp c i1 i2)
  | I i1, IU i2 | IU i1, I i2 | IU i1, IU i2 => Maybe (Int.cmp c i1 i2)
  | _, (I i | IU i) => cmp_intv c (sintv v) (Int.signed i)
  | (I i | IU i), _ => cmp_intv (swap_comparison c) (sintv w) (Int.signed i)
  | _, _ => Btop
  end.

Lemma cmp_bool_sound:
  forall c v w x y, vmatch v x -> vmatch w y -> cmatch (Val.cmp_bool c v w) (cmp_bool c x y).
Proof.
  intros.
  unfold cmp_bool; inversion H; subst; inversion H0; subst;
  auto using cmatch_top, cmp_intv_sound, cmp_intv_sound_2, cmp_intv_None;
  constructor.
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
  | IU i => Maybe (Int.eq (Int.and i mask) Int.zero)
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
  | Maybe b => IU (if b then Int.one else Int.zero)
  | _ => Uns Pbot 1
  end.

Lemma of_optbool_sound:
  forall ob ab, cmatch ob ab -> vmatch (Val.of_optbool ob) (of_optbool ab).
Proof.
  intros. inv H; simpl; auto with va.
- destruct b; constructor.
- destruct b; constructor.
- destruct ob; simpl; auto with va.
  destruct b; constructor; try lia.
  change 1 with (usize Int.one). apply is_uns_usize.
  red; intros. apply Int.bits_zero.
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

(** Add the possibility that the result may be [Vundef].
    Used for the [select] operation when the condition may be undefined. *)

Definition add_undef (x: aval) :=
  match x with
  | Vbot => ntop
  | I i => IU i
  | L _ | F _ | FS _ => ntop
  | _ => x
  end.

Lemma add_undef_sound:
  forall v x, vmatch v x -> vmatch v (add_undef x).
Proof.
  destruct 1; simpl; auto with va.
Qed.

Lemma add_undef_undef:
  forall x, vmatch Vundef (add_undef x).
Proof.
  destruct x; simpl; auto with va.
Qed.

(** Normalization by the select operation. *)

Definition vnormalize_type (ty: typ) (x: aval) : aval :=
  match x, ty with
  | Vbot, _ => Vbot
  | I _, Tint => x
  | L _, Tlong => x
  | F _, Tfloat => x
  | FS _, Tsingle => x
  | (I _ | FS _), Tany32 => x
  | (I _ | L _ | F _ | FS _), Tany64 => x
  | _, _ => add_undef x
  end.

Lemma vnormalize_type_sound: forall v x ty,
  vmatch v x -> vmatch (Val.normalize v ty) (vnormalize_type ty x).
Proof.
  intros.
  assert (A: Val.has_type v ty /\ vnormalize_type ty x = x
          \/ vnormalize_type ty x = add_undef x).
  { unfold vnormalize_type, Val.has_type; inv H; destruct ty; auto. }
  destruct A as [[A B] | A].
- rewrite B, Val.normalize_idem by auto. auto.
- rewrite A. destruct (Val.lessdef_normalize v ty);
  auto using add_undef_sound, add_undef_undef. 
Qed.

(** Select either returns one of its arguments, or Vundef. *)

Definition select (ab: abool) (x y: aval) (ty: typ) :=
  match ab with
  | Bnone => ntop
  | Just b => vnormalize_type ty (if b then x else y)
  | Maybe b => add_undef (vnormalize_type ty (if b then x else y))
  | Btop => add_undef (vnormalize_type ty (vlub x y))
  end.

Lemma select_sound:
  forall ob v w ab x y ty,
  cmatch ob ab -> vmatch v x -> vmatch w y ->
  vmatch (Val.select ob v w ty) (select ab x y ty).
Proof.
  unfold Val.select, select; intros. inv H.
- auto with va.
- apply vnormalize_type_sound; destruct b; auto.
- apply add_undef_undef.
- apply add_undef_sound; apply vnormalize_type_sound; destruct b; auto.
- destruct ob as [b|]. 
+ apply add_undef_sound; apply vnormalize_type_sound.
  destruct b; [apply vmatch_lub_l|apply vmatch_lub_r]; auto.
+ apply add_undef_undef.
Qed.

(** Normalization at load time *)

Definition vnormalize (chunk: memory_chunk) (v: aval) :=
  match chunk, v with
  | _, Vbot => Vbot
  | Mbool, I i =>
      let j := Int.zero_ext 8 i in
      if Int.eq j Int.zero || Int.eq j Int.one then I j else Uns Pbot 1
  | Mbool, IU i =>
      let j := Int.zero_ext 8 i in
      if Int.eq j Int.zero || Int.eq j Int.one then IU j else Uns Pbot 1
  | Mbool, _ => Uns (provenance v) 1
  | Mint8signed, I i => I (Int.sign_ext 8 i)
  | Mint8signed, IU i => IU (Int.sign_ext 8 i)
  | Mint8signed, Uns p n => if zlt n 8 then Uns (provenance v) n else Sgn (provenance v) 8
  | Mint8signed, Sgn p n => Sgn (provenance v) (Z.min n 8)
  | Mint8signed, _ => Sgn (provenance v) 8
  | Mint8unsigned, I i => I (Int.zero_ext 8 i)
  | Mint8unsigned, IU i => IU (Int.zero_ext 8 i)
  | Mint8unsigned, Uns p n => Uns (provenance v) (Z.min n 8)
  | Mint8unsigned, _ => Uns (provenance v) 8
  | Mint16signed, I i => I (Int.sign_ext 16 i)
  | Mint16signed, IU i => IU (Int.sign_ext 16 i)
  | Mint16signed, Uns p n => if zlt n 16 then Uns (provenance v) n else Sgn (provenance v) 16
  | Mint16signed, Sgn p n => Sgn (provenance v) (Z.min n 16)
  | Mint16signed, _ => Sgn (provenance v) 16
  | Mint16unsigned, I i => I (Int.zero_ext 16 i)
  | Mint16unsigned, IU i => IU (Int.zero_ext 16 i)
  | Mint16unsigned, Uns p n => Uns (provenance v) (Z.min n 16)
  | Mint16unsigned, _ => Uns (provenance v) 16
  | Mint32, (I _ | IU _ | Uns _ _ | Sgn _ _ | Num _) => v
  | Mint32, (Ptr p | Ifptr p) => if Archi.ptr64 then Num (provenance v) else v
  | Mint32, _ => Num (provenance v)
  | Mint64, L _ => v
  | Mint64, (Ptr p | Ifptr p) => if Archi.ptr64 then v else Num (provenance v)
  | Mint64, _ => Num (provenance v)
  | Mfloat32, FS f => v
  | Mfloat32, _ => Num (provenance v)
  | Mfloat64, F f => v
  | Mfloat64, _ => Num (provenance v)
  | Many32, (I _ | IU _ | Uns _ _ | Sgn _ _ | FS _) => v
  | Many32, (Ptr p | Ifptr p) => if Archi.ptr64 then Num (provenance v) else v
  | Many32, _ => Num (provenance v)
  | Many64, _ => v
  end.

Lemma vnormalize_sound:
  forall chunk v x, vmatch v x -> vmatch (Val.load_result chunk v) (vnormalize chunk x).
Proof.
  unfold Val.load_result, vnormalize; generalize Archi.ptr64; intros ptr64;
  induction 1; destruct chunk; eauto using is_zero_ext_uns, is_sign_ext_sgn with va;
  try (destruct ptr64; auto with va; fail).
- set (j := Int.zero_ext 8 i). unfold Val.norm_bool, Val.is_bool.
  predSpec Int.eq Int.eq_spec j Int.zero. rewrite H. apply vmatch_i.
  predSpec Int.eq Int.eq_spec j Int.one. rewrite H0. apply vmatch_i.
  simpl. unfold proj_sumbool, Vtrue, Vfalse. rewrite ! dec_eq_false by congruence. apply vmatch_Uns_undef.
- set (j := Int.zero_ext 8 i). unfold Val.norm_bool, Val.is_bool.
  predSpec Int.eq Int.eq_spec j Int.zero. rewrite H. apply vmatch_iu.
  predSpec Int.eq Int.eq_spec j Int.one. rewrite H0. apply vmatch_iu.
  simpl. unfold proj_sumbool, Vtrue, Vfalse. rewrite ! dec_eq_false by congruence. apply vmatch_Uns_undef.
- destruct orb; auto with va.
- destruct (zlt n 8); constructor; auto with va.
  apply is_sign_ext_uns; auto.
  apply is_sign_ext_sgn; auto with va.
- constructor. lia. apply is_zero_ext_uns. apply Z.min_case; auto with va.
- destruct (zlt n 16); constructor; auto with va.
  apply is_sign_ext_uns; auto.
  apply is_sign_ext_sgn; auto with va.
- constructor. extlia. apply is_zero_ext_uns. apply Z.min_case; auto with va.
- destruct (zlt n 8); auto with va.
- destruct (zlt n 16); auto with va.
- constructor. lia. apply is_sign_ext_sgn; auto with va. apply Z.min_case; auto with va.
- constructor. lia. apply is_sign_ext_sgn; auto with va. apply Z.min_case; auto with va.
Qed.

Lemma vnormalize_cast:
  forall chunk m b ofs v p,
  Mem.load chunk m b ofs = Some v ->
  vmatch v (Ifptr p) ->
  vmatch v (vnormalize chunk (Ifptr p)).
Proof.
  intros. exploit Mem.load_cast; eauto. exploit Mem.load_type; eauto.
  destruct chunk; simpl; intros.
- (* bool *)
  rewrite H2. auto with va.
- (* int8signed *)
  rewrite H2. destruct v; simpl; constructor. lia. apply is_sign_ext_sgn; auto with va.
- (* int8unsigned *)
  rewrite H2. destruct v; simpl; constructor. lia. apply is_zero_ext_uns; auto with va.
- (* int16signed *)
  rewrite H2. destruct v; simpl; constructor. lia. apply is_sign_ext_sgn; auto with va.
- (* int16unsigned *)
  rewrite H2. destruct v; simpl; constructor. lia. apply is_zero_ext_uns; auto with va.
- (* int32 *)
  red in H1. destruct Archi.ptr64; auto. destruct v; constructor || discriminate.
- (* int64 *)
  red in H1. destruct Archi.ptr64; auto. destruct v; constructor || discriminate.
- (* float32 *)
  destruct v; try contradiction; constructor.
- (* float64 *)
  destruct v; try contradiction; constructor.
- (* any32 *)
  red in H1. destruct Archi.ptr64; auto. destruct v; constructor || discriminate.
- (* any64 *)
  auto.
Qed.

Remark poffset_ge: forall p, pge (poffset p) p.
Proof.
  destruct p; constructor.
Qed.

Remark poffset_monotone:
  forall p q, pge p q -> pge (poffset p) (poffset q).
Proof.
  destruct 1; simpl; auto with va.
Qed.

Remark provenance_monotone:
  forall x y, vge x y -> pge (provenance x) (provenance y).
Proof.
  induction 1; simpl; eauto using poffset_ge, poffset_monotone, pge_trans with va.
Qed.

Remark provenance_ifptr_ge:
  forall p q, pge p q -> pge (provenance (Ifptr p)) q.
Proof.
  intros. simpl. apply pge_trans with p; auto. apply poffset_ge.
Qed.

Lemma vnormalize_monotone:
  forall chunk x y,
  vge x y -> vge (vnormalize chunk x) (vnormalize chunk y).
Proof with (auto using provenance_monotone, provenance_ifptr_ge with va).
Local Opaque provenance.
  assert (BOOL1: forall p i,
          vge (Uns p 1) (if Int.eq i Int.zero || Int.eq i Int.one then IU i else Uns Pbot 1)).
  {
    intros. predSpec Int.eq Int.eq_spec i Int.zero; subst.
    apply vge_uns_iu. lia. red; intros. apply Int.bits_zero.
    predSpec Int.eq Int.eq_spec i Int.one; subst.
    apply vge_uns_iu. lia. apply (is_uns_usize Int.one).
    apply vge_uns_uns. lia. auto with va.
  }
  assert (BOOL2: forall p i,
          vge (Uns p 1) (if Int.eq i Int.zero || Int.eq i Int.one then I i else Uns Pbot 1)).
  { intros. eapply vge_trans. apply (BOOL1 p i). destruct orb; auto with va. } 
  induction 1;
  unfold vnormalize; generalize Archi.ptr64; intro ptr64; subst; 
  destruct chunk eqn:C; simpl;
  repeat match goal with |- vge (if ?x then _ else _) _ => destruct x end...
- constructor... apply is_sign_ext_uns...
- constructor... apply is_sign_ext_sgn...
- constructor... apply is_zero_ext_uns... apply Z.min_case...
- constructor... apply is_sign_ext_uns...
- constructor... apply is_sign_ext_sgn...
- constructor... apply is_zero_ext_uns... apply Z.min_case...
- constructor... apply is_sign_ext_uns...
- constructor... apply is_sign_ext_sgn...
- constructor... apply is_zero_ext_uns... apply Z.min_case...
- constructor... apply is_sign_ext_uns...
- constructor... apply is_sign_ext_sgn...
- constructor... apply is_zero_ext_uns... apply Z.min_case...
- rewrite zlt_true by lia...
- destruct (zlt n2 8)...
- rewrite zlt_true by lia...
- destruct (zlt n2 16)...
- constructor... apply is_sign_ext_sgn... apply Z.min_case...
- constructor... apply is_zero_ext_uns...
- constructor... apply is_sign_ext_sgn... apply Z.min_case...
- constructor... apply is_zero_ext_uns...
- constructor... apply is_sign_ext_sgn... apply Z.min_case...
- constructor... apply is_zero_ext_uns...
- constructor... apply is_sign_ext_sgn... apply Z.min_case...
- constructor... apply is_zero_ext_uns...
- destruct (zlt n2 8); constructor...
- destruct (zlt n2 16); constructor...
- constructor... apply is_sign_ext_sgn...
- constructor... apply is_zero_ext_uns...
- constructor... apply is_sign_ext_sgn...
- constructor... apply is_zero_ext_uns...
- constructor... apply is_sign_ext_sgn...
- constructor... apply is_zero_ext_uns...
- constructor... apply is_sign_ext_sgn...
- constructor... apply is_zero_ext_uns...
- destruct (zlt n 8); constructor...
- destruct (zlt n 16); constructor...
- constructor... apply is_sign_ext_sgn...
- constructor... apply is_zero_ext_uns...
- constructor... apply is_sign_ext_sgn...
- constructor... apply is_zero_ext_uns...
- constructor... apply is_sign_ext_sgn...
- constructor... apply is_zero_ext_uns...
- constructor... apply is_sign_ext_sgn...
- constructor... apply is_zero_ext_uns...
- destruct (zlt n 8); constructor...
- destruct (zlt n 16); constructor...
Qed.

(** Analysis of known builtin functions.  All we have is a dynamic semantics
  as a function [list val -> option val], but we can still perform 
  some constant propagation. *)

Definition val_of_aval (a: aval) : val :=
  match a with
  | I n => Vint n
  | L n => Vlong n
  | F f => Vfloat f
  | FS f => Vsingle f
  | _ => Vundef
  end.

Definition aval_of_val (v: val) : option aval :=
  match v with
  | Vint n => Some (I n)
  | Vlong n => Some (L n)
  | Vfloat f => Some (F f)
  | Vsingle f => Some (FS f)
  | _ => None
  end.

Lemma val_of_aval_sound:
  forall v a, vmatch v a -> Val.lessdef (val_of_aval a) v.
Proof.
  destruct 1; simpl; auto.
Qed.

Corollary list_val_of_aval_sound:
  forall vl al, list_forall2 vmatch vl al -> Val.lessdef_list (map val_of_aval al) vl.
Proof.
  induction 1; simpl; constructor; auto using val_of_aval_sound.
Qed.

Lemma aval_of_val_sound:
  forall v a, aval_of_val v = Some a -> vmatch v a. 
Proof.
  intros v a E; destruct v; simpl in E; inv E; constructor.
Qed.

(** Lifting an extended type to a value approximation. *)

Definition of_xtype (x: xtype) (p: aptr) : aval :=
  match x with
  | Xbool => Uns p 1
  | Xint8signed => Sgn p 8
  | Xint8unsigned => Uns p 8
  | Xint16signed => Sgn p 16
  | Xint16unsigned => Uns p 16
  | _ => Ifptr p
  end.

Lemma of_xtype_arg_sound: forall v x p,
  Val.has_argtype v x ->
  vmatch v (Ifptr p) ->
  vmatch v (of_xtype x p).
Proof.
  intros. destruct x, v; simpl in *; try contradiction; auto with va.
- constructor. lia. apply is_uns_zero_ext. destruct H; subst i; auto.
- constructor. lia. apply is_sgn_sign_ext. lia. auto.
- constructor. lia. apply is_uns_zero_ext. auto.
- constructor. lia. apply is_sgn_sign_ext. lia. auto.
- constructor. lia. apply is_uns_zero_ext. auto.
Qed.

(** * Abstracting memory blocks *)

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
  intros; red; lia.
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
  intros; red; lia.
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
  subst v. apply Mem.loadbytes_load; auto. apply H; auto. generalize (size_chunk_pos chunk); lia.
Qed.

Lemma smatch_ext:
  forall m b p m',
  smatch m b p ->
  (forall ofs n bytes, Mem.loadbytes m' b ofs n = Some bytes -> n >= 0 -> Mem.loadbytes m b ofs n = Some bytes) ->
  smatch m' b p.
Proof.
  intros. destruct H. split; intros.
  eapply H; eauto. eapply loadbytes_load_ext; eauto.
  eapply H1; eauto. apply H0; eauto. lia.
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
    replace (1 + (sz - 1)) with sz by lia. auto.
    lia.
    lia.
    intros (bytes1 & bytes2 & LOAD1 & LOAD2 & CONCAT).
    subst bytes.
    exploit Mem.loadbytes_length. eexact LOAD1. change (Z.to_nat 1) with 1%nat. intros LENGTH1.
    rewrite in_app_iff in IN. destruct IN.
  * destruct bytes1; try discriminate. destruct bytes1; try discriminate.
    simpl in H. destruct H; try contradiction. subst m0.
    exists ofs; split. lia. auto.
  * exploit (REC (sz - 1)). red; lia. eexact LOAD2. auto.
    intros (ofs' & A & B).
    exists ofs'; split. lia. auto.
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
  replace (1 + (sz - 1)) with sz by lia. auto.
  lia.
  lia.
  intros (bytes1 & bytes2 & LOAD3 & LOAD4 & CONCAT). subst bytes. rewrite in_app_iff.
  destruct (zeq ofs ofs').
+ subst ofs'. rewrite LOAD1 in LOAD3; inv LOAD3. left; simpl; auto.
+ right. eapply (REC (sz - 1)). red; lia. eexact LOAD4. auto. lia.
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
    right. split. auto. lia.
  }
  destruct EITHER as [A | (A & B)].
- right. rewrite <- H0. symmetry. eapply Mem.loadbytes_storebytes_other; eauto. lia.
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
  unfold ablock_load, ablock_init; simpl.
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
  rewrite IHt by lia. apply ZTree.gro. unfold ZTree.elt, ZIndexed.t; lia.
  auto.
Qed.

Remark inval_after_contents:
  forall chunk av i lo hi c,
  (inval_after lo hi c)##i = Some (ACval chunk av) ->
  c##i = Some (ACval chunk av) /\ (i < lo \/ i > hi).
Proof.
  intros until c. functional induction (inval_after lo hi c); intros.
  destruct (zeq i hi).
  subst i. rewrite inval_after_outside in H by lia. rewrite ZTree.grs in H. discriminate.
  exploit IHt; eauto. intros [A B]. rewrite ZTree.gro in A by auto. split. auto. lia.
  split. auto. lia.
Qed.

Remark inval_before_outside:
  forall i hi lo c, i < lo \/ i >= hi -> (inval_before hi lo c)##i = c##i.
Proof.
  intros until c. functional induction (inval_before hi lo c); intros.
  rewrite IHt by lia. unfold inval_if. destruct (c##lo) as [[chunk av]|]; auto.
  destruct (zle (lo + size_chunk chunk) hi); auto.
  apply ZTree.gro. unfold ZTree.elt, ZIndexed.t; lia.
  auto.
Qed.

Remark inval_before_contents_1:
  forall i chunk av lo hi c,
  lo <= i < hi -> (inval_before hi lo c)##i = Some(ACval chunk av) ->
  c##i = Some(ACval chunk av) /\ i + size_chunk chunk <= hi.
Proof.
  intros until c. functional induction (inval_before hi lo c); intros.
- destruct (zeq lo i).
+ subst i. rewrite inval_before_outside in H0 by lia.
  unfold inval_if in H0. destruct (c##lo) as [[chunk0 v0]|] eqn:C; try congruence.
  destruct (zle (lo + size_chunk chunk0) hi).
  rewrite C in H0; inv H0. auto.
  rewrite ZTree.grs in H0. congruence.
+ exploit IHt. lia. auto. intros [A B]; split; auto.
  unfold inval_if in A. destruct (c##lo) as [[chunk0 v0]|] eqn:C; auto.
  destruct (zle (lo + size_chunk chunk0) hi); auto.
  rewrite ZTree.gro in A; auto.
- extlia.
Qed.

Lemma max_size_chunk: forall chunk, size_chunk chunk <= 8.
Proof.
  destruct chunk; simpl; lia.
Qed.

Remark inval_before_contents:
  forall i c chunk' av' j,
  (inval_before i (i - 7) c)##j = Some (ACval chunk' av') ->
  c##j = Some (ACval chunk' av') /\ (j + size_chunk chunk' <= i \/ i <= j).
Proof.
  intros. destruct (zlt j (i - 7)).
  rewrite inval_before_outside in H by lia.
  split. auto. left. generalize (max_size_chunk chunk'); lia.
  destruct (zlt j i).
  exploit inval_before_contents_1; eauto. lia. tauto.
  rewrite inval_before_outside in H by lia.
  split. auto. lia.
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
  split. auto. lia.
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
  split. auto. extlia.
Qed.

Lemma ablock_storebytes_sound:
  forall m b ofs bytes m' p ab sz,
  Mem.storebytes m b ofs bytes = Some m' ->
  length bytes = Z.to_nat sz ->
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
    rewrite U. rewrite LENGTH. rewrite Z_to_nat_max. right; lia. }
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
  apply P. generalize (size_chunk_pos chunk); lia.
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
  length bytes = Z.to_nat sz ->
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
- red; intros. exploit mmatch_below0; eauto. extlia.
Qed.

Lemma mmatch_free:
  forall m b lo hi m' am,
  Mem.free m b lo hi = Some m' ->
  mmatch m am ->
  mmatch m' am.
Proof.
  intros. apply mmatch_ext with m; auto.
  intros. eapply Mem.loadbytes_free_2; eauto.
  erewrite <- Mem.nextblock_free by eauto. extlia.
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

(** * Nonaliasing tests. *)

(** [pdisjoint p1 sz1 p2 sz2] returns [true] if there can be no overlap
    between a block of size [sz1] in the region characterized by [p1]
    and a block of size [sz2] in the region characterized by [p2]. *)

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
  forall (bc: block_classification) sz1 b1 ofs1 p1 sz2 b2 ofs2 p2,
  pdisjoint p1 sz1 p2 sz2 = true ->
  pmatch bc b1 ofs1 p1 -> pmatch bc b2 ofs2 p2 ->
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

(** This is a stronger property of [pdisjoint], guaranteeing nonaliasing
    even if the two pointers are considered in different, but compatible
    block classifications. *)

Lemma pdisjoint_sound_strong:
  forall sz1 b1 ofs1 bc1 p1 sz2 b2 ofs2 bc2 p2 ge sp,
  pdisjoint p1 sz1 p2 sz2 = true ->
  pmatch bc1 b1 ofs1 p1 -> pmatch bc2 b2 ofs2 p2 ->
  genv_match bc1 ge -> bc1 sp = BCstack ->
  genv_match bc2 ge -> bc2 sp = BCstack ->
  b1 <> b2 \/ Ptrofs.unsigned ofs1 + sz1 <= Ptrofs.unsigned ofs2 \/ Ptrofs.unsigned ofs2 + sz2 <= Ptrofs.unsigned ofs1.
Proof.
  assert (GLOB_GLOB: forall (bc1 bc2: block_classification) ge b1 b2 id1 id2,
           genv_match bc1 ge -> genv_match bc2 ge ->
           bc1 b1 = BCglob id1 -> bc2 b2 = BCglob id2 ->
           id1 <> id2 -> b1 <> b2).
  { intros until id2; intros GE1 GE2 EQ1 EQ2 DIFF.
    apply GE1 in EQ1; apply GE2 in EQ2.
    apply Genv.find_invert_symbol in EQ1; apply Genv.find_invert_symbol in EQ2.
    congruence. }
  assert (GLOB_STACK: forall (bc1 bc2: block_classification) ge sp b1 b2 id,
           genv_match bc1 ge -> bc1 sp = BCstack -> bc2 sp = BCstack ->
           bc1 b1 = BCglob id -> bc2 b2 = BCstack ->
           b1 <> b2).
  { intros until id; intros GE1 SP1 SP2 EQ1 EQ2.
    apply GE1 in EQ1.
    assert (bc1 b1 <> BCstack) by (apply GE1; eapply (Senv.find_symbol_below ge); eauto).
    assert (b2 = sp) by (eapply bc2.(bc_stack); eauto).
    congruence. }
  assert (STACK_OTHER: forall (bc1 bc2: block_classification) sp b1 b2,
           bc1 sp = BCstack -> bc2 sp = BCstack ->
           bc1 b1 = BCstack -> bc2 b2 <> BCstack ->
           b1 <> b2).
  { intros until b2; intros SP1 SP2 EQ1 EQ2.
    assert (b1 = sp) by (eapply bc1.(bc_stack); eauto).
    congruence. }
  intros until sp; intros DISJ PM1 PM2 GE1 SP1 GE2 SP2.
  inv PM1; inv PM2; simpl in DISJ; try discriminate; eauto using not_eq_sym.
  - destruct (peq id id0).
    + subst id0. destruct (orb_true_elim _ _ DISJ); InvBooleans; auto.
    + eauto.
  - destruct (peq id id0); discriminate || eauto.
  - destruct (peq id id0); discriminate || eauto.
  - destruct (peq id id0); discriminate || eauto.
  - destruct (orb_true_elim _ _ DISJ); InvBooleans; auto.
Qed.

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
    red; intros. replace ofs0 with ofs by lia. auto.
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
  rewrite Z.add_0_r. split. lia. apply Ptrofs.unsigned_range_2.
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

Fixpoint einit_regs (rl: list reg) (tl: list xtype) : aenv :=
  match rl, tl with
  | nil, _ => AE.top
  | r1 :: rs, t1 :: ts =>
      let a1 :=
        if Conventions1.parameter_needs_normalization t1
        then Ifptr Nonstack
        else of_xtype t1 Nonstack in
      AE.set r1 a1 (einit_regs rs ts)
  | r1 :: rs, nil => AE.set r1 (Ifptr Nonstack) (einit_regs rs nil)
  end.

Lemma ematch_init:
  forall rl vl tl,
  Val.has_argtype_list vl tl ->
  (forall v, In v vl -> vmatch bc v (Ifptr Nonstack)) ->
  ematch (init_regs vl rl) (einit_regs rl tl).
Proof.
Local Opaque Conventions1.parameter_needs_normalization.
  assert (A: forall rs ae, ematch rs ae -> ae <> AE.Bot).
  { intros; red; intros EQ. rewrite EQ in H. specialize (H 1%positive). simpl in H. inv H. }
  assert (B: ~AVal.eq (Ifptr Nonstack) AVal.bot) by (unfold AVal.eq, AVal.bot; congruence).
  assert (C: forall t, ~AVal.eq (of_xtype t Nonstack) AVal.bot).
  { intros. unfold AVal.eq, AVal.bot; destruct t; simpl; congruence. }
  induction rl; simpl; intros vl tl T V.
- red; intros. rewrite Regmap.gi. simpl. constructor.
- inv T.
  + assert (REC: ematch (init_regs nil rl) (einit_regs rl nil)).
    { apply IHrl. constructor. auto. }
    replace (init_regs nil rl) with (Regmap.init Vundef) in REC by (destruct rl; auto).
    red; intros. rewrite AE.gsspec by eauto. destruct (peq r a).
    rewrite Regmap.gi; constructor.
    apply REC.
  + assert (REC: ematch (init_regs al rl) (einit_regs rl bl)).
    { apply IHrl; eauto with coqlib. }
    red; intros. rewrite Regmap.gsspec, AE.gsspec; eauto.
    * destruct (peq r a).
      destruct (Conventions1.parameter_needs_normalization b1);
      auto using of_xtype_arg_sound with coqlib.
      apply REC.
    * destruct (Conventions1.parameter_needs_normalization b1); auto.
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

Global Hint Constructors cmatch : va.
Global Hint Constructors pmatch: va.
Global Hint Constructors vmatch: va.
Global Hint Resolve cnot_sound symbol_address_sound
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
       zero_ext_l_sound sign_ext_l_sound
       singleoffloat_sound floatofsingle_sound
       intoffloat_sound intuoffloat_sound floatofint_sound floatofintu_sound
       intofsingle_sound intuofsingle_sound singleofint_sound singleofintu_sound
       longoffloat_sound longuoffloat_sound floatoflong_sound floatoflongu_sound
       longofsingle_sound longuofsingle_sound singleoflong_sound singleoflongu_sound
       longofwords_sound loword_sound hiword_sound
       cmpu_bool_sound cmp_bool_sound cmplu_bool_sound cmpl_bool_sound
       cmpf_bool_sound cmpfs_bool_sound
       maskzero_sound : va.
