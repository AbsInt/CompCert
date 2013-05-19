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

(** Correctness proof for the [Allocation] pass (validated translation from
  RTL to LTL). *)

Require Import FSets.
Require Import Coqlib.
Require Import Ordered.
Require Import Errors.
Require Import Maps.
Require Import Lattice.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import RTLtyping.
Require Import Kildall.
Require Import Locations.
Require Import Conventions.
Require Import LTL.
Require Import Allocation.

(** * Soundness of structural checks *)

Definition expand_move (sd: loc * loc) : instruction :=
  match sd with
  | (R src, R dst) => Lop Omove (src::nil) dst
  | (S sl ofs ty, R dst) => Lgetstack sl ofs ty dst
  | (R src, S sl ofs ty) => Lsetstack src sl ofs ty
  | (S _ _ _, S _ _ _) => Lreturn    (**r should never happen *)
  end.

Definition expand_moves (mv: moves) (k: bblock) : bblock :=
  List.map expand_move mv ++ k.

Definition wf_move (sd: loc * loc) : Prop :=
  match sd with
  | (S _ _ _, S _ _ _) => False
  | _ => True
  end.

Definition wf_moves (mv: moves) : Prop :=
  forall sd, In sd mv -> wf_move sd.

Inductive expand_block_shape: block_shape -> RTL.instruction -> LTL.bblock -> Prop :=
  | ebs_nop: forall mv s k,
      wf_moves mv ->
      expand_block_shape (BSnop mv s)
                         (Inop s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_move: forall src dst mv s k,
      wf_moves mv ->
      expand_block_shape (BSmove src dst mv s)
                         (Iop Omove (src :: nil) dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_makelong: forall src1 src2 dst mv s k,
      wf_moves mv ->
      expand_block_shape (BSmakelong src1 src2 dst mv s)
                         (Iop Omakelong (src1 :: src2 :: nil) dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_lowlong: forall src dst mv s k,
      wf_moves mv ->
      expand_block_shape (BSlowlong src dst mv s)
                         (Iop Olowlong (src :: nil) dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_highlong: forall src dst mv s k,
      wf_moves mv ->
      expand_block_shape (BShighlong src dst mv s)
                         (Iop Ohighlong (src :: nil) dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_op: forall op args res mv1 args' res' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BSop op args res mv1 args' res' mv2 s)
                         (Iop op args res s)
                         (expand_moves mv1
                           (Lop op args' res' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_op_dead: forall op args res mv s k,
      wf_moves mv ->
      expand_block_shape (BSopdead op args res mv s)
                         (Iop op args res s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_load: forall chunk addr args dst mv1 args' dst' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BSload chunk addr args dst mv1 args' dst' mv2 s)
                         (Iload chunk addr args dst s)
                         (expand_moves mv1
                           (Lload chunk addr args' dst' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_load2: forall addr addr2 args dst mv1 args1' dst1' mv2 args2' dst2' mv3 s k,
      wf_moves mv1 -> wf_moves mv2 -> wf_moves mv3 ->
      offset_addressing addr (Int.repr 4) = Some addr2 ->
      expand_block_shape (BSload2 addr addr2 args dst mv1 args1' dst1' mv2 args2' dst2' mv3 s)
                         (Iload Mint64 addr args dst s)
                         (expand_moves mv1
                           (Lload Mint32 addr args1' dst1' ::
                           expand_moves mv2
                             (Lload Mint32 addr2 args2' dst2' :: 
                              expand_moves mv3 (Lbranch s :: k))))
  | ebs_load2_1: forall addr args dst mv1 args' dst' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BSload2_1 addr args dst mv1 args' dst' mv2 s)
                         (Iload Mint64 addr args dst s)
                         (expand_moves mv1
                           (Lload Mint32 addr args' dst' ::
                            expand_moves mv2 (Lbranch s :: k)))
  | ebs_load2_2: forall addr addr2 args dst mv1 args' dst' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      offset_addressing addr (Int.repr 4) = Some addr2 ->
      expand_block_shape (BSload2_2 addr addr2 args dst mv1 args' dst' mv2 s)
                         (Iload Mint64 addr args dst s)
                         (expand_moves mv1
                           (Lload Mint32 addr2 args' dst' ::
                            expand_moves mv2 (Lbranch s :: k)))
  | ebs_load_dead: forall chunk addr args dst mv s k,
      wf_moves mv ->
      expand_block_shape (BSloaddead chunk addr args dst mv s)
                         (Iload chunk addr args dst s)
                         (expand_moves mv (Lbranch s :: k))
  | ebs_store: forall chunk addr args src mv1 args' src' s k,
      wf_moves mv1 ->
      expand_block_shape (BSstore chunk addr args src mv1 args' src' s)
                         (Istore chunk addr args src s)
                         (expand_moves mv1
                           (Lstore chunk addr args' src' :: Lbranch s :: k))
  | ebs_store2: forall addr addr2 args src mv1 args1' src1' mv2 args2' src2' s k,
      wf_moves mv1 -> wf_moves mv2 ->
      offset_addressing addr (Int.repr 4) = Some addr2 ->
      expand_block_shape (BSstore2 addr addr2 args src mv1 args1' src1' mv2 args2' src2' s)
                         (Istore Mint64 addr args src s)
                         (expand_moves mv1
                           (Lstore Mint32 addr args1' src1' ::
                            expand_moves mv2
                             (Lstore Mint32 addr2 args2' src2' ::
                              Lbranch s :: k)))
  | ebs_call: forall sg ros args res mv1 ros' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BScall sg ros args res mv1 ros' mv2 s)
                         (Icall sg ros args res s)
                         (expand_moves mv1
                           (Lcall sg ros' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_tailcall: forall sg ros args mv ros' k,
      wf_moves mv ->
      expand_block_shape (BStailcall sg ros args mv ros')
                         (Itailcall sg ros args)
                         (expand_moves mv (Ltailcall sg ros' :: k))
  | ebs_builtin: forall ef args res mv1 args' res' mv2 s k,
      wf_moves mv1 -> wf_moves mv2 ->
      expand_block_shape (BSbuiltin ef args res mv1 args' res' mv2 s)
                         (Ibuiltin ef args res s)
                         (expand_moves mv1
                           (Lbuiltin ef args' res' :: expand_moves mv2 (Lbranch s :: k)))
  | ebs_annot: forall txt typ args res mv args' s k,
      wf_moves mv ->
      expand_block_shape (BSannot txt typ args res mv args' s)
                         (Ibuiltin (EF_annot txt typ) args res s)
                         (expand_moves mv
                           (Lannot (EF_annot txt typ) args' :: Lbranch s :: k))
  | ebs_cond: forall cond args mv args' s1 s2 k,
      wf_moves mv ->
      expand_block_shape (BScond cond args mv args' s1 s2)
                         (Icond cond args s1 s2)
                         (expand_moves mv (Lcond cond args' s1 s2 :: k))
  | ebs_jumptable: forall arg mv arg' tbl k,
      wf_moves mv ->
      expand_block_shape (BSjumptable arg mv arg' tbl)
                         (Ijumptable arg tbl)
                         (expand_moves mv (Ljumptable arg' tbl :: k))
  | ebs_return: forall optarg mv k,
      wf_moves mv ->
      expand_block_shape (BSreturn optarg mv)
                         (Ireturn optarg)
                         (expand_moves mv (Lreturn :: k)).

Ltac MonadInv :=
  match goal with
  | [ H: match ?x with Some _ => _ | None => None end = Some _ |- _ ] =>
        destruct x as [] eqn:? ; [MonadInv|discriminate]
  | [ H: match ?x with left _ => _ | right _ => None end = Some _ |- _ ] =>
        destruct x; [MonadInv|discriminate]
  | [ H: match negb (proj_sumbool ?x) with true => _ | false => None end = Some _ |- _ ] =>
        destruct x; [discriminate|simpl in H; MonadInv]
  | [ H: match negb ?x with true => _ | false => None end = Some _ |- _ ] =>
        destruct x; [discriminate|simpl in H; MonadInv]
  | [ H: match ?x with true => _ | false => None end = Some _ |- _ ] =>
        destruct x as [] eqn:? ; [MonadInv|discriminate]
  | [ H: match ?x with (_, _) => _ end = Some _ |- _ ] =>
        destruct x as [] eqn:? ; MonadInv
  | [ H: Some _ = Some _ |- _ ] =>
        inv H; MonadInv
  | [ H: None = Some _ |- _ ] =>
        discriminate
  | _ =>
        idtac
  end.

Lemma extract_moves_sound:
  forall b mv b',
  extract_moves nil b = (mv, b') ->
  wf_moves mv /\ b = expand_moves mv b'.
Proof.
  assert (BASE:
      forall accu b,
      wf_moves accu ->
      wf_moves (List.rev accu) /\ expand_moves (List.rev accu) b = expand_moves (List.rev accu) b).
   intros; split; auto.
   red; intros. apply H. rewrite <- in_rev in H0; auto.

  assert (IND: forall b accu mv b',
          extract_moves accu b = (mv, b') ->
          wf_moves accu ->
          wf_moves mv /\ expand_moves (List.rev accu) b = expand_moves mv b').
    induction b; simpl; intros. 
    inv H. auto.
    destruct a; try (inv H; apply BASE; auto; fail).
    destruct (is_move_operation op args) as [arg|] eqn:E.
    exploit is_move_operation_correct; eauto. intros [A B]; subst.
    (* reg-reg move *)
    exploit IHb; eauto.
      red; intros. destruct H1; auto. subst sd; exact I.
    intros [P Q].
    split; auto. rewrite <- Q. simpl. unfold expand_moves. rewrite map_app. 
    rewrite app_ass. simpl. auto.
    inv H; apply BASE; auto.
    (* stack-reg move *)
    exploit IHb; eauto.
      red; intros. destruct H1; auto. subst sd; exact I.
    intros [P Q].
    split; auto. rewrite <- Q. simpl. unfold expand_moves. rewrite map_app. 
    rewrite app_ass. simpl. auto.
    (* reg-stack move *)
    exploit IHb; eauto.
      red; intros. destruct H1; auto. subst sd; exact I.
    intros [P Q].
    split; auto. rewrite <- Q. simpl. unfold expand_moves. rewrite map_app. 
    rewrite app_ass. simpl. auto.

  intros. exploit IND; eauto. red; intros. elim H0. 
Qed.

Lemma check_succ_sound:
  forall s b, check_succ s b = true -> exists k, b = Lbranch s :: k.
Proof.
  intros. destruct b; simpl in H; try discriminate. 
  destruct i; try discriminate. 
  destruct (peq s s0); simpl in H; inv H. exists b; auto.
Qed.

Ltac UseParsingLemmas :=
  match goal with
  | [ H: extract_moves nil _ = (_, _) |- _ ] =>
      destruct (extract_moves_sound _ _ _ H); clear H; subst; UseParsingLemmas
  | [ H: check_succ _ _ = true |- _ ] =>
      try discriminate;
      destruct (check_succ_sound _ _ H); clear H; subst; UseParsingLemmas
  | _ => idtac
  end.

Lemma pair_instr_block_sound:
  forall i b bsh,
  pair_instr_block i b = Some bsh -> expand_block_shape bsh i b.
Proof.
  intros; destruct i; simpl in H; MonadInv; UseParsingLemmas.
(* nop *)
  econstructor; eauto.
(* op *)
  destruct (classify_operation o l). 
  (* move *)
  MonadInv; UseParsingLemmas. econstructor; eauto. 
  (* makelong *)
  MonadInv; UseParsingLemmas. econstructor; eauto.
  (* lowlong *)
  MonadInv; UseParsingLemmas. econstructor; eauto.
  (* highlong *)
  MonadInv; UseParsingLemmas. econstructor; eauto.
  (* other ops *)
  MonadInv. destruct b0.
  MonadInv; UseParsingLemmas.
  destruct i; MonadInv; UseParsingLemmas. 
  eapply ebs_op; eauto.
  inv H0. eapply ebs_op_dead; eauto.
(* load *)
  destruct b0.
  MonadInv; UseParsingLemmas.
  destruct i; MonadInv; UseParsingLemmas.
  destruct (chunk_eq m Mint64).
  MonadInv; UseParsingLemmas. 
  destruct b; MonadInv; UseParsingLemmas. destruct i; MonadInv; UseParsingLemmas. 
  eapply ebs_load2; eauto.
  destruct (eq_addressing a addr).
  MonadInv. inv H2. eapply ebs_load2_1; eauto.
  MonadInv. inv H2. eapply ebs_load2_2; eauto.
  MonadInv; UseParsingLemmas. eapply ebs_load; eauto.
  inv H. eapply ebs_load_dead; eauto.
(* store *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas.
  destruct (chunk_eq m Mint64).
  MonadInv; UseParsingLemmas.
  destruct b; MonadInv. destruct i; MonadInv; UseParsingLemmas.
  eapply ebs_store2; eauto.
  MonadInv; UseParsingLemmas.
  eapply ebs_store; eauto.
(* call *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas. econstructor; eauto. 
(* tailcall *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas. econstructor; eauto.
(* builtin *) 
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas.
  econstructor; eauto.
  destruct ef; inv H. econstructor; eauto. 
(* cond *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas. econstructor; eauto.
(* jumptable *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas. econstructor; eauto.
(* return *)
  destruct b0; MonadInv. destruct i; MonadInv; UseParsingLemmas. econstructor; eauto.
Qed.

Lemma matching_instr_block:
  forall f1 f2 pc bsh i,
  (pair_codes f1 f2)!pc = Some bsh ->
  (RTL.fn_code f1)!pc = Some i ->
  exists b, (LTL.fn_code f2)!pc = Some b /\ expand_block_shape bsh i b.
Proof.
  intros. unfold pair_codes in H. rewrite PTree.gcombine in H; auto. rewrite H0 in H.
  destruct (LTL.fn_code f2)!pc as [b|]. 
  exists b; split; auto. apply pair_instr_block_sound; auto. 
  discriminate.
Qed.

(** * Properties of equations *)

Module ESF := FSetFacts.Facts(EqSet).
Module ESP := FSetProperties.Properties(EqSet).
Module ESD := FSetDecide.Decide(EqSet).

Definition sel_val (k: equation_kind) (v: val) : val :=
  match k with
  | Full => v
  | Low => Val.loword v
  | High => Val.hiword v
  end.

(** A set of equations [e] is satisfied in a RTL pseudoreg state [rs]
  and an LTL location state [ls] if, for every equation [r = l [k]] in [e],
  [sel_val k (rs#r)] (the [k] fragment of [r]'s value in the RTL code)
  is less defined than [ls l] (the value of [l] in the LTL code). *)

Definition satisf (rs: regset) (ls: locset) (e: eqs) : Prop :=
  forall q, EqSet.In q e -> Val.lessdef (sel_val (ekind q) rs#(ereg q)) (ls (eloc q)).

Lemma empty_eqs_satisf:
  forall rs ls, satisf rs ls empty_eqs.
Proof.
  unfold empty_eqs; intros; red; intros. ESD.fsetdec.
Qed.

Lemma satisf_incr:
  forall rs ls (e1 e2: eqs),
  satisf rs ls e2 -> EqSet.Subset e1 e2 -> satisf rs ls e1.
Proof.
  unfold satisf; intros. apply H. ESD.fsetdec. 
Qed.

Lemma satisf_undef_reg:
  forall rs ls e r,
  satisf rs ls e ->
  satisf (rs#r <- Vundef) ls e.
Proof.
  intros; red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r); auto.
  destruct (ekind q); simpl; auto.
Qed.

Lemma add_equation_lessdef:
  forall rs ls q e,
  satisf rs ls (add_equation q e) -> Val.lessdef (sel_val (ekind q) rs#(ereg q)) (ls (eloc q)).
Proof.
  intros. apply H. unfold add_equation. simpl. apply EqSet.add_1. auto. 
Qed.

Lemma add_equation_satisf:
  forall rs ls q e,
  satisf rs ls (add_equation q e) -> satisf rs ls e.
Proof.
  intros. eapply satisf_incr; eauto. unfold add_equation. simpl. ESD.fsetdec. 
Qed.

Lemma add_equations_satisf:
  forall rs ls rl ml e e',
  add_equations rl ml e = Some e' ->
  satisf rs ls e' -> satisf rs ls e.
Proof.
  induction rl; destruct ml; simpl; intros; MonadInv.
  auto.
  eapply add_equation_satisf; eauto. 
Qed.

Lemma add_equations_lessdef:
  forall rs ls rl ml e e',
  add_equations rl ml e = Some e' ->
  satisf rs ls e' ->
  Val.lessdef_list (rs##rl) (reglist ls ml).
Proof.
  induction rl; destruct ml; simpl; intros; MonadInv.
  constructor.
  constructor; eauto.
  apply add_equation_lessdef with (e := e) (q := Eq Full a (R m)).
  eapply add_equations_satisf; eauto.
Qed.

Lemma add_equations_args_satisf:
  forall rs ls rl tyl ll e e',
  add_equations_args rl tyl ll e = Some e' ->
  satisf rs ls e' -> satisf rs ls e.
Proof.
  intros until e'. functional induction (add_equations_args rl tyl ll e); intros.
  inv H; auto. 
  eapply add_equation_satisf. eapply add_equation_satisf. eauto. 
  eapply add_equation_satisf. eauto.
  eapply add_equation_satisf. eauto.
  eapply add_equation_satisf. eauto.
  congruence.
Qed.

Lemma val_longofwords_eq:
  forall v,
  Val.has_type v Tlong ->
  Val.longofwords (Val.hiword v) (Val.loword v) = v.
Proof.
  intros. red in H. destruct v; try contradiction.
  reflexivity.
  simpl. rewrite Int64.ofwords_recompose. auto.
Qed.

Lemma add_equations_args_lessdef:
  forall rs ls rl tyl ll e e',
  add_equations_args rl tyl ll e = Some e' ->
  satisf rs ls e' ->
  Val.has_type_list (rs##rl) tyl ->
  Val.lessdef_list (rs##rl) (decode_longs tyl (map ls ll)).
Proof.
  intros until e'. functional induction (add_equations_args rl tyl ll e); simpl; intros.
- inv H; auto.
- destruct H1. constructor; auto. 
  rewrite <- (val_longofwords_eq (rs#r1)); auto. apply Val.longofwords_lessdef. 
  eapply add_equation_lessdef with (q := Eq High r1 l1). 
  eapply add_equation_satisf. eapply add_equations_args_satisf; eauto. 
  eapply add_equation_lessdef with (q := Eq Low r1 l2). 
  eapply add_equations_args_satisf; eauto.
- destruct H1. constructor; auto. 
  eapply add_equation_lessdef with (q := Eq Full r1 l1). eapply add_equations_args_satisf; eauto.
- destruct H1. constructor; auto. 
  eapply add_equation_lessdef with (q := Eq Full r1 l1). eapply add_equations_args_satisf; eauto.
- destruct H1. constructor; auto. 
  eapply add_equation_lessdef with (q := Eq Full r1 l1). eapply add_equations_args_satisf; eauto.
- discriminate.
Qed.

Lemma add_equation_ros_satisf:
  forall rs ls ros mos e e',
  add_equation_ros ros mos e = Some e' ->
  satisf rs ls e' -> satisf rs ls e.
Proof.
  unfold add_equation_ros; intros. destruct ros; destruct mos; MonadInv.
  eapply add_equation_satisf; eauto.
  auto.
Qed.

Lemma remove_equation_satisf:
  forall rs ls q e,
  satisf rs ls e -> satisf rs ls (remove_equation q e).
Proof.
  intros. eapply satisf_incr; eauto. unfold remove_equation; simpl. ESD.fsetdec. 
Qed.

Lemma remove_equation_res_satisf:
  forall rs ls r oty ll e e',
  remove_equations_res r oty ll e = Some e' ->
  satisf rs ls e -> satisf rs ls e'.
Proof.
  intros. functional inversion H. 
  apply remove_equation_satisf. apply remove_equation_satisf; auto.
  apply remove_equation_satisf; auto.
Qed.

Remark select_reg_l_monotone:
  forall r q1 q2,
  OrderedEquation.eq q1 q2 \/ OrderedEquation.lt q1 q2 ->
  select_reg_l r q1 = true -> select_reg_l r q2 = true.
Proof.
  unfold select_reg_l; intros. destruct H.
  red in H. congruence.
  rewrite Pos.leb_le in *. red in H. destruct H as [A | [A B]]. 
  red in A. zify; omega.
  rewrite <- A; auto.
Qed.

Remark select_reg_h_monotone:
  forall r q1 q2,
  OrderedEquation.eq q1 q2 \/ OrderedEquation.lt q2 q1 ->
  select_reg_h r q1 = true -> select_reg_h r q2 = true.
Proof.
  unfold select_reg_h; intros. destruct H.
  red in H. congruence.
  rewrite Pos.leb_le in *. red in H. destruct H as [A | [A B]]. 
  red in A. zify; omega.
  rewrite A; auto.
Qed.

Remark select_reg_charact:
  forall r q, select_reg_l r q = true /\ select_reg_h r q = true <-> ereg q = r.
Proof.
  unfold select_reg_l, select_reg_h; intros; split.
  rewrite ! Pos.leb_le. unfold reg; zify; omega.
  intros. rewrite H. rewrite ! Pos.leb_refl; auto. 
Qed.

Lemma reg_unconstrained_sound:
  forall r e q,
  reg_unconstrained r e = true ->
  EqSet.In q e ->
  ereg q <> r.
Proof.
  unfold reg_unconstrained; intros. red; intros.
  apply select_reg_charact in H1. 
  assert (EqSet.mem_between (select_reg_l r) (select_reg_h r) e = true).
  {
    apply EqSet.mem_between_2 with q; auto.
    exact (select_reg_l_monotone r).
    exact (select_reg_h_monotone r).
    tauto.
    tauto.
  }
  rewrite H2 in H; discriminate.
Qed.

Lemma reg_unconstrained_satisf:
  forall r e rs ls v,
  reg_unconstrained r e = true ->
  satisf rs ls e ->
  satisf (rs#r <- v) ls e.
Proof.
  red; intros. rewrite PMap.gso. auto. eapply reg_unconstrained_sound; eauto. 
Qed.

Remark select_loc_l_monotone:
  forall l q1 q2,
  OrderedEquation'.eq q1 q2 \/ OrderedEquation'.lt q1 q2 ->
  select_loc_l l q1 = true -> select_loc_l l q2 = true.
Proof.
  unfold select_loc_l; intros. set (lb := OrderedLoc.diff_low_bound l) in *.
  destruct H.
  red in H. subst q2; auto. 
  assert (eloc q1 = eloc q2 \/ OrderedLoc.lt (eloc q1) (eloc q2)).
    red in H. tauto. 
  destruct H1. rewrite <- H1; auto. 
  destruct (OrderedLoc.compare (eloc q2) lb); auto. 
  assert (OrderedLoc.lt (eloc q1) lb) by (eapply OrderedLoc.lt_trans; eauto). 
  destruct (OrderedLoc.compare (eloc q1) lb). 
  auto.
  eelim OrderedLoc.lt_not_eq; eauto.
  eelim OrderedLoc.lt_not_eq. eapply OrderedLoc.lt_trans. eexact l1. eexact H2. red; auto.
Qed.

Remark select_loc_h_monotone:
  forall l q1 q2,
  OrderedEquation'.eq q1 q2 \/ OrderedEquation'.lt q2 q1 ->
  select_loc_h l q1 = true -> select_loc_h l q2 = true.
Proof.
  unfold select_loc_h; intros. set (lb := OrderedLoc.diff_high_bound l) in *.
  destruct H.
  red in H. subst q2; auto. 
  assert (eloc q2 = eloc q1 \/ OrderedLoc.lt (eloc q2) (eloc q1)).
    red in H. tauto. 
  destruct H1. rewrite H1; auto. 
  destruct (OrderedLoc.compare (eloc q2) lb); auto. 
  assert (OrderedLoc.lt lb (eloc q1)) by (eapply OrderedLoc.lt_trans; eauto). 
  destruct (OrderedLoc.compare (eloc q1) lb). 
  eelim OrderedLoc.lt_not_eq. eapply OrderedLoc.lt_trans. eexact l1. eexact H2. red; auto.
  eelim OrderedLoc.lt_not_eq. eexact H2. apply OrderedLoc.eq_sym; auto.
  auto.
Qed.

Remark select_loc_charact:
  forall l q,
  select_loc_l l q = false \/ select_loc_h l q = false <-> Loc.diff l (eloc q).
Proof.
  unfold select_loc_l, select_loc_h; intros; split; intros.
  apply OrderedLoc.outside_interval_diff. 
  destruct H.
  left. destruct (OrderedLoc.compare (eloc q) (OrderedLoc.diff_low_bound l)); assumption || discriminate.
  right. destruct (OrderedLoc.compare (eloc q) (OrderedLoc.diff_high_bound l)); assumption || discriminate.
  exploit OrderedLoc.diff_outside_interval. eauto. 
  intros [A | A].
  left. destruct (OrderedLoc.compare (eloc q) (OrderedLoc.diff_low_bound l)).
  auto.
  eelim OrderedLoc.lt_not_eq; eauto. 
  eelim OrderedLoc.lt_not_eq. eapply OrderedLoc.lt_trans; eauto. red; auto.
  right. destruct (OrderedLoc.compare (eloc q) (OrderedLoc.diff_high_bound l)).
  eelim OrderedLoc.lt_not_eq. eapply OrderedLoc.lt_trans; eauto. red; auto.
  eelim OrderedLoc.lt_not_eq; eauto. apply OrderedLoc.eq_sym; auto. 
  auto.
Qed.

Lemma loc_unconstrained_sound:
  forall l e q,
  loc_unconstrained l e = true ->
  EqSet.In q e ->
  Loc.diff l (eloc q).
Proof.
  unfold loc_unconstrained; intros. 
  destruct (select_loc_l l q) eqn:SL.
  destruct (select_loc_h l q) eqn:SH.
  assert (EqSet2.mem_between (select_loc_l l) (select_loc_h l) (eqs2 e) = true).
  {
    apply EqSet2.mem_between_2 with q; auto.
    exact (select_loc_l_monotone l).
    exact (select_loc_h_monotone l).
    apply eqs_same. auto. 
  }
  rewrite H1 in H; discriminate.
  apply select_loc_charact; auto.
  apply select_loc_charact; auto.
Qed.

Lemma loc_unconstrained_satisf:
  forall rs ls k r mr e v,
  let l := R mr in
  satisf rs ls (remove_equation (Eq k r l) e) ->
  loc_unconstrained (R mr) (remove_equation (Eq k r l) e) = true ->
  Val.lessdef (sel_val k rs#r) v ->
  satisf rs (Locmap.set l v ls) e.
Proof.
  intros; red; intros. 
  destruct (OrderedEquation.eq_dec q (Eq k r l)). 
  subst q; simpl. unfold l; rewrite Locmap.gss_reg. auto.
  assert (EqSet.In q (remove_equation (Eq k r l) e)).
    simpl. ESD.fsetdec.  
  rewrite Locmap.gso. apply H; auto. eapply loc_unconstrained_sound; eauto. 
Qed.

Lemma reg_loc_unconstrained_sound:
  forall r l e q,
  reg_loc_unconstrained r l e = true ->
  EqSet.In q e ->
  ereg q <> r /\ Loc.diff l (eloc q).
Proof.
  intros. destruct (andb_prop _ _ H). 
  split. eapply reg_unconstrained_sound; eauto. eapply loc_unconstrained_sound; eauto.
Qed.

Lemma parallel_assignment_satisf:
  forall k r mr e rs ls v v',
  let l := R mr in
  Val.lessdef (sel_val k v) v' ->
  reg_loc_unconstrained r (R mr) (remove_equation (Eq k r l) e) = true ->
  satisf rs ls (remove_equation (Eq k r l) e) ->
  satisf (rs#r <- v) (Locmap.set l v' ls) e.
Proof.
  intros; red; intros.
  destruct (OrderedEquation.eq_dec q (Eq k r l)).
  subst q; simpl. unfold l; rewrite Regmap.gss; rewrite Locmap.gss_reg; auto.
  assert (EqSet.In q (remove_equation {| ekind := k; ereg := r; eloc := l |} e)).
    simpl. ESD.fsetdec.
  exploit reg_loc_unconstrained_sound; eauto. intros [A B].
  rewrite Regmap.gso; auto. rewrite Locmap.gso; auto. 
Qed.

Lemma parallel_assignment_satisf_2:
  forall rs ls res mres' oty e e' v v',
  let res' := map R mres' in
  remove_equations_res res oty res' e = Some e' ->
  satisf rs ls e' ->
  reg_unconstrained res e' = true ->
  forallb (fun l => loc_unconstrained l e') res' = true ->
  Val.lessdef v v' ->
  satisf (rs#res <- v) (Locmap.setlist res' (encode_long oty v') ls) e.
Proof.
  intros; red; intros.
  assert (ISREG: forall l, In l res' -> exists mr, l = R mr).
  { unfold res'; intros. exploit list_in_map_inv; eauto. intros [mr [A B]]. exists mr; auto. }
  functional inversion H.
- (* Two 32-bit halves *)
  subst. 
  set (e' := remove_equation {| ekind := Low; ereg := res; eloc := l2 |}
          (remove_equation {| ekind := High; ereg := res; eloc := l1 |} e)) in *.
  rewrite <- H5 in H2. simpl in H2. InvBooleans. simpl.
  destruct (OrderedEquation.eq_dec q (Eq Low res l2)).
  subst q; simpl. rewrite Regmap.gss.
  destruct (ISREG l2) as [r2 EQ]. rewrite <- H5; auto with coqlib. rewrite EQ. rewrite Locmap.gss_reg.
  apply Val.loword_lessdef; auto. 
  destruct (OrderedEquation.eq_dec q (Eq High res l1)).
  subst q; simpl. rewrite Regmap.gss. rewrite Locmap.gso by auto.
  destruct (ISREG l1) as [r1 EQ]. rewrite <- H5; auto with coqlib. rewrite EQ. rewrite Locmap.gss_reg.
  apply Val.hiword_lessdef; auto.
  assert (EqSet.In q e'). unfold e', remove_equation; simpl; ESD.fsetdec. 
  rewrite Regmap.gso. rewrite ! Locmap.gso. auto. 
  eapply loc_unconstrained_sound; eauto.
  eapply loc_unconstrained_sound; eauto.
  eapply reg_unconstrained_sound; eauto.
- (* One location *)
  subst. rewrite <- H5 in H2. simpl in H2. InvBooleans.
  replace (encode_long oty v') with (v' :: nil).
  set (e' := remove_equation {| ekind := Full; ereg := res; eloc := l1 |} e) in *.
  destruct (OrderedEquation.eq_dec q (Eq Full res l1)). 
  subst q; simpl. rewrite Regmap.gss.
  destruct (ISREG l1) as [r1 EQ]. rewrite <- H5; auto with coqlib. rewrite EQ. rewrite Locmap.gss_reg.
  auto.
  assert (EqSet.In q e'). unfold e', remove_equation; simpl. ESD.fsetdec. 
  simpl. rewrite Regmap.gso. rewrite Locmap.gso. auto.
  eapply loc_unconstrained_sound; eauto.
  eapply reg_unconstrained_sound; eauto.
  destruct oty as [[]|]; reflexivity || contradiction.
Qed.

Lemma in_subst_reg:
  forall r1 r2 q (e: eqs),
  EqSet.In q e ->
  ereg q = r1 /\ EqSet.In (Eq (ekind q) r2 (eloc q)) (subst_reg r1 r2 e)
  \/ ereg q <> r1 /\ EqSet.In q (subst_reg r1 r2 e).
Proof.
  intros r1 r2 q e0 IN0. unfold subst_reg.
  set (f := fun (q: EqSet.elt) e => add_equation (Eq (ekind q) r2 (eloc q)) (remove_equation q e)).
  set (elt := EqSet.elements_between (select_reg_l r1) (select_reg_h r1) e0).
  assert (IN_ELT: forall q, EqSet.In q elt <-> EqSet.In q e0 /\ ereg q = r1).
  {
    intros. unfold elt. rewrite EqSet.elements_between_iff.
    rewrite select_reg_charact. tauto. 
    exact (select_reg_l_monotone r1).
    exact (select_reg_h_monotone r1).
  }
  set (P := fun e1 e2 =>
         EqSet.In q e1 ->
         EqSet.In (Eq (ekind q) r2 (eloc q)) e2).
  assert (P elt (EqSet.fold f elt e0)).
  {
    apply ESP.fold_rec; unfold P; intros.
    - ESD.fsetdec.
    - simpl. red in H1. apply H1 in H3. destruct H3. 
      + subst x. ESD.fsetdec. 
      + rewrite ESF.add_iff. rewrite ESF.remove_iff. 
        destruct (OrderedEquation.eq_dec x {| ekind := ekind q; ereg := r2; eloc := eloc q |}); auto.
        left. subst x; auto. 
  }
  set (Q := fun e1 e2 =>
         ~EqSet.In q e1 ->
         EqSet.In q e2).
  assert (Q elt (EqSet.fold f elt e0)).
  {
    apply ESP.fold_rec; unfold Q; intros.
    - auto.
    - simpl. red in H2. rewrite H2 in H4.
      rewrite ESF.add_iff. rewrite ESF.remove_iff.
      right. split. apply H3. tauto. tauto. 
  }
  destruct (ESP.In_dec q elt).
  left. split. apply IN_ELT. auto. apply H. auto.
  right. split. red; intros. elim n. rewrite IN_ELT. auto. apply H0. auto. 
Qed.

Lemma subst_reg_satisf:
  forall src dst rs ls e,
  satisf rs ls (subst_reg dst src e) ->
  satisf (rs#dst <- (rs#src)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg dst src q e H0) as [[A B] | [A B]].
  subst dst. rewrite Regmap.gss. exploit H; eauto.
  rewrite Regmap.gso; auto.
Qed.

Lemma in_subst_reg_kind:
  forall r1 k1 r2 k2 q (e: eqs),
  EqSet.In q e ->
  (ereg q, ekind q) = (r1, k1) /\ EqSet.In (Eq k2 r2 (eloc q)) (subst_reg_kind r1 k1 r2 k2 e)
  \/ EqSet.In q (subst_reg_kind r1 k1 r2 k2 e).
Proof.
  intros r1 k1 r2 k2 q e0 IN0. unfold subst_reg.
  set (f := fun (q: EqSet.elt) e =>
      if IndexedEqKind.eq (ekind q) k1
      then add_equation (Eq k2 r2 (eloc q)) (remove_equation q e)
      else e).
  set (elt := EqSet.elements_between (select_reg_l r1) (select_reg_h r1) e0).
  assert (IN_ELT: forall q, EqSet.In q elt <-> EqSet.In q e0 /\ ereg q = r1).
  {
    intros. unfold elt. rewrite EqSet.elements_between_iff.
    rewrite select_reg_charact. tauto. 
    exact (select_reg_l_monotone r1).
    exact (select_reg_h_monotone r1).
  }
  set (P := fun e1 e2 =>
         EqSet.In q e1 -> ekind q = k1 ->
         EqSet.In (Eq k2 r2 (eloc q)) e2).
  assert (P elt (EqSet.fold f elt e0)).
  {
    intros; apply ESP.fold_rec; unfold P; intros.
    - ESD.fsetdec.
    - simpl. red in H1. apply H1 in H3. destruct H3. 
      + subst x. unfold f. destruct (IndexedEqKind.eq (ekind q) k1).
        simpl. ESD.fsetdec. contradiction.
      + unfold f. destruct (IndexedEqKind.eq (ekind x) k1).
        simpl. rewrite ESF.add_iff. rewrite ESF.remove_iff. 
        destruct (OrderedEquation.eq_dec x {| ekind := k2; ereg := r2; eloc := eloc q |}); auto.
        left. subst x; auto.
        auto. 
  }
  set (Q := fun e1 e2 =>
         ~EqSet.In q e1 \/ ekind q <> k1 ->
         EqSet.In q e2).
  assert (Q elt (EqSet.fold f elt e0)).
  {
    apply ESP.fold_rec; unfold Q; intros.
    - auto.
    - unfold f. red in H2. rewrite H2 in H4.
      destruct (IndexedEqKind.eq (ekind x) k1).
      simpl. rewrite ESF.add_iff. rewrite ESF.remove_iff.
      right. split. apply H3. tauto. intuition congruence. 
      apply H3. intuition. 
  }
  destruct (ESP.In_dec q elt).
  destruct (IndexedEqKind.eq (ekind q) k1).
  left. split. f_equal. apply IN_ELT. auto. auto. apply H. auto. auto.
  right. apply H0. auto.
  right. apply H0. auto.
Qed.

Lemma subst_reg_kind_satisf_makelong:
  forall src1 src2 dst rs ls e,
  let e1 := subst_reg_kind dst High src1 Full e in
  let e2 := subst_reg_kind dst Low src2 Full e1 in
  reg_unconstrained dst e2 = true ->
  satisf rs ls e2 ->
  satisf (rs#dst <- (Val.longofwords rs#src1 rs#src2)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg_kind dst High src1 Full q e H1) as [[A B] | B]; fold e1 in B.
  destruct (in_subst_reg_kind dst Low src2 Full _ e1 B) as [[C D] | D]; fold e2 in D.
  simpl in C; simpl in D. inv C.
  inversion A. rewrite H3; rewrite H4. rewrite Regmap.gss.
  apply Val.lessdef_trans with (rs#src1). 
  simpl. destruct (rs#src1); simpl; auto. destruct (rs#src2); simpl; auto. 
  rewrite Int64.hi_ofwords. auto.
  exploit H0. eexact D. simpl. auto. 
  destruct (in_subst_reg_kind dst Low src2 Full q e1 B) as [[C D] | D]; fold e2 in D.
  inversion C. rewrite H3; rewrite H4. rewrite Regmap.gss. 
  apply Val.lessdef_trans with (rs#src2). 
  simpl. destruct (rs#src1); simpl; auto. destruct (rs#src2); simpl; auto. 
  rewrite Int64.lo_ofwords. auto.
  exploit H0. eexact D. simpl. auto.
  rewrite Regmap.gso. apply H0; auto. eapply reg_unconstrained_sound; eauto. 
Qed.

Lemma subst_reg_kind_satisf_lowlong:
  forall src dst rs ls e,
  let e1 := subst_reg_kind dst Full src Low e in
  reg_unconstrained dst e1 = true ->
  satisf rs ls e1 ->
  satisf (rs#dst <- (Val.loword rs#src)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg_kind dst Full src Low q e H1) as [[A B] | B]; fold e1 in B.
  inversion A. rewrite H3; rewrite H4. simpl. rewrite Regmap.gss. 
  exploit H0. eexact B. simpl. auto. 
  rewrite Regmap.gso. apply H0; auto. eapply reg_unconstrained_sound; eauto.
Qed.

Lemma subst_reg_kind_satisf_highlong:
  forall src dst rs ls e,
  let e1 := subst_reg_kind dst Full src High e in
  reg_unconstrained dst e1 = true ->
  satisf rs ls e1 ->
  satisf (rs#dst <- (Val.hiword rs#src)) ls e.
Proof.
  intros; red; intros.
  destruct (in_subst_reg_kind dst Full src High q e H1) as [[A B] | B]; fold e1 in B.
  inversion A. rewrite H3; rewrite H4. simpl. rewrite Regmap.gss. 
  exploit H0. eexact B. simpl. auto. 
  rewrite Regmap.gso. apply H0; auto. eapply reg_unconstrained_sound; eauto.
Qed.

Module ESF2 := FSetFacts.Facts(EqSet2).
Module ESP2 := FSetProperties.Properties(EqSet2).
Module ESD2 := FSetDecide.Decide(EqSet2).

Lemma in_subst_loc:
  forall l1 l2 q (e e': eqs),
  EqSet.In q e ->
  subst_loc l1 l2 e = Some e' ->
  (eloc q = l1 /\ EqSet.In (Eq (ekind q) (ereg q) l2) e') \/ (Loc.diff l1 (eloc q) /\ EqSet.In q e').
Proof.
  intros l1 l2 q e0 e0'.
  unfold subst_loc. 
  set (f := fun (q0 : EqSet2.elt) (opte : option eqs) =>
   match opte with
   | Some e =>
       if Loc.eq l1 (eloc q0)
       then
        Some
          (add_equation {| ekind := ekind q0; ereg := ereg q0; eloc := l2 |}
             (remove_equation q0 e))
       else None
   | None => None
   end).
  set (elt := EqSet2.elements_between (select_loc_l l1) (select_loc_h l1) (eqs2 e0)).
  intros IN SUBST.
  set (P := fun e1 (opte: option eqs) =>
          match opte with
          | None => True
          | Some e2 =>
              EqSet2.In q e1 ->
              eloc q = l1 /\ EqSet.In (Eq (ekind q) (ereg q) l2) e2
          end).
  assert (P elt (EqSet2.fold f elt (Some e0))).
  {
    apply ESP2.fold_rec; unfold P; intros.
    - ESD2.fsetdec. 
    - destruct a as [e2|]; simpl; auto. 
      destruct (Loc.eq l1 (eloc x)); auto.
      unfold add_equation, remove_equation; simpl.
      red in H1. rewrite H1. intros [A|A]. 
      + subst x. split. auto. ESD.fsetdec.
      + exploit H2; eauto. intros [B C]. split. auto.
        rewrite ESF.add_iff. rewrite ESF.remove_iff. 
        destruct (OrderedEquation.eq_dec x {| ekind := ekind q; ereg := ereg q; eloc := l2 |}).
        left. rewrite e1; auto. 
        right; auto. 
  }
  set (Q := fun e1 (opte: option eqs) =>
          match opte with
          | None => True
          | Some e2 => ~EqSet2.In q e1 -> EqSet.In q e2
          end).
  assert (Q elt (EqSet2.fold f elt (Some e0))).
  {
    apply ESP2.fold_rec; unfold Q; intros.
    - auto. 
    - destruct a as [e2|]; simpl; auto. 
      destruct (Loc.eq l1 (eloc x)); auto. 
      red in H2. rewrite H2; intros. 
      unfold add_equation, remove_equation; simpl.
      rewrite ESF.add_iff. rewrite ESF.remove_iff.
      right; split. apply H3. tauto. tauto.
  }
  rewrite SUBST in H; rewrite SUBST in H0; simpl in *. 
  destruct (ESP2.In_dec q elt). 
  left. apply H; auto.
  right. split; auto. 
  rewrite <- select_loc_charact.
  destruct (select_loc_l l1 q) eqn: LL; auto.
  destruct (select_loc_h l1 q) eqn: LH; auto.
  elim n. eapply EqSet2.elements_between_iff. 
  exact (select_loc_l_monotone l1).
  exact (select_loc_h_monotone l1).
  split. apply eqs_same; auto. auto. 
Qed.

Lemma loc_type_compat_charact:
  forall env l e q,
  loc_type_compat env l e = true ->
  EqSet.In q e ->
  subtype (sel_type (ekind q) (env (ereg q))) (Loc.type l) = true \/ Loc.diff l (eloc q).
Proof.
  unfold loc_type_compat; intros. 
  rewrite EqSet2.for_all_between_iff in H.
  destruct (select_loc_l l q) eqn: LL.
  destruct (select_loc_h l q) eqn: LH.
  left; apply H; auto. apply eqs_same; auto. 
  right. apply select_loc_charact. auto. 
  right. apply select_loc_charact. auto.
  intros; subst; auto.
  exact (select_loc_l_monotone l).
  exact (select_loc_h_monotone l).
Qed.

Lemma well_typed_move_charact:
  forall env l e k r rs,
  well_typed_move env l e = true ->
  EqSet.In (Eq k r l) e ->
  wt_regset env rs ->
  match l with
  | R mr => True
  | S sl ofs ty => Val.has_type (sel_val k rs#r) ty
  end.
Proof.
  unfold well_typed_move; intros. 
  destruct l as [mr | sl ofs ty]. 
  auto.
  exploit loc_type_compat_charact; eauto. intros [A | A].
  simpl in A. eapply Val.has_subtype; eauto. 
  generalize (H1 r). destruct k; simpl; intros.
  auto.
  destruct (rs#r); exact I.
  destruct (rs#r); exact I.
  eelim Loc.diff_not_eq. eexact A. auto.
Qed.

Remark val_lessdef_normalize:
  forall v v' ty,
  Val.has_type v ty -> Val.lessdef v v' ->
  Val.lessdef v (Val.load_result (chunk_of_type ty) v').
Proof.
  intros. inv H0. rewrite Val.load_result_same; auto. auto. 
Qed.

Lemma subst_loc_satisf:
  forall env src dst rs ls e e',
  subst_loc dst src e = Some e' ->
  well_typed_move env dst e = true ->
  wt_regset env rs ->
  satisf rs ls e' ->
  satisf rs (Locmap.set dst (ls src) ls) e.
Proof.
  intros; red; intros.
  exploit in_subst_loc; eauto. intros [[A B] | [A B]].
  subst dst. rewrite Locmap.gss.
  destruct q as [k r l]; simpl in *.
  exploit well_typed_move_charact; eauto.
  destruct l as [mr | sl ofs ty]; intros.
  apply (H2 _ B). 
  apply val_lessdef_normalize; auto. apply (H2 _ B). 
  rewrite Locmap.gso; auto.
Qed.

Lemma can_undef_sound:
  forall e ml q,
  can_undef ml e = true -> EqSet.In q e -> Loc.notin (eloc q) (map R ml).
Proof.
  induction ml; simpl; intros.
  tauto.
  InvBooleans. split.
  apply Loc.diff_sym. eapply loc_unconstrained_sound; eauto. 
  eauto.
Qed.

Lemma undef_regs_outside:
  forall ml ls l,
  Loc.notin l (map R ml) -> undef_regs ml ls l = ls l.
Proof.
  induction ml; simpl; intros. auto.
  rewrite Locmap.gso. apply IHml. tauto. apply Loc.diff_sym. tauto. 
Qed.

Lemma can_undef_satisf:
  forall ml e rs ls,
  can_undef ml e = true ->
  satisf rs ls e ->
  satisf rs (undef_regs ml ls) e.
Proof.
  intros; red; intros. rewrite undef_regs_outside. eauto.
  eapply can_undef_sound; eauto.
Qed.

Lemma can_undef_except_sound:
  forall lx e ml q,
  can_undef_except lx ml e = true -> EqSet.In q e -> Loc.diff (eloc q) lx -> Loc.notin (eloc q) (map R ml).
Proof.
  induction ml; simpl; intros.
  tauto.
  InvBooleans. split.
  destruct (orb_true_elim _ _ H2). 
  apply proj_sumbool_true in e0. congruence.
  apply Loc.diff_sym. eapply loc_unconstrained_sound; eauto. 
  eapply IHml; eauto.
Qed.

Lemma subst_loc_undef_satisf:
  forall env src dst rs ls ml e e',
  subst_loc dst src e = Some e' ->
  well_typed_move env dst e = true ->
  can_undef_except dst ml e = true ->
  wt_regset env rs ->
  satisf rs ls e' ->
  satisf rs (Locmap.set dst (ls src) (undef_regs ml ls)) e.
Proof.
  intros; red; intros.
  exploit in_subst_loc; eauto. intros [[A B] | [A B]].
  subst dst. rewrite Locmap.gss.
  destruct q as [k r l]; simpl in *.
  exploit well_typed_move_charact; eauto.
  destruct l as [mr | sl ofs ty]; intros.
  apply (H3 _ B). 
  apply val_lessdef_normalize; auto. apply (H3 _ B). 
  rewrite Locmap.gso; auto. rewrite undef_regs_outside. eauto. 
  eapply can_undef_except_sound; eauto. apply Loc.diff_sym; auto.
Qed.

Lemma transfer_use_def_satisf:
  forall args res args' res' und e e' rs ls,
  transfer_use_def args res args' res' und e = Some e' ->
  satisf rs ls e' ->
  Val.lessdef_list rs##args (reglist ls args') /\
  (forall v v', Val.lessdef v v' ->
    satisf (rs#res <- v) (Locmap.set (R res') v' (undef_regs und ls)) e).
Proof.
  unfold transfer_use_def; intros. MonadInv. 
  split. eapply add_equations_lessdef; eauto.
  intros. eapply parallel_assignment_satisf; eauto. assumption. 
  eapply can_undef_satisf; eauto. 
  eapply add_equations_satisf; eauto. 
Qed.

Lemma add_equations_res_lessdef:
  forall r oty ll e e' rs ls,
  add_equations_res r oty ll e = Some e' ->
  satisf rs ls e' ->
  Val.lessdef_list (encode_long oty rs#r) (map ls ll).
Proof.
  intros. functional inversion H.
- subst. simpl. constructor. 
  eapply add_equation_lessdef with (q := Eq High r l1).
  eapply add_equation_satisf. eauto. 
  constructor.
  eapply add_equation_lessdef with (q := Eq Low r l2). eauto.
  constructor.
- subst. replace (encode_long oty rs#r) with (rs#r :: nil). simpl. constructor; auto.
  eapply add_equation_lessdef with (q := Eq Full r l1); eauto.
  destruct oty as [[]|]; reflexivity || contradiction.
Qed.

Definition callee_save_loc (l: loc) :=
  match l with
  | R r => ~(In r destroyed_at_call)
  | S sl ofs ty => sl <> Outgoing
  end.

Definition agree_callee_save (ls1 ls2: locset) : Prop :=
  forall l, callee_save_loc l -> ls1 l = ls2 l.

Lemma return_regs_agree_callee_save:
  forall caller callee,
  agree_callee_save caller (return_regs caller callee).
Proof.
  intros; red; intros. unfold return_regs. red in H. 
  destruct l.
  rewrite pred_dec_false; auto. 
  destruct sl; auto || congruence. 
Qed.

Lemma no_caller_saves_sound:
  forall e q,
  no_caller_saves e = true ->
  EqSet.In q e ->
  callee_save_loc (eloc q).
Proof.
  unfold no_caller_saves, callee_save_loc; intros.
  exploit EqSet.for_all_2; eauto.
  hnf. intros. simpl in H1. rewrite H1. auto.
  lazy beta. destruct (eloc q). 
  intros; red; intros. destruct (orb_true_elim _ _ H1); InvBooleans.
  eapply int_callee_save_not_destroyed; eauto.
  apply index_int_callee_save_pos2. omega.
  eapply float_callee_save_not_destroyed; eauto.
  apply index_float_callee_save_pos2. omega.
  destruct sl; congruence.
Qed.

Lemma function_return_satisf:
  forall rs ls_before ls_after res res' sg e e' v,
  res' = map R (loc_result sg) ->
  remove_equations_res res (sig_res sg) res' e = Some e' ->
  satisf rs ls_before e' ->
  forallb (fun l => reg_loc_unconstrained res l e') res' = true ->
  no_caller_saves e' = true ->
  Val.lessdef_list (encode_long (sig_res sg) v) (map ls_after res') ->
  agree_callee_save ls_before ls_after ->
  satisf (rs#res <- v) ls_after e.
Proof.
  intros; red; intros.
  functional inversion H0.
- subst. rewrite <- H11 in *. unfold encode_long in H4. rewrite <- H7 in H4. 
  simpl in H4. inv H4. inv H14. 
  set (e' := remove_equation {| ekind := Low; ereg := res; eloc := l2 |}
          (remove_equation {| ekind := High; ereg := res; eloc := l1 |} e)) in *.
  simpl in H2. InvBooleans.
  destruct (OrderedEquation.eq_dec q (Eq Low res l2)).
  subst q; simpl. rewrite Regmap.gss. auto.
  destruct (OrderedEquation.eq_dec q (Eq High res l1)).
  subst q; simpl. rewrite Regmap.gss. auto.
  assert (EqSet.In q e'). unfold e', remove_equation; simpl; ESD.fsetdec. 
  exploit reg_loc_unconstrained_sound. eexact H. eauto. intros [A B].
  exploit reg_loc_unconstrained_sound. eexact H2. eauto. intros [C D].
  rewrite Regmap.gso; auto.
  exploit no_caller_saves_sound; eauto. intros.
  red in H5. rewrite <- H5; auto. 
- subst. rewrite <- H11 in *.
  replace (encode_long (sig_res sg) v) with (v :: nil) in H4.
  simpl in H4. inv H4.
  simpl in H2. InvBooleans.
  set (e' := remove_equation {| ekind := Full; ereg := res; eloc := l1 |} e) in *.
  destruct (OrderedEquation.eq_dec q (Eq Full res l1)). 
  subst q; simpl. rewrite Regmap.gss; auto. 
  assert (EqSet.In q e'). unfold e', remove_equation; simpl. ESD.fsetdec. 
  exploit reg_loc_unconstrained_sound; eauto. intros [A B].
  rewrite Regmap.gso; auto.
  exploit no_caller_saves_sound; eauto. intros.
  red in H5. rewrite <- H5; auto.
  destruct (sig_res sg) as [[]|]; reflexivity || contradiction.
Qed.

Lemma compat_left_sound:
  forall r l e q,
  compat_left r l e = true -> EqSet.In q e -> ereg q = r -> ekind q = Full /\ eloc q = l.
Proof.
  unfold compat_left; intros.
  rewrite EqSet.for_all_between_iff in H. 
  apply select_reg_charact in H1. destruct H1. 
  exploit H; eauto. intros. 
  destruct (ekind q); try discriminate. 
  destruct (Loc.eq l (eloc q)); try discriminate. 
  auto.
  intros. subst x2. auto.
  exact (select_reg_l_monotone r).
  exact (select_reg_h_monotone r).
Qed.

Lemma compat_left2_sound:
  forall r l1 l2 e q,
  compat_left2 r l1 l2 e = true -> EqSet.In q e -> ereg q = r ->
  (ekind q = High /\ eloc q = l1) \/ (ekind q = Low /\ eloc q = l2).
Proof.
  unfold compat_left2; intros.
  rewrite EqSet.for_all_between_iff in H. 
  apply select_reg_charact in H1. destruct H1. 
  exploit H; eauto. intros. 
  destruct (ekind q); try discriminate. 
  InvBooleans. auto.
  InvBooleans. auto.
  intros. subst x2. auto.
  exact (select_reg_l_monotone r).
  exact (select_reg_h_monotone r).
Qed.

Lemma val_hiword_longofwords:
  forall v1 v2, Val.lessdef (Val.hiword (Val.longofwords v1 v2)) v1.
Proof.
  intros. destruct v1; simpl; auto. destruct v2; auto. unfold Val.hiword.
  rewrite Int64.hi_ofwords. auto.
Qed.

Lemma val_loword_longofwords:
  forall v1 v2, Val.lessdef (Val.loword (Val.longofwords v1 v2)) v2.
Proof.
  intros. destruct v1; simpl; auto. destruct v2; auto. unfold Val.loword.
  rewrite Int64.lo_ofwords. auto.
Qed.

Lemma compat_entry_satisf:
  forall rl tyl ll e,
  compat_entry rl tyl ll e = true ->
  forall vl ls,
  Val.lessdef_list vl (decode_longs tyl (map ls ll)) ->
  satisf (init_regs vl rl) ls e.
Proof.
  intros until e. functional induction (compat_entry rl tyl ll e); intros. 
- (* no params *)
  simpl. red; intros. rewrite Regmap.gi. destruct (ekind q); simpl; auto.
- (* a param of type Tlong *)
  InvBooleans. simpl in H0. inv H0. simpl.
  red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r1). 
  exploit compat_left2_sound; eauto.
  intros [[A B] | [A B]]; rewrite A; rewrite B; simpl.
  apply Val.lessdef_trans with (Val.hiword (Val.longofwords (ls l1) (ls l2))).
  apply Val.hiword_lessdef; auto. apply val_hiword_longofwords.
  apply Val.lessdef_trans with (Val.loword (Val.longofwords (ls l1) (ls l2))).
  apply Val.loword_lessdef; auto. apply val_loword_longofwords.
  eapply IHb; eauto.
- (* a param of type Tint *)
  InvBooleans. simpl in H0. inv H0. simpl.
  red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r1). 
  exploit compat_left_sound; eauto. intros [A B]. rewrite A; rewrite B; auto.
  eapply IHb; eauto.
- (* a param of type Tfloat *)
  InvBooleans. simpl in H0. inv H0. simpl.
  red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r1). 
  exploit compat_left_sound; eauto. intros [A B]. rewrite A; rewrite B; auto.
  eapply IHb; eauto.
- (* a param of type Tsingle *)
  InvBooleans. simpl in H0. inv H0. simpl.
  red; intros. rewrite Regmap.gsspec. destruct (peq (ereg q) r1). 
  exploit compat_left_sound; eauto. intros [A B]. rewrite A; rewrite B; auto.
  eapply IHb; eauto.
- (* error case *)
  discriminate.
Qed.

Lemma call_regs_param_values:
  forall sg ls,
  map (call_regs ls) (loc_parameters sg) = map ls (loc_arguments sg).
Proof.
  intros. unfold loc_parameters. rewrite list_map_compose. 
  apply list_map_exten; intros. unfold call_regs, parameter_of_argument.
  exploit loc_arguments_acceptable; eauto. unfold loc_argument_acceptable. 
  destruct x; auto. destruct sl; tauto. 
Qed.

Lemma return_regs_arg_values:
  forall sg ls1 ls2,
  tailcall_is_possible sg = true ->
  map (return_regs ls1 ls2) (loc_arguments sg) = map ls2 (loc_arguments sg).
Proof.
  intros. apply list_map_exten; intros. 
  exploit loc_arguments_acceptable; eauto.
  exploit tailcall_is_possible_correct; eauto. 
  unfold loc_argument_acceptable, return_regs.
  destruct x; intros.
  rewrite pred_dec_true; auto. 
  contradiction.
Qed.

Lemma find_function_tailcall:
  forall tge ros ls1 ls2,
  ros_compatible_tailcall ros = true ->
  find_function tge ros (return_regs ls1 ls2) = find_function tge ros ls2.
Proof.
  unfold ros_compatible_tailcall, find_function; intros. 
  destruct ros as [r|id]; auto.
  unfold return_regs. destruct (in_dec mreg_eq r destroyed_at_call); simpl in H.
  auto. congruence.
Qed.

(** * Properties of the dataflow analysis *)

Lemma analyze_successors:
  forall f env bsh an pc bs s e,
  analyze f env bsh = Some an ->
  bsh!pc = Some bs ->
  In s (successors_block_shape bs) ->
  an!!pc = OK e ->
  exists e', transfer f env bsh s an!!s = OK e' /\ EqSet.Subset e' e.
Proof.
  unfold analyze; intros. exploit DS.fixpoint_solution; eauto.
  instantiate (1 := pc). instantiate (1 := s). 
  unfold successors_list. rewrite PTree.gmap1. rewrite H0. simpl. auto. 
  rewrite H2. unfold DS.L.ge. destruct (transfer f env bsh s an#s); intros.
  exists e0; auto. 
  contradiction.
Qed.

Lemma satisf_successors:
  forall f env bsh an pc bs s e rs ls,
  analyze f env bsh = Some an ->
  bsh!pc = Some bs ->
  In s (successors_block_shape bs) ->
  an!!pc = OK e ->
  satisf rs ls e ->
  exists e', transfer f env bsh s an!!s = OK e' /\ satisf rs ls e'.
Proof.
  intros. exploit analyze_successors; eauto. intros [e' [A B]]. 
  exists e'; split; auto. eapply satisf_incr; eauto.
Qed.

(** Inversion on [transf_function] *)

Inductive transf_function_spec (f: RTL.function) (tf: LTL.function) : Prop :=
  | transf_function_spec_intro:  
      forall env an mv k e1 e2,
      wt_function f env ->
      analyze f env (pair_codes f tf) = Some an ->
      (LTL.fn_code tf)!(LTL.fn_entrypoint tf) = Some(expand_moves mv (Lbranch (RTL.fn_entrypoint f) :: k)) ->
      wf_moves mv ->
      transfer f env (pair_codes f tf) (RTL.fn_entrypoint f) an!!(RTL.fn_entrypoint f) = OK e1 ->
      track_moves env mv e1 = Some e2 ->
      compat_entry (RTL.fn_params f) (sig_args (RTL.fn_sig f)) (loc_parameters (fn_sig tf)) e2 = true ->
      can_undef destroyed_at_function_entry e2 = true ->
      RTL.fn_stacksize f = LTL.fn_stacksize tf ->
      RTL.fn_sig f = LTL.fn_sig tf ->
      transf_function_spec f tf.

Lemma transf_function_inv:
  forall f tf,
  transf_function f = OK tf ->
  transf_function_spec f tf.
Proof.
  unfold transf_function; intros.
  destruct (type_function f) as [env|] eqn:TY; try discriminate.
  destruct (regalloc f); try discriminate.
  destruct (check_function f f0 env) as [] eqn:?; inv H.
  unfold check_function in Heqr. 
  destruct (analyze f env (pair_codes f tf)) as [an|] eqn:?; try discriminate.
  monadInv Heqr. 
  destruct (check_entrypoints_aux f tf env x) as [y|] eqn:?; try discriminate.
  unfold check_entrypoints_aux, pair_entrypoints in Heqo0. MonadInv.
  exploit extract_moves_sound; eauto. intros [A B]. subst b.
  exploit check_succ_sound; eauto. intros [k EQ1]. subst b0.
  econstructor; eauto. eapply type_function_correct; eauto. congruence. 
Qed.

Lemma invert_code:
  forall f env tf pc i opte e,
  wt_function f env ->
  (RTL.fn_code f)!pc = Some i ->
  transfer f env (pair_codes f tf) pc opte = OK e ->
  exists eafter, exists bsh, exists bb,
  opte = OK eafter /\ 
  (pair_codes f tf)!pc = Some bsh /\
  (LTL.fn_code tf)!pc = Some bb /\
  expand_block_shape bsh i bb /\
  transfer_aux f env bsh eafter = Some e /\
  wt_instr f env i.
Proof.
  intros. destruct opte as [eafter|]; simpl in H1; try discriminate. exists eafter.
  destruct (pair_codes f tf)!pc as [bsh|] eqn:?; try discriminate. exists bsh. 
  exploit matching_instr_block; eauto. intros [bb [A B]].
  destruct (transfer_aux f env bsh eafter) as [e1|] eqn:?; inv H1. 
  exists bb. exploit wt_instr_at; eauto.
  tauto. 
Qed.

(** * Semantic preservation *)

Section PRESERVATION.

Variable prog: RTL.program.
Variable tprog: LTL.program.
Hypothesis TRANSF: transf_program prog = OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intro. unfold ge, tge.
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact TRANSF.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intro. unfold ge, tge.
  apply Genv.find_var_info_transf_partial with transf_fundef.
  exact TRANSF.
Qed.

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial transf_fundef _ TRANSF).

Lemma function_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial transf_fundef _ TRANSF).

Lemma sig_function_translated:
  forall f tf,
  transf_fundef f = OK tf ->
  LTL.funsig tf = RTL.funsig f.
Proof.
  intros; destruct f; monadInv H.
  destruct (transf_function_inv _ _ EQ). simpl; auto.
  auto.
Qed.

Lemma find_function_translated:
  forall ros rs fd ros' e e' ls,
  RTL.find_function ge ros rs = Some fd ->
  add_equation_ros ros ros' e = Some e' ->
  satisf rs ls e' ->
  exists tfd,
  LTL.find_function tge ros' ls = Some tfd /\ transf_fundef fd = OK tfd.
Proof.
  unfold RTL.find_function, LTL.find_function; intros.
  destruct ros as [r|id]; destruct ros' as [r'|id']; simpl in H0; MonadInv.
  (* two regs *)
  exploit add_equation_lessdef; eauto. intros LD. inv LD.
  eapply functions_translated; eauto.
  rewrite <- H2 in H. simpl in H. congruence.
  (* two symbols *)
  rewrite symbols_preserved. rewrite Heqo. 
  eapply function_ptr_translated; eauto.
Qed.

Lemma exec_moves:
  forall mv env rs s f sp bb m e e' ls,
  track_moves env mv e = Some e' ->
  wf_moves mv ->
  satisf rs ls e' ->
  wt_regset env rs ->
  exists ls',
    star step tge (Block s f sp (expand_moves mv bb) ls m)
               E0 (Block s f sp bb ls' m)
  /\ satisf rs ls' e.
Proof.
Opaque destroyed_by_op.
  induction mv; simpl; intros.
  (* base *)
- unfold expand_moves; simpl. inv H. exists ls; split. apply star_refl. auto.
  (* step *)
- destruct a as [src dst]. unfold expand_moves. simpl. 
  destruct (track_moves env mv e) as [e1|] eqn:?; MonadInv.
  assert (wf_moves mv). red; intros. apply H0; auto with coqlib. 
  destruct src as [rsrc | ssrc]; destruct dst as [rdst | sdst].
  (* reg-reg *)
+ exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto. 
  intros [ls' [A B]]. exists ls'; split; auto. eapply star_left; eauto. 
  econstructor. simpl. eauto. auto. auto.
  (* reg->stack *)
+ exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto. 
  intros [ls' [A B]]. exists ls'; split; auto. eapply star_left; eauto. 
  econstructor. simpl. eauto. auto.
  (* stack->reg *)
+ simpl in Heqb. exploit IHmv; eauto. eapply subst_loc_undef_satisf; eauto. 
  intros [ls' [A B]]. exists ls'; split; auto. eapply star_left; eauto. 
  econstructor. auto. auto. 
  (* stack->stack *)
+ exploit H0; auto with coqlib. unfold wf_move. tauto.
Qed.

(** The simulation relation *)

Inductive match_stackframes: list RTL.stackframe -> list LTL.stackframe -> signature -> Prop :=
  | match_stackframes_nil: forall sg,
      sg.(sig_res) = Some Tint ->
      match_stackframes nil nil sg
  | match_stackframes_cons:
      forall res f sp pc rs s tf bb ls ts sg an e env
        (STACKS: match_stackframes s ts (fn_sig tf))
        (FUN: transf_function f = OK tf)
        (ANL: analyze f env (pair_codes f tf) = Some an)
        (EQ: transfer f env (pair_codes f tf) pc an!!pc = OK e)
        (WTF: wt_function f env)
        (WTRS: wt_regset env rs)
        (WTRES: subtype (proj_sig_res sg) (env res) = true)
        (STEPS: forall v ls1 m,
           Val.lessdef_list (encode_long (sig_res sg) v) (map ls1 (map R (loc_result sg))) ->
           Val.has_type v (env res) ->
           agree_callee_save ls ls1 ->
           exists ls2,
           star LTL.step tge (Block ts tf sp bb ls1 m)
                          E0 (State ts tf sp pc ls2 m)
           /\ satisf (rs#res <- v) ls2 e),
      match_stackframes
        (RTL.Stackframe res f sp pc rs :: s)
        (LTL.Stackframe tf sp ls bb :: ts)
        sg.

Inductive match_states: RTL.state -> LTL.state -> Prop :=
  | match_states_intro:
      forall s f sp pc rs m ts tf ls m' an e env
        (STACKS: match_stackframes s ts (fn_sig tf))
        (FUN: transf_function f = OK tf)
        (ANL: analyze f env (pair_codes f tf) = Some an)
        (EQ: transfer f env (pair_codes f tf) pc an!!pc = OK e)
        (SAT: satisf rs ls e)
        (MEM: Mem.extends m m')
        (WTF: wt_function f env)
        (WTRS: wt_regset env rs),
      match_states (RTL.State s f sp pc rs m)
                   (LTL.State ts tf sp pc ls m')
  | match_states_call:
      forall s f args m ts tf ls m'
        (STACKS: match_stackframes s ts (funsig tf))
        (FUN: transf_fundef f = OK tf)
        (ARGS: Val.lessdef_list args (decode_longs (sig_args (funsig tf)) (map ls (loc_arguments (funsig tf)))))
        (AG: agree_callee_save (parent_locset ts) ls)
        (MEM: Mem.extends m m')
        (WTARGS: Val.has_type_list args (sig_args (funsig tf))),
      match_states (RTL.Callstate s f args m)
                   (LTL.Callstate ts tf ls m')
  | match_states_return:
      forall s res m ts ls m' sg
        (STACKS: match_stackframes s ts sg)
        (RES: Val.lessdef_list (encode_long (sig_res sg) res) (map ls (map R (loc_result sg))))
        (AG: agree_callee_save (parent_locset ts) ls)
        (MEM: Mem.extends m m')
        (WTRES: Val.has_type res (proj_sig_res sg)),
      match_states (RTL.Returnstate s res m)
                   (LTL.Returnstate ts ls m').

Lemma match_stackframes_change_sig:
  forall s ts sg sg',
  match_stackframes s ts sg ->
  sg'.(sig_res) = sg.(sig_res) ->
  match_stackframes s ts sg'.
Proof.
  intros. inv H. 
  constructor. congruence.
  econstructor; eauto.
  unfold proj_sig_res in *. rewrite H0; auto. 
  intros. unfold loc_result in H; rewrite H0 in H; eauto. 
Qed.

Ltac UseShape :=
  match goal with
  | [ WT: wt_function _ _, CODE: (RTL.fn_code _)!_ = Some _, EQ: transfer _ _ _ _ _ = OK _ |- _ ] =>
      destruct (invert_code _ _ _ _ _ _ _ WT CODE EQ) as (eafter & bsh & bb & AFTER & BSH & TCODE & EBS & TR & WTI); 
      inv EBS; unfold transfer_aux in TR; MonadInv
  end.

Remark addressing_not_long:
  forall env f addr args dst s r,
  wt_instr f env (Iload Mint64 addr args dst s) ->
  In r args -> r <> dst.
Proof.
  intros. 
  assert (forall ty, In ty (type_of_addressing addr) -> ty = Tint).
  { intros. destruct addr; simpl in H1; intuition. }
  inv H.
  assert (env r = Tint).
  { generalize args (type_of_addressing addr) H0 H1 H5.
    induction args0; simpl; intros.
    contradiction.
    destruct l. discriminate. InvBooleans. 
    destruct H2. subst a. 
    assert (t = Tint) by auto with coqlib. subst t. 
    destruct (env r); auto || discriminate. 
    eauto with coqlib. 
  }
  red; intros; subst r. rewrite H in H8; discriminate.
Qed.

(** The proof of semantic preservation is a simulation argument of the
    "plus" kind. *)

Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', plus LTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inv MS; try UseShape.

(* nop *)
  exploit exec_moves; eauto. intros [ls1 [X Y]]. 
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_right. eexact X. econstructor; eauto. 
  eauto. traceEq.
  exploit satisf_successors; eauto. simpl; eauto. intros [enext [U V]]. 
  econstructor; eauto. 

(* op move *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  simpl in H0. inv H0.  
  exploit (exec_moves mv); eauto. intros [ls1 [X Y]]. 
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_right. eexact X. econstructor; eauto. 
  eauto. traceEq.
  exploit satisf_successors; eauto. simpl; eauto. eapply subst_reg_satisf; eauto. 
  intros [enext [U V]]. 
  econstructor; eauto.

(* op makelong *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  simpl in H0. inv H0. 
  exploit (exec_moves mv); eauto. intros [ls1 [X Y]]. 
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_right. eexact X. econstructor; eauto. 
  eauto. traceEq.
  exploit satisf_successors; eauto. simpl; eauto.
  eapply subst_reg_kind_satisf_makelong. eauto. eauto. 
  intros [enext [U V]]. 
  econstructor; eauto.

(* op lowlong *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  simpl in H0. inv H0. 
  exploit (exec_moves mv); eauto. intros [ls1 [X Y]]. 
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_right. eexact X. econstructor; eauto. 
  eauto. traceEq.
  exploit satisf_successors; eauto. simpl; eauto.
  eapply subst_reg_kind_satisf_lowlong. eauto. eauto. 
  intros [enext [U V]]. 
  econstructor; eauto.

(* op highlong *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  simpl in H0. inv H0. 
  exploit (exec_moves mv); eauto. intros [ls1 [X Y]]. 
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_right. eexact X. econstructor; eauto. 
  eauto. traceEq.
  exploit satisf_successors; eauto. simpl; eauto.
  eapply subst_reg_kind_satisf_highlong. eauto. eauto. 
  intros [enext [U V]]. 
  econstructor; eauto.

(* op regular *)
- generalize (wt_exec_Iop _ _ _ _ _ _ _ _ _ _ _ WTI H0 WTRS). intros WTRS'.
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 
  exploit transfer_use_def_satisf; eauto. intros [X Y].
  exploit eval_operation_lessdef; eauto. intros [v' [F G]]. 
  exploit (exec_moves mv2); eauto. intros [ls2 [A2 B2]].
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_trans. eexact A1. 
  eapply star_left. econstructor. instantiate (1 := v'). rewrite <- F. 
  apply eval_operation_preserved. exact symbols_preserved.
  eauto. eapply star_right. eexact A2. constructor. 
  eauto. eauto. eauto. traceEq.
  exploit satisf_successors; eauto. simpl; eauto. intros [enext [U V]]. 
  econstructor; eauto.

(* op dead *)
- exploit exec_moves; eauto. intros [ls1 [X Y]]. 
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_right. eexact X. econstructor; eauto. 
  eauto. traceEq.
  exploit satisf_successors. eauto. eauto. simpl; eauto. eauto. 
  eapply reg_unconstrained_satisf; eauto. 
  intros [enext [U V]]. 
  econstructor; eauto.
  eapply wt_exec_Iop; eauto. 

(* load regular *)
- generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 
  exploit transfer_use_def_satisf; eauto. intros [X Y].
  exploit eval_addressing_lessdef; eauto. intros [a' [F G]].
  exploit Mem.loadv_extends; eauto. intros [v' [P Q]]. 
  exploit (exec_moves mv2); eauto. intros [ls2 [A2 B2]].
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_trans. eexact A1. 
  eapply star_left. econstructor. instantiate (1 := a'). rewrite <- F. 
  apply eval_addressing_preserved. exact symbols_preserved. eauto. eauto.
  eapply star_right. eexact A2. constructor. 
  eauto. eauto. eauto. traceEq.
  exploit satisf_successors; eauto. simpl; eauto. intros [enext [U V]]. 
  econstructor; eauto.

(* load pair *)
- generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
  exploit Mem.loadv_int64_split; eauto. intros (v1 & v2 & LOAD1 & LOAD2 & V12).
  set (v2' := if big_endian then v2 else v1) in *.
  set (v1' := if big_endian then v1 else v2) in *.
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 
  assert (LD1: Val.lessdef_list rs##args (reglist ls1 args1')).
  { eapply add_equations_lessdef; eauto. }
  exploit eval_addressing_lessdef. eexact LD1. eauto. intros [a1' [F1 G1]].
  exploit Mem.loadv_extends. eauto. eexact LOAD1. eexact G1. intros (v1'' & LOAD1' & LD2).
  set (ls2 := Locmap.set (R dst1') v1'' (undef_regs (destroyed_by_load Mint32 addr) ls1)).
  assert (SAT2: satisf (rs#dst <- v) ls2 e2).
  { eapply loc_unconstrained_satisf. eapply can_undef_satisf; eauto. 
    eapply reg_unconstrained_satisf. eauto. 
    eapply add_equations_satisf; eauto. assumption.
    rewrite Regmap.gss. apply Val.lessdef_trans with v1'; auto. 
    subst v. unfold v1', kind_first_word.
    destruct big_endian; apply val_hiword_longofwords || apply val_loword_longofwords.
  }
  exploit (exec_moves mv2); eauto. intros [ls3 [A3 B3]]. 
  assert (LD3: Val.lessdef_list rs##args (reglist ls3 args2')).
  { replace (rs##args) with ((rs#dst<-v)##args). 
    eapply add_equations_lessdef; eauto. 
    apply list_map_exten; intros. rewrite Regmap.gso; auto. 
    eapply addressing_not_long; eauto. 
  }
  exploit eval_addressing_lessdef. eexact LD3.
  eapply eval_offset_addressing; eauto. intros [a2' [F2 G2]].
  exploit Mem.loadv_extends. eauto. eexact LOAD2. eexact G2. intros (v2'' & LOAD2' & LD4).
  set (ls4 := Locmap.set (R dst2') v2'' (undef_regs (destroyed_by_load Mint32 addr2) ls3)).
  assert (SAT4: satisf (rs#dst <- v) ls4 e0).
  { eapply loc_unconstrained_satisf. eapply can_undef_satisf; eauto. 
    eapply add_equations_satisf; eauto. assumption.
    apply Val.lessdef_trans with v2'; auto. 
    rewrite Regmap.gss. subst v. unfold v2', kind_second_word.
    destruct big_endian; apply val_hiword_longofwords || apply val_loword_longofwords.
  }
  exploit (exec_moves mv3); eauto. intros [ls5 [A5 B5]].
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_trans. eexact A1. 
  eapply star_left. econstructor. 
  instantiate (1 := a1'). rewrite <- F1. apply eval_addressing_preserved. exact symbols_preserved.
  eexact LOAD1'. instantiate (1 := ls2); auto. 
  eapply star_trans. eexact A3.
  eapply star_left. econstructor.
  instantiate (1 := a2'). rewrite <- F2. apply eval_addressing_preserved. exact symbols_preserved.
  eexact LOAD2'. instantiate (1 := ls4); auto.
  eapply star_right. eexact A5.
  constructor. 
  eauto. eauto. eauto. eauto. eauto. traceEq.
  exploit satisf_successors; eauto. simpl; eauto. intros [enext [W Z]]. 
  econstructor; eauto.

(* load first word of a pair *)
- generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
  exploit Mem.loadv_int64_split; eauto. intros (v1 & v2 & LOAD1 & LOAD2 & V12).
  set (v2' := if big_endian then v2 else v1) in *.
  set (v1' := if big_endian then v1 else v2) in *.
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 
  assert (LD1: Val.lessdef_list rs##args (reglist ls1 args')).
  { eapply add_equations_lessdef; eauto. }
  exploit eval_addressing_lessdef. eexact LD1. eauto. intros [a1' [F1 G1]].
  exploit Mem.loadv_extends. eauto. eexact LOAD1. eexact G1. intros (v1'' & LOAD1' & LD2).
  set (ls2 := Locmap.set (R dst') v1'' (undef_regs (destroyed_by_load Mint32 addr) ls1)).
  assert (SAT2: satisf (rs#dst <- v) ls2 e0).
  { eapply parallel_assignment_satisf; eauto.
    apply Val.lessdef_trans with v1'; auto. 
    subst v. unfold v1', kind_first_word.
    destruct big_endian; apply val_hiword_longofwords || apply val_loword_longofwords.
    eapply can_undef_satisf. eauto. eapply add_equations_satisf; eauto.
  }
  exploit (exec_moves mv2); eauto. intros [ls3 [A3 B3]]. 
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_trans. eexact A1. 
  eapply star_left. econstructor. 
  instantiate (1 := a1'). rewrite <- F1. apply eval_addressing_preserved. exact symbols_preserved.
  eexact LOAD1'. instantiate (1 := ls2); auto. 
  eapply star_right. eexact A3.
  constructor. 
  eauto. eauto. eauto. traceEq.
  exploit satisf_successors; eauto. simpl; eauto. intros [enext [W Z]]. 
  econstructor; eauto.

(* load second word of a pair *)
- generalize (wt_exec_Iload _ _ _ _ _ _ _ _ _ _ _ WTI H1 WTRS). intros WTRS'.
  exploit Mem.loadv_int64_split; eauto. intros (v1 & v2 & LOAD1 & LOAD2 & V12).
  set (v2' := if big_endian then v2 else v1) in *.
  set (v1' := if big_endian then v1 else v2) in *.
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 
  assert (LD1: Val.lessdef_list rs##args (reglist ls1 args')).
  { eapply add_equations_lessdef; eauto. }
  exploit eval_addressing_lessdef. eexact LD1.
  eapply eval_offset_addressing; eauto. intros [a1' [F1 G1]].
  exploit Mem.loadv_extends. eauto. eexact LOAD2. eexact G1. intros (v2'' & LOAD2' & LD2).
  set (ls2 := Locmap.set (R dst') v2'' (undef_regs (destroyed_by_load Mint32 addr2) ls1)).
  assert (SAT2: satisf (rs#dst <- v) ls2 e0).
  { eapply parallel_assignment_satisf; eauto.
    apply Val.lessdef_trans with v2'; auto. 
    subst v. unfold v2', kind_second_word.
    destruct big_endian; apply val_hiword_longofwords || apply val_loword_longofwords.
    eapply can_undef_satisf. eauto. eapply add_equations_satisf; eauto.
  }
  exploit (exec_moves mv2); eauto. intros [ls3 [A3 B3]]. 
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_trans. eexact A1. 
  eapply star_left. econstructor. 
  instantiate (1 := a1'). rewrite <- F1. apply eval_addressing_preserved. exact symbols_preserved.
  eexact LOAD2'. instantiate (1 := ls2); auto. 
  eapply star_right. eexact A3.
  constructor. 
  eauto. eauto. eauto. traceEq.
  exploit satisf_successors; eauto. simpl; eauto. intros [enext [W Z]]. 
  econstructor; eauto.

(* load dead *)
- exploit exec_moves; eauto. intros [ls1 [X Y]]. 
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_right. eexact X. econstructor; eauto. 
  eauto. traceEq.
  exploit satisf_successors. eauto. eauto. simpl; eauto. eauto. 
  eapply reg_unconstrained_satisf; eauto. 
  intros [enext [U V]]. 
  econstructor; eauto.
  eapply wt_exec_Iload; eauto.

(* store *)
- exploit exec_moves; eauto. intros [ls1 [X Y]].
  exploit add_equations_lessdef; eauto. intros LD. simpl in LD. inv LD. 
  exploit eval_addressing_lessdef; eauto. intros [a' [F G]].
  exploit Mem.storev_extends; eauto. intros [m'' [P Q]].
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_trans. eexact X.
  eapply star_two. econstructor. instantiate (1 := a'). rewrite <- F. 
  apply eval_addressing_preserved. exact symbols_preserved. eauto. eauto.
  constructor. eauto. eauto. traceEq.
  exploit satisf_successors; eauto. simpl; eauto.
  eapply can_undef_satisf; eauto. eapply add_equations_satisf; eauto. intros [enext [U V]]. 
  econstructor; eauto.

(* store 2 *)
- exploit Mem.storev_int64_split; eauto. 
  replace (if big_endian then Val.hiword rs#src else Val.loword rs#src)
     with (sel_val kind_first_word rs#src)
       by (unfold kind_first_word; destruct big_endian; reflexivity).
  replace (if big_endian then Val.loword rs#src else Val.hiword rs#src)
     with (sel_val kind_second_word rs#src)
       by (unfold kind_second_word; destruct big_endian; reflexivity).
  intros [m1 [STORE1 STORE2]].
  exploit (exec_moves mv1); eauto. intros [ls1 [X Y]].
  exploit add_equations_lessdef. eexact Heqo1. eexact Y. intros LD1.
  exploit add_equation_lessdef. eapply add_equations_satisf. eexact Heqo1. eexact Y. 
  simpl. intros LD2.
  set (ls2 := undef_regs (destroyed_by_store Mint32 addr) ls1).
  assert (SAT2: satisf rs ls2 e1).
    eapply can_undef_satisf. eauto. 
    eapply add_equation_satisf. eapply add_equations_satisf; eauto.
  exploit eval_addressing_lessdef. eexact LD1. eauto. intros [a1' [F1 G1]].
  assert (F1': eval_addressing tge sp addr (reglist ls1 args1') = Some a1').
    rewrite <- F1. apply eval_addressing_preserved. exact symbols_preserved.
  exploit Mem.storev_extends. eauto. eexact STORE1. eexact G1. eauto. 
  intros [m1' [STORE1' EXT1]].
  exploit (exec_moves mv2); eauto. intros [ls3 [U V]].
  exploit add_equations_lessdef. eexact Heqo. eexact V. intros LD3.
  exploit add_equation_lessdef. eapply add_equations_satisf. eexact Heqo. eexact V.
  simpl. intros LD4.
  exploit eval_addressing_lessdef. eexact LD3. eauto. intros [a2' [F2 G2]].
  assert (F2': eval_addressing tge sp addr (reglist ls3 args2') = Some a2').
    rewrite <- F2. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_offset_addressing. eauto. eexact F2'. intros F2''.
  exploit Mem.storev_extends. eexact EXT1. eexact STORE2. 
  apply Val.add_lessdef. eexact G2. eauto. eauto. 
  intros [m2' [STORE2' EXT2]].
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_trans. eexact X.
  eapply star_left. 
  econstructor. eexact F1'. eexact STORE1'. instantiate (1 := ls2). auto.
  eapply star_trans. eexact U.
  eapply star_two.
  econstructor. eexact F2''. eexact STORE2'. eauto. 
  constructor. eauto. eauto. eauto. eauto. traceEq.
  exploit satisf_successors; eauto. simpl; eauto.
  eapply can_undef_satisf. eauto.
  eapply add_equation_satisf. eapply add_equations_satisf; eauto.
  intros [enext [P Q]]. 
  econstructor; eauto.

(* call *)
- set (sg := RTL.funsig fd) in *.
  set (args' := loc_arguments sg) in *.
  set (res' := map R (loc_result sg)) in *.
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 
  exploit find_function_translated. eauto. eauto. eapply add_equations_args_satisf; eauto. 
  intros [tfd [E F]].
  assert (SIG: funsig tfd = sg). eapply sig_function_translated; eauto.
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_right. eexact A1. econstructor; eauto.
  eauto. traceEq.
  exploit analyze_successors; eauto. simpl. left; eauto. intros [enext [U V]].
  econstructor; eauto.
  econstructor; eauto.
  inv WTI. rewrite SIG. auto. 
  intros. exploit (exec_moves mv2). eauto. eauto. 
  eapply function_return_satisf with (v := v) (ls_before := ls1) (ls_after := ls0); eauto.
  eapply add_equation_ros_satisf; eauto. 
  eapply add_equations_args_satisf; eauto. 
  congruence.
  apply wt_regset_assign; auto.
  intros [ls2 [A2 B2]].
  exists ls2; split. 
  eapply star_right. eexact A2. constructor. traceEq.
  apply satisf_incr with eafter; auto. 
  rewrite SIG. eapply add_equations_args_lessdef; eauto.
  inv WTI. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto. 
  simpl. red; auto.
  inv WTI. rewrite SIG. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto. 

(* tailcall *)
- set (sg := RTL.funsig fd) in *.
  set (args' := loc_arguments sg) in *.
  exploit Mem.free_parallel_extends; eauto. intros [m'' [P Q]]. 
  exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]]. 
  exploit find_function_translated. eauto. eauto. eapply add_equations_args_satisf; eauto. 
  intros [tfd [E F]].
  assert (SIG: funsig tfd = sg). eapply sig_function_translated; eauto.
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_right. eexact A1. econstructor; eauto.
  rewrite <- E. apply find_function_tailcall; auto. 
  replace (fn_stacksize tf) with (RTL.fn_stacksize f); eauto.
  destruct (transf_function_inv _ _ FUN); auto.
  eauto. traceEq.
  econstructor; eauto.
  eapply match_stackframes_change_sig; eauto. rewrite SIG. rewrite e0. decEq.
  destruct (transf_function_inv _ _ FUN); auto.
  rewrite SIG. rewrite return_regs_arg_values; auto. eapply add_equations_args_lessdef; eauto.
  inv WTI. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto. 
  apply return_regs_agree_callee_save.
  rewrite SIG. inv WTI. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto. 

(* builtin *)
- assert (WTRS': wt_regset env (rs#res <- v)) by (eapply wt_exec_Ibuiltin; eauto).
  exploit (exec_moves mv1); eauto. intros [ls1 [A1 B1]]. 
  exploit external_call_mem_extends; eauto.
  eapply add_equations_args_lessdef; eauto.
  inv WTI. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto. 
  intros [v' [m'' [F [G [J K]]]]].
  assert (E: map ls1 (map R args') = reglist ls1 args').
  { unfold reglist. rewrite list_map_compose. auto. }
  rewrite E in F. clear E.
  set (vl' := encode_long (sig_res (ef_sig ef)) v').
  set (ls2 := Locmap.setlist (map R res') vl' (undef_regs (destroyed_by_builtin ef) ls1)).
  assert (satisf (rs#res <- v) ls2 e0).
  { eapply parallel_assignment_satisf_2; eauto. 
    eapply can_undef_satisf; eauto.
    eapply add_equations_args_satisf; eauto. }
  exploit (exec_moves mv2); eauto. intros [ls3 [A3 B3]].
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_trans. eexact A1. 
  eapply star_left. econstructor. 
  econstructor. unfold reglist. eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
  instantiate (1 := vl'); auto. 
  instantiate (1 := ls2); auto. 
  eapply star_right. eexact A3.
  econstructor. 
  reflexivity. reflexivity. reflexivity. traceEq. 
  exploit satisf_successors; eauto. simpl; eauto.
  intros [enext [U V]]. 
  econstructor; eauto.
 
(* annot *)
- exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]]. 
  exploit external_call_mem_extends; eauto. eapply add_equations_args_lessdef; eauto.
  inv WTI. eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto. 
  intros [v' [m'' [F [G [J K]]]]].
  assert (v = Vundef). red in H0; inv H0. auto.
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_trans. eexact A1. 
  eapply star_two. econstructor.
  eapply external_call_symbols_preserved' with (ge1 := ge).
  econstructor; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
  eauto. constructor. eauto. eauto. traceEq.
  exploit satisf_successors. eauto. eauto. simpl; eauto. eauto. 
  eapply satisf_undef_reg with (r := res).
  eapply add_equations_args_satisf; eauto. 
  intros [enext [U V]]. 
  econstructor; eauto.
  change (destroyed_by_builtin (EF_annot txt typ)) with (@nil mreg). 
  simpl. subst v. assumption.
  apply wt_regset_assign; auto. subst v. constructor. 

(* cond *)
- exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_right. eexact A1.
  econstructor. eapply eval_condition_lessdef; eauto. eapply add_equations_lessdef; eauto. 
  eauto. eauto. eauto. traceEq. 
  exploit satisf_successors; eauto.
  instantiate (1 := if b then ifso else ifnot). simpl. destruct b; auto.
  eapply can_undef_satisf. eauto. eapply add_equations_satisf; eauto.
  intros [enext [U V]]. 
  econstructor; eauto.

(* jumptable *)
- exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
  assert (Val.lessdef (Vint n) (ls1 (R arg'))).
    rewrite <- H0. eapply add_equation_lessdef with (q := Eq Full arg (R arg')); eauto.
  inv H2.  
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_right. eexact A1.
  econstructor. eauto. eauto. eauto. eauto. traceEq. 
  exploit satisf_successors; eauto.
  instantiate (1 := pc'). simpl. eapply list_nth_z_in; eauto. 
  eapply can_undef_satisf. eauto. eapply add_equation_satisf; eauto.
  intros [enext [U V]]. 
  econstructor; eauto.

(* return *)
- destruct (transf_function_inv _ _ FUN). 
  exploit Mem.free_parallel_extends; eauto. rewrite H10. intros [m'' [P Q]].
  inv WTI; MonadInv.
  (* without an argument *)
+ exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_right. eexact A1.
  econstructor. eauto. eauto. traceEq.
  simpl. econstructor; eauto.
  unfold encode_long, loc_result. rewrite <- H11; rewrite H13. simpl; auto.
  apply return_regs_agree_callee_save.
  constructor.
  (* with an argument *)
+ exploit (exec_moves mv); eauto. intros [ls1 [A1 B1]].
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_right. eexact A1.
  econstructor. eauto. eauto. traceEq.
  simpl. econstructor; eauto. rewrite <- H11.
  replace (map (return_regs (parent_locset ts) ls1) (map R (loc_result (RTL.fn_sig f))))
     with (map ls1 (map R (loc_result (RTL.fn_sig f)))).
  eapply add_equations_res_lessdef; eauto.
  rewrite !list_map_compose. apply list_map_exten; intros.
  unfold return_regs. apply pred_dec_true. eapply loc_result_caller_save; eauto.
  apply return_regs_agree_callee_save.
  unfold proj_sig_res. rewrite <- H11; rewrite H13. 
  eapply Val.has_subtype; eauto. 

(* internal function *)
- monadInv FUN. simpl in *.
  destruct (transf_function_inv _ _ EQ). 
  exploit Mem.alloc_extends; eauto. apply Zle_refl. rewrite H8; apply Zle_refl. 
  intros [m'' [U V]].
  assert (WTRS: wt_regset env (init_regs args (fn_params f))).
  { apply wt_init_regs. inv H0. eapply Val.has_subtype_list; eauto. congruence. }
  exploit (exec_moves mv). eauto. eauto.
    eapply can_undef_satisf; eauto. eapply compat_entry_satisf; eauto. 
    rewrite call_regs_param_values. rewrite H9. eexact ARGS.
    exact WTRS.
  intros [ls1 [A B]].
  econstructor; split.
  eapply plus_left. econstructor; eauto. 
  eapply star_left. econstructor; eauto. 
  eapply star_right. eexact A. 
  econstructor; eauto. 
  eauto. eauto. traceEq.
  econstructor; eauto.

(* external function *)
- exploit external_call_mem_extends; eauto. intros [v' [m'' [F [G [J K]]]]].
  simpl in FUN; inv FUN.
  econstructor; split.
  apply plus_one. econstructor; eauto. 
  eapply external_call_symbols_preserved' with (ge1 := ge). 
  econstructor; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto. simpl.
  replace (map
           (Locmap.setlist (map R (loc_result (ef_sig ef)))
                (encode_long (sig_res (ef_sig ef)) v') ls)
           (map R (loc_result (ef_sig ef))))
  with (encode_long (sig_res (ef_sig ef)) v').
  apply encode_long_lessdef; auto.
  unfold encode_long, loc_result.
  destruct (sig_res (ef_sig ef)) as [[]|]; simpl; symmetry; f_equal; auto.
  red; intros. rewrite Locmap.gsetlisto. apply AG; auto.
  apply Loc.notin_iff. intros. 
  exploit list_in_map_inv; eauto. intros [r [A B]]; subst l'. 
  destruct l; simpl; auto. red; intros; subst r0; elim H0.
  eapply loc_result_caller_save; eauto.
  simpl. eapply external_call_well_typed; eauto. 
 
(* return *)
- inv STACKS.
  exploit STEPS; eauto. eapply Val.has_subtype; eauto. intros [ls2 [A B]].
  econstructor; split.
  eapply plus_left. constructor. eexact A. traceEq.
  econstructor; eauto.
  apply wt_regset_assign; auto. eapply Val.has_subtype; eauto. 
Qed.

Lemma initial_states_simulation:
  forall st1, RTL.initial_state prog st1 ->
  exists st2, LTL.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  exploit sig_function_translated; eauto. intros SIG.
  exists (LTL.Callstate nil tf (Locmap.init Vundef) m0); split.
  econstructor; eauto.
  eapply Genv.init_mem_transf_partial; eauto. 
  rewrite symbols_preserved. 
  rewrite (transform_partial_program_main _ _ TRANSF).  auto.
  congruence.
  constructor; auto.
  constructor. rewrite SIG; rewrite H3; auto. 
  rewrite SIG; rewrite H3; simpl; auto.
  red; auto.
  apply Mem.extends_refl.
  rewrite SIG; rewrite H3; simpl; auto.
Qed.

Lemma final_states_simulation:
  forall st1 st2 r, 
  match_states st1 st2 -> RTL.final_state st1 r -> LTL.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS.
  econstructor. simpl; reflexivity.  
  unfold loc_result in RES; rewrite H in RES. simpl in RES. inv RES. inv H3; auto. 
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (LTL.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  eexact symbols_preserved.
  eexact initial_states_simulation.
  eexact final_states_simulation.
  exact step_simulation. 
Qed.

End PRESERVATION.
