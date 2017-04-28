(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                 Xavier Leroy, INRIA Paris                           *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness of instruction selection for 64-bit integer operations *)

Require Import String Coqlib Maps Integers Floats Errors.
Require Archi.
Require Import AST Values Memory Globalenvs Events.
Require Import Cminor Op CminorSel.
Require Import SelectOp SelectOpproof SplitLong SplitLongproof.
Require Import SelectLong.

Local Open Scope cminorsel_scope.
Local Open Scope string_scope.

(** * Correctness of the instruction selection functions for 64-bit operators *)

Section CMCONSTR.

Variable prog: program.
Variable hf: helper_functions.
Hypothesis HELPERS: helper_functions_declared prog hf.
Let ge := Genv.globalenv prog.
Variable sp: val.
Variable e: env.
Variable m: mem.

Definition unary_constructor_sound (cstr: expr -> expr) (sem: val -> val) : Prop :=
  forall le a x,
  eval_expr ge sp e m le a x ->
  exists v, eval_expr ge sp e m le (cstr a) v /\ Val.lessdef (sem x) v.

Definition binary_constructor_sound (cstr: expr -> expr -> expr) (sem: val -> val -> val) : Prop :=
  forall le a x b y,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  exists v, eval_expr ge sp e m le (cstr a b) v /\ Val.lessdef (sem x y) v.

Definition partial_unary_constructor_sound (cstr: expr -> expr) (sem: val -> option val) : Prop :=
  forall le a x y,
  eval_expr ge sp e m le a x ->
  sem x = Some y ->
  exists v, eval_expr ge sp e m le (cstr a) v /\ Val.lessdef y v.

Definition partial_binary_constructor_sound (cstr: expr -> expr -> expr) (sem: val -> val -> option val) : Prop :=
  forall le a x b y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  sem x y = Some z ->
  exists v, eval_expr ge sp e m le (cstr a b) v /\ Val.lessdef z v.

Theorem eval_longconst:
  forall le n, eval_expr ge sp e m le (longconst n) (Vlong n).
Proof.
  unfold longconst; intros; destruct Archi.splitlong.
  apply SplitLongproof.eval_longconst.
  EvalOp.
Qed.

Lemma is_longconst_sound:
  forall v a n le,
  is_longconst a = Some n -> eval_expr ge sp e m le a v -> v = Vlong n.
Proof with (try discriminate).
  intros. unfold is_longconst in *. destruct Archi.splitlong.
  eapply SplitLongproof.is_longconst_sound; eauto.
  assert (a = Eop (Olongconst n) Enil).
  { destruct a... destruct o... destruct e0... congruence. }
  subst a. InvEval. auto.
Qed.

Theorem eval_intoflong: unary_constructor_sound intoflong Val.loword.
Proof.
  unfold intoflong; destruct Archi.splitlong. apply SplitLongproof.eval_intoflong.
  red; intros. destruct (is_longconst a) as [n|] eqn:C.
- TrivialExists. simpl. erewrite (is_longconst_sound x) by eauto. auto.
- TrivialExists.
Qed.

Theorem eval_longofintu: unary_constructor_sound longofintu Val.longofintu.
Proof.
  unfold longofintu; destruct Archi.splitlong. apply SplitLongproof.eval_longofintu.
  red; intros. destruct (is_intconst a) as [n|] eqn:C.
- econstructor; split. apply eval_longconst.
  exploit is_intconst_sound; eauto. intros; subst x. auto.
- TrivialExists.
Qed.

Theorem eval_longofint: unary_constructor_sound longofint Val.longofint.
Proof.
  unfold longofint; destruct Archi.splitlong. apply SplitLongproof.eval_longofint.
  red; intros. destruct (is_intconst a) as [n|] eqn:C.
- econstructor; split. apply eval_longconst.
  exploit is_intconst_sound; eauto. intros; subst x. auto.
- TrivialExists.
Qed.

Theorem eval_negl: unary_constructor_sound negl Val.negl.
Proof.
  unfold negl. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_negl; auto.
  red; intros. destruct (is_longconst a) as [n|] eqn:C.
- exploit is_longconst_sound; eauto. intros EQ; subst x.
  econstructor; split. apply eval_longconst. auto.
- TrivialExists.
Qed.

Theorem eval_addlimm: forall n, unary_constructor_sound (addlimm n) (fun v => Val.addl v (Vlong n)).
Proof.
  unfold addlimm; intros; red; intros.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
  subst. exists x; split; auto.
  destruct x; simpl; rewrite ?Int64.add_zero, ?Ptrofs.add_zero; auto.
  destruct Archi.ptr64; auto.
  destruct (addlimm_match a); InvEval.
- econstructor; split. apply eval_longconst. rewrite Int64.add_commut; auto.
- econstructor; split. EvalOp. simpl; eauto. 
  unfold Genv.symbol_address. destruct (Genv.find_symbol ge s); simpl; auto. 
  destruct Archi.ptr64; auto. rewrite Ptrofs.add_commut; auto. 
- econstructor; split. EvalOp. simpl; eauto. 
  destruct sp; simpl; auto. destruct Archi.ptr64; auto. 
  rewrite Ptrofs.add_assoc, (Ptrofs.add_commut m0). auto. 
- subst x. rewrite Val.addl_assoc. rewrite Int64.add_commut. TrivialExists.
- TrivialExists.
Qed.

Theorem eval_addl: binary_constructor_sound addl Val.addl.
Proof.
  unfold addl. destruct Archi.splitlong eqn:SL. 
  apply SplitLongproof.eval_addl. apply Archi.splitlong_ptr32; auto.
(*
  assert (SF: Archi.ptr64 = true).
  { Local Transparent Archi.splitlong. unfold Archi.splitlong in SL. 
    destruct Archi.ptr64; simpl in *; congruence. }  
*)
(*
  assert (B: forall id ofs n,
             Genv.symbol_address ge id (Ptrofs.add ofs (Ptrofs.repr n)) =
             Val.addl (Genv.symbol_address ge id ofs) (Vlong (Int64.repr n))).
  { intros. replace (Ptrofs.repr n) with (Ptrofs.of_int64 (Int64.repr n)) by auto with ptrofs.
    apply Genv.shift_symbol_address_64; auto. }

*)
  red; intros until y.
  case (addl_match a b); intros; InvEval.
  - rewrite Val.addl_commut. apply eval_addlimm; auto.
  - apply eval_addlimm; auto.
  - subst.
    replace (Val.addl (Val.addl v1 (Vlong n1)) (Val.addl v0 (Vlong n2)))
       with (Val.addl (Val.addl v1 v0) (Val.addl (Vlong n1) (Vlong n2))).
    apply eval_addlimm. EvalOp.
    repeat rewrite Val.addl_assoc. decEq. apply Val.addl_permut.
  - subst. econstructor; split.
    EvalOp. constructor. EvalOp. simpl; eauto. constructor. eauto. constructor. simpl; eauto.
    rewrite Val.addl_commut. destruct sp; simpl; auto.
    destruct v1; simpl; auto.
    destruct Archi.ptr64 eqn:SF; auto. 
    apply Val.lessdef_same. f_equal. rewrite ! Ptrofs.add_assoc. f_equal. 
    rewrite (Ptrofs.add_commut (Ptrofs.of_int64 n1)), Ptrofs.add_assoc. f_equal. auto with ptrofs.
    destruct Archi.ptr64 eqn:SF; auto.
  - subst. econstructor; split.
    EvalOp. constructor. EvalOp. simpl; eauto. constructor. eauto. constructor. simpl; eauto.
    destruct sp; simpl; auto.
    destruct v1; simpl; auto.
    destruct Archi.ptr64 eqn:SF; auto. 
    apply Val.lessdef_same. f_equal. rewrite ! Ptrofs.add_assoc. f_equal. f_equal.
    rewrite Ptrofs.add_commut. auto with ptrofs.
    destruct Archi.ptr64 eqn:SF; auto.
  - subst.
    replace (Val.addl (Val.addl v1 (Vlong n1)) y)
       with (Val.addl (Val.addl v1 y) (Vlong n1)).
    apply eval_addlimm. EvalOp.
    repeat rewrite Val.addl_assoc. decEq. apply Val.addl_commut.
  - subst.
    replace (Val.addl x (Val.addl v1 (Vlong n2)))
       with (Val.addl (Val.addl x v1) (Vlong n2)).
    apply eval_addlimm. EvalOp.
    repeat rewrite Val.addl_assoc. reflexivity.
  - TrivialExists.
Qed.

Theorem eval_subl: binary_constructor_sound subl Val.subl.
Proof.
  unfold subl. destruct Archi.splitlong eqn:SL.
  apply SplitLongproof.eval_subl. apply Archi.splitlong_ptr32; auto.
  red; intros; destruct (subl_match a b); InvEval.
- rewrite Val.subl_addl_opp. apply eval_addlimm; auto.
- subst. rewrite Val.subl_addl_l. rewrite Val.subl_addl_r.
  rewrite Val.addl_assoc. simpl. rewrite Int64.add_commut. rewrite <- Int64.sub_add_opp.
  apply eval_addlimm; EvalOp.
- subst. rewrite Val.subl_addl_l. apply eval_addlimm; EvalOp.
- subst. rewrite Val.subl_addl_r.
  apply eval_addlimm; EvalOp.
- TrivialExists.
Qed.

Theorem eval_shllimm: forall n, unary_constructor_sound (fun e => shllimm e n) (fun v => Val.shll v (Vint n)).
Proof.
  intros; unfold shllimm. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_shllimm; auto.
  red; intros.
  predSpec Int.eq Int.eq_spec n Int.zero.
  exists x; split; auto. subst n; destruct x; simpl; auto.
  destruct (Int.ltu Int.zero Int64.iwordsize'); auto.
  change (Int64.shl' i Int.zero) with (Int64.shl i Int64.zero). rewrite Int64.shl_zero; auto.
  destruct (Int.ltu n Int64.iwordsize') eqn:LT; simpl.
  assert (DEFAULT: exists v, eval_expr ge sp e m le (Eop (Oshllimm n) (a:::Enil)) v
                         /\  Val.lessdef (Val.shll x (Vint n)) v) by TrivialExists.
  destruct (shllimm_match a); InvEval.
- econstructor; split. apply eval_longconst. simpl; rewrite LT; auto.
- destruct (Int.ltu (Int.add n n1) Int64.iwordsize') eqn:LT'; auto.
  subst. econstructor; split. EvalOp. simpl; eauto.
  destruct v1; simpl; auto. rewrite LT'.
  destruct (Int.ltu n1 Int64.iwordsize') eqn:LT1; auto.
  simpl; rewrite LT. rewrite Int.add_commut, Int64.shl'_shl'; auto. rewrite Int.add_commut; auto.
- apply DEFAULT.  
- TrivialExists. constructor; eauto. constructor. EvalOp. simpl; eauto. constructor. auto.
Qed.

Theorem eval_shrluimm: forall n, unary_constructor_sound (fun e => shrluimm e n) (fun v => Val.shrlu v (Vint n)).
Proof.
  intros; unfold shrluimm. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_shrluimm; auto.
  red; intros.
  predSpec Int.eq Int.eq_spec n Int.zero.
  exists x; split; auto. subst n; destruct x; simpl; auto.
  destruct (Int.ltu Int.zero Int64.iwordsize'); auto.
  change (Int64.shru' i Int.zero) with (Int64.shru i Int64.zero). rewrite Int64.shru_zero; auto.
  destruct (Int.ltu n Int64.iwordsize') eqn:LT; simpl.
  assert (DEFAULT: exists v, eval_expr ge sp e m le (Eop (Oshrluimm n) (a:::Enil)) v
                         /\  Val.lessdef (Val.shrlu x (Vint n)) v) by TrivialExists.
  destruct (shrluimm_match a); InvEval.
- econstructor; split. apply eval_longconst. simpl; rewrite LT; auto.
- destruct (Int.ltu (Int.add n n1) Int64.iwordsize') eqn:LT'; auto.
  subst. econstructor; split. EvalOp. simpl; eauto.
  destruct v1; simpl; auto. rewrite LT'.
  destruct (Int.ltu n1 Int64.iwordsize') eqn:LT1; auto.
  simpl; rewrite LT. rewrite Int.add_commut, Int64.shru'_shru'; auto. rewrite Int.add_commut; auto.
- apply DEFAULT.
- TrivialExists. constructor; eauto. constructor. EvalOp. simpl; eauto. constructor. auto.
Qed.

Theorem eval_shrlimm: forall n, unary_constructor_sound (fun e => shrlimm e n) (fun v => Val.shrl v (Vint n)).
Proof.
  intros; unfold shrlimm. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_shrlimm; auto.
  red; intros.
  predSpec Int.eq Int.eq_spec n Int.zero.
  exists x; split; auto. subst n; destruct x; simpl; auto.
  destruct (Int.ltu Int.zero Int64.iwordsize'); auto.
  change (Int64.shr' i Int.zero) with (Int64.shr i Int64.zero). rewrite Int64.shr_zero; auto.
  destruct (Int.ltu n Int64.iwordsize') eqn:LT; simpl.
  assert (DEFAULT: exists v, eval_expr ge sp e m le (Eop (Oshrlimm n) (a:::Enil)) v
                         /\  Val.lessdef (Val.shrl x (Vint n)) v) by TrivialExists.
  destruct (shrlimm_match a); InvEval.
- econstructor; split. apply eval_longconst. simpl; rewrite LT; auto.
- destruct (Int.ltu (Int.add n n1) Int64.iwordsize') eqn:LT'; auto.
  subst. econstructor; split. EvalOp. simpl; eauto.
  destruct v1; simpl; auto. rewrite LT'.
  destruct (Int.ltu n1 Int64.iwordsize') eqn:LT1; auto.
  simpl; rewrite LT. rewrite Int.add_commut, Int64.shr'_shr'; auto. rewrite Int.add_commut; auto.
- apply DEFAULT.
- TrivialExists. constructor; eauto. constructor. EvalOp. simpl; eauto. constructor. auto.
Qed.

Theorem eval_shll: binary_constructor_sound shll Val.shll.
Proof.
  unfold shll. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_shll; auto.
  red; intros. destruct (is_intconst b) as [n2|] eqn:C.
- exploit is_intconst_sound; eauto. intros EQ; subst y. apply eval_shllimm; auto.
- TrivialExists.
Qed.

Theorem eval_shrlu: binary_constructor_sound shrlu Val.shrlu.
Proof.
  unfold shrlu. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_shrlu; auto.
  red; intros. destruct (is_intconst b) as [n2|] eqn:C.
- exploit is_intconst_sound; eauto. intros EQ; subst y. apply eval_shrluimm; auto.
- TrivialExists.
Qed.

Theorem eval_shrl: binary_constructor_sound shrl Val.shrl.
Proof.
  unfold shrl. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_shrl; auto.
  red; intros. destruct (is_intconst b) as [n2|] eqn:C.
- exploit is_intconst_sound; eauto. intros EQ; subst y. apply eval_shrlimm; auto.
- TrivialExists.
Qed.

Theorem eval_mullimm_base: forall n, unary_constructor_sound (mullimm_base n) (fun v => Val.mull v (Vlong n)).
Proof.
  intros; unfold mullimm_base. red; intros.
  assert (DEFAULT: exists v,
                eval_expr ge sp e m le (Eop Omull (a ::: longconst n ::: Enil)) v
             /\ Val.lessdef (Val.mull x (Vlong n)) v).
  { econstructor; split. EvalOp. constructor. eauto. constructor. apply eval_longconst. constructor. simpl; eauto.
    auto. }
  generalize (Int64.one_bits'_decomp n); intros D.
  destruct (Int64.one_bits' n) as [ | i [ | j [ | ? ? ]]] eqn:B.
- apply DEFAULT.
- replace (Val.mull x (Vlong n)) with (Val.shll x (Vint i)).
  apply eval_shllimm; auto.
  simpl in D. rewrite D, Int64.add_zero. destruct x; simpl; auto.
  rewrite (Int64.one_bits'_range n) by (rewrite B; auto with coqlib).
  rewrite Int64.shl'_mul; auto.
- set (le' := x :: le).
  assert (A0: eval_expr ge sp e m le' (Eletvar O) x) by (constructor; reflexivity).
  exploit (eval_shllimm i). eexact A0. intros (v1 & A1 & B1).
  exploit (eval_shllimm j). eexact A0. intros (v2 & A2 & B2).
  exploit (eval_addl). eexact A1. eexact A2. intros (v3 & A3 & B3).
  exists v3; split. econstructor; eauto.
  rewrite D. simpl. rewrite Int64.add_zero. destruct x; auto.
  simpl in *.
  rewrite (Int64.one_bits'_range n) in B1 by (rewrite B; auto with coqlib).
  rewrite (Int64.one_bits'_range n) in B2 by (rewrite B; auto with coqlib).
  inv B1; inv B2. simpl in B3; inv B3.
  rewrite Int64.mul_add_distr_r. rewrite <- ! Int64.shl'_mul. auto.
- apply DEFAULT.
Qed.

Theorem eval_mullimm: forall n, unary_constructor_sound (mullimm n) (fun v => Val.mull v (Vlong n)).
Proof.
  unfold mullimm. intros; red; intros.
  destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_mullimm; eauto.  
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
  exists (Vlong Int64.zero); split. apply eval_longconst.
  destruct x; simpl; auto. subst n; rewrite Int64.mul_zero; auto.
  predSpec Int64.eq Int64.eq_spec n Int64.one.
  exists x; split; auto.
  destruct x; simpl; auto. subst n; rewrite Int64.mul_one; auto.
  destruct (mullimm_match a); InvEval.
- econstructor; split. apply eval_longconst. rewrite Int64.mul_commut; auto.
- exploit (eval_mullimm_base n); eauto. intros (v2 & A2 & B2).
  exploit (eval_addlimm (Int64.mul n n2)). eexact A2. intros (v3 & A3 & B3).
  exists v3; split; auto.
  subst x. destruct v1; simpl; auto.
  simpl in B2; inv B2. simpl in B3; inv B3. rewrite Int64.mul_add_distr_l.
  rewrite (Int64.mul_commut n). auto.
  destruct Archi.ptr64; simpl; auto.
- apply eval_mullimm_base; auto.
Qed.

Theorem eval_mull: binary_constructor_sound mull Val.mull.
Proof.
  unfold mull. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_mull; auto.
  red; intros; destruct (mull_match a b); InvEval.
- rewrite Val.mull_commut. apply eval_mullimm; auto.
- apply eval_mullimm; auto.
- TrivialExists.
Qed.

Theorem eval_mullhu: 
  forall n, unary_constructor_sound (fun a => mullhu a n) (fun v => Val.mullhu v (Vlong n)).
Proof.
  unfold mullhu; intros. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_mullhu; auto.
  red; intros. TrivialExists. constructor. eauto. constructor. apply eval_longconst. constructor. auto.
Qed.

Theorem eval_mullhs: 
  forall n, unary_constructor_sound (fun a => mullhs a n) (fun v => Val.mullhs v (Vlong n)).
Proof.
  unfold mullhs; intros. destruct Archi.splitlong eqn:SL. apply SplitLongproof.eval_mullhs; auto.
  red; intros. TrivialExists. constructor. eauto. constructor. apply eval_longconst. constructor. auto.
Qed.

Theorem eval_andlimm: forall n, unary_constructor_sound (andlimm n) (fun v => Val.andl v (Vlong n)).
Proof.
  unfold andlimm; intros; red; intros.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
  exists (Vlong Int64.zero); split. apply eval_longconst.
  subst. destruct x; simpl; auto. rewrite Int64.and_zero; auto.
  predSpec Int64.eq Int64.eq_spec n Int64.mone.
  exists x; split. assumption.
  subst. destruct x; simpl; auto. rewrite Int64.and_mone; auto.
  destruct (andlimm_match a); InvEval; subst.
- econstructor; split. apply eval_longconst. simpl. rewrite Int64.and_commut; auto.
- TrivialExists. simpl. rewrite Val.andl_assoc. rewrite Int64.and_commut; auto.
- TrivialExists.
Qed.

Theorem eval_andl: binary_constructor_sound andl Val.andl.
Proof.
  unfold andl; destruct Archi.splitlong. apply SplitLongproof.eval_andl.
  red; intros. destruct (andl_match a b).
- InvEval. rewrite Val.andl_commut. apply eval_andlimm; auto.
- InvEval. apply eval_andlimm; auto.
- TrivialExists.
Qed.

Theorem eval_orlimm: forall n, unary_constructor_sound (orlimm n) (fun v => Val.orl v (Vlong n)).
Proof.
  unfold orlimm; intros; red; intros.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
  exists x; split; auto. subst. destruct x; simpl; auto. rewrite Int64.or_zero; auto.
  predSpec Int64.eq Int64.eq_spec n Int64.mone.
  econstructor; split. apply eval_longconst. subst. destruct x; simpl; auto. rewrite Int64.or_mone; auto.
  destruct (orlimm_match a); InvEval; subst.
- econstructor; split. apply eval_longconst. simpl. rewrite Int64.or_commut; auto.
- TrivialExists. simpl. rewrite Val.orl_assoc. rewrite Int64.or_commut; auto.
- TrivialExists.
Qed.

Theorem eval_orl: binary_constructor_sound orl Val.orl.
Proof.
  unfold orl; destruct Archi.splitlong. apply SplitLongproof.eval_orl.
  red; intros.
  destruct (orl_match a b).
- InvEval. rewrite Val.orl_commut. apply eval_orlimm; auto.
- InvEval. apply eval_orlimm; auto.
- TrivialExists.
Qed.

Theorem eval_xorlimm: forall n, unary_constructor_sound (xorlimm n) (fun v => Val.xorl v (Vlong n)).
Proof.
  unfold xorlimm; intros; red; intros.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
  exists x; split; auto. subst. destruct x; simpl; auto. rewrite Int64.xor_zero; auto.
  destruct (xorlimm_match a); InvEval; subst.
- econstructor; split. apply eval_longconst. simpl. rewrite Int64.xor_commut; auto.
- rewrite Val.xorl_assoc. simpl. rewrite (Int64.xor_commut n2).
  predSpec Int64.eq Int64.eq_spec (Int64.xor n n2) Int64.zero.
+ rewrite H. exists v1; split; auto. destruct v1; simpl; auto. rewrite Int64.xor_zero; auto. 
+ TrivialExists.
- TrivialExists.
Qed.

Theorem eval_xorl: binary_constructor_sound xorl Val.xorl.
Proof.
  unfold xorl; destruct Archi.splitlong. apply SplitLongproof.eval_xorl.
  red; intros. destruct (xorl_match a b).
- InvEval. rewrite Val.xorl_commut. apply eval_xorlimm; auto.
- InvEval. apply eval_xorlimm; auto.
- TrivialExists.
Qed.

Theorem eval_notl: unary_constructor_sound notl Val.notl.
Proof.
  unfold notl; destruct Archi.splitlong. apply SplitLongproof.eval_notl.
  red; intros. rewrite Val.notl_xorl. apply eval_xorlimm; auto.
Qed.

Theorem eval_divls_base: partial_binary_constructor_sound divls_base Val.divls.
Proof.
  unfold divls_base; red; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_divls_base; eauto.
  TrivialExists.
Qed.

Theorem eval_modls_base: partial_binary_constructor_sound modls_base Val.modls.
Proof.
  unfold modls_base; red; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_modls_base; eauto.
  TrivialExists.
Qed.

Theorem eval_divlu_base: partial_binary_constructor_sound divlu_base Val.divlu.
Proof.
  unfold divlu_base; red; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_divlu_base; eauto.
  TrivialExists.
Qed.

Theorem eval_modlu_base: partial_binary_constructor_sound modlu_base Val.modlu.
Proof.
  unfold modlu_base; red; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_modlu_base; eauto.
  TrivialExists.
Qed.

Theorem eval_shrxlimm:
  forall le a n x z,
  eval_expr ge sp e m le a x ->
  Val.shrxl x (Vint n) = Some z ->
  exists v, eval_expr ge sp e m le (shrxlimm a n) v /\ Val.lessdef z v.
Proof.
  unfold shrxlimm; intros. destruct Archi.splitlong eqn:SL.
+ eapply SplitLongproof.eval_shrxlimm; eauto using Archi.splitlong_ptr32.
+ predSpec Int.eq Int.eq_spec n Int.zero.
- subst n. destruct x; simpl in H0; inv H0. econstructor; split; eauto.
  change (Int.ltu Int.zero (Int.repr 63)) with true. simpl. rewrite Int64.shrx'_zero; auto.
- TrivialExists.
(*
  intros. unfold shrxlimm. destruct Archi.splitlong eqn:SL.
+ eapply SplitLongproof.eval_shrxlimm; eauto using Archi.splitlong_ptr32.
+ destruct x; simpl in H0; try discriminate. 
  destruct (Int.ltu n (Int.repr 63)) eqn:LTU; inv H0.
  predSpec Int.eq Int.eq_spec n Int.zero.
  - subst n. exists (Vlong i); split; auto. rewrite Int64.shrx'_zero. auto.
  - assert (NZ: Int.unsigned n <> 0).
    { intro EQ; elim H0. rewrite <- (Int.repr_unsigned n). rewrite EQ; auto. }
    assert (LT: 0 <= Int.unsigned n < 63) by (apply Int.ltu_inv in LTU; assumption).
    assert (LTU2: Int.ltu (Int.sub Int64.iwordsize' n) Int64.iwordsize' = true).
    { unfold Int.ltu; apply zlt_true.
      unfold Int.sub. change (Int.unsigned Int64.iwordsize') with 64. 
      rewrite Int.unsigned_repr. omega. 
      assert (64 < Int.max_unsigned) by reflexivity. omega. }
    assert (X: eval_expr ge sp e m le
               (Eop (Oshrlimm (Int.repr (Int64.zwordsize - 1))) (a ::: Enil))
               (Vlong (Int64.shr' i (Int.repr (Int64.zwordsize - 1))))).
    { EvalOp. }
    assert (Y: eval_expr ge sp e m le (shrxlimm_inner a n)
               (Vlong (Int64.shru' (Int64.shr' i (Int.repr (Int64.zwordsize - 1))) (Int.sub Int64.iwordsize' n)))).
    { EvalOp. simpl. rewrite LTU2. auto. }
    TrivialExists. 
    constructor. EvalOp. simpl; eauto. constructor. 
    simpl. unfold Int.ltu; rewrite zlt_true. rewrite Int64.shrx'_shr_2 by auto. reflexivity. 
    change (Int.unsigned Int64.iwordsize') with 64; omega.
*)
Qed.

Theorem eval_cmplu:
  forall c le a x b y v,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.cmplu (Mem.valid_pointer m) c x y = Some v ->
  eval_expr ge sp e m le (cmplu c a b) v.
Proof.
  unfold cmplu; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_cmplu; eauto using Archi.splitlong_ptr32.
  unfold Val.cmplu in H1.
  destruct (Val.cmplu_bool (Mem.valid_pointer m) c x y) as [vb|] eqn:C; simpl in H1; inv H1.
  destruct (is_longconst a) as [n1|] eqn:LC1; destruct (is_longconst b) as [n2|] eqn:LC2;
  try (assert (x = Vlong n1) by (eapply is_longconst_sound; eauto));
  try (assert (y = Vlong n2) by (eapply is_longconst_sound; eauto));
  subst.
- simpl in C; inv C. EvalOp. destruct (Int64.cmpu c n1 n2); reflexivity.
- EvalOp. simpl. rewrite Val.swap_cmplu_bool. rewrite C; auto.
- EvalOp. simpl; rewrite C; auto.
- EvalOp. simpl; rewrite C; auto.
Qed.

Theorem eval_cmpl:
  forall c le a x b y v,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.cmpl c x y = Some v ->
  eval_expr ge sp e m le (cmpl c a b) v.
Proof.
  unfold cmpl; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_cmpl; eauto.
  unfold Val.cmpl in H1.
  destruct (Val.cmpl_bool c x y) as [vb|] eqn:C; simpl in H1; inv H1.
  destruct (is_longconst a) as [n1|] eqn:LC1; destruct (is_longconst b) as [n2|] eqn:LC2;
  try (assert (x = Vlong n1) by (eapply is_longconst_sound; eauto));
  try (assert (y = Vlong n2) by (eapply is_longconst_sound; eauto));
  subst.
- simpl in C; inv C. EvalOp. destruct (Int64.cmp c n1 n2); reflexivity.
- EvalOp. simpl. rewrite Val.swap_cmpl_bool. rewrite C; auto.
- EvalOp. simpl; rewrite C; auto.
- EvalOp. simpl; rewrite C; auto.
Qed.

Theorem eval_longoffloat: partial_unary_constructor_sound longoffloat Val.longoffloat.
Proof.
  unfold longoffloat; red; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_longoffloat; eauto.
  TrivialExists.
Qed.

Theorem eval_longuoffloat: partial_unary_constructor_sound longuoffloat Val.longuoffloat.
Proof.
  unfold longuoffloat; red; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_longuoffloat; eauto.
  TrivialExists.
Qed.

Theorem eval_floatoflong: partial_unary_constructor_sound floatoflong Val.floatoflong.
Proof.
  unfold floatoflong; red; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_floatoflong; eauto.
  TrivialExists.
Qed.

Theorem eval_floatoflongu: partial_unary_constructor_sound floatoflongu Val.floatoflongu.
Proof.
  unfold floatoflongu; red; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_floatoflongu; eauto.
  TrivialExists.
Qed.

Theorem eval_longofsingle: partial_unary_constructor_sound longofsingle Val.longofsingle.
Proof.
  unfold longofsingle; red; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_longofsingle; eauto.
  TrivialExists.
Qed.

Theorem eval_longuofsingle: partial_unary_constructor_sound longuofsingle Val.longuofsingle.
Proof.
  unfold longuofsingle; red; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_longuofsingle; eauto.
  TrivialExists.
Qed.

Theorem eval_singleoflong: partial_unary_constructor_sound singleoflong Val.singleoflong.
Proof.
  unfold singleoflong; red; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_singleoflong; eauto.
  TrivialExists.
Qed.

Theorem eval_singleoflongu: partial_unary_constructor_sound singleoflongu Val.singleoflongu.
Proof.
  unfold singleoflongu; red; intros. destruct Archi.splitlong eqn:SL.
  eapply SplitLongproof.eval_singleoflongu; eauto.
  TrivialExists.
Qed.

End CMCONSTR.
