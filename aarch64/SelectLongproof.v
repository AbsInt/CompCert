(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Xavier Leroy, Collège de France and INRIA Paris             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness of instruction selection for 64-bit integer operators *)

Require Import Coqlib Zbits.
Require Import AST Integers Floats Values Memory Globalenvs.
Require Import Cminor Op CminorSel.
Require Import SelectOp SelectLong SelectOpproof.

Local Open Scope cminorsel_scope.
Local Transparent Archi.ptr64.

(** * Correctness of the smart constructors *)

Section CMCONSTR.

Variable ge: genv.
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

(** ** Constants *)

Theorem eval_longconst:
  forall le n, eval_expr ge sp e m le (longconst n) (Vlong n).
Proof.
  intros; EvalOp.
Qed.

(** ** Conversions *)

Theorem eval_intoflong: unary_constructor_sound intoflong Val.loword.
Proof.
  unfold intoflong; red; intros until x; destruct (intoflong_match a); intros; InvEval; subst.
- TrivialExists.
- TrivialExists.
Qed.

Theorem eval_longofintu: unary_constructor_sound longofintu Val.longofintu.
Proof.
  unfold longofintu; red; intros until x; destruct (longofintu_match a); intros; InvEval; subst.
- TrivialExists.
- TrivialExists. simpl. unfold eval_extend. rewrite mk_amount64_eq by reflexivity.
  destruct x; simpl; auto. rewrite Int64.shl'_zero. auto.
Qed.

Theorem eval_longofint: unary_constructor_sound longofint Val.longofint.
Proof.
  unfold longofint; red; intros until x; destruct (longofint_match a); intros; InvEval; subst.
- TrivialExists.
- TrivialExists. simpl. unfold eval_extend. rewrite mk_amount64_eq by reflexivity.
  destruct x; simpl; auto. rewrite Int64.shl'_zero. auto.
Qed.

(** ** Addition, opposite, subtraction *)

Theorem eval_addlimm:
  forall n, unary_constructor_sound (addlimm n) (fun x => Val.addl x (Vlong n)).
Proof.
  red; unfold addlimm; intros until x.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
- subst n. intros. exists x; split; auto.
  destruct x; simpl; auto.
  rewrite Int64.add_zero; auto.
  rewrite Ptrofs.add_zero; auto.
- case (addlimm_match a); intros; InvEval; subst.
+ rewrite Int64.add_commut; TrivialExists.
+ TrivialExists. simpl. rewrite Ptrofs.add_commut, Genv.shift_symbol_address_64; auto.
+ econstructor; split. EvalOp. destruct sp; simpl; auto. 
  rewrite Ptrofs.add_assoc, (Ptrofs.add_commut m0); auto.
+ rewrite Val.addl_assoc, Int64.add_commut; TrivialExists.  
+ TrivialExists.
Qed.

Theorem eval_addl: binary_constructor_sound addl Val.addl.
Proof.
  red; intros until y.
  unfold addl; case (addl_match a b); intros; InvEval; subst.
- rewrite Val.addl_commut. apply eval_addlimm; auto.
- apply eval_addlimm; auto.
- replace (Val.addl (Val.addl v1 (Vlong n1)) (Val.addl v0 (Vlong n2)))
     with (Val.addl (Val.addl v1 v0) (Val.addl (Vlong n1) (Vlong n2))).
  apply eval_addlimm. EvalOp.
  repeat rewrite Val.addl_assoc. decEq. apply Val.addl_permut.
- TrivialExists. simpl. 
  rewrite Val.addl_commut, Val.addl_assoc. f_equal; f_equal. 
  destruct sp; simpl; auto. rewrite Ptrofs.add_assoc, (Ptrofs.add_commut n2). auto.
- TrivialExists. simpl.
  rewrite <- (Val.addl_commut v1), <- (Val.addl_commut (Val.addl v1 (Vlong n2))).
  rewrite Val.addl_assoc. f_equal; f_equal.
  destruct sp; simpl; auto. rewrite Ptrofs.add_assoc. auto.
- replace (Val.addl (Val.addl v1 (Vlong n1)) y)
     with (Val.addl (Val.addl v1 y) (Vlong n1)).
  apply eval_addlimm. EvalOp.
  repeat rewrite Val.addl_assoc. decEq. apply Val.addl_commut.
- rewrite <- Val.addl_assoc. apply eval_addlimm. EvalOp.
- rewrite Val.addl_commut. TrivialExists.
- TrivialExists.
- rewrite Val.addl_commut. TrivialExists.
- TrivialExists.
- rewrite Val.addl_commut. TrivialExists.
- TrivialExists.
- TrivialExists.
Qed.

Theorem eval_negl: unary_constructor_sound negl (fun v => Val.subl (Vlong Int64.zero) v).
Proof.
  red; intros until x; unfold negl. case (negl_match a); intros; InvEval; subst.
- TrivialExists.
- TrivialExists.
- TrivialExists.
Qed.

Theorem eval_subl: binary_constructor_sound subl Val.subl.
Proof.
  red; intros until y; unfold subl; case (subl_match a b); intros; InvEval; subst.
- rewrite Val.subl_addl_opp. apply eval_addlimm; auto.
- rewrite Val.subl_addl_l. rewrite Val.subl_addl_r.
  rewrite Val.addl_assoc. simpl. rewrite Int64.add_commut. rewrite <- Int64.sub_add_opp.
  apply eval_addlimm; EvalOp.
- rewrite Val.subl_addl_l. apply eval_addlimm; EvalOp.
- rewrite Val.subl_addl_r. apply eval_addlimm; EvalOp.
- TrivialExists.
- TrivialExists.
- TrivialExists.
- TrivialExists.
Qed.

(** ** Immediate shifts *)

Remark eval_shllimm_base: forall le a n x,
  eval_expr ge sp e m le a x ->
  Int.ltu n Int64.iwordsize' = true ->
  eval_expr ge sp e m le (shllimm_base a n) (Val.shll x (Vint n)).
Proof.
Local Opaque mk_amount64.
  unfold shlimm_base; intros; EvalOp. simpl. rewrite mk_amount64_eq by auto. auto.
Qed.

Theorem eval_shllimm:
  forall n, unary_constructor_sound (fun a => shllimm a n)
                                    (fun x => Val.shll x (Vint n)).
Proof.
  red; intros until x; unfold shllimm.
  predSpec Int.eq Int.eq_spec n Int.zero; [| destruct (Int.ltu n Int64.iwordsize') eqn:L]; simpl.
- intros; subst. exists x; split; auto. destruct x; simpl; auto. rewrite Int64.shl'_zero; auto.
- destruct (shllimm_match a); intros; InvEval; subst.
+ TrivialExists. simpl; rewrite L; auto.
+ destruct (Int.ltu (Int.add a n) Int64.iwordsize') eqn:L2.
* econstructor; split. eapply eval_shllimm_base; eauto.
  destruct v1; simpl; auto. rewrite a64_range; simpl. rewrite L, L2. 
  rewrite Int64.shl'_shl'; auto using a64_range.
* econstructor; split; [|eauto]. apply eval_shllimm_base; auto. EvalOp.
+ TrivialExists. simpl. rewrite mk_amount64_eq; auto.
+ TrivialExists. simpl. rewrite mk_amount64_eq; auto.
+ destruct (Int.ltu (Int.add a n) Int64.iwordsize') eqn:L2.
* TrivialExists. simpl. rewrite mk_amount64_eq by auto. 
  destruct (Val.zero_ext_l s v1); simpl; auto.
  rewrite a64_range; simpl; rewrite L, L2.
  rewrite Int64.shl'_shl'; auto using a64_range.
* econstructor; split. eapply eval_shllimm_base; eauto. EvalOp; simpl; eauto. auto.
+ destruct (Int.ltu (Int.add a n) Int64.iwordsize') eqn:L2.
* TrivialExists. simpl. rewrite mk_amount64_eq by auto. 
  destruct (Val.sign_ext_l s v1); simpl; auto.
  rewrite a64_range; simpl; rewrite L, L2.
  rewrite Int64.shl'_shl'; auto using a64_range.
* econstructor; split. eapply eval_shllimm_base; eauto. EvalOp; simpl; eauto. auto.
+ destruct (Int.ltu (Int.add a n) Int64.iwordsize') eqn:L2.
* TrivialExists. simpl. unfold eval_extend. rewrite mk_amount64_eq by auto. 
  destruct (match x0 with Xsgn32 => Val.longofint v1 | Xuns32 => Val.longofintu v1 end); simpl; auto.
  rewrite a64_range; simpl; rewrite L, L2.
  rewrite Int64.shl'_shl'; auto using a64_range.
* econstructor; split. eapply eval_shllimm_base; eauto. EvalOp; simpl; eauto. auto.
+ econstructor; eauto using eval_shllimm_base.
- intros; TrivialExists.
Qed.

Remark eval_shrluimm_base: forall le a n x,
  eval_expr ge sp e m le a x ->
  Int.ltu n Int64.iwordsize' = true ->
  eval_expr ge sp e m le (shrluimm_base a n) (Val.shrlu x (Vint n)).
Proof.
  unfold shrluimm_base; intros; EvalOp. simpl. rewrite mk_amount64_eq by auto. auto.
Qed.

Remark sub_shift_amount:
  forall y z,
  Int.ltu y Int64.iwordsize' = true -> Int.ltu z Int64.iwordsize' = true -> Int.unsigned y <= Int.unsigned z ->
  Int.ltu (Int.sub z y) Int64.iwordsize' = true.
Proof.
  intros. unfold Int.ltu; apply zlt_true.
  apply Int.ltu_inv in H. apply Int.ltu_inv in H0.
  change (Int.unsigned Int64.iwordsize') with Int64.zwordsize in *.
  unfold Int.sub; rewrite Int.unsigned_repr. omega.
  assert (Int64.zwordsize < Int.max_unsigned) by reflexivity. omega.
Qed.

Theorem eval_shrluimm:
  forall n, unary_constructor_sound (fun a => shrluimm a n)
                                    (fun x => Val.shrlu x (Vint n)).
Proof.
Local Opaque Int64.zwordsize.
  red; intros until x; unfold shrluimm.
  predSpec Int.eq Int.eq_spec n Int.zero; [| destruct (Int.ltu n Int64.iwordsize') eqn:L]; simpl.
- intros; subst. exists x; split; auto. destruct x; simpl; auto. rewrite Int64.shru'_zero; auto.
- destruct (shrluimm_match a); intros; InvEval; subst.
+ TrivialExists. simpl; rewrite L; auto.
+ destruct (Int.ltu n a) eqn:L2.
* assert (L3: Int.ltu (Int.sub a n) Int64.iwordsize' = true).
  { apply sub_shift_amount; auto using a64_range.
    apply Int.ltu_inv in L2. omega. }
  econstructor; split. EvalOp.
  destruct v1; simpl; auto. rewrite mk_amount64_eq, L3, a64_range by auto.
  simpl. rewrite L. rewrite Int64.shru'_shl', L2 by auto using a64_range. auto.
* assert (L3: Int.ltu (Int.sub n a) Int64.iwordsize' = true).
  { apply sub_shift_amount; auto using a64_range.
    unfold Int.ltu in L2. destruct zlt in L2; discriminate || omega. }
  econstructor; split. EvalOp.
  destruct v1; simpl; auto. rewrite mk_amount64_eq, L3, a64_range by auto.
  simpl. rewrite L. rewrite Int64.shru'_shl', L2 by auto using a64_range. auto.
+ destruct (Int.ltu (Int.add a n) Int64.iwordsize') eqn:L2.
* econstructor; split. eapply eval_shrluimm_base; eauto.
  destruct v1; simpl; auto. rewrite a64_range; simpl. rewrite L, L2. 
  rewrite Int64.shru'_shru'; auto using a64_range.
* econstructor; split; [|eauto]. apply eval_shrluimm_base; auto. EvalOp.
+ destruct (zlt (Int.unsigned n) s).
* econstructor; split. EvalOp. rewrite mk_amount64_eq by auto.
  destruct v1; simpl; auto. rewrite ! L; simpl.
  set (s' := s - Int.unsigned n).
  replace s with (s' + Int.unsigned n) by (unfold s'; omega).
  rewrite Int64.shru'_zero_ext. auto. unfold s'; omega.
* econstructor; split. EvalOp.
  destruct v1; simpl; auto. rewrite ! L; simpl.
  rewrite Int64.shru'_zero_ext_0 by omega. auto. 
+ econstructor; eauto using eval_shrluimm_base.
- intros; TrivialExists.
Qed.

Remark eval_shrlimm_base: forall le a n x,
  eval_expr ge sp e m le a x ->
  Int.ltu n Int64.iwordsize' = true ->
  eval_expr ge sp e m le (shrlimm_base a n) (Val.shrl x (Vint n)).
Proof.
  unfold shrlimm_base; intros; EvalOp. simpl. rewrite mk_amount64_eq by auto. auto.
Qed.

Theorem eval_shrlimm:
  forall n, unary_constructor_sound (fun a => shrlimm a n)
                                    (fun x => Val.shrl x (Vint n)).
Proof.
  red; intros until x; unfold shrlimm.
  predSpec Int.eq Int.eq_spec n Int.zero; [| destruct (Int.ltu n Int64.iwordsize') eqn:L]; simpl.
- intros; subst. exists x; split; auto. destruct x; simpl; auto. rewrite Int64.shr'_zero; auto.
- destruct (shrlimm_match a); intros; InvEval; subst.
+ TrivialExists. simpl; rewrite L; auto.
+ destruct (Int.ltu n a) eqn:L2.
* assert (L3: Int.ltu (Int.sub a n) Int64.iwordsize' = true).
  { apply sub_shift_amount; auto using a64_range.
    apply Int.ltu_inv in L2. omega. }
  econstructor; split. EvalOp.
  destruct v1; simpl; auto. rewrite mk_amount64_eq, L3, a64_range by auto.
  simpl. rewrite L. rewrite Int64.shr'_shl', L2 by auto using a64_range. auto.
* assert (L3: Int.ltu (Int.sub n a) Int64.iwordsize' = true).
  { apply sub_shift_amount; auto using a64_range.
    unfold Int.ltu in L2. destruct zlt in L2; discriminate || omega. }
  econstructor; split. EvalOp.
  destruct v1; simpl; auto. rewrite mk_amount64_eq, L3, a64_range by auto.
  simpl. rewrite L. rewrite Int64.shr'_shl', L2 by auto using a64_range. auto.
+ destruct (Int.ltu (Int.add a n) Int64.iwordsize') eqn:L2.
* econstructor; split. eapply eval_shrlimm_base; eauto.
  destruct v1; simpl; auto. rewrite a64_range; simpl. rewrite L, L2. 
  rewrite Int64.shr'_shr'; auto using a64_range.
* econstructor; split; [|eauto]. apply eval_shrlimm_base; auto. EvalOp.
+ destruct (zlt (Int.unsigned n) s && zlt s Int64.zwordsize) eqn:E.
* InvBooleans. econstructor; split. EvalOp. rewrite mk_amount64_eq by auto.
  destruct v1; simpl; auto. rewrite ! L; simpl.
  set (s' := s - Int.unsigned n).
  replace s with (s' + Int.unsigned n) by (unfold s'; omega).
  rewrite Int64.shr'_sign_ext. auto. unfold s'; omega. unfold s'; omega.
* econstructor; split; [|eauto]. apply eval_shrlimm_base; auto. EvalOp.
+ econstructor; eauto using eval_shrlimm_base.
- intros; TrivialExists.
Qed.

(** ** Multiplication *)

Lemma eval_mullimm_base:
  forall n, unary_constructor_sound (mullimm_base n) (fun x => Val.mull x (Vlong n)).
Proof.
  intros; red; intros; unfold mullimm_base.
  assert (DFL: exists v, eval_expr ge sp e m le (Eop Omull (Eop (Olongconst n) Enil ::: a ::: Enil)) v /\ Val.lessdef (Val.mull x (Vlong n)) v).
  { rewrite Val.mull_commut; TrivialExists. } 
  generalize (Int64.one_bits'_decomp n); generalize (Int64.one_bits'_range n);
  destruct (Int64.one_bits' n) as [ | i [ | j []]]; intros P Q.
- apply DFL.
- replace (Val.mull x (Vlong n)) with (Val.shll x (Vint i)).
  apply eval_shllimm; auto.
  simpl in Q. destruct x; auto; simpl. rewrite P by auto with coqlib.
  rewrite Q, Int64.add_zero, Int64.shl'_mul. auto.
- exploit (eval_shllimm i (x :: le) (Eletvar 0) x). constructor; auto. intros [v1 [A1 B1]].
  exploit (eval_shllimm j (x :: le) (Eletvar 0) x). constructor; auto. intros [v2 [A2 B2]].
  exploit (eval_addl (x :: le)). eexact A1. eexact A2. intros [v [A B]].
  exists v; split. econstructor; eauto.
  simpl in Q. rewrite Q, Int64.add_zero. eapply Val.lessdef_trans; [|eexact B].
  eapply Val.lessdef_trans; [|eapply Val.addl_lessdef; eauto].
  destruct x; simpl; auto; rewrite ! P by auto with coqlib.
  rewrite Int64.mul_add_distr_r, <- ! Int64.shl'_mul. auto.
- apply DFL.
Qed.

Theorem eval_mullimm:
  forall n, unary_constructor_sound (mullimm n) (fun x => Val.mull x (Vlong n)).
Proof.
  intros; red; intros until x; unfold mullimm.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
  intros. exists (Vlong Int64.zero); split. EvalOp.
  destruct x; simpl; auto. subst n. rewrite Int64.mul_zero. auto.
  predSpec Int64.eq Int64.eq_spec n Int64.one.
  intros. exists x; split; auto.
  destruct x; simpl; auto. subst n. rewrite Int64.mul_one. auto.
  case (mullimm_match a); intros; InvEval; subst.
- TrivialExists. simpl. rewrite Int64.mul_commut; auto.
- rewrite Val.mull_addl_distr_l.
  exploit eval_mullimm_base; eauto. instantiate (1 := n). intros [v' [A1 B1]].
  exploit (eval_addlimm (Int64.mul n n2) le (mullimm_base n t2) v'). auto. intros [v'' [A2 B2]].
  exists v''; split; auto. eapply Val.lessdef_trans. eapply Val.addl_lessdef; eauto.
  rewrite Val.mull_commut; auto.
- apply eval_mullimm_base; auto.
Qed.

Theorem eval_mull: binary_constructor_sound mull Val.mull.
Proof.
  red; intros until y; unfold mull; case (mull_match a b); intros; InvEval; subst.
- rewrite Val.mull_commut. apply eval_mullimm; auto.
- apply eval_mullimm; auto.
- TrivialExists.
Qed.

Theorem eval_mullhu: 
  forall n, unary_constructor_sound (fun a => mullhu a n) (fun v => Val.mullhu v (Vlong n)).
Proof.
  unfold mullhu; red; intros; TrivialExists.
Qed.

Theorem eval_mullhs: 
  forall n, unary_constructor_sound (fun a => mullhs a n) (fun v => Val.mullhs v (Vlong n)).
Proof.
  unfold mullhs; red; intros; TrivialExists.
Qed.

(** Integer conversions *)

Theorem eval_zero_ext_l:
  forall sz, 0 <= sz -> unary_constructor_sound (zero_ext_l sz) (Val.zero_ext_l sz).
Proof.
  intros; red; intros until x; unfold zero_ext_l; case (zero_ext_l_match a); intros; InvEval; subst.
- TrivialExists.
- TrivialExists.
- destruct (zlt (Int.unsigned a0) sz).
+ econstructor; split. EvalOp. destruct v1; simpl; auto. rewrite a64_range; simpl.
  apply Val.lessdef_same. f_equal. rewrite Int64.shl'_zero_ext by omega. f_equal. omega.
+ TrivialExists.
- TrivialExists.
Qed.

(** Bitwise not, and, or, xor *)

Theorem eval_notl: unary_constructor_sound notl Val.notl.
Proof.
  assert (INV: forall v, Val.lessdef (Val.notl (Val.notl v)) v).
  { destruct v; auto. simpl; rewrite Int64.not_involutive; auto. } 
  unfold notl; red; intros until x; case (notl_match a); intros; InvEval; subst.
- TrivialExists.
- TrivialExists.
- exists v1; auto.
- exists (eval_shiftl s v1 a0); split; auto. EvalOp.
- econstructor; split. EvalOp. 
  destruct v1; simpl; auto; destruct v0; simpl; auto.
  rewrite Int64.not_and_or_not, Int64.not_involutive, Int64.or_commut. auto.
- econstructor; split. EvalOp. 
  destruct v1; simpl; auto; destruct v0; simpl; auto.
  rewrite Int64.not_or_and_not, Int64.not_involutive, Int64.and_commut. auto.
- econstructor; split. EvalOp.
  destruct v1; simpl; auto; destruct v0; simpl; auto.
  unfold Int64.not; rewrite ! Int64.xor_assoc. auto.
- econstructor; split. EvalOp.
  destruct v1; simpl; auto; destruct v0; simpl; auto.
  unfold Int64.not; rewrite ! Int64.xor_assoc, Int64.xor_idem, Int64.xor_zero. auto.
- TrivialExists.
Qed.

Lemma eval_andlimm_base:
  forall n, unary_constructor_sound (andlimm_base n) (fun x => Val.andl x (Vlong n)).
Proof.
  intros; red; intros. unfold andlimm_base.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
  exists (Vlong Int64.zero); split. EvalOp.
  destruct x; simpl; auto. subst n. rewrite Int64.and_zero. auto.
  predSpec Int64.eq Int64.eq_spec n Int64.mone.
  exists x; split; auto.
  subst. destruct x; simpl; auto. rewrite Int64.and_mone; auto.
  destruct (Z_is_power2m1 (Int64.unsigned n)) as [s|] eqn:P.
  assert (0 <= s) by (eapply Z_is_power2m1_nonneg; eauto).
  rewrite <- (Int64.repr_unsigned n), (Z_is_power2m1_sound _ _ P), <- Val.zero_ext_andl by auto.
  apply eval_zero_ext_l; auto.
  TrivialExists.
Qed.

Theorem eval_andlimm:
  forall n, unary_constructor_sound (andlimm n) (fun x => Val.andl x (Vlong n)).
Proof.
  intros; red; intros until x. unfold andlimm.
  case (andlimm_match a); intros; InvEval; subst.
- rewrite Int64.and_commut; TrivialExists.
- rewrite Val.andl_assoc, Int64.and_commut. apply eval_andlimm_base; auto.
- destruct (zle 0 s).
+ replace (Val.zero_ext_l s v1) with (Val.andl v1 (Vlong (Int64.repr (two_p s - 1)))).
  rewrite Val.andl_assoc, Int64.and_commut.
  apply eval_andlimm_base; auto.
  destruct v1; simpl; auto. rewrite Int64.zero_ext_and by auto. auto. 
+ apply eval_andlimm_base. EvalOp.
- apply eval_andlimm_base; auto.
Qed.

Theorem eval_andl: binary_constructor_sound andl Val.andl.
Proof.
  red; intros until y; unfold andl; case (andl_match a b); intros; InvEval; subst.
- rewrite Val.andl_commut; apply eval_andlimm; auto.
- apply eval_andlimm; auto.
- rewrite Val.andl_commut; TrivialExists.
- TrivialExists.
- rewrite Val.andl_commut; TrivialExists.
- TrivialExists.
- rewrite Val.andl_commut; TrivialExists.
- TrivialExists.
- TrivialExists.
Qed.

Theorem eval_orlimm:
  forall n, unary_constructor_sound (orlimm n) (fun x => Val.orl x (Vlong n)).
Proof.
  intros; red; intros until x. unfold orlimm.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
  intros. subst. exists x; split; auto.
  destruct x; simpl; auto. rewrite Int64.or_zero; auto.
  predSpec Int64.eq Int64.eq_spec n Int64.mone.
  intros. exists (Vlong Int64.mone); split. EvalOp.
  destruct x; simpl; auto. subst n. rewrite Int64.or_mone. auto.
  destruct (orlimm_match a); intros; InvEval; subst.
- rewrite Int64.or_commut; TrivialExists.
- rewrite Val.orl_assoc, Int64.or_commut; TrivialExists.
- TrivialExists.
Qed.

Theorem eval_orl: binary_constructor_sound orl Val.orl.
Proof.
  red; intros until y; unfold orl; case (orl_match a b); intros; InvEval; subst.
- rewrite Val.orl_commut. apply eval_orlimm; auto.
- apply eval_orlimm; auto.
- rewrite Val.orl_commut; TrivialExists.
- TrivialExists.
- rewrite Val.orl_commut; TrivialExists.
- TrivialExists.
- (* shl - shru *)
  destruct (Int.eq (Int.add a1 a2) Int64.iwordsize' && same_expr_pure t1 t2) eqn:?.
+ InvBooleans. apply Int.same_if_eq in H.
  exploit eval_same_expr; eauto. intros [EQ1 EQ2]. subst.
  econstructor; split. EvalOp.
  destruct v0; simpl; auto. rewrite ! a64_range. simpl. rewrite <- Int64.or_ror'; auto using a64_range.
+ TrivialExists.
- (* shru - shl *)
  destruct (Int.eq (Int.add a2 a1) Int64.iwordsize' && same_expr_pure t1 t2) eqn:?.
+ InvBooleans. apply Int.same_if_eq in H.
  exploit eval_same_expr; eauto. intros [EQ1 EQ2]. subst.
  econstructor; split. EvalOp.
  destruct v0; simpl; auto. rewrite ! a64_range. simpl.
  rewrite Int64.or_commut, <- Int64.or_ror'; auto using a64_range.
+ TrivialExists.
- rewrite Val.orl_commut; TrivialExists.
- TrivialExists.
- TrivialExists.
Qed.

Lemma eval_xorlimm_base:
  forall n, unary_constructor_sound (xorlimm_base n) (fun x => Val.xorl x (Vlong n)).
Proof.
  intros; red; intros. unfold xorlimm_base.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
  intros. exists x; split. auto.
  destruct x; simpl; auto. subst n. rewrite Int64.xor_zero. auto.
  predSpec Int64.eq Int64.eq_spec n Int64.mone.
  subst n. change (Val.xorl x (Vlong Int64.mone)) with (Val.notl x). apply eval_notl; auto.
  TrivialExists.
Qed.

Theorem eval_xorlimm:
  forall n, unary_constructor_sound (xorlimm n) (fun x => Val.xorl x (Vlong n)).
Proof.
  intros; red; intros until x. unfold xorlimm.
  destruct (xorlimm_match a); intros; InvEval; subst.
- rewrite Int64.xor_commut; TrivialExists.
- rewrite Val.xorl_assoc; simpl. rewrite (Int64.xor_commut n2). apply eval_xorlimm_base; auto.
- apply eval_xorlimm_base; auto.
Qed.

Theorem eval_xorl: binary_constructor_sound xorl Val.xorl.
Proof.
  red; intros until y; unfold xorl; case (xorl_match a b); intros; InvEval; subst.
- rewrite Val.xorl_commut; apply eval_xorlimm; auto.
- apply eval_xorlimm; auto.
- rewrite Val.xorl_commut; TrivialExists.
- TrivialExists.
- rewrite Val.xorl_commut; TrivialExists.
- TrivialExists.
- rewrite Val.xorl_commut; TrivialExists.
- TrivialExists.
- TrivialExists.
Qed.

(** ** Integer division and modulus *)

Theorem eval_divls_base: partial_binary_constructor_sound divls_base Val.divls.
Proof.
  red; intros; unfold divls_base; TrivialExists.
Qed.

Theorem eval_modls_base: partial_binary_constructor_sound modls_base Val.modls.
Proof.
  red; intros; unfold modls_base, modl_aux.
  exploit Val.modls_divls; eauto. intros (q & A & B). subst z.
  TrivialExists. repeat (econstructor; eauto with evalexpr). exact A.
Qed.

Theorem eval_divlu_base: partial_binary_constructor_sound divlu_base Val.divlu.
Proof.
  red; intros; unfold divlu_base; TrivialExists.
Qed.

Theorem eval_modlu_base: partial_binary_constructor_sound modlu_base Val.modlu.
Proof.
  red; intros; unfold modlu_base, modl_aux.
  exploit Val.modlu_divlu; eauto. intros (q & A & B). subst z.
  TrivialExists. repeat (econstructor; eauto with evalexpr). exact A.
Qed.

Theorem eval_shrxlimm:
  forall le a n x z,
  eval_expr ge sp e m le a x ->
  Val.shrxl x (Vint n) = Some z ->
  exists v, eval_expr ge sp e m le (shrxlimm a n) v /\ Val.lessdef z v.
Proof.
  intros; unfold shrxlimm. 
  predSpec Int.eq Int.eq_spec n Int.zero.
- subst n. exists x; split; auto.
  destruct x; simpl in H0; try discriminate.
  change (Int.ltu Int.zero (Int.repr 63)) with true in H0; inv H0.
  rewrite Int64.shrx'_zero. auto.
- TrivialExists.
Qed.

(** General shifts *)

Theorem eval_shll: binary_constructor_sound shll Val.shll.
Proof.
  red; intros until y; unfold shll; case (shll_match b); intros.
  InvEval. apply eval_shllimm; auto.
  TrivialExists.
Qed.

Theorem eval_shrl: binary_constructor_sound shrl Val.shrl.
Proof.
  red; intros until y; unfold shrl; case (shrl_match b); intros.
  InvEval. apply eval_shrlimm; auto.
  TrivialExists.
Qed.

Theorem eval_shrlu: binary_constructor_sound shrlu Val.shrlu.
Proof.
  red; intros until y; unfold shrlu; case (shrlu_match b); intros.
  InvEval. apply eval_shrluimm; auto.
  TrivialExists.
Qed.

(** Comparisons *)

Remark option_map_of_bool_inv: forall ov w,
  option_map Val.of_bool ov = Some w -> Val.of_optbool ov = w.
Proof.
  intros. destruct ov; inv H; auto.
Qed.

Section COMP_IMM.

Variable default: comparison -> int64 -> condition.
Variable intsem: comparison -> int64 -> int64 -> bool.
Variable sem: comparison -> val -> val -> option val.

Hypothesis sem_int: forall c x y, 
  sem c (Vlong x) (Vlong y) = Some (Val.of_bool (intsem c x y)).
Hypothesis sem_undef: forall c v,
  sem c Vundef v = None.
Hypothesis sem_eq: forall x y,
  sem Ceq (Vlong x) (Vlong y) = Some (Val.of_bool (Int64.eq x y)).
Hypothesis sem_ne: forall x y,
  sem Cne (Vlong x) (Vlong y) = Some (Val.of_bool (negb (Int64.eq x y))).
Hypothesis sem_default: forall c v n,
  sem c v (Vlong n) = option_map Val.of_bool (eval_condition (default c n) (v :: nil) m).

Lemma eval_complimm_default: forall le a x c n2 v,
  sem c x (Vlong n2) = Some v ->
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le (Eop (Ocmp (default c n2)) (a:::Enil)) v.
Proof.
  intros. EvalOp. simpl. rewrite sem_default in H. apply option_map_of_bool_inv in H.
  congruence.
Qed.

Lemma eval_complimm:
  forall le c a n2 x v,
  eval_expr ge sp e m le a x ->
  sem c x (Vlong n2) = Some v ->
  eval_expr ge sp e m le (complimm default intsem c a n2) v.
Proof.
  intros until x; unfold complimm; case (complimm_match c a); intros; InvEval; subst.
- (* constant *)
  rewrite sem_int in H0; inv H0. EvalOp. destruct (intsem c0 n1 n2); auto.
- (* mask zero *)
  predSpec Int64.eq Int64.eq_spec n2 Int64.zero.
+ subst n2. destruct v1; simpl in H0; rewrite ? sem_undef, ? sem_eq in H0; inv H0.
  EvalOp.
+ eapply eval_complimm_default; eauto. EvalOp. 
- (* mask not zero *)
  predSpec Int64.eq Int64.eq_spec n2 Int64.zero.
+ subst n2. destruct v1; simpl in H0; rewrite ? sem_undef, ? sem_ne in H0; inv H0.
  EvalOp.
+ eapply eval_complimm_default; eauto. EvalOp.
- (* default *)
  eapply eval_complimm_default; eauto.
Qed.

Hypothesis sem_swap:
  forall c x y, sem (swap_comparison c) x y = sem c y x.

Lemma eval_complimm_swap:
  forall le c a n2 x v,
  eval_expr ge sp e m le a x ->
  sem c (Vlong n2) x = Some v ->
  eval_expr ge sp e m le (complimm default intsem (swap_comparison c) a n2) v.
Proof.
  intros. eapply eval_complimm; eauto. rewrite sem_swap; auto.
Qed.

End COMP_IMM.

Theorem eval_cmpl:
  forall c le a x b y v,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.cmpl c x y = Some v ->
  eval_expr ge sp e m le (cmpl c a b) v.
Proof.
  intros until y; unfold cmpl; case (cmpl_match a b); intros; InvEval; subst.
- apply eval_complimm_swap with (sem := Val.cmpl) (x := y); auto.
  intros; unfold Val.cmpl; rewrite Val.swap_cmpl_bool; auto. 
- apply eval_complimm with (sem := Val.cmpl) (x := x); auto.
- EvalOp. simpl. rewrite Val.swap_cmpl_bool. apply option_map_of_bool_inv in H1. congruence.
- EvalOp. simpl. apply option_map_of_bool_inv in H1. congruence.
- EvalOp. simpl. apply option_map_of_bool_inv in H1. congruence.
Qed.

Theorem eval_cmplu:
  forall c le a x b y v,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.cmplu (Mem.valid_pointer m) c x y = Some v ->
  eval_expr ge sp e m le (cmplu c a b) v.
Proof.
  intros until y; unfold cmplu; case (cmplu_match a b); intros; InvEval; subst.
- apply eval_complimm_swap with (sem := Val.cmplu (Mem.valid_pointer m)) (x := y); auto.
  intros; unfold Val.cmplu; rewrite Val.swap_cmplu_bool; auto. 
- apply eval_complimm with (sem := Val.cmplu (Mem.valid_pointer m)) (x := x); auto.
- EvalOp. simpl. rewrite Val.swap_cmplu_bool. apply option_map_of_bool_inv in H1. congruence.
- EvalOp. simpl. apply option_map_of_bool_inv in H1. congruence.
- EvalOp. simpl. apply option_map_of_bool_inv in H1. congruence.
Qed.


(** Floating-point conversions *)

Theorem eval_longoffloat: partial_unary_constructor_sound longoffloat Val.longoffloat.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_longuoffloat: partial_unary_constructor_sound longuoffloat Val.longuoffloat.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_floatoflong: partial_unary_constructor_sound floatoflong Val.floatoflong.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_floatoflongu: partial_unary_constructor_sound floatoflongu Val.floatoflongu.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_longofsingle: partial_unary_constructor_sound longofsingle Val.longofsingle.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_longuofsingle: partial_unary_constructor_sound longuofsingle Val.longuofsingle.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_singleoflong: partial_unary_constructor_sound singleoflong Val.singleoflong.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_singleoflongu: partial_unary_constructor_sound singleoflongu Val.singleoflongu.
Proof.
  red; intros; TrivialExists.
Qed.

End CMCONSTR.
