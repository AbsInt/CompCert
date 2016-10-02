(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                 Xavier Leroy, INRIA Paris                           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness of instruction selection for 64-bit integer operations *)

Require Import String Coqlib Maps Integers Floats Errors.
Require Archi.
Require Import AST Values Memory Globalenvs Events.
Require Import Cminor Op CminorSel.
Require Import SelectOp SelectOpproof SplitLong SplitLongproof.
Require Import SelectLong.

Open Local Scope cminorsel_scope.
Open Local Scope string_scope.

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

Lemma is_longconst_sound_1:
  forall a n, is_longconst a = Some n -> a = Eop (Olongconst n) Enil.
Proof with (try discriminate).
  unfold is_longconst; intros. destruct a... destruct o... destruct e0... congruence.
Qed.

Lemma is_longconst_sound:
  forall v a n le,
  is_longconst a = Some n -> eval_expr ge sp e m le a v -> v = Vlong n.
Proof.
  intros. rewrite (is_longconst_sound_1 _ _ H) in H0. InvEval. auto.
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

Theorem eval_notl: unary_constructor_sound notl Val.notl.
Proof.
  unfold notl; destruct Archi.splitlong. apply SplitLongproof.eval_notl.
  red; intros. destruct (notl_match a). 
- InvEval. econstructor; split. apply eval_longconst. auto.
- InvEval. subst. exists v1; split; auto. destruct v1; simpl; auto. rewrite Int64.not_involutive; auto.
- TrivialExists. 
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
Admitted.

Theorem eval_orlimm: forall n, unary_constructor_sound (orlimm n) (fun v => Val.orl v (Vlong n)).
Admitted.

Theorem eval_orl: binary_constructor_sound orl Val.orl.
Admitted.

Theorem eval_xorlimm: forall n, unary_constructor_sound (xorlimm n) (fun v => Val.xorl v (Vlong n)).
Admitted.

Theorem eval_xorl: binary_constructor_sound xorl Val.xorl.
Admitted.

Theorem eval_shllimm: forall n, unary_constructor_sound (fun e => shllimm e n) (fun v => Val.shll v (Vint n)).
Admitted.

Theorem eval_shrluimm: forall n, unary_constructor_sound (fun e => shrluimm e n) (fun v => Val.shrlu v (Vint n)).
Admitted.

Theorem eval_shrlimm: forall n, unary_constructor_sound (fun e => shrlimm e n) (fun v => Val.shrl v (Vint n)).
Admitted.

Theorem eval_shll: binary_constructor_sound shll Val.shll.
Admitted.

Theorem eval_shrlu: binary_constructor_sound shrlu Val.shrlu.
Admitted.

Theorem eval_shrl: binary_constructor_sound shrl Val.shrl.
Admitted.

Theorem eval_negl: unary_constructor_sound negl Val.negl.
Admitted.

Theorem eval_addlimm: forall n, unary_constructor_sound (addlimm n) (fun v => Val.addl v (Vlong n)).
Proof.
  unfold addlimm; intros; red; intros. 
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
  subst. exists x; split; auto.
  destruct x; simpl; auto.
  rewrite Int64.add_zero; auto.
  destruct Archi.ptr64; auto. rewrite Ptrofs.add_zero; auto. 
  destruct (addlimm_match a); InvEval.
- econstructor; split. apply eval_longconst. rewrite Int64.add_commut; auto.
- inv H. simpl in H6. TrivialExists. simpl.
  erewrite eval_offset_addressing_total_64 by eauto. rewrite Int64.repr_signed; auto.
- TrivialExists. simpl. rewrite Int64.repr_signed; auto.
Qed.

Theorem eval_addl: binary_constructor_sound addl Val.addl.
Proof.
  assert (A: forall x y, Int64.repr (x + y) = Int64.add (Int64.repr x) (Int64.repr y)).
  { intros; apply Int64.eqm_samerepr; auto with ints. }
  assert (B: forall id ofs n, Archi.ptr64 = true ->
             Genv.symbol_address ge id (Ptrofs.add ofs (Ptrofs.repr n)) =
             Val.addl (Genv.symbol_address ge id ofs) (Vlong (Int64.repr n))).
  { intros. replace (Ptrofs.repr n) with (Ptrofs.of_int64 (Int64.repr n)) by auto with ptrofs. 
    apply Genv.shift_symbol_address_64; auto. }
  unfold addl. destruct Archi.splitlong eqn:SL.
  apply SplitLongproof.eval_addl. apply Archi.splitlong_ptr32; auto. 
  red; intros; destruct (addl_match a b); InvEval.
- rewrite Val.addl_commut. apply eval_addlimm; auto.
- apply eval_addlimm; auto.
- subst. TrivialExists. simpl. rewrite A, Val.addl_permut_4. auto.
- subst. TrivialExists. simpl. rewrite A, Val.addl_assoc. decEq; decEq. rewrite Val.addl_permut. auto.
- subst. TrivialExists. simpl. rewrite A, Val.addl_permut_4. rewrite <- Val.addl_permut. rewrite <- Val.addl_assoc. auto.
- subst. TrivialExists. simpl. rewrite Val.addl_commut; auto.
- subst. TrivialExists.
- subst. TrivialExists. simpl. rewrite ! Val.addl_assoc. rewrite (Val.addl_commut y). auto.
- subst. TrivialExists. simpl. rewrite ! Val.addl_assoc. auto.
- TrivialExists. simpl. destruct x; destruct y; simpl; auto.
    rewrite Int64.add_zero; auto.
    destruct Archi.ptr64 eqn:SF; simpl; auto. rewrite SF. rewrite Ptrofs.add_assoc, Ptrofs.add_zero. auto.
    destruct Archi.ptr64 eqn:SF; simpl; auto. rewrite SF. rewrite Ptrofs.add_assoc, Ptrofs.add_zero. auto.
Qed.

Theorem eval_subl: binary_constructor_sound subl Val.subl.
Proof.
  unfold subl. destruct Archi.splitlong eqn:SL.
  apply SplitLongproof.eval_subl. apply Archi.splitlong_ptr32; auto.
  red; intros; destruct (subl_match a b); InvEval.
- rewrite Val.subl_addl_opp. apply eval_addlimm; auto.
- subst. rewrite Val.subl_addl_l. rewrite Val.subl_addl_r.
  rewrite Val.addl_assoc. simpl. rewrite Int64.add_commut. rewrite <- Int64.sub_add_opp.
  replace (Int64.repr (n1 - n2)) with (Int64.sub (Int64.repr n1) (Int64.repr n2)).
  apply eval_addlimm; EvalOp.
  apply Int64.eqm_samerepr; auto with ints.
- subst. rewrite Val.subl_addl_l. apply eval_addlimm; EvalOp.
- subst. rewrite Val.subl_addl_r.
  replace (Int64.repr (-n2)) with (Int64.neg (Int64.repr n2)).
  apply eval_addlimm; EvalOp.
  apply Int64.eqm_samerepr; auto with ints.
- TrivialExists.
Qed.

Theorem eval_mullimm_base: forall n, unary_constructor_sound (mullimm_base n) (fun v => Val.mull v (Vlong n)).
Admitted.

Theorem eval_mullimm: forall n, unary_constructor_sound (mullimm n) (fun v => Val.mull v (Vlong n)).
Admitted.

Theorem eval_mull: binary_constructor_sound mull Val.mull.
Admitted.

Theorem eval_shrxlimm:
  forall le a n x z,
  eval_expr ge sp e m le a x ->
  Val.shrxl x (Vint n) = Some z ->
  exists v, eval_expr ge sp e m le (shrxlimm a n) v /\ Val.lessdef z v.
Proof.
  unfold shrxlimm; intros. destruct Archi.splitlong eqn:SL.
+ eapply SplitLongproof.eval_shrxlimm; eauto. apply Archi.splitlong_ptr32; auto.
+ predSpec Int.eq Int.eq_spec n Int.zero.
- subst n. destruct x; simpl in H0; inv H0. econstructor; split; eauto.
  change (Int.ltu Int.zero (Int.repr 63)) with true. simpl. rewrite Int64.shrx'_zero; auto.
- TrivialExists.
Qed.

Theorem eval_divls_base: partial_binary_constructor_sound divls_base Val.divls.
Admitted.

Theorem eval_modls_base: partial_binary_constructor_sound modls_base Val.modls.
Admitted.
  
Theorem eval_divlu_base: partial_binary_constructor_sound divlu_base Val.divlu.
Admitted.

Theorem eval_modlu_base: partial_binary_constructor_sound modlu_base Val.modlu.
Admitted.

Theorem eval_cmplu:
  forall c le a x b y v,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.cmplu (Mem.valid_pointer m) c x y = Some v ->
  eval_expr ge sp e m le (cmplu c a b) v.
Proof.
  unfold cmplu; intros. destruct Archi.splitlong eqn:SL. 
  eapply SplitLongproof.eval_cmplu; eauto. apply Archi.splitlong_ptr32; auto.
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
Admitted.  

Theorem eval_floatoflong: partial_unary_constructor_sound floatoflong Val.floatoflong.
Admitted.  

Theorem eval_longofsingle: partial_unary_constructor_sound longofsingle Val.longofsingle.
Admitted.  

Theorem eval_singleoflong: partial_unary_constructor_sound singleoflong Val.singleoflong.
Admitted.  

End CMCONSTR.
