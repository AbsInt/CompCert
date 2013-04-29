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

(** Correctness of instruction selection for 64-bit integer operations *)

Require Import Coqlib.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.
Require Import SelectOpproof.
Require Import SelectLong.

Open Local Scope cminorsel_scope.

(** * Axiomatization of the helper functions *)

Section HELPERS.

Context {F V: Type} (ge: Genv.t (AST.fundef F) V).

Definition helper_implements (id: ident) (sg: signature) (vargs: list val) (vres: val) : Prop :=
  exists b, exists ef,
     Genv.find_symbol ge id = Some b
  /\ Genv.find_funct_ptr ge b = Some (External ef)
  /\ ef_sig ef = sg
  /\ forall m, external_call ef ge vargs m E0 vres m.

Definition builtin_implements (id: ident) (sg: signature) (vargs: list val) (vres: val) : Prop :=
  forall m, external_call (EF_builtin id sg) ge vargs m E0 vres m.

Definition i64_helpers_correct (hf: helper_functions) : Prop :=
    (forall x z, Val.longoffloat x = Some z -> helper_implements hf.(i64_dtos) sig_f_l (x::nil) z)
  /\(forall x z, Val.longuoffloat x = Some z -> helper_implements hf.(i64_dtou) sig_f_l (x::nil) z)
  /\(forall x z, Val.floatoflong x = Some z -> helper_implements hf.(i64_stod) sig_l_f (x::nil) z)
  /\(forall x z, Val.floatoflongu x = Some z -> helper_implements hf.(i64_utod) sig_l_f (x::nil) z)
  /\(forall x, builtin_implements hf.(i64_neg) sig_l_l (x::nil) (Val.negl x))
  /\(forall x y, builtin_implements hf.(i64_add) sig_ll_l (x::y::nil) (Val.addl x y))
  /\(forall x y, builtin_implements hf.(i64_sub) sig_ll_l (x::y::nil) (Val.subl x y))
  /\(forall x y, builtin_implements hf.(i64_mul) sig_ii_l (x::y::nil) (Val.mull' x y))
  /\(forall x y z, Val.divls x y = Some z -> helper_implements hf.(i64_sdiv) sig_ll_l (x::y::nil) z)
  /\(forall x y z, Val.divlu x y = Some z -> helper_implements hf.(i64_udiv) sig_ll_l (x::y::nil) z)
  /\(forall x y z, Val.modls x y = Some z -> helper_implements hf.(i64_smod) sig_ll_l (x::y::nil) z)
  /\(forall x y z, Val.modlu x y = Some z -> helper_implements hf.(i64_umod) sig_ll_l (x::y::nil) z)
  /\(forall x y, helper_implements hf.(i64_shl) sig_li_l (x::y::nil) (Val.shll x y))
  /\(forall x y, helper_implements hf.(i64_shr) sig_li_l (x::y::nil) (Val.shrlu x y))
  /\(forall x y, helper_implements hf.(i64_sar) sig_li_l (x::y::nil) (Val.shrl x y)).

End HELPERS.

(** * Correctness of the instruction selection functions for 64-bit operators *)

Section CMCONSTR.

Variable hf: helper_functions.
Variable ge: genv.
Hypothesis HELPERS: i64_helpers_correct ge hf.
Variable sp: val.
Variable e: env.
Variable m: mem.

Ltac UseHelper :=
  red in HELPERS;
  repeat (eauto; match goal with | [ H: _ /\ _ |- _ ] => destruct H end).

Lemma eval_helper:
  forall le id sg args vargs vres,
  eval_exprlist ge sp e m le args vargs ->
  helper_implements ge id sg vargs vres ->
  eval_expr ge sp e m le (Eexternal id sg args) vres.
Proof.
  intros. destruct H0 as (b & ef & A & B & C & D). econstructor; eauto.
Qed.

Corollary eval_helper_1:
  forall le id sg arg1 varg1 vres,
  eval_expr ge sp e m le arg1 varg1 ->
  helper_implements ge id sg (varg1::nil) vres ->
  eval_expr ge sp e m le (Eexternal id sg (arg1 ::: Enil)) vres.
Proof.
  intros. eapply eval_helper; eauto. constructor; auto. constructor.
Qed.

Corollary eval_helper_2:
  forall le id sg arg1 arg2 varg1 varg2 vres,
  eval_expr ge sp e m le arg1 varg1 ->
  eval_expr ge sp e m le arg2 varg2 ->
  helper_implements ge id sg (varg1::varg2::nil) vres ->
  eval_expr ge sp e m le (Eexternal id sg (arg1 ::: arg2 ::: Enil)) vres.
Proof.
  intros. eapply eval_helper; eauto. constructor; auto. constructor; auto. constructor.
Qed.

Remark eval_builtin_1:
  forall le id sg arg1 varg1 vres,
  eval_expr ge sp e m le arg1 varg1 ->
  builtin_implements ge id sg (varg1::nil) vres ->
  eval_expr ge sp e m le (Ebuiltin (EF_builtin id sg) (arg1 ::: Enil)) vres.
Proof.
  intros. econstructor. econstructor. eauto. constructor. apply H0. 
Qed.

Remark eval_builtin_2:
  forall le id sg arg1 arg2 varg1 varg2 vres,
  eval_expr ge sp e m le arg1 varg1 ->
  eval_expr ge sp e m le arg2 varg2 ->
  builtin_implements ge id sg (varg1::varg2::nil) vres ->
  eval_expr ge sp e m le (Ebuiltin (EF_builtin id sg) (arg1 ::: arg2 ::: Enil)) vres.
Proof.
  intros. econstructor. constructor; eauto. constructor; eauto. constructor. apply H1.
Qed.

Definition unary_constructor_sound (cstr: expr -> expr) (sem: val -> val) : Prop :=
  forall le a x,
  eval_expr ge sp e m le a x ->
  exists v, eval_expr ge sp e m le (cstr a) v /\ Val.lessdef (sem x) v.

Definition binary_constructor_sound (cstr: expr -> expr -> expr) (sem: val -> val -> val) : Prop :=
  forall le a x b y,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  exists v, eval_expr ge sp e m le (cstr a b) v /\ Val.lessdef (sem x y) v.

Ltac EvalOp :=
  eauto;
  match goal with
  | [ |- eval_exprlist _ _ _ _ _ Enil _ ] => constructor
  | [ |- eval_exprlist _ _ _ _ _ (_:::_) _ ] => econstructor; EvalOp
  | [ |- eval_expr _ _ _ _ _ (Eletvar _) _ ] => constructor; simpl; eauto
  | [ |- eval_expr _ _ _ _ _ (Elet _ _) _ ] => econstructor; EvalOp
  | [ |- eval_expr _ _ _ _ _ (lift _) _ ] => apply eval_lift; EvalOp
  | [ |- eval_expr _ _ _ _ _ _ _ ] => eapply eval_Eop; [EvalOp | simpl; eauto]
  | _ => idtac
  end.

Lemma eval_splitlong:
  forall le a f v sem,
  (forall le a b x y,
   eval_expr ge sp e m le a x ->
   eval_expr ge sp e m le b y ->
   exists v, eval_expr ge sp e m le (f a b) v /\
             (forall p q, x = Vint p -> y = Vint q -> v = sem (Vlong (Int64.ofwords p q)))) ->
  match v with Vlong _ => True | _ => sem v = Vundef end ->
  eval_expr ge sp e m le a v ->
  exists v', eval_expr ge sp e m le (splitlong a f) v' /\ Val.lessdef (sem v) v'.
Proof.
  intros until sem; intros EXEC UNDEF.
  unfold splitlong. case (splitlong_match a); intros.
- InvEval. subst v.
  exploit EXEC. eexact H2. eexact H3. intros [v' [A B]]. 
  exists v'; split. auto.
  destruct v1; simpl in *; try (rewrite UNDEF; auto). 
  destruct v0; simpl in *; try (rewrite UNDEF; auto). 
  erewrite B; eauto.
- exploit (EXEC (v :: le) (Eop Ohighlong (Eletvar 0 ::: Enil)) (Eop Olowlong (Eletvar 0 ::: Enil))).
  EvalOp. EvalOp.
  intros [v' [A B]].
  exists v'; split. econstructor; eauto.
  destruct v; try (rewrite UNDEF; auto). erewrite B; simpl; eauto. rewrite Int64.ofwords_recompose. auto.
Qed.

Lemma eval_splitlong_strict:
  forall le a f va v,
  eval_expr ge sp e m le a (Vlong va) ->
  (forall le a1 a2,
     eval_expr ge sp e m le a1 (Vint (Int64.hiword va)) ->
     eval_expr ge sp e m le a2 (Vint (Int64.loword va)) ->
     eval_expr ge sp e m le (f a1 a2) v) ->
  eval_expr ge sp e m le (splitlong a f) v.
Proof.
  intros until v. 
  unfold splitlong. case (splitlong_match a); intros.
- InvEval. destruct v1; simpl in H; try discriminate. destruct v0; inv H. 
  apply H0. rewrite Int64.hi_ofwords; auto. rewrite Int64.lo_ofwords; auto.
- EvalOp. apply H0; EvalOp.
Qed.

Lemma eval_splitlong2:
  forall le a b f va vb sem,
  (forall le a1 a2 b1 b2 x1 x2 y1 y2,
   eval_expr ge sp e m le a1 x1 ->
   eval_expr ge sp e m le a2 x2 ->
   eval_expr ge sp e m le b1 y1 ->
   eval_expr ge sp e m le b2 y2 ->
   exists v,
     eval_expr ge sp e m le (f a1 a2 b1 b2) v /\
     (forall p1 p2 q1 q2,
       x1 = Vint p1 -> x2 = Vint p2 -> y1 = Vint q1 -> y2 = Vint q2 ->
       v = sem (Vlong (Int64.ofwords p1 p2)) (Vlong (Int64.ofwords q1 q2)))) ->
  match va, vb with Vlong _, Vlong _ => True | _, _ => sem va vb = Vundef end ->
  eval_expr ge sp e m le a va ->
  eval_expr ge sp e m le b vb ->
  exists v, eval_expr ge sp e m le (splitlong2 a b f) v /\ Val.lessdef (sem va vb) v.
Proof.
  intros until sem; intros EXEC UNDEF.
  unfold splitlong2. case (splitlong2_match a b); intros.
- InvEval. subst va vb.
  exploit (EXEC le h1 l1 h2 l2); eauto. intros [v [A B]].
  exists v; split; auto.
  destruct v1; simpl in *; try (rewrite UNDEF; auto).
  destruct v0; try (rewrite UNDEF; auto).
  destruct v2; simpl in *; try (rewrite UNDEF; auto).
  destruct v3; try (rewrite UNDEF; auto).
  erewrite B; eauto.
- InvEval. subst va. 
  exploit (EXEC (vb :: le) (lift h1) (lift l1) 
                (Eop Ohighlong (Eletvar 0 ::: Enil)) (Eop Olowlong (Eletvar 0 ::: Enil))).
  EvalOp. EvalOp. EvalOp. EvalOp. 
  intros [v [A B]].
  exists v; split.
  econstructor; eauto.
  destruct v1; simpl in *; try (rewrite UNDEF; auto).
  destruct v0; try (rewrite UNDEF; auto).
  destruct vb; try (rewrite UNDEF; auto).
  erewrite B; simpl; eauto. rewrite Int64.ofwords_recompose. auto.
- InvEval. subst vb. 
  exploit (EXEC (va :: le)
                (Eop Ohighlong (Eletvar 0 ::: Enil)) (Eop Olowlong (Eletvar 0 ::: Enil))
                (lift h2) (lift l2)).
  EvalOp. EvalOp. EvalOp. EvalOp.
  intros [v [A B]].
  exists v; split.
  econstructor; eauto.
  destruct va; try (rewrite UNDEF; auto).
  destruct v1; simpl in *; try (rewrite UNDEF; auto). 
  destruct v0; try (rewrite UNDEF; auto).
  erewrite B; simpl; eauto. rewrite Int64.ofwords_recompose. auto. 
- exploit (EXEC (vb :: va :: le)
                (Eop Ohighlong (Eletvar 1 ::: Enil)) (Eop Olowlong (Eletvar 1 ::: Enil))
                (Eop Ohighlong (Eletvar 0 ::: Enil)) (Eop Olowlong (Eletvar 0 ::: Enil))).
  EvalOp. EvalOp. EvalOp. EvalOp.
  intros [v [A B]].
  exists v; split. EvalOp. 
  destruct va; try (rewrite UNDEF; auto); destruct vb; try (rewrite UNDEF; auto).
  erewrite B; simpl; eauto. rewrite ! Int64.ofwords_recompose; auto.
Qed.

Lemma eval_splitlong2_strict:
  forall le a b f va vb v,
  eval_expr ge sp e m le a (Vlong va) ->
  eval_expr ge sp e m le b (Vlong vb) ->
  (forall le a1 a2 b1 b2,
     eval_expr ge sp e m le a1 (Vint (Int64.hiword va)) ->
     eval_expr ge sp e m le a2 (Vint (Int64.loword va)) ->
     eval_expr ge sp e m le b1 (Vint (Int64.hiword vb)) ->
     eval_expr ge sp e m le b2 (Vint (Int64.loword vb)) ->
     eval_expr ge sp e m le (f a1 a2 b1 b2) v) ->
  eval_expr ge sp e m le (splitlong2 a b f) v.
Proof.
  assert (INV: forall v1 v2 n,
    Val.longofwords v1 v2 = Vlong n -> v1 = Vint(Int64.hiword n) /\ v2 = Vint(Int64.loword n)).
  {
    intros. destruct v1; simpl in H; try discriminate. destruct v2; inv H.
    rewrite Int64.hi_ofwords; rewrite Int64.lo_ofwords; auto.
  }
  intros until v. 
  unfold splitlong2. case (splitlong2_match a b); intros.
- InvEval. exploit INV. eexact H. intros [EQ1 EQ2]. exploit INV. eexact H0. intros [EQ3 EQ4]. 
  subst. auto.
- InvEval. exploit INV; eauto. intros [EQ1 EQ2]. subst. 
  econstructor. eauto. apply H1; EvalOp. 
- InvEval. exploit INV; eauto. intros [EQ1 EQ2]. subst. 
  econstructor. eauto. apply H1; EvalOp.
- EvalOp. apply H1; EvalOp.
Qed.

Lemma is_longconst_sound:
  forall le a x n,
  is_longconst a = Some n ->
  eval_expr ge sp e m le a x ->
  x = Vlong n.
Proof.
  unfold is_longconst; intros until n; intros LC. 
  destruct (is_longconst_match a); intros.
  inv LC. InvEval. simpl in H5. inv H5. auto. 
  discriminate.
Qed.

Lemma is_longconst_zero_sound:
  forall le a x,
  is_longconst_zero a = true ->
  eval_expr ge sp e m le a x ->
  x = Vlong Int64.zero.
Proof.
  unfold is_longconst_zero; intros. 
  destruct (is_longconst a) as [n|] eqn:E; try discriminate.
  revert H. predSpec Int64.eq Int64.eq_spec n Int64.zero.
  intros. subst. eapply is_longconst_sound; eauto. 
  congruence.
Qed.

Lemma eval_lowlong: unary_constructor_sound lowlong Val.loword.
Proof.
  unfold lowlong; red. intros until x. destruct (lowlong_match a); intros.
  InvEval. subst x. exists v0; split; auto. 
  destruct v1; simpl; auto. destruct v0; simpl; auto. 
  rewrite Int64.lo_ofwords. auto. 
  exists (Val.loword x); split; auto. EvalOp. 
Qed.

Lemma eval_highlong: unary_constructor_sound highlong Val.hiword.
Proof.
  unfold highlong; red. intros until x. destruct (highlong_match a); intros.
  InvEval. subst x. exists v1; split; auto. 
  destruct v1; simpl; auto. destruct v0; simpl; auto. 
  rewrite Int64.hi_ofwords. auto. 
  exists (Val.hiword x); split; auto. EvalOp. 
Qed.

Lemma eval_longconst: 
  forall le n, eval_expr ge sp e m le (longconst n) (Vlong n).
Proof.
  intros. EvalOp. rewrite Int64.ofwords_recompose; auto. 
Qed.

Theorem eval_intoflong: unary_constructor_sound intoflong Val.loword.
Proof eval_lowlong.

Theorem eval_longofintu: unary_constructor_sound longofintu Val.longofintu.
Proof.
  red; intros. unfold longofintu. econstructor; split. EvalOp. 
  unfold Val.longofintu. destruct x; auto. 
  replace (Int64.repr (Int.unsigned i)) with (Int64.ofwords Int.zero i); auto.
  apply Int64.same_bits_eq; intros. 
  rewrite Int64.testbit_repr by auto.
  rewrite Int64.bits_ofwords by auto.
  fold (Int.testbit i i0).
  destruct (zlt i0 Int.zwordsize).
  auto.
  rewrite Int.bits_zero. rewrite Int.bits_above by omega. auto.
Qed.

Theorem eval_longofint: unary_constructor_sound longofint Val.longofint.
Proof.
  red; intros. unfold longofint.
  exploit (eval_shrimm ge sp e m (Int.repr 31) (x :: le) (Eletvar 0)). EvalOp.
  intros [v1 [A B]].
  econstructor; split. EvalOp.
  destruct x; simpl; auto. 
  simpl in B. inv B. simpl. 
  replace (Int64.repr (Int.signed i))
     with (Int64.ofwords (Int.shr i (Int.repr 31)) i); auto.
  apply Int64.same_bits_eq; intros. 
  rewrite Int64.testbit_repr by auto.
  rewrite Int64.bits_ofwords by auto.
  rewrite Int.bits_signed by omega.
  destruct (zlt i0 Int.zwordsize).
  auto.
  assert (Int64.zwordsize = 2 * Int.zwordsize) by reflexivity. 
  rewrite Int.bits_shr by omega.
  change (Int.unsigned (Int.repr 31)) with (Int.zwordsize - 1).
  f_equal. destruct (zlt (i0 - Int.zwordsize + (Int.zwordsize - 1)) Int.zwordsize); omega.
Qed.

Theorem eval_negl: unary_constructor_sound (negl hf) Val.negl.
Proof.
  unfold negl; red; intros. destruct (is_longconst a) eqn:E.
  econstructor; split. apply eval_longconst.  
  exploit is_longconst_sound; eauto. intros EQ; subst x. simpl. auto.
  econstructor; split. eapply eval_builtin_1; eauto. UseHelper. auto.
Qed.

Theorem eval_notl: unary_constructor_sound notl Val.notl.
Proof.
  red; intros. unfold notl. apply eval_splitlong; auto. 
  intros. 
  exploit eval_notint. eexact H0. intros [va [A B]].
  exploit eval_notint. eexact H1. intros [vb [C D]].
  exists (Val.longofwords va vb); split. EvalOp.
  intros; subst. simpl in *. inv B; inv D. 
  simpl. unfold Int.not. rewrite <- Int64.decompose_xor. auto.
  destruct x; auto.
Qed.

Theorem eval_longoffloat:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.longoffloat x = Some y ->
  exists v, eval_expr ge sp e m le (longoffloat hf a) v /\ Val.lessdef y v.
Proof.
  intros; unfold longoffloat. econstructor; split. 
  eapply eval_helper_1; eauto. UseHelper. 
  auto.
Qed.

Theorem eval_longuoffloat:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.longuoffloat x = Some y ->
  exists v, eval_expr ge sp e m le (longuoffloat hf a) v /\ Val.lessdef y v.
Proof.
  intros; unfold longuoffloat. econstructor; split. 
  eapply eval_helper_1; eauto. UseHelper. 
  auto.
Qed.

Theorem eval_floatoflong:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.floatoflong x = Some y ->
  exists v, eval_expr ge sp e m le (floatoflong hf a) v /\ Val.lessdef y v.
Proof.
  intros; unfold floatoflong. econstructor; split. 
  eapply eval_helper_1; eauto. UseHelper. 
  auto.
Qed.

Theorem eval_floatoflongu:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.floatoflongu x = Some y ->
  exists v, eval_expr ge sp e m le (floatoflongu hf a) v /\ Val.lessdef y v.
Proof.
  intros; unfold floatoflongu. econstructor; split. 
  eapply eval_helper_1; eauto. UseHelper. 
  auto.
Qed.

Theorem eval_andl: binary_constructor_sound andl Val.andl.
Proof.
  red; intros. unfold andl. apply eval_splitlong2; auto.
  intros. 
  exploit eval_and. eexact H1. eexact H3. intros [va [A B]].
  exploit eval_and. eexact H2. eexact H4. intros [vb [C D]].
  exists (Val.longofwords va vb); split. EvalOp. 
  intros; subst. simpl in B; inv B. simpl in D; inv D.
  simpl. f_equal. rewrite Int64.decompose_and. auto.
  destruct x; auto. destruct y; auto.
Qed.

Theorem eval_orl: binary_constructor_sound orl Val.orl.
Proof.
  red; intros. unfold orl. apply eval_splitlong2; auto.
  intros. 
  exploit eval_or. eexact H1. eexact H3. intros [va [A B]].
  exploit eval_or. eexact H2. eexact H4. intros [vb [C D]].
  exists (Val.longofwords va vb); split. EvalOp. 
  intros; subst. simpl in B; inv B. simpl in D; inv D.
  simpl. f_equal. rewrite Int64.decompose_or. auto.
  destruct x; auto. destruct y; auto.
Qed.

Theorem eval_xorl: binary_constructor_sound xorl Val.xorl.
Proof.
  red; intros. unfold xorl. apply eval_splitlong2; auto.
  intros. 
  exploit eval_xor. eexact H1. eexact H3. intros [va [A B]].
  exploit eval_xor. eexact H2. eexact H4. intros [vb [C D]].
  exists (Val.longofwords va vb); split. EvalOp. 
  intros; subst. simpl in B; inv B. simpl in D; inv D.
  simpl. f_equal. rewrite Int64.decompose_xor. auto.
  destruct x; auto. destruct y; auto.
Qed.

Lemma is_intconst_sound:
  forall le a x n,
  is_intconst a = Some n ->
  eval_expr ge sp e m le a x ->
  x = Vint n.
Proof.
  unfold is_intconst; intros until n; intros LC. 
  destruct a; try discriminate. destruct o; try discriminate. destruct e0; try discriminate.
  inv LC. intros. InvEval. auto.
Qed.

Remark eval_shift_imm:
  forall (P: expr -> Prop) n a0 a1 a2 a3,
  (n = Int.zero -> P a0) ->
  (0 <= Int.unsigned n < Int.zwordsize ->
   Int.ltu n Int.iwordsize = true ->
   Int.ltu (Int.sub Int.iwordsize n) Int.iwordsize = true ->
   Int.ltu n Int64.iwordsize' = true ->
   P a1) ->
  (Int.zwordsize <= Int.unsigned n < Int64.zwordsize ->
   Int.ltu (Int.sub n Int.iwordsize) Int.iwordsize = true ->
   P a2) ->
  P a3 ->
  P (if Int.eq n Int.zero then a0
     else if Int.ltu n Int.iwordsize then a1
     else if Int.ltu n Int64.iwordsize' then a2
     else a3).
Proof.
  intros until a3; intros A0 A1 A2 A3.
  predSpec Int.eq Int.eq_spec n Int.zero.
  apply A0; auto.
  assert (NZ: Int.unsigned n <> 0). 
  { red; intros. elim H. rewrite <- (Int.repr_unsigned n). rewrite H0. auto. }
  destruct (Int.ltu n Int.iwordsize) eqn:LT.
  exploit Int.ltu_iwordsize_inv; eauto. intros RANGE.
  assert (0 <= Int.zwordsize - Int.unsigned n < Int.zwordsize) by omega.
  apply A1. auto. auto. 
  unfold Int.ltu, Int.sub. rewrite Int.unsigned_repr_wordsize. 
  rewrite Int.unsigned_repr. rewrite zlt_true; auto. omega. 
  generalize Int.wordsize_max_unsigned; omega. 
  unfold Int.ltu. rewrite zlt_true; auto. 
  change (Int.unsigned Int64.iwordsize') with 64.
  change Int.zwordsize with 32 in RANGE. omega.
  destruct (Int.ltu n Int64.iwordsize') eqn:LT'.
  exploit Int.ltu_inv; eauto. 
  change (Int.unsigned Int64.iwordsize') with (Int.zwordsize * 2).
  intros RANGE.
  assert (Int.zwordsize <= Int.unsigned n).
    unfold Int.ltu in LT. rewrite Int.unsigned_repr_wordsize in LT. 
    destruct (zlt (Int.unsigned n) Int.zwordsize). discriminate. omega. 
  apply A2. tauto. unfold Int.ltu, Int.sub. rewrite Int.unsigned_repr_wordsize. 
  rewrite Int.unsigned_repr. rewrite zlt_true; auto. omega. 
  generalize Int.wordsize_max_unsigned; omega. 
  auto.
Qed.

Lemma eval_shllimm:
  forall n,
  unary_constructor_sound (fun e => shllimm hf e n) (fun v => Val.shll v (Vint n)).
Proof.
  unfold shllimm; red; intros.
  apply eval_shift_imm; intros.
  + (* n = 0 *)
    subst n. exists x; split; auto. destruct x; simpl; auto. 
    change (Int64.shl' i Int.zero) with (Int64.shl i Int64.zero). 
    rewrite Int64.shl_zero. auto.
  + (* 0 < n < 32 *)
    apply eval_splitlong with (sem := fun x => Val.shll x (Vint n)); auto.
    intros.
    exploit eval_shlimm. eexact H4. instantiate (1 := n). intros [v1 [A1 B1]].
    exploit eval_shlimm. eexact H5. instantiate (1 := n). intros [v2 [A2 B2]].
    exploit eval_shruimm. eexact H5. instantiate (1 := Int.sub Int.iwordsize n). intros [v3 [A3 B3]].
    exploit eval_or. eexact A1. eexact A3. intros [v4 [A4 B4]].
    econstructor; split. EvalOp. 
    intros. subst. simpl in *. rewrite H1 in *. rewrite H2 in *. rewrite H3. 
    inv B1; inv B2; inv B3. simpl in B4. inv B4.
    simpl. rewrite Int64.decompose_shl_1; auto.
    destruct x; auto.
  + (* 32 <= n < 64 *)
    exploit eval_lowlong. eexact H. intros [v1 [A1 B1]].
    exploit eval_shlimm. eexact A1. instantiate (1 := Int.sub n Int.iwordsize). intros [v2 [A2 B2]].
    econstructor; split. EvalOp.
    destruct x; simpl; auto.
    destruct (Int.ltu n Int64.iwordsize'); auto. 
    simpl in B1; inv B1. simpl in B2. rewrite H1 in B2. inv B2. 
    simpl. erewrite <- Int64.decompose_shl_2. instantiate (1 := Int64.hiword i). 
    rewrite Int64.ofwords_recompose. auto. auto.
  + (* n >= 64 *)
    econstructor; split. eapply eval_helper_2; eauto. EvalOp. UseHelper. auto.
Qed.

Theorem eval_shll: binary_constructor_sound (shll hf) Val.shll.
Proof.
  unfold shll; red; intros.
  destruct (is_intconst b) as [n|] eqn:IC.
- (* Immediate *)
  exploit is_intconst_sound; eauto. intros EQ; subst y; clear H0.
  eapply eval_shllimm; eauto.
- (* General case *)
  econstructor; split. eapply eval_helper_2; eauto. UseHelper. auto.
Qed.

Lemma eval_shrluimm:
  forall n,
  unary_constructor_sound (fun e => shrluimm hf e n) (fun v => Val.shrlu v (Vint n)).
Proof.
  unfold shrluimm; red; intros. apply eval_shift_imm; intros.
  + (* n = 0 *)
    subst n. exists x; split; auto. destruct x; simpl; auto. 
    change (Int64.shru' i Int.zero) with (Int64.shru i Int64.zero). 
    rewrite Int64.shru_zero. auto.
  + (* 0 < n < 32 *)
    apply eval_splitlong with (sem := fun x => Val.shrlu x (Vint n)); auto.
    intros.
    exploit eval_shruimm. eexact H5. instantiate (1 := n). intros [v1 [A1 B1]].
    exploit eval_shruimm. eexact H4. instantiate (1 := n). intros [v2 [A2 B2]].
    exploit eval_shlimm. eexact H4. instantiate (1 := Int.sub Int.iwordsize n). intros [v3 [A3 B3]].
    exploit eval_or. eexact A1. eexact A3. intros [v4 [A4 B4]].
    econstructor; split. EvalOp. 
    intros. subst. simpl in *. rewrite H1 in *. rewrite H2 in *. rewrite H3. 
    inv B1; inv B2; inv B3. simpl in B4. inv B4.
    simpl. rewrite Int64.decompose_shru_1; auto.
    destruct x; auto.
  + (* 32 <= n < 64 *)
    exploit eval_highlong. eexact H. intros [v1 [A1 B1]].
    exploit eval_shruimm. eexact A1. instantiate (1 := Int.sub n Int.iwordsize). intros [v2 [A2 B2]].
    econstructor; split. EvalOp.
    destruct x; simpl; auto.
    destruct (Int.ltu n Int64.iwordsize'); auto. 
    simpl in B1; inv B1. simpl in B2. rewrite H1 in B2. inv B2. 
    simpl. erewrite <- Int64.decompose_shru_2. instantiate (1 := Int64.loword i). 
    rewrite Int64.ofwords_recompose. auto. auto.
  + (* n >= 64 *)
    econstructor; split. eapply eval_helper_2; eauto. EvalOp. UseHelper. auto.
Qed.

Theorem eval_shrlu: binary_constructor_sound (shrlu hf) Val.shrlu.
Proof.
  unfold shrlu; red; intros.
  destruct (is_intconst b) as [n|] eqn:IC.
- (* Immediate *)
  exploit is_intconst_sound; eauto. intros EQ; subst y; clear H0.
  eapply eval_shrluimm; eauto.
- (* General case *)
  econstructor; split. eapply eval_helper_2; eauto. UseHelper. auto.
Qed.

Lemma eval_shrlimm:
  forall n,
  unary_constructor_sound (fun e => shrlimm hf e n) (fun v => Val.shrl v (Vint n)).
Proof.
  unfold shrlimm; red; intros. apply eval_shift_imm; intros.
  + (* n = 0 *)
    subst n. exists x; split; auto. destruct x; simpl; auto. 
    change (Int64.shr' i Int.zero) with (Int64.shr i Int64.zero). 
    rewrite Int64.shr_zero. auto.
  + (* 0 < n < 32 *)
    apply eval_splitlong with (sem := fun x => Val.shrl x (Vint n)); auto.
    intros.
    exploit eval_shruimm. eexact H5. instantiate (1 := n). intros [v1 [A1 B1]].
    exploit eval_shrimm. eexact H4. instantiate (1 := n). intros [v2 [A2 B2]].
    exploit eval_shlimm. eexact H4. instantiate (1 := Int.sub Int.iwordsize n). intros [v3 [A3 B3]].
    exploit eval_or. eexact A1. eexact A3. intros [v4 [A4 B4]].
    econstructor; split. EvalOp. 
    intros. subst. simpl in *. rewrite H1 in *. rewrite H2 in *. rewrite H3. 
    inv B1; inv B2; inv B3. simpl in B4. inv B4.
    simpl. rewrite Int64.decompose_shr_1; auto.
    destruct x; auto.
  + (* 32 <= n < 64 *)
    exploit eval_highlong. eexact H. intros [v1 [A1 B1]].
    assert (eval_expr ge sp e m (v1 :: le) (Eletvar 0) v1) by EvalOp.
    exploit eval_shrimm. eexact H2. instantiate (1 := Int.sub n Int.iwordsize). intros [v2 [A2 B2]].
    exploit eval_shrimm. eexact H2. instantiate (1 := Int.repr 31). intros [v3 [A3 B3]].
    econstructor; split. EvalOp.
    destruct x; simpl; auto.
    destruct (Int.ltu n Int64.iwordsize'); auto. 
    simpl in B1; inv B1. simpl in B2. rewrite H1 in B2. inv B2.
    simpl in B3. inv B3.
    change (Int.ltu (Int.repr 31) Int.iwordsize) with true. simpl.
    erewrite <- Int64.decompose_shr_2. instantiate (1 := Int64.loword i). 
    rewrite Int64.ofwords_recompose. auto. auto.
  + (* n >= 64 *)
    econstructor; split. eapply eval_helper_2; eauto. EvalOp. UseHelper. auto.
Qed.

Theorem eval_shrl: binary_constructor_sound (shrl hf) Val.shrl.
Proof.
  unfold shrl; red; intros.
  destruct (is_intconst b) as [n|] eqn:IC.
- (* Immediate *)
  exploit is_intconst_sound; eauto. intros EQ; subst y; clear H0.
  eapply eval_shrlimm; eauto.
- (* General case *)
  econstructor; split. eapply eval_helper_2; eauto. UseHelper. auto.
Qed.

Theorem eval_addl: binary_constructor_sound (addl hf) Val.addl.
Proof.
  unfold addl; red; intros.
  set (default := Ebuiltin (EF_builtin (i64_add hf) sig_ll_l) (a ::: b ::: Enil)).
  assert (DEFAULT:
    exists v, eval_expr ge sp e m le default v /\ Val.lessdef (Val.addl x y) v).
  {
    econstructor; split. eapply eval_builtin_2; eauto. UseHelper. auto. 
  }
  destruct (is_longconst a) as [p|] eqn:LC1;
  destruct (is_longconst b) as [q|] eqn:LC2.
- exploit (is_longconst_sound le a); eauto. intros EQ; subst x. 
  exploit (is_longconst_sound le b); eauto. intros EQ; subst y.
  econstructor; split. apply eval_longconst. simpl; auto.
- predSpec Int64.eq Int64.eq_spec p Int64.zero; auto.
  subst p. exploit (is_longconst_sound le a); eauto. intros EQ; subst x. 
  exists y; split; auto. simpl. destruct y; auto. rewrite Int64.add_zero_l; auto.
- predSpec Int64.eq Int64.eq_spec q Int64.zero; auto.
  subst q. exploit (is_longconst_sound le b); eauto. intros EQ; subst y. 
  exists x; split; auto. destruct x; simpl; auto. rewrite Int64.add_zero; auto.
- auto.
Qed.

Theorem eval_subl: binary_constructor_sound (subl hf) Val.subl.
Proof.
  unfold subl; red; intros.
  set (default := Ebuiltin (EF_builtin (i64_sub hf) sig_ll_l) (a ::: b ::: Enil)).
  assert (DEFAULT:
    exists v, eval_expr ge sp e m le default v /\ Val.lessdef (Val.subl x y) v).
  {
    econstructor; split. eapply eval_builtin_2; eauto. UseHelper. auto. 
  }
  destruct (is_longconst a) as [p|] eqn:LC1;
  destruct (is_longconst b) as [q|] eqn:LC2.
- exploit (is_longconst_sound le a); eauto. intros EQ; subst x. 
  exploit (is_longconst_sound le b); eauto. intros EQ; subst y.
  econstructor; split. apply eval_longconst. simpl; auto.
- predSpec Int64.eq Int64.eq_spec p Int64.zero; auto.
  replace (Val.subl x y) with (Val.negl y). eapply eval_negl; eauto.
  subst p. exploit (is_longconst_sound le a); eauto. intros EQ; subst x.
  destruct y; simpl; auto. 
- predSpec Int64.eq Int64.eq_spec q Int64.zero; auto.
  subst q. exploit (is_longconst_sound le b); eauto. intros EQ; subst y. 
  exists x; split; auto. destruct x; simpl; auto. rewrite Int64.sub_zero_l; auto.
- auto.
Qed.

Lemma eval_mull_base: binary_constructor_sound (mull_base hf) Val.mull.
Proof.
  unfold mull_base; red; intros. apply eval_splitlong2; auto.
- intros. 
  set (p := Val.mull' x2 y2). set (le1 := p :: le0).
  assert (E1: eval_expr ge sp e m le1 (Eop Olowlong (Eletvar O ::: Enil)) (Val.loword p)) by EvalOp.
  assert (E2: eval_expr ge sp e m le1 (Eop Ohighlong (Eletvar O ::: Enil)) (Val.hiword p)) by EvalOp.
  exploit eval_mul. apply eval_lift. eexact H2. apply eval_lift. eexact H3. 
  instantiate (1 := p). fold le1. intros [v3 [E3 L3]].
  exploit eval_mul. apply eval_lift. eexact H1. apply eval_lift. eexact H4. 
  instantiate (1 := p). fold le1. intros [v4 [E4 L4]].
  exploit eval_add. eexact E2. eexact E3. intros [v5 [E5 L5]].
  exploit eval_add. eexact E5. eexact E4. intros [v6 [E6 L6]].
  exists (Val.longofwords v6 (Val.loword p)); split.
  EvalOp. eapply eval_builtin_2; eauto. UseHelper. 
  intros. unfold le1, p in *; subst; simpl in *.
  inv L3. inv L4. inv L5. simpl in L6. inv L6. 
  simpl. f_equal. symmetry. apply Int64.decompose_mul. 
- destruct x; auto; destruct y; auto. 
Qed.

Lemma eval_mullimm:
  forall n, unary_constructor_sound (fun a => mullimm hf a n) (fun v => Val.mull v (Vlong n)).
Proof.
  unfold mullimm; red; intros.
  predSpec Int64.eq Int64.eq_spec n Int64.zero.
  subst n. econstructor; split. apply eval_longconst. 
  destruct x; simpl; auto. rewrite Int64.mul_zero. auto.
  predSpec Int64.eq Int64.eq_spec n Int64.one.
  subst n. exists x; split; auto. 
  destruct x; simpl; auto. rewrite Int64.mul_one. auto.
  destruct (Int64.is_power2 n) as [l|] eqn:P2. 
  exploit eval_shllimm. eauto. instantiate (1 := Int.repr (Int64.unsigned l)).
  intros [v [A B]].
  exists v; split; auto. 
  destruct x; simpl; auto. 
  erewrite Int64.mul_pow2 by eauto.
  assert (EQ: Int.unsigned (Int.repr (Int64.unsigned l)) = Int64.unsigned l).
  { apply Int.unsigned_repr.
    exploit Int64.is_power2_rng; eauto.
    assert (Int64.zwordsize < Int.max_unsigned) by (compute; auto). 
    omega.
  }
  simpl in B. 
  replace (Int.ltu (Int.repr (Int64.unsigned l)) Int64.iwordsize')
     with (Int64.ltu l Int64.iwordsize) in B.
  erewrite Int64.is_power2_range in B by eauto. 
  unfold Int64.shl' in B. rewrite EQ in B. auto. 
  unfold Int64.ltu, Int.ltu. rewrite EQ. auto.
  apply eval_mull_base; auto. apply eval_longconst. 
Qed.

Theorem eval_mull: binary_constructor_sound (mull hf) Val.mull.
Proof.
  unfold mull; red; intros.
  destruct (is_longconst a) as [p|] eqn:LC1;
  destruct (is_longconst b) as [q|] eqn:LC2.
- exploit (is_longconst_sound le a); eauto. intros EQ; subst x. 
  exploit (is_longconst_sound le b); eauto. intros EQ; subst y.
  econstructor; split. apply eval_longconst. simpl; auto.
- exploit (is_longconst_sound le a); eauto. intros EQ; subst x.
  replace (Val.mull (Vlong p) y) with (Val.mull y (Vlong p)) in *.
  eapply eval_mullimm; eauto. 
  destruct y; simpl; auto. rewrite Int64.mul_commut; auto. 
- exploit (is_longconst_sound le b); eauto. intros EQ; subst y.
  eapply eval_mullimm; eauto.
- apply eval_mull_base; auto.
Qed.

Lemma eval_binop_long:
  forall id sem le a b x y z,
  (forall p q, x = Vlong p -> y = Vlong q -> z = Vlong (sem p q)) ->
  helper_implements ge id sig_ll_l (x::y::nil) z ->
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  exists v, eval_expr ge sp e m le (binop_long id sem a b) v /\ Val.lessdef z v.
Proof.
  intros. unfold binop_long. 
  destruct (is_longconst a) as [p|] eqn:LC1. 
  destruct (is_longconst b) as [q|] eqn:LC2.
  exploit is_longconst_sound. eexact LC1. eauto. intros EQ; subst x.
  exploit is_longconst_sound. eexact LC2. eauto. intros EQ; subst y.
  econstructor; split. EvalOp. erewrite H by eauto. rewrite Int64.ofwords_recompose. auto. 
  econstructor; split. eapply eval_helper_2; eauto. auto.
  econstructor; split. eapply eval_helper_2; eauto. auto.
Qed.

Theorem eval_divl:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.divls x y = Some z ->
  exists v, eval_expr ge sp e m le (divl hf a b) v /\ Val.lessdef z v.
Proof.
  intros. eapply eval_binop_long; eauto. 
  intros; subst; simpl in H1.
  destruct (Int64.eq q Int64.zero
         || Int64.eq p (Int64.repr Int64.min_signed) && Int64.eq q Int64.mone); inv H1. 
  auto.
  UseHelper. 
Qed.

Theorem eval_modl:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.modls x y = Some z ->
  exists v, eval_expr ge sp e m le (modl hf a b) v /\ Val.lessdef z v.
Proof.
  intros. eapply eval_binop_long; eauto. 
  intros; subst; simpl in H1.
  destruct (Int64.eq q Int64.zero
         || Int64.eq p (Int64.repr Int64.min_signed) && Int64.eq q Int64.mone); inv H1. 
  auto.
  UseHelper. 
Qed.

Theorem eval_divlu:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.divlu x y = Some z ->
  exists v, eval_expr ge sp e m le (divlu hf a b) v /\ Val.lessdef z v.
Proof.
  intros. unfold divlu. 
  set (default := Eexternal (i64_udiv hf) sig_ll_l (a ::: b ::: Enil)).
  assert (DEFAULT:
    exists v, eval_expr ge sp e m le default v /\ Val.lessdef z v).
  {
    econstructor; split. eapply eval_helper_2; eauto. UseHelper. auto. 
  }
  destruct (is_longconst a) as [p|] eqn:LC1;
  destruct (is_longconst b) as [q|] eqn:LC2.
- exploit (is_longconst_sound le a); eauto. intros EQ; subst x. 
  exploit (is_longconst_sound le b); eauto. intros EQ; subst y.
  econstructor; split. apply eval_longconst.
  simpl in H1. destruct (Int64.eq q Int64.zero); inv H1. auto. 
- auto.
- destruct (Int64.is_power2 q) as [l|] eqn:P2; auto.
  exploit (is_longconst_sound le b); eauto. intros EQ; subst y.
  replace z with (Val.shrlu x (Vint (Int.repr (Int64.unsigned l)))).
  apply eval_shrluimm. auto.
  destruct x; simpl in H1; try discriminate. 
  destruct (Int64.eq q Int64.zero); inv H1. 
  simpl. 
  assert (EQ: Int.unsigned (Int.repr (Int64.unsigned l)) = Int64.unsigned l).
  { apply Int.unsigned_repr.
    exploit Int64.is_power2_rng; eauto.
    assert (Int64.zwordsize < Int.max_unsigned) by (compute; auto). 
    omega.
  }
  replace (Int.ltu (Int.repr (Int64.unsigned l)) Int64.iwordsize')
     with (Int64.ltu l Int64.iwordsize).
  erewrite Int64.is_power2_range by eauto.
  erewrite Int64.divu_pow2 by eauto. 
  unfold Int64.shru', Int64.shru. rewrite EQ. auto. 
  unfold Int64.ltu, Int.ltu. rewrite EQ. auto.
- auto.
Qed.

Theorem eval_modlu:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.modlu x y = Some z ->
  exists v, eval_expr ge sp e m le (modlu hf a b) v /\ Val.lessdef z v.
Proof.
  intros. unfold modlu. 
  set (default := Eexternal (i64_umod hf) sig_ll_l (a ::: b ::: Enil)).
  assert (DEFAULT:
    exists v, eval_expr ge sp e m le default v /\ Val.lessdef z v).
  {
    econstructor; split. eapply eval_helper_2; eauto. UseHelper. auto. 
  }
  destruct (is_longconst a) as [p|] eqn:LC1;
  destruct (is_longconst b) as [q|] eqn:LC2.
- exploit (is_longconst_sound le a); eauto. intros EQ; subst x. 
  exploit (is_longconst_sound le b); eauto. intros EQ; subst y.
  econstructor; split. apply eval_longconst.
  simpl in H1. destruct (Int64.eq q Int64.zero); inv H1. auto. 
- auto.
- destruct (Int64.is_power2 q) as [l|] eqn:P2; auto.
  exploit (is_longconst_sound le b); eauto. intros EQ; subst y.
  replace z with (Val.andl x (Vlong (Int64.sub q Int64.one))).
  apply eval_andl. auto. apply eval_longconst. 
  destruct x; simpl in H1; try discriminate. 
  destruct (Int64.eq q Int64.zero); inv H1. 
  simpl. 
  erewrite Int64.modu_and by eauto. auto.
- auto.
Qed.

Remark decompose_cmpl_eq_zero:
  forall h l,
  Int64.eq (Int64.ofwords h l) Int64.zero = Int.eq (Int.or h l) Int.zero.
Proof.
  intros. 
  assert (Int64.zwordsize = Int.zwordsize * 2) by reflexivity.
  predSpec Int64.eq Int64.eq_spec (Int64.ofwords h l) Int64.zero.
  replace (Int.or h l) with Int.zero. rewrite Int.eq_true. auto.
  apply Int.same_bits_eq; intros. 
  rewrite Int.bits_zero. rewrite Int.bits_or by auto. 
  symmetry. apply orb_false_intro. 
  transitivity (Int64.testbit (Int64.ofwords h l) (i + Int.zwordsize)).
  rewrite Int64.bits_ofwords by omega. rewrite zlt_false by omega. f_equal; omega.
  rewrite H0. apply Int64.bits_zero. 
  transitivity (Int64.testbit (Int64.ofwords h l) i).
  rewrite Int64.bits_ofwords by omega. rewrite zlt_true by omega. auto. 
  rewrite H0. apply Int64.bits_zero.
  symmetry. apply Int.eq_false. red; intros; elim H0. 
  apply Int64.same_bits_eq; intros. 
  rewrite Int64.bits_zero. rewrite Int64.bits_ofwords by auto. 
  destruct (zlt i Int.zwordsize).
  assert (Int.testbit (Int.or h l) i = false) by (rewrite H1; apply Int.bits_zero). 
  rewrite Int.bits_or in H3 by omega. exploit orb_false_elim; eauto. tauto. 
  assert (Int.testbit (Int.or h l) (i - Int.zwordsize) = false) by (rewrite H1; apply Int.bits_zero). 
  rewrite Int.bits_or in H3 by omega. exploit orb_false_elim; eauto. tauto.
Qed.

Lemma eval_cmpl_eq_zero:
  forall le a x,
  eval_expr ge sp e m le a (Vlong x) ->
  eval_expr ge sp e m le (cmpl_eq_zero a) (Val.of_bool (Int64.eq x Int64.zero)).
Proof.
  intros. unfold cmpl_eq_zero. 
  eapply eval_splitlong_strict; eauto. intros.
  exploit eval_or. eexact H0. eexact H1. intros [v1 [A1 B1]]. simpl in B1; inv B1.
  exploit eval_comp. eexact A1. instantiate (2 := Eop (Ointconst Int.zero) Enil). EvalOp.
  instantiate (1 := Ceq). intros [v2 [A2 B2]]. 
  unfold Val.cmp in B2; simpl in B2. 
  rewrite <- decompose_cmpl_eq_zero in B2. 
  rewrite Int64.ofwords_recompose in B2. 
  destruct (Int64.eq x Int64.zero); inv B2; auto.
Qed.

Lemma eval_cmpl_ne_zero:
  forall le a x,
  eval_expr ge sp e m le a (Vlong x) ->
  eval_expr ge sp e m le (cmpl_ne_zero a) (Val.of_bool (negb (Int64.eq x Int64.zero))).
Proof.
  intros. unfold cmpl_ne_zero. 
  eapply eval_splitlong_strict; eauto. intros.
  exploit eval_or. eexact H0. eexact H1. intros [v1 [A1 B1]]. simpl in B1; inv B1.
  exploit eval_comp. eexact A1. instantiate (2 := Eop (Ointconst Int.zero) Enil). EvalOp.
  instantiate (1 := Cne). intros [v2 [A2 B2]]. 
  unfold Val.cmp in B2; simpl in B2. 
  rewrite <- decompose_cmpl_eq_zero in B2. 
  rewrite Int64.ofwords_recompose in B2. 
  destruct (negb (Int64.eq x Int64.zero)); inv B2; auto.
Qed.

Lemma eval_cmplu_gen:
  forall ch cl a b le x y,
  eval_expr ge sp e m le a (Vlong x) ->
  eval_expr ge sp e m le b (Vlong y) ->
  eval_expr ge sp e m le (cmplu_gen ch cl a b)
    (Val.of_bool (if Int.eq (Int64.hiword x) (Int64.hiword y)
                  then Int.cmpu cl (Int64.loword x) (Int64.loword y)
                  else Int.cmpu ch (Int64.hiword x) (Int64.hiword y))).
Proof.
  intros. unfold cmplu_gen. eapply eval_splitlong2_strict; eauto. intros.
  econstructor. econstructor. EvalOp. simpl. eauto. 
  destruct (Int.eq (Int64.hiword x) (Int64.hiword y)); EvalOp.
Qed.

Remark int64_eq_xor:
  forall p q, Int64.eq p q = Int64.eq (Int64.xor p q) Int64.zero.
Proof.
  intros.
  predSpec Int64.eq Int64.eq_spec p q.
  subst q. rewrite Int64.xor_idem. rewrite Int64.eq_true. auto.
  predSpec Int64.eq Int64.eq_spec (Int64.xor p q) Int64.zero.
  elim H. apply Int64.xor_zero_equal; auto.
  auto.
Qed.

Theorem eval_cmplu:
  forall c le a x b y v, 
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.cmplu c x y = Some v ->
  eval_expr ge sp e m le (cmplu c a b) v.
Proof.
  intros. unfold Val.cmplu in H1.
  destruct x; simpl in H1; try discriminate. destruct y; inv H1. 
  rename i into x. rename i0 into y.
  destruct c; simpl.
- (* Ceq *)
  destruct (is_longconst_zero b) eqn:LC.
+ exploit is_longconst_zero_sound; eauto. intros EQ; inv EQ; clear H0.
  apply eval_cmpl_eq_zero; auto.
+ exploit eval_xorl. eexact H. eexact H0. intros [v1 [A B]]. simpl in B. inv B.
  rewrite int64_eq_xor. apply eval_cmpl_eq_zero; auto.  
- (* Cne *)
  destruct (is_longconst_zero b) eqn:LC.
+ exploit is_longconst_zero_sound; eauto. intros EQ; inv EQ; clear H0.
  apply eval_cmpl_ne_zero; auto.
+ exploit eval_xorl. eexact H. eexact H0. intros [v1 [A B]]. simpl in B. inv B.
  rewrite int64_eq_xor. apply eval_cmpl_ne_zero; auto.  
- (* Clt *)
  exploit (eval_cmplu_gen Clt Clt). eexact H. eexact H0. simpl.
  rewrite <- Int64.decompose_ltu. rewrite ! Int64.ofwords_recompose. auto.
- (* Cle *)
  exploit (eval_cmplu_gen Clt Cle). eexact H. eexact H0. intros. 
  rewrite <- (Int64.ofwords_recompose x). rewrite <- (Int64.ofwords_recompose y).
  rewrite Int64.decompose_leu. auto. 
- (* Cgt *)
  exploit (eval_cmplu_gen Cgt Cgt). eexact H. eexact H0. simpl.
  rewrite Int.eq_sym. rewrite <- Int64.decompose_ltu. rewrite ! Int64.ofwords_recompose. auto.
- (* Cge *)
  exploit (eval_cmplu_gen Cgt Cge). eexact H. eexact H0. intros. 
  rewrite <- (Int64.ofwords_recompose x). rewrite <- (Int64.ofwords_recompose y).
  rewrite Int64.decompose_leu. rewrite Int.eq_sym. auto.
Qed.

Lemma eval_cmpl_gen:
  forall ch cl a b le x y,
  eval_expr ge sp e m le a (Vlong x) ->
  eval_expr ge sp e m le b (Vlong y) ->
  eval_expr ge sp e m le (cmpl_gen ch cl a b)
    (Val.of_bool (if Int.eq (Int64.hiword x) (Int64.hiword y)
                  then Int.cmpu cl (Int64.loword x) (Int64.loword y)
                  else Int.cmp ch (Int64.hiword x) (Int64.hiword y))).
Proof.
  intros. unfold cmpl_gen. eapply eval_splitlong2_strict; eauto. intros.
  econstructor. econstructor. EvalOp. simpl. eauto. 
  destruct (Int.eq (Int64.hiword x) (Int64.hiword y)); EvalOp.
Qed.

Remark decompose_cmpl_lt_zero:
  forall h l,
  Int64.lt (Int64.ofwords h l) Int64.zero = Int.lt h Int.zero.
Proof.
  intros. 
  generalize (Int64.shru_lt_zero (Int64.ofwords h l)).
  change (Int64.shru (Int64.ofwords h l) (Int64.repr (Int64.zwordsize - 1)))
    with (Int64.shru' (Int64.ofwords h l) (Int.repr 63)).
  rewrite Int64.decompose_shru_2. 
  change (Int.sub (Int.repr 63) Int.iwordsize)
    with (Int.repr (Int.zwordsize - 1)). 
  rewrite Int.shru_lt_zero. 
  destruct (Int64.lt (Int64.ofwords h l) Int64.zero); destruct (Int.lt h Int.zero); auto; intros.
  elim Int64.one_not_zero. auto. 
  elim Int64.one_not_zero. auto.
  vm_compute. intuition congruence.
Qed.

Theorem eval_cmpl:
  forall c le a x b y v, 
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.cmpl c x y = Some v ->
  eval_expr ge sp e m le (cmpl c a b) v.
Proof.
  intros. unfold Val.cmpl in H1.
  destruct x; simpl in H1; try discriminate. destruct y; inv H1. 
  rename i into x. rename i0 into y.
  destruct c; simpl.
- (* Ceq *)
  destruct (is_longconst_zero b) eqn:LC.
+ exploit is_longconst_zero_sound; eauto. intros EQ; inv EQ; clear H0.
  apply eval_cmpl_eq_zero; auto.
+ exploit eval_xorl. eexact H. eexact H0. intros [v1 [A B]]. simpl in B; inv B.
  rewrite int64_eq_xor. apply eval_cmpl_eq_zero; auto.
- (* Cne *)
  destruct (is_longconst_zero b) eqn:LC.
+ exploit is_longconst_zero_sound; eauto. intros EQ; inv EQ; clear H0.
  apply eval_cmpl_ne_zero; auto.
+ exploit eval_xorl. eexact H. eexact H0. intros [v1 [A B]]. simpl in B; inv B.
  rewrite int64_eq_xor. apply eval_cmpl_ne_zero; auto.
- (* Clt *)
  destruct (is_longconst_zero b) eqn:LC.
+ exploit is_longconst_zero_sound; eauto. intros EQ; inv EQ; clear H0.
  exploit eval_highlong. eexact H. intros [v1 [A1 B1]]. simpl in B1. inv B1. 
  exploit eval_comp. eexact A1. 
  instantiate (2 := Eop (Ointconst Int.zero) Enil). EvalOp.
  instantiate (1 := Clt). intros [v2 [A2 B2]].
  unfold Val.cmp in B2. simpl in B2.
  rewrite <- (Int64.ofwords_recompose x). rewrite decompose_cmpl_lt_zero.
  destruct (Int.lt (Int64.hiword x) Int.zero); inv B2; auto.
+ exploit (eval_cmpl_gen Clt Clt). eexact H. eexact H0. simpl.
  rewrite <- Int64.decompose_lt. rewrite ! Int64.ofwords_recompose. auto.
- (* Cle *)
  exploit (eval_cmpl_gen Clt Cle). eexact H. eexact H0. intros. 
  rewrite <- (Int64.ofwords_recompose x). rewrite <- (Int64.ofwords_recompose y).
  rewrite Int64.decompose_le. auto. 
- (* Cgt *)
  exploit (eval_cmpl_gen Cgt Cgt). eexact H. eexact H0. simpl.
  rewrite Int.eq_sym. rewrite <- Int64.decompose_lt. rewrite ! Int64.ofwords_recompose. auto.
- (* Cge *)
  destruct (is_longconst_zero b) eqn:LC.
+ exploit is_longconst_zero_sound; eauto. intros EQ; inv EQ; clear H0.
  exploit eval_highlong. eexact H. intros [v1 [A1 B1]]. simpl in B1; inv B1.
  exploit eval_comp. eexact A1. 
  instantiate (2 := Eop (Ointconst Int.zero) Enil). EvalOp.
  instantiate (1 := Cge). intros [v2 [A2 B2]].
  unfold Val.cmp in B2; simpl in B2. 
  rewrite <- (Int64.ofwords_recompose x). rewrite decompose_cmpl_lt_zero.
  destruct (negb (Int.lt (Int64.hiword x) Int.zero)); inv B2; auto.
+ exploit (eval_cmpl_gen Cgt Cge). eexact H. eexact H0. intros. 
  rewrite <- (Int64.ofwords_recompose x). rewrite <- (Int64.ofwords_recompose y).
  rewrite Int64.decompose_le. rewrite Int.eq_sym. auto.
Qed.

End CMCONSTR.

