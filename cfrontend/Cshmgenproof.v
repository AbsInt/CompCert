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

(** * Correctness of the translation from Clight to C#minor. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import AST.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Clight.
Require Import Cminor.
Require Import Csharpminor.
Require Import Cshmgen.

(** * Properties of operations over types *)

Remark transl_params_types:
  forall params,
  map typ_of_type (map snd params) = typlist_of_typelist (type_of_params params).
Proof.
  induction params; simpl. auto. destruct a as [id ty]; simpl. f_equal; auto.
Qed.

Lemma transl_fundef_sig1:
  forall ce f tf args res cc,
  transl_fundef ce f = OK tf ->
  classify_fun (type_of_fundef f) = fun_case_f args res cc ->
  funsig tf = signature_of_type args res cc.
Proof.
  intros. destruct f; simpl in *.
  monadInv H. monadInv EQ. simpl. inversion H0.
  unfold signature_of_function, signature_of_type.
  f_equal. apply transl_params_types.
  destruct (signature_eq (ef_sig e) (signature_of_type t t0 c)); inv H.
  simpl. congruence.
Qed.

Lemma transl_fundef_sig2:
  forall ce f tf args res cc,
  transl_fundef ce f = OK tf ->
  type_of_fundef f = Tfunction args res cc ->
  funsig tf = signature_of_type args res cc.
Proof.
  intros. eapply transl_fundef_sig1; eauto.
  rewrite H0; reflexivity.
Qed.

(** * Properties of the translation functions *)

(** Transformation of expressions and statements. *)

Lemma transl_expr_lvalue:
  forall ge e le m a loc ofs ta,
  Clight.eval_lvalue ge e le m a loc ofs ->
  transl_expr ge a = OK ta ->
  (exists tb, transl_lvalue ge a = OK tb /\ make_load tb (typeof a) = OK ta).
Proof.
  intros until ta; intros EVAL TR. inv EVAL; simpl in TR.
  (* var local *)
  exists (Eaddrof id); auto.
  (* var global *)
  exists (Eaddrof id); auto.
  (* deref *)
  monadInv TR. exists x; auto.
  (* field struct *)
  monadInv TR. exists x0; split; auto. simpl; rewrite EQ; auto.
  (* field union *)
  monadInv TR. exists x0; split; auto. simpl; rewrite EQ; auto.
Qed.

(** Properties of labeled statements *)

Lemma transl_lbl_stmt_1:
  forall ce tyret nbrk ncnt n sl tsl,
  transl_lbl_stmt ce tyret nbrk ncnt sl = OK tsl ->
  transl_lbl_stmt ce tyret nbrk ncnt (Clight.select_switch n sl) = OK (select_switch n tsl).
Proof.
  intros until n.
  assert (DFL: forall sl tsl,
    transl_lbl_stmt ce tyret nbrk ncnt sl = OK tsl ->
    transl_lbl_stmt ce tyret nbrk ncnt (Clight.select_switch_default sl) = OK (select_switch_default tsl)).
  {
    induction sl; simpl; intros.
    inv H; auto.
    monadInv H. simpl. destruct o; eauto. simpl; rewrite EQ; simpl; rewrite EQ1; auto.
  }
  assert (CASE: forall sl tsl,
    transl_lbl_stmt ce tyret nbrk ncnt sl = OK tsl ->
    match Clight.select_switch_case n sl with
    | None =>
        select_switch_case n tsl = None
    | Some sl' =>
        exists tsl',
           select_switch_case n tsl = Some tsl'
        /\ transl_lbl_stmt ce tyret nbrk ncnt sl' = OK tsl'
    end).
  {
    induction sl; simpl; intros.
    inv H; auto.
    monadInv H; simpl. destruct o. destruct (zeq z n).
    econstructor; split; eauto. simpl; rewrite EQ; simpl; rewrite EQ1; auto.
    apply IHsl; auto.
    apply IHsl; auto.
  }
  intros. specialize (CASE _ _ H). unfold Clight.select_switch, select_switch.
  destruct (Clight.select_switch_case n sl) as [sl'|].
  destruct CASE as [tsl' [P Q]]. rewrite P, Q. auto.
  rewrite CASE. auto.
Qed.

Lemma transl_lbl_stmt_2:
  forall ce tyret nbrk ncnt sl tsl,
  transl_lbl_stmt ce tyret nbrk ncnt sl = OK tsl ->
  transl_statement ce tyret nbrk ncnt (seq_of_labeled_statement sl) = OK (seq_of_lbl_stmt tsl).
Proof.
  induction sl; intros.
  monadInv H. auto.
  monadInv H. simpl. rewrite EQ; simpl. rewrite (IHsl _ EQ1). simpl. auto.
Qed.

(** * Correctness of Csharpminor construction functions *)

Section CONSTRUCTORS.

Variable ce: composite_env.
Variable ge: genv.

Lemma make_intconst_correct:
  forall n e le m,
  eval_expr ge e le m (make_intconst n) (Vint n).
Proof.
  intros. unfold make_intconst. econstructor. reflexivity.
Qed.

Lemma make_floatconst_correct:
  forall n e le m,
  eval_expr ge e le m (make_floatconst n) (Vfloat n).
Proof.
  intros. unfold make_floatconst. econstructor. reflexivity.
Qed.

Lemma make_singleconst_correct:
  forall n e le m,
  eval_expr ge e le m (make_singleconst n) (Vsingle n).
Proof.
  intros. unfold make_singleconst. econstructor. reflexivity.
Qed.

Lemma make_longconst_correct:
  forall n e le m,
  eval_expr ge e le m (make_longconst n) (Vlong n).
Proof.
  intros. unfold make_floatconst. econstructor. reflexivity.
Qed.

Lemma make_singleoffloat_correct:
  forall a n e le m,
  eval_expr ge e le m a (Vfloat n) ->
  eval_expr ge e le m (make_singleoffloat a) (Vsingle (Float.to_single n)).
Proof.
  intros. econstructor. eauto. auto.
Qed.

Lemma make_floatofsingle_correct:
  forall a n e le m,
  eval_expr ge e le m a (Vsingle n) ->
  eval_expr ge e le m (make_floatofsingle a) (Vfloat (Float.of_single n)).
Proof.
  intros. econstructor. eauto. auto.
Qed.

Lemma make_floatofint_correct:
  forall a n sg e le m,
  eval_expr ge e le m a (Vint n) ->
  eval_expr ge e le m (make_floatofint a sg) (Vfloat(cast_int_float sg n)).
Proof.
  intros. unfold make_floatofint, cast_int_float.
  destruct sg; econstructor; eauto.
Qed.

Hint Resolve make_intconst_correct make_floatconst_correct make_longconst_correct
             make_singleconst_correct make_singleoffloat_correct make_floatofsingle_correct
             make_floatofint_correct: cshm.
Hint Constructors eval_expr eval_exprlist: cshm.
Hint Extern 2 (@eq trace _ _) => traceEq: cshm.

Lemma make_cmp_ne_zero_correct:
  forall e le m a n,
  eval_expr ge e le m a (Vint n) ->
  eval_expr ge e le m (make_cmp_ne_zero a) (Vint (if Int.eq n Int.zero then Int.zero else Int.one)).
Proof.
  intros.
  assert (DEFAULT: eval_expr ge e le m (Ebinop (Ocmp Cne) a (make_intconst Int.zero))
                                       (Vint (if Int.eq n Int.zero then Int.zero else Int.one))).
    econstructor; eauto with cshm. simpl. unfold Val.cmp, Val.cmp_bool.
    unfold Int.cmp. destruct (Int.eq n Int.zero); auto.
  assert (CMP: forall ob,
               Val.of_optbool ob = Vint n ->
               n = (if Int.eq n Int.zero then Int.zero else Int.one)).
    intros. destruct ob; simpl in H0; inv H0. destruct b; inv H2.
    rewrite Int.eq_false. auto. apply Int.one_not_zero.
    rewrite Int.eq_true. auto.
  destruct a; simpl; auto. destruct b; auto.
  inv H. econstructor; eauto. rewrite H6. decEq. decEq.
  simpl in H6. inv H6. unfold Val.cmp in H0. eauto.
  inv H. econstructor; eauto. rewrite H6. decEq. decEq.
  simpl in H6. inv H6. unfold Val.cmp in H0. eauto.
  inv H. econstructor; eauto. rewrite H6. decEq. decEq.
  simpl in H6. inv H6. unfold Val.cmp in H0. eauto.
  inv H. econstructor; eauto. rewrite H6. decEq. decEq.
  simpl in H6. unfold Val.cmpfs in H6.
  destruct (Val.cmpfs_bool c v1 v2) as [[]|]; inv H6; reflexivity.
  inv H. econstructor; eauto. rewrite H6. decEq. decEq.
  simpl in H6. unfold Val.cmpl in H6.
  destruct (Val.cmpl_bool c v1 v2) as [[]|]; inv H6; reflexivity.
  inv H. econstructor; eauto. rewrite H6. decEq. decEq.
  simpl in H6. unfold Val.cmplu in H6.
  destruct (Val.cmplu_bool c v1 v2) as [[]|]; inv H6; reflexivity.
Qed.

Lemma make_cast_int_correct:
  forall e le m a n sz si,
  eval_expr ge e le m a (Vint n) ->
  eval_expr ge e le m (make_cast_int a sz si) (Vint (cast_int_int sz si n)).
Proof.
  intros. unfold make_cast_int, cast_int_int.
  destruct sz.
  destruct si; eauto with cshm.
  destruct si; eauto with cshm.
  auto.
  apply make_cmp_ne_zero_correct; auto.
Qed.

Hint Resolve make_cast_int_correct: cshm.

Lemma make_cast_correct:
  forall e le m a b v ty1 ty2 v',
  make_cast ty1 ty2 a = OK b ->
  eval_expr ge e le m a v ->
  sem_cast v ty1 ty2 = Some v' ->
  eval_expr ge e le m b v'.
Proof.
  intros. unfold make_cast, sem_cast in *;
  destruct (classify_cast ty1 ty2); inv H; destruct v; inv H1; eauto with cshm.
  (* single -> int *)
  unfold make_singleofint, cast_int_float. destruct si1; eauto with cshm.
  (* float -> int *)
  destruct (cast_float_int si2 f) as [i|] eqn:E; inv H2.
  apply make_cast_int_correct.
  unfold cast_float_int in E. unfold make_intoffloat.
  destruct si2; econstructor; eauto; simpl; rewrite E; auto.
  (* single -> int *)
  destruct (cast_single_int si2 f) as [i|] eqn:E; inv H2.
  apply make_cast_int_correct.
  unfold cast_single_int in E. unfold make_intofsingle.
  destruct si2; econstructor; eauto with cshm; simpl; rewrite E; auto.
  (* long -> int *)
  unfold make_longofint, cast_int_long. destruct si1; eauto with cshm.
  (* long -> float *)
  unfold make_floatoflong, cast_long_float. destruct si1; eauto with cshm.
  (* long -> single *)
  unfold make_singleoflong, cast_long_single. destruct si1; eauto with cshm.
  (* float -> long *)
  destruct (cast_float_long si2 f) as [i|] eqn:E; inv H2.
  unfold cast_float_long in E. unfold make_longoffloat.
  destruct si2; econstructor; eauto; simpl; rewrite E; auto.
  (* single -> long *)
  destruct (cast_single_long si2 f) as [i|] eqn:E; inv H2.
  unfold cast_single_long in E. unfold make_longofsingle.
  destruct si2; econstructor; eauto with cshm; simpl; rewrite E; auto.
  (* float -> bool *)
  econstructor; eauto with cshm.
  simpl. unfold Val.cmpf, Val.cmpf_bool. rewrite Float.cmp_ne_eq.
  destruct (Float.cmp Ceq f Float.zero); auto.
  (* single -> bool *)
  econstructor; eauto with cshm.
  simpl. unfold Val.cmpfs, Val.cmpfs_bool. rewrite Float32.cmp_ne_eq.
  destruct (Float32.cmp Ceq f Float32.zero); auto.
  (* long -> bool *)
  econstructor; eauto with cshm.
  simpl. unfold Val.cmpl, Val.cmpl_bool, Int64.cmp.
  destruct (Int64.eq i Int64.zero); auto.
  (* int -> bool *)
  econstructor; eauto with cshm.
  simpl. unfold Val.cmpu, Val.cmpu_bool, Int.cmpu.
  destruct (Int.eq i Int.zero); auto.
  (* struct *)
  destruct (ident_eq id1 id2); inv H2; auto.
  (* union *)
  destruct (ident_eq id1 id2); inv H2; auto.
Qed.

Lemma make_boolean_correct:
 forall e le m a v ty b,
  eval_expr ge e le m a v ->
  bool_val v ty m = Some b ->
  exists vb,
    eval_expr ge e le m (make_boolean a ty) vb
    /\ Val.bool_of_val vb b.
Proof.
  intros. unfold make_boolean. unfold bool_val in H0.
  destruct (classify_bool ty); destruct v; inv H0.
(* int *)
  econstructor; split. apply make_cmp_ne_zero_correct with (n := i); auto.
  destruct (Int.eq i Int.zero); simpl; constructor.
(* float *)
  econstructor; split. econstructor; eauto with cshm. simpl. eauto.
  unfold Val.cmpf, Val.cmpf_bool. simpl. rewrite <- Float.cmp_ne_eq.
  destruct (Float.cmp Cne f Float.zero); constructor.
(* single *)
  econstructor; split. econstructor; eauto with cshm. simpl. eauto.
  unfold Val.cmpfs, Val.cmpfs_bool. simpl. rewrite <- Float32.cmp_ne_eq.
  destruct (Float32.cmp Cne f Float32.zero); constructor.
(* pointer *)
  econstructor; split. econstructor; eauto with cshm. simpl. eauto.
  unfold Val.cmpu, Val.cmpu_bool. simpl.
  destruct (Int.eq i Int.zero); simpl; constructor.
  econstructor; split. econstructor; eauto with cshm. simpl. eauto.
  destruct (Mem.weak_valid_pointer m b0 (Int.unsigned i)) eqn:V; inv H2.
  unfold Val.cmpu, Val.cmpu_bool. simpl.
  unfold Mem.weak_valid_pointer in V; rewrite V. constructor.
(* long *)
  econstructor; split. econstructor; eauto with cshm. simpl. unfold Val.cmpl. simpl. eauto.
  destruct (Int64.eq i Int64.zero); simpl; constructor.
Qed.

Lemma make_neg_correct:
  forall a tya c va v e le m,
  sem_neg va tya = Some v ->
  make_neg a tya = OK c ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m c v.
Proof.
  unfold sem_neg, make_neg; intros until m; intros SEM MAKE EV1;
  destruct (classify_neg tya); inv MAKE; destruct va; inv SEM; eauto with cshm.
Qed.

Lemma make_absfloat_correct:
  forall a tya c va v e le m,
  sem_absfloat va tya = Some v ->
  make_absfloat a tya = OK c ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m c v.
Proof.
  unfold sem_absfloat, make_absfloat; intros until m; intros SEM MAKE EV1;
  destruct (classify_neg tya); inv MAKE; destruct va; inv SEM; eauto with cshm.
  unfold make_floatoflong, cast_long_float. destruct s.
  econstructor. econstructor; simpl; eauto. simpl; eauto. simpl; eauto.
  econstructor. econstructor; simpl; eauto. simpl; eauto. simpl; eauto.
Qed.

Lemma make_notbool_correct:
  forall a tya c va v e le m,
  sem_notbool va tya m = Some v ->
  make_notbool a tya = OK c ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m c v.
Proof.
  unfold sem_notbool, make_notbool; intros until m; intros SEM MAKE EV1;
  destruct (classify_bool tya); inv MAKE; destruct va; inv SEM; eauto with cshm.
  destruct (Mem.weak_valid_pointer m b (Int.unsigned i)) eqn:V; inv H0.
  econstructor; eauto with cshm. simpl. unfold Val.cmpu, Val.cmpu_bool.
  unfold Mem.weak_valid_pointer in V; rewrite V. auto.
Qed.

Lemma make_notint_correct:
  forall a tya c va v e le m,
  sem_notint va tya = Some v ->
  make_notint a tya = OK c ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m c v.
Proof.
  unfold sem_notint, make_notint; intros until m; intros SEM MAKE EV1;
  destruct (classify_notint tya); inv MAKE; destruct va; inv SEM; eauto with cshm.
Qed.

Definition binary_constructor_correct
    (make: expr -> type -> expr -> type -> res expr)
    (sem: val -> type -> val -> type -> option val): Prop :=
  forall a tya b tyb c va vb v e le m,
  sem va tya vb tyb = Some v ->
  make a tya b tyb = OK c ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m b vb ->
  eval_expr ge e le m c v.

Section MAKE_BIN.

Variable sem_int: signedness -> int -> int -> option val.
Variable sem_long: signedness -> int64 -> int64 -> option val.
Variable sem_float: float -> float -> option val.
Variable sem_single: float32 -> float32 -> option val.
Variables iop iopu fop sop lop lopu: binary_operation.

Hypothesis iop_ok:
  forall x y m, eval_binop iop (Vint x) (Vint y) m = sem_int Signed x y.
Hypothesis iopu_ok:
  forall x y m, eval_binop iopu (Vint x) (Vint y) m = sem_int Unsigned x y.
Hypothesis lop_ok:
  forall x y m, eval_binop lop (Vlong x) (Vlong y) m = sem_long Signed x y.
Hypothesis lopu_ok:
  forall x y m, eval_binop lopu (Vlong x) (Vlong y) m = sem_long Unsigned x y.
Hypothesis fop_ok:
  forall x y m, eval_binop fop (Vfloat x) (Vfloat y) m = sem_float x y.
Hypothesis sop_ok:
  forall x y m, eval_binop sop (Vsingle x) (Vsingle y) m = sem_single x y.

Lemma make_binarith_correct:
  binary_constructor_correct
    (make_binarith iop iopu fop sop lop lopu)
    (sem_binarith sem_int sem_long sem_float sem_single).
Proof.
  red; unfold make_binarith, sem_binarith;
  intros until m; intros SEM MAKE EV1 EV2.
  set (cls := classify_binarith tya tyb) in *.
  set (ty := binarith_type cls) in *.
  monadInv MAKE.
  destruct (sem_cast va tya ty) as [va'|] eqn:Ca; try discriminate.
  destruct (sem_cast vb tyb ty) as [vb'|] eqn:Cb; try discriminate.
  exploit make_cast_correct. eexact EQ. eauto. eauto. intros EV1'.
  exploit make_cast_correct. eexact EQ1. eauto. eauto. intros EV2'.
  destruct cls; inv EQ2; destruct va'; try discriminate; destruct vb'; try discriminate.
- destruct s; inv H0; econstructor; eauto with cshm.
  rewrite iop_ok; auto. rewrite iopu_ok; auto.
- destruct s; inv H0; econstructor; eauto with cshm.
  rewrite lop_ok; auto. rewrite lopu_ok; auto.
- erewrite <- fop_ok in SEM; eauto with cshm.
- erewrite <- sop_ok in SEM; eauto with cshm.
Qed.

Lemma make_binarith_int_correct:
  binary_constructor_correct
    (make_binarith_int iop iopu lop lopu)
    (sem_binarith sem_int sem_long (fun x y => None) (fun x y => None)).
Proof.
  red; unfold make_binarith_int, sem_binarith;
  intros until m; intros SEM MAKE EV1 EV2.
  set (cls := classify_binarith tya tyb) in *.
  set (ty := binarith_type cls) in *.
  monadInv MAKE.
  destruct (sem_cast va tya ty) as [va'|] eqn:Ca; try discriminate.
  destruct (sem_cast vb tyb ty) as [vb'|] eqn:Cb; try discriminate.
  exploit make_cast_correct. eexact EQ. eauto. eauto. intros EV1'.
  exploit make_cast_correct. eexact EQ1. eauto. eauto. intros EV2'.
  destruct cls; inv EQ2; destruct va'; try discriminate; destruct vb'; try discriminate.
- destruct s; inv H0; econstructor; eauto with cshm.
  rewrite iop_ok; auto. rewrite iopu_ok; auto.
- destruct s; inv H0; econstructor; eauto with cshm.
  rewrite lop_ok; auto. rewrite lopu_ok; auto.
Qed.

End MAKE_BIN.

Hint Extern 2 (@eq (option val) _ _) => (simpl; reflexivity) : cshm.

Lemma make_add_correct: binary_constructor_correct (make_add ce) (sem_add ce).
Proof.
  red; unfold make_add, sem_add;
  intros until m; intros SEM MAKE EV1 EV2;
  destruct (classify_add tya tyb); inv MAKE.
- destruct va; try discriminate; destruct vb; inv SEM; eauto with cshm.
- destruct va; try discriminate; destruct vb; inv SEM; eauto with cshm.
- destruct va; try discriminate; destruct vb; inv SEM; eauto with cshm.
- destruct va; try discriminate; destruct vb; inv SEM; eauto with cshm.
- eapply make_binarith_correct; eauto; intros; auto.
Qed.

Lemma make_sub_correct: binary_constructor_correct (make_sub ce) (sem_sub ce).
Proof.
  red; unfold make_sub, sem_sub;
  intros until m; intros SEM MAKE EV1 EV2;
  destruct (classify_sub tya tyb); inv MAKE.
- destruct va; try discriminate; destruct vb; inv SEM; eauto with cshm.
- destruct va; try discriminate; destruct vb; inv SEM.
  destruct (eq_block b0 b1); try discriminate.
  set (sz := sizeof ce ty) in *.
  destruct (zlt 0 sz); try discriminate.
  destruct (zle sz Int.max_signed); simpl in H0; inv H0.
  econstructor; eauto with cshm.
  rewrite dec_eq_true; simpl.
  assert (E: Int.signed (Int.repr sz) = sz).
  { apply Int.signed_repr. generalize Int.min_signed_neg; omega. }
  predSpec Int.eq Int.eq_spec (Int.repr sz) Int.zero.
  rewrite H in E; rewrite Int.signed_zero in E; omegaContradiction.
  predSpec Int.eq Int.eq_spec (Int.repr sz) Int.mone.
  rewrite H0 in E; rewrite Int.signed_mone in E; omegaContradiction.
  rewrite andb_false_r; auto.
- destruct va; try discriminate; destruct vb; inv SEM; eauto with cshm.
- eapply make_binarith_correct; eauto; intros; auto.
Qed.

Lemma make_mul_correct: binary_constructor_correct make_mul sem_mul.
Proof.
  apply make_binarith_correct; intros; auto.
Qed.

Lemma make_div_correct: binary_constructor_correct make_div sem_div.
Proof.
  apply make_binarith_correct; intros; auto.
Qed.

Lemma make_mod_correct: binary_constructor_correct make_mod sem_mod.
Proof.
  apply make_binarith_int_correct; intros; auto.
Qed.

Lemma make_and_correct: binary_constructor_correct make_and sem_and.
Proof.
  apply make_binarith_int_correct; intros; auto.
Qed.

Lemma make_or_correct: binary_constructor_correct make_or sem_or.
Proof.
  apply make_binarith_int_correct; intros; auto.
Qed.

Lemma make_xor_correct: binary_constructor_correct make_xor sem_xor.
Proof.
  apply make_binarith_int_correct; intros; auto.
Qed.

Ltac comput val :=
  let x := fresh in set val as x in *; vm_compute in x; subst x.

Remark small_shift_amount_1:
  forall i,
  Int64.ltu i Int64.iwordsize = true ->
  Int.ltu (Int64.loword i) Int64.iwordsize' = true
  /\ Int64.unsigned i = Int.unsigned (Int64.loword i).
Proof.
  intros. apply Int64.ltu_inv in H. comput (Int64.unsigned Int64.iwordsize).
  assert (Int64.unsigned i = Int.unsigned (Int64.loword i)).
  {
    unfold Int64.loword. rewrite Int.unsigned_repr; auto.
    comput Int.max_unsigned; omega.
  }
  split; auto. unfold Int.ltu. apply zlt_true. rewrite <- H0. tauto.
Qed.

Remark small_shift_amount_2:
  forall i,
  Int64.ltu i (Int64.repr 32) = true ->
  Int.ltu (Int64.loword i) Int.iwordsize = true.
Proof.
  intros. apply Int64.ltu_inv in H. comput (Int64.unsigned (Int64.repr 32)).
  assert (Int64.unsigned i = Int.unsigned (Int64.loword i)).
  {
    unfold Int64.loword. rewrite Int.unsigned_repr; auto.
    comput Int.max_unsigned; omega.
  }
  unfold Int.ltu. apply zlt_true. rewrite <- H0. tauto.
Qed.

Lemma small_shift_amount_3:
  forall i,
  Int.ltu i Int64.iwordsize' = true ->
  Int64.unsigned (Int64.repr (Int.unsigned i)) = Int.unsigned i.
Proof.
  intros. apply Int.ltu_inv in H. comput (Int.unsigned Int64.iwordsize').
  apply Int64.unsigned_repr. comput Int64.max_unsigned; omega.
Qed.

Lemma make_shl_correct: binary_constructor_correct make_shl sem_shl.
Proof.
  red; unfold make_shl, sem_shl, sem_shift;
  intros until m; intros SEM MAKE EV1 EV2;
  destruct (classify_shift tya tyb); inv MAKE;
  destruct va; try discriminate; destruct vb; try discriminate.
- destruct (Int.ltu i0 Int.iwordsize) eqn:E; inv SEM.
  econstructor; eauto. simpl; rewrite E; auto.
- destruct (Int64.ltu i0 Int64.iwordsize) eqn:E; inv SEM.
  exploit small_shift_amount_1; eauto. intros [A B].
  econstructor; eauto with cshm. simpl. rewrite A.
  f_equal; f_equal. unfold Int64.shl', Int64.shl. rewrite B; auto.
- destruct (Int64.ltu i0 (Int64.repr 32)) eqn:E; inv SEM.
  econstructor; eauto with cshm. simpl. rewrite small_shift_amount_2; auto.
- destruct (Int.ltu i0 Int64.iwordsize') eqn:E; inv SEM.
  econstructor; eauto with cshm. simpl. rewrite E.
  unfold Int64.shl', Int64.shl. rewrite small_shift_amount_3; auto.
Qed.

Lemma make_shr_correct: binary_constructor_correct make_shr sem_shr.
Proof.
  red; unfold make_shr, sem_shr, sem_shift;
  intros until m; intros SEM MAKE EV1 EV2;
  destruct (classify_shift tya tyb); inv MAKE;
  destruct va; try discriminate; destruct vb; try discriminate.
- destruct (Int.ltu i0 Int.iwordsize) eqn:E; inv SEM.
  destruct s; inv H0; econstructor; eauto; simpl; rewrite E; auto.
- destruct (Int64.ltu i0 Int64.iwordsize) eqn:E; inv SEM.
  exploit small_shift_amount_1; eauto. intros [A B].
  destruct s; inv H0; econstructor; eauto with cshm; simpl; rewrite A;
  f_equal; f_equal.
  unfold Int64.shr', Int64.shr; rewrite B; auto.
  unfold Int64.shru', Int64.shru; rewrite B; auto.
- destruct (Int64.ltu i0 (Int64.repr 32)) eqn:E; inv SEM.
  destruct s; inv H0; econstructor; eauto with cshm; simpl; rewrite small_shift_amount_2; auto.
- destruct (Int.ltu i0 Int64.iwordsize') eqn:E; inv SEM.
  destruct s; inv H0; econstructor; eauto with cshm; simpl; rewrite E.
  unfold Int64.shr', Int64.shr; rewrite small_shift_amount_3; auto.
  unfold Int64.shru', Int64.shru; rewrite small_shift_amount_3; auto.
Qed.

Lemma make_cmp_correct:
  forall cmp a tya b tyb c va vb v e le m,
  sem_cmp cmp va tya vb tyb m = Some v ->
  make_cmp cmp a tya b tyb = OK c ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m b vb ->
  eval_expr ge e le m c v.
Proof.
  unfold sem_cmp, make_cmp; intros until m; intros SEM MAKE EV1 EV2;
  destruct (classify_cmp tya tyb).
- inv MAKE. destruct (Val.cmpu_bool (Mem.valid_pointer m) cmp va vb) as [bv|] eqn:E;
  simpl in SEM; inv SEM.
  econstructor; eauto. simpl. unfold Val.cmpu. rewrite E. auto.
- inv MAKE. destruct vb; try discriminate.
  set (vb := Vint (Int.repr (Int64.unsigned i))) in *.
  destruct (Val.cmpu_bool (Mem.valid_pointer m) cmp va vb) as [bv|] eqn:E;
  simpl in SEM; inv SEM.
  econstructor; eauto with cshm. simpl. change (Vint (Int64.loword i)) with vb.
  unfold Val.cmpu. rewrite E. auto.
- inv MAKE. destruct va; try discriminate.
  set (va := Vint (Int.repr (Int64.unsigned i))) in *.
  destruct (Val.cmpu_bool (Mem.valid_pointer m) cmp va vb) as [bv|] eqn:E;
  simpl in SEM; inv SEM.
  econstructor; eauto with cshm. simpl. change (Vint (Int64.loword i)) with va.
  unfold Val.cmpu. rewrite E. auto.
- eapply make_binarith_correct; eauto; intros; auto.
Qed.

Lemma transl_unop_correct:
  forall op a tya c va v e le m,
  transl_unop op a tya = OK c ->
  sem_unary_operation op va tya m = Some v ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m c v.
Proof.
  intros. destruct op; simpl in *.
  eapply make_notbool_correct; eauto.
  eapply make_notint_correct; eauto.
  eapply make_neg_correct; eauto.
  eapply make_absfloat_correct; eauto.
Qed.

Lemma transl_binop_correct:
  forall op a tya b tyb c va vb v e le m,
  transl_binop ce op a tya b tyb = OK c ->
  sem_binary_operation ce op va tya vb tyb m = Some v ->
  eval_expr ge e le m a va ->
  eval_expr ge e le m b vb ->
  eval_expr ge e le m c v.
Proof.
  intros. destruct op; simpl in *.
  eapply make_add_correct; eauto.
  eapply make_sub_correct; eauto.
  eapply make_mul_correct; eauto.
  eapply make_div_correct; eauto.
  eapply make_mod_correct; eauto.
  eapply make_and_correct; eauto.
  eapply make_or_correct; eauto.
  eapply make_xor_correct; eauto.
  eapply make_shl_correct; eauto.
  eapply make_shr_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
  eapply make_cmp_correct; eauto.
Qed.

Lemma make_load_correct:
  forall addr ty code b ofs v e le m,
  make_load addr ty = OK code ->
  eval_expr ge e le m addr (Vptr b ofs) ->
  deref_loc ty m b ofs v ->
  eval_expr ge e le m code v.
Proof.
  unfold make_load; intros until m; intros MKLOAD EVEXP DEREF.
  inv DEREF.
  (* scalar *)
  rewrite H in MKLOAD. inv MKLOAD. apply eval_Eload with (Vptr b ofs); auto.
  (* by reference *)
  rewrite H in MKLOAD. inv MKLOAD. auto.
  (* by copy *)
  rewrite H in MKLOAD. inv MKLOAD. auto.
Qed.

Lemma make_memcpy_correct:
  forall ce f dst src ty k e le m b ofs v m',
  eval_expr ge e le m dst (Vptr b ofs) ->
  eval_expr ge e le m src v ->
  assign_loc ce ty m b ofs v m' ->
  access_mode ty = By_copy ->
  step ge (State f (make_memcpy ce dst src ty) k e le m) E0 (State f Sskip k e le m').
Proof.
  intros. inv H1; try congruence.
  unfold make_memcpy. change le with (set_optvar None Vundef le) at 2.
  econstructor.
  econstructor. eauto. econstructor. eauto. constructor.
  econstructor; eauto.
  apply alignof_blockcopy_1248.
  apply sizeof_pos.
  apply sizeof_alignof_blockcopy_compat.
Qed.

Lemma make_store_correct:
  forall addr ty rhs code e le m b ofs v m' f k,
  make_store ce addr ty rhs = OK code ->
  eval_expr ge e le m addr (Vptr b ofs) ->
  eval_expr ge e le m rhs v ->
  assign_loc ce ty m b ofs v m' ->
  step ge (State f code k e le m) E0 (State f Sskip k e le m').
Proof.
  unfold make_store. intros until k; intros MKSTORE EV1 EV2 ASSIGN.
  inversion ASSIGN; subst.
  (* nonvolatile scalar *)
  rewrite H in MKSTORE; inv MKSTORE.
  econstructor; eauto.
  (* by copy *)
  rewrite H in MKSTORE; inv MKSTORE.
  eapply make_memcpy_correct; eauto.
Qed.

End CONSTRUCTORS.

(** * Basic preservation invariants *)

Section CORRECTNESS.

Variable prog: Clight.program.
Variable tprog: Csharpminor.program.
Hypothesis TRANSL: transl_program prog = OK tprog.

Let ge := globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall s, Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf_partial2 (transl_fundef ge) transl_globvar _ TRANSL).

Lemma public_preserved:
  forall s, Genv.public_symbol tge s = Genv.public_symbol ge s.
Proof (Genv.public_symbol_transf_partial2 (transl_fundef ge) transl_globvar _ TRANSL).

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ transl_fundef ge f = OK tf.
Proof (Genv.find_funct_transf_partial2 (transl_fundef ge) transl_globvar _ TRANSL).

Lemma function_ptr_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transl_fundef ge f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial2 (transl_fundef ge) transl_globvar _ TRANSL).

Lemma block_is_volatile_preserved:
  forall b, Genv.block_is_volatile tge b = Genv.block_is_volatile ge b.
Proof (Genv.block_is_volatile_transf_partial2 (transl_fundef ge) transl_globvar _ TRANSL).

(** * Matching between environments *)

(** In this section, we define a matching relation between
  a Clight local environment and a Csharpminor local environment. *)

Record match_env (e: Clight.env) (te: Csharpminor.env) : Prop :=
  mk_match_env {
    me_local:
      forall id b ty,
      e!id = Some (b, ty) -> te!id = Some(b, sizeof ge ty);
    me_local_inv:
      forall id b sz,
      te!id = Some (b, sz) -> exists ty, e!id = Some(b, ty)
  }.

Lemma match_env_globals:
  forall e te id,
  match_env e te ->
  e!id = None ->
  te!id = None.
Proof.
  intros. destruct (te!id) as [[b sz] | ] eqn:?; auto.
  exploit me_local_inv; eauto. intros [ty EQ]. congruence.
Qed.

Lemma match_env_same_blocks:
  forall e te,
  match_env e te ->
  blocks_of_env te = Clight.blocks_of_env ge e.
Proof.
  intros.
  set (R := fun (x: (block * type)) (y: (block * Z)) =>
         match x, y with
         | (b1, ty), (b2, sz) => b2 = b1 /\ sz = sizeof ge ty
         end).
  assert (list_forall2
            (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
            (PTree.elements e) (PTree.elements te)).
  apply PTree.elements_canonical_order.
  intros id [b ty] GET. exists (b, sizeof ge ty); split. eapply me_local; eauto. red; auto.
  intros id [b sz] GET. exploit me_local_inv; eauto. intros [ty EQ].
  exploit me_local; eauto. intros EQ1.
  exists (b, ty); split. auto. red; split; congruence.

  unfold blocks_of_env, Clight.blocks_of_env.
  generalize H0. induction 1. auto.
  simpl. f_equal; auto.
  unfold block_of_binding, Clight.block_of_binding.
  destruct a1 as [id1 [blk1 ty1]]. destruct b1 as [id2 [blk2 sz2]].
  simpl in *. destruct H1 as [A [B C]]. congruence.
Qed.

Lemma match_env_free_blocks:
  forall e te m m',
  match_env e te ->
  Mem.free_list m (Clight.blocks_of_env ge e) = Some m' ->
  Mem.free_list m (blocks_of_env te) = Some m'.
Proof.
  intros. rewrite (match_env_same_blocks _ _ H). auto.
Qed.

Lemma match_env_empty:
  match_env Clight.empty_env Csharpminor.empty_env.
Proof.
  unfold Clight.empty_env, Csharpminor.empty_env.
  constructor.
  intros until ty. repeat rewrite PTree.gempty. congruence.
  intros until sz. rewrite PTree.gempty. congruence.
Qed.

(** The following lemmas establish the [match_env] invariant at
  the beginning of a function invocation, after allocation of
  local variables and initialization of the parameters. *)

Lemma match_env_alloc_variables:
  forall e1 m1 vars e2 m2,
  Clight.alloc_variables ge e1 m1 vars e2 m2 ->
  forall te1,
  match_env e1 te1 ->
  exists te2,
  Csharpminor.alloc_variables te1 m1 (map (transl_var ge) vars) te2 m2
  /\ match_env e2 te2.
Proof.
  induction 1; intros; simpl.
  exists te1; split. constructor. auto.
  exploit (IHalloc_variables (PTree.set id (b1, sizeof ge ty) te1)).
  constructor.
    (* me_local *)
    intros until ty0. repeat rewrite PTree.gsspec.
    destruct (peq id0 id); intros. congruence. eapply me_local; eauto.
    (* me_local_inv *)
    intros until sz. repeat rewrite PTree.gsspec.
    destruct (peq id0 id); intros. exists ty; congruence. eapply me_local_inv; eauto.
  intros [te2 [ALLOC MENV]].
  exists te2; split. econstructor; eauto. auto.
Qed.

Lemma create_undef_temps_match:
  forall temps,
  create_undef_temps (map fst temps) = Clight.create_undef_temps temps.
Proof.
  induction temps; simpl. auto.
  destruct a as [id ty]. simpl. decEq. auto.
Qed.

Lemma bind_parameter_temps_match:
  forall vars vals le1 le2,
  Clight.bind_parameter_temps vars vals le1 = Some le2 ->
  bind_parameters (map fst vars) vals le1 = Some le2.
Proof.
  induction vars; simpl; intros.
  destruct vals; inv H. auto.
  destruct a as [id ty]. destruct vals; try discriminate. auto.
Qed.

(** * Proof of semantic preservation *)

(** ** Semantic preservation for expressions *)

(** The proof of semantic preservation for the translation of expressions
  relies on simulation diagrams of the following form:
<<
         e, le, m, a ------------------- te, le, m, ta
            |                                |
            |                                |
            |                                |
            v                                v
         e, le, m, v ------------------- te, le, m, v
>>
  Left: evaluation of r-value expression [a] in Clight.
  Right: evaluation of its translation [ta] in Csharpminor.
  Top (precondition): matching between environments [e], [te],
    plus well-typedness of expression [a].
  Bottom (postcondition): the result values [v]
    are identical in both evaluations.

  We state these diagrams as the following properties, parameterized
  by the Clight evaluation. *)

Section EXPR.

Variable e: Clight.env.
Variable le: temp_env.
Variable m: mem.
Variable te: Csharpminor.env.
Hypothesis MENV: match_env e te.

Lemma transl_expr_lvalue_correct:
  (forall a v,
   Clight.eval_expr ge e le m a v ->
   forall ta (TR: transl_expr ge a = OK ta) ,
   Csharpminor.eval_expr tge te le m ta v)
/\(forall a b ofs,
   Clight.eval_lvalue ge e le m a b ofs ->
   forall ta (TR: transl_lvalue ge a = OK ta),
   Csharpminor.eval_expr tge te le m ta (Vptr b ofs)).
Proof.
  apply eval_expr_lvalue_ind; intros; try (monadInv TR).
(* const int *)
  apply make_intconst_correct.
(* const float *)
  apply make_floatconst_correct.
(* const single *)
  apply make_singleconst_correct.
(* const long *)
  apply make_longconst_correct.
(* temp var *)
  constructor; auto.
(* addrof *)
  simpl in TR. auto.
(* unop *)
  eapply transl_unop_correct; eauto.
(* binop *)
  eapply transl_binop_correct; eauto.
(* cast *)
  eapply make_cast_correct; eauto.
(* sizeof *)
  apply make_intconst_correct.
(* alignof *)
  apply make_intconst_correct.
(* rvalue out of lvalue *)
  exploit transl_expr_lvalue; eauto. intros [tb [TRLVAL MKLOAD]].
  eapply make_load_correct; eauto.
(* var local *)
  exploit (me_local _ _ MENV); eauto. intros EQ.
  econstructor. eapply eval_var_addr_local. eauto.
(* var global *)
  econstructor. eapply eval_var_addr_global.
  eapply match_env_globals; eauto.
  rewrite symbols_preserved. auto.
(* deref *)
  simpl in TR. eauto.
(* field struct *)
  change (prog_comp_env prog) with (genv_cenv ge) in EQ0.
  unfold make_field_access in EQ0; rewrite H1, H2 in EQ0; monadInv EQ0.
  eapply eval_Ebinop; eauto.
  apply make_intconst_correct.
  simpl. congruence.
(* field union *)
  unfold make_field_access in EQ0; rewrite H1 in EQ0; monadInv EQ0.
  auto.
Qed.

Lemma transl_expr_correct:
   forall a v,
   Clight.eval_expr ge e le m a v ->
   forall ta, transl_expr ge a = OK ta ->
   Csharpminor.eval_expr tge te le m ta v.
Proof (proj1 transl_expr_lvalue_correct).

Lemma transl_lvalue_correct:
   forall a b ofs,
   Clight.eval_lvalue ge e le m a b ofs ->
   forall ta, transl_lvalue ge a = OK ta ->
   Csharpminor.eval_expr tge te le m ta (Vptr b ofs).
Proof (proj2 transl_expr_lvalue_correct).

Lemma transl_arglist_correct:
  forall al tyl vl,
  Clight.eval_exprlist ge e le m al tyl vl ->
  forall tal, transl_arglist ge al tyl = OK tal ->
  Csharpminor.eval_exprlist tge te le m tal vl.
Proof.
  induction 1; intros.
  monadInv H. constructor.
  monadInv H2. constructor.
  eapply make_cast_correct; eauto. eapply transl_expr_correct; eauto. auto.
Qed.

Lemma typlist_of_arglist_eq:
  forall al tyl vl,
  Clight.eval_exprlist ge e le m al tyl vl ->
  typlist_of_arglist al tyl = typlist_of_typelist tyl.
Proof.
  induction 1; simpl.
  auto.
  f_equal; auto.
Qed.

End EXPR.

(** ** Semantic preservation for statements *)

(** The simulation diagram for the translation of statements and functions
  is a "plus" diagram of the form
<<
           I
     S1 ------- R1
     |          |
   t |        + | t
     v          v
     S2 ------- R2
           I                         I
>>

The invariant [I] is the [match_states] predicate that we now define.
*)

Inductive match_transl: stmt -> cont -> stmt -> cont -> Prop :=
  | match_transl_0: forall ts tk,
      match_transl ts tk ts tk
  | match_transl_1: forall ts tk,
      match_transl (Sblock ts) tk ts (Kblock tk).

Lemma match_transl_step:
  forall ts tk ts' tk' f te le m,
  match_transl (Sblock ts) tk ts' tk' ->
  star step tge (State f ts' tk' te le m) E0 (State f ts (Kblock tk) te le m).
Proof.
  intros. inv H.
  apply star_one. constructor.
  apply star_refl.
Qed.

Inductive match_cont: type -> nat -> nat -> Clight.cont -> Csharpminor.cont -> Prop :=
  | match_Kstop: forall tyret nbrk ncnt,
      match_cont tyret nbrk ncnt Clight.Kstop Kstop
  | match_Kseq: forall tyret nbrk ncnt s k ts tk,
      transl_statement ge tyret nbrk ncnt s = OK ts ->
      match_cont tyret nbrk ncnt k tk ->
      match_cont tyret nbrk ncnt
                 (Clight.Kseq s k)
                 (Kseq ts tk)
  | match_Kloop1: forall tyret s1 s2 k ts1 ts2 nbrk ncnt tk,
      transl_statement ge tyret 1%nat 0%nat s1 = OK ts1 ->
      transl_statement ge tyret 0%nat (S ncnt) s2 = OK ts2 ->
      match_cont tyret nbrk ncnt k tk ->
      match_cont tyret 1%nat 0%nat
                 (Clight.Kloop1 s1 s2 k)
                 (Kblock (Kseq ts2 (Kseq (Sloop (Sseq (Sblock ts1) ts2)) (Kblock tk))))
  | match_Kloop2: forall tyret s1 s2 k ts1 ts2 nbrk ncnt tk,
      transl_statement ge tyret 1%nat 0%nat s1 = OK ts1 ->
      transl_statement ge tyret 0%nat (S ncnt) s2 = OK ts2 ->
      match_cont tyret nbrk ncnt k tk ->
      match_cont tyret 0%nat (S ncnt)
                 (Clight.Kloop2 s1 s2 k)
                 (Kseq (Sloop (Sseq (Sblock ts1) ts2)) (Kblock tk))
  | match_Kswitch: forall tyret nbrk ncnt k tk,
      match_cont tyret nbrk ncnt k tk ->
      match_cont tyret 0%nat (S ncnt)
                 (Clight.Kswitch k)
                 (Kblock tk)
  | match_Kcall_some: forall tyret nbrk ncnt nbrk' ncnt' f e k id tf te le tk,
      transl_function ge f = OK tf ->
      match_env e te ->
      match_cont (Clight.fn_return f) nbrk' ncnt' k tk ->
      match_cont tyret nbrk ncnt
                 (Clight.Kcall id f e le k)
                 (Kcall id tf te le tk).

Inductive match_states: Clight.state -> Csharpminor.state -> Prop :=
  | match_state:
      forall f nbrk ncnt s k e le m tf ts tk te ts' tk'
          (TRF: transl_function ge f = OK tf)
          (TR: transl_statement ge (Clight.fn_return f) nbrk ncnt s = OK ts)
          (MTR: match_transl ts tk ts' tk')
          (MENV: match_env e te)
          (MK: match_cont (Clight.fn_return f) nbrk ncnt k tk),
      match_states (Clight.State f s k e le m)
                   (State tf ts' tk' te le m)
  | match_callstate:
      forall fd args k m tfd tk targs tres cconv
          (TR: transl_fundef ge fd = OK tfd)
          (MK: match_cont Tvoid 0%nat 0%nat k tk)
          (ISCC: Clight.is_call_cont k)
          (TY: type_of_fundef fd = Tfunction targs tres cconv),
      match_states (Clight.Callstate fd args k m)
                   (Callstate tfd args tk m)
  | match_returnstate:
      forall res k m tk
          (MK: match_cont Tvoid 0%nat 0%nat k tk),
      match_states (Clight.Returnstate res k m)
                   (Returnstate res tk m).

Remark match_states_skip:
  forall f e le te nbrk ncnt k tf tk m,
  transl_function ge f = OK tf ->
  match_env e te ->
  match_cont (Clight.fn_return f) nbrk ncnt k tk ->
  match_states (Clight.State f Clight.Sskip k e le m) (State tf Sskip tk te le m).
Proof.
  intros. econstructor; eauto. simpl; reflexivity. constructor.
Qed.

(** Commutation between label resolution and compilation *)

Section FIND_LABEL.
Variable lbl: label.
Variable tyret: type.

Lemma transl_find_label:
  forall s nbrk ncnt k ts tk
  (TR: transl_statement ge tyret nbrk ncnt s = OK ts)
  (MC: match_cont tyret nbrk ncnt k tk),
  match Clight.find_label lbl s k with
  | None => find_label lbl ts tk = None
  | Some (s', k') =>
      exists ts', exists tk', exists nbrk', exists ncnt',
      find_label lbl ts tk = Some (ts', tk')
      /\ transl_statement ge tyret nbrk' ncnt' s' = OK ts'
      /\ match_cont tyret nbrk' ncnt' k' tk'
  end

with transl_find_label_ls:
  forall ls nbrk ncnt k tls tk
  (TR: transl_lbl_stmt ge tyret nbrk ncnt ls = OK tls)
  (MC: match_cont tyret nbrk ncnt k tk),
  match Clight.find_label_ls lbl ls k with
  | None => find_label_ls lbl tls tk = None
  | Some (s', k') =>
      exists ts', exists tk', exists nbrk', exists ncnt',
      find_label_ls lbl tls tk = Some (ts', tk')
      /\ transl_statement ge tyret nbrk' ncnt' s' = OK ts'
      /\ match_cont tyret nbrk' ncnt' k' tk'
  end.

Proof.
  intro s; case s; intros; try (monadInv TR); simpl.
(* skip *)
  auto.
(* assign *)
  unfold make_store, make_memcpy in EQ3.
  destruct (access_mode (typeof e)); inv EQ3; auto.
(* set *)
  auto.
(* call *)
  simpl in TR. destruct (classify_fun (typeof e)); monadInv TR. auto.
(* builtin *)
  auto.
(* seq *)
  exploit (transl_find_label s0 nbrk ncnt (Clight.Kseq s1 k)); eauto. constructor; eauto.
  destruct (Clight.find_label lbl s0 (Clight.Kseq s1 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H. eapply transl_find_label; eauto.
(* ifthenelse *)
  exploit (transl_find_label s0); eauto.
  destruct (Clight.find_label lbl s0 k) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H. eapply transl_find_label; eauto.
(* loop *)
  exploit (transl_find_label s0 1%nat 0%nat (Kloop1 s0 s1 k)); eauto. econstructor; eauto.
  destruct (Clight.find_label lbl s0 (Kloop1 s0 s1 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H.
  eapply transl_find_label; eauto. econstructor; eauto.
(* break *)
  auto.
(* continue *)
  auto.
(* return *)
  simpl in TR. destruct o; monadInv TR. auto. auto.
(* switch *)
  assert (exists b, ts = Sblock (Sswitch b x x0)).
  { destruct (classify_switch (typeof e)); inv EQ2; econstructor; eauto. }
  destruct H as [b EQ3]; rewrite EQ3; simpl.
  eapply transl_find_label_ls with (k := Clight.Kswitch k); eauto. econstructor; eauto.
(* label *)
  destruct (ident_eq lbl l).
  exists x; exists tk; exists nbrk; exists ncnt; auto.
  eapply transl_find_label; eauto.
(* goto *)
  auto.

  intro ls; case ls; intros; monadInv TR; simpl.
(* nil *)
  auto.
(* cons *)
  exploit (transl_find_label s nbrk ncnt (Clight.Kseq (seq_of_labeled_statement l) k)); eauto.
  econstructor; eauto. apply transl_lbl_stmt_2; eauto.
  destruct (Clight.find_label lbl s (Clight.Kseq (seq_of_labeled_statement l) k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B C]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H.
  eapply transl_find_label_ls; eauto.
Qed.

End FIND_LABEL.

(** Properties of call continuations *)

Lemma match_cont_call_cont:
  forall tyret' nbrk' ncnt' tyret nbrk ncnt k tk,
  match_cont tyret nbrk ncnt k tk ->
  match_cont tyret' nbrk' ncnt' (Clight.call_cont k) (call_cont tk).
Proof.
  induction 1; simpl; auto.
  constructor.
  econstructor; eauto.
Qed.

Lemma match_cont_is_call_cont:
  forall tyret nbrk ncnt k tk tyret' nbrk' ncnt',
  match_cont tyret nbrk ncnt k tk ->
  Clight.is_call_cont k ->
  match_cont tyret' nbrk' ncnt' k tk /\ is_call_cont tk.
Proof.
  intros. inv H; simpl in H0; try contradiction; simpl.
  split; auto; constructor.
  split; auto; econstructor; eauto.
Qed.

(** The simulation proof *)

Lemma transl_step:
  forall S1 t S2, Clight.step2 ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
  exists T2, plus step tge T1 t T2 /\ match_states S2 T2.
Proof.
  induction 1; intros T1 MST; inv MST.

(* assign *)
  monadInv TR.
  assert (SAME: ts' = ts /\ tk' = tk).
    inversion MTR. auto.
    subst ts. unfold make_store, make_memcpy in EQ3. destruct (access_mode (typeof a1)); congruence.
  destruct SAME; subst ts' tk'.
  econstructor; split.
  apply plus_one. eapply make_store_correct; eauto.
  eapply transl_lvalue_correct; eauto. eapply make_cast_correct; eauto.
  eapply transl_expr_correct; eauto.
  eapply match_states_skip; eauto.

(* set *)
  monadInv TR. inv MTR. econstructor; split.
  apply plus_one. econstructor. eapply transl_expr_correct; eauto.
  eapply match_states_skip; eauto.

(* call *)
  revert TR. simpl. case_eq (classify_fun (typeof a)); try congruence.
  intros targs tres cc CF TR. monadInv TR. inv MTR.
  exploit functions_translated; eauto. intros [tfd [FIND TFD]].
  rewrite H in CF. simpl in CF. inv CF.
  econstructor; split.
  apply plus_one. econstructor; eauto.
  exploit transl_expr_correct; eauto.
  exploit transl_arglist_correct; eauto.
  erewrite typlist_of_arglist_eq by eauto.
  eapply transl_fundef_sig1; eauto.
  rewrite H3. auto.
  econstructor; eauto.
  econstructor; eauto.
  simpl. auto.

(* builtin *)
  monadInv TR. inv MTR.
  econstructor; split.
  apply plus_one. econstructor.
  eapply transl_arglist_correct; eauto.
  eapply external_call_symbols_preserved_gen with (ge1 := ge).
  exact symbols_preserved. exact public_preserved. exact block_is_volatile_preserved. eauto.
  eapply match_states_skip; eauto.

(* seq *)
  monadInv TR. inv MTR.
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto. constructor.
  econstructor; eauto.

(* skip seq *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. apply step_skip_seq.
  econstructor; eauto. constructor.

(* continue seq *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto. simpl. reflexivity. constructor.

(* break seq *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto. simpl. reflexivity. constructor.

(* ifthenelse *)
  monadInv TR. inv MTR.
  exploit make_boolean_correct; eauto.
  exploit transl_expr_correct; eauto.
  intros [v [A B]].
  econstructor; split.
  apply plus_one. apply step_ifthenelse with (v := v) (b := b); auto.
  destruct b; econstructor; eauto; constructor.

(* loop *)
  monadInv TR.
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto.
  eapply plus_left. constructor.
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. traceEq.
  econstructor; eauto. constructor. econstructor; eauto.

(* skip-or-continue loop *)
  assert ((ts' = Sskip \/ ts' = Sexit ncnt) /\ tk' = tk).
    destruct H; subst x; monadInv TR; inv MTR; auto.
  destruct H0. inv MK.
  econstructor; split.
  eapply plus_left.
  destruct H0; subst ts'. 2:constructor. constructor.
  apply star_one. constructor. traceEq.
  econstructor; eauto. constructor. econstructor; eauto.

(* break loop1 *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  eapply plus_left. constructor.
  eapply star_left. constructor.
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. traceEq.
  eapply match_states_skip; eauto.

(* skip loop2 *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto.
Local Opaque ge.
  simpl. rewrite H5; simpl. rewrite H7; simpl. eauto.
  constructor.

(* break loop2 *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  eapply plus_left. constructor.
  apply star_one. constructor.
  traceEq.
  eapply match_states_skip; eauto.

(* return none *)
  monadInv TR. inv MTR.
  econstructor; split.
  apply plus_one. constructor.
  eapply match_env_free_blocks; eauto.
  econstructor; eauto.
  eapply match_cont_call_cont. eauto.

(* return some *)
  monadInv TR. inv MTR.
  econstructor; split.
  apply plus_one. constructor.
  eapply make_cast_correct; eauto. eapply transl_expr_correct; eauto.
  eapply match_env_free_blocks; eauto.
  econstructor; eauto.
  eapply match_cont_call_cont. eauto.

(* skip call *)
  monadInv TR. inv MTR.
  exploit match_cont_is_call_cont; eauto. intros [A B].
  econstructor; split.
  apply plus_one. apply step_skip_call. auto.
  eapply match_env_free_blocks; eauto.
  constructor. eauto.

(* switch *)
  monadInv TR.
  assert (E: exists b, ts = Sblock (Sswitch b x x0) /\ Switch.switch_argument b v n).
  { unfold sem_switch_arg in H0.
    destruct (classify_switch (typeof a)); inv EQ2; econstructor; split; eauto;
    destruct v; inv H0; constructor. }
  destruct E as (b & A & B). subst ts.
  exploit transl_expr_correct; eauto. intro EV.
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto.
  apply plus_one. econstructor; eauto. traceEq.
  econstructor; eauto.
  apply transl_lbl_stmt_2. apply transl_lbl_stmt_1. eauto.
  constructor.
  econstructor. eauto.

(* skip or break switch *)
  assert ((ts' = Sskip \/ ts' = Sexit nbrk) /\ tk' = tk).
    destruct H; subst x; monadInv TR; inv MTR; auto.
  destruct H0. inv MK.
  econstructor; split.
  apply plus_one. destruct H0; subst ts'. 2:constructor. constructor.
  eapply match_states_skip; eauto.


(* continue switch *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto. simpl. reflexivity. constructor.

(* label *)
  monadInv TR. inv MTR.
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto. constructor.

(* goto *)
  monadInv TR. inv MTR.
  generalize TRF. unfold transl_function. intro TRF'. monadInv TRF'.
  exploit (transl_find_label lbl). eexact EQ. eapply match_cont_call_cont. eauto.
  rewrite H.
  intros [ts' [tk'' [nbrk' [ncnt' [A [B C]]]]]].
  econstructor; split.
  apply plus_one. constructor. simpl. eexact A.
  econstructor; eauto. constructor.

(* internal function *)
  inv H. monadInv TR. monadInv EQ.
  exploit match_cont_is_call_cont; eauto. intros [A B].
  exploit match_env_alloc_variables; eauto.
  apply match_env_empty.
  intros [te1 [C D]].
  econstructor; split.
  apply plus_one. eapply step_internal_function.
  simpl. rewrite list_map_compose. simpl. assumption.
  simpl. auto.
  simpl. auto.
  simpl. eauto.
  simpl. rewrite create_undef_temps_match. eapply bind_parameter_temps_match; eauto.
  simpl. econstructor; eauto.
  unfold transl_function. rewrite EQ0; simpl. auto.
  constructor.

(* external function *)
  simpl in TR.
  destruct (signature_eq (ef_sig ef) (signature_of_type targs tres cconv)); inv TR.
  exploit match_cont_is_call_cont; eauto. intros [A B].
  econstructor; split.
  apply plus_one. constructor. eauto.
  eapply external_call_symbols_preserved_gen with (ge1 := ge).
  exact symbols_preserved. exact public_preserved. exact block_is_volatile_preserved. eauto.
  econstructor; eauto.

(* returnstate *)
  inv MK.
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto. simpl; reflexivity. constructor.
Qed.

Lemma transl_initial_states:
  forall S, Clight.initial_state prog S ->
  exists R, initial_state tprog R /\ match_states S R.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  assert (C: Genv.find_symbol tge (AST.prog_main tprog) = Some b).
    rewrite symbols_preserved. replace (AST.prog_main tprog) with (prog_main prog).
    auto. symmetry. unfold transl_program in TRANSL.
    change (prog_main prog) with (AST.prog_main (program_of_program prog)).
    eapply transform_partial_program2_main; eauto.
  assert (funsig tf = signature_of_type Tnil type_int32s cc_default).
    eapply transl_fundef_sig2; eauto.
  econstructor; split.
  econstructor; eauto. eapply Genv.init_mem_transf_partial2; eauto.
  econstructor; eauto. constructor; auto. exact I.
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> Clight.final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H. inv MK. constructor.
Qed.

Theorem transl_program_correct:
  forward_simulation (Clight.semantics2 prog) (Csharpminor.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  eexact public_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  eexact transl_step.
Qed.

End CORRECTNESS.
