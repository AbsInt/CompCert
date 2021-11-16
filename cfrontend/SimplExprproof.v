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

(** Correctness proof for expression simplification. *)

Require Import FunInd.
Require Import Coqlib Maps Errors Integers.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Ctypes Cop Csyntax Csem Cstrategy Clight.
Require Import SimplExpr SimplExprspec.

(** ** Relational specification of the translation. *)

Definition match_prog (p: Csyntax.program) (tp: Clight.program) :=
    match_program_gen tr_fundef eq p p tp
 /\ prog_types tp = prog_types p.

Lemma transf_program_match:
  forall p tp, transl_program p = OK tp -> match_prog p tp.
Proof.
  unfold transl_program; intros. monadInv H. split; auto.
  unfold program_of_program; simpl. destruct x; simpl.
  eapply match_transform_partial_program2; eauto.
- intros. apply transl_fundef_spec; auto.
- intros. inv H. auto.
Qed.

(** ** Semantic preservation *)

Section PRESERVATION.

Variable prog: Csyntax.program.
Variable tprog: Clight.program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge := Csem.globalenv prog.
Let tge := Clight.globalenv tprog.

(** Invariance properties. *)

Lemma comp_env_preserved:
  Clight.genv_cenv tge = Csem.genv_cenv ge.
Proof.
  simpl. destruct TRANSL. generalize (prog_comp_env_eq tprog) (prog_comp_env_eq prog). 
  congruence.
Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match (proj1 TRANSL)).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match (proj1 TRANSL)).

Lemma function_ptr_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists cu tf,
  Genv.find_funct_ptr tge b = Some tf /\ tr_fundef cu f tf /\ linkorder cu prog.
Proof (Genv.find_funct_ptr_match (proj1 TRANSL)).

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists cu tf,
  Genv.find_funct tge v = Some tf /\ tr_fundef cu f tf /\ linkorder cu prog.
Proof (Genv.find_funct_match (proj1 TRANSL)).

Lemma type_of_fundef_preserved:
  forall cu f tf, tr_fundef cu f tf ->
  type_of_fundef tf = Csyntax.type_of_fundef f.
Proof.
  intros. inv H.
  inv H0; simpl. unfold type_of_function, Csyntax.type_of_function. congruence.
  auto.
Qed.

Lemma function_return_preserved:
  forall ce f tf, tr_function ce f tf ->
  fn_return tf = Csyntax.fn_return f.
Proof.
  intros. inv H; auto.
Qed.

(** Properties of smart constructors. *)

Section TRANSLATION.

Variable cunit: Csyntax.program.
Hypothesis LINKORDER: linkorder cunit prog.
Let ce := cunit.(prog_comp_env).

Lemma eval_Ederef':
  forall ge e le m a t l ofs,
  eval_expr ge e le m a (Vptr l ofs) ->
  eval_lvalue ge e le m (Ederef' a t) l ofs Full.
Proof.
  intros. unfold Ederef'; destruct a; auto using eval_Ederef.
  destruct (type_eq t (typeof a)); auto using eval_Ederef.
  inv H.
- auto. 
- inv H0.
Qed.

Lemma typeof_Ederef':
  forall a t, typeof (Ederef' a t) = t.
Proof.
  unfold Ederef'; intros; destruct a; auto. destruct (type_eq t (typeof a)); auto. 
Qed.

Lemma eval_Eaddrof':
  forall ge e le m a t l ofs,
  eval_lvalue ge e le m a l ofs Full ->
  eval_expr ge e le m (Eaddrof' a t) (Vptr l ofs).
Proof.
  intros. unfold Eaddrof'; destruct a; auto using eval_Eaddrof.
  destruct (type_eq t (typeof a)); auto using eval_Eaddrof.
  inv H; auto.
Qed.

Lemma typeof_Eaddrof':
  forall a t, typeof (Eaddrof' a t) = t.
Proof.
  unfold Eaddrof'; intros; destruct a; auto. destruct (type_eq t (typeof a)); auto. 
Qed.

Lemma eval_make_normalize:
  forall ge e le m a n sz sg sg1 attr width,
  0 < width -> width <= bitsize_intsize sz ->
  typeof a = Tint sz sg1 attr ->
  eval_expr ge e le m a (Vint n) ->
  eval_expr ge e le m (make_normalize sz sg width a) (Vint (bitfield_normalize sz sg width n)).
Proof.
  intros. unfold make_normalize, bitfield_normalize.
  assert (bitsize_intsize sz <= Int.zwordsize) by (destruct sz; compute; congruence).
  destruct (intsize_eq sz IBool || signedness_eq sg Unsigned).
- rewrite Int.zero_ext_and by lia. econstructor. eauto. econstructor. 
  rewrite H1; simpl. unfold sem_and, sem_binarith.
  assert (A: exists sg2, classify_binarith (Tint sz sg1 attr) type_int32s = bin_case_i sg2).
  { unfold classify_binarith. unfold type_int32s. destruct sz, sg1; econstructor; eauto. }
  destruct A as (sg2 & A); rewrite A.
  unfold binarith_type.
  assert (B: forall i sz0 sg0 attr0,
             sem_cast (Vint i) (Tint sz0 sg0 attr0) (Tint I32 sg2 noattr) m = Some (Vint i)).
  { intros. unfold sem_cast, classify_cast. destruct Archi.ptr64; reflexivity. }
  unfold type_int32s; rewrite ! B. auto.
- rewrite Int.sign_ext_shr_shl by lia.
  set (amount := Int.repr (Int.zwordsize - width)).
  assert (LT: Int.ltu amount Int.iwordsize = true).
  { unfold Int.ltu. rewrite Int.unsigned_repr_wordsize. apply zlt_true.
    unfold amount; rewrite Int.unsigned_repr. lia.
    assert (Int.zwordsize < Int.max_unsigned) by reflexivity. lia. }
  econstructor.
  econstructor. eauto. econstructor.
  rewrite H1. unfold sem_binary_operation, sem_shl, sem_shift. rewrite LT. destruct sz, sg1; reflexivity.
  econstructor.
  unfold sem_binary_operation, sem_shr, sem_shift. rewrite LT. reflexivity.
Qed.

(** Translation of simple expressions. *)

Lemma tr_simple_nil:
  (forall le dst r sl a tmps, tr_expr ce le dst r sl a tmps ->
   dst = For_val \/ dst = For_effects -> simple r = true -> sl = nil)
/\(forall le rl sl al tmps, tr_exprlist ce le rl sl al tmps ->
   simplelist rl = true -> sl = nil).
Proof.
  assert (A: forall dst a, dst = For_val \/ dst = For_effects -> final dst a = nil).
    intros. destruct H; subst dst; auto.
  apply tr_expr_exprlist; intros; simpl in *; try discriminate; auto.
- rewrite H0; auto. simpl; auto.
- rewrite H0; auto. simpl; auto.
- destruct H1; congruence.
- destruct (andb_prop _ _ H6). inv H1.
    rewrite H0; eauto. simpl; auto.
    unfold chunk_for_volatile_type in H9.
    destruct (type_is_volatile (Csyntax.typeof e1)); simpl in H8; congruence.
- rewrite H0; auto. simpl; auto.
- rewrite H0; auto. simpl; auto.
- destruct (andb_prop _ _ H7). rewrite H0; auto. rewrite H2; auto. simpl; auto.
- rewrite H0; auto. simpl; auto.
- destruct (andb_prop _ _ H6). rewrite H0; auto.
Qed.

Lemma tr_simple_expr_nil:
  forall le dst r sl a tmps, tr_expr ce le dst r sl a tmps ->
  dst = For_val \/ dst = For_effects -> simple r = true -> sl = nil.
Proof (proj1 tr_simple_nil).

Lemma tr_simple_exprlist_nil:
  forall le rl sl al tmps, tr_exprlist ce le rl sl al tmps ->
  simplelist rl = true -> sl = nil.
Proof (proj2 tr_simple_nil).

(** Translation of [deref_loc] and [assign_loc] operations. *)

Remark deref_loc_translated:
  forall ty m b ofs bf t v,
  Csem.deref_loc ge ty m b ofs bf t v ->
  match chunk_for_volatile_type ty bf with
  | None => t = E0 /\ Clight.deref_loc ty m b ofs bf v
  | Some chunk => bf = Full /\ volatile_load tge chunk m b ofs t v
  end.
Proof.
  intros. unfold chunk_for_volatile_type. inv H.
- (* By_value, not volatile *)
  rewrite H1. split; auto. eapply deref_loc_value; eauto.
- (* By_value, volatile *)
  rewrite H0, H1. split; auto. eapply volatile_load_preserved with (ge1 := ge); auto. apply senv_preserved.
- (* By reference *)
  rewrite H0. destruct (type_is_volatile ty); split; auto; eapply deref_loc_reference; eauto.
- (* By copy *)
  rewrite H0. destruct (type_is_volatile ty); split; auto; eapply deref_loc_copy; eauto.
- (* Bitfield *)
  destruct (type_is_volatile ty); [destruct (access_mode ty)|]; auto using deref_loc_bitfield.
Qed.

Remark assign_loc_translated:
  forall ty m b ofs bf v t m' v',
  Csem.assign_loc ge ty m b ofs bf v t m' v' ->
  match chunk_for_volatile_type ty bf with
  | None => t = E0 /\ Clight.assign_loc tge ty m b ofs bf v m'
  | Some chunk => bf = Full /\ volatile_store tge chunk m b ofs v t m'
  end.
Proof.
  intros. unfold chunk_for_volatile_type. inv H.
- (* By_value, not volatile *)
  rewrite H1. split; auto. eapply assign_loc_value; eauto.
- (* By_value, volatile *)
  rewrite H0, H1. split; auto. eapply volatile_store_preserved with (ge1 := ge); auto. apply senv_preserved.
- (* By copy *)
  rewrite H0. rewrite <- comp_env_preserved in *.
  destruct (type_is_volatile ty); split; auto; eapply assign_loc_copy; eauto.
- (* Bitfield *)
  destruct (type_is_volatile ty); [destruct (access_mode ty)|]; eauto using assign_loc_bitfield.
Qed.

(** Bitfield accesses *)

Lemma is_bitfield_access_sound: forall e le m a b ofs bf bf',
  eval_lvalue tge e le m a b ofs bf ->
  tr_is_bitfield_access ce a bf' ->
  bf' = bf.
Proof.
  assert (A: forall id co co',
             tge.(genv_cenv)!id = Some co -> ce!id = Some co' ->
             co' = co /\ complete_members ce (co_members co) = true).
  { intros. rewrite comp_env_preserved in H.
    assert (ge.(Csem.genv_cenv) ! id = Some co') by (apply LINKORDER; auto).
    replace co' with co in * by congruence.
    split; auto. apply co_consistent_complete.
    eapply build_composite_env_consistent. eapply prog_comp_env_eq. eauto.
  } 
  induction 1; simpl; auto.
- rewrite H0. intros (co' & delta' & E1 & E2). rewrite comp_env_preserved in H2.
  exploit A; eauto. intros (E3 & E4). subst co'.
  assert (field_offset ge i (co_members co) = field_offset ce i (co_members co)).
  { apply field_offset_stable. apply LINKORDER. auto. }
  congruence.
- rewrite H0. intros (co' & delta' & E1 & E2). rewrite comp_env_preserved in H2.
  exploit A; eauto. intros (E3 & E4). subst co'.
  assert (union_field_offset ge i (co_members co) = union_field_offset ce i (co_members co)).
  { apply union_field_offset_stable. apply LINKORDER. auto. }
  congruence.
Qed.

Lemma make_assign_value_sound:
  forall ty m b ofs bf v t m' v',
  Csem.assign_loc ge ty m b ofs bf v t m' v' ->
  forall tge e le m'' r,
  typeof r = ty ->
  eval_expr tge e le m'' r v ->
  eval_expr tge e le m'' (make_assign_value bf r) v'.
Proof.
  unfold make_assign_value; destruct 1; intros; auto.
  inv H. eapply eval_make_normalize; eauto; lia.
Qed.

Lemma typeof_make_assign_value: forall bf r,
  typeof (make_assign_value bf r) = typeof r.
Proof.
  intros. destruct bf; simpl; auto. unfold make_normalize.
  destruct (intsize_eq sz IBool || signedness_eq sg Unsigned); auto.
Qed.

(** Evaluation of simple expressions and of their translation *)

Lemma tr_simple:
 forall e m,
 (forall r v,
  eval_simple_rvalue ge e m r v ->
  forall le dst sl a tmps,
  tr_expr ce le dst r sl a tmps ->
  match dst with
  | For_val => sl = nil /\ Csyntax.typeof r = typeof a /\ eval_expr tge e le m a v
  | For_effects => sl = nil
  | For_set sd =>
      exists b, sl = do_set sd b
             /\ Csyntax.typeof r = typeof b
             /\ eval_expr tge e le m b v
  end)
/\
 (forall l b ofs bf,
  eval_simple_lvalue ge e m l b ofs bf ->
  forall le sl a tmps,
  tr_expr ce le For_val l sl a tmps ->
  sl = nil /\ Csyntax.typeof l = typeof a /\ eval_lvalue tge e le m a b ofs bf).
Proof.
Opaque makeif.
  intros e m.
  apply (eval_simple_rvalue_lvalue_ind ge e m); intros until tmps; intros TR; inv TR.
- (* value *)
  auto.
- auto.
- exists a0; auto.
- (* rvalof *)
  inv H7; try congruence.
  exploit H0; eauto. intros [A [B C]].
  subst sl1; simpl.
  assert (eval_expr tge e le m a v).
    eapply eval_Elvalue. eauto.
    rewrite <- B.
    exploit deref_loc_translated; eauto. unfold chunk_for_volatile_type; rewrite H2. tauto.
  destruct dst; auto.
  econstructor. split. simpl; eauto. auto.
- (* addrof *)
  exploit H0; eauto. intros [A [B C]].
  subst sl1; simpl.
  assert (eval_expr tge e le m (Eaddrof' a1 ty) (Vptr b ofs)) by (apply eval_Eaddrof'; auto).
  assert (typeof (Eaddrof' a1 ty) = ty) by (apply typeof_Eaddrof').
  destruct dst; auto. simpl; econstructor; eauto.  
- (* unop *)
  exploit H0; eauto. intros [A [B C]].
  subst sl1; simpl.
  assert (eval_expr tge e le m (Eunop op a1 ty) v). econstructor; eauto. congruence.
  destruct dst; auto. simpl; econstructor; eauto.
- (* binop *)
  exploit H0; eauto. intros [A [B C]].
  exploit H2; eauto. intros [D [E F]].
  subst sl1 sl2; simpl.
  assert (eval_expr tge e le m (Ebinop op a1 a2 ty) v). econstructor; eauto. rewrite comp_env_preserved; congruence.
  destruct dst; auto. simpl; econstructor; eauto.
- (* cast effects *)
  exploit H0; eauto.
- (* cast val *)
  exploit H0; eauto. intros [A [B C]].
  subst sl1; simpl.
  assert (eval_expr tge e le m (Ecast a1 ty) v). econstructor; eauto. congruence.
  destruct dst; auto. simpl; econstructor; eauto.
- (* sizeof *)
  rewrite <- comp_env_preserved.
  destruct dst.
  split; auto. split; auto. constructor.
  auto.
  exists (Esizeof ty1 ty). split. auto. split. auto. constructor.
- (* alignof *)
  rewrite <- comp_env_preserved.
  destruct dst.
  split; auto. split; auto. constructor.
  auto.
  exists (Ealignof ty1 ty). split. auto. split. auto. constructor.
- (* var local *)
  split; auto. split; auto. apply eval_Evar_local; auto.
- (* var global *)
  split; auto. split; auto. apply eval_Evar_global; auto.
    rewrite symbols_preserved; auto.
- (* deref *)
  exploit H0; eauto. intros [A [B C]]. subst sl1.
  split; auto. split. rewrite typeof_Ederef'; auto. apply eval_Ederef'; auto. 
- (* field struct *)
  rewrite <- comp_env_preserved in *.
  exploit H0; eauto. intros [A [B C]]. subst sl1.
  split; auto. split; auto. rewrite B in H1. eapply eval_Efield_struct; eauto.
- (* field union *)
  rewrite <- comp_env_preserved in *.
  exploit H0; eauto. intros [A [B C]]. subst sl1.
  split; auto. split; auto. rewrite B in H1. eapply eval_Efield_union; eauto.
Qed.

Lemma tr_simple_rvalue:
  forall e m r v,
  eval_simple_rvalue ge e m r v ->
  forall le dst sl a tmps,
  tr_expr ce le dst r sl a tmps ->
  match dst with
  | For_val => sl = nil /\ Csyntax.typeof r = typeof a /\ eval_expr tge e le m a v
  | For_effects => sl = nil
  | For_set sd =>
      exists b, sl = do_set sd b
             /\ Csyntax.typeof r = typeof b
             /\ eval_expr tge e le m b v
  end.
Proof.
  intros e m. exact (proj1 (tr_simple e m)).
Qed.

Lemma tr_simple_lvalue:
  forall e m l b ofs bf,
  eval_simple_lvalue ge e m l b ofs bf ->
  forall le sl a tmps,
  tr_expr ce le For_val l sl a tmps ->
  sl = nil /\ Csyntax.typeof l = typeof a /\ eval_lvalue tge e le m a b ofs bf.
Proof.
  intros e m. exact (proj2 (tr_simple e m)).
Qed.

Lemma tr_simple_exprlist:
  forall le rl sl al tmps,
  tr_exprlist ce le rl sl al tmps ->
  forall e m tyl vl,
  eval_simple_list ge e m rl tyl vl ->
  sl = nil /\ eval_exprlist tge e le m al tyl vl.
Proof.
  induction 1; intros.
  inv H. split. auto. constructor.
  inv H4.
  exploit tr_simple_rvalue; eauto. intros [A [B C]].
  exploit IHtr_exprlist; eauto. intros [D E].
  split. subst; auto. econstructor; eauto. congruence.
Qed.

(** Commutation between the translation of expressions and left contexts. *)

Lemma typeof_context:
  forall k1 k2 C, leftcontext k1 k2 C ->
  forall e1 e2, Csyntax.typeof e1 = Csyntax.typeof e2 ->
  Csyntax.typeof (C e1) = Csyntax.typeof (C e2).
Proof.
  induction 1; intros; auto.
Qed.

Scheme leftcontext_ind2 := Minimality for leftcontext Sort Prop
  with leftcontextlist_ind2 := Minimality for leftcontextlist Sort Prop.
Combined Scheme leftcontext_leftcontextlist_ind from leftcontext_ind2, leftcontextlist_ind2.

Lemma tr_expr_leftcontext_rec:
 (
  forall from to C, leftcontext from to C ->
  forall le e dst sl a tmps,
  tr_expr ce le dst (C e) sl a tmps ->
  exists dst', exists sl1, exists sl2, exists a', exists tmp',
  tr_expr ce le dst' e sl1 a' tmp'
  /\ sl = sl1 ++ sl2
  /\ incl tmp' tmps
  /\ (forall le' e' sl3,
        tr_expr ce le' dst' e' sl3 a' tmp' ->
        (forall id, ~In id tmp' -> le'!id = le!id) ->
        Csyntax.typeof e' = Csyntax.typeof e ->
        tr_expr ce le' dst (C e') (sl3 ++ sl2) a tmps)
 ) /\ (
  forall from C, leftcontextlist from C ->
  forall le e sl a tmps,
  tr_exprlist ce le (C e) sl a tmps ->
  exists dst', exists sl1, exists sl2, exists a', exists tmp',
  tr_expr ce le dst' e sl1 a' tmp'
  /\ sl = sl1 ++ sl2
  /\ incl tmp' tmps
  /\ (forall le' e' sl3,
        tr_expr ce le' dst' e' sl3 a' tmp' ->
        (forall id, ~In id tmp' -> le'!id = le!id) ->
        Csyntax.typeof e' = Csyntax.typeof e ->
        tr_exprlist ce le' (C e') (sl3 ++ sl2) a tmps)
).
Proof.

Ltac TR :=
  econstructor; econstructor; econstructor; econstructor; econstructor;
  split; [eauto | split; [idtac | split]].

Ltac NOTIN :=
  match goal with
  | [ H1: In ?x ?l, H2: list_disjoint ?l _ |- ~In ?x _ ] =>
        red; intro; elim (H2 x x); auto; fail
  | [ H1: In ?x ?l, H2: list_disjoint _ ?l |- ~In ?x _ ] =>
        red; intro; elim (H2 x x); auto; fail
  end.

Ltac UNCHANGED :=
  match goal with
  | [ H: (forall (id: ident), ~In id _ -> ?le' ! id = ?le ! id) |-
         (forall (id: ident), In id _ -> ?le' ! id = ?le ! id) ] =>
      intros; apply H; NOTIN
  end.

  (*generalize compat_dest_change; intro CDC.*)
  apply leftcontext_leftcontextlist_ind; intros.

- (* base *)
  TR. rewrite <- app_nil_end; auto. red; auto.
  intros. rewrite <- app_nil_end; auto.
- (* deref *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1; rewrite app_ass; eauto. auto.
  intros. rewrite <- app_ass. econstructor; eauto.
- (* field *)
  inv H1.
  exploit H0. eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1; rewrite app_ass; eauto. auto.
  intros. rewrite <- app_ass. econstructor; eauto.
- (* rvalof *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1; rewrite app_ass; eauto. red; eauto.
  intros. rewrite <- app_ass; econstructor; eauto.
  exploit typeof_context; eauto. congruence.
- (* addrof *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1; rewrite app_ass; eauto. auto.
  intros. rewrite <- app_ass. econstructor; eauto.
- (* unop *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1; rewrite app_ass; eauto. auto.
  intros. rewrite <- app_ass. econstructor; eauto.
- (* binop left *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor; eauto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
- (* binop right *)
  inv H2.
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. change (sl3 ++ sl2') with (nil ++ sl3 ++ sl2'). rewrite app_ass. econstructor; eauto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
- (* cast *)
  inv H1.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. eauto. auto. 
  intros. econstructor; eauto.
+ (* generic *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto. auto. 
  intros. rewrite <- app_ass. econstructor; eauto.
- (* seqand *)
  inv H1.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto.
+ (* for set *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
- (* seqor *)
  inv H1.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto.
+ (* for set *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
- (* condition *)
  inv H1.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto. auto. auto.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. eapply tr_condition_effects. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto. auto.
+ (* for set *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR.
  rewrite Q. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. eapply tr_condition_set. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto. auto. auto.
- (* assign left *)
  inv H1.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto. auto. auto.
  eapply typeof_context. eauto. auto. eauto.
  auto.
- (* assign right *)
  inv H2.
+ (* for effects *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. change (sl3 ++ sl2') with (nil ++ (sl3 ++ sl2')). rewrite app_ass.
  econstructor.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto. auto. auto. auto. auto.
+ (* for val *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. change (sl3 ++ sl2') with (nil ++ (sl3 ++ sl2')). rewrite app_ass.
  econstructor.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto. auto. auto. auto. auto. auto. auto. auto.
  eapply typeof_context; eauto. auto.
- (* assignop left *)
  inv H1.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  symmetry; eapply typeof_context; eauto. eauto.
  auto. auto. auto. auto. auto. auto. auto.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  eauto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  eapply typeof_context; eauto. auto.
- (* assignop right *)
  inv H2.
+ (* for effects *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. change (sl0 ++ sl2') with (nil ++ sl0 ++ sl2'). rewrite app_ass. econstructor.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto. auto. eauto. auto. auto. auto. auto. auto. auto. auto.
+ (* for val *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. change (sl0 ++ sl2') with (nil ++ sl0 ++ sl2'). rewrite app_ass. econstructor.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto. eauto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
- (* postincr *)
  inv H1.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto. red; auto.
  intros. rewrite <- app_ass. econstructor; eauto.
  symmetry; eapply typeof_context; eauto.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto. red; auto.
  intros. rewrite <- app_ass. econstructor; eauto.
  eapply typeof_context; eauto.
- (* call left *)
  inv H1.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto. red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_exprlist_invariant; eauto. UNCHANGED.
  auto. auto. auto.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto. red; auto.
  intros. rewrite <- app_ass. econstructor. auto. apply S; auto.
  eapply tr_exprlist_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
- (* call right *)
  inv H2.
+ (* for effects *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto.
  (*destruct dst'; constructor||contradiction.*)
  red; auto.
  intros. rewrite <- app_ass. change (sl3++sl2') with (nil ++ sl3 ++ sl2'). rewrite app_ass. econstructor.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto. auto. auto. auto.
+ (* for val *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto.
  (*destruct dst'; constructor||contradiction.*)
  red; auto.
  intros. rewrite <- app_ass. change (sl3++sl2') with (nil ++ sl3 ++ sl2'). rewrite app_ass. econstructor.
  auto. eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto.
  auto. auto. auto. auto.
- (* builtin *)
  inv H1.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto.
  red; auto.
  intros. rewrite <- app_ass. change (sl3++sl2') with (nil ++ sl3 ++ sl2'). rewrite app_ass. econstructor.
  apply S; auto. auto.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto.
  red; auto.
  intros. rewrite <- app_ass. change (sl3++sl2') with (nil ++ sl3 ++ sl2'). rewrite app_ass. econstructor.
  auto. apply S; auto. auto. auto.
- (* comma *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto. red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto.
- (* paren *)
  inv H1.
+ (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q. eauto. red; auto.
  intros. econstructor; eauto.
+ (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q. eauto. auto.
  intros. econstructor; eauto.
+ (* for set *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q. eauto. auto.
  intros. econstructor; eauto.
- (* cons left *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto.
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_exprlist_invariant; eauto.  UNCHANGED.
  auto. auto. auto.
- (* cons right *)
  inv H2.
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. eauto.
  red; auto.
  intros. change sl3 with (nil ++ sl3). rewrite app_ass. econstructor.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto.
  auto. auto. auto.
Qed.

Theorem tr_expr_leftcontext:
  forall C le r dst sl a tmps,
  leftcontext RV RV C ->
  tr_expr ce le dst (C r) sl a tmps ->
  exists dst', exists sl1, exists sl2, exists a', exists tmp',
  tr_expr ce le dst' r sl1 a' tmp'
  /\ sl = sl1 ++ sl2
  /\ incl tmp' tmps
  /\ (forall le' r' sl3,
        tr_expr ce le' dst' r' sl3 a' tmp' ->
        (forall id, ~In id tmp' -> le'!id = le!id) ->
        Csyntax.typeof r' = Csyntax.typeof r ->
        tr_expr ce le' dst (C r') (sl3 ++ sl2) a tmps).
Proof.
  intros. eapply (proj1 tr_expr_leftcontext_rec); eauto.
Qed.

Theorem tr_top_leftcontext:
  forall e le m dst rtop sl a tmps,
  tr_top ce tge e le m dst rtop sl a tmps ->
  forall r C,
  rtop = C r ->
  leftcontext RV RV C ->
  exists dst', exists sl1, exists sl2, exists a', exists tmp',
  tr_top ce tge e le m dst' r sl1 a' tmp'
  /\ sl = sl1 ++ sl2
  /\ incl tmp' tmps
  /\ (forall le' m' r' sl3,
        tr_expr ce le' dst' r' sl3 a' tmp' ->
        (forall id, ~In id tmp' -> le'!id = le!id) ->
        Csyntax.typeof r' = Csyntax.typeof r ->
        tr_top ce tge e le' m' dst (C r') (sl3 ++ sl2) a tmps).
Proof.
  induction 1; intros.
(* val for val *)
  inv H2; inv H1.
  exists For_val; econstructor; econstructor; econstructor; econstructor.
  split. apply tr_top_val_val; eauto.
  split. instantiate (1 := nil); auto.
  split. apply incl_refl.
  intros. rewrite <- app_nil_end. constructor; auto.
(* base *)
  subst r. exploit tr_expr_leftcontext; eauto.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  exists dst'; exists sl1; exists sl2; exists a'; exists tmp'.
  split. apply tr_top_base; auto.
  split. auto. split. auto.
  intros. apply tr_top_base. apply S; auto.
Qed.

(** Semantics of smart constructors *)

Remark sem_cast_deterministic:
  forall v ty ty' m1 v1 m2 v2,
  sem_cast v ty ty' m1 = Some v1 ->
  sem_cast v ty ty' m2 = Some v2 ->
  v1 = v2.
Proof.
  unfold sem_cast; intros. destruct (classify_cast ty ty'); try congruence.
- destruct v; try congruence.
  destruct Archi.ptr64; try discriminate.
  destruct (Mem.weak_valid_pointer m1 b (Ptrofs.unsigned i)); inv H.
  destruct (Mem.weak_valid_pointer m2 b (Ptrofs.unsigned i)); inv H0.
  auto.
- destruct v; try congruence. 
  destruct (negb Archi.ptr64); try discriminate.
  destruct (Mem.weak_valid_pointer m1 b (Ptrofs.unsigned i)); inv H.
  destruct (Mem.weak_valid_pointer m2 b (Ptrofs.unsigned i)); inv H0.
  auto.
Qed.

Lemma eval_simpl_expr_sound:
  forall e le m a v, eval_expr tge e le m a v ->
  match eval_simpl_expr a with Some v' => v' = v | None => True end.
Proof.
  induction 1; simpl; auto.
  destruct (eval_simpl_expr a); auto. subst.
  destruct (sem_cast v1 (typeof a) ty Mem.empty) as [v'|] eqn:C; auto.
  eapply sem_cast_deterministic; eauto.
  inv H; simpl; auto.
Qed.

Lemma static_bool_val_sound:
  forall v t m b, bool_val v t Mem.empty = Some b -> bool_val v t m = Some b.
Proof.
  intros until b; unfold bool_val.
  destruct (classify_bool t); destruct v; destruct Archi.ptr64 eqn:SF; auto;
  simpl; congruence.
Qed.

Lemma step_makeif:
  forall f a s1 s2 k e le m v1 b,
  eval_expr tge e le m a v1 ->
  bool_val v1 (typeof a) m = Some b ->
  star step1 tge (State f (makeif a s1 s2) k e le m)
             E0 (State f (if b then s1 else s2) k e le m).
Proof.
  intros. functional induction (makeif a s1 s2).
- exploit eval_simpl_expr_sound; eauto. rewrite e0. intro EQ; subst v.
  assert (bool_val v1 (typeof a) m = Some true) by (apply static_bool_val_sound; auto).
  replace b with true by congruence. constructor.
- exploit eval_simpl_expr_sound; eauto. rewrite e0. intro EQ; subst v.
  assert (bool_val v1 (typeof a) m = Some false) by (apply static_bool_val_sound; auto).
  replace b with false by congruence. constructor.
- apply star_one. eapply step_ifthenelse; eauto.
- apply star_one. eapply step_ifthenelse; eauto.
Qed.

Lemma step_make_set:
  forall id a ty m b ofs bf t v e le f k,
  Csem.deref_loc ge ty m b ofs bf t v ->
  eval_lvalue tge e le m a b ofs bf ->
  typeof a = ty ->
  step1 tge (State f (make_set bf id a) k e le m)
          t (State f Sskip k e (PTree.set id v le) m).
Proof.
  intros. exploit deref_loc_translated; eauto. rewrite <- H1.
  unfold make_set. destruct (chunk_for_volatile_type (typeof a) bf) as [chunk|].
(* volatile case *)
  intros [A B]. subst bf.
  change (PTree.set id v le) with (set_opttemp (Some id) v le). econstructor.
  econstructor. constructor. eauto.
  simpl. unfold sem_cast. simpl. eauto. constructor.
  simpl. econstructor; eauto.
(* nonvolatile case *)
  intros [A B]. subst t. constructor. eapply eval_Elvalue; eauto.
Qed.

Lemma step_make_assign:
  forall a1 a2 ty m b ofs bf t v m' v' v2 e le f k,
  Csem.assign_loc ge ty m b ofs bf v t m' v' ->
  eval_lvalue tge e le m a1 b ofs bf ->
  eval_expr tge e le m a2 v2 ->
  sem_cast v2 (typeof a2) ty m = Some v ->
  typeof a1 = ty ->
  step1 tge (State f (make_assign bf a1 a2) k e le m)
          t (State f Sskip k e le m').
Proof.
  intros. exploit assign_loc_translated; eauto. rewrite <- H3.
  unfold make_assign. destruct (chunk_for_volatile_type (typeof a1) bf) as [chunk|].
(* volatile case *)
  intros [A B]. subst bf. change le with (set_opttemp None Vundef le) at 2. econstructor.
  econstructor. constructor. eauto.
  simpl. unfold sem_cast. simpl. eauto.
  econstructor; eauto. rewrite H3; eauto. constructor.
  simpl. econstructor; eauto.
(* nonvolatile case *)
  intros [A B]. subst t. econstructor; eauto. congruence.
Qed.

Fixpoint Kseqlist (sl: list statement) (k: cont) :=
  match sl with
  | nil => k
  | s :: l => Kseq s (Kseqlist l k)
  end.

Remark Kseqlist_app:
  forall sl1 sl2 k,
  Kseqlist (sl1 ++ sl2) k = Kseqlist sl1 (Kseqlist sl2 k).
Proof.
  induction sl1; simpl; congruence.
Qed.

Lemma push_seq:
  forall f sl k e le m,
  star step1 tge (State f (makeseq sl) k e le m)
              E0 (State f Sskip (Kseqlist sl k) e le m).
Proof.
  intros. unfold makeseq. generalize Sskip. revert sl k.
  induction sl; simpl; intros.
  apply star_refl.
  eapply star_right. apply IHsl. constructor. traceEq.
Qed.

Lemma step_tr_rvalof:
  forall ty m b ofs bf t v e le a sl a' tmp f k,
  Csem.deref_loc ge ty m b ofs bf t v ->
  eval_lvalue tge e le m a b ofs bf ->
  tr_rvalof ce ty a sl a' tmp ->
  typeof a = ty ->
  exists le',
    star step1 tge (State f Sskip (Kseqlist sl k) e le m)
                 t (State f Sskip k e le' m)
  /\ eval_expr tge e le' m a' v
  /\ typeof a' = typeof a
  /\ forall x, ~In x tmp -> le'!x = le!x.
Proof.
  intros. inv H1.
  (* not volatile *)
  exploit deref_loc_translated; eauto. unfold chunk_for_volatile_type; rewrite H3.
  intros [A B]. subst t.
  exists le; split. apply star_refl.
  split. eapply eval_Elvalue; eauto.
  auto.
  (* volatile *)
  intros.
  exploit is_bitfield_access_sound; eauto. intros EQ; subst bf0. 
  exists (PTree.set t0 v le); split.
  simpl. eapply star_two. econstructor. eapply step_make_set; eauto. traceEq.
  split. constructor. apply PTree.gss.
  split. auto.
  intros. apply PTree.gso. congruence.
Qed.

End TRANSLATION.


(** Matching between continuations *)

Inductive match_cont : composite_env -> Csem.cont -> cont -> Prop :=
  | match_Kstop: forall ce,
      match_cont ce Csem.Kstop Kstop
  | match_Kseq: forall ce s k ts tk,
      tr_stmt ce s ts ->
      match_cont ce k tk ->
      match_cont ce (Csem.Kseq s k) (Kseq ts tk)
  | match_Kwhile2: forall ce r s k s' ts tk,
      tr_if ce r Sskip Sbreak s' ->
      tr_stmt ce s ts ->
      match_cont ce k tk ->
      match_cont ce (Csem.Kwhile2 r s k)
                    (Kloop1 (Ssequence s' ts) Sskip tk)
  | match_Kdowhile1: forall ce r s k s' ts tk,
      tr_if ce r Sskip Sbreak s' ->
      tr_stmt ce s ts ->
      match_cont ce k tk ->
      match_cont ce (Csem.Kdowhile1 r s k)
                    (Kloop1 ts s' tk)
  | match_Kfor3: forall ce r s3 s k ts3 s' ts tk,
      tr_if ce r Sskip Sbreak s' ->
      tr_stmt ce s3 ts3 ->
      tr_stmt ce s ts ->
      match_cont ce k tk ->
      match_cont ce (Csem.Kfor3 r s3 s k)
                    (Kloop1 (Ssequence s' ts) ts3 tk)
  | match_Kfor4: forall ce r s3 s k ts3 s' ts tk,
      tr_if ce r Sskip Sbreak s' ->
      tr_stmt ce s3 ts3 ->
      tr_stmt ce s ts ->
      match_cont ce k tk ->
      match_cont ce (Csem.Kfor4 r s3 s k)
                    (Kloop2 (Ssequence s' ts) ts3 tk)
  | match_Kswitch2: forall ce k tk,
      match_cont ce k tk ->
      match_cont ce (Csem.Kswitch2 k) (Kswitch tk)
  | match_Kcall: forall f e C ty k optid tf le sl tk a dest tmps cu ce,
      linkorder cu prog ->
      tr_function cu.(prog_comp_env) f tf ->
      leftcontext RV RV C ->
      (forall v m, tr_top cu.(prog_comp_env) tge e (set_opttemp optid v le) m dest (C (Csyntax.Eval v ty)) sl a tmps) ->
      match_cont_exp cu.(prog_comp_env) dest a k tk ->
      match_cont ce (Csem.Kcall f e C ty k)
                    (Kcall optid tf e le (Kseqlist sl tk))

with match_cont_exp : composite_env -> destination -> expr -> Csem.cont -> cont -> Prop :=
  | match_Kdo: forall ce k a tk,
      match_cont ce k tk ->
      match_cont_exp ce For_effects a (Csem.Kdo k) tk
  | match_Kifthenelse_empty: forall ce a k tk,
      match_cont ce k tk ->
      match_cont_exp ce For_val a (Csem.Kifthenelse Csyntax.Sskip Csyntax.Sskip k) (Kseq Sskip tk)
  | match_Kifthenelse_1: forall ce a s1 s2 k ts1 ts2 tk,
      tr_stmt ce s1 ts1 -> tr_stmt ce s2 ts2 ->
      match_cont ce k tk ->
      match_cont_exp ce For_val a (Csem.Kifthenelse s1 s2 k) (Kseq (Sifthenelse a ts1 ts2) tk)
  | match_Kwhile1: forall ce r s k s' a ts tk,
      tr_if ce r Sskip Sbreak s' ->
      tr_stmt ce s ts ->
      match_cont ce k tk ->
      match_cont_exp ce For_val a
         (Csem.Kwhile1 r s k)
         (Kseq (makeif a Sskip Sbreak)
           (Kseq ts (Kloop1 (Ssequence s' ts) Sskip tk)))
  | match_Kdowhile2: forall ce r s k s' a ts tk,
      tr_if ce r Sskip Sbreak s' ->
      tr_stmt ce s ts ->
      match_cont ce k tk ->
      match_cont_exp ce For_val a
        (Csem.Kdowhile2 r s k)
        (Kseq (makeif a Sskip Sbreak) (Kloop2 ts s' tk))
  | match_Kfor2: forall ce r s3 s k s' a ts3 ts tk,
      tr_if ce r Sskip Sbreak s' ->
      tr_stmt ce s3 ts3 ->
      tr_stmt ce s ts ->
      match_cont ce k tk ->
      match_cont_exp ce For_val a
        (Csem.Kfor2 r s3 s k)
        (Kseq (makeif a Sskip Sbreak)
          (Kseq ts (Kloop1 (Ssequence s' ts) ts3 tk)))
  | match_Kswitch1: forall ce ls k a tls tk,
      tr_lblstmts ce ls tls ->
      match_cont ce k tk ->
      match_cont_exp ce For_val a (Csem.Kswitch1 ls k) (Kseq (Sswitch a tls) tk)
  | match_Kreturn: forall ce k a tk,
      match_cont ce k tk ->
      match_cont_exp ce For_val a (Csem.Kreturn k) (Kseq (Sreturn (Some a)) tk).

Lemma match_cont_is_call_cont:
  forall ce k tk,
  match_cont ce k tk -> Csem.is_call_cont k ->
  forall ce', match_cont ce' k tk.
Proof.
  destruct 1; simpl; intros; try contradiction; econstructor; eauto.
Qed. 

Lemma match_cont_call_cont:
  forall ce k tk,
  match_cont ce k tk ->
  forall ce', match_cont ce' (Csem.call_cont k) (call_cont tk).
Proof.
  induction 1; simpl; auto; intros; econstructor; eauto.
Qed.

(** Matching between states *)

Inductive match_states: Csem.state -> state -> Prop :=
  | match_exprstates: forall f r k e m tf sl tk le dest a tmps cu
      (LINK: linkorder cu prog)
      (TRF: tr_function cu.(prog_comp_env) f tf)
      (TR: tr_top cu.(prog_comp_env) tge e le m dest r sl a tmps)
      (MK: match_cont_exp cu.(prog_comp_env) dest a k tk),
      match_states (Csem.ExprState f r k e m)
                   (State tf Sskip (Kseqlist sl tk) e le m)
  | match_regularstates: forall f s k e m tf ts tk le cu
      (LINK: linkorder cu prog)
      (TRF: tr_function cu.(prog_comp_env) f tf)
      (TR: tr_stmt cu.(prog_comp_env) s ts)
      (MK: match_cont cu.(prog_comp_env) k tk),
      match_states (Csem.State f s k e m)
                   (State tf ts tk e le m)
  | match_callstates: forall fd args k m tfd tk cu
      (LINK: linkorder cu prog)
      (TR: tr_fundef cu fd tfd)
      (MK: forall ce, match_cont ce k tk),
      match_states (Csem.Callstate fd args k m)
                   (Callstate tfd args tk m)
  | match_returnstates: forall res k m tk
      (MK: forall ce, match_cont ce k tk),
      match_states (Csem.Returnstate res k m)
                   (Returnstate res tk m)
  | match_stuckstate: forall S,
      match_states Csem.Stuckstate S.

(** Additional results on translation of statements *)

Lemma tr_select_switch:
  forall ce n ls tls,
  tr_lblstmts ce ls tls ->
  tr_lblstmts ce (Csem.select_switch n ls) (select_switch n tls).
Proof.
  intros ce.
  assert (DFL: forall ls tls,
      tr_lblstmts ce ls tls ->
      tr_lblstmts ce (Csem.select_switch_default ls) (select_switch_default tls)).
  { induction 1; simpl. constructor. destruct c; auto. constructor; auto. }
  assert (CASE: forall n ls tls,
      tr_lblstmts ce ls tls ->
      match Csem.select_switch_case n ls with
      | None =>
          select_switch_case n tls = None
      | Some ls' =>
          exists tls', select_switch_case n tls = Some tls' /\ tr_lblstmts ce ls' tls'
      end).
  { induction 1; simpl; intros.
    auto.
    destruct c; auto. destruct (zeq z n); auto.
    econstructor; split; eauto. constructor; auto. }
  intros. unfold Csem.select_switch, select_switch.
  specialize (CASE n ls tls H).
  destruct (Csem.select_switch_case n ls) as [ls'|].
  destruct CASE as [tls' [P Q]]. rewrite P. auto.
  rewrite CASE. apply DFL; auto.
Qed.

Lemma tr_seq_of_labeled_statement:
  forall ce ls tls,
  tr_lblstmts ce ls tls ->
  tr_stmt ce (Csem.seq_of_labeled_statement ls) (seq_of_labeled_statement tls).
Proof.
  induction 1; simpl; constructor; auto.
Qed.

(** Commutation between translation and the "find label" operation. *)

Section FIND_LABEL.

Variable ce: composite_env.
Variable lbl: label.

Definition nolabel (s: statement) : Prop :=
  forall k, find_label lbl s k = None.

Fixpoint nolabel_list (sl: list statement) : Prop :=
  match sl with
  | nil => True
  | s1 :: sl' => nolabel s1 /\ nolabel_list sl'
  end.

Lemma nolabel_list_app:
  forall sl2 sl1, nolabel_list sl1 -> nolabel_list sl2 -> nolabel_list (sl1 ++ sl2).
Proof.
  induction sl1; simpl; intros. auto. tauto.
Qed.

Lemma makeseq_nolabel:
  forall sl, nolabel_list sl -> nolabel (makeseq sl).
Proof.
  assert (forall sl s, nolabel s -> nolabel_list sl -> nolabel (makeseq_rec s sl)).
  induction sl; simpl; intros. auto. destruct H0. apply IHsl; auto.
  red. intros; simpl. rewrite H. apply H0.
  intros. unfold makeseq. apply H; auto. red. auto.
Qed.

Lemma makeif_nolabel:
  forall a s1 s2, nolabel s1 -> nolabel s2 -> nolabel (makeif a s1 s2).
Proof.
  intros. functional induction (makeif a s1 s2); auto.
  red; simpl; intros. rewrite H; auto.
  red; simpl; intros. rewrite H; auto.
Qed.

Lemma make_set_nolabel:
  forall bf t a, nolabel (make_set bf t a).
Proof.
  unfold make_set; intros; red; intros.
  destruct (chunk_for_volatile_type (typeof a) bf); auto.
Qed.

Lemma make_assign_nolabel:
  forall bf l r, nolabel (make_assign bf l r).
Proof.
  unfold make_assign; intros; red; intros.
  destruct (chunk_for_volatile_type (typeof l) bf); auto.
Qed.

Lemma tr_rvalof_nolabel:
  forall ce ty a sl a' tmp, tr_rvalof ce ty a sl a' tmp -> nolabel_list sl.
Proof.
  destruct 1; simpl; intuition. apply make_set_nolabel.
Qed.

Lemma nolabel_do_set:
  forall sd a, nolabel_list (do_set sd a).
Proof.
  induction sd; intros; simpl; split; auto; red; auto.
Qed.

Lemma nolabel_final:
  forall dst a, nolabel_list (final dst a).
Proof.
  destruct dst; simpl; intros. auto. auto. apply nolabel_do_set.
Qed.

Ltac NoLabelTac :=
  match goal with
  | [ |- nolabel_list nil ] => exact I
  | [ |- nolabel_list (final _ _) ] => apply nolabel_final (*; NoLabelTac*)
  | [ |- nolabel_list (_ :: _) ] => simpl; split; NoLabelTac
  | [ |- nolabel_list (_ ++ _) ] => apply nolabel_list_app; NoLabelTac
  | [ H: _ -> nolabel_list ?x |- nolabel_list ?x ] => apply H; NoLabelTac
  | [ |- nolabel (makeseq _) ] => apply makeseq_nolabel; NoLabelTac
  | [ |- nolabel (makeif _ _ _) ] => apply makeif_nolabel; NoLabelTac
  | [ |- nolabel (make_set _ _ _) ] => apply make_set_nolabel
  | [ |- nolabel (make_assign _ _ _) ] => apply make_assign_nolabel
  | [ |- nolabel _ ] => red; intros; simpl; auto
  | [ |- _ /\ _ ] => split; NoLabelTac
  | _ => auto
  end.

Lemma tr_find_label_expr:
  (forall le dst r sl a tmps, tr_expr ce le dst r sl a tmps -> nolabel_list sl)
/\(forall le rl sl al tmps, tr_exprlist ce le rl sl al tmps -> nolabel_list sl).
Proof.
  apply tr_expr_exprlist; intros; NoLabelTac.
  apply nolabel_do_set.
  eapply tr_rvalof_nolabel; eauto.
  apply nolabel_do_set.
  apply nolabel_do_set.
  eapply tr_rvalof_nolabel; eauto.
  eapply tr_rvalof_nolabel; eauto.
  eapply tr_rvalof_nolabel; eauto.
Qed.

Lemma tr_find_label_top:
  forall e le m dst r sl a tmps,
  tr_top ce tge e le m dst r sl a tmps -> nolabel_list sl.
Proof.
  induction 1; intros; NoLabelTac.
  eapply (proj1 tr_find_label_expr); eauto.
Qed.

Lemma tr_find_label_expression:
  forall r s a, tr_expression ce r s a -> forall k, find_label lbl s k = None.
Proof.
  intros. inv H.
  assert (nolabel (makeseq sl)). apply makeseq_nolabel.
  eapply tr_find_label_top with (e := empty_env) (le := PTree.empty val) (m := Mem.empty).
  eauto. apply H.
Qed.

Lemma tr_find_label_expr_stmt:
  forall r s, tr_expr_stmt ce r s -> forall k, find_label lbl s k = None.
Proof.
  intros. inv H.
  assert (nolabel (makeseq sl)). apply makeseq_nolabel.
  eapply tr_find_label_top with (e := empty_env) (le := PTree.empty val) (m := Mem.empty).
  eauto. apply H.
Qed.

Lemma tr_find_label_if:
  forall r s,
  tr_if ce r Sskip Sbreak s ->
  forall k, find_label lbl s k = None.
Proof.
  intros. inv H.
  assert (nolabel (makeseq (sl ++ makeif a Sskip Sbreak :: nil))).
  apply makeseq_nolabel.
  apply nolabel_list_app.
  eapply tr_find_label_top with (e := empty_env) (le := PTree.empty val) (m := Mem.empty).
  eauto.
  simpl; split; auto. apply makeif_nolabel. red; simpl; auto. red; simpl; auto.
  apply H.
Qed.

Lemma tr_find_label:
  forall s k ts tk
    (TR: tr_stmt ce s ts)
    (MC: match_cont ce k tk),
  match Csem.find_label lbl s k with
  | None =>
      find_label lbl ts tk = None
  | Some (s', k') =>
      exists ts', exists tk',
          find_label lbl ts tk = Some (ts', tk')
       /\ tr_stmt ce s' ts'
       /\ match_cont ce k' tk'
  end
with tr_find_label_ls:
  forall s k ts tk
    (TR: tr_lblstmts ce s ts)
    (MC: match_cont ce k tk),
  match Csem.find_label_ls lbl s k with
  | None =>
      find_label_ls lbl ts tk = None
  | Some (s', k') =>
      exists ts', exists tk',
          find_label_ls lbl ts tk = Some (ts', tk')
       /\ tr_stmt ce s' ts'
       /\ match_cont ce k' tk'
  end.
Proof.
  induction s; intros; inversion TR; subst; clear TR; simpl.
  auto.
  eapply tr_find_label_expr_stmt; eauto.
(* seq *)
  exploit (IHs1 (Csem.Kseq s2 k)); eauto. constructor; eauto.
  destruct (Csem.find_label lbl s1 (Csem.Kseq s2 k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; auto.
  intro EQ. rewrite EQ. eapply IHs2; eauto.
(* if empty *)
  rename s' into sr.
  rewrite (tr_find_label_expression _ _ _ H3).
  auto.
(* if not empty *)
  rename s' into sr.
  rewrite (tr_find_label_expression _ _ _ H2).
  exploit (IHs1 k); eauto.
  destruct (Csem.find_label lbl s1 k) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ. rewrite EQ. eapply IHs2; eauto.
(* while *)
  rename s' into sr.
  rewrite (tr_find_label_if _ _ H1); auto.
  exploit (IHs (Kwhile2 e s k)); eauto. econstructor; eauto.
  destruct (Csem.find_label lbl s (Kwhile2 e s k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ. rewrite EQ. auto.
(* dowhile *)
  rename s' into sr.
  rewrite (tr_find_label_if _ _ H1); auto.
  exploit (IHs (Kdowhile1 e s k)); eauto. econstructor; eauto.
  destruct (Csem.find_label lbl s (Kdowhile1 e s k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ. rewrite EQ. auto.
(* for skip *)
  rename s' into sr.
  rewrite (tr_find_label_if _ _ H4); auto.
  exploit (IHs3 (Csem.Kfor3 e s2 s3 k)); eauto. econstructor; eauto.
  destruct (Csem.find_label lbl s3 (Csem.Kfor3 e s2 s3 k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ. rewrite EQ.
  exploit (IHs2 (Csem.Kfor4 e s2 s3 k)); eauto. econstructor; eauto.
(* for not skip *)
  rename s' into sr.
  rewrite (tr_find_label_if _ _ H3); auto.
  exploit (IHs1 (Csem.Kseq (Csyntax.Sfor Csyntax.Sskip e s2 s3) k)); eauto.
    econstructor; eauto. econstructor; eauto.
  destruct (Csem.find_label lbl s1
               (Csem.Kseq (Csyntax.Sfor Csyntax.Sskip e s2 s3) k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ; rewrite EQ.
  exploit (IHs3 (Csem.Kfor3 e s2 s3 k)); eauto. econstructor; eauto.
  destruct (Csem.find_label lbl s3 (Csem.Kfor3 e s2 s3 k)) as [[s'' k''] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; intuition.
  intro EQ'. rewrite EQ'.
  exploit (IHs2 (Csem.Kfor4 e s2 s3 k)); eauto. econstructor; eauto.
(* break, continue, return 0 *)
  auto. auto. auto.
(* return 1 *)
  rewrite (tr_find_label_expression _ _ _ H0). auto.
(* switch *)
  rewrite (tr_find_label_expression _ _ _ H1). apply tr_find_label_ls. auto. constructor; auto.
(* labeled stmt *)
  destruct (ident_eq lbl l). exists ts0; exists tk; auto. apply IHs; auto.
(* goto *)
  auto.

  induction s; intros; inversion TR; subst; clear TR; simpl.
(* nil *)
  auto.
(* case *)
  exploit (tr_find_label s (Csem.Kseq (Csem.seq_of_labeled_statement s0) k)); eauto.
  econstructor; eauto. apply tr_seq_of_labeled_statement; eauto.
  destruct (Csem.find_label lbl s
    (Csem.Kseq (Csem.seq_of_labeled_statement s0) k)) as [[s' k'] | ].
  intros [ts' [tk' [A [B C]]]]. rewrite A. exists ts'; exists tk'; auto.
  intro EQ. rewrite EQ. eapply IHs; eauto.
Qed.

End FIND_LABEL.

(** Anti-stuttering measure *)

(** There are some stuttering steps in the translation:
- The execution of [Sdo a] where [a] is side-effect free,
  which is three transitions in the source:
<<
    Sdo a, k  --->  a, Kdo k ---> rval v, Kdo k ---> Sskip, k
>>
  but the translation, which is [Sskip], makes no transitions.
- The reduction [Ecomma (Eval v) r2 --> r2].
- The reduction [Eparen (Eval v) --> Eval v] in a [For_effects] context.

The following measure decreases for these stuttering steps. *)

Fixpoint esize (a: Csyntax.expr) : nat :=
  match a with
  | Csyntax.Eloc _ _ _ _ => 1%nat
  | Csyntax.Evar _ _ => 1%nat
  | Csyntax.Ederef r1 _ => S(esize r1)
  | Csyntax.Efield l1 _ _ => S(esize l1)
  | Csyntax.Eval _ _ => O
  | Csyntax.Evalof l1 _ => S(esize l1)
  | Csyntax.Eaddrof l1 _ => S(esize l1)
  | Csyntax.Eunop _ r1 _ => S(esize r1)
  | Csyntax.Ebinop _ r1 r2 _ => S(esize r1 + esize r2)%nat
  | Csyntax.Ecast r1 _ => S(esize r1)
  | Csyntax.Eseqand r1 _ _ => S(esize r1)
  | Csyntax.Eseqor r1 _ _ => S(esize r1)
  | Csyntax.Econdition r1 _ _ _ => S(esize r1)
  | Csyntax.Esizeof _ _ => 1%nat
  | Csyntax.Ealignof _ _ => 1%nat
  | Csyntax.Eassign l1 r2 _ => S(esize l1 + esize r2)%nat
  | Csyntax.Eassignop _ l1 r2 _ _ => S(esize l1 + esize r2)%nat
  | Csyntax.Epostincr _ l1 _ => S(esize l1)
  | Csyntax.Ecomma r1 r2 _ => S(esize r1 + esize r2)%nat
  | Csyntax.Ecall r1 rl2 _ => S(esize r1 + esizelist rl2)%nat
  | Csyntax.Ebuiltin ef _ rl _ => S(esizelist rl)%nat
  | Csyntax.Eparen r1 _ _ => S(esize r1)
  end

with esizelist (el: Csyntax.exprlist) : nat :=
  match el with
  | Csyntax.Enil => O
  | Csyntax.Econs r1 rl2 => (esize r1 + esizelist rl2)%nat
  end.

Definition measure (st: Csem.state) : nat :=
  match st with
  | Csem.ExprState _ r _ _ _ => (esize r + 1)%nat
  | Csem.State _ Csyntax.Sskip _ _ _ => 0%nat
  | Csem.State _ (Csyntax.Sdo r) _ _ _ => (esize r + 2)%nat
  | Csem.State _ (Csyntax.Sifthenelse r _ _) _ _ _ => (esize r + 2)%nat
  | _ => 0%nat
  end.

Lemma leftcontext_size:
  forall from to C,
  leftcontext from to C ->
  forall e1 e2,
  (esize e1 < esize e2)%nat ->
  (esize (C e1) < esize (C e2))%nat
with leftcontextlist_size:
  forall from C,
  leftcontextlist from C ->
  forall e1 e2,
  (esize e1 < esize e2)%nat ->
  (esizelist (C e1) < esizelist (C e2))%nat.
Proof.
  induction 1; intros; simpl; auto with arith.
  exploit leftcontextlist_size; eauto. auto with arith.
  exploit leftcontextlist_size; eauto. auto with arith.
  induction 1; intros; simpl; auto with arith. exploit leftcontext_size; eauto. auto with arith.
Qed.

(** Forward simulation for expressions. *)

Lemma tr_val_gen:
  forall ce le dst v ty a tmp,
  typeof a = ty ->
  (forall tge e le' m,
      (forall id, In id tmp -> le'!id = le!id) ->
      eval_expr tge e le' m a v) ->
  tr_expr ce le dst (Csyntax.Eval v ty) (final dst a) a tmp.
Proof.
  intros. destruct dst; simpl; econstructor; auto.
Qed.

Lemma estep_simulation:
  forall S1 t S2, Cstrategy.estep ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  exists S2',
     (plus step1 tge S1' t S2' \/
       (star step1 tge S1' t S2' /\ measure S2 < measure S1)%nat)
  /\ match_states S2 S2'.
Proof.

Ltac NOTIN :=
  match goal with
  | [ H1: In ?x ?l, H2: list_disjoint ?l _ |- ~In ?x _ ] =>
        red; intro; elim (H2 x x); auto; fail
  | [ H1: In ?x ?l, H2: list_disjoint _ ?l |- ~In ?x _ ] =>
        red; intro; elim (H2 x x); auto; fail
  end.

  induction 1; intros; inv MS.
- (* expr *)
  assert (tr_expr (prog_comp_env cu) le dest r sl a tmps).
  { inv TR. contradiction. auto. }
  exploit tr_simple_rvalue; eauto. destruct dest.
+ (* for val *)
  intros [SL1 [TY1 EV1]]. subst sl.
  econstructor; split.
  right; split. apply star_refl. destruct r; simpl; (contradiction || lia).
  econstructor; eauto.
  instantiate (1 := tmps). apply tr_top_val_val; auto.
+ (* for effects *)
  intros SL1. subst sl.
  econstructor; split.
  right; split. apply star_refl. destruct r; simpl; (contradiction || lia).
  econstructor; eauto.
  instantiate (1 := tmps). apply tr_top_base. constructor.
+ (* for set *)
  inv MK.
- (* rval volatile *)
  exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H2. inv H7; try congruence.
  exploit tr_simple_lvalue; eauto. intros [SL [TY EV]]. subst sl0; simpl.
  exploit is_bitfield_access_sound; eauto. intros EQ; subst bf0.
  econstructor; split.
  left. eapply plus_two. constructor. eapply step_make_set; eauto. traceEq.
  econstructor; eauto.
  change (final dst' (Etempvar t0 (Csyntax.typeof l)) ++ sl2) with (nil ++ (final dst' (Etempvar t0 (Csyntax.typeof l)) ++ sl2)).
  apply S. apply tr_val_gen. auto.
  intros. constructor. rewrite H7; auto. apply PTree.gss.
  intros. apply PTree.gso. red; intros; subst; elim H7; auto.
  auto.
- (* seqand true *)
  exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H2.
+ (* for val *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. apply tr_paren_val with (a1 := a2); auto.
  apply tr_expr_monotone with tmp2; eauto. auto. auto.
+ (* for effects *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. apply tr_paren_effects with (a1 := a2); auto.
  apply tr_expr_monotone with tmp2; eauto. auto. auto.
+  (* for set *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. apply tr_paren_set with (a1 := a2) (t := sd_temp sd); auto.
  apply tr_expr_monotone with tmp2; eauto. auto. auto.
- (* seqand false *)
  exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H2.
+ (* for val *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
  apply star_one. constructor. constructor. reflexivity. reflexivity.
  eapply match_exprstates; eauto.
  change sl2 with (nil ++ sl2). apply S. econstructor; eauto.
  intros. constructor. rewrite H2. apply PTree.gss. auto.
  intros. apply PTree.gso. congruence.
  auto.
+ (* for effects *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  apply step_makeif with (b := false) (v1 := v); auto. congruence.
  reflexivity.
  eapply match_exprstates; eauto.
  change sl2 with (nil ++ sl2). apply S. econstructor; eauto.
  auto. auto.
+ (* for set *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. econstructor; eauto. intros. constructor. auto. auto.
- (* seqor true *)
  exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H2.
+ (* for val *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
  apply star_one. constructor. constructor. reflexivity. reflexivity.
  eapply match_exprstates; eauto.
  change sl2 with (nil ++ sl2). apply S. econstructor; eauto.
  intros. constructor. rewrite H2. apply PTree.gss. auto.
  intros. apply PTree.gso. congruence.
  auto.
+ (* for effects *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  apply step_makeif with (b := true) (v1 := v); auto. congruence.
  reflexivity.
  eapply match_exprstates; eauto.
  change sl2 with (nil ++ sl2). apply S. econstructor; eauto.
  auto. auto.
+ (* for set *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. econstructor; eauto. intros. constructor. auto. auto.
- (* seqand false *)
  exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H2.
+ (* for val *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. apply tr_paren_val with (a1 := a2); auto.
  apply tr_expr_monotone with tmp2; eauto. auto. auto.
+ (* for effects *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. apply tr_paren_effects with (a1 := a2); auto.
  apply tr_expr_monotone with tmp2; eauto. auto. auto.
+ (* for set *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. apply tr_paren_set with (a1 := a2) (t := sd_temp sd); auto.
  apply tr_expr_monotone with tmp2; eauto. auto. auto.
- (* condition *)
  exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H2.
+ (* for value *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist. destruct b.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. econstructor; eauto. apply tr_expr_monotone with tmp2; eauto. auto. auto.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. econstructor; eauto. apply tr_expr_monotone with tmp3; eauto. auto. auto.
+ (* for effects *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist. destruct b.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
  apply push_seq.
  reflexivity. traceEq.
  rewrite <- Kseqlist_app.
  econstructor; eauto. apply S.
    econstructor; eauto. apply tr_expr_monotone with tmp2; eauto.
    econstructor; eauto.
  auto. auto.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
  apply push_seq.
  reflexivity. traceEq.
  rewrite <- Kseqlist_app.
  econstructor; eauto. apply S.
    econstructor; eauto. apply tr_expr_monotone with tmp3; eauto.
    econstructor; eauto.
  auto.
+ (* for set *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist. destruct b.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
  apply push_seq.
  reflexivity. traceEq.
  rewrite <- Kseqlist_app.
  econstructor; eauto. apply S.
    econstructor; eauto. apply tr_expr_monotone with tmp2; eauto.
    econstructor; eauto.
  auto.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
  apply push_seq.
  reflexivity. traceEq.
  rewrite <- Kseqlist_app.
  econstructor; eauto. apply S.
    econstructor; eauto. apply tr_expr_monotone with tmp3; eauto.
    econstructor; eauto.
  auto.
- (* assign *)
  exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H4.
+ (* for effects *)
  exploit tr_simple_rvalue; eauto. intros [SL2 [TY2 EV2]].
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  assert (bf0 = bf) by (eapply is_bitfield_access_sound; eauto).
  subst; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  apply star_one. eapply step_make_assign; eauto.
  rewrite <- TY2; eauto. traceEq.
  econstructor; eauto. change sl2 with (nil ++ sl2). apply S.
  constructor. auto. auto.
+ (* for value *)
  exploit tr_simple_rvalue; eauto. intros [SL2 [TY2 EV2]].
  exploit tr_simple_lvalue. eauto.
    eapply tr_expr_invariant with (le' := PTree.set t0 v1 le). eauto.
    intros. apply PTree.gso. intuition congruence.
  intros [SL1 [TY1 EV1]].
  assert (bf0 = bf) by (eapply is_bitfield_access_sound; eauto).
  subst; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_left. constructor. econstructor. eauto. rewrite <- TY2; eauto. 
  eapply star_left. constructor.
  apply star_one. eapply step_make_assign; eauto.
  constructor. apply PTree.gss. simpl. eapply cast_idempotent; eauto. 
  reflexivity. reflexivity. traceEq.
  econstructor; eauto. apply S.
  apply tr_val_gen. rewrite typeof_make_assign_value; auto.
  intros. eapply make_assign_value_sound; eauto. 
  constructor. rewrite H4; auto. apply PTree.gss.
  intros. apply PTree.gso. intuition congruence.
  auto.
- (* assignop *)
  exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H6.
+ (* for effects *)
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit step_tr_rvalof; eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
  exploit tr_simple_lvalue. eauto. eapply tr_expr_invariant with (le := le) (le' := le'). eauto.
  intros. apply INV. NOTIN. intros [? [? EV1']].
  exploit tr_simple_rvalue. eauto. eapply tr_expr_invariant with (le := le) (le' := le'). eauto.
  intros. apply INV. NOTIN. simpl. intros [SL2 [TY2 EV2]].
  assert (bf0 = bf) by (eapply is_bitfield_access_sound; eauto).
  subst; simpl Kseqlist.
  econstructor; split.
  left. eapply star_plus_trans. rewrite app_ass. rewrite Kseqlist_app. eexact EXEC.
  eapply plus_two. simpl. econstructor. eapply step_make_assign; eauto.
    econstructor. eexact EV3. eexact EV2.
    rewrite TY3; rewrite <- TY1; rewrite <- TY2; rewrite comp_env_preserved; auto.
  reflexivity. traceEq.
  econstructor; eauto. change sl2 with (nil ++ sl2). apply S.
  constructor. auto. auto.
+ (* for value *)
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit step_tr_rvalof; eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
  exploit tr_simple_lvalue. eauto. eapply tr_expr_invariant with (le := le) (le' := le'). eauto.
  intros. apply INV. NOTIN. intros [? [? EV1']].
  exploit tr_simple_rvalue. eauto. eapply tr_expr_invariant with (le := le) (le' := le'). eauto.
  intros. apply INV. NOTIN. simpl. intros [SL2 [TY2 EV2]].
  exploit tr_simple_lvalue. eauto.
    eapply tr_expr_invariant with (le := le) (le' := PTree.set t v4 le'). eauto.
    intros. rewrite PTree.gso. apply INV. NOTIN. intuition congruence.
  intros [? [? EV1'']].
  assert (bf0 = bf) by (eapply is_bitfield_access_sound; eauto).
  subst; simpl Kseqlist.
  econstructor; split.
  left. rewrite app_ass. rewrite Kseqlist_app.
  eapply star_plus_trans. eexact EXEC.
  simpl. eapply plus_four. econstructor. econstructor.
    econstructor. econstructor. eexact EV3. eexact EV2.
    rewrite TY3; rewrite <- TY1; rewrite <- TY2; rewrite comp_env_preserved; eauto.
    eassumption.
  econstructor. eapply step_make_assign; eauto.
    constructor. apply PTree.gss. simpl. eapply cast_idempotent; eauto.
    reflexivity. traceEq.
  econstructor; eauto. apply S.
  apply tr_val_gen. rewrite typeof_make_assign_value; auto.
  intros. eapply make_assign_value_sound; eauto.
  constructor. rewrite H10; auto. apply PTree.gss.
  intros. rewrite PTree.gso. apply INV.
  red; intros; elim H10; auto.
  intuition congruence.
  auto.
- (* assignop stuck *)
  exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H4.
+ (* for effects *)
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit tr_simple_rvalue; eauto. intros [SL2 [TY2 EV2]].
  exploit step_tr_rvalof; eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
  subst; simpl Kseqlist.
  econstructor; split.
  right; split. rewrite app_ass. rewrite Kseqlist_app. eexact EXEC.
  simpl. lia.
  constructor.
+ (* for value *)
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit tr_simple_rvalue; eauto. intros [SL2 [TY2 EV2]].
  exploit step_tr_rvalof; eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
  subst; simpl Kseqlist.
  econstructor; split.
  right; split. rewrite app_ass. rewrite Kseqlist_app. eexact EXEC.
  simpl. lia.
  constructor.
- (* postincr *)
  exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H5.
+ (* for effects *)
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit step_tr_rvalof; eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
  exploit tr_simple_lvalue. eauto. eapply tr_expr_invariant with (le := le) (le' := le'). eauto.
  intros. apply INV. NOTIN. intros [? [? EV1']].
  assert (bf0 = bf) by (eapply is_bitfield_access_sound; eauto).
  subst; simpl Kseqlist.
  econstructor; split.
  left. rewrite app_ass; rewrite Kseqlist_app.
  eapply star_plus_trans. eexact EXEC.
  eapply plus_two. simpl. constructor.
  eapply step_make_assign; eauto.
  unfold transl_incrdecr. destruct id; simpl in H2.
  econstructor. eauto. constructor. rewrite TY3; rewrite <- TY1; rewrite comp_env_preserved. simpl; eauto.
  econstructor. eauto. constructor. rewrite TY3; rewrite <- TY1; rewrite comp_env_preserved. simpl; eauto.
  destruct id; auto.
  reflexivity. traceEq.
  econstructor; eauto. change sl2 with (nil ++ sl2). apply S.
  constructor. auto. auto.
+ (* for value *)
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit tr_simple_lvalue. eauto.
    eapply tr_expr_invariant with (le' := PTree.set t v1 le). eauto.
    intros. apply PTree.gso. intuition congruence.
  intros [SL2 [TY2 EV2]].
  assert (bf0 = bf) by (eapply is_bitfield_access_sound; eauto).
  subst; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_four. constructor.
  eapply step_make_set; eauto.
  constructor.
  eapply step_make_assign; eauto.
  unfold transl_incrdecr. destruct id; simpl in H2.
  econstructor. constructor. apply PTree.gss. constructor.
  rewrite comp_env_preserved; simpl; eauto.
  econstructor. constructor. apply PTree.gss. constructor.
  rewrite comp_env_preserved; simpl; eauto.
  destruct id; auto.
  traceEq.
  econstructor; eauto. apply S.
  apply tr_val_gen. auto. intros. econstructor; eauto.
  rewrite H5; auto. apply PTree.gss.
  intros. apply PTree.gso. intuition congruence.
  auto.
- (* postincr stuck *)
  exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H3.
+ (* for effects *)
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit step_tr_rvalof; eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
  subst. simpl Kseqlist.
  econstructor; split.
  right; split. rewrite app_ass; rewrite Kseqlist_app. eexact EXEC.
  simpl; lia.
  constructor.
+ (* for value *)
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  assert (bf0 = bf) by (eapply is_bitfield_access_sound; eauto).
  subst. simpl Kseqlist.
  econstructor; split.
  left. eapply plus_two. constructor. eapply step_make_set; eauto.
  traceEq.
  constructor.
- (* comma *)
  exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H1.
  exploit tr_simple_rvalue; eauto. simpl; intro SL1.
  subst sl0; simpl Kseqlist.
  econstructor; split.
  right; split. apply star_refl. simpl. apply plus_lt_compat_r.
  apply (leftcontext_size _ _ _ H). simpl. lia.
  econstructor; eauto. apply S.
  eapply tr_expr_monotone; eauto.
  auto. auto.
- (* paren *)
  exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H2.
+ (* for value *)
  exploit tr_simple_rvalue; eauto. intros [b [SL1 [TY1 EV1]]].
  subst sl1; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor. apply star_one.
  econstructor. econstructor; eauto. rewrite <- TY1; eauto. traceEq.
  econstructor; eauto.
  change sl2 with (final For_val (Etempvar t (Csyntax.typeof r)) ++ sl2). apply S.
  constructor. auto. intros. constructor. rewrite H2; auto. apply PTree.gss.
  intros. apply PTree.gso. intuition congruence.
  auto.
+ (* for effects *)
  econstructor; split.
  right; split. apply star_refl. simpl. apply plus_lt_compat_r.
  apply (leftcontext_size _ _ _ H). simpl. lia.
  econstructor; eauto.
  exploit tr_simple_rvalue; eauto. simpl. intros A. subst sl1.
  apply S. constructor; auto. auto. auto.
+ (* for set *)
  exploit tr_simple_rvalue; eauto. simpl. intros [b [SL1 [TY1 EV1]]]. subst sl1.
  simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor. apply star_one. econstructor. econstructor; eauto.
  rewrite <- TY1; eauto. traceEq.
  econstructor; eauto.
  apply S. constructor; auto.
  intros. constructor. rewrite H2. apply PTree.gss. auto.
  intros. apply PTree.gso. congruence.
  auto.

- (* call *)
  exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H5.
+ (* for effects *)
  exploit tr_simple_rvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit tr_simple_exprlist; eauto. intros [SL2 EV2].
  subst. simpl Kseqlist.
  exploit functions_translated; eauto. intros (cu' & tfd & J & K & L).
  econstructor; split.
  left. eapply plus_left. constructor.  apply star_one.
  econstructor; eauto. rewrite <- TY1; eauto.
  exploit type_of_fundef_preserved; eauto. congruence.
  traceEq.
  econstructor. eexact L. eauto. econstructor. eexact LINK. auto. auto.
  intros. change sl2 with (nil ++ sl2). apply S.
  constructor. auto. auto. auto.
+ (* for value *)
  exploit tr_simple_rvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit tr_simple_exprlist; eauto. intros [SL2 EV2].
  subst. simpl Kseqlist.
  exploit functions_translated; eauto. intros (cu' & tfd & J & K & L).
  econstructor; split.
  left. eapply plus_left. constructor.  apply star_one.
  econstructor; eauto. rewrite <- TY1; eauto.
  exploit type_of_fundef_preserved; eauto. congruence.
  traceEq.
  econstructor. eexact L. eauto. econstructor. eexact LINK. auto. auto.
  intros. apply S.
  destruct dst'; constructor.
  auto. intros. constructor. rewrite H5; auto. apply PTree.gss.
  auto. intros. constructor. rewrite H5; auto. apply PTree.gss.
  intros. apply PTree.gso. intuition congruence.
  auto. auto.

- (* builtin *)
  exploit tr_top_leftcontext; eauto. clear TR.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H2.
+ (* for effects *)
  exploit tr_simple_exprlist; eauto. intros [SL EV].
  subst. simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.  apply star_one.
  econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  traceEq.
  econstructor; eauto.
  change sl2 with (nil ++ sl2). apply S. constructor. simpl; auto. auto.
+ (* for value *)
  exploit tr_simple_exprlist; eauto. intros [SL EV].
  subst. simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor. apply star_one.
  econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  traceEq.
  econstructor; eauto.
  change sl2 with (nil ++ sl2). apply S.
  apply tr_val_gen. auto. intros. constructor. rewrite H2; auto. simpl. apply PTree.gss.
  intros; simpl. apply PTree.gso. intuition congruence.
  auto.
Qed.

(** Forward simulation for statements. *)

Lemma tr_top_val_for_val_inv:
  forall ce e le m v ty sl a tmps,
  tr_top ce tge e le m For_val (Csyntax.Eval v ty) sl a tmps ->
  sl = nil /\ typeof a = ty /\ eval_expr tge e le m a v.
Proof.
  intros. inv H. auto. inv H0. auto.
Qed.

Lemma alloc_variables_preserved:
  forall e m params e' m',
  Csem.alloc_variables ge e m params e' m' ->
  alloc_variables tge e m params e' m'.
Proof.
  induction 1; econstructor; eauto. rewrite comp_env_preserved; auto.
Qed.

Lemma bind_parameters_preserved:
  forall e m params args m',
  Csem.bind_parameters ge e m params args m' ->
  bind_parameters tge e m params args m'.
Proof.
  induction 1; econstructor; eauto. inv H0.
- eapply assign_loc_value; eauto.
- inv H4. eapply assign_loc_value; eauto.
- rewrite <- comp_env_preserved in *. eapply assign_loc_copy; eauto.
Qed.

Lemma blocks_of_env_preserved:
  forall e, blocks_of_env tge e = Csem.blocks_of_env ge e.
Proof.
  intros; unfold blocks_of_env, Csem.blocks_of_env.
  unfold block_of_binding, Csem.block_of_binding.
  rewrite comp_env_preserved. auto.
Qed.

Lemma sstep_simulation:
  forall S1 t S2, Csem.sstep ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  exists S2',
     (plus step1 tge S1' t S2' \/
       (star step1 tge S1' t S2' /\ measure S2 < measure S1)%nat)
  /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
- (* do 1 *)
  inv TR. inv H0.
  econstructor; split.
  right; split. apply push_seq.
  simpl. lia.
  econstructor; eauto. constructor. auto.
- (* do 2 *)
  inv MK. inv TR. inv H.
  econstructor; split.
  right; split. apply star_refl. simpl. lia.
  econstructor; eauto. constructor.

- (* seq *)
  inv TR. econstructor; split. left. apply plus_one. constructor.
  econstructor; eauto. constructor; auto.
- (* skip seq *)
  inv TR; inv MK. econstructor; split.
  left. apply plus_one; constructor.
  econstructor; eauto.
- (* continue seq *)
  inv TR; inv MK. econstructor; split.
  left. apply plus_one; constructor.
  econstructor; eauto. constructor.
- (* break seq *)
  inv TR; inv MK. econstructor; split.
  left. apply plus_one; constructor.
  econstructor; eauto. constructor.
- (* ifthenelse *)
  inv TR.
+ (* ifthenelse empty *)
  inv H3. econstructor; split.
  left. eapply plus_left. constructor. apply push_seq.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
+ (* ifthenelse non empty *)
  inv H2. econstructor; split.
  left. eapply plus_left. constructor. apply push_seq. traceEq.
  econstructor; eauto. econstructor; eauto.
- (* ifthenelse *)
  inv MK.
+ (* ifthenelse empty *)
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  econstructor; split; simpl.
  right. destruct b; econstructor; eauto.
  eapply star_left. apply step_skip_seq. econstructor. traceEq.
  eapply star_left. apply step_skip_seq. econstructor. traceEq.
  destruct b; econstructor; eauto. econstructor; eauto. econstructor; eauto.
+ (* ifthenelse non empty *)
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  econstructor; split.
  left. eapply plus_two. constructor.
  apply step_ifthenelse with (v1 := v) (b := b); auto. traceEq.
  destruct b; econstructor; eauto.
- (* while *)
  inv TR. inv H1. econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_left. constructor.
  apply push_seq.
  reflexivity. traceEq. rewrite Kseqlist_app.
  econstructor; eauto. simpl. econstructor; eauto. econstructor; eauto.
- (* while false *)
  inv MK.
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (v1 := v) (b := false); auto.
  eapply star_two. constructor. apply step_break_loop1.
  reflexivity. reflexivity. traceEq.
  econstructor; eauto. constructor.
- (* while true *)
  inv MK.
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_right. apply step_makeif with (v1 := v) (b := true); auto.
  constructor.
  reflexivity. traceEq.
  econstructor; eauto. constructor; auto.
- (* skip-or-continue while *)
  assert (ts = Sskip \/ ts = Scontinue). { destruct H; subst s0; inv TR; auto. }
  inv MK.
  econstructor; split.
  left. eapply plus_two. apply step_skip_or_continue_loop1; auto.
  apply step_skip_loop2. traceEq.
  econstructor; eauto. constructor; auto.
- (* break while *)
  inv TR. inv MK.
  econstructor; split.
  left. apply plus_one. apply step_break_loop1.
  econstructor; eauto. constructor.

- (* dowhile *)
  inv TR.
  econstructor; split.
  left. apply plus_one. apply step_loop.
  econstructor; eauto. constructor; auto.
- (* skip_or_continue dowhile *)
  assert (ts = Sskip \/ ts = Scontinue). { destruct H; subst s0; inv TR; auto. }
  inv MK. inv H5.
  econstructor; split.
  left. eapply plus_left. apply step_skip_or_continue_loop1. auto.
  apply push_seq.
  traceEq.
  rewrite Kseqlist_app.
  econstructor; eauto. simpl. econstructor; auto. econstructor; eauto.
- (* dowhile false *)
  inv MK.
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_right. apply step_makeif with (v1 := v) (b := false); auto.
  constructor.
  reflexivity. traceEq.
  econstructor; eauto. constructor.
- (* dowhile true *)
  inv MK.
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_right. apply step_makeif with (v1 := v) (b := true); auto.
  constructor.
  reflexivity. traceEq.
  econstructor; eauto. constructor; auto.
- (* break dowhile *)
  inv TR. inv MK.
  econstructor; split.
  left. apply plus_one. apply step_break_loop1.
  econstructor; eauto. constructor.

- (* for start *)
  inv TR. congruence.
  econstructor; split.
  left; apply plus_one. constructor.
  econstructor; eauto. constructor; auto. econstructor; eauto.
- (* for *)
  inv TR; try congruence. inv H2.
  econstructor; split.
  left. eapply plus_left. apply step_loop.
  eapply star_left. constructor. apply push_seq.
  reflexivity. traceEq.
  rewrite Kseqlist_app. econstructor; eauto. simpl. constructor; auto. econstructor; eauto.
- (* for false *)
  inv MK. exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (v1 := v) (b := false); auto.
  eapply star_two. constructor. apply step_break_loop1.
  reflexivity. reflexivity. traceEq.
  econstructor; eauto. constructor.
- (* for true *)
  inv MK. exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_right. apply step_makeif with (v1 := v) (b := true); auto.
  constructor.
  reflexivity. traceEq.
  econstructor; eauto. constructor; auto.
- (* skip_or_continue for3 *)
  assert (ts = Sskip \/ ts = Scontinue). { destruct H; subst x; inv TR; auto. }
  inv MK.
  econstructor; split.
  left. apply plus_one. apply step_skip_or_continue_loop1. auto.
  econstructor; eauto. econstructor; auto.
- (* break for3 *)
  inv TR. inv MK.
  econstructor; split.
  left. apply plus_one. apply step_break_loop1.
  econstructor; eauto. constructor.
- (* skip for4 *)
  inv TR. inv MK.
  econstructor; split.
  left. apply plus_one. constructor.
  econstructor; eauto. constructor; auto.

- (* return none *)
  inv TR. econstructor; split.
  left. apply plus_one. econstructor; eauto. rewrite blocks_of_env_preserved; eauto.
  econstructor. intros; eapply match_cont_call_cont; eauto.
- (* return some 1 *)
  inv TR. inv H0. econstructor; split.
  left; eapply plus_left. constructor. apply push_seq. traceEq.
  econstructor; eauto. constructor. auto.
- (* return some 2 *)
  inv MK. exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  econstructor; split.
  left. eapply plus_two. constructor. econstructor. eauto.
  erewrite function_return_preserved; eauto. rewrite blocks_of_env_preserved; eauto.
  eauto. traceEq.
  econstructor. intros; eapply match_cont_call_cont; eauto.
- (* skip return *)
  inv TR.
  assert (is_call_cont tk). { inv MK; simpl in *; auto. }
  econstructor; split.
  left. apply plus_one. apply step_skip_call; eauto. rewrite blocks_of_env_preserved; eauto.
  econstructor. intros; eapply match_cont_is_call_cont; eauto.

- (* switch *)
  inv TR. inv H1.
  econstructor; split.
  left; eapply plus_left. constructor. apply push_seq. traceEq.
  econstructor; eauto. constructor; auto.
- (* expr switch *)
  inv MK. exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  econstructor; split.
  left; eapply plus_two. constructor. econstructor; eauto. traceEq.
  econstructor; eauto.
  apply tr_seq_of_labeled_statement. apply tr_select_switch. auto.
  constructor; auto.

- (* skip-or-break switch *)
  assert (ts = Sskip \/ ts = Sbreak). { destruct H; subst x; inv TR; auto. }
  inv MK.
  econstructor; split.
  left; apply plus_one. apply step_skip_break_switch. auto.
  econstructor; eauto. constructor.

- (* continue switch *)
  inv TR. inv MK.
  econstructor; split.
  left; apply plus_one. apply step_continue_switch.
  econstructor; eauto. constructor.

- (* label *)
  inv TR. econstructor; split.
  left; apply plus_one. constructor.
  econstructor; eauto.

- (* goto *)
  inv TR.
  inversion TRF; subst.
  exploit tr_find_label. eauto. eapply match_cont_call_cont; eauto.
  instantiate (1 := lbl). rewrite H.
  intros [ts' [tk' [P [Q R]]]].
  econstructor; split.
  left. apply plus_one. econstructor; eauto.
  econstructor; eauto.

- (* internal function *)
  inv TR. inversion H3; subst.
  econstructor; split.
  left; apply plus_one. eapply step_internal_function. econstructor.
  rewrite H6; rewrite H7; auto.
  rewrite H6; rewrite H7. eapply alloc_variables_preserved; eauto.
  rewrite H6. eapply bind_parameters_preserved; eauto.
  eauto.
  econstructor; eauto. 

- (* external function *)
  inv TR.
  econstructor; split.
  left; apply plus_one. econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.

- (* return *)
  specialize (MK (PTree.empty _)). inv MK.
  econstructor; split.
  left; apply plus_one. constructor.
  econstructor; eauto.
Qed.

(** Semantic preservation *)

Theorem simulation:
  forall S1 t S2, Cstrategy.step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  exists S2',
     (plus step1 tge S1' t S2' \/
       (star step1 tge S1' t S2' /\ measure S2 < measure S1)%nat)
  /\ match_states S2 S2'.
Proof.
  intros S1 t S2 STEP. destruct STEP.
  apply estep_simulation; auto.
  apply sstep_simulation; auto.
Qed.

Lemma transl_initial_states:
  forall S,
  Csem.initial_state prog S ->
  exists S', Clight.initial_state tprog S' /\ match_states S S'.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros (cu & tf & FIND & TR & L).
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_match (proj1 TRANSL)); eauto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto. 
  destruct TRANSL. destruct H as (A & B & C). simpl in B. auto. 
  eexact FIND.
  rewrite <- H3. eapply type_of_fundef_preserved; eauto.
  econstructor; eauto. intros; constructor.
Qed.

Lemma transl_final_states:
  forall S S' r,
  match_states S S' -> Csem.final_state S r -> Clight.final_state S' r.
Proof.
  intros. inv H0. inv H. specialize (MK (PTree.empty _)). inv MK. constructor.
Qed.

Theorem transl_program_correct:
  forward_simulation (Cstrategy.semantics prog) (Clight.semantics1 tprog).
Proof.
  eapply forward_simulation_star_wf with (order := ltof _ measure).
  eapply senv_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  apply well_founded_ltof.
  exact simulation.
Qed.

End PRESERVATION.

(** ** Commutation with linking *)

Global Instance TransfSimplExprLink : TransfLink match_prog.
Proof.
  red; intros. eapply Ctypes.link_match_program_gen; eauto. 
- intros.
Local Transparent Linker_fundef.
  simpl in *; unfold link_fundef in *. inv H3; inv H4; try discriminate.
  destruct ef; inv H2. exists (Internal tf); split; auto. left; constructor; auto.
  destruct ef; inv H2. exists (Internal tf); split; auto. right; constructor; auto.
  destruct (external_function_eq ef ef0 && typelist_eq targs targs0 &&
            type_eq tres tres0 && calling_convention_eq cconv cconv0); inv H2.
  exists (External ef targs tres cconv); split; auto. left; constructor.
Qed.
