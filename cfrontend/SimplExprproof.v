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

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Smallstep.
Require Import Globalenvs.
Require Import Ctypes.
Require Import Cop.
Require Import Csyntax.
Require Import Csem.
Require Import Cstrategy.
Require Import Clight.
Require Import SimplExpr.
Require Import SimplExprspec.

Section PRESERVATION.

Variable prog: Csyntax.program.
Variable tprog: Clight.program.
Hypothesis TRANSL: transl_program prog = OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

(** Invariance properties. *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof
  (Genv.find_symbol_transf_partial transl_fundef _ TRANSL).

Lemma function_ptr_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transl_fundef _ TRANSL).

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef f = OK tf.
Proof
  (Genv.find_funct_transf_partial transl_fundef _ TRANSL).

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof
  (Genv.find_var_info_transf_partial transl_fundef _ TRANSL).

Lemma block_is_volatile_preserved:
  forall b, block_is_volatile tge b = block_is_volatile ge b.
Proof.
  intros. unfold block_is_volatile. rewrite varinfo_preserved. auto.
Qed.

Lemma type_of_fundef_preserved:
  forall f tf, transl_fundef f = OK tf ->
  type_of_fundef tf = Csyntax.type_of_fundef f.
Proof.
  intros. destruct f; monadInv H.
  exploit transl_function_spec; eauto. intros [A [B [C D]]].
  simpl. unfold type_of_function, Csyntax.type_of_function. congruence.
  auto.
Qed.

Lemma function_return_preserved:
  forall f tf, transl_function f = OK tf ->
  fn_return tf = Csyntax.fn_return f.
Proof.
  intros. unfold transl_function in H.
  destruct (transl_stmt (Csyntax.fn_body f) (initial_generator tt)); inv H.
  auto.
Qed.

Lemma type_of_global_preserved:
  forall b ty,
  Csem.type_of_global ge b = Some ty ->
  type_of_global tge b = Some ty.
Proof.
  intros until ty. unfold Csem.type_of_global, type_of_global.
  rewrite varinfo_preserved. destruct (Genv.find_var_info ge b). auto. 
  case_eq (Genv.find_funct_ptr ge b); intros. 
  inv H0. exploit function_ptr_translated; eauto. intros [tf [A B]]. 
  rewrite A. decEq. apply type_of_fundef_preserved; auto.
  congruence.
Qed.

(** Translation of simple expressions. *)

Lemma tr_simple_nil:
  (forall le dst r sl a tmps, tr_expr le dst r sl a tmps ->
   dst = For_val \/ dst = For_effects -> simple r = true -> sl = nil)
/\(forall le rl sl al tmps, tr_exprlist le rl sl al tmps ->
   simplelist rl = true -> sl = nil).
Proof.
  assert (A: forall dst a, dst = For_val \/ dst = For_effects -> final dst a = nil).
    intros. destruct H; subst dst; auto.
  apply tr_expr_exprlist; intros; simpl in *; try discriminate; auto.
  rewrite H0; auto. simpl; auto.
  rewrite H0; auto. simpl; auto.
  destruct H1; congruence.
  destruct (andb_prop _ _ H6). inv H1.
    rewrite H0; eauto. simpl; auto. 
    unfold chunk_for_volatile_type in H9.
    destruct (type_is_volatile (Csyntax.typeof e1)); simpl in H8; congruence.
  rewrite H0; auto. simpl; auto.
  rewrite H0; auto. simpl; auto.
  destruct (andb_prop _ _ H7). rewrite H0; auto. rewrite H2; auto. simpl; auto.
  rewrite H0; auto. simpl; auto.
  destruct (andb_prop _ _ H6). rewrite H0; auto.
Qed.

Lemma tr_simple_expr_nil:
  forall le dst r sl a tmps, tr_expr le dst r sl a tmps ->
  dst = For_val \/ dst = For_effects -> simple r = true -> sl = nil.
Proof (proj1 tr_simple_nil).

Lemma tr_simple_exprlist_nil:
  forall le rl sl al tmps, tr_exprlist le rl sl al tmps ->
  simplelist rl = true -> sl = nil.
Proof (proj2 tr_simple_nil).

(** Translation of [deref_loc] and [assign_loc] operations. *)

Remark deref_loc_translated:
  forall ty m b ofs t v,
  Csem.deref_loc ge ty m b ofs t v ->
  match chunk_for_volatile_type ty with
  | None => t = E0 /\ Clight.deref_loc ty m b ofs v
  | Some chunk => volatile_load tge chunk m b ofs t v
  end.
Proof.
  intros. unfold chunk_for_volatile_type. inv H. 
  (* By_value, not volatile *)
  rewrite H1. split; auto. eapply deref_loc_value; eauto.
  (* By_value, volatile *)
  rewrite H0; rewrite H1. eapply volatile_load_preserved with (ge1 := ge); auto.
  exact symbols_preserved. exact block_is_volatile_preserved.
  (* By reference *)
  rewrite H0. destruct (type_is_volatile ty); split; auto; eapply deref_loc_reference; eauto.
  (* By copy *)
  rewrite H0. destruct (type_is_volatile ty); split; auto; eapply deref_loc_copy; eauto.
Qed.

Remark assign_loc_translated:
  forall ty m b ofs v t m',
  Csem.assign_loc ge ty m b ofs v t m' ->
  match chunk_for_volatile_type ty with
  | None => t = E0 /\ Clight.assign_loc ty m b ofs v m'
  | Some chunk => volatile_store tge chunk m b ofs v t m'
  end.
Proof.
  intros. unfold chunk_for_volatile_type. inv H. 
  (* By_value, not volatile *)
  rewrite H1. split; auto. eapply assign_loc_value; eauto.
  (* By_value, volatile *)
  rewrite H0; rewrite H1. eapply volatile_store_preserved with (ge1 := ge); auto.
  exact symbols_preserved. exact block_is_volatile_preserved.
  (* By copy *)
  rewrite H0. destruct (type_is_volatile ty); split; auto; eapply assign_loc_copy; eauto.
Qed.

(** Evaluation of simple expressions and of their translation *)

Lemma tr_simple:
 forall e m,
 (forall r v,
  eval_simple_rvalue ge e m r v ->
  forall le dst sl a tmps,
  tr_expr le dst r sl a tmps ->
  match dst with
  | For_val => sl = nil /\ Csyntax.typeof r = typeof a /\ eval_expr tge e le m a v
  | For_effects => sl = nil
  | For_set tyl t =>
      exists b, sl = do_set t tyl b
             /\ Csyntax.typeof r = typeof b
             /\ eval_expr tge e le m b v
  end)
/\
 (forall l b ofs,
  eval_simple_lvalue ge e m l b ofs ->
  forall le sl a tmps,
  tr_expr le For_val l sl a tmps ->
  sl = nil /\ Csyntax.typeof l = typeof a /\ eval_lvalue tge e le m a b ofs).
Proof.
Opaque makeif.
  intros e m.
  apply (eval_simple_rvalue_lvalue_ind ge e m); intros until tmps; intros TR; inv TR.
(* value *)
  auto.
  auto.
  exists a0; auto.
(* rvalof *)
  inv H7; try congruence.
  exploit H0; eauto. intros [A [B C]].
  subst sl1; simpl.
  assert (eval_expr tge e le m a v).
    eapply eval_Elvalue. eauto.
    rewrite <- B.
    exploit deref_loc_translated; eauto. unfold chunk_for_volatile_type; rewrite H2. tauto.
  destruct dst; auto.
  econstructor. split. simpl; eauto. auto. 
(* addrof *)
  exploit H0; eauto. intros [A [B C]].
  subst sl1; simpl.
  assert (eval_expr tge e le m (Eaddrof a1 ty) (Vptr b ofs)). econstructor; eauto.
  destruct dst; auto. simpl; econstructor; eauto. 
(* unop *)
  exploit H0; eauto. intros [A [B C]].
  subst sl1; simpl.
  assert (eval_expr tge e le m (Eunop op a1 ty) v). econstructor; eauto. congruence.
  destruct dst; auto. simpl; econstructor; eauto.
(* binop *)
  exploit H0; eauto. intros [A [B C]].
  exploit H2; eauto. intros [D [E F]].
  subst sl1 sl2; simpl.
  assert (eval_expr tge e le m (Ebinop op a1 a2 ty) v). econstructor; eauto. congruence.
  destruct dst; auto. simpl; econstructor; eauto.
(* cast *)
  exploit H0; eauto. intros [A [B C]].
  subst sl1; simpl.
  assert (eval_expr tge e le m (Ecast a1 ty) v). econstructor; eauto. congruence.
  destruct dst; auto. simpl; econstructor; eauto.
(* sizeof *)
  destruct dst.
  split; auto. split; auto. constructor.
  auto.
  exists (Esizeof ty1 ty). split. auto. split. auto. constructor.
(* alignof *)
  destruct dst.
  split; auto. split; auto. constructor.
  auto.
  exists (Ealignof ty1 ty). split. auto. split. auto. constructor.
(* var local *)
  split; auto. split; auto. apply eval_Evar_local; auto. 
(* var global *)
  split; auto. split; auto. apply eval_Evar_global; auto.
    rewrite symbols_preserved; auto.
    eapply type_of_global_preserved; eauto. 
(* deref *)
  exploit H0; eauto. intros [A [B C]]. subst sl1.
  split; auto. split; auto. constructor; auto.
(* field struct *)
  exploit H0; eauto. intros [A [B C]]. subst sl1.
  split; auto. split; auto. rewrite B in H1. eapply eval_Efield_struct; eauto.
(* field union *)
  exploit H0; eauto. intros [A [B C]]. subst sl1.
  split; auto. split; auto. rewrite B in H1. eapply eval_Efield_union; eauto.
Qed.

Lemma tr_simple_rvalue:
  forall e m r v,
  eval_simple_rvalue ge e m r v ->
  forall le dst sl a tmps,
  tr_expr le dst r sl a tmps ->
  match dst with
  | For_val => sl = nil /\ Csyntax.typeof r = typeof a /\ eval_expr tge e le m a v
  | For_effects => sl = nil
  | For_set tyl t =>
      exists b, sl = do_set t tyl b
             /\ Csyntax.typeof r = typeof b
             /\ eval_expr tge e le m b v
  end.
Proof.
  intros e m. exact (proj1 (tr_simple e m)).
Qed.

Lemma tr_simple_lvalue: 
  forall e m l b ofs,
  eval_simple_lvalue ge e m l b ofs ->
  forall le sl a tmps,
  tr_expr le For_val l sl a tmps ->
  sl = nil /\ Csyntax.typeof l = typeof a /\ eval_lvalue tge e le m a b ofs.
Proof.
  intros e m. exact (proj2 (tr_simple e m)).
Qed.

Lemma tr_simple_exprlist:
  forall le rl sl al tmps,
  tr_exprlist le rl sl al tmps ->
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
  tr_expr le dst (C e) sl a tmps ->
  exists dst', exists sl1, exists sl2, exists a', exists tmp',
  tr_expr le dst' e sl1 a' tmp'
  /\ sl = sl1 ++ sl2
  /\ incl tmp' tmps
  /\ (forall le' e' sl3,
        tr_expr le' dst' e' sl3 a' tmp' ->
        (forall id, ~In id tmp' -> le'!id = le!id) ->
        Csyntax.typeof e' = Csyntax.typeof e ->
        tr_expr le' dst (C e') (sl3 ++ sl2) a tmps)
 ) /\ (
  forall from C, leftcontextlist from C ->
  forall le e sl a tmps,
  tr_exprlist le (C e) sl a tmps ->
  exists dst', exists sl1, exists sl2, exists a', exists tmp',
  tr_expr le dst' e sl1 a' tmp'
  /\ sl = sl1 ++ sl2
  /\ incl tmp' tmps
  /\ (forall le' e' sl3,
        tr_expr le' dst' e' sl3 a' tmp' ->
        (forall id, ~In id tmp' -> le'!id = le!id) ->
        Csyntax.typeof e' = Csyntax.typeof e ->
        tr_exprlist le' (C e') (sl3 ++ sl2) a tmps)
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

(* base *)
  TR. rewrite <- app_nil_end; auto. red; auto.
  intros. rewrite <- app_nil_end; auto. 
(* deref *)
  inv H1. 
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1; rewrite app_ass; eauto. auto.  
  intros. rewrite <- app_ass. econstructor; eauto. 
(* field *)
  inv H1.
  exploit H0. eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1; rewrite app_ass; eauto. auto. 
  intros. rewrite <- app_ass. econstructor; eauto.
(* rvalof *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1; rewrite app_ass; eauto. red; eauto. 
  intros. rewrite <- app_ass; econstructor; eauto. 
  exploit typeof_context; eauto. congruence.
(* addrof *)
  inv H1. 
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1; rewrite app_ass; eauto. auto. 
  intros. rewrite <- app_ass. econstructor; eauto.
(* unop *) 
  inv H1. 
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1; rewrite app_ass; eauto. auto. 
  intros. rewrite <- app_ass. econstructor; eauto. 
(* binop left *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto. 
  red; auto. 
  intros. rewrite <- app_ass. econstructor; eauto.
  eapply tr_expr_invariant; eauto. UNCHANGED. 
(* binop right *)
  inv H2. 
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. rewrite app_ass. eauto. 
  red; auto. 
  intros. rewrite <- app_ass. change (sl3 ++ sl2') with (nil ++ sl3 ++ sl2'). rewrite app_ass. econstructor; eauto.
  eapply tr_expr_invariant; eauto. UNCHANGED. 
(* cast *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1; rewrite app_ass; eauto. auto. 
  intros. rewrite <- app_ass. econstructor; eauto.
(* seqand *)
  inv H1.
  (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. 
  rewrite Q. rewrite app_ass. eauto. 
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto. 
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
  (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. 
  rewrite Q. rewrite app_ass. eauto. 
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto. 
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
  (* for set *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. 
  rewrite Q. rewrite app_ass. eauto. 
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto. 
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
(* seqor *)
  inv H1.
  (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. 
  rewrite Q. rewrite app_ass. eauto. 
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto. 
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
  (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. 
  rewrite Q. rewrite app_ass. eauto. 
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto. 
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
  (* for set *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. 
  rewrite Q. rewrite app_ass. eauto. 
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto. 
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto.
(* condition *)
  inv H1.
  (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. 
  rewrite Q. rewrite app_ass. eauto. 
  red; auto.
  intros. rewrite <- app_ass. econstructor. apply S; auto. 
  eapply tr_expr_invariant; eauto. UNCHANGED.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto. auto. auto.
  (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. 
  rewrite Q. rewrite app_ass. eauto. 
  red; auto.
  intros. rewrite <- app_ass. eapply tr_condition_effects. apply S; auto. 
  eapply tr_expr_invariant; eauto. UNCHANGED.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto. auto.
  (* for set *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. 
  rewrite Q. rewrite app_ass. eauto. 
  red; auto.
  intros. rewrite <- app_ass. eapply tr_condition_set. apply S; auto. 
  eapply tr_expr_invariant; eauto. UNCHANGED.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto. auto. auto.
(* assign left *)
  inv H1.
  (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto. 
  red; auto. 
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto.
  (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto. 
  red; auto. 
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto. auto. auto.
  eapply typeof_context; eauto.
  auto. 
(* assign right *)
  inv H2. 
  (* for effects *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. rewrite app_ass. eauto. 
  red; auto. 
  intros. rewrite <- app_ass. change (sl3 ++ sl2') with (nil ++ (sl3 ++ sl2')). rewrite app_ass. 
  econstructor. 
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto. auto. auto. auto.
  (* for val *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. rewrite app_ass. eauto. 
  red; auto. 
  intros. rewrite <- app_ass. change (sl3 ++ sl2') with (nil ++ (sl3 ++ sl2')). rewrite app_ass. 
  econstructor. 
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto. auto. auto. auto. auto. auto. auto. auto. 
  eapply typeof_context; eauto.
(* assignop left *)
  inv H1.
  (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto. 
  red; auto. 
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED. 
  symmetry; eapply typeof_context; eauto. eauto.  
  auto. auto. auto. auto. auto. auto.
  (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto. 
  red; auto. 
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED. 
  eauto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  eapply typeof_context; eauto.
(* assignop right *)
  inv H2.
  (* for effects *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. rewrite app_ass. eauto. 
  red; auto.
  intros. rewrite <- app_ass. change (sl0 ++ sl2') with (nil ++ sl0 ++ sl2'). rewrite app_ass. econstructor. 
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto. auto. eauto. auto. auto. auto. auto. auto. auto. 
  (* for val *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl.
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl2. rewrite app_ass. eauto. 
  red; auto. 
  intros. rewrite <- app_ass. change (sl0 ++ sl2') with (nil ++ sl0 ++ sl2'). rewrite app_ass. econstructor. 
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto. eauto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
(* postincr *)
  inv H1.
  (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto. red; auto. 
  intros. rewrite <- app_ass. econstructor; eauto. 
  symmetry; eapply typeof_context; eauto. 
  (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto. red; auto. 
  intros. rewrite <- app_ass. econstructor; eauto. 
  eapply typeof_context; eauto.
(* call left *)
  inv H1.
  (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto. red; auto. 
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_exprlist_invariant; eauto. UNCHANGED.
  auto. auto. auto.
  (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto. red; auto. 
  intros. rewrite <- app_ass. econstructor. auto. apply S; auto.
  eapply tr_exprlist_invariant; eauto. UNCHANGED.
  auto. auto. auto. auto. 
(* call right *)
  inv H2.
  (* for effects *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl. 
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto.
  (*destruct dst'; constructor||contradiction.*)
  red; auto. 
  intros. rewrite <- app_ass. change (sl3++sl2') with (nil ++ sl3 ++ sl2'). rewrite app_ass. econstructor.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto. auto. auto. auto.
  (* for val *)
  assert (sl1 = nil) by (eapply tr_simple_expr_nil; eauto). subst sl1; simpl. 
  exploit H1; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto.
  (*destruct dst'; constructor||contradiction.*)
  red; auto. 
  intros. rewrite <- app_ass. change (sl3++sl2') with (nil ++ sl3 ++ sl2'). rewrite app_ass. econstructor.
  auto. eapply tr_expr_invariant; eauto. UNCHANGED.
  apply S; auto.
  auto. auto. auto. auto.
(* builtin *)
  inv H1.
  (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto.
  red; auto. 
  intros. rewrite <- app_ass. change (sl3++sl2') with (nil ++ sl3 ++ sl2'). rewrite app_ass. econstructor.
  apply S; auto. auto.
  (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto.
  red; auto. 
  intros. rewrite <- app_ass. change (sl3++sl2') with (nil ++ sl3 ++ sl2'). rewrite app_ass. econstructor.
  auto. apply S; auto. auto. auto.
(* comma *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q; rewrite app_ass; eauto. red; auto. 
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_expr_invariant; eauto. UNCHANGED.
  auto. auto. auto.
(* paren *)
  inv H1. 
  (* for val *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q. eauto. red; auto. 
  intros. econstructor; eauto.
  (* for effects *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q. eauto. auto.
  intros. econstructor; eauto.
  (* for set *)
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. rewrite Q. eauto. auto.
  intros. econstructor; eauto.
(* cons left *)
  inv H1.
  exploit H0; eauto. intros [dst' [sl1' [sl2' [a' [tmp' [P [Q [R S]]]]]]]].
  TR. subst sl1. rewrite app_ass. eauto. 
  red; auto. 
  intros. rewrite <- app_ass. econstructor. apply S; auto.
  eapply tr_exprlist_invariant; eauto.  UNCHANGED.
  auto. auto. auto.
(* cons right *)
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
  tr_expr le dst (C r) sl a tmps ->
  exists dst', exists sl1, exists sl2, exists a', exists tmp',
  tr_expr le dst' r sl1 a' tmp'
  /\ sl = sl1 ++ sl2
  /\ incl tmp' tmps
  /\ (forall le' r' sl3,
        tr_expr le' dst' r' sl3 a' tmp' ->
        (forall id, ~In id tmp' -> le'!id = le!id) ->
        Csyntax.typeof r' = Csyntax.typeof r ->
        tr_expr le' dst (C r') (sl3 ++ sl2) a tmps).
Proof.
  intros. eapply (proj1 tr_expr_leftcontext_rec); eauto.
Qed.

Theorem tr_top_leftcontext:
  forall e le m dst rtop sl a tmps,
  tr_top tge e le m dst rtop sl a tmps ->
  forall r C,
  rtop = C r ->
  leftcontext RV RV C ->
  exists dst', exists sl1, exists sl2, exists a', exists tmp',
  tr_top tge e le m dst' r sl1 a' tmp'
  /\ sl = sl1 ++ sl2
  /\ incl tmp' tmps
  /\ (forall le' m' r' sl3,
        tr_expr le' dst' r' sl3 a' tmp' ->
        (forall id, ~In id tmp' -> le'!id = le!id) ->
        Csyntax.typeof r' = Csyntax.typeof r ->
        tr_top tge e le' m' dst (C r') (sl3 ++ sl2) a tmps).
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

Lemma eval_simpl_expr_sound:
  forall e le m a v, eval_expr tge e le m a v ->
  match eval_simpl_expr a with Some v' => v' = v | None => True end.
Proof.
  induction 1; simpl; auto. 
  destruct (eval_simpl_expr a); auto. subst. rewrite H0. auto. 
  inv H; simpl; auto.
Qed.

Lemma step_makeif:
  forall f a s1 s2 k e le m v1 b,
  eval_expr tge e le m a v1 ->
  bool_val v1 (typeof a) = Some b ->
  star step1 tge (State f (makeif a s1 s2) k e le m)
             E0 (State f (if b then s1 else s2) k e le m).
Proof.
  intros. functional induction (makeif a s1 s2).
  exploit eval_simpl_expr_sound; eauto. rewrite e0. intro EQ; subst v. 
  rewrite e1 in H0. inv H0. constructor.
  exploit eval_simpl_expr_sound; eauto. rewrite e0. intro EQ; subst v. 
  rewrite e1 in H0. inv H0. constructor.
  apply star_one. eapply step_ifthenelse; eauto. 
  apply star_one. eapply step_ifthenelse; eauto. 
Qed.

Lemma step_make_set:
  forall id a ty m b ofs t v e le f k,
  Csem.deref_loc ge ty m b ofs t v ->
  eval_lvalue tge e le m a b ofs ->
  typeof a = ty ->
  step1 tge (State f (make_set id a) k e le m)
          t (State f Sskip k e (PTree.set id v le) m).
Proof.
  intros. exploit deref_loc_translated; eauto. rewrite <- H1.
  unfold make_set. destruct (chunk_for_volatile_type (typeof a)) as [chunk|].
(* volatile case *)
  intros. change (PTree.set id v le) with (set_opttemp (Some id) v le). econstructor.
  econstructor. constructor. eauto.
  simpl. unfold sem_cast. simpl. eauto. constructor.
  simpl. econstructor; eauto. 
(* nonvolatile case *)
  intros [A B]. subst t. constructor. eapply eval_Elvalue; eauto.
Qed.

Lemma step_make_assign:
  forall a1 a2 ty m b ofs t v m' v2 e le f k,
  Csem.assign_loc ge ty m b ofs v t m' ->
  eval_lvalue tge e le m a1 b ofs ->
  eval_expr tge e le m a2 v2 ->
  sem_cast v2 (typeof a2) ty = Some v ->
  typeof a1 = ty ->
  step1 tge (State f (make_assign a1 a2) k e le m)
          t (State f Sskip k e le m').
Proof.
  intros. exploit assign_loc_translated; eauto. rewrite <- H3.
  unfold make_assign. destruct (chunk_for_volatile_type (typeof a1)) as [chunk|].
(* volatile case *)
  intros. change le with (set_opttemp None Vundef le) at 2. econstructor.
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
  forall ty m b ofs t v e le a sl a' tmp f k,
  Csem.deref_loc ge ty m b ofs t v ->
  eval_lvalue tge e le m a b ofs ->
  tr_rvalof ty a sl a' tmp ->
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
  intros. exists (PTree.set t0 v le); split.
  simpl. eapply star_two. econstructor. eapply step_make_set; eauto. traceEq.  
  split. constructor. apply PTree.gss.
  split. auto.
  intros. apply PTree.gso. congruence. 
Qed.

(** Matching between continuations *)

Inductive match_cont : Csem.cont -> cont -> Prop :=
  | match_Kstop:
      match_cont Csem.Kstop Kstop
  | match_Kseq: forall s k ts tk,
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont (Csem.Kseq s k) (Kseq ts tk)
  | match_Kwhile2: forall r s k s' ts tk,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont (Csem.Kwhile2 r s k)
                 (Kloop1 (Ssequence s' ts) Sskip tk)
  | match_Kdowhile1: forall r s k s' ts tk,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont (Csem.Kdowhile1 r s k)
                 (Kloop1 ts s' tk)
  | match_Kfor3: forall r s3 s k ts3 s' ts tk,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s3 ts3 ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont (Csem.Kfor3 r s3 s k)
                 (Kloop1 (Ssequence s' ts) ts3 tk)
  | match_Kfor4: forall r s3 s k ts3 s' ts tk,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s3 ts3 ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont (Csem.Kfor4 r s3 s k)
                 (Kloop2 (Ssequence s' ts) ts3 tk)
  | match_Kswitch2: forall k tk,
      match_cont k tk ->
      match_cont (Csem.Kswitch2 k) (Kswitch tk)
  | match_Kcall: forall f e C ty k optid tf le sl tk a dest tmps,
      transl_function f = Errors.OK tf ->
      leftcontext RV RV C ->
      (forall v m, tr_top tge e (set_opttemp optid v le) m dest (C (Csyntax.Eval v ty)) sl a tmps) ->
      match_cont_exp dest a k tk ->
      match_cont (Csem.Kcall f e C ty k)
                 (Kcall optid tf e le (Kseqlist sl tk))
(*
  | match_Kcall_some: forall f e C ty k dst tf le sl tk a dest tmps,
      transl_function f = Errors.OK tf ->
      leftcontext RV RV C ->
      (forall v m, tr_top tge e (PTree.set dst v le) m dest (C (C.Eval v ty)) sl a tmps) ->
      match_cont_exp dest a k tk ->
      match_cont (Csem.Kcall f e C ty k)
                 (Kcall (Some dst) tf e le (Kseqlist sl tk))
*)

with match_cont_exp : destination -> expr -> Csem.cont -> cont -> Prop :=
  | match_Kdo: forall k a tk,
      match_cont k tk ->
      match_cont_exp For_effects a (Csem.Kdo k) tk
  | match_Kifthenelse_1: forall a s1 s2 k ts1 ts2 tk,
      tr_stmt s1 ts1 -> tr_stmt s2 ts2 ->
      match_cont k tk ->
      match_cont_exp For_val a (Csem.Kifthenelse s1 s2 k) (Kseq (Sifthenelse a ts1 ts2) tk)
  | match_Kwhile1: forall r s k s' a ts tk,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont_exp For_val a
         (Csem.Kwhile1 r s k)
         (Kseq (makeif a Sskip Sbreak)
           (Kseq ts (Kloop1 (Ssequence s' ts) Sskip tk)))
  | match_Kdowhile2: forall r s k s' a ts tk,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont_exp For_val a
        (Csem.Kdowhile2 r s k)
        (Kseq (makeif a Sskip Sbreak) (Kloop2 ts s' tk))
  | match_Kfor2: forall r s3 s k s' a ts3 ts tk,
      tr_if r Sskip Sbreak s' ->
      tr_stmt s3 ts3 ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_cont_exp For_val a
        (Csem.Kfor2 r s3 s k)
        (Kseq (makeif a Sskip Sbreak)
          (Kseq ts (Kloop1 (Ssequence s' ts) ts3 tk)))
  | match_Kswitch1: forall ls k a tls tk,
      tr_lblstmts ls tls ->
      match_cont k tk ->
      match_cont_exp For_val a (Csem.Kswitch1 ls k) (Kseq (Sswitch a tls) tk)
  | match_Kreturn: forall k a tk,
      match_cont k tk ->
      match_cont_exp For_val a (Csem.Kreturn k) (Kseq (Sreturn (Some a)) tk).

Lemma match_cont_call:
  forall k tk,
  match_cont k tk ->
  match_cont (Csem.call_cont k) (call_cont tk).
Proof.
  induction 1; simpl; auto. constructor. econstructor; eauto. 
Qed.

(** Matching between states *)

Inductive match_states: Csem.state -> state -> Prop :=
  | match_exprstates: forall f r k e m tf sl tk le dest a tmps,
      transl_function f = Errors.OK tf ->
      tr_top tge e le m dest r sl a tmps ->
      match_cont_exp dest a k tk ->
      match_states (Csem.ExprState f r k e m)
                   (State tf Sskip (Kseqlist sl tk) e le m)
  | match_regularstates: forall f s k e m tf ts tk le,
      transl_function f = Errors.OK tf ->
      tr_stmt s ts ->
      match_cont k tk ->
      match_states (Csem.State f s k e m)
                   (State tf ts tk e le m)
  | match_callstates: forall fd args k m tfd tk,
      transl_fundef fd = Errors.OK tfd ->
      match_cont k tk ->
      match_states (Csem.Callstate fd args k m)
                   (Callstate tfd args tk m)
  | match_returnstates: forall res k m tk,
      match_cont k tk ->
      match_states (Csem.Returnstate res k m)
                   (Returnstate res tk m)
  | match_stuckstate: forall S,
      match_states Csem.Stuckstate S.

(** Additional results on translation of statements *)

Lemma tr_select_switch:
  forall n ls tls,
  tr_lblstmts ls tls ->
  tr_lblstmts (Csem.select_switch n ls) (select_switch n tls).
Proof.
  induction 1; simpl.
  constructor; auto.
  destruct (Int.eq n0 n). constructor; auto. auto.
Qed.

Lemma tr_seq_of_labeled_statement:
  forall ls tls,
  tr_lblstmts ls tls ->
  tr_stmt (Csem.seq_of_labeled_statement ls) (seq_of_labeled_statement tls).
Proof.
  induction 1; simpl. auto. constructor; auto.
Qed.

(** Commutation between translation and the "find label" operation. *)

Section FIND_LABEL.

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
  forall t a, nolabel (make_set t a).
Proof.
  unfold make_set; intros; red; intros. 
  destruct (chunk_for_volatile_type (typeof a)); auto.
Qed.

Lemma make_assign_nolabel:
  forall l r, nolabel (make_assign l r).
Proof.
  unfold make_assign; intros; red; intros. 
  destruct (chunk_for_volatile_type (typeof l)); auto.
Qed.

Lemma tr_rvalof_nolabel:
  forall ty a sl a' tmp, tr_rvalof ty a sl a' tmp -> nolabel_list sl.
Proof.
  destruct 1; simpl; intuition. apply make_set_nolabel. 
Qed.

Lemma nolabel_do_set:
  forall tmp tyl a, nolabel_list (do_set tmp tyl a).
Proof.
  induction tyl; intros; simpl; split; auto; red; auto.
Qed.

Lemma nolabel_final:
  forall dst a, nolabel_list (final dst a).
Proof.
  destruct dst; simpl; intros. auto. auto. apply nolabel_do_set. 
Qed. 

(*
Lemma nolabel_dest_cast:
  forall ty dst, nolabel_dest dst -> nolabel_dest (cast_destination ty dst).
Proof.
  unfold nolabel_dest; intros; destruct dst; auto.
Qed.
*)

Ltac NoLabelTac :=
  match goal with
  | [ |- nolabel_list nil ] => exact I
  | [ |- nolabel_list (final _ _) ] => apply nolabel_final (*; NoLabelTac*)
  | [ |- nolabel_list (_ :: _) ] => simpl; split; NoLabelTac
  | [ |- nolabel_list (_ ++ _) ] => apply nolabel_list_app; NoLabelTac
  | [ H: _ -> nolabel_list ?x |- nolabel_list ?x ] => apply H; NoLabelTac
  | [ |- nolabel (makeseq _) ] => apply makeseq_nolabel; NoLabelTac
  | [ |- nolabel (makeif _ _ _) ] => apply makeif_nolabel; NoLabelTac
  | [ |- nolabel (make_set _ _) ] => apply make_set_nolabel
  | [ |- nolabel (make_assign _ _) ] => apply make_assign_nolabel
  | [ |- nolabel _ ] => red; intros; simpl; auto
  | [ |- _ /\ _ ] => split; NoLabelTac
  | _ => auto
  end.

Lemma tr_find_label_expr:
  (forall le dst r sl a tmps, tr_expr le dst r sl a tmps -> nolabel_list sl)
/\(forall le rl sl al tmps, tr_exprlist le rl sl al tmps -> nolabel_list sl).
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
  tr_top tge e le m dst r sl a tmps -> nolabel_list sl.
Proof.
  induction 1; intros; NoLabelTac.
  eapply (proj1 tr_find_label_expr); eauto.
Qed.

Lemma tr_find_label_expression:
  forall r s a, tr_expression r s a -> forall k, find_label lbl s k = None.
Proof.
  intros. inv H.
  assert (nolabel (makeseq sl)). apply makeseq_nolabel.
  eapply tr_find_label_top with (e := empty_env) (le := PTree.empty val) (m := Mem.empty).
  eauto. apply H.
Qed.

Lemma tr_find_label_expr_stmt:
  forall r s, tr_expr_stmt r s -> forall k, find_label lbl s k = None.
Proof.
  intros. inv H.
  assert (nolabel (makeseq sl)). apply makeseq_nolabel.
  eapply tr_find_label_top with (e := empty_env) (le := PTree.empty val) (m := Mem.empty).
  eauto. apply H.
Qed.

Lemma tr_find_label_if:
  forall r s,
  tr_if r Sskip Sbreak s ->
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
    (TR: tr_stmt s ts)
    (MC: match_cont k tk),
  match Csem.find_label lbl s k with
  | None =>
      find_label lbl ts tk = None
  | Some (s', k') =>
      exists ts', exists tk',
          find_label lbl ts tk = Some (ts', tk')
       /\ tr_stmt s' ts'
       /\ match_cont k' tk'
  end
with tr_find_label_ls:
  forall s k ts tk
    (TR: tr_lblstmts s ts)
    (MC: match_cont k tk),
  match Csem.find_label_ls lbl s k with
  | None =>
      find_label_ls lbl ts tk = None
  | Some (s', k') =>
      exists ts', exists tk',
          find_label_ls lbl ts tk = Some (ts', tk')
       /\ tr_stmt s' ts'
       /\ match_cont k' tk'
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
(* if *)
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
(* default *)
  apply tr_find_label; auto. 
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
  | Csyntax.Eloc _ _ _ => 1%nat
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
  | Csyntax.Eparen r1 _ => S(esize r1)
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
  forall le dst v ty a tmp,
  typeof a = ty ->
  (forall tge e le' m,
      (forall id, In id tmp -> le'!id = le!id) ->
      eval_expr tge e le' m a v) ->
  tr_expr le dst (Csyntax.Eval v ty) (final dst a) a tmp.
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
  induction 1; intros; inv MS.
(* expr *)
  assert (tr_expr le dest r sl a tmps).
    inv H9. contradiction. auto. 
  exploit tr_simple_rvalue; eauto. destruct dest.
  (* for val *)
  intros [SL1 [TY1 EV1]]. subst sl.
  econstructor; split.
  right; split. apply star_refl. destruct r; simpl; (contradiction || omega).
  econstructor; eauto.
  instantiate (1 := tmps). apply tr_top_val_val; auto.
  (* for effects *)
  intros SL1. subst sl.
  econstructor; split.
  right; split. apply star_refl. destruct r; simpl; (contradiction || omega).
  econstructor; eauto.
  instantiate (1 := tmps). apply tr_top_base. constructor.
  (* for set *)
  inv H10.
(* rval volatile *)
  exploit tr_top_leftcontext; eauto. clear H11.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H2. inv H7; try congruence.
  exploit tr_simple_lvalue; eauto. intros [SL [TY EV]]. subst sl0; simpl.
  econstructor; split.
  left. eapply plus_two. constructor. eapply step_make_set; eauto. traceEq. 
  econstructor; eauto.
  change (final dst' (Etempvar t0 (Csyntax.typeof l)) ++ sl2) with (nil ++ (final dst' (Etempvar t0 (Csyntax.typeof l)) ++ sl2)).
  apply S. apply tr_val_gen. auto. 
  intros. constructor. rewrite H5; auto. apply PTree.gss.
  intros. apply PTree.gso. red; intros; subst; elim H5; auto. 
  auto.
(* seqand true *)
  exploit tr_top_leftcontext; eauto. clear H9. 
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H2.
  (* for val *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. apply tr_paren_val with (a1 := dummy_expr); auto. econstructor; eauto. 
  apply tr_expr_monotone with tmp2; eauto. auto. auto.
  (* for effects *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. apply tr_paren_effects with (a1 := dummy_expr); auto. econstructor; eauto. 
  apply tr_expr_monotone with tmp2; eauto. auto. auto.
  (* for set *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. apply tr_paren_set with (a1 := dummy_expr); auto. econstructor; eauto. 
  apply tr_expr_monotone with tmp2; eauto. auto. auto.
(* seqand false *)
  exploit tr_top_leftcontext; eauto. clear H9. 
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H2.
  (* for val *)
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
  (* for effects *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  apply step_makeif with (b := false) (v1 := v); auto. congruence.
  reflexivity. 
  eapply match_exprstates; eauto.
  change sl2 with (nil ++ sl2). apply S. econstructor; eauto.
  auto. auto.
  (* for set *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. econstructor; eauto. intros. constructor. auto. auto.
(* seqor true *)
  exploit tr_top_leftcontext; eauto. clear H9. 
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H2.
  (* for val *)
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
  (* for effects *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  apply step_makeif with (b := true) (v1 := v); auto. congruence.
  reflexivity. 
  eapply match_exprstates; eauto.
  change sl2 with (nil ++ sl2). apply S. econstructor; eauto.
  auto. auto.
  (* for set *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. econstructor; eauto. intros. constructor. auto. auto.
(* seqand false *)
  exploit tr_top_leftcontext; eauto. clear H9. 
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H2.
  (* for val *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. apply tr_paren_val with (a1 := dummy_expr); auto. econstructor; eauto. 
  apply tr_expr_monotone with tmp2; eauto. auto. auto.
  (* for effects *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. apply tr_paren_effects with (a1 := dummy_expr); auto. econstructor; eauto. 
  apply tr_expr_monotone with tmp2; eauto. auto. auto.
  (* for set *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
  apply push_seq. reflexivity. reflexivity.
  rewrite <- Kseqlist_app.
  eapply match_exprstates; eauto.
  apply S. apply tr_paren_set with (a1 := dummy_expr); auto. econstructor; eauto. 
  apply tr_expr_monotone with tmp2; eauto. auto. auto.
(* condition *)
  exploit tr_top_leftcontext; eauto. clear H9. 
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H2. 
  (* for value *)
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
  (* for effects *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist. destruct b.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
  apply push_seq. 
  reflexivity. traceEq.
  rewrite <- Kseqlist_app.
  econstructor. eauto. apply S.
    econstructor; eauto. apply tr_expr_monotone with tmp2; eauto. 
    econstructor; eauto. 
  auto. auto.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
  apply push_seq. 
  reflexivity. traceEq.
  rewrite <- Kseqlist_app.
  econstructor. eauto. apply S.
    econstructor; eauto. apply tr_expr_monotone with tmp3; eauto. 
    econstructor; eauto. 
  auto. auto.
  (* for set *)
  exploit tr_simple_rvalue; eauto. intros [SL [TY EV]].
  subst sl0; simpl Kseqlist. destruct b.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := true) (v1 := v); auto. congruence.
  apply push_seq. 
  reflexivity. traceEq.
  rewrite <- Kseqlist_app.
  econstructor. eauto. apply S.
    econstructor; eauto. apply tr_expr_monotone with tmp2; eauto. 
    econstructor; eauto. 
  auto. auto.
  econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (b := false) (v1 := v); auto. congruence.
  apply push_seq. 
  reflexivity. traceEq.
  rewrite <- Kseqlist_app.
  econstructor. eauto. apply S.
    econstructor; eauto. apply tr_expr_monotone with tmp3; eauto. 
    econstructor; eauto. 
  auto. auto.
(* assign *)
  exploit tr_top_leftcontext; eauto. clear H12. 
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H4.
  (* for effects *)
  exploit tr_simple_rvalue; eauto. intros [SL2 [TY2 EV2]].
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  subst; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor.
  apply star_one. eapply step_make_assign; eauto. 
  rewrite <- TY2; eauto. traceEq.
  econstructor. auto. change sl2 with (nil ++ sl2). apply S.
  constructor. auto. auto. auto.
  (* for value *)
  exploit tr_simple_rvalue; eauto. intros [SL2 [TY2 EV2]].
  exploit tr_simple_lvalue. eauto.
    eapply tr_expr_invariant with (le' := PTree.set t0 v le). eauto. 
    intros. apply PTree.gso. intuition congruence.
  intros [SL1 [TY1 EV1]].
  subst; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_left. constructor. 
  eapply star_left. constructor. eauto. 
  eapply star_left. constructor.
  apply star_one. eapply step_make_assign; eauto. 
  constructor. apply PTree.gss. reflexivity. reflexivity. traceEq. 
  econstructor. auto. apply S.
  apply tr_val_gen. auto. intros. econstructor; eauto. constructor. 
  rewrite H4; auto. apply PTree.gss. 
  intros. apply PTree.gso. intuition congruence.
  auto. auto.
(* assignop *)
  exploit tr_top_leftcontext; eauto. clear H15. 
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H6.
  (* for effects *)
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit step_tr_rvalof; eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
  exploit tr_simple_lvalue. eauto. eapply tr_expr_invariant with (le := le) (le' := le'). eauto. 
  intros. apply INV. NOTIN. intros [? [? EV1']].
  exploit tr_simple_rvalue. eauto. eapply tr_expr_invariant with (le := le) (le' := le'). eauto. 
  intros. apply INV. NOTIN. simpl. intros [SL2 [TY2 EV2]].
  subst; simpl Kseqlist. 
  econstructor; split.
  left. eapply star_plus_trans. rewrite app_ass. rewrite Kseqlist_app. eexact EXEC.
  eapply plus_two. simpl. econstructor. eapply step_make_assign; eauto. 
    econstructor. eexact EV3. eexact EV2. 
    rewrite TY3; rewrite <- TY1; rewrite <- TY2; eauto.
  reflexivity. traceEq.
  econstructor. auto. change sl2 with (nil ++ sl2). apply S.
  constructor. auto. auto. auto.
  (* for value *)
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit step_tr_rvalof; eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
  exploit tr_simple_lvalue. eauto. eapply tr_expr_invariant with (le := le) (le' := le'). eauto. 
  intros. apply INV. NOTIN. intros [? [? EV1']].
  exploit tr_simple_rvalue. eauto. eapply tr_expr_invariant with (le := le) (le' := le'). eauto. 
  intros. apply INV. NOTIN. simpl. intros [SL2 [TY2 EV2]].
  exploit tr_simple_lvalue. eauto. 
    eapply tr_expr_invariant with (le := le) (le' := PTree.set t v3 le'). eauto. 
    intros. rewrite PTree.gso. apply INV. NOTIN. intuition congruence.
  intros [? [? EV1'']].
  subst; simpl Kseqlist.
  econstructor; split.
  left. rewrite app_ass. rewrite Kseqlist_app. 
  eapply star_plus_trans. eexact EXEC.
  simpl. eapply plus_four. econstructor. econstructor.
    econstructor. eexact EV3. eexact EV2. 
    rewrite TY3; rewrite <- TY1; rewrite <- TY2. eauto.
  econstructor. eapply step_make_assign; eauto. 
    constructor. apply PTree.gss. 
    reflexivity. traceEq.
  econstructor. auto. apply S.
  apply tr_val_gen. auto. intros. econstructor; eauto. constructor. 
  rewrite H10; auto. apply PTree.gss. 
  intros. rewrite PTree.gso. apply INV. 
  red; intros; elim H10; auto. 
  intuition congruence.
  auto. auto.
(* assignop stuck *)
  exploit tr_top_leftcontext; eauto. clear H12. 
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H4.
  (* for effects *)
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit tr_simple_rvalue; eauto. intros [SL2 [TY2 EV2]].
  exploit step_tr_rvalof; eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
  subst; simpl Kseqlist. 
  econstructor; split.
  right; split. rewrite app_ass. rewrite Kseqlist_app. eexact EXEC. 
  simpl. omega.
  constructor.
  (* for value *)
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit tr_simple_rvalue; eauto. intros [SL2 [TY2 EV2]].
  exploit step_tr_rvalof; eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
  subst; simpl Kseqlist. 
  econstructor; split.
  right; split. rewrite app_ass. rewrite Kseqlist_app. eexact EXEC. 
  simpl. omega.
  constructor.
(* postincr *)
  exploit tr_top_leftcontext; eauto. clear H14. 
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H5.
  (* for effects *)
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit step_tr_rvalof; eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
  exploit tr_simple_lvalue. eauto. eapply tr_expr_invariant with (le := le) (le' := le'). eauto. 
  intros. apply INV. NOTIN. intros [? [? EV1']].
  subst; simpl Kseqlist.
  econstructor; split.
  left. rewrite app_ass; rewrite Kseqlist_app. 
  eapply star_plus_trans. eexact EXEC. 
  eapply plus_two. simpl. constructor.
  eapply step_make_assign; eauto. 
  unfold transl_incrdecr. destruct id; simpl in H2. 
  econstructor. eauto. constructor. simpl. rewrite TY3; rewrite <- TY1. eauto.
  econstructor. eauto. constructor. simpl. rewrite TY3; rewrite <- TY1. eauto.
  destruct id; auto. 
  reflexivity. traceEq.
  econstructor. auto. change sl2 with (nil ++ sl2). apply S.
  constructor. auto. auto. auto.
  (* for value *)
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit tr_simple_lvalue. eauto.
    eapply tr_expr_invariant with (le' := PTree.set t v1 le). eauto. 
    intros. apply PTree.gso. intuition congruence.
  intros [SL2 [TY2 EV2]].
  subst; simpl Kseqlist.
  econstructor; split.
  left. eapply plus_four. constructor.
  eapply step_make_set; eauto. 
  constructor.
  eapply step_make_assign; eauto. 
  unfold transl_incrdecr. destruct id; simpl in H2. 
  econstructor. constructor. apply PTree.gss. constructor. simpl. eauto.
  econstructor. constructor. apply PTree.gss. constructor. simpl. eauto.
  destruct id; auto. 
  traceEq.
  econstructor. auto. apply S.
  apply tr_val_gen. auto. intros. econstructor; eauto.
  rewrite H5; auto. apply PTree.gss. 
  intros. apply PTree.gso. intuition congruence.
  auto. auto.
(* postincr stuck *)
  exploit tr_top_leftcontext; eauto. clear H11. 
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H3.
  (* for effects *)
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit step_tr_rvalof; eauto. intros [le' [EXEC [EV3 [TY3 INV]]]].
  subst. simpl Kseqlist. 
  econstructor; split.
  right; split. rewrite app_ass; rewrite Kseqlist_app. eexact EXEC.
  simpl; omega.
  constructor.
  (* for value *)
  exploit tr_simple_lvalue; eauto. intros [SL1 [TY1 EV1]].
  subst. simpl Kseqlist. 
  econstructor; split.
  left. eapply plus_two. constructor. eapply step_make_set; eauto. 
  traceEq.
  constructor.
(* comma *)
  exploit tr_top_leftcontext; eauto. clear H9. 
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H1.
  exploit tr_simple_rvalue; eauto. simpl; intro SL1.
  subst sl0; simpl Kseqlist.
  econstructor; split.
  right; split. apply star_refl. simpl. apply plus_lt_compat_r. 
  apply (leftcontext_size _ _ _ H). simpl. omega. 
  econstructor; eauto. apply S. 
  eapply tr_expr_monotone; eauto. 
  auto. auto. 
(* paren *)
  exploit tr_top_leftcontext; eauto. clear H9. 
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H2.
  (* for value *)
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
  (* for effects *)
  econstructor; split.
  right; split. apply star_refl. simpl. apply plus_lt_compat_r.
  apply (leftcontext_size _ _ _ H). simpl. omega.
  econstructor; eauto.
  exploit tr_simple_rvalue; eauto. simpl. intros A. subst sl1.
  apply S. constructor; auto. auto. auto.
  (* for set *)
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

(* call *)
  exploit tr_top_leftcontext; eauto. clear H12. 
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H5.
  (* for effects *)
  exploit tr_simple_rvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit tr_simple_exprlist; eauto. intros [SL2 EV2].
  subst. simpl Kseqlist.
  exploit functions_translated; eauto. intros [tfd [J K]].
  econstructor; split. 
  left. eapply plus_left. constructor.  apply star_one.
  econstructor; eauto. rewrite <- TY1; eauto.
  exploit type_of_fundef_preserved; eauto. congruence.
  traceEq.
  constructor; auto. econstructor; eauto.
  intros. change sl2 with (nil ++ sl2). apply S.
  constructor. auto. auto. 
  (* for value *)
  exploit tr_simple_rvalue; eauto. intros [SL1 [TY1 EV1]].
  exploit tr_simple_exprlist; eauto. intros [SL2 EV2].
  subst. simpl Kseqlist.
  exploit functions_translated; eauto. intros [tfd [J K]].
  econstructor; split. 
  left. eapply plus_left. constructor.  apply star_one.
  econstructor; eauto. rewrite <- TY1; eauto.
  exploit type_of_fundef_preserved; eauto. congruence.
  traceEq.
  constructor; auto. econstructor; eauto.
  intros. apply S.
  destruct dst'; constructor.
  auto. intros. constructor. rewrite H5; auto. apply PTree.gss. 
  auto. intros. constructor. rewrite H5; auto. apply PTree.gss.  
  intros. apply PTree.gso. intuition congruence.
  auto. 

(* builtin *)
  exploit tr_top_leftcontext; eauto. clear H9.
  intros [dst' [sl1 [sl2 [a' [tmp' [P [Q [R S]]]]]]]].
  inv P. inv H2.
  (* for effects *)
  exploit tr_simple_exprlist; eauto. intros [SL EV].
  subst. simpl Kseqlist.
  econstructor; split. 
  left. eapply plus_left. constructor.  apply star_one.
  econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved. 
  traceEq.
  econstructor; eauto.
  change sl2 with (nil ++ sl2). apply S. constructor. simpl; auto. auto. 
  (* for value *)
  exploit tr_simple_exprlist; eauto. intros [SL EV].
  subst. simpl Kseqlist.
  econstructor; split. 
  left. eapply plus_left. constructor. apply star_one.
  econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved. 
  traceEq.
  econstructor; eauto.
  change sl2 with (nil ++ sl2). apply S.
  apply tr_val_gen. auto. intros. constructor. rewrite H2; auto. simpl. apply PTree.gss.
  intros; simpl. apply PTree.gso. intuition congruence.
  auto.
Qed.

(** Forward simulation for statements. *)

Lemma tr_top_val_for_val_inv:
  forall e le m v ty sl a tmps,
  tr_top tge e le m For_val (Csyntax.Eval v ty) sl a tmps ->
  sl = nil /\ typeof a = ty /\ eval_expr tge e le m a v.
Proof.
  intros. inv H. auto. inv H0. auto. 
Qed.

Lemma alloc_variables_preserved:
  forall e m params e' m',
  Csem.alloc_variables e m params e' m' ->
  alloc_variables e m params e' m'.
Proof.
  induction 1; econstructor; eauto.
Qed.

Lemma bind_parameters_preserved:
  forall e m params args m',
  Csem.bind_parameters ge e m params args m' ->
  bind_parameters e m params args m'.
Proof.
  induction 1; econstructor; eauto.
  inv H0. 
  eapply assign_loc_value; eauto.
  inv H4. eapply assign_loc_value; eauto. 
  eapply assign_loc_copy; eauto.
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
(* do 1 *)
  inv H6. inv H0. 
  econstructor; split.
  right; split. apply push_seq. 
  simpl. omega.
  econstructor; eauto. constructor. auto.
(* do 2 *)
  inv H7. inv H6. inv H.  
  econstructor; split. 
  right; split. apply star_refl. simpl. omega.
  econstructor; eauto. constructor.

(* seq *)
  inv H6. econstructor; split. left. apply plus_one. constructor.
  econstructor; eauto. constructor; auto.
(* skip seq *)
  inv H6; inv H7. econstructor; split.
  left. apply plus_one; constructor.
  econstructor; eauto.
(* continue seq *)
  inv H6; inv H7. econstructor; split.
  left. apply plus_one; constructor.
  econstructor; eauto. constructor.
(* break seq *)
  inv H6; inv H7. econstructor; split.
  left. apply plus_one; constructor.
  econstructor; eauto. constructor.

(* ifthenelse *)
  inv H6.
  inv H2. econstructor; split.
  left. eapply plus_left. constructor. apply push_seq. traceEq.
  econstructor; eauto. econstructor; eauto.

(* ifthenelse *)
  inv H8. 
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst. 
  econstructor; split.
  left. eapply plus_two. constructor.
  apply step_ifthenelse with (v1 := v) (b := b); auto. traceEq.
  destruct b; econstructor; eauto.

(* while *)
  inv H6. inv H1. econstructor; split.
  left. eapply plus_left. constructor.
  eapply star_left. constructor.
  apply push_seq.
  reflexivity. traceEq. rewrite Kseqlist_app.
  econstructor; eauto. simpl.  econstructor; eauto. econstructor; eauto.
(* while false *)
  inv H8. 
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst. 
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (v1 := v) (b := false); auto.
  eapply star_two. constructor. apply step_break_loop1. 
  reflexivity. reflexivity. traceEq.
  constructor; auto. constructor.
(* while true *)
  inv H8. 
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst. 
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_right. apply step_makeif with (v1 := v) (b := true); auto.
  constructor.
  reflexivity. traceEq.
  constructor; auto. constructor; auto. 
(* skip-or-continue while *)
  assert (ts = Sskip \/ ts = Scontinue). destruct H; subst s0; inv H7; auto.
  inv H8.
  econstructor; split.
  left. eapply plus_two. apply step_skip_or_continue_loop1; auto.
  apply step_skip_loop2. traceEq.
  constructor; auto. constructor; auto. 
(* break while *)
  inv H6. inv H7. 
  econstructor; split.
  left. apply plus_one. apply step_break_loop1.
  constructor; auto. constructor.

(* dowhile *)
  inv H6. 
  econstructor; split.
  left. apply plus_one. apply step_loop. 
  constructor; auto. constructor; auto.
(* skip_or_continue dowhile *)
  assert (ts = Sskip \/ ts = Scontinue). destruct H; subst s0; inv H7; auto.
  inv H8. inv H4.
  econstructor; split.
  left. eapply plus_left. apply step_skip_or_continue_loop1. auto.
  apply push_seq. 
  traceEq.
  rewrite Kseqlist_app.
  econstructor; eauto. simpl. econstructor; auto. econstructor; eauto. 
(* dowhile false *)
  inv H8. 
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst. 
  econstructor; split.
  left. simpl. eapply plus_left. constructor. 
  eapply star_right. apply step_makeif with (v1 := v) (b := false); auto. 
  constructor. 
  reflexivity. traceEq.
  constructor; auto. constructor.
(* dowhile true *)
  inv H8. 
  exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst. 
  econstructor; split.
  left. simpl. eapply plus_left. constructor. 
  eapply star_right. apply step_makeif with (v1 := v) (b := true); auto. 
  constructor. 
  reflexivity. traceEq.
  constructor; auto. constructor; auto. 
(* break dowhile *)
  inv H6. inv H7.
  econstructor; split.
  left. apply plus_one. apply step_break_loop1.
  constructor; auto. constructor.

(* for start *)
  inv H7. congruence. 
  econstructor; split. 
  left; apply plus_one. constructor.
  econstructor; eauto. constructor; auto. econstructor; eauto. 
(* for *)
  inv H6; try congruence. inv H2. 
  econstructor; split.
  left. eapply plus_left. apply step_loop. 
  eapply star_left. constructor. apply push_seq.
  reflexivity. traceEq.
  rewrite Kseqlist_app. econstructor; eauto. simpl. constructor; auto. econstructor; eauto.
(* for false *)
  inv H8. exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  econstructor; split.
  left. simpl. eapply plus_left. constructor.
  eapply star_trans. apply step_makeif with (v1 := v) (b := false); auto.
  eapply star_two. constructor. apply step_break_loop1.
  reflexivity. reflexivity. traceEq.
  constructor; auto. constructor.
(* for true *)
  inv H8. exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  econstructor; split.
  left. simpl. eapply plus_left. constructor. 
  eapply star_right. apply step_makeif with (v1 := v) (b := true); auto.
  constructor.
  reflexivity. traceEq.
  constructor; auto. constructor; auto. 
(* skip_or_continue for3 *)
  assert (ts = Sskip \/ ts = Scontinue). destruct H; subst x; inv H7; auto.
  inv H8.
  econstructor; split.
  left. apply plus_one. apply step_skip_or_continue_loop1. auto.
  econstructor; eauto. econstructor; auto.
(* break for3 *)
  inv H6. inv H7. 
  econstructor; split.
  left. apply plus_one. apply step_break_loop1.
  econstructor; eauto. constructor.
(* skip for4 *)
  inv H6. inv H7. 
  econstructor; split.
  left. apply plus_one. constructor.
  econstructor; eauto. constructor; auto. 

(* return none *)
  inv H7. econstructor; split.
  left. apply plus_one. econstructor; eauto. 
  constructor. apply match_cont_call; auto. 
(* return some 1 *)
  inv H6. inv H0. econstructor; split.
  left; eapply plus_left. constructor. apply push_seq. traceEq.
  econstructor; eauto. constructor. auto.
(* return some 2 *)
  inv H9. exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  econstructor; split.
  left. eapply plus_two. constructor. econstructor. eauto.
  replace (fn_return tf) with (Csyntax.fn_return f). eauto.
  exploit transl_function_spec; eauto. intuition congruence. 
  eauto. traceEq.
  constructor. apply match_cont_call; auto.
(* skip return *)
  inv H8. 
  assert (is_call_cont tk). inv H9; simpl in *; auto.
  econstructor; split.
  left. apply plus_one. apply step_skip_call; eauto.
  constructor. auto.

(* switch *)
  inv H6. inv H1. 
  econstructor; split. 
  left; eapply plus_left. constructor. apply push_seq. traceEq.
  econstructor; eauto. constructor; auto. 
(* expr switch *)
  inv H7. exploit tr_top_val_for_val_inv; eauto. intros [A [B C]]. subst.
  econstructor; split.
  left; eapply plus_two. constructor. econstructor; eauto. traceEq.
  econstructor; eauto.
  apply tr_seq_of_labeled_statement. apply tr_select_switch. auto. 
  constructor; auto.

(* skip-or-break switch *)
  assert (ts = Sskip \/ ts = Sbreak). destruct H; subst x; inv H7; auto.
  inv H8.
  econstructor; split.
  left; apply plus_one. apply step_skip_break_switch. auto. 
  constructor; auto. constructor.

(* continue switch *)
  inv H6. inv H7.
  econstructor; split.
  left; apply plus_one. apply step_continue_switch.
  constructor; auto. constructor.

(* label *)
  inv H6. econstructor; split.
  left; apply plus_one. constructor.
  constructor; auto.

(* goto *)
  inv H7.
  exploit transl_function_spec; eauto. intros [A [B [C D]]].
  exploit tr_find_label. eexact A. apply match_cont_call. eauto. 
  instantiate (1 := lbl). rewrite H. 
  intros [ts' [tk' [P [Q R]]]]. 
  econstructor; split. 
  left. apply plus_one. econstructor; eauto.
  econstructor; eauto. 

(* internal function *)
  monadInv H7. 
  exploit transl_function_spec; eauto. intros [A [B [C D]]].
  econstructor; split.
  left; apply plus_one. eapply step_internal_function. econstructor.
  rewrite C; rewrite D; auto.
  rewrite C; rewrite D. eapply alloc_variables_preserved; eauto.
  rewrite C. eapply bind_parameters_preserved; eauto.
  eauto. 
  constructor; auto. 

(* external function *)
  monadInv H5. 
  econstructor; split.
  left; apply plus_one. econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved. 
  constructor; auto.

(* return *)
  inv H3.
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
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  econstructor; split.
  econstructor.
  apply (Genv.init_mem_transf_partial _ _ TRANSL). eauto. 
  simpl. fold tge. rewrite symbols_preserved.
  replace (prog_main tprog) with (prog_main prog). eexact H1.
  symmetry. unfold transl_program in TRANSL.
  eapply transform_partial_program_main; eauto.
  eexact FIND.
  rewrite <- H3. apply type_of_fundef_preserved. auto.
  constructor. auto. constructor.
Qed.

Lemma transl_final_states:
  forall S S' r,
  match_states S S' -> Csem.final_state S r -> Clight.final_state S' r.
Proof.
  intros. inv H0. inv H. inv H4. constructor.
Qed.

Theorem transl_program_correct:
  forward_simulation (Cstrategy.semantics prog) (Clight.semantics1 tprog).
Proof.
  eapply forward_simulation_star_wf with (order := ltof _ measure).
  eexact symbols_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  apply well_founded_ltof.
  exact simulation.
Qed.

End PRESERVATION.
