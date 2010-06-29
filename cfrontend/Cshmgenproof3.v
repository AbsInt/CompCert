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

(** * Correctness of the C front end, part 3: semantic preservation *)

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
Require Import Csyntax.
Require Import Csem.
Require Import Ctyping.
Require Import Cminor.
Require Import Csharpminor.
Require Import Cshmgen.
Require Import Cshmgenproof1.
Require Import Cshmgenproof2.

Section CORRECTNESS.

Variable prog: Csyntax.program.
Variable tprog: Csharpminor.program.
Hypothesis WTPROG: wt_program prog.
Hypothesis TRANSL: transl_program prog = OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Let tgvare : gvarenv := global_var_env tprog.
Let tgve := (tge, tgvare).

Lemma symbols_preserved:
  forall s, Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf_partial2 transl_fundef transl_globvar _ TRANSL).

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial2 transl_fundef transl_globvar _ TRANSL).

Lemma function_ptr_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial2 transl_fundef transl_globvar _ TRANSL).

Lemma functions_well_typed:
  forall v f,
  Genv.find_funct ge v = Some f ->
  wt_fundef (global_typenv prog) f.
Proof.
  intros. inversion WTPROG. 
  apply (@Genv.find_funct_prop _ _ (wt_fundef (global_typenv prog)) prog v f).
  intros. apply wt_program_funct with id. assumption.
  assumption.
Qed.

Lemma function_ptr_well_typed:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  wt_fundef (global_typenv prog) f.
Proof.
  intros. inversion WTPROG. 
  apply (@Genv.find_funct_ptr_prop _ _ (wt_fundef (global_typenv prog)) prog b f).
  intros. apply wt_program_funct with id. assumption.
  assumption.
Qed.

(** * Matching between environments *)

(** In this section, we define a matching relation between
  a Clight local environment and a Csharpminor local environment,
  parameterized by an assignment of types to the Clight variables. *)

Record match_env (tyenv: typenv) (e: Csem.env) (te: Csharpminor.env) : Prop :=
  mk_match_env {
    me_local:
      forall id b ty,
      e!id = Some (b, ty) ->
      exists vk,
        tyenv!id = Some ty
        /\ var_kind_of_type ty = OK vk
        /\ te!id = Some (b, vk);
    me_local_inv:
      forall id b vk,
      te!id = Some (b, vk) -> exists ty, e!id = Some(b, ty);
    me_global:
      forall id ty,
      e!id = None -> tyenv!id = Some ty ->
      te!id = None /\ 
      (forall chunk, access_mode ty = By_value chunk -> (global_var_env tprog)!id = Some (Vscalar chunk))
  }.

Lemma match_env_same_blocks:
  forall tyenv e te,
  match_env tyenv e te ->
  blocks_of_env te = Csem.blocks_of_env e.
Proof.
  intros.
  set (R := fun (x: (block * type)) (y: (block * var_kind)) =>
         match x, y with
         | (b1, ty), (b2, vk) => b2 = b1 /\ var_kind_of_type ty = OK vk
         end).
  assert (list_forall2 
            (fun i_x i_y => fst i_x = fst i_y /\ R (snd i_x) (snd i_y))
            (PTree.elements e) (PTree.elements te)).
  apply PTree.elements_canonical_order.
  intros id [b ty] GET. exploit me_local; eauto. intros [vk [A [B C]]].
  exists (b, vk); split; auto. red. auto.
  intros id [b vk] GET. 
  exploit me_local_inv; eauto. intros [ty A]. 
  exploit me_local; eauto. intros [vk' [B [C D]]]. 
  assert (vk' = vk) by congruence. subst vk'.
  exists (b, ty); split; auto. red. auto.

  unfold blocks_of_env, Csem.blocks_of_env.
  generalize H0. induction 1. auto. 
  simpl. f_equal; auto.
  unfold block_of_binding, Csem.block_of_binding. 
  destruct a1 as [id1 [blk1 ty1]]. destruct b1 as [id2 [blk2 vk2]].
  simpl in *. destruct H1 as [A [B C]]. subst blk2 id2. f_equal.
  apply sizeof_var_kind_of_type. auto. 
Qed.

Lemma match_env_free_blocks:
  forall tyenv e te m m',
  match_env tyenv e te ->
  Mem.free_list m (Csem.blocks_of_env e) = Some m' ->
  Mem.free_list m (blocks_of_env te) = Some m'.
Proof.
  intros. rewrite (match_env_same_blocks _ _ _ H). auto.
Qed.

Definition match_globalenv (tyenv: typenv) (gv: gvarenv): Prop :=
  forall id ty chunk,
  tyenv!id = Some ty -> access_mode ty = By_value chunk ->
  gv!id = Some (Vscalar chunk).

Lemma match_globalenv_match_env_empty:
  forall tyenv,
  match_globalenv tyenv (global_var_env tprog) ->
  match_env tyenv Csem.empty_env Csharpminor.empty_env.
Proof.
  intros. unfold Csem.empty_env, Csharpminor.empty_env.
  constructor.
  intros until b. repeat rewrite PTree.gempty. congruence.
  intros until vk. rewrite PTree.gempty. congruence.
  intros. split.
  apply PTree.gempty. 
  intros. red in H. eauto.
Qed.

(** The following lemmas establish the [match_env] invariant at
  the beginning of a function invocation, after allocation of
  local variables and initialization of the parameters. *)

Lemma match_env_alloc_variables:
  forall e1 m1 vars e2 m2,
  Csem.alloc_variables e1 m1 vars e2 m2 ->
  forall tyenv te1 tvars,
  match_env tyenv e1 te1 ->
  transl_vars vars = OK tvars ->
  exists te2,
  Csharpminor.alloc_variables te1 m1 tvars te2 m2
  /\ match_env (Ctyping.add_vars tyenv vars) e2 te2.
Proof.
  induction 1; intros.
  simpl in H0. inversion H0; subst; clear H0. 
  exists te1; split. constructor. simpl. auto.
  generalize H2. simpl. 
  caseEq (var_kind_of_type ty); simpl; [intros vk VK | congruence].
  caseEq (transl_vars vars); simpl; [intros tvrs TVARS | congruence].
  intro EQ; inversion EQ; subst tvars; clear EQ.
  set (te2 := PTree.set id (b1, vk) te1).
  assert (match_env (add_var tyenv (id, ty)) (PTree.set id (b1, ty) e) te2).
    inversion H1. unfold te2, add_var. constructor.
    (* me_local *)
    intros until ty0. simpl. repeat rewrite PTree.gsspec.
    destruct (peq id0 id); intros.
    inv H3. exists vk; intuition.
    auto.
    (* me_local_inv *)
    intros until vk0. repeat rewrite PTree.gsspec. 
    destruct (peq id0 id); intros. exists ty; congruence. eauto. 
    (* me_global *)
    intros until ty0. repeat rewrite PTree.gsspec. simpl. destruct (peq id0 id); intros.
    discriminate.
    auto.
  destruct (IHalloc_variables _ _ _ H3 TVARS) as [te3 [ALLOC MENV]]. 
  exists te3; split.
  econstructor; eauto.
  rewrite (sizeof_var_kind_of_type _ _ VK). eauto. 
  auto. 
Qed. 

Lemma bind_parameters_match_rec:
  forall e m1 vars vals m2,
  Csem.bind_parameters e m1 vars vals m2 ->
  forall tyenv te tvars,
  (forall id ty, In (id, ty) vars -> tyenv!id = Some ty) ->
  match_env tyenv e te ->
  transl_params vars = OK tvars ->
  Csharpminor.bind_parameters te m1 tvars vals m2.
Proof.
  induction 1; intros.
  simpl in H1. inversion H1. constructor.
  generalize H4; clear H4; simpl. 
  caseEq (chunk_of_type ty); simpl; [intros chunk CHK | congruence].
  caseEq (transl_params params); simpl; [intros tparams TPARAMS | congruence].
  intro EQ; inversion EQ; clear EQ; subst tvars.
  generalize CHK. unfold chunk_of_type. 
  caseEq (access_mode ty); intros; try discriminate.
  inversion CHK0; clear CHK0; subst m0.
  unfold store_value_of_type in H0. rewrite H4 in H0.
  apply bind_parameters_cons with b m1. 
  assert (tyenv!id = Some ty). apply H2. apply in_eq.
  destruct (me_local _ _ _ H3 _ _ _ H)  as [vk [A [B C]]].
  exploit var_kind_by_value; eauto. congruence.
  assumption.
  apply IHbind_parameters with tyenv; auto.
  intros. apply H2. apply in_cons; auto.
Qed.

Lemma tyenv_add_vars_norepet:
  forall vars tyenv,
  list_norepet (var_names vars) ->
  (forall id ty,
   In (id, ty) vars -> (Ctyping.add_vars tyenv vars)!id = Some ty)
  /\
  (forall id,
   ~In id (var_names vars) -> (Ctyping.add_vars tyenv vars)!id = tyenv!id).
Proof.
  induction vars; simpl; intros.
  tauto.
  destruct a as [id1 ty1]. simpl in *. inversion H; clear H; subst.
  destruct (IHvars (add_var tyenv (id1, ty1)) H3) as [A B].
  split; intros.
  destruct H. inversion H; subst id1 ty1; clear H. 
  rewrite B. unfold add_var. simpl. apply PTree.gss. auto.
  auto.
  rewrite B. unfold add_var; simpl. apply PTree.gso. apply sym_not_equal; tauto. tauto.
Qed.

Lemma bind_parameters_match:
  forall e m1 params vals vars m2 tyenv tvars te,
  Csem.bind_parameters e m1 params vals m2 ->
  list_norepet (var_names params ++ var_names vars) ->
  match_env (Ctyping.add_vars tyenv (params ++ vars)) e te ->
  transl_params params = OK tvars ->
  Csharpminor.bind_parameters te m1 tvars vals m2.
Proof.
  intros. 
  eapply bind_parameters_match_rec; eauto.
  assert (list_norepet (var_names (params ++ vars))).
    unfold var_names. rewrite List.map_app. assumption.
  destruct (tyenv_add_vars_norepet _ tyenv H3) as [A B].
  intros. apply A. apply List.in_or_app. auto. 
Qed.

(** The following lemmas establish the matching property
  between the global environments constructed at the beginning
  of program execution. *)

Definition globvarenv 
    (gv: gvarenv)
    (vars: list (ident * globvar var_kind)) :=
  List.fold_left
    (fun gve x => match x with (id, v) => PTree.set id (gvar_info v) gve end)
    vars gv.

Definition type_not_by_value (ty: type) : Prop :=
  match access_mode ty with
  | By_value _ => False
  | _ => True
  end.

Lemma add_global_funs_charact:
  forall fns tyenv,
  (forall id ty, tyenv!id = Some ty -> type_not_by_value ty) ->
  (forall id ty, (add_global_funs tyenv fns)!id = Some ty -> type_not_by_value ty).
Proof.
  induction fns; simpl; intros.
  eauto.
  apply IHfns with (add_global_fun tyenv a) id.
  intros until ty0. destruct a as [id1 fn1]. 
  unfold add_global_fun; simpl. rewrite PTree.gsspec.
  destruct (peq id0 id1). 
  intros. inversion H1. 
  unfold type_of_fundef. destruct fn1; exact I.
  eauto.
  auto.
Qed.

Definition global_fun_typenv :=
  add_global_funs (PTree.empty type) prog.(prog_funct).

Lemma add_global_funs_match_global_env:
  match_globalenv global_fun_typenv (PTree.empty var_kind).
Proof.
  intros; red; intros.
  assert (type_not_by_value ty).
    apply add_global_funs_charact with (prog_funct prog) (PTree.empty type) id.
    intros until ty0. rewrite PTree.gempty. congruence.
    assumption.
  red in H1. rewrite H0 in H1. contradiction.
Qed.

Lemma add_global_var_match_globalenv:
  forall vars tenv gv tvars,
  match_globalenv tenv gv ->
  map_partial AST.prefix_name (transf_globvar transl_globvar) vars = OK tvars ->
  match_globalenv (add_global_vars tenv vars) (globvarenv gv tvars).
Proof.
  induction vars; simpl.
  intros. inversion H0. assumption.
  destruct a as [id v]. intros until tvars; intro.
  caseEq (transf_globvar transl_globvar v); simpl; try congruence. intros vk VK. 
  caseEq (map_partial AST.prefix_name (transf_globvar transl_globvar) vars); simpl; try congruence. intros tvars' EQ1 EQ2.
  inversion EQ2; clear EQ2. simpl. 
  apply IHvars; auto.
  red. intros until chunk. unfold add_global_var. repeat rewrite PTree.gsspec. simpl. 
  destruct (peq id0 id); intros.
  inv H0. monadInv VK. unfold transl_globvar in EQ.  
  generalize (var_kind_by_value _ _ H2). simpl. congruence.
  red in H. eauto. 
Qed.

Lemma match_global_typenv:
  match_globalenv (global_typenv prog) (global_var_env tprog).
Proof.
  change (global_var_env tprog)
    with (globvarenv (PTree.empty var_kind) (prog_vars tprog)).
  unfold global_typenv.
  apply add_global_var_match_globalenv.
  apply add_global_funs_match_global_env. 
  unfold transl_program in TRANSL. monadInv TRANSL. auto.
Qed.

(* ** Correctness of variable accessors *)

(** Correctness of the code generated by [var_get]. *)

Lemma var_get_correct:
  forall e m id ty loc ofs v tyenv code te,
  Csem.eval_lvalue ge e m (Expr (Csyntax.Evar id) ty) loc ofs ->
  load_value_of_type ty m loc ofs = Some v ->
  wt_expr tyenv (Expr (Csyntax.Evar id) ty) ->
  var_get id ty = OK code ->
  match_env tyenv e te ->
  eval_expr tgve te m code v.
Proof.
  intros. inversion H1; subst; clear H1. 
  unfold load_value_of_type in H0.
  unfold var_get in H2. 
  caseEq (access_mode ty).
  (* access mode By_value *)
  intros chunk ACC. rewrite ACC in H0. rewrite ACC in H2. 
  inversion H2; clear H2; subst.
  inversion H; subst; clear H.
    (* local variable *)
    exploit me_local; eauto. intros [vk [A [B C]]].
    assert (vk = Vscalar chunk).
    exploit var_kind_by_value; eauto. congruence.
    subst vk.
    eapply eval_Evar. 
    eapply eval_var_ref_local. eauto. assumption. 
    (* global variable *)
    exploit me_global; eauto. intros [A B].
    eapply eval_Evar. 
    eapply eval_var_ref_global. auto. 
    fold tge. rewrite symbols_preserved. eauto.
    eauto. assumption. 
  (* access mode By_reference *)
  intros ACC. rewrite ACC in H0. rewrite ACC in H2.
  inversion H0; clear H0; subst.
  inversion H2; clear H2; subst.
  inversion H; subst; clear H.
    (* local variable *)
    exploit me_local; eauto. intros [vk [A [B C]]].
    eapply eval_Eaddrof.
    eapply eval_var_addr_local. eauto. 
    (* global variable *)
    exploit me_global; eauto. intros [A B].
    eapply eval_Eaddrof.
    eapply eval_var_addr_global. auto. 
    fold tge. rewrite symbols_preserved. eauto.
  (* access mode By_nothing *)
  intros. rewrite H1 in H0; discriminate.
Qed.

(** Correctness of the code generated by [var_set]. *)

Lemma var_set_correct:
  forall e m id ty loc ofs v m' tyenv code te rhs f k, 
  Csem.eval_lvalue ge e m (Expr (Csyntax.Evar id) ty) loc ofs ->
  store_value_of_type ty m loc ofs v = Some m' ->
  wt_expr tyenv (Expr (Csyntax.Evar id) ty) ->
  var_set id ty rhs = OK code ->
  match_env tyenv e te ->
  eval_expr tgve te m rhs v ->
  step tgve (State f code k te m) E0 (State f Sskip k te m').
Proof.
  intros. inversion H1; subst; clear H1. 
  unfold store_value_of_type in H0.
  unfold var_set in H2. 
  caseEq (access_mode ty).
  (* access mode By_value *)
  intros chunk ACC. rewrite ACC in H0. rewrite ACC in H2. 
  inversion H2; clear H2; subst.
  inversion H; subst; clear H. 
    (* local variable *)
    exploit me_local; eauto. intros [vk [A [B C]]].
    assert (vk = Vscalar chunk).
      exploit var_kind_by_value; eauto. congruence.
    subst vk.
    eapply step_assign. eauto.
    econstructor. eapply eval_var_ref_local. eauto. assumption. 
    (* global variable *)
    exploit me_global; eauto. intros [A B].
    eapply step_assign. eauto.
    econstructor. eapply eval_var_ref_global. auto.
    change (fst tgve) with tge. rewrite symbols_preserved. eauto.
    eauto. assumption. 
  (* access mode By_reference *)
  intros ACC. rewrite ACC in H0. discriminate.
  (* access mode By_nothing *)
  intros. rewrite H1 in H0; discriminate.
Qed.

Lemma call_dest_correct:
  forall e m lhs loc ofs tyenv optid te,
  Csem.eval_lvalue ge e m lhs loc ofs ->
  wt_expr tyenv lhs ->
  transl_lhs_call (Some lhs) = OK optid ->
  match_env tyenv e te ->
  exists id,
     optid = Some id
  /\ tyenv!id = Some (typeof lhs)
  /\ ofs = Int.zero
  /\ match access_mode (typeof lhs) with
     | By_value chunk => eval_var_ref tgve te id loc chunk
     | _ => True
     end.
Proof.
  intros. generalize H1. simpl. caseEq (is_variable lhs); try congruence.
  intros id ISV EQ. inv EQ. 
  exploit is_variable_correct; eauto. intro EQ.
  rewrite EQ in H0. inversion H0. subst id0 ty. 
  exists id. split; auto. split. rewrite EQ in H0. inversion H0. auto.
  rewrite EQ in H. inversion H.
(* local variable *)
  split. auto. 
  subst id0 ty l ofs. exploit me_local; eauto. 
  intros [vk [A [B C]]].
  case_eq (access_mode (typeof lhs)); intros; auto.
  assert (vk = Vscalar m0).
    exploit var_kind_by_value; eauto. congruence.
  subst vk. apply eval_var_ref_local; auto.
(* global variable *)
  split. auto.
  subst id0 ty l ofs. exploit me_global; eauto. intros [A B].
  case_eq (access_mode (typeof lhs)); intros; auto.
  apply eval_var_ref_global; auto.
  simpl. rewrite <- H9. apply symbols_preserved. 
Qed.

Lemma set_call_dest_correct:
  forall ty m loc v m' tyenv e te id,
  store_value_of_type ty m loc Int.zero v = Some m' ->
  match access_mode ty with
  | By_value chunk => eval_var_ref tgve te id loc chunk
  | _ => True
  end ->
  match_env tyenv e te ->
  tyenv!id = Some ty ->
  exec_opt_assign tgve te m (Some id) v m'.
Proof.
  intros. generalize H. unfold store_value_of_type. case_eq (access_mode ty); intros; try congruence.
  rewrite H3 in H0. 
  constructor. econstructor. eauto. auto.
Qed.

(** * Proof of semantic preservation *)

(** ** Semantic preservation for expressions *)

(** The proof of semantic preservation for the translation of expressions
  relies on simulation diagrams of the following form:
<<
         e, m, a ------------------- te, m, ta
            |                           |
            |                           |
            |                           |
            v                           v
         e, m, v ------------------- te, m, v
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

Variable e: Csem.env.
Variable m: mem.
Variable te: Csharpminor.env.
Variable tyenv: typenv.
Hypothesis MENV: match_env tyenv e te.

Definition eval_expr_prop (a: Csyntax.expr) (v: val) : Prop :=
  forall ta
    (WT: wt_expr tyenv a)
    (TR: transl_expr a = OK ta),
  Csharpminor.eval_expr tgve te m ta v.

Definition eval_lvalue_prop (a: Csyntax.expr) (b: block) (ofs: int) : Prop :=
  forall ta
    (WT: wt_expr tyenv a)
    (TR: transl_lvalue a = OK ta),
  Csharpminor.eval_expr tgve te m ta (Vptr b ofs).

Definition eval_exprlist_prop (al: list Csyntax.expr) (vl: list val) : Prop :=
  forall tal
    (WT: wt_exprlist tyenv al)
    (TR: transl_exprlist al = OK tal),
  Csharpminor.eval_exprlist tgve te m tal vl.

(* Check (eval_expr_ind2 ge e m eval_expr_prop eval_lvalue_prop). *)

Lemma transl_Econst_int_correct:
  forall (i : int) (ty : type),
  eval_expr_prop (Expr (Econst_int i) ty) (Vint i).
Proof.
  intros; red; intros.
  monadInv TR. apply make_intconst_correct.
Qed.

Lemma transl_Econst_float_correct:
  forall (f0 : float) (ty : type),
  eval_expr_prop (Expr (Econst_float f0) ty) (Vfloat f0).
Proof.
  intros; red; intros.
  monadInv TR. apply make_floatconst_correct.
Qed.

Lemma transl_Elvalue_correct:
  forall (a : expr_descr) (ty : type) (loc : block) (ofs : int)
         (v : val),
  eval_lvalue ge e m (Expr a ty) loc ofs ->
  eval_lvalue_prop (Expr a ty) loc ofs ->
  load_value_of_type ty m loc ofs = Some v ->
  eval_expr_prop (Expr a ty) v.
Proof.
  intros; red; intros.
  exploit transl_expr_lvalue; eauto. 
  intros [[id [EQ VARGET]] | [tb [TRLVAL MKLOAD]]].
  (* Case a is a variable *)
  subst a. eapply var_get_correct; eauto.
  (* Case a is another lvalue *)
  eapply make_load_correct; eauto. 
Qed.

Lemma transl_Eaddrof_correct:
  forall (a : Csyntax.expr) (ty : type) (loc : block) (ofs : int),
  eval_lvalue ge e m a loc ofs ->
  eval_lvalue_prop a loc ofs ->
  eval_expr_prop (Expr (Csyntax.Eaddrof a) ty) (Vptr loc ofs).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR. 
  eauto.
Qed.

Lemma transl_Esizeof_correct:
  forall ty' ty : type,
  eval_expr_prop (Expr (Esizeof ty') ty)
                 (Vint (Int.repr (Csyntax.sizeof ty'))).
Proof.
  intros; red; intros. monadInv TR. apply make_intconst_correct. 
Qed.

Lemma transl_Eunop_correct:
  forall (op : Csyntax.unary_operation) (a : Csyntax.expr) (ty : type)
         (v1 v : val),
  Csem.eval_expr ge e m a v1 ->
  eval_expr_prop a v1 ->
  sem_unary_operation op v1 (typeof a) = Some v ->
  eval_expr_prop (Expr (Csyntax.Eunop op a) ty) v.
Proof.
  intros; red; intros.
  inversion WT; clear WT; subst.
  monadInv TR. 
  eapply transl_unop_correct; eauto. 
Qed.

Lemma transl_Ebinop_correct:
  forall (op : Csyntax.binary_operation) (a1 a2 : Csyntax.expr)
         (ty : type) (v1 v2 v : val),
  Csem.eval_expr ge e m a1 v1 ->
  eval_expr_prop a1 v1 ->
  Csem.eval_expr ge e m a2 v2 ->
  eval_expr_prop a2 v2 ->
  sem_binary_operation op v1 (typeof a1) v2 (typeof a2) m = Some v ->
  eval_expr_prop (Expr (Csyntax.Ebinop op a1 a2) ty) v.
Proof.
  intros; red; intros.
  inversion WT; clear WT; subst.
  monadInv TR. 
  eapply transl_binop_correct; eauto. 
Qed.

Lemma transl_Econdition_true_correct:
  forall (a1 a2 a3 : Csyntax.expr) (ty : type) (v1 v2 : val),
  Csem.eval_expr ge e m a1 v1 ->
  eval_expr_prop a1 v1 ->
  is_true v1 (typeof a1) ->
  Csem.eval_expr ge e m a2 v2 ->
  eval_expr_prop a2 v2 ->
  eval_expr_prop (Expr (Csyntax.Econdition a1 a2 a3) ty) v2.
Proof.
  intros; red; intros. inv WT. monadInv TR. 
  exploit make_boolean_correct_true. eapply H0; eauto. eauto.
  intros [vb [EVAL ISTRUE]].
  eapply eval_Econdition; eauto. apply Val.bool_of_true_val; eauto.
  simpl. eauto. 
Qed.

Lemma transl_Econdition_false_correct:
  forall (a1 a2 a3 : Csyntax.expr) (ty : type) (v1 v3 : val),
  Csem.eval_expr ge e m a1 v1 ->
  eval_expr_prop a1 v1 ->
  is_false v1 (typeof a1) ->
  Csem.eval_expr ge e m a3 v3 ->
  eval_expr_prop a3 v3 ->
  eval_expr_prop (Expr (Csyntax.Econdition a1 a2 a3) ty) v3.
Proof.
  intros; red; intros. inv WT. monadInv TR. 
  exploit make_boolean_correct_false. eapply H0; eauto. eauto.
  intros [vb [EVAL ISTRUE]].
  eapply eval_Econdition; eauto. apply Val.bool_of_false_val; eauto.
  simpl. eauto. 
Qed.

Lemma transl_Eorbool_1_correct:
  forall (a1 a2 : Csyntax.expr) (ty : type) (v1 : val),
  Csem.eval_expr ge e m a1 v1 ->
  eval_expr_prop a1 v1 ->
  is_true v1 (typeof a1) ->
  eval_expr_prop (Expr (Eorbool a1 a2) ty) Vtrue.
Proof.
  intros; red; intros. inversion WT; clear WT; subst. monadInv TR.
  unfold make_orbool.
  exploit make_boolean_correct_true; eauto. intros [vb [EVAL ISTRUE]].
  eapply eval_Econdition; eauto. apply Val.bool_of_true_val; eauto.
  simpl. unfold Vtrue; apply make_intconst_correct. 
Qed.

Lemma transl_Eorbool_2_correct:
  forall (a1 a2 : Csyntax.expr) (ty : type) (v1 v2 v : val),
  Csem.eval_expr ge e m a1 v1 ->
  eval_expr_prop a1 v1 ->
  is_false v1 (typeof a1) ->
  Csem.eval_expr ge e m a2 v2 ->
  eval_expr_prop a2 v2 ->
  bool_of_val v2 (typeof a2) v ->
  eval_expr_prop (Expr (Eorbool a1 a2) ty) v.
Proof.
  intros; red; intros. inversion WT; clear WT; subst. monadInv TR.
  unfold make_orbool.
  exploit make_boolean_correct_false. eapply H0; eauto. eauto. intros [vb [EVAL ISFALSE]].
  eapply eval_Econdition; eauto. apply Val.bool_of_false_val; eauto.
  simpl. inversion H4; subst.
  exploit make_boolean_correct_true. eapply H3; eauto. eauto. intros [vc [EVAL' ISTRUE']].
  eapply eval_Econdition; eauto. apply Val.bool_of_true_val; eauto. 
  unfold Vtrue; apply make_intconst_correct.
  exploit make_boolean_correct_false. eapply H3; eauto. eauto. intros [vc [EVAL' ISFALSE']].
  eapply eval_Econdition; eauto. apply Val.bool_of_false_val; eauto. 
  unfold Vfalse; apply make_intconst_correct. 
Qed.

Lemma transl_Eandbool_1_correct:
  forall (a1 a2 : Csyntax.expr) (ty : type) (v1 : val),
  Csem.eval_expr ge e m a1 v1 ->
  eval_expr_prop a1 v1 ->
  is_false v1 (typeof a1) ->
  eval_expr_prop (Expr (Eandbool a1 a2) ty) Vfalse.
Proof.
  intros; red; intros. inversion WT; clear WT; subst. monadInv TR.
  unfold make_andbool.
  exploit make_boolean_correct_false; eauto. intros [vb [EVAL ISFALSE]].
  eapply eval_Econdition; eauto. apply Val.bool_of_false_val; eauto. 
  unfold Vfalse; apply make_intconst_correct. 
Qed.

Lemma transl_Eandbool_2_correct:
  forall (a1 a2 : Csyntax.expr) (ty : type) (v1 v2 v : val),
  Csem.eval_expr ge e m a1 v1 ->
  eval_expr_prop a1 v1 ->
  is_true v1 (typeof a1) ->
  Csem.eval_expr ge e m a2 v2 ->
  eval_expr_prop a2 v2 ->
  bool_of_val v2 (typeof a2) v ->
  eval_expr_prop (Expr (Eandbool a1 a2) ty) v.
Proof.
  intros; red; intros. inversion WT; clear WT; subst. monadInv TR.
  unfold make_andbool.
  exploit make_boolean_correct_true. eapply H0; eauto. eauto. intros [vb [EVAL ISTRUE]].
  eapply eval_Econdition; eauto. apply Val.bool_of_true_val; eauto. 
  simpl. inversion H4; subst.
  exploit make_boolean_correct_true. eapply H3; eauto. eauto. intros [vc [EVAL' ISTRUE']].
  eapply eval_Econdition; eauto. apply Val.bool_of_true_val; eauto.
  unfold Vtrue; apply make_intconst_correct.
  exploit make_boolean_correct_false. eapply H3; eauto. eauto. intros [vc [EVAL' ISFALSE']].
  eapply eval_Econdition; eauto. apply Val.bool_of_false_val; eauto.
  unfold Vfalse; apply make_intconst_correct.
Qed.

Lemma transl_Ecast_correct:
  forall (a : Csyntax.expr) (ty ty': type) (v1 v : val),
  Csem.eval_expr ge e m a v1 ->
  eval_expr_prop a v1 ->
  cast v1 (typeof a) ty v -> eval_expr_prop (Expr (Ecast ty a) ty') v.
Proof.
  intros; red; intros. inversion WT; clear WT; subst. monadInv TR.
  eapply make_cast_correct; eauto.
Qed.

Lemma transl_Evar_local_correct:
  forall (id : ident) (l : block) (ty : type),
  e ! id = Some(l, ty) ->
  eval_lvalue_prop (Expr (Csyntax.Evar id) ty) l Int.zero.
Proof.
  intros; red; intros. inversion WT; clear WT; subst. monadInv TR.
  exploit (me_local _ _ _ MENV); eauto.
  intros [vk [A [B C]]].
  econstructor. eapply eval_var_addr_local. eauto. 
Qed.

Lemma transl_Evar_global_correct:
  forall (id : ident) (l : block) (ty : type),
  e ! id = None ->
  Genv.find_symbol ge id = Some l ->
  eval_lvalue_prop (Expr (Csyntax.Evar id) ty) l Int.zero.
Proof.
  intros; red; intros. inversion WT; clear WT; subst. monadInv TR. 
  exploit (me_global _ _ _ MENV); eauto. intros [A B].
  econstructor. eapply eval_var_addr_global. eauto. 
  rewrite symbols_preserved. auto.
Qed.

Lemma transl_Ederef_correct:
  forall (a : Csyntax.expr) (ty : type) (l : block) (ofs : int),
  Csem.eval_expr ge e m a (Vptr l ofs) ->
  eval_expr_prop a (Vptr l ofs) ->
  eval_lvalue_prop (Expr (Ederef a) ty) l ofs.
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR. 
  eauto.
Qed.

Lemma transl_Efield_struct_correct:
  forall (a : Csyntax.expr) (i : ident) (ty : type) (l : block)
         (ofs : int) (id : ident) (fList : fieldlist) (delta : Z),
  eval_lvalue ge e m a l ofs ->
  eval_lvalue_prop a l ofs ->
  typeof a = Tstruct id fList ->
  field_offset i fList = OK delta ->
  eval_lvalue_prop (Expr (Efield a i) ty) l (Int.add ofs (Int.repr delta)).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. 
  simpl in TR. rewrite H1 in TR. monadInv TR.
  eapply eval_Ebinop; eauto.
  apply make_intconst_correct. 
  simpl. congruence.
Qed.

Lemma transl_Efield_union_correct:
  forall (a : Csyntax.expr) (i : ident) (ty : type) (l : block)
         (ofs : int) (id : ident) (fList : fieldlist),
  eval_lvalue ge e m a l ofs ->
  eval_lvalue_prop a l ofs ->
  typeof a = Tunion id fList ->
  eval_lvalue_prop (Expr (Efield a i) ty) l ofs.
Proof.
  intros; red; intros. inversion WT; clear WT; subst. 
  simpl in TR. rewrite H1 in TR. eauto.
Qed.

Lemma transl_expr_correct:
  forall a v,
  Csem.eval_expr ge e m a v ->
  eval_expr_prop a v.
Proof
  (eval_expr_ind2 ge e m eval_expr_prop eval_lvalue_prop
         transl_Econst_int_correct
         transl_Econst_float_correct
         transl_Elvalue_correct
         transl_Eaddrof_correct
         transl_Esizeof_correct
         transl_Eunop_correct
         transl_Ebinop_correct
         transl_Econdition_true_correct
         transl_Econdition_false_correct
         transl_Eorbool_1_correct
         transl_Eorbool_2_correct
         transl_Eandbool_1_correct
         transl_Eandbool_2_correct
         transl_Ecast_correct
         transl_Evar_local_correct
         transl_Evar_global_correct
         transl_Ederef_correct
         transl_Efield_struct_correct
         transl_Efield_union_correct).

Lemma transl_lvalue_correct:
  forall a blk ofs,
  Csem.eval_lvalue ge e m a blk ofs ->
  eval_lvalue_prop a blk ofs.
Proof
  (eval_lvalue_ind2 ge e m eval_expr_prop eval_lvalue_prop
         transl_Econst_int_correct
         transl_Econst_float_correct
         transl_Elvalue_correct
         transl_Eaddrof_correct
         transl_Esizeof_correct
         transl_Eunop_correct
         transl_Ebinop_correct
         transl_Econdition_true_correct
         transl_Econdition_false_correct
         transl_Eorbool_1_correct
         transl_Eorbool_2_correct
         transl_Eandbool_1_correct
         transl_Eandbool_2_correct
         transl_Ecast_correct
         transl_Evar_local_correct
         transl_Evar_global_correct
         transl_Ederef_correct
         transl_Efield_struct_correct
         transl_Efield_union_correct).

Lemma transl_exprlist_correct:
  forall al vl,
  Csem.eval_exprlist ge e m al vl ->
  eval_exprlist_prop al vl.
Proof.
  induction 1; red; intros; monadInv TR; inv WT.
  constructor.
  constructor. eapply (transl_expr_correct _ _ H); eauto. eauto.
Qed.

End EXPR.

Lemma exit_if_false_true:
  forall a ts e m v tyenv te f tk,
  exit_if_false a = OK ts ->
  Csem.eval_expr ge e m a v ->
  is_true v (typeof a) ->
  match_env tyenv e te ->
  wt_expr tyenv a ->
  step tgve (State f ts tk te m) E0 (State f Sskip tk te m).
Proof.
  intros. monadInv H.
  exploit make_boolean_correct_true.
    eapply (transl_expr_correct _ _ _ _ H2 _ _ H0); eauto.
    eauto.
  intros [vb [EVAL ISTRUE]].
  change Sskip with (if true then Sskip else Sexit 0).
  eapply step_ifthenelse; eauto. 
  apply Val.bool_of_true_val; eauto.  
Qed.
 
Lemma exit_if_false_false:
  forall a ts e m v tyenv te f tk,
  exit_if_false a = OK ts ->
  Csem.eval_expr ge e m a v ->
  is_false v (typeof a) ->
  match_env tyenv e te ->
  wt_expr tyenv a ->
  step tgve (State f ts tk te m) E0 (State f (Sexit 0) tk te m).
Proof.
  intros. monadInv H.
  exploit make_boolean_correct_false.
    eapply (transl_expr_correct _ _ _ _ H2 _ _ H0); eauto.
    eauto.
  intros [vb [EVAL ISFALSE]].
  change (Sexit 0) with (if false then Sskip else Sexit 0).
  eapply step_ifthenelse; eauto. 
  apply Val.bool_of_false_val; eauto. 
Qed.

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

Definition typenv_fun (f: Csyntax.function) :=
  add_vars (global_typenv prog) (f.(Csyntax.fn_params) ++ f.(Csyntax.fn_vars)).

Inductive match_transl: stmt -> cont -> stmt -> cont -> Prop :=
  | match_transl_0: forall ts tk,
      match_transl ts tk ts tk
  | match_transl_1: forall ts tk,
      match_transl (Sblock ts) tk ts (Kblock tk).

Lemma match_transl_step:
  forall ts tk ts' tk' f te m,
  match_transl (Sblock ts) tk ts' tk' ->
  star step tgve (State f ts' tk' te m) E0 (State f ts (Kblock tk) te m).
Proof.
  intros. inv H. 
  apply star_one. constructor. 
  apply star_refl.
Qed.

Inductive match_cont: typenv -> nat -> nat -> Csem.cont -> Csharpminor.cont -> Prop :=
  | match_Kstop: forall tyenv nbrk ncnt,
      match_cont tyenv nbrk ncnt Csem.Kstop Kstop
  | match_Kseq: forall tyenv nbrk ncnt s k ts tk,
      transl_statement nbrk ncnt s = OK ts ->
      wt_stmt tyenv s ->
      match_cont tyenv nbrk ncnt k tk ->
      match_cont tyenv nbrk ncnt
                 (Csem.Kseq s k)
                 (Kseq ts tk)
  | match_Kwhile: forall tyenv nbrk ncnt a s k ta ts tk,
      exit_if_false a = OK ta ->
      transl_statement 1%nat 0%nat s = OK ts ->
      wt_expr tyenv a ->
      wt_stmt tyenv s ->
      match_cont tyenv nbrk ncnt k tk ->
      match_cont tyenv 1%nat 0%nat
                 (Csem.Kwhile a s k) 
                 (Kblock (Kseq (Sloop (Sseq ta (Sblock ts))) (Kblock tk)))
  | match_Kdowhile: forall tyenv nbrk ncnt a s k ta ts tk,
      exit_if_false a = OK ta ->
      transl_statement 1%nat 0%nat s = OK ts ->
      wt_expr tyenv a ->
      wt_stmt tyenv s ->
      match_cont tyenv nbrk ncnt k tk ->
      match_cont tyenv 1%nat 0%nat
                 (Csem.Kdowhile a s k) 
                 (Kblock (Kseq ta (Kseq (Sloop (Sseq (Sblock ts) ta)) (Kblock tk))))
  | match_Kfor2: forall tyenv nbrk ncnt a2 a3 s k ta2 ta3 ts tk,
      exit_if_false a2 = OK ta2 ->
      transl_statement nbrk ncnt a3 = OK ta3 ->
      transl_statement 1%nat 0%nat s = OK ts ->
      wt_expr tyenv a2 -> wt_stmt tyenv a3 -> wt_stmt tyenv s ->
      match_cont tyenv nbrk ncnt k tk ->
      match_cont tyenv 1%nat 0%nat
                 (Csem.Kfor2 a2 a3 s k)
                 (Kblock (Kseq ta3 (Kseq (Sloop (Sseq ta2 (Sseq (Sblock ts) ta3))) (Kblock tk))))
  | match_Kfor3: forall tyenv nbrk ncnt a2 a3 s k ta2 ta3 ts tk,
      exit_if_false a2 = OK ta2 ->
      transl_statement nbrk ncnt a3 = OK ta3 ->
      transl_statement 1%nat 0%nat s = OK ts ->
      wt_expr tyenv a2 -> wt_stmt tyenv a3 -> wt_stmt tyenv s ->
      match_cont tyenv nbrk ncnt k tk ->
      match_cont tyenv nbrk ncnt
                 (Csem.Kfor3 a2 a3 s k)
                 (Kseq (Sloop (Sseq ta2 (Sseq (Sblock ts) ta3))) (Kblock tk))
  | match_Kswitch: forall tyenv nbrk ncnt k tk,
      match_cont tyenv nbrk ncnt k tk ->
      match_cont tyenv 0%nat (S ncnt)
                 (Csem.Kswitch k)
                 (Kblock tk)
  | match_Kcall_none: forall tyenv nbrk ncnt nbrk' ncnt' f e k tf te tk,
      transl_function f = OK tf ->
      wt_stmt (typenv_fun f) f.(Csyntax.fn_body) ->
      match_env (typenv_fun f) e te ->
      match_cont (typenv_fun f) nbrk' ncnt' k tk ->
      match_cont tyenv nbrk ncnt
                 (Csem.Kcall None f e k)
                 (Kcall None tf te tk)
  | match_Kcall_some: forall tyenv nbrk ncnt nbrk' ncnt' loc ofs ty f e k id tf te tk,
      transl_function f = OK tf ->
      wt_stmt (typenv_fun f) f.(Csyntax.fn_body) ->
      match_env (typenv_fun f) e te ->
      ofs = Int.zero ->
      (typenv_fun f)!id = Some ty ->
      match access_mode ty with
      | By_value chunk => eval_var_ref tgve te id loc chunk
      | _ => True
      end ->
      match_cont (typenv_fun f) nbrk' ncnt' k tk ->
      match_cont tyenv nbrk ncnt 
                 (Csem.Kcall (Some(loc, ofs, ty)) f e k)
                 (Kcall (Some id) tf te tk).

Inductive match_states: Csem.state -> Csharpminor.state -> Prop :=
  | match_state:
      forall f nbrk ncnt s k e m tf ts tk te ts' tk'
          (TRF: transl_function f = OK tf)
          (TR: transl_statement nbrk ncnt s = OK ts)
          (MTR: match_transl ts tk ts' tk')
          (WTF: wt_stmt (typenv_fun f) f.(Csyntax.fn_body))
          (WT: wt_stmt (typenv_fun f) s)
          (MENV: match_env (typenv_fun f) e te)
          (MK: match_cont (typenv_fun f) nbrk ncnt k tk),
      match_states (Csem.State f s k e m)
                   (State tf ts' tk' te m)
  | match_callstate:
      forall fd args k m tfd tk
          (TR: transl_fundef fd = OK tfd)
          (WT: wt_fundef (global_typenv prog) fd)
          (MK: match_cont (global_typenv prog) 0%nat 0%nat k tk)
          (ISCC: Csem.is_call_cont k),
      match_states (Csem.Callstate fd args k m)
                   (Callstate tfd args tk m)
  | match_returnstate:
      forall res k m tk 
          (MK: match_cont (global_typenv prog) 0%nat 0%nat k tk),
      match_states (Csem.Returnstate res k m)
                   (Returnstate res tk m).

Remark match_states_skip:
  forall f e te nbrk ncnt k tf tk m,
  transl_function f = OK tf ->
  wt_stmt (typenv_fun f) f.(Csyntax.fn_body) ->
  match_env (typenv_fun f) e te ->
  match_cont (typenv_fun f) nbrk ncnt k tk ->
  match_states (Csem.State f Csyntax.Sskip k e m) (State tf Sskip tk te m).
Proof.
  intros. econstructor; eauto. simpl; reflexivity. constructor. constructor.
Qed.

(** Commutation between label resolution and compilation *)

Section FIND_LABEL.
Variable lbl: label.
Variable tyenv: typenv.

Remark exit_if_false_no_label:
  forall a s, exit_if_false a = OK s -> forall k, find_label lbl s k = None.
Proof.
  intros. unfold exit_if_false in H. monadInv H. simpl. auto.
Qed.
  
Lemma transl_find_label:
  forall s nbrk ncnt k ts tk
  (WT: wt_stmt tyenv s)
  (TR: transl_statement nbrk ncnt s = OK ts)
  (MC: match_cont tyenv nbrk ncnt k tk),
  match Csem.find_label lbl s k with
  | None => find_label lbl ts tk = None
  | Some (s', k') =>
      exists ts', exists tk', exists nbrk', exists ncnt',
      find_label lbl ts tk = Some (ts', tk')
      /\ transl_statement nbrk' ncnt' s' = OK ts'
      /\ match_cont tyenv nbrk' ncnt' k' tk'
      /\ wt_stmt tyenv s'
  end

with transl_find_label_ls:
  forall ls nbrk ncnt k tls tk
  (WT: wt_lblstmts tyenv ls)
  (TR: transl_lbl_stmt nbrk ncnt ls = OK tls)
  (MC: match_cont tyenv nbrk ncnt k tk),
  match Csem.find_label_ls lbl ls k with
  | None => find_label_ls lbl tls tk = None
  | Some (s', k') =>
      exists ts', exists tk', exists nbrk', exists ncnt',
      find_label_ls lbl tls tk = Some (ts', tk')
      /\ transl_statement nbrk' ncnt' s' = OK ts'
      /\ match_cont tyenv nbrk' ncnt' k' tk'
      /\ wt_stmt tyenv s'
  end.

Proof.
  intro s; case s; intros; inv WT; try (monadInv TR); simpl.
(* skip *)
  auto.
(* assign *)
  simpl in TR. destruct (is_variable e); monadInv TR.
  unfold var_set in EQ0. destruct (access_mode (typeof e)); inv EQ0. auto.
  unfold make_store in EQ2. destruct (access_mode (typeof e)); inv EQ2. auto.
(* call *)
  simpl in TR. destruct (classify_fun (typeof e)); monadInv TR. auto.
(* seq *)
  exploit (transl_find_label s0 nbrk ncnt (Csem.Kseq s1 k)); eauto. constructor; eauto. 
  destruct (Csem.find_label lbl s0 (Csem.Kseq s1 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B [C D]]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H. eapply transl_find_label; eauto.
(* ifthenelse *)
  exploit (transl_find_label s0); eauto. 
  destruct (Csem.find_label lbl s0 k) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B [C D]]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H. eapply transl_find_label; eauto.
(* while *)
  rewrite (exit_if_false_no_label _ _ EQ).
  eapply transl_find_label; eauto. econstructor; eauto.
(* dowhile *)
  exploit (transl_find_label s0 1%nat 0%nat (Csem.Kdowhile e s0 k)); eauto. econstructor; eauto.
  destruct (Csem.find_label lbl s0 (Kdowhile e s0 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B [C D]]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H. eapply exit_if_false_no_label; eauto.
(* for *)
  simpl in TR. destruct (is_Sskip s0); monadInv TR. 
  simpl. rewrite (exit_if_false_no_label _ _ EQ). 
  exploit (transl_find_label s2 1%nat 0%nat (Kfor2 e s1 s2 k)); eauto. econstructor; eauto.
  destruct (Csem.find_label lbl s2 (Kfor2 e s1 s2 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B [C D]]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H.
  eapply transl_find_label; eauto. econstructor; eauto.
  exploit (transl_find_label s0 nbrk ncnt (Csem.Kseq (Sfor Csyntax.Sskip e s1 s2) k)); eauto.
  econstructor; eauto. simpl. rewrite is_Sskip_true. rewrite EQ1; simpl. rewrite EQ0; simpl. rewrite EQ2; simpl. reflexivity.
  constructor; auto. constructor. 
  simpl. rewrite (exit_if_false_no_label _ _ EQ1). 
  destruct (Csem.find_label lbl s0 (Csem.Kseq (Sfor Csyntax.Sskip e s1 s2) k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B [C D]]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H. 
  exploit (transl_find_label s2 1%nat 0%nat (Kfor2 e s1 s2 k)); eauto. econstructor; eauto.
  destruct (Csem.find_label lbl s2 (Kfor2 e s1 s2 k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B [C D]]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H0.
  eapply transl_find_label; eauto. econstructor; eauto.
(* break *)
  auto.
(* continue *)
  auto.
(* return *)
  simpl in TR. destruct o; monadInv TR. auto. auto. 
(* switch *)
  eapply transl_find_label_ls with (k := Csem.Kswitch k); eauto. econstructor; eauto. 
(* label *)
  destruct (ident_eq lbl l). 
  exists x; exists tk; exists nbrk; exists ncnt; auto.
  eapply transl_find_label; eauto.
(* goto *)
  auto.

  intro ls; case ls; intros; inv WT; monadInv TR; simpl.
(* default *)
  eapply transl_find_label; eauto.
(* case *)
  exploit (transl_find_label s nbrk ncnt (Csem.Kseq (seq_of_labeled_statement l) k)); eauto. 
  econstructor; eauto. apply transl_lbl_stmt_2; eauto.
  apply wt_seq_of_labeled_statement; auto.
  destruct (Csem.find_label lbl s (Csem.Kseq (seq_of_labeled_statement l) k)) as [[s' k'] | ].
  intros [ts' [tk' [nbrk' [ncnt' [A [B [C D]]]]]]].
  rewrite A. exists ts'; exists tk'; exists nbrk'; exists ncnt'; auto.
  intro. rewrite H.
  eapply transl_find_label_ls; eauto.
Qed.

End FIND_LABEL.

(** Properties of call continuations *)

Lemma match_cont_call_cont:
  forall nbrk' ncnt' tyenv' tyenv nbrk ncnt k tk,
  match_cont tyenv nbrk ncnt k tk ->
  match_cont tyenv' nbrk' ncnt' (Csem.call_cont k) (call_cont tk).
Proof.
  induction 1; simpl; auto.
  constructor.
  econstructor; eauto. 
  econstructor; eauto.
Qed.

Lemma match_cont_is_call_cont:
  forall typenv nbrk ncnt k tk typenv' nbrk' ncnt',
  match_cont typenv nbrk ncnt k tk ->
  Csem.is_call_cont k ->
  match_cont typenv' nbrk' ncnt' k tk /\ is_call_cont tk.
Proof.
  intros. inv H; simpl in H0; try contradiction; simpl; intuition.
  constructor. 
  econstructor; eauto. 
  econstructor; eauto.
Qed.

(** The simulation proof *)

Lemma transl_step:
  forall S1 t S2, Csem.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
  exists T2, plus step tgve T1 t T2 /\ match_states S2 T2.
Proof.
  induction 1; intros T1 MST; inv MST.

(* assign *)
  simpl in TR. inv WT. 
  case_eq (is_variable a1); intros. 
  rewrite H2 in TR. monadInv TR. 
  exploit is_variable_correct; eauto. intro EQ1. rewrite EQ1 in H.
  assert (ts' = ts /\ tk' = tk).
    inversion MTR. auto. 
    subst ts. unfold var_set in EQ0. destruct (access_mode (typeof a1)); congruence.
  destruct H3; subst ts' tk'.
  econstructor; split.
  apply plus_one. eapply var_set_correct; eauto. congruence. 
  exploit transl_expr_correct; eauto.
  eapply match_states_skip; eauto.

  rewrite H2 in TR. monadInv TR. 
  assert (ts' = ts /\ tk' = tk).
    inversion MTR. auto. 
    subst ts. unfold make_store in EQ2. destruct (access_mode (typeof a1)); congruence.
  destruct H3; subst ts' tk'.
  econstructor; split.
  apply plus_one. eapply make_store_correct; eauto.
  exploit transl_lvalue_correct; eauto.
  exploit transl_expr_correct; eauto.
  eapply match_states_skip; eauto.

(* call none *)
  generalize TR. simpl. case_eq (classify_fun (typeof a)); try congruence.
  intros targs tres CF TR'. monadInv TR'. inv MTR. inv WT.
  exploit functions_translated; eauto. intros [tfd [FIND TFD]].
  econstructor; split.
  apply plus_one. econstructor; eauto. 
  exploit transl_expr_correct; eauto.
  exploit transl_exprlist_correct; eauto.
  eapply transl_fundef_sig1; eauto. eapply functions_well_typed; eauto.
  congruence.
  econstructor; eauto. eapply functions_well_typed; eauto. 
  econstructor; eauto. simpl. auto. 

(* call some *)
  generalize TR. simpl. case_eq (classify_fun (typeof a)); try congruence.
  intros targs tres CF TR'. monadInv TR'. inv MTR. inv WT.
  exploit functions_translated; eauto. intros [tfd [FIND TFD]].
  inv H7. exploit call_dest_correct; eauto.
  intros [id [A [B [C D]]]]. subst x ofs. 
  econstructor; split.
  apply plus_one. econstructor; eauto. 
  exploit transl_expr_correct; eauto.
  exploit transl_exprlist_correct; eauto.
  eapply transl_fundef_sig1; eauto. eapply functions_well_typed; eauto.
  congruence.
  econstructor; eauto. eapply functions_well_typed; eauto.
  econstructor; eauto. simpl; auto. 

(* seq *)
  monadInv TR. inv WT. inv MTR.
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

(* ifthenelse true *)
  monadInv TR. inv MTR. inv WT.
  exploit make_boolean_correct_true; eauto. 
  exploit transl_expr_correct; eauto.
  intros [v [A B]].
  econstructor; split.
  apply plus_one. apply step_ifthenelse with (v := v) (b := true). 
  auto. apply Val.bool_of_true_val. auto.
  econstructor; eauto. constructor.

(* ifthenelse false *)
  monadInv TR. inv MTR. inv WT.
  exploit make_boolean_correct_false; eauto. 
  exploit transl_expr_correct; eauto.
  intros [v [A B]].
  econstructor; split.
  apply plus_one. apply step_ifthenelse with (v := v) (b := false). 
  auto. apply Val.bool_of_false_val. auto.
  econstructor; eauto. constructor.

(* while false *)
  monadInv TR. inv WT.
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto. 
  eapply plus_left. constructor. 
  eapply star_left. constructor.
  eapply star_left. eapply exit_if_false_false; eauto.
  eapply star_left. constructor. 
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. traceEq.
  eapply match_states_skip; eauto.

(* while true *)
  monadInv TR. inv WT.
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto. 
  eapply plus_left. constructor.
  eapply star_left. constructor.
  eapply star_left. eapply exit_if_false_true; eauto.
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. reflexivity. reflexivity. traceEq.
  econstructor; eauto. constructor. 
  econstructor; eauto.

(* skip or continue while *)
  assert ((ts' = Sskip \/ ts' = Sexit ncnt) /\ tk' = tk).
    destruct H; subst x; monadInv TR; inv MTR; auto.
  destruct H0. inv MK.
  econstructor; split.
  eapply plus_left.
  destruct H0; subst ts'; constructor. 
  apply star_one. constructor. traceEq.
  econstructor; eauto.
  simpl. rewrite H5; simpl. rewrite H6; simpl. reflexivity.
  constructor. constructor; auto.

(* break while *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  eapply plus_left. constructor.
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. traceEq.
  eapply match_states_skip; eauto.

(* dowhile *)
  monadInv TR. inv WT.
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto. 
  eapply plus_left. constructor.
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. traceEq.
  econstructor; eauto. constructor.
  econstructor; eauto.

(* skip or continue dowhile false *)
  assert ((ts' = Sskip \/ ts' = Sexit ncnt) /\ tk' = tk).
    destruct H; subst x; monadInv TR; inv MTR; auto.
  destruct H2. inv MK.
  econstructor; split.
  eapply plus_left. destruct H2; subst ts'; constructor.
  eapply star_left. constructor.
  eapply star_left. eapply exit_if_false_false; eauto.
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. reflexivity. traceEq.
  eapply match_states_skip; eauto.

(* skip or continue dowhile true *)
  assert ((ts' = Sskip \/ ts' = Sexit ncnt) /\ tk' = tk).
    destruct H; subst x; monadInv TR; inv MTR; auto.
  destruct H2. inv MK.
  econstructor; split.
  eapply plus_left. destruct H2; subst ts'; constructor.
  eapply star_left. constructor.
  eapply star_left. eapply exit_if_false_true; eauto.
  apply star_one. constructor.
  reflexivity. reflexivity. traceEq.
  econstructor; eauto.
  simpl. rewrite H7; simpl. rewrite H8; simpl. reflexivity. constructor.
  constructor; auto.

(* break dowhile *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  eapply plus_left. constructor.
  eapply star_left. constructor.
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. traceEq.
  eapply match_states_skip; eauto.

(* for start *)
  simpl in TR. rewrite is_Sskip_false in TR; auto. monadInv TR. inv MTR. inv WT.
  econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto. constructor.
  constructor; auto. simpl. rewrite is_Sskip_true. rewrite EQ1; simpl. rewrite EQ0; simpl. rewrite EQ2; auto. 
  constructor; auto. constructor.

(* for false *)
  simpl in TR. rewrite is_Sskip_true in TR. monadInv TR. inv WT.
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto.
  eapply plus_left. constructor.
  eapply star_left. constructor.
  eapply star_left. eapply exit_if_false_false; eauto.
  eapply star_left. constructor. 
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity.
  eapply match_states_skip; eauto.

(* for true *)
  simpl in TR. rewrite is_Sskip_true in TR. monadInv TR. inv WT. 
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto.
  eapply plus_left. constructor.
  eapply star_left. constructor.
  eapply star_left. eapply exit_if_false_true; eauto.
  eapply star_left. constructor. 
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. reflexivity. reflexivity. reflexivity. reflexivity.
  econstructor; eauto. constructor.
  econstructor; eauto. 

(* skip or continue for2 *)
  assert ((ts' = Sskip \/ ts' = Sexit ncnt) /\ tk' = tk).
    destruct H; subst x; monadInv TR; inv MTR; auto.
  destruct H0. inv MK.
  econstructor; split.
  eapply plus_left. destruct H0; subst ts'; constructor.
  apply star_one. constructor. reflexivity. 
  econstructor; eauto. constructor. 
  constructor; auto. 

(* break for2 *) 
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  eapply plus_left. constructor.
  eapply star_left. constructor.
  eapply star_left. constructor.
  apply star_one. constructor.
  reflexivity. reflexivity. traceEq.
  eapply match_states_skip; eauto.

(* skip for3 *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto.
  simpl. rewrite is_Sskip_true. rewrite H3; simpl. rewrite H4; simpl. rewrite H5; simpl. reflexivity.
  constructor. constructor; auto. 

(* return none *)
  monadInv TR. inv MTR. 
  econstructor; split.
  apply plus_one. constructor. monadInv TRF. simpl. rewrite H. auto.
  eapply match_env_free_blocks; eauto. 
  econstructor; eauto.
  eapply match_cont_call_cont. eauto. 

(* return some *)
  monadInv TR. inv MTR. inv WT. inv H3. 
  econstructor; split.
  apply plus_one. constructor. monadInv TRF. simpl.
  unfold opttyp_of_type. destruct (Csyntax.fn_return f); congruence.
  exploit transl_expr_correct; eauto.
  eapply match_env_free_blocks; eauto.
  econstructor; eauto.
  eapply match_cont_call_cont. eauto. 

(* skip call *)
  monadInv TR. inv MTR.
  exploit match_cont_is_call_cont; eauto. intros [A B].
  econstructor; split.
  apply plus_one. apply step_skip_call. auto.
  monadInv TRF. simpl. rewrite H0. auto.
  eapply match_env_free_blocks; eauto.
  constructor. eauto.

(* switch *)
  monadInv TR. inv WT.
  exploit transl_expr_correct; eauto. intro EV.
  econstructor; split.
  eapply star_plus_trans. eapply match_transl_step; eauto.
  apply plus_one. econstructor. eauto. traceEq. 
  econstructor; eauto.
  apply transl_lbl_stmt_2. apply transl_lbl_stmt_1. eauto. 
  constructor.
  apply wt_seq_of_labeled_statement. apply wt_select_switch. auto.
  econstructor. eauto.

(* skip or break switch *)
  assert ((ts' = Sskip \/ ts' = Sexit nbrk) /\ tk' = tk).
    destruct H; subst x; monadInv TR; inv MTR; auto.
  destruct H0. inv MK.
  econstructor; split.
  apply plus_one. destruct H0; subst ts'; constructor.
  eapply match_states_skip; eauto.


(* continue switch *)
  monadInv TR. inv MTR. inv MK.
  econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto. simpl. reflexivity. constructor.

(* label *)
  monadInv TR. inv WT. inv MTR. 
  econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto. constructor.

(* goto *)
  monadInv TR. inv MTR.
  generalize TRF. unfold transl_function. intro TRF'. monadInv TRF'.
  exploit (transl_find_label lbl). eexact WTF. eexact EQ0. eapply match_cont_call_cont. eauto.
  rewrite H. 
  intros [ts' [tk'' [nbrk' [ncnt' [A [B [C D]]]]]]].
  econstructor; split.
  apply plus_one. constructor. simpl. eexact A. 
  econstructor; eauto. constructor.

(* internal function *)
  monadInv TR. inv WT. inv H3. monadInv EQ.
  exploit match_cont_is_call_cont; eauto. intros [A B].
  exploit match_env_alloc_variables; eauto. 
  apply match_globalenv_match_env_empty. apply match_global_typenv. 
  apply transl_fn_variables. eauto. eauto. 
  intros [te1 [C D]].
  econstructor; split.
  apply plus_one. econstructor.
  eapply transl_names_norepet; eauto. 
  eexact C. eapply bind_parameters_match; eauto. 
  econstructor; eauto.
  unfold transl_function. rewrite EQ0; simpl. rewrite EQ; simpl. rewrite EQ1; auto. 
  constructor.

(* external function *)
  monadInv TR. 
  exploit match_cont_is_call_cont; eauto. intros [A B].
  econstructor; split.
  apply plus_one. constructor. eauto. 
  eapply external_call_symbols_preserved_2; eauto.
  exact symbols_preserved.
  eexact (Genv.find_var_info_transf_partial2 transl_fundef transl_globvar _ TRANSL).
  eexact (Genv.find_var_info_rev_transf_partial2 transl_fundef transl_globvar _ TRANSL).
  econstructor; eauto.

(* returnstate 0 *)
  inv MK. 
  econstructor; split.
  apply plus_one. constructor. constructor. 
  econstructor; eauto. simpl; reflexivity. constructor. constructor.

(* returnstate 1 *)
  inv MK.
  econstructor; split.
  apply plus_one. constructor. eapply set_call_dest_correct; eauto. 
  econstructor; eauto. simpl; reflexivity. constructor. constructor.
Qed.

Lemma transl_initial_states:
  forall S t S', Csem.initial_state prog S -> Csem.step ge S t S' ->
  exists R, initial_state tprog R /\ match_states S R.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  assert (C: Genv.find_symbol tge (prog_main tprog) = Some b).
    rewrite symbols_preserved. replace (prog_main tprog) with (prog_main prog).
    exact H2. symmetry. unfold transl_program in TRANSL. 
    eapply transform_partial_program2_main; eauto.
  exploit function_ptr_well_typed. eauto. intro WTF.
  assert (exists targs, type_of_fundef f = Tfunction targs (Tint I32 Signed)).
    eapply wt_program_main. eauto. 
    eapply Genv.find_funct_ptr_symbol_inversion; eauto.
  destruct H as [targs D].
  assert (targs = Tnil). 
    inv H0.
    (* internal function *)
    inv H10. simpl in D. unfold type_of_function in D. rewrite <- H5 in D. 
    simpl in D. congruence.
    (* external function *)
    simpl in D. inv D.
    exploit external_call_arity; eauto. intro ARITY.
    exploit function_ptr_well_typed; eauto. intro WT. inv WT.
    rewrite H5 in ARITY. destruct targs; simpl in ARITY; congruence.
  subst targs. 
  assert (funsig tf = signature_of_type Tnil (Tint I32 Signed)).
    eapply transl_fundef_sig2; eauto. 
  econstructor; split.
  econstructor; eauto. eapply Genv.init_mem_transf_partial2; eauto. 
  constructor; auto. constructor. exact I.
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> Csem.final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H. inv MK. constructor.
Qed.

Theorem transl_program_correct:
  forall (beh: program_behavior),
  not_wrong beh -> Csem.exec_program prog beh ->
  Csharpminor.exec_program tprog beh.
Proof.
  set (order := fun (S1 S2: Csem.state) => False).
  assert (WF: well_founded order).
  unfold order; red. intros. constructor; intros. contradiction.
  assert (transl_step':
     forall S1 t S2, Csem.step ge S1 t S2 ->
     forall T1, match_states S1 T1 ->
     exists T2,
      (plus step tgve T1 t T2 \/ star step tgve T1 t T2 /\ order S2 S1)
      /\ match_states S2 T2).
  intros. exploit transl_step; eauto. intros [T2 [A B]].
  exists T2; split. auto. auto.
  intros. inv H0.
(* Terminates *)
  assert (exists t1, exists s1, Csem.step (Genv.globalenv prog) s t1 s1).
  inv H3. inv H2. inv H1. exists t1; exists s2; auto.
  destruct H0 as [t1 [s1 ST]].
  exploit transl_initial_states; eauto. intros [R [A B]].
  exploit simulation_star_star; eauto. intros [R' [C D]]. 
  econstructor; eauto. eapply transl_final_states; eauto.
(* Diverges *)
  assert (exists t1, exists s1, Csem.step (Genv.globalenv prog) s t1 s1).
  inv H2. inv H3. exists E0; exists s2; auto. exists t1; exists s2; auto.
  destruct H0 as [t1 [s1 ST]].
  exploit transl_initial_states; eauto. intros [R [A B]].
  exploit simulation_star_star; eauto. intros [R' [C D]]. 
  econstructor; eauto. eapply simulation_star_forever_silent; eauto.
(* Reacts *)
  assert (exists t1, exists s1, Csem.step (Genv.globalenv prog) s t1 s1).
  inv H2. inv H0. congruence. exists t1; exists s0; auto.
  destruct H0 as [t1 [s1 ST]].
  exploit transl_initial_states; eauto. intros [R [A B]].
  exploit simulation_star_forever_reactive; eauto.
  intro C.
  econstructor; eauto.
(* Goes wrong *)
  contradiction. contradiction.
Qed.

End CORRECTNESS.
