(** * Correctness of the C front end, part 3: semantic preservation *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import AST.
Require Import Values.
Require Import Events.
Require Import Mem.
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

Lemma symbols_preserved:
  forall s, Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf_partial2 transl_fundef transl_globvar _ TRANSL).

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial2 transl_fundef transl_globvar TRANSL).

Lemma function_ptr_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial2 transl_fundef transl_globvar TRANSL).

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

Definition match_var_kind (ty: type) (vk: var_kind) : Prop :=
  match access_mode ty with
  | By_value chunk => vk = Vscalar chunk
  | _ => True
  end.

Record match_env (tyenv: typenv) (e: Csem.env) (te: Csharpminor.env) : Prop :=
  mk_match_env {
    me_local:
      forall id b ty,
      e!id = Some b -> tyenv!id = Some ty ->
      exists vk, match_var_kind ty vk /\ te!id = Some (b, vk);
    me_global:
      forall id ty,
      e!id = None -> tyenv!id = Some ty ->
      te!id = None /\ 
      (forall chunk, access_mode ty = By_value chunk -> (global_var_env tprog)!id = Some (Vscalar chunk))
  }.

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
  intros until ty. repeat rewrite PTree.gempty. congruence.
  intros. split.
  apply PTree.gempty. 
  intros. red in H. eauto.
Qed.

Lemma match_var_kind_of_type:
  forall ty vk, var_kind_of_type ty = OK vk -> match_var_kind ty vk.
Proof.
  intros; red. 
  caseEq (access_mode ty); auto.
  intros chunk AM. generalize (var_kind_by_value _ _ AM). congruence.
Qed.

(** The following lemmas establish the [match_env] invariant at
  the beginning of a function invocation, after allocation of
  local variables and initialization of the parameters. *)

Lemma match_env_alloc_variables:
  forall e1 m1 vars e2 m2 lb,
  Csem.alloc_variables e1 m1 vars e2 m2 lb ->
  forall tyenv te1 tvars,
  match_env tyenv e1 te1 ->
  transl_vars vars = OK tvars ->
  exists te2,
  Csharpminor.alloc_variables te1 m1 tvars te2 m2 lb
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
  assert (match_env (add_var tyenv (id, ty)) (PTree.set id b1 e) te2).
    inversion H1. unfold te2, add_var. constructor.
    (* me_local *)
    intros until ty0. repeat rewrite PTree.gsspec. simpl. destruct (peq id0 id); intros.
    subst id0. exists vk; split. 
    apply match_var_kind_of_type. congruence. congruence.
    auto.
    (* me_global *)
    intros until ty0. repeat rewrite PTree.gsspec. simpl. destruct (peq id0 id); intros.
    discriminate.
    auto.
  destruct (IHalloc_variables _ _ _ H3 TVARS) as [te3 [ALLOC MENV]]. 
  exists te3; split.
  econstructor; eauto.
  rewrite (sizeof_var_kind_of_type _ _ VK). auto. 
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
  destruct (me_local _ _ _ H3 _ _ _ H H5) as [vk [A B]]. 
  red in A; rewrite H4 in A. congruence.
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
    (vars: list (ident * list init_data * var_kind)) :=
  List.fold_left
    (fun gve x => match x with (id, init, k) => PTree.set id k gve end)
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
  map_partial AST.prefix_var_name transl_globvar vars = OK tvars ->
  match_globalenv (add_global_vars tenv vars) (globvarenv gv tvars).
Proof.
  induction vars; simpl.
  intros. inversion H0. assumption.
  destruct a as [[id init] ty]. intros until tvars; intro.
  caseEq (transl_globvar ty); simpl; try congruence. intros vk VK. 
  caseEq (map_partial AST.prefix_var_name transl_globvar vars); simpl; try congruence. intros tvars' EQ1 EQ2.
  inversion EQ2; clear EQ2. simpl. 
  apply IHvars; auto.
  red. intros until chunk. repeat rewrite PTree.gsspec. 
  destruct (peq id0 id); intros.
  inversion H0; clear H0; subst id0 ty0. 
  generalize (var_kind_by_value _ _ H2). 
  unfold transl_globvar in VK. congruence.
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
  eval_expr tprog te m code v.
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
    exploit me_local; eauto. intros [vk [A B]].
    red in A; rewrite ACC in A.
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
    exploit me_local; eauto. intros [vk [A B]].
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
  forall e m id ty loc ofs v m' tyenv code te rhs, 
  Csem.eval_lvalue ge e m (Expr (Csyntax.Evar id) ty) loc ofs ->
  store_value_of_type ty m loc ofs v = Some m' ->
  wt_expr tyenv (Expr (Csyntax.Evar id) ty) ->
  var_set id ty rhs = OK code ->
  match_env tyenv e te ->
  eval_expr tprog te m rhs v ->
  exec_stmt tprog te m code E0 m' Out_normal.
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
    exploit me_local; eauto. intros [vk [A B]].
    red in A; rewrite ACC in A; subst vk.
    eapply exec_Sassign. eauto.
    econstructor. eapply eval_var_ref_local. eauto. assumption. 
    (* global variable *)
    exploit me_global; eauto. intros [A B].
    eapply exec_Sassign. eauto.
    econstructor. eapply eval_var_ref_global. auto. 
    fold tge. rewrite symbols_preserved. eauto.
    eauto. assumption. 
  (* access mode By_reference *)
  intros ACC. rewrite ACC in H0. discriminate.
  (* access mode By_nothing *)
  intros. rewrite H1 in H0; discriminate.
Qed.

Lemma call_dest_set_correct:
  forall e m0 lhs loc ofs m1 v m2 tyenv optid te,
  Csem.eval_lvalue ge e m0 lhs loc ofs ->
  store_value_of_type (typeof lhs) m1 loc ofs v = Some m2 ->
  wt_expr tyenv lhs ->
  transl_lhs_call (Some lhs) = OK optid ->
  match_env tyenv e te ->
  exec_opt_assign tprog te m1 optid v m2.
Proof.
  intros. generalize H2. simpl. caseEq (is_variable lhs). 2: congruence. 
  intros. inv H5. 
  exploit is_variable_correct; eauto. intro.
  rewrite H5 in H. rewrite H5 in H1. inversion H1. subst i ty.
  constructor.  
  generalize H0. unfold store_value_of_type. 
  caseEq (access_mode (typeof lhs)); intros; try discriminate.
  (* access mode By_value *)
  inversion H. 
  (* local variable *)
  subst id0 ty l ofs. exploit me_local; eauto. 
  intros [vk [A B]]. red in A. rewrite H6 in A. subst vk.
  econstructor. eapply eval_var_ref_local; eauto. assumption.
  (* global variable *)
  subst id0 ty l ofs. exploit me_global; eauto. 
  intros [A B]. 
  econstructor. eapply eval_var_ref_global; eauto. 
  rewrite symbols_preserved. eauto. assumption. 
Qed.

(** * Proof of semantic preservation *)

(** ** Semantic preservation for expressions *)

(** The proof of semantic preservation for the translation of expressions
  relies on simulation diagrams of the following form:
<<
         e, m, a ------------------- te, m, ta
            |                           |
           t|                           |t
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
  Csharpminor.eval_expr tprog te m ta v.

Definition eval_lvalue_prop (a: Csyntax.expr) (b: block) (ofs: int) : Prop :=
  forall ta
    (WT: wt_expr tyenv a)
    (TR: transl_lvalue a = OK ta),
  Csharpminor.eval_expr tprog te m ta (Vptr b ofs).

Definition eval_exprlist_prop (al: list Csyntax.expr) (vl: list val) : Prop :=
  forall tal
    (WT: wt_exprlist tyenv al)
    (TR: transl_exprlist al = OK tal),
  Csharpminor.eval_exprlist tprog te m tal vl.

(* Check (eval_expr_ind2 ge e m eval_expr_prop eval_lvalue_prop).*)

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
  forall (a : Csyntax.expr) (ty : type) (v1 v : val),
  Csem.eval_expr ge e m a v1 ->
  eval_expr_prop a v1 ->
  cast v1 (typeof a) ty v -> eval_expr_prop (Expr (Ecast ty a) ty) v.
Proof.
  intros; red; intros. inversion WT; clear WT; subst. monadInv TR.
  eapply make_cast_correct; eauto.
Qed.

Lemma transl_Evar_local_correct:
  forall (id : ident) (l : block) (ty : type),
  e ! id = Some l ->
  eval_lvalue_prop (Expr (Csyntax.Evar id) ty) l Int.zero.
Proof.
  intros; red; intros. inversion WT; clear WT; subst. monadInv TR.
  exploit (me_local _ _ _ MENV); eauto. intros [vk [A B]].
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

Lemma transl_Eindex_correct:
  forall (a1 a2 : Csyntax.expr) (ty : type) (v1 v2 : val) (l : block)
         (ofs : int),
  Csem.eval_expr ge e m a1 v1 ->
  eval_expr_prop a1 v1 ->
  Csem.eval_expr ge e m a2 v2 ->
  eval_expr_prop a2 v2 ->
  sem_add v1 (typeof a1) v2 (typeof a2) = Some (Vptr l ofs) ->
  eval_lvalue_prop (Expr (Eindex a1 a2) ty) l ofs.
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR. monadInv TR.
  eapply (make_add_correct tprog); eauto. 
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
         transl_Eorbool_1_correct
         transl_Eorbool_2_correct
         transl_Eandbool_1_correct
         transl_Eandbool_2_correct
         transl_Ecast_correct
         transl_Evar_local_correct
         transl_Evar_global_correct
         transl_Ederef_correct
         transl_Eindex_correct
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
         transl_Eorbool_1_correct
         transl_Eorbool_2_correct
         transl_Eandbool_1_correct
         transl_Eandbool_2_correct
         transl_Ecast_correct
         transl_Evar_local_correct
         transl_Evar_global_correct
         transl_Ederef_correct
         transl_Eindex_correct
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

(** ** Semantic preservation for statements *)

(** The simulation diagrams for terminating statements and function
  calls are of the following form:
  relies on simulation diagrams of the following form:
<<
         e, m1, s ------------------- te, m1, ts
            |                           |
           t|                           |t
            |                           |
            v                           v
         e, m2, out ----------------- te, m2, tout
>>
  Left: execution of statement [s] in Clight.
  Right: execution of its translation [ts] in Csharpminor.
  Top (precondition): matching between environments [e], [te], 
    plus well-typedness of statement [s].
  Bottom (postcondition): the outcomes [out] and [tout] are
    related per the following function [transl_outcome].
*)

Definition transl_outcome (nbrk ncnt: nat) (out: Csem.outcome): Csharpminor.outcome :=
  match out with
  | Csem.Out_normal => Csharpminor.Out_normal
  | Csem.Out_break  => Csharpminor.Out_exit nbrk
  | Csem.Out_continue => Csharpminor.Out_exit ncnt
  | Csem.Out_return vopt => Csharpminor.Out_return vopt
  end.

Definition exec_stmt_prop
    (e: Csem.env) (m1: mem) (s: Csyntax.statement) (t: trace)
    (m2: mem) (out: Csem.outcome) : Prop :=
  forall tyenv nbrk ncnt ts te
    (WT: wt_stmt tyenv s)
    (TR: transl_statement nbrk ncnt s = OK ts)   
    (MENV: match_env tyenv e te),
  Csharpminor.exec_stmt tprog te m1 ts t m2 (transl_outcome nbrk ncnt out).

Definition exec_lblstmts_prop
    (e: Csem.env) (m1: mem) (s: Csyntax.labeled_statements)
    (t: trace) (m2: mem) (out: Csem.outcome) : Prop :=
  forall tyenv nbrk ncnt body ts te m0 t0
    (WT: wt_lblstmts tyenv s)
    (TR: transl_lblstmts (lblstmts_length s)
                         (1 + lblstmts_length s + ncnt)
                         s body = OK ts)   
    (MENV: match_env tyenv e te)
    (BODY: Csharpminor.exec_stmt tprog te m0 body t0 m1 Out_normal),
  Csharpminor.exec_stmt tprog te m0 ts (t0 ** t) m2 
       (transl_outcome nbrk ncnt (outcome_switch out)).

Definition eval_funcall_prop
    (m1: mem) (f: Csyntax.fundef) (params: list val)
    (t: trace) (m2: mem) (res: val) : Prop :=
  forall tf
    (WT: wt_fundef (global_typenv prog) f)
    (TR: transl_fundef f = OK tf),
   Csharpminor.eval_funcall tprog m1 tf params t m2 res.

(*
Set Printing Depth 100.
Check (Csem.eval_funcall_ind3 ge exec_stmt_prop exec_lblstmts_prop eval_funcall_prop).
*)

Lemma transl_Sskip_correct:
       (forall (e : Csem.env) (m : mem),
        exec_stmt_prop e m Csyntax.Sskip E0 m Csem.Out_normal).
Proof.
  intros; red; intros. monadInv TR. simpl. constructor.
Qed.

Lemma transl_Sassign_correct:
  forall (e : Csem.env) (m : mem) (a1 a2 : Csyntax.expr) (loc : block)
         (ofs : int) (v2 : val) (m' : mem),
  eval_lvalue ge e m a1 loc ofs ->
  Csem.eval_expr ge e m a2 v2 ->
  store_value_of_type (typeof a1) m loc ofs v2 = Some m' ->
  exec_stmt_prop e m (Csyntax.Sassign a1 a2) E0 m' Csem.Out_normal.
Proof.
  intros; red; intros.
  inversion WT; subst; clear WT.
  simpl in TR. 
  caseEq (is_variable a1).
  (* a = variable id *)
  intros id ISVAR. rewrite ISVAR in TR. 
  generalize (is_variable_correct _ _ ISVAR). intro EQ. 
  rewrite EQ in H; rewrite EQ in H4.
  monadInv TR.
  eapply var_set_correct; eauto.
  eapply (transl_expr_correct _ _ _ _ MENV _ _ H0); eauto.  
  (* a is not a variable *)
  intro ISVAR; rewrite ISVAR in TR. monadInv TR.
  eapply make_store_correct; eauto.
  eapply (transl_lvalue_correct _ _ _ _ MENV _ _ _ H); eauto.
  eapply (transl_expr_correct _ _ _ _ MENV _ _ H0); eauto.  
Qed.

Lemma transl_Scall_None_correct:
  forall (e : Csem.env) (m : mem) (a : Csyntax.expr)
         (al : list Csyntax.expr) (vf : val) (vargs : list val)
         (f : Csyntax.fundef) (t : trace) (m' : mem) (vres : val),
  Csem.eval_expr ge e m a vf ->
  Csem.eval_exprlist ge e m al vargs ->
  Genv.find_funct ge vf = Some f ->
  type_of_fundef f = typeof a ->
  Csem.eval_funcall ge m f vargs t m' vres ->
  eval_funcall_prop m f vargs t m' vres ->
  exec_stmt_prop e m (Csyntax.Scall None a al) t m' Csem.Out_normal.
Proof.
  intros; red; intros; simpl.
  inv WT. simpl in TR. 
  caseEq (classify_fun (typeof a)); intros; rewrite H5 in TR; monadInv TR.
  exploit functions_translated; eauto. intros [tf [TFIND TFD]].
  econstructor. 
  eapply (transl_expr_correct _ _ _ _ MENV _ _ H); eauto.
  eapply (transl_exprlist_correct _ _ _ _ MENV _ _ H0); eauto.
  eauto. 
  eapply transl_fundef_sig1; eauto. rewrite H2; auto. 
  eapply H4; eauto. 
  eapply functions_well_typed; eauto.
  constructor. 
Qed.

Lemma transl_Scall_Some_correct:
  forall (e : Csem.env) (m : mem) (lhs a : Csyntax.expr)
         (al : list Csyntax.expr) (loc : block) (ofs : int) (vf : val)
         (vargs : list val) (f : Csyntax.fundef) (t : trace) (m' : mem)
         (vres : val) (m'' : mem),
  eval_lvalue ge e m lhs loc ofs ->
  Csem.eval_expr ge e m a vf ->
  Csem.eval_exprlist ge e m al vargs ->
  Genv.find_funct ge vf = Some f ->
  type_of_fundef f = typeof a ->
  Csem.eval_funcall ge m f vargs t m' vres ->
  eval_funcall_prop m f vargs t m' vres ->
  store_value_of_type (typeof lhs) m' loc ofs vres = Some m'' ->
  exec_stmt_prop e m (Csyntax.Scall (Some lhs) a al) t m'' Csem.Out_normal.
Proof.
  intros; red; intros; simpl.
  inv WT. inv H10. unfold transl_statement in TR.
  caseEq (classify_fun (typeof a)); intros; rewrite H7 in TR; monadInv TR.
  exploit functions_translated; eauto. intros [tf [TFIND TFD]].
  econstructor. 
  eapply (transl_expr_correct _ _ _ _ MENV _ _ H0); eauto.
  eapply (transl_exprlist_correct _ _ _ _ MENV _ _ H1); eauto.
  eauto. 
  eapply transl_fundef_sig1; eauto. rewrite H3; auto. 
  eapply H5; eauto. 
  eapply functions_well_typed; eauto.
  eapply call_dest_set_correct; eauto. 
Qed.

Lemma transl_Ssequence_1_correct:
       (forall (e : Csem.env) (m : mem) (s1 s2 : statement) (t1 : trace)
          (m1 : mem) (t2 : trace) (m2 : mem) (out : Csem.outcome),
        Csem.exec_stmt ge e m s1 t1 m1 Csem.Out_normal ->
        exec_stmt_prop e m s1 t1 m1 Csem.Out_normal ->
        Csem.exec_stmt ge e m1 s2 t2 m2 out ->
        exec_stmt_prop e m1 s2 t2 m2 out ->
        exec_stmt_prop e m (Ssequence s1 s2) (t1 ** t2) m2 out).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  red in H0; simpl in H0. eapply exec_Sseq_continue; eauto. 
Qed.

Lemma transl_Ssequence_2_correct:
       (forall (e : Csem.env) (m : mem) (s1 s2 : statement) (t1 : trace)
          (m1 : mem) (out : Csem.outcome),
        Csem.exec_stmt ge e m s1 t1 m1 out ->
        exec_stmt_prop e m s1 t1 m1 out ->
        out <> Csem.Out_normal ->
        exec_stmt_prop e m (Ssequence s1 s2) t1 m1 out).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  eapply exec_Sseq_stop; eauto. 
  destruct out; simpl; congruence.
Qed.

Lemma transl_Sifthenelse_true_correct:
        (forall (e : Csem.env) (m : mem) (a : Csyntax.expr)
          (s1 s2 : statement) (v1 : val) (t : trace) (m' : mem)
          (out : Csem.outcome),
        Csem.eval_expr ge e m a v1 ->
        is_true v1 (typeof a) ->
        Csem.exec_stmt ge e m s1 t m' out ->
        exec_stmt_prop e m s1 t m' out ->
        exec_stmt_prop e m (Csyntax.Sifthenelse a s1 s2) t m' out).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  exploit make_boolean_correct_true.
    eapply (transl_expr_correct _ _ _ _ MENV _ _ H); eauto.
    eauto.
  intros [vb [EVAL ISTRUE]].
  eapply exec_Sifthenelse; eauto. apply Val.bool_of_true_val; eauto. simpl; eauto. 
Qed.

Lemma transl_Sifthenelse_false_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr)
          (s1 s2 : statement) (v1 : val) (t : trace) (m' : mem)
          (out : Csem.outcome),
        Csem.eval_expr ge e m a v1 ->
        is_false v1 (typeof a) ->
        Csem.exec_stmt ge e m s2 t m' out ->
        exec_stmt_prop e m s2 t m' out ->
        exec_stmt_prop e m (Csyntax.Sifthenelse a s1 s2) t m' out).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  exploit make_boolean_correct_false.
    eapply (transl_expr_correct _ _ _ _ MENV _ _ H); eauto.
    eauto.
  intros [vb [EVAL ISFALSE]].
  eapply exec_Sifthenelse; eauto. apply Val.bool_of_false_val; eauto. simpl; eauto. 
Qed.

Lemma transl_Sreturn_none_correct:
       (forall (e : Csem.env) (m : mem),
        exec_stmt_prop e m (Csyntax.Sreturn None) E0 m (Csem.Out_return None)).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  simpl. apply exec_Sreturn_none. 
Qed.

Lemma transl_Sreturn_some_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr) (v : val),
        Csem.eval_expr ge e m a v ->
        exec_stmt_prop e m (Csyntax.Sreturn (Some a)) E0 m (Csem.Out_return (Some v))).
Proof.
  intros; red; intros. inv WT. inv H1. monadInv TR.
  simpl. eapply exec_Sreturn_some; eauto.
  eapply (transl_expr_correct _ _ _ _ MENV _ _ H); eauto.
Qed.

Lemma transl_Sbreak_correct:
       (forall (e : Csem.env) (m : mem),
        exec_stmt_prop e m Sbreak E0 m Out_break).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  simpl. apply exec_Sexit.  
Qed.

Lemma transl_Scontinue_correct:
       (forall (e : Csem.env) (m : mem),
        exec_stmt_prop e m Scontinue E0 m Out_continue).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  simpl. apply exec_Sexit.  
Qed.

Lemma exit_if_false_true:
  forall a ts e m v tyenv te,
  exit_if_false a = OK ts ->
  Csem.eval_expr ge e m a v ->
  is_true v (typeof a) ->
  match_env tyenv e te ->
  wt_expr tyenv a ->
  exec_stmt tprog te m ts E0 m Out_normal.
Proof.
  intros. monadInv H.
  exploit make_boolean_correct_true.
    eapply (transl_expr_correct _ _ _ _ H2 _ _ H0); eauto.
    eauto.
  intros [vb [EVAL ISTRUE]].
  eapply exec_Sifthenelse with (v := vb); eauto.
  apply Val.bool_of_true_val; eauto.  
  constructor.
Qed.
 
Lemma exit_if_false_false:
  forall a ts e m v tyenv te,
  exit_if_false a = OK ts ->
  Csem.eval_expr ge e m a v ->
  is_false v (typeof a) ->
  match_env tyenv e te ->
  wt_expr tyenv a ->
  exec_stmt tprog te m ts E0 m (Out_exit 0).
Proof.
  intros. monadInv H.
  exploit make_boolean_correct_false.
    eapply (transl_expr_correct _ _ _ _ H2 _ _ H0); eauto.
    eauto.
  intros [vb [EVAL ISFALSE]].
  eapply exec_Sifthenelse with (v := vb); eauto.
  apply Val.bool_of_false_val; eauto. 
  simpl. constructor.
Qed.

Lemma transl_Swhile_false_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr) (s : statement)
          (v : val),
        Csem.eval_expr ge e m a v ->
        is_false v (typeof a) ->
        exec_stmt_prop e m (Swhile a s) E0 m Csem.Out_normal).
Proof.
  intros; red; intros; simpl. inv WT. monadInv TR.
  change Out_normal with (outcome_block (Out_exit 0)).
  apply exec_Sblock. apply exec_Sloop_stop. apply exec_Sseq_stop.
  eapply exit_if_false_false; eauto. congruence. congruence.
Qed.

Lemma transl_out_break_or_return:
  forall out1 out2 nbrk ncnt,
  out_break_or_return out1 out2 ->
  transl_outcome nbrk ncnt out2 =
  outcome_block (outcome_block (transl_outcome 1 0 out1)).
Proof.
  intros. inversion H; subst; reflexivity.
Qed.

Lemma transl_out_normal_or_continue:
  forall out,
  out_normal_or_continue out ->
  Out_normal = outcome_block (transl_outcome 1 0 out).
Proof.
  intros; inversion H; reflexivity.
Qed.

Lemma transl_Swhile_stop_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr) (v : val)
          (s : statement) (t : trace) (m' : mem) (out' out : Csem.outcome),
        Csem.eval_expr ge e m a v ->
        is_true v (typeof a) ->
        Csem.exec_stmt ge e m s t m' out' ->
        exec_stmt_prop e m s t m' out' ->
        out_break_or_return out' out ->
        exec_stmt_prop e m (Swhile a s) t m' out).
Proof.
  intros; red; intros. inv WT. monadInv TR.
  rewrite (transl_out_break_or_return _ _ nbrk ncnt H3).
  apply exec_Sblock. apply exec_Sloop_stop. 
  eapply exec_Sseq_continue. 
  eapply exit_if_false_true; eauto. 
  apply exec_Sblock. eauto. traceEq.
  inversion H3; simpl; congruence.
Qed.

Lemma transl_Swhile_loop_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr) (s : statement)
          (v : val) (t1 : trace) (m1 : mem) (out1 : Csem.outcome)
          (t2 : trace) (m2 : mem) (out : Csem.outcome),
        Csem.eval_expr ge e m a v ->
        is_true v (typeof a) ->
        Csem.exec_stmt ge e m s t1 m1 out1 ->
        exec_stmt_prop e m s t1 m1 out1 ->
        out_normal_or_continue out1 ->
        Csem.exec_stmt ge e m1 (Swhile a s) t2 m2 out ->
        exec_stmt_prop e m1 (Swhile a s) t2 m2 out ->
        exec_stmt_prop e m (Swhile a s) (t1 ** t2) m2 out).
Proof.
  intros; red; intros. 
  exploit H5; eauto. intro NEXTITER.
  inv WT. monadInv TR. 
  inversion NEXTITER; subst.
  apply exec_Sblock. 
  eapply exec_Sloop_loop. eapply exec_Sseq_continue.
  eapply exit_if_false_true; eauto. 
  rewrite (transl_out_normal_or_continue _ H3).
  apply exec_Sblock. eauto. 
  reflexivity. eassumption.
  traceEq.
Qed.

Lemma transl_Sdowhile_false_correct:
       (forall (e : Csem.env) (m : mem) (s : statement) (a : Csyntax.expr)
          (t : trace) (m1 : mem) (out1 : Csem.outcome) (v : val),
        Csem.exec_stmt ge e m s t m1 out1 ->
        exec_stmt_prop e m s t m1 out1 ->
        out_normal_or_continue out1 ->
        Csem.eval_expr ge e m1 a v ->
        is_false v (typeof a) ->
        exec_stmt_prop e m (Sdowhile a s) t m1 Csem.Out_normal).
Proof.
  intros; red; intros. inv WT. monadInv TR.
  simpl.
  change Out_normal with (outcome_block (Out_exit 0)).
  apply exec_Sblock. apply exec_Sloop_stop. eapply exec_Sseq_continue.
  rewrite (transl_out_normal_or_continue out1 H1).
  apply exec_Sblock. eauto. 
  eapply exit_if_false_false; eauto. traceEq. congruence. 
Qed.

Lemma transl_Sdowhile_stop_correct:
       (forall (e : Csem.env) (m : mem) (s : statement) (a : Csyntax.expr)
          (t : trace) (m1 : mem) (out1 out : Csem.outcome),
        Csem.exec_stmt ge e m s t m1 out1 ->
        exec_stmt_prop e m s t m1 out1 ->
        out_break_or_return out1 out ->
        exec_stmt_prop e m (Sdowhile a s) t m1 out).
Proof.
  intros; red; intros. inv WT. monadInv TR.
  simpl.
  assert (outcome_block (transl_outcome 1 0 out1) <> Out_normal).
    inversion H1; simpl; congruence.
  rewrite (transl_out_break_or_return _ _ nbrk ncnt H1). 
  apply exec_Sblock. apply exec_Sloop_stop. 
  apply exec_Sseq_stop. apply exec_Sblock. eauto. 
  auto. auto. 
Qed.

Lemma transl_Sdowhile_loop_correct:
       (forall (e : Csem.env) (m : mem) (s : statement) (a : Csyntax.expr)
          (m1 m2 : mem) (t1 t2 : trace) (out out1 : Csem.outcome) (v : val),
        Csem.exec_stmt ge e m s t1 m1 out1 ->
        exec_stmt_prop e m s t1 m1 out1 ->
        out_normal_or_continue out1 ->
        Csem.eval_expr ge e m1 a v ->
        is_true v (typeof a) ->
        Csem.exec_stmt ge e m1 (Sdowhile a s) t2 m2 out ->
        exec_stmt_prop e m1 (Sdowhile a s) t2 m2 out ->
        exec_stmt_prop e m (Sdowhile a s) (t1 ** t2) m2 out).
Proof.
  intros; red; intros. 
  exploit H5; eauto. intro NEXTITER.
  inv WT. monadInv TR. inversion NEXTITER; subst.
  apply exec_Sblock. 
  eapply exec_Sloop_loop. eapply exec_Sseq_continue.
  rewrite (transl_out_normal_or_continue _ H1).
  apply exec_Sblock. eauto. 
  eapply exit_if_false_true; eauto. 
  reflexivity. eassumption. traceEq.
Qed.

Lemma transl_Sfor_start_correct:
       (forall (e : Csem.env) (m : mem) (s a1 : statement)
          (a2 : Csyntax.expr) (a3 : statement) (out : Csem.outcome)
          (m1 m2 : mem) (t1 t2 : trace),
        a1 <> Csyntax.Sskip ->
        Csem.exec_stmt ge e m a1 t1 m1 Csem.Out_normal ->
        exec_stmt_prop e m a1 t1 m1 Csem.Out_normal ->
        Csem.exec_stmt ge e m1 (Sfor Csyntax.Sskip a2 a3 s) t2 m2 out ->
        exec_stmt_prop e m1 (Sfor Csyntax.Sskip a2 a3 s) t2 m2 out ->
        exec_stmt_prop e m (Sfor a1 a2 a3 s) (t1 ** t2) m2 out).
Proof.
  intros; red; intros.
  destruct (transl_stmt_Sfor_start _ _ _ _ _ _ _ TR H) as [ts1 [ts2 [EQ [TR1 TR2]]]].
  subst ts.
  inv WT.
  assert (WT': wt_stmt tyenv (Sfor Csyntax.Sskip a2 a3 s)).
    constructor; auto. constructor.
  exploit H1; eauto. simpl. intro EXEC1.
  exploit H3; eauto. intro EXEC2.
  eapply exec_Sseq_continue; eauto.  
Qed.

Lemma transl_Sfor_false_correct:
       (forall (e : Csem.env) (m : mem) (s : statement) (a2 : Csyntax.expr)
          (a3 : statement) (v : val),
        Csem.eval_expr ge e m a2 v ->
        is_false v (typeof a2) ->
        exec_stmt_prop e m (Sfor Csyntax.Sskip a2 a3 s) E0 m Csem.Out_normal).
Proof.
  intros; red; intros. inv WT.
  rewrite transl_stmt_Sfor_not_start in TR; monadInv TR.
  simpl.
  change Out_normal with (outcome_block (Out_exit 0)).
  apply exec_Sblock. apply exec_Sloop_stop. 
  apply exec_Sseq_stop. eapply exit_if_false_false; eauto. 
  congruence. congruence.  
Qed.

Lemma transl_Sfor_stop_correct:
       (forall (e : Csem.env) (m : mem) (s : statement) (a2 : Csyntax.expr)
          (a3 : statement) (v : val) (m1 : mem) (t : trace)
          (out1 out : Csem.outcome),
        Csem.eval_expr ge e m a2 v ->
        is_true v (typeof a2) ->
        Csem.exec_stmt ge e m s t m1 out1 ->
        exec_stmt_prop e m s t m1 out1 ->
        out_break_or_return out1 out ->
        exec_stmt_prop e m (Sfor Csyntax.Sskip a2 a3 s) t m1 out).
Proof.
  intros; red; intros. inv WT.
  rewrite transl_stmt_Sfor_not_start in TR; monadInv TR.
  assert (outcome_block (transl_outcome 1 0 out1) <> Out_normal).
    inversion H3; simpl; congruence.
  rewrite (transl_out_break_or_return _ _ nbrk ncnt H3). 
  apply exec_Sblock. apply exec_Sloop_stop. 
  eapply exec_Sseq_continue. eapply exit_if_false_true; eauto.
  apply exec_Sseq_stop. apply exec_Sblock. eauto. 
  auto. reflexivity. auto. 
Qed.

Lemma transl_Sfor_loop_correct:
       (forall (e : Csem.env) (m : mem) (s : statement) (a2 : Csyntax.expr)
          (a3 : statement) (v : val) (m1 m2 m3 : mem) (t1 t2 t3 : trace)
          (out1 out : Csem.outcome),
        Csem.eval_expr ge e m a2 v ->
        is_true v (typeof a2) ->
        Csem.exec_stmt ge e m s t1 m1 out1 ->
        exec_stmt_prop e m s t1 m1 out1 ->
        out_normal_or_continue out1 ->
        Csem.exec_stmt ge e m1 a3 t2 m2 Csem.Out_normal ->
        exec_stmt_prop e m1 a3 t2 m2 Csem.Out_normal ->
        Csem.exec_stmt ge e m2 (Sfor Csyntax.Sskip a2 a3 s) t3 m3 out ->
        exec_stmt_prop e m2 (Sfor Csyntax.Sskip a2 a3 s) t3 m3 out ->
        exec_stmt_prop e m (Sfor Csyntax.Sskip a2 a3 s) (t1 ** t2 ** t3) m3 out).
Proof.
  intros; red; intros. 
  exploit H7; eauto. intro NEXTITER.
  inv WT.
  rewrite transl_stmt_Sfor_not_start in TR; monadInv TR.
  inversion NEXTITER; subst.
  apply exec_Sblock. 
  eapply exec_Sloop_loop. eapply exec_Sseq_continue.
  eapply exit_if_false_true; eauto.
  eapply exec_Sseq_continue.
  rewrite (transl_out_normal_or_continue _ H3).
  apply exec_Sblock. eauto. 
  red in H5; simpl in H5; eauto.
  reflexivity. reflexivity. eassumption. 
  traceEq. 
Qed.

Lemma transl_lblstmts_switch:
  forall e m0 m1 n nbrk ncnt tyenv te t0 t m2 out sl body ts,
  exec_stmt tprog te m0 body t0 m1 
    (Out_exit (switch_target n (lblstmts_length sl) (switch_table sl 0))) ->
  transl_lblstmts 
    (lblstmts_length sl)
    (S (lblstmts_length sl + ncnt))
    sl (Sblock body) = OK ts ->
  wt_lblstmts tyenv sl ->
  match_env tyenv e te ->
  exec_lblstmts_prop e m1 (select_switch n sl) t m2 out ->
  Csharpminor.exec_stmt tprog te m0 ts (t0 ** t) m2 
    (transl_outcome nbrk ncnt (outcome_switch out)).
Proof.
  induction sl; intros.
  simpl in H. simpl in H3.
  eapply H3; eauto. 
  change Out_normal with (outcome_block (Out_exit 0)).
  apply exec_Sblock. auto.
  (* Inductive case *)
  simpl in H. simpl in H3. rewrite Int.eq_sym in H3. destruct (Int.eq n i).
  (* first case selected *)
  eapply H3; eauto. 
  change Out_normal with (outcome_block (Out_exit 0)).
  apply exec_Sblock. auto.
  (* next case selected *)
  inversion H1; clear H1; subst.
  simpl in H0; monadInv H0.
  eapply IHsl with (body := Sseq (Sblock body) x); eauto.
  apply exec_Sseq_stop. 
  change (Out_exit (switch_target n (lblstmts_length sl) (switch_table sl 0)))
    with (outcome_block (Out_exit (S (switch_target n (lblstmts_length sl) (switch_table sl 0))))).
  apply exec_Sblock. 
  rewrite switch_target_table_shift in H. auto. congruence.
Qed.

Lemma transl_Sswitch_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr) (t : trace)
          (n : int) (sl : labeled_statements) (m1 : mem) (out : Csem.outcome),
        Csem.eval_expr ge e m a (Vint n) ->
        exec_lblstmts ge e m (select_switch n sl) t m1 out ->
        exec_lblstmts_prop e m (select_switch n sl) t m1 out ->
        exec_stmt_prop e m (Csyntax.Sswitch a sl) t m1 (outcome_switch out)).
Proof.
  intros; red; intros.
  inv WT. monadInv TR.
  rewrite length_switch_table in EQ0. 
  replace (ncnt + lblstmts_length sl + 1)%nat
     with (S (lblstmts_length sl + ncnt))%nat in EQ0 by omega.
  change t with (E0 ** t). eapply transl_lblstmts_switch; eauto. 
  constructor. eapply (transl_expr_correct _ _ _ _ MENV _ _ H); eauto. 
Qed.

Lemma transl_LSdefault_correct:
       (forall (e : Csem.env) (m : mem) (s : statement) (t : trace)
          (m1 : mem) (out : Csem.outcome),
        Csem.exec_stmt ge e m s t m1 out ->
        exec_stmt_prop e m s t m1 out ->
        exec_lblstmts_prop e m (LSdefault s) t m1 out).
Proof.
  intros; red; intros. inv WT. monadInv TR.
  replace (transl_outcome nbrk ncnt (outcome_switch out))
     with (outcome_block (transl_outcome 0 (S ncnt) out)).
  constructor. 
  eapply exec_Sseq_continue. eauto. 
  eapply H0; eauto. traceEq.
  destruct out; simpl; auto.
Qed.

Lemma transl_LScase_fallthrough_correct:
       (forall (e : Csem.env) (m : mem) (n : int) (s : statement)
          (ls : labeled_statements) (t1 : trace) (m1 : mem) (t2 : trace)
          (m2 : mem) (out : Csem.outcome),
        Csem.exec_stmt ge e m s t1 m1 Csem.Out_normal ->
        exec_stmt_prop e m s t1 m1 Csem.Out_normal ->
        exec_lblstmts ge e m1 ls t2 m2 out ->
        exec_lblstmts_prop e m1 ls t2 m2 out ->
        exec_lblstmts_prop e m (LScase n s ls) (t1 ** t2) m2 out).
Proof.
  intros; red; intros. inv WT. monadInv TR. 
  assert (exec_stmt tprog te m0 (Sblock (Sseq body x)) 
                          (t0 ** t1) m1 Out_normal).
  change Out_normal with
    (outcome_block (transl_outcome (S (lblstmts_length ls))
                                   (S (S (lblstmts_length ls + ncnt)))
                                   Csem.Out_normal)).
  apply exec_Sblock. eapply exec_Sseq_continue. eexact BODY. 
  eapply H0; eauto.
  auto.
  exploit H2. eauto. simpl; eauto. eauto. eauto. simpl. 
  rewrite Eapp_assoc. eauto.
Qed.

Lemma transl_LScase_stop_correct:
      (forall (e : Csem.env) (m : mem) (n : int) (s : statement)
          (ls : labeled_statements) (t : trace) (m1 : mem)
          (out : Csem.outcome),
        Csem.exec_stmt ge e m s t m1 out ->
        exec_stmt_prop e m s t m1 out ->
        out <> Csem.Out_normal ->
        exec_lblstmts_prop e m (LScase n s ls) t m1 out).
Proof.
  intros; red; intros. inv WT. monadInv TR.
  exploit H0; eauto. intro EXEC.
  destruct out; simpl; simpl in EXEC.
  (* out = Out_break *)
  change Out_normal with (outcome_block (Out_exit 0)).
  eapply transl_lblstmts_exit with (body := Sblock (Sseq body x)); eauto.
  rewrite plus_0_r. 
  change (Out_exit (lblstmts_length ls))
    with (outcome_block (Out_exit (S (lblstmts_length ls)))).
  constructor. eapply exec_Sseq_continue; eauto.
  (* out = Out_continue *)
  change (Out_exit ncnt) with (outcome_block (Out_exit (S ncnt))).
  eapply transl_lblstmts_exit with (body := Sblock (Sseq body x)); eauto.
  replace (Out_exit (lblstmts_length ls + S ncnt))
    with (outcome_block (Out_exit (S (S (lblstmts_length ls + ncnt))))).
  constructor. eapply exec_Sseq_continue; eauto.
  simpl. decEq. omega. 
  (* out = Out_normal *)
  congruence.
  (* out = Out_return *)
  eapply transl_lblstmts_return with (body := Sblock (Sseq body x)); eauto.
  change (Out_return o)
    with (outcome_block (Out_return o)).
  constructor. eapply exec_Sseq_continue; eauto.
Qed.

Remark outcome_result_value_match:
  forall out ty v nbrk ncnt,
  Csem.outcome_result_value out ty v ->
  Csharpminor.outcome_result_value (transl_outcome nbrk ncnt out) (opttyp_of_type ty) v.
Proof.
  intros until ncnt.
  destruct out; simpl; try contradiction.
  destruct ty; simpl; auto.
  destruct o. intros [A B]. destruct ty; simpl; congruence.
  destruct ty; simpl; auto.
Qed.

Lemma transl_funcall_internal_correct:
       (forall (m : mem) (f : Csyntax.function) (vargs : list val)
          (t : trace) (e : Csem.env) (m1 : mem) (lb : list block)
          (m2 m3 : mem) (out : Csem.outcome) (vres : val),
        Csem.alloc_variables Csem.empty_env m
          (Csyntax.fn_params f ++ Csyntax.fn_vars f) e m1 lb ->
        Csem.bind_parameters e m1 (Csyntax.fn_params f) vargs m2 ->
        Csem.exec_stmt ge e m2 (Csyntax.fn_body f) t m3 out ->
        exec_stmt_prop e m2 (Csyntax.fn_body f) t m3 out ->
        Csem.outcome_result_value out (fn_return f) vres ->
        eval_funcall_prop m (Internal f) vargs t (free_list m3 lb) vres).
Proof.
  intros; red; intros.
  (* Exploitation of typing hypothesis *)
  inv WT. inv H6.
  (* Exploitation of translation hypothesis *)
  monadInv TR. 
  monadInv EQ.
  (* Allocation of variables *)
  exploit match_env_alloc_variables; eauto.
  apply match_globalenv_match_env_empty. 
  apply match_global_typenv.
  eexact (transl_fn_variables _ _ (signature_of_function f) _ _ x2 EQ0 EQ).
  intros [te [ALLOCVARS MATCHENV]].
  (* Execution *)
  econstructor; simpl.
    (* Norepet *)
    eapply transl_names_norepet; eauto. 
    (* Alloc *)
    eexact ALLOCVARS.
    (* Bind *)
    eapply bind_parameters_match; eauto.
    (* Execution of body *)
    eapply H2; eauto.
    (* Outcome_result_value *)
    apply outcome_result_value_match; auto.
Qed.

Lemma transl_funcall_external_correct:
       (forall (m : mem) (id : ident) (targs : typelist) (tres : type)
          (vargs : list val) (t : trace) (vres : val),
        event_match (external_function id targs tres) vargs t vres ->
        eval_funcall_prop m (External id targs tres) vargs t m vres).
Proof.
  intros; red; intros.
  monadInv TR. constructor. auto.
Qed.

Theorem transl_funcall_correct:
  forall (m : mem) (f : Csyntax.fundef) (l : list val) (t : trace)
         (m0 : mem) (v : val),
  Csem.eval_funcall ge m f l t m0 v ->
  eval_funcall_prop m f l t m0 v.
Proof
  (Csem.eval_funcall_ind3 ge
         exec_stmt_prop
         exec_lblstmts_prop
         eval_funcall_prop

         transl_Sskip_correct
         transl_Sassign_correct
         transl_Scall_None_correct
         transl_Scall_Some_correct
         transl_Ssequence_1_correct
         transl_Ssequence_2_correct
         transl_Sifthenelse_true_correct
         transl_Sifthenelse_false_correct
         transl_Sreturn_none_correct
         transl_Sreturn_some_correct
         transl_Sbreak_correct
         transl_Scontinue_correct
         transl_Swhile_false_correct
         transl_Swhile_stop_correct
         transl_Swhile_loop_correct
         transl_Sdowhile_false_correct
         transl_Sdowhile_stop_correct
         transl_Sdowhile_loop_correct
         transl_Sfor_start_correct
         transl_Sfor_false_correct
         transl_Sfor_stop_correct
         transl_Sfor_loop_correct
         transl_Sswitch_correct
         transl_LSdefault_correct
         transl_LScase_fallthrough_correct
         transl_LScase_stop_correct
         transl_funcall_internal_correct
         transl_funcall_external_correct).

Theorem transl_stmt_correct:
  forall (e: Csem.env) (m1: mem) (s: Csyntax.statement) (t: trace)
         (m2: mem) (out: Csem.outcome),
  Csem.exec_stmt ge e m1 s t m2 out ->
  exec_stmt_prop e m1 s t m2 out.
Proof
  (Csem.exec_stmt_ind3 ge
         exec_stmt_prop
         exec_lblstmts_prop
         eval_funcall_prop

         transl_Sskip_correct
         transl_Sassign_correct
         transl_Scall_None_correct
         transl_Scall_Some_correct
         transl_Ssequence_1_correct
         transl_Ssequence_2_correct
         transl_Sifthenelse_true_correct
         transl_Sifthenelse_false_correct
         transl_Sreturn_none_correct
         transl_Sreturn_some_correct
         transl_Sbreak_correct
         transl_Scontinue_correct
         transl_Swhile_false_correct
         transl_Swhile_stop_correct
         transl_Swhile_loop_correct
         transl_Sdowhile_false_correct
         transl_Sdowhile_stop_correct
         transl_Sdowhile_loop_correct
         transl_Sfor_start_correct
         transl_Sfor_false_correct
         transl_Sfor_stop_correct
         transl_Sfor_loop_correct
         transl_Sswitch_correct
         transl_LSdefault_correct
         transl_LScase_fallthrough_correct
         transl_LScase_stop_correct
         transl_funcall_internal_correct
         transl_funcall_external_correct).

(** ** Semantic preservation for divergence *)

Lemma transl_funcall_divergence_correct:
  forall m1 f params t tf,
  Csem.evalinf_funcall ge m1 f params t ->
  wt_fundef (global_typenv prog) f ->
  transl_fundef f = OK tf ->
  Csharpminor.evalinf_funcall tprog m1 tf params t.
Proof.
  cofix FUNCALL.
  assert (STMT: 
    forall e m1 s t,
    Csem.execinf_stmt ge e m1 s t ->
    forall tyenv nbrk ncnt ts te
      (WT: wt_stmt tyenv s)
      (TR: transl_statement nbrk ncnt s = OK ts)   
      (MENV: match_env tyenv e te),
    Csharpminor.execinf_stmt tprog te m1 ts t).
  cofix STMT.
  assert(LBLSTMT:
  forall s ncnt body ts tyenv e te m0 t0 m1 t1 n,
  transl_lblstmts (lblstmts_length s)
                  (S (lblstmts_length s + ncnt))
                  s body = OK ts ->
  wt_lblstmts tyenv s ->
  match_env tyenv e te ->
      (exec_stmt tprog te m0 body t0 m1
        (outcome_block (Out_exit
           (switch_target n (lblstmts_length s) (switch_table s 0))))
       /\ execinf_lblstmts ge e m1 (select_switch n s) t1)
   \/ (exec_stmt tprog te m0 body t0 m1 Out_normal
       /\ execinf_lblstmts ge e m1 s t1) ->
  execinf_stmt_N tprog (lblstmts_length s) te m0 ts (t0 *** t1)).

  cofix LBLSTMT; intros.
  destruct s; simpl in *; monadInv H; inv H0.
  (* 1. LSdefault *)
  assert (exec_stmt tprog te m0 body t0 m1 Out_normal) by tauto.
  assert (execinf_lblstmts ge e m1 (LSdefault s) t1) by tauto.
  clear H2. inv H0.  
  change (Sblock (Sseq body x))
    with ((fun z => Sblock z) (Sseq body x)).
  apply execinf_context. 
  eapply execinf_Sseq_2. eauto. eapply STMT; eauto. auto.
  constructor.
  (* 2. LScase *)
  elim H2; clear H2.
  (* 2.1 searching for the case *)
  rewrite (Int.eq_sym i n). 
  destruct (Int.eq n i).
  (* 2.1.1 found it! *)
  intros [A B]. inv B.
  (* 2.1.1.1 we diverge because of this case *)
  destruct (transl_lblstmts_context _ _ _ _ _ EQ0) as [ctx [CTX EQ1]].
  rewrite EQ1. apply execinf_context; auto. 
  apply execinf_Sblock. eapply execinf_Sseq_2. eauto. 
  eapply STMT; eauto. auto.
  (* 2.1.1.2 we diverge later, after falling through *)
  simpl. apply execinf_sleep.
  replace (t0 *** t2 *** t3) with ((t0 ** t2) *** t3). 
  eapply LBLSTMT with (n := n); eauto. right. split.
  change Out_normal with (outcome_block Out_normal). 
  apply exec_Sblock.
  eapply exec_Sseq_continue. eauto. 
  change Out_normal with (transl_outcome (S (lblstmts_length s0)) (S (S (lblstmts_length s0 + ncnt))) Csem.Out_normal).
  eapply (transl_stmt_correct _ _ _ _ _ _ H8); eauto.
  auto. auto. traceEq.
  (* 2.1.2 still searching *)
  rewrite switch_target_table_shift. intros [A B].
  apply execinf_sleep.
  eapply LBLSTMT with (n := n); eauto. left. split.
  fold (outcome_block (Out_exit (switch_target n (lblstmts_length s0) (switch_table s0 0)))).
  apply exec_Sblock. apply exec_Sseq_stop. eauto. congruence.
  auto.
  (* 2.2 found the case already, falling through next cases *)
  intros [A B]. inv B.
  (* 2.2.1 we diverge because of this case *)
  destruct (transl_lblstmts_context _ _ _ _ _ EQ0) as [ctx [CTX EQ1]].
  rewrite EQ1. apply execinf_context; auto. 
  apply execinf_Sblock. eapply execinf_Sseq_2. eauto. 
  eapply STMT; eauto. auto.
  (* 2.2.2 we diverge later *)
  simpl. apply execinf_sleep.
  replace (t0 *** t2 *** t3) with ((t0 ** t2) *** t3). 
  eapply LBLSTMT with (n := n); eauto. right. split.
  change Out_normal with (outcome_block Out_normal). 
  apply exec_Sblock.
  eapply exec_Sseq_continue. eauto. 
  change Out_normal with (transl_outcome (S (lblstmts_length s0)) (S (S (lblstmts_length s0 + ncnt))) Csem.Out_normal).
  eapply (transl_stmt_correct _ _ _ _ _ _ H8); eauto.
  auto. auto. traceEq.


  intros. inv H; inv WT; try (generalize TR; intro TR'; monadInv TR').
  (* Scall *)
  simpl in TR.
  caseEq (classify_fun (typeof a)); intros; rewrite H in TR; monadInv TR.
  destruct (functions_translated _ _ H2) as [tf [TFIND TFD]].
  eapply execinf_Scall. 
  eapply (transl_expr_correct _ _ _ _ MENV _ _ H0); eauto.
  eapply (transl_exprlist_correct _ _ _ _ MENV _ _ H1); eauto.
  eauto. 
  eapply transl_fundef_sig1; eauto. rewrite H3; auto. 
  eapply FUNCALL; eauto.
  eapply functions_well_typed; eauto.
  (* Sseq 1 *)
  apply execinf_Sseq_1. eapply STMT; eauto. 
  (* Sseq 2 *)
  eapply execinf_Sseq_2. 
  change Out_normal with (transl_outcome nbrk ncnt Csem.Out_normal).
  eapply (transl_stmt_correct _ _ _ _ _ _ H0); eauto.
  eapply STMT; eauto. auto.
  (* Sifthenelse, true *)
  assert (eval_expr tprog te m1 x v1).
    eapply (transl_expr_correct _ _ _ _ MENV _ _ H0); eauto.
  destruct (make_boolean_correct_true _ _ _ _ _ _ H H1) as [vb [A B]].
  eapply execinf_Sifthenelse. eauto. apply Val.bool_of_true_val; eauto.
  auto. eapply STMT; eauto.
  (* Sifthenelse, false *)
  assert (eval_expr tprog te m1 x v1).
    eapply (transl_expr_correct _ _ _ _ MENV _ _ H0); eauto.
  destruct (make_boolean_correct_false _ _ _ _ _ _ H H1) as [vb [A B]].
  eapply execinf_Sifthenelse. eauto. apply Val.bool_of_false_val; eauto.
  auto. eapply STMT; eauto.
  (* Swhile, body *)
  apply execinf_Sblock. apply execinf_Sloop_body.  
  eapply execinf_Sseq_2. eapply exit_if_false_true; eauto. 
  apply execinf_Sblock. eapply STMT; eauto. traceEq.
  (* Swhile, loop *)
  apply execinf_Sblock. eapply execinf_Sloop_block.
  eapply exec_Sseq_continue. eapply exit_if_false_true; eauto.
  rewrite (transl_out_normal_or_continue out1 H3). 
  apply exec_Sblock. 
  eapply (transl_stmt_correct _ _ _ _ _ _ H2); eauto. reflexivity.
  eapply STMT with (nbrk := 1%nat) (ncnt := 0%nat); eauto.
  constructor; eauto.
  traceEq.
  (* Sdowhile, body *)
  apply execinf_Sblock. apply execinf_Sloop_body.  
  apply execinf_Sseq_1. apply execinf_Sblock.
  eapply STMT; eauto.
  (* Sdowhile, loop *)
  apply execinf_Sblock. eapply execinf_Sloop_block.
  eapply exec_Sseq_continue.
  rewrite (transl_out_normal_or_continue out1 H1). 
  apply exec_Sblock. 
  eapply (transl_stmt_correct _ _ _ _ _ _ H0); eauto. 
  eapply exit_if_false_true; eauto. reflexivity.
  eapply STMT with (nbrk := 1%nat) (ncnt := 0%nat); eauto.
  constructor; auto.
  traceEq.
  (* Sfor start 1 *)
  simpl in TR. destruct (is_Sskip a1). 
  subst a1. inv H0.
  monadInv TR. 
  apply execinf_Sseq_1. eapply STMT; eauto.
  (* Sfor start 2 *)
  destruct (transl_stmt_Sfor_start _ _ _ _ _ _ _ TR H0) as [ts1 [ts2 [EQ [TR1 TR2]]]].
  subst ts. 
  eapply execinf_Sseq_2. 
  change Out_normal with (transl_outcome nbrk ncnt Csem.Out_normal).
  eapply (transl_stmt_correct _ _ _ _ _ _ H1); eauto.
  eapply STMT; eauto. 
    constructor; auto. constructor.
  auto.
  (* Sfor_body *)
  rewrite transl_stmt_Sfor_not_start in TR; monadInv TR.
  apply execinf_Sblock. apply execinf_Sloop_body.
  eapply execinf_Sseq_2. 
  eapply exit_if_false_true; eauto.
  apply execinf_Sseq_1. apply execinf_Sblock. 
  eapply STMT; eauto.
  traceEq.
  (* Sfor next *)
  rewrite transl_stmt_Sfor_not_start in TR; monadInv TR.
  apply execinf_Sblock. apply execinf_Sloop_body.
  eapply execinf_Sseq_2. 
  eapply exit_if_false_true; eauto.
  eapply execinf_Sseq_2.
  rewrite (transl_out_normal_or_continue out1 H3). 
  apply exec_Sblock. 
  eapply (transl_stmt_correct _ _ _ _ _ _ H2); eauto.
  eapply STMT; eauto.
  reflexivity. traceEq. 
  (* Sfor loop *)
  generalize TR. rewrite transl_stmt_Sfor_not_start; intro TR'; monadInv TR'.
  apply execinf_Sblock. eapply execinf_Sloop_block.
  eapply exec_Sseq_continue.
  eapply exit_if_false_true; eauto.
  eapply exec_Sseq_continue.
  rewrite (transl_out_normal_or_continue out1 H3). 
  apply exec_Sblock. 
  eapply (transl_stmt_correct _ _ _ _ _ _ H2); eauto.
  change Out_normal with (transl_outcome nbrk ncnt Csem.Out_normal).
  eapply (transl_stmt_correct _ _ _ _ _ _ H4); eauto.
  reflexivity. reflexivity. 
  eapply STMT; eauto. 
    constructor; auto.
  traceEq.
  (* Sswitch *)
  apply execinf_stutter with (lblstmts_length sl).
  rewrite length_switch_table in EQ0.
  replace (ncnt + lblstmts_length sl + 1)%nat
     with (S (lblstmts_length sl + ncnt))%nat in EQ0 by omega.
  change t with (E0 *** t).
  eapply LBLSTMT; eauto.
  left. split. apply exec_Sblock. constructor. 
  eapply (transl_expr_correct _ _ _ _ MENV _ _ H0); eauto.
  auto. 

  (* Functions *)
  intros. inv H. 
  (* Exploitation of typing hypothesis *)
  inv H0. inv H6. 
  (* Exploitation of translation hypothesis *)
  monadInv H1. monadInv EQ.
  (* Allocation of variables *)
  assert (match_env (global_typenv prog) Csem.empty_env Csharpminor.empty_env).
    apply match_globalenv_match_env_empty. apply match_global_typenv. 
  generalize (transl_fn_variables _ _ (signature_of_function f0) _ _ x2 EQ0 EQ).
  intro. 
  destruct (match_env_alloc_variables _ _ _ _ _ _ H2 _ _ _ H1 H5)
  as [te [ALLOCVARS MATCHENV]].
  (* Execution *)
  econstructor; simpl.
  eapply transl_names_norepet; eauto. 
  eexact ALLOCVARS.
  eapply bind_parameters_match; eauto.
  eapply STMT; eauto. 
Qed.

End CORRECTNESS.

(** Semantic preservation for whole programs. *)

Theorem transl_program_correct:
  forall prog tprog beh,
  transl_program prog = OK tprog ->
  Ctyping.wt_program prog ->
  Csem.exec_program prog beh ->
  Csharpminor.exec_program tprog beh.
Proof.
  intros. inversion H0; subst. inv H1.
  (* Termination *)
  assert (exists targs, type_of_fundef f = Tfunction targs (Tint I32 Signed)).
    apply wt_program_main.
    eapply Genv.find_funct_ptr_symbol_inversion; eauto. 
  elim H1; clear H1; intros targs TYP.
  assert (targs = Tnil).
    inv H4; simpl in TYP.
    inv H5. injection TYP. rewrite <- H10. simpl. auto.
    inv TYP. inv H1. 
    destruct targs; simpl in H4. auto. inv H4. 
  subst targs.
  exploit function_ptr_translated; eauto. intros [tf [TFINDF TRANSLFD]].
  apply program_terminates with b tf m1.
  rewrite (symbols_preserved _ _ H).
  rewrite (transform_partial_program2_main transl_fundef transl_globvar prog H). auto.
  auto.
  generalize (transl_fundef_sig2 _ _ _ _ TRANSLFD TYP). simpl; auto.
  rewrite (@Genv.init_mem_transf_partial2 _ _ _ _ transl_fundef transl_globvar prog tprog H).
  generalize (transl_funcall_correct _ _ H0 H _ _ _ _ _ _ H4).
  intro. eapply H1. 
  eapply function_ptr_well_typed; eauto.
  auto.
  (* Divergence *)
  assert (exists targs, type_of_fundef f = Tfunction targs (Tint I32 Signed)).
    apply wt_program_main.
    eapply Genv.find_funct_ptr_symbol_inversion; eauto. 
  elim H1; clear H1; intros targs TYP.
  assert (targs = Tnil).
    inv H4; simpl in TYP.
    inv H5. injection TYP. rewrite <- H9. simpl. auto.
  subst targs.
  exploit function_ptr_translated; eauto. intros [tf [TFINDF TRANSLFD]].
  apply program_diverges with b tf.
  rewrite (symbols_preserved _ _ H).
  rewrite (transform_partial_program2_main transl_fundef transl_globvar prog H). auto.
  auto.
  generalize (transl_fundef_sig2 _ _ _ _ TRANSLFD TYP). simpl; auto.
  rewrite (@Genv.init_mem_transf_partial2 _ _ _ _ transl_fundef transl_globvar prog tprog H).
  eapply transl_funcall_divergence_correct; eauto. 
  eapply function_ptr_well_typed; eauto.
Qed.
