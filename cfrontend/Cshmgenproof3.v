(** * Correctness of the C front end, part 3: semantic preservation *)

Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import AST.
Require Import Values.
Require Import Events.
Require Import Mem.
Require Import Globalenvs.
Require Import Csyntax.
Require Import Csem.
Require Import Ctyping.
Require Import Csharpminor.
Require Import Cshmgen.
Require Import Cshmgenproof1.
Require Import Cshmgenproof2.

Section CORRECTNESS.

Variable prog: Csyntax.program.
Variable tprog: Csharpminor.program.
Hypothesis WTPROG: wt_program prog.
Hypothesis TRANSL: transl_program prog = Some tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall s, Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_symbol_transf_partial2 with transl_fundef transl_globvar.
  auto.
Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ transl_fundef f = Some tf.
Proof.
  intros. 
  generalize (Genv.find_funct_transf_partial2 transl_fundef transl_globvar TRANSL H).
  intros [A B]. 
  destruct (transl_fundef f). exists f0; split. assumption. auto. congruence.
Qed.

Lemma function_ptr_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = Some tf.
Proof.
  intros. 
  generalize (Genv.find_funct_ptr_transf_partial2 transl_fundef transl_globvar TRANSL H).
  intros [A B]. 
  destruct (transl_fundef f). exists f0; split. assumption. auto. congruence.
Qed.

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

(** ** Matching between environments *)

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
  forall ty vk, var_kind_of_type ty = Some vk -> match_var_kind ty vk.
Proof.
  intros; red. 
  caseEq (access_mode ty); auto.
  intros chunk AM. generalize (var_kind_by_value _ _ AM). congruence.
Qed.

Lemma match_env_alloc_variables:
  forall e1 m1 vars e2 m2 lb,
  Csem.alloc_variables e1 m1 vars e2 m2 lb ->
  forall tyenv te1 tvars,
  match_env tyenv e1 te1 ->
  transl_vars vars = Some tvars ->
  exists te2,
  Csharpminor.alloc_variables te1 m1 tvars te2 m2 lb
  /\ match_env (Ctyping.add_vars tyenv vars) e2 te2.
Proof.
  induction 1; intros.
  simpl in H0. inversion H0; subst; clear H0. 
  exists te1; split. constructor. simpl. auto.
  generalize H2. simpl. 
  caseEq (var_kind_of_type ty); [intros vk VK | congruence].
  caseEq (transl_vars vars); [intros tvrs TVARS | congruence].
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
  transl_params vars = Some tvars ->
  Csharpminor.bind_parameters te m1 tvars vals m2.
Proof.
  induction 1; intros.
  simpl in H1. inversion H1. constructor.
  generalize H4; clear H4; simpl. 
  caseEq (chunk_of_type ty); [intros chunk CHK | congruence].
  caseEq (transl_params params); [intros tparams TPARAMS | congruence].
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
  transl_params params = Some tvars ->
  Csharpminor.bind_parameters te m1 tvars vals m2.
Proof.
  intros. 
  eapply bind_parameters_match_rec; eauto.
  assert (list_norepet (var_names (params ++ vars))).
    unfold var_names. rewrite List.map_app. assumption.
  destruct (tyenv_add_vars_norepet _ tyenv H3) as [A B].
  intros. apply A. apply List.in_or_app. auto. 
Qed.

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
  map_partial transl_globvar vars = Some tvars ->
  match_globalenv (add_global_vars tenv vars) (globvarenv gv tvars).
Proof.
  induction vars; simpl.
  intros. inversion H0. assumption.
  destruct a as [[id init] ty]. intros until tvars; intro.
  caseEq (transl_globvar ty); try congruence. intros vk VK. 
  caseEq (map_partial transl_globvar vars); try congruence. intros tvars' EQ1 EQ2.
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
  unfold transl_program in TRANSL. functional inversion TRANSL. auto.
Qed.

(** ** Variable accessors *)

Lemma var_get_correct:
  forall e m id ty loc ofs v tyenv code te le,
  Csem.eval_lvalue ge e m (Expr (Csyntax.Evar id) ty) E0 m loc ofs ->
  load_value_of_type ty m loc ofs = Some v ->
  wt_expr tyenv (Expr (Csyntax.Evar id) ty) ->
  var_get id ty = Some code ->
  match_env tyenv e te ->
  eval_expr tprog le te m code E0 m v.
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

Lemma var_set_correct:
  forall e m id ty m1 loc ofs t1 m2 v t2 m3 tyenv code te rhs, 
  Csem.eval_lvalue ge e m (Expr (Csyntax.Evar id) ty) t1 m1 loc ofs ->
  store_value_of_type ty m2 loc ofs v = Some m3 ->
  wt_expr tyenv (Expr (Csyntax.Evar id) ty) ->
  var_set id ty rhs = Some code ->
  match_env tyenv e te ->
  eval_expr tprog nil te m1 rhs t2 m2 v ->
  exec_stmt tprog te m code (t1 ** t2) m3 Out_normal.
Proof.
  intros. inversion H1; subst; clear H1. 
  unfold store_value_of_type in H0.
  unfold var_set in H2. 
  caseEq (access_mode ty).
  (* access mode By_value *)
  intros chunk ACC. rewrite ACC in H0. rewrite ACC in H2. 
  inversion H2; clear H2; subst.
  inversion H; subst; clear H; rewrite E0_left.
    (* local variable *)
    exploit me_local; eauto. intros [vk [A B]].
    red in A; rewrite ACC in A; subst vk.
    eapply eval_Sassign. eauto. 
    eapply eval_var_ref_local. eauto. assumption. 
    (* global variable *)
    exploit me_global; eauto. intros [A B].
    eapply eval_Sassign. eauto.
    eapply eval_var_ref_global. auto. 
    fold tge. rewrite symbols_preserved. eauto.
    eauto. assumption. 
  (* access mode By_reference *)
  intros ACC. rewrite ACC in H0. discriminate.
  (* access mode By_nothing *)
  intros. rewrite H1 in H0; discriminate.
Qed.

(** ** Proof of semantic simulation *)

(** Inductive properties *)

Definition eval_expr_prop 
    (e: Csem.env) (m1: mem) (a: Csyntax.expr) (t: trace) (m2: mem) (v: val) : Prop :=
  forall tyenv ta te tle
    (WT: wt_expr tyenv a)
    (TR: transl_expr a = Some ta)
    (MENV: match_env tyenv e te),
  Csharpminor.eval_expr tprog tle te m1 ta t m2 v.

Definition eval_lvalue_prop
    (e: Csem.env) (m1: mem) (a: Csyntax.expr) (t: trace)
    (m2: mem) (b: block) (ofs: int) : Prop :=
  forall tyenv ta te tle
    (WT: wt_expr tyenv a)
    (TR: transl_lvalue a = Some ta)
    (MENV: match_env tyenv e te),
  Csharpminor.eval_expr tprog tle te m1 ta t m2 (Vptr b ofs).

Definition eval_exprlist_prop
    (e: Csem.env) (m1: mem) (al: Csyntax.exprlist) (t: trace)
    (m2: mem) (vl: list val) : Prop :=
  forall tyenv tal te tle
    (WT: wt_exprlist tyenv al)
    (TR: transl_exprlist al = Some tal)
    (MENV: match_env tyenv e te),
  Csharpminor.eval_exprlist tprog tle te m1 tal t m2 vl.

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
    (TR: transl_statement nbrk ncnt s = Some ts)   
    (MENV: match_env tyenv e te),
  Csharpminor.exec_stmt tprog te m1 ts t m2 (transl_outcome nbrk ncnt out).

Definition exec_lblstmts_prop
    (e: Csem.env) (m1: mem) (s: Csyntax.labeled_statements)
    (t: trace) (m2: mem) (out: Csem.outcome) : Prop :=
  forall tyenv nbrk ncnt body ts te m0 t0
    (WT: wt_lblstmts tyenv s)
    (TR: transl_lblstmts (lblstmts_length s)
                         (1 + lblstmts_length s + ncnt)
                         s body = Some ts)   
    (MENV: match_env tyenv e te)
    (BODY: Csharpminor.exec_stmt tprog te m0 body t0 m1 Out_normal),
  Csharpminor.exec_stmt tprog te m0 ts (t0 ** t) m2 
       (transl_outcome nbrk ncnt (outcome_switch out)).

Definition eval_funcall_prop
    (m1: mem) (f: Csyntax.fundef) (params: list val)
    (t: trace) (m2: mem) (res: val) : Prop :=
  forall tf
    (WT: wt_fundef (global_typenv prog) f)
    (TR: transl_fundef f = Some tf),
   Csharpminor.eval_funcall tprog m1 tf params t m2 res.

(*
Set Printing Depth 100.
Check (Csem.eval_funcall_ind6 ge eval_expr_prop eval_lvalue_prop
         eval_exprlist_prop exec_stmt_prop exec_lblstmts_prop eval_funcall_prop).
*)

Lemma transl_Econst_int_correct:
       (forall (e : Csem.env) (m : mem) (i : int) (ty : type),
        eval_expr_prop e m (Expr (Econst_int i) ty) E0 m (Vint i)).
Proof.
  intros; red; intros.
  monadInv TR. subst ta. apply make_intconst_correct.
Qed.

Lemma transl_Econst_float_correct:
       (forall (e : Csem.env) (m : mem) (f0 : float) (ty : type),
        eval_expr_prop e m (Expr (Econst_float f0) ty) E0 m (Vfloat f0)).
Proof.
  intros; red; intros.
  monadInv TR. subst ta. apply make_floatconst_correct.
Qed.

Lemma transl_Elvalue_correct:
       (forall (e : Csem.env) (m : mem) (a : expr_descr) (ty : type)
          (t : trace) (m1 : mem) (loc : block) (ofs : int) (v : val),
        eval_lvalue ge e m (Expr a ty) t m1 loc ofs ->
        eval_lvalue_prop e m (Expr a ty) t m1 loc ofs ->
        load_value_of_type ty m1 loc ofs = Some v ->
        eval_expr_prop e m (Expr a ty) t m1 v).
Proof.
  intros; red; intros.
  exploit transl_expr_lvalue; eauto. 
  intros [[id [EQ VARGET]] | [tb [TRLVAL MKLOAD]]].
  (* Case a is a variable *)
  subst a. 
  assert (t = E0 /\ m1 = m). inversion H; auto. 
  destruct H2; subst t m1.
  eapply var_get_correct; eauto.
  (* Case a is another lvalue *)
  eapply make_load_correct; eauto. 
Qed.

Lemma transl_Eaddrof_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr) (t : trace)
          (m1 : mem) (loc : block) (ofs : int) (ty : type),
        eval_lvalue ge e m a t m1 loc ofs ->
        eval_lvalue_prop e m a t m1 loc ofs ->
        eval_expr_prop e m (Expr (Csyntax.Eaddrof a) ty) t m1 (Vptr loc ofs)).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR. 
  eauto.
Qed.

Lemma transl_Esizeof_correct:
       (forall (e : Csem.env) (m : mem) (ty' ty : type),
        eval_expr_prop e m (Expr (Esizeof ty') ty) E0 m
          (Vint (Int.repr (Csyntax.sizeof ty')))).
Proof.
  intros; red; intros. monadInv TR. subst ta. apply make_intconst_correct. 
Qed.

Lemma transl_Eunop_correct:
       (forall (e : Csem.env) (m : mem) (op : unary_operation)
          (a : Csyntax.expr) (ty : type) (t : trace) (m1 : mem) (v1 v : val),
        Csem.eval_expr ge e m a t m1 v1 ->
        eval_expr_prop e m a t m1 v1 ->
        sem_unary_operation op v1 (typeof a) = Some v ->
        eval_expr_prop e m (Expr (Eunop op a) ty) t m1 v).
Proof.
  intros; red; intros.
  inversion WT; clear WT; subst.
  monadInv TR. 
  eapply transl_unop_correct; eauto. 
Qed.

Lemma transl_Ebinop_correct:
       (forall (e : Csem.env) (m : mem) (op : binary_operation)
          (a1 a2 : Csyntax.expr) (ty : type) (t1 : trace) (m1 : mem)
          (v1 : val) (t2 : trace) (m2 : mem) (v2 v : val),
        Csem.eval_expr ge e m a1 t1 m1 v1 ->
        eval_expr_prop e m a1 t1 m1 v1 ->
        Csem.eval_expr ge e m1 a2 t2 m2 v2 ->
        eval_expr_prop e m1 a2 t2 m2 v2 ->
        sem_binary_operation op v1 (typeof a1) v2 (typeof a2) m2 = Some v ->
        eval_expr_prop e m (Expr (Ebinop op a1 a2) ty) (t1 ** t2) m2 v).
Proof.
  intros; red; intros.
  inversion WT; clear WT; subst.
  monadInv TR. 
  eapply transl_binop_correct; eauto. 
Qed.

Lemma transl_Eorbool_1_correct:
       (forall (e : Csem.env) (m : mem) (a1 a2 : Csyntax.expr) (t : trace)
          (m1 : mem) (v1 : val) (ty : type),
        Csem.eval_expr ge e m a1 t m1 v1 ->
        eval_expr_prop e m a1 t m1 v1 ->
        is_true v1 (typeof a1) ->
        eval_expr_prop e m (Expr (Eorbool a1 a2) ty) t m1 Vtrue).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. monadInv TR.
  rewrite <- H3; unfold make_orbool.
  exploit make_boolean_correct_true; eauto. intros [vb [EVAL ISTRUE]].
  eapply eval_Econdition_true; eauto.
  unfold Vtrue; apply make_intconst_correct. traceEq.
Qed.

Lemma transl_Eorbool_2_correct:
       (forall (e : Csem.env) (m : mem) (a1 a2 : Csyntax.expr) (ty : type)
          (t1 : trace) (m1 : mem) (v1 : val) (t2 : trace) (m2 : mem)
          (v2 v : val),
        Csem.eval_expr ge e m a1 t1 m1 v1 ->
        eval_expr_prop e m a1 t1 m1 v1 ->
        is_false v1 (typeof a1) ->
        Csem.eval_expr ge e m1 a2 t2 m2 v2 ->
        eval_expr_prop e m1 a2 t2 m2 v2 ->
        bool_of_val v2 (typeof a2) v ->
        eval_expr_prop e m (Expr (Eorbool a1 a2) ty) (t1 ** t2) m2 v).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. monadInv TR.
  rewrite <- H6; unfold make_orbool.
  exploit make_boolean_correct_false. eapply H0; eauto. eauto. intros [vb [EVAL ISFALSE]].
  eapply eval_Econdition_false; eauto.
  inversion H4; subst.
  exploit make_boolean_correct_true. eapply H3; eauto. eauto. intros [vc [EVAL' ISTRUE']].
  eapply eval_Econdition_true; eauto. 
  unfold Vtrue; apply make_intconst_correct. traceEq.
  exploit make_boolean_correct_false. eapply H3; eauto. eauto. intros [vc [EVAL' ISFALSE']].
  eapply eval_Econdition_false; eauto.
  unfold Vfalse; apply make_intconst_correct. traceEq.
Qed.

Lemma transl_Eandbool_1_correct:
       (forall (e : Csem.env) (m : mem) (a1 a2 : Csyntax.expr) (t : trace)
          (m1 : mem) (v1 : val) (ty : type),
        Csem.eval_expr ge e m a1 t m1 v1 ->
        eval_expr_prop e m a1 t m1 v1 ->
        is_false v1 (typeof a1) ->
        eval_expr_prop e m (Expr (Eandbool a1 a2) ty) t m1 Vfalse).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. monadInv TR.
  rewrite <- H3; unfold make_andbool.
  exploit make_boolean_correct_false; eauto. intros [vb [EVAL ISFALSE]].
  eapply eval_Econdition_false; eauto.
  unfold Vfalse; apply make_intconst_correct. traceEq.
Qed.

Lemma transl_Eandbool_2_correct:
       (forall (e : Csem.env) (m : mem) (a1 a2 : Csyntax.expr) (ty : type)
          (t1 : trace) (m1 : mem) (v1 : val) (t2 : trace) (m2 : mem)
          (v2 v : val),
        Csem.eval_expr ge e m a1 t1 m1 v1 ->
        eval_expr_prop e m a1 t1 m1 v1 ->
        is_true v1 (typeof a1) ->
        Csem.eval_expr ge e m1 a2 t2 m2 v2 ->
        eval_expr_prop e m1 a2 t2 m2 v2 ->
        bool_of_val v2 (typeof a2) v ->
        eval_expr_prop e m (Expr (Eandbool a1 a2) ty) (t1 ** t2) m2 v).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. monadInv TR.
  rewrite <- H6; unfold make_andbool.
  exploit make_boolean_correct_true. eapply H0; eauto. eauto. intros [vb [EVAL ISTRUE]].
  eapply eval_Econdition_true; eauto.
  inversion H4; subst.
  exploit make_boolean_correct_true. eapply H3; eauto. eauto. intros [vc [EVAL' ISTRUE']].
  eapply eval_Econdition_true; eauto. 
  unfold Vtrue; apply make_intconst_correct. traceEq.
  exploit make_boolean_correct_false. eapply H3; eauto. eauto. intros [vc [EVAL' ISFALSE']].
  eapply eval_Econdition_false; eauto.
  unfold Vfalse; apply make_intconst_correct. traceEq.
Qed.

Lemma transl_Ecast_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr) (ty : type)
          (t : trace) (m1 : mem) (v1 v : val),
        Csem.eval_expr ge e m a t m1 v1 ->
        eval_expr_prop e m a t m1 v1 ->
        cast v1 (typeof a) ty v ->
        eval_expr_prop e m (Expr (Ecast ty a) ty) t m1 v).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. monadInv TR. subst ta.
  eapply make_cast_correct; eauto.
Qed.

Lemma transl_Ecall_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr)
          (bl : Csyntax.exprlist) (ty : type) (m3 : mem) (vres : val)
          (t1 : trace) (m1 : mem) (vf : val) (t2 : trace) (m2 : mem)
          (vargs : list val) (f : Csyntax.fundef) (t3 : trace),
        Csem.eval_expr ge e m a t1 m1 vf ->
        eval_expr_prop e m a t1 m1 vf ->
        Csem.eval_exprlist ge e m1 bl t2 m2 vargs ->
        eval_exprlist_prop e m1 bl t2 m2 vargs ->
        Genv.find_funct ge vf = Some f ->
        type_of_fundef f = typeof a ->
        Csem.eval_funcall ge m2 f vargs t3 m3 vres ->
        eval_funcall_prop m2 f vargs t3 m3 vres ->
        eval_expr_prop e m (Expr (Csyntax.Ecall a bl) ty) (t1 ** t2 ** t3) m3
          vres).
Proof.
  intros; red; intros.
  inversion WT; clear WT; subst.
  simpl in TR. 
  caseEq (classify_fun (typeof a)).
  2: intros; rewrite H7 in TR; discriminate.
  intros targs tres EQ. rewrite EQ in TR. 
  monadInv TR. clear TR. subst ta.
  rewrite <- H4 in EQ.
  exploit functions_translated; eauto. intros [tf [FIND TRL]].
  econstructor.
  eapply H0; eauto.
  eapply H2; eauto.
  eexact FIND. 
  eapply transl_fundef_sig1; eauto. 
  eapply H6; eauto. 
  eapply functions_well_typed; eauto.
  auto.
Qed.

Lemma transl_Evar_local_correct:
       (forall (e : Csem.env) (m : mem) (id : positive) (l : block)
          (ty : type),
        e ! id = Some l ->
        eval_lvalue_prop e m (Expr (Csyntax.Evar id) ty) E0 m l Int.zero).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. monadInv TR. subst ta.
  exploit (me_local _ _ _ MENV); eauto. intros [vk [A B]].
  econstructor. eapply eval_var_addr_local. eauto. 
Qed.

Lemma transl_Evar_global_correct:
       (forall (e : PTree.t block) (m : mem) (id : positive) (l : block)
          (ty : type),
        e ! id = None ->
        Genv.find_symbol ge id = Some l ->
        eval_lvalue_prop e m (Expr (Csyntax.Evar id) ty) E0 m l Int.zero).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. monadInv TR. subst ta.
  exploit (me_global _ _ _ MENV); eauto. intros [A B].
  econstructor. eapply eval_var_addr_global. eauto. 
  rewrite symbols_preserved. auto.
Qed.

Lemma transl_Ederef_correct:
       (forall (e : Csem.env) (m m1 : mem) (a : Csyntax.expr) (t : trace)
          (ofs : int) (ty : type) (l : block),
        Csem.eval_expr ge e m a t m1 (Vptr l ofs) ->
        eval_expr_prop e m a t m1 (Vptr l ofs) ->
        eval_lvalue_prop e m (Expr (Ederef a) ty) t m1 l ofs).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR. 
  eauto.
Qed.

Lemma transl_Eindex_correct:
       (forall (e : Csem.env) (m : mem) (a1 : Csyntax.expr) (t1 : trace)
          (m1 : mem) (v1 : val) (a2 : Csyntax.expr) (t2 : trace) (m2 : mem)
          (v2 : val) (l : block) (ofs : int) (ty : type),
        Csem.eval_expr ge e m a1 t1 m1 v1 ->
        eval_expr_prop e m a1 t1 m1 v1 ->
        Csem.eval_expr ge e m1 a2 t2 m2 v2 ->
        eval_expr_prop e m1 a2 t2 m2 v2 ->
        sem_add v1 (typeof a1) v2 (typeof a2) = Some (Vptr l ofs) ->
        eval_lvalue_prop e m (Expr (Eindex a1 a2) ty) (t1 ** t2) m2 l ofs).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR. monadInv TR.
  eapply (make_add_correct tprog); eauto. 
Qed.

Lemma transl_Efield_struct_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr) (t : trace)
          (m1 : mem) (l : block) (ofs : int) (id: ident) (fList : fieldlist) (i : ident)
          (ty : type) (delta : Z),
        eval_lvalue ge e m a t m1 l ofs ->
        eval_lvalue_prop e m a t m1 l ofs ->
        typeof a = Tstruct id fList ->
        field_offset i fList = Some delta ->
        eval_lvalue_prop e m (Expr (Efield a i) ty) t m1 l
          (Int.add ofs (Int.repr delta))).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. 
  simpl in TR. rewrite H1 in TR. monadInv TR.
  rewrite <- H5. eapply make_binop_correct; eauto.
  apply make_intconst_correct. 
  simpl. congruence. traceEq.
Qed.

Lemma transl_Efield_union_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr) (t : trace)
          (m1 : mem) (l : block) (ofs : int) (id: ident) (fList : fieldlist) (i : ident)
          (ty : type),
        eval_lvalue ge e m a t m1 l ofs ->
        eval_lvalue_prop e m a t m1 l ofs ->
        typeof a = Tunion id fList ->
        eval_lvalue_prop e m (Expr (Efield a i) ty) t m1 l ofs).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. 
  simpl in TR. rewrite H1 in TR. eauto.
Qed.

Lemma transl_Enil_correct:
       (forall (e : Csem.env) (m : mem),
        eval_exprlist_prop e m Csyntax.Enil E0 m nil).
Proof.
  intros; red; intros. monadInv TR. subst tal. constructor.
Qed.

Lemma transl_Econs_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr)
          (bl : Csyntax.exprlist) (t1 : trace) (m1 : mem) (v : val)
          (t2 : trace) (m2 : mem) (vl : list val),
        Csem.eval_expr ge e m a t1 m1 v ->
        eval_expr_prop e m a t1 m1 v ->
        Csem.eval_exprlist ge e m1 bl t2 m2 vl ->
        eval_exprlist_prop e m1 bl t2 m2 vl ->
        eval_exprlist_prop e m (Csyntax.Econs a bl) (t1 ** t2) m2 (v :: vl)).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR. 
  subst tal. econstructor; eauto. 
Qed.

Lemma transl_Sskip_correct:
       (forall (e : Csem.env) (m : mem),
        exec_stmt_prop e m Csyntax.Sskip E0 m Csem.Out_normal).
Proof.
  intros; red; intros. monadInv TR. subst ts. simpl. constructor.
Qed.

Lemma transl_Sexpr_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr) (t : trace)
          (m1 : mem) (v : val),
        Csem.eval_expr ge e m a t m1 v ->
        eval_expr_prop e m a t m1 v ->
        exec_stmt_prop e m (Csyntax.Sexpr a) t m1 Csem.Out_normal).
Proof.
  intros; red; intros; simpl. inversion WT; clear WT; subst. 
  monadInv TR. subst ts. 
  econstructor; eauto.
Qed.

Lemma transl_Sassign_correct:
       (forall (e : Csem.env) (m : mem) (a1 a2 : Csyntax.expr) (t1 : trace)
          (m1 : mem) (loc : block) (ofs : int) (t2 : trace) (m2 : mem)
          (v2 : val) (m3 : mem),
        eval_lvalue ge e m a1 t1 m1 loc ofs ->
        eval_lvalue_prop e m a1 t1 m1 loc ofs ->
        Csem.eval_expr ge e m1 a2 t2 m2 v2 ->
        eval_expr_prop e m1 a2 t2 m2 v2 ->
        store_value_of_type (typeof a1) m2 loc ofs v2 = Some m3 ->
        exec_stmt_prop e m (Csyntax.Sassign a1 a2) (t1 ** t2) m3
          Csem.Out_normal).
Proof.
  intros; red; intros.
  inversion WT; subst; clear WT.
  simpl in TR. 
  caseEq (is_variable a1).
  (* a = variable id *)
  intros id ISVAR. rewrite ISVAR in TR. 
  generalize (is_variable_correct _ _ ISVAR). intro EQ. 
  rewrite EQ in H; rewrite EQ in H0; rewrite EQ in H6.
  monadInv TR.
  eapply var_set_correct; eauto. 
  (* a is not a variable *)
  intro ISVAR; rewrite ISVAR in TR. monadInv TR.
  eapply make_store_correct; eauto.
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
  subst ts. red in H0; simpl in H0. eapply exec_Sseq_continue; eauto. 
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
  subst ts. eapply exec_Sseq_stop; eauto. 
  destruct out; simpl; congruence.
Qed.

Lemma transl_Sifthenelse_true_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr)
          (s1 s2 : statement) (t1 : trace) (m1 : mem) (v1 : val) (t2 : trace)
          (m2 : mem) (out : Csem.outcome),
        Csem.eval_expr ge e m a t1 m1 v1 ->
        eval_expr_prop e m a t1 m1 v1 ->
        is_true v1 (typeof a) ->
        Csem.exec_stmt ge e m1 s1 t2 m2 out ->
        exec_stmt_prop e m1 s1 t2 m2 out ->
        exec_stmt_prop e m (Csyntax.Sifthenelse a s1 s2) (t1 ** t2) m2 out).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  exploit make_boolean_correct_true. eapply H0; eauto. eauto. intros [vb [EVAL ISTRUE]].
  subst ts. eapply exec_Sifthenelse_true; eauto. 
Qed.

Lemma transl_Sifthenelse_false_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr)
          (s1 s2 : statement) (t1 : trace) (m1 : mem) (v1 : val) (t2 : trace)
          (m2 : mem) (out : Csem.outcome),
        Csem.eval_expr ge e m a t1 m1 v1 ->
        eval_expr_prop e m a t1 m1 v1 ->
        is_false v1 (typeof a) ->
        Csem.exec_stmt ge e m1 s2 t2 m2 out ->
        exec_stmt_prop e m1 s2 t2 m2 out ->
        exec_stmt_prop e m (Csyntax.Sifthenelse a s1 s2) (t1 ** t2) m2 out).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  exploit make_boolean_correct_false. eapply H0; eauto. eauto. intros [vb [EVAL ISFALSE]].
  subst ts. eapply exec_Sifthenelse_false; eauto. 
Qed.

Lemma transl_Sreturn_none_correct:
       (forall (e : Csem.env) (m : mem),
        exec_stmt_prop e m (Csyntax.Sreturn None) E0 m (Csem.Out_return None)).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  subst ts. simpl. apply exec_Sreturn_none. 
Qed.

Lemma transl_Sreturn_some_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr) (t : trace)
          (m1 : mem) (v : val),
        Csem.eval_expr ge e m a t m1 v ->
        eval_expr_prop e m a t m1 v ->
        exec_stmt_prop e m (Csyntax.Sreturn (Some a)) t m1
          (Csem.Out_return (Some v))).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  subst ts. simpl. eapply exec_Sreturn_some; eauto. 
Qed.

Lemma transl_Sbreak_correct:
       (forall (e : Csem.env) (m : mem),
        exec_stmt_prop e m Sbreak E0 m Out_break).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  subst ts. simpl. apply exec_Sexit.  
Qed.

Lemma transl_Scontinue_correct:
       (forall (e : Csem.env) (m : mem),
        exec_stmt_prop e m Scontinue E0 m Out_continue).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  subst ts. simpl. apply exec_Sexit.  
Qed.

Lemma exit_if_false_true:
  forall a ts e m1 t m2 v tyenv te,
  exit_if_false a = Some ts ->
  eval_expr_prop e m1 a t m2 v ->
  match_env tyenv e te ->
  wt_expr tyenv a ->
  is_true v (typeof a) ->
  exec_stmt tprog te m1 ts t m2 Out_normal.
Proof.
  intros. monadInv H. rewrite <- H5. 
  exploit make_boolean_correct_true. eapply H0; eauto. eauto.
  intros [vb [EVAL ISTRUE]].
  eapply exec_Sifthenelse_true with (v1 := vb); eauto. 
  constructor. traceEq.
Qed.
 
Lemma exit_if_false_false:
  forall a ts e m1 t m2 v tyenv te,
  exit_if_false a = Some ts ->
  eval_expr_prop e m1 a t m2 v ->
  match_env tyenv e te ->
  wt_expr tyenv a ->
  is_false v (typeof a) ->
  exec_stmt tprog te m1 ts t m2 (Out_exit 0).
Proof.
  intros. monadInv H. rewrite <- H5. 
  exploit make_boolean_correct_false. eapply H0; eauto. eauto.
  intros [vb [EVAL ISFALSE]].
  eapply exec_Sifthenelse_false with (v1 := vb); eauto. 
  constructor. traceEq.
Qed.

Lemma transl_Swhile_false_correct:
       (forall (e : Csem.env) (m : mem) (s : statement) (a : Csyntax.expr)
          (t : trace) (v : val) (m1 : mem),
        Csem.eval_expr ge e m a t m1 v ->
        eval_expr_prop e m a t m1 v ->
        is_false v (typeof a) ->
        exec_stmt_prop e m (Swhile a s) t m1 Csem.Out_normal).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  subst ts. simpl.
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
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr) (t1 : trace)
          (m1 : mem) (v : val) (s : statement) (m2 : mem) (t2 : trace)
          (out2 out : Csem.outcome),
        Csem.eval_expr ge e m a t1 m1 v ->
        eval_expr_prop e m a t1 m1 v ->
        is_true v (typeof a) ->
        Csem.exec_stmt ge e m1 s t2 m2 out2 ->
        exec_stmt_prop e m1 s t2 m2 out2 ->
        out_break_or_return out2 out ->
        exec_stmt_prop e m (Swhile a s) (t1 ** t2) m2 out).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  subst ts. rewrite (transl_out_break_or_return _ _ nbrk ncnt H4).
  apply exec_Sblock. apply exec_Sloop_stop. 
  eapply exec_Sseq_continue. 
  eapply exit_if_false_true; eauto. 
  apply exec_Sblock. eauto.
  auto. inversion H4; simpl; congruence.
Qed.

Lemma transl_Swhile_loop_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr) (t1 : trace)
          (m1 : mem) (v : val) (s : statement) (out2 out : Csem.outcome)
          (t2 : trace) (m2 : mem) (t3 : trace) (m3 : mem),
        Csem.eval_expr ge e m a t1 m1 v ->
        eval_expr_prop e m a t1 m1 v ->
        is_true v (typeof a) ->
        Csem.exec_stmt ge e m1 s t2 m2 out2 ->
        exec_stmt_prop e m1 s t2 m2 out2 ->
        out_normal_or_continue out2 ->
        Csem.exec_stmt ge e m2 (Swhile a s) t3 m3 out ->
        exec_stmt_prop e m2 (Swhile a s) t3 m3 out ->
        exec_stmt_prop e m (Swhile a s) (t1 ** t2 ** t3) m3 out).
Proof.
  intros; red; intros. 
  exploit H6; eauto. intro NEXTITER.
  inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  subst ts. 
  inversion NEXTITER; subst.
  apply exec_Sblock. 
  eapply exec_Sloop_loop. eapply exec_Sseq_continue.
  eapply exit_if_false_true; eauto. 
  rewrite (transl_out_normal_or_continue _ H4).
  apply exec_Sblock. eauto. 
  reflexivity. eassumption.
  traceEq.
Qed.

Lemma transl_Sdowhile_false_correct:
       (forall (e : Csem.env) (m : mem) (s : statement) (a : Csyntax.expr)
          (t1 : trace) (m1 : mem) (out1 : Csem.outcome) (v : val)
          (t2 : trace) (m2 : mem),
        Csem.exec_stmt ge e m s t1 m1 out1 ->
        exec_stmt_prop e m s t1 m1 out1 ->
        out_normal_or_continue out1 ->
        Csem.eval_expr ge e m1 a t2 m2 v ->
        eval_expr_prop e m1 a t2 m2 v ->
        is_false v (typeof a) ->
        exec_stmt_prop e m (Sdowhile a s) (t1 ** t2) m2 Csem.Out_normal).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  subst ts. simpl.
  change Out_normal with (outcome_block (Out_exit 0)).
  apply exec_Sblock. apply exec_Sloop_stop. eapply exec_Sseq_continue.
  rewrite (transl_out_normal_or_continue out1 H1).
  apply exec_Sblock. eauto. 
  eapply exit_if_false_false; eauto. auto. congruence. 
Qed.

Lemma transl_Sdowhile_stop_correct:
       (forall (e : Csem.env) (m : mem) (s : statement) (a : Csyntax.expr)
          (t : trace) (m1 : mem) (out1 out : Csem.outcome),
        Csem.exec_stmt ge e m s t m1 out1 ->
        exec_stmt_prop e m s t m1 out1 ->
        out_break_or_return out1 out ->
        exec_stmt_prop e m (Sdowhile a s) t m1 out).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  subst ts. simpl.
  assert (outcome_block (transl_outcome 1 0 out1) <> Out_normal).
    inversion H1; simpl; congruence.
  rewrite (transl_out_break_or_return _ _ nbrk ncnt H1). 
  apply exec_Sblock. apply exec_Sloop_stop. 
  apply exec_Sseq_stop. apply exec_Sblock. eauto. 
  auto. auto. 
Qed.

Lemma transl_Sdowhile_loop_correct:
       (forall (e : Csem.env) (m : mem) (s : statement) (a : Csyntax.expr)
          (m1 m2 m3 : mem) (t1 t2 t3 : trace) (out out1 : Csem.outcome)
          (v : val),
        Csem.exec_stmt ge e m s t1 m1 out1 ->
        exec_stmt_prop e m s t1 m1 out1 ->
        out_normal_or_continue out1 ->
        Csem.eval_expr ge e m1 a t2 m2 v ->
        eval_expr_prop e m1 a t2 m2 v ->
        is_true v (typeof a) ->
        Csem.exec_stmt ge e m2 (Sdowhile a s) t3 m3 out ->
        exec_stmt_prop e m2 (Sdowhile a s) t3 m3 out ->
        exec_stmt_prop e m (Sdowhile a s) (t1 ** t2 ** t3) m3 out).
Proof.
  intros; red; intros. 
  exploit H6; eauto. intro NEXTITER.
  inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  subst ts. 
  inversion NEXTITER; subst.
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
        Csem.exec_stmt ge e m a1 t1 m1 Csem.Out_normal ->
        exec_stmt_prop e m a1 t1 m1 Csem.Out_normal ->
        Csem.exec_stmt ge e m1 (Sfor Csyntax.Sskip a2 a3 s) t2 m2 out ->
        exec_stmt_prop e m1 (Sfor Csyntax.Sskip a2 a3 s) t2 m2 out ->
        exec_stmt_prop e m (Sfor a1 a2 a3 s) (t1 ** t2) m2 out).
Proof.
  intros; red; intros.
  exploit transl_stmt_Sfor_start; eauto. 
  intros [ts1 [ts2 [A [B C]]]].
  clear TR; subst ts. 
  inversion WT; subst.
  assert (WT': wt_stmt tyenv (Sfor Csyntax.Sskip a2 a3 s)).
    constructor; auto. constructor.
  exploit H0; eauto. simpl. intro EXEC1.
  exploit H2; eauto. intro EXEC2. 
  assert (EXEC3: exec_stmt tprog te m1 ts2 t2 m2 (transl_outcome nbrk ncnt out)).
    inversion EXEC2; subst.
    inversion H5; subst. rewrite E0_left; auto.
    inversion H11; subst. congruence.
  eapply exec_Sseq_continue; eauto. 
Qed.

Lemma transl_Sfor_false_correct:
       (forall (e : Csem.env) (m : mem) (s : statement) (a2 : Csyntax.expr)
          (a3 : statement) (t : trace) (v : val) (m1 : mem),
        Csem.eval_expr ge e m a2 t m1 v ->
        eval_expr_prop e m a2 t m1 v ->
        is_false v (typeof a2) ->
        exec_stmt_prop e m (Sfor Csyntax.Sskip a2 a3 s) t m1 Csem.Out_normal).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  subst ts. simpl.
  eapply exec_Sseq_continue. apply exec_Sskip.
  change Out_normal with (outcome_block (Out_exit 0)).
  apply exec_Sblock. apply exec_Sloop_stop. 
  apply exec_Sseq_stop. eapply exit_if_false_false; eauto. 
  congruence. congruence. traceEq. 
Qed.

Lemma transl_Sfor_stop_correct:
       (forall (e : Csem.env) (m : mem) (s : statement) (a2 : Csyntax.expr)
          (a3 : statement) (v : val) (m1 m2 : mem) (t1 t2 : trace)
          (out2 out : Csem.outcome),
        Csem.eval_expr ge e m a2 t1 m1 v ->
        eval_expr_prop e m a2 t1 m1 v ->
        is_true v (typeof a2) ->
        Csem.exec_stmt ge e m1 s t2 m2 out2 ->
        exec_stmt_prop e m1 s t2 m2 out2 ->
        out_break_or_return out2 out ->
        exec_stmt_prop e m (Sfor Csyntax.Sskip a2 a3 s) (t1 ** t2) m2 out).
Proof.
  intros; red; intros. inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  subst ts. simpl.
  assert (outcome_block (transl_outcome 1 0 out2) <> Out_normal).
    inversion H4; simpl; congruence.
  rewrite (transl_out_break_or_return _ _ nbrk ncnt H4). 
  eapply exec_Sseq_continue. apply exec_Sskip.
  apply exec_Sblock. apply exec_Sloop_stop. 
  eapply exec_Sseq_continue. eapply exit_if_false_true; eauto.
  apply exec_Sseq_stop. apply exec_Sblock. eauto. 
  auto. reflexivity. auto. traceEq. 
Qed.

Lemma transl_Sfor_loop_correct:
       (forall (e : Csem.env) (m : mem) (s : statement) (a2 : Csyntax.expr)
          (a3 : statement) (v : val) (m1 m2 m3 m4 : mem)
          (t1 t2 t3 t4 : trace) (out2 out : Csem.outcome),
        Csem.eval_expr ge e m a2 t1 m1 v ->
        eval_expr_prop e m a2 t1 m1 v ->
        is_true v (typeof a2) ->
        Csem.exec_stmt ge e m1 s t2 m2 out2 ->
        exec_stmt_prop e m1 s t2 m2 out2 ->
        out_normal_or_continue out2 ->
        Csem.exec_stmt ge e m2 a3 t3 m3 Csem.Out_normal ->
        exec_stmt_prop e m2 a3 t3 m3 Csem.Out_normal ->
        Csem.exec_stmt ge e m3 (Sfor Csyntax.Sskip a2 a3 s) t4 m4 out ->
        exec_stmt_prop e m3 (Sfor Csyntax.Sskip a2 a3 s) t4 m4 out ->
        exec_stmt_prop e m (Sfor Csyntax.Sskip a2 a3 s)
          (t1 ** t2 ** t3 ** t4) m4 out).
Proof.
  intros; red; intros. 
  exploit H8; eauto. intro NEXTITER.
  inversion WT; clear WT; subst. simpl in TR; monadInv TR.
  subst ts. 
  inversion NEXTITER; subst.
  inversion H11; subst.
  inversion H18; subst.   
  eapply exec_Sseq_continue. apply exec_Sskip.
  apply exec_Sblock. 
  eapply exec_Sloop_loop. eapply exec_Sseq_continue.
  eapply exit_if_false_true; eauto.
  eapply exec_Sseq_continue.
  rewrite (transl_out_normal_or_continue _ H4).
  apply exec_Sblock. eauto. 
  red in H6; simpl in H6; eauto.
  reflexivity. reflexivity. eassumption. 
  reflexivity. traceEq. 
  inversion H17. congruence.
Qed.

Lemma transl_lblstmts_switch:
  forall e m0 t1 m1 n nbrk ncnt tyenv te t2 m2 out sl body ts,
  exec_stmt tprog te m0 body t1 m1 
    (Out_exit (switch_target n (lblstmts_length sl) (switch_table sl 0))) ->
  transl_lblstmts 
    (lblstmts_length sl)
    (S (lblstmts_length sl + ncnt))
    sl (Sblock body) = Some ts ->
  wt_lblstmts tyenv sl ->
  match_env tyenv e te ->
  exec_lblstmts_prop e m1 (select_switch n sl) t2 m2 out ->
  Csharpminor.exec_stmt tprog te m0 ts (t1 ** t2) m2 
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
  eapply IHsl with (body := Sseq (Sblock body) s0); eauto.
  apply exec_Sseq_stop. 
  change (Out_exit (switch_target n (lblstmts_length sl) (switch_table sl 0)))
    with (outcome_block (Out_exit (S (switch_target n (lblstmts_length sl) (switch_table sl 0))))).
  apply exec_Sblock. 
  rewrite switch_target_table_shift in H. auto. congruence.
Qed.

Lemma transl_Sswitch_correct:
       (forall (e : Csem.env) (m : mem) (a : Csyntax.expr) (t1 : trace)
          (m1 : mem) (n : int) (sl : labeled_statements) (t2 : trace)
          (m2 : mem) (out : Csem.outcome),
        Csem.eval_expr ge e m a t1 m1 (Vint n) ->
        eval_expr_prop e m a t1 m1 (Vint n) ->
        exec_lblstmts ge e m1 (select_switch n sl) t2 m2 out ->
        exec_lblstmts_prop e m1 (select_switch n sl) t2 m2 out ->
        exec_stmt_prop e m (Csyntax.Sswitch a sl) (t1 ** t2) m2
          (outcome_switch out)).
Proof.
  intros; red; intros.
  inversion WT; clear WT; subst.
  simpl in TR. monadInv TR; clear TR. 
  rewrite length_switch_table in EQ0. 
  replace (ncnt + lblstmts_length sl + 1)%nat
     with (S (lblstmts_length sl + ncnt))%nat in EQ0 by omega.
  eapply transl_lblstmts_switch; eauto. 
  constructor. eapply H0; eauto. 
Qed.

Lemma transl_LSdefault_correct:
       (forall (e : Csem.env) (m : mem) (s : statement) (t : trace)
          (m1 : mem) (out : Csem.outcome),
        Csem.exec_stmt ge e m s t m1 out ->
        exec_stmt_prop e m s t m1 out ->
        exec_lblstmts_prop e m (LSdefault s) t m1 out).
Proof.
  intros; red; intros.
  inversion WT; subst.
  simpl in TR. monadInv TR.
  rewrite <- H3. 
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
  intros; red; intros.
  inversion WT; subst.
  simpl in TR. monadInv TR; clear TR.
  assert (exec_stmt tprog te m0 (Sblock (Sseq body s0)) 
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
  intros; red; intros.
  inversion WT; subst.
  simpl in TR. monadInv TR; clear TR.
  exploit H0; eauto. intro EXEC.
  destruct out; simpl; simpl in EXEC.
  (* out = Out_break *)
  change Out_normal with (outcome_block (Out_exit 0)).
  eapply transl_lblstmts_exit with (body := Sblock (Sseq body s0)); eauto.
  rewrite plus_0_r. 
  change (Out_exit (lblstmts_length ls))
    with (outcome_block (Out_exit (S (lblstmts_length ls)))).
  constructor. eapply exec_Sseq_continue; eauto.
  (* out = Out_continue *)
  change (Out_exit ncnt) with (outcome_block (Out_exit (S ncnt))).
  eapply transl_lblstmts_exit with (body := Sblock (Sseq body s0)); eauto.
  replace (Out_exit (lblstmts_length ls + S ncnt))
    with (outcome_block (Out_exit (S (S (lblstmts_length ls + ncnt))))).
  constructor. eapply exec_Sseq_continue; eauto.
  simpl. decEq. omega. 
  (* out = Out_normal *)
  congruence.
  (* out = Out_return *)
  eapply transl_lblstmts_return with (body := Sblock (Sseq body s0)); eauto.
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
  inversion WT; clear WT; subst. 
  inversion H6; clear H6; subst.
  (* Exploitation of translation hypothesis *)
  monadInv TR. subst tf. clear TR. 
  monadInv EQ. clear EQ. subst f0.
  (* Allocation of variables *)
  exploit match_env_alloc_variables; eauto.
  apply match_globalenv_match_env_empty. 
  apply match_global_typenv.
  eexact (transl_fn_variables _ _ (signature_of_function f) _ _ s EQ0 EQ1).
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
  monadInv TR. subst tf. constructor. auto.
Qed.

Theorem transl_funcall_correct:
  forall (m : mem) (f : Csyntax.fundef) (l : list val) (t : trace)
         (m0 : mem) (v : val),
  Csem.eval_funcall ge m f l t m0 v ->
  eval_funcall_prop m f l t m0 v.
Proof
  (Csem.eval_funcall_ind6 ge
         eval_expr_prop
         eval_lvalue_prop
         eval_exprlist_prop
         exec_stmt_prop
         exec_lblstmts_prop
         eval_funcall_prop

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
         transl_Ecall_correct
         transl_Evar_local_correct
         transl_Evar_global_correct
         transl_Ederef_correct
         transl_Eindex_correct
         transl_Efield_struct_correct
         transl_Efield_union_correct
         transl_Enil_correct
         transl_Econs_correct
         transl_Sskip_correct
         transl_Sexpr_correct
         transl_Sassign_correct
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

End CORRECTNESS.

(** Semantic preservation for whole programs. *)

Theorem transl_program_correct:
  forall prog tprog t r,
  transl_program prog = Some tprog ->
  Ctyping.wt_program prog ->
  Csem.exec_program prog t r ->
  Csharpminor.exec_program tprog t r.
Proof.
  intros until r. intros TRANSL WT [b [f [m1 [FINDS [FINDF EVAL]]]]].
  inversion WT; subst.

  assert (exists targs, type_of_fundef f = Tfunction targs (Tint I32 Signed)).
    apply wt_program_main.
    eapply Genv.find_funct_ptr_symbol_inversion; eauto. 
  elim H; clear H; intros targs TYP.
  assert (targs = Tnil).
    inversion EVAL; subst; simpl in TYP.
    inversion H0; subst. injection TYP. rewrite <- H6. simpl; auto.
    inversion TYP; subst targs0 tres. inversion H. simpl in H0. 
    inversion H0. destruct targs; simpl in H8; congruence.
  subst targs.
  exploit function_ptr_translated; eauto. intros [tf [TFINDF TRANSLFD]].
  exists b; exists tf; exists m1.
  split. 
    rewrite (symbols_preserved _ _ TRANSL).
    rewrite (transform_partial_program2_main transl_fundef transl_globvar prog TRANSL). auto.
  split. auto.
  split. 
    generalize (transl_fundef_sig2 _ _ _ _ TRANSLFD TYP). simpl; auto.
  rewrite (@Genv.init_mem_transf_partial2 _ _ _ _ transl_fundef transl_globvar prog tprog TRANSL).
  generalize (transl_funcall_correct _ _ WT TRANSL _ _ _ _ _ _ EVAL).
  intro. eapply H. 
  eapply function_ptr_well_typed; eauto.
  auto.
Qed.
