(** * Correctness of the C front end, part 1: syntactic properties *)

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
Require Import Csyntax.
Require Import Csem.
Require Import Ctyping.
Require Import Cminor.
Require Import Csharpminor.
Require Import Cshmgen.

(** * Properties of operations over types *)

Lemma transl_fundef_sig1:
  forall f tf args res,
  transl_fundef f = OK tf ->
  classify_fun (type_of_fundef f) = fun_case_f args res ->
  funsig tf = signature_of_type args res.
Proof.
  intros. destruct f; monadInv H. 
  monadInv EQ. simpl.  
  simpl in H0. inversion H0. reflexivity. 
  simpl. 
  simpl in H0. congruence.
Qed.

Lemma transl_fundef_sig2:
  forall f tf args res,
  transl_fundef f = OK tf ->
  type_of_fundef f = Tfunction args res ->
  funsig tf = signature_of_type args res.
Proof.
  intros. eapply transl_fundef_sig1; eauto.
  rewrite H0; reflexivity.
Qed.

Lemma var_kind_by_value:
  forall ty chunk,
  access_mode ty = By_value chunk ->
  var_kind_of_type ty = OK(Vscalar chunk).
Proof.
  intros ty chunk; destruct ty; simpl; try congruence.
  destruct i; try congruence; destruct s; congruence.
  destruct f; congruence.
Qed.

Lemma sizeof_var_kind_of_type:
  forall ty vk,
  var_kind_of_type ty = OK vk ->
  Csharpminor.sizeof vk = Csyntax.sizeof ty.
Proof.
  intros ty vk.
  assert (sizeof (Varray (Csyntax.sizeof ty)) = Csyntax.sizeof ty).
    simpl. rewrite Zmax_spec. apply zlt_false. 
    generalize (Csyntax.sizeof_pos ty). omega.
  destruct ty; try (destruct i; try destruct s); try (destruct f); 
  simpl; intro EQ; inversion EQ; subst vk; auto.
Qed.

(** * Properties of the translation functions *)

Lemma map_partial_names:
  forall (A B: Set) (f: A -> res B)
         (l: list (ident * A)) (tl: list (ident * B)),
  map_partial prefix_var_name f l = OK tl ->
  List.map (@fst ident B) tl = List.map (@fst ident A) l.
Proof.
  induction l; simpl.
  intros. inversion H. reflexivity.
  intro tl. destruct a as [id x]. destruct (f x); try congruence.
  caseEq (map_partial prefix_var_name f l); simpl; intros; try congruence.
  inv H0. simpl. decEq. auto.
Qed.
   
Lemma map_partial_append:
  forall (A B: Set) (f: A -> res B)
         (l1 l2: list (ident * A)) (tl1 tl2: list (ident * B)),
  map_partial prefix_var_name f l1 = OK tl1 ->
  map_partial prefix_var_name f l2 = OK tl2 ->
  map_partial prefix_var_name f (l1 ++ l2) = OK (tl1 ++ tl2).
Proof.
  induction l1; intros until tl2; simpl.
  intros. inversion H. simpl; auto.
  destruct a as [id x]. destruct (f x); try congruence.
  caseEq (map_partial prefix_var_name f l1); simpl; intros; try congruence.
  inv H0. rewrite (IHl1 _ _ _ H H1). auto.
Qed.
 
Lemma transl_params_names:
  forall vars tvars,
  transl_params vars = OK tvars ->
  List.map (@fst ident memory_chunk) tvars = Ctyping.var_names vars.
Proof.
  exact (map_partial_names _ _ chunk_of_type).
Qed.

Lemma transl_vars_names:
  forall vars tvars,
  transl_vars vars = OK tvars ->
  List.map (@fst ident var_kind) tvars = Ctyping.var_names vars.
Proof.
  exact (map_partial_names _ _ var_kind_of_type).
Qed.

Lemma transl_names_norepet:
  forall params vars sg tparams tvars body,
  list_norepet (var_names params ++ var_names vars) ->
  transl_params params = OK tparams ->
  transl_vars vars = OK tvars ->
  let f := Csharpminor.mkfunction sg tparams tvars body in
  list_norepet (fn_params_names f ++ fn_vars_names f).
Proof.
  intros. unfold fn_params_names, fn_vars_names, f. simpl.
  rewrite (transl_params_names _ _ H0).
  rewrite (transl_vars_names _ _ H1).
  auto.
Qed.

Lemma transl_vars_append:
  forall l1 l2 tl1 tl2,
  transl_vars l1 = OK tl1 -> transl_vars l2 = OK tl2 ->
  transl_vars (l1 ++ l2) = OK (tl1 ++ tl2).
Proof.
  exact (map_partial_append _ _ var_kind_of_type).
Qed.

Lemma transl_params_vars:
  forall params tparams,
  transl_params params = OK tparams ->
  transl_vars params =
  OK (List.map (fun id_chunk => (fst id_chunk, Vscalar (snd id_chunk))) tparams).
Proof.
  induction params; intro tparams; simpl.
  intros. inversion H. reflexivity.
  destruct a as [id x]. 
  unfold chunk_of_type. caseEq (access_mode x); try congruence.
  intros chunk AM. 
  caseEq (transl_params params); simpl; intros; try congruence.
  inv H0. 
  rewrite (var_kind_by_value _ _ AM). 
  rewrite (IHparams _ H). reflexivity.
Qed.

Lemma transl_fn_variables:
  forall params vars sg tparams tvars body,
  transl_params params = OK tparams ->
  transl_vars vars = OK tvars ->
  let f := Csharpminor.mkfunction sg tparams tvars body in
  transl_vars (params ++ vars) = OK (fn_variables f).
Proof.
  intros. 
  generalize (transl_params_vars _ _ H); intro.
  rewrite (transl_vars_append _ _ _ _ H1 H0).
  reflexivity.
Qed.

(** Transformation of expressions and statements. *)

Lemma is_variable_correct:
  forall a id,
  is_variable a = Some id ->
  a = Csyntax.Expr (Csyntax.Evar id) (typeof a).
Proof.
  intros until id. destruct a as [ad aty]; simpl. 
  destruct ad; intros; try discriminate.
  congruence.
Qed.

Lemma transl_expr_lvalue:
  forall ge e m1 a ty t m2 loc ofs ta,
  Csem.eval_lvalue ge e m1 (Expr a ty) t m2 loc ofs ->
  transl_expr (Expr a ty) = OK ta ->
  (exists id, a = Csyntax.Evar id /\ var_get id ty = OK ta) \/
  (exists tb, transl_lvalue (Expr a ty) = OK tb /\
              make_load tb ty = OK ta).
Proof.
  intros. inversion H; subst; clear H; simpl in H0.
  left; exists id; auto.
  left; exists id; auto.
  monadInv H0. right. exists x; split; auto. 
  simpl. monadInv H0. right. exists x1; split; auto. 
  simpl. rewrite EQ; rewrite EQ1. simpl. auto.
  rewrite H6 in H0. monadInv H0. right.  
  exists (Ebinop Oadd x (make_intconst (Int.repr x0))). split; auto.
  simpl. rewrite H6. rewrite EQ. rewrite EQ1. auto.
  rewrite H10 in H0. monadInv H0. right.
  exists x; split; auto. 
  simpl. rewrite H10. auto.
Qed.

Lemma transl_stmt_Sfor_start:
  forall nbrk ncnt s1 e2 s3 s4 ts,
  transl_statement nbrk ncnt (Sfor s1 e2 s3 s4) = OK ts ->
  exists ts1, exists ts2,
    ts = Sseq ts1 ts2
  /\ transl_statement nbrk ncnt s1 = OK ts1
  /\ transl_statement nbrk ncnt (Sfor Csyntax.Sskip e2 s3 s4) = OK (Sseq Sskip ts2).
Proof.
  intros. monadInv H. econstructor; econstructor.
  split. reflexivity. split. auto. simpl.
  rewrite EQ1; rewrite EQ0; rewrite EQ2; auto.
Qed.

(** Properties related to [switch] constructs. *)

Fixpoint lblstmts_length (sl: labeled_statements) : nat :=
  match sl with
  | LSdefault _ => 0%nat
  | LScase _ _ sl' => S (lblstmts_length sl')
  end.

Lemma switch_target_table_shift:
  forall n sl base dfl,
  switch_target n (S dfl) (switch_table sl (S base)) =
  S(switch_target n dfl (switch_table sl base)).
Proof.
  induction sl; intros; simpl.
  auto.
  case (Int.eq n i). auto. auto. 
Qed.

Lemma length_switch_table:
  forall sl base, List.length (switch_table sl base) = lblstmts_length sl.
Proof.
  induction sl; intro; simpl. auto. decEq; auto. 
Qed.


