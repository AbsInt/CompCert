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

(** Correctness of instruction selection *)

From Coq Require Import FunInd.
Require Import Coqlib Maps.
Require Import AST Linking Errors Integers.
Require Import Values Memory Builtins Events Globalenvs Smallstep.
Require Import Switch Cminor Op CminorSel Cminortyping.
Require Import SelectOp SelectDiv SplitLong SelectLong Selection.
Require Import SelectOpproof SelectDivproof SplitLongproof SelectLongproof.

Local Open Scope cminorsel_scope.
Local Open Scope error_monad_scope.

(** * Relational specification of instruction selection *)

Definition match_fundef (cunit: Cminor.program) (f: Cminor.fundef) (tf: CminorSel.fundef) : Prop :=
  exists hf, helper_functions_declared cunit hf /\ sel_fundef (prog_defmap cunit) hf f = OK tf.

Definition match_prog (p: Cminor.program) (tp: CminorSel.program) :=
  match_program match_fundef eq p tp.

(** Processing of helper functions *)

Lemma record_globdefs_sound:
  forall dm id gd, (record_globdefs dm)!id = Some gd -> dm!id = Some gd.
Proof.
  intros.
  set (f := fun m id gd => if globdef_of_interest gd then PTree.set id gd m else m) in *.
  set (P := fun m m' => m'!id = Some gd -> m!id = Some gd).
  assert (X: P dm (PTree.fold f dm (PTree.empty _))).
  { apply PTree_Properties.fold_rec.
  - unfold P; intros. rewrite <- H0; auto.
  - red. rewrite ! PTree.gempty. auto.
  - unfold P; intros. rewrite PTree.gsspec. unfold f in H3.
    destruct (globdef_of_interest v).
    + rewrite PTree.gsspec in H3. destruct (peq id k); auto.
    + apply H2 in H3. destruct (peq id k). congruence. auto. }
  apply X. auto.
Qed.

Lemma lookup_helper_correct_1:
  forall globs name sg id,
  lookup_helper globs name sg = OK id ->
  globs!id = Some (Gfun (External (EF_runtime name sg))).
Proof.
  intros.
  set (P := fun (m: PTree.t globdef) res => res = Some id -> m!id = Some(Gfun(External (EF_runtime name sg)))).
  assert (P globs (PTree.fold (lookup_helper_aux name sg) globs None)).
  { apply PTree_Properties.fold_rec; red; intros.
  - rewrite <- H0. apply H1; auto.
  - discriminate.
  - assert (EITHER: k = id /\ v = Gfun (External (EF_runtime name sg))
                \/  a = Some id).
    { unfold lookup_helper_aux in H3. destruct v; auto. destruct f; auto. destruct e; auto.
      destruct (String.string_dec name name0); auto.
      destruct (signature_eq sg sg0); auto.
      inversion H3. left; split; auto. repeat f_equal; auto. }
    destruct EITHER as [[X Y] | X].
    subst k v. apply PTree.gss.
    apply H2 in X. rewrite PTree.gso by congruence. auto.
  }
  red in H0. unfold lookup_helper in H.
  destruct (PTree.fold (lookup_helper_aux name sg) globs None); inv H. auto.
Qed.

Lemma lookup_helper_correct:
  forall p name sg id,
  lookup_helper (record_globdefs (prog_defmap p)) name sg = OK id ->
  helper_declared p id name sg.
Proof.
  intros. apply lookup_helper_correct_1 in H. apply record_globdefs_sound in H. auto.
Qed.

Lemma get_helpers_correct:
  forall p hf,
  get_helpers (prog_defmap p) = OK hf -> helper_functions_declared p hf.
Proof.
  intros. monadInv H. red; simpl. auto 20 using lookup_helper_correct.
Qed.

Theorem transf_program_match:
  forall p tp, sel_program p = OK tp -> match_prog p tp.
Proof.
  intros. monadInv H.
  eapply match_transform_partial_program_contextual. eexact EQ0.
  intros. exists x; split; auto. apply get_helpers_correct; auto.
Qed.

Lemma helper_functions_declared_linkorder:
  forall (p p': Cminor.program) hf,
  helper_functions_declared p hf -> linkorder p p' -> helper_functions_declared p' hf.
Proof.
  intros.
  assert (X: forall id name sg, helper_declared p id name sg -> helper_declared p' id name sg).
  { unfold helper_declared; intros.
    destruct (prog_defmap_linkorder _ _ _ _ H0 H1) as (gd & P & Q).
    inv Q. inv H3. auto. }
  red in H. decompose [Logic.and] H; clear H. red; auto 20.
Qed.

(** * Correctness of the instruction selection functions for expressions *)

Section PRESERVATION.

Variable prog: Cminor.program.
Variable tprog: CminorSel.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSF: match_prog prog tprog.

Lemma wt_prog : wt_program prog.
Proof.
  red; intros. destruct TRANSF as [A _].
  exploit list_forall2_in_left; eauto.
  intros ((i' & gd') & B & (C & D)). simpl in *. inv D. 
  destruct H2 as (hf & P & Q). destruct f; monadInv Q.
- monadInv EQ. econstructor; apply type_function_sound; eauto.
- constructor.
Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
Proof (Genv.senv_match TRANSF).

Lemma function_ptr_translated:
  forall (b: block) (f: Cminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cu tf, Genv.find_funct_ptr tge b = Some tf /\ match_fundef cu f tf /\ linkorder cu prog.
Proof (Genv.find_funct_ptr_match TRANSF).

Lemma functions_translated:
  forall (v v': val) (f: Cminor.fundef),
  Genv.find_funct ge v = Some f ->
  Val.lessdef v v' ->
  exists cu tf, Genv.find_funct tge v' = Some tf /\ match_fundef cu f tf /\ linkorder cu prog.
Proof.
  intros. inv H0.
  eapply Genv.find_funct_match; eauto.
  discriminate.
Qed.

Lemma sig_function_translated:
  forall cu f tf, match_fundef cu f tf -> funsig tf = Cminor.funsig f.
Proof.
  intros. destruct H as (hf & P & Q). destruct f; monadInv Q; auto. monadInv EQ; auto.
Qed.

Lemma stackspace_function_translated:
  forall dm hf f tf, sel_function dm hf f = OK tf -> fn_stackspace tf = Cminor.fn_stackspace f.
Proof.
  intros. monadInv H. auto.
Qed.

Lemma helper_functions_preserved:
  forall hf, helper_functions_declared prog hf -> helper_functions_declared tprog hf.
Proof.
  assert (X: forall id name sg, helper_declared prog id name sg -> helper_declared tprog id name sg).
  { unfold helper_declared; intros.
    generalize (match_program_defmap _ _ _ _ _ TRANSF id).
    unfold Cminor.fundef; rewrite H; intros R; inv R. inv H2.
    destruct H4 as (cu & A & B). monadInv B. auto. }
  unfold helper_functions_declared; intros. decompose [Logic.and] H; clear H. auto 20.
Qed.

Section CMCONSTR.

Variable cunit: Cminor.program.
Variable hf: helper_functions.
Hypothesis LINK: linkorder cunit prog.
Hypothesis HF: helper_functions_declared cunit hf.

Let HF': helper_functions_declared tprog hf.
Proof.
  apply helper_functions_preserved. eapply helper_functions_declared_linkorder; eauto.
Defined.

Variable sp: val.
Variable e: env.
Variable m: mem.

Lemma eval_condexpr_of_expr:
  forall a le v b,
  eval_expr tge sp e m le a v ->
  Val.bool_of_val v b ->
  eval_condexpr tge sp e m le (condexpr_of_expr a) b.
Proof.
  intros until a. functional induction (condexpr_of_expr a); intros.
(* compare *)
  inv H. econstructor; eauto.
  simpl in H6. inv H6. apply Val.bool_of_val_of_optbool. auto.
(* condition *)
  inv H. econstructor; eauto. destruct va; eauto.
(* let *)
  inv H. econstructor; eauto.
(* default *)
  econstructor. constructor. eauto. constructor.
  simpl. inv H0. auto.
Qed.

Lemma eval_condition_of_expr:
  forall a le v b,
  eval_expr tge sp e m le a v ->
  Val.bool_of_val v b ->
  exists vl,
     eval_exprlist tge sp e m le (snd (condition_of_expr a)) vl
  /\ eval_condition (fst (condition_of_expr a)) vl m = Some b.
Proof.
  intros a; functional induction (condition_of_expr a); intros; simpl.
- inv H. exists vl; split; auto.
  simpl in H6. inv H6. apply Val.bool_of_val_of_optbool in H0. auto.
- exists (v :: nil); split.
  constructor; auto; constructor.
  inv H0; simpl; auto.
Qed.

Lemma eval_load:
  forall le a v chunk v',
  eval_expr tge sp e m le a v ->
  Mem.loadv chunk m v = Some v' ->
  eval_expr tge sp e m le (load chunk a) v'.
Proof.
  intros. generalize H0; destruct v; simpl; intro; try discriminate.
  unfold load.
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (eq_refl _)).
  destruct (addressing chunk a). intros [vl [EV EQ]].
  eapply eval_Eload; eauto.
Qed.

Lemma eval_store:
  forall chunk a1 a2 v1 v2 f k m',
  eval_expr tge sp e m nil a1 v1 ->
  eval_expr tge sp e m nil a2 v2 ->
  Mem.storev chunk m v1 v2 = Some m' ->
  step tge (State f (store chunk a1 a2) k sp e m)
        E0 (State f Sskip k sp e m').
Proof.
  intros. generalize H1; destruct v1; simpl; intro; try discriminate.
  unfold store.
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (eq_refl _)).
  destruct (addressing chunk a1). intros [vl [EV EQ]].
  eapply step_store; eauto.
Qed.

(** Correctness of instruction selection for operators *)

Lemma eval_sel_unop:
  forall le op a1 v1 v,
  eval_expr tge sp e m le a1 v1 ->
  eval_unop op v1 = Some v ->
  exists v', eval_expr tge sp e m le (sel_unop op a1) v' /\ Val.lessdef v v'.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_cast8unsigned; auto.
  apply eval_cast8signed; auto.
  apply eval_cast16unsigned; auto.
  apply eval_cast16signed; auto.
  apply eval_negint; auto.
  apply eval_notint; auto.
  apply eval_negf; auto.
  apply eval_absf; auto.
  apply eval_negfs; auto.
  apply eval_absfs; auto.
  apply eval_singleoffloat; auto.
  apply eval_floatofsingle; auto.
  eapply eval_intoffloat; eauto.
  eapply eval_intuoffloat; eauto.
  eapply eval_floatofint; eauto.
  eapply eval_floatofintu; eauto.
  eapply eval_intofsingle; eauto.
  eapply eval_intuofsingle; eauto.
  eapply eval_singleofint; eauto.
  eapply eval_singleofintu; eauto.
  eapply eval_negl; eauto.
  eapply eval_notl; eauto.
  eapply eval_intoflong; eauto.
  eapply eval_longofint; eauto.
  eapply eval_longofintu; eauto.
  eapply eval_longoffloat; eauto.
  eapply eval_longuoffloat; eauto.
  eapply eval_floatoflong; eauto.
  eapply eval_floatoflongu; eauto.
  eapply eval_longofsingle; eauto.
  eapply eval_longuofsingle; eauto.
  eapply eval_singleoflong; eauto.
  eapply eval_singleoflongu; eauto.
Qed.

Lemma eval_sel_binop:
  forall le op a1 a2 v1 v2 v,
  eval_expr tge sp e m le a1 v1 ->
  eval_expr tge sp e m le a2 v2 ->
  eval_binop op v1 v2 m = Some v ->
  exists v', eval_expr tge sp e m le (sel_binop op a1 a2) v' /\ Val.lessdef v v'.
Proof.
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_add; auto.
  apply eval_sub; auto.
  apply eval_mul; auto.
  eapply eval_divs; eauto.
  eapply eval_divu; eauto.
  eapply eval_mods; eauto.
  eapply eval_modu; eauto.
  apply eval_and; auto.
  apply eval_or; auto.
  apply eval_xor; auto.
  apply eval_shl; auto.
  apply eval_shr; auto.
  apply eval_shru; auto.
  apply eval_addf; auto.
  apply eval_subf; auto.
  apply eval_mulf; auto.
  apply eval_divf; auto.
  apply eval_addfs; auto.
  apply eval_subfs; auto.
  apply eval_mulfs; auto.
  apply eval_divfs; auto.
  eapply eval_addl; eauto.
  eapply eval_subl; eauto.
  eapply eval_mull; eauto.
  eapply eval_divls; eauto.
  eapply eval_divlu; eauto.
  eapply eval_modls; eauto.
  eapply eval_modlu; eauto.
  eapply eval_andl; eauto.
  eapply eval_orl; eauto.
  eapply eval_xorl; eauto.
  eapply eval_shll; eauto.
  eapply eval_shrl; eauto.
  eapply eval_shrlu; eauto.
  apply eval_comp; auto.
  apply eval_compu; auto.
  apply eval_compf; auto.
  apply eval_compfs; auto.
  exists v; split; auto. eapply eval_cmpl; eauto.
  exists v; split; auto. eapply eval_cmplu; eauto.
Qed.

Lemma eval_sel_select:
  forall le a1 a2 a3 v1 v2 v3 b ty,
  eval_expr tge sp e m le a1 v1 ->
  eval_expr tge sp e m le a2 v2 ->
  eval_expr tge sp e m le a3 v3 ->
  Val.bool_of_val v1 b ->
  exists v, eval_expr tge sp e m le (sel_select ty a1 a2 a3) v
        /\  Val.lessdef (Val.select (Some b) v2 v3 ty) v.
Proof.
  unfold sel_select; intros.
  specialize (eval_condition_of_expr _ _ _ _ H H2).
  destruct (condition_of_expr a1) as [cond args]; simpl fst; simpl snd. intros (vl & A & B).
  destruct (select_supported ty) eqn:SUP.
- rewrite <- B. eapply eval_select; eauto. 
- exists (if b then v2 else v3); split.
  econstructor; eauto. eapply eval_condexpr_of_expr; eauto. destruct b; auto.
  apply Val.lessdef_normalize.
Qed.

(** Known built-in functions *)

Lemma eval_sel_known_builtin:
  forall bf args a vl v le,
  sel_known_builtin bf args = Some a ->
  eval_exprlist tge sp e m le args vl ->
  builtin_function_sem bf vl = Some v ->
  exists v', eval_expr tge sp e m le a v' /\ Val.lessdef v v'.
Proof.
  intros until le; intros SEL ARGS SEM.
  destruct bf as [bf|bf]; simpl in SEL.
- destruct bf; try discriminate.
+ (* select *)
  inv ARGS; try discriminate. inv H0; try discriminate. inv H2; try discriminate. inv H3; try discriminate.
  inv SEL.
  simpl in SEM. destruct v1; inv SEM.
  replace (Val.normalize (if Int.eq i Int.zero then v2 else v0) t)
     with (Val.select (Some (negb (Int.eq i Int.zero))) v0 v2 t)
       by (destruct (Int.eq i Int.zero); reflexivity).
  eapply eval_sel_select; eauto. constructor.
+ (* fabs *)
  inv ARGS; try discriminate. inv H0; try discriminate.
  inv SEL.  
  simpl in SEM; inv SEM. apply eval_absf; auto.
+ (* fabsf *)
  inv ARGS; try discriminate. inv H0; try discriminate.
  inv SEL.  
  simpl in SEM; inv SEM. apply eval_absfs; auto.
- eapply eval_platform_builtin; eauto.
Qed.

End CMCONSTR.

(** Recognition of calls to built-in functions *)

Lemma expr_is_addrof_ident_correct:
  forall e id,
  expr_is_addrof_ident e = Some id ->
  e = Cminor.Econst (Cminor.Oaddrsymbol id Ptrofs.zero).
Proof.
  intros e id. unfold expr_is_addrof_ident.
  destruct e; try congruence.
  destruct c; try congruence.
  predSpec Ptrofs.eq Ptrofs.eq_spec i0 Ptrofs.zero; congruence.
Qed.

Lemma classify_call_correct:
  forall unit sp e m a v fd,
  linkorder unit prog ->
  Cminor.eval_expr ge sp e m a v ->
  Genv.find_funct ge v = Some fd ->
  match classify_call (prog_defmap unit) a with
  | Call_default => True
  | Call_imm id => exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Ptrofs.zero
  | Call_builtin ef => fd = External ef
  end.
Proof.
  unfold classify_call; intros.
  destruct (expr_is_addrof_ident a) as [id|] eqn:EA; auto.
  exploit expr_is_addrof_ident_correct; eauto. intros EQ; subst a.
  inv H0. inv H3. unfold Genv.symbol_address in *.
  destruct (Genv.find_symbol ge id) as [b|] eqn:FS; try discriminate.
  rewrite Genv.find_funct_find_funct_ptr in H1.
  assert (DFL: exists b1, Genv.find_symbol ge id = Some b1 /\ Vptr b Ptrofs.zero = Vptr b1 Ptrofs.zero) by (exists b; auto).
  unfold globdef; destruct (prog_defmap unit)!id as [[[f|ef] |gv] |] eqn:G; auto.
  destruct (ef_inline ef) eqn:INLINE; auto.
  destruct (prog_defmap_linkorder _ _ _ _ H G) as (gd & P & Q).
  inv Q. inv H2.
- apply Genv.find_def_symbol in P. destruct P as (b' & X & Y). fold ge in X, Y.
  rewrite <- Genv.find_funct_ptr_iff in Y. congruence.
- simpl in INLINE. discriminate.
Qed.

(** Translation of [switch] statements *)

Inductive Rint: Z -> val -> Prop :=
  | Rint_intro: forall n, Rint (Int.unsigned n) (Vint n).

Inductive Rlong: Z -> val -> Prop :=
  | Rlong_intro: forall n, Rlong (Int64.unsigned n) (Vlong n).

Section SEL_SWITCH.

Variable make_cmp_eq: expr -> Z -> expr.
Variable make_cmp_ltu: expr -> Z -> expr.
Variable make_sub: expr -> Z -> expr.
Variable make_to_int: expr -> expr.
Variable modulus: Z.
Variable R: Z -> val -> Prop.

Hypothesis eval_make_cmp_eq: forall sp e m le a v i n,
  eval_expr tge sp e m le a v -> R i v -> 0 <= n < modulus ->
  eval_expr tge sp e m le (make_cmp_eq a n) (Val.of_bool (zeq i n)).
Hypothesis eval_make_cmp_ltu: forall sp e m le a v i n,
  eval_expr tge sp e m le a v -> R i v -> 0 <= n < modulus ->
  eval_expr tge sp e m le (make_cmp_ltu a n) (Val.of_bool (zlt i n)).
Hypothesis eval_make_sub: forall sp e m le a v i n,
  eval_expr tge sp e m le a v -> R i v -> 0 <= n < modulus ->
  exists v', eval_expr tge sp e m le (make_sub a n) v' /\ R ((i - n) mod modulus) v'.
Hypothesis eval_make_to_int: forall sp e m le a v i,
  eval_expr tge sp e m le a v -> R i v ->
  exists v', eval_expr tge sp e m le (make_to_int a) v' /\ Rint (i mod Int.modulus) v'.

Lemma sel_switch_correct_rec:
  forall sp e m varg i x,
  R i varg ->
  forall t arg le,
  wf_comptree modulus t ->
  nth_error le arg = Some varg ->
  comptree_match modulus i t = Some x ->
  eval_exitexpr tge sp e m le (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg t) x.
Proof.
  intros until x; intros Ri. induction t; simpl; intros until le; intros WF ARG MATCH.
- (* base case *)
  inv MATCH. constructor.
- (* eq test *)
  inv WF.
  assert (eval_expr tge sp e m le (make_cmp_eq (Eletvar arg) key) (Val.of_bool (zeq i key))).
  { eapply eval_make_cmp_eq; eauto. constructor; auto. }
  eapply eval_XEcondition with (va := zeq i key).
  eapply eval_condexpr_of_expr; eauto. destruct (zeq i key); constructor; auto.
  destruct (zeq i key); simpl.
  + inv MATCH. constructor.
  + eapply IHt; eauto.
- (* lt test *)
  inv WF.
  assert (eval_expr tge sp e m le (make_cmp_ltu (Eletvar arg) key) (Val.of_bool (zlt i key))).
  { eapply eval_make_cmp_ltu; eauto. constructor; auto. }
  eapply eval_XEcondition with (va := zlt i key).
  eapply eval_condexpr_of_expr; eauto. destruct (zlt i key); constructor; auto.
  destruct (zlt i key); simpl.
  + eapply IHt1; eauto.
  + eapply IHt2; eauto.
- (* jump table *)
  inv WF.
  exploit (eval_make_sub sp e m le). eapply eval_Eletvar. eauto. eauto.
  instantiate (1 := ofs). auto.
  intros (v' & A & B).
  set (i' := (i - ofs) mod modulus) in *.
  assert (eval_expr tge sp e m (v' :: le) (make_cmp_ltu (Eletvar O) sz) (Val.of_bool (zlt i' sz))).
  { eapply eval_make_cmp_ltu; eauto. constructor; auto. }
  econstructor. eauto.
  eapply eval_XEcondition with (va := zlt i' sz).
  eapply eval_condexpr_of_expr; eauto. destruct (zlt i' sz); constructor; auto.
  destruct (zlt i' sz); simpl.
  + exploit (eval_make_to_int sp e m (v' :: le) (Eletvar O)).
    constructor. simpl; eauto. eauto. intros (v'' & C & D). inv D.
    econstructor; eauto. congruence.
  + eapply IHt; eauto.
Qed.

Lemma sel_switch_correct:
  forall dfl cases arg sp e m varg i t le,
  validate_switch modulus dfl cases t = true ->
  eval_expr tge sp e m le arg varg ->
  R i varg ->
  0 <= i < modulus ->
  eval_exitexpr tge sp e m le
     (XElet arg (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int O t))
     (switch_target i dfl cases).
Proof.
  intros. exploit validate_switch_correct; eauto. lia. intros [A B].
  econstructor. eauto. eapply sel_switch_correct_rec; eauto.
Qed.

End SEL_SWITCH.

Section SEL_SWITCH_INT.

Variable cunit: Cminor.program.
Variable hf: helper_functions.
Hypothesis LINK: linkorder cunit prog.
Hypothesis HF: helper_functions_declared cunit hf.

Let HF': helper_functions_declared tprog hf.
Proof.
  apply helper_functions_preserved. eapply helper_functions_declared_linkorder; eauto.
Defined.

Lemma sel_switch_int_correct:
  forall dfl cases arg sp e m i t le,
  validate_switch Int.modulus dfl cases t = true ->
  eval_expr tge sp e m le arg (Vint i) ->
  eval_exitexpr tge sp e m le (XElet arg (sel_switch_int O t)) (switch_target (Int.unsigned i) dfl cases).
Proof.
  assert (INTCONST: forall n sp e m le,
            eval_expr tge sp e m le (Eop (Ointconst n) Enil) (Vint n)).
  { intros. econstructor. constructor. auto. }
  intros. eapply sel_switch_correct with (R := Rint); eauto.
- intros until n; intros EVAL R RANGE.
  exploit eval_comp. eexact EVAL. apply (INTCONST (Int.repr n)).
  instantiate (1 := Ceq). intros (vb & A & B).
  inv R. unfold Val.cmp in B. simpl in B. revert B.
  predSpec Int.eq Int.eq_spec n0 (Int.repr n); intros B; inv B.
  rewrite Int.unsigned_repr. unfold proj_sumbool; rewrite zeq_true; auto.
  unfold Int.max_unsigned; lia.
  unfold proj_sumbool; rewrite zeq_false; auto.
  red; intros; elim H1. rewrite <- (Int.repr_unsigned n0). congruence.
- intros until n; intros EVAL R RANGE.
  exploit eval_compu. eexact EVAL. apply (INTCONST (Int.repr n)).
  instantiate (1 := Clt). intros (vb & A & B).
  inv R. unfold Val.cmpu in B. simpl in B.
  unfold Int.ltu in B. rewrite Int.unsigned_repr in B.
  destruct (zlt (Int.unsigned n0) n); inv B; auto.
  unfold Int.max_unsigned; lia.
- intros until n; intros EVAL R RANGE.
  exploit eval_sub. eexact EVAL. apply (INTCONST (Int.repr n)). intros (vb & A & B).
  inv R. simpl in B. inv B. econstructor; split; eauto.
  replace ((Int.unsigned n0 - n) mod Int.modulus)
     with (Int.unsigned (Int.sub n0 (Int.repr n))).
  constructor.
  unfold Int.sub. rewrite Int.unsigned_repr_eq. f_equal. f_equal.
  apply Int.unsigned_repr. unfold Int.max_unsigned; lia.
- intros until i0; intros EVAL R. exists v; split; auto.
  inv R. rewrite Z.mod_small by (apply Int.unsigned_range). constructor.
- constructor.
- apply Int.unsigned_range.
Qed.

Lemma sel_switch_long_correct:
  forall dfl cases arg sp e m i t le,
  validate_switch Int64.modulus dfl cases t = true ->
  eval_expr tge sp e m le arg (Vlong i) ->
  eval_exitexpr tge sp e m le (XElet arg (sel_switch_long O t)) (switch_target (Int64.unsigned i) dfl cases).
Proof.
  intros. eapply sel_switch_correct with (R := Rlong); eauto.
- intros until n; intros EVAL R RANGE.
  eapply eval_cmpl. eexact EVAL. apply eval_longconst with (n := Int64.repr n).
  inv R. unfold Val.cmpl. simpl. f_equal; f_equal. unfold Int64.eq.
  rewrite Int64.unsigned_repr. destruct (zeq (Int64.unsigned n0) n); auto.
  unfold Int64.max_unsigned; lia.
- intros until n; intros EVAL R RANGE.
  eapply eval_cmplu; auto. eexact EVAL. apply eval_longconst with (n := Int64.repr n).
  inv R. unfold Val.cmplu. simpl. f_equal; f_equal. unfold Int64.ltu.
  rewrite Int64.unsigned_repr. destruct (zlt (Int64.unsigned n0) n); auto.
  unfold Int64.max_unsigned; lia.
- intros until n; intros EVAL R RANGE.
  exploit eval_subl; auto; try apply HF'. eexact EVAL. apply eval_longconst with (n := Int64.repr n).
  intros (vb & A & B).
  inv R. simpl in B. inv B. econstructor; split; eauto.
  replace ((Int64.unsigned n0 - n) mod Int64.modulus)
     with (Int64.unsigned (Int64.sub n0 (Int64.repr n))).
  constructor.
  unfold Int64.sub. rewrite Int64.unsigned_repr_eq. f_equal. f_equal.
  apply Int64.unsigned_repr. unfold Int64.max_unsigned; lia.
- intros until i0; intros EVAL R.
  exploit eval_lowlong. eexact EVAL. intros (vb & A & B).
  inv R. simpl in B. inv B. econstructor; split; eauto.
  replace (Int64.unsigned n mod Int.modulus) with (Int.unsigned (Int64.loword n)).
  constructor.
  unfold Int64.loword. apply Int.unsigned_repr_eq.
- constructor.
- apply Int64.unsigned_range.
Qed.

End SEL_SWITCH_INT.

(** Compatibility of evaluation functions with the "less defined than" relation. *)

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, Some ?x = Some v /\ _ ] => exists x; split; auto
  | _ => idtac
  end.

Lemma eval_unop_lessdef:
  forall op v1 v1' v,
  eval_unop op v1 = Some v -> Val.lessdef v1 v1' ->
  exists v', eval_unop op v1' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until v; intros EV LD. inv LD.
  exists v; auto.
  destruct op; simpl in *; inv EV; TrivialExists.
Qed.

Lemma eval_binop_lessdef:
  forall op v1 v1' v2 v2' v m m',
  eval_binop op v1 v2 m = Some v ->
  Val.lessdef v1 v1' -> Val.lessdef v2 v2' -> Mem.extends m m' ->
  exists v', eval_binop op v1' v2' m' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until m'; intros EV LD1 LD2 ME.
  assert (exists v', eval_binop op v1' v2' m = Some v' /\ Val.lessdef v v').
  { inv LD1. inv LD2. exists v; auto.
    destruct op; destruct v1'; simpl in *; inv EV; TrivialExists.
    destruct op; simpl in *; inv EV; TrivialExists. }
  assert (CMPU: forall c,
    eval_binop (Ocmpu c) v1 v2 m = Some v ->
    exists v' : val, eval_binop (Ocmpu c) v1' v2' m' = Some v' /\ Val.lessdef v v').
  { intros c A. simpl in *. inv A. econstructor; split. eauto.
    apply Val.of_optbool_lessdef.
    intros. apply Val.cmpu_bool_lessdef with (Mem.valid_pointer m) v1 v2; auto.
    intros; eapply Mem.valid_pointer_extends; eauto. }
  assert (CMPLU: forall c,
    eval_binop (Ocmplu c) v1 v2 m = Some v ->
    exists v' : val, eval_binop (Ocmplu c) v1' v2' m' = Some v' /\ Val.lessdef v v').
  { intros c A. simpl in *. unfold Val.cmplu in *.
    destruct (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2) as [b|] eqn:C; simpl in A; inv A.
    eapply Val.cmplu_bool_lessdef with (valid_ptr' := (Mem.valid_pointer m')) in C;
    eauto using Mem.valid_pointer_extends.
    rewrite C. exists (Val.of_bool b); auto. }
  destruct op; auto.
Qed.

(** * Semantic preservation for instruction selection. *)

(** Relationship between the local environments. *)

Definition env_lessdef (e1 e2: env) : Prop :=
  forall id v1, e1!id = Some v1 -> exists v2, e2!id = Some v2 /\ Val.lessdef v1 v2.

Lemma set_var_lessdef:
  forall e1 e2 id v1 v2,
  env_lessdef e1 e2 -> Val.lessdef v1 v2 ->
  env_lessdef (PTree.set id v1 e1) (PTree.set id v2 e2).
Proof.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  exists v2; split; congruence.
  auto.
Qed.

Lemma set_optvar_lessdef:
  forall e1 e2 optid v1 v2,
  env_lessdef e1 e2 -> Val.lessdef v1 v2 ->
  env_lessdef (set_optvar optid v1 e1) (set_optvar optid v2 e2).
Proof.
  unfold set_optvar; intros. destruct optid; auto. apply set_var_lessdef; auto.
Qed.

Lemma set_params_lessdef:
  forall il vl1 vl2,
  Val.lessdef_list vl1 vl2 ->
  env_lessdef (set_params vl1 il) (set_params vl2 il).
Proof.
  induction il; simpl; intros.
  red; intros. rewrite PTree.gempty in H0; congruence.
  inv H; apply set_var_lessdef; auto.
Qed.

Lemma set_locals_lessdef:
  forall e1 e2, env_lessdef e1 e2 ->
  forall il, env_lessdef (set_locals il e1) (set_locals il e2).
Proof.
  induction il; simpl. auto. apply set_var_lessdef; auto.
Qed.

(** Semantic preservation for expressions. *)

Section EXPRESSIONS.

Variable cunit: Cminor.program.
Variable hf: helper_functions.
Hypothesis LINK: linkorder cunit prog.
Hypothesis HF: helper_functions_declared cunit hf.

Lemma sel_expr_correct:
  forall sp e m a v,
  Cminor.eval_expr ge sp e m a v ->
  forall e' le m',
  env_lessdef e e' -> Mem.extends m m' ->
  exists v', eval_expr tge sp e' m' le (sel_expr a) v' /\ Val.lessdef v v'.
Proof.
  induction 1; intros; simpl.
  (* Evar *)
  exploit H0; eauto. intros [v' [A B]]. exists v'; split; auto. constructor; auto.
  (* Econst *)
  destruct cst; simpl in *; inv H.
  exists (Vint i); split; auto. econstructor. constructor. auto.
  exists (Vfloat f); split; auto. econstructor. constructor. auto.
  exists (Vsingle f); split; auto. econstructor. constructor. auto.
  exists (Vlong i); split; auto. apply eval_longconst.
  unfold Genv.symbol_address; rewrite <- symbols_preserved; fold (Genv.symbol_address tge i i0). apply eval_addrsymbol.
  apply eval_addrstack.
  (* Eunop *)
  exploit IHeval_expr; eauto. intros [v1' [A B]].
  exploit eval_unop_lessdef; eauto. intros [v' [C D]].
  exploit eval_sel_unop; eauto. intros [v'' [E F]].
  exists v''; split; eauto. eapply Val.lessdef_trans; eauto.
  (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [v1' [A B]].
  exploit IHeval_expr2; eauto. intros [v2' [C D]].
  exploit eval_binop_lessdef; eauto. intros [v' [E F]].
  assert (G: exists v'', eval_expr tge sp e' m' le (sel_binop op (sel_expr a1) (sel_expr a2)) v'' /\ Val.lessdef v' v'')
  by (eapply eval_sel_binop; eauto).
  destruct G as [v'' [P Q]].
  exists v''; split; eauto. eapply Val.lessdef_trans; eauto.
  (* Eload *)
  exploit IHeval_expr; eauto. intros [vaddr' [A B]].
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  exists v'; split; auto. eapply eval_load; eauto.
Qed.

Lemma sel_exprlist_correct:
  forall sp e m a v,
  Cminor.eval_exprlist ge sp e m a v ->
  forall e' le m',
  env_lessdef e e' -> Mem.extends m m' ->
  exists v', eval_exprlist tge sp e' m' le (sel_exprlist a) v' /\ Val.lessdef_list v v'.
Proof.
  induction 1; intros; simpl.
  exists (@nil val); split; auto. constructor.
  exploit sel_expr_correct; eauto. intros [v1' [A B]].
  exploit IHeval_exprlist; eauto. intros [vl' [C D]].
  exists (v1' :: vl'); split; auto. constructor; eauto.
Qed.

Lemma sel_select_expr_correct:
  forall ty cond a1 a2 sp e m vcond v1 v2 b e' m' le,
  SelectOp.select_supported ty = true ->
  Cminor.eval_expr ge sp e m cond vcond ->
  Cminor.eval_expr ge sp e m a1 v1 ->
  Cminor.eval_expr ge sp e m a2 v2 ->
  Val.bool_of_val vcond b ->
  env_lessdef e e' -> Mem.extends m m' ->
  exists v', eval_expr tge sp e' m' le (sel_select_expr ty cond a1 a2) v'
          /\ Val.lessdef (Val.select (Some b) v1 v2 ty) v'.
Proof.
  unfold sel_select_expr; intros. 
  destruct (condition_of_expr (sel_expr cond)) as [cnd args] eqn:C.
  exploit sel_expr_correct. eexact H0. eauto. eauto. intros (vcond' & EVC & LDC).
  exploit sel_expr_correct. eexact H1. eauto. eauto. intros (v1' & EV1 & LD1).
  exploit sel_expr_correct. eexact H2. eauto. eauto. intros (v2' & EV2 & LD2).
  assert (Val.bool_of_val vcond' b) by (inv H3; inv LDC; constructor).
  exploit eval_condition_of_expr. eexact EVC. eauto. rewrite C. intros (vargs' & EVARGS & EVCOND).
  exploit (eval_select tge sp e' m' le ty cnd args vargs' (sel_expr a1) v1' (sel_expr a2) v2'); eauto.
  simpl in EVCOND; rewrite EVCOND. intros (v' & X & Y). 
  exists v'; split; eauto. 
  eapply Val.lessdef_trans; [|eexact Y].
  apply Val.normalize_lessdef. destruct b; auto.
Qed.

Lemma sel_builtin_arg_correct:
  forall sp e e' m m' a v c,
  env_lessdef e e' -> Mem.extends m m' ->
  Cminor.eval_expr ge sp e m a v ->
  exists v',
     CminorSel.eval_builtin_arg tge sp e' m' (sel_builtin_arg a c) v'
  /\ Val.lessdef v v'.
Proof.
  intros. unfold sel_builtin_arg.
  exploit sel_expr_correct; eauto. intros (v1 & A & B).
  exists v1; split; auto.
  destruct (builtin_arg_ok (builtin_arg (sel_expr a)) c).
  apply eval_builtin_arg; eauto.
  constructor; auto.
Qed.

Lemma sel_builtin_args_correct:
  forall sp e e' m m',
  env_lessdef e e' -> Mem.extends m m' ->
  forall al vl,
  Cminor.eval_exprlist ge sp e m al vl ->
  forall cl,
  exists vl',
     list_forall2 (CminorSel.eval_builtin_arg tge sp e' m')
                  (sel_builtin_args al cl)
                  vl'
  /\ Val.lessdef_list vl vl'.
Proof.
  induction 3; intros; simpl.
- exists (@nil val); split; constructor.
- exploit sel_builtin_arg_correct; eauto. intros (v1' & A & B).
  edestruct IHeval_exprlist as (vl' & C & D).
  exists (v1' :: vl'); split; auto. constructor; eauto.
Qed.

Lemma sel_builtin_res_correct:
  forall oid v e v' e',
  env_lessdef e e' -> Val.lessdef v v' ->
  env_lessdef (set_optvar oid v e) (set_builtin_res (sel_builtin_res oid) v' e').
Proof.
  intros. destruct oid; simpl; auto. apply set_var_lessdef; auto.
Qed.

Lemma sel_builtin_default_correct:
  forall optid ef al sp e1 m1 vl t v m2 e1' m1' f k,
  Cminor.eval_exprlist ge sp e1 m1 al vl ->
  external_call ef ge vl m1 t v m2 ->
  env_lessdef e1 e1' -> Mem.extends m1 m1' ->
  exists e2' m2',
     plus step tge (State f (sel_builtin_default optid ef al) k sp e1' m1')
                 t (State f Sskip k sp e2' m2')
  /\ env_lessdef (set_optvar optid v e1) e2'
  /\ Mem.extends m2 m2'.
Proof.
  intros. unfold sel_builtin_default.
  exploit sel_builtin_args_correct; eauto. intros (vl' & A & B).
  exploit external_call_mem_extends; eauto. intros (v' & m2' & D & E & F & _).
  econstructor; exists m2'; split.
  apply plus_one.
  econstructor. eexact A. eapply external_call_symbols_preserved. eexact senv_preserved. eexact D.
  split; auto. apply sel_builtin_res_correct; auto.
Qed. 

Lemma sel_builtin_correct:
  forall optid ef al sp e1 m1 vl t v m2 e1' m1' f k,
  Cminor.eval_exprlist ge sp e1 m1 al vl ->
  external_call ef ge vl m1 t v m2 ->
  env_lessdef e1 e1' -> Mem.extends m1 m1' ->
  exists e2' m2',
     plus step tge (State f (sel_builtin optid ef al) k sp e1' m1')
                 t (State f Sskip k sp e2' m2')
  /\ env_lessdef (set_optvar optid v e1) e2'
  /\ Mem.extends m2 m2'.
Proof.
  intros. 
  exploit sel_exprlist_correct; eauto. intros (vl' & A & B).
  exploit external_call_mem_extends; eauto. intros (v' & m2' & D & E & F & _).
  unfold sel_builtin.
  destruct ef; eauto using sel_builtin_default_correct.
  destruct (lookup_builtin_function name sg) as [bf|] eqn:LKUP; eauto using sel_builtin_default_correct.
  simpl in D. red in D. rewrite LKUP in D. inv D.
  destruct optid as [id|]; eauto using sel_builtin_default_correct.
- destruct (sel_known_builtin bf (sel_exprlist al)) as [a|] eqn:SKB; eauto using sel_builtin_default_correct.
  exploit eval_sel_known_builtin; eauto. intros (v'' & U & V).
  econstructor; exists m2'; split.
  apply plus_one. econstructor. eexact U.
  split; auto. apply set_var_lessdef; auto. apply Val.lessdef_trans with v'; auto.
- exists e1', m2'; split.
  eapply plus_two. constructor. constructor. auto.
  simpl; auto.  
Qed.

(** If-conversion *)

Definition eventually := Smallstep.eventually Cminor.step Cminor.final_state ge.

Lemma eventually_step: forall f s k sp e m n P,
  (forall t S', Cminor.step ge (Cminor.State f s k sp e m) t S' -> t = E0 /\ eventually n S' P) ->
  eventually (S n) (Cminor.State f s k sp e m) P.
Proof.
  intros. apply Smallstep.eventually_later; auto. intros r FS. inv FS.
Qed.

Lemma classify_stmt_sound:
  forall s,
  match classify_stmt s with
  | SCskip =>
      exists n, forall f k sp e m,
      eventually n (Cminor.State f s k sp e m) (eq (Cminor.State f Cminor.Sskip k sp e m))
  | SCassign id a =>
      exists n, forall f k sp e m v,
      Cminor.eval_expr ge sp e m a v ->
      eventually n (Cminor.State f s k sp e m) (eq (Cminor.State f Cminor.Sskip k sp (PTree.set id v e) m))
  | SCother => True
  end.
Proof.
  induction s; simpl; auto.
- (* skip *)
  exists O; intros. constructor; auto.
- (* assign *)
  assert (BASE:
           exists n : nat,
           forall (f : Cminor.function) (k : Cminor.cont) (sp : val) (e0 : env) (m : mem) (v : val),
           Cminor.eval_expr ge sp e0 m e v ->
           eventually n (Cminor.State f (Cminor.Sassign i e) k sp e0 m) (eq (Cminor.State f Cminor.Sskip k sp (PTree.set i v e0) m))).
  {
    exists 1%nat; intros. apply eventually_step; intros. inv H0.
    assert (v0 = v) by eauto using eval_expr_determ. subst v0.
    split; auto. apply eventually_now. auto.
  }
  destruct e; try destruct (ident_eq i i0); auto.
  exists 1%nat. intros. apply eventually_step; intros. inv H.
  rewrite PTree.gsident by (inv H9; auto).
  split; auto. apply eventually_now. auto.
- (* builtin *)
  destruct o; auto. destruct e; auto. 
  exists 1%nat; intros. apply eventually_step; intros. inv H. inv H11.
  split; auto. apply eventually_now; auto.
- (* sequence *)
  assert (ESEQ: forall n1 n2 f sp m e e' e'',
    (forall k, eventually n1 (Cminor.State f s1 k sp e m) (eq (Cminor.State f Cminor.Sskip k sp e' m))) ->
    (forall k, eventually n2 (Cminor.State f s2 k sp e' m) (eq (Cminor.State f Cminor.Sskip k sp e'' m))) ->
    (forall k, eventually (S (n1 + S n2))%nat 
                          (Cminor.State f (Cminor.Sseq s1 s2) k sp e m)
                          (eq (Cminor.State f Cminor.Sskip k sp e'' m)))).
  { intros.
    apply eventually_step. intros t S' ST; inv ST. split; auto.
    eapply eventually_trans. eapply H. intros S' EQ; subst S'.
    apply eventually_step. intros t S' ST; inv ST; [auto | inv H8].
  }
  destruct (classify_stmt s1), (classify_stmt s2); auto;
  destruct IHs1 as (n1 & E1), IHs2 as (n2 & E2);
  exists (S (n1 + (S n2)))%nat; intros;
  eapply ESEQ; eauto.
Qed.

Lemma classify_stmt_wt:
  forall env tyret id a s,
  classify_stmt s = SCassign id a ->
  wt_stmt env tyret s ->
  wt_expr env a (env id).
Proof.
  induction s; simpl; intros CL WT; try discriminate.
- destruct e; try destruct (ident_eq i i0); inv CL; inv WT; auto.
- destruct o; try discriminate. destruct e; discriminate.
- inv WT. destruct (classify_stmt s1), (classify_stmt s2); try discriminate; eauto.
Qed.

Lemma if_conversion_base_correct:
  forall f env cond id ifso ifnot kont s e ty vb b sp m tf tk e' m',
  if_conversion_base (known_id f) env cond id ifso ifnot kont = Some s ->
  def_env f e -> wt_env env e ->
  env id = ty ->
  wt_expr env ifso ty ->
  wt_expr env ifnot ty ->
  Cminor.eval_expr ge sp e m cond vb -> Val.bool_of_val vb b ->
  env_lessdef e e' -> Mem.extends m m' ->
  exists v1 v2 v',
     Cminor.eval_expr ge sp e m ifso v1
  /\ Cminor.eval_expr ge sp e m ifnot v2
  /\ Val.lessdef (if b then v1 else v2) v'
  /\ step tge (State tf s tk sp e' m')
           E0 (State tf Sskip tk sp (PTree.set id v' e') m').
Proof.
  unfold if_conversion_base; intros. rewrite H2 in H. clear H2.
  destruct andb eqn:C; inv H. InvBooleans.
  destruct (eval_safe_expr ge f sp e m ifso) as (v1 & EV1); auto.
  destruct (eval_safe_expr ge f sp e m ifnot) as (v2 & EV2); auto.
  assert (TY1: Val.has_type v1 ty) by (eapply wt_eval_expr; eauto).
  assert (TY2: Val.has_type v2 ty) by (eapply wt_eval_expr; eauto).
  exploit (sel_select_expr_correct ty cond ifso ifnot); eauto. intros (v' & EV & LD).
  simpl in LD. rewrite Val.normalize_idem in LD by (destruct b; auto).
  exists v1, v2, v'; intuition auto.
  constructor. exact EV.
Qed.

Lemma if_conversion_correct:
  forall f env tyret cond ifso ifnot kont s vb b k f' k' sp e m e' m',
  if_conversion (known_id f) env cond ifso ifnot kont = Some s ->
  def_env f e -> wt_env env e ->
  wt_stmt env tyret ifso ->
  wt_stmt env tyret ifnot ->
  Cminor.eval_expr ge sp e m cond vb -> Val.bool_of_val vb b ->
  env_lessdef e e' -> Mem.extends m m' ->
  let s0 := if b then ifso else ifnot in
  exists n e1 e1',
     step tge (State f' s k' sp e' m') E0 (State f' Sskip k' sp e1' m')
  /\ eventually n (Cminor.State f s0 k sp e m) (eq (Cminor.State f Cminor.Sskip k sp e1 m))
  /\ env_lessdef e1 e1'.
Proof.
  unfold if_conversion; intros until m'; intros IFC DE WTE WT1 WT2 EVC BOV ELD MEXT.
  set (s0 := if b then ifso else ifnot). set (ki := known_id f) in *.
  generalize (classify_stmt_sound ifso) (classify_stmt_sound ifnot).
  destruct (classify_stmt ifso) eqn:IFSO; try discriminate;
  destruct (classify_stmt ifnot) eqn:IFNOT; try discriminate;
  intros (n1 & EV1) (n2 & EV2).
- exploit if_conversion_base_correct; eauto using wt_expr, classify_stmt_wt.
  intros (v1 & v2 & v' & E1 & E2 & VLD & STEP).
  exists (if b then n1 else n2), (PTree.set id (if b then v1 else v2) e), (PTree.set id v' e').
  split. eexact STEP. 
  split. unfold s0; destruct b.
    rewrite PTree.gsident by (inv E1; auto). eapply EV1.
    eapply EV2; eauto.
  apply set_var_lessdef; auto.
- exploit if_conversion_base_correct; eauto using wt_expr, classify_stmt_wt.
  intros (v1 & v2 & v' & E1 & E2 & VLD & STEP).
  exists (if b then n1 else n2), (PTree.set id (if b then v1 else v2) e), (PTree.set id v' e').
  split. eexact STEP. 
  split. unfold s0; destruct b.
    eapply EV1; eauto.
    rewrite PTree.gsident by (inv E2; auto). eapply EV2.
  apply set_var_lessdef; auto.
- destruct (ident_eq id id0); try discriminate. subst id0.
  exploit if_conversion_base_correct; eauto using wt_expr, classify_stmt_wt.
  intros (v1 & v2 & v' & E1 & E2 & VLD & STEP).
  exists (if b then n1 else n2), (PTree.set id (if b then v1 else v2) e), (PTree.set id v' e').
  split. eexact STEP. 
  split. unfold s0; destruct b. eapply EV1; eauto. eapply EV2; eauto.
  apply set_var_lessdef; auto.
Qed.

End EXPRESSIONS.

(** Semantic preservation for functions and statements. *)

Inductive match_cont: Cminor.program -> helper_functions -> known_idents -> typenv -> Cminor.cont -> CminorSel.cont -> Prop :=
  | match_cont_seq: forall cunit hf ki env s kont s' k k',
      sel_stmt (prog_defmap cunit) ki env s kont = OK s' ->
      match_cont cunit hf ki env k k' ->
      match_cont cunit hf ki env (Cminor.Kseq s k) (Kseq s' k')
  | match_cont_block: forall cunit hf ki env k k',
      match_cont cunit hf ki env k k' ->
      match_cont cunit hf ki env (Cminor.Kblock k) (Kblock k')
  | match_cont_other: forall cunit hf ki env k k',
      match_call_cont k k' ->
      match_cont cunit hf ki env k k'

with match_call_cont: Cminor.cont -> CminorSel.cont -> Prop :=
  | match_cont_stop:
      match_call_cont Cminor.Kstop Kstop
  | match_cont_call: forall cunit hf env id f sp e k f' e' k',
      linkorder cunit prog ->
      helper_functions_declared cunit hf ->
      sel_function (prog_defmap cunit) hf f = OK f' ->
      type_function f = OK env ->
      match_cont cunit hf (known_id f) env k k' ->
      env_lessdef e e' ->
      match_call_cont (Cminor.Kcall id f sp e k) (Kcall id f' sp e' k').

Inductive match_states: Cminor.state -> CminorSel.state -> Prop :=
  | match_state: forall cunit hf f f' s kont k s' k' sp e m e' m' env
        (LINK: linkorder cunit prog)
        (HF: helper_functions_declared cunit hf)
        (TF: sel_function (prog_defmap cunit) hf f = OK f')
        (TYF: type_function f = OK env)
        (TS: sel_stmt (prog_defmap cunit) (known_id f) env s kont = OK s')
        (MC: match_cont cunit hf (known_id f) env k k')
        (LD: env_lessdef e e')
        (ME: Mem.extends m m'),
      match_states
        (Cminor.State f s k sp e m)
        (State f' s' k' sp e' m')
  | match_callstate: forall cunit f f' args args' k k' m m'
        (LINK: linkorder cunit prog)
        (TF: match_fundef cunit f f')
        (MC: match_call_cont k k')
        (LD: Val.lessdef_list args args')
        (ME: Mem.extends m m'),
      match_states
        (Cminor.Callstate f args k m)
        (Callstate f' args' k' m')
  | match_returnstate: forall v v' k k' m m'
        (MC: match_call_cont k k')
        (LD: Val.lessdef v v')
        (ME: Mem.extends m m'),
      match_states
        (Cminor.Returnstate v k m)
        (Returnstate v' k' m')
  | match_builtin_1: forall cunit hf ef args optid f sp e k m al f' e' k' m' env
        (LINK: linkorder cunit prog)
        (HF: helper_functions_declared cunit hf)
        (TF: sel_function (prog_defmap cunit) hf f = OK f')
        (TYF: type_function f = OK env)
        (MC: match_cont cunit hf (known_id f) env k k')
        (EA: Cminor.eval_exprlist ge sp e m al args)
        (LDE: env_lessdef e e')
        (ME: Mem.extends m m'),
      match_states
        (Cminor.Callstate (External ef) args (Cminor.Kcall optid f sp e k) m)
        (State f' (sel_builtin optid ef al) k' sp e' m')
  | match_builtin_2: forall cunit hf v v' optid f sp e k m f' e' m' k' env
        (LINK: linkorder cunit prog)
        (HF: helper_functions_declared cunit hf)
        (TF: sel_function (prog_defmap cunit) hf f = OK f')
        (TYF: type_function f = OK env)
        (MC: match_cont cunit hf (known_id f) env k k')
        (LDV: Val.lessdef v v')
        (LDE: env_lessdef (set_optvar optid v e) e')
        (ME: Mem.extends m m'),
      match_states
        (Cminor.Returnstate v (Cminor.Kcall optid f sp e k) m)
        (State f' Sskip k' sp e' m').

Remark match_states_skip: forall cunit hf f f' k k' sp e m e' m' env
        (LINK: linkorder cunit prog)
        (HF: helper_functions_declared cunit hf)
        (TF: sel_function (prog_defmap cunit) hf f = OK f')
        (TYF: type_function f = OK env)
        (MC: match_cont cunit hf (known_id f) env k k')
        (LD: env_lessdef e e')
        (ME: Mem.extends m m'),
  match_states (Cminor.State f Cminor.Sskip k sp e m) (State f' Sskip k' sp e' m').
Proof.
  intros. eapply match_state with (kont := Sskip); eauto.
Qed.

Remark call_cont_commut:
  forall cunit hf ki env k k',
  match_cont cunit hf ki env k k' -> match_call_cont (Cminor.call_cont k) (call_cont k').
Proof.
  induction 1; simpl; auto. inversion H; subst; auto.
Qed.

Remark match_is_call_cont:
  forall cunit hf ki env k k',
  match_cont cunit ki env hf k k' -> Cminor.is_call_cont k ->
  match_call_cont k k' /\ is_call_cont k'.
Proof.
  destruct 1; intros; try contradiction. split; auto. inv H; auto.
Qed.

Definition nolabel (s: Cminor.stmt) : Prop :=
  forall lbl k, Cminor.find_label lbl s k = None.
Definition nolabel' (s: stmt) : Prop :=
  forall lbl k, find_label lbl s k = None.

Remark classify_stmt_nolabel:
  forall s, classify_stmt s <> SCother -> nolabel s.
Proof.
  induction s; simpl; intros DIFF; try congruence.
- (* skip *) red; auto.
- (* assign *) red; auto.
- (* builtin *) red; auto.
- (* seq *)
  assert (CL: classify_stmt s1 <> SCother /\ classify_stmt s2 <> SCother).
  { destruct (classify_stmt s1), (classify_stmt s2); intuition congruence. }
  destruct CL as [CL1 CL2]. apply IHs1 in CL1; apply IHs2 in CL2.
  red; intros; simpl. rewrite CL1; apply CL2.
Qed.

Lemma if_conversion_base_nolabel: forall (hf: helper_functions) ki env a id a1 a2 kont s,
  if_conversion_base ki env a id a1 a2 kont = Some s ->
  nolabel' s.
Proof.
  unfold if_conversion_base; intros.
  destruct andb; inv H. 
  red; auto.
Qed.

Lemma if_conversion_nolabel: forall (hf: helper_functions) ki env a s1 s2 kont s,
  if_conversion ki env a s1 s2 kont = Some s ->
  nolabel s1 /\ nolabel s2 /\ nolabel' s.
Proof.
  unfold if_conversion; intros.
  Ltac conclude :=
    split; [apply classify_stmt_nolabel;congruence
           |split; [apply classify_stmt_nolabel;congruence
                   |eapply if_conversion_base_nolabel; eauto]].
  destruct (classify_stmt s1) eqn:C1; try discriminate;
  destruct (classify_stmt s2) eqn:C2; try discriminate.
  conclude.
  conclude.
  destruct (ident_eq id id0). conclude. discriminate.
Qed.

Remark sel_builtin_nolabel:
  forall (hf: helper_functions) optid ef args, nolabel' (sel_builtin optid ef args).
Proof.
  unfold sel_builtin; intros; red; intros.
  destruct ef; auto. destruct lookup_builtin_function; auto.
  destruct optid; auto. destruct sel_known_builtin; auto. 
Qed. 

Remark find_label_commut:
  forall cunit hf ki env lbl s kont k s' k',
  match_cont cunit hf ki env k k' ->
  sel_stmt (prog_defmap cunit) ki env s kont = OK s' ->
  match Cminor.find_label lbl s k, find_label lbl s' k' with
  | None, None => True
  | Some(s1, k1), Some(s1', k1') => exists kont1, sel_stmt (prog_defmap cunit) ki env s1 kont1 = OK s1' /\ match_cont cunit hf ki env k1 k1'
  | _, _ => False
  end.
Proof.
  induction s; intros until k'; simpl; intros MC SE; try (monadInv SE); simpl; auto.
- (* store *)
  unfold store. destruct (addressing m (sel_expr e)); simpl; auto.
- (* call *)
  destruct (classify_call (prog_defmap cunit) e); simpl; auto.
  rewrite sel_builtin_nolabel; auto.
- (* tailcall *)
  destruct (classify_call (prog_defmap cunit) e); simpl; auto.
- (* builtin *)
  rewrite sel_builtin_nolabel; auto.
- (* seq *)
  exploit (IHs1 x (Cminor.Kseq s2 k)). econstructor; eauto. eauto.
  destruct (Cminor.find_label lbl s1 (Cminor.Kseq s2 k)) as [[sx kx] | ];
  destruct (find_label lbl x0 (Kseq x k')) as [[sy ky] | ];
  intuition. apply (IHs2 kont); eauto.
- (* ifthenelse *)
  destruct if_conversion as [s|] eqn:IFC.
  inv SE. exploit if_conversion_nolabel; eauto. intros (A & B & C).
  rewrite A, B, C. auto.
  monadInv SE; simpl.
  exploit (IHs1 kont k); eauto.
  destruct (Cminor.find_label lbl s1 k) as [[sx kx] | ];
  destruct (find_label lbl x k') as [[sy ky] | ];
  intuition. apply (IHs2 kont); eauto.
- (* loop *) 
  apply (IHs Sskip). apply match_cont_seq with (kont := Sskip); auto. simpl; rewrite EQ; auto. auto.
- (* block *)
  apply (IHs kont). constructor; auto. auto.
- (* switch *)
  destruct b.
  destruct (validate_switch Int64.modulus n l (compile_switch Int64.modulus n l)); inv SE.
  simpl; auto.
  destruct (validate_switch Int.modulus n l (compile_switch Int.modulus n l)); inv SE.
  simpl; auto.
- (* return *)
  destruct o; inv SE; simpl; auto.
- (* label *)
  destruct (ident_eq lbl l).
  + eauto.
  + apply (IHs kont); eauto.
Qed.

(** The simulation diagram *)

Definition measure (s: Cminor.state) : nat :=
  match s with
  | Cminor.Callstate _ _ _ _ => 0%nat
  | Cminor.State _ _ _ _ _ _ => 1%nat
  | Cminor.Returnstate _ _ _ => 2%nat
  end.

Lemma sel_step_correct:
  forall S1 t S2, Cminor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 -> wt_state S1 ->
  (exists T2, plus step tge T1 t T2 /\ match_states S2 T2)
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 T1)%nat
  \/ (exists T2 n, step tge T1 t T2 /\ eventually n S2 (fun S3 => match_states S3 T2)).
Proof.
  induction 1; intros T1 ME WTS; inv ME; try (monadInv TS).
- (* skip seq *)
  inv MC. left; econstructor; split. apply plus_one; econstructor. econstructor; eauto.
  inv H.
- (* skip block *)
  inv MC. left; econstructor; split. apply plus_one; econstructor. eauto using match_states_skip.
  inv H.
- (* skip call *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  left; econstructor; split.
  apply plus_one; econstructor. eapply match_is_call_cont; eauto.
  erewrite stackspace_function_translated; eauto.
  econstructor; eauto. eapply match_is_call_cont; eauto.
- (* assign *)
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split.
  apply plus_one; econstructor; eauto.
  eapply match_states_skip; eauto. apply set_var_lessdef; auto.
- (* store *)
  exploit sel_expr_correct. try apply LINK. try apply HF. eexact H. eauto. eauto. intros [vaddr' [A B]].
  exploit sel_expr_correct. try apply LINK. try apply HF. eexact H0. eauto. eauto. intros [v' [C D]].
  exploit Mem.storev_extends; eauto. intros [m2' [P Q]].
  left; econstructor; split.
  apply plus_one; eapply eval_store; eauto.
  eauto using match_states_skip.
- (* Scall *)
  exploit classify_call_correct; eauto.
  destruct (classify_call (prog_defmap cunit) a) as [ | id | ef].
+ (* indirect *)
  exploit sel_expr_correct; eauto. intros [vf' [A B]].
  exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].
  exploit functions_translated; eauto. intros (cunit' & fd' & U & V & W).
  left; econstructor; split.
  apply plus_one; econstructor; eauto. econstructor; eauto.
  eapply sig_function_translated; eauto.
  eapply match_callstate with (cunit := cunit'); eauto.
  eapply match_cont_call with (cunit := cunit) (hf := hf); eauto.
+ (* direct *)
  intros [b [U V]].
  exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].
  exploit functions_translated; eauto. intros (cunit' & fd' & X & Y & Z).
  left; econstructor; split.
  apply plus_one; econstructor; eauto.
  subst vf. econstructor; eauto. rewrite symbols_preserved; eauto.
  eapply sig_function_translated; eauto.
  eapply match_callstate with (cunit := cunit'); eauto.
  eapply match_cont_call with (cunit := cunit) (hf := hf); eauto.
+ (* turned into Sbuiltin *)
  intros EQ. subst fd.
  right; left; split. simpl; lia. split; auto. econstructor; eauto.
- (* Stailcall *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  exploit sel_expr_correct; eauto. intros [vf' [A B]].
  exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].
  exploit functions_translated; eauto. intros (cunit' & fd' & E & F & G).
  left; econstructor; split.
  apply plus_one.
  exploit classify_call_correct. eexact LINK. eauto. eauto.
  destruct (classify_call (prog_defmap cunit)) as [ | id | ef]; intros.
  econstructor; eauto. econstructor; eauto. eapply sig_function_translated; eauto.
  destruct H2 as [b [U V]]. subst vf. inv B.
  econstructor; eauto. econstructor; eauto. rewrite symbols_preserved; eauto. eapply sig_function_translated; eauto.
  econstructor; eauto. econstructor; eauto. eapply sig_function_translated; eauto.
  eapply match_callstate with (cunit := cunit'); eauto.
  eapply call_cont_commut; eauto.
- (* Sbuiltin *)
  exploit sel_builtin_correct; eauto. intros (e2' & m2' & P & Q & R).
  left; econstructor; split. eexact P. eauto using match_states_skip.
- (* Seq *)
  left; econstructor; split.
  apply plus_one; constructor.
  econstructor; eauto. econstructor; eauto.
- (* Sifthenelse *)
  simpl in TS. destruct if_conversion as [s|] eqn:IFC; monadInv TS.
+ inv WTS. inv WT_FN. assert (env0 = env) by congruence. subst env0. inv WT_STMT.
  exploit if_conversion_correct; eauto.
  set (s0 := if b then s1 else s2). intros (n & e1 & e1' & A & B & C).
  right; right. econstructor; exists n.
  split. eexact A. eapply eventually_implies. eexact B.
  intros S3 EQ; subst S3. eauto using match_states_skip.
+ exploit sel_expr_correct; eauto. intros [v' [A B]].
  assert (Val.bool_of_val v' b). inv B. auto. inv H0.
  left; exists (State f' (if b then x else x0) k' sp e' m'); split.
  apply plus_one; econstructor; eauto. eapply eval_condexpr_of_expr; eauto.
  econstructor; eauto. destruct b; eauto.
- (* Sloop *)
  left; econstructor; split. apply plus_one; constructor. econstructor; eauto.
  apply match_cont_seq with Sskip; auto. simpl; rewrite EQ; auto.
- (* Sblock *)
  left; econstructor; split. apply plus_one; constructor. econstructor; eauto. constructor; auto.
- (* Sexit seq *)
  inv MC. left; econstructor; split. apply plus_one; constructor.
  eapply match_state with (kont := Sskip); eauto.
  inv H.
- (* Sexit0 block *)
  inv MC. left; econstructor; split. apply plus_one; constructor. eauto using match_states_skip.
  inv H.
- (* SexitS block *)
  inv MC. left; econstructor; split. apply plus_one; constructor.
  eapply match_state with (kont := Sskip); eauto.
  inv H.
- (* Sswitch *)
  inv H0; simpl in TS.
+ set (ct := compile_switch Int.modulus default cases) in *.
  destruct (validate_switch Int.modulus default cases ct) eqn:VALID; inv TS.
  exploit sel_expr_correct; eauto. intros [v' [A B]]. inv B.
  left; econstructor; split.
  apply plus_one; econstructor. eapply sel_switch_int_correct; eauto.
  eapply match_state with (kont := Sskip); eauto.
+ set (ct := compile_switch Int64.modulus default cases) in *.
  destruct (validate_switch Int64.modulus default cases ct) eqn:VALID; inv TS.
  exploit sel_expr_correct; eauto. intros [v' [A B]]. inv B.
  left; econstructor; split.
  apply plus_one; econstructor. eapply sel_switch_long_correct; eauto.
  eapply match_state with (kont := Sskip); eauto.
- (* Sreturn None *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  left; econstructor; split.
  apply plus_one; econstructor. simpl; eauto.
  econstructor; eauto. eapply call_cont_commut; eauto.
- (* Sreturn Some *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split.
  apply plus_one; econstructor; eauto.
  econstructor; eauto. eapply call_cont_commut; eauto.
- (* Slabel *)
  left; econstructor; split. apply plus_one; constructor. econstructor; eauto.
- (* Sgoto *)
  assert (sel_stmt (prog_defmap cunit) (known_id f) env (Cminor.fn_body f) Sskip = OK (fn_body f')).
  { monadInv TF; simpl. congruence. }
  exploit (find_label_commut cunit hf (known_id f) env lbl (Cminor.fn_body f) Sskip (Cminor.call_cont k)).
    apply match_cont_other. eapply call_cont_commut; eauto. eauto.
  rewrite H.
  destruct (find_label lbl (fn_body f') (call_cont k'0))
  as [[s'' k'']|] eqn:?; intros; try contradiction.
  destruct H1 as (cont1 & P & Q).
  left; econstructor; split.
  apply plus_one; econstructor; eauto.
  econstructor; eauto.
- (* internal function *)
  destruct TF as (hf & HF & TF). 
  monadInv TF. generalize EQ; intros TF; monadInv TF.
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m2' [A B]].
  left; econstructor; split.
  apply plus_one; econstructor; simpl; eauto using Val.has_argtype_list_lessdef.
  econstructor; simpl; eauto.
  apply match_cont_other; auto.
  apply set_locals_lessdef. apply set_params_lessdef; auto.
- (* external call *)
  destruct TF as (hf & HF & TF).
  monadInv TF.
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  apply plus_one; econstructor. eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.
- (* external call turned into a Sbuiltin *)
  exploit sel_builtin_correct; eauto. intros (e2' & m2' & P & Q & R).
  left; econstructor; split. eexact P. econstructor; eauto.
- (* return *)
  inv MC.
  left; econstructor; split.
  apply plus_one; econstructor.
  eapply match_states_skip; eauto. destruct optid; simpl; auto. apply set_var_lessdef; auto.
- (* return of an external call turned into a Sbuiltin *)
  right; left; split. simpl; lia. split. auto. eauto using match_states_skip.
Qed.

Lemma sel_initial_states:
  forall S, Cminor.initial_state prog S ->
  exists R, initial_state tprog R /\ match_states S R.
Proof.
  destruct 1.
  exploit function_ptr_translated; eauto. intros (cu & f' & A & B & C).
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_match TRANSF); eauto.
  rewrite (match_program_main TRANSF). fold tge. rewrite symbols_preserved. eauto.
  eexact A.
  rewrite <- H2. eapply sig_function_translated; eauto.
  econstructor; eauto. constructor. apply Mem.extends_refl.
Qed.

Lemma sel_final_states:
  forall S R r,
  match_states S R -> Cminor.final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H. inv MC. inv LD. constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (Cminor.semantics prog) (CminorSel.semantics tprog).
Proof.
  set (MS := fun S T => match_states S T /\ wt_state S).
  apply forward_simulation_eventually_star with (measure := measure) (match_states := MS);
  unfold MS.
- apply senv_preserved.
- intros S INIT. exploit sel_initial_states; eauto. intros (T & P & Q).
  assert (W: wt_state S). { eapply wt_initial_state. eexact wt_prog. auto. }
  eauto.
- intros S T r (M & W) FIN.
  eapply sel_final_states; eauto.
- intros S1 t S2 A T1 (M & W1).
  assert (W2: wt_state S2) by (eapply subject_reduction; eauto using wt_prog).
  exploit sel_step_correct; eauto.
  intros [(T2 & D & E) | [(D & E & F) | (T2 & n & D & E)]].
+ left; exists T2; auto.
+ subst t. left; exists T1; auto using star_refl.
+ right; exists n, T2; split.
  apply plus_one; auto.
  apply eventually_and_invariant; eauto using subject_reduction, wt_prog.
Qed.

End PRESERVATION.

(** ** Commutation with linking *)

Global Instance TransfSelectionLink : TransfLink match_prog.
Proof.
  red; intros. destruct (link_linkorder _ _ _ H) as [LO1 LO2].
  eapply link_match_program; eauto.
  intros. elim H3; intros hf1 [A1 B1]. elim H4; intros hf2 [A2 B2].
Local Transparent Linker_fundef.
  simpl in *. destruct f1, f2; simpl in *; monadInv B1; monadInv B2; simpl.
- discriminate.
- destruct e; inv H2. econstructor; eauto.
- destruct e; inv H2. econstructor; eauto.
- destruct (external_function_eq e e0); inv H2. econstructor; eauto.
Qed.
