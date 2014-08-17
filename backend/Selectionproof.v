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

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Switch.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.
Require Import SelectDiv.
Require Import SelectLong.
Require Import Selection.
Require Import SelectOpproof.
Require Import SelectDivproof.
Require Import SelectLongproof.

Local Open Scope cminorsel_scope.
Local Open Scope error_monad_scope.


(** * Correctness of the instruction selection functions for expressions *)

Section PRESERVATION.

Variable prog: Cminor.program.
Variable tprog: CminorSel.program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Variable hf: helper_functions.
Hypothesis HELPERS: i64_helpers_correct tge hf.
Hypothesis TRANSFPROG: transform_partial_program (sel_fundef hf ge) prog = OK tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros. eapply Genv.find_symbol_transf_partial; eauto. 
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: Cminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ sel_fundef hf ge f = OK tf.
Proof.  
  intros. eapply Genv.find_funct_ptr_transf_partial; eauto.
Qed.

Lemma functions_translated:
  forall (v v': val) (f: Cminor.fundef),
  Genv.find_funct ge v = Some f ->
  Val.lessdef v v' ->
  exists tf, Genv.find_funct tge v' = Some tf /\ sel_fundef hf ge f = OK tf.
Proof.  
  intros. inv H0.
  eapply Genv.find_funct_transf_partial; eauto.
  simpl in H. discriminate.
Qed.

Lemma sig_function_translated:
  forall f tf, sel_fundef hf ge f = OK tf -> funsig tf = Cminor.funsig f.
Proof.
  intros. destruct f; monadInv H; auto. monadInv EQ. auto. 
Qed.

Lemma stackspace_function_translated:
  forall f tf, sel_function hf ge f = OK tf -> fn_stackspace tf = Cminor.fn_stackspace f.
Proof.
  intros. monadInv H. auto. 
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros; eapply Genv.find_var_info_transf_partial; eauto.
Qed.

Lemma helper_implements_preserved:
  forall id sg vargs vres,
  helper_implements ge id sg vargs vres ->
  helper_implements tge id sg vargs vres.
Proof.
  intros. destruct H as (b & ef & A & B & C & D).
  exploit function_ptr_translated; eauto. simpl. intros (tf & P & Q). inv Q. 
  exists b; exists ef. 
  split. rewrite symbols_preserved. auto.
  split. auto.
  split. auto.
  intros. eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
Qed.

Lemma builtin_implements_preserved:
  forall id sg vargs vres,
  builtin_implements ge id sg vargs vres ->
  builtin_implements tge id sg vargs vres.
Proof.
  unfold builtin_implements; intros.
  eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
Qed.

Lemma helpers_correct_preserved:
  forall h, i64_helpers_correct ge h -> i64_helpers_correct tge h.
Proof.
  unfold i64_helpers_correct; intros.
  repeat (match goal with [ H: _ /\ _ |- _ /\ _ ] => destruct H; split end);
  intros; try (eapply helper_implements_preserved; eauto);
  try (eapply builtin_implements_preserved; eauto).
Qed.

Section CMCONSTR.

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
  simpl. inv H0. auto. auto. 
Qed.

Lemma eval_load:
  forall le a v chunk v',
  eval_expr tge sp e m le a v ->
  Mem.loadv chunk m v = Some v' ->
  eval_expr tge sp e m le (load chunk a) v'.
Proof.
  intros. generalize H0; destruct v; simpl; intro; try discriminate.
  unfold load. 
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (refl_equal _)).
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
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (refl_equal _)).
  destruct (addressing chunk a1). intros [vl [EV EQ]]. 
  eapply step_store; eauto. 
Qed.

(** Correctness of instruction selection for operators *)

Lemma eval_sel_unop:
  forall le op a1 v1 v,
  eval_expr tge sp e m le a1 v1 ->
  eval_unop op v1 = Some v ->
  exists v', eval_expr tge sp e m le (sel_unop hf op a1) v' /\ Val.lessdef v v'.
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
  exists v', eval_expr tge sp e m le (sel_binop hf op a1 a2) v' /\ Val.lessdef v v'.
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
  eapply eval_divl; eauto.
  eapply eval_divlu; eauto.
  eapply eval_modl; eauto.
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

End CMCONSTR.

(** Recognition of calls to built-in functions *)

Lemma expr_is_addrof_ident_correct:
  forall e id,
  expr_is_addrof_ident e = Some id ->
  e = Cminor.Econst (Cminor.Oaddrsymbol id Int.zero).
Proof.
  intros e id. unfold expr_is_addrof_ident. 
  destruct e; try congruence.
  destruct c; try congruence.
  predSpec Int.eq Int.eq_spec i0 Int.zero; congruence.
Qed.

Lemma classify_call_correct:
  forall sp e m a v fd,
  Cminor.eval_expr ge sp e m a v ->
  Genv.find_funct ge v = Some fd ->
  match classify_call ge a with
  | Call_default => True
  | Call_imm id => exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Int.zero
  | Call_builtin ef => fd = External ef
  end.
Proof.
  unfold classify_call; intros. 
  destruct (expr_is_addrof_ident a) as [id|] eqn:?. 
  exploit expr_is_addrof_ident_correct; eauto. intros EQ; subst a.
  inv H. inv H2. 
  destruct (Genv.find_symbol ge id) as [b|] eqn:?. 
  rewrite Genv.find_funct_find_funct_ptr in H0. 
  rewrite H0. 
  destruct fd. exists b; auto. 
  destruct (ef_inline e0). auto. exists b; auto.
  simpl in H0. discriminate.
  auto.
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
  intros. exploit validate_switch_correct; eauto. omega. intros [A B].
  econstructor. eauto. eapply sel_switch_correct_rec; eauto.
Qed.

End SEL_SWITCH.

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
  unfold Int.max_unsigned; omega.
  unfold proj_sumbool; rewrite zeq_false; auto.
  red; intros; elim H1. rewrite <- (Int.repr_unsigned n0). congruence.
- intros until n; intros EVAL R RANGE.
  exploit eval_compu. eexact EVAL. apply (INTCONST (Int.repr n)).  
  instantiate (1 := Clt). intros (vb & A & B). 
  inv R. unfold Val.cmpu in B. simpl in B.
  unfold Int.ltu in B. rewrite Int.unsigned_repr in B. 
  destruct (zlt (Int.unsigned n0) n); inv B; auto. 
  unfold Int.max_unsigned; omega.
- intros until n; intros EVAL R RANGE.
  exploit eval_sub. eexact EVAL. apply (INTCONST (Int.repr n)). intros (vb & A & B).
  inv R. simpl in B. inv B. econstructor; split; eauto. 
  replace ((Int.unsigned n0 - n) mod Int.modulus)
     with (Int.unsigned (Int.sub n0 (Int.repr n))).
  constructor.
  unfold Int.sub. rewrite Int.unsigned_repr_eq. f_equal. f_equal. 
  apply Int.unsigned_repr. unfold Int.max_unsigned; omega.
- intros until i0; intros EVAL R. exists v; split; auto. 
  inv R. rewrite Zmod_small by (apply Int.unsigned_range). constructor.
- constructor. 
- apply Int.unsigned_range.
Qed.

Lemma sel_switch_long_correct:
  forall dfl cases arg sp e m i t le,
  validate_switch Int64.modulus dfl cases t = true ->
  eval_expr tge sp e m le arg (Vlong i) ->
  eval_exitexpr tge sp e m le (XElet arg (sel_switch_long hf O t)) (switch_target (Int64.unsigned i) dfl cases).
Proof.
  intros. eapply sel_switch_correct with (R := Rlong); eauto.
- intros until n; intros EVAL R RANGE.
  eapply eval_cmpl. eexact EVAL. apply eval_longconst with (n := Int64.repr n).
  inv R. unfold Val.cmpl. simpl. f_equal; f_equal. unfold Int64.eq. 
  rewrite Int64.unsigned_repr. destruct (zeq (Int64.unsigned n0) n); auto. 
  unfold Int64.max_unsigned; omega.
- intros until n; intros EVAL R RANGE. 
  eapply eval_cmplu. eexact EVAL. apply eval_longconst with (n := Int64.repr n).
  inv R. unfold Val.cmplu. simpl. f_equal; f_equal. unfold Int64.ltu. 
  rewrite Int64.unsigned_repr. destruct (zlt (Int64.unsigned n0) n); auto. 
  unfold Int64.max_unsigned; omega.
- intros until n; intros EVAL R RANGE.
  exploit eval_subl. eexact HELPERS. eexact EVAL. apply eval_longconst with (n := Int64.repr n).
  intros (vb & A & B).
  inv R. simpl in B. inv B. econstructor; split; eauto. 
  replace ((Int64.unsigned n0 - n) mod Int64.modulus)
     with (Int64.unsigned (Int64.sub n0 (Int64.repr n))).
  constructor.
  unfold Int64.sub. rewrite Int64.unsigned_repr_eq. f_equal. f_equal. 
  apply Int64.unsigned_repr. unfold Int64.max_unsigned; omega.
- intros until i0; intros EVAL R. 
  exploit eval_lowlong. eexact EVAL. intros (vb & A & B). 
  inv R. simpl in B. inv B. econstructor; split; eauto.
  replace (Int64.unsigned n mod Int.modulus) with (Int.unsigned (Int64.loword n)).
  constructor.
  unfold Int64.loword. apply Int.unsigned_repr_eq. 
- constructor. 
- apply Int64.unsigned_range.
Qed.

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
  inv LD1. inv LD2. exists v; auto. 
  destruct op; destruct v1'; simpl in *; inv EV; TrivialExists.
  destruct op; simpl in *; inv EV; TrivialExists.
  destruct op; try (exact H). 
  simpl in *. TrivialExists. inv EV. apply Val.of_optbool_lessdef. 
  intros. apply Val.cmpu_bool_lessdef with (Mem.valid_pointer m) v1 v2; auto.
  intros; eapply Mem.valid_pointer_extends; eauto.
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

Lemma sel_expr_correct:
  forall sp e m a v,
  Cminor.eval_expr ge sp e m a v ->
  forall e' le m',
  env_lessdef e e' -> Mem.extends m m' ->
  exists v', eval_expr tge sp e' m' le (sel_expr hf a) v' /\ Val.lessdef v v'.
Proof.
  induction 1; intros; simpl.
  (* Evar *)
  exploit H0; eauto. intros [v' [A B]]. exists v'; split; auto. constructor; auto.
  (* Econst *)
  destruct cst; simpl in *; inv H. 
  exists (Vint i); split; auto. econstructor. constructor. auto. 
  exists (Vfloat f); split; auto. econstructor. constructor. auto.
  exists (Vsingle f); split; auto. econstructor. constructor. auto. 
  exists (Val.longofwords (Vint (Int64.hiword i)) (Vint (Int64.loword i))); split.
  eapply eval_Eop. constructor. EvalOp. simpl; eauto. constructor. EvalOp. simpl; eauto. constructor. auto.
  simpl. rewrite Int64.ofwords_recompose. auto.
  rewrite <- symbols_preserved. fold (Genv.symbol_address tge i i0). apply eval_addrsymbol.
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
  exploit eval_sel_binop. eexact A. eexact C. eauto. intros [v'' [P Q]].
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
  exists v', eval_exprlist tge sp e' m' le (sel_exprlist hf a) v' /\ Val.lessdef_list v v'.
Proof.
  induction 1; intros; simpl. 
  exists (@nil val); split; auto. constructor.
  exploit sel_expr_correct; eauto. intros [v1' [A B]].
  exploit IHeval_exprlist; eauto. intros [vl' [C D]].
  exists (v1' :: vl'); split; auto. constructor; eauto.
Qed.

(** Semantic preservation for functions and statements. *)

Inductive match_cont: Cminor.cont -> CminorSel.cont -> Prop :=
  | match_cont_stop:
      match_cont Cminor.Kstop Kstop
  | match_cont_seq: forall s s' k k',
      sel_stmt hf ge s = OK s' ->
      match_cont k k' ->
      match_cont (Cminor.Kseq s k) (Kseq s' k')
  | match_cont_block: forall k k',
      match_cont k k' ->
      match_cont (Cminor.Kblock k) (Kblock k')
  | match_cont_call: forall id f sp e k f' e' k',
      sel_function hf ge f = OK f' ->
      match_cont k k' -> env_lessdef e e' ->
      match_cont (Cminor.Kcall id f sp e k) (Kcall id f' sp e' k').

Inductive match_states: Cminor.state -> CminorSel.state -> Prop :=
  | match_state: forall f f' s k s' k' sp e m e' m'
        (TF: sel_function hf ge f = OK f')
        (TS: sel_stmt hf ge s = OK s')
        (MC: match_cont k k')
        (LD: env_lessdef e e')
        (ME: Mem.extends m m'),
      match_states
        (Cminor.State f s k sp e m)
        (State f' s' k' sp e' m')
  | match_callstate: forall f f' args args' k k' m m'
        (TF: sel_fundef hf ge f = OK f')
        (MC: match_cont k k')
        (LD: Val.lessdef_list args args')
        (ME: Mem.extends m m'),
      match_states
        (Cminor.Callstate f args k m)
        (Callstate f' args' k' m')
  | match_returnstate: forall v v' k k' m m'
        (MC: match_cont k k')
        (LD: Val.lessdef v v')
        (ME: Mem.extends m m'),
      match_states
        (Cminor.Returnstate v k m)
        (Returnstate v' k' m')
  | match_builtin_1: forall ef args args' optid f sp e k m al f' e' k' m'
        (TF: sel_function hf ge f = OK f')
        (MC: match_cont k k')
        (LDA: Val.lessdef_list args args')
        (LDE: env_lessdef e e')
        (ME: Mem.extends m m')
        (EA: eval_exprlist tge sp e' m' nil al args'),
      match_states
        (Cminor.Callstate (External ef) args (Cminor.Kcall optid f sp e k) m)
        (State f' (Sbuiltin optid ef al) k' sp e' m')
  | match_builtin_2: forall v v' optid f sp e k m f' e' m' k'
        (TF: sel_function hf ge f = OK f')
        (MC: match_cont k k')
        (LDV: Val.lessdef v v')
        (LDE: env_lessdef e e')
        (ME: Mem.extends m m'),
      match_states
        (Cminor.Returnstate v (Cminor.Kcall optid f sp e k) m)
        (State f' Sskip k' sp (set_optvar optid v' e') m').

Remark call_cont_commut:
  forall k k', match_cont k k' -> match_cont (Cminor.call_cont k) (call_cont k').
Proof.
  induction 1; simpl; auto. constructor. constructor; auto.
Qed.

Remark find_label_commut:
  forall lbl s k s' k',
  match_cont k k' ->
  sel_stmt hf ge s = OK s' ->
  match Cminor.find_label lbl s k, find_label lbl s' k' with
  | None, None => True
  | Some(s1, k1), Some(s1', k1') => sel_stmt hf ge s1 = OK s1' /\ match_cont k1 k1'
  | _, _ => False
  end.
Proof.
  induction s; intros until k'; simpl; intros MC SE; try (monadInv SE); simpl; auto.
(* store *)
  unfold store. destruct (addressing m (sel_expr hf e)); simpl; auto.
(* call *)
  destruct (classify_call ge e); simpl; auto.
(* tailcall *)
  destruct (classify_call ge e); simpl; auto.
(* seq *)
  exploit (IHs1 (Cminor.Kseq s2 k)). constructor; eauto. eauto.  
  destruct (Cminor.find_label lbl s1 (Cminor.Kseq s2 k)) as [[sx kx] | ];
  destruct (find_label lbl x (Kseq x0 k')) as [[sy ky] | ];
  intuition. apply IHs2; auto.
(* ifthenelse *)
  exploit (IHs1 k); eauto. 
  destruct (Cminor.find_label lbl s1 k) as [[sx kx] | ];
  destruct (find_label lbl x k') as [[sy ky] | ];
  intuition. apply IHs2; auto.
(* loop *)
  apply IHs. constructor; auto. simpl; rewrite EQ; auto. auto.
(* block *)
  apply IHs. constructor; auto. auto.
(* switch *)
  destruct b. 
  destruct (validate_switch Int64.modulus n l (compile_switch Int64.modulus n l)); inv SE.
  simpl; auto.
  destruct (validate_switch Int.modulus n l (compile_switch Int.modulus n l)); inv SE.
  simpl; auto.
(* return *)
  destruct o; inv SE; simpl; auto.
(* label *)
  destruct (ident_eq lbl l). auto. apply IHs; auto.
Qed.

Definition measure (s: Cminor.state) : nat :=
  match s with
  | Cminor.Callstate _ _ _ _ => 0%nat
  | Cminor.State _ _ _ _ _ _ => 1%nat
  | Cminor.Returnstate _ _ _ => 2%nat
  end.

Lemma sel_step_correct:
  forall S1 t S2, Cminor.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
  (exists T2, step tge T1 t T2 /\ match_states S2 T2)
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 T1)%nat.
Proof.
  induction 1; intros T1 ME; inv ME; try (monadInv TS).
- (* skip seq *)
  inv MC. left; econstructor; split. econstructor. constructor; auto.
- (* skip block *)
  inv MC. left; econstructor; split. econstructor. constructor; auto.
- (* skip call *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].
  left; econstructor; split. 
  econstructor. inv MC; simpl in H; simpl; auto. 
  eauto. 
  erewrite stackspace_function_translated; eauto. 
  constructor; auto.
- (* assign *)
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split.
  econstructor; eauto.
  constructor; auto. apply set_var_lessdef; auto.
- (* store *)
  exploit sel_expr_correct. eexact H. eauto. eauto. intros [vaddr' [A B]].
  exploit sel_expr_correct. eexact H0. eauto. eauto. intros [v' [C D]].
  exploit Mem.storev_extends; eauto. intros [m2' [P Q]].
  left; econstructor; split.
  eapply eval_store; eauto.
  constructor; auto.
- (* Scall *)
  exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].
  exploit classify_call_correct; eauto. 
  destruct (classify_call ge a) as [ | id | ef].
+ (* indirect *)
  exploit sel_expr_correct; eauto. intros [vf' [A B]].
  exploit functions_translated; eauto. intros (fd' & U & V).
  left; econstructor; split.
  econstructor; eauto. econstructor; eauto. 
  apply sig_function_translated; auto.
  constructor; auto. constructor; auto.
+ (* direct *)
  intros [b [U V]]. 
  exploit functions_translated; eauto. intros (fd' & X & Y).
  left; econstructor; split.
  econstructor; eauto.
  subst vf. econstructor; eauto. rewrite symbols_preserved; eauto.
  apply sig_function_translated; auto.
  constructor; auto. constructor; auto.
+ (* turned into Sbuiltin *)
  intros EQ. subst fd. 
  right; split. simpl. omega. split. auto. 
  econstructor; eauto.
- (* Stailcall *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  exploit sel_expr_correct; eauto. intros [vf' [A B]].
  exploit sel_exprlist_correct; eauto. intros [vargs' [C D]].
  exploit functions_translated; eauto. intros [fd' [E F]].
  left; econstructor; split.
  exploit classify_call_correct; eauto. 
  destruct (classify_call ge a) as [ | id | ef]; intros. 
  econstructor; eauto. econstructor; eauto. apply sig_function_translated; auto.
  destruct H2 as [b [U V]]. subst vf. inv B. 
  econstructor; eauto. econstructor; eauto. rewrite symbols_preserved; eauto. apply sig_function_translated; auto.
  econstructor; eauto. econstructor; eauto. apply sig_function_translated; auto.
  constructor; auto. apply call_cont_commut; auto.
- (* Sbuiltin *)
  exploit sel_exprlist_correct; eauto. intros [vargs' [P Q]].
  exploit external_call_mem_extends; eauto. 
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  econstructor. eauto. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.
  destruct optid; simpl; auto. apply set_var_lessdef; auto.
- (* Seq *)
  left; econstructor; split.
  constructor. constructor; auto. constructor; auto.
- (* Sifthenelse *)
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  assert (Val.bool_of_val v' b). inv B. auto. inv H0.
  left; exists (State f' (if b then x else x0) k' sp e' m'); split.
  econstructor; eauto. eapply eval_condexpr_of_expr; eauto. 
  constructor; auto. destruct b; auto.
- (* Sloop *)
  left; econstructor; split. constructor. constructor; auto.
  constructor; auto. simpl; rewrite EQ; auto.
- (* Sblock *)
  left; econstructor; split. constructor. constructor; auto. constructor; auto.
- (* Sexit seq *)
  inv MC. left; econstructor; split. constructor. constructor; auto.
- (* Sexit0 block *)
  inv MC. left; econstructor; split. constructor. constructor; auto.
- (* SexitS block *)
  inv MC. left; econstructor; split. constructor. constructor; auto.
- (* Sswitch *)
  inv H0; simpl in TS.
+ set (ct := compile_switch Int.modulus default cases) in *.
  destruct (validate_switch Int.modulus default cases ct) eqn:VALID; inv TS.
  exploit sel_expr_correct; eauto. intros [v' [A B]]. inv B.
  left; econstructor; split. 
  econstructor. eapply sel_switch_int_correct; eauto. 
  constructor; auto.
+ set (ct := compile_switch Int64.modulus default cases) in *.
  destruct (validate_switch Int64.modulus default cases ct) eqn:VALID; inv TS.
  exploit sel_expr_correct; eauto. intros [v' [A B]]. inv B.
  left; econstructor; split.
  econstructor. eapply sel_switch_long_correct; eauto. 
  constructor; auto.
- (* Sreturn None *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  left; econstructor; split. 
  econstructor. simpl; eauto. 
  constructor; auto. apply call_cont_commut; auto.
- (* Sreturn Some *)
  exploit Mem.free_parallel_extends; eauto. intros [m2' [P Q]].
  erewrite <- stackspace_function_translated in P by eauto.
  exploit sel_expr_correct; eauto. intros [v' [A B]].
  left; econstructor; split. 
  econstructor; eauto.
  constructor; auto. apply call_cont_commut; auto.
- (* Slabel *)
  left; econstructor; split. constructor. constructor; auto.
- (* Sgoto *)
  assert (sel_stmt hf ge (Cminor.fn_body f) = OK (fn_body f')).
  { monadInv TF; simpl; auto. }
  exploit (find_label_commut lbl (Cminor.fn_body f) (Cminor.call_cont k)).
    apply call_cont_commut; eauto. eauto.
  rewrite H. 
  destruct (find_label lbl (fn_body f') (call_cont k'0))
  as [[s'' k'']|] eqn:?; intros; try contradiction.
  destruct H1. 
  left; econstructor; split.
  econstructor; eauto. 
  constructor; auto.
- (* internal function *)
  monadInv TF. generalize EQ; intros TF; monadInv TF.
  exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl. 
  intros [m2' [A B]].
  left; econstructor; split.
  econstructor; simpl; eauto.
  constructor; simpl; auto. apply set_locals_lessdef. apply set_params_lessdef; auto.
- (* external call *)
  monadInv TF.
  exploit external_call_mem_extends; eauto. 
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  econstructor. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.
- (* external call turned into a Sbuiltin *)
  exploit external_call_mem_extends; eauto. 
  intros [vres' [m2 [A [B [C D]]]]].
  left; econstructor; split.
  econstructor. eauto. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.
- (* return *)
  inv MC. 
  left; econstructor; split. 
  econstructor. 
  constructor; auto. destruct optid; simpl; auto. apply set_var_lessdef; auto.
- (* return of an external call turned into a Sbuiltin *)
  right; split. simpl; omega. split. auto. constructor; auto. 
  destruct optid; simpl; auto. apply set_var_lessdef; auto.
Qed.

Lemma sel_initial_states:
  forall S, Cminor.initial_state prog S ->
  exists R, initial_state tprog R /\ match_states S R.
Proof.
  induction 1.
  exploit function_ptr_translated; eauto. intros (f' & A & B).
  econstructor; split.
  econstructor.
  eapply Genv.init_mem_transf_partial; eauto.
  simpl. fold tge. rewrite symbols_preserved.
  erewrite transform_partial_program_main by eauto. eexact H0.
  eauto.
  rewrite <- H2. apply sig_function_translated; auto.
  constructor; auto. constructor. apply Mem.extends_refl.
Qed.

Lemma sel_final_states:
  forall S R r,
  match_states S R -> Cminor.final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H. inv MC. inv LD. constructor.
Qed.

End PRESERVATION.

Axiom get_helpers_correct:
  forall ge hf, get_helpers ge = OK hf -> i64_helpers_correct ge hf.

Theorem transf_program_correct:
  forall prog tprog,
  sel_program prog = OK tprog ->
  forward_simulation (Cminor.semantics prog) (CminorSel.semantics tprog).
Proof.
  intros. unfold sel_program in H. 
  destruct (get_helpers (Genv.globalenv prog)) as [hf|] eqn:E; simpl in H; try discriminate.
  apply forward_simulation_opt with (match_states := match_states prog tprog hf) (measure := measure). 
  eapply symbols_preserved; eauto.
  apply sel_initial_states; auto.
  apply sel_final_states; auto.
  apply sel_step_correct; auto. eapply helpers_correct_preserved; eauto. apply get_helpers_correct. auto.
Qed.
