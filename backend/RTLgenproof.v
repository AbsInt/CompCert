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

(** Correctness proof for RTL generation. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Smallstep.
Require Import Globalenvs.
Require Import Switch.
Require Import Registers.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import RTL.
Require Import RTLgen.
Require Import RTLgenspec.

(** * Correspondence between Cminor environments and RTL register sets *)

(** A compilation environment (mapping) is well-formed if
  the following properties hold:
- Two distinct Cminor local variables are mapped to distinct pseudo-registers.
- A Cminor local variable and a let-bound variable are mapped to
  distinct pseudo-registers.
*)

Record map_wf (m: mapping) : Prop :=
  mk_map_wf {
    map_wf_inj:
      (forall id1 id2 r,
         m.(map_vars)!id1 = Some r -> m.(map_vars)!id2 = Some r -> id1 = id2);
     map_wf_disj:
      (forall id r,
         m.(map_vars)!id = Some r -> In r m.(map_letvars) -> False)
  }.

Lemma init_mapping_wf:
  map_wf init_mapping.
Proof.
  unfold init_mapping; split; simpl.
  intros until r. rewrite PTree.gempty. congruence.
  tauto.
Qed.

Lemma add_var_wf:
  forall s1 s2 map name r map' i,
  add_var map name s1 = OK (r,map') s2 i -> 
  map_wf map -> map_valid map s1 -> map_wf map'.
Proof.
  intros. monadInv H. 
  apply mk_map_wf; simpl.
  intros until r0. repeat rewrite PTree.gsspec.
  destruct (peq id1 name); destruct (peq id2 name).
  congruence.
  intros. inv H. elimtype False. 
  apply valid_fresh_absurd with r0 s1. 
  apply H1. left; exists id2; auto.
  eauto with rtlg.
  intros. inv H2. elimtype False. 
  apply valid_fresh_absurd with r0 s1. 
  apply H1. left; exists id1; auto.
  eauto with rtlg.
  inv H0. eauto.
  intros until r0. rewrite PTree.gsspec.
  destruct (peq id name). 
  intros. inv H.
  apply valid_fresh_absurd with r0 s1.
  apply H1. right; auto.
  eauto with rtlg.
  inv H0; eauto.
Qed.

Lemma add_vars_wf:
  forall names s1 s2 map map' rl i,
  add_vars map names s1 = OK (rl,map') s2 i ->
  map_wf map -> map_valid map s1 -> map_wf map'.
Proof.
  induction names; simpl; intros; monadInv H. 
  auto.
  exploit add_vars_valid; eauto. intros [A B].
  eapply add_var_wf; eauto.
Qed.

Lemma add_letvar_wf:
  forall map r,
  map_wf map -> ~reg_in_map map r -> map_wf (add_letvar map r).
Proof.
  intros. inv H. unfold add_letvar; constructor; simpl.
  auto.
  intros. elim H1; intro. subst r0. elim H0. left; exists id; auto.
  eauto.
Qed.

(** An RTL register environment matches a CminorSel local environment and
  let-environment if the value of every local or let-bound variable in
  the CminorSel environments is identical to the value of the
  corresponding pseudo-register in the RTL register environment. *)

Record match_env
      (map: mapping) (e: env) (le: letenv) (rs: regset) : Prop :=
  mk_match_env {
    me_vars:
      (forall id v,
         e!id = Some v -> exists r, map.(map_vars)!id = Some r /\ rs#r = v);
    me_letvars:
      rs##(map.(map_letvars)) = le
  }.

Lemma match_env_find_var:
  forall map e le rs id v r,
  match_env map e le rs ->
  e!id = Some v ->
  map.(map_vars)!id = Some r ->
  rs#r = v.
Proof.
  intros. exploit me_vars; eauto. intros [r' [EQ' RS]].
  replace r with r'. auto. congruence.
Qed.

Lemma match_env_find_letvar:
  forall map e le rs idx v r,
  match_env map e le rs ->
  List.nth_error le idx = Some v ->
  List.nth_error map.(map_letvars) idx = Some r ->
  rs#r = v.
Proof.
  intros. exploit me_letvars; eauto. intros.
  rewrite <- H2 in H0. rewrite list_map_nth in H0. 
  change reg with positive in H1. rewrite H1 in H0. 
  simpl in H0. congruence.
Qed.

Lemma match_env_invariant:
  forall map e le rs rs',
  match_env map e le rs ->
  (forall r, (reg_in_map map r) -> rs'#r = rs#r) ->
  match_env map e le rs'.
Proof.
  intros. inversion H. apply mk_match_env.
  intros. exploit me_vars0; eauto. intros [r [A B]].
  exists r; split. auto. rewrite H0; auto. left; exists id; auto.
  rewrite <- me_letvars0. apply list_map_exten. intros.
  symmetry. apply H0. right; auto.
Qed.

(** Matching between environments is preserved when an unmapped register
  (not corresponding to any Cminor variable) is assigned in the RTL
  execution. *)

Lemma match_env_update_temp:
  forall map e le rs r v,
  match_env map e le rs ->
  ~(reg_in_map map r) ->
  match_env map e le (rs#r <- v).
Proof.
  intros. apply match_env_invariant with rs; auto.
  intros. case (Reg.eq r r0); intro. 
  subst r0; contradiction.
  apply Regmap.gso; auto.
Qed.
Hint Resolve match_env_update_temp: rtlg.

(** Matching between environments is preserved by simultaneous
  assignment to a Cminor local variable (in the Cminor environments)
  and to the corresponding RTL pseudo-register (in the RTL register
  environment). *)

Lemma match_env_update_var:
  forall map e le rs id r v,
  map_wf map ->
  map.(map_vars)!id = Some r ->
  match_env map e le rs ->
  match_env map (PTree.set id v e) le (rs#r <- v).
Proof.
  intros. inversion H. inversion H1. apply mk_match_env.
  intros id' v'. rewrite PTree.gsspec. destruct (peq id' id); intros.
  subst id'. inv H2. exists r; split. auto. apply PMap.gss.
  exploit me_vars0; eauto. intros [r' [A B]].
  exists r'; split. auto. rewrite PMap.gso; auto.
  red; intros. subst r'. elim n. eauto.
  rewrite <- me_letvars0. apply list_map_exten; intros.
  symmetry. apply PMap.gso. red; intros. subst x. eauto. 
Qed.

Lemma match_env_bind_letvar:
  forall map e le rs r v,
  match_env map e le rs ->
  rs#r = v ->
  match_env (add_letvar map r) e (v :: le) rs.
Proof.
  intros. inv H. unfold add_letvar. apply mk_match_env; simpl; auto.
Qed.

Lemma match_env_unbind_letvar:
  forall map e le rs r v,
  match_env (add_letvar map r) e (v :: le) rs ->
  match_env map e le rs.
Proof.
  unfold add_letvar; intros. inv H. simpl in *. 
  constructor. auto. congruence.
Qed.

Lemma match_env_empty:
  forall map,
  map.(map_letvars) = nil ->
  match_env map (PTree.empty val) nil (Regmap.init Vundef).
Proof.
  intros. apply mk_match_env.
  intros. rewrite PTree.gempty in H0. discriminate.
  rewrite H. reflexivity.
Qed.

(** The assignment of function arguments to local variables (on the Cminor
  side) and pseudo-registers (on the RTL side) preserves matching
  between environments. *)

Lemma match_set_params_init_regs:
  forall il rl s1 map2 s2 vl i,
  add_vars init_mapping il s1 = OK (rl, map2) s2 i ->
  match_env map2 (set_params vl il) nil (init_regs vl rl)
  /\ (forall r, reg_fresh r s2 -> (init_regs vl rl)#r = Vundef).
Proof.
  induction il; intros.

  inv H. split. apply match_env_empty. auto. intros. 
  simpl. apply Regmap.gi.

  monadInv H. simpl.
  exploit add_vars_valid; eauto. apply init_mapping_valid. intros [A B].
  exploit add_var_valid; eauto. intros [A' B']. clear B'.
  monadInv EQ1. 
  destruct vl as [ | v1 vs].
  (* vl = nil *)
  destruct (IHil _ _ _ _ nil _ EQ) as [ME UNDEF]. inv ME. split.
  constructor; simpl.
  intros id v. repeat rewrite PTree.gsspec. destruct (peq id a); intros.
  subst a. inv H. exists x1; split. auto. apply Regmap.gi.
  replace (init_regs nil x) with (Regmap.init Vundef) in me_vars0. eauto.
  destruct x; reflexivity.
  destruct (map_letvars x0). auto. simpl in me_letvars0. congruence.
  intros. apply Regmap.gi.
  (* vl = v1 :: vs *)
  destruct (IHil _ _ _ _ vs _ EQ) as [ME UNDEF]. inv ME. split.
  constructor; simpl.
  intros id v. repeat rewrite PTree.gsspec. destruct (peq id a); intros.
  subst a. inv H. exists x1; split. auto. apply Regmap.gss.
  exploit me_vars0; eauto. intros [r' [C D]]. 
  exists r'; split. auto. rewrite Regmap.gso. auto.
  apply valid_fresh_different with s.
  apply B. left; exists id; auto.
  eauto with rtlg. 
  destruct (map_letvars x0). auto. simpl in me_letvars0. congruence.
  intros. rewrite Regmap.gso. apply UNDEF. 
  apply reg_fresh_decr with s2; eauto with rtlg.
  apply sym_not_equal. apply valid_fresh_different with s2; auto.
Qed.

Lemma match_set_locals:
  forall map1 s1,
  map_wf map1 ->
  forall il rl map2 s2 e le rs i,
  match_env map1 e le rs ->
  (forall r, reg_fresh r s1 -> rs#r = Vundef) ->
  add_vars map1 il s1 = OK (rl, map2) s2 i ->
  match_env map2 (set_locals il e) le rs.
Proof.
  induction il; simpl in *; intros.

  inv H2. auto.

  monadInv H2. 
  exploit IHil; eauto. intro. 
  monadInv EQ1.
  constructor.
  intros id v. simpl. repeat rewrite PTree.gsspec. 
  destruct (peq id a). subst a. intro. 
  exists x1. split. auto. inv H3. 
  apply H1. apply reg_fresh_decr with s. auto.
  eauto with rtlg.
  intros. eapply me_vars; eauto. 
  simpl. eapply me_letvars; eauto.
Qed.

Lemma match_init_env_init_reg:
  forall params s0 rparams map1 s1 i1 vars rvars map2 s2 i2 vparams,
  add_vars init_mapping params s0 = OK (rparams, map1) s1 i1 ->
  add_vars map1 vars s1 = OK (rvars, map2) s2 i2 ->
  match_env map2 (set_locals vars (set_params vparams params))
            nil (init_regs vparams rparams).
Proof.
  intros.
  exploit match_set_params_init_regs; eauto. intros [A B].
  eapply match_set_locals; eauto.
  eapply add_vars_wf; eauto. apply init_mapping_wf.
  apply init_mapping_valid.
Qed.

(** * The simulation argument *)

Require Import Errors.

Section CORRECTNESS.

Variable prog: CminorSel.program.
Variable tprog: RTL.program.
Hypothesis TRANSL: transl_program prog = OK tprog.

Let ge : CminorSel.genv := Genv.globalenv prog.
Let tge : RTL.genv := Genv.globalenv tprog.

(** Relationship between the global environments for the original
  CminorSel program and the generated RTL program. *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof
  (Genv.find_symbol_transf_partial transl_fundef _ TRANSL).

Lemma function_ptr_translated:
  forall (b: block) (f: CminorSel.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transl_fundef TRANSL).

Lemma functions_translated:
  forall (v: val) (f: CminorSel.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef f = OK tf.
Proof
  (Genv.find_funct_transf_partial transl_fundef TRANSL).

Lemma sig_transl_function:
  forall (f: CminorSel.fundef) (tf: RTL.fundef),
  transl_fundef f = OK tf ->
  RTL.funsig tf = CminorSel.funsig f.
Proof.
  intros until tf. unfold transl_fundef, transf_partial_fundef.
  case f; intro.
  unfold transl_function. 
  case (transl_fun f0 init_state); simpl; intros.
  discriminate.
  destruct p. simpl in H. inversion H. reflexivity.
  intro. inversion H. reflexivity.
Qed.

(** Correctness of the code generated by [add_move]. *)

Lemma tr_move_correct:
  forall r1 ns r2 nd cs code sp rs m,
  tr_move code ns r1 nd r2 ->
  exists rs',
  star step tge (State cs code sp ns rs m) E0 (State cs code sp nd rs' m) /\
  rs'#r2 = rs#r1 /\
  (forall r, r <> r2 -> rs'#r = rs#r).
Proof.
  intros. inv H. 
  exists rs; split. constructor. auto.
  exists (rs#r2 <- (rs#r1)); split. 
  apply star_one. eapply exec_Iop. eauto. auto. 
  split. apply Regmap.gss. intros; apply Regmap.gso; auto.
Qed.

(** Correctness of the code generated by [store_var] and [store_optvar]. *)

Lemma tr_store_var_correct:
  forall rs cs code map r id ns nd e sp m,
  tr_store_var code map r id ns nd ->
  map_wf map ->
  match_env map e nil rs ->
  exists rs',
     star step tge (State cs code sp ns rs m)
                E0 (State cs code sp nd rs' m)
  /\ match_env map (PTree.set id rs#r e) nil rs'.
Proof.
  intros. destruct H as [rv [A B]].
  exploit tr_move_correct; eauto. intros [rs' [EX [RES OTHER]]].
  exists rs'; split. eexact EX.
  apply match_env_invariant with (rs#rv <- (rs#r)).
  apply match_env_update_var; auto.
  intros. rewrite Regmap.gsspec. destruct (peq r0 rv).
  subst r0; auto.
  auto.
Qed.

Lemma tr_store_optvar_correct:
  forall rs cs code map r optid ns nd e sp m,
  tr_store_optvar code map r optid ns nd ->
  map_wf map ->
  match_env map e nil rs ->
  exists rs',
     star step tge (State cs code sp ns rs m)
                E0 (State cs code sp nd rs' m)
  /\ match_env map (set_optvar optid rs#r e) nil rs'.
Proof.
  intros. destruct optid; simpl in *.
  eapply tr_store_var_correct; eauto.
  exists rs; split. subst nd. apply star_refl. auto.  
Qed.

(** ** Semantic preservation for the translation of expressions *)

Section CORRECTNESS_EXPR.

Variable sp: val.
Variable e: env.
Variable m: mem.

(** The proof of semantic preservation for the translation of expressions
  is a simulation argument based on diagrams of the following form:
<<
                    I /\ P
    e, le, m, a ------------- State cs code sp ns rs m
         ||                      |
        t||                     t|*
         ||                      |
         \/                      v
    e, le, m', v ------------ State cs code sp nd rs' m'
                    I /\ Q
>>
  where [tr_expr code map pr a ns nd rd] is assumed to hold.
  The left vertical arrow represents an evaluation of the expression [a].
  The right vertical arrow represents the execution of zero, one or
  several instructions in the generated RTL flow graph [code].

  The invariant [I] is the agreement between Cminor environments and
  RTL register environment, as captured by [match_envs].

  The precondition [P] includes the well-formedness of the compilation
  environment [mut].

  The postconditions [Q] state that in the final register environment
  [rs'], register [rd] contains value [v], and the registers in
  the set of preserved registers [pr] are unchanged, as are the registers
  in the codomain of [map].

  We formalize this simulation property by the following predicate
  parameterized by the CminorSel evaluation (left arrow).  *)

Definition transl_expr_prop 
     (le: letenv) (a: expr) (v: val) : Prop :=
  forall cs code map pr ns nd rd rs
    (MWF: map_wf map)
    (TE: tr_expr code map pr a ns nd rd)
    (ME: match_env map e le rs),
  exists rs',
     star step tge (State cs code sp ns rs m) E0 (State cs code sp nd rs' m)
  /\ match_env map e le rs'
  /\ rs'#rd = v
  /\ (forall r, reg_in_map map r \/ In r pr -> rs'#r = rs#r).

(** The simulation properties for lists of expressions and for
  conditional expressions are similar. *)

Definition transl_exprlist_prop 
     (le: letenv) (al: exprlist) (vl: list val) : Prop :=
  forall cs code map pr ns nd rl rs
    (MWF: map_wf map)
    (TE: tr_exprlist code map pr al ns nd rl)
    (ME: match_env map e le rs),
  exists rs',
     star step tge (State cs code sp ns rs m) E0 (State cs code sp nd rs' m)
  /\ match_env map e le rs'
  /\ rs'##rl = vl
  /\ (forall r, reg_in_map map r \/ In r pr -> rs'#r = rs#r).

Definition transl_condition_prop 
     (le: letenv) (a: condexpr) (vb: bool) : Prop :=
  forall cs code map pr ns ntrue nfalse rs
    (MWF: map_wf map)
    (TE: tr_condition code map pr a ns ntrue nfalse)
    (ME: match_env map e le rs),
  exists rs',
     star step tge (State cs code sp ns rs m) E0
                   (State cs code sp (if vb then ntrue else nfalse) rs' m)
  /\ match_env map e le rs'
  /\ (forall r, reg_in_map map r \/ In r pr -> rs'#r = rs#r).



(** The correctness of the translation is a huge induction over
  the Cminor evaluation derivation for the source program.  To keep
  the proof manageable, we put each case of the proof in a separate
  lemma.  There is one lemma for each Cminor evaluation rule.
  It takes as hypotheses the premises of the Cminor evaluation rule,
  plus the induction hypotheses, that is, the [transl_expr_prop], etc,
  corresponding to the evaluations of sub-expressions or sub-statements. *)

Lemma transl_expr_Evar_correct:
  forall (le : letenv) (id : positive) (v : val),
  e ! id = Some v ->
  transl_expr_prop le (Evar id) v.
Proof.
  intros; red; intros. inv TE.
  exploit tr_move_correct; eauto. intros [rs' [A [B C]]]. 
  exists rs'; split. eauto.
  destruct H2 as [D | [E F]].
  (* optimized case *)
  subst r.
  assert (forall r, rs'#r = rs#r).
    intros. destruct (Reg.eq r rd). subst r. auto. auto. 
  split. eapply match_env_invariant; eauto.
  split. rewrite B. eapply match_env_find_var; eauto.
  auto.
  (* general case *)
  split. eapply match_env_invariant; eauto. 
    intros. apply C. congruence. 
  split. rewrite B. eapply match_env_find_var; eauto. 
  intros. apply C. intuition congruence.
Qed.

Lemma transl_expr_Eop_correct:
  forall (le : letenv) (op : operation) (args : exprlist)
         (vargs : list val) (v : val),
  eval_exprlist ge sp e m le args vargs ->
  transl_exprlist_prop le args vargs ->
  eval_operation ge sp op vargs m = Some v ->
  transl_expr_prop le (Eop op args) v.
Proof.
  intros; red; intros. inv TE. 
  exploit H0; eauto. intros [rs1 [EX1 [ME1 [RR1 RO1]]]].
  exists (rs1#rd <- v).
(* Exec *)
  split. eapply star_right. eexact EX1.
  eapply exec_Iop; eauto.  
  subst vargs.
  rewrite (@eval_operation_preserved CminorSel.fundef RTL.fundef ge tge). 
  auto. 
  exact symbols_preserved. traceEq.
(* Match-env *)
  split. eauto with rtlg.  
(* Result reg *)
  split. apply Regmap.gss.
(* Other regs *)
  intros. rewrite Regmap.gso. auto. intuition congruence.
Qed.

Lemma transl_expr_Eload_correct:
  forall (le : letenv) (chunk : memory_chunk) (addr : Op.addressing)
         (args : exprlist) (vargs : list val) (vaddr v : val),
  eval_exprlist ge sp e m le args vargs ->
  transl_exprlist_prop le args vargs ->
  Op.eval_addressing ge sp addr vargs = Some vaddr ->
  loadv chunk m vaddr = Some v ->
  transl_expr_prop le (Eload chunk addr args) v.
Proof.
  intros; red; intros. inv TE.
  exploit H0; eauto. intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  exists (rs1#rd <- v).
(* Exec *)
  split. eapply star_right. eexact EX1. eapply exec_Iload; eauto.
  rewrite RES1. rewrite (@eval_addressing_preserved _ _ ge tge).
  exact H1. exact symbols_preserved. traceEq.
(* Match-env *)
  split. eauto with rtlg. 
(* Result *)
  split. apply Regmap.gss.
(* Other regs *)
  intros. rewrite Regmap.gso. auto. intuition congruence. 
Qed.

Lemma transl_expr_Econdition_correct:
  forall (le : letenv) (cond : condexpr) (ifso ifnot : expr)
         (vcond : bool) (v : val),
  eval_condexpr ge sp e m le cond vcond ->
  transl_condition_prop le cond vcond ->
  eval_expr ge sp e m le (if vcond then ifso else ifnot) v ->
  transl_expr_prop le (if vcond then ifso else ifnot) v ->
  transl_expr_prop le (Econdition cond ifso ifnot) v.
Proof.
  intros; red; intros; inv TE. 
  exploit H0; eauto. intros [rs1 [EX1 [ME1 OTHER1]]].
  assert (tr_expr code map pr (if vcond then ifso else ifnot) (if vcond then ntrue else nfalse) nd rd).
    destruct vcond; auto.
  exploit H2; eauto. intros [rs2 [EX2 [ME2 [RES2 OTHER2]]]].
  exists rs2.
(* Exec *)
  split. eapply star_trans. eexact EX1. eexact EX2. auto. 
(* Match-env *)
  split. assumption.
(* Result value *)
  split. assumption.
(* Other regs *)
  intros. transitivity (rs1#r); auto.
Qed.

Lemma transl_expr_Elet_correct:
  forall (le : letenv) (a1 a2 : expr) (v1 v2 : val),
  eval_expr ge sp e m le a1 v1 ->
  transl_expr_prop le a1 v1 ->
  eval_expr ge sp e m (v1 :: le) a2 v2 ->
  transl_expr_prop (v1 :: le) a2 v2 ->
  transl_expr_prop le (Elet a1 a2) v2.
Proof.
  intros; red; intros; inv TE. 
  exploit H0; eauto. intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  assert (map_wf (add_letvar map r)).
    eapply add_letvar_wf; eauto. 
  exploit H2; eauto. eapply match_env_bind_letvar; eauto. 
  intros [rs2 [EX2 [ME3 [RES2 OTHER2]]]].
  exists rs2.
(* Exec *)
  split. eapply star_trans. eexact EX1. eexact EX2. auto.
(* Match-env *)
  split. eapply match_env_unbind_letvar; eauto.
(* Result *)
  split. assumption.
(* Other regs *)
  intros. transitivity (rs1#r0). 
  apply OTHER2. elim H4; intro; auto.
  unfold reg_in_map, add_letvar; simpl.
  unfold reg_in_map in H6; tauto.
  auto.
Qed.

Lemma transl_expr_Eletvar_correct:
  forall (le : list val) (n : nat) (v : val),
  nth_error le n = Some v ->
  transl_expr_prop le (Eletvar n) v.
Proof.
  intros; red; intros; inv TE.
  exploit tr_move_correct; eauto. intros [rs1 [EX1 [RES1 OTHER1]]].
  exists rs1.
(* Exec *)
  split. eexact EX1.
(* Match-env *)
  split. apply match_env_invariant with rs. auto.
  intros. destruct H2 as [A | [B C]]. 
  subst r. destruct (Reg.eq r0 rd). subst r0; auto. auto.
  apply OTHER1. intuition congruence.
(* Result *)
  split. rewrite RES1. eapply match_env_find_letvar; eauto. 
(* Other regs *)
  intros. destruct H2 as [A | [B C]]. 
  subst r. destruct (Reg.eq r0 rd). subst r0; auto. auto.
  apply OTHER1. intuition congruence.
Qed.

Lemma transl_condition_CEtrue_correct:
  forall (le : letenv),
  transl_condition_prop le CEtrue true.
Proof.
  intros; red; intros; inv TE. 
  exists rs. split. apply star_refl. split. auto. auto.
Qed.    

Lemma transl_condition_CEfalse_correct:
  forall (le : letenv),
  transl_condition_prop le CEfalse false.
Proof.
  intros; red; intros; inv TE. 
  exists rs. split. apply star_refl. split. auto. auto.
Qed.    

Lemma transl_condition_CEcond_correct:
  forall (le : letenv) (cond : condition) (args : exprlist)
         (vargs : list val) (b : bool),
  eval_exprlist ge sp e m le args vargs ->
  transl_exprlist_prop le args vargs ->
  eval_condition cond vargs m = Some b ->
  transl_condition_prop le (CEcond cond args) b.
Proof.
  intros; red; intros; inv TE.
  exploit H0; eauto. intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  exists rs1.
(* Exec *)
  split. eapply star_right. eexact EX1. 
  destruct b.
  eapply exec_Icond_true; eauto. 
  rewrite RES1. assumption.
  eapply exec_Icond_false; eauto. 
  rewrite RES1. assumption.
  traceEq.
(* Match-env *)
  split. assumption.
(* Regs *)
  auto.
Qed.

Lemma transl_condition_CEcondition_correct:
  forall (le : letenv) (cond ifso ifnot : condexpr) (vcond v : bool),
  eval_condexpr ge sp e m le cond vcond ->
  transl_condition_prop le cond vcond ->
  eval_condexpr ge sp e m le (if vcond then ifso else ifnot) v ->
  transl_condition_prop le (if vcond then ifso else ifnot) v ->
  transl_condition_prop le (CEcondition cond ifso ifnot) v.
Proof.
  intros; red; intros; inv TE. 
  exploit H0; eauto. intros [rs1 [EX1 [ME1 OTHER1]]].
  assert (tr_condition code map pr (if vcond then ifso else ifnot)
             (if vcond then ntrue' else nfalse') ntrue nfalse).
    destruct vcond; auto.
  exploit H2; eauto. intros [rs2 [EX2 [ME2 OTHER2]]].
  exists rs2.
(* Execution *)
  split. eapply star_trans. eexact EX1. eexact EX2. auto. 
(* Match-env *)
  split. auto.
(* Regs *)
  intros. transitivity (rs1#r); auto.
Qed.
 
Lemma transl_exprlist_Enil_correct:
  forall (le : letenv),
  transl_exprlist_prop le Enil nil.
Proof.
  intros; red; intros; inv TE.
  exists rs.
  split. apply star_refl.
  split. assumption.
  split. reflexivity.
  auto.
Qed.

Lemma transl_exprlist_Econs_correct:
  forall (le : letenv) (a1 : expr) (al : exprlist) (v1 : val)
         (vl : list val),
  eval_expr ge sp e m le a1 v1 ->
  transl_expr_prop le a1 v1 ->
  eval_exprlist ge sp e m le al vl ->
  transl_exprlist_prop le al vl ->
  transl_exprlist_prop le (Econs a1 al) (v1 :: vl).
Proof.
  intros; red; intros; inv TE.
  exploit H0; eauto. intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  exploit H2; eauto. intros [rs2 [EX2 [ME2 [RES2 OTHER2]]]].
  exists rs2.
(* Exec *)
  split. eapply star_trans. eexact EX1. eexact EX2. auto. 
(* Match-env *)
  split. assumption.
(* Results *)
  split. simpl. rewrite RES2. rewrite OTHER2. rewrite RES1. auto.
  simpl; tauto. 
(* Other regs *)
  intros. transitivity (rs1#r).
  apply OTHER2; auto. simpl; tauto. 
  apply OTHER1; auto.
Qed.

Theorem transl_expr_correct:
  forall le a v,
  eval_expr ge sp e m le a v ->
  transl_expr_prop le a v.
Proof
  (eval_expr_ind3 ge sp e m
     transl_expr_prop
     transl_condition_prop
     transl_exprlist_prop
     transl_expr_Evar_correct
     transl_expr_Eop_correct
     transl_expr_Eload_correct
     transl_expr_Econdition_correct
     transl_expr_Elet_correct
     transl_expr_Eletvar_correct
     transl_condition_CEtrue_correct
     transl_condition_CEfalse_correct
     transl_condition_CEcond_correct
     transl_condition_CEcondition_correct
     transl_exprlist_Enil_correct
     transl_exprlist_Econs_correct).

Theorem transl_condexpr_correct:
  forall le a v,
  eval_condexpr ge sp e m le a v ->
  transl_condition_prop le a v.
Proof
  (eval_condexpr_ind3 ge sp e m
     transl_expr_prop
     transl_condition_prop
     transl_exprlist_prop
     transl_expr_Evar_correct
     transl_expr_Eop_correct
     transl_expr_Eload_correct
     transl_expr_Econdition_correct
     transl_expr_Elet_correct
     transl_expr_Eletvar_correct
     transl_condition_CEtrue_correct
     transl_condition_CEfalse_correct
     transl_condition_CEcond_correct
     transl_condition_CEcondition_correct
     transl_exprlist_Enil_correct
     transl_exprlist_Econs_correct).


Theorem transl_exprlist_correct:
  forall le a v,
  eval_exprlist ge sp e m le a v ->
  transl_exprlist_prop le a v.
Proof
  (eval_exprlist_ind3 ge sp e m
     transl_expr_prop
     transl_condition_prop
     transl_exprlist_prop
     transl_expr_Evar_correct
     transl_expr_Eop_correct
     transl_expr_Eload_correct
     transl_expr_Econdition_correct
     transl_expr_Elet_correct
     transl_expr_Eletvar_correct
     transl_condition_CEtrue_correct
     transl_condition_CEfalse_correct
     transl_condition_CEcond_correct
     transl_condition_CEcondition_correct
     transl_exprlist_Enil_correct
     transl_exprlist_Econs_correct).

End CORRECTNESS_EXPR.

(** ** Semantic preservation for the translation of terminating statements *)   

(** The simulation diagram for the translation of statements
  is of the following form:
<<
                    I /\ P
       e, m, a ---------------- State cs code sp ns rs m
         ||                          |
        t||                         t|*
         ||                          |
         \/                          v
     e', m', out ------------------ st'
                    I /\ Q
>>
  where [tr_stmt code map a ns ncont nexits nret rret] holds.
  The left vertical arrow represents an execution of the statement [a].
  The right vertical arrow represents the execution of
  zero, one or several instructions in the generated RTL flow graph [code].

  The invariant [I] is the agreement between Cminor environments and
  RTL register environment, as captured by [match_envs].

  The precondition [P] is the well-formedness of the compilation
  environment [mut].

  The postcondition [Q] characterizes the final RTL state [st'].
  It must have memory state [m'] and register state [rs'] that matches
  [e'].  Moreover, the program point reached must correspond to the outcome
  [out].  This is captured by the following [state_for_outcome] predicate. *)

Inductive state_for_outcome
           (ncont: node) (nexits: list node) (nret: node) (rret: option reg)
           (cs: list stackframe) (c: code) (sp: val) (rs: regset) (m: mem):
           outcome -> RTL.state -> Prop :=
  | state_for_normal:
      state_for_outcome ncont nexits nret rret cs c sp rs m
                        Out_normal (State cs c sp ncont rs m)
  | state_for_exit: forall n nexit,
      nth_error nexits n = Some nexit ->
      state_for_outcome ncont nexits nret rret cs c sp rs m
                        (Out_exit n) (State cs c sp nexit rs m)
  | state_for_return_none:
      rret = None ->
      state_for_outcome ncont nexits nret rret cs c sp rs m
                        (Out_return None) (State cs c sp nret rs m)
  | state_for_return_some: forall r v,
      rret = Some r ->
      rs#r = v ->
      state_for_outcome ncont nexits nret rret cs c sp rs m
                        (Out_return (Some v)) (State cs c sp nret rs m)
  | state_for_return_tail: forall v,
      state_for_outcome ncont nexits nret rret cs c sp rs m
                        (Out_tailcall_return v) (Returnstate cs v m).

Definition transl_stmt_prop 
  (sp: val) (e: env) (m: mem) (a: stmt)
  (t: trace) (e': env) (m': mem) (out: outcome) : Prop :=
  forall cs code map ns ncont nexits nret rret rs
    (MWF: map_wf map)
    (TE: tr_stmt code map a ns ncont nexits nret rret)
    (ME: match_env map e nil rs),
  exists rs', exists st,
     state_for_outcome ncont nexits nret rret cs code sp rs' m' out st
  /\ star step tge (State cs code sp ns rs m) t st
  /\ match_env map e' nil rs'.

(** Finally, the correctness condition for the translation of functions
  is that the translated RTL function, when applied to the same arguments
  as the original Cminor function, returns the same value and performs
  the same modifications on the memory state. *)

Definition transl_function_prop
    (m: mem) (f: CminorSel.fundef) (vargs: list val)
    (t: trace) (m': mem) (vres: val) : Prop :=
  forall cs tf
    (TE: transl_fundef f = OK tf),
  star step tge (Callstate cs tf vargs m) t (Returnstate cs vres m').

Lemma transl_funcall_internal_correct:
  forall (m : mem) (f : CminorSel.function)
         (vargs : list val) (m1 : mem) (sp : block) (e : env) (t : trace)
         (e2 : env) (m2 : mem) (out: outcome) (vres : val),
  Mem.alloc m 0 (fn_stackspace f) = (m1, sp) ->
  set_locals (fn_vars f) (set_params vargs (CminorSel.fn_params f)) = e ->
  exec_stmt ge (Vptr sp Int.zero) e m1 (fn_body f) t e2 m2 out ->
  transl_stmt_prop (Vptr sp Int.zero) e m1 (fn_body f) t e2 m2 out ->
  outcome_result_value out f.(CminorSel.fn_sig).(sig_res) vres ->
  transl_function_prop m (Internal f) vargs t 
                            (outcome_free_mem out m2 sp) vres.
Proof.
  intros; red; intros.
  generalize TE; simpl. caseEq (transl_function f); simpl. 2: congruence.
  intros tfi EQ1 EQ2. injection EQ2; clear EQ2; intro EQ2.
  assert (TR: tr_function f tfi). apply transl_function_charact; auto.
  rewrite <- EQ2. inversion TR. subst f0. 

  pose (rs := init_regs vargs rparams).
  assert (ME: match_env map2 e nil rs).
  rewrite <- H0. unfold rs. 
  eapply match_init_env_init_reg; eauto.

  assert (MWF: map_wf map2).
    assert (map_valid init_mapping init_state) by apply init_mapping_valid.
    exploit (add_vars_valid (CminorSel.fn_params f)); eauto. intros [A B].
    eapply add_vars_wf; eauto. eapply add_vars_wf; eauto. apply init_mapping_wf.

  exploit H2; eauto. intros [rs' [st [OUT [EX ME']]]].

  eapply star_left.
  eapply exec_function_internal; eauto. simpl.
  inversion OUT; clear OUT; subst out st; simpl in H3; simpl.

  (* Out_normal *)
  unfold ret_reg in H6. destruct (sig_res (CminorSel.fn_sig f)). contradiction. 
  subst vres orret. 
  eapply star_right. unfold rs in EX. eexact EX.
  change Vundef with (regmap_optget None Vundef rs').
  apply exec_Ireturn. auto. reflexivity.

  (* Out_exit *)
  contradiction.

  (* Out_return None *)
  subst orret.
  unfold ret_reg in H8. destruct (sig_res (CminorSel.fn_sig f)). contradiction.
  subst vres. 
  eapply star_right. unfold rs in EX. eexact EX. 
  change Vundef with (regmap_optget None Vundef rs').
  apply exec_Ireturn. auto.
  reflexivity. 

  (* Out_return Some *)
  subst orret. 
  unfold ret_reg in H8. unfold ret_reg in H9.
  destruct (sig_res (CminorSel.fn_sig f)). inversion H9.
  subst vres.    
  eapply star_right. unfold rs in EX. eexact EX.
  replace v with (regmap_optget (Some rret) Vundef rs').
  apply exec_Ireturn. auto.
  simpl. congruence. 
  reflexivity.
  contradiction.

  (* a tail call *)
  subst v. rewrite E0_right. auto. traceEq.
Qed.

Lemma transl_funcall_external_correct:
  forall (ef : external_function) (m : mem) (args : list val) (t: trace) (res : val),
  event_match ef args t res ->
  transl_function_prop m (External ef) args t m res.
Proof.
  intros; red; intros. unfold transl_function in TE; simpl in TE.
  inversion TE; subst tf. 
  apply star_one. apply exec_function_external. auto.
Qed.

Lemma transl_stmt_Sskip_correct:
  forall (sp: val) (e : env) (m : mem),
  transl_stmt_prop sp e m Sskip E0 e m Out_normal.
Proof.
  intros; red; intros; inv TE.
  exists rs; econstructor.
  split. constructor.
  split. apply star_refl.
  auto.
Qed.

Remark state_for_outcome_stop:
  forall ncont1 ncont2 nexits nret rret cs code sp rs m out st,
  state_for_outcome ncont1 nexits nret rret cs code sp rs m out st ->
  out <> Out_normal ->
  state_for_outcome ncont2 nexits nret rret cs code sp rs m out st.
Proof.
  intros. inv H; congruence || econstructor; eauto.
Qed.

Lemma transl_stmt_Sseq_continue_correct:
  forall (sp : val) (e : env) (m : mem) (t: trace) (s1 : stmt)
         (t1: trace) (e1 : env) (m1 : mem) (s2 : stmt) (t2: trace)
         (e2 : env) (m2 : mem) (out : outcome),
  exec_stmt ge sp e m s1 t1 e1 m1 Out_normal ->
  transl_stmt_prop sp e m s1 t1 e1 m1 Out_normal ->
  exec_stmt ge sp e1 m1 s2 t2 e2 m2 out ->
  transl_stmt_prop sp e1 m1 s2 t2 e2 m2 out ->
  t = t1 ** t2 ->
  transl_stmt_prop sp e m (Sseq s1 s2) t e2 m2 out.
Proof.
  intros; red; intros; inv TE. 
  exploit H0; eauto. intros [rs1 [st1 [OUT1 [EX1 ME1]]]]. inv OUT1. 
  exploit H2; eauto. intros [rs2 [st2 [OUT2 [EX2 ME2]]]].
  exists rs2; exists st2.
  split. eauto.
  split. eapply star_trans; eauto.
  auto.
Qed.

Lemma transl_stmt_Sseq_stop_correct:
  forall (sp : val) (e : env) (m : mem) (t: trace) (s1 s2 : stmt) (e1 : env)
         (m1 : mem) (out : outcome),
  exec_stmt ge sp e m s1 t e1 m1 out ->
  transl_stmt_prop sp e m s1 t e1 m1 out ->
  out <> Out_normal ->
  transl_stmt_prop sp e m (Sseq s1 s2) t e1 m1 out.
Proof.
  intros; red; intros; inv TE.
  exploit H0; eauto. intros [rs1 [st1 [OUT1 [EX1 ME1]]]].
  exists rs1; exists st1.
  split. eapply state_for_outcome_stop; eauto. 
  auto.
Qed.

Lemma transl_stmt_Sassign_correct:
  forall (sp : val) (e : env) (m : mem) (id : ident) (a : expr)
         (v : val),
  eval_expr ge sp e m nil a v ->
  transl_stmt_prop sp e m (Sassign id a) E0 (PTree.set id v e) m Out_normal.
Proof.
  intros; red; intros; inv TE.
  exploit transl_expr_correct; eauto.
  intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  exploit tr_store_var_correct; eauto. intros [rs2 [EX2 ME2]].
  exists rs2; econstructor.
  split. constructor.
  split. eapply star_trans. eexact EX1. eexact EX2. traceEq.
  congruence. 
Qed.

Lemma transl_stmt_Sstore_correct:
  forall (sp : val) (e : env) (m : mem) (chunk : memory_chunk)
         (addr: addressing) (al: exprlist) (b: expr)
         (vl: list val) (v: val) (vaddr: val) (m' : mem),
  eval_exprlist ge sp e m nil al vl ->
  eval_expr ge sp e m nil b v ->
  eval_addressing ge sp addr vl = Some vaddr ->
  storev chunk m vaddr v = Some m' ->
  transl_stmt_prop sp e m (Sstore chunk addr al b) E0 e m' Out_normal.
Proof.
  intros; red; intros; inv TE.
  exploit transl_exprlist_correct; eauto. intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  exploit transl_expr_correct; eauto. intros [rs2 [EX2 [ME2 [RES2 OTHER2]]]].
  exists rs2; econstructor.
  (* Outcome *)
  split. constructor.
  (* Exec *)
  split. eapply star_trans. eexact EX1. 
  eapply star_right. eexact EX2.
  eapply exec_Istore; eauto.
  assert (rs2##rl = rs1##rl).
    apply list_map_exten. intros r' IN. symmetry. apply OTHER2. auto.
  rewrite H3; rewrite RES1. 
  rewrite (@eval_addressing_preserved _ _ ge tge). eexact H1.
  exact symbols_preserved.
  rewrite RES2. auto.
  reflexivity. traceEq.
  (* Match-env *)
  auto.
Qed.

Lemma transl_stmt_Scall_correct:
  forall (sp : val) (e : env) (m : mem) (optid : option ident)
         (sig : signature) (a : expr) (bl : exprlist) (vf : val)
         (vargs : list val) (f : CminorSel.fundef) (t : trace) (m' : mem)
         (vres : val) (e' : env),
  eval_expr ge sp e m nil a vf ->
  eval_exprlist ge sp e m nil bl vargs ->
  Genv.find_funct ge vf = Some f ->
  CminorSel.funsig f = sig ->
  eval_funcall ge m f vargs t m' vres ->
  transl_function_prop m f vargs t m' vres ->
  e' = set_optvar optid vres e ->
  transl_stmt_prop sp e m (Scall optid sig a bl) t e' m' Out_normal.
Proof.
  intros; red; intros; inv TE.
  exploit transl_expr_correct; eauto.
  intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  exploit transl_exprlist_correct; eauto.
  intros [rs2 [EX2 [ME2 [RES2 OTHER2]]]].
  exploit functions_translated; eauto. intros [tf [TFIND TF]].
  exploit H4; eauto. intro EXF.
  exploit (tr_store_optvar_correct (rs2#rd <- vres)); eauto.
    apply match_env_update_temp; eauto.
  intros [rs3 [EX3 ME3]].
  exists rs3; econstructor.
  (* Outcome *)
  split. constructor.
  (* Exec *)
  split. eapply star_trans. eexact EX1.
  eapply star_trans. eexact EX2. 
  eapply star_left. eapply exec_Icall; eauto.
  simpl. rewrite OTHER2. rewrite RES1. eauto. simpl; tauto. 
  eapply sig_transl_function; eauto.
  eapply star_trans. rewrite RES2. eexact EXF.
  eapply star_left. apply exec_return.
  eexact EX3. 
  reflexivity. reflexivity. reflexivity. reflexivity. traceEq.
  (* Match-env *)
  rewrite Regmap.gss in ME3. auto.
Qed. 

Lemma transl_stmt_Salloc_correct:
  forall (sp : val) (e : env) (m : mem) (id : ident) (a : expr)
         (n : int) (m' : mem) (b : block),
  eval_expr ge sp e m nil a (Vint n) ->
  alloc m 0 (Int.signed n) = (m', b) ->
  transl_stmt_prop sp e m (Salloc id a) E0
                      (PTree.set id (Vptr b Int.zero) e) m' Out_normal.
Proof.
  intros; red; intros; inv TE.
  exploit transl_expr_correct; eauto.
  intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  exploit (tr_store_var_correct (rs1#rd <- (Vptr b Int.zero))); eauto.
    apply match_env_update_temp; eauto.
  intros [rs2 [EX2 ME2]].
  exists rs2; econstructor.
  (* Outcome *)
  split. constructor.
  (* Execution *)
  split. eapply star_trans. eexact EX1. 
  eapply star_left. 2: eexact EX2. 
  eapply exec_Ialloc; eauto. 
  reflexivity. traceEq.
  (* Match-env *)
  rewrite Regmap.gss in ME2. auto.
Qed.

Lemma transl_stmt_Sifthenelse_correct:
  forall (sp : val) (e : env) (m : mem) (a : condexpr) (s1 s2 : stmt)
         (v : bool) (t : trace) (e' : env) (m' : mem) (out : outcome),
  eval_condexpr ge sp e m nil a v ->
  exec_stmt ge sp e m (if v then s1 else s2) t e' m' out ->
  transl_stmt_prop sp e m (if v then s1 else s2) t e' m' out ->
  transl_stmt_prop sp e m (Sifthenelse a s1 s2) t e' m' out.
Proof.
  intros; red; intros; inv TE.
  exploit transl_condexpr_correct; eauto.
  intros [rs1 [EX1 [ME1 OTHER1]]].
  assert (tr_stmt code map (if v then s1 else s2) (if v then ntrue else nfalse)
                  ncont nexits nret rret).
    destruct v; auto. 
  exploit H1; eauto. intros [rs2 [st2 [OUT2 [EX2 ME2]]]].
  exists rs2; exists st2.
  split. eauto.
  split. eapply star_trans. eexact EX1. eexact EX2. auto.
  auto.
Qed.

Lemma transl_stmt_Sloop_loop_correct:
  forall (sp: val) (e : env) (m : mem) (sl : stmt) (t t1: trace)
    (e1 : env) (m1 : mem) (t2: trace) (e2 : env) (m2 : mem) 
    (out : outcome),
  exec_stmt ge sp e m sl t1 e1 m1 Out_normal ->
  transl_stmt_prop sp e m sl t1 e1 m1 Out_normal ->
  exec_stmt ge sp e1 m1 (Sloop sl) t2 e2 m2 out ->
  transl_stmt_prop sp e1 m1 (Sloop sl) t2 e2 m2 out ->
  t = t1 ** t2 ->
  transl_stmt_prop sp e m (Sloop sl) t e2 m2 out.
Proof.
  intros; red; intros; inversion TE. subst. 
  exploit H0; eauto. intros [rs1 [st1 [OUT1 [EX1 ME1]]]]. inv OUT1.
  exploit H2; eauto. intros [rs2 [st2 [OUT2 [EX2 ME2]]]].
  exists rs2; exists st2. 
  split. eauto.
  split. eapply star_trans. eexact EX1. 
  eapply star_left. apply exec_Inop; eauto. eexact EX2. 
  reflexivity. traceEq.
  auto.
Qed.

Lemma transl_stmt_Sloop_stop_correct:
  forall (sp: val) (e : env) (m : mem) (t: trace) (sl : stmt) 
    (e1 : env) (m1 : mem) (out : outcome),
  exec_stmt ge sp e m sl t e1 m1 out ->
  transl_stmt_prop sp e m sl t e1 m1 out ->
  out <> Out_normal ->
  transl_stmt_prop sp e m (Sloop sl) t e1 m1 out.
Proof.
  intros; red; intros; inv TE. 
  exploit H0; eauto. intros [rs1 [st1 [OUT1 [EX1 ME1]]]].
  exists rs1; exists st1.
  split. eapply state_for_outcome_stop; eauto.
  auto.
Qed.

Lemma transl_stmt_Sblock_correct:
  forall (sp: val) (e : env) (m : mem) (sl : stmt) (t: trace)
    (e1 : env) (m1 : mem) (out : outcome),
  exec_stmt ge sp e m sl t e1 m1 out ->
  transl_stmt_prop sp e m sl t e1 m1 out ->
  transl_stmt_prop sp e m (Sblock sl) t e1 m1 (outcome_block out).
Proof.
  intros; red; intros; inv TE.
  exploit H0; eauto. intros [rs1 [st1 [OUT1 [EX1 ME1]]]].
  exists rs1; exists st1.
  split. inv OUT1; simpl; try (econstructor; eauto).
  destruct n; simpl in H1.
    inv H1. constructor.
    constructor. auto.
  auto.
Qed.

Lemma transl_stmt_Sexit_correct:
  forall (sp: val) (e : env) (m : mem) (n : nat),
  transl_stmt_prop sp e m (Sexit n) E0 e m (Out_exit n).
Proof.
  intros; red; intros; inv TE.
  exists rs; econstructor.
  split. econstructor; eauto.
  split. apply star_refl.
  auto.
Qed.

Lemma transl_switch_correct:
  forall cs sp rs m i code r nexits t ns,
  tr_switch code r nexits t ns ->
  rs#r = Vint i ->
  exists nd,
  star step tge (State cs code sp ns rs m) E0 (State cs code sp nd rs m) /\
  nth_error nexits (comptree_match i t) = Some nd.
Proof.
  induction 1; intros; simpl.
  exists n. split. apply star_refl. auto. 

  caseEq (Int.eq i key); intros.
  exists nfound; split. 
  apply star_one. eapply exec_Icond_true; eauto. 
  simpl. rewrite H2. congruence. auto.
  exploit IHtr_switch; eauto. intros [nd [EX MATCH]].
  exists nd; split.
  eapply star_step. eapply exec_Icond_false; eauto. 
  simpl. rewrite H2. congruence. eexact EX. traceEq.
  auto.

  caseEq (Int.ltu i key); intros.
  exploit IHtr_switch1; eauto. intros [nd [EX MATCH]].
  exists nd; split. 
  eapply star_step. eapply exec_Icond_true; eauto. 
  simpl. rewrite H2. congruence. eexact EX. traceEq.
  auto.
  exploit IHtr_switch2; eauto. intros [nd [EX MATCH]].
  exists nd; split. 
  eapply star_step. eapply exec_Icond_false; eauto. 
  simpl. rewrite H2. congruence. eexact EX. traceEq.
  auto.
Qed.

Lemma transl_stmt_Sswitch_correct:
  forall (sp : val) (e : env) (m : mem) (a : expr)
         (cases : list (int * nat)) (default : nat) (n : int),
  eval_expr ge sp e m nil a (Vint n) ->
  transl_stmt_prop sp e m (Sswitch a cases default) E0 e m
         (Out_exit (switch_target n default cases)).
Proof.
  intros; red; intros; inv TE.
  exploit transl_expr_correct; eauto. 
  intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  exploit transl_switch_correct; eauto. intros [nd [EX2 MO2]].
  exists rs1; econstructor.
  split. econstructor. 
  rewrite (validate_switch_correct _ _ _ H3 n). eauto.  
  split. eapply star_trans. eexact EX1. eexact EX2. traceEq.
  auto.
Qed.

Lemma transl_stmt_Sreturn_none_correct:
  forall (sp: val) (e : env) (m : mem),
  transl_stmt_prop sp e m (Sreturn None) E0 e m (Out_return None).
Proof.
  intros; red; intros; inv TE.
  exists rs; econstructor.
  split. constructor. auto.
  split. apply star_refl. 
  auto.
Qed.

Lemma transl_stmt_Sreturn_some_correct:
  forall (sp : val) (e : env) (m : mem) (a : expr) (v : val),
  eval_expr ge sp e m nil a v ->
  transl_stmt_prop sp e m (Sreturn (Some a)) E0 e m (Out_return (Some v)).
Proof.
  intros; red; intros; inv TE. 
  exploit transl_expr_correct; eauto.
  intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  exists rs1; econstructor.
  split. econstructor. reflexivity. auto.
  eauto.
Qed.

Lemma transl_stmt_Stailcall_correct:
  forall (sp : block) (e : env) (m : mem) (sig : signature) (a : expr)
         (bl : exprlist) (vf : val) (vargs : list val) (f : CminorSel.fundef)
         (t : trace) (m' : mem) (vres : val),
  eval_expr ge (Vptr sp Int.zero) e m nil a vf ->
  eval_exprlist ge (Vptr sp Int.zero) e m nil bl vargs ->
  Genv.find_funct ge vf = Some f ->
  CminorSel.funsig f = sig ->
  eval_funcall ge (free m sp) f vargs t m' vres ->
  transl_function_prop (free m sp) f vargs t m' vres ->
  transl_stmt_prop (Vptr sp Int.zero) e m (Stailcall sig a bl) t e
          m' (Out_tailcall_return vres).
Proof.
  intros; red; intros; inv TE.
  exploit transl_expr_correct; eauto. intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  exploit transl_exprlist_correct; eauto. intros [rs2 [EX2 [ME2 [RES2 OTHER2]]]].
  exploit functions_translated; eauto. intros [tf [TFIND TF]].
  exploit H4; eauto. intro EXF.
  exists rs2; econstructor. 
  split. constructor. 
  split. 
  eapply star_trans. eexact EX1. 
  eapply star_trans. eexact EX2. 
  eapply star_step. 
  eapply exec_Itailcall; eauto.
  simpl. rewrite OTHER2. rewrite RES1. eauto. simpl; tauto.
  eapply sig_transl_function; eauto.
  rewrite RES2. eexact EXF. 
  reflexivity. reflexivity. traceEq.
  auto.
Qed.

(** The correctness of the translation then follows by application
  of the mutual induction principle for Cminor evaluation derivations
  to the lemmas above. *)

Theorem transl_function_correct:
  forall m f vargs t m' vres,
  eval_funcall ge m f vargs t m' vres ->
  transl_function_prop m f vargs t m' vres.
Proof
  (eval_funcall_ind2 ge
    transl_function_prop
    transl_stmt_prop

    transl_funcall_internal_correct
    transl_funcall_external_correct
    transl_stmt_Sskip_correct
    transl_stmt_Sassign_correct
    transl_stmt_Sstore_correct
    transl_stmt_Scall_correct
    transl_stmt_Salloc_correct
    transl_stmt_Sifthenelse_correct
    transl_stmt_Sseq_continue_correct
    transl_stmt_Sseq_stop_correct
    transl_stmt_Sloop_loop_correct
    transl_stmt_Sloop_stop_correct
    transl_stmt_Sblock_correct
    transl_stmt_Sexit_correct
    transl_stmt_Sswitch_correct
    transl_stmt_Sreturn_none_correct
    transl_stmt_Sreturn_some_correct
    transl_stmt_Stailcall_correct).

Theorem transl_stmt_correct:
  forall sp e m s t e' m' out,
  exec_stmt ge sp e m s t e' m' out ->
  transl_stmt_prop sp e m s t e' m' out.
Proof
  (exec_stmt_ind2 ge
    transl_function_prop
    transl_stmt_prop

    transl_funcall_internal_correct
    transl_funcall_external_correct
    transl_stmt_Sskip_correct
    transl_stmt_Sassign_correct
    transl_stmt_Sstore_correct
    transl_stmt_Scall_correct
    transl_stmt_Salloc_correct
    transl_stmt_Sifthenelse_correct
    transl_stmt_Sseq_continue_correct
    transl_stmt_Sseq_stop_correct
    transl_stmt_Sloop_loop_correct
    transl_stmt_Sloop_stop_correct
    transl_stmt_Sblock_correct
    transl_stmt_Sexit_correct
    transl_stmt_Sswitch_correct
    transl_stmt_Sreturn_none_correct
    transl_stmt_Sreturn_some_correct
    transl_stmt_Stailcall_correct).

(** ** Semantic preservation for the translation of divering statements *)   

Fixpoint size_stmt (s: stmt) : nat :=
  match s with
  | Sseq s1 s2 => (1 + size_stmt s1 + size_stmt s2)%nat
  | Sifthenelse e s1 s2 => (1 + size_stmt s1 + size_stmt s2)%nat
  | Sloop s1 => (1 + size_stmt s1)%nat
  | Sblock s1 => (1 + size_stmt s1)%nat
  | _ => 1%nat
  end.

Theorem transl_function_correct_divergence:
  forall m fd vargs t tfd cs,
  evalinf_funcall ge m fd vargs t ->
  transl_fundef fd = OK tfd ->
  forever_N step tge O (Callstate cs tfd vargs m) t.
Proof.
  cofix FUNCALL.
  assert (STMT: forall sp e m s t,
     execinf_stmt ge sp e m s t ->
     forall cs code map ns ncont nexits nret rret rs
       (MWF: map_wf map)
       (TE: tr_stmt code map s ns ncont nexits nret rret)
       (ME: match_env map e nil rs),
     forever_N step tge (size_stmt s) (State cs code sp ns rs m) t).
  cofix STMT; intros. 
  inv H; inversion TE; subst.
  (* Scall *)
  destruct (transl_expr_correct _ _ _ _ _ _ H0
              cs _ _ _ _ _ _ _ MWF H7 ME)
  as [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  destruct (transl_exprlist_correct _ _ _ _ _ _ H1
              cs _ _ _ _ _ _ _ MWF H8 ME1)
  as [rs2 [EX2 [ME2 [RES2 OTHER2]]]].
  destruct (functions_translated _ _ H2) as [tf [TFIND TF]].
  eapply forever_N_star with (p := O).
  eapply star_trans. eexact EX1. eexact EX2. reflexivity.
  simpl; omega. 
  eapply forever_N_plus with (p := O).
  apply plus_one. eapply exec_Icall; eauto. 
  simpl. rewrite OTHER2. rewrite RES1. eauto. simpl; tauto. 
  eapply sig_transl_function; eauto.
  eapply FUNCALL. rewrite RES2. eexact H4. assumption.
  reflexivity. traceEq.    
  (* Sifthenelse *)
  destruct (transl_condexpr_correct _ _ _ _ _ _ H0
              cs _ _ _ _ _ _ _ MWF H11 ME)
  as [rs1 [EX1 [ME1 OTHER1]]].
  eapply forever_N_star with (p := size_stmt (if v then s1 else s2)).
  eexact EX1. destruct v; simpl; omega.
  eapply STMT. eexact H1. eauto. destruct v; eauto. eauto.
  traceEq. 
  (* Sseq, 1 *)
  eapply forever_N_star with (p := size_stmt s1).
  apply star_refl. simpl; omega.
  eapply STMT; eauto.
  traceEq.
  (* Sseq, 2 *)
  destruct (transl_stmt_correct _ _ _ _ _ _ _ _ H0
              cs _ _ _ _ _ _ _ _ MWF H9 ME)
  as [rs1 [st1 [OUT1 [EX1 ME1]]]].
  inv OUT1. 
  eapply forever_N_star with (p := size_stmt s2).
  eexact EX1. simpl; omega.
  eapply STMT; eauto.
  traceEq.
  (* Sloop, body *)
  eapply forever_N_star with (p := size_stmt s0).
  apply star_refl. simpl; omega.
  eapply STMT; eauto.
  traceEq.
  (* Sloop, loop *)
  destruct (transl_stmt_correct _ _ _ _ _ _ _ _ H0
              cs _ _ _ _ _ _ _ _ MWF H2 ME)
  as [rs1 [st1 [OUT1 [EX1 ME1]]]].
  inv OUT1. 
  eapply forever_N_plus with (p := size_stmt (Sloop s0)).
  eapply plus_right. eexact EX1. eapply exec_Inop; eauto. reflexivity.
  eapply STMT; eauto.
  traceEq. 
  (* Sblock *)
  eapply forever_N_star with (p := size_stmt s0).
  apply star_refl. simpl; omega.
  eapply STMT; eauto.
  traceEq.
  (* Stailcall *)
  destruct (transl_expr_correct _ _ _ _ _ _ H0
              cs _ _ _ _ _ _ _ MWF H6 ME)
  as [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  destruct (transl_exprlist_correct _ _ _ _ _ _ H1
              cs _ _ _ _ _ _ _ MWF H12 ME1)
  as [rs2 [EX2 [ME2 [RES2 OTHER2]]]].
  destruct (functions_translated _ _ H2) as [tf [TFIND TF]].
  eapply forever_N_star with (p := O).
  eapply star_trans. eexact EX1. eexact EX2. reflexivity.
  simpl; omega. 
  eapply forever_N_plus with (p := O).
  apply plus_one. eapply exec_Itailcall; eauto. 
  simpl. rewrite OTHER2. rewrite RES1. eauto. simpl; tauto. 
  eapply sig_transl_function; eauto.
  eapply FUNCALL. rewrite RES2. eexact H4. assumption.
  reflexivity. traceEq.
  (* funcall *)
  intros. inversion H. subst m0 fd vargs0 t0. 
  generalize H0; simpl. caseEq (transl_function f); simpl. 2: congruence.
  intros tfi EQ1 EQ2. injection EQ2; clear EQ2; intro EQ2.
  assert (TR: tr_function f tfi). apply transl_function_charact; auto.
  rewrite <- EQ2. inversion TR. subst f0. 
  pose (rs := init_regs vargs rparams).
  assert (ME: match_env map2 e nil rs).
  rewrite <- H2. unfold rs. 
  eapply match_init_env_init_reg; eauto.
  assert (MWF: map_wf map2).
    assert (map_valid init_mapping init_state) by apply init_mapping_valid.
    exploit (add_vars_valid (CminorSel.fn_params f)); eauto. intros [A B].
    eapply add_vars_wf; eauto. eapply add_vars_wf; eauto. apply init_mapping_wf.
  eapply forever_N_plus with (p := size_stmt (fn_body f)).
  apply plus_one. eapply exec_function_internal; eauto.
  simpl. eapply STMT; eauto.
  traceEq.
Qed.

(** ** Semantic preservation for whole programs. *)

(** The correctness of the translation follows: 
  if the original Cminor program executes with observable behavior [beh],
  then the generated RTL program executes with the same behavior. *)

Theorem transl_program_correct:
  forall (beh: program_behavior),
  CminorSel.exec_program prog beh ->
  RTL.exec_program tprog beh.
Proof.
  intros. inv H.
  (* termination *)
  exploit function_ptr_translated; eauto. intros [tf [TFIND TRANSLF]].
  exploit transl_function_correct; eauto. intro EX.
  econstructor.
  econstructor. 
  rewrite symbols_preserved. 
  replace (prog_main tprog) with (prog_main prog). eauto.
  symmetry; apply transform_partial_program_main with transl_fundef.
  exact TRANSL.
  eexact TFIND.
  generalize (sig_transl_function _ _ TRANSLF). congruence.
  unfold fundef; rewrite (Genv.init_mem_transf_partial transl_fundef prog TRANSL).
  eexact EX. 
  constructor.
  (* divergence *)
  exploit function_ptr_translated; eauto. intros [tf [TFIND TRANSLF]].
  exploit transl_function_correct_divergence; eauto. intro EX.
  econstructor.
  econstructor. 
  rewrite symbols_preserved. 
  replace (prog_main tprog) with (prog_main prog). eauto.
  symmetry; apply transform_partial_program_main with transl_fundef.
  exact TRANSL.
  eexact TFIND.
  generalize (sig_transl_function _ _ TRANSLF). congruence.
  eapply forever_N_forever. 
  unfold fundef; rewrite (Genv.init_mem_transf_partial transl_fundef prog TRANSL).
  eexact EX. 
Qed.

End CORRECTNESS.
