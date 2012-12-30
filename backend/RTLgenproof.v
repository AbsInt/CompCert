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
Require Import Memory.
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
         e!id = Some v -> exists r, map.(map_vars)!id = Some r /\ Val.lessdef v rs#r);
    me_letvars:
      Val.lessdef_list le rs##(map.(map_letvars))
  }.

Lemma match_env_find_var:
  forall map e le rs id v r,
  match_env map e le rs ->
  e!id = Some v ->
  map.(map_vars)!id = Some r ->
  Val.lessdef v rs#r.
Proof.
  intros. exploit me_vars; eauto. intros [r' [EQ' RS]].
  replace r with r'. auto. congruence.
Qed.

Lemma match_env_find_letvar:
  forall map e le rs idx v r,
  match_env map e le rs ->
  List.nth_error le idx = Some v ->
  List.nth_error map.(map_letvars) idx = Some r ->
  Val.lessdef v rs#r.
Proof.
  intros. exploit me_letvars; eauto.
  clear H. revert le H0 H1. generalize (map_letvars map). clear map.
  induction idx; simpl; intros.
  inversion H; subst le; inversion H0. subst v1.
  destruct l; inversion H1. subst r0.
  inversion H2. subst v2. auto.
  destruct l; destruct le; try discriminate.
  eapply IHidx; eauto.
  inversion H. auto.
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
  replace (rs'##(map_letvars map)) with (rs ## (map_letvars map)). auto.
  apply list_map_exten. intros. apply H0. right; auto.
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
  forall map e le rs id r v tv,
  Val.lessdef v tv ->
  map_wf map ->
  map.(map_vars)!id = Some r ->
  match_env map e le rs ->
  match_env map (PTree.set id v e) le (rs#r <- tv).
Proof.
  intros. inversion H0. inversion H2. apply mk_match_env.
  intros id' v'. rewrite PTree.gsspec. destruct (peq id' id); intros.
  subst id'. inv H3. exists r; split. auto. rewrite PMap.gss. auto.
  exploit me_vars0; eauto. intros [r' [A B]].
  exists r'; split. auto. rewrite PMap.gso; auto.
  red; intros. subst r'. elim n. eauto.
  erewrite list_map_exten. eauto.
  intros. symmetry. apply PMap.gso. red; intros. subst x. eauto. 
Qed.

(** A variant of [match_env_update_var] where a variable is optionally
  assigned to, depending on the [dst] parameter. *)

Lemma match_env_update_dest:
  forall map e le rs dst r v tv,
  Val.lessdef v tv ->
  map_wf map ->
  reg_map_ok map r dst ->
  match_env map e le rs ->
  match_env map (set_optvar dst v e) le (rs#r <- tv).
Proof.
  intros. inv H1; simpl. 
  eapply match_env_update_temp; eauto. 
  eapply match_env_update_var; eauto.
Qed.
Hint Resolve match_env_update_dest: rtlg.

(** Matching and [let]-bound variables. *)

Lemma match_env_bind_letvar:
  forall map e le rs r v,
  match_env map e le rs ->
  Val.lessdef v rs#r ->
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
  constructor. auto. inversion me_letvars0. auto.
Qed.

(** Matching between initial environments. *)

Lemma match_env_empty:
  forall map,
  map.(map_letvars) = nil ->
  match_env map (PTree.empty val) nil (Regmap.init Vundef).
Proof.
  intros. apply mk_match_env.
  intros. rewrite PTree.gempty in H0. discriminate.
  rewrite H. constructor.
Qed.

(** The assignment of function arguments to local variables (on the Cminor
  side) and pseudo-registers (on the RTL side) preserves matching
  between environments. *)

Lemma match_set_params_init_regs:
  forall il rl s1 map2 s2 vl tvl i,
  add_vars init_mapping il s1 = OK (rl, map2) s2 i ->
  Val.lessdef_list vl tvl ->
  match_env map2 (set_params vl il) nil (init_regs tvl rl)
  /\ (forall r, reg_fresh r s2 -> (init_regs tvl rl)#r = Vundef).
Proof.
  induction il; intros.

  inv H. split. apply match_env_empty. auto. intros. 
  simpl. apply Regmap.gi.

  monadInv H. simpl.
  exploit add_vars_valid; eauto. apply init_mapping_valid. intros [A B].
  exploit add_var_valid; eauto. intros [A' B']. clear B'.
  monadInv EQ1. 
  destruct H0 as [ | v1 tv1 vs tvs].
  (* vl = nil *)
  destruct (IHil _ _ _ _ nil nil _ EQ) as [ME UNDEF]. constructor. inv ME. split.
  replace (init_regs nil x) with (Regmap.init Vundef) in me_vars0, me_letvars0.
  constructor; simpl.
  intros id v. repeat rewrite PTree.gsspec. destruct (peq id a); intros.
  subst a. inv H. exists x1; split. auto. constructor.
  eauto.
  eauto.
  destruct x; reflexivity.
  intros. apply Regmap.gi.
  (* vl = v1 :: vs *)
  destruct (IHil _ _ _ _ _ _ _ EQ H0) as [ME UNDEF]. inv ME. split.
  constructor; simpl.
  intros id v. repeat rewrite PTree.gsspec. destruct (peq id a); intros.
  subst a. inv H. inv H1. exists x1; split. auto. rewrite Regmap.gss. constructor.
  inv H1. eexists; eauto.
  exploit me_vars0; eauto. intros [r' [C D]]. 
  exists r'; split. auto. rewrite Regmap.gso. auto.
  apply valid_fresh_different with s.
  apply B. left; exists id; auto.
  eauto with rtlg. 
  destruct (map_letvars x0). auto. simpl in me_letvars0. inversion me_letvars0.
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
  exists x1. split. auto. inv H3. constructor.
  eauto with rtlg.
  intros. eapply me_vars; eauto. 
  simpl. eapply me_letvars; eauto.
Qed.

Lemma match_init_env_init_reg:
  forall params s0 rparams map1 s1 i1 vars rvars map2 s2 i2 vparams tvparams,
  add_vars init_mapping params s0 = OK (rparams, map1) s1 i1 ->
  add_vars map1 vars s1 = OK (rvars, map2) s2 i2 ->
  Val.lessdef_list vparams tvparams ->
  match_env map2 (set_locals vars (set_params vparams params))
            nil (init_regs tvparams rparams).
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
  (Genv.find_funct_ptr_transf_partial transl_fundef _ TRANSL).

Lemma functions_translated:
  forall (v: val) (f: CminorSel.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef f = OK tf.
Proof
  (Genv.find_funct_transf_partial transl_fundef _ TRANSL).

Lemma sig_transl_function:
  forall (f: CminorSel.fundef) (tf: RTL.fundef),
  transl_fundef f = OK tf ->
  RTL.funsig tf = CminorSel.funsig f.
Proof.
  intros until tf. unfold transl_fundef, transf_partial_fundef.
  case f; intro.
  unfold transl_function. 
  destruct (reserve_labels (fn_body f0) (PTree.empty node, init_state)) as [ngoto s0].
  case (transl_fun f0 ngoto s0); simpl; intros.
  discriminate.
  destruct p. simpl in H. inversion H. reflexivity.
  intro. inversion H. reflexivity.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof
  (Genv.find_var_info_transf_partial transl_fundef _ TRANSL).

(** Correctness of the code generated by [add_move]. *)

Lemma tr_move_correct:
  forall r1 ns r2 nd cs f sp rs m,
  tr_move f.(fn_code) ns r1 nd r2 ->
  exists rs',
  star step tge (State cs f sp ns rs m) E0 (State cs f sp nd rs' m) /\
  rs'#r2 = rs#r1 /\
  (forall r, r <> r2 -> rs'#r = rs#r).
Proof.
  intros. inv H. 
  exists rs; split. constructor. auto.
  exists (rs#r2 <- (rs#r1)); split. 
  apply star_one. eapply exec_Iop. eauto. auto. 
  split. apply Regmap.gss. intros; apply Regmap.gso; auto.
Qed.

(** Correctness of the translation of [switch] statements *)

Lemma transl_switch_correct:
  forall cs sp e m f map r nexits t ns,
  tr_switch f.(fn_code) map r nexits t ns ->
  forall rs i act,
  rs#r = Vint i ->
  map_wf map ->
  match_env map e nil rs ->
  comptree_match i t = Some act ->
  exists nd, exists rs',
  star step tge (State cs f sp ns rs m) E0 (State cs f sp nd rs' m) /\
  nth_error nexits act = Some nd /\
  match_env map e nil rs'.
Proof.
  Opaque Int.sub.
  induction 1; simpl; intros.
(* action *)
  inv H3. exists n; exists rs; intuition.
  apply star_refl.
(* ifeq *)
  caseEq (Int.eq i key); intro EQ; rewrite EQ in H5.
  inv H5. exists nfound; exists rs; intuition.
  apply star_one. eapply exec_Icond with (b := true); eauto. 
  simpl. rewrite H2. simpl. congruence.
  exploit IHtr_switch; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply star_step. eapply exec_Icond with (b := false); eauto. 
  simpl. rewrite H2. simpl. congruence. eexact EX. traceEq.
(* iflt *)
  caseEq (Int.ltu i key); intro EQ; rewrite EQ in H5.
  exploit IHtr_switch1; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply star_step. eapply exec_Icond with (b := true); eauto. 
  simpl. rewrite H2. simpl. congruence. eexact EX. traceEq.
  exploit IHtr_switch2; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply star_step. eapply exec_Icond with (b := false); eauto. 
  simpl. rewrite H2. simpl. congruence. eexact EX. traceEq.
(* jumptable *)
  set (rs1 := rs#rt <- (Vint(Int.sub i ofs))).
  assert (ME1: match_env map e nil rs1).
    unfold rs1. eauto with rtlg.
  assert (EX1: step tge (State cs f sp n rs m) E0 (State cs f sp n1 rs1 m)).
    eapply exec_Iop; eauto. 
    predSpec Int.eq Int.eq_spec ofs Int.zero; simpl.
    rewrite H10. rewrite Int.sub_zero_l. congruence.
    rewrite H6. simpl. rewrite <- Int.sub_add_opp. auto. 
  caseEq (Int.ltu (Int.sub i ofs) sz); intro EQ; rewrite EQ in H9.
  exploit H5; eauto. intros [nd [A B]].
  exists nd; exists rs1; intuition. 
  eapply star_step. eexact EX1.
  eapply star_step. eapply exec_Icond with (b := true); eauto. 
  simpl. unfold rs1. rewrite Regmap.gss. simpl. congruence. 
  apply star_one. eapply exec_Ijumptable; eauto. unfold rs1. apply Regmap.gss. 
  reflexivity. traceEq.
  exploit (IHtr_switch rs1); eauto. unfold rs1. rewrite Regmap.gso; auto.
  intros [nd [rs' [EX [NTH ME]]]].
  exists nd; exists rs'; intuition.
  eapply star_step. eexact EX1.
  eapply star_step. eapply exec_Icond with (b := false); eauto. 
  simpl. unfold rs1. rewrite Regmap.gss. simpl. congruence.
  eexact EX. reflexivity. traceEq.
Qed.

(** ** Semantic preservation for the translation of expressions *)

Section CORRECTNESS_EXPR.

Variable sp: val.
Variable e: env.
Variable m tm: mem.
Hypothesis mem_extends: Mem.extends m tm.

(** The proof of semantic preservation for the translation of expressions
  is a simulation argument based on diagrams of the following form:
<<
                    I /\ P
    e, le, m, a ------------- State cs code sp ns rs m
         ||                      |
         ||                      |*
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
  forall cs f map pr ns nd rd rs dst
    (MWF: map_wf map)
    (TE: tr_expr f.(fn_code) map pr a ns nd rd dst)
    (ME: match_env map e le rs),
  exists rs',
     star step tge (State cs f sp ns rs tm) E0 (State cs f sp nd rs' tm)
  /\ match_env map (set_optvar dst v e) le rs'
  /\ Val.lessdef v rs'#rd
  /\ (forall r, In r pr -> rs'#r = rs#r).

Definition transl_exprlist_prop 
     (le: letenv) (al: exprlist) (vl: list val) : Prop :=
  forall cs f map pr ns nd rl rs
    (MWF: map_wf map)
    (TE: tr_exprlist f.(fn_code) map pr al ns nd rl)
    (ME: match_env map e le rs),
  exists rs',
     star step tge (State cs f sp ns rs tm) E0 (State cs f sp nd rs' tm)
  /\ match_env map e le rs'
  /\ Val.lessdef_list vl rs'##rl
  /\ (forall r, In r pr -> rs'#r = rs#r).

(** The correctness of the translation is a huge induction over
  the Cminor evaluation derivation for the source program.  To keep
  the proof manageable, we put each case of the proof in a separate
  lemma.  There is one lemma for each Cminor evaluation rule.
  It takes as hypotheses the premises of the Cminor evaluation rule,
  plus the induction hypotheses, that is, the [transl_expr_prop], etc,
  corresponding to the evaluations of sub-expressions or sub-statements. *)

Lemma transl_expr_Evar_correct:
  forall (le : letenv) (id : positive) (v: val),
  e ! id = Some v ->
  transl_expr_prop le (Evar id) v.
Proof.
  intros; red; intros. inv TE.
  exploit match_env_find_var; eauto. intro EQ.
  exploit tr_move_correct; eauto. intros [rs' [A [B C]]]. 
  exists rs'; split. eauto.
  destruct H2 as [[D E] | [D E]].
  (* optimized case *)
  subst r dst. simpl.
  assert (forall r, rs'#r = rs#r).
    intros. destruct (Reg.eq r rd). subst r. auto. auto. 
  split. eapply match_env_invariant; eauto.
  split. congruence. auto.
  (* general case *)
  split.
  apply match_env_invariant with (rs#rd <- (rs#r)).
  apply match_env_update_dest; auto. 
  intros. rewrite Regmap.gsspec. destruct (peq r0 rd). congruence. auto. 
  split. congruence. 
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
(* normal case *) 
  exploit H0; eauto. intros [rs1 [EX1 [ME1 [RR1 RO1]]]].
  edestruct eval_operation_lessdef as [v' []]; eauto.
  exists (rs1#rd <- v').
(* Exec *)
  split. eapply star_right. eexact EX1.
  eapply exec_Iop; eauto.
  rewrite (@eval_operation_preserved CminorSel.fundef _ _ _ ge tge). eauto.
  exact symbols_preserved. traceEq.
(* Match-env *)
  split. eauto with rtlg.
(* Result reg *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  intros. rewrite Regmap.gso. auto. intuition congruence.
Qed.

Lemma transl_expr_Eload_correct:
  forall (le : letenv) (chunk : memory_chunk) (addr : Op.addressing)
         (args : exprlist) (vargs : list val) (vaddr v : val),
  eval_exprlist ge sp e m le args vargs ->
  transl_exprlist_prop le args vargs ->
  Op.eval_addressing ge sp addr vargs = Some vaddr ->
  Mem.loadv chunk m vaddr = Some v ->
  transl_expr_prop le (Eload chunk addr args) v.
Proof.
  intros; red; intros. inv TE.
  exploit H0; eauto. intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]].
  edestruct eval_addressing_lessdef as [vaddr' []]; eauto.
  edestruct Mem.loadv_extends as [v' []]; eauto.
  exists (rs1#rd <- v').
(* Exec *)
  split. eapply star_right. eexact EX1. eapply exec_Iload. eauto.
  instantiate (1 := vaddr'). rewrite <- H3.
  apply eval_addressing_preserved. exact symbols_preserved.
  auto. traceEq.
(* Match-env *)
  split. eauto with rtlg. 
(* Result *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  intros. rewrite Regmap.gso. auto. intuition congruence. 
Qed.

Lemma transl_expr_Econdition_correct:
  forall (le : letenv) (cond : condition) (al: exprlist) (ifso ifnot : expr)
         (vl: list val) (vcond : bool) (v : val),
  eval_exprlist ge sp e m le al vl ->
  transl_exprlist_prop le al vl ->
  eval_condition cond vl m = Some vcond ->
  eval_expr ge sp e m le (if vcond then ifso else ifnot) v ->
  transl_expr_prop le (if vcond then ifso else ifnot) v ->
  transl_expr_prop le (Econdition cond al ifso ifnot) v.
Proof.
  intros; red; intros; inv TE. inv H14.
  exploit H0; eauto. intros [rs1 [EX1 [ME1 [RES1 OTHER1]]]]. 
  assert (tr_expr f.(fn_code) map pr (if vcond then ifso else ifnot) (if vcond then ntrue else nfalse) nd rd dst).
    destruct vcond; auto.
  exploit H3; eauto. intros [rs2 [EX2 [ME2 [RES2 OTHER2]]]].
  exists rs2.
(* Exec *)
  split. eapply star_trans. eexact EX1.
  eapply star_left. eapply exec_Icond. eauto. eapply eval_condition_lessdef; eauto. reflexivity. 
  eexact EX2. reflexivity. traceEq.
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
  intros. transitivity (rs1#r0); auto.
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
  split. 
  destruct H2 as [[A B] | [A B]].
  subst r dst; simpl. 
  apply match_env_invariant with rs. auto.
  intros. destruct (Reg.eq r rd). subst r. auto. auto.
  apply match_env_invariant with (rs#rd <- (rs#r)).
  apply match_env_update_dest; auto.
  eapply match_env_find_letvar; eauto.
  intros. rewrite Regmap.gsspec. destruct (peq r0 rd); auto.
  congruence.
(* Result *)
  split. rewrite RES1. eapply match_env_find_letvar; eauto. 
(* Other regs *)
  intros. 
  destruct H2 as [[A B] | [A B]].
  destruct (Reg.eq r0 rd); subst; auto.
  apply OTHER1. intuition congruence.
Qed.

Lemma transl_exprlist_Enil_correct:
  forall (le : letenv),
  transl_exprlist_prop le Enil nil.
Proof.
  intros; red; intros; inv TE.
  exists rs.
  split. apply star_refl.
  split. assumption.
  split. constructor.
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
  split. simpl. constructor. rewrite OTHER2. auto.
  simpl; tauto.
  auto.
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
  (eval_expr_ind2 ge sp e m
     transl_expr_prop
     transl_exprlist_prop
     transl_expr_Evar_correct
     transl_expr_Eop_correct
     transl_expr_Eload_correct
     transl_expr_Econdition_correct
     transl_expr_Elet_correct
     transl_expr_Eletvar_correct
     transl_exprlist_Enil_correct
     transl_exprlist_Econs_correct).

Theorem transl_exprlist_correct:
  forall le a v,
  eval_exprlist ge sp e m le a v ->
  transl_exprlist_prop le a v.
Proof
  (eval_exprlist_ind2 ge sp e m
     transl_expr_prop
     transl_exprlist_prop
     transl_expr_Evar_correct
     transl_expr_Eop_correct
     transl_expr_Eload_correct
     transl_expr_Econdition_correct
     transl_expr_Elet_correct
     transl_expr_Eletvar_correct
     transl_exprlist_Enil_correct
     transl_exprlist_Econs_correct).

End CORRECTNESS_EXPR.

(** ** Measure over CminorSel states *)

Open Local Scope nat_scope.

Fixpoint size_stmt (s: stmt) : nat :=
  match s with
  | Sskip => 0
  | Sseq s1 s2 => (size_stmt s1 + size_stmt s2 + 1)
  | Sifthenelse cond el s1 s2 => (size_stmt s1 + size_stmt s2 + 1)
  | Sloop s1 => (size_stmt s1 + 1)
  | Sblock s1 => (size_stmt s1 + 1)
  | Sexit n => 0
  | Slabel lbl s1 => (size_stmt s1 + 1)
  | _ => 1
  end.

Fixpoint size_cont (k: cont) : nat :=
  match k with
  | Kseq s k1 => (size_stmt s + size_cont k1 + 1)
  | Kblock k1 => (size_cont k1 + 1)
  | _ => 0%nat
  end.

Definition measure_state (S: CminorSel.state) :=
  match S with
  | CminorSel.State _ s k _ _ _ => (size_stmt s + size_cont k, size_stmt s)
  | _                           => (0, 0)
  end.

Definition lt_state (S1 S2: CminorSel.state) :=
  lex_ord lt lt (measure_state S1) (measure_state S2).

Lemma lt_state_intro:
  forall f1 s1 k1 sp1 e1 m1 f2 s2 k2 sp2 e2 m2,
  size_stmt s1 + size_cont k1 < size_stmt s2 + size_cont k2
  \/ (size_stmt s1 + size_cont k1 = size_stmt s2 + size_cont k2
      /\ size_stmt s1 < size_stmt s2) ->
  lt_state (CminorSel.State f1 s1 k1 sp1 e1 m1)
           (CminorSel.State f2 s2 k2 sp2 e2 m2).
Proof.
  intros. unfold lt_state. simpl. destruct H as [A | [A B]].
  left. auto.
  rewrite A. right. auto.
Qed.

Ltac Lt_state :=
  apply lt_state_intro; simpl; try omega.

Require Import Wellfounded.

Lemma lt_state_wf:
  well_founded lt_state.
Proof.
  unfold lt_state. apply wf_inverse_image with (f := measure_state).
  apply wf_lex_ord. apply lt_wf. apply lt_wf. 
Qed.

(** ** Semantic preservation for the translation of statements *)   

(** The simulation diagram for the translation of statements
  and functions is a "star" diagram of the form:
<<
           I                         I
     S1 ------- R1             S1 ------- R1
     |          |              |          |
   t |        + | t      or  t |        * | t    and |S2| < |S1|
     v          v              v          |
     S2 ------- R2             S2 ------- R2
           I                         I
>>
  where [I] is the [match_states] predicate defined below.  It includes:
- Agreement between the Cminor statement under consideration and
  the current program point in the RTL control-flow graph,
  as captured by the [tr_stmt] predicate.
- Agreement between the Cminor continuation and the RTL control-flow
  graph and call stack, as captured by the [tr_cont] predicate below.
- Agreement between Cminor environments and RTL register environments,
  as captured by [match_envs].

*)

Inductive tr_fun (tf: function) (map: mapping) (f: CminorSel.function)
                     (ngoto: labelmap) (nret: node) (rret: option reg) : Prop :=
  | tr_fun_intro: forall nentry r,
      rret = ret_reg f.(CminorSel.fn_sig) r ->
      tr_stmt tf.(fn_code) map f.(fn_body) nentry nret nil ngoto nret rret ->
      tf.(fn_stacksize) = f.(fn_stackspace) ->
      tr_fun tf map f ngoto nret rret.

Inductive tr_cont: RTL.code -> mapping -> 
                   CminorSel.cont -> node -> list node -> labelmap -> node -> option reg ->
                   list RTL.stackframe -> Prop :=
  | tr_Kseq: forall c map s k nd nexits ngoto nret rret cs n,
      tr_stmt c map s nd n nexits ngoto nret rret ->
      tr_cont c map k n nexits ngoto nret rret cs ->
      tr_cont c map (Kseq s k) nd nexits ngoto nret rret cs
  | tr_Kblock: forall c map k nd nexits ngoto nret rret cs,
      tr_cont c map k nd nexits ngoto nret rret cs ->
      tr_cont c map (Kblock k) nd (nd :: nexits) ngoto nret rret cs
  | tr_Kstop: forall c map ngoto nret rret cs,
      c!nret = Some(Ireturn rret) ->
      match_stacks Kstop cs ->
      tr_cont c map Kstop nret nil ngoto nret rret cs
  | tr_Kcall: forall c map optid f sp e k ngoto nret rret cs,
      c!nret = Some(Ireturn rret) ->
      match_stacks (Kcall optid f sp e k) cs ->
      tr_cont c map (Kcall optid f sp e k) nret nil ngoto nret rret cs

with match_stacks: CminorSel.cont -> list RTL.stackframe -> Prop :=
  | match_stacks_stop:
      match_stacks Kstop nil
  | match_stacks_call: forall optid f sp e k r tf n rs cs map nexits ngoto nret rret,
      map_wf map ->
      tr_fun tf map f ngoto nret rret ->
      match_env map e nil rs ->
      reg_map_ok map r optid ->
      tr_cont tf.(fn_code) map k n nexits ngoto nret rret cs ->
      match_stacks (Kcall optid f sp e k) (Stackframe r tf sp n rs :: cs).

Inductive match_states: CminorSel.state -> RTL.state -> Prop :=
  | match_state:
      forall f s k sp e m tm cs tf ns rs map ncont nexits ngoto nret rret
        (MWF: map_wf map)
        (TS: tr_stmt tf.(fn_code) map s ns ncont nexits ngoto nret rret)
        (TF: tr_fun tf map f ngoto nret rret)
        (TK: tr_cont tf.(fn_code) map k ncont nexits ngoto nret rret cs)
        (ME: match_env map e nil rs)
        (MEXT: Mem.extends m tm),
      match_states (CminorSel.State f s k sp e m)
                   (RTL.State cs tf sp ns rs tm)
  | match_callstate:
      forall f args targs k m tm cs tf
        (TF: transl_fundef f = OK tf)
        (MS: match_stacks k cs)
        (LD: Val.lessdef_list args targs)
        (MEXT: Mem.extends m tm),
      match_states (CminorSel.Callstate f args k m)
                   (RTL.Callstate cs tf targs tm)
  | match_returnstate:
      forall v tv k m tm cs
        (MS: match_stacks k cs)
        (LD: Val.lessdef v tv)
        (MEXT: Mem.extends m tm),
      match_states (CminorSel.Returnstate v k m)
                   (RTL.Returnstate cs tv tm).

Lemma match_stacks_call_cont:
  forall c map k ncont nexits ngoto nret rret cs,
  tr_cont c map k ncont nexits ngoto nret rret cs ->
  match_stacks (call_cont k) cs /\ c!nret = Some(Ireturn rret).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma tr_cont_call_cont:
  forall c map k ncont nexits ngoto nret rret cs,
  tr_cont c map k ncont nexits ngoto nret rret cs ->
  tr_cont c map (call_cont k) nret nil ngoto nret rret cs.
Proof.
  induction 1; simpl; auto; econstructor; eauto.
Qed.

Lemma tr_find_label:
  forall c map lbl n (ngoto: labelmap) nret rret s' k' cs,
  ngoto!lbl = Some n ->
  forall s k ns1 nd1 nexits1,
  find_label lbl s k = Some (s', k') ->
  tr_stmt c map s ns1 nd1 nexits1 ngoto nret rret ->
  tr_cont c map k nd1 nexits1 ngoto nret rret cs ->
  exists ns2, exists nd2, exists nexits2,
     c!n = Some(Inop ns2)
  /\ tr_stmt c map s' ns2 nd2 nexits2 ngoto nret rret
  /\ tr_cont c map k' nd2 nexits2 ngoto nret rret cs.
Proof.
  induction s; intros until nexits1; simpl; try congruence.
  (* seq *)
  caseEq (find_label lbl s1 (Kseq s2 k)); intros.
  inv H1. inv H2. eapply IHs1; eauto. econstructor; eauto.
  inv H2. eapply IHs2; eauto. 
  (* ifthenelse *)
  caseEq (find_label lbl s1 k); intros.
  inv H1. inv H2. eapply IHs1; eauto.
  inv H2. eapply IHs2; eauto.
  (* loop *)
  intros. inversion H1; subst.
  eapply IHs; eauto. econstructor; eauto. econstructor; eauto.
  (* block *)
  intros. inv H1.
  eapply IHs; eauto. econstructor; eauto.
  (* label *)
  destruct (ident_eq lbl l); intros.
  inv H0. inv H1.
  assert (n0 = n). change positive with node in H4. congruence. subst n0.
  exists ns1; exists nd1; exists nexits1; auto.
  inv H1. eapply IHs; eauto.
Qed.

Theorem transl_step_correct:
  forall S1 t S2, CminorSel.step ge S1 t S2 ->
  forall R1, match_states S1 R1 ->
  exists R2,
  (plus RTL.step tge R1 t R2 \/ (star RTL.step tge R1 t R2 /\ lt_state S2 S1))
  /\ match_states S2 R2.
Proof.
  induction 1; intros R1 MSTATE; inv MSTATE.

  (* skip seq *)
  inv TS. inv TK. econstructor; split.
  right; split. apply star_refl. Lt_state.
  econstructor; eauto.

  (* skip block *)
  inv TS. inv TK. econstructor; split.
  right; split. apply star_refl. Lt_state.
  econstructor; eauto. constructor.

  (* skip return *)
  inv TS. 
  assert ((fn_code tf)!ncont = Some(Ireturn rret)
          /\ match_stacks k cs).
    inv TK; simpl in H; try contradiction; auto. 
  destruct H1.
  assert (fn_stacksize tf = fn_stackspace f).
    inv TF. auto. 
  edestruct Mem.free_parallel_extends as [tm' []]; eauto.
  econstructor; split.
  left; apply plus_one. eapply exec_Ireturn. eauto.
  rewrite H3. eauto.
  constructor; auto.
  
  (* assign *)
  inv TS.
  (* optimized translation (not 2 addr) *)
  exploit transl_expr_correct; eauto. 
  intros [rs' [A [B [C D]]]].
  econstructor; split.
  right; split. eauto. Lt_state.
  econstructor; eauto. constructor.
  (* alternate translation (2 addr) *)
  exploit transl_expr_correct; eauto.
  intros [rs' [A [B [C D]]]].
  exploit tr_move_correct; eauto. 
  intros [rs'' [P [Q R]]].
  econstructor; split.
  right; split. eapply star_trans. eexact A. eexact P. traceEq. Lt_state.
  econstructor; eauto. constructor. 
  simpl in B. apply match_env_invariant with (rs'#r <- (rs'#rd)). 
  apply match_env_update_var; auto. 
  intros. rewrite Regmap.gsspec. destruct (peq r0 r). congruence. auto. 

  (* store *)
  inv TS.
  exploit transl_exprlist_correct; eauto.
  intros [rs' [A [B [C D]]]].
  exploit transl_expr_correct; eauto.
  intros [rs'' [E [F [G J]]]].
  assert (Val.lessdef_list vl rs''##rl).
    replace (rs'' ## rl) with (rs' ## rl). auto.
    apply list_map_exten. intros. apply J. auto.
  edestruct eval_addressing_lessdef as [vaddr' []]; eauto.
  edestruct Mem.storev_extends as [tm' []]; eauto.
  econstructor; split.
  left; eapply plus_right. eapply star_trans. eexact A. eexact E. reflexivity.
  eapply exec_Istore with (a := vaddr'). eauto.
  rewrite <- H4. apply eval_addressing_preserved. exact symbols_preserved.
  eauto. traceEq.
  econstructor; eauto. constructor.

  (* call *)
  inv TS; inv H.
  (* indirect *)
  exploit transl_expr_correct; eauto.
  intros [rs' [A [B [C D]]]].
  exploit transl_exprlist_correct; eauto.
  intros [rs'' [E [F [G J]]]].
  exploit functions_translated; eauto. intros [tf' [P Q]].
  econstructor; split.
  left; eapply plus_right. eapply star_trans. eexact A. eexact E. reflexivity.
  eapply exec_Icall; eauto. simpl. rewrite J. destruct C. eauto. discriminate P. simpl; auto.
  apply sig_transl_function; auto.
  traceEq.
  constructor; auto. econstructor; eauto.
  (* direct *)
  exploit transl_exprlist_correct; eauto.
  intros [rs'' [E [F [G J]]]].
  exploit functions_translated; eauto. intros [tf' [P Q]].
  econstructor; split.
  left; eapply plus_right. eexact E.
  eapply exec_Icall; eauto. simpl. rewrite symbols_preserved. rewrite H4. 
    rewrite Genv.find_funct_find_funct_ptr in P. eauto. 
  apply sig_transl_function; auto.
  traceEq.
  constructor; auto. econstructor; eauto.

  (* tailcall *)
  inv TS; inv H.
  (* indirect *)
  exploit transl_expr_correct; eauto.
  intros [rs' [A [B [C D]]]].
  exploit transl_exprlist_correct; eauto.
  intros [rs'' [E [F [G J]]]].
  exploit functions_translated; eauto. intros [tf' [P Q]].
  exploit match_stacks_call_cont; eauto. intros [U V].
  assert (fn_stacksize tf = fn_stackspace f). inv TF; auto.
  edestruct Mem.free_parallel_extends as [tm' []]; eauto.
  econstructor; split.
  left; eapply plus_right. eapply star_trans. eexact A. eexact E. reflexivity.
  eapply exec_Itailcall; eauto. simpl. rewrite J. destruct C. eauto. discriminate P. simpl; auto.
  apply sig_transl_function; auto.
  rewrite H; eauto.
  traceEq.
  constructor; auto.
  (* direct *)
  exploit transl_exprlist_correct; eauto.
  intros [rs'' [E [F [G J]]]].
  exploit functions_translated; eauto. intros [tf' [P Q]].
  exploit match_stacks_call_cont; eauto. intros [U V].
  assert (fn_stacksize tf = fn_stackspace f). inv TF; auto.
  edestruct Mem.free_parallel_extends as [tm' []]; eauto.
  econstructor; split.
  left; eapply plus_right. eexact E.
  eapply exec_Itailcall; eauto. simpl. rewrite symbols_preserved. rewrite H5. 
  rewrite Genv.find_funct_find_funct_ptr in P. eauto. 
  apply sig_transl_function; auto.
  rewrite H; eauto.
  traceEq.
  constructor; auto.

  (* builtin *)
  inv TS. 
  exploit transl_exprlist_correct; eauto.
  intros [rs' [E [F [G J]]]].
  edestruct external_call_mem_extends as [tv [tm' [A [B [C D]]]]]; eauto.
  econstructor; split.
  left. eapply plus_right. eexact E.
  eapply exec_Ibuiltin. eauto. 
  eapply external_call_symbols_preserved. eauto.
  exact symbols_preserved. exact varinfo_preserved.
  traceEq. 
  econstructor; eauto. constructor.
  eapply match_env_update_dest; eauto.

  (* seq *)
  inv TS. 
  econstructor; split.
  right; split. apply star_refl. Lt_state.
  econstructor; eauto. econstructor; eauto. 

  (* ifthenelse *)
  inv TS. inv H13.
  exploit transl_exprlist_correct; eauto. intros [rs' [A [B [C D]]]].
  econstructor; split.
  left. eapply plus_right. eexact A. eapply exec_Icond; eauto.
  eapply eval_condition_lessdef; eauto. traceEq.
  destruct b; econstructor; eauto. 

  (* loop *)
  inversion TS; subst.
  econstructor; split.
  left. apply plus_one. eapply exec_Inop; eauto. 
  econstructor; eauto. 
  econstructor; eauto.
  econstructor; eauto.

  (* block *)
  inv TS.
  econstructor; split.
  right; split. apply star_refl. Lt_state.
  econstructor; eauto. econstructor; eauto.

  (* exit seq *)
  inv TS. inv TK. 
  econstructor; split.
  right; split. apply star_refl. Lt_state.
  econstructor; eauto. econstructor; eauto.

  (* exit block 0 *)
  inv TS. inv TK. simpl in H0. inv H0.
  econstructor; split.
  right; split. apply star_refl. Lt_state.
  econstructor; eauto. econstructor; eauto.

  (* exit block n+1 *)
  inv TS. inv TK. simpl in H0.
  econstructor; split.
  right; split. apply star_refl. Lt_state.
  econstructor; eauto. econstructor; eauto.

  (* switch *)
  inv TS.
  exploit validate_switch_correct; eauto. intro CTM.
  exploit transl_expr_correct; eauto. 
  intros [rs' [A [B [C D]]]].
  exploit transl_switch_correct; eauto. inv C. auto.
  intros [nd [rs'' [E [F G]]]].
  econstructor; split.
  right; split. eapply star_trans. eexact A. eexact E.  traceEq. Lt_state. 
  econstructor; eauto.
  constructor. auto.

  (* return none *)
  inv TS.
  exploit match_stacks_call_cont; eauto. intros [U V].
  inversion TF.
  edestruct Mem.free_parallel_extends as [tm' []]; eauto.
  econstructor; split.
  left; apply plus_one. eapply exec_Ireturn; eauto.
  rewrite H2; eauto.
  constructor; auto.

  (* return some *)
  inv TS.
  exploit transl_expr_correct; eauto.
  intros [rs' [A [B [C D]]]].
  exploit match_stacks_call_cont; eauto. intros [U V].
  inversion TF.
  edestruct Mem.free_parallel_extends as [tm' []]; eauto.
  econstructor; split.
  left; eapply plus_right. eexact A. eapply exec_Ireturn; eauto.
  rewrite H4; eauto. traceEq.
  simpl. constructor; auto.

  (* label *)
  inv TS.
  econstructor; split.
  right; split. apply star_refl. Lt_state.
  econstructor; eauto.

  (* goto *)
  inv TS. inversion TF; subst.
  exploit tr_find_label; eauto. eapply tr_cont_call_cont; eauto. 
  intros [ns2 [nd2 [nexits2 [A [B C]]]]].
  econstructor; split.
  left; apply plus_one. eapply exec_Inop; eauto.
  econstructor; eauto. 

  (* internal call *)
  monadInv TF. exploit transl_function_charact; eauto. intro TRF.
  inversion TRF. subst f0.
  pose (e := set_locals (fn_vars f) (set_params vargs (CminorSel.fn_params f))).
  pose (rs := init_regs targs rparams).
  assert (ME: match_env map2 e nil rs).
    unfold rs, e. eapply match_init_env_init_reg; eauto.
  assert (MWF: map_wf map2).
    assert (map_valid init_mapping s0) by apply init_mapping_valid.
    exploit (add_vars_valid (CminorSel.fn_params f)); eauto. intros [A B].
    eapply add_vars_wf; eauto. eapply add_vars_wf; eauto. apply init_mapping_wf.
  edestruct Mem.alloc_extends as [tm' []]; eauto; try apply Zle_refl.
  econstructor; split.
  left; apply plus_one. eapply exec_function_internal; simpl; eauto.
  simpl. econstructor; eauto.
  econstructor; eauto.
  inversion MS; subst; econstructor; eauto.

  (* external call *)
  monadInv TF. 
  edestruct external_call_mem_extends as [tvres [tm' [A [B [C D]]]]]; eauto.
  econstructor; split.
  left; apply plus_one. eapply exec_function_external; eauto. 
  eapply external_call_symbols_preserved. eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.

  (* return *)
  inv MS.
  econstructor; split. 
  left; apply plus_one; constructor. 
  econstructor; eauto. constructor. 
  eapply match_env_update_dest; eauto.
Qed.

Lemma transl_initial_states:
  forall S, CminorSel.initial_state prog S ->
  exists R, RTL.initial_state tprog R /\ match_states S R.
Proof.
  induction 1.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  econstructor; split.
  econstructor. apply (Genv.init_mem_transf_partial _ _ TRANSL); eauto.
  rewrite (transform_partial_program_main _ _ TRANSL). fold tge.
  rewrite symbols_preserved. eauto.
  eexact A.
  rewrite <- H2. apply sig_transl_function; auto.
  constructor. auto. constructor.
  constructor. apply Mem.extends_refl.
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> CminorSel.final_state S r -> RTL.final_state R r.
Proof.
  intros. inv H0. inv H. inv MS. inv LD. constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (CminorSel.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_star_wf with (order := lt_state).
  eexact symbols_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  apply lt_state_wf. 
  exact transl_step_correct. 
Qed.

End CORRECTNESS.
