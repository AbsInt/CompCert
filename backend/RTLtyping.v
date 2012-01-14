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

(** Typing rules and a type inference algorithm for RTL. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import Globalenvs.
Require Import Values.
Require Import Memory.
Require Import Integers.
Require Import Events.
Require Import Smallstep.
Require Import RTL.
Require Import Conventions.

(** * The type system *)

(** Like Cminor and all intermediate languages, RTL can be equipped with
  a simple type system that statically guarantees that operations
  and addressing modes are applied to the right number of arguments
  and that the arguments are of the correct types.  The type algebra
  is trivial, consisting of the two types [Tint] (for integers and pointers)
  and [Tfloat] (for floats).  

  Additionally, we impose that each pseudo-register has the same type
  throughout the function.  This requirement helps with register allocation,
  enabling each pseudo-register to be mapped to a single hardware register
  or stack location of the correct type.

  Finally, we also check that the successors of instructions
  are valid, i.e. refer to non-empty nodes in the CFG.

  The typing judgement for instructions is of the form [wt_instr f env
  instr], where [f] is the current function (used to type-check
  [Ireturn] instructions) and [env] is a typing environment
  associating types to pseudo-registers.  Since pseudo-registers have
  unique types throughout the function, the typing environment does
  not change during type-checking of individual instructions.  One
  point to note is that we have one polymorphic operator, [Omove],
  which can work over both integers and floats.
*)

Definition regenv := reg -> typ.

Section WT_INSTR.

Variable env: regenv.
Variable funct: function.

Definition valid_successor (s: node) : Prop :=
  exists i, funct.(fn_code)!s = Some i.

Inductive wt_instr : instruction -> Prop :=
  | wt_Inop:
      forall s,
      valid_successor s ->
      wt_instr (Inop s)
  | wt_Iopmove:
      forall r1 r s,
      env r1 = env r ->
      valid_successor s ->
      wt_instr (Iop Omove (r1 :: nil) r s)
  | wt_Iop:
      forall op args res s,
      op <> Omove ->
      (List.map env args, env res) = type_of_operation op ->
      valid_successor s ->
      wt_instr (Iop op args res s)
  | wt_Iload:
      forall chunk addr args dst s,
      List.map env args = type_of_addressing addr ->
      env dst = type_of_chunk chunk ->
      valid_successor s ->
      wt_instr (Iload chunk addr args dst s)
  | wt_Istore:
      forall chunk addr args src s,
      List.map env args = type_of_addressing addr ->
      env src = type_of_chunk chunk ->
      valid_successor s ->
      wt_instr (Istore chunk addr args src s)
  | wt_Icall:
      forall sig ros args res s,
      match ros with inl r => env r = Tint | inr s => True end ->
      List.map env args = sig.(sig_args) ->
      env res = proj_sig_res sig ->
      valid_successor s ->
      wt_instr (Icall sig ros args res s)
  | wt_Itailcall:
      forall sig ros args,
      match ros with inl r => env r = Tint | inr s => True end ->
      sig.(sig_res) = funct.(fn_sig).(sig_res) ->
      List.map env args = sig.(sig_args) ->
      tailcall_possible sig ->
      wt_instr (Itailcall sig ros args)
  | wt_Ibuiltin:
      forall ef args res s,
      List.map env args = (ef_sig ef).(sig_args) ->
      env res = proj_sig_res (ef_sig ef) ->
      arity_ok (ef_sig ef).(sig_args) = true \/ ef_reloads ef = false ->
      valid_successor s ->
      wt_instr (Ibuiltin ef args res s)
  | wt_Icond:
      forall cond args s1 s2,
      List.map env args = type_of_condition cond ->
      valid_successor s1 ->
      valid_successor s2 ->
      wt_instr (Icond cond args s1 s2)
  | wt_Ijumptable:
      forall arg tbl,
      env arg = Tint ->
      (forall s, In s tbl -> valid_successor s) ->
      list_length_z tbl * 4 <= Int.max_unsigned ->
      wt_instr (Ijumptable arg tbl)
  | wt_Ireturn: 
      forall optres,
      option_map env optres = funct.(fn_sig).(sig_res) ->
      wt_instr (Ireturn optres).

End WT_INSTR.

(** A function [f] is well-typed w.r.t. a typing environment [env],
   written [wt_function env f], if all instructions are well-typed,
   parameters agree in types with the function signature, and
   parameters are pairwise distinct. *)

Record wt_function (f: function) (env: regenv): Prop :=
  mk_wt_function {
    wt_params:
      List.map env f.(fn_params) = f.(fn_sig).(sig_args);
    wt_norepet:
      list_norepet f.(fn_params);
    wt_instrs:
      forall pc instr, 
      f.(fn_code)!pc = Some instr -> wt_instr env f instr;
    wt_entrypoint:
      valid_successor f f.(fn_entrypoint)
}.

Inductive wt_fundef: fundef -> Prop :=
  | wt_fundef_external: forall ef,
      wt_fundef (External ef)
  | wt_function_internal: forall f env,
      wt_function f env ->
      wt_fundef (Internal f).

Definition wt_program (p: program): Prop :=
  forall i f, In (i, f) (prog_funct p) -> wt_fundef f.

(** * Type inference *)

(** There are several ways to ensure that RTL code is well-typed and
  to obtain the typing environment (type assignment for pseudo-registers)
  needed for register allocation.  One is to start with well-typed Cminor
  code and show type preservation for RTL generation and RTL optimizations.
  Another is to start with untyped RTL and run a type inference algorithm
  that reconstructs the typing environment, determining the type of
  each pseudo-register from its uses in the code.  We follow the second
  approach.

  We delegate the task of determining the type of each pseudo-register
  to an external ``oracle'': a function written in Caml and not
  proved correct.  We verify the returned type environment using
  the following Coq code, which we will prove correct. *)

Parameter infer_type_environment:
  function -> list (node * instruction) -> option regenv.

(** ** Algorithm to check the correctness of a type environment *)

Section TYPECHECKING.

Variable funct: function.
Variable env: regenv.

Definition check_reg (r: reg) (ty: typ): bool :=
  if typ_eq (env r) ty then true else false.

Fixpoint check_regs (rl: list reg) (tyl: list typ) {struct rl}: bool :=
  match rl, tyl with
  | nil, nil => true
  | r1::rs, ty::tys => check_reg r1 ty && check_regs rs tys
  | _, _ => false
  end.

Definition check_op (op: operation) (args: list reg) (res: reg): bool :=
  let (targs, tres) := type_of_operation op in
  check_regs args targs && check_reg res tres.

Definition check_successor (s: node) : bool :=
  match funct.(fn_code)!s with None => false | Some i => true end.

Definition check_instr (i: instruction) : bool :=
  match i with
  | Inop s =>
      check_successor s
  | Iop Omove (arg::nil) res s =>
      if typ_eq (env arg) (env res) 
      then check_successor s
      else false
  | Iop Omove args res s =>
      false
  | Iop op args res s =>
      check_op op args res && check_successor s
  | Iload chunk addr args dst s =>
      check_regs args (type_of_addressing addr)
      && check_reg dst (type_of_chunk chunk)
      && check_successor s
  | Istore chunk addr args src s =>
      check_regs args (type_of_addressing addr)
      && check_reg src (type_of_chunk chunk)
      && check_successor s
  | Icall sig ros args res s =>
      match ros with inl r => check_reg r Tint | inr s => true end
      && check_regs args sig.(sig_args)
      && check_reg res (proj_sig_res sig)
      && check_successor s
  | Itailcall sig ros args =>
      match ros with inl r => check_reg r Tint | inr s => true end
      && check_regs args sig.(sig_args)
      && opt_typ_eq sig.(sig_res) funct.(fn_sig).(sig_res)
      && tailcall_is_possible sig
  | Ibuiltin ef args res s =>
      check_regs args (ef_sig ef).(sig_args)
      && check_reg res (proj_sig_res (ef_sig ef))
      && (if ef_reloads ef then arity_ok (ef_sig ef).(sig_args) else true)
      && check_successor s
  | Icond cond args s1 s2 =>
      check_regs args (type_of_condition cond)
      && check_successor s1
      && check_successor s2
  | Ijumptable arg tbl =>
      check_reg arg Tint
      && List.forallb check_successor tbl
      && zle (list_length_z tbl * 4) Int.max_unsigned
  | Ireturn optres =>
      match optres, funct.(fn_sig).(sig_res) with
      | None, None => true
      | Some r, Some t => check_reg r t
      | _, _ => false
      end
  end.

Definition check_params_norepet (params: list reg): bool :=
  if list_norepet_dec Reg.eq params then true else false.

Fixpoint check_instrs (instrs: list (node * instruction)) : bool :=
  match instrs with
  | nil => true
  | (pc, i) :: rem => check_instr i && check_instrs rem
  end.

(** ** Correctness of the type-checking algorithm *)

Ltac elimAndb :=
  match goal with
  | [ H: _ && _ = true |- _ ] =>
      elim (andb_prop _ _ H); clear H; intros; elimAndb
  | _ =>
      idtac
  end.

Lemma check_reg_correct:
  forall r ty, check_reg r ty = true -> env r = ty.
Proof.
  unfold check_reg; intros.
  destruct (typ_eq (env r) ty). auto. discriminate.
Qed.

Lemma check_regs_correct:
  forall rl tyl, check_regs rl tyl = true -> List.map env rl = tyl.
Proof.
  induction rl; destruct tyl; simpl; intros.
  auto. discriminate. discriminate.
  elimAndb.
  rewrite (check_reg_correct _ _ H). rewrite (IHrl tyl H0). auto.
Qed.

Lemma check_op_correct:
  forall op args res,
  check_op op args res = true ->
  (List.map env args, env res) = type_of_operation op.
Proof.
  unfold check_op; intros.
  destruct (type_of_operation op) as [targs tres].
  elimAndb. 
  rewrite (check_regs_correct _ _ H).
  rewrite (check_reg_correct _ _ H0).
  auto.
Qed.

Lemma check_successor_correct:
  forall s,
  check_successor s = true -> valid_successor funct s.
Proof.
  intro; unfold check_successor, valid_successor.
  destruct (fn_code funct)!s; intro.
  exists i; auto.
  discriminate.
Qed.

Lemma check_instr_correct:
  forall i, check_instr i = true -> wt_instr env funct i.
Proof.
  unfold check_instr; intros; destruct i; elimAndb.
  (* nop *)
  constructor. apply check_successor_correct; auto.
  (* op *)
  destruct o; elimAndb;
  try (apply wt_Iop; [ congruence
                     | apply check_op_correct; auto
                     | apply check_successor_correct; auto ]).
  destruct l; try discriminate. destruct l; try discriminate.
  destruct (typ_eq (env r0) (env r)); try discriminate.
  apply wt_Iopmove; auto. apply check_successor_correct; auto.
  (* load *)
  constructor. apply check_regs_correct; auto. apply check_reg_correct; auto.
  apply check_successor_correct; auto.
  (* store *)
  constructor. apply check_regs_correct; auto. apply check_reg_correct; auto.
  apply check_successor_correct; auto.
  (* call *)
  constructor.
  destruct s0; auto. apply check_reg_correct; auto.
  apply check_regs_correct; auto.
  apply check_reg_correct; auto.
  apply check_successor_correct; auto.
  (* tailcall *)
  constructor.
  destruct s0; auto. apply check_reg_correct; auto.
  eapply proj_sumbool_true; eauto.
  apply check_regs_correct; auto.
  apply tailcall_is_possible_correct; auto.
  (* builtin *)
  constructor.
  apply check_regs_correct; auto.
  apply check_reg_correct; auto.
  auto.
  destruct (ef_reloads e); auto. 
  apply check_successor_correct; auto.
  (* cond *)
  constructor. apply check_regs_correct; auto.
  apply check_successor_correct; auto.
  apply check_successor_correct; auto.
  (* jumptable *)
  constructor. apply check_reg_correct; auto.
  rewrite List.forallb_forall in H1. intros. apply check_successor_correct; auto.
  eapply proj_sumbool_true. eauto.  
  (* return *)
  constructor. 
  destruct o; simpl; destruct funct.(fn_sig).(sig_res); try discriminate.
  rewrite (check_reg_correct _ _ H); auto.
  auto.
Qed.

Lemma check_instrs_correct:
  forall instrs,
  check_instrs instrs = true ->
  forall pc i, In (pc, i) instrs -> wt_instr env funct i.
Proof.
  induction instrs; simpl; intros.
  elim H0.
  destruct a as [pc' i']. elimAndb. 
  elim H0; intro.
  inversion H2; subst pc' i'. apply check_instr_correct; auto.
  eauto.
Qed.

End TYPECHECKING.

(** ** The type inference function **)

Open Scope string_scope.

Definition type_function (f: function): res regenv :=
  let instrs := PTree.elements f.(fn_code) in
  match infer_type_environment f instrs with
  | None => Error (msg "RTL type inference error")
  | Some env =>
      if check_regs env f.(fn_params) f.(fn_sig).(sig_args)
      && check_params_norepet f.(fn_params)
      && check_instrs f env instrs
      && check_successor f f.(fn_entrypoint)
      then OK env
      else Error (msg "RTL type checking error")
  end.

Lemma type_function_correct:
  forall f env,
  type_function f = OK env ->
  wt_function f env.
Proof.
  unfold type_function; intros until env.
  set (instrs := PTree.elements f.(fn_code)).
  case (infer_type_environment f instrs).
  intro env'. 
  caseEq (check_regs env' f.(fn_params) f.(fn_sig).(sig_args)); intro; simpl; try congruence.
  caseEq (check_params_norepet f.(fn_params)); intro; simpl; try congruence.
  caseEq (check_instrs f env' instrs); intro; simpl; try congruence.
  caseEq (check_successor f (fn_entrypoint f)); intro; simpl; try congruence.
  intro EQ; inversion EQ; subst env'.
  constructor. 
  apply check_regs_correct; auto.
  unfold check_params_norepet in H0. 
  destruct (list_norepet_dec Reg.eq (fn_params f)). auto. discriminate.
  intros. eapply check_instrs_correct. eauto. 
  unfold instrs. apply PTree.elements_correct. eauto.
  apply check_successor_correct. auto.
  congruence.
Qed.

(** * Type preservation during evaluation *)

(** The type system for RTL is not sound in that it does not guarantee
  progress: well-typed instructions such as [Icall] can fail because
  of run-time type tests (such as the equality between callee and caller's
  signatures).  However, the type system guarantees a type preservation
  property: if the execution does not fail because of a failed run-time
  test, the result values and register states match the static
  typing assumptions.  This preservation property will be useful
  later for the proof of semantic equivalence between [Linear] and [Mach].
  Even though we do not need it for [RTL], we show preservation for [RTL]
  here, as a warm-up exercise and because some of the lemmas will be
  useful later. *)

Definition wt_regset (env: regenv) (rs: regset) : Prop :=
  forall r, Val.has_type (rs#r) (env r).

Lemma wt_regset_assign:
  forall env rs v r,
  wt_regset env rs ->
  Val.has_type v (env r) ->
  wt_regset env (rs#r <- v).
Proof.
  intros; red; intros. 
  rewrite Regmap.gsspec.
  case (peq r0 r); intro.
  subst r0. assumption.
  apply H.
Qed.

Lemma wt_regset_list:
  forall env rs,
  wt_regset env rs ->
  forall rl, Val.has_type_list (rs##rl) (List.map env rl).
Proof.
  induction rl; simpl.
  auto.
  split. apply H. apply IHrl.
Qed.  

Lemma wt_init_regs:
  forall env rl args,
  Val.has_type_list args (List.map env rl) ->
  wt_regset env (init_regs args rl).
Proof.
  induction rl; destruct args; simpl; intuition.
  red; intros. rewrite Regmap.gi. simpl; auto. 
  apply wt_regset_assign; auto.
Qed.

Inductive wt_stackframes: list stackframe -> option typ -> Prop :=
  | wt_stackframes_nil:
      wt_stackframes nil (Some Tint)
  | wt_stackframes_cons:
      forall s res f sp pc rs env tyres,
      wt_function f env ->
      wt_regset env rs ->
      env res = match tyres with None => Tint | Some t => t end ->
      wt_stackframes s (sig_res (fn_sig f)) ->
      wt_stackframes (Stackframe res f sp pc rs :: s) tyres.

Inductive wt_state: state -> Prop :=
  | wt_state_intro:
      forall s f sp pc rs m env
        (WT_STK: wt_stackframes s (sig_res (fn_sig f)))
        (WT_FN: wt_function f env)
        (WT_RS: wt_regset env rs),
      wt_state (State s f sp pc rs m)
  | wt_state_call:
      forall s f args m,
      wt_stackframes s (sig_res (funsig f)) ->
      wt_fundef f ->
      Val.has_type_list args (sig_args (funsig f)) ->
      wt_state (Callstate s f args m)
  | wt_state_return:
      forall s v m tyres,
      wt_stackframes s tyres ->
      Val.has_type v (match tyres with None => Tint | Some t => t end) ->
      wt_state (Returnstate s v m).

Section SUBJECT_REDUCTION.

Variable p: program.

Hypothesis wt_p: wt_program p.

Let ge := Genv.globalenv p.

Lemma subject_reduction:
  forall st1 t st2, step ge st1 t st2 ->
  forall (WT: wt_state st1), wt_state st2.
Proof.
  induction 1; intros; inv WT;
  try (generalize (wt_instrs _ _ WT_FN pc _ H);
       intro WT_INSTR;
       inv WT_INSTR).
  (* Inop *)
  econstructor; eauto.
  (* Iop *)
  econstructor; eauto.
  apply wt_regset_assign. auto. 
  simpl in H0. inv H0. rewrite <- H3. apply WT_RS.
  econstructor; eauto.
  apply wt_regset_assign. auto.
  replace (env res) with (snd (type_of_operation op)).
  eapply type_of_operation_sound; eauto.
  rewrite <- H6. reflexivity.
  (* Iload *)
  econstructor; eauto.
  apply wt_regset_assign. auto. rewrite H8. 
  eapply type_of_chunk_correct; eauto.
  (* Istore *)
  econstructor; eauto.
  (* Icall *)
  assert (wt_fundef fd).
    destruct ros; simpl in H0.
    pattern fd. apply Genv.find_funct_prop with fundef unit p (rs#r).
    exact wt_p. exact H0. 
    caseEq (Genv.find_symbol ge i); intros; rewrite H1 in H0.
    pattern fd. apply Genv.find_funct_ptr_prop with fundef unit p b.
    exact wt_p. exact H0.
    discriminate.
  econstructor; eauto.
  econstructor; eauto.
  rewrite <- H7. apply wt_regset_list. auto.
  (* Itailcall *)
  assert (wt_fundef fd).
    destruct ros; simpl in H0.
    pattern fd. apply Genv.find_funct_prop with fundef unit p (rs#r).
    exact wt_p. exact H0. 
    caseEq (Genv.find_symbol ge i); intros; rewrite H1 in H0.
    pattern fd. apply Genv.find_funct_ptr_prop with fundef unit p b.
    exact wt_p. exact H0.
    discriminate.
  econstructor; eauto.
  rewrite H6; auto.
  rewrite <- H7. apply wt_regset_list. auto.
  (* Ibuiltin *)
  econstructor; eauto.
  apply wt_regset_assign. auto. 
  rewrite H6. eapply external_call_well_typed; eauto. 
  (* Icond *)
  econstructor; eauto.
  (* Ijumptable *)
  econstructor; eauto.
  (* Ireturn *)
  econstructor; eauto. 
  destruct or; simpl in *.
  rewrite <- H2. apply WT_RS. exact I.
  (* internal function *)
  simpl in *. inv H5. inversion H1; subst.  
  econstructor; eauto.
  apply wt_init_regs; auto. rewrite wt_params0; auto.
  (* external function *)
  simpl in *. inv H5. 
  econstructor; eauto. 
  change (Val.has_type res (proj_sig_res (ef_sig ef))).
  eapply external_call_well_typed; eauto.
  (* return *)
  inv H1. econstructor; eauto. 
  apply wt_regset_assign; auto. congruence. 
Qed.

End SUBJECT_REDUCTION.
