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
Require Import Unityping.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import Globalenvs.
Require Import Values.
Require Import Integers.
Require Import Memory.
Require Import Events.
Require Import RTL.
Require Import Conventions.

(** * The type system *)

(** Like Cminor and all intermediate languages, RTL can be equipped with
  a simple type system that statically guarantees that operations
  and addressing modes are applied to the right number of arguments
  and that the arguments are of the correct types.   The type algebra
  is very simple, consisting of the four types [Tint] (for integers
  and pointers), [Tfloat] (for double-precision floats), [Tlong]
  (for 64-bit integers) and [Tsingle] (for single-precision floats).

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

Variable funct: function.
Variable env: regenv.

Definition valid_successor (s: node) : Prop :=
  exists i, funct.(fn_code)!s = Some i.

Inductive wt_instr : instruction -> Prop :=
  | wt_Inop:
      forall s,
      valid_successor s ->
      wt_instr (Inop s)
  | wt_Iopmove:
      forall r1 r s,
      env r = env r1 ->
      valid_successor s ->
      wt_instr (Iop Omove (r1 :: nil) r s)
  | wt_Iop:
      forall op args res s,
      op <> Omove ->
      map env args = fst (type_of_operation op) ->
      env res = snd (type_of_operation op) ->
      valid_successor s ->
      wt_instr (Iop op args res s)
  | wt_Iload:
      forall chunk addr args dst s,
      map env args = type_of_addressing addr ->
      env dst = type_of_chunk chunk ->
      valid_successor s ->
      wt_instr (Iload chunk addr args dst s)
  | wt_Istore:
      forall chunk addr args src s,
      map env args = type_of_addressing addr ->
      env src = type_of_chunk chunk ->
      valid_successor s ->
      wt_instr (Istore chunk addr args src s)
  | wt_Icall:
      forall sig ros args res s,
      match ros with inl r => env r = Tint | inr s => True end ->
      map env args = sig.(sig_args) ->
      env res = proj_sig_res sig ->
      valid_successor s ->
      wt_instr (Icall sig ros args res s)
  | wt_Itailcall:
      forall sig ros args,
      match ros with inl r => env r = Tint | inr s => True end ->
      map env args = sig.(sig_args) ->
      sig.(sig_res) = funct.(fn_sig).(sig_res) ->
      tailcall_possible sig ->
      wt_instr (Itailcall sig ros args)
  | wt_Ibuiltin:
      forall ef args res s,
      map env args = (ef_sig ef).(sig_args) ->
      env res = proj_sig_res (ef_sig ef) ->
      valid_successor s ->
      wt_instr (Ibuiltin ef args res s)
  | wt_Icond:
      forall cond args s1 s2,
      map env args = type_of_condition cond ->
      valid_successor s1 ->
      valid_successor s2 ->
      wt_instr (Icond cond args s1 s2)
  | wt_Ijumptable:
      forall arg tbl,
      env arg = Tint ->
      (forall s, In s tbl -> valid_successor s) ->
      list_length_z tbl * 4 <= Int.max_unsigned ->
      wt_instr (Ijumptable arg tbl)
  | wt_Ireturn_none:
      funct.(fn_sig).(sig_res) = None ->
      wt_instr (Ireturn None)
  | wt_Ireturn_some:
      forall arg ty,
      funct.(fn_sig).(sig_res) = Some ty ->
      env arg = ty ->
      wt_instr (Ireturn (Some arg)).

End WT_INSTR.

(** A function [f] is well-typed w.r.t. a typing environment [env],
   written [wt_function env f], if all instructions are well-typed,
   parameters agree in types with the function signature, and
   parameters are pairwise distinct. *)

Record wt_function (f: function) (env: regenv): Prop :=
  mk_wt_function {
    wt_params:
      map env f.(fn_params) = f.(fn_sig).(sig_args);
    wt_norepet:
      list_norepet f.(fn_params);
    wt_instrs:
      forall pc instr, 
      f.(fn_code)!pc = Some instr -> wt_instr f env instr;
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
  forall i f, In (i, Gfun f) (prog_defs p) -> wt_fundef f.

(** * Type inference *)

(** Type inference reuses the generic solver for unification constraints
  defined in module [Unityping]. *)

Module RTLtypes <: TYPE_ALGEBRA.

Definition t := typ.
Definition eq := typ_eq.
Definition default := Tint.

End RTLtypes.

Module S := UniSolver(RTLtypes).

Section INFERENCE.

Local Open Scope error_monad_scope.

Variable f: function.

(** Checking the validity of successor nodes. *)

Definition check_successor (s: node): res unit :=
  match f.(fn_code)!s with
  | None => Error (MSG "bad successor " :: POS s :: nil)
  | Some i => OK tt
  end.

Fixpoint check_successors (sl: list node): res unit :=
  match sl with
  | nil => OK tt
  | s1 :: sl' => do x <- check_successor s1; check_successors sl'
  end.

(** Check structural constraints and process / record all type constraints. *)

Definition type_ros (e: S.typenv) (ros: reg + ident) : res S.typenv :=
  match ros with
  | inl r => S.set e r Tint
  | inr s => OK e
  end.

Definition is_move (op: operation) : bool :=
  match op with Omove => true | _ => false end.

Definition type_instr (e: S.typenv) (i: instruction) : res S.typenv :=
  match i with
  | Inop s =>
      do x <- check_successor s; OK e
  | Iop op args res s =>
      do x <- check_successor s;
      if is_move op then
        match args with
        | arg :: nil => do (changed, e') <- S.move e res arg; OK e'
        | _ => Error (msg "ill-formed move")
        end
      else
       (let (targs, tres) := type_of_operation op in
        do e1 <- S.set_list e args targs; S.set e1 res tres)
  | Iload chunk addr args dst s =>
      do x <- check_successor s;
      do e1 <- S.set_list e args (type_of_addressing addr);
      S.set e1 dst (type_of_chunk chunk)
  | Istore chunk addr args src s =>
      do x <- check_successor s;
      do e1 <- S.set_list e args (type_of_addressing addr);
      S.set e1 src (type_of_chunk chunk)
  | Icall sig ros args res s =>
      do x <- check_successor s;
      do e1 <- type_ros e ros;
      do e2 <- S.set_list e1 args sig.(sig_args);
      S.set e2 res (proj_sig_res sig)
  | Itailcall sig ros args =>
      do e1 <- type_ros e ros;
      do e2 <- S.set_list e1 args sig.(sig_args);
      if opt_typ_eq sig.(sig_res) f.(fn_sig).(sig_res) then
        if tailcall_is_possible sig
        then OK e2
        else Error(msg "tailcall not possible")
      else Error(msg "bad return type in tailcall")
  | Ibuiltin ef args res s =>
      let sig := ef_sig ef in
      do x <- check_successor s;
      do e1 <- S.set_list e args sig.(sig_args);
      S.set e1 res (proj_sig_res sig)
 | Icond cond args s1 s2 =>
      do x1 <- check_successor s1;
      do x2 <- check_successor s2;
      S.set_list e args (type_of_condition cond)
 | Ijumptable arg tbl =>
      do x <- check_successors tbl;
      do e1 <- S.set e arg Tint;
      if zle (list_length_z tbl * 4) Int.max_unsigned
      then OK e1
      else Error(msg "jumptable too big")
  | Ireturn optres =>
      match optres, f.(fn_sig).(sig_res) with
      | None, None => OK e
      | Some r, Some t => S.set e r t
      | _, _ => Error(msg "bad return")
      end
  end.

Definition type_code (e: S.typenv): res S.typenv :=
  PTree.fold (fun re pc i =>
    match re with
    | Error _ => re
    | OK e =>
        match type_instr e i with
        | Error msg => Error(MSG "At PC " :: POS pc :: MSG ": " :: msg)
        | OK e' => OK e'
        end
    end)
  f.(fn_code) (OK e).

(** Solve remaining constraints *)

Definition check_params_norepet (params: list reg): res unit := 
  if list_norepet_dec Reg.eq params
  then OK tt
  else Error(msg "duplicate parameters").

Definition type_function : res regenv :=
  do e1 <- type_code S.initial;
  do e2 <- S.set_list e1 f.(fn_params) f.(fn_sig).(sig_args);
  do te <- S.solve e2;
  do x1 <- check_params_norepet f.(fn_params);
  do x2 <- check_successor f.(fn_entrypoint);
  OK te.

(** ** Soundness proof *)

Remark type_ros_incr:
  forall e ros e' te, type_ros e ros = OK e' -> S.satisf te e' -> S.satisf te e.
Proof.
  unfold type_ros; intros. destruct ros. eauto with ty. inv H; auto with ty.
Qed.

Hint Resolve type_ros_incr: ty.

Lemma type_ros_sound:
  forall e ros e' te, type_ros e ros = OK e' -> S.satisf te e' ->
  match ros with inl r => te r = Tint | inr s => True end.
Proof.
  unfold type_ros; intros. destruct ros. 
  eapply S.set_sound; eauto.
  auto.
Qed.

Lemma check_successor_sound:
  forall s x, check_successor s = OK x -> valid_successor f s.
Proof.
  unfold check_successor, valid_successor; intros. 
  destruct (fn_code f)!s; inv H. exists i; auto.
Qed.

Hint Resolve check_successor_sound: ty.

Lemma check_successors_sound:
  forall sl x, check_successors sl = OK x -> forall s, In s sl -> valid_successor f s.
Proof.
  induction sl; simpl; intros. 
  contradiction.
  monadInv H. destruct H0. subst a; eauto with ty. eauto. 
Qed.

Lemma type_instr_incr:
  forall e i e' te,
  type_instr e i = OK e' -> S.satisf te e' -> S.satisf te e.
Proof.
  intros; destruct i; try (monadInv H); eauto with ty.
- (* op *)
  destruct (is_move o) eqn:ISMOVE.
  destruct l; try discriminate. destruct l; monadInv EQ0. eauto with ty.
  destruct (type_of_operation o) as [targs tres] eqn:TYOP. monadInv EQ0. eauto with ty.
- (* tailcall *)
  destruct (opt_typ_eq (sig_res s) (sig_res (fn_sig f))); try discriminate.
  destruct (tailcall_is_possible s) eqn:TCIP; inv EQ2.
  eauto with ty.
- (* jumptable *)
  destruct (zle (list_length_z l * 4) Int.max_unsigned); inv EQ2.
  eauto with ty.
- (* return *)
  simpl in H. destruct o as [r|] eqn: RET; destruct (sig_res (fn_sig f)) as [t|] eqn: RES; try discriminate.
  eauto with ty.
  inv H; auto with ty.
Qed.

Lemma type_instr_sound:
  forall e i e' te,
  type_instr e i = OK e' -> S.satisf te e' -> wt_instr f te i.
Proof.
  intros; destruct i; try (monadInv H); simpl.
- (* nop *)
  constructor; eauto with ty.
- (* op *)
  destruct (is_move o) eqn:ISMOVE.
  (* move *)
  + assert (o = Omove) by (unfold is_move in ISMOVE; destruct o; congruence).
    subst o.
    destruct l; try discriminate. destruct l; monadInv EQ0.
    constructor. eapply S.move_sound; eauto. eauto with ty.
  + destruct (type_of_operation o) as [targs tres] eqn:TYOP. monadInv EQ0.
    apply wt_Iop. 
    unfold is_move in ISMOVE; destruct o; congruence.
    rewrite TYOP. eapply S.set_list_sound; eauto with ty.
    rewrite TYOP. eapply S.set_sound; eauto with ty.
    eauto with ty.
- (* load *)
  constructor.
  eapply S.set_list_sound; eauto with ty.
  eapply S.set_sound; eauto with ty.
  eauto with ty.
- (* store *)
  constructor.
  eapply S.set_list_sound; eauto with ty.
  eapply S.set_sound; eauto with ty.
  eauto with ty.
- (* call *)
  constructor. 
  eapply type_ros_sound; eauto with ty.
  eapply S.set_list_sound; eauto with ty.
  eapply S.set_sound; eauto with ty.
  eauto with ty.
- (* tailcall *)
  destruct (opt_typ_eq (sig_res s) (sig_res (fn_sig f))); try discriminate.
  destruct (tailcall_is_possible s) eqn:TCIP; inv EQ2.
  constructor.
  eapply type_ros_sound; eauto with ty. 
  eapply S.set_list_sound; eauto with ty.
  auto.
  apply tailcall_is_possible_correct; auto.
- (* builtin *)
  constructor.
  eapply S.set_list_sound; eauto with ty.
  eapply S.set_sound; eauto with ty.
  eauto with ty.
- (* cond *)
  constructor.
  eapply S.set_list_sound; eauto with ty.
  eauto with ty.
  eauto with ty.
- (* jumptable *)
  destruct (zle (list_length_z l * 4) Int.max_unsigned); inv EQ2.
  constructor.
  eapply S.set_sound; eauto.
  eapply check_successors_sound; eauto. 
  auto.
- (* return *)
  simpl in H. destruct o as [r|] eqn: RET; destruct (sig_res (fn_sig f)) as [t|] eqn: RES; try discriminate.
  econstructor. eauto. eapply S.set_sound; eauto with ty.
  inv H. constructor. auto. 
Qed.

Lemma type_code_sound:
  forall pc i e e' te,
  type_code e = OK e' ->
  f.(fn_code)!pc = Some i -> S.satisf te e' -> wt_instr f te i.
Proof.
  intros pc i e0 e1 te TCODE.
  set (P := fun c opte =>
         match opte with
         | Error _ => True
         | OK e' => c!pc = Some i -> S.satisf te e' -> wt_instr f te i
         end).
  change (P f.(fn_code) (OK e1)).
  rewrite <- TCODE. unfold type_code. apply PTree_Properties.fold_rec; unfold P; intros. 
  - (* extensionality *)
    destruct a; auto; intros. rewrite <- H in H1. eapply H0; eauto. 
  - (* base case *)
    rewrite PTree.gempty in H; discriminate.
  - (* inductive case *)
    destruct a as [e|?]; auto. 
    destruct (type_instr e v) as [e'|?] eqn:TYINSTR; auto.
    intros. rewrite PTree.gsspec in H2. destruct (peq pc k). 
    inv H2. eapply type_instr_sound; eauto. 
    eapply H1; eauto. eapply type_instr_incr; eauto.
Qed.

Theorem type_function_correct:
  forall env, type_function = OK env -> wt_function f env.
Proof.
  unfold type_function; intros. monadInv H.
  assert (SAT0: S.satisf env x0) by (eapply S.solve_sound; eauto).
  assert (SAT1: S.satisf env x) by (eauto with ty).
  constructor.
- (* type of parameters *)
  eapply S.set_list_sound; eauto.
- (* parameters are unique *)
  unfold check_params_norepet in EQ2. 
  destruct (list_norepet_dec Reg.eq (fn_params f)); inv EQ2; auto. 
- (* instructions are well typed *)
  intros. eapply type_code_sound; eauto. 
- (* entry point is valid *)
  eauto with ty. 
Qed.

(** ** Completeness proof *)

Lemma type_ros_complete:
  forall te ros e,
  S.satisf te e ->
  match ros with inl r => te r = Tint | inr s => True end ->
  exists e', type_ros e ros = OK e' /\ S.satisf te e'.
Proof.
  intros; destruct ros; simpl. 
  eapply S.set_complete; eauto.
  exists e; auto.
Qed.

Lemma check_successor_complete:
  forall s, valid_successor f s -> check_successor s = OK tt.
Proof.
  unfold valid_successor, check_successor; intros. 
  destruct H as [i EQ]; rewrite EQ; auto.
Qed.

Lemma type_instr_complete:
  forall te e i,
  S.satisf te e ->
  wt_instr f te i ->
  exists e', type_instr e i = OK e' /\ S.satisf te e'.
Proof.
  induction 2; simpl.
- (* nop *)
  econstructor; split. rewrite check_successor_complete; simpl; eauto. auto.
- (* move *)
  exploit S.move_complete; eauto. intros (changed & e' & A & B).
  exists e'; split. rewrite check_successor_complete by auto; simpl. rewrite A; auto. auto.
- (* other op *)
  destruct (type_of_operation op) as [targ tres]. simpl in *.
  exploit S.set_list_complete. eauto. eauto. intros [e1 [A B]].
  exploit S.set_complete. eexact B. eauto. intros [e2 [C D]].
  exists e2; split; auto.
  rewrite check_successor_complete by auto; simpl. 
  replace (is_move op) with false. rewrite A; simpl; rewrite C; auto.
  destruct op; reflexivity || congruence.
- (* load *)
  exploit S.set_list_complete. eauto. eauto. intros [e1 [A B]].
  exploit S.set_complete. eexact B. eauto. intros [e2 [C D]].
  exists e2; split; auto.
  rewrite check_successor_complete by auto; simpl. 
  rewrite A; simpl; rewrite C; auto.
- (* store *)
  exploit S.set_list_complete. eauto. eauto. intros [e1 [A B]].
  exploit S.set_complete. eexact B. eauto. intros [e2 [C D]].
  exists e2; split; auto.
  rewrite check_successor_complete by auto; simpl. 
  rewrite A; simpl; rewrite C; auto.
- (* call *)
  exploit type_ros_complete. eauto. eauto. intros [e1 [A B]].
  exploit S.set_list_complete. eauto. eauto. intros [e2 [C D]].
  exploit S.set_complete. eexact D. eauto. intros [e3 [E F]].
  exists e3; split; auto. 
  rewrite check_successor_complete by auto; simpl. 
  rewrite A; simpl; rewrite C; simpl; rewrite E; auto.
- (* tailcall *)
  exploit type_ros_complete. eauto. eauto. intros [e1 [A B]].
  exploit S.set_list_complete. eauto. eauto. intros [e2 [C D]].
  exists e2; split; auto. 
  rewrite A; simpl; rewrite C; simpl. 
  rewrite H2; rewrite dec_eq_true. 
  replace (tailcall_is_possible sig) with true; auto. 
  revert H3. unfold tailcall_possible, tailcall_is_possible. generalize (loc_arguments sig). 
  induction l; simpl; intros. auto.
  exploit (H3 a); auto. intros. destruct a; try contradiction. apply IHl.
  intros; apply H3; auto. 
- (* builtin *)
  exploit S.set_list_complete. eauto. eauto. intros [e1 [A B]].
  exploit S.set_complete. eexact B. eauto. intros [e2 [C D]].
  exists e2; split; auto.
  rewrite check_successor_complete by auto; simpl. 
  rewrite A; simpl; rewrite C; auto.
- (* cond *)
  exploit S.set_list_complete. eauto. eauto. intros [e1 [A B]].
  exists e1; split; auto.
  rewrite check_successor_complete by auto; simpl. 
  rewrite check_successor_complete by auto; simpl.
  auto.
- (* jumptbl *)
  exploit S.set_complete. eauto. eauto. intros [e1 [A B]].
  exists e1; split; auto.
  replace (check_successors tbl) with (OK tt). simpl. 
  rewrite A; simpl. apply zle_true; auto. 
  revert H1. generalize tbl. induction tbl0; simpl; intros. auto. 
  rewrite check_successor_complete by auto; simpl.
  apply IHtbl0; intros; auto.
- (* return none *)
  rewrite H0. exists e; auto.
- (* return some *)
  rewrite H0. apply S.set_complete; auto.
Qed.

Lemma type_code_complete:
  forall te e,
  (forall pc instr, f.(fn_code)!pc = Some instr -> wt_instr f te instr) ->
  S.satisf te e ->
  exists e', type_code e = OK e' /\ S.satisf te e'.
Proof.
  intros te e0 WTC SAT0.
  set (P := fun c res =>
        (forall pc i, c!pc = Some i -> wt_instr f te i) ->
        exists e', res = OK e' /\ S.satisf te e').
  assert (P f.(fn_code) (type_code e0)).
  {
    unfold type_code. apply PTree_Properties.fold_rec; unfold P; intros.
    - apply H0. intros. apply H1 with pc. rewrite <- H; auto. 
    - exists e0; auto. 
    - destruct H1 as [e [A B]]. 
      intros. apply H2 with pc. rewrite PTree.gso; auto. congruence.
      subst a. 
      destruct (type_instr_complete te e v) as [e' [C D]].
      auto. apply H2 with k. apply PTree.gss. 
      exists e'; split; auto. rewrite C; auto. 
  }
  apply H; auto.
Qed.

Theorem type_function_complete:
  forall te, wt_function f te -> exists te, type_function = OK te.
Proof.
  intros. destruct H. 
  destruct (type_code_complete te S.initial) as (e1 & A & B).
  auto. apply S.satisf_initial. 
  destruct (S.set_list_complete te f.(fn_params) f.(fn_sig).(sig_args) e1) as (e2 & C & D); auto.
  destruct (S.solve_complete te e2) as (te' & E); auto.
  exists te'; unfold type_function.
  rewrite A; simpl. rewrite C; simpl. rewrite E; simpl. 
  unfold check_params_norepet. rewrite pred_dec_true; auto. simpl. 
  rewrite check_successor_complete by auto. auto. 
Qed.

End INFERENCE.

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

Lemma wt_exec_Iop:
  forall (ge: genv) env f sp op args res s rs m v,
  wt_instr f env (Iop op args res s) ->
  eval_operation ge sp op rs##args m = Some v ->
  wt_regset env rs ->
  wt_regset env (rs#res <- v).
Proof.
  intros. inv H. 
  simpl in H0. inv H0. apply wt_regset_assign; auto.
  rewrite H4; auto.
  eapply wt_regset_assign; auto.
  rewrite H8. eapply type_of_operation_sound; eauto.
Qed.

Lemma wt_exec_Iload:
  forall env f chunk addr args dst s m a v rs,
  wt_instr f env (Iload chunk addr args dst s) ->
  Mem.loadv chunk m a = Some v ->
  wt_regset env rs ->
  wt_regset env (rs#dst <- v).
Proof.
  intros. destruct a; simpl in H0; try discriminate. inv H.
  eapply wt_regset_assign; eauto. rewrite H8; eapply Mem.load_type; eauto.
Qed.

Lemma wt_exec_Ibuiltin:
  forall env f ef (ge: genv) args res s vargs m t vres m' rs,
  wt_instr f env (Ibuiltin ef args res s) ->
  external_call ef ge vargs m t vres m' ->
  wt_regset env rs ->
  wt_regset env (rs#res <- vres).
Proof.
  intros. inv H. 
  eapply wt_regset_assign; eauto. 
  rewrite H7; eapply external_call_well_typed; eauto.
Qed.

Lemma wt_instr_at:
  forall f env pc i,
  wt_function f env -> f.(fn_code)!pc = Some i -> wt_instr f env i.
Proof.
  intros. inv H. eauto. 
Qed.

Inductive wt_stackframes: list stackframe -> signature -> Prop :=
  | wt_stackframes_nil: forall sg,
      sg.(sig_res) = Some Tint ->
      wt_stackframes nil sg
  | wt_stackframes_cons:
      forall s res f sp pc rs env sg,
      wt_function f env ->
      wt_regset env rs ->
      env res = proj_sig_res sg ->
      wt_stackframes s (fn_sig f) ->
      wt_stackframes (Stackframe res f sp pc rs :: s) sg.

Inductive wt_state: state -> Prop :=
  | wt_state_intro:
      forall s f sp pc rs m env
        (WT_STK: wt_stackframes s (fn_sig f))
        (WT_FN: wt_function f env)
        (WT_RS: wt_regset env rs),
      wt_state (State s f sp pc rs m)
  | wt_state_call:
      forall s f args m,
      wt_stackframes s (funsig f) ->
      wt_fundef f ->
      Val.has_type_list args (sig_args (funsig f)) ->
      wt_state (Callstate s f args m)
  | wt_state_return:
      forall s v m sg,
      wt_stackframes s sg ->
      Val.has_type v (proj_sig_res sg) ->
      wt_state (Returnstate s v m).

Remark wt_stackframes_change_sig:
  forall s sg1 sg2,
  sg1.(sig_res) = sg2.(sig_res) -> wt_stackframes s sg1 -> wt_stackframes s sg2.
Proof.
  intros. inv H0. 
- constructor; congruence.
- econstructor; eauto. rewrite H3. unfold proj_sig_res. rewrite H. auto. 
Qed.

Section SUBJECT_REDUCTION.

Variable p: program.

Hypothesis wt_p: wt_program p.

Let ge := Genv.globalenv p.

Lemma subject_reduction:
  forall st1 t st2, step ge st1 t st2 ->
  forall (WT: wt_state st1), wt_state st2.
Proof.
  induction 1; intros; inv WT;
  try (generalize (wt_instrs _ _ WT_FN pc _ H); intros WTI).
  (* Inop *)
  econstructor; eauto.
  (* Iop *)
  econstructor; eauto. eapply wt_exec_Iop; eauto.
  (* Iload *)
  econstructor; eauto. eapply wt_exec_Iload; eauto.
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
  econstructor; eauto. inv WTI; auto. 
  inv WTI. rewrite <- H8. apply wt_regset_list. auto.
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
  inv WTI. apply wt_stackframes_change_sig with (fn_sig f); auto.
  inv WTI. rewrite <- H7. apply wt_regset_list. auto.
  (* Ibuiltin *)
  econstructor; eauto. eapply wt_exec_Ibuiltin; eauto.
  (* Icond *)
  econstructor; eauto.
  (* Ijumptable *)
  econstructor; eauto.
  (* Ireturn *)
  econstructor; eauto. 
  inv WTI; simpl. auto. unfold proj_sig_res; rewrite H2. auto. 
  (* internal function *)
  simpl in *. inv H5.
  econstructor; eauto.
  inv H1. apply wt_init_regs; auto. rewrite wt_params0. auto. 
  (* external function *)
  econstructor; eauto. simpl.  
  eapply external_call_well_typed; eauto.
  (* return *)
  inv H1. econstructor; eauto.
  apply wt_regset_assign; auto. rewrite H10; auto. 
Qed.

Lemma wt_initial_state:
  forall S, initial_state p S -> wt_state S.
Proof.
  intros. inv H. constructor. constructor. rewrite H3; auto. 
  pattern f. apply Genv.find_funct_ptr_prop with fundef unit p b.
  exact wt_p. exact H2.
  rewrite H3. constructor.
Qed.

Lemma wt_instr_inv:
  forall s f sp pc rs m i,
  wt_state (State s f sp pc rs m) ->
  f.(fn_code)!pc = Some i ->
  exists env, wt_instr f env i /\ wt_regset env rs.
Proof.
  intros. inv H. exists env; split; auto. 
  inv WT_FN. eauto. 
Qed.

End SUBJECT_REDUCTION.

  
