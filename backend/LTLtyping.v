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

(** Type-checking LTL code, adapted with tiny changes from [Lineartyping]. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Memory.
Require Import Events.
Require Import Op.
Require Import Machregs.
Require Import Locations.
Require Import Conventions.
Require Import LTL.

(** The rules are presented as boolean-valued functions so that we
  get an executable type-checker for free. *)

Section WT_INSTR.

Variable funct: function.

Definition slot_valid (sl: slot) (ofs: Z) (ty: typ): bool :=
  match sl with
  | Local => zle 0 ofs
  | Outgoing => zle 0 ofs
  | Incoming => In_dec Loc.eq (S Incoming ofs ty) (regs_of_rpairs (loc_parameters funct.(fn_sig)))
  end
  && Zdivide_dec (typealign ty) ofs (typealign_pos ty).

Definition slot_writable (sl: slot) : bool :=
  match sl with
  | Local => true
  | Outgoing => true
  | Incoming => false
  end.

Definition loc_valid (l: loc) : bool :=
  match l with
  | R r => true
  | S Local ofs ty => slot_valid Local ofs ty
  | S _ _ _ => false
  end.

Definition wt_builtin_res (ty: typ) (res: builtin_res mreg) : bool :=
  match res with
  | BR r => subtype ty (mreg_type r)
  | BR_none => true
  | BR_splitlong hi lo => subtype Tint (mreg_type hi) && subtype Tint (mreg_type lo)
  end.

Definition wt_instr (i: instruction) : bool :=
  match i with
  | Lgetstack sl ofs ty r =>
      subtype ty (mreg_type r) && slot_valid sl ofs ty
  | Lsetstack r sl ofs ty =>
      slot_valid sl ofs ty && slot_writable sl
  | Lop op args res =>
      match is_move_operation op args with
      | Some arg =>
          subtype (mreg_type arg) (mreg_type res)
      | None =>
          let (targs, tres) := type_of_operation op in
          subtype tres (mreg_type res)
      end
  | Lload chunk addr args dst =>
      subtype (type_of_chunk chunk) (mreg_type dst)
  | Ltailcall sg ros =>
      zeq (size_arguments sg) 0
  | Lbuiltin ef args res =>
      wt_builtin_res (proj_sig_res (ef_sig ef)) res
      && forallb loc_valid (params_of_builtin_args args)
  | _ =>
      true
  end.

End WT_INSTR.

Definition wt_bblock (f: function) (b: bblock) : bool :=
  forallb (wt_instr f) b.

Definition wt_function (f: function) : bool :=
  let bs := map snd (Maps.PTree.elements f.(fn_code)) in
  forallb (wt_bblock f) bs.

Lemma wt_function_wt_bblock:
  forall f pc b,
  wt_function f = true ->
  Maps.PTree.get pc (fn_code f) = Some b ->
  wt_bblock f b = true.
Proof.
  intros. apply Maps.PTree.elements_correct in H0.
  unfold wt_function, wt_bblock in *. eapply forallb_forall in H; eauto.
  change b with (snd (pc, b)). apply in_map; auto.
Qed.

(** Typing the run-time state. *)

Definition wt_locset (ls: locset) : Prop :=
  forall l, Val.has_type (ls @ l) (Loc.type l).

Lemma well_typed_locset:
  forall ls, wt_locset ls.
Proof.
  unfold wt_locset, Locmap.get, Locmap.chunk_of_loc. intros.
  set (chunk := chunk_of_type (Loc.type l)).
  rewrite <- type_of_chunk_of_type.
  apply decode_val_type.
Qed.

(** Soundness of the type system *)

Definition wt_fundef (fd: fundef) :=
  match fd with
  | Internal f => wt_function f = true
  | External ef => True
  end.

Definition wt_program (prog: program): Prop :=
  forall i fd, In (i, Gfun fd) prog.(prog_defs) -> wt_fundef fd.

Inductive wt_callstack: list stackframe -> Prop :=
  | wt_callstack_nil:
      wt_callstack nil
  | wt_callstack_cons: forall f sp rs b s
        (WTSTK: wt_callstack s)
        (WTF: wt_function f = true)
        (WTB: wt_bblock f b = true),
      wt_callstack (Stackframe f sp rs b :: s).

Inductive wt_state: state -> Prop :=
  | wt_branch_state: forall s f sp n rs m
        (WTSTK: wt_callstack s )
        (WTF: wt_function f = true),
      wt_state (State s f sp n rs m)
  | wt_regular_state: forall s f sp b rs m
        (WTSTK: wt_callstack s )
        (WTF: wt_function f = true)
        (WTB: wt_bblock f b = true),
      wt_state (Block s f sp b rs m)
  | wt_call_state: forall s fd rs m
        (WTSTK: wt_callstack s)
        (WTFD: wt_fundef fd),
      wt_state (Callstate s fd rs m)
  | wt_return_state: forall s rs m
        (WTSTK: wt_callstack s),
      wt_state (Returnstate s rs m).

(** Preservation of state typing by transitions *)

Section SOUNDNESS.

Variable prog: program.
Let ge := Genv.globalenv prog.

Hypothesis wt_prog: wt_program prog.

Lemma wt_find_function:
  forall ros rs f, find_function ge ros rs = Some f -> wt_fundef f.
Proof.
  intros.
  assert (X: exists i, In (i, Gfun f) prog.(prog_defs)).
  {
    destruct ros as [r | s]; simpl in H.
    eapply Genv.find_funct_inversion; eauto.
    destruct (Genv.find_symbol ge s) as [b|]; try discriminate.
    eapply Genv.find_funct_ptr_inversion; eauto.
  }
  destruct X as [i IN]. eapply wt_prog; eauto.
Qed.

Theorem step_type_preservation:
  forall S1 t S2, step ge S1 t S2 -> wt_state S1 -> wt_state S2.
Proof.
Local Opaque mreg_type.
  induction 1; intros WTS; inv WTS.
- (* startblock *)
  econstructor; eauto.
  apply Maps.PTree.elements_correct in H.
  unfold wt_function in WTF. eapply forallb_forall in WTF; eauto.
  change bb with (snd (pc, bb)). apply in_map; auto.
- (* op *)
  simpl in *. destruct (is_move_operation op args) as [src | ] eqn:ISMOVE.
  + (* move *)
    InvBooleans. exploit is_move_operation_correct; eauto. intros [EQ1 EQ2]; subst.
    simpl in H. inv H.
    econstructor; eauto.
  + (* other ops *)
    destruct (type_of_operation op) as [ty_args ty_res] eqn:TYOP. InvBooleans.
    econstructor; eauto.
- (* load *)
  simpl in *; InvBooleans.
  econstructor; eauto.
- (* getstack *)
  simpl in *; InvBooleans.
  econstructor; eauto.
- (* setstack *)
  simpl in *; InvBooleans.
  econstructor; eauto.
- (* store *)
  simpl in *; InvBooleans.
  econstructor. eauto. eauto. eauto.
- (* call *)
  simpl in *; InvBooleans.
  econstructor; eauto. econstructor; eauto.
  eapply wt_find_function; eauto.
- (* tailcall *)
  simpl in *; InvBooleans.
  econstructor; eauto.
  eapply wt_find_function; eauto.
- (* builtin *)
  simpl in *; InvBooleans.
  econstructor; eauto.
- (* branch *)
  simpl in *. econstructor; eauto.
- (* cond branch *)
  simpl in *. econstructor; auto.
- (* jumptable *)
  simpl in *. econstructor; auto.
- (* return *)
  simpl in *. InvBooleans.
  econstructor; eauto.
- (* internal function *)
  simpl in WTFD.
  econstructor. eauto. eauto.
- (* external function *)
  econstructor. auto.
- (* return *)
  inv WTSTK. econstructor; eauto.
Qed.

Theorem wt_initial_state:
  forall S, initial_state prog S -> wt_state S.
Proof.
  induction 1. econstructor. constructor.
  unfold ge0 in H1. exploit Genv.find_funct_ptr_inversion; eauto.
  intros [id IN]. eapply wt_prog; eauto.
Qed.

End SOUNDNESS.

(** Properties of well-typed states that are used in [Allocproof]. *)

Lemma wt_state_getstack:
  forall s f sp sl ofs ty rd c rs m,
  wt_state (Block s f sp (Lgetstack sl ofs ty rd :: c) rs m) ->
  slot_valid f sl ofs ty = true.
Proof.
  intros. inv H. simpl in WTB; InvBooleans. auto.
Qed.

Lemma wt_state_setstack:
  forall s f sp sl ofs ty r c rs m,
  wt_state (Block s f sp (Lsetstack r sl ofs ty :: c) rs m) ->
  slot_valid f sl ofs ty = true /\ slot_writable sl = true.
Proof.
  intros. inv H. simpl in WTB; InvBooleans. intuition.
Qed.

Lemma wt_state_tailcall:
  forall s f sp sg ros c rs m,
  wt_state (Block s f sp (Ltailcall sg ros :: c) rs m) ->
  size_arguments sg = 0.
Proof.
  intros. inv H. simpl in WTB; InvBooleans. auto.
Qed.

Lemma wt_state_builtin:
  forall s f sp ef args res c rs m,
  wt_state (Block s f sp (Lbuiltin ef args res :: c) rs m) ->
  forallb (loc_valid f) (params_of_builtin_args args) = true.
Proof.
  intros. inv H. simpl in WTB; InvBooleans. auto.
Qed.

Lemma wt_callstate_wt_regs:
  forall s f rs m,
  wt_state (Callstate s f rs m) ->
  forall r, Val.has_type (rs @ (R r)) (mreg_type r).
Proof.
  intros. apply well_typed_locset.
Qed.
