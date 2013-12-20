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

(** Liveness analysis over RTL *)

Require Import Coqlib.
Require Import Maps.
Require Import Lattice.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Kildall.

(** A register [r] is live at a point [p] if there exists a path
  from [p] to some instruction that uses [r] as argument,
  and [r] is not redefined along this path.
  Liveness can be computed by a backward dataflow analysis.
  The analysis operates over sets of (live) pseudo-registers. *)

Notation reg_live := Regset.add.
Notation reg_dead := Regset.remove.

Definition reg_option_live (or: option reg) (lv: Regset.t) :=
  match or with None => lv | Some r => reg_live r lv end.

Definition reg_sum_live (ros: reg + ident) (lv: Regset.t) :=
  match ros with inl r => reg_live r lv | inr s => lv end.

Fixpoint reg_list_live
             (rl: list reg) (lv: Regset.t) {struct rl} : Regset.t :=
  match rl with
  | nil => lv
  | r1 :: rs => reg_list_live rs (reg_live r1 lv)
  end.

Fixpoint reg_list_dead
             (rl: list reg) (lv: Regset.t) {struct rl} : Regset.t :=
  match rl with
  | nil => lv
  | r1 :: rs => reg_list_dead rs (reg_dead r1 lv)
  end.

(** Here is the transfer function for the dataflow analysis.
  Since this is a backward dataflow analysis, it takes as argument
  the abstract register set ``after'' the given instruction,
  i.e. the registers that are live after; and it returns as result
  the abstract register set ``before'' the given instruction,
  i.e. the registers that must be live before.
  The general relation between ``live before'' and ``live after''
  an instruction is that a register is live before if either
  it is one of the arguments of the instruction, or it is not the result
  of the instruction and it is live after.
  However, if the result of a side-effect-free instruction is not 
  live ``after'', the whole instruction will be removed later
  (since it computes a useless result), thus its arguments need not
  be live ``before''. *)

Definition transfer
            (f: function) (pc: node) (after: Regset.t) : Regset.t :=
  match f.(fn_code)!pc with
  | None =>
      Regset.empty
  | Some i =>
      match i with
      | Inop s =>
          after
      | Iop op args res s =>
          if Regset.mem res after then
            reg_list_live args (reg_dead res after)
          else
            after
      | Iload chunk addr args dst s =>
          if Regset.mem dst after then
            reg_list_live args (reg_dead dst after)
          else
            after
      | Istore chunk addr args src s =>
          reg_list_live args (reg_live src after)
      | Icall sig ros args res s =>
          reg_list_live args
           (reg_sum_live ros (reg_dead res after))
      | Itailcall sig ros args =>
          reg_list_live args (reg_sum_live ros Regset.empty)
      | Ibuiltin ef args res s =>
          reg_list_live args (reg_dead res after)
      | Icond cond args ifso ifnot =>
          reg_list_live args after
      | Ijumptable arg tbl =>
          reg_live arg after
      | Ireturn optarg =>
          reg_option_live optarg Regset.empty
      end
  end.

(** The liveness analysis is then obtained by instantiating the
  general framework for backward dataflow analysis provided by
  module [Kildall].  *)

Module RegsetLat := LFSet(Regset).
Module DS := Backward_Dataflow_Solver(RegsetLat)(NodeSetBackward).

Definition analyze (f: function): option (PMap.t Regset.t) :=
  DS.fixpoint f.(fn_code) successors_instr (transfer f).

(** Basic property of the liveness information computed by [analyze]. *)

Lemma analyze_solution:
  forall f live n i s,
  analyze f = Some live ->
  f.(fn_code)!n = Some i ->
  In s (successors_instr i) ->
  Regset.Subset (transfer f s live!!s) live!!n.
Proof.
  unfold analyze; intros. eapply DS.fixpoint_solution; eauto. 
  intros. unfold transfer; rewrite H2. apply DS.L.eq_refl. 
Qed.

(** Given an RTL function, compute (for every PC) the list of 
  pseudo-registers that are used for the last time in the instruction
  at PC.  These are the registers that are used or defined by the instruction
  and dead afterwards.  *)

Definition last_uses_at (live: PMap.t Regset.t) (pc: node) (i: instruction) : list reg :=
  let l := live!!pc in
  let lu := List.filter (fun r => negb (Regset.mem r l)) (instr_uses i) in
  match instr_defs i with
  | None => lu
  | Some r => if Regset.mem r l then lu else r :: lu
  end.

Definition last_uses (f: function) : PTree.t (list reg) :=
  match analyze f with
  | None => PTree.empty (list reg)
  | Some live => PTree.map (last_uses_at live) f.(fn_code)
  end.

      
