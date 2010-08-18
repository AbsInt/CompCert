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

(** Register allocation. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Lattice.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import RTLtyping.
Require Import Kildall.
Require Import Locations.
Require Import Conventions.
Require Import Coloring.

(** * Liveness analysis over RTL *)

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
            (f: RTL.function) (pc: node) (after: Regset.t) : Regset.t :=
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

Definition analyze (f: RTL.function): option (PMap.t Regset.t) :=
  DS.fixpoint (successors f)  (transfer f) nil.

(** * Translation from RTL to LTL *)

Require Import LTL.

(** Each [RTL] instruction translates to an [LTL] instruction.
  The register assignment [assign] returned by register allocation
  is applied to the arguments and results of the RTL
  instruction.  Moreover, dead instructions and redundant moves
  are eliminated (turned into a [Lnop] instruction).
  Dead instructions are instructions without side-effects ([Iop] and
  [Iload]) whose result register is dead, i.e. whose result value
  is never used.  Redundant moves are moves whose source and destination
  are assigned the same location. *)

Definition is_redundant_move
    (op: operation) (args: list reg) (res: reg) (assign: reg -> loc) : bool :=
  match is_move_operation op args with
  | None => false
  | Some src => if Loc.eq (assign src) (assign res) then true else false
  end.

Definition transf_instr
         (f: RTL.function) (live: PMap.t Regset.t) (assign: reg -> loc)
         (pc: node) (instr: RTL.instruction) : LTL.instruction :=
  match instr with
  | Inop s =>
      Lnop s
  | Iop op args res s =>
      if Regset.mem res live!!pc then
        if is_redundant_move op args res assign then
          Lnop s
        else 
          Lop op (List.map assign args) (assign res) s
      else
        Lnop s
  | Iload chunk addr args dst s =>
      if Regset.mem dst live!!pc then
        Lload chunk addr (List.map assign args) (assign dst) s
      else
        Lnop s
  | Istore chunk addr args src s =>
      Lstore chunk addr (List.map assign args) (assign src) s
  | Icall sig ros args res s =>
      Lcall sig (sum_left_map assign ros) (List.map assign args)
                (assign res) s
  | Itailcall sig ros args =>
      Ltailcall sig (sum_left_map assign ros) (List.map assign args)
  | Ibuiltin ef args res s =>
      Lbuiltin ef (List.map assign args) (assign res) s
  | Icond cond args ifso ifnot =>
      Lcond cond (List.map assign args) ifso ifnot
  | Ijumptable arg tbl =>
      Ljumptable (assign arg) tbl
  | Ireturn optarg =>
      Lreturn (option_map assign optarg)
  end.

Definition transf_fun (f: RTL.function) (live: PMap.t Regset.t)
                      (assign: reg -> loc) : LTL.function :=
  LTL.mkfunction
     (RTL.fn_sig f)
     (List.map assign (RTL.fn_params f))
     (RTL.fn_stacksize f)
     (PTree.map (transf_instr f live assign) (RTL.fn_code f))
     (RTL.fn_entrypoint f).

(** The translation of a function performs liveness analysis,
  construction and coloring of the inference graph, and per-instruction
  transformation as described above. *)

Definition live0 (f: RTL.function) (live: PMap.t Regset.t) :=
  transfer f f.(RTL.fn_entrypoint) live!!(f.(RTL.fn_entrypoint)).

Open Scope string_scope.

Definition transf_function (f: RTL.function) : res LTL.function :=
  match type_function f with
  | Error msg => Error msg
  | OK env =>
    match analyze f with
    | None => Error (msg "Liveness analysis failure")
    | Some live =>
        match regalloc f live (live0 f live) env with
        | None => Error (msg "Incorrect graph coloring")
        | Some assign => OK (transf_fun f live assign)
        end
    end
  end.

Definition transf_fundef (fd: RTL.fundef) : res LTL.fundef :=
  AST.transf_partial_fundef transf_function fd.

Definition transf_program (p: RTL.program) : res LTL.program :=
  transform_partial_program transf_fundef p.

