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
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import RTLtyping.
Require Import Liveness.
Require Import Locations.
Require Import LTL.
Require Import Coloring.

(** * Translation from RTL to LTL *)

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

