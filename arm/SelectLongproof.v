(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                 Xavier Leroy, INRIA Paris                           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Instruction selection for 64-bit integer operations *)

Require Import String compcert.Coqlib compcert.Maps compcert.Integers compcert.Floats compcert.Errors.
Require compcert.Archi.
Require Import compcert.AST compcert.Values compcert.Memory compcert.Globalenvs compcert.Events.
Require Import compcert.Cminor compcert.Op compcert.CminorSel.
Require Import compcert.SelectOp compcert.SelectOpproof compcert.SplitLong compcert.SplitLongproof.
Require Import compcert.SelectLong.

(** This file is empty because we use the default implementation provided in [SplitLong]. *)
