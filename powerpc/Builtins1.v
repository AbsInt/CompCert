(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria Paris            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Platform-specific built-in functions *)

Require Import String Coqlib.
Require Import AST Integers Floats Values.
Require Import Builtins0.

Inductive platform_builtin : Type := .

Local Open Scope string_scope.

Definition platform_builtin_table : list (string * platform_builtin) :=
  nil.

Definition platform_builtin_sig (b: platform_builtin) : signature :=
  match b with end.

Definition platform_builtin_sem (b: platform_builtin) : builtin_sem (sig_res (platform_builtin_sig b)) :=
  match b with end.
