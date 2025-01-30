(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria Paris            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Platform-specific built-in functions *)

From Coq Require Import String.
Require Import Coqlib AST Integers Floats Values.
Require Import Builtins0.
Local Open Scope asttyp_scope.

Inductive platform_builtin : Type :=
  | BI_fmin
  | BI_fmax.

Local Open Scope string_scope.

Definition platform_builtin_table : list (string * platform_builtin) :=
     ("__builtin_fmin", BI_fmin)
  :: ("__builtin_fmax", BI_fmax)
  :: nil.

Definition platform_builtin_sig (b: platform_builtin) : signature :=
  match b with
  | BI_fmin | BI_fmax => [Xfloat; Xfloat ---> Xfloat]
  end.

Definition platform_builtin_sem (b: platform_builtin) : builtin_sem (sig_res (platform_builtin_sig b)) :=
  match b with
  | BI_fmin =>
      mkbuiltin_n2t Tfloat Tfloat Xfloat
        (fun f1 f2 => match Float.compare f1 f2 with
                      | Some Lt => f1
                      | Some Eq | Some Gt | None => f2
                      end)
  | BI_fmax =>
      mkbuiltin_n2t Tfloat Tfloat Xfloat
        (fun f1 f2 => match Float.compare f1 f2 with
                      | Some Gt => f1
                      | Some Eq | Some Lt | None => f2
                      end)
  end.

Definition eq_platform_builtin: forall (x y: platform_builtin), {x=y} + {x<>y}.
Proof.
  decide equality.
Defined.
