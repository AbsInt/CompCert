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
  | BI_isel
  | BI_uisel
  | BI_isel64
  | BI_uisel64
  | BI_bsel
  | BI_mulhw
  | BI_mulhwu
  | BI_mulhd
  | BI_mulhdu.

Local Open Scope string_scope.

Definition platform_builtin_table : list (string * platform_builtin) :=
     ("__builtin_isel", BI_isel)
  :: ("__builtin_uisel", BI_uisel)
  :: ("__builtin_isel64", BI_isel64)
  :: ("__builtin_uisel64", BI_uisel64)
  :: ("__builtin_bsel", BI_bsel)
  :: ("__builtin_mulhw", BI_mulhw)
  :: ("__builtin_mulhwu", BI_mulhwu)
  :: ("__builtin_mulhd", BI_mulhd)
  :: ("__builtin_mulhdu", BI_mulhdu)
  :: nil.

Definition platform_builtin_sig (b: platform_builtin) : signature :=
  match b with
  | BI_isel | BI_uisel =>
     [Xint; Xint; Xint ---> Xint]
  | BI_isel64 | BI_uisel64 =>
     [Xint; Xlong; Xlong ---> Xlong]
  | BI_bsel =>
     [Xint; Xint; Xint ---> Xbool]
  | BI_mulhw | BI_mulhwu =>
     [Xint; Xint ---> Xint]
  | BI_mulhd | BI_mulhdu =>
     [Xlong; Xlong ---> Xlong]
  end.

Definition isel {A: Type} (c: int) (n1 n2: A) : A :=
  if Int.eq c Int.zero then n2 else n1.

Program Definition bsel (c n1 n2: int) : { n : int | n = Int.zero \/ n = Int.one } :=
  if  Int.eq (isel c n1 n2) Int.zero then Int.zero else Int.one.

Definition platform_builtin_sem (b: platform_builtin) : builtin_sem (sig_res (platform_builtin_sig b)) :=
  match b with
  | BI_isel | BI_uisel =>
    mkbuiltin_n3t Tint Tint Tint Xint isel
  | BI_isel64 | BI_uisel64 =>
    mkbuiltin_n3t Tint Tlong Tlong Xlong isel
  | BI_bsel =>
    mkbuiltin_n3t Tint Tint Tint Xbool bsel
  | BI_mulhw =>
    mkbuiltin_n2t Tint Tint Xint Int.mulhs
  | BI_mulhwu =>
    mkbuiltin_n2t Tint Tint Xint Int.mulhu
  | BI_mulhd =>
    mkbuiltin_n2t Tlong Tlong Xlong Int64.mulhs
  | BI_mulhdu =>
    mkbuiltin_n2t Tlong Tlong Xlong Int64.mulhu
  end.

Definition eq_platform_builtin: forall (x y: platform_builtin), {x=y} + {x<>y}.
Proof.
  decide equality.
Defined.
