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

Require Import String Coqlib.
Require Import AST Integers Floats Values.
Require Import Builtins0.

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
     mksignature (Tint :: Tint :: Tint :: nil) Tint cc_default
  | BI_isel64 | BI_uisel64 =>
     mksignature (Tint :: Tlong :: Tlong :: nil) Tlong cc_default
  | BI_bsel =>
     mksignature (Tint :: Tint :: Tint :: nil) Tint8unsigned cc_default
  | BI_mulhw | BI_mulhwu =>
     mksignature (Tint :: Tint :: nil) Tint cc_default
  | BI_mulhd | BI_mulhdu =>
     mksignature (Tlong :: Tlong :: nil) Tlong cc_default
  end.

Definition isel {A: Type} (c: int) (n1 n2: A) : A :=
  if Int.eq c Int.zero then n2 else n1.

Program Definition bsel (c n1 n2: int) : { n : int | n = Int.zero_ext 8 n } :=
  Int.zero_ext 8 (isel c n1 n2).
Next Obligation.
  symmetry. apply Int.zero_ext_idem. lia.
Qed.

Definition platform_builtin_sem (b: platform_builtin) : builtin_sem (sig_res (platform_builtin_sig b)) :=
  match b with
  | BI_isel | BI_uisel =>
    mkbuiltin_n3t Tint Tint Tint Tint isel
  | BI_isel64 | BI_uisel64 =>
    mkbuiltin_n3t Tint Tlong Tlong Tlong isel
  | BI_bsel =>
    mkbuiltin_n3t Tint Tint Tint Tint8unsigned bsel
  | BI_mulhw =>
    mkbuiltin_n2t Tint Tint Tint Int.mulhs
  | BI_mulhwu =>
    mkbuiltin_n2t Tint Tint Tint Int.mulhu
  | BI_mulhd =>
    mkbuiltin_n2t Tlong Tlong Tlong Int64.mulhs
  | BI_mulhdu =>
    mkbuiltin_n2t Tlong Tlong Tlong Int64.mulhu
  end.
