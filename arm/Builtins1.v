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
| BI_idiv
| BI_uidiv.

Local Open Scope string_scope.

Definition platform_builtin_table : list (string * platform_builtin) :=
  ("__aeabi_idiv", BI_idiv) ::   ("__aeabi_uidiv", BI_uidiv) :: nil.

Definition platform_builtin_sig (b: platform_builtin) : signature :=
  match b with
  | BI_idiv | BI_uidiv => mksignature (Tint :: Tint :: nil) Tint cc_default
  end.

Definition divs (n1 n2: int) : option int :=
  if Int.eq n2 Int.zero || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone then None else Some (Int.divs n1 n2).

Remark divs_is_divs : forall n1 n2, Val.divs (Vint n1) (Vint n2) = option_map Vint (divs n1 n2).
Proof.
  unfold divs. simpl. intros.
  destruct (Int.eq n2 Int.zero || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone);reflexivity.
Qed.

Definition divu (n1 n2: int) : option int :=
  if Int.eq n2 Int.zero then None else Some (Int.divu n1 n2).

Remark divu_is_divu : forall n1 n2, Val.divu (Vint n1) (Vint n2) = option_map Vint (divu n1 n2).
Proof.
  unfold divu. simpl. intros.
  destruct (Int.eq n2 Int.zero);reflexivity.
Qed.

Definition platform_builtin_sem (b: platform_builtin) : builtin_sem (sig_res (platform_builtin_sig b)) :=
  match b with
  | BI_idiv => mkbuiltin_n2p Tint Tint (Tret Tint) divs
  | BI_uidiv => mkbuiltin_n2p Tint Tint (Tret Tint) divu
  end.
