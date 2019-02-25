(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Machine-dependent aspects *)
type struct_passing_style =
  | SP_ref_callee                       (* by reference, callee takes copy *)
  | SP_ref_caller                       (* by reference, caller takes copy *)
  | SP_split_args                       (* by value, as a sequence of ints *)

type struct_return_style =
  | SR_int1248      (* return by content if size is 1, 2, 4 or 8 bytes *)
  | SR_int1to4      (* return by content if size is <= 4 *)
  | SR_int1to8      (* return by content if size is <= 8 *)
  | SR_ref          (* always return by assignment to a reference
                       given as extra argument *)

type t = {
  name: string;
  char_signed: bool;
  sizeof_ptr: int;
  sizeof_short: int;
  sizeof_int: int;
  sizeof_long: int;
  sizeof_longlong: int;
  sizeof_float: int;
  sizeof_double: int;
  sizeof_longdouble: int;
  sizeof_void: int option;
  sizeof_fun: int option;
  sizeof_wchar: int;
  wchar_signed: bool;
  sizeof_size_t: int;
  sizeof_ptrdiff_t: int;
  sizeof_intreg: int;
  alignof_ptr: int;
  alignof_short: int;
  alignof_int: int;
  alignof_long: int;
  alignof_longlong: int;
  alignof_float: int;
  alignof_double: int;
  alignof_longdouble: int;
  alignof_void: int option;
  alignof_fun: int option;
  bigendian: bool;
  bitfields_msb_first: bool;
  supports_unaligned_accesses: bool;
  struct_passing_style: struct_passing_style;
  struct_return_style: struct_return_style;
}

(* The current configuration *)

val config : t ref

(* Canned configurations *)

val ilp32ll64 : t
val i32lpll64 : t
val il32pll64 : t
val x86_32 : t
val x86_32_macosx : t
val x86_32_bsd : t
val x86_64 : t
val win32 : t
val win64 : t
val ppc_32_bigendian : t
val ppc_32_diab_bigendian : t
val ppc_32_linux_bigendian : t
val ppc_32_r64_bigendian : t
val ppc_32_r64_diab_bigendian : t
val ppc_32_r64_linux_bigendian : t
val arm_littleendian : t
val arm_bigendian : t
val rv32 : t
val rv64 : t

val gcc_extensions : t -> t
val compcert_interpreter : t -> t
