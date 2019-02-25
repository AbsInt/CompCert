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
  struct_return_style : struct_return_style;
}

let ilp32ll64 = {
  name = "ilp32ll64";
  char_signed = false;
  sizeof_ptr = 4;
  sizeof_short = 2;
  sizeof_int = 4;
  sizeof_long = 4;
  sizeof_longlong = 8;
  sizeof_float = 4;
  sizeof_double = 8;
  sizeof_longdouble = 8;
  sizeof_void = None;
  sizeof_fun = None;
  sizeof_wchar = 4;
  wchar_signed = true;
  sizeof_size_t = 4;
  sizeof_ptrdiff_t = 4;
  sizeof_intreg = 4;
  alignof_ptr = 4;
  alignof_short = 2;
  alignof_int = 4;
  alignof_long = 4;
  alignof_longlong = 8;
  alignof_float = 4;
  alignof_double = 8;
  alignof_longdouble = 8;
  alignof_void = None;
  alignof_fun = None;
  bigendian = false;
  bitfields_msb_first = false;
  supports_unaligned_accesses = false;
  struct_passing_style = SP_ref_callee;
  struct_return_style = SR_ref;
}

let i32lpll64 = {
  name = "i32lpll64";
  char_signed = false;
  sizeof_ptr = 8;
  sizeof_short = 2;
  sizeof_int = 4;
  sizeof_long = 8;
  sizeof_longlong = 8;
  sizeof_float = 4;
  sizeof_double = 8;
  sizeof_longdouble = 8;
  sizeof_void = None;
  sizeof_fun = None;
  sizeof_wchar = 4;
  wchar_signed = true;
  sizeof_size_t = 8;
  sizeof_ptrdiff_t = 8;
  sizeof_intreg = 8;
  alignof_ptr = 8;
  alignof_short = 2;
  alignof_int = 4;
  alignof_long = 8;
  alignof_longlong = 8;
  alignof_float = 4;
  alignof_double = 8;
  alignof_longdouble = 8;
  alignof_void = None;
  alignof_fun = None;
  bigendian = false;
  bitfields_msb_first = false;
  supports_unaligned_accesses = false;
  struct_passing_style = SP_ref_callee;
  struct_return_style = SR_ref;
}

let il32pll64 = {
  name = "il32pll64";
  char_signed = false;
  sizeof_ptr = 8;
  sizeof_short = 2;
  sizeof_int = 4;
  sizeof_long = 4;
  sizeof_longlong = 8;
  sizeof_float = 4;
  sizeof_double = 8;
  sizeof_longdouble = 8;
  sizeof_void = None;
  sizeof_fun = None;
  sizeof_wchar = 4;
  wchar_signed = true;
  sizeof_size_t = 8;
  sizeof_ptrdiff_t = 8;
  sizeof_intreg = 8;
  alignof_ptr = 8;
  alignof_short = 2;
  alignof_int = 4;
  alignof_long = 4;
  alignof_longlong = 8;
  alignof_float = 4;
  alignof_double = 8;
  alignof_longdouble = 8;
  alignof_void = None;
  alignof_fun = None;
  bigendian = false;
  bitfields_msb_first = false;
  supports_unaligned_accesses = false;
  struct_passing_style = SP_ref_callee;
  struct_return_style = SR_ref;
}

(* Canned configurations for some ABIs *)

let x86_32 =
  { ilp32ll64 with name = "x86_32";
                   char_signed = true;
                   alignof_longlong = 4; alignof_double = 4;
                   alignof_longdouble = 4;
                   supports_unaligned_accesses = true;
                   struct_passing_style = SP_split_args;
                   struct_return_style = SR_ref}

let x86_32_macosx =
  {x86_32 with struct_passing_style = SP_split_args;
               struct_return_style = SR_int1248 }

let x86_32_bsd =
  x86_32_macosx

let x86_64 =
  { i32lpll64 with name = "x86_64"; char_signed = true;
                   struct_passing_style = SP_ref_callee; (* wrong *)
                   struct_return_style = SR_ref } (* to check *)

let win32 =
  { ilp32ll64 with name = "win32"; char_signed = true;
                   sizeof_wchar = 2; wchar_signed = false;
                   struct_passing_style = SP_split_args;
                   struct_return_style = SR_ref }
let win64 =
  { il32pll64 with name = "win64"; char_signed = true;
                   sizeof_wchar = 2; wchar_signed = false }
let ppc_32_bigendian =
  { ilp32ll64 with name = "powerpc";
                   bigendian = true;
                   bitfields_msb_first = true;
                   supports_unaligned_accesses = true;
                   struct_passing_style = SP_ref_caller;
                   struct_return_style =  SR_int1to8; }

let ppc_32_r64_bigendian =
  { ppc_32_bigendian with sizeof_intreg = 8;}

let ppc_32_diab_bigendian =
  { ppc_32_bigendian with sizeof_wchar = 2; wchar_signed = false }

let ppc_32_r64_diab_bigendian =
  { ppc_32_diab_bigendian with sizeof_intreg = 8;}

let ppc_32_linux_bigendian = {ppc_32_bigendian with struct_return_style = SR_ref;}

let ppc_32_r64_linux_bigendian =
  { ppc_32_linux_bigendian with sizeof_intreg = 8;}

let arm_littleendian =
  { ilp32ll64 with name = "arm"; struct_passing_style = SP_split_args;
                   struct_return_style = SR_int1to4;}

let arm_bigendian =
  { arm_littleendian with bigendian = true;
                          bitfields_msb_first = true }

let rv32 =
  { ilp32ll64 with name = "rv32";
                   struct_passing_style = SP_ref_callee; (* Wrong *)
                   struct_return_style = SR_ref } (* to check *)
let rv64 =
  { i32lpll64 with name = "rv64";
                   struct_passing_style = SP_ref_callee; (* Wrong *)
                   struct_return_style = SR_ref } (* to check *)

(* Add GCC extensions re: sizeof and alignof *)

let gcc_extensions c =
  { c with sizeof_void = Some 1; sizeof_fun = Some 1;
           alignof_void = Some 1; alignof_fun = Some 1 }

(* Normalize configuration for use with the CompCert reference interpreter *)

let compcert_interpreter c =
  { c with supports_unaligned_accesses = false }

(* Undefined configuration *)

let undef = {
  name = "UNDEFINED";
  char_signed = false;
  sizeof_ptr = 0;
  sizeof_short = 0;
  sizeof_int = 0;
  sizeof_long = 0;
  sizeof_longlong = 0;
  sizeof_float = 0;
  sizeof_double = 0;
  sizeof_longdouble = 0;
  sizeof_void = None;
  sizeof_fun = None;
  sizeof_wchar = 0;
  wchar_signed = true;
  sizeof_size_t = 0;
  sizeof_ptrdiff_t = 0;
  sizeof_intreg = 0;
  alignof_ptr = 0;
  alignof_short = 0;
  alignof_int = 0;
  alignof_long = 0;
  alignof_longlong = 0;
  alignof_float = 0;
  alignof_double = 0;
  alignof_longdouble = 0;
  alignof_void = None;
  alignof_fun = None;
  bigendian = false;
  bitfields_msb_first = false;
  supports_unaligned_accesses = false;
  struct_passing_style = SP_ref_callee;
  struct_return_style = SR_ref;
}

(* The current configuration.  Must be initialized before use. *)

let config = ref undef
