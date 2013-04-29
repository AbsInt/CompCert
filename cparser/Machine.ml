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
  sizeof_size_t: int;
  sizeof_ptrdiff_t: int;
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
  bitfields_msb_first: bool
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
  sizeof_longdouble = 16;
  sizeof_void = None;
  sizeof_fun = None;
  sizeof_wchar = 4;
  sizeof_size_t = 4;
  sizeof_ptrdiff_t = 4;
  alignof_ptr = 4;
  alignof_short = 2;
  alignof_int = 4;
  alignof_long = 4;
  alignof_longlong = 8;
  alignof_float = 4;
  alignof_double = 8;
  alignof_longdouble = 16;
  alignof_void = None;
  alignof_fun = None;
  bigendian = false;
  bitfields_msb_first = false
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
  sizeof_longdouble = 16;
  sizeof_void = None;
  sizeof_fun = None;
  sizeof_wchar = 4;
  sizeof_size_t = 8;
  sizeof_ptrdiff_t = 8;
  alignof_ptr = 8;
  alignof_short = 2;
  alignof_int = 4;
  alignof_long = 8;
  alignof_longlong = 8;
  alignof_float = 4;
  alignof_double = 8;
  alignof_longdouble = 16;
  alignof_void = None;
  alignof_fun = None;
  bigendian = false;
  bitfields_msb_first = false
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
  sizeof_longdouble = 16;
  sizeof_void = None;
  sizeof_fun = None;
  sizeof_wchar = 4;
  sizeof_size_t = 8;
  sizeof_ptrdiff_t = 8;
  alignof_ptr = 8;
  alignof_short = 2;
  alignof_int = 4;
  alignof_long = 4;
  alignof_longlong = 8;
  alignof_float = 4;
  alignof_double = 8;
  alignof_longdouble = 16;
  alignof_void = None;
  alignof_fun = None;
  bigendian = false;
  bitfields_msb_first = false
}

(* Canned configurations for some ABIs *)

let x86_32 =
  { ilp32ll64 with char_signed = true; name = "x86_32" }
let x86_64 =
  { i32lpll64 with char_signed = true; name = "x86_64" }
let win64 =
  { il32pll64 with char_signed = true; name = "x86_64" }
let ppc_32_bigendian =
  { ilp32ll64 with bigendian = true; bitfields_msb_first = true; name = "powerpc" }
let arm_littleendian = { ilp32ll64 with name = "arm" }

(* Add GCC extensions re: sizeof and alignof *)

let gcc_extensions c =
  { c with sizeof_void = Some 1; sizeof_fun = Some 1;
           alignof_void = Some 1; alignof_fun = Some 1 }

(* Default configuration *)

let config =
  ref (match Sys.word_size with
           | 32 -> ilp32ll64
           | 64 -> if Sys.os_type = "Win32" then il32pll64 else i32lpll64
           | _  -> assert false)
