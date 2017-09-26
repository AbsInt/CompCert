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

(* Processor-dependent builtin C functions *)

open C

let builtins = {
  Builtins.typedefs = [
    "__builtin_va_list", TPtr(TVoid [], [])
  ];
  Builtins.functions = [
    (* Synchronization *)
    "__builtin_fence",
      (TVoid [], [], false);
    (* Integer arithmetic *)
    "__builtin_bswap64",
      (TInt(IULongLong, []), [TInt(IULongLong, [])], false);
    (* Float arithmetic *)
    "__builtin_fmadd",
      (TFloat(FDouble, []),
       [TFloat(FDouble, []); TFloat(FDouble, []); TFloat(FDouble, [])],
       false);
    "__builtin_fmsub",
      (TFloat(FDouble, []),
       [TFloat(FDouble, []); TFloat(FDouble, []); TFloat(FDouble, [])],
       false);
    "__builtin_fnmadd",
      (TFloat(FDouble, []),
       [TFloat(FDouble, []); TFloat(FDouble, []); TFloat(FDouble, [])],
       false);
    "__builtin_fnmsub",
      (TFloat(FDouble, []),
       [TFloat(FDouble, []); TFloat(FDouble, []); TFloat(FDouble, [])],
       false);
    "__builtin_fmax",
      (TFloat(FDouble, []), [TFloat(FDouble, []); TFloat(FDouble, [])], false);
    "__builtin_fmin",
      (TFloat(FDouble, []), [TFloat(FDouble, []); TFloat(FDouble, [])], false);
  ]
}

let va_list_type = TPtr(TVoid [], [])  (* to check! *)
let size_va_list = if Archi.ptr64 then 8 else 4
let va_list_scalar = true

(* Expand memory references inside extended asm statements.  Used in C2C. *)

let asm_mem_argument arg = Printf.sprintf "0(%s)" arg
