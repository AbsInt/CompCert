(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Xavier Leroy, Collège de France and INRIA Paris             *)
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

(* Processor-dependent builtin C functions *)

open C

(* AAPCS64:
     va_list is a struct of size 32 and alignment 8, passed by reference
   Apple:
     va_list is a pointer (size 8, alignment 8), passed by reference *)

let (va_list_type, size_va_list, va_list_scalar) =
  match Archi.abi with
  | Archi.AAPCS64 -> (TArray(TInt(IULong, []), Some 4L, []), 32, false)
  | Archi.Apple   -> (TPtr(TVoid [], []), 8, true)

(* Some macOS headers use the GCC built-in types "__int128_t" and
   "__uint128_t" unconditionally.  Provide a dummy definition. *)

let int128_type = TArray(TInt(IULong, []), Some 2L, [])

let builtins = {
  builtin_typedefs =
  [ "__builtin_va_list", va_list_type ] @
  (if Configuration.system = "macos" then
  [ "__int128_t", int128_type;
    "__uint128_t", int128_type ]
  else []);
  builtin_functions = [
    (* Synchronization *)
    "__builtin_fence",
      (TVoid [], [], false);
    (* Integer arithmetic *)
    "__builtin_cls",
      (TInt(IInt, []), [TInt(IInt, [])], false);
    "__builtin_clsl",
      (TInt(IInt, []), [TInt(ILong, [])], false);
    "__builtin_clsll",
      (TInt(IInt, []), [TInt(ILongLong, [])], false);
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

(* Expand memory references inside extended asm statements.  Used in C2C. *)

let asm_mem_argument arg = Printf.sprintf "[%s]" arg
