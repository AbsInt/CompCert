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
    (* Integer arithmetic *)
    "__builtin_clz",
      (TInt(IInt, []), [TInt(IUInt, [])], false);
    "__builtin_clzl",
      (TInt(IInt, []), [TInt(IULong, [])], false);
    "__builtin_clzll",
      (TInt(IInt, []), [TInt(IULongLong, [])], false);
    "__builtin_ctz",
      (TInt(IInt, []), [TInt(IUInt, [])], false);
    "__builtin_ctzl",
      (TInt(IInt, []), [TInt(IULong, [])], false);
    "__builtin_ctzll",
      (TInt(IInt, []), [TInt(IULongLong, [])], false);
    (* Memory accesses *)
    "__builtin_read16_reversed",
      (TInt(IUShort, []), [TPtr(TInt(IUShort, [AConst]), [])], false);
    "__builtin_read32_reversed",
      (TInt(IUInt, []), [TPtr(TInt(IUInt, [AConst]), [])], false);
    "__builtin_write16_reversed",
      (TVoid [], [TPtr(TInt(IUShort, []), []); TInt(IUShort, [])], false);
    "__builtin_write32_reversed",
      (TVoid [], [TPtr(TInt(IUInt, []), []); TInt(IUInt, [])], false);
    (* Synchronization *)
    "__builtin_dmb",
      (TVoid [], [], false);
    "__builtin_dsb",
      (TVoid [], [], false);
    "__builtin_isb",
      (TVoid [], [], false)
  ]
}

let size_va_list = 4
let va_list_scalar = true

(* Expand memory references inside extended asm statements.  Used in C2C. *)

let asm_mem_argument arg = Printf.sprintf "[%s, #0]" arg
