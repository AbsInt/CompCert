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
    "__builtin_bswap",
      (TInt(IUInt, []), [TInt(IUInt, [])], false);
    "__builtin_bswap32",
      (TInt(IUInt, []), [TInt(IUInt, [])], false);
    "__builtin_bswap16",
      (TInt(IUShort, []), [TInt(IUShort, [])], false);
    "__builtin_cntlz",
      (TInt(IUInt, []), [TInt(IUInt, [])], false);
    (* Float arithmetic *)
    "__builtin_fsqrt",
      (TFloat(FDouble, []), [TFloat(FDouble, [])], false);
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
      (TVoid [], [], false);
    "__builtin_ldrex",
      (TInt(IUInt, []), [TPtr(TInt(IUInt, [AConst]), [])], false);
    "__builtin_ldrexb",
      (TInt(IUChar, []), [TPtr(TInt(IUChar, [AConst]), [])], false);
    "__builtin_ldrexh",
      (TInt(IUShort, []), [TPtr(TInt(IUShort, [AConst]), [])], false);
    "__builtin_ldrexd",
      (TInt(IULongLong, []), [TPtr(TInt(IULongLong, [AConst]), [])], false);
    "__builtin_strex",
      (TInt(IInt, []), [TPtr(TInt(IUInt, [AConst]), []); TInt(IUInt, [])], false);
    "__builtin_strexb",
      (TInt(IInt, []), [TPtr(TInt(IUChar, [AConst]), []); TInt(IUChar, [])], false);
    "__builtin_strexh",
      (TInt(IInt, []), [TPtr(TInt(IUShort, [AConst]), []); TInt(IUShort, [])], false);
    "__builtin_strexd",
      (TInt(IInt, []), [TPtr(TInt(IULongLong, [AConst]), []); TInt(IULongLong, [])], false);
  ]
}

let size_va_list = 4
let va_list_scalar = true
