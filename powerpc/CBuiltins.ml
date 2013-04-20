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
  Builtins.typedefs = [];
  Builtins.functions = [
    (* Integer arithmetic *)
    "__builtin_mulhw",
      (TInt(IInt, []), [TInt(IInt, []); TInt(IInt, [])], false);
    "__builtin_mulhwu",
      (TInt(IUInt, []), [TInt(IUInt, []); TInt(IUInt, [])], false);
    "__builtin_cntlz",
      (TInt(IUInt, []), [TInt(IUInt, [])], false);
    "__builtin_bswap",
      (TInt(IUInt, []), [TInt(IUInt, [])], false);
    "__builtin_bswap32",
      (TInt(IUInt, []), [TInt(IUInt, [])], false);
    "__builtin_bswap16",
      (TInt(IUShort, []), [TInt(IUShort, [])], false);
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
    "__builtin_fsqrt",
      (TFloat(FDouble, []), [TFloat(FDouble, [])], false);
    "__builtin_frsqrte",
      (TFloat(FDouble, []), [TFloat(FDouble, [])], false);
    "__builtin_fres",
      (TFloat(FFloat, []), [TFloat(FFloat, [])], false);
    "__builtin_fsel",
      (TFloat(FDouble, []), 
       [TFloat(FDouble, []); TFloat(FDouble, []); TFloat(FDouble, [])],
       false);
    "__builtin_fcti",
      (TInt(IInt, []),
       [TFloat(FDouble, [])],
       false);
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
    "__builtin_eieio",
      (TVoid [], [], false);
    "__builtin_sync",
      (TVoid [], [], false);
    "__builtin_isync",
      (TVoid [], [], false);
    "__builtin_trap",
      (TVoid [], [], false)
  ]
}
