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
    "__builtin_va_list",
    TArray(TInt(IUInt, []), Some 3L, [])
  ];
  Builtins.functions = [
    (* Integer arithmetic *)
    "__builtin_mulhw",
      (TInt(IInt, []), [TInt(IInt, []); TInt(IInt, [])], false);
    "__builtin_mulhwu",
      (TInt(IUInt, []), [TInt(IUInt, []); TInt(IUInt, [])], false);
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
    "__builtin_cmpb",
      (TInt (IUInt, []),  [TInt(IUInt, []);TInt(IUInt, [])], false);
    (* Integer arithmetic in 32/64-bit hybrid mode *)
    "__builtin_mulhd",
      (TInt(ILongLong, []), [TInt(ILongLong, []); TInt(ILongLong, [])], false);
    "__builtin_mulhdu",
      (TInt(IULongLong, []), [TInt(IULongLong, []); TInt(IULongLong, [])], false);
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
    (* Memory accesses in 32/64-bit hybrid mode *)
    "__builtin_read64_reversed",
      (TInt(IULongLong, []), [TPtr(TInt(IULongLong, [AConst]), [])], false);
    "__builtin_write64_reversed",
      (TVoid [], [TPtr(TInt(IULongLong, []), []); TInt(IULongLong, [])], false);
    (* Synchronization *)
    "__builtin_eieio",
      (TVoid [], [], false);
    "__builtin_sync",
      (TVoid [], [], false);
    "__builtin_isync",
      (TVoid [], [], false);
    "__builtin_lwsync",
      (TVoid [], [], false);
    "__builtin_mbar",
      (TVoid [], [TInt(IInt, [])], false);
    "__builtin_trap",
      (TVoid [], [], false);
    (* Cache instructions *)
    "__builtin_dcbf",
      (TVoid [],[TPtr(TVoid [], [])],false);
    "__builtin_dcbi",
      (TVoid [],[TPtr(TVoid [], [])],false);
    "__builtin_icbi",
      (TVoid [],[TPtr(TVoid [], [])],false);
    "__builtin_prefetch",
      (TVoid [], [TPtr (TVoid [],[]);TInt (IInt, []);TInt (IInt,[])],false);
    "__builtin_dcbtls",
      (TVoid[], [TPtr (TVoid [],[]);TInt (IInt,[])],false);
    "__builtin_icbtls",
      (TVoid[], [TPtr (TVoid [],[]);TInt (IInt,[])],false);
    "__builtin_dcbz",
      (TVoid[], [TPtr (TVoid [],[])],false);
    (* Access to special registers *)
    "__builtin_get_spr",
      (TInt(IUInt, []), [TInt(IInt, [])], false);
    "__builtin_set_spr",
      (TVoid [], [TInt(IInt, []); TInt(IUInt, [])], false);
    (* Access to special registers in 32/64-bit hybrid mode *)
    "__builtin_get_spr64",
      (TInt(IULongLong, []), [TInt(IInt, [])], false);
    "__builtin_set_spr64",
      (TVoid [], [TInt(IInt, []); TInt(IULongLong, [])], false);
    (* Move register *)
    "__builtin_mr",
      (TVoid [], [TInt(IInt, []); TInt(IInt, [])], false);
    (* Frame and return address *)
    "__builtin_call_frame",
      (TPtr (TVoid [],[]),[],false);
    "__builtin_return_address",
      (TPtr (TVoid [],[]),[],false);
    (* isel *)
    "__builtin_isel",
      (TInt (IInt, []),[TInt(IBool, []);TInt(IInt, []);TInt(IInt, [])],false);
    (* uisel *)
    "__builtin_uisel",
      (TInt (IUInt, []),[TInt(IBool, []);TInt(IUInt, []);TInt(IUInt, [])],false);
    (* isel64 *)
    "__builtin_isel64",
      (TInt (ILongLong, []),[TInt(IBool, []);TInt(ILongLong, []);TInt(ILongLong, [])],false);
    (* uisel *)
    "__builtin_uisel64",
      (TInt (IULongLong, []),[TInt(IBool, []);TInt(IULongLong, []);TInt(IULongLong, [])],false);
    (* bsel *)
    "__builtin_bsel",
      (TInt (IBool, []),[TInt(IBool, []);TInt(IBool, []);TInt(IBool, [])],false);
    (* no operation *)
    "__builtin_nop",
      (TVoid [], [], false);
    (* Atomic operations *)
    "__builtin_atomic_exchange",
      (TVoid [], [TPtr (TInt(IInt, []),[]);TPtr (TInt(IInt, []),[]);TPtr (TInt(IInt, []),[])],false);
    "__builtin_atomic_load",
      (TVoid [], [TPtr (TInt(IInt, []),[]);TPtr (TInt(IInt, []),[])],false);
    "__builtin_atomic_compare_exchange",
      (TInt (IBool, []), [TPtr (TInt(IInt, []),[]);TPtr (TInt(IInt, []),[]);TPtr (TInt(IInt, []),[])],false);
    "__builtin_sync_fetch_and_add",
      (TInt (IInt, []),  [TPtr (TInt(IInt, []),[]);TInt(IInt, [])],false);
  ]
}

let size_va_list = 12
let va_list_scalar = false

(* Expand memory references inside extended asm statements.  Used in C2C. *)

let asm_mem_argument arg = Printf.sprintf "0(%s)" arg
