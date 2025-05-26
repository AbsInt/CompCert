(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
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

(* Additional extraction directives specific to the x86-64 port *)

Require Archi SelectOp.

(* Archi *)

Extract Constant Archi.win64 =>
  "match Configuration.system with
    | ""cygwin"" when ptr64 -> true
    | _ -> false".

(* SelectOp *)

Extract Constant SelectOp.symbol_is_relocatable =>
  "match Configuration.system with
    | ""macos"" -> C2C.atom_is_external
    | ""cygwin"" -> if Archi.ptr64 then C2C.atom_is_external else (fun _ -> false)
    | _ -> C2C.atom_needs_GOT_access".
