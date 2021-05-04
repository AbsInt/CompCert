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

(* Additional extraction directives specific to the AArch64 port *)

Require Archi Asm Asmgen SelectOp.

(* Archi *)

Extract Constant Archi.abi =>
  "match Configuration.abi with
    | ""apple"" -> Apple
    | _ -> AAPCS64".
  
(* SelectOp *)

Extract Constant SelectOp.symbol_is_relocatable =>
  "match Configuration.system with
    | ""macos"" -> C2C.atom_is_extern
    | _ -> (fun _ -> false)".

(* Asm *)

Extract Constant Asm.symbol_low => "fun _ _ _ -> assert false".
Extract Constant Asm.symbol_high => "fun _ _ _ -> assert false".

(* Asmgen *)

Extract Constant Asmgen.symbol_is_aligned => "C2C.atom_is_aligned".
