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

(* Additional extraction directives specific to the PowerPC port *)

(* Asm *)
Extract Constant Asm.low_half => "fun _ _ _ -> assert false".
Extract Constant Asm.high_half => "fun _ _ _ -> assert false".
Extract Constant Asm.symbol_is_small_data => "C2C.atom_is_small_data".
Extract Constant Asm.small_data_area_offset => "fun _ _ _ -> assert false".
Extract Constant Asm.symbol_is_rel_data => "C2C.atom_is_rel_data".

(* Suppression of stupidly big equality functions *)
Extract Constant Asm.ireg_eq => "fun (x: ireg) (y: ireg) -> x = y".
Extract Constant Asm.freg_eq => "fun (x: freg) (y: freg) -> x = y".
Extract Constant Asm.preg_eq => "fun (x: preg) (y: preg) -> x = y".

(* Choice of PPC splitlong *)
Extract Constant Archi.ppc64 =>
  "begin match Configuration.model with
   | ""ppc64"" -> true
   | ""e5500"" -> true
   | _ -> false
   end".
