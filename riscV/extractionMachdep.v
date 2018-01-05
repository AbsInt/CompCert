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

(* Additional extraction directives specific to the RISC-V port *)

Require Archi Asm.

(* Archi *)

Extract Constant Archi.ptr64 => " Configuration.model = ""64"" ".
Extract Constant Archi.pic_code => "fun () -> false".  (* for the time being *)

(* Asm *)
Extract Constant Asm.low_half => "fun _ _ _ -> assert false".
Extract Constant Asm.high_half => "fun _ _ _ -> assert false".
