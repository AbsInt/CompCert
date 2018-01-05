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

(* Additional extraction directives specific to the ARM port *)

(* Suppression of stupidly big equality functions *)
Extract Constant Asm.ireg_eq => "fun (x: ireg) (y: ireg) -> x = y".
Extract Constant Asm.freg_eq => "fun (x: freg) (y: freg) -> x = y".
Extract Constant Asm.preg_eq => "fun (x: preg) (y: preg) -> x = y".

(* Choice of calling conventions *)
Extract Constant Archi.abi =>
  "begin match Configuration.abi with
   | ""eabi"" -> Softfloat
   | ""hardfloat"" -> Hardfloat
   | _ -> assert false
   end".

(* Choice of endianness *)
Extract Constant Archi.big_endian =>
  "Configuration.is_big_endian".

(* Whether the model is ARMv6T2 or above and hence supports Thumb2. *)
Extract Constant Archi.thumb2_support =>
  "(Configuration.model = ""armv6t2"" || Configuration.model >= ""armv7"")".
