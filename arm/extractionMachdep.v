(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Additional extraction directives specific to the ARM port *)

(* Suppression of stupidly big equality functions *)
Extract Constant Asm.ireg_eq => "fun (x: ireg) (y: ireg) -> x = y".
Extract Constant Asm.freg_eq => "fun (x: freg) (y: freg) -> x = y".
Extract Constant Asm.preg_eq => "fun (x: preg) (y: preg) -> x = y".
