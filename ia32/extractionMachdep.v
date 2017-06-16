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

(* Additional extraction directives specific to the IA32 port *)

Require SelectOp.

(* SelectOp *)

Extract Constant SelectOp.symbol_is_external =>
  "fun id -> Configuration.system = ""macosx"" && C2C.atom_is_extern id".
