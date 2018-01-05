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

(* Additional extraction directives specific to the x86-64 port *)

Require SelectOp ConstpropOp.

(* SelectOp *)

Extract Constant SelectOp.symbol_is_external =>
  "fun id -> Configuration.system = ""macosx"" && C2C.atom_is_extern id".

(* ConstpropOp *)

Extract Constant ConstpropOp.symbol_is_external =>
  "fun id -> Configuration.system = ""macosx"" && C2C.atom_is_extern id".

