(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

open DwarfTypes

module DwarfPrinter: functor (Target: DWARF_TARGET) -> functor (DwarfAbbrevs: DWARF_ABBREVS) ->
  sig
    val print_debug: out_channel -> dw_entry -> dw_locations -> unit
  end
