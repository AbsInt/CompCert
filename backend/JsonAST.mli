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



val pp_mnemonics : Format.formatter -> string list -> unit
val pp_ast : out_channel -> (out_channel  -> Asm.code -> unit) -> (Asm.coq_function AST.fundef, 'a) AST.program  -> string -> unit
