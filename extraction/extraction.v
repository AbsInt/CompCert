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

Require List.
Require Iteration.
Require Floats.
Require RTLgen.
Require Coloring.
Require Allocation.
Require Compiler.

(* Standard lib *)
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive List.list => "list" [ "[]" "(::)" ].

(* Float *)
Extract Inlined Constant Floats.float => "float".
Extract Constant Floats.Float.zero   => "0.".
Extract Constant Floats.Float.one   => "1.".
Extract Constant Floats.Float.neg => "( ~-. )".
Extract Constant Floats.Float.abs => "abs_float".
Extract Constant Floats.Float.singleoffloat => "Floataux.singleoffloat".
Extract Constant Floats.Float.intoffloat => "Floataux.intoffloat".
Extract Constant Floats.Float.intuoffloat => "Floataux.intuoffloat".
Extract Constant Floats.Float.floatofint => "Floataux.floatofint".
Extract Constant Floats.Float.floatofintu => "Floataux.floatofintu".
Extract Constant Floats.Float.add => "( +. )".
Extract Constant Floats.Float.sub => "( -. )".
Extract Constant Floats.Float.mul => "( *. )".
Extract Constant Floats.Float.div => "( /. )".
Extract Constant Floats.Float.cmp => "Floataux.cmp".
Extract Constant Floats.Float.eq_dec => "fun (x: float) (y: float) -> x = y".
Extract Constant Floats.Float.bits_of_double => "Floataux.bits_of_double".
Extract Constant Floats.Float.double_of_bits => "Floataux.double_of_bits".
Extract Constant Floats.Float.bits_of_single => "Floataux.bits_of_single".
Extract Constant Floats.Float.single_of_bits => "Floataux.single_of_bits".

(* Memdata *)
Extract Constant Memdata.big_endian => "Memdataaux.big_endian".

(* Memory - work around an extraction bug. *)
Extraction NoInline Memory.Mem.valid_pointer.

(* Iteration *)
Extract Constant Iteration.dependent_description' =>
  "fun x -> assert false".

Extract Constant Iteration.GenIter.iterate =>
  "let rec iter f a =
     match f a with Coq_inl b -> Some b | Coq_inr a' -> iter f a'
   in iter".

(* RTLgen *)
Extract Constant RTLgen.compile_switch => "RTLgenaux.compile_switch".
Extract Constant RTLgen.more_likely => "RTLgenaux.more_likely".

(* RTLtyping *)
Extract Constant RTLtyping.infer_type_environment => "RTLtypingaux.infer_type_environment".

(* Coloring *)
Extract Constant Coloring.graph_coloring => "Coloringaux.graph_coloring".

(* Linearize *)
Extract Constant Linearize.enumerate_aux => "Linearizeaux.enumerate_aux".

(* Compiler *)
Extract Constant Compiler.print_Csyntax => "PrintCsyntax.print_if".
Extract Constant Compiler.print_Clight => "PrintClight.print_if".
Extract Constant Compiler.print_Cminor => "PrintCminor.print_if".
Extract Constant Compiler.print_RTL => "PrintRTL.print_rtl".
Extract Constant Compiler.print_RTL_tailcall => "PrintRTL.print_tailcall".
Extract Constant Compiler.print_RTL_castopt => "PrintRTL.print_castopt".
Extract Constant Compiler.print_RTL_constprop => "PrintRTL.print_constprop".
Extract Constant Compiler.print_RTL_cse => "PrintRTL.print_cse".
Extract Constant Compiler.print_LTLin => "PrintLTLin.print_if".

(* Suppression of stupidly big equality functions *)
Extract Constant Op.eq_operation => "fun (x: operation) (y: operation) -> x = y".
Extract Constant Op.eq_addressing => "fun (x: addressing) (y: addressing) -> x = y".
(*Extract Constant CSE.eq_rhs => "fun (x: rhs) (y: rhs) -> x = y".*)
Extract Constant Machregs.mreg_eq => "fun (x: mreg) (y: mreg) -> x = y".

(* Processor-specific extraction directives *)

Load extractionMachdep.

(* Avoid name clashes *)
Extraction Blacklist List String Int.

(* Go! *)
Cd "extraction".
Recursive Extraction Library Compiler.
