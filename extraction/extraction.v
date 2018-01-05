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

Require Coqlib.
Require Wfsimpl.
Require DecidableClass Decidableplus.
Require AST.
Require Iteration.
Require Floats.
Require SelectLong.
Require Selection.
Require RTLgen.
Require Inlining.
Require ValueDomain.
Require Tailcall.
Require Allocation.
Require Bounds.
Require Ctypes.
Require Csyntax.
Require Ctyping.
Require Clight.
Require Compiler.
Require Parser.
Require Initializers.
Require Int31.

(* Standard lib *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(* Coqlib *)
Extract Inlined Constant Coqlib.proj_sumbool => "(fun x -> x)".

(* Datatypes *)
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

(* Decidable *)

Extraction Inline DecidableClass.Decidable_witness DecidableClass.decide
   Decidableplus.Decidable_and Decidableplus.Decidable_or
   Decidableplus.Decidable_not Decidableplus.Decidable_implies.

(* Wfsimpl *)
Extraction Inline Wfsimpl.Fix Wfsimpl.Fixm.

(* Memory - work around an extraction bug. *)
Extraction NoInline Memory.Mem.valid_pointer.

(* Errors *)
Extraction Inline Errors.bind Errors.bind2.

(* Iteration *)

Extract Constant Iteration.GenIter.iterate =>
  "let rec iter f a =
     match f a with Coq_inl b -> Some b | Coq_inr a' -> iter f a'
   in iter".

(* Selection *)

Extract Constant Selection.compile_switch => "Switchaux.compile_switch".

(* RTLgen *)
Extract Constant RTLgen.more_likely => "RTLgenaux.more_likely".
Extraction Inline RTLgen.ret RTLgen.error RTLgen.bind RTLgen.bind2.

(* Inlining *)
Extract Inlined Constant Inlining.should_inline => "Inliningaux.should_inline".
Extract Inlined Constant Inlining.inlining_info => "Inliningaux.inlining_info".
Extract Inlined Constant Inlining.inlining_analysis => "Inliningaux.inlining_analysis".
Extraction Inline Inlining.ret Inlining.bind.

(* Allocation *)
Extract Constant Allocation.regalloc => "Regalloc.regalloc".

(* Linearize *)
Extract Constant Linearize.enumerate_aux => "Linearizeaux.enumerate_aux".

(* SimplExpr *)
Extract Constant SimplExpr.first_unused_ident => "Camlcoq.first_unused_ident".
Extraction Inline SimplExpr.ret SimplExpr.error SimplExpr.bind SimplExpr.bind2.

(* Compopts *)
Extract Constant Compopts.optim_for_size =>
  "fun _ -> !Clflags.option_Osize".
Extract Constant Compopts.va_strict =>
  "fun _ -> false".
Extract Constant Compopts.propagate_float_constants =>
  "fun _ -> !Clflags.option_ffloatconstprop >= 1".
Extract Constant Compopts.generate_float_constants =>
  "fun _ -> !Clflags.option_ffloatconstprop >= 2".
Extract Constant Compopts.optim_tailcalls =>
  "fun _ -> !Clflags.option_ftailcalls".
Extract Constant Compopts.optim_constprop =>
  "fun _ -> !Clflags.option_fconstprop".
Extract Constant Compopts.optim_CSE =>
  "fun _ -> !Clflags.option_fcse".
Extract Constant Compopts.optim_redundancy =>
  "fun _ -> !Clflags.option_fredundancy".
Extract Constant Compopts.thumb =>
  "fun _ -> !Clflags.option_mthumb".
Extract Constant Compopts.debug =>
  "fun _ -> !Clflags.option_g".

(* Compiler *)
Extract Constant Compiler.print_Clight => "PrintClight.print_if".
Extract Constant Compiler.print_Cminor => "PrintCminor.print_if".
Extract Constant Compiler.print_RTL => "PrintRTL.print_if".
Extract Constant Compiler.print_LTL => "PrintLTL.print_if".
Extract Constant Compiler.print_Mach => "PrintMach.print_if".
Extract Constant Compiler.print => "fun (f: 'a -> unit) (x: 'a) -> f x; x".
Extract Constant Compiler.time  => "Timing.time_coq".

(*Extraction Inline Compiler.apply_total Compiler.apply_partial.*)

(* Cabs *)
Extract Constant Cabs.cabsloc =>
"{ lineno : int;
   filename: string;
   byteno: int;
   ident : int;
 }".
Extract Inlined Constant Cabs.string => "String.t".
Extract Constant Cabs.char_code => "int64".

(* Int31 *)
Extract Inductive Int31.digits => "bool" [ "false" "true" ].
Extract Inductive Int31.int31 => "int" [ "Camlcoq.Int31.constr" ] "Camlcoq.Int31.destr".
Extract Constant Int31.twice => "Camlcoq.Int31.twice".
Extract Constant Int31.twice_plus_one => "Camlcoq.Int31.twice_plus_one".
Extract Constant Int31.compare31 => "Camlcoq.Int31.compare".
Extract Constant Int31.On => "0".
Extract Constant Int31.In => "1".

(* Processor-specific extraction directives *)

Load extractionMachdep.

(* Avoid name clashes *)
Extraction Blacklist List String Int.

(* Cutting the dependency to R. *)
Extract Inlined Constant Fcore_defs.F2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.FF2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.B2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.round_mode => "fun _ -> assert false".
Extract Inlined Constant Fcalc_bracket.inbetween_loc => "fun _ -> assert false".

(* Needed in Coq 8.4 to avoid problems with Function definitions. *)
Set Extraction AccessOpaque.

(* Go! *)

Cd "extraction".

Separate Extraction
   Compiler.transf_c_program Compiler.transf_cminor_program
   Cexec.do_initial_state Cexec.do_step Cexec.at_final_state
   Ctypes.merge_attributes Ctypes.remove_attributes Ctypes.build_composite_env
   Initializers.transl_init Initializers.constval
   Csyntax.Eindex Csyntax.Epreincr
   Ctyping.typecheck_program
   Ctyping.epostincr Ctyping.epostdecr Ctyping.epreincr Ctyping.epredecr
   Ctypes.make_program
   Clight.type_of_function
   Conventions1.callee_save_type Conventions1.is_float_reg
   Conventions1.int_caller_save_regs Conventions1.float_caller_save_regs
   Conventions1.int_callee_save_regs Conventions1.float_callee_save_regs
   Conventions1.dummy_int_reg Conventions1.dummy_float_reg
   RTL.instr_defs RTL.instr_uses
   Machregs.mregs_for_operation Machregs.mregs_for_builtin
   Machregs.two_address_op Machregs.is_stack_reg
   Machregs.destroyed_at_indirect_call
   AST.signature_main
   Floats.Float32.from_parsed Floats.Float.from_parsed
   Globalenvs.Senv.invert_symbol
   Parser.translation_unit_file.
