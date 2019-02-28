(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open AST
open Camlcoq
open DwarfPrinter
open PrintAsmaux
open Printf
open Sections
open TargetPrinter
open AisAnnot

module Printer(Target:TARGET) =
  struct

    let get_fun_addr name txt =
      let s = new_label ()
      and e = new_label () in
      Debug.add_fun_addr name txt (e,s);
      s,e

    let print_debug_label oc l =
      if !Clflags.option_g then
        fprintf oc "%a:\n" Target.label l
      else
        ()

    let print_location oc loc =
      if loc <> Cutil.no_loc then Target.print_file_line oc (fst loc) (snd loc)

    let print_function oc name fn =
      Hashtbl.clear current_function_labels;
      let (text, lit, jmptbl) = Target.get_section_names name in
      Target.section oc text;
      let alignment =
        match !Clflags.option_falignfunctions with Some n -> n | None -> Target.default_falignment in
      Target.print_align oc alignment;
      if not (C2C.atom_is_static name) then
        fprintf oc "	.globl %a\n" Target.symbol name;
      Target.print_optional_fun_info oc;
      let s,e = if !Clflags.option_g then
        get_fun_addr name text
      else
        -1,-1 in
      print_debug_label oc s;
      fprintf oc "%a:\n" Target.symbol name;
      print_location oc (C2C.atom_location name);
      Target.cfi_startproc oc;
      Target.print_instructions oc fn;
      Target.cfi_endproc oc;
      print_debug_label oc e;
      Target.print_fun_info oc name;
      Target.emit_constants oc lit;
      Target.print_jumptable oc jmptbl;
      if !Clflags.option_g then
        Hashtbl.iter (fun p i -> Debug.add_label name p i) current_function_labels

    let print_init oc init =
      let symbol_offset oc (symb,ofs) =
        Target.symbol oc symb;
        let ofs = camlint64_of_ptrofs ofs in
        if ofs <> 0L then fprintf oc " + %Ld" ofs in
      let splitlong b =
        let b = camlint64_of_coqint b in
        if Archi.big_endian then
          (Int64.shift_right_logical b 32),
          (Int64.logand b 0xFFFFFFFFL)
        else
          (Int64.logand b 0xFFFFFFFFL),
          (Int64.shift_right_logical b 32) in
      match init with
      | Init_int8 n ->
          fprintf oc "	.byte	%ld\n" (camlint_of_coqint n)
      | Init_int16 n ->
      fprintf oc "	.short	%ld\n" (camlint_of_coqint n)
      | Init_int32 n ->
          fprintf oc "	.long	%ld\n" (camlint_of_coqint n)
      | Init_int64 n ->
          let hi,lo = splitlong n in
          fprintf oc "	.long	0x%Lx, 0x%Lx\n" hi lo
      | Init_float32 n ->
          fprintf oc "	.long	0x%lx %s %.18g\n"
            (camlint_of_coqint (Floats.Float32.to_bits n))
            Target.comment (camlfloat_of_coqfloat32 n)
      | Init_float64 n ->
          let hi,lo = splitlong (Floats.Float.to_bits n) in
          fprintf oc "	.long	0x%Lx, 0x%Lx %s %.18g\n" hi lo
            Target.comment (camlfloat_of_coqfloat n)
      | Init_space n ->
          if Z.gt n Z.zero then
            fprintf oc "	.space	%s\n" (Z.to_string n)
      | Init_addrof(symb, ofs) ->
        fprintf oc "	%s	%a\n"
          Target.address
          symbol_offset (symb, ofs)


    let print_init_data oc name id =
      if Str.string_match PrintCsyntax.re_string_literal (extern_atom name) 0
          && List.for_all (function Init_int8 _ -> true | _ -> false) id
      then
        fprintf oc "	.ascii	\"%s\"\n" (PrintCsyntax.string_of_init id)
      else
        List.iter (print_init oc) id

    let print_var oc name v =
      match v.gvar_init with
      | [] -> ()
      | _  ->
          Debug.variable_printed (extern_atom name);
          let sec =
            match C2C.atom_sections name with
            | [s] -> s
            |  _  -> Section_data true
          and align =
            match C2C.atom_alignof name with
            | Some a -> a
            | None -> 8 in (* 8-alignment is a safe default *)
          let name_sec = Target.name_of_section sec in
          if name_sec <> "COMM" then begin
            fprintf oc "	%s\n" name_sec;
            Target.print_align oc align;
            if not (C2C.atom_is_static name) then
              fprintf oc "	.globl	%a\n" Target.symbol name;
            fprintf oc "%a:\n" Target.symbol name;
            print_init_data oc name v.gvar_init;
            Target.print_var_info oc name;
          end else
            let sz =
              match v.gvar_init with [Init_space sz] -> sz | _ -> assert false in
            Target.print_comm_symb oc sz name align

    let print_globdef oc (name,gdef) =
      match gdef with
      | Gfun (Internal code) ->
        if not (C2C.atom_is_iso_inline_definition name) then
          print_function oc name code
      | Gfun (External ef) ->   ()
      | Gvar v -> print_var oc name v

    let print_ais_annot oc =
      let annots = get_ais_annots () in
      if annots <> [] then begin
        Target.section oc Section_ais_annotation;
        let print_addr oc pp_addr addr =
          fprintf oc "	.byte 7,%d\n" (if Archi.ptr64 then 8 else 4);
          fprintf oc "	%s %a\n" Target.address pp_addr addr in
        let annot_part oc = function
          | AisAnnot.Label lbl  ->
            print_addr oc Target.label lbl
          | AisAnnot.Symbol symb ->
            print_addr oc Target.symbol symb
          | AisAnnot.String a -> fprintf oc "	.ascii %S\n" a in
        let annot oc str =
          List.iter (annot_part oc) str
        in
        List.iter (annot oc) annots
      end

    module DwarfTarget: DwarfTypes.DWARF_TARGET =
      struct
        let label = Target.label
        let section = Target.section
        let symbol = Target.symbol
        let comment = Target.comment
        let address = Target.address
      end

    module DebugPrinter = DwarfPrinter (DwarfTarget)
  end

let print_program oc p =
  let module Target = (val (sel_target ()):TARGET) in
  let module Printer = Printer(Target) in
  Fileinfo.reset_filenames ();
  print_version_and_options oc Target.comment;
  Target.print_prologue oc;
  List.iter (Printer.print_globdef oc) p.prog_defs;
  Target.print_epilogue oc;
  Printer.print_ais_annot oc;
  if !Clflags.option_g then
    begin
      let atom_to_s s =
        let s = C2C.atom_sections s in
        match s with
        | [] -> Target.name_of_section Section_text
        | (Section_user (n,_,_))::_ -> n
        | a::_ ->
            Target.name_of_section a in
      match Debug.generate_debug_info atom_to_s (Target.name_of_section Section_text) with
      | None -> ()
      | Some db ->
          Printer.DebugPrinter.print_debug oc db
    end;
  Fileinfo.close_filenames ()
