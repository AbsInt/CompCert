open ELF_types
open ELF_utils
open Library
open PPC_parsers
open PPC_types

let code_at_vaddr (e: elf) (vaddr: int32) (nb_instr: int): ecode option =
  match section_at_vaddr e vaddr with
  | None -> None
  | Some(sndx) ->
      let code_bs =
        bitstring_at_vaddr e sndx vaddr (32 * nb_instr) in
      Some (parse_code_as_list code_bs)

let code_of_sym_ndx (e: elf) (ndx: int): ecode option =
  let sym = e.e_symtab.(ndx) in
  match sym.st_type with
  | STT_FUNC ->
      let sym_vaddr = sym.st_value in
      let sym_size = 8 * (int32_int sym.st_size) in
      let sym_sndx = sym.st_shndx in
      let code_bs =
        bitstring_at_vaddr e sym_sndx sym_vaddr sym_size in
      Some (parse_code_as_list code_bs)
  | _ -> None

let code_of_sym_name (e: elf) (name: string): ecode option =
  match ndx_of_sym_name e name with
  | Some ndx -> code_of_sym_ndx e ndx
  | None     -> None

      
