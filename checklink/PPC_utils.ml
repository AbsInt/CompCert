open ELF_types
open ELF_utils
open Library
open PPC_parsers
open PPC_types

let code_at_vaddr (e: elf)(vaddr: int32)(nb_instr: int): ecode option =
  begin match bitstring_at_vaddr e vaddr (Safe32.of_int (4 * nb_instr)) with
  | None -> None
  | Some(code_bs, _, _) -> Some (parse_code_as_list code_bs)
  end

let code_of_sym (e: elf) (sym: elf32_sym): ecode option =
  begin match bitstring_at_vaddr e sym.st_value sym.st_size with
  | None -> None
  | Some(bs, _, _) -> Some(parse_code_as_list bs)
  end

let code_of_sym_ndx (e: elf) (ndx: int): ecode option =
  code_of_sym e e.e_symtab.(ndx)

let code_of_sym_name (e: elf) (name: string): ecode option =
  begin match ndx_of_sym_name e name with
  | Some ndx -> code_of_sym_ndx e ndx
  | None     -> None
  end
