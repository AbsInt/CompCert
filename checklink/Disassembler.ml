open ELF_parsers
open ELF_types
open PPC_printers
open PPC_utils

let disassemble elf sym_name =
  let sym =
    List.find
      (fun sym -> sym.st_name = sym_name)
      (Array.to_list elf.e_symtab)
  in
  match code_of_sym elf sym with
  | None -> "Couldn't find the code for that symbol name"
  | Some(ecode) ->
      string_of_instr_list ecode
