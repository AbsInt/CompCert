open ELF_types
open Library

let string_of_elf32_half    = string_of_int
let string_of_elf32_addr    = string_of_int32
let string_of_elf32_off     = string_of_int32
let string_of_elf32_word    = string_of_int32

let string_of_elfclass = function
| ELFCLASSNONE    -> "ELFCLASSNONE"
| ELFCLASS32      -> "ELFCLASS32"
| ELFCLASS64      -> "ELFCLASS64"
| ELFCLASSUNKNOWN -> "ELFCLASSUNKNOWN"

let string_of_elfdata = function
| ELFDATANONE    -> "ELFDATANONE"
| ELFDATA2LSB    -> "ELFDATA2LSB"
| ELFDATA2MSB    -> "ELFDATA2MSB"
| ELFDATAUNKNOWN -> "ELFDATAUNKNOWN"

let string_of_ev = function
| EV_NONE    -> "EV_NONE"
| EV_CURRENT -> "EV_CURRENT"
| EV_UNKNOWN -> "EV_UNKNOWN"

let string_of_elf_identification ei =
  "{\nei_class   = " ^ string_of_elfclass ei.ei_class ^
  ";\nei_data    = " ^ string_of_elfdata ei.ei_data ^
  ";\nei_version = " ^ string_of_ev ei.ei_version ^
  ";\n}"

let string_of_et = function
| ET_NONE    -> "ET_NONE"
| ET_REL     -> "ET_REL"
| ET_EXEC    -> "ET_EXEC"
| ET_DYN     -> "ET_DYN"
| ET_CORE    -> "ET_CORE"
| ET_UNKNOWN -> "ET_UNKNOWN"

let string_of_em = function
| EM_NONE        -> "EM_NONE"
| EM_M32         -> "EM_M32"
| EM_SPARC       -> "EM_SPARC"
| EM_386         -> "EM_386"
| EM_68K         -> "EM_68K"
| EM_88K         -> "EM_88K"
| EM_860         -> "EM_860"
| EM_MIPS        -> "EM_MIPS"
| EM_MIPS_RS4_BE -> "EM_MIPS_RS4_BE"
| EM_PPC         -> "EM_PPC"
| EM_UNKNOWN     -> "EM_UNKNOWN"

let string_of_elf32_ehdr eh =
  "{\ne_ident     = " ^ string_of_elf_identification  eh.e_ident      ^
  ";\ne_type      = " ^ string_of_et                  eh.e_type       ^
  ";\ne_machine   = " ^ string_of_em                  eh.e_machine    ^
  ";\ne_version   = " ^ string_of_ev                  eh.e_version    ^
  ";\ne_entry     = " ^ string_of_elf32_addr          eh.e_entry      ^
  ";\ne_phoff     = " ^ string_of_elf32_off           eh.e_phoff      ^
  ";\ne_shoff     = " ^ string_of_elf32_off           eh.e_shoff      ^
  ";\ne_flags     = " ^ string_of_bitstring           eh.e_flags      ^
  ";\ne_ehsize    = " ^ string_of_elf32_half          eh.e_ehsize     ^
  ";\ne_phentsize = " ^ string_of_elf32_half          eh.e_phentsize  ^
  ";\ne_phnum     = " ^ string_of_elf32_half          eh.e_phnum      ^
  ";\ne_shentsize = " ^ string_of_elf32_half          eh.e_shentsize  ^
  ";\ne_shnum     = " ^ string_of_elf32_half          eh.e_shnum      ^
  ";\ne_shstrndx  = " ^ string_of_elf32_half          eh.e_shstrndx   ^
  ";\n}"

let string_of_sht = function
| SHT_NULL     -> "SHT_NULL"
| SHT_PROGBITS -> "SHT_PROGBITS"
| SHT_SYMTAB   -> "SHT_SYMTAB"
| SHT_STRTAB   -> "SHT_STRTAB"
| SHT_RELA     -> "SHT_RELA"
| SHT_HASH     -> "SHT_HASH"
| SHT_DYNAMIC  -> "SHT_DYNAMIC"
| SHT_NOTE     -> "SHT_NOTE"
| SHT_NOBITS   -> "SHT_NOBITS"
| SHT_REL      -> "SHT_REL"
| SHT_SHLIB    -> "SHT_SHLIB"
| SHT_DYNSYM   -> "SHT_DYNSYM"
| SHT_UNKNOWN  -> "SHT_UNKNOWN"

let string_of_elf32_shdr sh =
  "{\nsh_name      = " ^ sh.sh_name ^
  ";\nsh_type      = " ^ string_of_sht         sh.sh_type      ^
  ";\nsh_flags     = " ^ string_of_elf32_word  sh.sh_flags     ^
  ";\nsh_addr      = " ^ string_of_elf32_addr  sh.sh_addr      ^
  ";\nsh_offset    = " ^ string_of_elf32_off   sh.sh_offset    ^
  ";\nsh_size      = " ^ string_of_elf32_word  sh.sh_size      ^
  ";\nsh_link      = " ^ string_of_elf32_word  sh.sh_link      ^
  ";\nsh_info      = " ^ string_of_elf32_word  sh.sh_info      ^
  ";\nsh_addralign = " ^ string_of_elf32_word  sh.sh_addralign ^
  ";\nsh_entsize   = " ^ string_of_elf32_word  sh.sh_entsize   ^
  ";\n}"

let string_of_p_type = function
| PT_NULL    -> "PT_NULL"
| PT_LOAD    -> "PT_LOAD"
| PT_DYNAMIC -> "PT_DYNAMIC"
| PT_INTERP  -> "PT_INTERP"
| PT_NOTE    -> "PT_NOTE"
| PT_SHLIB   -> "PT_SHLIB"
| PT_PHDR    -> "PT_PHDR"
| PT_UNKNOWN -> "PT_UNKNOWN"

let string_of_elf32_phdr ph =
  "{\np_type   = " ^ string_of_p_type      ph.p_type   ^
  ";\np_offset = " ^ string_of_elf32_off   ph.p_offset ^
  ";\np_vaddr  = " ^ string_of_elf32_addr  ph.p_vaddr  ^
  ";\np_paddr  = " ^ string_of_elf32_addr  ph.p_paddr  ^
  ";\np_filesz = " ^ string_of_elf32_word  ph.p_filesz ^
  ";\np_memsz  = " ^ string_of_elf32_word  ph.p_memsz  ^
  ";\np_flags  = " ^ string_of_bitstring   ph.p_flags  ^
  ";\np_align  = " ^ string_of_elf32_word  ph.p_align  ^
  ";\n}"

let string_of_elf32_st_bind = function
| STB_LOCAL   -> "STB_LOCAL"
| STB_GLOBAL  -> "STB_GLOBAL"
| STB_WEAK    -> "STB_WEAK"
| STB_UNKNOWN -> "STB_UNKNOWN"

let string_of_elf32_st_type = function
| STT_NOTYPE  -> "STT_NOTYPE"
| STT_OBJECT  -> "STT_OBJECT"
| STT_FUNC    -> "STT_FUNC"
| STT_SECTION -> "STT_SECTION"
| STT_FILE    -> "STT_FILE"
| STT_UNKNOWN -> "STT_UNKNOWN"

let string_of_elf32_sym s =
  "{\nst_name  = " ^ s.st_name ^
  ";\nst_value = " ^ string_of_elf32_addr      s.st_value  ^
  ";\nst_size  = " ^ string_of_elf32_word      s.st_size   ^
  ";\nst_bind  = " ^ string_of_elf32_st_bind   s.st_bind   ^
  ";\nst_type  = " ^ string_of_elf32_st_type   s.st_type   ^
  ";\nst_other = " ^ string_of_int             s.st_other  ^
  ";\nst_shndx = " ^ string_of_elf32_half      s.st_shndx  ^
  ";\n}"

let string_of_elf e =
  "{\ne_header   = " ^ string_of_elf32_ehdr e.e_hdr ^
  ";\ne_sections = " ^ string_of_array string_of_elf32_shdr ",\n" e.e_shdra ^
  ";\ne_programs = " ^ string_of_array string_of_elf32_phdr ",\n" e.e_phdra ^
  ";\ne_symtab   = " ^ string_of_array string_of_elf32_sym ",\n" e.e_symtab ^
  ";\n}"
