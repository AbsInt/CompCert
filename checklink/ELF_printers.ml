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
  Printf.sprintf
    "{
ei_class   = %s;
ei_data    = %s;
ei_version = %s;
}"
    (string_of_elfclass ei.ei_class  )
    (string_of_elfdata  ei.ei_data   )
    (string_of_ev       ei.ei_version)

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
  Printf.sprintf
    "{
e_ident     = %s;
e_type      = %s;
e_machine   = %s;
e_version   = %s;
e_entry     = %s;
e_phoff     = %s;
e_shoff     = %s;
e_flags     = %s;
e_ehsize    = %s;
e_phentsize = %s;
e_phnum     = %s;
e_shentsize = %s;
e_shnum     = %s;
e_shstrndx  = %s;
}"
    (string_of_elf_identification eh.e_ident    )
    (string_of_et                 eh.e_type     )
    (string_of_em                 eh.e_machine  )
    (string_of_ev                 eh.e_version  )
    (string_of_elf32_addr         eh.e_entry    )
    (string_of_elf32_off          eh.e_phoff    )
    (string_of_elf32_off          eh.e_shoff    )
    (string_of_bitstring          eh.e_flags    )
    (string_of_elf32_half         eh.e_ehsize   )
    (string_of_elf32_half         eh.e_phentsize)
    (string_of_elf32_half         eh.e_phnum    )
    (string_of_elf32_half         eh.e_shentsize)
    (string_of_elf32_half         eh.e_shnum    )
    (string_of_elf32_half         eh.e_shstrndx )

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
  Printf.sprintf
    "{
sh_name      = %s;
sh_type      = %s;
sh_flags     = %s;
sh_addr      = %s;
sh_offset    = %s;
sh_size      = %s;
sh_link      = %s;
sh_info      = %s;
sh_addralign = %s;
sh_entsize   = %s;
}"
    (sh.sh_name                           )
    (string_of_sht         sh.sh_type     )
    (string_of_elf32_word  sh.sh_flags    )
    (string_of_elf32_addr  sh.sh_addr     )
    (string_of_elf32_off   sh.sh_offset   )
    (string_of_elf32_word  sh.sh_size     )
    (string_of_elf32_word  sh.sh_link     )
    (string_of_elf32_word  sh.sh_info     )
    (string_of_elf32_word  sh.sh_addralign)
    (string_of_elf32_word  sh.sh_entsize  )

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
  Printf.sprintf
    "{
p_type   = %s;
p_offset = %s;
p_vaddr  = %s;
p_paddr  = %s;
p_filesz = %s;
p_memsz  = %s;
p_flags  = %s;
p_align  = %s;
}"
    (string_of_p_type     ph.p_type  )
    (string_of_elf32_off  ph.p_offset)
    (string_of_elf32_addr ph.p_vaddr )
    (string_of_elf32_addr ph.p_paddr )
    (string_of_elf32_word ph.p_filesz)
    (string_of_elf32_word ph.p_memsz )
    (string_of_bitstring  ph.p_flags )
    (string_of_elf32_word ph.p_align )

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
  Printf.sprintf
    "{
st_name  = %s;
st_value = %s;
st_size  = %s;
st_bind  = %s;
st_type  = %s;
st_other = %s;
st_shndx = %s;
}"
    (s.st_name                           )
    (string_of_elf32_addr      s.st_value)
    (string_of_elf32_word      s.st_size )
    (string_of_elf32_st_bind   s.st_bind )
    (string_of_elf32_st_type   s.st_type )
    (string_of_int             s.st_other)
    (string_of_elf32_half      s.st_shndx)

let string_of_elf e =
  Printf.sprintf
    "{
e_header   = %s;
e_sections = %s;
e_programs = %s;
e_symtab   = %s;
}"
    (string_of_elf32_ehdr e.e_hdr                        )
    (string_of_array string_of_elf32_shdr ",\n" e.e_shdra)
    (string_of_array string_of_elf32_phdr ",\n" e.e_phdra)
    (string_of_array string_of_elf32_sym ",\n" e.e_symtab)
