open Library

type elf32_addr     = int32
type elf32_half     = int
type elf32_off      = int32
type elf32_sword    = int32
type elf32_word     = int32
type byte           = int

(** ELF identification *)

type elfclass =
  | ELFCLASSNONE
  | ELFCLASS32
  | ELFCLASS64
  | ELFCLASSUNKNOWN

type elfdata =
  | ELFDATANONE
  | ELFDATA2LSB
  | ELFDATA2MSB
  | ELFDATAUNKNOWN

type ev =
  | EV_NONE
  | EV_CURRENT
  | EV_UNKNOWN

type elf_identification =
    { ei_class   : elfclass (* 32/64 bit *)
    ; ei_data    : elfdata  (* endianness *)
    ; ei_version : ev       (* ELF header version *)
    }

(** ELF header *)

type et =
  | ET_NONE
  | ET_REL
  | ET_EXEC
  | ET_DYN
  | ET_CORE
  | ET_UNKNOWN

type em =
  | EM_NONE
  | EM_M32
  | EM_SPARC
  | EM_386
  | EM_68K
  | EM_88K
  | EM_860
  | EM_MIPS
  | EM_MIPS_RS4_BE
  | EM_PPC
  | EM_UNKNOWN

let shn_UNDEF  = 0
let shn_ABS    = 0xFFF1
let shn_COMMON = 0xFFF2

type elf32_ehdr =
    { e_ident     : elf_identification  (* Machine-independent data *)
    ; e_type      : et                  (* Object file type *)
    ; e_machine   : em                  (* Required architecture *)
    ; e_version   : ev                  (* Object file version *)
    ; e_entry     : elf32_addr          (* Entry point virtual address *)
    ; e_phoff     : elf32_off           (* Program header table's offset *)
    ; e_shoff     : elf32_off           (* Section header table's offset *)
    ; e_flags     : Bitstring.bitstring (* Processor-specific flags *)
    ; e_ehsize    : elf32_half          (* ELF header size *)
    ; e_phentsize : elf32_half          (* Size of a program header's entry *)
    ; e_phnum     : elf32_half          (* Number of program header entries *)
    ; e_shentsize : elf32_half          (* Size of a section header's entry *)
    ; e_shnum     : elf32_half          (* Number of section header entries *)
    ; e_shstrndx  : elf32_half          (* Section name string table index *)
    }

(** ELF section header *)

type sht =
  | SHT_NULL
  | SHT_PROGBITS
  | SHT_SYMTAB
  | SHT_STRTAB
  | SHT_RELA
  | SHT_HASH
  | SHT_DYNAMIC
  | SHT_NOTE
  | SHT_NOBITS
  | SHT_REL
  | SHT_SHLIB
  | SHT_DYNSYM
  | SHT_UNKNOWN

type elf32_shdr =
    { sh_name      : string
    ; sh_type      : sht
    ; sh_flags     : elf32_word
    ; sh_addr      : elf32_addr
    ; sh_offset    : elf32_off
    ; sh_size      : elf32_word
    ; sh_link      : elf32_word
    ; sh_info      : elf32_word
    ; sh_addralign : elf32_word
    ; sh_entsize   : elf32_word
    }

let shf_WRITE = 0x1l
let shf_ALLOC = 0x2l
let shf_EXECINSTR = 0x4l

type elf32_st_bind =
  | STB_LOCAL
  | STB_GLOBAL
  | STB_WEAK
  | STB_UNKNOWN

type elf32_st_type =
  | STT_NOTYPE
  | STT_OBJECT
  | STT_FUNC
  | STT_SECTION
  | STT_FILE
  | STT_UNKNOWN

type elf32_sym =
    { st_name  : string
    ; st_value : elf32_addr
    ; st_size  : elf32_word
    ; st_bind  : elf32_st_bind
    ; st_type  : elf32_st_type
    ; st_other : byte
    ; st_shndx : elf32_half
    }

(** ELF program header *)

type p_type =
  | PT_NULL
  | PT_LOAD
  | PT_DYNAMIC
  | PT_INTERP
  | PT_NOTE
  | PT_SHLIB
  | PT_PHDR
  | PT_UNKNOWN

type elf32_phdr =
    { p_type   : p_type
    ; p_offset : elf32_off
    ; p_vaddr  : elf32_addr
    ; p_paddr  : elf32_addr
    ; p_filesz : elf32_word
    ; p_memsz  : elf32_word
    ; p_flags  : bitstring
    ; p_align  : elf32_word
    }

(** ELF *)
type elf =
    { e_bitstring    : bitstring
    ; e_hdr          : elf32_ehdr
    ; e_shdra        : elf32_shdr array
    ; e_phdra        : elf32_phdr array
    ; e_symtab       : elf32_sym array
    ; e_symtab_sndx  : int (* section index of the symbol table *)
    ; e_sym_phdr     : int32 -> int option (* fast sym -> phdr lookup *)
    ; e_syms_by_name : int list StringMap.t (* fast name -> sym lookup *)
    }
