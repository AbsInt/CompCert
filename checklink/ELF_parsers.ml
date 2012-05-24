open Bitstring_utils
open ELF_types
open ELF_printers
open ELF_utils
open Library
open PPC_parsers

(** Allows relaxations of the parser:

    1. Any segment that has the same p_offset and p_memsz as another segment,
    and a null p_filesz, will be considered as having a p_filesz equal to the
    other segment. This allow symbol's contents resolution to succeed even in
    the presence of a bootstrapping copy mechanism from one segment to the
    other.
*)
let relaxed = ref false

exception Unknown_endianness

(** Converts an elf endian into a bitstring endian *)
let elfdata_to_endian (e: elfdata): Bitstring.endian =
  match e with
  | ELFDATA2LSB -> Bitstring.LittleEndian
  | ELFDATA2MSB -> Bitstring.BigEndian
  | _           -> raise Unknown_endianness

(** Parses an elf32 header *)
let read_elf32_ehdr (bs: bitstring): elf32_ehdr =
  bitmatch bs with
  | { e_ident : 16*8 : bitstring ;
      rest    : -1   : bitstring } ->
      (
        bitmatch e_ident with
        | { 0x7F       : 8              ;
            "ELF"      : 24 : string    ;
            ei_class   : 8  : int       ;
            ei_data    : 8  : int       ;
            ei_version : 8  : int       ;
            padding    : 72 : bitstring } ->
            assert (is_zeros padding 72);
            let ei_data =
              begin match ei_data with
              | 0 -> ELFDATANONE
              | 1 -> ELFDATA2LSB
              | 2 -> ELFDATA2MSB
              | _ -> ELFDATAUNKNOWN
              end
            in
            let e = elfdata_to_endian ei_data in
            (
              bitmatch rest with
              | { e_type      : 16 : int, endian(e) ;
                  e_machine   : 16 : int, endian(e) ;
                  e_version   : 32 : int, endian(e) ;
                  e_entry     : 32 : int, endian(e) ;
                  e_phoff     : 32 : int, endian(e) ;
                  e_shoff     : 32 : int, endian(e) ;
                  e_flags     : 32 : bitstring      ;
                  e_ehsize    : 16 : int, endian(e) ;
                  e_phentsize : 16 : int, endian(e) ;
                  e_phnum     : 16 : int, endian(e) ;
                  e_shentsize : 16 : int, endian(e) ;
                  e_shnum     : 16 : int, endian(e) ;
                  e_shstrndx  : 16 : int, endian(e) } ->
                  (* These shouldn't be different than this... *)
                  assert (e_ehsize = 52);
                  assert (e_phentsize = 32);
                  assert (e_shentsize = 40);
                  {
                    e_ident =
                      {
                        ei_class      =
                          begin match ei_class with
                          | 0 -> ELFCLASSNONE
                          | 1 -> ELFCLASS32
                          | 2 -> ELFCLASS64
                          | _ -> ELFCLASSUNKNOWN
                          end;
                        ei_data     = ei_data;
                        ei_version  =
                          begin match ei_version with
                          | 0 -> EV_NONE
                          | 1 -> EV_CURRENT
                          | _ -> EV_UNKNOWN
                          end;
                      };
                    e_type        =
                      begin match e_type with
                      | 0 -> ET_NONE
                      | 1 -> ET_REL
                      | 2 -> ET_EXEC
                      | 3 -> ET_DYN
                      | 4 -> ET_CORE
                      | _ -> ET_UNKNOWN
                      end;
                    e_machine     =
                      begin match e_machine with
                      | 0  -> EM_NONE
                      | 1  -> EM_M32
                      | 2  -> EM_SPARC
                      | 3  -> EM_386
                      | 4  -> EM_68K
                      | 5  -> EM_88K
                      | 7  -> EM_860
                      | 8  -> EM_MIPS
                      | 10 -> EM_MIPS_RS4_BE
                      | 20 -> EM_PPC
                      | _  -> EM_UNKNOWN
                      end;
                    e_version     =
                      begin match e_version with
                      | 0l -> EV_NONE
                      | 1l -> EV_CURRENT
                      | _ -> EV_UNKNOWN
                      end;
                    e_entry     = e_entry;
                    e_phoff     = e_phoff;
                    e_shoff     = e_shoff;
                    e_flags     = e_flags;
                    e_ehsize    = e_ehsize;
                    e_phentsize = e_phentsize;
                    e_phnum     = e_phnum;
                    e_shentsize = e_shentsize;
                    e_shnum     = e_shnum;
                    e_shstrndx  = e_shstrndx;
                  }
            )
      )

(** Returns the file offset of the section header indexed *)
let section_header_offset (e_hdr: elf32_ehdr) (sndx: int): int =
  Safe.(of_int32 e_hdr.e_shoff + (sndx * e_hdr.e_shentsize))

(** Returns the ndx-th string in the provided bitstring, according to null
    characters *)
let strtab_string (bs: bitstring) (ndx: int): string =
  let (str, ofs, _) = bs in
  let start = (ofs / 8 + ndx) in
  String.sub str start (String.index_from str start '\000' - start)

(** Reads an ELF section header *)
let read_elf32_shdr (e_hdr: elf32_ehdr) (bs: bitstring) (strtab: bitstring)
    (num: int): elf32_shdr =
  let e = elfdata_to_endian e_hdr.e_ident.ei_data in
  let bit_ofs = Safe.(
    (section_header_offset e_hdr num) * 8
  ) in
  bitmatch bs with
  | { sh_name      : 32 : endian(e), offset(bit_ofs) ;
      sh_type      : 32 : endian(e) ;
      sh_flags     : 32 : endian(e) ;
      sh_addr      : 32 : endian(e) ;
      sh_offset    : 32 : endian(e) ;
      sh_size      : 32 : endian(e) ;
      sh_link      : 32 : endian(e) ;
      sh_info      : 32 : endian(e) ;
      sh_addralign : 32 : endian(e) ;
      sh_entsize   : 32 : endian(e) } ->
      {
        sh_name         = strtab_string strtab (Safe32.to_int sh_name);
        sh_type         =
          begin match sh_type with
          |  0l -> SHT_NULL
          |  1l -> SHT_PROGBITS
          |  2l -> SHT_SYMTAB
          |  3l -> SHT_STRTAB
          |  4l -> SHT_RELA
          |  5l -> SHT_HASH
          |  6l -> SHT_DYNAMIC
          |  7l -> SHT_NOTE
          |  8l -> SHT_NOBITS
          |  9l -> SHT_REL
          | 10l -> SHT_SHLIB
          | 11l -> SHT_DYNSYM
          | _   -> SHT_UNKNOWN
          end;
        sh_flags     = sh_flags     ;
        sh_addr      = sh_addr      ;
        sh_offset    = sh_offset    ;
        sh_size      = sh_size      ;
        sh_link      = sh_link      ;
        sh_info      = sh_info      ;
        sh_addralign = sh_addralign ;
        sh_entsize   = sh_entsize   ;
      }

(** Reads an elf program header *)
let read_elf32_phdr (e_hdr: elf32_ehdr) (bs: bitstring) (ndx: int): elf32_phdr =
  let e = elfdata_to_endian e_hdr.e_ident.ei_data in
  let bit_ofs = Safe.(
    ((of_int32 e_hdr.e_phoff) + (ndx * e_hdr.e_phentsize)) * 8
  ) in
  bitmatch bs with
  | { p_type   : 32 : endian(e), offset(bit_ofs) ;
      p_offset : 32 : endian(e) ;
      p_vaddr  : 32 : endian(e) ;
      p_paddr  : 32 : endian(e) ;
      p_filesz : 32 : endian(e) ;
      p_memsz  : 32 : endian(e) ;
      p_flags  : 32 : bitstring ;
      p_align  : 32 : endian(e) } ->
      {
        p_type      =
          begin match p_type with
          | 0l -> PT_NULL
          | 1l -> PT_LOAD
          | 2l -> PT_DYNAMIC
          | 3l -> PT_INTERP
          | 4l -> PT_NOTE
          | 5l -> PT_SHLIB
          | 6l -> PT_PHDR
          | _  -> PT_UNKNOWN
          end;
        p_offset = p_offset ;
        p_vaddr  = p_vaddr  ;
        p_paddr  = p_paddr  ;
        p_filesz = p_filesz ;
        p_memsz  = p_memsz  ;
        p_flags  = p_flags  ;
        p_align  = p_align  ;
      }

(** Reads an ELF symbol *)
let read_elf32_sym (e_hdr: elf32_ehdr) (symtab: bitstring) (strtab: bitstring)
    (num: int): elf32_sym =
  let e = elfdata_to_endian e_hdr.e_ident.ei_data in
  let bit_ofs = Safe.(num * 128) in (* each symbol takes 16 bytes = 128 bits *)
  bitmatch symtab with
  | { st_name  : 32 : endian(e), offset(bit_ofs) ;
      st_value : 32 : endian(e) ;
      st_size  : 32 : endian(e) ;
      st_bind  : 4 ;
      st_type  : 4 ;
      st_other : 8 ;
      st_shndx : 16 : endian(e) } ->
      {
        st_name  = strtab_string strtab (Safe32.to_int st_name) ;
        st_value = st_value ;
        st_size  = st_size  ;
        st_bind  =
          begin match st_bind with
          | 0 -> STB_LOCAL
          | 1 -> STB_GLOBAL
          | 2 -> STB_WEAK
          | _ -> STB_UNKNOWN
          end;
        st_type  =
          begin match st_type with
          | 0 -> STT_NOTYPE
          | 1 -> STT_OBJECT
          | 2 -> STT_FUNC
          | 3 -> STT_SECTION
          | 4 -> STT_FILE
          | _ -> STT_UNKNOWN
          end;
        st_other = st_other ;
        st_shndx = st_shndx ;
      }

(** Reads a whole ELF file from a bitstring *)
let read_elf_bs (bs: bitstring): elf =
  let e_hdr = read_elf32_ehdr bs in
  (* To initialize section names we need the string table *)
  let strtab = (
    let e = elfdata_to_endian e_hdr.e_ident.ei_data in
    let strtab_sndx = e_hdr.e_shstrndx in
    let strtab_shofs = section_header_offset e_hdr strtab_sndx in
    let skipped_bits = Safe.(strtab_shofs * 8 + 128) in
    bitmatch bs with
    | { ofs  : 32 : endian(e), offset(skipped_bits) ;
        size : 32 : endian(e) } ->
        Bitstring.subbitstring bs Safe.(of_int32 ofs * 8) Safe.(of_int32 size * 8)
  )
  in
  let e_shdra =
    Array.init e_hdr.e_shnum (read_elf32_shdr e_hdr bs strtab)
  in
  let symtab_sndx = section_ndx_by_name_noelf e_shdra ".symtab" in
  let e_symtab = (
    let symtab_shdr = e_shdra.(symtab_sndx) in
    let symtab_strtab_sndx = symtab_shdr.sh_link in
    let symtab_nb_ent = (Safe32.to_int symtab_shdr.sh_size / 16) in
    Array.init symtab_nb_ent
      (read_elf32_sym e_hdr
         (section_bitstring_noelf bs e_shdra symtab_sndx)
         (section_bitstring_noelf bs e_shdra (Safe32.to_int symtab_strtab_sndx)))
  ) in
  let e_phdra =
    let untweaked = Array.init e_hdr.e_phnum (read_elf32_phdr e_hdr bs) in
    if !relaxed
    then
      Array.mapi
        (fun ndx curr ->
          if ndx < 1
          then curr
          else
            let prev = untweaked.(ndx - 1) in
            if (curr.p_offset = prev.p_offset)
              && (curr.p_memsz = prev.p_memsz)
            then { curr with p_filesz = prev.p_filesz }
            else curr
        )
        untweaked
    else untweaked
  in
  let e_sym_phdr =
    let intervals =
      Array.mapi
        (fun ndx phdr -> (* (ndx, (start, stop), type) *)
          (ndx,
           (phdr.p_vaddr, Safe32.(phdr.p_vaddr + phdr.p_memsz - 1l)),
           phdr.p_type
          )
        )
        e_phdra
    in
    let intervals = Array.of_list (
      List.filter
        (function (_, _, PT_LOAD) -> true | _ -> false)
        (Array.to_list intervals)
    ) in
    Array.fast_sort (fun (_, (x, _), _) (_, (y, _), _) -> compare x y) intervals;
    let lookup =
      sorted_lookup
        (
          fun (_, (a, b), _) v ->
            if a <= v && v <= b
            then 0
            else compare a v
        )
        intervals
    in
    fun vaddr ->
      begin match lookup vaddr with
      | None -> None
      | Some(ndx, (_, _), _) -> Some(ndx)
      end
  in
  let e_syms_by_name =
    let m = ref StringMap.empty in
    for i = 0 to Array.length e_symtab - 1 do
      let name = strip_versioning e_symtab.(i).st_name in
      let list = try StringMap.find name !m with Not_found -> [] in
      m := StringMap.add name (i :: list) !m
    done;
    !m
  in
  {
    e_bitstring    = bs;
    e_hdr          = e_hdr;
    e_shdra        = e_shdra;
    e_phdra        = e_phdra;
    e_symtab       = e_symtab;
    e_symtab_sndx  = symtab_sndx;
    e_sym_phdr     = e_sym_phdr;
    e_syms_by_name = e_syms_by_name;
  }

(** Reads a whole ELF file from a file name *)
let read_elf (elffilename: string): elf =
  let bs = Bitstring.bitstring_of_file elffilename in
  read_elf_bs bs
