open ELF_types
open Library

let section_ndx_by_name_noelf (eshdra: elf32_shdr array)(name: string): int =
  match array_exists (fun eshdr -> eshdr.sh_name = name) eshdra with
  | Some sndx -> sndx
  | None      -> assert false

let section_ndx_by_name (e: elf)(name: string): int option =
  array_exists (fun eshdr -> eshdr.sh_name = name) e.e_shdra

let section_bitstring_noelf
    (bs: bitstring)(eshdra: elf32_shdr array)(sndx: int): bitstring =
  let sofs = Safe32.to_int eshdra.(sndx).sh_offset in
  let size = Safe32.to_int eshdra.(sndx).sh_size in
  Bitstring.subbitstring bs Safe.(sofs * 8) Safe.(size * 8)

let section_bitstring (e: elf): int -> bitstring =
  section_bitstring_noelf e.e_bitstring e.e_shdra

let physical_offset_of_vaddr (e: elf)(vaddr: int32): int32 option =
  begin match e.e_sym_phdr vaddr with
  | None -> None
  | Some(pndx) ->
      let phdr = e.e_phdra.(pndx) in
      let vaddr_ofs = Safe32.(vaddr - phdr.p_vaddr) in
      Some(Safe32.(phdr.p_offset + vaddr_ofs))
  end

(* TODO: could make this more efficient, but it's not often called *)
let section_at_vaddr (e: elf)(vaddr: int32): int option =
  array_exists
    (fun shdr ->
      shdr.sh_addr <= vaddr && vaddr < Int32.add shdr.sh_addr shdr.sh_size
    )
    e.e_shdra

(**
   Returns the bitstring of the specified byte size beginning at the specified
   virtual address, along with its physical byte offset and physical byte size,
   that is, the space it occupies in the file.
*)
let bitstring_at_vaddr (e: elf)(vaddr: int32)(size:int32):
    (bitstring * int32 * int32) option =
  match e.e_sym_phdr vaddr with
  | None -> None
  | Some(pndx) ->
      let phdr = e.e_phdra.(pndx) in
      let phdr_mem_first = phdr.p_vaddr in
      let phdr_mem_last = Safe32.(phdr.p_vaddr + phdr.p_memsz - 1l) in
      let vaddr_mem_first = vaddr in
      let vaddr_mem_last = Safe32.(vaddr + size - 1l) in
      if not (phdr_mem_first <= vaddr_mem_first && vaddr_mem_last <= phdr_mem_last)
      then None (* we're overlapping segments *)
      else
        let vaddr_relative_ofs = Safe32.(vaddr_mem_first - phdr_mem_first) in
        let vaddr_file_ofs = Safe32.(phdr.p_offset + vaddr_relative_ofs) in
        if phdr.p_filesz = 0l || vaddr_relative_ofs > phdr.p_filesz
        then
          Some(
            Bitstring.create_bitstring Safe32.(to_int (8l * size)),
            phdr.p_offset, (* whatever? *)
            0l
          )
        else if Safe32.(vaddr_relative_ofs + size) > phdr.p_filesz
        then
          let bit_start = Safe32.(to_int (8l * vaddr_file_ofs)) in
          let vaddr_file_len = Safe32.(phdr.p_filesz - vaddr_relative_ofs) in
          let bit_len = Safe32.(to_int (8l * vaddr_file_len)) in
          let first = Bitstring.subbitstring e.e_bitstring bit_start bit_len in
          let rest = Bitstring.create_bitstring (8 * Safe32.to_int size - bit_len) in
          Some(
            Bitstring.concat [first; rest],
            vaddr_file_ofs,
            vaddr_file_len
          )
        else
          let bit_start = Safe32.(to_int (8l * (phdr.p_offset + vaddr_relative_ofs))) in
          let bit_len = Safe.(8 * Safe32.to_int size) in
          Some(
            Bitstring.subbitstring e.e_bitstring bit_start bit_len,
            vaddr_file_ofs,
            size
          )

(**
   Returns the entire bitstring that begins at the specified virtual address and
   ends at the end of the segment.
*)
let bitstring_at_vaddr_nosize (e: elf)(vaddr: int32):
    (bitstring * int32 * int32) option =
  match e.e_sym_phdr vaddr with
  | None -> None
  | Some(pndx) ->
      let phdr = e.e_phdra.(pndx) in
      let first_byte_vaddr = vaddr in
      let last_byte_vaddr = Safe32.(phdr.p_vaddr + phdr.p_memsz - 1l) in
      let size = Safe32.(last_byte_vaddr - first_byte_vaddr + 1l) in
      bitstring_at_vaddr e vaddr size

(**
   Removes symbol version for GCC's symbols.
*)
let strip_versioning (s: string): string =
  try String.sub s 0 (String.index s '@')
  with Not_found -> s

(**
   Removes CompCert's mangling of variadic functions
*)
let strip_mangling (s: string): string =
  try String.sub s 0 (String.index s '$')
  with Not_found -> s

(**
   Returns the list of all symbols matching the specified name.
*)
let ndxes_of_sym_name (e: elf) (name: string): int list =
  try StringMap.find (strip_mangling name) e.e_syms_by_name with Not_found -> []

(**
   Returns the index of the first symbol matching the specified name, if it
   exists.
*)
let ndx_of_sym_name (e: elf) (name: string): int option =
  match ndxes_of_sym_name e name with
  | [] -> None
  | h::_ -> Some(h)
