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

let physical_offset_of_vaddr (e: elf)(sndx: int)(vaddr: int32): int32 =
  let shdr = e.e_shdra.(sndx) in
  Int32.(add shdr.sh_offset (sub vaddr shdr.sh_addr))

let section_at_vaddr (e: elf)(vaddr: int32): int option =
  array_exists
    (fun shdr ->
      shdr.sh_addr <= vaddr && vaddr < Int32.add shdr.sh_addr shdr.sh_size
    )
    e.e_shdra

(**
   Returns the bitstring of the specified size beginning at the specified
   virtual address within the specified section.
*)
let bitstring_at_vaddr e sndx vaddr size =
  let shdr = e.e_shdra.(sndx) in
  let bs = section_bitstring e sndx in
  let bit_ofs = Safe.(8 * Safe32.(to_int (vaddr - shdr.sh_addr))) in
  Bitstring.subbitstring bs bit_ofs size

(**
   Returns the entire bitstring that begins at the specified virtual address
   within the specified section and ends at the end of the file. This is useful
   when you don't know the sections size yet.
*)
let bitstring_at_vaddr_nosize (e: elf)(sndx: int)(vaddr: int32): bitstring =
  let shdr = e.e_shdra.(sndx) in
  let bs = section_bitstring e sndx in
  let bit_ofs = Safe.(8 * Safe32.(to_int (vaddr - shdr.sh_addr))) in
  Bitstring.dropbits bit_ofs bs

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
   Returns the index of the first symbol matching the specified name, if it
   exists.
*)
let ndx_of_sym_name (e: elf) (name: string): int option =
  array_exists
    (fun x -> strip_versioning x.st_name = strip_mangling name)
    e.e_symtab

(**
   Returns the list of all symbols matching the specified name.
*)
let ndxes_of_sym_name (e: elf) (name: string): int list =
  List.map fst
    (List.filter
       (fun (_, x) -> strip_versioning x.st_name = strip_mangling name)
       (Array.to_list (Array.mapi (fun a b -> (a, b)) e.e_symtab)))
