open Check
open ELF_parsers
open ELF_types
open Frameworks
open Library

let fuzz_debug = ref false

let string_of_byte = Printf.sprintf "0x%02x"

let full_range_of_byte elfmap byte =
  let byte = Int32.of_int byte in
  List.find (fun (a, b, _, _) -> a <= byte && byte <= b) elfmap 

let range_of_byte elfmap byte =
  let (_, _, _, r) = full_range_of_byte elfmap byte in
  r

(** [fuzz_check] will print what happened on stderr, and report errors (that is,
    when the check went fine) to stdout.
*)
let fuzz_check elfmap bs byte old sdumps =
  let is_error = function ERROR(_) -> true | _ -> false in
  let (str, _, _) = bs in
  let fuzz_description =
    string_of_int32 (Int32.of_int byte) ^ " <- " ^
      string_of_byte (Char.code str.[byte]) ^ " (was " ^
      string_of_byte (Char.code old) ^ ") - " ^
      string_of_byte_chunk_desc (range_of_byte elfmap byte)
  in
  if !fuzz_debug
  then print_endline fuzz_description;
  try
    (* The point here is to go all the way through the checks, and see whether
       the checker returns an ERROR or raises an exception. If not, then we
       might be missing a bug!
    *)
    let elf = read_elf_bs bs in
    let efw = check_elf_nodump elf sdumps in
    if List.exists is_error efw.log
    then (* finding an ERROR is the expected behavior *)
      begin
        if !fuzz_debug
        then print_endline (
          string_of_log_entry false (List.find is_error efw.log)
        )
      end
    else (* not finding an ERROR is bad thus reported *)
      print_endline (fuzz_description ^ " DID NOT CAUSE AN ERROR!")
  with
  | Assert_failure(s, l, c) ->
      if !fuzz_debug
      then Printf.printf "fuzz_check failed an assertion at %s (%d, %d)\n" s l c
  | Exc.IntOverflow | Exc.Int32Overflow ->
      if !fuzz_debug
      then Printf.printf "fuzz_check raised an integer overflow exception\n"
  | Match_failure(s, l, c) ->
      if !fuzz_debug
      then Printf.printf "fuzz_check raised a match failure at %s (%d, %d)\n" s l c
  | Not_found ->
      if !fuzz_debug
      then Printf.printf "fuzz_check raised a not found exception\n"
  | Invalid_argument(s) ->
      if !fuzz_debug
      then Printf.printf "fuzz_check raised an invalid argument: %s\n" s
  | ELF_parsers.Unknown_endianness ->
      if !fuzz_debug
      then Printf.printf "fuzz_check raised an unknown endianness exception\n"

(** Tries to prevent some easy-to-catch false positives. Some known false
    positives are however hard to predict. For instance, when the virtual
    address of a stub is replaced by the virtual address of another exact
    same stub.
*)
let ok_fuzz elfmap str byte fuzz =
  let (a, b, _, r) = full_range_of_byte elfmap byte in
  let a = Safe32.to_int a in
  let b = Safe32.to_int b in
  let old = Char.code str.[byte] in
  let fuz = Char.code fuzz in
  match r with
  | ELF_header         ->
      not (List.mem byte
             [
               0x18; 0x19; 0x1a; 0x1b; (* e_entry *)
               0x1c; 0x1d; 0x1e; 0x1f; (* e_phoff *)
               0x24; 0x25; 0x26; 0x27; (* e_flags *)
               0x2c; 0x2d (* e_phnum *)
             ]
      )
  | ELF_progtab        -> false
  | ELF_shtab          -> false
  | ELF_section_strtab -> false
  | ELF_symbol_strtab  -> false
  | Symtab_data(_)     ->
      (* False positive: switching from/to STT_NOTYPE *)
      not (byte = a + 12
          && ((old land 0xf = 0) || (fuz land 0xf = 0))
      )
  | Symtab_function(_) -> true
  | Data_symbol(_)     ->
      (* False positive: 0. becomes -0. *)
      not (
        (byte + 7 <= b)
        && (fuz = 0x80) (* sign bit *)
        && String.sub str byte 8 = "\000\000\000\000\000\000\000\000"
      )
  | Function_symbol(_) ->
      let opcode = Char.code str.[byte - 3] in
      (* False positive: rlwinm with bitmask 0 31 = bitmask n (n - 1) *)
      not (0x54 <= opcode && opcode <= 0x57 && old = 0x3E
          && (fuz = 0x40 || fuz = 0x82 || fuz = 0xc4))
  | Zero_symbol        -> false
  | Stub(_)            -> true
  | Jumptable          -> true
  | Float_literal(_)   ->
      (* False positive: 0. becomes -0. *)
      not (
        (byte = a)
        && (fuz = 0x80) (* sign bit *)
        && String.sub str byte 8 = "\000\000\000\000\000\000\000\000"
      )
  (* padding is allowed to be non-null, but won't be recognized as padding, but
     as unknown, which is not an ERROR *)
  | Padding            -> false
  | Unknown(_)         -> false

let fuzz_byte str byte_ndx =
  let rand = Char.chr (Random.int 255) in (* [0 - 254] *)
  if rand = str.[byte_ndx] (* if we picked a byte equal to the current *)
  then Char.chr 255        (* then replace with byte 255 *)
  else rand                (* else replace with the byte we picked *)

let rec find_byte_to_fuzz elfmap str byterange =
  let byte = Random.int byterange in
  let fuzz = fuzz_byte str byte in
  if ok_fuzz elfmap str byte fuzz
  then (byte, fuzz)
  else find_byte_to_fuzz elfmap str byterange

let get_elfmap elffilename =
  let ic = open_in (elffilename ^ ".elfmap") in
  let elfmap = input_value ic in
  close_in ic;
  elfmap

(** Randomly fuzz bytes forever *)
let fuzz_loop elffilename sdumps =
  let elfmap = get_elfmap elffilename in
  let (str, ofs, len) = Bitstring.bitstring_of_file elffilename in
  let rec fuzz_loop_aux () =
    let (byte, fuzz) = find_byte_to_fuzz elfmap str (len/8) in
    let str' = String.copy str in
    str'.[byte] <- fuzz;
    fuzz_check elfmap (str', ofs, len) byte str.[byte] sdumps;
    fuzz_loop_aux ()
  in fuzz_loop_aux ()

let rec fuzz_every_byte_once_aux elfmap bs sdumps (current: int): unit =
  let (str, ofs, len) = bs in
  if current = len / 8 (* len is in bits *)
  then ()
  else (
    let fuzz = fuzz_byte str current in
    if ok_fuzz elfmap str current fuzz
    then (
      let str' = String.copy str in
      str'.[current] <- fuzz;
      fuzz_check elfmap (str', ofs, len) current str.[current] sdumps
    );
    fuzz_every_byte_once_aux elfmap bs sdumps (current + 1)
  )

(** Fuzz each byte of the file once with a random new value *)
let fuzz_every_byte_once elffilename sdumps =
  let elfmap = get_elfmap elffilename in
  let bs = Bitstring.bitstring_of_file elffilename in
  fuzz_every_byte_once_aux elfmap bs sdumps 0

(** Fuzz each byte of the file, then loop *)
let fuzz_every_byte_loop elffilename sdumps =
  let elfmap = get_elfmap elffilename in
  let bs = Bitstring.bitstring_of_file elffilename in
  let rec fuzz_every_byte_loop_aux () =
    fuzz_every_byte_once_aux elfmap bs sdumps 0;
    fuzz_every_byte_loop_aux ()
  in fuzz_every_byte_loop_aux ()
