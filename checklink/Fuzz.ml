open Check
open ELF_parsers
open ELF_types
open Frameworks
open Library

let string_of_byte = Printf.sprintf "0x%02x"

let full_range_of_byte elfmap byte =
  let byte = int_int32 byte in
  List.find (fun (a, b, _, _) -> a <= byte && byte <= b) elfmap 

let range_of_byte elfmap byte =
  let (_, _, _, r) = full_range_of_byte elfmap byte in
  r

let fuzz_check elfmap bs byte old sdumps =
  let (str, _, _) = bs in
  try (
    let elf = read_elf_bs bs in
    try (
      let efw = check_elf elf sdumps in
      try (
        let _ = List.find (function ERROR(s) -> true | _ -> false) efw.log in
        ()
      ) with
      | Not_found ->
          print_endline (
            string_of_int32 (int_int32 byte) ^ " <- " ^
              string_of_byte (Char.code str.[byte]) ^ " (was " ^
              string_of_byte (Char.code old) ^ ") - " ^
              string_of_byte_chunk_desc (range_of_byte elfmap byte)
          )
    ) with
    | e -> ()
  ) with
  | e -> ()

let ok_fuzz elfmap str byte fuzz =
  let (a, b, _, r) = full_range_of_byte elfmap byte in
  let a = int32_int a in
  let b = int32_int b in
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
        && (fuz = 0x80)
        && (Char.code str.[byte + 0] = 0x00)
        && (Char.code str.[byte + 1] = 0x00)
        && (Char.code str.[byte + 2] = 0x00)
        && (Char.code str.[byte + 3] = 0x00)
        && (Char.code str.[byte + 4] = 0x00)
        && (Char.code str.[byte + 5] = 0x00)
        && (Char.code str.[byte + 6] = 0x00)
        && (Char.code str.[byte + 7] = 0x00)
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
        && (fuz = 0x80)
        && (Char.code str.[byte + 0] = 0x00)
        && (Char.code str.[byte + 1] = 0x00)
        && (Char.code str.[byte + 2] = 0x00)
        && (Char.code str.[byte + 3] = 0x00)
        && (Char.code str.[byte + 4] = 0x00)
        && (Char.code str.[byte + 5] = 0x00)
        && (Char.code str.[byte + 6] = 0x00)
        && (Char.code str.[byte + 7] = 0x00)
      )
  | Padding            -> false (* padding may be non-null *)
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
(*
  let fuzz_all elffilename sdumps =
  let elfmap = get_elfmap elffilename in
  let (str, ofs, len) = Bitstring.bitstring_of_file elffilename in
  let rec fuzz_all_aux current limit =
  if current = limit
  then ()
  else (
  if ok_fuzz elfmap current
  then (
  let str' = String.copy str in
  fuzz_byte str' current;
  let msg = string_of_int32 (int_int32 current) ^ " <- " ^
  string_of_byte (Char.code str'.[current]) ^ " (was " ^
  string_of_byte (Char.code str.[current]) ^ ") - " ^
  string_of_elf_range (range_of_byte elfmap current)
  in
  fuzz_check msg (str', ofs, len) sdumps
  );
  fuzz_all_aux (current + 1) limit
  )
  in fuzz_all_aux 0 (len/8)
*)
