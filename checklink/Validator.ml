open Check
open ELF_parsers
open ELF_printers
open Fuzz

let elf_file = ref (None: string option)
let sdump_files = ref ([] : string list)
let option_fuzz = ref false
let option_bytefuzz = ref false
let option_printelf = ref false

let set_elf_file s =
  match !elf_file with
  | None -> elf_file := Some s
  | Some _ -> raise (Arg.Bad "multiple ELF executables given on command line")

let options = [
  "-exe <filename>", Arg.String set_elf_file,
  "Specify the ELF executable file to analyze";
  "-debug", Arg.Set Check.debug,
  "Print a detailed trace of verification";
  "-noexhaust", Arg.Clear Check.exhaustivity,
  "Disable the exhaustivity check of ELF function and data symbols";
  "-printelf", Arg.Set option_printelf,
  "Print the contents of the unanalyzed ELF executable";
  "-printelfmap", Arg.Set Check.print_elfmap,
  "Print a map of the analyzed ELF executable";
  "-dumpelfmap", Arg.Set Check.dump_elfmap,
  "Dump an ELF map to <exename>.elfmap, for use with random fuzzing";
  "-fuzz", Arg.Set option_fuzz,
  "Random fuzz testing";
  "-bytefuzz", Arg.Set option_bytefuzz,
  "Random fuzz testing byte per byte";
  "-debugfuzz", Arg.Set Fuzz.fuzz_debug,
  "Print a detailed trace of ongoing fuzz testing";
]

let anonymous arg =
  if Filename.check_suffix arg ".sdump" then
    sdump_files := arg :: !sdump_files
  else
    set_elf_file arg

let usage =
  "The CompCert C post-linking validator, version " ^ Configuration.version ^ "
Usage: cchecklink [options] <.sdump files> <ELF executable>
In the absence of options, checks are performed and a short result is displayed.
Options are:"

let _ =
  Arg.parse options anonymous usage;
  match !elf_file with
  | None ->
      Arg.usage options usage;
      exit 2
  | Some elffilename ->
      let sdumps = List.rev !sdump_files in
      if !option_bytefuzz then begin
        Random.self_init();
        fuzz_every_byte_loop elffilename sdumps
      end else if !option_fuzz then begin
        Random.self_init();
        fuzz_loop elffilename sdumps
      end else if !option_printelf then begin
        let elf = read_elf elffilename in
        print_endline (string_of_elf elf)
      end else begin
        check_elf_dump elffilename sdumps
      end
