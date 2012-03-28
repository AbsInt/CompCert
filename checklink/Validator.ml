open Check
open ELF_parsers
open ELF_printers
open Fuzz

let elf_file = ref (None: string option)
let sdump_files = ref ([] : string list)
let option_fuzz = ref false
let option_dumpelf = ref false

let set_elf_file s =
  match !elf_file with
  | None -> elf_file := Some s
  | Some _ -> raise (Arg.Bad "multiple ELF executables given on command line")

let options = [
  "-dumpelf", Arg.Set option_dumpelf,
    "Print the contents of the ELF executable";
  "-debug", Arg.Set Check.debug,
    "Print a detailed trace of verification";
  "-elfmap", Arg.Set Check.dump_elfmap,
    "Dump an ELF map to <exename>.elfmap>, for use with random fuzzing";
  "-exe <filename>", Arg.String set_elf_file,
    "Specify the ELF executable file to analyze";
  "-fuzz", Arg.Set option_fuzz,
    "Random fuzzing test"
]

let anonymous arg =
  if Filename.check_suffix arg ".sdump" then
    sdump_files := arg :: !sdump_files
  else
    set_elf_file arg

let usage =
"The CompCert C post-linking validator, version " ^ Configuration.version ^ "
Usage: valink [options] <.sdump files> <ELF executable>
Options are:"

let _ =
  Arg.parse options anonymous usage;
  match !elf_file with
  | None ->
      Arg.usage options usage;
      exit 2
  | Some elffilename ->
      let sdumps = List.rev !sdump_files in
      if !option_fuzz then begin
        Random.self_init();
        fuzz_loop elffilename sdumps
      end else if !option_dumpelf then begin
        let elf = read_elf elffilename in
        print_endline (string_of_elf elf)
      end else begin
        check_and_dump elffilename sdumps
      end
