open Check
open Disassembler
open ELF_parsers
open ELF_printers
open Fuzz

let elf_file = ref (None: string option)
let sdump_files = ref ([] : string list)
let option_fuzz = ref false
let option_bytefuzz = ref false
let option_printelf = ref false

let set_elf_file s =
  begin match !elf_file with
  | None -> elf_file := Some s
  | Some _ -> raise (Arg.Bad "multiple ELF executables given on command line")
  end

let set_conf_file s =
  begin match !conf_file with
  | None -> conf_file := Some s
  | Some _ -> raise (Arg.Bad "multiple configuration files given on command line")
  end

let option_disassemble = ref false
let disassemble_list = ref ([]: string list)
let add_disassemble s =
  disassemble_list := s :: !disassemble_list;
  option_disassemble := true

let options = [
  (* Main options *)
  "-exe", Arg.String set_elf_file,
  "<filename> Specify the ELF executable file to analyze";
  "-conf", Arg.String set_conf_file,
  "<filename> Specify a configuration file";
  (* Parsing behavior *)
  "-relaxed", Arg.Set ELF_parsers.relaxed,
  "Allows the following behaviors in the ELF parser:
\t* Use of a fallback heuristic to resolve symbols bootstrapped at load time";
  (* Printing behavior *)
  "-no-exhaustive", Arg.Clear Check.exhaustivity,
  "Disable the exhaustivity check of ELF function and data symbols";
  "-list-missing", Arg.Set Check.list_missing,
  "List function and data symbols that were missing in the exhaustivity check";
  (* Alternative outputs *)
  "-debug", Arg.Set Check.debug,
  "Print a detailed trace of verification";
  "-disass", Arg.String add_disassemble,
  "<symname> Disassemble the symbol with specified name (can be repeated)";
  "-print-elf", Arg.Set option_printelf,
  "Print the contents of the unanalyzed ELF executable";
  (* ELF map related *)
  "-print-elfmap", Arg.Set Check.print_elfmap,
  "Print a map of the analyzed ELF executable";
  "-verbose-elfmap", Arg.Set Frameworks.verbose_elfmap,
  "Show sections and symbols contained in the unknown parts of the elf map";
  (* Fuzz testing related *)
  "-dump-elfmap", Arg.Set Check.dump_elfmap,
  "Dump an ELF map to <exename>.elfmap, for use with random fuzzing";
  "-fuzz", Arg.Set option_fuzz,
  "Random fuzz testing";
  "-fuzz-byte", Arg.Set option_bytefuzz,
  "Random fuzz testing byte per byte";
  "-fuzz-debug", Arg.Set Fuzz.fuzz_debug,
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
  begin match !elf_file with
  | None ->
      Arg.usage options usage;
      exit 2
  | Some elffilename ->
      let sdumps = List.rev !sdump_files in
      if !option_disassemble then begin
        let elf = read_elf elffilename in
        List.iter
          (fun s ->
            Printf.printf "Disassembling %s:\n%s\n\n" s (disassemble elf s)
          )
          !disassemble_list
      end else if !option_bytefuzz then begin
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
  end
