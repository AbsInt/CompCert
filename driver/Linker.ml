(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*      Bernhard Schommer, AbsInt Angewandte Informatik GmbH           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Clflags
open Commandline
open Driveraux


(* Linking *)

let linker exe_name files =
  let cmd = List.concat [
    Configuration.linker;
    ["-o"; exe_name];
    files;
    (if Configuration.has_runtime_lib
     then ["-L" ^ !stdlib_path; "-lcompcert"]
     else [])
  ] in
  let exc = command cmd in
  if exc <> 0 then begin
    command_error "linker" exc;
    exit 2
  end


let gnu_linker_help =
"  -nostartfiles  Do not use the standard system startup files when\n\
\                 linking\n\
\  -nodefaultlibs Do not use the standard system libraries when\n\
\                 linking\n\
\  -nostdlib      Do not use the standard system startup files or\n\
\                 libraries when linking\n"

let linker_help =
"Linking options:\n\
\  -l<lib>        Link library <lib>\n\
\  -L<dir>        Add <dir> to search path for libraries\n" ^
 (if gnu_system then gnu_linker_help else "") ^
"  -s             Remove all symbol table and relocation information from the\n\
\                 executable\n\
\  -static        Prevent linking with the shared libraries\n\
\  -T <file>      Use <file> as linker command file\n\
\  -Wl,<opt>      Pass option <opt> to the linker\n\
\  -WUl,<opt>     Pass option <opt> to the gcc or dcc used for linking\n\
\  -Xlinker <opt> Pass <opt> as an option to the linker\n\
\  -u <symb>      Pretend the symbol <symb> is undefined to force linking of\n\
\                 library modules to define it.\n"

let linker_actions =
  [ Prefix "-l", Self push_linker_arg;
    Prefix "-L", Self push_linker_arg; ] @
  (if gnu_system then
    [ Exact "-nostartfiles", Self push_linker_arg;
      Exact "-nodefaultlibs", Self push_linker_arg;
      Exact "-nostdlib", Self push_linker_arg;]
  else []) @
  [ Exact "-s", Self push_linker_arg;
    Exact "-static", Self push_linker_arg;
    Exact "-T", String (fun s -> if gnu_system then begin
      push_linker_arg ("-T");
      push_linker_arg(s)
    end else
      push_linker_arg ("-Wm"^s));
    Exact "-Xlinker", String (fun s -> if Configuration.system = "diab" then
      push_linker_arg ("-Wl,"^s)
    else
      push_linker_arg s);
    Prefix "-Wl,", Self push_linker_arg;
    Prefix "-WUl,", Self (fun s -> List.iter push_linker_arg (explode_comma_option s));
    Exact "-u", Self push_linker_arg;]
