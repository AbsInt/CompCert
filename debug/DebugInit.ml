(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  AbsInt Angewandte Informatik GmbH. All rights reserved. This file  *)
(*  is distributed under the terms of the INRIA Non-Commercial         *)
(*  License Agreement.                                                 *)
(*                                                                     *)
(* *********************************************************************)

open Clflags
open Commandline
open Debug


let init_debug () =
  implem :=
  if Configuration.gnu_toolchain then
    {DebugInformation.default_debug with generate_debug_info = (fun a b -> Some (Dwarfgen.gen_gnu_debug_info a b));
     add_fun_addr = DebugInformation.gnu_add_fun_addr}
  else
    let gen = (fun a b -> Some (Dwarfgen.gen_diab_debug_info a b)) in
    {DebugInformation.default_debug with generate_debug_info = gen;
     add_diab_info = DebugInformation.add_diab_info;
     add_fun_addr = DebugInformation.diab_add_fun_addr;}

let init_none () =
  implem := default_implem

let init () =
  if !option_g then
    init_debug ()
  else
    init_none ()

let gnu_debugging_help =
"  -gdwarf-       Generate debug information in DWARF v2 or DWARF v3\n"

let debugging_help =
{|Debugging options:
  -g             Generate debugging information
  -g<n>          Control generation of debugging information
                 (<n>=0: none, <n>=1: only-globals, <n>=2: globals + locals
                 without locations, <n>=3: full;)
|}
^ (if Configuration.gnu_toolchain then gnu_debugging_help else "")

let gnu_debugging_actions =
  let version version () =
    option_g:=true;
    option_gdwarf:=version
  in
  [Exact "-gdwarf-2", Unit (version 2);
   Exact "-gdwarf-3", Unit (version 3);]

let debugging_actions =
  let depth depth () =
    option_g:=true;
    option_gdepth := depth
  in
  [Exact "-g", Unit (depth 3);
   Exact "-g0", Unset option_g;
   Exact "-g1", Unit (depth 1);
   Exact "-g2", Unit (depth 2);
   Exact "-g3", Unit (depth 3);]
  @
  (if Configuration.gnu_toolchain then gnu_debugging_actions else [])
