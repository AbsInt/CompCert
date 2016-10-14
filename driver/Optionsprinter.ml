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
open Json
open Machine
open Printf

let print_list oc name l =
  p_jmember oc name (p_jarray p_jstring) l

let print_clflags oc =
  fprintf oc "{";
  print_list oc "prepro_options" !prepro_options;
  print_list oc "linker_options" !linker_options;
  print_list oc "assembler_options" !assembler_options;
  p_jmember oc "flongdouble" p_jbool !option_flongdouble;
  p_jmember oc "fstruct_passing" p_jbool !option_fstruct_passing;
  p_jmember oc "fbitfields" p_jbool !option_fbitfields;
  p_jmember oc "fvarag_calls" p_jbool !option_fvararg_calls;
  p_jmember oc "funprototyped" p_jbool !option_funprototyped;
  p_jmember oc "fpacked_structs" p_jbool !option_fpacked_structs;
  p_jmember oc "ffpu" p_jbool !option_ffpu;
  p_jmember oc "ffloatconstprop" p_jint !option_ffloatconstprop;
  p_jmember oc "ftailcalls" p_jbool !option_ftailcalls;
  p_jmember oc "fconstprop" p_jbool !option_fconstprop;
  p_jmember oc "fcse" p_jbool !option_fcse;
  p_jmember oc "fredundance" p_jbool !option_fredundancy;
  p_jmember oc "falignfunctions" (p_jopt p_jint) !option_falignfunctions;
  p_jmember oc "falignbranchtargets" p_jint !option_falignbranchtargets;
  p_jmember oc "faligncondbranchs" p_jint !option_faligncondbranchs;
  p_jmember oc "finline_asm" p_jbool !option_finline_asm;
  p_jmember oc "mthumb" p_jbool !option_mthumb;
  p_jmember oc "Osize" p_jbool !option_Osize;
  p_jmember oc "dprepro" p_jbool !option_dprepro;
  p_jmember oc "dparse" p_jbool !option_dparse;
  p_jmember oc "dcmedium" p_jbool !option_dcmedium;
  p_jmember oc "dclight" p_jbool !option_dclight;
  p_jmember oc "dcminor" p_jbool !option_dcminor;
  p_jmember oc "drtl" p_jbool !option_drtl;
  p_jmember oc "dltl" p_jbool !option_dltl;
  p_jmember oc "dalloctrace" p_jbool !option_dalloctrace;
  p_jmember oc "dmach" p_jbool !option_dmach;
  p_jmember oc "dasm" p_jbool !option_dasm;
  p_jmember oc "sdump" p_jbool !option_sdump;
  p_jmember oc "g" p_jbool !option_g;
  p_jmember oc "gdwarf" p_jint !option_gdwarf;
  p_jmember oc "gdepth" p_jint !option_gdepth;
  p_jmember oc "o" (p_jopt p_jstring) !option_o;
  p_jmember oc "E" p_jbool !option_E;
  p_jmember oc "S" p_jbool !option_S;
  p_jmember oc "c" p_jbool !option_c;
  p_jmember oc "v" p_jbool !option_v;
  p_jmember oc "interp" p_jbool !option_interp;
  p_jmember oc "small_data" p_jint !option_small_data;
  p_jmember oc "small_data" p_jint !option_small_const;
  p_jmember oc "timings" p_jbool !option_timings;
  fprintf oc "\n}"

let print_struct_passing_style oc = function
  | Configuration.SP_ref_callee -> p_jstring oc "SP_ref_callee"
  | Configuration.SP_ref_caller -> p_jstring oc "SP_ref_caller"
  | Configuration.SP_split_args -> p_jstring oc "SP_split_args"

let print_struct_return_style oc = function
  | Configuration.SR_int1248 -> p_jstring oc "SR_int1248"
  | Configuration.SR_int1to4 -> p_jstring oc "SR_int1to4"
  | Configuration.SR_int1to8 -> p_jstring oc "SR_int1to8"
  | Configuration.SR_ref -> p_jstring oc "SR_ref"

let print_configurations oc lib_path =
  fprintf oc "{";
  p_jmember oc "arch" p_jstring Configuration.arch;
  p_jmember oc "model" p_jstring Configuration.model;
  p_jmember oc "abi" p_jstring Configuration.abi;
  p_jmember oc "system" p_jstring Configuration.abi;
  print_list oc "prepro" Configuration.prepro;
  print_list oc "asm" Configuration.asm;
  print_list oc "linker" Configuration.linker;
  p_jmember oc "asm_supports_cfi" p_jbool Configuration.asm_supports_cfi;
  p_jmember oc "stdlib_path" p_jstring lib_path;
  p_jmember oc "has_runtime_lib" p_jbool Configuration.has_runtime_lib;
  p_jmember oc "has_standard_headers" p_jbool Configuration.has_standard_headers;
  p_jmember oc "struct_passing_style" print_struct_passing_style Configuration.struct_passing_style;
  p_jmember oc "struct_return_style" print_struct_return_style Configuration.struct_return_style;
  fprintf oc "\n}"

let print_machine oc  =
  fprintf oc "{";
  p_jmember oc "name" p_jstring !config.name;
  p_jmember oc "char_signed" p_jbool !config.char_signed;
  p_jmember oc "sizeof_ptr" p_jint !config.sizeof_ptr;
  p_jmember oc "sizeof_short" p_jint !config.sizeof_short;
  p_jmember oc "sizeof_int" p_jint !config.sizeof_int;
  p_jmember oc "sizeof_long" p_jint !config.sizeof_long;
  p_jmember oc "sizeof_longlong" p_jint !config.sizeof_longlong;
  p_jmember oc "sizeof_float" p_jint !config.sizeof_float;
  p_jmember oc "sizeof_double" p_jint !config.sizeof_double;
  p_jmember oc "sizeof_longdouble" p_jint !config.sizeof_longdouble;
  p_jmember oc "sizeof_void" (p_jopt p_jint) !config.sizeof_void;
  p_jmember oc "sizeof_fun" (p_jopt p_jint) !config.sizeof_fun;
  p_jmember oc "sizeof_wchar" p_jint !config.sizeof_wchar;
  p_jmember oc "wchar_signed" p_jbool !config.wchar_signed;
  p_jmember oc "sizeof_size_t" p_jint !config.sizeof_size_t;
  p_jmember oc "sizeof_ptrdiff_t" p_jint !config.sizeof_ptrdiff_t;
  p_jmember oc "alignof_ptr" p_jint !config.alignof_ptr;
  p_jmember oc "alignof_short" p_jint !config.alignof_short;
  p_jmember oc "alignof_int" p_jint !config.alignof_int;
  p_jmember oc "alignof_long" p_jint !config.alignof_long;
  p_jmember oc "alignof_longlong" p_jint !config.alignof_longlong;
  p_jmember oc "alignof_float" p_jint !config.alignof_float;
  p_jmember oc "alignof_double" p_jint !config.alignof_double;
  p_jmember oc "alignof_longdouble" p_jint !config.alignof_longdouble;
  p_jmember oc "alignof_void" (p_jopt p_jint) !config.alignof_void;
  p_jmember oc "alignof_fun" (p_jopt p_jint) !config.alignof_fun;
  p_jmember oc "bigendian" p_jbool !config.bigendian;
  p_jmember oc "bitfields_msb_first" p_jbool !config.bitfields_msb_first;
  p_jmember oc "supports_unaligned_accesses" p_jbool !config.supports_unaligned_accesses;
  fprintf oc "\n}"

let print file stdlib =
  let oc = open_out file in
  fprintf oc "{";
  p_jmember oc "Version" p_jstring Version.version;
  p_jmember oc "Buildnr" p_jstring Version.buildnr;
  p_jmember oc "Tag" p_jstring Version.tag;
  p_jmember oc "Cwd" p_jstring (Sys.getcwd ());
  fprintf oc "%a:%t" p_jstring "Clflags" print_clflags;
  p_jmember oc "Configurations" print_configurations stdlib;
  fprintf oc "%a:%t" p_jstring "Machine" print_machine;
  fprintf oc "}";
  close_out oc
