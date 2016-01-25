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
open Printf

let print_member oc name p_mem mem =
  fprintf oc "\n%a:%a" p_jstring name p_mem mem

let print_list oc name l =
  print_member oc name (p_jarray p_jstring) l

let print oc ((): unit) =
  fprintf oc "{";
  print_list oc "Preprocessor Options" !prepro_options;
  print_list oc "Linker Options" !linker_options;
  print_list oc "Assembler Options" !assembler_options;
  print_member oc "Flongdouble" p_jbool !option_flongdouble;
  print_member oc "Fstruct_passing" p_jbool !option_fstruct_passing;
  print_member oc "Fbitfields" p_jbool !option_fbitfields;
  print_member oc "Fvarag_calls" p_jbool !option_fvararg_calls;
  print_member oc "Funprototyped" p_jbool !option_funprototyped;
  print_member oc "Fpacked_structs" p_jbool !option_fpacked_structs;
  print_member oc "Ffpu" p_jbool !option_ffpu;
  print_member oc "Ffloatconstprop" p_jint !option_ffloatconstprop;
  print_member oc "Ftailcalls" p_jbool !option_ftailcalls;
  print_member oc "Fconstprop" p_jbool !option_fconstprop;
  print_member oc "Fcse" p_jbool !option_fcse;
  print_member oc "Fredundance" p_jbool !option_fredundancy;
  
  fprintf oc "\n}"
