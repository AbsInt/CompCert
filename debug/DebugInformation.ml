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

open C

(* This implements an interface for the collection of debugging 
   information. *)

(* Types for the information of type info *)
type composite_field =
    {
     cfd_name:        string;
     cfd_typ:         int;
     cfd_bit_size:    int option;
     cfd_bit_offset:  int option;
     cfd_byte_offset: int option;
     cfd_byte_size:   int option;
   }

type composite_type =
    {
     ct_name:     string;
     ct_file_loc: location option;
     ct_members:  composite_field list;
     ct_alignof:  int option;
     ct_sizeof:   int option;
   }

type ptr_type = {
    pts: int
  }

type array_type = {
    arr_type: int;
    arr_size: int64 option;
  }

type typedef = {
    typedef_name: string;
    typ:          int;
  }

type enumerator = {
    enumerator_file_loc: location option;
    enumerator_name:     string;
    enumerator_const:    int;
  }

type emum_type = {
    enum_name:        string;
    enum_byte_size:   int option;
    enum_file_loc:    location option;
    enum_enumerators: enumerator list; 
  }

type int_type = {
    int_kind: ikind;
  }

type float_type = {
    float_kind: fkind;
  }

type parameter_type = {
    param_type: int;
    param_name: string;
  }

type function_type = {
    fun_return_type: int;
    fun_prototyped:  int;
    fun_params:      parameter_type list;
  }

type debug_types =
  | IntegerType of int_type
  | FloatType of float_type
  | PointerType of ptr_type
  | ArrayType of array_type
  | StructType of composite_type
  | UnionType of composite_type
  | FunctionType of function_type
  | Typedef of typedef

(* All types encountered *)
let all_types: (int,debug_types) Hashtbl.t = Hashtbl.create 7

(* The basetypes, pointer, typedefs and enums all must have names *)
let name_types: (string,int) Hashtbl.t = Hashtbl.create 7

(* Composite types do not need to have a name. We thereore use the stamp for the mapping *)
let composite_types_table: (int, composite_type) Hashtbl.t = Hashtbl.create 7

(* Translate a C.typ to a string needed for hashing *)
let typ_to_string (ty: typ) =
  let buf = Buffer.create 7 in
  let chan = Format.formatter_of_buffer buf in
  Cprint.typ chan ty;
  Format.pp_print_flush chan ();
  Buffer.contents buf
