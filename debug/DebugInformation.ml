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

(* Simple id generator *)
let id = ref 0

let next_id () =
  let nid = !id in
  incr id; nid

let reset_id () =
  id := 0


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

type const_type = {
    const_type: int
  }

type volatile_type = {
    volatile_type: int
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
  | ConstType of const_type
  | VolatileType of volatile_type
  | Void

(* All types encountered *)
let all_types: (int,debug_types) Hashtbl.t = Hashtbl.create 7

(* Lookup table for types *)
let lookup_types: (string, int) Hashtbl.t = Hashtbl.create 7

(* Translate a C.typ to a string needed for hashing *)
let typ_to_string (ty: typ) =
  let buf = Buffer.create 7 in
  let chan = Format.formatter_of_buffer buf in
  let old = !Cprint.print_idents_in_full in
  Cprint.print_idents_in_full := true;
  Cprint.typ chan ty;
  Cprint.print_idents_in_full := old;
  Format.pp_print_flush chan ();
  Buffer.contents buf

(* Helper functions for the attributes *)
let strip_attributes typ =
  let strip = List.filter (fun a -> a = AConst || a = AVolatile) in 
  match typ with
  | TVoid at -> TVoid (strip at)
  | TInt (k,at) ->  TInt (k,strip at)
  | TFloat (k,at) -> TFloat(k,strip at)
  | TPtr (t,at) -> TPtr(t,strip at)
  | TArray (t,s,at) -> TArray(t,s,strip at)
  | TFun (t,arg,v,at) -> TFun(t,arg,v,strip at)
  | TNamed (n,at) -> TNamed(n,strip at)
  | TStruct (n,at) -> TStruct(n,strip at)
  | TUnion (n,at) -> TUnion(n,strip at)
  | TEnum (n,at) -> TEnum(n,strip at)

let strip_last_attribute typ  = 
  let rec hd_opt l = match l with
    [] -> None,[]
  | AConst::rest -> Some AConst,rest
  | AVolatile::rest -> Some AVolatile,rest 
  | _::rest -> hd_opt rest in
  match typ with
  | TVoid at -> let l,r = hd_opt at in
    l,TVoid r
  | TInt (k,at) -> let l,r = hd_opt at in
    l,TInt (k,r)
  | TFloat (k,at) -> let l,r = hd_opt at in
    l,TFloat (k,r)
  | TPtr (t,at) -> let l,r = hd_opt at in
    l,TPtr(t,r)
  | TArray (t,s,at) -> let l,r = hd_opt at in
    l,TArray(t,s,r)
  | TFun (t,arg,v,at) -> let l,r = hd_opt at in
    l,TFun(t,arg,v,r)
  | TNamed (n,at) -> let l,r = hd_opt at in
    l,TNamed(n,r)
  | TStruct (n,at) -> let l,r = hd_opt at in
    l,TStruct(n,r)
  | TUnion (n,at) -> let l,r = hd_opt at in
    l,TUnion(n,r)
  | TEnum (n,at) -> let l,r = hd_opt at in
    l,TEnum(n,r)

(* Does the type already exist? *)
let exist_type (ty: typ) =
  (* We are only interrested in Const and Volatile *)
  let ty = strip_attributes ty in
  Hashtbl.mem lookup_types (typ_to_string ty)

(* Find the type id to an type *)
let find_type (ty: typ) =
  (* We are only interrested in Const and Volatile *)
  let ty = strip_attributes ty in
  Hashtbl.find lookup_types (typ_to_string ty)

(* Add type and information *)
let insert_type (ty: typ) = 
  (* We are only interrested in Const and Volatile *)
  let ty = strip_attributes ty in
  if not (exist_type ty) then
    begin
      let rec typ_aux ty = ()
      and attr_aux ty = 
        match strip_last_attribute ty with
        | Some AConst,t -> 
            ()
        | None,t -> typ_aux t
      in
      attr_aux ty
    end
