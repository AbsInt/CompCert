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
open Cprint
open DwarfTypes
open DwarfUtil
open Machine

(* Functions to translate a C Ast into Dwarf 2 debugging information *)


(* Hashtable from type name to entry id *)
let type_table: (string, int) Hashtbl.t = Hashtbl.create 7

(* Hashtable from typedefname to entry id *)
let defined_types_table: (string, int) Hashtbl.t = Hashtbl.create 7

let typ_to_string (ty: typ) =
  let buf = Buffer.create 7 in
  let chan = Format.formatter_of_buffer buf in
  typ chan ty;
  Format.pp_print_flush chan ();
  Buffer.contents buf

let rec mmap f env = function
  | [] -> ([],env)
  | hd :: tl ->
      let (hd',env1) = f env hd in
      let (tl', env2) = mmap f env1 tl in
      (hd' :: tl', env2)

let rec type_to_dwarf (typ: typ): int * dw_entry list =
  let typ_string = typ_to_string typ in
  try
    Hashtbl.find type_table typ_string,[]
  with Not_found ->
    let attr_to_dw attr_list id entries =
      List.fold_left (fun (id,entry) attr ->
        match attr with
        | AConst -> let const_tag = DW_TAG_const_type ({const_type = id;}) in
          let const_entry = new_entry const_tag in
          const_entry.id,const_entry::entry
        | AVolatile ->  let volatile_tag = DW_TAG_volatile_type ({volatile_type = id;}) in
          let volatile_entry = new_entry volatile_tag in
          volatile_entry.id,volatile_entry::entry
        | ARestrict 
        | AAlignas _
        | Attr _ -> id,entry) (id,entries) (List.rev attr_list) in
    let attr_to_dw_tag attr_list tag =
      let entry = new_entry tag in
      attr_to_dw attr_list entry.id [entry] in
    let id,entries = 
      match typ with
      | TVoid at -> let void = {
          base_type_byte_size = 0;
          base_type_encoding = None;
          base_type_name = "void";
        } in
        attr_to_dw_tag at (DW_TAG_base_type void)
      | TInt (k,at) ->
          let byte_size,encoding,name =
            (match k with
            | IBool -> 1,DW_ATE_boolean,"_Bool" 
            | IChar -> 1,(if !config.char_signed then DW_ATE_signed_char else DW_ATE_unsigned_char),"char" 
            | ISChar -> 1,DW_ATE_signed_char,"signed char"
            | IUChar -> 1,DW_ATE_unsigned_char,"unsigned char"
            | IInt -> !config.sizeof_int,DW_ATE_signed,"signed int"
            | IUInt -> !config.sizeof_int,DW_ATE_unsigned,"unsigned int"
            | IShort -> !config.sizeof_short,DW_ATE_signed,"signed short"
            | IUShort -> !config.sizeof_short,DW_ATE_unsigned,"unsigned short"
            | ILong -> !config.sizeof_long, DW_ATE_signed,"long"
            | IULong -> !config.sizeof_long, DW_ATE_unsigned,"unsigned long"
            | ILongLong -> !config.sizeof_longlong, DW_ATE_signed,"long long"
            | IULongLong -> !config.sizeof_longlong, DW_ATE_unsigned,"unsigned long long")in
          let int = {
            base_type_byte_size = byte_size;
            base_type_encoding = Some encoding;
            base_type_name = name;} in
          attr_to_dw_tag at (DW_TAG_base_type int)
      | TFloat (k,at) ->
          let byte_size,name =
            (match k with
            | FFloat -> !config.sizeof_float,"float"
            | FDouble -> !config.sizeof_double,"double"
            | FLongDouble -> !config.sizeof_longdouble,"long double") in
          let float = {
            base_type_byte_size = byte_size;
            base_type_encoding = Some DW_ATE_float;
            base_type_name = name;
          } in
          attr_to_dw_tag at (DW_TAG_base_type float)
      | TPtr (t,at) ->
          let t,e = type_to_dwarf t in
          let pointer = {pointer_type = t;} in
          let t,e2 = attr_to_dw_tag at (DW_TAG_pointer_type pointer) in
          t,e2@e
      | TFun (rt,args,_,at) ->
          let ret,et = (match rt with
          | TVoid _ -> None,[] (* Void return *)
          | _ -> let ret,et = type_to_dwarf rt in
            Some ret,et) in
          let prototyped,children,others =
            (match args with 
            | None -> 
                let u = {
                  unspecified_parameter_file_loc = None;
                  unspecified_parameter_artificial = None;
                } in
                let u = new_entry (DW_TAG_unspecified_parameter u) in 
                false,[u],[]
            | Some [] -> true,[],[]
            | Some l ->
                let c,e = mmap (fun acc (_,t) ->
                  let t,e = type_to_dwarf t in
                  let fp =
                    {
                     formal_parameter_file_loc = None;
                     formal_parameter_artificial = None;
                     formal_parameter_location = None;
                     formal_parameter_name = None;
                     formal_parameter_segment = None;
                     formal_parameter_type = t;
                     formal_parameter_variable_parameter = None;
                   } in
                  let entry = new_entry (DW_TAG_formal_parameter fp) in
                  entry,(e@acc)) [] l in
                true,c,e) in
          let s = {
            subroutine_type = ret;
            subroutine_prototyped = prototyped;
          } in
          let s = new_entry (DW_TAG_subroutine_type s) in
          let s = add_children s children in
          attr_to_dw at s.id ((s::others)@et)
      | TStruct (i,at)
      | TUnion (i,at)
      | TEnum (i,at)
      | TNamed (i,at) ->
          let t = Hashtbl.find defined_types_table i.name in
          attr_to_dw at t []
      | TArray (child,size,at) ->
          let size_to_subrange s =
            let b = (match s with 
            | None -> None
            | Some i ->
                let i = Int64.to_int i in
                Some (BoundConst i)) in
            let s = {
              subrange_type = None;
              subrange_upper_bound = b;
            } in
            new_entry (DW_TAG_subrange_type s) in 
          let rec aux t = 
            (match t with
            | TArray (child,size,_) ->
                let sub = size_to_subrange size in
                let t,c,e = aux child in
                t,sub::c,e
            | _ -> let t,e = type_to_dwarf t in
            t,[],e) in
          let t,children,e = aux child in
          let sub = size_to_subrange size in
          let children = List.rev (sub::children) in
          let arr = {
            array_type_file_loc = None;
            array_type = t;
          } in
          let arr = new_entry (DW_TAG_array_type arr) in
          let arr = add_children arr children in
          attr_to_dw at arr.id (arr::e)          
    in
    Hashtbl.add type_table typ_string id;
    id,entries
        
let rec globdecl_to_dwarf decl =
  match decl.gdesc with
  | Gtypedef (n,t) -> let i,t = type_to_dwarf t in
    Hashtbl.add defined_types_table n.name i;
    t
  | Gpragma _ 
  | _ ->  []

let program_to_dwarf prog name =
  Hashtbl.reset type_table;
  Hashtbl.reset defined_types_table;
  reset_id ();
  let defs = List.concat (List.map globdecl_to_dwarf prog) in
  let cp = {
    compile_unit_name = name;
  } in
  let cp = new_entry (DW_TAG_compile_unit cp) in
  add_children cp defs
