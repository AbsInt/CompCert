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
open Cutil
open DebugInformation
open DwarfTypes
open DwarfUtil
(* Generate the dwarf DIE's from the information collected in DebugInformation *)

(* Helper function to get values that must be set. *)
let get_opt_val = function
  | Some a -> a
  | None -> assert false

(* Functions to translate the basetypes. *)
let int_type_to_entry id i =
   let encoding =
    (match i.int_kind with
    | IBool -> DW_ATE_boolean
    | IChar ->
        if !Machine.config.Machine.char_signed then 
          DW_ATE_signed_char 
        else 
          DW_ATE_unsigned_char
    | IInt | ILong | ILongLong | IShort | ISChar -> DW_ATE_signed
    | _ -> DW_ATE_unsigned)in
  let int = {
    base_type_byte_size = sizeof_ikind i.int_kind;
    base_type_encoding = Some encoding;
    base_type_name = typ_to_string (TInt (i.int_kind,[]));} in
  new_entry id (DW_TAG_base_type int)

let float_type_to_entry id f = 
  let byte_size = sizeof_fkind f.float_kind in
  let float = {
    base_type_byte_size = byte_size;
    base_type_encoding = Some DW_ATE_float;
    base_type_name = typ_to_string (TFloat (f.float_kind,[]));
  } in
  new_entry id (DW_TAG_base_type float)

let void_to_entry id =
  let void = {
    base_type_byte_size = 0;
    base_type_encoding = None;
    base_type_name = "void";
  } in
  new_entry id (DW_TAG_base_type void)

let typedef_to_entry id t =
  let i = get_opt_val t.typ in
  let td = {
    typedef_file_loc = t.typedef_file_loc;
    typedef_name = t.typedef_name;
    typedef_type = i;
  } in
  new_entry id (DW_TAG_typedef td) 

let pointer_to_entry id p =
  let p = {pointer_type = p.pts} in
  new_entry id (DW_TAG_pointer_type p)

let array_to_entry id arr =
  let arr_tag = {
    array_type_file_loc = None;
    array_type = arr.arr_type;
  } in
  let arr_entry = new_entry id (DW_TAG_array_type arr_tag) in
  let children = List.map (fun a ->
    let r = match a with
    | None -> None
    | Some i ->
        let bound = Int64.to_int (Int64.sub i Int64.one) in
        Some (BoundConst bound) in
    let s = {
       subrange_type = None;
       subrange_upper_bound = r;
    } in
    new_entry (next_id ()) (DW_TAG_subrange_type s)) arr.arr_size in
  add_children arr_entry children

let const_to_entry id c =
  new_entry id (DW_TAG_const_type ({const_type = c.cst_type}))

let volatile_to_entry id v =
  new_entry id (DW_TAG_volatile_type ({volatile_type = v.vol_type}))

let enum_to_entry id e =
  let enumerator_to_entry e =
    let tag =
      {
       enumerator_file_loc = None;
       enumerator_value = Int64.to_int (e.enumerator_const);
       enumerator_name = e.enumerator_name;
     } in
    new_entry (next_id ()) (DW_TAG_enumerator tag) in
  let bs = sizeof_ikind enum_ikind in
  let enum = {
    enumeration_file_loc = e.enum_file_loc;
    enumeration_byte_size = bs;
    enumeration_declaration = Some false;
    enumeration_name = Some e.enum_name;
  } in
  let enum = new_entry id (DW_TAG_enumeration_type enum) in
  let child = List.map enumerator_to_entry e.enum_enumerators in
  add_children enum child

let fun_type_to_entry id f =
  let children = if f.fun_prototyped then
    let u = {
      unspecified_parameter_file_loc = None;
      unspecified_parameter_artificial = None;
    } in
    [new_entry (next_id ()) (DW_TAG_unspecified_parameter u)]
  else
    List.map (fun p ->
      let fp = {
        formal_parameter_file_loc = None;
        formal_parameter_artificial = None;
        formal_parameter_name = if p.param_name <> "" then Some p.param_name else None;
        formal_parameter_type = p.param_type;
        formal_parameter_variable_parameter = None;
      } in
      new_entry (next_id ()) (DW_TAG_formal_parameter fp)) f.fun_params;
  in
  let s = {
    subroutine_type = f.fun_return_type;
    subroutine_prototyped = f.fun_prototyped
  } in
  let s = new_entry id (DW_TAG_subroutine_type s) in
  add_children s children

let member_to_entry mem =
  let mem = {
    member_file_loc = None;
    member_byte_size = mem.cfd_byte_size;
    member_bit_offset = mem.cfd_bit_offset;
    member_bit_size = mem.cfd_bit_size;
    member_data_member_location = Some (DataLocBlock [DW_OP_plus_uconst (get_opt_val mem.cfd_byte_offset)]);
    member_declaration = None;
    member_name = Some (mem.cfd_name);
    member_type = mem.cfd_typ;
  } in
  new_entry (next_id ()) (DW_TAG_member mem)

let struct_to_entry id s =
  let tag = {
     structure_file_loc = s.ct_file_loc;
     structure_byte_size = s.ct_sizeof;
     structure_declaration = Some s.ct_declaration;
     structure_name = if s.ct_name <> "" then Some s.ct_name else None;
  } in
  let entry = new_entry id (DW_TAG_structure_type tag) in
  let child = List.map member_to_entry s.ct_members in
  add_children entry child

let union_to_entry id s =
  let tag = {
    union_file_loc = s.ct_file_loc;
    union_byte_size = s.ct_sizeof;
    union_declaration = Some s.ct_declaration;
    union_name = if s.ct_name <> "" then Some s.ct_name else None;
  } in
  let entry = new_entry id (DW_TAG_union_type tag) in
  let child = List.map member_to_entry s.ct_members in
  add_children entry child

let composite_to_entry id s =
  match s.ct_sou with
  | Struct -> struct_to_entry id s
  | Union -> union_to_entry id s

let infotype_to_entry id = function
  | IntegerType i -> int_type_to_entry id i
  | FloatType f -> float_type_to_entry id f
  | PointerType p -> pointer_to_entry id p
  | ArrayType arr -> array_to_entry id arr
  | CompositeType c -> composite_to_entry id c
  | EnumType e -> enum_to_entry id e
  | FunctionType f -> fun_type_to_entry id f
  | Typedef t -> typedef_to_entry id t
  | ConstType c -> const_to_entry id c
  | VolatileType v -> volatile_to_entry id v
  | Void -> void_to_entry id

let gen_types () =
  List.rev (Hashtbl.fold (fun id t acc -> (infotype_to_entry id t)::acc) types [])

let global_variable_to_entry id v =
  let var = {
    variable_file_loc = v.gvar_file_loc;
    variable_declaration = Some v.gvar_declaration;
    variable_external = Some v.gvar_external;
    variable_name = v.gvar_name;
    variable_type = v.gvar_type;
    variable_location = match v.gvar_atom with Some a -> Some (LocSymbol a) | None -> None;
  } in
  new_entry id (DW_TAG_variable var)

let function_parameter_to_entry p =
  let p = {
    formal_parameter_file_loc = None;
    formal_parameter_artificial = None;
    formal_parameter_name = Some p.parameter_name;
    formal_parameter_type = p.parameter_type;
    formal_parameter_variable_parameter = None;
  } in
  new_entry (next_id ()) (DW_TAG_formal_parameter p)

let function_to_entry id f =
  let f_tag = {
    subprogram_file_loc = f.fun_file_loc;
    subprogram_external = Some f.fun_external;
    subprogram_name = f.fun_name;
    subprogram_prototyped = true;
    subprogram_type = f.fun_return_type;
    subprogram_high_pc = f.fun_high_pc;
    subprogram_low_pc = f.fun_low_pc;
  } in
 let f_entry =  new_entry id (DW_TAG_subprogram f_tag) in
 let child = List.map function_parameter_to_entry f.fun_parameter in
 add_children f_entry child
     
let definition_to_entry id t =
  match t with
  | GlobalVariable g -> global_variable_to_entry id g
  | Function f -> function_to_entry id f

let gen_defs () =
  List.rev (Hashtbl.fold (fun id t acc -> (definition_to_entry id t)::acc) definitions [])

let gen_debug_info () =
  let cp =  {
    compile_unit_name = !file_name;
  } in
  let cp = new_entry (next_id ()) (DW_TAG_compile_unit cp) in
  add_children cp ((gen_types ()) @ (gen_defs ()))
