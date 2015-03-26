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
open Cutil
open C2C
open DwarfTypes
open DwarfUtil
open Env

(* Functions to translate a C Ast into Dwarf 2 debugging information *)


(* Hashtable from type name to entry id *)
let type_table: (string, int) Hashtbl.t = Hashtbl.create 7

(* Hashtable for typedefname to entry id *)
let typedef_table: (string, int) Hashtbl.t = Hashtbl.create 7

(* Hashtable from composite table to entry id *)
let composite_types_table: (string, int) Hashtbl.t = Hashtbl.create 7

let get_composite_type (name: string): int =
  try 
    Hashtbl.find composite_types_table name
  with Not_found ->
    let id = next_id () in
    Hashtbl.add composite_types_table name id;
    id


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
    | Attr _ -> id,entry) (id,entries) (List.rev attr_list)
let attr_to_dw_tag attr_list tag =
  let entry = new_entry tag in
  attr_to_dw attr_list entry.id [entry]


let rec type_to_dwarf (typ: typ): int * dw_entry list =
  let typ_string = typ_to_string typ in
  try
    Hashtbl.find type_table typ_string,[]
  with Not_found ->
    let id,entries = 
      match typ with
      | TVoid at -> let void = {
          base_type_byte_size = 0;
          base_type_encoding = None;
          base_type_name = "void";
        } in
        attr_to_dw_tag at (DW_TAG_base_type void)
      | TInt (k,at) ->
          let encoding =
            (match k with
            | IBool -> DW_ATE_boolean
            | IChar -> (if !Machine.config.Machine.char_signed then DW_ATE_signed_char else DW_ATE_unsigned_char) 
            | ILong | ILongLong | IShort | ISChar -> DW_ATE_signed_char
            | _ -> DW_ATE_unsigned)in
          let int = {
            base_type_byte_size = sizeof_ikind k;
            base_type_encoding = Some encoding;
            base_type_name = typ_string;} in
          attr_to_dw_tag at (DW_TAG_base_type int)
      | TFloat (k,at) ->
          let byte_size = sizeof_fkind k in
          let float = {
            base_type_byte_size = byte_size;
            base_type_encoding = Some DW_ATE_float;
            base_type_name = typ_string;
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
      | TEnum (i,at) ->
          let t = get_composite_type i.name in
          attr_to_dw at t []
      | TNamed (i,at) ->
          let t = Hashtbl.find typedef_table i.name in
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
        
let rec globdecl_to_dwarf env decl =
  match decl.gdesc with
  | Gtypedef (n,t) ->
      let i,t = type_to_dwarf t in
      Hashtbl.add typedef_table n.name i;
      let td = {
        typedef_file_loc = Some (decl.gloc);
        typedef_name = n.name;
        typedef_type = i;
      } in 
      let td = new_entry (DW_TAG_typedef td) in
      td::t     
  | Gdecl (s,n,t,_) ->
      let i,t = type_to_dwarf t in
      let at_decl = (match s with
      | Storage_extern -> true
      | _ -> false) in
      let ext = (match s with
      | Storage_static -> false
      | _ -> true) in
      let decl = {
        variable_file_loc = (Some decl.gloc);
        variable_declaration = Some at_decl;
        variable_external = Some ext;
        variable_location = None;
        variable_name = n.name;
        variable_segment = None;
        variable_type = i;
      } in
      let decl = new_entry (DW_TAG_variable decl) in
      decl::t
  | Gfundef f -> 
      let ret,e = (match f.fd_ret with
      | TVoid _ -> None,[]
      | _ -> let i,t = type_to_dwarf f.fd_ret in
        Some i,t) in
      let ext = (match f.fd_storage with
      | Storage_static -> false
      | _ -> true) in
      let fdef = {
        subprogram_file_loc = (Some decl.gloc);
        subprogram_external = Some ext;
        subprogram_frame_base = None;
        subprogram_name = f.fd_name.name;
        subprogram_prototyped = true;
        subprogram_type = ret;
      } in
      let fp,e =  mmap (fun acc (p,t) ->
        let t,e = type_to_dwarf t in
        let fp =
          {
           formal_parameter_file_loc = None;
           formal_parameter_artificial = None;
           formal_parameter_location = None;
           formal_parameter_name = (Some p.name);
           formal_parameter_segment = None;
           formal_parameter_type = t;
           formal_parameter_variable_parameter = None;
         } in
        let entry = new_entry (DW_TAG_formal_parameter fp) in
        entry,(e@acc)) e f.fd_params in
      let fdef = new_entry (DW_TAG_subprogram fdef) in
      let fdef = add_children fdef fp in
      fdef::e
  | Genumdef (n,at,e) -> 
      let bs = sizeof_ikind enum_ikind in
      let enum = {
        enumeration_file_loc = Some decl.gloc;
        enumeration_byte_size = bs;
        enumeration_declaration = Some false;
        enumeration_name = n.name;
      } in
      let id = get_composite_type n.name in
      let child = List.map (fun (i,c,_) ->
        new_entry (DW_TAG_enumerator (
                   {
                    enumerator_file_loc = None;
                    enumerator_value = Int64.to_int c;
                    enumerator_name = i.name;
                  }))) e in
      let enum = 
        {
         tag = DW_TAG_enumeration_type enum;
         children = child;
         id = id;} in
      [enum]
  | Gcompositedef (sou,n,at,m) ->
      let tag = (match sou with
      | Struct ->
          let info = Env.find_struct env n in
          DW_TAG_structure_type {
          structure_file_loc = Some decl.gloc;
          structure_byte_size = info.ci_sizeof;
          structure_declaration = Some false;
          structure_name = n.name;
        }
      | Union ->
          let info = Env.find_union env n in
          DW_TAG_union_type {
          union_file_loc = Some decl.gloc;
          union_byte_size = info.ci_sizeof;
          union_declaration = Some false;
          union_name = n.name;
        }) in
      let id = get_composite_type n.name in
      let children,e = 
        (match sou with
        | Struct -> 
            (* This is the same layout used in Cutil *)
            let rec pack acc bcc l m =
              match m with
              | [] -> acc,bcc,[]
              | m::ms as ml ->
                 (match m.fld_bitfield with
                 | None -> acc,bcc,ml
                 | Some n ->
                     if n = 0 then
                       acc,bcc,ms (* bit width 0 means end of pack *)
                     else if l + n > 8 * !Machine.config.Machine.sizeof_int then
                       acc,bcc,ml (* doesn't fit in current word *)
                     else
                       let t,e = type_to_dwarf m.fld_typ in
                       let um = {
                        member_file_loc = None;
                        member_byte_size = Some !Machine.config.Machine.sizeof_int;
                        member_bit_offset = Some l;
                        member_bit_size = Some n;
                        member_data_member_location = None;
                        member_declaration = None;
                        member_name = m.fld_name;
                        member_type = t;
                      } in
                       pack ((new_entry (DW_TAG_member um))::acc) (e@bcc) (l + n) ms)
            and translate acc bcc m =
              match m with
                [] -> acc,bcc
              | m::ms as ml ->
                  (match m.fld_bitfield with
                  | None -> 
                      let t,e = type_to_dwarf m.fld_typ in
                      let um = {
                        member_file_loc = None;
                        member_byte_size = None;
                        member_bit_offset = None;
                        member_bit_size = None;
                        member_data_member_location = None;
                        member_declaration = None;
                        member_name = m.fld_name;
                        member_type = t;
                      } in
                      translate ((new_entry (DW_TAG_member um))::acc) (e@bcc) ms
                  | Some _ -> let acc,bcc,rest = pack acc bcc 0 ml in 
                    translate acc bcc rest)
            in
            let children,e = translate [] []  m in
            List.rev children,e
        | Union -> mmap 
              (fun  acc f ->
                let t,e = type_to_dwarf f.fld_typ in
                let um = {
                  member_file_loc = None;
                  member_byte_size = None;
                  member_bit_offset = None;
                  member_bit_size = None;
                  member_data_member_location = None;
                  member_declaration = None;
                  member_name = f.fld_name;
                  member_type = t;
               } in
                new_entry (DW_TAG_member um),e@acc)[] m) in
      let sou = {
        tag = tag;
        children = children;
        id = id;} in
      sou::e
  | Gcompositedecl _
  | Gpragma _ -> []       

let add_size prog debug =
  let env = translEnv Env.empty prog in
  entry_map (function
    | DW_TAG_structure_type s ->
        let _,info = Env.lookup_struct env s.structure_name in
        DW_TAG_structure_type {s with structure_byte_size = info.ci_sizeof;}
    | DW_TAG_union_type u ->
        let _,info = Env.lookup_union env u.union_name in
        DW_TAG_union_type {u with union_byte_size = info.ci_sizeof;}
    | e -> e) debug

let program_to_dwarf prog prog1 name =
  Hashtbl.reset type_table;
  Hashtbl.reset composite_types_table;
  Hashtbl.reset typedef_table;
  let prog = cleanupGlobals (prog) in
  let env = translEnv Env.empty prog1 in
  reset_id ();
  let defs = List.concat (List.map (globdecl_to_dwarf env) prog) in
  let cp = {
    compile_unit_name = name;
  } in
  let cp = new_entry (DW_TAG_compile_unit cp) in
  add_children cp defs
