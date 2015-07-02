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

open Builtins
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

(* Get the type id of a composite_type *)
let get_composite_type (name: string): int =
  try 
    Hashtbl.find composite_types_table name
  with Not_found ->
    let id = next_id () in
    Hashtbl.add composite_types_table name id;
    id

(* Translate a C.typ to a string needed for hashing *)
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

(*  Dwarf tag for the void type*)
let rec void_dwarf_tag =
  let void = {
    base_type_byte_size = 0;
    base_type_encoding = None;
    base_type_name = "void";
  } in
  DW_TAG_base_type void

(* Generate a dwarf tag for the given integer type *)
and int_to_dwarf_tag k =  
  let encoding =
    (match k with
    | IBool -> DW_ATE_boolean
    | IChar ->
        if !Machine.config.Machine.char_signed then 
          DW_ATE_signed_char 
        else 
          DW_ATE_unsigned_char
    | ILong | ILongLong | IShort | ISChar -> DW_ATE_signed_char
    | _ -> DW_ATE_unsigned)in
  let int = {
    base_type_byte_size = sizeof_ikind k;
    base_type_encoding = Some encoding;
    base_type_name = typ_to_string (TInt (k,[]));} in
  DW_TAG_base_type int

(* Generate a dwarf tag for the given floating point type *)
and float_to_dwarf_tag k = 
  let byte_size = sizeof_fkind k in
  let float = {
    base_type_byte_size = byte_size;
    base_type_encoding = Some DW_ATE_float;
    base_type_name = typ_to_string (TFloat (k,[]));
  } in
  DW_TAG_base_type float

(* Generate a dwarf tag for the given function type *)
and fun_to_dwarf_tag rt args =
  let ret,et = (match rt with
  | TVoid _ -> None,[]
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
  s.id,((s::others)@et)

(* Generate a dwarf tag for the given array type *)
and array_to_dwarf_tag child size = 
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
  arr.id,(arr::e)

(* Translate a typ without attributes to a dwarf_tag *)
and type_to_dwarf_entry typ typ_string=
   let id,entries = 
   (match typ with
   | TVoid _ -> 
       let e = new_entry void_dwarf_tag in
       e.id,[e]
   | TInt (k,_) ->
       let e = new_entry (int_to_dwarf_tag k) in
       e.id,[e]
   | TFloat (k,_) ->
       let e = new_entry (float_to_dwarf_tag k) in
       e.id,[e]
   | TPtr (t,_) ->
       let t,e = type_to_dwarf t in
       let pointer = {pointer_type = t;} in
       let t = new_entry (DW_TAG_pointer_type pointer) in
       t.id,t::e
   | TFun (rt,args,_,_) -> fun_to_dwarf_tag rt args
   | TStruct (i,_)
   | TUnion (i,_)
   | TEnum (i,_) ->
       let t = get_composite_type i.name in
       t,[]
   | TNamed (i,at) ->
       let t = Hashtbl.find typedef_table i.name in
       t,[]
   | TArray (child,size,_) -> array_to_dwarf_tag child size)         
   in
   Hashtbl.add type_table typ_string id;
   id,entries

(* Tranlate type with attributes to their corresponding dwarf represenation *)
and attr_type_to_dwarf typ typ_string =
  let l,t = strip_last_attribute typ in
  match l with
  | Some AConst -> let id,t = type_to_dwarf t in
    let const_tag = DW_TAG_const_type ({const_type = id;}) in
    let const_entry = new_entry const_tag in
    let id = const_entry.id in
    Hashtbl.add type_table typ_string id;
    id,const_entry::t
  | Some AVolatile -> let id,t = type_to_dwarf t in 
    let volatile_tag = DW_TAG_volatile_type ({volatile_type = id;}) in
    let volatile_entry = new_entry volatile_tag in
    let id = volatile_entry.id in
    Hashtbl.add type_table typ_string id;
    id,volatile_entry::t
  | Some (ARestrict|AAlignas _| Attr(_,_)) -> type_to_dwarf t (* This should not happen *)
  | None -> type_to_dwarf_entry typ typ_string
        
(* Translate a given type to its dwarf representation *)
and type_to_dwarf (typ: typ): int * dw_entry list =
  let typ = strip_attributes typ in
  let typ_string = typ_to_string typ in
  try
    Hashtbl.find type_table typ_string,[]
  with Not_found ->
    attr_type_to_dwarf typ typ_string

(* Translate a typedef to its corresponding dwarf representation *)
let typedef_to_dwarf gloc (name,t) =
  let i,t = type_to_dwarf t in
  Hashtbl.add typedef_table name i;
  let td = {
    typedef_file_loc = gloc;
    typedef_name = name;
    typedef_type = i;
  } in 
  let td = new_entry (DW_TAG_typedef td) in
  td::t     

(* Translate a global var to its corresponding dwarf representation *)
let glob_var_to_dwarf (s,n,t,_) gloc =
   let i,t = type_to_dwarf t in
   let at_decl = (match s with
   | Storage_extern -> true
   | _ -> false) in
   let ext = (match s with
   | Storage_static -> false
   | _ -> true) in
   let decl = {
     variable_file_loc = (Some gloc);
     variable_declaration = Some at_decl;
     variable_external = Some ext;
     variable_location = None;
     variable_name = n.name;
     variable_segment = None;
     variable_type = i;
   } in
   let decl = new_entry (DW_TAG_variable decl) in
   t,decl

(* Translate a function definition to its corresponding dwarf representation *)
let fundef_to_dwarf f gloc =
  let ret,e = (match f.fd_ret with
  | TVoid _ -> None,[]
  | _ -> let i,t = type_to_dwarf f.fd_ret in
    Some i,t) in
  let ext = (match f.fd_storage with
  | Storage_static -> false
  | _ -> true) in
  let fdef = {
    subprogram_file_loc = (Some gloc);
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
  e,fdef

(* Translate a enum definition to its corresponding dwarf representation *)
let enum_to_dwarf (n,at,e) gloc =
  let enumerator_to_dwarf (i,c,_)=
    let tag =      
      {
       enumerator_file_loc = None;
       enumerator_value = Int64.to_int c;
       enumerator_name = i.name;
     } in
    new_entry (DW_TAG_enumerator tag) in
  let bs = sizeof_ikind enum_ikind in
  let enum = {
    enumeration_file_loc = Some gloc;
    enumeration_byte_size = bs;
    enumeration_declaration = Some false;
    enumeration_name = n.name;
  } in
  let id = get_composite_type n.name in
  let child = List.map enumerator_to_dwarf e in
  let enum = 
    {
     tag = DW_TAG_enumeration_type enum;
     children = child;
     id = id;
   } in
  [enum]
  
(* Translate a struct definition to its corresponding dwarf representation *)
let struct_to_dwarf (n,at,m) env gloc =
  let info = Env.find_struct env n in
  let tag =DW_TAG_structure_type {
    structure_file_loc = Some gloc;
    structure_byte_size = info.ci_sizeof;
    structure_declaration = Some false;
    structure_name = n.name;
  } in
  let id = get_composite_type n.name in
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
  let children,e = List.rev children,e in
  let sou = {
    tag = tag;
    children = children;
    id = id;} in
  sou::e

(* Translate a union definition to its corresponding dwarf representation *)
let union_to_dwarf (n,at,m) env gloc = 
  let info = Env.find_union env n in
  let tag = DW_TAG_union_type {
    union_file_loc = Some gloc;
    union_byte_size = info.ci_sizeof;
    union_declaration = Some false;
    union_name = n.name;
  } in
  let id = get_composite_type n.name in
  let children,e = mmap 
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
        new_entry (DW_TAG_member um),e@acc)[] m in
  let sou = {
    tag = tag;
    children = children;
    id = id;} in
  sou::e

(* Translate global declarations to there dwarf representation *)
let globdecl_to_dwarf env (typs,decls) decl =
  PrintAsmaux.add_file (fst decl.gloc);
  match decl.gdesc with
  | Gtypedef (n,t) -> let ret = typedef_to_dwarf (Some decl.gloc) (n.name,t)  in
    typs@ret,decls
  | Gdecl d -> let t,d = glob_var_to_dwarf d decl.gloc in
    typs@t,d::decls
  | Gfundef f ->   let t,d = fundef_to_dwarf f decl.gloc in
    typs@t,d::decls
  | Genumdef (n,at,e) ->let ret = enum_to_dwarf (n,at,e) decl.gloc in
    typs@ret,decls
  | Gcompositedef (Struct,n,at,m) -> let ret = struct_to_dwarf (n,at,m) env decl.gloc in
    typs@ret,decls
  | Gcompositedef (Union,n,at,m) -> let ret = union_to_dwarf (n,at,m) env decl.gloc in
    typs@ret,decls
  | Gcompositedecl _
  | Gpragma _ -> typs,decls       

(* Compute the dwarf representations of global declarations. The second program argument is the 
   program after the bitfield and packed struct transformation *)
let program_to_dwarf prog prog1 name =
  Hashtbl.reset type_table;
  Hashtbl.reset composite_types_table;
  Hashtbl.reset typedef_table;
  let prog = cleanupGlobals (prog) in
  let env = translEnv Env.empty prog1 in
  reset_id ();
  let typs = List.map (typedef_to_dwarf None) C2C.builtins.typedefs in
  let typs = List.concat typs in
  let typs,defs = List.fold_left (globdecl_to_dwarf env) (typs,[]) prog in
  let defs = typs @ defs in
  let cp = {
    compile_unit_name = name;
  } in
  let cp = new_entry (DW_TAG_compile_unit cp) in
  add_children cp defs
