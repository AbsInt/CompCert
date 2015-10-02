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

open AST
open C
open Camlcoq
open Cutil
open DebugInformation
open DebugTypes
open DwarfTypes
open DwarfUtil

(* Generate the dwarf DIE's from the information collected in DebugInformation *)

(* Helper function to get values that must be set. *)
let get_opt_val = function
  | Some a -> a
  | None -> assert false

(* Auxiliary data structures and functions *)
module IntSet = Set.Make(struct
  type t = int
  let compare (x:int) (y:int) = compare x y
end)

let rec mmap f env = function
  | [] -> ([],env)
  | hd :: tl ->
      let (hd',env1) = f env hd in
      let (tl', env2) = mmap f env1 tl in
      (hd' :: tl', env2)

let rec mmap_opt f env = function
  | [] -> ([],env)
  | hd :: tl ->
      let (hd',env1) = f env hd in
      let (tl', env2) = mmap_opt f env1 tl in
      begin
        match hd' with
        | Some hd -> (hd :: tl', env2)
        | None -> tl',env2
      end

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

let file_loc_opt file = function
  | None -> None
  | Some (f,l) ->
    try 
      Some (file (f,l))
    with Not_found -> None

let typedef_to_entry file id t =
  let i = get_opt_val t.typ in
  let td = {
    typedef_file_loc = file_loc_opt file t.typedef_file_loc;
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

let enum_to_entry file id e =
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
    enumeration_file_loc = file_loc_opt file e.enum_file_loc;
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
        formal_parameter_location = None;
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
    member_data_member_location =
    (match mem.cfd_byte_offset with 
    | None -> None 
    | Some s -> Some (DataLocBlock (DW_OP_plus_uconst s)));
    member_declaration = None;
    member_name = Some (mem.cfd_name);
    member_type = mem.cfd_typ;
  } in
  new_entry (next_id ()) (DW_TAG_member mem)

let struct_to_entry file id s =
  let tag = {
     structure_file_loc = file_loc_opt file s.ct_file_loc;
     structure_byte_size = s.ct_sizeof;
     structure_declaration = if s.ct_declaration then Some s.ct_declaration else None;
     structure_name = if s.ct_name <> "" then Some s.ct_name else None;
  } in
  let entry = new_entry id (DW_TAG_structure_type tag) in
  let child = List.map member_to_entry s.ct_members in
  add_children entry child

let union_to_entry file id s =
  let tag = {
    union_file_loc =  file_loc_opt file s.ct_file_loc;
    union_byte_size = s.ct_sizeof;
    union_declaration = if s.ct_declaration then Some s.ct_declaration else None;
    union_name = if s.ct_name <> "" then Some s.ct_name else None;
  } in
  let entry = new_entry id (DW_TAG_union_type tag) in
  let child = List.map member_to_entry s.ct_members in
  add_children entry child

let composite_to_entry file id s =
  match s.ct_sou with
  | Struct -> struct_to_entry file id s
  | Union -> union_to_entry file id s

let infotype_to_entry file id = function
  | IntegerType i -> int_type_to_entry id i
  | FloatType f -> float_type_to_entry id f
  | PointerType p -> pointer_to_entry id p
  | ArrayType arr -> array_to_entry id arr
  | CompositeType c -> composite_to_entry file id c
  | EnumType e -> enum_to_entry file id e
  | FunctionType f -> fun_type_to_entry id f
  | Typedef t -> typedef_to_entry file id t
  | ConstType c -> const_to_entry id c
  | VolatileType v -> volatile_to_entry id v
  | Void -> void_to_entry id

let needs_types id d =
  let add_type id d =
    if not (IntSet.mem id d) then
        IntSet.add id d,true
      else 
        d,false in
  let t = Hashtbl.find types id in
  match t with
  | IntegerType _ 
  | FloatType _
  | Void
  | EnumType _ -> d,false
  | Typedef t ->
      add_type (get_opt_val t.typ) d
  | PointerType p -> 
      add_type p.pts d
  | ArrayType arr -> 
      add_type arr.arr_type d
  | ConstType c ->
      add_type c.cst_type d
  | VolatileType v ->
      add_type v.vol_type d
  | FunctionType f ->
      let d,c = match f.fun_return_type with
      | Some t -> add_type t d 
      | None -> d,false in
      List.fold_left (fun (d,c) p ->
        let d,c' = add_type p.param_type d in
        d,c||c') (d,c) f.fun_params
  | CompositeType c -> 
      List.fold_left (fun (d,c) f ->
        let d,c' = add_type f.cfd_typ d in
        d,c||c') (d,false) c.ct_members

let gen_types file needed =
  let rec aux d =
    let d,c = IntSet.fold (fun id (d,c) ->
      let d,c' = needs_types id d in
      d,c||c') d (d,false) in
    if c then
      aux d
    else
      d in
  let typs = aux needed in
  List.rev (Hashtbl.fold (fun id t acc -> 
    if IntSet.mem id typs then
      (infotype_to_entry file id t)::acc
    else 
      acc) types [])

let global_variable_to_entry file acc id v =
  let loc = match v.gvar_atom with
  | Some a when StringSet.mem (extern_atom a) !printed_vars ->
        Some (LocSymbol a)
  | _ -> None in
  let var = {
    variable_file_loc = file v.gvar_file_loc;
    variable_declaration = Some v.gvar_declaration;
    variable_external = Some v.gvar_external;
    variable_name = v.gvar_name;
    variable_type = v.gvar_type;
    variable_location = loc;
  } in
  new_entry id (DW_TAG_variable var),IntSet.add v.gvar_type acc

let gen_splitlong op_hi op_lo =
  let op_piece = DW_OP_piece 4 in
  op_piece::op_hi@(op_piece::op_lo)
  
let translate_function_loc a = function 
  | BA_addrstack (ofs) ->
      let ofs = camlint_of_coqint ofs in
      Some (LocSimple (DW_OP_bregx (a,ofs))),[]
  | BA_splitlong (BA_addrstack hi,BA_addrstack lo)->
      let hi = camlint_of_coqint hi 
      and lo = camlint_of_coqint lo in
      if lo = Int32.add hi 4l then
        Some (LocSimple (DW_OP_bregx (a,hi))),[]
      else
        let op_hi = [DW_OP_bregx (a,hi)]
        and op_lo = [DW_OP_bregx (a,lo)] in
        Some (LocList (gen_splitlong op_hi op_lo)),[]
  | _ -> None,[]
      
let range_entry_loc (sp,l) =
  let rec aux = function
    | BA i ->  [DW_OP_reg i]
    | BA_addrstack ofs -> 
        let ofs = camlint_of_coqint ofs in
        [DW_OP_bregx (sp,ofs)]
    | BA_splitlong (hi,lo) ->
        let hi = aux hi
        and lo = aux lo in
        gen_splitlong hi lo
    | _ -> assert false in
  match aux l with
  | [] -> assert false
  | [a] -> LocSimple a
  | a::rest -> LocList (a::rest)

let location_entry f_id atom =
  try
    begin 
      match (Hashtbl.find var_locations (f_id,atom)) with
      | FunctionLoc (a,r) ->
          translate_function_loc a r
      | RangeLoc l ->
          let l = List.map (fun i -> 
            let hi = get_opt_val i.range_start
            and lo = get_opt_val i.range_end in
            let hi = Hashtbl.find label_translation (f_id,hi)
            and lo = Hashtbl.find label_translation (f_id,lo) in
            hi,lo,range_entry_loc i.var_loc) l in
          let id = next_id () in
        Some (LocRef id),[{loc = l;loc_id = id;}]
    end
  with Not_found -> None,[]

let function_parameter_to_entry f_id (acc,bcc) p =
  let loc,loc_list = location_entry f_id (get_opt_val p.parameter_atom) in
  let p = {
    formal_parameter_file_loc = None;
    formal_parameter_artificial = None;
    formal_parameter_name = Some p.parameter_name;
    formal_parameter_type = p.parameter_type;
    formal_parameter_variable_parameter = None;
    formal_parameter_location = loc;
  } in
  new_entry (next_id ()) (DW_TAG_formal_parameter p),(IntSet.add p.formal_parameter_type acc,loc_list@bcc)

let rec local_variable_to_entry file f_id (acc,bcc) v id =
  match v.lvar_atom with
  | None -> None,(acc,bcc)
  | Some loc ->
      let loc,loc_list = location_entry f_id loc in
      let var = {
        variable_file_loc = file v.lvar_file_loc;
        variable_declaration = None;
        variable_external = None;
        variable_name = v.lvar_name;
        variable_type = v.lvar_type;
        variable_location = loc;
      } in
      Some (new_entry id (DW_TAG_variable var)),(IntSet.add v.lvar_type acc,loc_list@bcc)

and scope_to_entry file f_id acc sc id =
  let l_pc,h_pc = try
    let r = Hashtbl.find scope_ranges id in
    let lbl l = match l with 
    | Some l -> Some (Hashtbl.find label_translation (f_id,l)) 
    | None -> None in
    begin
      match r with
      | [] -> None,None
      | [a] -> lbl a.start_addr, lbl a.end_addr
      | a::rest -> lbl (List.hd (List.rev rest)).start_addr,lbl a.end_addr
    end
  with Not_found -> None,None in
  let scope = {
    lexical_block_high_pc = h_pc;
    lexical_block_low_pc = l_pc;
  } in
  let vars,acc = mmap_opt (local_to_entry file f_id) acc sc.scope_variables in
  let entry = new_entry id (DW_TAG_lexical_block scope) in
  add_children entry vars,acc

and local_to_entry file f_id acc id =
  match Hashtbl.find local_variables id with
  | LocalVariable v -> local_variable_to_entry file f_id acc v id
  | Scope v -> let s,acc = 
      (scope_to_entry file f_id acc v id) in 
    Some s,acc

let fun_scope_to_entries file f_id acc id =
  match id with
  | None -> [],acc
  | Some id ->
      let sc = Hashtbl.find local_variables id in
      (match sc with
      | Scope sc ->mmap_opt (local_to_entry file f_id) acc sc.scope_variables
      | _ -> assert false)

let function_to_entry file (acc,bcc) id f =
  let f_tag = {
    subprogram_file_loc = file f.fun_file_loc;
    subprogram_external = Some f.fun_external;
    subprogram_name = f.fun_name;
    subprogram_prototyped = true;
    subprogram_type = f.fun_return_type;
    subprogram_high_pc = f.fun_high_pc;
    subprogram_low_pc = f.fun_low_pc;
  } in
  let f_id = get_opt_val f.fun_atom in
  let acc = match f.fun_return_type with Some s -> IntSet.add s acc | None -> acc in
  let f_entry =  new_entry id (DW_TAG_subprogram f_tag) in
  let params,(acc,bcc) = mmap (function_parameter_to_entry f_id) (acc,bcc) f.fun_parameter in
  let vars,(acc,bcc) = fun_scope_to_entries file f_id (acc,bcc) f.fun_scope in
  add_children f_entry (params@vars),(acc,bcc)
     
let definition_to_entry file (acc,bcc) id t =
  match t with
  | GlobalVariable g -> let e,acc = global_variable_to_entry file acc id g in
    e,(acc,bcc)
  | Function f -> function_to_entry file (acc,bcc) id f

module StringMap = Map.Make(String)

let diab_file_loc sec (f,l)  =
  Diab_file_loc (Hashtbl.find filenum (sec,f),l)

let gen_diab_debug_info sec_name var_section : debug_entries =
  let defs = Hashtbl.fold (fun id t acc ->
    let s = match t with
    | GlobalVariable _ -> var_section
    | Function f -> sec_name (get_opt_val f.fun_atom) in
    let old = try StringMap.find s acc with Not_found -> [] in
    StringMap.add s ((id,t)::old) acc) definitions StringMap.empty in
  let entries = StringMap.fold (fun s defs acc ->
    let defs,(ty,locs) = List.fold_left (fun (acc,bcc) (id,t) -> 
      let t,bcc = definition_to_entry (diab_file_loc s) bcc id t in
      t::acc,bcc) ([],(IntSet.empty,[])) defs in
    let low_pc = Hashtbl.find compilation_section_start s
    and line_start,debug_start,_ = Hashtbl.find diab_additional s
    and high_pc = Hashtbl.find compilation_section_end s in
    let cp = {
      compile_unit_name = !file_name;
      compile_unit_low_pc = low_pc;
      compile_unit_high_pc = high_pc; 
    } in
    let cp = new_entry (next_id ()) (DW_TAG_compile_unit cp) in
    let cp = add_children cp ((gen_types (diab_file_loc s) ty) @ defs) in
    (s,debug_start,line_start,cp,(low_pc,locs))::acc) defs [] in
  Diab entries

let gnu_file_loc (f,l) =
    Gnu_file_loc ((fst (Hashtbl.find Fileinfo.filename_info f),l))

let gen_gnu_debug_info sec_name var_section : debug_entries =
  let low_pc = Hashtbl.find compilation_section_start ".text"
  and high_pc = Hashtbl.find compilation_section_end ".text" in
  let defs,(ty,locs) = Hashtbl.fold (fun  id t (acc,bcc) -> 
    let t,bcc = definition_to_entry gnu_file_loc bcc id t in
    t::acc,bcc) definitions ([],(IntSet.empty,[])) in
  let types = gen_types gnu_file_loc ty in
  let cp = {
    compile_unit_name = !file_name;
    compile_unit_low_pc = low_pc;
    compile_unit_high_pc = high_pc; 
  } in
  let cp = new_entry (next_id ()) (DW_TAG_compile_unit cp) in
  let cp = add_children cp (types@defs) in
  Gnu (cp,(low_pc,locs))
