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

module StringSet = Set.Make(String)

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

module type TARGET =
    sig
      val file_loc: string * int -> file_loc
      val string_entry: string -> string_const
    end

type dwarf_accu =
    {
     typs:  IntSet.t;
     locs:   location_entry list;
     ranges: int * dw_ranges
   }

let up_typs acc t =
  {acc with typs = IntSet.add t acc.typs;}

let up_locs acc loc =
  {acc with locs = loc@acc.locs;}

let up_ranges acc r =
  {acc with ranges = r;}

let empty_accu =
  {
   typs = IntSet.empty;
   locs = [];
   ranges = 0,[]
 }

module Dwarfgenaux (Target: TARGET) =
  struct

    include Target

    let name_opt n = if n <> "" then Some (string_entry n) else None

    let subrange_type : int option ref = ref None

    let encoding_of_ikind = function
      | IBool -> DW_ATE_boolean
      | IChar ->
          if !Machine.config.Machine.char_signed then
            DW_ATE_signed_char
          else
            DW_ATE_unsigned_char
      | IInt | ILong | ILongLong | IShort | ISChar -> DW_ATE_signed
      | _ -> DW_ATE_unsigned

    (* Functions to translate the basetypes. *)
    let int_type_to_entry id i =
      let encoding = encoding_of_ikind i.int_kind in
      let int = {
        base_type_byte_size = sizeof_ikind i.int_kind;
        base_type_encoding = Some encoding;
        base_type_name = string_entry (typ_to_string (TInt (i.int_kind,[])));
      } in
      new_entry id (DW_TAG_base_type int)

    let float_type_to_entry id f =
      let byte_size = sizeof_fkind f.float_kind in
      let float = {
        base_type_byte_size = byte_size;
        base_type_encoding = Some DW_ATE_float;
        base_type_name = string_entry (typ_to_string (TFloat (f.float_kind,[])));
      } in
      new_entry id (DW_TAG_base_type float)

    let void_to_entry id =
      let void = {
        base_type_byte_size = 0;
        base_type_encoding = None;
        base_type_name = string_entry "void";
      } in
      new_entry id (DW_TAG_base_type void)

    let file_loc_opt = function
      | None -> None
      | Some (f,l) ->
          try
            Some (file_loc (f,l))
          with Not_found -> None

    let typedef_to_entry id t =
      let i = get_opt_val t.typ in
      let td = {
        typedef_file_loc = file_loc_opt t.td_file_loc;
        typedef_name = string_entry t.td_name;
        typedef_type = i;
      } in
      new_entry id (DW_TAG_typedef td)

    let pointer_to_entry id p =
      let p = {pointer_type = p.pts} in
      new_entry id (DW_TAG_pointer_type p)

    let array_to_entry id arr =
      let arr_tag = {
        array_type = arr.arr_type;
      } in
      let arr_entry = new_entry id (DW_TAG_array_type arr_tag) in
      let children = List.map (fun a ->
        let r = match a with
        | None -> None
        | Some i ->
            if i <> 0L then
              let bound = Int64.to_int (Int64.sub i Int64.one) in
              Some (BoundConst bound)
            else
              None in
        let st = match !subrange_type with
        | None -> let id = next_id () in
          subrange_type := Some id;
          id
        | Some id  -> id in
        let s = {
          subrange_type = st;
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
           enumerator_value = Int64.to_int (e.e_const);
           enumerator_name = string_entry e.e_name;
         } in
        new_entry (next_id ()) (DW_TAG_enumerator tag) in
      let bs = sizeof_ikind enum_ikind in
      let enum = {
        enumeration_file_loc = file_loc_opt e.enum_file_loc;
        enumeration_byte_size = bs;
        enumeration_declaration = Some false;
        enumeration_name = string_entry e.enum_name;
      } in
      let enum = new_entry id (DW_TAG_enumeration_type enum) in
      let children = List.map enumerator_to_entry e.enum_enumerators in
      add_children enum children

    let fun_type_to_entry id f =
      let children = if not f.fun_type_prototyped then
        let u = {
          unspecified_parameter_artificial = None;
        } in
        [new_entry (next_id ()) (DW_TAG_unspecified_parameter u)]
      else
        List.map (fun p ->
          let fp = {
            formal_parameter_artificial = None;
            formal_parameter_name = None;
            formal_parameter_type = p.param_type;
            formal_parameter_variable_parameter = None;
            formal_parameter_location = None;
          } in
          new_entry (next_id ()) (DW_TAG_formal_parameter fp)) f.fun_type_params;
      in
      let s = {
        subroutine_type = f.fun_type_return_type;
        subroutine_prototyped = f.fun_type_prototyped
      } in
      let s = new_entry id (DW_TAG_subroutine_type s) in
      add_children s children

    let member_to_entry mem =
      let mem = {
        member_byte_size = mem.cfd_byte_size;
        member_bit_offset = mem.cfd_bit_offset;
        member_bit_size = mem.cfd_bit_size;
        member_data_member_location =
        (match mem.cfd_byte_offset with
        | None -> None
        | Some s -> Some (DataLocBlock (DW_OP_plus_uconst s)));
        member_declaration = None;
        member_name = if mem.cfd_anon then None else Some (string_entry mem.cfd_name);
        member_type = mem.cfd_typ;
      } in
      new_entry (next_id ()) (DW_TAG_member mem)

    let struct_to_entry id s =
      let tag = {
        structure_file_loc = file_loc_opt s.ct_file_loc;
        structure_byte_size = s.ct_sizeof;
        structure_declaration = if s.ct_declaration then Some s.ct_declaration else None;
        structure_name = name_opt s.ct_name;
      } in
      let entry = new_entry id (DW_TAG_structure_type tag) in
      let child = List.map member_to_entry s.ct_members in
      add_children entry child

    let union_to_entry id s =
      let tag = {
        union_file_loc =  file_loc_opt s.ct_file_loc;
        union_byte_size = s.ct_sizeof;
        union_declaration = if s.ct_declaration then Some s.ct_declaration else None;
        union_name = name_opt s.ct_name;
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

    let needs_types id d =
      let add_type id d =
        if not (IntSet.mem id d) then
          IntSet.add id d,true
        else
          d,false in
      let t = get_type id in
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
          let d,c = match f.fun_type_return_type with
          | Some t -> add_type t d
          | None -> d,false in
          List.fold_left (fun (d,c) p ->
            let d,c' = add_type p.param_type d in
            d,c||c') (d,c) f.fun_type_params
      | CompositeType c ->
          List.fold_left (fun (d,c) f ->
            let d,c' = add_type f.cfd_typ d in
            d,c||c') (d,false) c.ct_members

    let gen_types needed =
      let rec aux d =
        let d,c = IntSet.fold (fun id (d,c) ->
          let d,c' = needs_types id d in
          d,c||c') d (d,false) in
        if c then
          aux d
        else
          d in
      let typs = aux needed in
      let res =
        List.rev (fold_types (fun id t acc ->
          if IntSet.mem id typs then
            (infotype_to_entry id t)::acc
          else
            acc) []) in
      match !subrange_type with
      | None -> res
      | Some id ->
          let encoding = encoding_of_ikind (Cutil.size_t_ikind ()) in
          let tag = {
            base_type_byte_size = !Machine.config.Machine.sizeof_size_t;
            base_type_encoding = Some encoding;
            base_type_name = string_entry "sizetype";
          } in
          (new_entry id (DW_TAG_base_type tag))::res

    let global_variable_to_entry acc id v =
      let loc = match v.gvar_atom with
      | Some a when is_variable_printed (extern_atom a) ->
          Some (LocSymbol a)
      | _ -> None in
      let var = {
        variable_file_loc = file_loc v.gvar_file_loc;
        variable_declaration = Some v.gvar_declaration;
        variable_external = Some v.gvar_external;
        variable_name = string_entry v.gvar_name;
        variable_type = v.gvar_type;
        variable_location = loc;
      } in
      let acc = up_typs acc v.gvar_type in
      new_entry id (DW_TAG_variable var),acc

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
      if !Clflags.option_gdepth > 2 then
        try
          begin
            match variable_location f_id atom with
            | FunctionLoc (a,r) ->
                translate_function_loc a r
            | RangeLoc l ->
                let l = List.rev_map (fun i ->
                  let hi = get_opt_val i.range_start
                  and lo = get_opt_val i.range_end in
                  let hi = translate_label f_id hi
                  and lo = translate_label f_id lo in
                  hi,lo,range_entry_loc i.var_loc) l in
                let id = next_id () in
                Some (LocRef id),[{loc = l;loc_id = id;}]
          end
        with Not_found -> None,[]
      else
        None,[]

    let function_parameter_to_entry f_id acc p =
      let loc,loc_list = match p.parameter_atom with
      | None -> None,[]
      | Some p -> location_entry f_id p in
      let p = {
        formal_parameter_artificial = None;
        formal_parameter_name = name_opt p.parameter_name;
        formal_parameter_type = p.parameter_type;
        formal_parameter_variable_parameter = None;
        formal_parameter_location = loc;
      } in
      let acc = up_locs (up_typs acc p.formal_parameter_type) loc_list in
      new_entry (next_id ()) (DW_TAG_formal_parameter p),acc

    let scope_range f_id id (o,dwr) =
      try
        let r = get_scope_ranges id in
        let lbl l h = match l,h with
        | Some l,Some h->
            let l = translate_label f_id l
            and h = translate_label f_id h in
            l,h
        | _ -> raise Not_found in
        begin
          match r with
          | [] -> Empty,(o,dwr)
          | [a] ->
              let l,h = lbl a.start_addr a.end_addr in
              Pc_pair (l,h),(o,dwr)
          | a::rest ->
              if !Clflags.option_gdwarf > 2 then
                let r = List.map (fun e -> lbl e.start_addr e.end_addr) r in
                (Offset o), (o + 2 + 4 * (List.length r),r::dwr)
              else
                let l,h = lbl (List.hd (List.rev rest)).start_addr a.end_addr in
                Pc_pair (l,h),(o,dwr)
        end
      with Not_found -> Empty,(o,dwr)

    let rec local_variable_to_entry f_id acc v id =
      match v.lvar_atom with
      | None -> None,acc
      | Some loc ->
          let loc,loc_list = location_entry f_id loc in
          let var = {
            variable_file_loc = file_loc v.lvar_file_loc;
            variable_declaration = None;
            variable_external = None;
            variable_name = string_entry v.lvar_name;
            variable_type = v.lvar_type;
            variable_location = loc;
          } in
          let acc = up_locs (up_typs acc v.lvar_type)  loc_list in
          Some (new_entry id (DW_TAG_variable var)),acc

    and scope_to_entry f_id acc sc id =
      let r,dwr = scope_range f_id id acc.ranges in
      let scope = {
        lexical_block_range = r;
      } in
      let acc = up_ranges acc dwr in
      let vars,acc = mmap_opt (local_to_entry  f_id) acc sc.scope_variables in
      let entry = new_entry id (DW_TAG_lexical_block scope) in
      add_children entry vars,acc

    and local_to_entry f_id acc id =
      match get_local_variable id with
      | LocalVariable v -> local_variable_to_entry f_id acc v id
      | Scope v -> let s,acc = (scope_to_entry f_id acc v id) in
        Some s,acc

    let fun_scope_to_entries f_id acc id =
      match id with
      | None -> [],acc
      | Some id ->
          let sc = get_local_variable id in
          (match sc with
          | Scope sc -> mmap_opt (local_to_entry f_id) acc sc.scope_variables
          | _ -> assert false)

    let function_to_entry acc id f =
      let r = match f.fun_low_pc, f.fun_high_pc with
      | Some l,Some h -> Pc_pair (l,h)
      | _ -> Empty in
      let f_tag = {
        subprogram_file_loc = file_loc f.fun_file_loc;
        subprogram_external = Some f.fun_external;
        subprogram_name = string_entry f.fun_name;
        subprogram_prototyped = true;
        subprogram_type = f.fun_return_type;
        subprogram_range = r;
      } in
      let f_id = get_opt_val f.fun_atom in
      let acc = match f.fun_return_type with Some s -> up_typs acc s | None -> acc in
      let f_entry =  new_entry id (DW_TAG_subprogram f_tag) in
      let children,acc =
        if !Clflags.option_gdepth > 1 then
          let params,acc = mmap (function_parameter_to_entry f_id) acc f.fun_parameter in
          let vars,acc = fun_scope_to_entries f_id acc f.fun_scope in
          params@vars,acc
        else
          [],acc in
      add_children f_entry (children),acc

    let definition_to_entry acc id t =
      match t with
      | GlobalVariable g -> global_variable_to_entry acc id g
      | Function f -> function_to_entry acc id f

  end

module StringMap = Map.Make(String)

let diab_file_loc sec (f,l)  =
  Diab_file_loc ((diab_file_loc sec f),l)

let prod_name =
  let version_string =
    if Version.buildnr <> "" && Version.tag <> "" then
      Printf.sprintf "%s, Build: %s, Tag: %s" Version.version Version.buildnr Version.tag
    else
      Version.version in
  Printf.sprintf "AbsInt Angewandte Informatik GmbH:CompCert Version %s:(%s,%s,%s,%s)"
    version_string Configuration.arch Configuration.system Configuration.abi Configuration.model

let diab_gen_compilation_section s defs acc =
  let module Gen = Dwarfgenaux(struct
    let file_loc = diab_file_loc s
    let string_entry s =  Simple_string s
  end) in
  let defs,accu = List.fold_left (fun (acc,bcc) (id,t) ->
    let t,bcc = Gen.definition_to_entry bcc id t in
    t::acc,bcc) ([],empty_accu) defs in
  let low_pc = section_start s
  and line_start,debug_start = diab_additional_section s
  and high_pc = section_end s in
  let cp = {
    compile_unit_name = Simple_string !file_name;
    compile_unit_range = Pc_pair (low_pc,high_pc);
    compile_unit_dir = Simple_string (Sys.getcwd ());
    compile_unit_prod_name = Simple_string prod_name
  } in
  let cp = new_entry (next_id ()) (DW_TAG_compile_unit cp) in
  let cp = add_children cp ((Gen.gen_types accu.typs) @ defs) in
  {
    section_name = s;
    start_label = debug_start;
    line_label = line_start;
    entry = cp;
    dlocs = Some low_pc,accu.locs;
  }::acc

let gen_diab_debug_info sec_name var_section : debug_entries =
  let defs = fold_definitions (fun id t acc ->
    let s = match t with
    | GlobalVariable _ -> var_section
    | Function f -> sec_name (get_opt_val f.fun_atom) in
    let old = try StringMap.find s acc with Not_found -> [] in
    StringMap.add s ((id,t)::old) acc) StringMap.empty in
  let entries = StringMap.fold diab_gen_compilation_section defs [] in
  Diab entries

let gnu_file_loc (f,l) =
  Gnu_file_loc ((fst (Hashtbl.find Fileinfo.filename_info f),l))

let string_table: (string,int) Hashtbl.t = Hashtbl.create 7

let gnu_string_entry s =
  if (String.length s < 4 && Configuration.system <> "macosx") (* macosx needs debug_str *)
  || Configuration.system = "cygwin" then (*Cygwin does not use the debug_str seciton*)
    Simple_string s
  else
    try
      Offset_string ((Hashtbl.find string_table s),s)
    with Not_found ->
      let id = next_id () in
      Hashtbl.add string_table s id;
      Offset_string (id,s)


let gen_gnu_debug_info sec_name var_section : debug_entries =
  Hashtbl.clear string_table;
  let r,dwr,low_pc =
    try if !Clflags.option_gdwarf > 3 then
        let pcs  = fold_section_start (fun s low acc ->
          (low,section_end s)::acc) [] in
        match pcs with
        | [] ->  Empty,(0,[]),None
        | [(l,h)] ->   Pc_pair (l,h),(0,[]),Some l
        | _ -> Offset 0,(2 + 4 * (List.length pcs),[pcs]),None
    else
        let l = section_start ".text"
        and h = section_end ".text" in
        Pc_pair(l,h),(0,[]),Some l
    with Not_found ->  Empty,(0,[]),None in
  let accu = up_ranges empty_accu dwr in
  let module Gen = Dwarfgenaux (struct
    let file_loc = gnu_file_loc
    let string_entry = gnu_string_entry
  end) in
  let defs,accu,sec = fold_definitions (fun  id t (acc,bcc,sec) ->
    let s = match t with
    | GlobalVariable _ -> var_section
    | Function f -> sec_name (get_opt_val f.fun_atom) in
    let t,bcc = Gen.definition_to_entry bcc id t in
    t::acc,bcc,StringSet.add s sec) ([],accu,StringSet.empty) in
  let types = Gen.gen_types accu.typs in
  let cp = {
    compile_unit_name = gnu_string_entry !file_name;
    compile_unit_range = r;
    compile_unit_dir = gnu_string_entry (Sys.getcwd ());
    compile_unit_prod_name = gnu_string_entry prod_name;
  } in
  let cp = new_entry (next_id ()) (DW_TAG_compile_unit cp) in
  let cp = add_children cp (types@defs) in
  let loc_pc = if StringSet.cardinal sec > 1 then None else low_pc in
  let string_table = Hashtbl.fold (fun s i acc -> (i,s)::acc) string_table [] in
  Gnu (cp,(loc_pc,accu.locs),string_table,snd accu.ranges)
