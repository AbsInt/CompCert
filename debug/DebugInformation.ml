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
open Camlcoq
open Cutil

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
    typ:          int option;
  }

type enumerator = {
    enumerator_file_loc: location option;
    enumerator_name:     string;
    enumerator_const:    int;
  }

type enum_type = {
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
    fun_prototyped:  bool;
    fun_params:      parameter_type list;
  }

type debug_types =
  | IntegerType of int_type
  | FloatType of float_type
  | PointerType of ptr_type
  | ArrayType of array_type
  | StructType of composite_type
  | UnionType of composite_type
  | EnumType of enum_type
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
  let strip =  List.filter (fun a -> a = AConst || a = AVolatile) in 
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
  let insert d_ty ty =
    let id = next_id () 
    and name = typ_to_string ty in
    Hashtbl.add all_types id d_ty;
    Hashtbl.add lookup_types name id;
    id in
  (* We are only interrested in Const and Volatile *)
  let ty = strip_attributes ty in
  let rec typ_aux ty = 
    try find_type ty with
    | Not_found ->
        let d_ty =
          match ty with
          | TVoid _ -> Void
          | TInt (k,_) -> 
              IntegerType ({int_kind = k })
          | TFloat (k,_) ->
              FloatType ({float_kind = k})
          | TPtr (t,_) ->
              let id = attr_aux t in
              PointerType ({pts = id})
          | TArray (t,s,_) ->
              let id = attr_aux t in
              let arr = {
                arr_type = id;
                arr_size= s;
              } in
              ArrayType arr
          | TFun (t,param,va,_) ->
              let param,prot = (match param with 
              | None -> [],false
              | Some p -> List.map (fun (i,t) -> let t = attr_aux t in 
                {
                 param_type = t;
                 param_name = i.name;               
               }) p,true) in
              let ret = attr_aux t in
              let ftype = {
                fun_return_type = ret;
                fun_prototyped = prot;
                fun_params = param;
              } in
              FunctionType ftype
          | TNamed (id,_) ->
              let t = {
                typedef_name = id.name;
                typ = None;
              } in
              Typedef t
          | TStruct (id,_) ->
              let str =
                {
                 ct_name = id.name;
                 ct_file_loc = None;
                 ct_members = [];
                 ct_alignof = None;
                 ct_sizeof = None;
               } in
              StructType str
          | TUnion (id,_) ->
              let union =
                {
                 ct_name = id.name;
                 ct_file_loc = None;
                 ct_members = [];
                 ct_alignof = None;
                 ct_sizeof = None;
               } in
              UnionType union
          | TEnum (id,_) ->
              let enum = 
                {
                 enum_name = id.name;
                 enum_byte_size = None;
                 enum_file_loc = None;
                 enum_enumerators = [];
               } in
              EnumType enum in
        insert d_ty ty
  and attr_aux ty = 
    try
      find_type ty
    with
      Not_found ->
        match strip_last_attribute ty with
        | Some AConst,t -> 
            let id = attr_aux t in
            let const = { const_type = id} in
            insert (ConstType const) ty
        | Some AVolatile,t ->
            let id = attr_aux t in
            let volatile = {volatile_type = id} in
            insert (VolatileType volatile) ty
        | Some (ARestrict|AAlignas _| Attr(_,_)),t ->
            attr_aux t
        | None,t -> typ_aux t
  in
  attr_aux ty

(* Replace the struct information *)
let replace_struct id f =
  let str = Hashtbl.find all_types id in
  match str with
  | StructType comp -> let comp' = f comp in
    if comp <> comp' then Hashtbl.replace all_types id (StructType comp')
  | _ -> assert false (* This should never happen *)

(* Replace the union information *)
let replace_union id f =
  let union = Hashtbl.find all_types id in
  match union with
  | UnionType comp -> let comp' = f comp in
    if comp <> comp' then Hashtbl.replace all_types id (UnionType comp')
  | _ -> assert false (* This should never happen *)

(* Replace the typdef information *)
let replace_typedef id f =
  let typdef = Hashtbl.find all_types id in
  match typdef with
  | Typedef typ -> let typ' = f typ in
    if typ <> typ' then Hashtbl.replace all_types id (Typedef typ')
  | _ -> assert false (* This should never happen *)

(* Types for global definitions *)

(* Information for a global variable *)
type global_variable_information = {
    gvar_name:        string;
    gvar_atom:        atom option;
    gvar_file_loc:    location;
    gvar_declaration: bool;
    gvar_external:    bool;
    gvar_type:        int;
  }

type parameter_information = 
 {
  parameter_name:     string;
  parameter_atom:     atom option;
  parameter_type:     int;
}

type function_information = {
    fun_name:        string;
    fun_atom:        atom option;
    fun_file_loc:    location;
    fun_external:    bool;
    fun_return_type: int option; (* Again the special case of void functions *)
    fun_vararg:      bool;
    fun_parameter:   parameter_information list;
    fun_locals:       int list;
  }

type definition_type =
  | GlobalVariable of global_variable_information
  | Function of function_information

(* All definitions encountered *)
let definitions: (int,definition_type) Hashtbl.t = Hashtbl.create 7

(* Mapping from stamp to debug id *)
let stamp_to_definition: (int,int) Hashtbl.t = Hashtbl.create 7

let find_var_stamp id =
  let id = (Hashtbl.find stamp_to_definition id) in
  let var = Hashtbl.find definitions id in
  match var with
  | GlobalVariable var -> id,var
  |  _ -> assert false

let replace_var id var =
  let var = GlobalVariable var in
  Hashtbl.replace definitions id var

let insert_declaration dec env =
  let insert d_dec stamp =
    let id = next_id () in
    Hashtbl.add definitions id d_dec;
    Hashtbl.add stamp_to_definition stamp id
  in
  match dec.gdesc with
  | Gdecl (sto,id,ty,init) ->
      if  not (is_function_type env ty) then begin
        if not (Hashtbl.mem stamp_to_definition id.stamp)  then begin
          let at_decl,ext = (match sto with
          | Storage_extern -> init = None,true
          | Storage_static -> false,false
          | _ -> false,true) in
          let ty = insert_type ty in
          let decl = {
            gvar_name = id.name;
            gvar_atom = None;
            gvar_file_loc = dec.gloc;
            gvar_declaration = at_decl;
            gvar_external = ext;
            gvar_type = ty;
          } in
          insert (GlobalVariable decl) id.stamp
        end else if init <> None || sto <> Storage_extern then begin (* It is a definition *)
          let id,var = find_var_stamp id.stamp in
          replace_var id ({var with gvar_declaration = false;})
        end
      end
  | Gfundef f -> 
      let ret =  (match f.fd_ret with
      | TVoid _ -> None
      | _ -> Some (insert_type f.fd_ret)) in
      let ext =  (match f.fd_storage with
      | Storage_static -> false
      | _ -> true) in
      let params = List.map (fun (p,ty) ->
        let ty = insert_type ty in
        {
         parameter_name = p.name;
         parameter_atom = None;
         parameter_type = ty;
       }) f.fd_params in
      let fd =
      { 
        fun_name = f.fd_name.name;
        fun_atom = None;
        fun_file_loc = dec.gloc;
        fun_external = ext;
        fun_return_type = ret;
        fun_vararg = f.fd_vararg;
        fun_parameter = params;
        fun_locals = [];
      } in
      insert (Function fd) f.fd_name.stamp
  | Gcompositedecl (Struct,id,at) -> 
      ignore (insert_type (TStruct (id,at)));
      let id = find_type (TStruct (id,[])) in
      replace_struct id (fun comp -> if comp.ct_file_loc = None then
        {comp with ct_file_loc = Some (dec.gloc);}
      else comp)
  | Gcompositedecl (Union,id,at) -> 
      ignore (insert_type (TUnion (id,at)));
      let id = find_type (TUnion (id,[])) in
      replace_union id (fun comp -> if comp.ct_file_loc = None then
        {comp with ct_file_loc = Some (dec.gloc);}
      else comp)
  | Gcompositedef _ -> ()
  | Gtypedef (id,t) -> 
      let id = insert_type (TNamed (id,[])) in
      let tid = insert_type t in
      replace_typedef id (fun typ -> {typ with typ = Some tid;});
  | Genumdef _ -> ()
  | Gpragma _ -> ()
