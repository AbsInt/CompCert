(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Emulation of #pragma pack (experimental) *)

open Printf
open Machine
open C
open Cutil
open Env
open Cerrors
open Transform

type field_info = {
  fi_offset: int;                       (* byte offset within struct *)
  fi_swap: bool                         (* true if byte-swapped *)
}

(* Mapping from struct name to size.
   Only packed structs are mentioned in this table. *)

let packed_structs : (ident, int) Hashtbl.t = Hashtbl.create 17

(* Mapping from (struct name, field name) to field_info.
   Only fields of packed structs are mentioned in this table. *)

let packed_fields : (ident * string, field_info) Hashtbl.t
                  = Hashtbl.create 57

(* The current packing parameters.  The first two are 0 if packing is
   turned off. *)

let max_field_align = ref 0
let min_struct_align = ref 0
let byte_swap_fields = ref false

(* Alignment *)

let is_pow2 n =
  n > 0 && n land (n - 1) = 0

let align x boundary =
  assert (is_pow2 boundary);
  (x + boundary - 1) land (lnot (boundary - 1))

(* What are the types that can be byte-swapped? *)

let rec can_byte_swap env ty =
  match unroll env ty with
  | TInt(ik, _) -> (sizeof_ikind ik <= 4, sizeof_ikind ik > 1)
  | TEnum(_, _) -> (true, sizeof_ikind enum_ikind > 1)
  | TPtr(_, _) -> (true, true)          (* tolerance? *)
  | TArray(ty_elt, _, _) -> can_byte_swap env ty_elt
  | _ -> (false, false)

(* Compute size and alignment of a type, taking "aligned" attributes
   into account *)

let sizeof_alignof loc env ty =
  match sizeof env ty, alignof env ty with
  | Some sz, Some al ->
      begin match find_custom_attributes ["aligned"; "__aligned__"]
                                      (attributes_of_type env ty) with
      | [] ->
          (sz, al)
      | [[AInt n]] when is_pow2 (Int64.to_int n) ->
          let al' = max al (Int64.to_int n) in
          (align sz al', al')
      | _ ->
          warning "%a: Warning: Ill-formed 'aligned' attribute, ignored"
                  formatloc loc;
          (sz, al)
      end
  | _, _ ->
      error "%a: Error: struct field has incomplete type" formatloc loc;
      (0, 1)

(* Layout algorithm *)

let layout_struct mfa msa swapped loc env struct_id fields =
  let rec layout max_al pos = function
  | [] ->
      (max_al, pos)
  | f :: rem -> 
      if f.fld_bitfield <> None then
        error "%a: Error: bitfields in packed structs not allowed"
              formatloc loc;
      let (sz, al) = sizeof_alignof loc env f.fld_typ in
      let swap =
        if swapped then begin
          let (can_swap, must_swap) = can_byte_swap env f.fld_typ in
          if not can_swap then
            error "%a: Error: cannot byte-swap field of type '%a'"
                  formatloc loc Cprint.typ f.fld_typ;
          must_swap
        end else false in
      let al1 = min al mfa in
      let pos1 = align pos al1 in
      Hashtbl.add packed_fields
         (struct_id, f.fld_name)
         {fi_offset = pos1; fi_swap = swap};
      let pos2 = pos1 + sz in
      layout (max max_al al1) pos2 rem in
  let (al, sz) = layout 1 0 fields in
  if al >= msa then
    (0, sz)
  else
    (msa, align sz msa)

(* Rewriting of struct declarations *)

let payload_field sz =
  { fld_name = "__payload";
    fld_typ = TArray(TInt(IUChar, []), Some(Int64.of_int sz), []);
    fld_bitfield = None}

let transf_composite loc env su id attrs ml =
  match su with
  | Union -> (attrs, ml)
  | Struct ->
      let (mfa, msa, swapped) =
        if !max_field_align > 0 then
          (!max_field_align, !min_struct_align, !byte_swap_fields)
        else if find_custom_attributes ["packed";"__packed__"] attrs <> [] then
          (1, 0, false)
        else
          (0, 0, false) in
      if mfa = 0 then (attrs, ml) else begin
        let (al, sz) = layout_struct mfa msa swapped loc env id ml in
        Hashtbl.add packed_structs id sz;
        let attrs =
          if al = 0 then attrs else
            add_attributes [Attr("__aligned__", [AInt(Int64.of_int al)])] attrs
        and field =
          payload_field sz
        in (attrs, [field])
      end

(* Accessor functions *)

let lookup_function loc env name =
  match Env.lookup_ident env name with
  | (id, II_ident(sto, ty)) -> (id, ty)
  | (id, II_enum _) -> raise (Env.Error(Env.Unbound_identifier name))

(* Type for the access *)

let accessor_type loc env ty =
  match unroll env ty with
  | TInt(ik,_) -> (8 * sizeof_ikind ik, TInt(unsigned_ikind_of ik,[]))
  | TEnum(_,_) -> (8 * sizeof_ikind enum_ikind, TInt(unsigned_ikind_of enum_ikind,[]))
  | TPtr _     -> (8 * !config.sizeof_ptr, TInt(ptr_t_ikind,[]))
  | _ ->
     error "%a: unsupported type for byte-swapped field access" formatloc loc;
     (32, TVoid [])

(*  (ty) e *)
let ecast ty e = {edesc = ECast(ty, e); etyp = ty}

let ecast_opt env ty e =
  if compatible_types env ty e.etyp then e else ecast ty e

(*  *e  *)
let ederef ty e = {edesc = EUnop(Oderef, e); etyp = ty}

(*  e + n *)
let eoffset e n =
  {edesc = EBinop(Oadd, e, intconst (Int64.of_int n) IInt, e.etyp);
   etyp = e.etyp}

(*  *((ty * ) (base.__payload + offset))  *)
let dot_packed_field base pf ty =
  let payload =
    {edesc = EUnop(Odot "__payload", base);
     etyp = TArray(TInt(IChar,[]),None,[]) } in
  ederef ty (ecast (TPtr(ty, [])) (eoffset payload pf.fi_offset))

(*  *((ty * ) (base->__payload + offset))  *)
let arrow_packed_field base pf ty =
  let payload =
    {edesc = EUnop(Oarrow "__payload", base);
     etyp = TArray(TInt(IChar,[]),None,[]) } in
  ederef ty (ecast (TPtr(ty, [])) (eoffset payload pf.fi_offset))

(*  (ty) __builtin_readNN_reversed(&lval)
 or (ty) __builtin_bswapNN(lval) *)

let use_reversed =
  match !Machine.config.Machine.name with
  | "powerpc" -> true
  | _ -> false

let bswap_read loc env lval =
  let ty = lval.etyp in
  let (bsize, aty) = accessor_type loc env ty in
  assert (bsize = 16 || bsize = 32);
  try
    if use_reversed then begin
      let (id, fty) =
        lookup_function loc env (sprintf "__builtin_read%d_reversed" bsize) in
      let fn = {edesc = EVar id; etyp = fty} in
      let args = [ecast_opt env (TPtr(aty,[])) (eaddrof lval)] in
      let call = {edesc = ECall(fn, args); etyp = aty} in
      ecast_opt env ty call
    end else begin
      let (id, fty) =
        lookup_function loc env (sprintf "__builtin_bswap%d" bsize) in
      let fn = {edesc = EVar id; etyp = fty} in
      let args = [ecast_opt env aty lval] in
      let call = {edesc = ECall(fn, args); etyp = aty} in
      ecast_opt env ty call
    end
  with Env.Error msg ->
    fatal_error "%a: Error: %s" formatloc loc (Env.error_message msg)

(*  __builtin_write_intNN_reversed(&lhs,rhs)
  or  lhs = __builtin_bswapNN(rhs) *)

let bswap_write loc env lhs rhs =
  let ty = lhs.etyp in
  let (bsize, aty) =
    accessor_type loc env ty in
  assert (bsize = 16 || bsize = 32);
  try
    if use_reversed then begin
      let (id, fty) =
        lookup_function loc env (sprintf "__builtin_write%d_reversed" bsize) in
      let fn = {edesc = EVar id; etyp = fty} in
      let args = [ecast_opt env (TPtr(aty,[])) (eaddrof lhs); 
                  ecast_opt env aty rhs] in
      {edesc = ECall(fn, args); etyp = TVoid[]}
    end else begin
      let (id, fty) =
        lookup_function loc env (sprintf "__builtin_bswap%d" bsize) in
      let fn = {edesc = EVar id; etyp = fty} in
      let args = [ecast_opt env aty rhs] in
      let call = {edesc = ECall(fn, args); etyp = aty} in
      eassign lhs (ecast_opt env ty call)
    end
  with Env.Error msg ->
    fatal_error "%a: Error: %s" formatloc loc (Env.error_message msg)

(* Expressions *)

let transf_expr loc env ctx e =

  let is_packed_access ty fieldname =
    match unroll env ty with
    | TStruct(id, _) ->
        (try Some(Hashtbl.find packed_fields (id, fieldname))
         with Not_found -> None)
    | _ -> None in

  let is_packed_access_ptr ty fieldname =
    match unroll env ty with
    | TPtr(ty', _) -> is_packed_access ty' fieldname
    | _ -> None in 

  (* Transformation of l-values.  Return transformed expr plus
     [true] if l-value is a byte-swapped field and [false] otherwise. *)
  let rec lvalue e =
    match e.edesc with
    | EUnop(Odot fieldname, e1) ->
        let e1' = texp Val e1 in
        begin match is_packed_access e1.etyp fieldname with
        | None ->
            ({edesc = EUnop(Odot fieldname, e1'); etyp = e.etyp}, false)
        | Some pf ->
            (dot_packed_field e1' pf e.etyp, pf.fi_swap)
        end
    | EUnop(Oarrow fieldname, e1) ->
        let e1' = texp Val e1 in
        begin match is_packed_access_ptr e1.etyp fieldname with
        | None ->
            ({edesc = EUnop(Oarrow fieldname, e1'); etyp = e.etyp}, false)
        | Some pf ->
            (arrow_packed_field e1' pf e.etyp, pf.fi_swap)
        end
    | EBinop(Oindex, e1, e2, tyres) ->
        let (e1', swap) = lvalue e1 in
        ({edesc = EBinop(Oindex, e1', e2, tyres); etyp = e.etyp}, swap)
    | _ ->
        (texp Val e, false) 

  and texp ctx e =
    match e.edesc with
    | EConst _ -> e
    | ESizeof _ -> e
    | EAlignof _ -> e
    | EVar _ -> e

    | EUnop(Odot _, _) | EUnop(Oarrow _, _) | EBinop(Oindex, _, _, _) ->
        let (e', swap) = lvalue e in
        if swap then bswap_read loc env e' else e'

    | EUnop(Oaddrof, e1) ->
        let (e1', swap) = lvalue e1 in
        if swap then
          error "%a: Error: & over byte-swapped field" formatloc loc;
        {edesc = EUnop(Oaddrof, e1'); etyp = e.etyp}

    | EUnop((Opreincr|Opredecr) as op, e1) ->
        let (e1', swap) = lvalue e1 in
        if swap then
          expand_preincrdecr
            ~read:(bswap_read loc env) ~write:(bswap_write loc env)
            env ctx op e1'
        else
          {edesc = EUnop(op, e1'); etyp = e.etyp}

    | EUnop((Opostincr|Opostdecr as op), e1) ->
        let (e1', swap) = lvalue e1 in
        if swap then
          expand_postincrdecr
            ~read:(bswap_read loc env) ~write:(bswap_write loc env)
            env ctx op e1'
        else
          {edesc = EUnop(op, e1'); etyp = e.etyp}

    | EUnop(op, e1) ->
        {edesc = EUnop(op, texp Val e1); etyp = e.etyp}

    | EBinop(Oassign, e1, e2, ty) ->
        let (e1', swap) = lvalue e1 in
        let e2' = texp Val e2 in
        if swap then
          expand_assign ~write:(bswap_write loc env) env ctx e1' e2'
        else
          {edesc = EBinop(Oassign, e1', e2', ty); etyp = e.etyp}

    | EBinop((Oadd_assign|Osub_assign|Omul_assign|Odiv_assign|Omod_assign|
              Oand_assign|Oor_assign|Oxor_assign|Oshl_assign|Oshr_assign as op),
              e1, e2, ty) ->
        let (e1', swap) = lvalue e1 in
        let e2' = texp Val e2 in
        if swap then
          expand_assignop
            ~read:(bswap_read loc env) ~write:(bswap_write loc env)
            env ctx op e1' e2' ty
        else
          {edesc = EBinop(op, e1', e2', ty); etyp = e.etyp}

    | EBinop(Ocomma, e1, e2, ty) ->
        {edesc = EBinop(Ocomma, texp Effects e1, texp Val e2, ty);
         etyp = e.etyp}

    | EBinop(op, e1, e2, ty) ->
        {edesc = EBinop(op, texp Val e1, texp Val e2, ty); etyp = e.etyp}

    | EConditional(e1, e2, e3) ->
        {edesc = EConditional(texp Val e1, texp ctx e2, texp ctx e3);
         etyp = e.etyp}

    | ECast(ty, e1) ->
        {edesc = ECast(ty, texp Val e1); etyp = e.etyp}

    | ECall(e1, el) ->
        {edesc = ECall(texp Val e1, List.map (texp Val) el); etyp = e.etyp}

  in texp ctx e

(* Statements *)

let transf_stmt env s =
  Transform.stmt transf_expr env s

(* Functions *)

let transf_fundef env f =
  Transform.fundef transf_stmt env f

(* Initializers *)

let extract_byte env e i =
  let ty = unary_conversion env e.etyp in
  let e1 =
    if i = 0 then e else
      { edesc = EBinop(Oshr, e, intconst (Int64.of_int (i*8)) IInt, ty);
        etyp = ty } in
  { edesc = EBinop(Oand, e1, intconst 0xFFL IInt, ty); etyp = ty }

let init_packed_struct loc env struct_id struct_sz initdata =

  let new_initdata = Array.make struct_sz (Init_single (intconst 0L IUChar)) in

  let enter_scalar pos e sz bigendian =
    for i = 0 to sz - 1 do
      let bytenum = if bigendian then sz - 1 - i else i in
      new_initdata.(pos + i) <- Init_single(extract_byte env e bytenum)
    done in

  let rec enter_init pos ty init bigendian =
    match (unroll env ty, init) with
    | (TInt(ik, _), Init_single e) ->
        enter_scalar pos e (sizeof_ikind ik) bigendian
    | (TEnum(_, _), Init_single e) ->
        enter_scalar pos e (sizeof_ikind enum_ikind) bigendian
    | (TPtr _, Init_single e) ->
        enter_scalar pos e ((!Machine.config).sizeof_ptr) bigendian
    | (TArray(ty_elt, _, _), Init_array il) ->
        begin match sizeof env ty_elt with
        | Some sz -> enter_init_array pos ty_elt sz il bigendian
        | None -> fatal_error "%a: Internal error: incomplete type in init data" formatloc loc
        end
    | (_, _) ->
        error "%a: Unsupported initializer for packed struct" formatloc loc
  and enter_init_array pos ty sz il bigendian =
    match il with
    | [] -> ()
    | i1 :: il' ->
        enter_init pos ty i1 bigendian;
        enter_init_array (pos + sz) ty sz il' bigendian in

  let enter_field (fld, init) =
    let finfo =
      try Hashtbl.find packed_fields (struct_id, fld.fld_name)
      with Not_found ->
        fatal_error "%a: Internal error: non-packed field in packed struct"
                    formatloc loc in
    enter_init finfo.fi_offset fld.fld_typ init
               ((!Machine.config).bigendian <> finfo.fi_swap) in

  List.iter enter_field initdata;

  Init_struct(struct_id, [
    (payload_field struct_sz, Init_array (Array.to_list new_initdata))
  ])

let transf_init loc env i =
  let rec trinit = function
  | Init_single e as i -> i
  | Init_array il -> Init_array (List.map trinit il)
  | Init_struct(id, fld_init_list) ->
      begin try
        let sz = Hashtbl.find packed_structs id in
        init_packed_struct loc env id sz fld_init_list
      with Not_found ->
        Init_struct(id, List.map (fun (f,i) -> (f, trinit i)) fld_init_list)
      end
  | Init_union(id, fld, i) -> Init_union(id, fld, trinit i)
  in trinit i

(* Declarations *)

let transf_decl loc env (sto, id, ty, init_opt) =
  (sto, id, ty,
   match init_opt with
   | None -> None
   | Some i -> Some (transf_init loc env i))

(* Pragmas *)

let re_pack = Str.regexp "pack\\b"
let re_pack_1 = Str.regexp "pack[ \t]*(\\([ \t0-9,]*\\))[ \t]*$"
let re_comma = Str.regexp ",[ \t]*"

let process_pragma loc s =
  if Str.string_match re_pack s 0 then begin
    if Str.string_match re_pack_1 s 0 then begin
      let arg = Str.matched_group 1 s in
      let (mfa, msa, bs) =
        match List.map int_of_string (Str.split re_comma arg) with
        | [] -> (0, 0, false)
        | [x] -> (x, 0, false)
        | [x;y] -> (x, y, false)
        | x :: y :: z :: _ -> (x, y, z = 1) in
      if mfa = 0 || is_pow2 mfa then
        max_field_align := mfa
      else
        error "%a: Error: In #pragma pack, max field alignment must be a power of 2" formatloc loc;
      if msa = 0 || is_pow2 msa then
        min_struct_align := msa
      else
        error "%a: Error: In #pragma pack, min struct alignment must be a power of 2" formatloc loc;
      byte_swap_fields := bs;
      true
    end else begin
      warning "%a: Warning: Ill-formed #pragma pack, ignored" formatloc loc;
      false
    end
  end else
    false

(* Global declarations *)

let rec transf_globdecls env accu = function
  | [] -> List.rev accu
  | g :: gl ->
      match g.gdesc with
      | Gdecl((sto, id, ty, init) as d) ->
          transf_globdecls
            (Env.add_ident env id sto ty)
            ({g with gdesc = Gdecl(transf_decl g.gloc env d)} :: accu)
            gl
      | Gfundef f ->
          transf_globdecls
            (Env.add_ident env f.fd_name f.fd_storage (fundef_typ f))
            ({g with gdesc = Gfundef(transf_fundef env f)} :: accu)
            gl
      | Gcompositedecl(su, id, attr) ->
          transf_globdecls
            (Env.add_composite env id (composite_info_decl env su attr))
            (g :: accu)
            gl
      | Gcompositedef(su, id, attr, fl) ->
          let (attr', fl') = transf_composite g.gloc env su id attr fl in
          transf_globdecls
            (Env.add_composite env id (composite_info_def env su attr' fl'))
            ({g with gdesc = Gcompositedef(su, id, attr', fl')} :: accu)
            gl
      | Gtypedef(id, ty) ->
          transf_globdecls
            (Env.add_typedef env id ty)
            (g :: accu)
            gl
      | Genumdef _  ->
          transf_globdecls
            env
            (g :: accu)
            gl
      | Gpragma p ->
          if process_pragma g.gloc p
          then transf_globdecls env accu gl
          else transf_globdecls env (g :: accu) gl

(* Program *)

let program p =
  min_struct_align := 0;
  max_field_align := 0;
  byte_swap_fields := false;
  transf_globdecls (Builtins.environment()) [] p
