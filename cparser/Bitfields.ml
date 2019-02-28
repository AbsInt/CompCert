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

(* Elimination of bit fields in structs *)

(* Assumes: nothing. *)

open Machine
open C
open Cutil
open Transform

(* Info associated to each bitfield *)

type bitfield_info =
  { bf_carrier: string; (* name of underlying regular field *)
    bf_carrier_typ: typ; (* type of underlying regular field *)
    bf_pos: int;        (* start bit *)
    bf_size: int;       (* size in bit *)
    bf_signed: bool;    (* is field signed or unsigned? *)
    bf_signed_res: bool; (* is result of extracting field signed or unsigned? *)
    bf_bool: bool       (* does field have type _Bool? *)
  }

(* invariants:
     0 <= pos < bitsizeof(int)
     0 < sz <= bitsizeof(int)
     0 < pos + sz <= bitsizeof(int)
*)

let carrier_field bf =
  { fld_name = bf.bf_carrier; fld_typ = bf.bf_carrier_typ;
    fld_bitfield = None; fld_anonymous = false }

(* Mapping (struct/union identifier, bitfield name) -> bitfield info *)

let bitfield_table =
      (Hashtbl.create 57: (ident * string, bitfield_info) Hashtbl.t)

let is_bitfield structid fieldname =
  try Some (Hashtbl.find bitfield_table (structid, fieldname))
  with Not_found -> None

(* Mapping struct/union identifier -> list of members after transformation,
   including the carrier fields, but without the bit fields.
   structs and unions containing no bit fields are not put in this table. *)

let composite_transformed_members =
      (Hashtbl.create 57: (ident, C.field list) Hashtbl.t)

(* Signedness issues *)

let unsigned_ikind_for_carrier nbits =
  if nbits <= 8 then IUChar else
  if nbits <= 8 * !config.sizeof_short then IUShort else
  if nbits <= 8 * !config.sizeof_int then IUInt else
  if nbits <= 8 * !config.sizeof_long then IULong else
  if nbits <= 8 * !config.sizeof_longlong then IULongLong else
  assert false

let is_signed_enum_bitfield env sid fld eid n =
  let info = Env.find_enum env eid in
  if List.for_all (fun (_, v, _) -> int_representable v n false) info.Env.ei_members
  then false
  else if List.for_all (fun (_, v, _) -> int_representable v n true) info.Env.ei_members
  then true
  else begin
    Diagnostics.warning Diagnostics.no_loc Diagnostics.Unnamed
      "not all values of type 'enum %s' can be represented in bit-field '%s' of struct '%s' (%d bits are not enough)"
      eid.C.name fld sid.C.name n;
    false
  end

(* Packing algorithm -- keep consistent with [Cutil.pack_bitfield]! *)

let pack_bitfields env sid ml =
  let rec pack accu pos = function
  | [] ->
      (pos, accu, [])
  | m :: ms as ml ->
      match m.fld_bitfield with
      | None -> (pos, accu, ml)
      | Some n ->
          if n = 0 then
            (pos, accu, ms) (* bit width 0 means end of pack *)
          else if pos + n > 8 * !config.sizeof_int then
            (pos, accu, ml) (* doesn't fit in current word *)
          else begin
            let signed =
              match unroll env m.fld_typ with
              | TInt(ik, _) -> is_signed_ikind ik
              | TEnum(eid, _) -> is_signed_enum_bitfield env sid m.fld_name eid n
              | _ -> assert false (* should never happen, checked in Elab *) in
            let signed2 =
              match unroll env (type_of_member env m) with
              | TInt(ik, _) -> is_signed_ikind ik
              | _ -> assert false (* should never happen, checked in Elab *) in
            let is_bool =
              match unroll env m.fld_typ with
              | TInt(IBool, _) -> true
              | _ -> false in

            pack ((m.fld_name, pos, n, signed, signed2, is_bool) :: accu)
                 (pos + n) ms
          end
  in pack [] 0 ml

let rec transf_struct_members env id count = function
  | [] -> []
  | m :: ms as ml ->
      if m.fld_bitfield = None then
        m :: transf_struct_members env id count ms
      else begin
        let (nbits, bitfields, ml') = pack_bitfields env id ml in
        if nbits = 0 then
          (* Lone zero-size bitfield: just ignore *)
          transf_struct_members env id count ml'
        else begin
          (* Create integer field of sufficient size for this bitfield group *)
          let carrier = Printf.sprintf "__bf%d" count in
          let carrier_ikind = unsigned_ikind_for_carrier nbits in
          let carrier_typ = TInt(carrier_ikind, []) in
          (* Enter each field with its bit position, size, signedness *)
          List.iter
            (fun (name, pos, sz, signed, signed2, is_bool) ->
              if name <> "" then begin
                let pos' =
                  if !config.bitfields_msb_first
                  then sizeof_ikind carrier_ikind * 8 - pos - sz
                  else pos in
                Debug.set_bitfield_offset id name pos carrier (sizeof_ikind carrier_ikind);
                Hashtbl.add bitfield_table
                  (id, name)
                  {bf_carrier = carrier; bf_carrier_typ = carrier_typ;
                   bf_pos = pos'; bf_size = sz;
                   bf_signed = signed; bf_signed_res = signed2;
                   bf_bool = is_bool}
              end)
            bitfields;
          { fld_name = carrier; fld_typ = carrier_typ; fld_bitfield = None; fld_anonymous = false;}
          :: transf_struct_members env id (count + 1) ml'
        end
      end

let rec transf_union_members env id count = function
  | [] -> []
  | m :: ms ->
      (match m.fld_bitfield with
      | None ->  m::transf_union_members env id count ms
      | Some nbits ->
          let carrier = Printf.sprintf "__bf%d" count in
          let carrier_ikind = unsigned_ikind_for_carrier nbits in
          let carrier_typ = TInt(carrier_ikind, []) in
          let signed =
            match unroll env m.fld_typ with
            | TInt(ik, _) -> is_signed_ikind ik
            | TEnum(eid, _) -> is_signed_enum_bitfield env id m.fld_name eid nbits
            | _ -> assert false (* should never happen, checked in Elab *) in
          let signed2 =
            match unroll env (type_of_member env m) with
            | TInt(ik, _) -> is_signed_ikind ik
            | _ -> assert false (* should never happen, checked in Elab *) in
          let pos' =
            if !config.bitfields_msb_first
            then sizeof_ikind carrier_ikind * 8 - nbits
            else 0 in
          let is_bool =
            match unroll env m.fld_typ with
            | TInt(IBool, _) -> true
            | _ -> false in
          Hashtbl.add bitfield_table
            (id, m.fld_name)
            {bf_carrier = carrier; bf_carrier_typ = carrier_typ;
             bf_pos = pos'; bf_size = nbits;
             bf_signed = signed; bf_signed_res = signed2;
             bf_bool = is_bool};
          { fld_name = carrier; fld_typ = carrier_typ; fld_bitfield = None; fld_anonymous = false;}
          :: transf_union_members env id (count + 1) ms)

let transf_composite env su id attr ml =
  if List.for_all (fun f -> f.fld_bitfield = None) ml then
    (attr, ml)
  else begin
    let ml' =
      match su with
      | Struct -> transf_struct_members env id 1 ml
      | Union  -> transf_union_members env id 1 ml in
    Hashtbl.add composite_transformed_members id ml';
    (attr, ml')
  end

(* Bitfield manipulation expressions *)

let left_shift_count bf =
  intconst
    (Int64.of_int (8 * !config.sizeof_int - (bf.bf_pos + bf.bf_size)))
    IInt

let right_shift_count bf =
  intconst
    (Int64.of_int (8 * !config.sizeof_int - bf.bf_size))
    IInt

let uintconst_hex v =
  { edesc = EConst(CInt(v, IUInt, Printf.sprintf "0x%LXU" v));
    etyp = TInt(IUInt, []) }

let insertion_mask bf =
  let m =
    Int64.shift_left
      (Int64.pred (Int64.shift_left 1L bf.bf_size))
      bf.bf_pos in
  (* Give the mask an hexadecimal string representation, nicer to read *)
  uintconst_hex m

let eshift env op a b =
  let ty = unary_conversion env a.etyp in
  { edesc = EBinop(op, a, b, ty); etyp = ty }

let ebinint env op a b =
  let ty = binary_conversion env a.etyp b.etyp in
  { edesc = EBinop(op, a, b, ty); etyp = ty }

(* Extract the value of a bitfield *)

(* Reference C code:

unsigned int bitfield_unsigned_extract(unsigned int x, int ofs, int sz)
{
  return (x << (BITSIZE_UINT - (ofs + sz))) >> (BITSIZE_UINT - sz);
}

signed int bitfield_signed_extract(unsigned int x, int ofs, int sz)
{
  return ((signed int) (x << (BITSIZE_UINT - (ofs + sz))))
         >> (BITSIZE_UINT - sz);
}

*)

let bitfield_extract env bf carrier =
  let e1 = eshift env Oshl carrier (left_shift_count bf) in
  let ty = TInt((if bf.bf_signed then IInt else IUInt), []) in
  let e2 = ecast ty e1 in
  let e3 = eshift env Oshr e2 (right_shift_count bf) in
  if bf.bf_signed_res = bf.bf_signed
  then e3
  else ecast (TInt((if bf.bf_signed_res then IInt else IUInt), [])) e3

(* Assign a bitfield within a carrier *)

(* Reference C code:

unsigned int bitfield_insert(unsigned int x, int ofs, int sz, unsigned int y)
{
  unsigned int mask = ((1U << sz) - 1) << ofs;
  return (x & ~mask) | ((y << ofs) & mask);
}

If the bitfield is of type _Bool, the new value (y above) must be converted
to _Bool to normalize it to 0 or 1.
*)

let bitfield_assign env bf carrier newval =
  let msk = insertion_mask bf in
  let notmsk = {edesc = EUnop(Onot, msk); etyp = msk.etyp} in
  let newval_casted =
    ecast (TInt(IUInt,[]))
          (if bf.bf_bool then ecast (TInt(IBool,[])) newval else newval) in
  let newval_shifted =
    eshift env Oshl newval_casted (intconst (Int64.of_int bf.bf_pos) IUInt) in
  let newval_masked = ebinint env Oand newval_shifted msk
  and oldval_masked = ebinint env Oand carrier notmsk in
  ebinint env Oor oldval_masked newval_masked

(* Initialize a bitfield *)

(* Reference C code:

unsigned int bitfield_init(int ofs, int sz, unsigned int y)
{
  unsigned int mask = (1U << sz) - 1;
  return (y & mask) << ofs;
}

If the bitfield is of type _Bool, the new value (y above) must be converted
to _Bool to normalize it to 0 or 1.
*)

let bitfield_initializer bf i =
  match i with
  | Init_single e ->
      let m = Int64.pred (Int64.shift_left 1L bf.bf_size) in
      let e_cast =
        if bf.bf_bool then ecast (TInt(IBool,[])) e else e in
      let e_mask = uintconst_hex m in
      let e_and =
        {edesc = EBinop(Oand, e_cast, e_mask, TInt(IUInt,[]));
         etyp = TInt(IUInt,[])} in
      {edesc = EBinop(Oshl, e_and, intconst (Int64.of_int bf.bf_pos) IInt,
                      TInt(IUInt, []));
       etyp = TInt(IUInt, [])}
  | _ ->
      assert false

(* Associate to the left so that it prints more nicely *)

let or_expr_list = function
  | [] -> intconst 0L IUInt
  | [e] -> e
  | e1 :: el ->
      List.fold_left
        (fun accu e ->
          {edesc = EBinop(Oor, accu, e, TInt(IUInt,[]));
           etyp = TInt(IUInt,[])})
        e1 el

(* Initialize the carrier for consecutive bitfields  *)

let rec pack_bitfield_init id carrier fld_init_list =
  match fld_init_list with
  | [] -> ([], [])
  | (fld, i) :: rem ->
      match is_bitfield id fld.fld_name with
      | None ->
          ([], fld_init_list)
      | Some bf ->
          if bf.bf_carrier <> carrier then
            ([], fld_init_list)
          else begin
            let (el, rem') = pack_bitfield_init id carrier rem in
            (bitfield_initializer bf i :: el, rem')
          end

let rec transf_struct_init id fld_init_list =
  match fld_init_list with
  | [] -> []
  | (fld, i) :: rem ->
      match is_bitfield id fld.fld_name with
      | None ->
          (fld, i) :: transf_struct_init id rem
      | Some bf ->
          let (el, rem') =
            pack_bitfield_init id bf.bf_carrier fld_init_list in
          (carrier_field bf,
           Init_single {edesc = ECast(bf.bf_carrier_typ, or_expr_list el);
                        etyp = bf.bf_carrier_typ})
          :: transf_struct_init id rem'

(* Add default initialization for carrier fields that are not listed in the output of
   [transf_struct_init].  This happens with carrier fields that contain no named
   bitfields, only anonymous bitfields. *)

let rec completed_struct_init env actual expected =
  match actual, expected with
  | [], [] -> []
  | (f_a, i) :: actual', f_e :: expected' when f_a.fld_name = f_e.fld_name ->
      (f_a, i) :: completed_struct_init env actual' expected'
  | _, f_e :: expected' ->
      (f_e, default_init env f_e.fld_typ) :: completed_struct_init env actual expected'
  | _, [] ->
      assert false

(* Check whether a field access (e.f or e->f) is a bitfield access.
   If so, return carrier expression (e and *e, respectively)
   and bitfield_info *)

let rec is_bitfield_access env e =
  match e.edesc with
  | EUnop(Odot fieldname, e1) ->
      begin match unroll env e1.etyp with
      | TUnion (id,_)
      | TStruct(id, _) ->
          (try Some(e1, Hashtbl.find bitfield_table (id, fieldname))
           with Not_found -> None)
      | _ ->
          None
      end
  | EUnop(Oarrow fieldname, e1) ->
      begin match unroll env e1.etyp with
      | TPtr(ty, _) | TArray(ty, _, _) ->
          is_bitfield_access env
            {edesc = EUnop(Odot fieldname,
                           {edesc = EUnop(Oderef, e1); etyp = ty});
             etyp = e.etyp}
      | _ ->
          None
      end
  | _ -> None

(* Expressions *)

let rec transf_exp env ctx e =
  match e.edesc with
  | EConst _ -> e
  | ESizeof _ -> e
  | EAlignof _ -> e
  | EVar _ -> e

  | EUnop(Odot s, e1) ->
      begin match is_bitfield_access env e with
      | None ->
          {edesc = EUnop(Odot s, transf_exp env Val e1); etyp = e.etyp}
      | Some(ex, bf) ->
          transf_read env ex bf
      end
  | EUnop(Oarrow s, e1) ->
      begin match is_bitfield_access env e with
      | None ->
          {edesc = EUnop(Oarrow s, transf_exp env Val e1); etyp = e.etyp}
      | Some(ex, bf) ->
          transf_read env ex bf
        end
  | EUnop((Opreincr|Opredecr) as op, e1) ->
      begin match is_bitfield_access env e1 with
      | None ->
          {edesc = EUnop(op, transf_exp env Val e1); etyp = e.etyp}
      | Some(ex, bf) ->
          transf_pre env ctx (op_for_incr_decr op) ex bf e1.etyp
        end
  | EUnop((Opostincr|Opostdecr) as op, e1) ->
      begin match is_bitfield_access env e1 with
      | None ->
          {edesc = EUnop(op, transf_exp env Val e1); etyp = e.etyp}
      | Some(ex, bf) ->
          transf_post env ctx (op_for_incr_decr op) ex bf e1.etyp
      end
  | EUnop(op, e1) ->
      {edesc = EUnop(op, transf_exp env Val e1); etyp = e.etyp}

  | EBinop(Oassign, e1, e2, ty) ->
      begin match is_bitfield_access env e1 with
      | None ->
          {edesc = EBinop(Oassign, transf_exp env Val e1,
                                   transf_exp env Val e2, ty);
           etyp = e.etyp}
      | Some(ex, bf) ->
          transf_assign env ctx ex bf e2
      end
  | EBinop((Oadd_assign|Osub_assign|Omul_assign|Odiv_assign
                       |Omod_assign|Oand_assign|Oor_assign|Oxor_assign
                       |Oshl_assign|Oshr_assign) as op,
           e1, e2, ty) ->
      begin match is_bitfield_access env e1 with
      | None ->
          {edesc = EBinop(op, transf_exp env Val e1,
                              transf_exp env Val e2, ty); etyp = e.etyp}
      | Some(ex, bf) ->
          transf_assignop env ctx (op_for_assignop op) ex bf e2 ty
      end
  | EBinop(Ocomma, e1, e2, ty) ->
      {edesc = EBinop(Ocomma, transf_exp env Effects e1,
                              transf_exp env Val e2, ty);
       etyp = e.etyp}
  | EBinop(op, e1, e2, ty) ->
      {edesc = EBinop(op, transf_exp env Val e1, transf_exp env Val e2, ty);
       etyp = e.etyp}

  | EConditional(e1, e2, e3) ->
      {edesc = EConditional(transf_exp env Val e1,
                            transf_exp env ctx e2, transf_exp env ctx e3);
       etyp = e.etyp}
  | ECast(ty, e1) ->
      {edesc = ECast(ty, transf_exp env Val e1); etyp = e.etyp}
  | ECompound(ty, i) ->
      {edesc = ECompound(ty, transf_init env i); etyp = e.etyp}
  | ECall(e1, el) ->
      {edesc = ECall(transf_exp env Val e1, List.map (transf_exp env Val) el);
       etyp = e.etyp}

and transf_read env e bf =
  bitfield_extract env bf
    {edesc = EUnop(Odot bf.bf_carrier, transf_exp env Val e);
     etyp = bf.bf_carrier_typ}

and transf_assign env ctx e1 bf e2 =
  bind_lvalue env (transf_exp env Val e1) (fun base ->
    let carrier =
      {edesc = EUnop(Odot bf.bf_carrier, base); etyp = bf.bf_carrier_typ} in
    let asg =
      eassign carrier (bitfield_assign env bf carrier (transf_exp env Val e2)) in
    if ctx = Val then ecomma asg (bitfield_extract env bf carrier) else asg)

and transf_assignop env ctx op e1 bf e2 tyres =
  bind_lvalue env (transf_exp env Val e1) (fun base ->
    let carrier =
      {edesc = EUnop(Odot bf.bf_carrier, base); etyp = bf.bf_carrier_typ} in
    let rhs =
      {edesc = EBinop(op, bitfield_extract env bf carrier, transf_exp env Val e2, tyres);
       etyp = tyres} in
    let asg =
      eassign carrier (bitfield_assign env bf carrier rhs) in
    if ctx = Val then ecomma asg (bitfield_extract env bf carrier) else asg)

and transf_pre env ctx op e1 bf tyfield =
  transf_assignop env ctx op e1 bf (intconst 1L IInt)
                                   (unary_conversion env tyfield)

and transf_post env ctx op e1 bf tyfield  =
  if ctx = Effects then
    transf_pre env ctx op e1 bf tyfield
  else begin
    bind_lvalue env (transf_exp env Val e1) (fun base ->
      let carrier =
        {edesc = EUnop(Odot bf.bf_carrier, base); etyp = bf.bf_carrier_typ} in
      let temp = mk_temp env tyfield in
      let tyres = unary_conversion env tyfield in
      let settemp = eassign temp (bitfield_extract env bf carrier) in
      let rhs =
        {edesc = EBinop(op, temp, intconst 1L IInt, tyres); etyp = tyres} in
      let asg =
        eassign carrier (bitfield_assign env bf carrier rhs) in
      ecomma (ecomma settemp asg) temp)
  end

(* Initializers *)

and transf_init env i =
  match i with
  | Init_single e -> Init_single (transf_exp env Val e)
  | Init_array il -> Init_array (List.rev (List.rev_map (transf_init env) il))
  | Init_struct(id, fld_init_list) ->
      let fld_init_list' =
        List.map (fun (f, i) -> (f, transf_init env i)) fld_init_list in
      begin match Hashtbl.find composite_transformed_members id with
      | exception Not_found ->
          Init_struct(id, fld_init_list')
      | ml ->
          Init_struct(id, completed_struct_init env (transf_struct_init id fld_init_list') ml)
      end
  | Init_union(id, fld, i) ->
      let i' = transf_init env i in
      match is_bitfield id fld.fld_name with
      | None ->
          Init_union(id, fld, i')
      | Some bf ->
          Init_union(id, carrier_field bf, Init_single (bitfield_initializer bf i'))

(* Declarations *)

let transf_decl env (sto, id, ty, init_opt) =
  (sto, id, ty,
   match init_opt with None -> None | Some i -> Some(transf_init env i))

(* Statements *)

let transf_stmt env s =
  Transform.stmt
     ~expr:(fun loc env ctx e -> transf_exp env ctx e)
     ~decl:transf_decl
     env s

(* Functions *)

let transf_fundef env f =
  Transform.fundef transf_stmt env f

(* Programs *)

let program p =
  Hashtbl.clear bitfield_table;
  Hashtbl.clear composite_transformed_members;
  Transform.program
    ~composite:transf_composite
    ~decl: transf_decl
    ~fundef:transf_fundef
    p
