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

(* Assumes: unblocked code.
   Preserves: unblocked code. *)

open Printf
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
    bf_signed_res: bool (* is result of extracting field signed or unsigned? *)
  }

(* invariants:
     0 <= pos < bitsizeof(int)
     0 < sz <= bitsizeof(int)
     0 < pos + sz <= bitsizeof(int)
*)

(* Mapping (struct identifier, bitfield name) -> bitfield info *)

let bitfield_table =
      (Hashtbl.create 57: (ident * string, bitfield_info) Hashtbl.t)

(* Signedness issues *)

let unsigned_ikind_for_carrier nbits =
  if nbits <= 8 then IUChar else
  if nbits <= 8 * !config.sizeof_short then IUShort else
  if nbits <= 8 * !config.sizeof_int then IUInt else
  if nbits <= 8 * !config.sizeof_long then IULong else
  if nbits <= 8 * !config.sizeof_longlong then IULongLong else
  assert false

let fits_unsigned v n =
  v >= 0L && v < Int64.shift_left 1L n

let fits_signed v n =
  let p =  Int64.shift_left 1L (n-1) in v >= Int64.neg p && v < p

let is_signed_enum_bitfield env sid fld eid n =
  let info = Env.find_enum env eid in
  if List.for_all (fun (_, v, _) -> int_representable v n false) info.Env.ei_members
  then false
  else if List.for_all (fun (_, v, _) -> int_representable v n true) info.Env.ei_members
  then true
  else begin
    Cerrors.warning "Warning: not all values of type 'enum %s' can be represented in bit-field '%s' of struct '%s' (%d bits are not enough)" eid.name fld sid.name n;
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
            pack ((m.fld_name, pos, n, signed, signed2) :: accu) (pos + n) ms
          end
  in pack [] 0 ml

let rec transf_members env id count = function
  | [] -> []
  | m :: ms as ml ->
      if m.fld_bitfield = None then
        m :: transf_members env id count ms
      else begin
        let (nbits, bitfields, ml') = pack_bitfields env id ml in
        if nbits = 0 then
          (* Lone zero-size bitfield: just ignore *)
          transf_members env id count ml'
        else begin
          (* Create integer field of sufficient size for this bitfield group *)
          let carrier = sprintf "__bf%d" count in
          let carrier_ikind = unsigned_ikind_for_carrier nbits in
          let carrier_typ = TInt(carrier_ikind, []) in
          (* Enter each field with its bit position, size, signedness *)
          List.iter
            (fun (name, pos, sz, signed, signed2) ->
              if name <> "" then begin
                let pos' =
                  if !config.bitfields_msb_first
                  then sizeof_ikind carrier_ikind * 8 - pos - sz
                  else pos in
                Hashtbl.add bitfield_table
                  (id, name)
                  {bf_carrier = carrier; bf_carrier_typ = carrier_typ;
                   bf_pos = pos'; bf_size = sz;
                   bf_signed = signed; bf_signed_res = signed2}
              end)
            bitfields;
          { fld_name = carrier; fld_typ = carrier_typ; fld_bitfield = None}
          :: transf_members env id (count + 1) ml'
        end
      end

let transf_composite env su id attr ml =
  match su with
  | Struct -> (attr, transf_members env id 1 ml)
  | Union  -> (attr, ml)

(* Bitfield manipulation expressions *)

let left_shift_count bf =
  intconst 
    (Int64.of_int (8 * !config.sizeof_int - (bf.bf_pos + bf.bf_size)))
    IInt

let right_shift_count bf =
  intconst 
    (Int64.of_int (8 * !config.sizeof_int - bf.bf_size))
    IInt

let insertion_mask bf =
  let m =
    Int64.shift_left
      (Int64.pred (Int64.shift_left 1L bf.bf_size))
      bf.bf_pos in
  (* Give the mask an hexadecimal string representation, nicer to read *)
  {edesc = EConst(CInt(m, IUInt, sprintf "0x%LXU" m)); etyp = TInt(IUInt, [])}

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

let bitfield_extract bf carrier =
  let e1 =
    {edesc = EBinop(Oshl, carrier, left_shift_count bf, TInt(IUInt, []));
     etyp = carrier.etyp} in
  let ty = TInt((if bf.bf_signed then IInt else IUInt), []) in
  let e2 =
    {edesc = ECast(ty, e1); etyp = ty} in
  let e3 =
    {edesc = EBinop(Oshr, e2, right_shift_count bf, e2.etyp);
     etyp = ty} in
  if bf.bf_signed_res = bf.bf_signed then e3 else begin
    let ty' = TInt((if bf.bf_signed_res then IInt else IUInt), []) in
    {edesc = ECast(ty', e3); etyp = ty'}
  end

(* Assign a bitfield within a carrier *)

(* Reference C code:

unsigned int bitfield_insert(unsigned int x, int ofs, int sz, unsigned int y)
{
  unsigned int mask = ((1U << sz) - 1) << ofs;
  return (x & ~mask) | ((y << ofs) & mask);
}

*)

let bitfield_assign bf carrier newval =
  let msk = insertion_mask bf in
  let notmsk = {edesc = EUnop(Onot, msk); etyp = msk.etyp} in
  let newval_shifted =
    {edesc = EBinop(Oshl, newval, intconst (Int64.of_int bf.bf_pos) IUInt,
                    TInt(IUInt,[]));
     etyp = TInt(IUInt,[])} in
  let newval_masked =
    {edesc = EBinop(Oand, newval_shifted, msk, TInt(IUInt,[]));
     etyp = TInt(IUInt,[])}
  and oldval_masked =
    {edesc = EBinop(Oand, carrier, notmsk, TInt(IUInt,[]));
     etyp = TInt(IUInt,[])} in
  {edesc = EBinop(Oor,  oldval_masked, newval_masked,  TInt(IUInt,[]));
   etyp =  TInt(IUInt,[])}

(* Check whether a field access (e.f or e->f) is a bitfield access.
   If so, return carrier expression (e and *e, respectively)
   and bitfield_info *)

let rec is_bitfield_access env e =
  match e.edesc with
  | EUnop(Odot fieldname, e1) ->
      begin match unroll env e1.etyp with
      | TStruct(id, _) ->
          (try Some(e1, Hashtbl.find bitfield_table (id, fieldname))
           with Not_found -> None)
      | _ ->
          None
      end
  | EUnop(Oarrow fieldname, e1) ->
      begin match unroll env e1.etyp with
      | TPtr(ty, _) ->
          is_bitfield_access env
            {edesc = EUnop(Odot fieldname,
                           {edesc = EUnop(Oderef, e1); etyp = ty});
             etyp = e.etyp}
      | _ ->
          None
      end
  | _ -> None

(* Expressions *)

let transf_expr env ctx e =

  let rec texp ctx e =
    match e.edesc with
    | EConst _ -> e
    | ESizeof _ -> e
    | EAlignof _ -> e
    | EVar _ -> e

    | EUnop(Odot s, e1) ->
        begin match is_bitfield_access env e with
        | None ->
            {edesc = EUnop(Odot s, texp Val e1); etyp = e.etyp}
        | Some(ex, bf) ->
            transf_read ex bf
        end
    | EUnop(Oarrow s, e1) ->
        begin match is_bitfield_access env e with
        | None ->
            {edesc = EUnop(Oarrow s, texp Val e1); etyp = e.etyp}
        | Some(ex, bf) ->
            transf_read ex bf
        end
    | EUnop((Opreincr|Opredecr) as op, e1) ->
        begin match is_bitfield_access env e1 with
        | None ->
            {edesc = EUnop(op, texp Val e1); etyp = e.etyp}
        | Some(ex, bf) ->
            transf_pre ctx (op_for_incr_decr op) ex bf e1.etyp
        end
    | EUnop((Opostincr|Opostdecr) as op, e1) ->
        begin match is_bitfield_access env e1 with
        | None ->
            {edesc = EUnop(op, texp Val e1); etyp = e.etyp}
        | Some(ex, bf) ->
            transf_post ctx (op_for_incr_decr op) ex bf e1.etyp
        end
    | EUnop(op, e1) -> 
        {edesc = EUnop(op, texp Val e1); etyp = e.etyp}

    | EBinop(Oassign, e1, e2, ty) ->
        begin match is_bitfield_access env e1 with
        | None ->
            {edesc = EBinop(Oassign, texp Val e1, texp Val e2, ty);
             etyp = e.etyp}
        | Some(ex, bf) ->
            transf_assign ctx ex bf e2
        end
    | EBinop((Oadd_assign|Osub_assign|Omul_assign|Odiv_assign
                         |Omod_assign|Oand_assign|Oor_assign|Oxor_assign
                         |Oshl_assign|Oshr_assign) as op,
             e1, e2, ty) ->
        begin match is_bitfield_access env e1 with
        | None ->
            {edesc = EBinop(op, texp Val e1, texp Val e2, ty); etyp = e.etyp}
        | Some(ex, bf) ->
            transf_assignop ctx (op_for_assignop op) ex bf e2 ty
        end
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

  and transf_read e bf =
    bitfield_extract bf
      {edesc = EUnop(Odot bf.bf_carrier, texp Val e); etyp = bf.bf_carrier_typ}

  and transf_assign ctx e1 bf e2 =
    bind_lvalue env (texp Val e1) (fun base ->
      let carrier =
        {edesc = EUnop(Odot bf.bf_carrier, base); etyp = bf.bf_carrier_typ} in
      let asg =
        eassign carrier (bitfield_assign bf carrier (texp Val e2)) in
      if ctx = Val then ecomma asg (bitfield_extract bf carrier) else asg)

  and transf_assignop ctx op e1 bf e2 tyres =
    bind_lvalue env (texp Val e1) (fun base ->
      let carrier =
        {edesc = EUnop(Odot bf.bf_carrier, base); etyp = bf.bf_carrier_typ} in
      let rhs =
        {edesc = EBinop(op, bitfield_extract bf carrier, texp Val e2, tyres);
         etyp = tyres} in
      let asg =
        eassign carrier (bitfield_assign bf carrier rhs) in
      if ctx = Val then ecomma asg (bitfield_extract bf carrier) else asg)

  and transf_pre ctx op e1 bf tyfield =
    transf_assignop ctx op e1 bf (intconst 1L IInt)
                                 (unary_conversion env tyfield)

  and transf_post ctx op e1 bf tyfield  =
    if ctx = Effects then
      transf_pre ctx op e1 bf tyfield
    else begin
      bind_lvalue env (texp Val e1) (fun base ->
        let carrier =
          {edesc = EUnop(Odot bf.bf_carrier, base); etyp = bf.bf_carrier_typ} in
        let temp = mk_temp env tyfield in
        let tyres = unary_conversion env tyfield in
        let settemp = eassign temp (bitfield_extract bf carrier) in
        let rhs =
          {edesc = EBinop(op, temp, intconst 1L IInt, tyres); etyp = tyres} in
        let asg =
          eassign carrier (bitfield_assign bf carrier rhs) in
        ecomma (ecomma settemp asg) temp)
    end

  in texp ctx e

(* Statements *)

let transf_stmt env s =
  Transform.stmt (fun loc env ctx e -> transf_expr env ctx e) env s

(* Functions *)

let transf_fundef env f =
  Transform.fundef transf_stmt env f

(* Initializers *)

let bitfield_initializer bf i =
  match i with
  | Init_single e ->
      let m = Int64.pred (Int64.shift_left 1L bf.bf_size) in
      let e_mask =
        {edesc = EConst(CInt(m, IUInt, sprintf "0x%LXU" m));
         etyp = TInt(IUInt, [])} in
      let e_and =
        {edesc = EBinop(Oand, e, e_mask, TInt(IUInt,[]));
         etyp = TInt(IUInt,[])} in
      {edesc = EBinop(Oshl, e_and, intconst (Int64.of_int bf.bf_pos) IInt,
                      TInt(IUInt, []));
       etyp = TInt(IUInt, [])}
  | _ -> assert false

let rec pack_bitfield_init id carrier fld_init_list =
  match fld_init_list with
  | [] -> ([], [])
  | (fld, i) :: rem ->
      try
        let bf = Hashtbl.find bitfield_table (id, fld.fld_name) in
        if bf.bf_carrier <> carrier then
          ([], fld_init_list)
        else begin
          let (el, rem') = pack_bitfield_init id carrier rem in
          (bitfield_initializer bf i :: el, rem')
        end
      with Not_found ->
        ([], fld_init_list)

let rec or_expr_list = function
  | [] -> assert false
  | [e] -> e
  | e1 :: el ->
      {edesc = EBinop(Oor, e1, or_expr_list el, TInt(IUInt,[]));
       etyp = TInt(IUInt,[])}

let rec transf_struct_init id fld_init_list =
  match fld_init_list with
  | [] -> []
  | (fld, i) :: rem ->
      try
        let bf = Hashtbl.find bitfield_table (id, fld.fld_name) in
        let (el, rem') =
          pack_bitfield_init id bf.bf_carrier fld_init_list in
        ({fld_name = bf.bf_carrier; fld_typ = bf.bf_carrier_typ;
          fld_bitfield = None},
         Init_single {edesc = ECast(bf.bf_carrier_typ, or_expr_list el);
                      etyp = bf.bf_carrier_typ})
        :: transf_struct_init id rem'
      with Not_found ->
        (fld, i) :: transf_struct_init id rem

let rec transf_init env i =
  match i with
  | Init_single e -> Init_single (transf_expr env Val e)
  | Init_array il -> Init_array (List.map (transf_init env) il)
  | Init_struct(id, fld_init_list) ->
      let fld_init_list' =
        List.map (fun (f, i) -> (f, transf_init env i)) fld_init_list in
        Init_struct(id, transf_struct_init id fld_init_list')
  | Init_union(id, fld, i) -> Init_union(id, fld, transf_init env i)

let transf_decl env (sto, id, ty, init_opt) =
  (sto, id, ty,
   match init_opt with None -> None | Some i -> Some(transf_init env i))

(* Programs *)

let program p =
  Transform.program
    ~composite:transf_composite
    ~decl: transf_decl
    ~fundef:transf_fundef 
    p
