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

(* Assumes: unblocked, simplified code.
   Preserves: unblocked, simplified code. *)

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
    bf_signed: bool }   (* signed or unsigned *)

(* invariants:
     0 <= pos < bitsizeof(int)
     0 < sz <= bitsizeof(int)
     0 < pos + sz <= bitsizeof(int)
*)

(* Mapping (struct identifier, bitfield name) -> bitfield info *)

let bitfield_table =
      (Hashtbl.create 57: (ident * string, bitfield_info) Hashtbl.t)

(* Packing algorithm -- keep consistent with [Cutil.pack_bitfield]! *)

let unsigned_ikind_for_carrier nbits =
  if nbits <= 8 then IUChar else
  if nbits <= 8 * !config.sizeof_short then IUShort else
  if nbits <= 8 * !config.sizeof_int then IUInt else
  if nbits <= 8 * !config.sizeof_long then IULong else
  if nbits <= 8 * !config.sizeof_longlong then IULongLong else
  assert false

let pack_bitfields env id ml =
  let rec pack accu pos = function
  | [] ->
      (pos, accu, [])
  | m :: ms as ml ->
      match m.fld_bitfield with
      | None -> (pos, accu, ml)
      | Some n ->
          if n = 0 then
            (pos, accu, ms) (* bit width 0 means end of pack *)
          else if pos + n >= 8 * !config.sizeof_int then
            (pos, accu, ml) (* doesn't fit in current word *)
          else begin
            let signed =
              match unroll env m.fld_typ with
              | TInt(ik, _) -> is_signed_ikind ik
              | _ -> assert false (* should never happen, checked in Elab *) in
            pack ((m.fld_name, pos, n, signed) :: accu) (pos + n) ms
          end
  in pack [] 0 ml

let rec transf_members env id count = function
  | [] -> []
  | m :: ms as ml ->
      if m.fld_bitfield = None then
        m :: transf_members env id count ms
      else begin
        let (nbits, bitfields, ml') = pack_bitfields env id ml in
        let carrier = sprintf "__bf%d" count in
        let carrier_typ = TInt(unsigned_ikind_for_carrier nbits, []) in
        List.iter
          (fun (name, pos, sz, signed) ->
            Hashtbl.add bitfield_table
              (id, name)
              {bf_carrier = carrier; bf_carrier_typ = carrier_typ;
               bf_pos = pos; bf_size = sz; bf_signed = signed})
          bitfields;
        { fld_name = carrier; fld_typ = carrier_typ; fld_bitfield = None}
        :: transf_members env id (count + 1) ml'
      end

let transf_composite env su id ml =
  match su with
  | Struct -> transf_members env id 1 ml
  | Union  -> ml

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
  {edesc = EBinop(Oshr, e2, right_shift_count bf, e2.etyp);
   etyp = e2.etyp}

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

(* Expressions *)

let transf_expr env e =

  let is_bitfield_access ty fieldname =
    match unroll env ty with
    | TStruct(id, _) ->
        (try Some(Hashtbl.find bitfield_table (id, fieldname))
         with Not_found -> None)
    | _ -> None in

  let is_bitfield_access_ptr ty fieldname =
    match unroll env ty with
    | TPtr(ty', _) -> is_bitfield_access ty' fieldname
    | _ -> None in 

  let rec texp e =
    match e.edesc with
    | EConst _ -> e
    | ESizeof _ -> e
    | EVar _ -> e

    | EUnop(Odot fieldname, e1) ->
        let e1' = texp e1 in
        begin match is_bitfield_access e1.etyp fieldname with
        | None ->
            {edesc = EUnop(Odot fieldname, e1'); etyp = e.etyp}
        | Some bf ->
            bitfield_extract bf
              {edesc = EUnop(Odot bf.bf_carrier, e1');
               etyp = bf.bf_carrier_typ}
        end

    | EUnop(Oarrow fieldname, e1) ->
        let e1' = texp e1 in
        begin match is_bitfield_access_ptr e1.etyp fieldname with
        | None ->
            {edesc = EUnop(Oarrow fieldname, e1'); etyp = e.etyp}
        | Some bf ->
            bitfield_extract bf
              {edesc = EUnop(Oarrow bf.bf_carrier, e1');
               etyp = bf.bf_carrier_typ}
        end

    | EUnop(op, e1) ->
        (* Note: simplified expr, so no ++/-- *)
        {edesc = EUnop(op, texp e1); etyp = e.etyp}

    | EBinop(Oassign, e1, e2, ty) ->
        begin match e1.edesc with
        | EUnop(Odot fieldname, e11) ->
            let lhs = texp e11 in let rhs = texp e2 in
            begin match is_bitfield_access e11.etyp fieldname with
            | None ->
                {edesc = EBinop(Oassign,
                                {edesc = EUnop(Odot fieldname, lhs);
                                 etyp = e1.etyp},
                                rhs, ty);
                 etyp = e.etyp}
            | Some bf ->
                let carrier =
                  {edesc = EUnop(Odot bf.bf_carrier, lhs);
                   etyp = bf.bf_carrier_typ} in
                {edesc = EBinop(Oassign, carrier,
                                bitfield_assign bf carrier rhs,
                                carrier.etyp);
                 etyp = carrier.etyp}
            end
        | EUnop(Oarrow fieldname, e11) ->
            let lhs = texp e11 in let rhs = texp e2 in
            begin match is_bitfield_access_ptr e11.etyp fieldname with
            | None ->
                {edesc = EBinop(Oassign,
                                {edesc = EUnop(Oarrow fieldname, lhs);
                                 etyp = e1.etyp},
                                rhs, ty);
                 etyp = e.etyp}
            | Some bf ->
                let carrier =
                  {edesc = EUnop(Oarrow bf.bf_carrier, lhs);
                   etyp = bf.bf_carrier_typ} in
                {edesc = EBinop(Oassign, carrier,
                                bitfield_assign bf carrier rhs,
                                carrier.etyp);
                 etyp = carrier.etyp}
            end
        | _ ->
            {edesc = EBinop(Oassign, texp e1, texp e2, e1.etyp); etyp = e1.etyp}
        end

    | EBinop(op, e1, e2, ty) ->
        (* Note: simplified expr assumed, so no assign-op *)
        {edesc = EBinop(op, texp e1, texp e2, ty); etyp = e.etyp}
    | EConditional(e1, e2, e3) ->
        {edesc = EConditional(texp e1, texp e2, texp e3); etyp = e.etyp}
    | ECast(ty, e1) ->
        {edesc = ECast(ty, texp e1); etyp = e.etyp}
    | ECall(e1, el) ->
        {edesc = ECall(texp e1, List.map texp el); etyp = e.etyp}

  in texp e

(* Statements *)

let rec transf_stmt env s =
  match s.sdesc with
  | Sskip -> s
  | Sdo e ->
      {sdesc = Sdo(transf_expr env e); sloc = s.sloc}
  | Sseq(s1, s2) -> 
      {sdesc = Sseq(transf_stmt env s1, transf_stmt env s2); sloc = s.sloc }
  | Sif(e, s1, s2) ->
      {sdesc = Sif(transf_expr env e, transf_stmt env s1, transf_stmt env s2);
       sloc = s.sloc}
  | Swhile(e, s1) ->
      {sdesc = Swhile(transf_expr env e, transf_stmt env s1);
       sloc = s.sloc}
  | Sdowhile(s1, e) ->
      {sdesc = Sdowhile(transf_stmt env s1, transf_expr env e);
       sloc = s.sloc}
  | Sfor(s1, e, s2, s3) ->
      {sdesc = Sfor(transf_stmt env s1, transf_expr env e, transf_stmt env s2,
                    transf_stmt env s3);
       sloc = s.sloc}
  | Sbreak -> s
  | Scontinue -> s
  | Sswitch(e, s1) ->
      {sdesc = Sswitch(transf_expr env e, transf_stmt env s1); sloc = s.sloc}
  | Slabeled(lbl, s) ->
      {sdesc = Slabeled(lbl, transf_stmt env s); sloc = s.sloc}
  | Sgoto lbl -> s
  | Sreturn None -> s
  | Sreturn (Some e) ->
      {sdesc = Sreturn(Some(transf_expr env e)); sloc = s.sloc}
  | Sblock _ | Sdecl _ ->
      assert false     (* should not occur in unblocked code *)

(* Functions *)

let transf_fundef env f =
  { f with fd_body = transf_stmt env f.fd_body }

(* Programs *)

let program p =
  Transform.program ~composite:transf_composite ~fundef:transf_fundef p
