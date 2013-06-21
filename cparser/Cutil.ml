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

(* Operations on C types and abstract syntax *)

open Printf
open Cerrors
open C
open Env
open Machine

(* Set and Map structures over identifiers *)

module Ident = struct
  type t = ident
  let compare id1 id2 = Pervasives.compare id1.stamp id2.stamp
end

module IdentSet = Set.Make(Ident)
module IdentMap = Map.Make(Ident)

(* Operations on attributes *)

(* Lists of attributes are kept sorted in increasing order *)

let rec add_attributes (al1: attributes) (al2: attributes) =
  match al1, al2 with
  | [], _ -> al2
  | _, [] -> al1
  | a1 :: al1', a2 :: al2' ->
      if a1 < a2 then a1 :: add_attributes al1' al2
      else if a1 > a2 then a2 :: add_attributes al1 al2'
      else a1 :: add_attributes al1' al2'

let rec remove_attributes (al1: attributes) (al2: attributes) = 
  (* viewed as sets: al1 \ al2 *)
  match al1, al2 with
  | [], _ -> []
  | _, [] -> al1
  | a1 :: al1', a2 :: al2' ->
      if a1 < a2 then a1 :: remove_attributes al1' al2
      else if a1 > a2 then remove_attributes al1 al2'
      else remove_attributes al1' al2'

let rec incl_attributes (al1: attributes) (al2: attributes) =
  match al1, al2 with
  | [], _ -> true
  | _ :: _, [] -> false
  | a1 :: al1', a2 :: al2' ->
      if a1 < a2 then false
      else if a1 > a2 then incl_attributes al1 al2'
      else incl_attributes al1' al2'

let rec find_custom_attributes (names: string list)  (al: attributes) =
  match al with
  | [] -> []
  | Attr(name, args) :: tl when List.mem name names ->
      args :: find_custom_attributes names tl
  | _ :: tl ->
      find_custom_attributes names tl

(* Adding top-level attributes to a type.  Doesn't need to unroll defns. *)
(* Array types cannot carry attributes, so add them to the element type. *)

let rec add_attributes_type attr t =
  match t with
  | TVoid a -> TVoid (add_attributes attr a)
  | TInt(ik, a) -> TInt(ik, add_attributes attr a)
  | TFloat(fk, a) -> TFloat(fk, add_attributes attr a)
  | TPtr(ty, a) -> TPtr(ty, add_attributes attr a)
  | TArray(ty, sz, a) -> TArray(add_attributes_type attr ty, sz, a)
  | TFun(ty, params, vararg, a) -> TFun(ty, params, vararg, add_attributes attr 
a)
  | TNamed(s, a) -> TNamed(s, add_attributes attr a)
  | TStruct(s, a) -> TStruct(s, add_attributes attr a)
  | TUnion(s, a) -> TUnion(s, add_attributes attr a)
  | TEnum(s, a) -> TEnum(s, add_attributes attr a)

(* Unrolling of typedef *)

let rec unroll env t =
  match t with
  | TNamed(name, attr) ->
      let ty = Env.find_typedef env name in
      unroll env (add_attributes_type attr ty)
  | _ -> t

(* Extracting the attributes of a type *)

let rec attributes_of_type env t =
  match t with
  | TVoid a -> a
  | TInt(ik, a) -> a
  | TFloat(fk, a) -> a
  | TPtr(ty, a) -> a
  | TArray(ty, sz, a) -> add_attributes a (attributes_of_type env ty)
  | TFun(ty, params, vararg, a) -> a
  | TNamed(s, a) -> attributes_of_type env (unroll env t)
  | TStruct(s, a) -> 
      let ci = Env.find_struct env s in add_attributes ci.ci_attr a
  | TUnion(s, a) ->
      let ci = Env.find_union env s in add_attributes ci.ci_attr a
  | TEnum(s, a) ->
      let ei = Env.find_enum env s in add_attributes ei.ei_attr a

(* Changing the attributes of a type (at top-level) *)
(* Same hack as above for array types. *)

let rec change_attributes_type env (f: attributes -> attributes) t =
  match t with
  | TVoid a -> TVoid (f a)
  | TInt(ik, a) -> TInt(ik, f a)
  | TFloat(fk, a) -> TFloat(fk, f a)
  | TPtr(ty, a) -> TPtr(ty, f a)
  | TArray(ty, sz, a) ->
      TArray(change_attributes_type env f ty, sz, a)
  | TFun(ty, params, vararg, a) -> TFun(ty, params, vararg, f a)
  | TNamed(s, a) ->
      let t1 = unroll env t in
      let t2 = change_attributes_type env f t1 in
      if t2 = t1 then t else t2         (* avoid useless expansion *)
  | TStruct(s, a) -> TStruct(s, f a)
  | TUnion(s, a) -> TUnion(s, f a)
  | TEnum(s, a) -> TEnum(s, f a)

let remove_attributes_type env attr t =
  change_attributes_type env (fun a -> remove_attributes a attr) t

let erase_attributes_type env t =
  change_attributes_type env (fun a -> []) t

(* Is an attribute type-related (true) or variable-related (false)? *)

let attr_is_type_related = function
  | Attr(("packed" | "__packed__"), _) -> true
  | _ -> false

(* Type compatibility *)

exception Incompat

let combine_types ?(noattrs = false) env t1 t2 =

  let comp_attr a1 a2 =
    if a1 = a2 then a2
    else if noattrs then add_attributes a1 a2
    else raise Incompat
  and comp_base x1 x2 =
    if x1 = x2 then x2 else raise Incompat
  and comp_array_size sz1 sz2 =
    match sz1, sz2 with
    | None, _ -> sz2
    | _, None -> sz1
    | Some n1, Some n2 -> if n1 = n2 then Some n2 else raise Incompat
  and comp_conv (id, ty) =
    match unroll env ty with
    | TInt(kind, attr) ->
        begin match kind with
        | IBool | IChar | ISChar | IUChar | IShort | IUShort -> raise Incompat
        | _ -> ()
        end
    | TFloat(kind, attr) ->
        begin match kind with
        | FFloat -> raise Incompat
        | _ -> ()
        end
    | _ -> () in

  let rec comp t1 t2 =
    match t1, t2 with
    | TVoid a1, TVoid a2 ->
        TVoid(comp_attr a1 a2)
    | TInt(ik1, a1), TInt(ik2, a2) ->
        TInt(comp_base ik1 ik2, comp_attr a1 a2)
    | TFloat(fk1, a1), TFloat(fk2, a2) ->
        TFloat(comp_base fk1 fk2, comp_attr a1 a2)
    | TPtr(ty1, a1), TPtr(ty2, a2) ->
        TPtr(comp ty1 ty2, comp_attr a1 a2)
    | TArray(ty1, sz1, a1), TArray(ty2, sz2, a2) ->
        TArray(comp ty1 ty2, comp_array_size sz1 sz2, comp_attr a1 a2)
    | TFun(ty1, params1, vararg1, a1), TFun(ty2, params2, vararg2, a2) ->
        let (params, vararg) =
          match params1, params2 with
          | None, None -> None, false
          | None, Some l2 -> List.iter comp_conv l2; (params2, vararg2)
          | Some l1, None -> List.iter comp_conv l1; (params1, vararg1)
          | Some l1, Some l2 ->
              if List.length l1 <> List.length l2 then raise Incompat;
              (Some(List.map2 (fun (id1, ty1) (id2, ty2) -> (id2, comp ty1 ty2))
                              l1 l2),
               comp_base vararg1 vararg2)
        in
          TFun(comp ty1 ty2, params, vararg, comp_attr a1 a2)
    | TNamed _, _ -> comp (unroll env t1) t2
    | _, TNamed _ -> comp t1 (unroll env t2)
    | TStruct(s1, a1), TStruct(s2, a2) ->
        TStruct(comp_base s1 s2, comp_attr a1 a2)
    | TUnion(s1, a1), TUnion(s2, a2) -> 
        TUnion(comp_base s1 s2, comp_attr a1 a2)
    | TEnum(s1, a1), TEnum(s2, a2) -> 
        TEnum(comp_base s1 s2, comp_attr a1 a2)
    | _, _ ->
        raise Incompat

  in try Some(comp t1 t2) with Incompat -> None

let compatible_types  ?noattrs env t1 t2 =
  match combine_types ?noattrs env t1 t2 with Some _ -> true | None -> false

(* Naive placement algorithm for bit fields, might not match that
   of the compiler. *)

let pack_bitfields ml =
  let rec pack nbits = function
  | [] ->
      (nbits, [])
  | m :: ms as ml ->
      match m.fld_bitfield with
      | None -> (nbits, ml)
      | Some n ->
          if n = 0 then
            (nbits, ms) (* bit width 0 means end of pack *)
          else if nbits + n > 8 * !config.sizeof_int then
            (nbits, ml) (* doesn't fit in current word *)
          else
            pack (nbits + n) ms (* add to current word *)
  in
  let (nbits, ml') = pack 0 ml in
  let (sz, al) =
    (* A lone bitfield of width 0 consumes no space and aligns to 1 *) 
    if nbits = 0 then (0, 1) else
    if nbits <= 8 then (1, 1) else
    if nbits <= 16 then (2, 2) else
    if nbits <= 32 then (4, 4) else
    if nbits <= 64 then (8, 8) else assert false in
  (sz, al, ml')

(* Natural alignment, in bytes *)

let alignof_ikind = function
  | IBool | IChar | ISChar | IUChar -> 1
  | IInt | IUInt -> !config.alignof_int
  | IShort | IUShort -> !config.alignof_short
  | ILong | IULong -> !config.alignof_long
  | ILongLong | IULongLong -> !config.alignof_longlong

let alignof_fkind = function
  | FFloat -> !config.alignof_float
  | FDouble -> !config.alignof_double
  | FLongDouble -> !config.alignof_longdouble

(* Return natural alignment of given type, or None if the type is incomplete *)

let enum_ikind = IInt

let rec alignof env t =
  match t with
  | TVoid _ -> !config.alignof_void
  | TInt(ik, _) -> Some(alignof_ikind ik)
  | TFloat(fk, _) -> Some(alignof_fkind fk)
  | TPtr(_, _) -> Some(!config.alignof_ptr)
  | TArray(ty, _, _) -> alignof env ty
  | TFun(_, _, _, _) -> !config.alignof_fun
  | TNamed(_, _) -> alignof env (unroll env t)
  | TStruct(name, _) ->
      let ci = Env.find_struct env name in ci.ci_alignof
  | TUnion(name, _) ->
      let ci = Env.find_union env name in ci.ci_alignof
  | TEnum(_, _) -> Some(alignof_ikind enum_ikind)

(* Compute the natural alignment of a struct or union. *)

let alignof_struct_union env members =
  let rec align_rec al = function
  | [] -> Some al
  | m :: rem as ml ->
      if m.fld_bitfield = None then begin
        match alignof env m.fld_typ with
        | None -> None
        | Some a -> align_rec (max a al) rem
      end else begin
        let (s, a, ml') = pack_bitfields ml in
        align_rec (max a al) ml'
      end
  in align_rec 1 members

let align x boundary =
  (* boundary must be a power of 2 *)
  (x + boundary - 1) land (lnot (boundary - 1))

(* Size of, in bytes *)

let sizeof_ikind = function
  | IBool | IChar | ISChar | IUChar -> 1
  | IInt | IUInt -> !config.sizeof_int
  | IShort | IUShort -> !config.sizeof_short
  | ILong | IULong -> !config.sizeof_long
  | ILongLong | IULongLong -> !config.sizeof_longlong

let sizeof_fkind = function
  | FFloat -> !config.sizeof_float
  | FDouble -> !config.sizeof_double
  | FLongDouble -> !config.sizeof_longdouble

(* Overflow-avoiding multiplication of an int64 and an int, with
   result in type int. *)

let cautious_mul (a: int64) (b: int) =
  if b = 0 || a <= Int64.of_int (max_int / b)
  then Some(Int64.to_int a * b)
  else None

(* Return size of type, in bytes, or [None] if the type is incomplete *)

let rec sizeof env t =
  match t with
  | TVoid _ -> !config.sizeof_void
  | TInt(ik, _) -> Some(sizeof_ikind ik)
  | TFloat(fk, _) -> Some(sizeof_fkind fk)
  | TPtr(_, _) -> Some(!config.sizeof_ptr)
  | TArray(ty, None, _) -> None
  | TArray(ty, Some n, _) as t' ->
      begin match sizeof env ty with
      | None -> None
      | Some s ->
          match cautious_mul n s with
          | Some sz -> Some sz
          | None -> error "sizeof(%a) overflows" Cprint.typ t'; Some 1
      end
  | TFun(_, _, _, _) -> !config.sizeof_fun
  | TNamed(_, _) -> sizeof env (unroll env t)
  | TStruct(name, _) ->
      let ci = Env.find_struct env name in ci.ci_sizeof
  | TUnion(name, _) ->
      let ci = Env.find_union env name in ci.ci_sizeof
  | TEnum(_, _) -> Some(sizeof_ikind enum_ikind)

(* Compute the size of a union.
   It is the size is the max of the sizes of fields, rounded up to the
   natural alignment. *)

let sizeof_union env members =
  let rec sizeof_rec sz = function
  | [] ->
      begin match alignof_struct_union env members with
      | None -> None                    (* should not happen? *)
      | Some al -> Some (align sz al)
      end
  | m :: rem ->
      begin match sizeof env m.fld_typ with
      | None -> None
      | Some s -> sizeof_rec (max sz s) rem
      end
  in sizeof_rec 0 members

(* Compute the size of a struct.
   We lay out fields consecutively, inserting padding to preserve
   their natural alignment. *)

let sizeof_struct env members =
  let rec sizeof_rec ofs = function
  | [] | [ { fld_typ = TArray(_, None, _) } ] ->
      (* C99: ty[] allowed as last field *)
      begin match alignof_struct_union env members with
      | None -> None                    (* should not happen? *)
      | Some al -> Some (align ofs al)
      end
  | m :: rem as ml ->
      if m.fld_bitfield = None then begin
        match alignof env m.fld_typ, sizeof env m.fld_typ with
        | Some a, Some s -> sizeof_rec (align ofs a + s) rem
        | _, _ -> None
      end else begin
        let (s, a, ml') = pack_bitfields ml in
        sizeof_rec (align ofs a + s) ml'
      end
  in sizeof_rec 0 members

(* Determine whether a type is incomplete *)

let incomplete_type env t =
  match sizeof env t with None -> true | Some _ -> false

(* Computing composite_info records *)

let composite_info_decl env su attr =
  { ci_kind = su; ci_members = [];
    ci_alignof = None; ci_sizeof = None;
    ci_attr = attr }

let composite_info_def env su attr m =
  { ci_kind = su; ci_members = m;
    ci_alignof = alignof_struct_union env m;
    ci_sizeof =
      begin match su with
      | Struct -> sizeof_struct env m
      | Union -> sizeof_union env m
      end;
    ci_attr = attr }

(* Is an integer [v] representable in [n] bits, signed or unsigned? *)

let int_representable v nbits sgn =
  if nbits >= 64 then true else
  if sgn then 
    let p = Int64.shift_left 1L (nbits - 1) in Int64.neg p <= v && v < p
  else
    0L <= v && v < Int64.shift_left 1L nbits
  
(* Type of a function definition *)

let fundef_typ fd =
  TFun(fd.fd_ret, Some fd.fd_params, fd.fd_vararg, [])

(* Signedness of integer kinds *)

let is_signed_ikind = function
  | IBool -> false
  | IChar -> !config.char_signed
  | ISChar -> true
  | IUChar -> false
  | IInt -> true
  | IUInt -> false
  | IShort -> true
  | IUShort -> false
  | ILong -> true
  | IULong -> false
  | ILongLong -> true
  | IULongLong -> false

(* Conversion to unsigned ikind *)

let unsigned_ikind_of = function
  | IBool -> IBool
  | IChar | ISChar | IUChar -> IUChar
  | IInt | IUInt -> IUInt
  | IShort | IUShort -> IUShort
  | ILong | IULong -> IULong
  | ILongLong | IULongLong -> IULongLong

(* Conversion to signed ikind *)

let signed_ikind_of = function
  | IBool -> IBool
  | IChar | ISChar | IUChar -> ISChar
  | IInt | IUInt -> IInt
  | IShort | IUShort -> IShort
  | ILong | IULong -> ILong
  | ILongLong | IULongLong -> ILongLong

(* Some classification functions over types *)

let is_void_type env t =
  match unroll env t with
  | TVoid _ -> true
  | _ -> false

let is_integer_type env t =
  match unroll env t with
  | TInt(_, _) -> true
  | TEnum(_, _) -> true
  | _ -> false

let is_arith_type env t =
  match unroll env t with
  | TInt(_, _) -> true
  | TFloat(_, _) -> true
  | TEnum(_, _) -> true
  | _ -> false

let is_pointer_type env t =
  match unroll env t with
  | TPtr _ -> true
  | _ -> false

let is_scalar_type env t =
  match unroll env t with
  | TInt(_, _) -> true
  | TFloat(_, _) -> true
  | TPtr _ -> true
  | TArray _ -> true                    (* assume implicit decay *)
  | TFun _ -> true                      (* assume implicit decay *)
  | TEnum(_, _) -> true
  | _ -> false

let is_composite_type env t =
  match unroll env t with
  | TStruct _ | TUnion _ -> true
  | _ -> false

let is_function_type env t =
  match unroll env t with
  | TFun _ -> true
  | _ -> false

(* Ranking of integer kinds *)

let integer_rank = function
  | IBool -> 1
  | IChar | ISChar | IUChar -> 2
  | IShort | IUShort -> 3
  | IInt | IUInt -> 4
  | ILong | IULong -> 5
  | ILongLong | IULongLong -> 6

(* Ranking of float kinds *)

let float_rank = function
  | FFloat -> 1
  | FDouble -> 2
  | FLongDouble -> 3

(* Array and function types "decay" to pointer types in many cases *)

let pointer_decay env t =
  match unroll env t with
  | TArray(ty, _, _) -> TPtr(ty, [])
  | TFun _ as ty -> TPtr(ty, [])
  | t -> t

(* The usual unary conversions (H&S 6.3.3) *) 

let unary_conversion env t = 
  match unroll env t with
  (* Promotion of small integer types *)
  | TInt(kind, attr) ->
      begin match kind with
      | IBool | IChar | ISChar | IUChar | IShort | IUShort ->
          TInt(IInt, attr)
      | IInt | IUInt | ILong | IULong | ILongLong | IULongLong ->
          TInt(kind, attr)
      end
  (* Enums are like signed ints *)
  | TEnum(id, attr) -> TInt(enum_ikind, attr)
  (* Arrays and functions decay automatically to pointers *)
  | TArray(ty, _, _) -> TPtr(ty, [])
  | TFun _ as ty -> TPtr(ty, [])
  (* Other types are not changed *)
  | t -> t

(* The usual binary conversions  (H&S 6.3.4).
   Applies only to arithmetic types.
   Return the type to which both sides are to be converted. *)

let binary_conversion env t1 t2 =
  let t1 = unary_conversion env t1 in
  let t2 = unary_conversion env t2 in
  match unroll env t1, unroll env t2 with
  | TFloat(FLongDouble, _), (TInt _ | TFloat _) -> t1
  | (TInt _ | TFloat _), TFloat(FLongDouble, _) -> t2
  | TFloat(FDouble, _), (TInt _ | TFloat _)     -> t1
  | (TInt _ | TFloat _), TFloat(FDouble, _)     -> t2
  | TFloat(FFloat, _), (TInt _ | TFloat _)      -> t1
  | (TInt _), TFloat(FFloat, _)      -> t2
  | TInt(k1, _), TInt(k2, _)  ->
      if k1 = k2 then t1 else begin
        match is_signed_ikind k1, is_signed_ikind k2 with
        | true, true | false, false ->
            (* take the bigger of the two types *)
            if integer_rank k1 >= integer_rank k2 then t1 else t2
        | false, true ->
            (* if rank (unsigned type) >= rank (signed type),
               take the unsigned type *)
            if integer_rank k1 >= integer_rank k2 then t1
            (* if rank (unsigned type) < rank (signed type)
               and all values of the unsigned type can be represented
               in the signed type, take the signed type *)
            else if sizeof_ikind k2 > sizeof_ikind k1 then t2
            (* if rank (unsigned type) < rank (signed type)
               and some values of the unsigned type cannot be represented
               in the signed type,
               take the unsigned type corresponding to the signed type *)
            else TInt(unsigned_ikind_of k2, [])
        | true, false ->
            if integer_rank k2 >= integer_rank k1 then t2
            else if sizeof_ikind k1 > sizeof_ikind k2 then t1
            else TInt(unsigned_ikind_of k1, [])
      end
  | _, _ -> assert false

(* Conversion on function arguments (with protoypes) *)

let argument_conversion env t = 
  (* Arrays and functions degrade automatically to pointers *)
  (* Other types are not changed *)
  match unroll env t with
  | TArray(ty, _, _) -> TPtr(ty, [])
  | TFun _ as ty -> TPtr(ty, [])
  | _ -> t (* preserve typedefs *)

(* Conversion on function arguments (old-style unprototyped, or vararg *)
(* H&S 6.3.5 *)

let default_argument_conversion env t =
  match unary_conversion env t with
  | TFloat(FFloat, attr) -> TFloat(FDouble, attr)
  | t' -> t'

(** Is the type Tptr(ty, a) appropriate for pointer arithmetic? *)

let pointer_arithmetic_ok env ty =
  match unroll env ty with
  | TVoid _ | TFun _ -> false
  | _ -> not (incomplete_type env ty)

(** The type of [x.fld].  Normally, it's the type of the field [fld],
  but if it is an unsigned bitfield of size < length of its type,
  its type is the corresponding signed int. *)

let type_of_member env fld =
  match fld.fld_bitfield with
  | None -> fld.fld_typ
  | Some w ->
      let (ik, attr) =
        match unroll env fld.fld_typ with
        | TInt(ik, attr) -> (ik, attr)
        | TEnum(_, attr) -> (enum_ikind, attr)
        | _ -> assert false in
      if w < sizeof_ikind ik * 8
      then TInt(signed_ikind_of ik, attr)
      else fld.fld_typ

(** Special types *)

let find_matching_unsigned_ikind sz =
  if sz = !config.sizeof_int then IUInt
  else if sz = !config.sizeof_long then IULong
  else if sz = !config.sizeof_longlong then IULongLong
  else assert false

let find_matching_signed_ikind sz =
  if sz = !config.sizeof_int then IInt
  else if sz = !config.sizeof_long then ILong
  else if sz = !config.sizeof_longlong then ILongLong
  else assert false

let wchar_ikind = find_matching_unsigned_ikind !config.sizeof_wchar
let size_t_ikind = find_matching_unsigned_ikind !config.sizeof_size_t
let ptr_t_ikind = find_matching_unsigned_ikind !config.sizeof_ptr
let ptrdiff_t_ikind = find_matching_signed_ikind !config.sizeof_ptrdiff_t

(** The type of a constant *)

let type_of_constant = function
  | CInt(_, ik, _) -> TInt(ik, [])
  | CFloat(_, fk) -> TFloat(fk, [])
  | CStr _ -> TPtr(TInt(IChar, []), [])
  | CWStr _ -> TPtr(TInt(wchar_ikind, []), [])
  | CEnum(_, _) -> TInt(IInt, [])

(* Check that a C expression is a lvalue *)

let rec is_lvalue e =
  match e.edesc with
  | EVar id -> true
  | EUnop((Oderef | Oarrow _), _) -> true
  | EUnop(Odot _, e') -> is_lvalue e'
  | EBinop(Oindex, _, _, _) -> true
  | _ -> false

(* Check that a C expression is a modifiable l-value: an l-value
   whose type is not const, neither an array type, nor a function type,
   nor an incomplete type. *)

let is_modifiable_lvalue env e =
  is_lvalue e
  && not (List.mem AConst (attributes_of_type env e.etyp))
  && not (incomplete_type env e.etyp)
  && begin match unroll env e.etyp with
     | TFun _ | TArray _ -> false
     | _ -> true
     end

(* Check that a C expression is the literal "0", which can be used
   as a pointer. *)

let is_literal_0 e =
  match e.edesc with
  | EConst(CInt(0L, _, _)) -> true
  | _ -> false

(* Assignment compatibility check over attributes.
   Standard attributes ("const", "volatile", "restrict") can safely
   be added (to the rhs type to get the lhs type) but must not be dropped.
   Custom attributes can safely be dropped but must not be added. *)

let valid_assignment_attr afrom ato =
  let is_covariant = function Attr _ -> false | _ -> true in
  let (afrom1, afrom2) = List.partition is_covariant afrom
  and (ato1, ato2) = List.partition is_covariant ato in
  incl_attributes afrom1 ato1 && incl_attributes ato2 afrom2

(* Check that an assignment is allowed *)

let valid_assignment env from tto =
  match pointer_decay env from.etyp, pointer_decay env tto with
  | (TInt _ | TFloat _ | TEnum _), (TInt _ | TFloat _ | TEnum _) -> true
  | TInt _, TPtr _ -> is_literal_0 from
  | TPtr(ty, _), TPtr(ty', _) ->
      valid_assignment_attr (attributes_of_type env ty)
                            (attributes_of_type env ty')
      && (is_void_type env ty || is_void_type env ty'
          || compatible_types env
               (erase_attributes_type env ty)
               (erase_attributes_type env ty'))
  | TStruct(s, _), TStruct(s', _) -> s = s'
  | TUnion(s, _), TUnion(s', _) -> s = s'
  | _, _ -> false

(* Check that a cast is allowed *)

let valid_cast env tfrom tto =
  compatible_types ~noattrs:true env tfrom tto ||
  begin match unroll env tfrom, unroll env tto with
  | _, TVoid _ -> true
  (* from any int-or-pointer (with array and functions decaying to pointers)
     to any int-or-pointer *)
  | (TInt _ | TPtr _ | TArray _ | TFun _ | TEnum _), (TInt _ | TPtr _ | TEnum _) -> true
  (* between int and float types *)
  | (TInt _ | TFloat _ | TEnum _), (TInt _ | TFloat _ | TEnum _) -> true
  | _, _ -> false
  end

(* Construct an integer constant *)

let intconst v ik =
  { edesc = EConst(CInt(v, ik, "")); etyp = TInt(ik, []) }

(* Construct the 0 float constant of double type *)

let floatconst0 =
  { edesc = EConst(CFloat({hex=false; intPart="0"; fracPart="0"; exp="0"}, FDouble));
    etyp = TFloat(FDouble, []) }

(* Construct the literal "0" with void * type *)

let nullconst =
  { edesc = EConst(CInt(0L, ptr_t_ikind, "0")); etyp = TPtr(TVoid [], []) }

(* Construct a cast expression *)

let ecast ty e = { edesc = ECast(ty, e); etyp = ty }

(* Construct an assignment expression *)

let eassign e1 e2 = { edesc = EBinop(Oassign, e1, e2, e1.etyp); etyp = e1.etyp }

(* Construct a "," expression *)

let ecomma e1 e2 = { edesc = EBinop(Ocomma, e1, e2, e2.etyp); etyp = e2.etyp }

(* Construct an address-of expression.  Can be applied not just to
   an l-value but also to a sequence or a conditional of l-values. *)

let rec eaddrof e =
  match e.edesc with
  | EUnop(Oderef, e1) -> e1
  | EBinop(Ocomma, e1, e2, _) -> ecomma e1 (eaddrof e2)
  | EConditional(e1, e2, e3) -> 
      { edesc = EConditional(e1, eaddrof e2, eaddrof e3); etyp = TPtr(e.etyp, []) }
  | _ -> { edesc = EUnop(Oaddrof, e); etyp = TPtr(e.etyp, []) }

(* Construct a sequence *)

let sseq loc s1 s2 =
  match s1.sdesc, s2.sdesc with
  | Sskip, _ -> s2
  | _, Sskip -> s1
  | _, Sblock sl -> { sdesc = Sblock(s1 :: sl); sloc = loc }
  | _, _ -> { sdesc = Sseq(s1, s2); sloc = loc }

(* Construct an assignment statement *)

let sassign loc lv rv =
  { sdesc = Sdo (eassign lv rv); sloc = loc }

(* Empty location *)

let no_loc = ("", -1)

(* Dummy skip statement *)

let sskip = { sdesc = Sskip; sloc = no_loc }

(* Print a location *)

let printloc oc (filename, lineno) =
  if filename <> "" then Printf.fprintf oc "%s:%d: " filename lineno

(* Format a location *)

let formatloc pp (filename, lineno) =
  if filename <> "" then Format.fprintf pp "%s:%d: " filename lineno


