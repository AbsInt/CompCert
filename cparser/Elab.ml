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

(* Elaboration from Cabs parse tree to C simplified, typed syntax tree *)

(* Numbered references are to sections of the ISO C99 standard *)

open Format
open Machine
open Cabs
open Cabshelper
open C
open Cutil
open Env

(** * Utility functions *)

(* Error reporting  *)

let fatal_error loc fmt =
  Cerrors.fatal_error ("%a: Error:@ " ^^ fmt) format_cabsloc loc

let error loc fmt =
  Cerrors.error ("%a: Error:@ " ^^ fmt) format_cabsloc loc

let warning loc fmt =
  Cerrors.warning ("%a: Warning:@ " ^^ fmt) format_cabsloc loc

(* Error reporting for Env functions *)

let wrap fn loc env arg =
  try fn env arg
  with Env.Error msg -> fatal_error loc "%s" (Env.error_message msg)

(* Translation of locations *)

let elab_loc l = (l.filename, l.lineno)

(* Buffering of the result (a list of topdecl *)

let top_declarations = ref ([] : globdecl list)

let emit_elab loc td =
  let loc = elab_loc loc in
  top_declarations := { gdesc = td; gloc = loc } :: !top_declarations

let reset() = top_declarations := []

let elaborated_program () =
  let p = !top_declarations in
  top_declarations := [];
  (* Reverse it and eliminate unreferenced declarations *)
  Cleanup.program p

(* Monadic map for functions env -> 'a -> 'b * env *)

let rec mmap f env = function
  | [] -> ([], env)
  | hd :: tl ->
      let (hd', env1) = f env hd in
      let (tl', env2) = mmap f env1 tl in
      (hd' :: tl', env2)

(* To detect redefinitions within the same scope *)

let previous_def fn env arg =
  try
    Some (fn env arg)
  with Env.Error _ ->
    None

let redef fn env arg =
  match previous_def fn env arg with
  | None -> false
  | Some(id, info) -> Env.in_current_scope env id

(* Forward declarations *)

let elab_expr_f : (cabsloc -> Env.t -> Cabs.expression -> C.exp) ref
  = ref (fun _ _ _ -> assert false)

let elab_funbody_f : (C.typ -> Env.t -> statement -> C.stmt) ref
  = ref (fun _ _ _ -> assert false)


(** * Elaboration of constants - C99 section 6.4.4 *)

let has_suffix s suff = 
  let ls = String.length s and lsuff = String.length suff in
  ls >= lsuff && String.sub s (ls - lsuff) lsuff = suff

let chop_last s n =
  assert (String.length s >= n);
  String.sub s 0 (String.length s - n)

let has_prefix s pref = 
  let ls = String.length s and lpref = String.length pref in
  ls >= lpref && String.sub s 0 lpref = pref

let chop_first s n =
  assert (String.length s >= n);
  String.sub s n (String.length s - n)

exception Overflow
exception Bad_digit

let parse_int base s =
  let max_val = (* (2^64-1) / base, unsigned *)
    match base with
    |  8 -> 2305843009213693951L
    | 10 -> 1844674407370955161L
    | 16 -> 1152921504606846975L
    |  _ -> assert false in
  let v = ref 0L in
  for i = 0 to String.length s - 1 do
    if !v > max_val then raise Overflow;
    v := Int64.mul !v (Int64.of_int base);
    let c = s.[i] in
    let digit =
      if c >= '0' && c <= '9' then Char.code c - 48
      else if c >= 'A' && c <= 'F' then Char.code c - 55
      else raise Bad_digit in
    if digit >= base then raise Bad_digit;
    v := Int64.add !v (Int64.of_int digit)
  done;
  !v

let integer_representable v ik =
  let bitsize = sizeof_ikind ik * 8
  and signed = is_signed_ikind ik in
  if bitsize >= 64 then
    (not signed) || (v >= 0L && v <= 0x7FFF_FFFF_FFFF_FFFFL)
  else if not signed then
    v >= 0L && v < Int64.shift_left 1L bitsize
  else
    v >= 0L && v < Int64.shift_left 1L (bitsize - 1)

let elab_int_constant loc s0 =
  let s = String.uppercase s0 in
  (* Determine possible types and chop type suffix *)
  let (s, dec_kinds, hex_kinds) =
    if has_suffix s "ULL" || has_suffix s "LLU" then
      (chop_last s 3, [IULongLong], [IULongLong])
    else if has_suffix s "LL" then
      (chop_last s 2, [ILongLong], [ILongLong; IULongLong])
    else if has_suffix s "UL" || has_suffix s "LU" then
      (chop_last s 2, [IULong; IULongLong], [IULong; IULongLong])
    else if has_suffix s "L" then
      (chop_last s 1, [ILong; ILongLong],
                      [ILong; IULong; ILongLong; IULongLong])
    else if has_suffix s "U" then
      (chop_last s 1, [IUInt; IULong; IULongLong],
                      [IUInt; IULong; IULongLong])
    else
      (s, [IInt; ILong; ILongLong],
          [IInt; IUInt; ILong; IULong; ILongLong; IULongLong])
  in
  (* Determine base *)
  let (s, base) =
    if has_prefix s "0X" then
      (chop_first s 2, 16)
    else if has_prefix s "0" then
      (chop_first s 1, 8)
    else
      (s, 10)
  in
  (* Parse digits *)
  let v =
    try parse_int base s
    with
    | Overflow ->
        error loc "integer literal '%s' is too large" s0;
        0L
    | Bad_digit ->
        error loc "bad digit in integer literal '%s'" s0;
        0L
  in
  (* Find smallest allowable type that fits *)
  let ty =
    try List.find (fun ty -> integer_representable v ty) 
                  (if base = 10 then dec_kinds else hex_kinds)
    with Not_found ->
      error loc "integer literal '%s' cannot be represented" s0;
      IInt
  in
  (v, ty)

let elab_float_constant loc f =
  let ty = match f.suffix_FI with
    | Some ("l"|"L") -> FLongDouble
    | Some ("f"|"F") -> FFloat
    | None -> FDouble
    | _ -> assert false (* The lexer should not accept anything else. *)
  in
  let v = {
    hex=f.isHex_FI;
    intPart=begin match f.integer_FI with Some s -> s | None -> "0" end;
    fracPart=begin match f.fraction_FI with Some s -> s | None -> "0" end;
    exp=begin match f.exponent_FI with Some s -> s | None -> "0" end }
  in
  (v, ty)

let elab_char_constant loc wide chars =
  let nbits = if wide then 8 * !config.sizeof_wchar else 8 in
  (* Treat multi-char constants as a number in base 2^nbits *)
  let max_digit = Int64.shift_left 1L nbits in
  let max_val = Int64.shift_left 1L (64 - nbits) in
  let v =
    List.fold_left 
      (fun acc d ->
        if acc >= max_val then
          error loc "character constant overflows";
        if d >= max_digit then
          warning loc "escape sequence is out of range (code 0x%LX)" d;
        Int64.add (Int64.shift_left acc nbits) d)
      0L chars in
  if not (integer_representable v IInt) then
    warning loc "character constant cannot be represented at type 'int'";
  (* C99 6.4.4.4 item 10: single character -> represent at type char *)
  Ceval.normalize_int v (if List.length chars = 1 then IChar else IInt)

let elab_string_literal loc wide chars =
  let nbits = if wide then 8 * !config.sizeof_wchar else 8 in 
  let char_max = Int64.shift_left 1L nbits in
  List.iter
    (fun c ->
      if c < 0L || c >= char_max
      then warning loc "escape sequence is out of range (code 0x%LX)" c)
    chars;
  if wide then
    CWStr chars
  else begin
    let res = String.create (List.length chars) in
    List.iteri
      (fun i c -> res.[i] <- Char.chr (Int64.to_int c))
      chars;
    CStr res
  end

let elab_constant loc = function
  | CONST_INT s ->
      let (v, ik) = elab_int_constant loc s in
      CInt(v, ik, s)
  | CONST_FLOAT f ->
      let (v, fk) = elab_float_constant loc f in
      CFloat(v, fk)
  | CONST_CHAR(wide, s) ->
      CInt(elab_char_constant loc wide s, IInt, "")
  | CONST_STRING(wide, s) ->
      elab_string_literal loc wide s


(** * Elaboration of type expressions, type specifiers, name declarations *)

(* Elaboration of attributes *)

exception Wrong_attr_arg

let elab_attr_arg loc env a =
  match a with
  | VARIABLE s ->
      begin try
        match Env.lookup_ident env s with
        | (id, II_ident(sto, ty)) ->  AIdent s
        | (id, II_enum v) -> AInt v
      with Env.Error _ ->
        AIdent s
      end
  | _ ->
      let b = !elab_expr_f loc env a in
      match Ceval.constant_expr env b.etyp b with
      | Some(CInt(n, _, _)) -> AInt n
      | Some(CStr s) -> AString s
      | _ -> raise Wrong_attr_arg

let elab_gcc_attr_word = function
  | GCC_ATTR_IDENT s -> s
  | GCC_ATTR_CONST -> "const"
  | GCC_ATTR_PACKED -> "__packed__"

let elab_gcc_attr loc env = function
  | GCC_ATTR_EMPTY -> []
  | GCC_ATTR_NOARGS w ->
      let v = elab_gcc_attr_word w in
      [Attr(v, [])]
  | GCC_ATTR_ARGS (w, args) ->
      let v = elab_gcc_attr_word w in
      begin try
        [Attr(v, List.map (elab_attr_arg loc env) args)]
      with Wrong_attr_arg ->
        warning loc "cannot parse '%s' attribute, ignored" v; []
      end

let is_power_of_two n = n > 0L && Int64.(logand n (pred n)) = 0L

let extract_alignas loc a =
  match a with
  | Attr(("aligned"|"__aligned__"), args) ->
      begin match args with
      | [AInt n] when is_power_of_two n -> AAlignas (Int64.to_int n)
      | _ -> warning loc "bad 'aligned' attribute, ignored"; a
      end
  | _ -> a

let elab_attribute env = function
  | GCC_ATTR (l, loc) ->
      List.fold_left add_attributes []
        (List.map (fun attr -> [attr])
           (List.map (extract_alignas loc)
              (List.flatten
                 (List.map (elab_gcc_attr loc env) l))))
  | PACKED_ATTR (args, loc) ->
      [Attr("__packed__", List.map (elab_attr_arg loc env) args)]
  | ALIGNAS_ATTR ([a], loc) ->
      begin match elab_attr_arg loc env a with
      | AInt n when is_power_of_two n -> [AAlignas (Int64.to_int n)]
      | _ -> warning loc "bad _Alignas value, ignored"; []
      end
  | ALIGNAS_ATTR (_, loc) ->
      warning loc "_Alignas takes exactly one parameter, ignored"; []

let elab_attributes env al =
  List.fold_left add_attributes [] (List.map (elab_attribute env) al)

(* Auxiliary for typespec elaboration *)

let typespec_rank = function (* Don't change this *)
  | Cabs.Tvoid -> 0
  | Cabs.Tsigned -> 1
  | Cabs.Tunsigned -> 2
  | Cabs.Tchar -> 3
  | Cabs.Tshort -> 4
  | Cabs.Tlong -> 5
  | Cabs.Tint -> 6
  | Cabs.Tfloat -> 8
  | Cabs.Tdouble -> 9
  | Cabs.T_Bool -> 10
  | _ -> 11 (* There should be at most one of the others *)

let typespec_order t1 t2 = compare (typespec_rank t1) (typespec_rank t2)

(* Elaboration of a type specifier.  Returns 5-tuple:
     (storage class, "inline" flag, "typedef" flag, elaborated type, new env)
   Optional argument "only" is true if this is a standalone
   struct or union declaration, without variable names.
   C99 section 6.7.2.
*)

let rec elab_specifier ?(only = false) loc env specifier =
  (* We first divide the parts of the specifier as follows:
       - a storage class
       - a set of attributes (const, volatile, restrict)
       - a list of type specifiers *)
  let sto = ref Storage_default
  and inline = ref false
  and attr = ref []
  and tyspecs = ref [] 
  and typedef = ref false in

  let do_specifier = function
  | SpecCV cv ->
      attr := add_attributes (elab_cvspec env cv) !attr
  | SpecStorage st ->
      if !sto <> Storage_default && st <> TYPEDEF then
        error loc "multiple storage specifiers";
      begin match st with
      | AUTO -> ()
      | STATIC -> sto := Storage_static
      | EXTERN -> sto := Storage_extern
      | REGISTER -> sto := Storage_register
      | TYPEDEF -> 
          if !typedef then
            error loc "multiple uses of 'typedef'";
          typedef := true
      end
  | SpecInline -> inline := true
  | SpecType tys -> tyspecs := tys :: !tyspecs in

  List.iter do_specifier specifier;

  let simple ty = (!sto, !inline, !typedef, add_attributes_type !attr ty, env) in

  (* As done in CIL, partition !attr into type-related attributes,
     which are returned, and other attributes, which are left in !attr.
     The returned type-related attributes are applied to the
     struct/union/enum being defined.
     The leftover non-type-related attributes will be applied
     to the variable being defined. *)
  let get_type_attrs () =
    let (ta, nta) = List.partition attr_is_type_related !attr in
    attr := nta;
    ta in

  (* Now interpret the list of type specifiers.  Much of this code
     is stolen from CIL. *)
  match List.stable_sort typespec_order (List.rev !tyspecs) with
    | [Cabs.Tvoid] -> simple (TVoid [])

    | [Cabs.T_Bool] -> simple (TInt(IBool, []))
    | [Cabs.Tchar] -> simple (TInt(IChar, []))
    | [Cabs.Tsigned; Cabs.Tchar] -> simple (TInt(ISChar, []))
    | [Cabs.Tunsigned; Cabs.Tchar] -> simple (TInt(IUChar, []))

    | [Cabs.Tshort] -> simple (TInt(IShort, []))
    | [Cabs.Tsigned; Cabs.Tshort] -> simple (TInt(IShort, []))
    | [Cabs.Tshort; Cabs.Tint] -> simple (TInt(IShort, []))
    | [Cabs.Tsigned; Cabs.Tshort; Cabs.Tint] -> simple (TInt(IShort, []))

    | [Cabs.Tunsigned; Cabs.Tshort] -> simple (TInt(IUShort, []))
    | [Cabs.Tunsigned; Cabs.Tshort; Cabs.Tint] -> simple (TInt(IUShort, []))

    | [] -> simple (TInt(IInt, []))
    | [Cabs.Tint] -> simple (TInt(IInt, []))
    | [Cabs.Tsigned] -> simple (TInt(IInt, []))
    | [Cabs.Tsigned; Cabs.Tint] -> simple (TInt(IInt, []))

    | [Cabs.Tunsigned] -> simple (TInt(IUInt, []))
    | [Cabs.Tunsigned; Cabs.Tint] -> simple (TInt(IUInt, []))

    | [Cabs.Tlong] -> simple (TInt(ILong, []))
    | [Cabs.Tsigned; Cabs.Tlong] -> simple (TInt(ILong, []))
    | [Cabs.Tlong; Cabs.Tint] -> simple (TInt(ILong, []))
    | [Cabs.Tsigned; Cabs.Tlong; Cabs.Tint] -> simple (TInt(ILong, []))

    | [Cabs.Tunsigned; Cabs.Tlong] -> simple (TInt(IULong, []))
    | [Cabs.Tunsigned; Cabs.Tlong; Cabs.Tint] -> simple (TInt(IULong, []))

    | [Cabs.Tlong; Cabs.Tlong] -> simple (TInt(ILongLong, []))
    | [Cabs.Tsigned; Cabs.Tlong; Cabs.Tlong] -> simple (TInt(ILongLong, []))
    | [Cabs.Tlong; Cabs.Tlong; Cabs.Tint] -> simple (TInt(ILongLong, []))
    | [Cabs.Tsigned; Cabs.Tlong; Cabs.Tlong; Cabs.Tint] -> simple (TInt(ILongLong, []))

    | [Cabs.Tunsigned; Cabs.Tlong; Cabs.Tlong] -> simple (TInt(IULongLong, []))
    | [Cabs.Tunsigned; Cabs.Tlong; Cabs.Tlong; Cabs.Tint] -> simple (TInt(IULongLong, []))

    | [Cabs.Tfloat] -> simple (TFloat(FFloat, []))
    | [Cabs.Tdouble] -> simple (TFloat(FDouble, []))

    | [Cabs.Tlong; Cabs.Tdouble] -> simple (TFloat(FLongDouble, []))

    (* Now the other type specifiers *)

    | [Cabs.Tnamed id] ->
        let (id', info) = wrap Env.lookup_typedef loc env id in
        simple (TNamed(id', []))

    | [Cabs.Tstruct_union(STRUCT, id, optmembers, a)] ->
        let a' =
          add_attributes (get_type_attrs()) (elab_attributes env a) in
        let (id', env') =
          elab_struct_or_union only Struct loc id optmembers a' env in
        (!sto, !inline, !typedef, TStruct(id', !attr), env')

    | [Cabs.Tstruct_union(UNION, id, optmembers, a)] ->
        let a' =
          add_attributes (get_type_attrs()) (elab_attributes env a) in
        let (id', env') =
          elab_struct_or_union only Union loc id optmembers a' env in
        (!sto, !inline, !typedef, TUnion(id', !attr), env')

    | [Cabs.Tenum(id, optmembers, a)] ->
        let a' =
          add_attributes (get_type_attrs()) (elab_attributes env a) in
        let (id', env') =
          elab_enum only loc id optmembers a' env in
        (!sto, !inline, !typedef, TEnum(id', !attr), env')

    (* Specifier doesn't make sense *)
    | _ ->
        fatal_error loc "illegal combination of type specifiers"

(* Elaboration of a type qualifier. *)

and elab_cvspec env = function
  | CV_CONST -> [AConst]
  | CV_VOLATILE -> [AVolatile]
  | CV_RESTRICT -> [ARestrict]
  | CV_ATTR attr -> elab_attribute env attr

(* Elaboration of a type declarator.  C99 section 6.7.5. *)

and elab_type_declarator loc env ty = function
  | Cabs.JUSTBASE ->
      (ty, env)
  | Cabs.ARRAY(d, cv_specs, sz) ->
      let a = List.fold_left add_attributes [] (List.map (elab_cvspec env) cv_specs) in
      let sz' =
        match sz with
        | None ->
            None
        | Some sz ->
            match Ceval.integer_expr env (!elab_expr_f loc env sz) with
            | Some n ->
                if n < 0L then error loc "array size is negative";
                if n = 0L then warning loc "array of size 0";
                Some n
            | None ->
                error loc "array size is not a compile-time constant";
                Some 1L in (* produces better error messages later *)
       elab_type_declarator loc env (TArray(ty, sz', a)) d
  | Cabs.PTR(cv_specs, d) ->
      let a = List.fold_left add_attributes [] (List.map (elab_cvspec env) cv_specs) in
      elab_type_declarator loc env (TPtr(ty, a)) d
  | Cabs.PROTO(d, (params, vararg)) ->
       begin match unroll env ty with
       | TArray _ | TFun _ ->
           error loc "illegal function return type@ %a" Cprint.typ ty
       | _ -> ()
       end;
       let params' = elab_parameters env params in
       elab_type_declarator loc env (TFun(ty, params', vararg, [])) d

(* Elaboration of parameters in a prototype *)

and elab_parameters env params =
  match params with
  | [] -> (* old-style K&R prototype *)
      None
  | _ ->
      (* Prototype introduces a new scope *)
      let (vars, _) = mmap elab_parameter (Env.new_scope env) params in
      (* Catch special case f(void) *)
      match vars with
        | [ ( {name=""}, TVoid _) ] -> Some []
        | _ -> Some vars

(* Elaboration of a function parameter *)

and elab_parameter env (PARAM (spec, id, decl, attr, loc)) =
  let (sto, inl, tydef, bty, env1) = elab_specifier loc env spec in
  if tydef then
    error loc "'typedef' used in function parameter";
  let (ty, env2) = elab_type_declarator loc env1 bty decl in
  let ty = add_attributes_type (elab_attributes env attr) ty in
  if sto <> Storage_default && sto <> Storage_register then
    error loc
      "'extern' or 'static' storage not supported for function parameter";
  if inl then
    error loc "'inline' can only appear on functions";
  let id = match id with None -> "" | Some id -> id in
  if id <> "" && redef Env.lookup_ident env id then
    error loc "redefinition of parameter '%s'" id;
  (* replace array and function types by pointer types *)
  let ty1 = argument_conversion env1 ty in
  let (id', env2) = Env.enter_ident env1 id sto ty1 in
  ( (id', ty1) , env2 )

(* Elaboration of a (specifier, Cabs "name") pair *)

and elab_name env spec (Name (id, decl, attr, loc)) =
  let (sto, inl, tydef, bty, env') = elab_specifier loc env spec in
  if tydef then
    error loc "'typedef' is forbidden here";
  let (ty, env'') = elab_type_declarator loc env' bty decl in 
  let a = elab_attributes env attr in
  (id, sto, inl, add_attributes_type a ty, env'')

(* Elaboration of a name group.  C99 section 6.7.6 *)

and elab_name_group loc env (spec, namelist) =
  let (sto, inl, tydef, bty, env') =
    elab_specifier loc env spec in
  if tydef then
    error loc "'typedef' is forbidden here";
  if inl then
    error loc "'inline' is forbidden here";
  let elab_one_name env (Name (id, decl, attr, loc)) =
    let (ty, env1) =
      elab_type_declarator loc env bty decl in 
    let a = elab_attributes env attr in
    ((id, add_attributes_type a ty), env1) in
  (mmap elab_one_name env' namelist, sto)

(* Elaboration of an init-name group *)

and elab_init_name_group loc env (spec, namelist) =
  let (sto, inl, tydef, bty, env') =
    elab_specifier ~only:(namelist=[]) loc env spec in
  let elab_one_name env (Init_name (Name (id, decl, attr, loc), init)) =
    let (ty, env1) =
      elab_type_declarator loc env bty decl in 
    let a = elab_attributes env attr in
    if inl && not (is_function_type env ty) then
      error loc "'inline' can only appear on functions";
    ((id, add_attributes_type a ty, init), env1) in
  (mmap elab_one_name env' namelist, sto, tydef)

(* Elaboration of a field group *)

and elab_field_group env (Field_group (spec, fieldlist, loc)) =
  let fieldlist = List.map (
    function
      | (None, x) -> (Name ("", JUSTBASE, [], cabslu), x)
      | (Some n, x) -> (n, x))
    fieldlist
  in

  let ((names, env'), sto) =
    elab_name_group loc env (spec, List.map fst fieldlist) in

  if sto <> Storage_default then
    error loc "non-default storage in struct or union";

  let elab_bitfield (Name (_, _, _, loc), optbitsize) (id, ty) =
    let optbitsize' =
      match optbitsize with
      | None -> None
      | Some sz ->
          let ik =
            match unroll env' ty with
            | TInt(ik, _) -> ik
            | TEnum(_, _) -> enum_ikind
            | _ -> ILongLong (* trigger next error message *) in
          if integer_rank ik > integer_rank IInt then begin
            error loc
              "the type of bitfield '%s' must be an integer type \
               no bigger than 'int'" id;
            None
          end else begin
            match Ceval.integer_expr env' (!elab_expr_f loc env sz) with
            | Some n ->
                if n < 0L then begin
                  error loc "bit size of '%s' (%Ld) is negative" id n;
                  None
                end else
                if n > Int64.of_int(sizeof_ikind ik * 8) then begin
                  error loc "bit size of '%s' (%Ld) exceeds its type" id n;
                  None
                end else
                if n = 0L && id <> "" then begin
                  error loc "member '%s' has zero size" id;
                  None
                end else
                  Some(Int64.to_int n)
            | None ->
                error loc "bit size of '%s' is not a compile-time constant" id;
                None
          end in
    { fld_name = id; fld_typ = ty; fld_bitfield = optbitsize' } 
  in
  (List.map2 elab_bitfield fieldlist names, env')

(* Elaboration of a struct or union. C99 section 6.7.2.1 *)

and elab_struct_or_union_info kind loc env members attrs =
  let (m, env') = mmap elab_field_group env members in
  let m = List.flatten m in
  (* Check for incomplete types *)
  let rec check_incomplete = function
  | [] -> ()
  | [ { fld_typ = TArray(ty_elt, None, _) } ] when kind = Struct -> ()
        (* C99: ty[] allowed as last field of a struct *)
  | fld :: rem ->
      if wrap incomplete_type loc env' fld.fld_typ then
        error loc "member '%s' has incomplete type" fld.fld_name;
      check_incomplete rem in
  check_incomplete m;
  (* Warn for empty structs or unions *)
  if m = [] then
    warning loc "empty %s" (if kind = Struct then "struct" else "union");
  (composite_info_def env' kind attrs m, env')

and elab_struct_or_union only kind loc tag optmembers attrs env =
  let warn_attrs () =
    if attrs <> [] then
      warning loc "attributes over struct/union ignored in this context" in
  let optbinding, tag =
    match tag with
      | None -> None, ""
      | Some s ->
          Env.lookup_composite env s, s
  in
  match optbinding, optmembers with
  | Some(tag', ci), None
    when (not only) || Env.in_current_scope env tag' ->
      (* Reference to an already declared struct or union.
         Special case: if this is an "only" declaration (without variable names)
         and the composite was bound in another scope,
         create a new incomplete composite instead via the case
         "_, None" below. *)
      warn_attrs();
      (tag', env)
  | Some(tag', ({ci_sizeof = None} as ci)), Some members
    when Env.in_current_scope env tag' ->
      if ci.ci_kind <> kind then
        error loc "struct/union mismatch on tag '%s'" tag;
      (* finishing the definition of an incomplete struct or union *)
      let (ci', env') = elab_struct_or_union_info kind loc env members attrs in
      (* Emit a global definition for it *)
      emit_elab loc (Gcompositedef(kind, tag', attrs, ci'.ci_members));
      (* Replace infos but keep same ident *)
      (tag', Env.add_composite env' tag' ci')
  | Some(tag', {ci_sizeof = Some _}), Some _
    when Env.in_current_scope env tag' ->
      error loc "redefinition of struct or union '%s'" tag;
      (tag', env)
  | _, None ->
      (* declaration of an incomplete struct or union *)
      if tag = "" then
        error loc "anonymous, incomplete struct or union";
      let ci = composite_info_decl env kind attrs in
      (* enter it with a new name *)
      let (tag', env') = Env.enter_composite env tag ci in
      (* emit it *)
      emit_elab loc (Gcompositedecl(kind, tag', attrs));
      (tag', env')
  | _, Some members ->
      (* definition of a complete struct or union *)
      let ci1 = composite_info_decl env kind attrs in
      (* enter it, incomplete, with a new name *)
      let (tag', env') = Env.enter_composite env tag ci1 in
      (* emit a declaration so that inner structs and unions can refer to it *)
      emit_elab loc (Gcompositedecl(kind, tag', attrs));
      (* elaborate the members *)
      let (ci2, env'') =
        elab_struct_or_union_info kind loc env' members attrs in
      (* emit a definition *)
      emit_elab loc (Gcompositedef(kind, tag', attrs, ci2.ci_members));
      (* Replace infos but keep same ident *)
      (tag', Env.add_composite env'' tag' ci2)

(* Elaboration of an enum item.  C99 section 6.7.2.2 *)

and elab_enum_item env ((s, exp), loc) nextval =
  let (v, exp') =
    match exp with
    | None ->
        (nextval, None)
    | Some exp ->
        let exp' = !elab_expr_f loc env exp in
        match Ceval.integer_expr env exp' with
        | Some n -> (n, Some exp')
        | None ->
            error loc
              "value of enumerator '%s' is not a compile-time constant" s;
            (nextval, Some exp') in
  if redef Env.lookup_ident env s then
    error loc "redefinition of enumerator '%s'" s;
  if not (int_representable v (8 * sizeof_ikind enum_ikind) (is_signed_ikind enum_ikind)) then
     warning loc "the value of '%s' is not representable with type %a"
                 s Cprint.typ (TInt(enum_ikind, []));
  let (id, env') = Env.enter_enum_item env s v in
  ((id, v, exp'), Int64.succ v, env')

(* Elaboration of an enumeration declaration.   C99 section 6.7.2.2  *)

and elab_enum only loc tag optmembers attrs env =
  let tag = match tag with None -> "" | Some s -> s in
  match optmembers with
  | None ->
    if only then
      fatal_error loc
         "forward declaration of 'enum %s' is not allowed in ISO C" tag;
      let (tag', info) = wrap Env.lookup_enum loc env tag in (tag', env)
  | Some members ->
      if tag <> "" && redef Env.lookup_enum env tag then
        error loc "redefinition of 'enum %s'" tag;
      let rec elab_members env nextval = function
      | [] -> ([], env)
      | hd :: tl ->
          let (dcl1, nextval1, env1) = elab_enum_item env hd nextval in
          let (dcl2, env2) = elab_members env1 nextval1 tl in
          (dcl1 :: dcl2, env2) in
      let (dcls, env') = elab_members env 0L members in
      let info = { ei_members = dcls; ei_attr = attrs } in
      let (tag', env'') = Env.enter_enum env' tag info in
      emit_elab loc (Genumdef(tag', attrs, dcls));
      (tag', env'')

(* Elaboration of a naked type, e.g. in a cast *)

let elab_type loc env spec decl =
  let (sto, inl, tydef, bty, env') = elab_specifier loc env spec in
  let (ty, env'') = elab_type_declarator loc env' bty decl in 
  if sto <> Storage_default || inl || tydef then
    error loc "'typedef', 'extern', 'static', 'register' and 'inline' are meaningless in cast";
  ty


(* Elaboration of initializers. C99 section 6.7.8 *)

let init_char_array_string opt_size s =
  let len = Int64.of_int (String.length s) in
  let size =
    match opt_size with
    | Some sz -> sz
    | None -> Int64.succ len  (* include final 0 character *) in
  let rec add_chars i init =
    if i < 0L then init else begin
      let c =
        if i < len then Int64.of_int (Char.code s.[Int64.to_int i]) else 0L in
      add_chars (Int64.pred i) (Init_single (intconst c IInt) :: init)
    end in
  Init_array (add_chars (Int64.pred size) [])

let init_int_array_wstring opt_size s =
  let len = Int64.of_int (List.length s) in
  let size =
    match opt_size with
    | Some sz -> sz
    | None -> Int64.succ len  (* include final 0 character *) in
  let rec add_chars i s init =
    if i < 0L then init else begin
      let (c, s') =
        match s with [] -> (0L, []) | c::s' -> (c, s') in
      add_chars (Int64.pred i) s' (Init_single (intconst c IInt) :: init)
    end in
  Init_array (add_chars (Int64.pred size) (List.rev s) [])

let check_init_type loc env a ty =
  if valid_assignment env a ty then ()
  else if valid_cast env a.etyp ty then
    warning loc
      "initializer has type@ %a@ instead of the expected type @ %a"
      Cprint.typ a.etyp Cprint.typ ty
  else
    error loc
      "initializer has type@ %a@ instead of the expected type @ %a"
      Cprint.typ a.etyp Cprint.typ ty

(* Representing initialization state using zippers *)

module I = struct

  type zipinit =
    | Ztop of string * typ

    | Zarray of zipinit                 (* ancestor *)
              * typ                     (* type of elements *)
              * int64 option            (* size *)
              * init                    (* default initializer *)
              * init list               (* elements before point, reversed *)
              * int64                   (* position of point *)
              * init list               (* elements after point *)

    | Zstruct of zipinit                (* ancestor *)
               * ident                  (* struct type *)
               * (field * init) list    (* elements before current, reversed *)
               * field                  (* current field *)
               * (field * init) list    (* elements after current *)

    | Zunion of zipinit                 (* ancestor *)
              * ident                   (* union type *)
              * field                   (* current member *)

  type state = zipinit * init        (* current point & init for this point *)

  (* The initial state: default initialization, current point at top *)
  let top env name ty = (Ztop(name, ty), default_init env ty)

  (* Change the initializer for the current point *)
  let set (z, i) i' = (z, i')

  (* Put the current point back to the top *)
  let rec to_top = function
    | Ztop(name, ty), i as zi -> zi
    | Zarray(z, ty, sz, dfl, before, idx, after), i ->
        to_top (z, Init_array (List.rev_append before (i :: after)))
    | Zstruct(z, id, before, fld, after), i ->
        to_top (z, Init_struct(id, List.rev_append before ((fld, i) :: after)))
    | Zunion(z, id, fld), i ->
        to_top (z, Init_union(id, fld, i))

  (* Extract the initializer corresponding to the current state *)
  let to_init zi = snd (to_top zi)

  (* The type of the current point *)
  let typeof = function
    | Ztop(name, ty), i -> ty
    | Zarray(z, ty, sz, dfl, before, idx, after), i -> ty
    | Zstruct(z, id, before, fld, after), i -> fld.fld_typ
    | Zunion(z, id, fld), i -> fld.fld_typ

  (* The name of the path leading to the current point, for error reporting *)
  let rec zipname = function
    | Ztop(name, ty) -> name
    | Zarray(z, ty, sz, dfl, before, idx, after) ->
        sprintf "%s[%Ld]" (zipname z) idx
    | Zstruct(z, id, before, fld, after) ->
        sprintf "%s.%s" (zipname z) fld.fld_name
    | Zunion(z, id, fld) ->
        sprintf "%s.%s" (zipname z) fld.fld_name

  let name (z, i) = zipname z

  (* Auxiliary functions to deal with arrays *)
  let index_below (idx: int64) (sz: int64 option) =
    match sz with None -> true | Some sz -> idx < sz

  let il_head dfl = function [] -> dfl | i1 :: il -> i1
  let il_tail = function [] -> [] | i1 :: il -> il

  (* Advance the current point to the next point in right-up order.
     Return None if no next point, i.e. we are at top *)
  let rec next = function
    | Ztop(name, ty), i -> None
    | Zarray(z, ty, sz, dfl, before, idx, after), i ->
        let idx' = Int64.succ idx in
        if index_below idx' sz
        then Some(Zarray(z, ty, sz, dfl, i :: before, idx', il_tail after),
                  il_head dfl after)
        else next (z, Init_array (List.rev_append before (i :: after)))
    | Zstruct(z, id, before, fld, []), i ->
        next (z, Init_struct(id, List.rev_append before [(fld, i)]))
    | Zstruct(z, id, before, fld, (fld1, i1) :: after), i ->
        Some(Zstruct(z, id, (fld, i) :: before, fld1, after), i1)
    | Zunion(z, id, fld), i ->
        next (z, Init_union(id, fld, i))

  (* Move the current point "down" to the first component of an array,
     struct, or union.  No effect if the current point is a scalar. *)
  let rec first env (z, i as zi) =
    let ty = typeof zi in
    match unroll env ty, i with
    | TArray(ty, sz, _), Init_array il ->
        if index_below 0L sz then begin
          let dfl = default_init env ty in
          Some(Zarray(z, ty, sz, dfl, [], 0L, il_tail il), il_head dfl il)
        end
        else None
    | TStruct(id, _), Init_struct(id', []) ->
        None
    | TStruct(id, _), Init_struct(id', (fld1, i1) :: flds) ->
        Some(Zstruct(z, id, [], fld1, flds), i1)
    | TUnion(id, _), Init_union(id', fld, i) ->
        begin match (Env.find_union env id).ci_members with
        | [] -> None
        | fld1 :: _ ->
            Some(Zunion(z, id, fld1),
                 if fld.fld_name = fld1.fld_name
                 then i
                 else default_init env fld1.fld_typ)
        end 
    | (TStruct _ | TUnion _), Init_single a ->
        (* This is a previous whole-struct initialization that we
           are going to overwrite.  Revert to the default initializer. *)
        first env (z, default_init env ty)
    | _ ->
        Some (z, i)

  (* Move to the [n]-th element of the current point, which must be
     an array. *)
  let index env (z, i as zi) n =
    match unroll env (typeof zi), i with
    | TArray(ty, sz, _), Init_array il ->
        if n >= 0L && index_below n sz then begin 
          let dfl = default_init env ty in
          let rec loop p before after =
            if p = n then
              Some(Zarray(z, ty, sz, dfl, before, n, il_tail after),
                   il_head dfl after)
            else
              loop (Int64.succ p)
                   (il_head dfl after :: before)
                   (il_tail after)
          in loop 0L [] il
        end else
          None
    | _, _ ->
        None

  (* Move to the member named [name] of the current point, which must be
     a struct or a union. *)
  let rec member env (z, i as zi) name =
    let ty = typeof zi in
    match unroll env ty, i with
    | TStruct(id, _), Init_struct(id', flds) ->
        let rec find before = function
          | [] -> None
          | (fld, i as f_i) :: after ->
              if fld.fld_name = name then
                Some(Zstruct(z, id, before, fld, after), i)
              else
                find (f_i :: before) after
        in find [] flds
    | TUnion(id, _), Init_union(id', fld, i) ->
        if fld.fld_name = name then
          Some(Zunion(z, id, fld), i)
        else begin
          let rec find = function
            | [] -> None
            | fld1 :: rem ->
                if fld1.fld_name = name then
                  Some(Zunion(z, id, fld1), default_init env fld1.fld_typ)
                else
                  find rem
           in find (Env.find_union env id).ci_members
         end
    | (TStruct _ | TUnion _), Init_single a ->
        member env (z, default_init env ty) name
    | _, _ ->
        None
end

(* Interpret the given designator, moving the initialization state [zi]
   "down" accordingly. *)

let rec elab_designator loc env zi desig =
  match desig with
  | [] -> 
      zi
  | INFIELD_INIT name :: desig' ->
      begin match I.member env zi name with
      | Some zi' ->
          elab_designator loc env zi' desig'
      | None ->
          error loc "%s has no member named %s" (I.name zi) name;
          raise Exit
      end
  | ATINDEX_INIT a :: desig' ->
      begin match Ceval.integer_expr env (!elab_expr_f loc env a) with
      | None ->
          error loc "array element designator for %s is not a compile-time constant"
                    (I.name zi);
          raise Exit
      | Some n ->
          match I.index env zi n with
          | Some zi' ->
              elab_designator loc env zi' desig'
          | None ->
              error loc "bad array element designator %Ld within %s"
                      n (I.name zi);
            raise Exit
      end

(* Elaboration of an initialization expression.  Return the corresponding
   initializer. *)

let elab_init loc env root ty_root ie =

(* Perform the initializations described by the list [il] over
   the initialization state [zi].  [first] is true if we are at the
   beginning of a braced initializer.  Returns the final initializer. *)

let rec elab_list zi il first =
  match il with
  | [] ->
      (* All initialization items consumed. *)
      I.to_init zi
  | (desig, item) :: il' ->
      if desig = [] then begin
        match (if first then I.first env zi else I.next zi)
        with
        | None ->
            warning loc "excess elements at end of initializer for %s, ignored"
                        (I.name zi);
            I.to_init zi
        | Some zi' ->
            elab_item zi' item il'
      end else
        elab_item (elab_designator loc env (I.to_top zi) desig) item il'

(* Perform the initialization described by [item] for the current
   subobject of state [zi].  Continue initializing with the list [il]. *)

and elab_item zi item il =
  let ty = I.typeof zi in
  match item, unroll env ty with
  (* Special case char array = "string literal" 
               or wchar array = L"wide string literal" *)
  | (SINGLE_INIT (CONSTANT (CONST_STRING(w, s)))
     | COMPOUND_INIT [_, SINGLE_INIT(CONSTANT (CONST_STRING(w, s)))]),
    TArray(ty_elt, sz, _)
    when is_integer_type env ty_elt ->
      begin match elab_string_literal loc w s, unroll env ty_elt with
      | CStr s, TInt((IChar | ISChar | IUChar), _) ->
          if not (I.index_below (Int64.of_int(String.length s - 1)) sz) then
            warning loc "initializer string for array of chars %s is too long"
                        (I.name zi);
          elab_list (I.set zi (init_char_array_string sz s)) il false
      | CStr _, _ ->
          error loc "initialization of an array of non-char elements with a string literal";
          elab_list zi il false
      | CWStr s, TInt(ik, _) when ik = wchar_ikind ->
          if not (I.index_below (Int64.of_int(List.length s - 1)) sz) then
            warning loc "initializer string for array of wide chars %s is too long"
                        (I.name zi);
          elab_list (I.set zi (init_int_array_wstring sz s)) il false
      | CWStr _, _ ->
          error loc "initialization of an array of non-wchar_t elements with a wide string literal";
          elab_list zi il false
      | _ -> assert false
      end
  (* Brace-enclosed compound initializer *)
  | COMPOUND_INIT il', _ ->
      (* Process the brace-enclosed stuff, obtaining its initializer *)
      let ini' = elab_list (I.top env (I.name zi) ty) il' true in
      (* Initialize current subobject with this state, and continue *)
      elab_list (I.set zi ini') il false
  (* Single expression *)
  | SINGLE_INIT a, _ ->
      let a' = !elab_expr_f loc env a in
      elab_single zi a' il
  (* No initializer: can this happen? *)
  | NO_INIT, _ ->
      elab_list zi il false

(* Perform initialization by a single expression [a] for the current
   subobject of state [zi],  Continue initializing with the list [il']. *)

and elab_single zi a il =
  let ty = I.typeof zi in
  match unroll env ty with
  | TInt _ | TEnum _ | TFloat _ | TPtr _ ->
      (* This is a scalar: do direct initialization and continue *)
      check_init_type loc env a ty;
      elab_list (I.set zi (Init_single a)) il false
  | TStruct _ | TUnion _ when compatible_types ~noattrs:true env ty a.etyp ->
      (* This is a composite that can be initialized directly
         from the expression: do as above *)
      elab_list (I.set zi (Init_single a)) il false
  | TStruct _ | TUnion _ | TArray _ ->
      (* This is an aggregate: we need to drill into it, recursively *)
      begin match I.first env zi with
      | Some zi' ->
          elab_single zi' a il
      | None ->
          error loc "initializer for aggregate %s with no elements requires explicit braces"
                    (I.name zi);
          raise Exit
      end
  | _ ->
      error loc "impossible to initialize %s of type@ %a"
                (I.name zi) Cprint.typ ty;
      raise Exit

(* Start with top-level object initialized to default *)

in elab_item (I.top env root ty_root) ie []

(* Elaboration of a top-level initializer *)

let elab_initial loc env root ty ie =
  match ie with
  | NO_INIT -> None
  | _ ->
    try
      Some (elab_init loc env root ty ie)
    with
    | Exit -> None  (* error was already reported *)
    | Env.Error msg -> error loc "%s" (Env.error_message msg); None

(* Complete an array type with the size obtained from the initializer:
   "int x[] = { 1, 2, 3 }" becomes "int x[3] = ..." *)

let fixup_typ loc env ty init =
  match unroll env ty, init with
  | TArray(ty_elt, None, attr), Init_array il ->
      if il = [] then warning loc "array of size 0";
      TArray(ty_elt, Some(Int64.of_int(List.length il)), attr)
  | _ -> ty

(* Entry point *)

let elab_initializer loc env root ty ie =
  match elab_initial loc env root ty ie with
  | None ->
      (ty, None)
  | Some init ->
      (fixup_typ loc env ty init, Some init)


(* Elaboration of expressions *)

let elab_expr loc env a =

  let err fmt = error loc fmt in  (* non-fatal error *)
  let error fmt = fatal_error loc fmt in
  let warning fmt = warning loc fmt in

  let rec elab = function

(* 6.5.1 Primary expressions *)

  | VARIABLE s ->
      begin match wrap Env.lookup_ident loc env s with
      | (id, II_ident(sto, ty)) ->
          { edesc = EVar id; etyp = ty }
      | (id, II_enum v) ->
          { edesc = EConst(CEnum(id, v)); etyp = TInt(enum_ikind, []) }
      end

  | CONSTANT cst ->
      let cst' = elab_constant loc cst in
      { edesc = EConst cst'; etyp = type_of_constant cst' }

(* 6.5.2 Postfix expressions *)

  | INDEX(a1, a2) ->            (* e1[e2] *)
      let b1 = elab a1 in let b2 = elab a2 in
      let tres =
        match (unroll env b1.etyp, unroll env b2.etyp) with
        | (TPtr(t, _) | TArray(t, _, _)), (TInt _ | TEnum _) -> t
        | (TInt _ | TEnum _), (TPtr(t, _) | TArray(t, _, _)) -> t
        | t1, t2 -> error "incorrect types for array subscripting" in
      { edesc = EBinop(Oindex, b1, b2, TPtr(tres, [])); etyp = tres }

  | MEMBEROF(a1, fieldname) ->
      let b1 = elab a1 in
      let (fld, attrs) =
        match unroll env b1.etyp with
        | TStruct(id, attrs) ->
            (wrap Env.find_struct_member loc env (id, fieldname), attrs)
        | TUnion(id, attrs) ->
            (wrap Env.find_union_member loc env (id, fieldname), attrs)
        | _ ->
            error "left-hand side of '.' is not a struct or union" in
      (* A field of a const/volatile struct or union is itself const/volatile *)
      { edesc = EUnop(Odot fieldname, b1);
        etyp = add_attributes_type (List.filter attr_inherited_by_members attrs)
                                   (type_of_member env fld) }

  | MEMBEROFPTR(a1, fieldname) ->
      let b1 = elab a1 in
      let (fld, attrs) =
        match unroll env b1.etyp with
        | TPtr(t, _) | TArray(t,_,_) ->
            begin match unroll env t with
            | TStruct(id, attrs) ->
                (wrap Env.find_struct_member loc env (id, fieldname), attrs)
            | TUnion(id, attrs) ->
                (wrap Env.find_union_member loc env (id, fieldname), attrs)
            | _ ->
                error "left-hand side of '->' is not a pointer to a struct or union"
            end
        | _ ->
            error "left-hand side of '->' is not a pointer " in
      { edesc = EUnop(Oarrow fieldname, b1);
        etyp = add_attributes_type (List.filter attr_inherited_by_members attrs)
                                   (type_of_member env fld) }

(* Hack to treat vararg.h functions the GCC way.  Helps with testing.
    va_start(ap,n)
      (preprocessing) --> __builtin_va_start(ap, arg)
      (elaboration)   --> __builtin_va_start(ap)
    va_arg(ap, ty)
      (preprocessing) --> __builtin_va_arg(ap, ty)
      (elaboration)   --> __builtin_va_arg(ap, sizeof(ty))
*)
  | CALL((VARIABLE "__builtin_va_start" as a1), [a2; a3]) ->
      let b1 = elab a1 and b2 = elab a2 and _b3 = elab a3 in
      { edesc = ECall(b1, [b2]);
        etyp = TVoid [] }

  | BUILTIN_VA_ARG (a2, a3) ->
      let ident =
        match wrap Env.lookup_ident loc env "__builtin_va_arg" with
          | (id, II_ident(sto, ty)) -> { edesc = EVar id; etyp = ty }
          | _ -> assert false
      in
      let b2 = elab a2 and b3 = elab (TYPE_SIZEOF a3) in
      let ty = match b3.edesc with ESizeof ty -> ty | _ -> assert false in
      let ty' = default_argument_conversion env ty in
      if not (compatible_types env ty ty') then
        warning "'%a' is promoted to '%a' when passed through '...'.@ You should pass '%a', not '%a', to 'va_arg'"
                Cprint.typ ty Cprint.typ ty'
                Cprint.typ ty' Cprint.typ ty;
      { edesc = ECall(ident, [b2; b3]); etyp = ty }

  | CALL(a1, al) ->
      let b1 =
        (* Catch the old-style usage of calling a function without
           having declared it *)
        match a1 with
        | VARIABLE n when not (Env.ident_is_bound env n) ->
            warning "implicit declaration of function '%s'" n;
            let ty = TFun(TInt(IInt, []), None, false, []) in
            (* Emit an extern declaration for it *)
            let id = Env.fresh_ident n in
            emit_elab loc (Gdecl(Storage_extern, id, ty, None));
            { edesc = EVar id; etyp = ty }
        | _ -> elab a1 in
      let bl = List.map elab al in
      (* Extract type information *)
      let (res, args, vararg) =
        match unroll env b1.etyp with
        | TFun(res, args, vararg, a) -> (res, args, vararg)
        | TPtr(ty, a) ->
            begin match unroll env ty with
            | TFun(res, args, vararg, a) -> (res, args, vararg)
            | _ -> error "the function part of a call does not have a function type"
            end
        | _ -> error "the function part of a call does not have a function type"
      in
      (* Type-check the arguments against the prototype *)
      let bl' =
        match args with
        | None -> bl
        | Some proto -> elab_arguments 1 bl proto vararg in
      { edesc = ECall(b1, bl'); etyp = res }

  | UNARY(POSINCR, a1) ->
      elab_pre_post_incr_decr Opostincr "postfix '++'" a1
  | UNARY(POSDECR, a1) ->
      elab_pre_post_incr_decr Opostdecr "postfix '--'" a1

(* 6.5.4 Cast operators *)

  | CAST ((spec, dcl), SINGLE_INIT a1) ->
      let ty = elab_type loc env spec dcl in
      let b1 = elab a1 in
      if not (valid_cast env b1.etyp ty) then
        err "illegal cast from %a@ to %a" Cprint.typ b1.etyp Cprint.typ ty;
      { edesc = ECast(ty, b1); etyp = ty }

(* 6.5.2.5 Compound literals *)

  | CAST ((spec, dcl), ie) ->
      let ty = elab_type loc env spec dcl in
      begin match elab_initializer loc env "<compound literal>" ty ie with
      | (ty', Some i) -> { edesc = ECompound(ty', i); etyp = ty' }
      | (ty', None)   -> error "ill-formed compound literal"
      end

(* 6.5.3 Unary expressions *)

  | EXPR_SIZEOF a1 ->
      let b1 = elab a1 in
      if wrap incomplete_type loc env b1.etyp then
        err "incomplete type %a" Cprint.typ b1.etyp;
      let bdesc =
        (* Catch special cases sizeof("string literal") *)
        match b1.edesc with
        | EConst(CStr s) ->
            let sz = String.length s + 1 in
            EConst(CInt(Int64.of_int sz, size_t_ikind, ""))
        | EConst(CWStr s) ->
            let sz = (!config).sizeof_wchar * (List.length s + 1) in
            EConst(CInt(Int64.of_int sz, size_t_ikind, ""))
        | _ ->
            ESizeof b1.etyp in
      { edesc = bdesc; etyp = TInt(size_t_ikind, []) }

  | TYPE_SIZEOF (spec, dcl) ->
      let ty = elab_type loc env spec dcl in
      if wrap incomplete_type loc env ty then
        err "incomplete type %a" Cprint.typ ty;
      { edesc = ESizeof ty; etyp = TInt(size_t_ikind, []) }

  | EXPR_ALIGNOF a1 ->
      let b1 = elab a1 in
      if wrap incomplete_type loc env b1.etyp then
        err "incomplete type %a" Cprint.typ b1.etyp;
      { edesc = EAlignof b1.etyp; etyp =  TInt(size_t_ikind, []) }

  | TYPE_ALIGNOF (spec, dcl) ->
      let ty = elab_type loc env spec dcl in
      if wrap incomplete_type loc env ty then
        err "incomplete type %a" Cprint.typ ty;
      { edesc = EAlignof ty; etyp =  TInt(size_t_ikind, []) }

  | UNARY(PLUS, a1) ->
      let b1 = elab a1 in
      if not (is_arith_type env b1.etyp) then
        err "argument of unary '+' is not an arithmetic type";
      { edesc = EUnop(Oplus, b1); etyp = unary_conversion env b1.etyp }

  | UNARY(MINUS, a1) ->
      let b1 = elab a1 in
      if not (is_arith_type env b1.etyp) then
        err "argument of unary '-' is not an arithmetic type";
      { edesc = EUnop(Ominus, b1); etyp = unary_conversion env b1.etyp }

  | UNARY(BNOT, a1) ->
      let b1 = elab a1 in
      if not (is_integer_type env b1.etyp) then
        err "argument of '~' is not an integer type";
      { edesc = EUnop(Onot, b1); etyp = unary_conversion env b1.etyp }

  | UNARY(NOT, a1) ->
      let b1 = elab a1 in
      if not (is_scalar_type env b1.etyp) then
        err "argument of '!' is not a scalar type";
      { edesc = EUnop(Olognot, b1); etyp = TInt(IInt, []) }

  | UNARY(ADDROF, a1) ->
      let b1 = elab a1 in
      if not (is_lvalue b1 || is_function_type env b1.etyp) then
        err "argument of '&' is not an l-value";
      { edesc = EUnop(Oaddrof, b1); etyp = TPtr(b1.etyp, []) }

  | UNARY(MEMOF, a1) ->
      let b1 = elab a1 in
      begin match unroll env b1.etyp with
      (* '*' applied to a function type has no effect *)
      | TFun _ -> b1
      | TPtr(ty, _) | TArray(ty, _, _) ->
          { edesc = EUnop(Oderef, b1); etyp = ty }
      | _ ->
          error "argument of unary '*' is not a pointer"
      end

  | UNARY(PREINCR, a1) ->
      elab_pre_post_incr_decr Opreincr "prefix '++'" a1
  | UNARY(PREDECR, a1) ->
      elab_pre_post_incr_decr Opredecr "prefix '--'" a1

(* 6.5.5 to 6.5.12  Binary operator expressions *)

  | BINARY(MUL, a1, a2) ->
      elab_binary_arithmetic "*" Omul a1 a2

  | BINARY(DIV, a1, a2) ->
      elab_binary_arithmetic "/" Odiv a1 a2

  | BINARY(MOD, a1, a2) ->
      elab_binary_integer "/" Omod a1 a2

  | BINARY(ADD, a1, a2) ->
      let b1 = elab a1 in
      let b2 = elab a2 in
      let tyres =
        if is_arith_type env b1.etyp && is_arith_type env b2.etyp then
          binary_conversion env b1.etyp b2.etyp
        else begin
          let ty =
            match unroll env b1.etyp, unroll env b2.etyp with
            | (TPtr(ty, a) | TArray(ty, _, a)), (TInt _ | TEnum _) -> ty
            | (TInt _ | TEnum _), (TPtr(ty, a) | TArray(ty, _, a)) -> ty
            | _, _ -> error "type error in binary '+'" in
          if not (pointer_arithmetic_ok env ty) then
            err "illegal pointer arithmetic in binary '+'";
          TPtr(ty, [])
        end in
      { edesc = EBinop(Oadd, b1, b2, tyres); etyp = tyres }

  | BINARY(SUB, a1, a2) ->
      let b1 = elab a1 in
      let b2 = elab a2 in
      let (tyop, tyres) =
        if is_arith_type env b1.etyp && is_arith_type env b2.etyp then begin
          let tyres = binary_conversion env b1.etyp b2.etyp in
          (tyres, tyres)
        end else begin
          match unroll env b1.etyp, unroll env b2.etyp with
          | (TPtr(ty, a) | TArray(ty, _, a)), (TInt _ | TEnum _) ->
              if not (pointer_arithmetic_ok env ty) then
                err "illegal pointer arithmetic in binary '-'";
              (TPtr(ty, []), TPtr(ty, []))
          | (TInt _ | TEnum _), (TPtr(ty, a) | TArray(ty, _, a)) ->
              if not (pointer_arithmetic_ok env ty) then
                err "illegal pointer arithmetic in binary '-'";
              (TPtr(ty, []), TPtr(ty, []))
          | (TPtr(ty1, a1) | TArray(ty1, _, a1)),
            (TPtr(ty2, a2) | TArray(ty2, _, a2)) ->
              if not (compatible_types ~noattrs:true env ty1 ty2) then
                err "mismatch between pointer types in binary '-'";
              if not (pointer_arithmetic_ok env ty1) then
                err "illegal pointer arithmetic in binary '-'";
              if wrap sizeof loc env ty1 = Some 0 then
                err "subtraction between two pointers to zero-sized objects";
              (TPtr(ty1, []), TInt(ptrdiff_t_ikind, []))
          | _, _ -> error "type error in binary '-'"
        end in
      { edesc = EBinop(Osub, b1, b2, tyop); etyp = tyres }

  | BINARY(SHL, a1, a2) ->
      elab_shift "<<" Oshl a1 a2

  | BINARY(SHR, a1, a2) ->
      elab_shift ">>" Oshr a1 a2

  | BINARY(EQ, a1, a2) ->
      elab_comparison Oeq a1 a2
  | BINARY(NE, a1, a2) ->
      elab_comparison One a1 a2
  | BINARY(LT, a1, a2) ->
      elab_comparison Olt a1 a2
  | BINARY(GT, a1, a2) ->
      elab_comparison Ogt a1 a2
  | BINARY(LE, a1, a2) ->
      elab_comparison Ole a1 a2
  | BINARY(GE, a1, a2) ->
      elab_comparison Oge a1 a2

  | BINARY(BAND, a1, a2) ->
      elab_binary_integer "&" Oand a1 a2
  | BINARY(BOR, a1, a2) ->
      elab_binary_integer "|" Oor a1 a2
  | BINARY(XOR, a1, a2) ->
      elab_binary_integer "^" Oxor a1 a2

(* 6.5.13 and 6.5.14 Logical operator expressions *)

  | BINARY(AND, a1, a2) ->
      elab_logical_operator "&&" Ologand a1 a2
  | BINARY(OR, a1, a2) ->
      elab_logical_operator "||" Ologor a1 a2

(* 6.5.15 Conditional expressions *)
  | QUESTION(a1, a2, a3) ->
      let b1 = elab a1 in
      let b2 = elab a2 in
      let b3 = elab a3 in
      if not (is_scalar_type env b1.etyp) then
        err ("the first argument of '? :' is not a scalar type");
      begin match pointer_decay env b2.etyp, pointer_decay env b3.etyp with
      | (TInt _ | TFloat _ | TEnum _), (TInt _ | TFloat _ | TEnum _) ->
          { edesc = EConditional(b1, b2, b3);
            etyp = binary_conversion env b2.etyp b3.etyp }
      | TPtr(ty1, a1), TPtr(ty2, a2) ->
          let tyres =
            if is_void_type env ty1 || is_void_type env ty2 then
              TPtr(TVoid (add_attributes a1 a2), [])
            else
              match combine_types ~noattrs:true env
                                  (TPtr(ty1, a1)) (TPtr(ty2, a2)) with
              | None ->
                  error "the second and third arguments of '? :' \
                         have incompatible pointer types"
              | Some ty -> ty
            in
          { edesc = EConditional(b1, b2, b3); etyp = tyres }
      | TPtr(ty1, a1), TInt _ when is_literal_0 b3 ->
          { edesc = EConditional(b1, b2, nullconst); etyp = TPtr(ty1, []) }
      | TInt _, TPtr(ty2, a2) when is_literal_0 b2 ->
          { edesc = EConditional(b1, nullconst, b3); etyp = TPtr(ty2, []) }
      | ty1, ty2 ->
          match combine_types ~noattrs:true env ty1 ty2 with
          | None ->
              error ("the second and third arguments of '? :' have incompatible types")
          | Some tyres ->
              { edesc = EConditional(b1, b2, b3); etyp = tyres }
      end

(* 6.5.16 Assignment expressions *)

  | BINARY(ASSIGN, a1, a2) ->
      let b1 = elab a1 in
      let b2 = elab a2 in
      if List.mem AConst (attributes_of_type env b1.etyp) then
        err "left-hand side of assignment has 'const' type";
      if not (is_modifiable_lvalue env b1) then
        err "left-hand side of assignment is not a modifiable l-value";
      if not (valid_assignment env b2 b1.etyp) then begin
        if valid_cast env b2.etyp b1.etyp then
          warning "assigning a value of type@ %a@ to a lvalue of type@ %a"
                  Cprint.typ b2.etyp Cprint.typ b1.etyp
        else
          err "assigning a value of type@ %a@ to a lvalue of type@ %a"
                  Cprint.typ b2.etyp Cprint.typ b1.etyp;
      end;
      { edesc = EBinop(Oassign, b1, b2, b1.etyp); etyp = b1.etyp }

  | BINARY((ADD_ASSIGN | SUB_ASSIGN | MUL_ASSIGN | DIV_ASSIGN | MOD_ASSIGN
            | BAND_ASSIGN | BOR_ASSIGN | XOR_ASSIGN | SHL_ASSIGN | SHR_ASSIGN
            as op), a1, a2) ->
      let (sop, top) =
        match op with
        | ADD_ASSIGN -> (ADD, Oadd_assign)
        | SUB_ASSIGN -> (SUB, Osub_assign)
        | MUL_ASSIGN -> (MUL, Omul_assign)
        | DIV_ASSIGN -> (DIV, Odiv_assign)
        | MOD_ASSIGN -> (MOD, Omod_assign)
        | BAND_ASSIGN -> (BAND, Oand_assign)
        | BOR_ASSIGN -> (BOR, Oor_assign)
        | XOR_ASSIGN -> (XOR, Oxor_assign)
        | SHL_ASSIGN -> (SHL, Oshl_assign)
        | SHR_ASSIGN -> (SHR, Oshr_assign)
        | _ -> assert false in
      begin match elab (BINARY(sop, a1, a2)) with
      | { edesc = EBinop(_, b1, b2, _); etyp = ty } as b ->
          if List.mem AConst (attributes_of_type env b1.etyp) then
            err "left-hand side of assignment has 'const' type";
          if not (is_modifiable_lvalue env b1) then
            err ("left-hand side of assignment is not a modifiable l-value");
          if not (valid_assignment env b b1.etyp) then begin
            if valid_cast env ty b1.etyp then
              warning "assigning a value of type@ %a@ to a lvalue of type@ %a"
                      Cprint.typ ty Cprint.typ b1.etyp
            else
              err "assigning a value of type@ %a@ to a lvalue of type@ %a"
                      Cprint.typ ty Cprint.typ b1.etyp;
          end;
          { edesc = EBinop(top, b1, b2, ty); etyp = b1.etyp }
      | _ -> assert false
      end

(* 6.5.17 Sequential expressions *)

  | BINARY(COMMA, a1, a2) ->
      let b1 = elab a1 in
      let b2 = elab a2 in
      { edesc = EBinop (Ocomma, b1, b2, b2.etyp); etyp = b2.etyp }

(* Elaboration of pre- or post- increment/decrement *)
  and elab_pre_post_incr_decr op msg a1 =
      let b1 = elab a1 in
      if not (is_modifiable_lvalue env b1) then
        err "the argument of %s is not a modifiable l-value" msg;
      if not (is_scalar_type env b1.etyp) then
        err "the argument of %s must be an arithmetic or pointer type" msg;
      { edesc = EUnop(op, b1); etyp = b1.etyp }

(* Elaboration of binary operators over integers *)
  and elab_binary_integer msg op a1 a2 =
      let b1 = elab a1 in
      if not (is_integer_type env b1.etyp) then
        error "the first argument of '%s' is not an integer type" msg;
      let b2 = elab a2 in
      if not (is_integer_type env b2.etyp) then
        error "the second argument of '%s' is not an integer type" msg;
      let tyres = binary_conversion env b1.etyp b2.etyp in
      { edesc = EBinop(op, b1, b2, tyres); etyp = tyres }

(* Elaboration of binary operators over arithmetic types *)
  and elab_binary_arithmetic msg op a1 a2 =
      let b1 = elab a1 in
      if not (is_arith_type env b1.etyp) then
        error "the first argument of '%s' is not an arithmetic type" msg;
      let b2 = elab a2 in
      if not (is_arith_type env b2.etyp) then
        error "the second argument of '%s' is not an arithmetic type" msg;
      let tyres = binary_conversion env b1.etyp b2.etyp in
      { edesc = EBinop(op, b1, b2, tyres); etyp = tyres }

(* Elaboration of shift operators *)
  and elab_shift msg op a1 a2 =
      let b1 = elab a1 in
      if not (is_integer_type env b1.etyp) then
        error "the first argument of '%s' is not an integer type" msg;
      let b2 = elab a2 in
      if not (is_integer_type env b2.etyp) then
        error "the second argument of '%s' is not an integer type" msg;
      let tyres = unary_conversion env b1.etyp in
      { edesc = EBinop(op, b1, b2, tyres); etyp = tyres }

(* Elaboration of comparisons *)
  and elab_comparison op a1 a2 =
      let b1 = elab a1 in
      let b2 = elab a2 in
      let resdesc =
        match pointer_decay env b1.etyp, pointer_decay env b2.etyp with
        | (TInt _ | TFloat _ | TEnum _), (TInt _ | TFloat _ | TEnum _) ->
            EBinop(op, b1, b2, binary_conversion env b1.etyp b2.etyp)
        | TInt _, TPtr(ty, _) when is_literal_0 b1 ->
            EBinop(op, nullconst, b2, TPtr(ty, []))
        | TPtr(ty, _), TInt _ when is_literal_0 b2 ->
            EBinop(op, b1, nullconst, TPtr(ty, []))
        | TPtr(ty1, _), TPtr(ty2, _)
          when is_void_type env ty1 ->
            EBinop(op, b1, b2, TPtr(ty2, []))
        | TPtr(ty1, _), TPtr(ty2, _)
          when is_void_type env ty2 ->
            EBinop(op, b1, b2, TPtr(ty1, []))
        | TPtr(ty1, _), TPtr(ty2, _) ->
            if not (compatible_types ~noattrs:true env ty1 ty2) then
              warning "comparison between incompatible pointer types";
            EBinop(op, b1, b2, TPtr(ty1, []))
        | TPtr _, (TInt _ | TEnum _)
        | (TInt _ | TEnum _), TPtr _ ->
            warning "comparison between integer and pointer";
            EBinop(op, b1, b2, TPtr(TVoid [], []))
        | ty1, ty2 ->
            error "illegal comparison between types@ %a@ and %a"
                  Cprint.typ b1.etyp Cprint.typ b2.etyp in
      { edesc = resdesc; etyp = TInt(IInt, []) }

(* Elaboration of && and || *)
  and elab_logical_operator msg op a1 a2 =
      let b1 = elab a1 in
      if not (is_scalar_type env b1.etyp) then
        err "the first argument of '%s' is not a scalar type" msg;
      let b2 = elab a2 in
      if not (is_scalar_type env b2.etyp) then
        err "the second argument of '%s' is not a scalar type" msg;
      { edesc = EBinop(op, b1, b2, TInt(IInt, [])); etyp = TInt(IInt, []) }

(* Type-checking of function arguments *)
  and elab_arguments argno args params vararg =
    match args, params with
    | [], [] -> []
    | [], _::_ -> err "not enough arguments in function call"; []
    | _::_, [] -> 
        if vararg 
        then args
        else (err "too many arguments in function call"; args)
    | arg1 :: argl, (_, ty_p) :: paraml ->
        let ty_a = argument_conversion env arg1.etyp in
        if not (valid_assignment env {arg1 with etyp = ty_a} ty_p) then begin
          if valid_cast env ty_a ty_p then
            warning
              "argument #%d of function call has type@ %a@ \
               instead of the expected type@ %a"
              argno Cprint.typ ty_a Cprint.typ ty_p
          else
            err
              "argument #%d of function call has type@ %a@ \
               instead of the expected type@ %a"
              argno Cprint.typ ty_a Cprint.typ ty_p
        end;
        arg1 :: elab_arguments (argno + 1) argl paraml vararg

  in elab a

(* Filling in forward declaration *)
let _ = elab_expr_f := elab_expr

let elab_opt_expr loc env = function
  | None -> None
  | Some a -> Some (elab_expr loc env a)

let elab_for_expr loc env = function
  | None -> { sdesc = Sskip; sloc = elab_loc loc }
  | Some a -> { sdesc = Sdo (elab_expr loc env a); sloc = elab_loc loc }

(* Handling of __func__ (section 6.4.2.2) *)

let __func__type_and_init s = 
  (TArray(TInt(IChar, [AConst]), Some(Int64.of_int (String.length s + 1)), []),
   init_char_array_string None s)


(* Elaboration of top-level and local definitions *)

let enter_typedefs loc env sto dl =
  if sto <> Storage_default then
    error loc "Non-default storage on 'typedef' definition";
  List.fold_left (fun env (s, ty, init) ->
    if init <> NO_INIT then
      error loc "initializer in typedef";
    if redef Env.lookup_typedef env s then
      error loc "redefinition of typedef '%s'" s;
    let (id, env') = Env.enter_typedef env s ty in
    emit_elab loc (Gtypedef(id, ty));
    env') env dl

let enter_or_refine_ident local loc env s sto ty =
  match previous_def Env.lookup_ident env s with
  | Some(id, II_ident(old_sto, old_ty))
    when sto = Storage_extern || Env.in_current_scope env id ->
      if local && Env.in_current_scope env id then
        error loc "redefinition of local variable '%s'" s;
      let new_ty =
        match combine_types env old_ty ty with
        | Some new_ty ->
            new_ty
        | None ->
            warning loc "redefinition of '%s' with incompatible type" s; ty in
      let new_sto =
        if old_sto = Storage_extern then sto else
        if sto = Storage_extern then old_sto else
        if old_sto = sto then sto else begin
          warning loc "redefinition of '%s' with incompatible storage class" s;
          sto
        end in
      (id, new_sto, Env.add_ident env id new_sto new_ty)
  | Some(id, II_enum v) when Env.in_current_scope env id ->
      error loc "illegal redefinition of enumerator '%s'" s;
      (id, sto, Env.add_ident env id sto ty)
  | _ ->
      let (id, env') = Env.enter_ident env s sto ty in (id, sto, env')

let enter_decdefs local loc env sto dl =
  (* Sanity checks on storage class *)
  if sto = Storage_register && not local then
    error loc "'register' on global declaration";
  if sto <> Storage_default && dl = [] then
    warning loc "Storage class specifier on empty declaration";
  let rec enter_decdef (decls, env) (s, ty, init) =
    let isfun = is_function_type env ty in
    if sto = Storage_extern && init <> NO_INIT then
      error loc "'extern' declaration cannot have an initializer";
    if local && isfun && (sto = Storage_static || sto = Storage_register) then
      error loc "invalid storage class for '%s'" s;
    (* Local function declarations are always treated as extern *)
    let sto1 = if local && isfun then Storage_extern else sto in
    (* enter ident in environment with declared type, because
       initializer can refer to the ident *)
    let (id, sto', env1) = enter_or_refine_ident local loc env s sto1 ty in
    (* process the initializer *)
    let (ty', init') = elab_initializer loc env1 s ty init in
    (* update environment with refined type *)
    let env2 = Env.add_ident env1 id sto' ty' in
    (* check for incomplete type *)
    if local && sto' <> Storage_extern
             && not isfun
             && wrap incomplete_type loc env ty' then
      error loc "'%s' has incomplete type" s;
    if local && not isfun && sto' <> Storage_extern && sto' <> Storage_static then
      (* Local definition *)
      ((sto', id, ty', init') :: decls, env2)
    else begin
      (* Global definition *)
      emit_elab loc (Gdecl(sto', id, ty', init'));
      (decls, env2)
    end in
  let (decls, env') = List.fold_left enter_decdef ([], env) dl in
  (List.rev decls, env')

let elab_fundef env spec name body loc =
  let (s, sto, inline, ty, env1) = elab_name env spec name in
  if sto = Storage_register then
    error loc "a function definition cannot have 'register' storage class";
  (* Fix up the type.  We can have params = None but only for an
     old-style parameterless function "int f() {...}" *)
  let ty =
    match ty with
    | TFun(ty_ret, None, vararg, attr) -> TFun(ty_ret, Some [], vararg, attr)
    | _ -> ty in
  (* Extract info from type *)
  let (ty_ret, params, vararg, attr) =
    match ty with
    | TFun(ty_ret, Some params, vararg, attr) -> (ty_ret, params, vararg, attr)
    | _ -> fatal_error loc "wrong type for function definition" in
  (* Enter function in the environment, for recursive references *)
  let (fun_id, sto1, env1) = enter_or_refine_ident false loc env s sto ty in
  (* Enter parameters in the environment *)
  let env2 =
    List.fold_left (fun e (id, ty) -> Env.add_ident e id Storage_default ty)
                   (Env.new_scope env1) params in
  (* Define "__func__" and enter it in the environment *)
  let (func_ty, func_init) = __func__type_and_init s in
  let (func_id, _, env3) =
    enter_or_refine_ident true loc env2 "__func__" Storage_static func_ty in
  emit_elab loc (Gdecl(Storage_static, func_id, func_ty, Some func_init));
  (* Elaborate function body *)
  let body' = !elab_funbody_f ty_ret env3 body in
  (* Build and emit function definition *)
  let fn =
    { fd_storage = sto1;
      fd_inline = inline;
      fd_name = fun_id;
      fd_attrib = attr;
      fd_ret = ty_ret;
      fd_params = params;
      fd_vararg = vararg;
      fd_locals = [];
      fd_body = body' } in
  emit_elab loc (Gfundef fn);
  env1

let elab_kr_fundef env spec name params defs body loc =
  warning loc "Non-prototype, pre-standard function definition.@  Converting to prototype form";
  (* Check that the declarations only declare parameters *)
  let check_one_decl (Init_name(Name(s, dty, attrs, loc'), ie)) =
    if not (List.mem s params) then
      error loc' "Declaration of '%s' which is not a function parameter" s;
    if ie <> NO_INIT then
      error loc' "Illegal initialization of function parameter '%s'" s in
  let check_decl = function
  | DECDEF((spec', name_init_list), loc') ->
      List.iter check_one_decl name_init_list
  | d ->
      (* Should never be produced by the parser *)
      fatal_error (get_definitionloc d)
                  "Illegal declaration of function parameter" in
  List.iter check_decl defs;
  (* Convert old-style K&R function definition to modern prototyped form *)
  let rec convert_param param = function
  | [] ->
      (* Parameter is not declared, defaults to "int" in ISO C90,
         is an error in ISO C99.  Just emit a warning. *)
      warning loc "Type of '%s' defaults to 'int'" param;
      PARAM([SpecType Tint], Some param, JUSTBASE, [], loc)
  | DECDEF((spec', name_init_list), loc') :: defs ->
      let rec convert = function
        | [] -> convert_param param defs
        | Init_name(Name(s, dty, attrs, loc''), ie) :: l ->
            if s = param
            then PARAM(spec', Some param, dty, attrs, loc'')
            else convert l
      in convert name_init_list
  | _ ->
      assert false (* checked earlier *) in
  let params' =
    List.map (fun p -> convert_param p defs) params in
  let name' =
    let (Name(s, dty, attr, loc')) = name in
    Name(s, append_decltype dty (PROTO(JUSTBASE, (params', false))),
         attr, loc') in
  (* Elaborate the prototyped form *)
  elab_fundef env spec name' body loc

let rec elab_definition (local: bool) (env: Env.t) (def: Cabs.definition)
                    : decl list * Env.t =
  match def with
  (* "int f(int x) { ... }" *)
  | FUNDEF(spec, name, body, loc) ->
      if local then error loc "local definition of a function";
      let env1 = elab_fundef env spec name body loc in
      ([], env1)

  (* "int f(x, y) double y; { ... }" *)
  | KRFUNDEF(spec, name, params, defs, body, loc) ->
      if local then error loc "local definition of a function";
      let env1 = elab_kr_fundef env spec name params defs body loc in
      ([], env1)

  (* "int x = 12, y[10], *z" *)
  | DECDEF(init_name_group, loc) ->
      let ((dl, env1), sto, tydef) = 
        elab_init_name_group loc env init_name_group in
      if tydef then
        let env2 = enter_typedefs loc env1 sto dl
        in ([], env2)
      else
        enter_decdefs local loc env1 sto dl

  (* pragma *)
  | PRAGMA(s, loc) ->
      emit_elab loc (Gpragma s);
      ([], env)

and elab_definitions local env = function
  | [] -> ([], env)
  | d1 :: dl ->
      let (decl1, env1) = elab_definition local env d1 in
      let (decl2, env2) = elab_definitions local env1 dl in
      (decl1 @ decl2, env2)


(* Contexts for elaborating statements *)

module StringSet = Set.Make(String)

type stmt_context = {
  ctx_return_typ: typ;          (**r return type for the function *)
  ctx_labels: StringSet.t;      (**r all labels defined in the function *)
  ctx_break: bool;              (**r is 'break' allowed? *)
  ctx_continue: bool            (**r is 'continue' allowed? *)
}

let stmt_labels stmt =
  let lbls = ref StringSet.empty in
  let rec do_stmt = function
  | BLOCK(b, _) -> do_block b
  | If(_, s1, Some s2, _) -> do_stmt s1; do_stmt s2
  | If(_, s1, None, _) -> do_stmt s1
  | WHILE(_, s1, _) -> do_stmt s1
  | DOWHILE(_, s1, _) -> do_stmt s1
  | FOR(_, _, _, s1, _) -> do_stmt s1
  | SWITCH(_, s1, _) -> do_stmt s1
  | CASE(_, s1, _) -> do_stmt s1
  | DEFAULT(s1, _) -> do_stmt s1
  | LABEL(lbl, s1, loc) ->
      if StringSet.mem lbl !lbls then
        error loc "multiply-defined label '%s'\n" lbl;
      lbls := StringSet.add lbl !lbls;
      do_stmt s1
  | _ -> ()
  and do_block b = List.iter do_stmt b
  in do_stmt stmt; !lbls

let ctx_loop ctx = { ctx with ctx_break = true; ctx_continue = true }

let ctx_switch ctx = { ctx with ctx_break = true }

(* Elaboration of statements *)

let rec elab_stmt env ctx s =

  match s with

(* 6.8.3 Expression statements *)

  | COMPUTATION(a, loc) ->
      { sdesc = Sdo (elab_expr loc env a); sloc = elab_loc loc }

(* 6.8.1 Labeled statements *)

  | LABEL(lbl, s1, loc) ->
      { sdesc = Slabeled(Slabel lbl, elab_stmt env ctx s1); sloc = elab_loc loc }

  | CASE(a, s1, loc) ->
      let a' = elab_expr loc env a in
      begin match Ceval.integer_expr env a' with
        | None ->
            error loc "argument of 'case' must be an integer compile-time constant"
        | Some n -> ()
      end;
      { sdesc = Slabeled(Scase a', elab_stmt env ctx s1); sloc = elab_loc loc }

  | DEFAULT(s1, loc) ->
      { sdesc = Slabeled(Sdefault, elab_stmt env ctx s1); sloc = elab_loc loc }

(* 6.8.2 Compound statements *)

  | BLOCK(b, loc) ->
      elab_block loc env ctx b

(* 6.8.4 Conditional statements *)

  | If(a, s1, s2, loc) ->
      let a' = elab_expr loc env a in
      if not (is_scalar_type env a'.etyp) then
        error loc "the condition of 'if' does not have scalar type";
      let s1' = elab_stmt env ctx s1 in
      let s2' = 
        match s2 with
          | None -> sskip
          | Some s2 -> elab_stmt env ctx s2
      in
      { sdesc = Sif(a', s1', s2'); sloc = elab_loc loc }

(* 6.8.5 Iterative statements *)

  | WHILE(a, s1, loc) ->
      let a' = elab_expr loc env a in
      if not (is_scalar_type env a'.etyp) then
        error loc "the condition of 'while' does not have scalar type";
      let s1' = elab_stmt env (ctx_loop ctx) s1 in
      { sdesc = Swhile(a', s1'); sloc = elab_loc loc }

  | DOWHILE(a, s1, loc) ->
      let s1' = elab_stmt env (ctx_loop ctx) s1 in
      let a' = elab_expr loc env a in
      if not (is_scalar_type env a'.etyp) then
        error loc "the condition of 'while' does not have scalar type";
      { sdesc = Sdowhile(s1', a'); sloc = elab_loc loc }

  | FOR(fc, a2, a3, s1, loc) ->
      let (a1', env', decls') =
        match fc with
        | Some (FC_EXP a1) ->
            (elab_for_expr loc env (Some a1), env, None)
        | None ->
            (elab_for_expr loc env None, env, None)
        | Some (FC_DECL def) ->
            let (dcl, env') = elab_definition true (Env.new_scope env) def in
            let loc = elab_loc (get_definitionloc def) in
            (sskip, env', 
             Some(List.map (fun d -> {sdesc = Sdecl d; sloc = loc}) dcl)) in
      let a2' =
        match a2 with
          | None -> intconst 1L IInt
          | Some a2 -> elab_expr loc env' a2 
      in
      if not (is_scalar_type env' a2'.etyp) then
        error loc "the condition of 'for' does not have scalar type";
      let a3' = elab_for_expr loc env' a3 in
      let s1' = elab_stmt env' (ctx_loop ctx) s1 in
      let sfor = { sdesc = Sfor(a1', a2', a3', s1'); sloc = elab_loc loc } in
      begin match decls' with
      | None -> sfor
      | Some sl -> { sdesc = Sblock (sl @ [sfor]); sloc = elab_loc loc }
      end

(* 6.8.4 Switch statement *)
  | SWITCH(a, s1, loc) ->
      let a' = elab_expr loc env a in
      if not (is_integer_type env a'.etyp) then
        error loc "the argument of 'switch' is not an integer";
      let s1' = elab_stmt env (ctx_switch ctx) s1 in
      { sdesc = Sswitch(a', s1'); sloc = elab_loc loc }

(* 6.8.6 Break and continue statements *)
  | BREAK loc ->
      if not ctx.ctx_break then
        error loc "'break' outside of a loop or a 'switch'";
      { sdesc = Sbreak; sloc = elab_loc loc }
  | CONTINUE loc ->
      if not ctx.ctx_continue then
        error loc "'continue' outside of a loop";
      { sdesc = Scontinue; sloc = elab_loc loc }

(* 6.8.6 Return statements *)
  | RETURN(a, loc) ->
      let a' = elab_opt_expr loc env a in
      begin match (unroll env ctx.ctx_return_typ, a') with
      | TVoid _, None -> ()
      | TVoid _, Some _ ->
          error loc
            "'return' with a value in a function of return type 'void'"
      | _, None ->
          warning loc
            "'return' without a value in a function of return type@ %a"
            Cprint.typ ctx.ctx_return_typ
      | _, Some b ->
          if not (valid_assignment env b ctx.ctx_return_typ) then begin
            if valid_cast env b.etyp ctx.ctx_return_typ then
              warning loc
                "return value has type@ %a@ \
                 instead of the expected type@ %a"
                Cprint.typ b.etyp Cprint.typ ctx.ctx_return_typ
            else
              error loc
                "return value has type@ %a@ \
                 instead of the expected type@ %a"
                Cprint.typ b.etyp Cprint.typ ctx.ctx_return_typ
          end
      end;
      { sdesc = Sreturn a'; sloc = elab_loc loc }

(* 6.8.6 Goto statements *)
  | GOTO(lbl, loc) ->
      if not (StringSet.mem lbl ctx.ctx_labels) then
        error loc "unknown 'goto' label %s" lbl;
      { sdesc = Sgoto lbl; sloc = elab_loc loc }

(* 6.8.3 Null statements *)
  | NOP loc ->
      { sdesc = Sskip; sloc = elab_loc loc }

(* Traditional extensions *)
  | ASM(wide, chars, loc) ->
      begin match elab_string_literal loc wide chars with
      | CStr s ->
          { sdesc = Sasm s; sloc = elab_loc loc }
      | _ ->
          error loc "wide strings not supported in asm statement";
          sskip
      end

(* Unsupported *)
  | DEFINITION def ->
      error (get_definitionloc def) "ill-placed definition";
      sskip

and elab_block loc env ctx b =
  let b' = elab_block_body (Env.new_scope env) ctx b in
  { sdesc = Sblock b'; sloc = elab_loc loc }

and elab_block_body env ctx sl =
  match sl with
  | [] ->
      []
  | DEFINITION def :: sl1 ->
      let (dcl, env') = elab_definition true env def in
      let loc = elab_loc (get_definitionloc def) in
      List.map (fun d -> {sdesc = Sdecl d; sloc = loc}) dcl
      @ elab_block_body env' ctx sl1
  | s :: sl1 ->
      let s' = elab_stmt env ctx s in
      s' :: elab_block_body env ctx sl1

(* Elaboration of a function body.  Return the corresponding C statement. *)

let elab_funbody return_typ env b =
  let ctx =
    { ctx_return_typ = return_typ;
      ctx_labels = stmt_labels b;
      ctx_break = false;
      ctx_continue = false } in
  elab_stmt env ctx b

(* Filling in forward declaration *)
let _ = elab_funbody_f := elab_funbody


(** * Entry point *)

let elab_file prog =
  reset();
  ignore (elab_definitions false (Builtins.environment()) prog);
  elaborated_program()
(*
  let rec inf = Datatypes.S inf in
  let ast:Cabs.definition list =
    Obj.magic
      (match Parser.translation_unit_file inf (Lexer.tokens_stream lb) with
         | Parser.Parser.Inter.Fail_pr ->
             (* Theoretically impossible : implies inconsistencies
                between grammars. *)
             Cerrors.fatal_error "Internal error while parsing"
         | Parser.Parser.Inter.Timeout_pr -> assert false
         | Parser.Parser.Inter.Parsed_pr (ast, _ ) -> ast)
  in
  reset();
  ignore (elab_definitions false (Builtins.environment()) ast);
  elaborated_program()
*)

