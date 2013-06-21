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

open Format
open Cerrors
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
  top_declarations := { gdesc = td; gloc = loc } :: !top_declarations

let reset() = top_declarations := []

let elaborated_program () =
  let p = !top_declarations in
  top_declarations := [];
  (* Reverse it and eliminate unreferenced declarations *)
  Cleanup.program p

(* Location stuff *)

let loc_of_name (_, _, _, loc) = loc

(* Monadic map for functions env -> 'a -> 'b * env *)

let rec mmap f env = function
  | [] -> ([], env)
  | hd :: tl ->
      let (hd', env1) = f env hd in
      let (tl', env2) = mmap f env1 tl in
      (hd' :: tl', env2)

(* To detect redefinitions within the same scope *)

let redef fn env arg =
  try
    let (id, info) = fn env arg in
    if Env.in_current_scope env id then Some(id, info) else None
  with Env.Error _ ->
    None

(* Forward declarations *)

let elab_expr_f : (cabsloc -> Env.t -> Cabs.expression -> C.exp) ref
  = ref (fun _ _ _ -> assert false)

let elab_funbody_f : (cabsloc -> C.typ -> Env.t -> Cabs.block -> C.stmt) ref
  = ref (fun _ _ _ _ -> assert false)


(** * Elaboration of constants *)

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
      (s, [IInt; ILong; IULong; ILongLong],
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
    | Some 'l' | Some 'L' -> FLongDouble
    | Some 'f' | Some 'F' -> FFloat
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

let elab_char_constant loc sz cl =
  let nbits = 8 * sz in
  (* Treat multi-char constants as a number in base 2^nbits *)
  let max_val = Int64.shift_left 1L (64 - nbits) in
  let v =
    List.fold_left 
      (fun acc d ->
        if acc >= max_val then begin
          error loc "character literal overflows";
        end;
        Int64.add (Int64.shift_left acc nbits) d)
      0L cl in
  let ty =
    if v < 256L then IInt
    else if v < Int64.shift_left 1L (8 * sizeof_ikind IULong) then IULong
    else IULongLong in
  (v, ty)

let elab_constant loc = function
  | CONST_INT s ->
      let (v, ik) = elab_int_constant loc s in
      CInt(v, ik, s)
  | CONST_FLOAT f ->
      let (v, fk) = elab_float_constant loc f in
      CFloat(v, fk)
  | CONST_CHAR cl ->
      let (v, ik) = elab_char_constant loc 1 cl in
      CInt(v, ik, "")
  | CONST_WCHAR cl -> 
      let (v, ik) = elab_char_constant loc !config.sizeof_wchar cl in
      CInt(v, ik, "")
  | CONST_STRING s -> CStr s
  | CONST_WSTRING s -> CWStr s


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

let elab_gcc_attr loc env = function
  | VARIABLE v ->
      [Attr(v, [])]
  | CALL(VARIABLE v, args) ->
      begin try
        [Attr(v, List.map (elab_attr_arg loc env) args)]
      with Wrong_attr_arg ->
        warning loc "cannot parse '%s' attribute, ignored" v; []
      end
  | _ ->
      warning loc "ill-formed attribute, ignored"; []

let elab_attribute loc env = function
  | ("const", []) -> [AConst]
  | ("restrict", []) -> [ARestrict]
  | ("volatile", []) -> [AVolatile]
  | (("__attribute" | "__attribute__"), l) ->
        List.flatten (List.map (elab_gcc_attr loc env) l)
  | ("__asm__", _) -> []    (* MacOS X noise *)
  | (name, _) -> warning loc "`%s' annotation ignored" name; []

let elab_attributes loc env al =
  List.fold_left add_attributes [] (List.map (elab_attribute loc env) al)

(* Auxiliary for typespec elaboration *)

let typespec_rank = function (* Don't change this *)
  | Cabs.Tvoid -> 0
  | Cabs.Tsigned -> 1
  | Cabs.Tunsigned -> 2
  | Cabs.Tchar -> 3
  | Cabs.Tshort -> 4
  | Cabs.Tlong -> 5
  | Cabs.Tint -> 6
  | Cabs.Tint64 -> 7
  | Cabs.Tfloat -> 8
  | Cabs.Tdouble -> 9
  | Cabs.T_Bool -> 10
  | _ -> 11 (* There should be at most one of the others *)

let typespec_order t1 t2 = compare (typespec_rank t1) (typespec_rank t2)

(* Elaboration of a type specifier.  Returns 4-tuple:
     (storage class, "inline" flag, elaborated type, new env)
   Optional argument "only" is true if this is a standalone
   struct or union declaration, without variable names.
*)

let rec elab_specifier ?(only = false) loc env specifier =
  (* We first divide the parts of the specifier as follows:
       - a storage class
       - a set of attributes (const, volatile, restrict)
       - a list of type specifiers *)
  let sto = ref Storage_default
  and inline = ref false
  and attr = ref []
  and tyspecs = ref [] in

  let do_specifier = function
  | SpecTypedef -> ()
  | SpecCV cv ->
      let a =
        match cv with
        | CV_CONST -> AConst
        | CV_VOLATILE -> AVolatile
        | CV_RESTRICT -> ARestrict in
      attr := add_attributes [a] !attr
  | SpecAttr a ->
      attr := add_attributes (elab_attributes loc env [a]) !attr
  | SpecStorage st ->
      if !sto <> Storage_default then
        error loc "multiple storage specifiers";
      begin match st with
      | NO_STORAGE -> ()
      | AUTO -> ()
      | STATIC -> sto := Storage_static
      | EXTERN -> sto := Storage_extern
      | REGISTER -> sto := Storage_register
      end
  | SpecInline -> inline := true
  | SpecType tys -> tyspecs := tys :: !tyspecs in

  List.iter do_specifier specifier;

  let simple ty = (!sto, !inline, add_attributes_type !attr ty, env) in

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

    (* int64 is a MSVC extension *)
    | [Cabs.Tint64] -> simple (TInt(ILongLong, []))
    | [Cabs.Tsigned; Cabs.Tint64] -> simple (TInt(ILongLong, []))
    | [Cabs.Tunsigned; Cabs.Tint64] -> simple (TInt(IULongLong, []))

    | [Cabs.Tfloat] -> simple (TFloat(FFloat, []))
    | [Cabs.Tdouble] -> simple (TFloat(FDouble, []))

    | [Cabs.Tlong; Cabs.Tdouble] -> simple (TFloat(FLongDouble, []))

    (* Now the other type specifiers *)

    | [Cabs.Tnamed id] ->
        let (id', info) = wrap Env.lookup_typedef loc env id in
        simple (TNamed(id', []))

    | [Cabs.Tstruct(id, optmembers, a)] ->
        let a' =
          add_attributes (get_type_attrs()) (elab_attributes loc env a) in
        let (id', env') =
          elab_struct_or_union only Struct loc id optmembers a' env in
        (!sto, !inline, TStruct(id', !attr), env')

    | [Cabs.Tunion(id, optmembers, a)] ->
        let a' =
          add_attributes (get_type_attrs()) (elab_attributes loc env a) in
        let (id', env') =
          elab_struct_or_union only Union loc id optmembers a' env in
        (!sto, !inline, TUnion(id', !attr), env')

    | [Cabs.Tenum(id, optmembers, a)] ->
        let a' =
          add_attributes (get_type_attrs()) (elab_attributes loc env a) in
        let (id', env') = 
          elab_enum loc id optmembers a' env in
        (!sto, !inline, TEnum(id', !attr), env')

    | [Cabs.TtypeofE _] ->
        fatal_error loc "GCC __typeof__ not supported"
    | [Cabs.TtypeofT _] ->
        fatal_error loc "GCC __typeof__ not supported"

    (* Specifier doesn't make sense *)
    | _ ->
        fatal_error loc "illegal combination of type specifiers"

(* Elaboration of a type declarator.  *)

and elab_type_declarator loc env ty = function
  | Cabs.JUSTBASE ->
      (ty, env)
  | Cabs.PARENTYPE(attr1, d, attr2) ->
      (* XXX ignoring the distinction between attrs after and before *)
      let a = elab_attributes loc env (attr1 @ attr2) in
      elab_type_declarator loc env (add_attributes_type a ty) d
  | Cabs.ARRAY(d, attr, sz) ->
      let a = elab_attributes loc env attr in
      let sz' =
        match sz with
        | Cabs.NOTHING ->
            None
        | _ ->
            match Ceval.integer_expr env (!elab_expr_f loc env sz) with
            | Some n ->
                if n < 0L then error loc "array size is negative";
                Some n
            | None ->
                error loc "array size is not a compile-time constant";
                Some 1L in (* produces better error messages later *)
       elab_type_declarator loc env (TArray(ty, sz', a)) d
  | Cabs.PTR(attr, d) ->
      let a = elab_attributes loc env attr in
       elab_type_declarator loc env (TPtr(ty, a)) d
  | Cabs.PROTO(d, params, vararg) ->
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

and elab_parameter env (spec, name) =
  let (id, sto, inl, ty, env1) = elab_name env spec name in
  if sto <> Storage_default && sto <> Storage_register then
    error (loc_of_name name)
      "'extern' or 'static' storage not supported for function parameter";
  (* replace array and function types by pointer types *)
  let ty1 = argument_conversion env1 ty in
  let (id', env2) = Env.enter_ident env1 id sto ty1 in
  ( (id', ty1) , env2 )

(* Elaboration of a (specifier, Cabs "name") pair *)

and elab_name env spec (id, decl, attr, loc) =
  let (sto, inl, bty, env') = elab_specifier loc env spec in
  let (ty, env'') = elab_type_declarator loc env' bty decl in 
  let a = elab_attributes loc env attr in
  (id, sto, inl, add_attributes_type a ty, env'')

(* Elaboration of a name group *)

and elab_name_group loc env (spec, namelist) =
  let (sto, inl, bty, env') =
    elab_specifier loc env spec in
  let elab_one_name env (id, decl, attr, loc) =
    let (ty, env1) =
      elab_type_declarator loc env bty decl in 
    let a = elab_attributes loc env attr in
    ((id, sto, add_attributes_type a ty), env1) in
  mmap elab_one_name env' namelist

(* Elaboration of an init-name group *)

and elab_init_name_group loc env (spec, namelist) =
  let (sto, inl, bty, env') =
    elab_specifier loc env spec in
  let elab_one_name env ((id, decl, attr, loc), init) =
    let (ty, env1) =
      elab_type_declarator loc env bty decl in 
    let a = elab_attributes loc env attr in
    ((id, sto, add_attributes_type a ty, init), env1) in
  mmap elab_one_name env' namelist

(* Elaboration of a field group *)

and elab_field_group loc env (spec, fieldlist) =
  let (names, env') =
    elab_name_group loc env (spec, List.map fst fieldlist) in

  let elab_bitfield ((_, _, _, loc), optbitsize) (id, sto, ty) =
    if sto <> Storage_default then
      error loc "member '%s' has non-default storage" id;
    let optbitsize' =
      match optbitsize with
      | None -> None
      | Some sz ->
          let ik =
            match unroll env' ty with
            | TInt(ik, _) -> ik
            | TEnum(_, _) -> enum_ikind
            | _ -> ILongLong (* trigger next error message *) in
          if integer_rank ik > integer_rank IInt then
              error loc
                "the type of '%s' must be an integer type \
                 no bigger than 'int'" id;
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
              None in
    { fld_name = id; fld_typ = ty; fld_bitfield = optbitsize' } 
  in
  (List.map2 elab_bitfield fieldlist names, env')

(* Elaboration of a struct or union *)

and elab_struct_or_union_info kind loc env members attrs =
  let (m, env') = mmap (elab_field_group loc) env members in
  let m = List.flatten m in
  (* Check for incomplete types *)
  let rec check_incomplete = function
  | [] -> ()
  | [ { fld_typ = TArray(ty_elt, None, _) } ] when kind = Struct -> ()
        (* C99: ty[] allowed as last field of a struct *)
  | fld :: rem ->
      if incomplete_type env' fld.fld_typ then
        error loc "member '%s' has incomplete type" fld.fld_name;
      check_incomplete rem in
  check_incomplete m;
  (composite_info_def env' kind attrs m, env')

(* Elaboration of a struct or union *)

and elab_struct_or_union only kind loc tag optmembers attrs env =
  let warn_attrs () =
    if attrs <> [] then
      warning loc "attributes over struct/union ignored in this context" in
  let optbinding =
    if tag = "" then None else Env.lookup_composite env tag in
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
      emit_elab (elab_loc loc)
                (Gcompositedef(kind, tag', attrs, ci'.ci_members));
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
      emit_elab (elab_loc loc)
                (Gcompositedecl(kind, tag', attrs));
      (tag', env')
  | _, Some members ->
      (* definition of a complete struct or union *)
      let ci1 = composite_info_decl env kind attrs in
      (* enter it, incomplete, with a new name *)
      let (tag', env') = Env.enter_composite env tag ci1 in
      (* emit a declaration so that inner structs and unions can refer to it *)
      emit_elab (elab_loc loc)
                (Gcompositedecl(kind, tag', attrs));
      (* elaborate the members *)
      let (ci2, env'') =
        elab_struct_or_union_info kind loc env' members attrs in
      (* emit a definition *)
      emit_elab (elab_loc loc)
                (Gcompositedef(kind, tag', attrs, ci2.ci_members));
      (* Replace infos but keep same ident *)
      (tag', Env.add_composite env'' tag' ci2)

(* Elaboration of an enum item *)

and elab_enum_item env (s, exp, loc) nextval =
  let (v, exp') =
    match exp with
    | NOTHING ->
        (nextval, None)
    | _ ->
        let exp' = !elab_expr_f loc env exp in
        match Ceval.integer_expr env exp' with
        | Some n -> (n, Some exp')
        | None ->
            error loc
              "value of enumerator '%s' is not a compile-time constant" s;
            (nextval, Some exp') in
  if redef Env.lookup_ident env s <> None then
    error loc "redefinition of enumerator '%s'" s;
  if not (int_representable v (8 * sizeof_ikind enum_ikind) (is_signed_ikind enum_ikind)) then
     warning loc "the value of '%s' is not representable with type %a"
                 s Cprint.typ (TInt(enum_ikind, []));
  let (id, env') = Env.enter_enum_item env s v in
  ((id, v, exp'), Int64.succ v, env')

(* Elaboration of an enumeration declaration *)

and elab_enum loc tag optmembers attrs env =
  match optmembers with
  | None ->
      let (tag', info) = wrap Env.lookup_enum loc env tag in (tag', env)
      (* XXX this will cause an error for incomplete enum definitions. *)
  | Some members ->
      let rec elab_members env nextval = function
      | [] -> ([], env)
      | hd :: tl ->
          let (dcl1, nextval1, env1) = elab_enum_item env hd nextval in
          let (dcl2, env2) = elab_members env1 nextval1 tl in
          (dcl1 :: dcl2, env2) in
      let (dcls, env') = elab_members env 0L members in
      let info = { ei_members = dcls; ei_attr = attrs } in
      let (tag', env'') = Env.enter_enum env' tag info in
      emit_elab (elab_loc loc) (Genumdef(tag', attrs, dcls));
      (tag', env'')

(* Elaboration of a naked type, e.g. in a cast *)

let elab_type loc env spec decl =
  let (sto, inl, bty, env') = elab_specifier loc env spec in
  let (ty, env'') = elab_type_declarator loc env' bty decl in 
  if sto <> Storage_default || inl then
    error loc "'extern', 'static', 'register' and 'inline' are meaningless in cast";
  ty


(* Elaboration of expressions *)

let elab_expr loc env a =

  let err fmt = error loc fmt in  (* non-fatal error *)
  let error fmt = fatal_error loc fmt in
  let warning fmt = warning loc fmt in

  let rec elab = function

  | NOTHING ->
      error "empty expression"

(* 7.3 Primary expressions *)

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

  | PAREN e ->
      elab e

(* 7.4 Postfix expressions *)

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
        etyp = add_attributes_type attrs (type_of_member env fld) }

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
        etyp = add_attributes_type attrs (type_of_member env fld) }

(* Hack to treat vararg.h functions the GCC way.  Helps with testing.
    va_start(ap,n)
      (preprocessing) --> __builtin_va_start(ap, arg)
      (elaboration)   --> __builtin_va_start(ap, &arg)
    va_arg(ap, ty)
      (preprocessing) --> __builtin_va_arg(ap, ty)
      (parsing)       --> __builtin_va_arg(ap, sizeof(ty))
*)
  | CALL((VARIABLE "__builtin_va_start" as a1), [a2; a3]) ->
      let b1 = elab a1 and b2 = elab a2 and b3 = elab a3 in
      { edesc = ECall(b1, [b2; {edesc = EUnop(Oaddrof, b3);
                                etyp = TPtr(b3.etyp, [])}]);
        etyp = TVoid [] }
  | CALL((VARIABLE "__builtin_va_arg" as a1),
         [a2; (TYPE_SIZEOF _) as a3]) ->
      let b1 = elab a1 and b2 = elab a2 and b3 = elab a3 in
      let ty = match b3.edesc with ESizeof ty -> ty | _ -> assert false in
      { edesc = ECall(b1, [b2; b3]); etyp = ty }

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
            emit_elab (elab_loc loc) (Gdecl(Storage_extern, id, ty, None));
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

(* 7.5 Unary expressions *)

  | CAST ((spec, dcl), SINGLE_INIT a1) ->
      let ty = elab_type loc env spec dcl in
      let b1 = elab a1 in
      if not (valid_cast env b1.etyp ty) then
        err "illegal cast from %a@ to %a" Cprint.typ b1.etyp Cprint.typ ty;
      { edesc = ECast(ty, b1); etyp = ty }

  | CAST ((spec, dcl), _) ->
      error "cast of initializer expression is not supported"

  | EXPR_SIZEOF a1 ->
      let b1 = elab a1 in
      if sizeof env b1.etyp = None then
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
      if sizeof env ty = None then
        err "incomplete type %a" Cprint.typ ty;
      { edesc = ESizeof ty; etyp = TInt(size_t_ikind, []) }

  | EXPR_ALIGNOF a1 ->
      let b1 = elab a1 in
      if sizeof env b1.etyp = None then
        err "incomplete type %a" Cprint.typ b1.etyp;
      { edesc = EAlignof b1.etyp; etyp =  TInt(size_t_ikind, []) }

  | TYPE_ALIGNOF (spec, dcl) ->
      let ty = elab_type loc env spec dcl in
      if sizeof env ty = None then
        err "incomplete type %a" Cprint.typ ty;
      { edesc = EAlignof ty; etyp =  TInt(size_t_ikind, []) }

  | UNARY(PLUS, a1) ->
      let b1 = elab a1 in
      if not (is_arith_type env b1.etyp) then
        error "argument of unary '+' is not an arithmetic type";
      { edesc = EUnop(Oplus, b1); etyp = unary_conversion env b1.etyp }

  | UNARY(MINUS, a1) ->
      let b1 = elab a1 in
      if not (is_arith_type env b1.etyp) then
        error "argument of unary '-' is not an arithmetic type";
      { edesc = EUnop(Ominus, b1); etyp = unary_conversion env b1.etyp }

  | UNARY(BNOT, a1) ->
      let b1 = elab a1 in
      if not (is_integer_type env b1.etyp) then
        error "argument of '~' is not an integer type";
      { edesc = EUnop(Onot, b1); etyp = unary_conversion env b1.etyp }

  | UNARY(NOT, a1) ->
      let b1 = elab a1 in
      if not (is_scalar_type env b1.etyp) then
        error "argument of '!' is not a scalar type";
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

(* 7.6 Binary operator expressions *)

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
          let (ty, attr) =
            match unroll env b1.etyp, unroll env b2.etyp with
            | (TPtr(ty, a) | TArray(ty, _, a)), (TInt _ | TEnum _) -> (ty, a)
            | (TInt _ | TEnum _), (TPtr(ty, a) | TArray(ty, _, a)) -> (ty, a)
            | _, _ -> error "type error in binary '+'" in
          if not (pointer_arithmetic_ok env ty) then
            err "illegal pointer arithmetic in binary '+'";
          TPtr(ty, attr)
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
              (TPtr(ty, a), TPtr(ty, a))
          | (TInt _ | TEnum _), (TPtr(ty, a) | TArray(ty, _, a)) ->
              if not (pointer_arithmetic_ok env ty) then
                err "illegal pointer arithmetic in binary '-'";
              (TPtr(ty, a), TPtr(ty, a))
          | (TPtr(ty1, a1) | TArray(ty1, _, a1)),
            (TPtr(ty2, a2) | TArray(ty2, _, a2)) ->
              if not (compatible_types ~noattrs:true env ty1 ty2) then
                err "mismatch between pointer types in binary '-'";
              if not (pointer_arithmetic_ok env ty1) then
                err "illegal pointer arithmetic in binary '-'";
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

(* 7.7 Logical operator expressions *)

  | BINARY(AND, a1, a2) ->
      elab_logical_operator "&&" Ologand a1 a2
  | BINARY(OR, a1, a2) ->
      elab_logical_operator "||" Ologor a1 a2

(* 7.8 Conditional expressions *)
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
              TPtr(TVoid [], add_attributes a1 a2)
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
          { edesc = EConditional(b1, b2, nullconst); etyp = TPtr(ty1, a1) }
      | TInt _, TPtr(ty2, a2) when is_literal_0 b2 ->
          { edesc = EConditional(b1, nullconst, b3); etyp = TPtr(ty2, a2) }
      | ty1, ty2 ->
          match combine_types ~noattrs:true env ty1 ty2 with
          | None ->
              error ("the second and third arguments of '? :' have incompatible types")
          | Some tyres ->
              { edesc = EConditional(b1, b2, b3); etyp = tyres }
      end

(* 7.9 Assignment expressions *)

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

(* 7.10 Sequential expressions *)

  | COMMA [] ->
      error "empty sequential expression"
  | COMMA (a1 :: al) ->                 (* watch for left associativity *)
      let rec elab_comma accu = function
      | [] -> accu
      | a :: l ->
          let b = elab a in
          elab_comma { edesc = EBinop(Ocomma, accu, b, b.etyp); etyp = b.etyp } l
      in elab_comma (elab a1) al

(* Extensions that we do not handle *)

  | LABELADDR _ ->
      error "GCC's &&label construct is not supported"
  | GNU_BODY _ ->
      error "GCC's statements within expressions are not supported"

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
  | NOTHING -> None
  | a -> Some (elab_expr loc env a)

let elab_for_expr loc env = function
  | NOTHING -> { sdesc = Sskip; sloc = elab_loc loc }
  | a -> { sdesc = Sdo (elab_expr loc env a); sloc = elab_loc loc }


(* Elaboration of initializers *)

let project_init loc il =
  List.map
   (fun (what, i) ->
      if what <> NEXT_INIT then
        error loc "C99 initializers are not supported";
      i)
   il

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
      add_chars (Int64.pred i) (Init_single (intconst c IChar) :: init)
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

(* Build an initializer for type [ty], consuming initialization items
   from the list [ile].  Return a pair (initializer, items not consumed). *)

let rec elab_init loc env ty ile =
  match unroll env ty with
  | TArray(ty_elt, opt_sz, _) ->
      let rec elab_init_array n accu rem =
        match opt_sz, rem with
        | Some sz, _ when n >= sz ->
            (Init_array(List.rev accu), rem)
        | None, [] ->
            (Init_array(List.rev accu), rem)
        | _, _ ->
          let (i, rem') = elab_init loc env ty_elt rem in
          elab_init_array (Int64.succ n) (i :: accu) rem' in
      begin match ile with
      (* char array = "string literal" *)
      | (SINGLE_INIT (CONSTANT (CONST_STRING s)) 
         | COMPOUND_INIT [_, SINGLE_INIT(CONSTANT (CONST_STRING s))]) :: ile1
        when (match unroll env ty_elt with
              | TInt((IChar|IUChar|ISChar), _) -> true
              | _ -> false) ->
          (init_char_array_string opt_sz s, ile1)
      (* wchar array = L"wide string literal" *)
      | (SINGLE_INIT (CONSTANT (CONST_WSTRING s))
         | COMPOUND_INIT [_, SINGLE_INIT(CONSTANT (CONST_WSTRING s))]) :: ile1
        when (match unroll env ty_elt with
              | TInt _ -> true
              | _ -> false) ->
          (init_int_array_wstring opt_sz s, ile1)
      (* array = { elt, ..., elt } *)
      | COMPOUND_INIT ile1 :: ile2 ->
          let (ie, rem) = elab_init_array 0L [] (project_init loc ile1) in
          if rem <> [] then
            warning loc "excess elements at end of array initializer";
          (ie, ile2)
      (* array = elt, ..., elt  (within a bigger compound initializer) *)
      | _ ->
          elab_init_array 0L [] ile
      end
  | TStruct(id, _) ->
      let ci = wrap Env.find_struct loc env id in
      let rec elab_init_fields fld accu rem =
        match fld with
        | [] -> 
            (Init_struct(id, List.rev accu), rem)
        | {fld_name = ""} :: fld' ->
            (* anonymous bitfields consume no initializer *)
            elab_init_fields fld' accu rem
        | fld1 :: fld' ->
            let (i, rem') = elab_init loc env fld1.fld_typ rem in
            elab_init_fields fld' ((fld1, i) :: accu) rem' in
      begin match ile with
      (* struct = { elt, ..., elt } *)
      | COMPOUND_INIT ile1 :: ile2 ->
          let (ie, rem) = 
            elab_init_fields ci.ci_members [] (project_init loc ile1) in
          if rem <> [] then
            warning loc "excess elements at end of struct initializer";
          (ie, ile2)
      (* struct = elt, ..., elt (within a bigger compound initializer) *)
      | _ ->
          elab_init_fields ci.ci_members [] ile
      end
  | TUnion(id, _) ->
      let ci = wrap Env.find_union loc env id in
      let fld1 =
        match ci.ci_members with [] -> assert false | hd :: tl -> hd in
      begin match ile with
      (* union = { elt } *)
      | COMPOUND_INIT ile1 :: ile2 ->
          let (i, rem) = 
            elab_init loc env fld1.fld_typ (project_init loc ile1) in
          if rem <> [] then
            warning loc "excess elements at end of union initializer";
          (Init_union(id, fld1, i), ile2)
      (* union = elt (within a bigger compound initializer) *)
      | _ ->
          let (i, rem) = elab_init loc env fld1.fld_typ ile in
          (Init_union(id, fld1, i), rem)
      end
  | TInt _ | TFloat _ | TPtr _ | TEnum _ ->
      begin match ile with
      (* scalar = elt *)
      | SINGLE_INIT a :: ile1 ->
          let a' = elab_expr loc env a in
          check_init_type loc env a' ty;
          (Init_single a', ile1)
      (* scalar = nothing (within a bigger compound initializer) *)
      | (NO_INIT :: ile1) | ([] as ile1) ->
          begin match unroll env ty with
          | TInt _ | TEnum _ -> (Init_single (intconst 0L IInt), ile1)
          | TFloat _ -> (Init_single floatconst0, ile1)
          | TPtr _   -> (Init_single nullconst, ile1)
          | _        -> assert false
          end
      | COMPOUND_INIT _ :: ile1 ->
          fatal_error loc "compound initializer for type@ %a" Cprint.typ ty
      end
  | _ ->
      fatal_error loc "impossible to initialize at type@ %a" Cprint.typ ty

let elab_initial loc env ty ie =
  match unroll env ty, ie with
  | _, NO_INIT -> None
  (* scalar or composite = expr *)
  | (TInt _ | TFloat _ | TPtr _ | TStruct _ | TUnion _ | TEnum _), SINGLE_INIT a ->
      let a' = elab_expr loc env a in
      check_init_type loc env a' ty;
      Some (Init_single a')
  (* array = expr or 
     array or struct or union = { elt, ..., elt } *)
  | (TArray _, SINGLE_INIT _)
  | ((TArray _ | TStruct _ | TUnion _), COMPOUND_INIT _) ->
      let (i, rem) = elab_init loc env ty [ie] in  
      if rem <> [] then
        warning loc "excess elements at end of compound initializer";
      Some i
  | _, _ ->
      error loc "ill-formed initializer for type@ %a" Cprint.typ ty;
      None

(* Complete an array type with the size obtained from the initializer:
   "int x[] = { 1, 2, 3 }" becomes "int x[3] = ..." *)

let fixup_typ env ty init =
  match unroll env ty, init with
  | TArray(ty_elt, None, attr), Init_array il ->
      TArray(ty_elt, Some(Int64.of_int(List.length il)), attr)
  | _ -> ty

(* Entry point *)

let elab_initializer loc env ty ie =
  match elab_initial loc env ty ie with
  | None ->
      (ty, None)
  | Some init ->
      (fixup_typ env ty init, Some init)


(* Elaboration of top-level and local definitions *)

let enter_typedef loc env (s, sto, ty) =
  if sto <> Storage_default then
    error loc "Non-default storage on 'typedef' definition";
  if redef Env.lookup_typedef env s <> None then
    error loc "Redefinition of typedef '%s'" s;
  let (id, env') =
    Env.enter_typedef env s ty in
  emit_elab (elab_loc loc) (Gtypedef(id, ty));
  env'

let enter_or_refine_ident local loc env s sto ty =
  match redef Env.lookup_ident env s with
  | Some(id, II_ident(old_sto, old_ty)) ->
      let new_ty =
        if local then begin
          error loc "redefinition of local variable '%s'" s;
          ty
        end else begin
          match combine_types env old_ty ty with
          | Some new_ty ->
              new_ty
          | None ->
              warning loc "redefinition of '%s' with incompatible type" s; ty
        end in
      let new_sto =
        if old_sto = Storage_extern then sto else
        if sto = Storage_extern then old_sto else
        if old_sto = sto then sto else begin
          warning loc "redefinition of '%s' with incompatible storage class" s;
          sto
        end in
      (id, Env.add_ident env id new_sto new_ty)
  | Some(id, II_enum v) ->
      error loc "illegal redefinition of enumerator '%s'" s;
      (id, Env.add_ident env id sto ty)
  | _ ->
      Env.enter_ident env s sto ty

let rec enter_decdefs local loc env = function
  | [] ->
      ([], env)
  | (s, sto, ty, init) :: rem ->
      (* Sanity checks on storage class *)
      begin match sto with
      | Storage_extern ->
          if init <> NO_INIT then error loc
                           "'extern' declaration cannot have an initializer"
      | Storage_register ->
          if not local then error loc "'register' on global declaration"
      | _ -> ()
      end;
      (* function declarations are always extern *)
      let sto' =
        match unroll env ty with TFun _ -> Storage_extern | _ -> sto in
      (* enter ident in environment with declared type, because
         initializer can refer to the ident *)
      let (id, env1) = enter_or_refine_ident local loc env s sto' ty in
      (* process the initializer *)
      let (ty', init') = elab_initializer loc env1 ty init in
      (* update environment with refined type *)
      let env2 = Env.add_ident env1 id sto' ty' in
      (* check for incomplete type *)
      if sto' <> Storage_extern && incomplete_type env ty' then
        warning loc "'%s' has incomplete type" s;
      if local && sto' <> Storage_extern && sto' <> Storage_static then begin
        (* Local definition *)
        let (decls, env3) = enter_decdefs local loc env2 rem in
        ((sto', id, ty', init') :: decls, env3)
      end else begin
        (* Global definition *)
        emit_elab (elab_loc loc) (Gdecl(sto', id, ty', init'));
        enter_decdefs local loc env2 rem
      end

let elab_fundef env (spec, name) body loc1 loc2 =
  let (s, sto, inline, ty, env1) = elab_name env spec name in
  if sto = Storage_register then
    error loc1 "a function definition cannot have 'register' storage class";
  (* Fix up the type.  We can have params = None but only for an
     old-style parameterless function "int f() {...}" *)
  let ty =
    match ty with
    | TFun(ty_ret, None, vararg, attr) -> TFun(ty_ret, Some [], vararg, attr)
    | _ -> ty in
  (* Extract info from type *)
  let (ty_ret, params, vararg) =
    match ty with
    | TFun(ty_ret, Some params, vararg, attr) -> (ty_ret, params, vararg)
    | _ -> fatal_error loc1 "wrong type for function definition" in
  (* Enter function in the environment, for recursive references *)
  let (fun_id, env1) = enter_or_refine_ident false loc1 env s sto ty in
  (* Enter parameters in the environment *)
  let env2 =
    List.fold_left (fun e (id, ty) -> Env.add_ident e id Storage_default ty)
                   (Env.new_scope env1) params in
  (* Elaborate function body *)
  let body' = !elab_funbody_f loc2 ty_ret env2 body in
  (* Build and emit function definition *)
  let fn =
    { fd_storage = sto;
      fd_inline = inline;
      fd_name = fun_id;
      fd_ret = ty_ret;
      fd_params = params;
      fd_vararg = vararg;
      fd_locals = [];
      fd_body = body' } in
  emit_elab (elab_loc loc1) (Gfundef fn);
  env1

let rec elab_definition (local: bool) (env: Env.t) (def: Cabs.definition)
                    : decl list * Env.t =
  match def with
  (* "int f(int x) { ... }" *)
  | FUNDEF(spec_name, body, loc1, loc2) ->
      if local then error loc1 "local definition of a function";
      let env1 = elab_fundef env spec_name body loc1 loc2 in
      ([], env1)

  (* "int x = 12, y[10], *z" *)
  | DECDEF(init_name_group, loc) ->
      let (dl, env1) = elab_init_name_group loc env init_name_group in
      enter_decdefs local loc env1 dl

  (* "typedef int * x, y[10]; " *)
  | TYPEDEF(namegroup, loc) ->
      let (dl, env1) = elab_name_group loc env namegroup in
      let env2 = List.fold_left (enter_typedef loc) env1 dl in
      ([], env2)

  (* "struct s { ...};" or "union u;" *)
  | ONLYTYPEDEF(spec, loc) ->
      let (sto, inl, ty, env') = elab_specifier ~only:true loc env spec in
      if sto <> Storage_default || inl then
        error loc "Non-default storage or 'inline' on 'struct' or 'union' declaration";
      ([], env')

  (* global asm statement *)
  | GLOBASM(_, loc) ->
      error loc "Top-level 'asm' statement is not supported";
      ([], env)

  (* pragma *)
  | PRAGMA(s, loc) ->
      emit_elab (elab_loc loc) (Gpragma s);
      ([], env)

  (* extern "C" { ... } *)
  | LINKAGE(_, loc, defs) ->
      elab_definitions local env defs

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

let block_labels b =
  let lbls = ref StringSet.empty in
  let rec do_stmt = function
  | BLOCK(b, _) -> do_block b
  | IF(_, s1, s2, _) -> do_stmt s1; do_stmt s2
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
  and do_block b = List.iter do_stmt b.bstmts
  in do_block b; !lbls

let ctx_loop ctx = { ctx with ctx_break = true; ctx_continue = true }

let ctx_switch ctx = { ctx with ctx_break = true }

(* Extract list of Cabs statements from a Cabs block *)

let block_body loc b =
  if b.blabels <> [] then
    error loc "GCC's '__label__' declaration is not supported";
  if b.battrs <> [] then
    warning loc "ignoring attributes on this block";
  b.bstmts


(* Elaboration of statements *)

let rec elab_stmt env ctx s =

  match s with

(* 8.2 Expression statements *)

  | COMPUTATION(a, loc) ->
      { sdesc = Sdo (elab_expr loc env a); sloc = elab_loc loc }

(* 8.3 Labeled statements *)

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

  | CASERANGE(_, _, _, loc) ->
      error loc "GCC's 'case' with range of values is not supported";
      sskip

  | DEFAULT(s1, loc) ->
      { sdesc = Slabeled(Sdefault, elab_stmt env ctx s1); sloc = elab_loc loc }

(* 8.4 Compound statements *)

  | BLOCK(b, loc) ->
      elab_block loc env ctx b

(* 8.5 Conditional statements *)

  | IF(a, s1, s2, loc) ->
      let a' = elab_expr loc env a in
      if not (is_scalar_type env a'.etyp) then
        error loc "the condition of 'if' does not have scalar type";
      let s1' = elab_stmt env ctx s1 in
      let s2' = elab_stmt env ctx s2 in
      { sdesc = Sif(a', s1', s2'); sloc = elab_loc loc }

(* 8.6 Iterative statements *)

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
      let a1' =
        match fc with
        | FC_EXP a1 ->
            elab_for_expr loc env a1
        | FC_DECL def ->
            error loc "C99 declaration within `for' not supported";
            sskip in
      let a2' =
        if a2 = NOTHING
        then intconst 1L IInt
        else elab_expr loc env a2 in
      if not (is_scalar_type env a2'.etyp) then
        error loc "the condition of 'for' does not have scalar type";
      let a3' = elab_for_expr loc env a3 in
      let s1' = elab_stmt env (ctx_loop ctx) s1 in
      { sdesc = Sfor(a1', a2', a3', s1'); sloc = elab_loc loc }

(* 8.7 Switch statement *)
  | SWITCH(a, s1, loc) ->
      let a' = elab_expr loc env a in
      if not (is_integer_type env a'.etyp) then
        error loc "the argument of 'switch' is not an integer";
      let s1' = elab_stmt env (ctx_switch ctx) s1 in
      { sdesc = Sswitch(a', s1'); sloc = elab_loc loc }

(* 8,8 Break and continue statements *)
  | BREAK loc ->
      if not ctx.ctx_break then
        error loc "'break' outside of a loop or a 'switch'";
      { sdesc = Sbreak; sloc = elab_loc loc }
  | CONTINUE loc ->
      if not ctx.ctx_continue then
        error loc "'continue' outside of a loop";
      { sdesc = Scontinue; sloc = elab_loc loc }

(* 8.9 Return statements *)
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

(* 8.10 Goto statements *)
  | GOTO(lbl, loc) ->
      if not (StringSet.mem lbl ctx.ctx_labels) then
        error loc "unknown 'goto' label %s" lbl;
      { sdesc = Sgoto lbl; sloc = elab_loc loc }

(* 8.11 Null statements *)
  | NOP loc ->
      { sdesc = Sskip; sloc = elab_loc loc }

(* Traditional extensions *)
  | ASM(attr, txt, details, loc) ->
      if details <> None then
        error loc "GCC's extended 'asm' statements are not supported";
      { sdesc = Sasm(String.concat "" txt); sloc = elab_loc loc }

(* Unsupported *)
  | DEFINITION def ->
      error (get_definitionloc def) "ill-placed definition";
      sskip
  | COMPGOTO(a, loc) ->
      error loc "GCC's computed 'goto' is not supported";
      sskip
  | TRY_EXCEPT(_, _, _, loc) ->
      error loc "'try ... except' statement is not supported";
      sskip
  | TRY_FINALLY(_, _, loc) ->
      error loc "'try ... finally' statement is not supported";
      sskip
      
and elab_block loc env ctx b =
  let b' = elab_block_body (Env.new_scope env) ctx (block_body loc b) in
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

let elab_funbody loc return_typ env b =
  let ctx =
    { ctx_return_typ = return_typ;
      ctx_labels = block_labels b;
      ctx_break = false;
      ctx_continue = false } in
  elab_block loc env ctx b

(* Filling in forward declaration *)
let _ = elab_funbody_f := elab_funbody


(** * Entry point *)

let elab_preprocessed_file name ic =
  let lb = Lexer.init name ic in
  reset();
  ignore (elab_definitions false (Builtins.environment())
                                 (Parser.file Lexer.initial lb));
  Lexer.finish();
  elaborated_program()
