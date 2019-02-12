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

open C

open Camlcoq
open! Floats
open Values
open Ctypes
open Csyntax

(** ** Extracting information about global variables from their atom *)

(** Record useful information about global variables and functions,
  and associate it with the corresponding atoms. *)

type inline_status =
  | No_specifier (* No inline specifier and no noinline attribute *)
  | Noinline     (* The atom is declared with the noinline attribute *)
  | Inline       (* The atom is declared inline *)

type atom_info =
  { a_storage: C.storage;              (* storage class *)
    a_alignment: int option;           (* alignment *)
    a_sections: Sections.section_name list; (* in which section to put it *)
      (* 1 section for data, 3 sections (code/lit/jumptbl) for functions *)
    a_access: Sections.access_mode;    (* access mode, e.g. small data area *)
    a_inline: inline_status;           (* function declared inline? *)
    a_loc: location                    (* source location *)
}

let decl_atom : (AST.ident, atom_info) Hashtbl.t = Hashtbl.create 103

let atom_is_static a =
  try
    (Hashtbl.find decl_atom a).a_storage = C.Storage_static
  with Not_found ->
    false

let atom_is_extern a =
  try
    (Hashtbl.find decl_atom a).a_storage = C.Storage_extern
  with Not_found ->
    false

let atom_alignof a =
  try
    (Hashtbl.find decl_atom a).a_alignment
  with Not_found ->
    None

let atom_sections a =
  try
    (Hashtbl.find decl_atom a).a_sections
  with Not_found ->
    []

let atom_is_small_data a ofs =
  try
    (Hashtbl.find decl_atom a).a_access = Sections.Access_near
  with Not_found ->
    false

let atom_is_rel_data a ofs =
  try
    (Hashtbl.find decl_atom a).a_access = Sections.Access_far
  with Not_found ->
    false

let atom_inline a =
  try
    (Hashtbl.find decl_atom a).a_inline
  with Not_found ->
    No_specifier

(** Iso C99 defines inline definitions of functions as functions
    with inline specifier and without extern. These functions do
    not provide an external definition. In the case of non static
    functions this means that no code should be generated for these
    functions. *)
let atom_is_iso_inline_definition a =
  try
    let i = Hashtbl.find decl_atom a in
    match i.a_storage with
    | C.Storage_default -> i.a_inline = Inline
    | _ -> false
  with Not_found ->
    false

let atom_location a =
  try
    (Hashtbl.find decl_atom a).a_loc
  with Not_found ->
    Cutil.no_loc

(** The current environment of composite definitions *)

let comp_env : composite_env ref = ref Maps.PTree.empty

(** Hooks -- overriden in machine-dependent CPragmas module *)

let process_pragma_hook = ref (fun (_: string) -> false)

(** ** Error handling *)

let currentLocation = ref Cutil.no_loc

let updateLoc l = currentLocation := l

let currentFunction = ref ""

let updateFunction f = currentFunction := f

let error fmt =
  Diagnostics.error !currentLocation fmt

let fatal_error fmt =
  Diagnostics.fatal_error !currentLocation fmt

let unsupported msg =
  Diagnostics.error !currentLocation "unsupported feature: %s"  msg

let warning t msg =
  Diagnostics.warning !currentLocation t msg

let string_of_errmsg msg =
  let string_of_err = function
  | Errors.MSG s -> camlstring_of_coqstring s
  | Errors.CTX i -> extern_atom i
  | Errors.POS i -> Z.to_string (Z.Zpos i)
  in String.concat "" (List.map string_of_err msg)

(** ** The builtin environment *)

let ais_annot_functions =
  if Configuration.elf_target then
    [(* Ais Annotations, only available for ELF targets *)
       "__builtin_ais_annot",
     (TVoid [],
      [TPtr(TInt(IChar, [AConst]), [])],
      true);]
  else
    []

let builtins_generic = {
  Builtins.typedefs = [];
  Builtins.functions =
    ais_annot_functions
      @
    [
    (* Integer arithmetic *)
    "__builtin_bswap",
    (TInt(IUInt, []), [TInt(IUInt, [])], false);
    "__builtin_bswap32",
      (TInt(IUInt, []), [TInt(IUInt, [])], false);
    "__builtin_bswap16",
      (TInt(IUShort, []), [TInt(IUShort, [])], false);
    (* Floating-point absolute value *)
    "__builtin_fabs",
    (TFloat(FDouble, []), [TFloat(FDouble, [])], false);
    (* Float arithmetic *)
    "__builtin_fsqrt",
    (TFloat(FDouble, []), [TFloat(FDouble, [])], false);
    (* Block copy *)
    "__builtin_memcpy_aligned",
         (TVoid [],
           [TPtr(TVoid [], []);
            TPtr(TVoid [AConst], []);
            TInt(IULong, []);
            TInt(IULong, [])],
          false);
    (* Annotations *)
    "__builtin_annot",
        (TVoid [],
          [TPtr(TInt(IChar, [AConst]), [])],
          true);
    "__builtin_annot_intval",
        (TInt(IInt, []),
          [TPtr(TInt(IChar, [AConst]), []); TInt(IInt, [])],
          false);
    (* Software memory barrier *)
    "__builtin_membar",
        (TVoid [],
          [],
          false);
    (* Variable arguments *)
(* va_start(ap,n)
      (preprocessing) --> __builtin_va_start(ap, arg)
      (elaboration)   --> __builtin_va_start(ap) *)
    "__builtin_va_start",
        (TVoid [],
          [TPtr(TVoid [], [])],
          false);
(* va_arg(ap, ty)
      (preprocessing) --> __builtin_va_arg(ap, ty)
      (parsing)       --> __builtin_va_arg(ap, sizeof(ty)) *)
    "__builtin_va_arg",
        (TVoid [],
          [TPtr(TVoid [], []); TInt(IUInt, [])],
          false);
    "__builtin_va_copy",
        (TVoid [],
          [TPtr(TVoid [], []); TPtr(TVoid [], [])],
          false);
    "__builtin_va_end",
        (TVoid [],
          [TPtr(TVoid [], [])],
          false);
    "__compcert_va_int32",
        (TInt(IUInt, []),
          [TPtr(TVoid [], [])],
          false);
    "__compcert_va_int64",
        (TInt(IULongLong, []),
          [TPtr(TVoid [], [])],
          false);
    "__compcert_va_float64",
        (TFloat(FDouble, []),
          [TPtr(TVoid [], [])],
          false);
    "__compcert_va_composite",
        (TPtr(TVoid [], []),
          [TPtr(TVoid [], []); TInt(IULong, [])],
          false);
  (* Helper functions for int64 arithmetic *)
    "__compcert_i64_dtos",
        (TInt(ILongLong, []),
         [TFloat(FDouble, [])],
         false);
    "__compcert_i64_dtou",
        (TInt(IULongLong, []),
         [TFloat(FDouble, [])],
         false);
    "__compcert_i64_stod",
        (TFloat(FDouble, []),
         [TInt(ILongLong, [])],
         false);
    "__compcert_i64_utod",
        (TFloat(FDouble, []),
         [TInt(IULongLong, [])],
         false);
    "__compcert_i64_stof",
        (TFloat(FFloat, []),
         [TInt(ILongLong, [])],
         false);
    "__compcert_i64_utof",
        (TFloat(FFloat, []),
         [TInt(IULongLong, [])],
         false);
    "__compcert_i64_sdiv",
        (TInt(ILongLong, []),
         [TInt(ILongLong, []); TInt(ILongLong, [])],
         false);
    "__compcert_i64_udiv",
        (TInt(IULongLong, []),
         [TInt(IULongLong, []); TInt(IULongLong, [])],
         false);
    "__compcert_i64_smod",
        (TInt(ILongLong, []),
         [TInt(ILongLong, []); TInt(ILongLong, [])],
         false);
    "__compcert_i64_umod",
        (TInt(IULongLong, []),
         [TInt(IULongLong, []); TInt(IULongLong, [])],
         false);
    "__compcert_i64_shl",
        (TInt(ILongLong, []),
         [TInt(ILongLong, []); TInt(IInt, [])],
         false);
    "__compcert_i64_shr",
        (TInt(IULongLong, []),
         [TInt(IULongLong, []); TInt(IInt, [])],
         false);
    "__compcert_i64_sar",
        (TInt(ILongLong, []),
         [TInt(ILongLong, []); TInt(IInt, [])],
         false);
    "__compcert_i64_smulh",
        (TInt(ILongLong, []),
         [TInt(ILongLong, []); TInt(ILongLong, [])],
         false);
    "__compcert_i64_umulh",
        (TInt(IULongLong, []),
         [TInt(IULongLong, []); TInt(IULongLong, [])],
         false)
  ]
}

(* Add processor-dependent builtins *)

let builtins =
  Builtins.({ typedefs = builtins_generic.typedefs @ CBuiltins.builtins.typedefs;
    functions = builtins_generic.Builtins.functions @ CBuiltins.builtins.functions })

(** ** The known attributes *)

let attributes = [
  (* type-related -- currently none *)
  (* struct-related *)
  ("packed", Cutil.Attr_struct);
  (* function-related *)
  ("noreturn", Cutil.Attr_function);
  ("noinline",Cutil.Attr_function);
  (* name-related *)
  ("aligned", Cutil.Attr_name);
  (* object-related *)
  ("section", Cutil.Attr_object);
  ("unused", Cutil.Attr_object)
]


(** ** Functions used to handle string literals *)

let stringNum = ref 0   (* number of next global for string literals *)
let stringTable : (string, AST.ident) Hashtbl.t = Hashtbl.create 47
let wstringTable : (int64 list, AST.ident) Hashtbl.t = Hashtbl.create 47

let name_for_string_literal s =
  try
    Hashtbl.find stringTable s
  with Not_found ->
    incr stringNum;
    let name = Printf.sprintf "__stringlit_%d" !stringNum in
    let id = intern_string name in
    Hashtbl.add decl_atom id
      { a_storage = C.Storage_static;
        a_alignment = Some 1;
        a_sections = [Sections.for_stringlit()];
        a_access = Sections.Access_default;
        a_inline = No_specifier;
        a_loc = Cutil.no_loc };
    Hashtbl.add stringTable s id;
    id

let typeStringLiteral s =
  let sg = if Machine.((!config).char_signed) then Signed else Unsigned in
  Tarray(Tint(I8, sg, noattr), Z.of_uint (String.length s + 1), noattr)

let global_for_string s id =
  let init = ref [] in
  let add_char c =
    init := AST.Init_int8(Z.of_uint(Char.code c)) :: !init in
  add_char '\000';
  for i = String.length s - 1 downto 0 do add_char s.[i] done;
  (id, AST.Gvar { AST.gvar_info = typeStringLiteral s;  AST.gvar_init = !init;
              AST.gvar_readonly = true;  AST.gvar_volatile = false})

let name_for_wide_string_literal s =
  try
    Hashtbl.find wstringTable s
  with Not_found ->
    incr stringNum;
    let name = Printf.sprintf "__stringlit_%d" !stringNum in
    let id = intern_string name in
    Hashtbl.add decl_atom id
      { a_storage = C.Storage_static;
        a_alignment = Some Machine.((!config).sizeof_wchar);
        a_sections = [Sections.for_stringlit()];
        a_access = Sections.Access_default;
        a_inline = No_specifier;
        a_loc = Cutil.no_loc };
    Hashtbl.add wstringTable s id;
    id

let typeWideStringLiteral s =
  let sz =
    match Machine.((!config).sizeof_wchar) with
    | 2 -> I16
    | 4 -> I32
    | _ -> assert false in
  let sg =
    if Machine.((!config).wchar_signed) then Signed else Unsigned in
  Tarray(Tint(sz, sg, noattr), Z.of_uint (List.length s + 1), noattr)

let global_for_wide_string s id =
  let init = ref [] in
  let init_of_char =
    match Machine.((!config).sizeof_wchar) with
    | 2 -> (fun z -> AST.Init_int16 z)
    | 4 -> (fun z -> AST.Init_int32 z)
    | _ -> assert false in
  let add_char c =
    init := init_of_char(Z.of_uint64 c) :: !init in
  List.iter add_char s;
  add_char 0L;
   AST.(id,  Gvar { gvar_info = typeWideStringLiteral s;  gvar_init = List.rev !init;
             gvar_readonly = true; gvar_volatile = false})

let globals_for_strings globs =
  let globs1 =
    Hashtbl.fold
      (fun s id l -> global_for_wide_string s id :: l)
      wstringTable globs in
  let globs2 =
    Hashtbl.fold
      (fun s id l -> global_for_string s id :: l)
      stringTable globs1 in
  globs2

(** ** Handling of inlined memcpy functions *)

let constant_size_t a =
  match Initializers.constval_cast !comp_env a Ctyping.size_t with
  | Errors.OK(Vint n) -> Some(Integers.Int.unsigned n)
  | Errors.OK(Vlong n) -> Some(Integers.Int64.unsigned n)
  | _ -> None

let make_builtin_memcpy args =
  match args with
  | Econs(dst, Econs(src, Econs(sz, Econs(al, Enil)))) ->
      let sz1 =
        match constant_size_t sz with
        | Some n -> n
        | None -> error "size argument of '__builtin_memcpy_aligned' must be a constant"; Z.zero in
      let al1 =
        match constant_size_t al with
        | Some n -> n
        | None -> error "alignment argument of '__builtin_memcpy_aligned' must be a constant"; Z.one in
      if not (Z.is_power2 al1) then
        error "alignment argument of '__builtin_memcpy_aligned' must be a power of 2";
      if not (Z.eq (Z.modulo sz1 al1) Z.zero) then
        error "alignment argument of '__builtin_memcpy_aligned' must be a divisor of the size";
      (* Issue #28: must decay array types to pointer types *)
      Ebuiltin( AST.EF_memcpy(sz1, al1),
               Tcons(typeconv(typeof dst),
                     Tcons(typeconv(typeof src), Tnil)),
               Econs(dst, Econs(src, Enil)), Tvoid)
  | _ ->
    assert false

(** ** Translation of [va_arg] for variadic functions. *)

let va_list_ptr e =
  if not CBuiltins.va_list_scalar then e else
    match e with
    | Evalof(e', _) -> Eaddrof(e', Tpointer(typeof e, noattr))
    | _             -> error "bad use of a va_list object"; e

let make_builtin_va_arg_by_val helper ty ty_ret arg =
  let ty_fun =
    Tfunction(Tcons(Tpointer(Tvoid, noattr), Tnil), ty_ret,  AST.cc_default) in
  Ecast
    (Ecall(Evalof(Evar(intern_string helper, ty_fun), ty_fun),
           Econs(va_list_ptr arg, Enil),
           ty_ret),
     ty)

let make_builtin_va_arg_by_ref helper ty arg =
  let ty_fun =
    Tfunction(Tcons(Tpointer(Tvoid, noattr), Tcons(Ctyping.size_t, Tnil)),
              Tpointer(Tvoid, noattr),  AST.cc_default) in
  let ty_ptr =
    Tpointer(ty, noattr) in
  let call =
    Ecall(Evalof(Evar(intern_string helper, ty_fun), ty_fun),
          Econs(va_list_ptr arg, Econs(Esizeof(ty, Ctyping.size_t), Enil)),
          Tpointer(Tvoid, noattr)) in
  Evalof(Ederef(Ecast(call, ty_ptr), ty), ty)

let make_builtin_va_arg env ty e =
  match ty with
  | Ctypes.Tint _ ->
      make_builtin_va_arg_by_val
        "__compcert_va_int32" ty (Tint(I32, Unsigned, noattr)) e
  | Tpointer _ when Archi.ptr64 = false ->
      make_builtin_va_arg_by_val
        "__compcert_va_int32" ty (Tint(I32, Unsigned, noattr)) e
  | Tpointer _ when Archi.ptr64 = true ->
      make_builtin_va_arg_by_val
        "__compcert_va_int64" ty (Tlong(Unsigned, noattr)) e
  | Tlong _ ->
      make_builtin_va_arg_by_val
        "__compcert_va_int64" ty (Tlong(Unsigned, noattr)) e
  | Tfloat _ ->
      make_builtin_va_arg_by_val
        "__compcert_va_float64" ty (Tfloat(F64, noattr)) e
  | Tstruct _ | Tunion _ ->
      make_builtin_va_arg_by_ref
        "__compcert_va_composite" ty e
  | _ ->
      unsupported "va_arg at this type";
      Eval(Vint(coqint_of_camlint 0l), type_int32s)

(** ** Translation functions *)

(** Constants *)

let convertInt32 (n: int64) = coqint_of_camlint(Int64.to_int32 n)
let convertInt64 (n: int64) = coqint_of_camlint64 n
let convertIntZ  (n: int64) = Z.of_sint64 n

(** Attributes *)

let rec log2 n = if n = 1 then 0 else 1 + log2 (n lsr 1)

let convertAttr a =
  { attr_volatile = List.mem AVolatile a;
    attr_alignas =
      let n = Cutil.alignas_attribute a in
      if n > 0 then Some (N.of_int (log2 n)) else None }

let convertCallconv va unproto attr =
  let sr =
    Cutil.find_custom_attributes ["structreturn"; "__structreturn"] attr in
  {  AST.cc_vararg = va; cc_unproto = unproto; cc_structret = sr <> [] }

(** Types *)

let convertIkind k a : coq_type =
    match k with
  | C.IBool -> Tint (Ctypes.IBool, Unsigned, a)
  | C.IChar -> Tint (I8, (if Machine.((!config).char_signed)
                          then Signed else Unsigned), a)
  | C.ISChar -> Tint (I8, Signed, a)
  | C.IUChar -> Tint (I8, Unsigned, a)
  | C.IInt -> Tint (I32, Signed, a)
  | C.IUInt -> Tint (I32, Unsigned, a)
  | C.IShort -> Tint (I16, Signed, a)
  | C.IUShort -> Tint (I16, Unsigned, a)
  | C.ILong -> if Machine.((!config).sizeof_long) = 8
               then Tlong (Signed, a) else Tint (I32, Signed, a)
  | C.IULong -> if Machine.((!config).sizeof_long) = 8
                then Tlong (Unsigned, a) else Tint (I32, Unsigned, a)
  | C.ILongLong -> Tlong (Signed, a)
  | C.IULongLong -> Tlong (Unsigned, a)

let convertFkind k a : coq_type =
  match k with
  | C.FFloat -> Tfloat (F32, a)
  | C.FDouble -> Tfloat (F64, a)
  | C.FLongDouble ->
      if not !Clflags.option_flongdouble then unsupported "'long double' type";
      Tfloat (F64, a)

let checkFunctionType env tres targs =
  if not !Clflags.option_fstruct_passing then begin
    if Cutil.is_composite_type env tres then
      unsupported "function returning a struct or union (consider adding option [-fstruct-passing])";
    begin match targs with
    | None -> ()
    | Some l ->
        List.iter
          (fun (id, ty) ->
            if Cutil.is_composite_type env ty then
              unsupported "function parameter of struct or union type (consider adding option [-fstruct-passing])")
          l
    end
  end

let rec convertTyp env t =
  match t with
  | C.TVoid a -> Tvoid
  | C.TInt(ik, a) ->
      convertIkind ik (convertAttr a)
  | C.TFloat(fk, a) ->
      convertFkind fk (convertAttr a)
  | C.TPtr(ty, a) ->
      Tpointer(convertTyp env ty, convertAttr a)
  | C.TArray(ty, None, a) ->
      (* Cparser verified that the type ty[] occurs only in
         contexts that are safe for Clight, so just treat as ty[0]. *)
      (* warning "array type of unspecified size"; *)
      Tarray(convertTyp env ty, Z.zero, convertAttr a)
  | C.TArray(ty, Some sz, a) ->
      Tarray(convertTyp env ty, convertIntZ sz, convertAttr a)
  | C.TFun(tres, targs, va, a) ->
      checkFunctionType env tres targs;
      Tfunction(begin match targs with
                | None -> Tnil
                | Some tl -> convertParams env tl
                end,
                convertTyp env tres,
                convertCallconv va (targs = None) a)
  | C.TNamed _ ->
      convertTyp env (Cutil.unroll env t)
  | C.TStruct(id, a) ->
      Ctypes.Tstruct(intern_string id.name, convertAttr a)
  | C.TUnion(id, a) ->
      Tunion(intern_string id.name, convertAttr a)
  | C.TEnum(id, a) ->
      convertIkind Cutil.enum_ikind (convertAttr a)

and convertParams env = function
    | [] -> Tnil
    | (id, ty) :: rem -> Tcons(convertTyp env ty, convertParams env rem)

let rec convertTypArgs env tl el =
  match tl, el with
  | _, [] -> Tnil
  | [], e1 :: el ->
      Tcons(convertTyp env (Cutil.default_argument_conversion env e1.etyp),
            convertTypArgs env [] el)
  | (id, t1) :: tl, e1 :: el ->
      Tcons(convertTyp env t1, convertTypArgs env tl el)

let convertField env f =
  if f.fld_bitfield <> None then
    unsupported "bit field in struct or union (consider adding option [-fbitfields])";
  (intern_string f.fld_name, convertTyp env f.fld_typ)

let convertCompositedef env su id attr members =
  if Cutil.find_custom_attributes ["packed";"__packed__"] attr <> [] then
    unsupported "packed struct (consider adding option [-fpacked-structs])";
  let t = match su with
  | C.Struct ->
      let layout = Cutil.struct_layout env attr members in
      List.iter (fun (a,b) -> Debug.set_member_offset id a b) layout;
      TStruct (id,attr)
  | C.Union -> TUnion (id,attr) in
  Debug.set_composite_size id su (Cutil.sizeof env t);
  Composite(intern_string id.name,
            begin match su with C.Struct -> Ctypes.Struct | C.Union -> Ctypes.Union end,
            List.map (convertField env) members,
            convertAttr attr)

let rec projFunType env ty =
  match Cutil.unroll env ty with
  | TFun(res, args, vararg, attr) -> Some(res, args, vararg)
  | TPtr(ty', attr) -> projFunType env ty'
  | _ -> None

let string_of_type ty =
  let b = Buffer.create 20 in
  let fb = Format.formatter_of_buffer b in
  Cprint.typ fb ty;
  Format.pp_print_flush fb ();
  Buffer.contents b

let is_int64 env ty =
  match Cutil.unroll env ty with
  | C.TInt(k, _) -> Cutil.sizeof_ikind k = 8
  | C.TEnum(_, _) -> false
  | _ -> assert false

(** Floating point constants *)

let z_of_str hex str fst =
  let res = ref Z.Z0 in
  let base = if hex then 16 else 10 in
  for i = fst to String.length str - 1 do
    let d = int_of_char str.[i] in
    let d =
      if hex && d >= int_of_char 'a' && d <= int_of_char 'f' then
	d - int_of_char 'a' + 10
      else if hex && d >= int_of_char 'A' && d <= int_of_char 'F' then
	d - int_of_char 'A' + 10
      else
	d - int_of_char '0'
    in
    assert (d >= 0 && d < base);
    res := Z.add (Z.mul (Z.of_uint base) !res) (Z.of_uint d)
  done;
  !res


let checkFloatOverflow f typ =
  match f with
  | Fappli_IEEE.B754_finite _ -> ()
  | Fappli_IEEE.B754_zero _ ->
      warning Diagnostics.Literal_range "magnitude of floating-point constant too small for type '%s'"  typ
  | Fappli_IEEE.B754_infinity _ ->
      warning Diagnostics.Literal_range "magnitude of floating-point constant too large for type '%s'"  typ
  | Fappli_IEEE.B754_nan _ ->
      warning Diagnostics.Literal_range "floating-point converts converts to 'NaN'"

let convertFloat f kind =
  let mant = z_of_str f.C.hex (f.C.intPart ^ f.C.fracPart) 0 in
  match mant with
    | Z.Z0 ->
      begin match kind with
      | FFloat ->
	  Ctyping.econst_single (Float.to_single Float.zero)
      | FDouble | FLongDouble ->
	  Ctyping.econst_float Float.zero
      end
    | Z.Zpos mant ->

      let sgExp = match f.C.exp.[0] with '+' | '-' -> true | _ -> false in
      let exp = z_of_str false f.C.exp (if sgExp then 1 else 0) in
      let exp = if f.C.exp.[0] = '-' then Z.neg exp else exp in
      let shift_exp =
	(if f.C.hex then 4 else 1) * String.length f.C.fracPart in
      let exp = Z.sub exp (Z.of_uint shift_exp) in

      let base = P.of_int (if f.C.hex then 2 else 10) in

      begin match kind with
      | FFloat ->
	  let f = Float32.from_parsed base mant exp in
          checkFloatOverflow f "float";
          Ctyping.econst_single f
      | FDouble | FLongDouble ->
	  let f = Float.from_parsed base mant exp in
          checkFloatOverflow f "double";
          Ctyping.econst_float f
      end

    | Z.Zneg _ -> assert false

(** Expressions *)

let ezero = Eval(Vint(coqint_of_camlint 0l), type_int32s)

let ewrap = function
  | Errors.OK e -> e
  | Errors.Error msg ->
      error "retyping error: %s" (string_of_errmsg msg); ezero

let rec convertExpr env e =
  match e.edesc with
  | C.EConst (C.CStr _ | C.CWStr _)
  | C.EVar _
  | C.EUnop((C.Oderef|C.Odot _|C.Oarrow _), _)
  | C.EBinop(C.Oindex, _, _, _) ->
      let l = convertLvalue env e in
      ewrap (Ctyping.evalof l)

  | C.EConst(C.CInt(i, k, _)) ->
      let sg = if Cutil.is_signed_ikind k then Signed else Unsigned in
      if Cutil.sizeof_ikind k = 8
      then Ctyping.econst_long (convertInt64 i) sg
      else Ctyping.econst_int (convertInt32 i) sg
  | C.EConst(C.CFloat(f, k)) ->
      if k = C.FLongDouble && not !Clflags.option_flongdouble then
        unsupported "'long double' floating-point constant";
      convertFloat f k
  | C.EConst(C.CEnum(id, i)) ->
      Ctyping.econst_int (convertInt32 i) Signed
  | C.ESizeof ty1 ->
      Ctyping.esizeof (convertTyp env ty1)
  | C.EAlignof ty1 ->
      Ctyping.ealignof (convertTyp env ty1)

  | C.EUnop(C.Ominus, e1) ->
      ewrap (Ctyping.eunop Cop.Oneg (convertExpr env e1))
  | C.EUnop(C.Oplus, e1) ->
      convertExpr env e1
  | C.EUnop(C.Olognot, e1) ->
      ewrap (Ctyping.eunop Cop.Onotbool (convertExpr env e1))
  | C.EUnop(C.Onot, e1) ->
      ewrap (Ctyping.eunop Cop.Onotint (convertExpr env e1))
  | C.EUnop(C.Oaddrof, e1) ->
      ewrap (Ctyping.eaddrof (convertLvalue env e1))
  | C.EUnop(C.Opreincr, e1) ->
      ewrap (Ctyping.epreincr (convertLvalue env e1))
  | C.EUnop(C.Opredecr, e1) ->
      ewrap (Ctyping.epredecr (convertLvalue env e1))
  | C.EUnop(C.Opostincr, e1) ->
      ewrap (Ctyping.epostincr (convertLvalue env e1))
  | C.EUnop(C.Opostdecr, e1) ->
      ewrap (Ctyping.epostdecr (convertLvalue env e1))

  | C.EBinop((C.Oadd|C.Osub|C.Omul|C.Odiv|C.Omod|C.Oand|C.Oor|C.Oxor|
              C.Oshl|C.Oshr|C.Oeq|C.One|C.Olt|C.Ogt|C.Ole|C.Oge) as op,
             e1, e2, tyres) ->
      let op' =
        match op with
        | C.Oadd -> Cop.Oadd
        | C.Osub -> Cop.Osub
        | C.Omul -> Cop.Omul
        | C.Odiv -> Cop.Odiv
        | C.Omod -> Cop.Omod
        | C.Oand -> Cop.Oand
        | C.Oor  -> Cop.Oor
        | C.Oxor -> Cop.Oxor
        | C.Oshl -> Cop.Oshl
        | C.Oshr -> Cop.Oshr
        | C.Oeq  -> Cop.Oeq
        | C.One  -> Cop.One
        | C.Olt  -> Cop.Olt
        | C.Ogt  -> Cop.Ogt
        | C.Ole  -> Cop.Ole
        | C.Oge  -> Cop.Oge
        | _ -> assert false in
      ewrap (Ctyping.ebinop op' (convertExpr env e1) (convertExpr env e2))
  | C.EBinop(C.Oassign, e1, e2, _) ->
      let e1' = convertLvalue env e1 in
      let e2' = convertExpr env e2 in
      if Cutil.is_composite_type env e1.etyp
      && List.mem AVolatile (Cutil.attributes_of_type env e1.etyp) then
        warning Diagnostics.Unnamed "assignment to an lvalue of volatile composite type, the 'volatile' qualifier is ignored";
      if Cutil.is_composite_type env e2.etyp
      && List.mem AVolatile (Cutil.attributes_of_type env e2.etyp) then
        warning Diagnostics.Unnamed "assignment of a value of volatile composite type, the 'volatile' qualifier is ignored";
      ewrap (Ctyping.eassign e1' e2')
  | C.EBinop((C.Oadd_assign|C.Osub_assign|C.Omul_assign|C.Odiv_assign|
              C.Omod_assign|C.Oand_assign|C.Oor_assign|C.Oxor_assign|
              C.Oshl_assign|C.Oshr_assign) as op,
             e1, e2, tyres) ->
      let op' =
        match op with
        | C.Oadd_assign -> Cop.Oadd
        | C.Osub_assign -> Cop.Osub
        | C.Omul_assign -> Cop.Omul
        | C.Odiv_assign -> Cop.Odiv
        | C.Omod_assign -> Cop.Omod
        | C.Oand_assign -> Cop.Oand
        | C.Oor_assign  -> Cop.Oor
        | C.Oxor_assign -> Cop.Oxor
        | C.Oshl_assign -> Cop.Oshl
        | C.Oshr_assign -> Cop.Oshr
        | _ -> assert false in
      let e1' = convertLvalue env e1 in
      let e2' = convertExpr env e2 in
      ewrap (Ctyping.eassignop op' e1' e2')
  | C.EBinop(C.Ocomma, e1, e2, _) ->
      ewrap (Ctyping.ecomma (convertExpr env e1) (convertExpr env e2))
  | C.EBinop(C.Ologand, e1, e2, _) ->
      ewrap (Ctyping.eseqand (convertExpr env e1) (convertExpr env e2))
  | C.EBinop(C.Ologor, e1, e2, _) ->
      ewrap (Ctyping.eseqor (convertExpr env e1) (convertExpr env e2))

  | C.EConditional(e1, e2, e3) ->
      ewrap (Ctyping.econdition (convertExpr env e1)
                                (convertExpr env e2) (convertExpr env e3))
  | C.ECast(ty1, e1) ->
      ewrap (Ctyping.ecast (convertTyp env ty1) (convertExpr env e1))
  | C.ECompound(ty1, ie) ->
      unsupported "compound literals"; ezero

  | C.ECall({edesc = C.EVar {name = "__builtin_debug"}}, args) when List.length args < 2 ->
      error "too few arguments to function call, expected at least 2, have 0";
      ezero
  | C.ECall({edesc = C.EVar {name = "__builtin_debug"}}, args) ->
      let (kind, args1) =
        match args with
        | {edesc = C.EConst(CInt(n,_,_))} :: args1 when n <> 0L-> (n, args1)
        | _::args -> error "argument 1 of '__builtin_debug' must be a non-zero constant"; (1L, args)
        | [] -> assert false (* catched earlier *) in
      let (text, args2) =
        match args1 with
        | {edesc = C.EConst(CStr(txt))} :: args2 -> (txt, args2)
        | {edesc = C.EVar id} :: args2 -> (id.name, args2)
        | _::args2 -> error "argument 2 of '__builtin_debug' must be either a string literal or a variable"; ("", args2)
        | [] -> assert false (* catched earlier *) in
      let targs2 = convertTypArgs env [] args2 in
      Ebuiltin(
         AST.EF_debug(P.of_int64 kind, intern_string text,
                 typlist_of_typelist targs2),
        targs2, convertExprList env args2, convertTyp env e.etyp)

  | C.ECall({edesc = C.EVar {name = "__builtin_annot"}}, args) ->
      begin match args with
      | {edesc = C.EConst(CStr txt)} :: args1 ->
          let targs1 = convertTypArgs env [] args1 in
          Ebuiltin(
             AST.EF_annot(P.of_int 1,coqstring_of_camlstring txt, typlist_of_typelist targs1),
            targs1, convertExprList env args1, convertTyp env e.etyp)
      | _ ->
          error "argument 1 of '__builtin_annot' must be a string literal";
          ezero
      end

  | C.ECall({edesc = C.EVar {name = "__builtin_annot_intval"}}, args) ->
      begin match args with
      | [ {edesc = C.EConst(CStr txt)}; arg ] ->
          let targ = convertTyp env
                         (Cutil.default_argument_conversion env arg.etyp) in
          Ebuiltin(AST.EF_annot_val(P.of_int 1,coqstring_of_camlstring txt, typ_of_type targ),
                   Tcons(targ, Tnil), convertExprList env [arg],
                   convertTyp env e.etyp)
      | _ ->
          error "argument 1 of '__builtin_annot_intval' must be a string literal";
          ezero
      end

  | C.ECall({edesc = C.EVar {name = "__builtin_ais_annot"}}, args) when Configuration.elf_target ->
      begin match args with
      | {edesc = C.EConst(CStr txt)} :: args1 ->
        let file,line = !currentLocation in
        let fun_name = !currentFunction in
        let loc_string = Printf.sprintf "# file:%s line:%d function:%s\n" file line fun_name in
        let targs1 = convertTypArgs env [] args1 in
        AisAnnot.validate_ais_annot env !currentLocation txt args1;
          Ebuiltin(
             AST.EF_annot(P.of_int 2,coqstring_of_camlstring (loc_string ^ txt), typlist_of_typelist targs1),
            targs1, convertExprList env args1, convertTyp env e.etyp)
      | _ ->
          error "argument 1 of '__builtin_ais_annot' must be a string literal";
          ezero
      end

 | C.ECall({edesc = C.EVar {name = "__builtin_memcpy_aligned"}}, args) ->
      make_builtin_memcpy (convertExprList env args)

  | C.ECall({edesc = C.EVar {name = "__builtin_fabs"}}, [arg]) ->
      ewrap (Ctyping.eunop Cop.Oabsfloat (convertExpr env arg))

  | C.ECall({edesc = C.EVar {name = "__builtin_va_start"}} as fn, [arg]) ->
      Ecall(convertExpr env fn,
            Econs(va_list_ptr(convertExpr env arg), Enil),
            convertTyp env e.etyp)

  | C.ECall({edesc = C.EVar {name = "__builtin_va_arg"}}, [arg1; arg2]) ->
      make_builtin_va_arg env (convertTyp env e.etyp) (convertExpr env arg1)

  | C.ECall({edesc = C.EVar {name = "__builtin_va_end"}}, _) ->
      Ecast (ezero, Tvoid)

  | C.ECall({edesc = C.EVar {name = "__builtin_va_copy"}}, [arg1; arg2]) ->
      let dst = convertExpr env arg1 in
      let src = convertExpr env arg2 in
      Ebuiltin( AST.EF_memcpy(Z.of_uint CBuiltins.size_va_list, Z.of_uint 4),
               Tcons(Tpointer(Tvoid, noattr),
                 Tcons(Tpointer(Tvoid, noattr), Tnil)),
               Econs(va_list_ptr dst, Econs(va_list_ptr src, Enil)),
               Tvoid)

  | C.ECall({edesc = C.EVar {name = "printf"}}, args)
    when !Clflags.option_interp ->
      let targs = convertTypArgs env [] args
      and tres = convertTyp env e.etyp in
      let sg =
        signature_of_type targs tres
           { AST.cc_vararg = true; cc_unproto = false; cc_structret = false} in
      Ebuiltin( AST.EF_external(coqstring_of_camlstring "printf", sg),
               targs, convertExprList env args, tres)

  | C.ECall(fn, args) ->
      begin match projFunType env fn.etyp with
      | None ->
          error "wrong type for function part of a call"
      | Some(tres, targs, va) ->
          checkFunctionType env tres targs;
          if targs = None && not !Clflags.option_funprototyped then
            unsupported "call to unprototyped function (consider adding option [-funprototyped])";
          if va && not !Clflags.option_fvararg_calls then
            unsupported "call to variable-argument function (consider adding option [-fvararg-calls])"
      end;
      ewrap (Ctyping.ecall (convertExpr env fn) (convertExprList env args))

and convertLvalue env e =
  match e.edesc with
  | C.EVar id ->
      Evar(intern_string id.name, convertTyp env e.etyp)
  | C.EUnop(C.Oderef, e1) ->
      ewrap (Ctyping.ederef (convertExpr env e1))
  | C.EUnop(C.Odot id, e1) ->
      ewrap (Ctyping.efield !comp_env (convertExpr env e1) (intern_string id))
  | C.EUnop(C.Oarrow id, e1) ->
      let e1' = convertExpr env e1 in
      let e2' = ewrap (Ctyping.ederef e1') in
      let e3' = ewrap (Ctyping.evalof e2') in
      ewrap (Ctyping.efield !comp_env e3' (intern_string id))
  | C.EBinop(C.Oindex, e1, e2, _) ->
      let e1' = convertExpr env e1 and e2' = convertExpr env e2 in
      let e3' = ewrap (Ctyping.ebinop Cop.Oadd e1' e2') in
      ewrap (Ctyping.ederef e3')
  | C.EConst(C.CStr s) ->
      let ty = typeStringLiteral s in
      Evar(name_for_string_literal s, ty)
  | C.EConst(C.CWStr s) ->
      let ty = typeWideStringLiteral s in
      Evar(name_for_wide_string_literal s, ty)
  | _ ->
      error "illegal lvalue"; ezero

and convertExprList env el =
  match el with
  | [] -> Enil
  | e1 :: el' -> Econs(convertExpr env e1, convertExprList env el')

(* Extended assembly *)

let convertAsm loc env txt outputs inputs clobber =
  let (txt', output', inputs') =
    ExtendedAsm.transf_asm loc env txt outputs inputs clobber in
  let clobber' =
    List.map (fun s -> coqstring_uppercase_ascii_of_camlstring s) clobber in
  let ty_res =
    match output' with None -> TVoid [] | Some e -> e.etyp in
  (* Build the Ebuiltin expression *)
  let e =
    let tinputs = convertTypArgs env [] inputs' in
    let toutput = convertTyp env ty_res in
    Ebuiltin( AST.EF_inline_asm(coqstring_of_camlstring txt',
                           signature_of_type tinputs toutput  AST.cc_default,
                           clobber'),
             tinputs,
             convertExprList env inputs',
             convertTyp env ty_res) in
  (* Add an assignment to the output, if any *)
  match output' with
  | None -> e
  | Some lhs -> Eassign (convertLvalue env lhs, e, typeof e)

(* Separate the cases of a switch statement body *)

type switchlabel =
  | Case of C.exp
  | Default

type switchbody =
  | Label of switchlabel
  | Stmt of C.stmt

let rec flattenSwitch = function
  | {sdesc = C.Sseq(s1, s2)} ->
      flattenSwitch s1 @ flattenSwitch s2
  | {sdesc = C.Slabeled(C.Scase(e, _), s1)} ->
      Label(Case e) :: flattenSwitch s1
  | {sdesc = C.Slabeled(C.Sdefault, s1)} ->
      Label Default :: flattenSwitch s1
  | {sdesc = C.Slabeled(C.Slabel lbl, s1); sloc = loc} ->
      Stmt {sdesc = C.Slabeled(C.Slabel lbl, Cutil.sskip); sloc = loc}
      :: flattenSwitch s1
  | s ->
      [Stmt s]

let rec groupSwitch = function
  | [] ->
      (Cutil.sskip, [])
  | Label case :: rem ->
      let (fst, cases) = groupSwitch rem in
      (Cutil.sskip, (case, fst) :: cases)
  | Stmt s :: rem ->
      let (fst, cases) = groupSwitch rem in
      (Cutil.sseq s.sloc s fst, cases)

(* Test whether the statement contains case and give an *)
let rec contains_case s =
  match s.sdesc with
  | C.Sskip
  | C.Sdo _
  | C.Sbreak
  | C.Scontinue
  | C.Sswitch _ (* Stop at a switch *)
  | C.Sgoto _
  | C.Sreturn _
  | C.Sdecl _
  | C.Sasm _ ->  ()
  | C.Sseq (s1,s2)
  | C.Sif(_,s1,s2) -> contains_case s1; contains_case s2
  | C.Swhile (_,s1)
  | C.Sdowhile (s1,_) -> contains_case s1
  | C.Sfor (s1,e,s2,s3) ->  contains_case s1; contains_case s2; contains_case s3
  | C.Slabeled(C.Scase _, _) ->
      unsupported "'case' statement not in 'switch' statement"
  | C.Slabeled(_,s) -> contains_case s
  | C.Sblock b -> List.iter contains_case b

(** Annotations for line numbers *)

(** Statements *)

let swrap = function
  | Errors.OK s -> s
  | Errors.Error msg ->
      error "retyping error: %s" (string_of_errmsg msg); Csyntax.Sskip

let rec convertStmt env s =
  updateLoc s.sloc;
  match s.sdesc with
  | C.Sskip ->
      Csyntax.Sskip
  | C.Sdo e ->
      swrap (Ctyping.sdo (convertExpr env e))
  | C.Sseq(s1, s2) ->
      let s1' = convertStmt env s1 in
      let s2' = convertStmt env s2 in
      Ssequence(s1', s2')
  | C.Sif(e, s1, s2) ->
      let te = convertExpr env e in
      swrap (Ctyping.sifthenelse te (convertStmt env s1) (convertStmt env s2))
  | C.Swhile(e, s1) ->
      let te = convertExpr env e in
      swrap (Ctyping.swhile te (convertStmt env s1))
  | C.Sdowhile(s1, e) ->
      let te = convertExpr env e in
      swrap (Ctyping.sdowhile te (convertStmt env s1))
  | C.Sfor(s1, e, s2, s3) ->
      let te = convertExpr env e in
      swrap (Ctyping.sfor
                  (convertStmt env s1) te
                  (convertStmt env s2) (convertStmt env s3))
  | C.Sbreak ->
      Csyntax.Sbreak
  | C.Scontinue ->
      Csyntax.Scontinue
  | C.Sswitch(e, s1) ->
      let (init, cases) = groupSwitch (flattenSwitch s1) in
      let rec init_debug s =
        match s.sdesc with
        | Sseq (a,b) -> init_debug a && init_debug b
        | C.Sskip -> true
        | _ -> Cutil.is_debug_stmt s in
      if init.sdesc <> C.Sskip && not (init_debug init) then
        begin
          warning Diagnostics.Unnamed "ignored code at beginning of 'switch'";
          contains_case init
        end;
      let te = convertExpr env e in
      swrap (Ctyping.sswitch te
               (convertSwitch env (is_int64 env e.etyp) cases))
  | C.Slabeled(C.Slabel lbl, s1) ->
      Csyntax.Slabel(intern_string lbl, convertStmt env s1)
  | C.Slabeled(C.Scase _, _) ->
      unsupported "'case' statement not in 'switch' statement"; Csyntax.Sskip
  | C.Slabeled(C.Sdefault, _) ->
      unsupported "'default' statement not in 'switch' statement"; Csyntax.Sskip
  | C.Sgoto lbl ->
      Csyntax.Sgoto(intern_string lbl)
  | C.Sreturn None ->
      Csyntax.Sreturn None
  | C.Sreturn(Some e) ->
      Csyntax.Sreturn(Some(convertExpr env e))
  | C.Sblock _ ->
      unsupported "nested blocks"; Csyntax.Sskip
  | C.Sdecl _ ->
      unsupported "inner declarations"; Csyntax.Sskip
  | C.Sasm(attrs, txt, outputs, inputs, clobber) ->
      if not !Clflags.option_finline_asm then
        unsupported "inline 'asm' statement (consider adding option [-finline-asm])";
      Csyntax.Sdo (convertAsm s.sloc env txt outputs inputs clobber)

and convertSwitch env is_64 = function
  | [] ->
      LSnil
  | (lbl, s) :: rem ->
      updateLoc s.sloc;
      let lbl' =
        match lbl with
        | Default ->
            None
        | Case e ->
            match Ceval.integer_expr env e with
            | None -> unsupported "expression is not an integer constant expression";
                      None
            | Some v -> Some (if is_64
                              then Z.of_uint64 v
                              else Z.of_uint32 (Int64.to_int32 v))
      in
      LScons(lbl', convertStmt env s, convertSwitch env is_64 rem)

(** Function definitions *)

let convertFundef loc env fd =
  checkFunctionType env fd.fd_ret (Some fd.fd_params);
  updateFunction fd.fd_name.name;
  if fd.fd_vararg && not !Clflags.option_fvararg_calls then
    unsupported "variable-argument function (consider adding option [-fvararg-calls])";
  let ret =
    convertTyp env fd.fd_ret in
  let params =
    List.map
      (fun (id, ty) ->
        let id' = intern_string id.name in
        Debug.atom_parameter fd.fd_name id id';
        (id', convertTyp env ty))
      fd.fd_params in
  let vars =
    List.map
      (fun (sto, id, ty, init) ->
        if sto = Storage_extern || sto = Storage_static then
          unsupported "'static' or 'extern' local variable";
        if init <> None then
          unsupported "initialized local variable";
        let id' = intern_string id.name in
        Debug.atom_local_variable id id';
        (id', convertTyp env ty))
      fd.fd_locals in
  let body' = convertStmt env fd.fd_body in
  let id' = intern_string fd.fd_name.name in
  let noinline =  Cutil.find_custom_attributes ["noinline";"__noinline__"] fd.fd_attrib <> [] in
  let inline = if noinline || fd.fd_vararg then (* PR#15 *)
      Noinline
    else if fd.fd_inline then
      Inline
    else
      No_specifier in
  Debug.atom_global fd.fd_name id';
  Hashtbl.add decl_atom id'
    { a_storage = fd.fd_storage;
      a_alignment = None;
      a_sections = Sections.for_function env id' fd.fd_attrib;
      a_access = Sections.Access_default;
      a_inline = inline;
      a_loc = loc };
  (id',  AST.Gfun(Ctypes.Internal
          {fn_return = ret;
           fn_callconv = convertCallconv fd.fd_vararg false fd.fd_attrib;
           fn_params = params;
           fn_vars = vars;
           fn_body = body'}))

(** External function declaration *)

let re_builtin = Str.regexp "__builtin_"
let re_runtime = Str.regexp "__compcert_i64_"

let convertFundecl env (sto, id, ty, optinit) =
  let (args, res, cconv) =
    match convertTyp env ty with
    | Tfunction(args, res, cconv) -> (args, res, cconv)
    | _ -> assert false in
  let id' = intern_string id.name in
  let id'' = coqstring_of_camlstring id.name in
  let sg = signature_of_type args res cconv in
  let ef =
    if id.name = "malloc" then AST.EF_malloc else
    if id.name = "free" then AST.EF_free else
    if Str.string_match re_runtime id.name 0 then  AST.EF_runtime(id'', sg) else
    if Str.string_match re_builtin id.name 0
    && List.mem_assoc id.name builtins.Builtins.functions
    then AST.EF_builtin(id'', sg)
    else AST.EF_external(id'', sg) in
  (id',  AST.Gfun(Ctypes.External(ef, args, res, cconv)))

(** Initializers *)

let rec convertInit env init =
  match init with
  | C.Init_single e ->
      Initializers.Init_single (convertExpr env e)
  | C.Init_array il ->
      Initializers.Init_array (convertInitList env (List.rev il) Initializers.Init_nil)
  | C.Init_struct(_, flds) ->
      Initializers.Init_struct (convertInitList env (List.rev_map snd flds) Initializers.Init_nil)
  | C.Init_union(_, fld, i) ->
      Initializers.Init_union (intern_string fld.fld_name, convertInit env i)

and convertInitList env il accu =
  match il with
  | [] -> accu
  | i :: il' -> convertInitList env il' (Initializers.Init_cons(convertInit env i, accu))

let convertInitializer env ty i =
  match Initializers.transl_init
               !comp_env (convertTyp env ty) (convertInit env i)
  with
  | Errors.OK init -> init
  | Errors.Error msg ->
      error "initializer element is not a compile-time constant (%s)"
                     (string_of_errmsg msg); []

(** Global variable *)

let convertGlobvar loc env (sto, id, ty, optinit) =
  let id' = intern_string id.name in
  Debug.atom_global id id';
  let ty' = convertTyp env ty in
  let sz = Ctypes.sizeof !comp_env ty' in
  let al = Ctypes.alignof !comp_env ty' in
  let attr = Cutil.attributes_of_type env ty in
  let init' =
    match optinit with
    | None ->
        if sto = C.Storage_extern then [] else [AST.Init_space sz]
    | Some i ->
        convertInitializer env ty i in
  let (section, access) =
    Sections.for_variable env id' ty (optinit <> None) in
  if Z.gt sz (Z.of_uint64 0xFFFF_FFFFL) then
    error "'%s' is too big (%s bytes)"
                   id.name (Z.to_string sz);
  if sto <> C.Storage_extern && Cutil.incomplete_type env ty then
    error "'%s' has incomplete type" id.name;
  Hashtbl.add decl_atom id'
    { a_storage = sto;
      a_alignment = Some (Z.to_int al);
      a_sections = [section];
      a_access = access;
      a_inline = No_specifier;
      a_loc = loc };
  let volatile = List.mem C.AVolatile attr in
  let readonly = List.mem C.AConst attr && not volatile in
  (id',  AST.Gvar { AST.gvar_info = ty'; gvar_init = init';
              gvar_readonly = readonly; gvar_volatile = volatile})

(** Convert a list of global declarations.
  Result is a list of CompCert C global declarations (functions +
  variables). *)

let rec convertGlobdecls env res gl =
  match gl with
  | [] -> List.rev res
  | g :: gl' ->
      updateLoc g.gloc;
      match g.gdesc with
      | C.Gdecl((sto, id, ty, optinit) as d) ->
          (* Functions become external declarations.
             Other types become variable declarations. *)
          begin match Cutil.unroll env ty with
          | TFun(tres, targs, va, a) ->
              if targs = None then
                warning Diagnostics.Unnamed "'%s' is declared without a function prototype" id.name;
              convertGlobdecls env (convertFundecl env d :: res) gl'
          | _ ->
              convertGlobdecls env (convertGlobvar g.gloc env d :: res) gl'
          end
      | C.Gfundef fd ->
          convertGlobdecls env (convertFundef g.gloc env fd :: res) gl'
      | C.Gcompositedecl _ | C.Gcompositedef _ | C.Gtypedef _ | C.Genumdef _ ->
          (* Composites are treated in a separate pass,
             typedefs are unrolled, and enum tags are folded.
             So we just skip their declarations. *)
          convertGlobdecls env res gl'
      | C.Gpragma s ->
          if not (!process_pragma_hook s) then
            warning Diagnostics.Unknown_pragmas "unknown pragma ignored";
          convertGlobdecls env res gl'

(** Convert struct and union declarations.
    Result is a list of CompCert C composite declarations. *)

let rec convertCompositedefs env res gl =
  match gl with
  | [] -> List.rev res
  | g :: gl' ->
      updateLoc g.gloc;
      match g.gdesc with
      | C.Gcompositedef(su, id, a, m) ->
          convertCompositedefs env
             (convertCompositedef env su id a m :: res) gl'
      | _ ->
          convertCompositedefs env res gl'

(** Build environment of typedefs, structs, unions and enums *)

let rec translEnv env = function
  | [] -> env
  | g :: gl ->
      let env' =
        match g.gdesc with
        | C.Gcompositedecl(su, id, attr) ->
            Env.add_composite env id (Cutil.composite_info_decl su attr)
        | C.Gcompositedef(su, id, attr, fld) ->
            Env.add_composite env id (Cutil.composite_info_def env su attr fld)
        | C.Gtypedef(id, ty) ->
            Env.add_typedef env id ty
        | C.Genumdef(id, attr, members) ->
            Env.add_enum env id {Env.ei_members = members; ei_attr = attr}
        | _ ->
            env in
      translEnv env' gl

(** Eliminate multiple declarations of globals. *)

module IdentSet = Set.Make(struct type t = C.ident let compare = compare end)

let cleanupGlobals p =

  (* First pass: determine what is defined *)
  let strong = ref IdentSet.empty (* def functions or variables with inits *)
  and weak = ref IdentSet.empty (* variables without inits *)
  and extern = ref IdentSet.empty in (* extern decls *)
  let classify_def g =
        updateLoc g.gloc;
    match g.gdesc with
    | C.Gfundef fd ->
        if IdentSet.mem fd.fd_name !strong then
          error "multiple definitions of %s" fd.fd_name.name;
        strong := IdentSet.add fd.fd_name !strong
    | C.Gdecl(Storage_extern, id, ty, init) ->
        extern := IdentSet.add id !extern
    | C.Gdecl(sto, id, ty, Some i) ->
        if IdentSet.mem id !strong then
          error "multiple definitions of %s" id.name;
        strong := IdentSet.add id !strong
    | C.Gdecl(sto, id, ty, None) ->
        weak := IdentSet.add id !weak
    | _ -> () in
  List.iter classify_def p;

  (* Second pass: keep "best" definition for each identifier *)
  let rec clean defs accu = function
    | [] -> accu
    | g :: gl ->
        updateLoc g.gloc;
        match g.gdesc with
        | C.Gdecl(sto, id, ty, init) ->
            let better_def_exists =
              if sto = Storage_extern then
                IdentSet.mem id !strong || IdentSet.mem id !weak
              else if init = None then
                IdentSet.mem id !strong
              else
                false in
            if IdentSet.mem id defs || better_def_exists
            then clean defs accu gl
            else clean (IdentSet.add id defs) (g :: accu) gl
        | C.Gfundef fd ->
            clean (IdentSet.add fd.fd_name defs) (g :: accu) gl
        | _ ->
            clean defs (g :: accu) gl
  in clean IdentSet.empty [] (List.rev p)

(** Extract the list of public (non-static) names *)

let public_globals gl =
  List.fold_left
    (fun accu (id, g) -> if atom_is_static id then accu else id :: accu)
    [] gl

(** Convert a [C.program] into a [Csyntax.program] *)

let convertProgram p =
  Diagnostics.reset();
  stringNum := 0;
  Hashtbl.clear decl_atom;
  Hashtbl.clear stringTable;
  Hashtbl.clear wstringTable;
  let p = cleanupGlobals (Builtins.declarations() @ p) in
  try
    let env = translEnv Env.empty p in
    let typs = convertCompositedefs env [] p in
    match build_composite_env typs with
    | Errors.Error msg ->
      fatal_error "incorrect struct or union definition: %s"
                       (string_of_errmsg msg)
    | Errors.OK ce ->
        comp_env := ce;
        let gl1 = convertGlobdecls env [] p in
        let gl2 = globals_for_strings gl1 in
        comp_env := Maps.PTree.empty;
        let p' =
          { prog_defs = gl2;
            prog_public = public_globals gl2;
            prog_main = intern_string "main";
            prog_types = typs;
            prog_comp_env = ce } in
        Diagnostics.check_errors ();
        p'
  with Env.Error msg ->
    fatal_error "%s" (Env.error_message msg)
