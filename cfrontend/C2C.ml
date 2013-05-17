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

open Printf

open C
open Env
open Builtins

open Camlcoq
open AST
open Values
open Ctypes
open Cop
open Csyntax
open Initializers
open Floats

(** Record useful information about global variables and functions,
  and associate it with the corresponding atoms. *)

type atom_info =
  { a_storage: C.storage;              (* storage class *)
    a_alignment: int option;           (* alignment *)
    a_sections: Sections.section_name list; (* in which section to put it *)
      (* 1 section for data, 3 sections (code/lit/jumptbl) for functions *)
    a_small_data: bool;                (* data in a small data area? *)
    a_inline: bool;                    (* function declared inline? *)
    a_loc: location                    (* source location *)
}

let decl_atom : (AST.ident, atom_info) Hashtbl.t = Hashtbl.create 103

(** Hooks -- overriden in machine-dependent CPragmas module *)

let process_pragma_hook = ref (fun (s: string) -> false)

(** ** Error handling *)

let currentLocation = ref Cutil.no_loc

let updateLoc l = currentLocation := l

let numErrors = ref 0

let error msg =
  incr numErrors;
  eprintf "%aError: %s\n" Cutil.printloc !currentLocation msg

let unsupported msg =
  incr numErrors;
  eprintf "%aUnsupported feature: %s\n" Cutil.printloc !currentLocation msg

let warning msg =
  eprintf "%aWarning: %s\n" Cutil.printloc !currentLocation msg


(** ** The builtin environment *)

let builtins_generic = {
  typedefs = [
    (* keeps GCC-specific headers happy, harmless for others *)
    "__builtin_va_list", C.TPtr(C.TVoid [], [])
  ];
  functions = [
    (* Floating-point absolute value *)
    "__builtin_fabs",
      (TFloat(FDouble, []), [TFloat(FDouble, [])], false);
    (* Block copy *)
    "__builtin_memcpy_aligned",
         (TVoid [],
           [TPtr(TVoid [], []); 
            TPtr(TVoid [AConst], []); 
            TInt(Cutil.size_t_ikind, []);
            TInt(Cutil.size_t_ikind, [])],
          false);
    (* Annotations *)
    "__builtin_annot",
        (TVoid [],
          [TPtr(TInt(IChar, [AConst]), [])],
          true);
    "__builtin_annot_intval",
        (TInt(IInt, []),
          [TPtr(TInt(IChar, [AConst]), []); TInt(IInt, [])],
          false)
  ]
}

(* Add processor-dependent builtins *)

let builtins =
  { typedefs = builtins_generic.typedefs @ CBuiltins.builtins.typedefs;
    functions = builtins_generic.functions @ CBuiltins.builtins.functions }

(** ** Functions used to handle string literals *)

let stringNum = ref 0   (* number of next global for string literals *)
let stringTable = Hashtbl.create 47

let name_for_string_literal env s =
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
        a_small_data = false;
        a_inline = false;
        a_loc = Cutil.no_loc };
    Hashtbl.add stringTable s id;
    id

let typeStringLiteral s =
  Tarray(Tint(I8, Unsigned, noattr), Z.of_uint (String.length s + 1), noattr)

let global_for_string s id =
  let init = ref [] in
  let add_char c =
    init := AST.Init_int8(Z.of_uint(Char.code c)) :: !init in
  add_char '\000';
  for i = String.length s - 1 downto 0 do add_char s.[i] done;
  (id, Gvar {gvar_info = typeStringLiteral s; gvar_init = !init;
             gvar_readonly = true; gvar_volatile = false})

let globals_for_strings globs =
  Hashtbl.fold
    (fun s id l -> global_for_string s id :: l)
    stringTable globs

(** ** Declaration of special external functions *)

let special_externals_table : (string, fundef) Hashtbl.t = Hashtbl.create 47

let register_special_external name ef targs tres =
  if not (Hashtbl.mem special_externals_table name) then
    Hashtbl.add special_externals_table name (External(ef, targs, tres))

let declare_special_externals k =
  Hashtbl.fold
    (fun name fd k -> (intern_string name, Gfun fd) :: k)
    special_externals_table k

(** ** Handling of stubs for variadic functions *)

let register_stub_function name tres targs =
  let rec letters_of_type = function
    | Tnil -> []
    | Tcons(Tfloat _, tl) -> "f" :: letters_of_type tl
    | Tcons(Tlong _, tl) -> "l" :: letters_of_type tl
    | Tcons(_, tl) -> "i" :: letters_of_type tl in
  let rec types_of_types = function
    | Tnil -> Tnil
    | Tcons(Tfloat _, tl) -> Tcons(Tfloat(F64, noattr), types_of_types tl)
    | Tcons(Tlong _, tl) -> Tcons(Tlong(Signed, noattr), types_of_types tl)
    | Tcons(_, tl) -> Tcons(Tpointer(Tvoid, noattr), types_of_types tl) in
  let stub_name =
    name ^ "$" ^ String.concat "" (letters_of_type targs) in
  let targs = types_of_types targs in
  let ef = EF_external(intern_string stub_name, signature_of_type targs tres) in
  register_special_external stub_name ef targs tres;
  (stub_name, Tfunction (targs, tres))

(** ** Handling of inlined memcpy functions *)

let make_builtin_memcpy args =
  match args with
  | Econs(dst, Econs(src, Econs(sz, Econs(al, Enil)))) ->
      let sz1 =
        match Initializers.constval sz with
        | Errors.OK(Vint n) -> n
        | _ -> error "ill-formed __builtin_memcpy_aligned (3rd argument must be 
a constant)"; Integers.Int.zero in
      let al1 =
        match Initializers.constval al with
        | Errors.OK(Vint n) -> n
        | _ -> error "ill-formed __builtin_memcpy_aligned (4th argument must be 
a constant)"; Integers.Int.one in
      (* to check: sz1 > 0, al1 divides sz1, al1 = 1|2|4|8 *)
      Ebuiltin(EF_memcpy(sz1, al1),
               Tcons(typeof dst, Tcons(typeof src, Tnil)),
               Econs(dst, Econs(src, Enil)), Tvoid)
  | _ ->
    assert false

(** ** Translation functions *)

(** Constants *)

let convertInt n = coqint_of_camlint(Int64.to_int32 n)

(** Attributes *)

let convertAttr a = List.mem AVolatile a

let mergeAttr a1 a2 = a1 || a2

let mergeTypAttr ty a2 =
  match ty with
  | Tvoid -> ty
  | Tint(sz, sg, a1) -> Tint(sz, sg, mergeAttr a1 a2)
  | Tfloat(sz, a1) -> Tfloat(sz, mergeAttr a1 a2)
  | Tlong(sg, a1) -> Tlong(sg, mergeAttr a1 a2)
  | Tpointer(ty', a1) -> Tpointer(ty', mergeAttr a1 a2)
  | Tarray(ty', sz, a1) -> Tarray(ty', sz, mergeAttr a1 a2)
  | Tfunction(targs, tres) -> ty
  | Tstruct(id, fld, a1) -> Tstruct(id, fld, mergeAttr a1 a2)
  | Tunion(id, fld, a1) -> Tunion(id, fld, mergeAttr a1 a2)
  | Tcomp_ptr(id, a1) -> Tcomp_ptr(id, mergeAttr a1 a2)

(** Types *)

let convertIkind = function
  | C.IBool -> (Unsigned, IBool)
  | C.IChar -> ((if (!Machine.config).Machine.char_signed
                 then Signed else Unsigned), I8)
  | C.ISChar -> (Signed, I8)
  | C.IUChar -> (Unsigned, I8)
  | C.IInt -> (Signed, I32)
  | C.IUInt -> (Unsigned, I32)
  | C.IShort -> (Signed, I16)
  | C.IUShort -> (Unsigned, I16)
  | C.ILong -> (Signed, I32)
  | C.IULong -> (Unsigned, I32)
  (* Special-cased in convertTyp below *)
  | C.ILongLong | C.IULongLong -> assert false

let convertFkind = function
  | C.FFloat -> F32
  | C.FDouble -> F64
  | C.FLongDouble ->
      if not !Clflags.option_flongdouble then unsupported "'long double' type"; 
      F64

(** A cache for structs and unions already converted *)

let compositeCache : (C.ident, coq_type) Hashtbl.t = Hashtbl.create 77

let convertTyp env t =

  let rec convertTyp seen t =
    match Cutil.unroll env t with
    | C.TVoid a -> Tvoid
    | C.TInt(C.ILongLong, a) ->
        Tlong(Signed, convertAttr a)
    | C.TInt(C.IULongLong, a) ->
        Tlong(Unsigned, convertAttr a)
    | C.TInt(ik, a) ->
        let (sg, sz) = convertIkind ik in Tint(sz, sg, convertAttr a)
    | C.TFloat(fk, a) ->
        Tfloat(convertFkind fk, convertAttr a)
    | C.TPtr(ty, a) ->
        begin match Cutil.unroll env ty with
        | C.TStruct(id, _) when List.mem id seen ->
            Tcomp_ptr(intern_string ("struct " ^ id.name), convertAttr a)
        | C.TUnion(id, _) when List.mem id seen ->
            Tcomp_ptr(intern_string ("union " ^ id.name), convertAttr a)
        | _ ->
            Tpointer(convertTyp seen ty, convertAttr a)
        end
    | C.TArray(ty, None, a) ->
        (* Cparser verified that the type ty[] occurs only in
           contexts that are safe for Clight, so just treat as ty[0]. *)
        (* warning "array type of unspecified size"; *)
        Tarray(convertTyp seen ty, coqint_of_camlint 0l, convertAttr a)
    | C.TArray(ty, Some sz, a) ->
        Tarray(convertTyp seen ty, convertInt sz, convertAttr a)
    | C.TFun(tres, targs, va, a) ->
        if va then unsupported "variadic function type";
        if Cutil.is_composite_type env tres then
          unsupported "return type is a struct or union";
        Tfunction(begin match targs with
                  | None -> (*warning "un-prototyped function type";*) Tnil
                  | Some tl -> convertParams seen tl
                  end,
                  convertTyp seen tres)
    | C.TNamed _ ->
        assert false
    | C.TStruct(id, a) ->
        let a' = convertAttr a in
        begin try
          mergeTypAttr (Hashtbl.find compositeCache id) a'
        with Not_found ->
          let flds =
            try
              convertFields (id :: seen) (Env.find_struct env id)
            with Env.Error e ->
              error (Env.error_message e); Fnil in
          Tstruct(intern_string("struct " ^ id.name), flds, a')
        end
    | C.TUnion(id, a) ->
        let a' = convertAttr a in
        begin try
          mergeTypAttr (Hashtbl.find compositeCache id) a'
        with Not_found ->
          let flds =
            try
              convertFields (id :: seen) (Env.find_union env id)
            with Env.Error e ->
              error (Env.error_message e); Fnil in
          Tunion(intern_string("union " ^ id.name), flds, a')
        end
    | C.TEnum(id, a) ->
        let (sg, sz) = convertIkind Cutil.enum_ikind in
        Tint(sz, sg, convertAttr a)

  and convertParams seen = function
    | [] -> Tnil
    | (id, ty) :: rem ->
        Tcons(convertTyp seen ty, convertParams seen rem)

  and convertFields seen ci =
    convertFieldList seen ci.Env.ci_members

  and convertFieldList seen = function
    | [] -> Fnil
    | f :: fl ->
        Fcons(intern_string f.fld_name, convertTyp seen f.fld_typ,
              convertFieldList seen fl)

  in convertTyp [] t

let rec convertTypList env = function
  | [] -> Tnil
  | t1 :: tl -> Tcons(convertTyp env t1, convertTypList env tl)

let cacheCompositeDef env su id attr flds =
  (* we currently ignore attributes on structs and unions *)
  let ty =
    match su with C.Struct -> C.TStruct(id, []) | C.Union -> C.TUnion(id, []) in
  Hashtbl.add compositeCache id (convertTyp env ty)

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

let supported_return_type env ty =
  match Cutil.unroll env ty with
  | C.TStruct _  | C.TUnion _ -> false
  | _ -> true

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

let convertFloat f kind =
  let mant = z_of_str f.C.hex (f.C.intPart ^ f.C.fracPart) 0 in
  match mant with
    | Z.Z0 -> Float.zero
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
	  Float.build_from_parsed32 base mant exp
	| FDouble | FLongDouble ->
	  Float.build_from_parsed64 base mant exp
      end

    | Z.Zneg _ -> assert false

(** Expressions *)

let ezero = Eval(Vint(coqint_of_camlint 0l), type_int32s)

let rec convertExpr env e =
  let ty = convertTyp env e.etyp in
  match e.edesc with
  | C.EVar _
  | C.EUnop((C.Oderef|C.Odot _|C.Oarrow _), _)
  | C.EBinop(C.Oindex, _, _, _) ->
      let l = convertLvalue env e in
      Evalof(l, ty)

  | C.EConst(C.CInt(i, (ILongLong|IULongLong), _)) ->
      Eval(Vlong(coqint_of_camlint64 i), ty)
  | C.EConst(C.CInt(i, k, _)) ->
      Eval(Vint(convertInt i), ty)
  | C.EConst(C.CFloat(f, k)) ->
      if k = C.FLongDouble && not !Clflags.option_flongdouble then
        unsupported "'long double' floating-point literal";
      Eval(Vfloat(convertFloat f k), ty)
  | C.EConst(C.CStr s) ->
      let ty = typeStringLiteral s in
      Evalof(Evar(name_for_string_literal env s, ty), ty)
  | C.EConst(C.CWStr s) ->
      unsupported "wide string literal"; ezero
  | C.EConst(C.CEnum(id, i)) ->
      Eval(Vint(convertInt i), ty)
  | C.ESizeof ty1 ->
      Esizeof(convertTyp env ty1, ty)
  | C.EAlignof ty1 ->
      Ealignof(convertTyp env ty1, ty)

  | C.EUnop(C.Ominus, e1) ->
      Eunop(Oneg, convertExpr env e1, ty)
  | C.EUnop(C.Oplus, e1) ->
      convertExpr env e1
  | C.EUnop(C.Olognot, e1) ->
      Eunop(Onotbool, convertExpr env e1, ty)
  | C.EUnop(C.Onot, e1) ->
      Eunop(Onotint, convertExpr env e1, ty)
  | C.EUnop(C.Oaddrof, e1) ->
      Eaddrof(convertLvalue env e1, ty)
  | C.EUnop(C.Opreincr, e1) ->
      coq_Epreincr Incr (convertLvalue env e1) ty
  | C.EUnop(C.Opredecr, e1) ->
      coq_Epreincr Decr (convertLvalue env e1) ty
  | C.EUnop(C.Opostincr, e1) ->
      Epostincr(Incr, convertLvalue env e1, ty)
  | C.EUnop(C.Opostdecr, e1) ->
      Epostincr(Decr, convertLvalue env e1, ty)

  | C.EBinop((C.Oadd|C.Osub|C.Omul|C.Odiv|C.Omod|C.Oand|C.Oor|C.Oxor|
              C.Oshl|C.Oshr|C.Oeq|C.One|C.Olt|C.Ogt|C.Ole|C.Oge) as op,
             e1, e2, tyres) ->
      let op' =
        match op with
        | C.Oadd -> Oadd
        | C.Osub -> Osub
        | C.Omul -> Omul
        | C.Odiv -> Odiv
        | C.Omod -> Omod
        | C.Oand -> Oand
        | C.Oor  -> Oor
        | C.Oxor -> Oxor
        | C.Oshl -> Oshl
        | C.Oshr -> Oshr
        | C.Oeq  -> Oeq
        | C.One  -> One
        | C.Olt  -> Olt
        | C.Ogt  -> Ogt
        | C.Ole  -> Ole
        | C.Oge  -> Oge
        | _ -> assert false in
      Ebinop(op', convertExpr env e1, convertExpr env e2, ty)
  | C.EBinop(C.Oassign, e1, e2, _) ->
      let e1' = convertLvalue env e1 in
      let e2' = convertExpr env e2 in
      Eassign(e1', e2', ty)
  | C.EBinop((C.Oadd_assign|C.Osub_assign|C.Omul_assign|C.Odiv_assign|
              C.Omod_assign|C.Oand_assign|C.Oor_assign|C.Oxor_assign|
              C.Oshl_assign|C.Oshr_assign) as op,
             e1, e2, tyres) ->
      let tyres = convertTyp env tyres in
      let op' =
        match op with
        | C.Oadd_assign -> Oadd
        | C.Osub_assign -> Osub
        | C.Omul_assign -> Omul
        | C.Odiv_assign -> Odiv
        | C.Omod_assign -> Omod
        | C.Oand_assign -> Oand
        | C.Oor_assign  -> Oor
        | C.Oxor_assign -> Oxor
        | C.Oshl_assign -> Oshl
        | C.Oshr_assign -> Oshr
        | _ -> assert false in
      let e1' = convertLvalue env e1 in
      let e2' = convertExpr env e2 in
      Eassignop(op', e1', e2', tyres, ty)
  | C.EBinop(C.Ocomma, e1, e2, _) ->
      Ecomma(convertExpr env e1, convertExpr env e2, ty)
  | C.EBinop(C.Ologand, e1, e2, _) ->
      Eseqand(convertExpr env e1, convertExpr env e2, ty)
  | C.EBinop(C.Ologor, e1, e2, _) ->
      Eseqor(convertExpr env e1, convertExpr env e2, ty)

  | C.EConditional(e1, e2, e3) ->
      Econdition(convertExpr env e1, convertExpr env e2, convertExpr env e3, ty)
  | C.ECast(ty1, e1) ->
      Ecast(convertExpr env e1, convertTyp env ty1)

  | C.ECall({edesc = C.EVar {name = "__builtin_annot"}}, args) ->
      begin match args with
      | {edesc = C.EConst(CStr txt)} :: args1 ->
          let targs1 = convertTypList env (List.map (fun e -> e.etyp) args1) in
          Ebuiltin(
            EF_annot(intern_string txt,
                     List.map (fun t -> AA_arg t) (typlist_of_typelist targs1)),
            targs1, convertExprList env args1, ty)
      | _ ->
          error "ill-formed __builtin_annot (first argument must be string literal)";
          ezero
      end          
 
  | C.ECall({edesc = C.EVar {name = "__builtin_annot_intval"}}, args) ->
      begin match args with
      | [ {edesc = C.EConst(CStr txt)}; arg ] ->
          let targ = convertTyp env arg.etyp in
          Ebuiltin(EF_annot_val(intern_string txt, typ_of_type targ),
                   Tcons(targ, Tnil), convertExprList env [arg], ty)
      | _ ->
          error "ill-formed __builtin_annot_intval (first argument must be string literal)";
          ezero
      end          

 | C.ECall({edesc = C.EVar {name = "__builtin_memcpy_aligned"}}, args) ->
      make_builtin_memcpy (convertExprList env args)

  | C.ECall(fn, args) ->
      if not (supported_return_type env e.etyp) then
        unsupported ("function returning a result of type " ^ string_of_type e.etyp);
      match projFunType env fn.etyp with
      | None ->
          error "wrong type for function part of a call"; ezero
      | Some(tres, targs, false) ->
          (* Non-variadic function *)
          if targs = None then
            unsupported "call to non-prototyped function";
          Ecall(convertExpr env fn, convertExprList env args, ty)
      | Some(tres, targs, true) ->
          (* Variadic function: generate a call to a stub function with
             the appropriate number and types of arguments.  Works only if
             the function expression e is a global variable. *)
          let fun_name =
            match fn with
            | {edesc = C.EVar id} when !Clflags.option_fvararg_calls ->
                (*warning "emulating call to variadic function"; *)
                id.name
            | _ ->
                unsupported "call to variadic function";
                "<error>" in
          let targs = convertTypList env (List.map (fun e -> e.etyp) args) in
          let tres = convertTyp env tres in
          let (stub_fun_name, stub_fun_typ) =
            register_stub_function fun_name tres targs in
          Ecall(Evalof(Evar(intern_string stub_fun_name, stub_fun_typ),
                       stub_fun_typ),
                convertExprList env args, ty)

and convertLvalue env e =
  let ty = convertTyp env e.etyp in
  match e.edesc with
  | C.EVar id ->
      Evar(intern_string id.name, ty)
  | C.EUnop(C.Oderef, e1) ->
      Ederef(convertExpr env e1, ty)
  | C.EUnop(C.Odot id, e1) ->
      Efield(convertExpr env e1, intern_string id, ty)
  | C.EUnop(C.Oarrow id, e1) ->
      let e1' = convertExpr env e1 in
      let ty1 =
        match typeof e1' with
        | Tpointer(t, _) | Tarray(t, _, _) -> t
        | _ -> error ("wrong type for ->" ^ id ^ " access"); Tvoid in
      Efield(Evalof(Ederef(e1', ty1), ty1), intern_string id, ty)
  | C.EBinop(C.Oindex, e1, e2, _) ->
      coq_Eindex (convertExpr env e1) (convertExpr env e2) ty
  | _ ->
      error "illegal l-value"; ezero

and convertExprList env el =
  match el with
  | [] -> Enil
  | e1 :: el' -> Econs(convertExpr env e1, convertExprList env el')

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
  | {sdesc = C.Slabeled(C.Scase e, s1)} ->
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

(** Annotations for line numbers *)

let add_lineno prev_loc this_loc s =
  if !Clflags.option_g && prev_loc <> this_loc && this_loc <> Cutil.no_loc
  then begin
    let txt = sprintf "#line:%s:%d" (fst this_loc) (snd this_loc) in
     Ssequence(Sdo(Ebuiltin(EF_annot(intern_string txt, []),
                            Tnil, Enil, Tvoid)),
               s)
  end else
    s

(** Statements *)

let rec convertStmt ploc env s =
  updateLoc s.sloc;
  match s.sdesc with
  | C.Sskip ->
      Sskip
  | C.Sdo e ->
      add_lineno ploc s.sloc (Sdo(convertExpr env e))
  | C.Sseq(s1, s2) ->
      Ssequence(convertStmt ploc env s1, convertStmt s1.sloc env s2)
  | C.Sif(e, s1, s2) ->
      let te = convertExpr env e in
      add_lineno ploc s.sloc 
        (Sifthenelse(te, convertStmt s.sloc env s1, convertStmt s.sloc env s2))
  | C.Swhile(e, s1) ->
      let te = convertExpr env e in
      add_lineno ploc s.sloc (Swhile(te, convertStmt s.sloc env s1))
  | C.Sdowhile(s1, e) ->
      let te = convertExpr env e in
      add_lineno ploc s.sloc (Sdowhile(te, convertStmt s.sloc env s1))
  | C.Sfor(s1, e, s2, s3) ->
      let te = convertExpr env e in
      add_lineno ploc s.sloc
        (Sfor(convertStmt s.sloc env s1, te,
              convertStmt s.sloc env s2, convertStmt s.sloc env s3))
  | C.Sbreak ->
      Sbreak
  | C.Scontinue ->
      Scontinue
  | C.Sswitch(e, s1) ->
      let (init, cases) = groupSwitch (flattenSwitch s1) in
      if cases = [] then
        unsupported "ill-formed 'switch' statement";
      if init.sdesc <> C.Sskip then
        warning "ignored code at beginning of 'switch'";
      let te = convertExpr env e in
      add_lineno ploc s.sloc (Sswitch(te, convertSwitch s.sloc env cases))
  | C.Slabeled(C.Slabel lbl, s1) ->
      add_lineno ploc s.sloc
        (Slabel(intern_string lbl, convertStmt s.sloc env s1))
  | C.Slabeled(C.Scase _, _) ->
      unsupported "'case' outside of 'switch'"; Sskip
  | C.Slabeled(C.Sdefault, _) ->
      unsupported "'default' outside of 'switch'"; Sskip
  | C.Sgoto lbl ->
      add_lineno ploc s.sloc (Sgoto(intern_string lbl))
  | C.Sreturn None ->
      add_lineno ploc s.sloc (Sreturn None)
  | C.Sreturn(Some e) ->
      add_lineno ploc s.sloc (Sreturn(Some(convertExpr env e)))
  | C.Sblock _ ->
      unsupported "nested blocks"; Sskip
  | C.Sdecl _ ->
      unsupported "inner declarations"; Sskip
  | C.Sasm txt ->
      if not !Clflags.option_finline_asm then
        unsupported "inline 'asm' statement (consider adding option -finline-asm)";
      add_lineno ploc s.sloc
        (Sdo (Ebuiltin (EF_inline_asm (intern_string txt), Tnil, Enil, Tvoid)))

and convertSwitch ploc env = function
  | [] ->
      LSdefault Sskip
  | [Default, s] ->
      LSdefault (convertStmt ploc env s)
  | (Default, s) :: _ ->
      updateLoc s.sloc;
      unsupported "'default' case must occur last";
      LSdefault Sskip
  | (Case e, s) :: rem ->
      updateLoc s.sloc;
      let v =
        match Ceval.integer_expr env e with
        | None -> unsupported "'case' label is not a compile-time integer"; 0L
        | Some v -> v in
      LScase(convertInt v,
             convertStmt ploc env s,
             convertSwitch s.sloc env rem)

(** Function definitions *)

let convertFundef loc env fd =
  if Cutil.is_composite_type env fd.fd_ret then
    unsupported "function returning a struct or union";
  let ret =
    convertTyp env fd.fd_ret in
  let params =
    List.map
      (fun (id, ty) ->
        (intern_string id.name, convertTyp env ty))
      fd.fd_params in
  let vars =
    List.map
      (fun (sto, id, ty, init) ->
        if sto = Storage_extern || sto = Storage_static then
          unsupported "'static' or 'extern' local variable";
        if init <> None then
          unsupported "initialized local variable";
        (intern_string id.name, convertTyp env ty))
      fd.fd_locals in
  let body' = convertStmt loc env fd.fd_body in
  let id' = intern_string fd.fd_name.name in
  Hashtbl.add decl_atom id'
    { a_storage = fd.fd_storage;
      a_alignment = None;
      a_sections = Sections.for_function env id' fd.fd_ret;
      a_small_data = false;
      a_inline = fd.fd_inline;
      a_loc = loc };
  (id', Gfun(Internal {fn_return = ret; fn_params = params;
                       fn_vars = vars; fn_body = body'}))

(** External function declaration *)

let convertFundecl env (sto, id, ty, optinit) =
  let (args, res) =
    match convertTyp env ty with
    | Tfunction(args, res) -> (args, res)
    | _ -> assert false in
  let id' = intern_string id.name in
  let sg = signature_of_type args res in
  let ef =
    if id.name = "malloc" then EF_malloc else
    if id.name = "free" then EF_free else
    if List.mem_assoc id.name builtins.functions
    then EF_builtin(id', sg)
    else EF_external(id', sg) in
  (id', Gfun(External(ef, args, res)))

(** Initializers *)

let string_of_errmsg msg =
  let string_of_err = function
  | Errors.MSG s -> camlstring_of_coqstring s
  | Errors.CTX i -> extern_atom i
  | Errors.POS i -> Z.to_string (Z.Zpos i)
  in String.concat "" (List.map string_of_err msg)

let rec convertInit env init =
  match init with
  | C.Init_single e ->
      Init_single (convertExpr env e)
  | C.Init_array il ->
      Init_compound (convertInitList env il)
  | C.Init_struct(_, flds) ->
      Init_compound (convertInitList env (List.map snd flds))
  | C.Init_union(_, fld, i) ->
      Init_compound (Init_cons(convertInit env i, Init_nil))

and convertInitList env il =
  match il with
  | [] -> Init_nil
  | i :: il' -> Init_cons(convertInit env i, convertInitList env il')

let convertInitializer env ty i =
  match Initializers.transl_init (convertTyp env ty) (convertInit env i)
  with
  | Errors.OK init -> init
  | Errors.Error msg ->
      error (sprintf "Initializer is not a compile-time constant (%s)"
                     (string_of_errmsg msg)); []

(** Global variable *)

let convertGlobvar loc env (sto, id, ty, optinit) =
  let id' = intern_string id.name in
  let ty' = convertTyp env ty in 
  let sz = Ctypes.sizeof ty' in
  let attr = Cutil.attributes_of_type env ty in
  let init' =
    match optinit with
    | None ->
        if sto = C.Storage_extern then [] else [Init_space sz]
    | Some i ->
        convertInitializer env ty i in
  let align =
    match Cutil.find_custom_attributes ["aligned"; "__aligned__"] attr with
    | [[C.AInt n]] -> Some(Int64.to_int n)
    | _            -> Cutil.alignof env ty in
  let (section, near_access) =
    Sections.for_variable env id' ty (optinit <> None) in
  if Z.gt sz (Z.of_uint64 0xFFFF_FFFFL) then
    error (sprintf "Variable %s is too big (%s bytes)"
                   id.name (Z.to_string sz));
  Hashtbl.add decl_atom id'
    { a_storage = sto;
      a_alignment = align;
      a_sections = [section];
      a_small_data = near_access;
      a_inline = false;
      a_loc = loc };
  let volatile = List.mem C.AVolatile attr in
  let readonly = List.mem C.AConst attr && not volatile in
  (id', Gvar {gvar_info = ty'; gvar_init = init';
              gvar_readonly = readonly; gvar_volatile = volatile})

(** Sanity checks on composite declarations. *)

let checkComposite env si id attr flds =
  let checkField f =
    if f.fld_bitfield <> None then
      unsupported "bit field in struct or union";
    if Cutil.find_custom_attributes ["aligned"; "__aligned__"] 
          (Cutil.attributes_of_type env f.fld_typ) <> [] then
      warning ("ignoring 'aligned' attribute on field " ^ f.fld_name)
  in List.iter checkField flds

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
          (* Prototyped functions become external declarations.
             Variadic functions are skipped.
             Other types become variable declarations. *)
          begin match Cutil.unroll env ty with
          | TFun(_, Some _, false, _) ->
              convertGlobdecls env (convertFundecl env d :: res) gl'
          | TFun(_, None, false, _) ->
              unsupported ("'" ^ id.name ^ "' is declared without a function prototype");
              convertGlobdecls env res gl'
          | TFun(_, _, true, _) ->
              convertGlobdecls env res gl'
          | _ ->
              convertGlobdecls env (convertGlobvar g.gloc env d :: res) gl'
          end
      | C.Gfundef fd ->
          convertGlobdecls env (convertFundef g.gloc env fd :: res) gl'
      | C.Gcompositedecl _ | C.Gtypedef _ | C.Genumdef _ ->
          (* typedefs are unrolled, structs are expanded inline, and
             enum tags are folded.  So we just skip their declarations. *)
          convertGlobdecls env res gl'
      | C.Gcompositedef(su, id, attr, flds) ->
          (* sanity checks on fields *)
          checkComposite env su id attr flds;
          (* convert it to a CompCert C type and cache this type *)
          cacheCompositeDef env su id attr flds;
          convertGlobdecls env res gl'
      | C.Gpragma s ->
          if not (!process_pragma_hook s) then
            warning ("'#pragma " ^ s ^ "' directive ignored");
          convertGlobdecls env res gl'

(** Build environment of typedefs, structs, unions and enums *)

let rec translEnv env = function
  | [] -> env
  | g :: gl ->
      let env' =
        match g.gdesc with
        | C.Gcompositedecl(su, id, attr) ->
            Env.add_composite env id (Cutil.composite_info_decl env su attr)
        | C.Gcompositedef(su, id, attr, fld) ->
            Env.add_composite env id (Cutil.composite_info_def env su attr fld)
        | C.Gtypedef(id, ty) ->
            Env.add_typedef env id ty
        | C.Genumdef(id, attr, members) ->
            Env.add_enum env id {ei_members = members; ei_attr = attr}
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
          error ("multiple definitions of " ^ fd.fd_name.name);
        strong := IdentSet.add fd.fd_name !strong
    | C.Gdecl(Storage_extern, id, ty, init) ->
        extern := IdentSet.add id !extern
    | C.Gdecl(sto, id, ty, Some i) ->
        if IdentSet.mem id !strong then
          error ("multiple definitions of " ^ id.name);
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

(** Convert a [C.program] into a [Csyntax.program] *)

let convertProgram p =
  numErrors := 0;
  stringNum := 0;
  Hashtbl.clear decl_atom;
  Hashtbl.clear stringTable;
  Hashtbl.clear compositeCache;
  Hashtbl.clear special_externals_table;
  let p = Builtins.declarations() @ p in
  try
    let gl1 = convertGlobdecls (translEnv Env.empty p) [] (cleanupGlobals p) in
    let gl2 = declare_special_externals gl1 in
    let gl3 = globals_for_strings gl2 in
    if !numErrors > 0
    then None
    else Some { AST.prog_defs = gl3;
                AST.prog_main = intern_string "main" }
  with Env.Error msg ->
    error (Env.error_message msg); None

(** ** Extracting information about global variables from their atom *)

let atom_is_static a =
  try
    let i = Hashtbl.find decl_atom a in
    i.a_storage = C.Storage_static || i.a_inline
    (* inline functions can remain in generated code, but at least
       let's not make them global *)
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
    (Hashtbl.find decl_atom a).a_small_data
  with Not_found ->
    false

let atom_is_inline a =
  try
    (Hashtbl.find decl_atom a).a_inline
  with Not_found ->
    false

let atom_location a =
  try
    (Hashtbl.find decl_atom a).a_loc
  with Not_found ->
    Cutil.no_loc
