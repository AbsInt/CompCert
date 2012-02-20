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

module CompcertErrors = Errors (* avoid shadowing by Cparser.Errors *)

open Cparser
open Cparser.C
open Cparser.Env
open Cparser.Builtins

open Camlcoq
open AST
open Values
open Csyntax
open Initializers

(** Record the declarations of global variables and associate them
    with the corresponding atom. *)

type atom_info =
  { a_storage: C.storage;
    a_env: Env.t;
    a_type: C.typ;
    a_fundef: C.fundef option }

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
    let sz = Int64.of_int (String.length s + 1) in
    Hashtbl.add decl_atom id
      { a_storage = C.Storage_static;
        a_env = env;
        a_type = C.TArray(C.TInt(C.IChar,[C.AConst]), Some sz, []);
        a_fundef = None };
    Sections.define_stringlit id;
    Hashtbl.add stringTable s id;
    id

let typeStringLiteral s =
  Tarray(Tint(I8, Unsigned, noattr),
         z_of_camlint(Int32.of_int(String.length s + 1)),
         noattr)

let global_for_string s id =
  let init = ref [] in
  let add_char c =
    init :=
       AST.Init_int8(coqint_of_camlint(Int32.of_int(Char.code c)))
       :: !init in
  add_char '\000';
  for i = String.length s - 1 downto 0 do add_char s.[i] done;
  (id, {gvar_info = typeStringLiteral s; gvar_init = !init;
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
    (fun name fd k -> (intern_string name, fd) :: k)
    special_externals_table k

(** ** Handling of stubs for variadic functions *)

let register_stub_function name tres targs =
  let rec letters_of_type = function
    | Tnil -> []
    | Tcons(Tfloat _, tl) -> "f" :: letters_of_type tl
    | Tcons(_, tl) -> "i" :: letters_of_type tl in
  let rec types_of_types = function
    | Tnil -> Tnil
    | Tcons(Tfloat _, tl) -> Tcons(Tfloat(F64, noattr), types_of_types tl)
    | Tcons(_, tl) -> Tcons(Tpointer(Tvoid, noattr), types_of_types tl) in
  let stub_name =
    name ^ "$" ^ String.concat "" (letters_of_type targs) in
  let targs = types_of_types targs in
  let ef = EF_external(intern_string stub_name, signature_of_type targs tres) in
  register_special_external stub_name ef targs tres;
  (stub_name, Tfunction (targs, tres))

(** ** Handling of annotations *)

let annot_function_next = ref 0

let register_annotation_stmt txt targs =
  let tres = Tvoid in
  incr annot_function_next;
  let fun_name =
    Printf.sprintf "__builtin_annot_%d" !annot_function_next
  and ef =
    EF_annot (intern_string txt, typlist_of_typelist targs) in
  register_special_external fun_name ef targs tres;
  Evalof(Evar(intern_string fun_name, Tfunction(targs, tres)), 
         Tfunction(targs, tres))

let register_annotation_val txt targ =
  let targs = Tcons(targ, Tnil)
  and tres = targ in
  incr annot_function_next;
  let fun_name =
    Printf.sprintf "__builtin_annot_val_%d" !annot_function_next
  and ef =
    EF_annot_val (intern_string txt, typ_of_type targ) in
  register_special_external fun_name ef targs tres;
  Evalof(Evar(intern_string fun_name, Tfunction(targs, tres)),
         Tfunction(targs, tres))

(** ** Translation functions *)

(** Constants *)

let convertInt n = coqint_of_camlint(Int64.to_int32 n)

(** Attributes *)

let convertAttr a = List.mem AVolatile a

(** Types *)

let convertIkind = function
  | C.IBool -> (Unsigned, IBool)
  | C.IChar -> ((if (!Cparser.Machine.config).Cparser.Machine.char_signed
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
  | C.ILongLong -> unsupported "'long long' type"; (Signed, I32)
  | C.IULongLong -> unsupported "'unsigned long long' type"; (Unsigned, I32)

let convertFkind = function
  | C.FFloat -> F32
  | C.FDouble -> F64
  | C.FLongDouble ->
      if not !Clflags.option_flongdouble then unsupported "'long double' type"; 
      F64

let int64_struct a =
  let ty = Tint(I32,Unsigned,noattr) in
  Tstruct(intern_string "struct __int64",
    (if Memdataaux.big_endian
     then Fcons(intern_string "hi", ty, Fcons(intern_string "lo", ty, Fnil))
     else Fcons(intern_string "lo", ty, Fcons(intern_string "hi", ty, Fnil))),
    a)

let convertTyp env t =

  let rec convertTyp seen t =
    match Cutil.unroll env t with
    | C.TVoid a -> Tvoid
    | C.TInt((C.ILongLong|C.IULongLong), a) when !Clflags.option_flonglong ->
        int64_struct (convertAttr a)
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
                  | None -> warning "un-prototyped function type"; Tnil
                  | Some tl -> convertParams seen tl
                  end,
                  convertTyp seen tres)
    | C.TNamed _ ->
        assert false
    | C.TStruct(id, a) ->
        let flds =
          try
            convertFields (id :: seen) (Env.find_struct env id)
          with Env.Error e ->
            error (Env.error_message e); Fnil in
        Tstruct(intern_string("struct " ^ id.name), flds, convertAttr a)
    | C.TUnion(id, a) ->
        let flds =
          try
            convertFields (id :: seen) (Env.find_union env id)
          with Env.Error e ->
            error (Env.error_message e); Fnil in
        Tunion(intern_string("union " ^ id.name), flds, convertAttr a)

  and convertParams seen = function
    | [] -> Tnil
    | (id, ty) :: rem ->
        Tcons(convertTyp seen ty, convertParams seen rem)

  and convertFields seen ci =
    convertFieldList seen ci.Env.ci_members

  and convertFieldList seen = function
    | [] -> Fnil
    | f :: fl ->
        if f.fld_bitfield <> None then
          unsupported "bit field in struct or union";
        Fcons(intern_string f.fld_name, convertTyp seen f.fld_typ,
              convertFieldList seen fl)

  in convertTyp [] t

let rec convertTypList env = function
  | [] -> Tnil
  | t1 :: tl -> Tcons(convertTyp env t1, convertTypList env tl)

let rec projFunType env ty =
  match Cutil.unroll env ty with
  | TFun(res, args, vararg, attr) -> Some(res, vararg)
  | TPtr(ty', attr) -> projFunType env ty'
  | _ -> None

let string_of_type ty =
  let b = Buffer.create 20 in
  let fb = Format.formatter_of_buffer b in
  Cprint.typ fb ty;
  Format.pp_print_flush fb ();
  Buffer.contents b

let first_class_value env ty =
  match Cutil.unroll env ty with
  | C.TInt((C.ILongLong|C.IULongLong), _) -> false
  | _ -> true

(************ REMOVED

(* Handling of volatile *)

let is_volatile_access env e =
  List.mem C.AVolatile (Cutil.attributes_of_type env e.etyp)
  && Cutil.is_lvalue e
  && begin match Cutil.unroll env e.etyp with
     | TFun _ | TArray _ -> false
     | _ -> true
     end

let volatile_kind ty =
  match ty with
  | Tint(I8, Unsigned) -> ("int8unsigned", ty, Mint8unsigned)
  | Tint(I8, Signed) -> ("int8signed", ty, Mint8signed)
  | Tint(I16, Unsigned) -> ("int16unsigned", ty, Mint16unsigned)
  | Tint(I16, Signed) -> ("int16signed", ty, Mint16signed)
  | Tint(I32, _) -> ("int32", Tint(I32, Signed), Mint32)
  | Tfloat F32 -> ("float32", ty, Mfloat32)
  | Tfloat F64 -> ("float64", ty, Mfloat64)
  | Tpointer _ -> ("pointer", Tpointer Tvoid, Mint32)
  | _ ->
      unsupported "operation on volatile struct or union"; ("", Tvoid, Mint32)

let volatile_read_fun ty =
  let (suffix, ty', chunk) = volatile_kind ty in
  let targs = Tcons(Tpointer Tvoid, Tnil) in
  let name = "__builtin_volatile_read_" ^ suffix in
  register_special_external name (EF_vload chunk) targs ty';
  Evalof(Evar(intern_string name, Tfunction(targs, ty')), Tfunction(targs, ty'))

let volatile_write_fun ty =
  let (suffix, ty', chunk) = volatile_kind ty in
  let targs = Tcons(Tpointer Tvoid, Tcons(ty', Tnil)) in
  let name = "__builtin_volatile_write_" ^ suffix in
  register_special_external name (EF_vstore chunk) targs Tvoid;
  Evalof(Evar(intern_string name, Tfunction(targs, Tvoid)), Tfunction(targs, Tvoid))
****************************)

(** Expressions *)

let ezero = Eval(Vint(coqint_of_camlint 0l), type_int32s)

let check_assignop msg env e =
  if not (first_class_value env e.etyp) then
    unsupported (msg ^ " on a l-value of type " ^ string_of_type e.etyp)

let rec convertExpr env e =
  let ty = convertTyp env e.etyp in
  match e.edesc with
  | C.EVar _
  | C.EUnop((C.Oderef|C.Odot _|C.Oarrow _), _)
  | C.EBinop(C.Oindex, _, _, _) ->
      let l = convertLvalue env e in
      if not (first_class_value env e.etyp) then
        unsupported ("r-value of type " ^ string_of_type e.etyp);
      Evalof(l, ty)

  | C.EConst(C.CInt(i, k, _)) ->
      if k = C.ILongLong || k = C.IULongLong then
        unsupported "'long long' integer literal";
      Eval(Vint(convertInt i), ty)
  | C.EConst(C.CFloat(f, k, _)) ->
      if k = C.FLongDouble then
        unsupported "'long double' floating-point literal";
      Eval(Vfloat(f), ty)
  | C.EConst(C.CStr s) ->
      let ty = typeStringLiteral s in
      Evalof(Evar(name_for_string_literal env s, ty), ty)
  | C.EConst(C.CWStr s) ->
      unsupported "wide string literal"; ezero
  | C.EConst(C.CEnum(id, i)) ->
      Eval(Vint(convertInt i), ty)
  | C.ESizeof ty1 ->
      Esizeof(convertTyp env ty1, ty)

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
      check_assignop "pre-increment" env e1;
      coq_Epreincr Incr (convertLvalue env e1) ty
  | C.EUnop(C.Opredecr, e1) ->
      check_assignop "pre-decrement" env e1;
      coq_Epreincr Decr (convertLvalue env e1) ty
  | C.EUnop(C.Opostincr, e1) ->
      check_assignop "post-increment" env e1;
      Epostincr(Incr, convertLvalue env e1, ty)
  | C.EUnop(C.Opostdecr, e1) ->
      check_assignop "post-decrement" env e1;
      Epostincr(Decr, convertLvalue env e1, ty)

  | C.EBinop((C.Oadd|C.Osub|C.Omul|C.Odiv|C.Omod|C.Oand|C.Oor|C.Oxor|
              C.Oshl|C.Oshr|C.Oeq|C.One|C.Olt|C.Ogt|C.Ole|C.Oge) as op,
             e1, e2, _) ->
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
      check_assignop "assignment" env e1;
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
      check_assignop "assignment-operation" env e1;
      Eassignop(op', e1', e2', tyres, ty)
  | C.EBinop(C.Ocomma, e1, e2, _) ->
      Ecomma(convertExpr env e1, convertExpr env e2, ty)
  | C.EBinop(C.Ologand, e1, e2, _) ->
      coq_Eseqand (convertExpr env e1) (convertExpr env e2) ty
  | C.EBinop(C.Ologor, e1, e2, _) ->
      coq_Eseqor (convertExpr env e1) (convertExpr env e2) ty

  | C.EConditional(e1, e2, e3) ->
      Econdition(convertExpr env e1, convertExpr env e2, convertExpr env e3, ty)
  | C.ECast(ty1, e1) ->
      Ecast(convertExpr env e1, convertTyp env ty1)

  | C.ECall({edesc = C.EVar {name = "__builtin_annot"}}, args) ->
      begin match args with
      | {edesc = C.EConst(CStr txt)} :: args1 ->
          let targs1 = convertTypList env (List.map (fun e -> e.etyp) args1) in
          let fn' = register_annotation_stmt txt targs1 in
          Ecall(fn', convertExprList env args1, ty)
      | _ ->
          error "ill-formed __builtin_annot (first argument must be string literal)";
          ezero
      end          
 
  | C.ECall({edesc = C.EVar {name = "__builtin_annot_intval"}}, args) ->
      begin match args with
      | [ {edesc = C.EConst(CStr txt)}; arg ] ->
          let targ = convertTyp env arg.etyp in
          let fn' = register_annotation_val txt targ in
          Ecall(fn', convertExprList env [arg], ty)
      | _ ->
          error "ill-formed __builtin_annot_intval (first argument must be string literal)";
          ezero
      end          

  | C.ECall(fn, args) ->
      match projFunType env fn.etyp with
      | None ->
          error "wrong type for function part of a call"; ezero
      | Some(res, false) ->
          (* Non-variadic function *)
          Ecall(convertExpr env fn, convertExprList env args, ty)
      | Some(res, true) ->
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
          let tres = convertTyp env res in
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
        | Tpointer(t, _) -> t
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

(* Statement *)

let rec convertStmt env s =
  updateLoc s.sloc;
  match s.sdesc with
  | C.Sskip ->
      Sskip
  | C.Sdo e ->
      Sdo(convertExpr env e)
  | C.Sseq(s1, s2) ->
      Ssequence(convertStmt env s1, convertStmt env s2)
  | C.Sif(e, s1, s2) ->
      let te = convertExpr env e in
      Sifthenelse(te, convertStmt env s1, convertStmt env s2)
  | C.Swhile(e, s1) ->
      let te = convertExpr env e in
      Swhile(te, convertStmt env s1)
  | C.Sdowhile(s1, e) ->
      let te = convertExpr env e in
      Sdowhile(te, convertStmt env s1)
  | C.Sfor(s1, e, s2, s3) ->
      let te = convertExpr env e in
      Sfor(convertStmt env s1, te, convertStmt env s2, convertStmt env s3)
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
      Sswitch(te, convertSwitch env cases)
  | C.Slabeled(C.Slabel lbl, s1) ->
      Slabel(intern_string lbl, convertStmt env s1)
  | C.Slabeled(C.Scase _, _) ->
      unsupported "'case' outside of 'switch'"; Sskip
  | C.Slabeled(C.Sdefault, _) ->
      unsupported "'default' outside of 'switch'"; Sskip
  | C.Sgoto lbl ->
      Sgoto(intern_string lbl)
  | C.Sreturn None ->
      Sreturn None
  | C.Sreturn(Some e) ->
      Sreturn(Some(convertExpr env e))
  | C.Sblock _ ->
      unsupported "nested blocks"; Sskip
  | C.Sdecl _ ->
      unsupported "inner declarations"; Sskip

and convertSwitch env = function
  | [] ->
      LSdefault Sskip
  | [Default, s] ->
      LSdefault (convertStmt env s)
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
             convertStmt env s,
             convertSwitch env rem)

(** Function definitions *)

let convertFundef env fd =
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
  let body' = convertStmt env fd.fd_body in
  let id' = intern_string fd.fd_name.name in
  Hashtbl.add decl_atom id'
    { a_storage = fd.fd_storage;
      a_env = env;
      a_type = Cutil.fundef_typ fd;
      a_fundef = Some fd };
  Sections.define_function env id' fd.fd_ret;
  (id', Internal {fn_return = ret; fn_params = params;
                  fn_vars = vars; fn_body = body'})

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
  (id', External(ef, args, res))

(** Initializers *)

let string_of_errmsg msg =
  let string_of_err = function
  | CompcertErrors.MSG s -> camlstring_of_coqstring s
  | CompcertErrors.CTX i -> extern_atom i
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
  | CompcertErrors.OK init -> init
  | CompcertErrors.Error msg ->
      error (sprintf "Initializer is not a compile-time constant (%s)"
                     (string_of_errmsg msg)); []

(** Global variable *)

let convertGlobvar env (sto, id, ty, optinit) =
  let id' = intern_string id.name in
  let ty' = convertTyp env ty in 
  let init' =
    match optinit with
    | None ->
        if sto = C.Storage_extern then [] else [Init_space(Csyntax.sizeof ty')]
    | Some i ->
        convertInitializer env ty i in
  Hashtbl.add decl_atom id'
    { a_storage = sto;
      a_env = env;
      a_type = ty;
      a_fundef = None };
  Sections.define_variable env id' ty;
  let a = Cutil.attributes_of_type env ty in
  let volatile = List.mem C.AVolatile a in
  let readonly = List.mem C.AConst a && not volatile in
  (id', {gvar_info = ty'; gvar_init = init';
         gvar_readonly = readonly; gvar_volatile = volatile})

(** Convert a list of global declarations.
  Result is a pair [(funs, vars)] where [funs] are 
  the function definitions (internal and external)
  and [vars] the variable declarations. *)

let rec convertGlobdecls env funs vars gl =
  match gl with
  | [] -> (List.rev funs, List.rev vars)
  | g :: gl' ->
      updateLoc g.gloc;
      match g.gdesc with
      | C.Gdecl((sto, id, ty, optinit) as d) ->
          (* Prototyped functions become external declarations.
             Variadic functions are skipped.
             Other types become variable declarations. *)
          begin match Cutil.unroll env ty with
          | TFun(_, Some _, false, _) ->
              convertGlobdecls env (convertFundecl env d :: funs) vars gl'
          | TFun(_, None, false, _) ->
              error "function declaration without prototype";
              convertGlobdecls env funs vars gl'
          | TFun(_, _, true, _) ->
              convertGlobdecls env funs vars gl'
          | _ ->
              convertGlobdecls env funs (convertGlobvar env d :: vars) gl'
          end
      | C.Gfundef fd ->
          convertGlobdecls env (convertFundef env fd :: funs) vars gl'
      | C.Gcompositedecl _ | C.Gcompositedef _
      | C.Gtypedef _ | C.Genumdef _ ->
          (* typedefs are unrolled, structs are expanded inline, and
             enum tags are folded.  So we just skip their declarations. *)
          convertGlobdecls env funs vars gl'
      | C.Gpragma s ->
          if not (!process_pragma_hook s) then
            warning ("'#pragma " ^ s ^ "' directive ignored");
          convertGlobdecls env funs vars gl'

(** Build environment of typedefs and structs *)

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
        | _ ->
            env in
      translEnv env' gl

(** Eliminate forward declarations of globals that are defined later. *)

module IdentSet = Set.Make(struct type t = C.ident let compare = compare end)

let cleanupGlobals p =
  
  let rec clean defs accu = function
    | [] -> accu
    | g :: gl ->
        updateLoc g.gloc;
        match g.gdesc with
        | C.Gdecl(sto, id, ty, None) ->
            if IdentSet.mem id defs
            then clean defs accu gl
            else clean (IdentSet.add id defs) (g :: accu) gl
        | C.Gdecl(_, id, ty, _) ->
            if IdentSet.mem id defs then
              error ("multiple definitions of " ^ id.name);
            clean (IdentSet.add id defs) (g :: accu) gl
        | C.Gfundef fd ->
            if IdentSet.mem fd.fd_name defs then
              error ("multiple definitions of " ^ fd.fd_name.name);
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
  Hashtbl.clear special_externals_table;
  let p = Builtins.declarations() @ p in
  try
    let (funs1, vars1) =
      convertGlobdecls (translEnv Env.empty p) [] [] (cleanupGlobals p) in
    let funs2 = declare_special_externals funs1 in
    let vars2 = globals_for_strings vars1 in
    if !numErrors > 0
    then None
    else Some { AST.prog_funct = funs2;
                AST.prog_vars = vars2;
                AST.prog_main = intern_string "main" }
  with Env.Error msg ->
    error (Env.error_message msg); None

(** ** Extracting information about global variables from their atom *)

let atom_is_static a =
  try
    match Hashtbl.find decl_atom a with
    | { a_storage = C.Storage_static } -> true
    (* We do not inline functions, but at least let's not make them globals *)
    | { a_fundef = Some { fd_inline = true } } -> true 
    | _ -> false
  with Not_found ->
    false

let atom_is_extern a =
  try
    let i = Hashtbl.find decl_atom a in i.a_storage = C.Storage_extern
  with Not_found ->
    false

(*
let atom_is_readonly a =
  try
    let i = Hashtbl.find decl_atom a in type_is_readonly i.a_env i.a_type
  with Not_found ->
    false

let atom_sizeof a =
  try
    let i = Hashtbl.find decl_atom a in Cutil.sizeof i.a_env i.a_type
  with Not_found ->
    None
*)

let atom_alignof a =
  try
    let i = Hashtbl.find decl_atom a in
    match Cutil.find_custom_attributes
                  ["aligned"; "__aligned__"]
                  (Cutil.attributes_of_type i.a_env i.a_type) with
    | [[C.AInt n]] -> Some(Int64.to_int n)
    | _            -> Cutil.alignof i.a_env i.a_type
  with Not_found ->
    None

