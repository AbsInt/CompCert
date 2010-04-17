open Printf

open Cparser
open Cparser.C
open Cparser.Env

open Camlcoq
open AST
open Csyntax

(** Record the declarations of global variables and associate them
    with the corresponding atom. *)

let decl_atom : (AST.ident, Env.t * C.decl) Hashtbl.t = Hashtbl.create 103

(** Hooks -- overriden in machine-dependent CPragmas module *)

let process_pragma_hook = ref (fun (s: string) -> false)
let define_variable_hook = ref (fun (id: ident) (d: C.decl) -> ())
let define_function_hook = ref (fun (id: ident) (d: C.decl) -> ())
let define_stringlit_hook = ref (fun (id: ident) -> ())

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
      (env, (C.Storage_static,
             Env.fresh_ident name,
             C.TPtr(C.TInt(C.IChar,[C.AConst]),[]),
             None));
    !define_stringlit_hook id;
    Hashtbl.add stringTable s id;
    id

let typeStringLiteral s =
  Tarray(Tint(I8, Unsigned), z_of_camlint(Int32.of_int(String.length s + 1)))

let global_for_string s id =
  let init = ref [] in
  let add_char c =
    init :=
       AST.Init_int8(coqint_of_camlint(Int32.of_int(Char.code c)))
       :: !init in
  add_char '\000';
  for i = String.length s - 1 downto 0 do add_char s.[i] done;
  Datatypes.Coq_pair(Datatypes.Coq_pair(id, !init), typeStringLiteral s)

let globals_for_strings globs =
  Hashtbl.fold
    (fun s id l -> global_for_string s id :: l)
    stringTable globs

(** ** Handling of stubs for variadic functions *)

let stub_function_table = Hashtbl.create 47

let register_stub_function name tres targs =
  let rec letters_of_type = function
    | Tnil -> []
    | Tcons(Tfloat _, tl) -> "f" :: letters_of_type tl
    | Tcons(_, tl) -> "i" :: letters_of_type tl in
  let stub_name =
    name ^ "$" ^ String.concat "" (letters_of_type targs) in
  try
    (stub_name, Hashtbl.find stub_function_table stub_name)
  with Not_found ->
    let rec types_of_types = function
      | Tnil -> Tnil
      | Tcons(Tfloat _, tl) -> Tcons(Tfloat F64, types_of_types tl)
      | Tcons(_, tl) -> Tcons(Tpointer Tvoid, types_of_types tl) in
    let stub_type = Tfunction (types_of_types targs, tres) in
    Hashtbl.add stub_function_table stub_name stub_type;
    (stub_name, stub_type)

let declare_stub_function stub_name stub_type =
  match stub_type with
  | Tfunction(targs, tres) ->
      Datatypes.Coq_pair(intern_string stub_name,
                         External(intern_string stub_name, targs, tres))
  | _ -> assert false

let declare_stub_functions k =
  Hashtbl.fold (fun n i k -> declare_stub_function n i :: k)
               stub_function_table k

(** ** Translation functions *)

(** Constants *)

let convertInt n = coqint_of_camlint(Int64.to_int32 n)

(** Types *)

let convertIkind = function
  | C.IBool -> unsupported "'_Bool' type"; (Unsigned, I8)
  | C.IChar -> (Unsigned, I8)
  | C.ISChar -> (Signed, I8)
  | C.IUChar -> (Unsigned, I8)
  | C.IInt -> (Signed, I32)
  | C.IUInt -> (Unsigned, I32)
  | C.IShort -> (Signed, I16)
  | C.IUShort -> (Unsigned, I16)
  | C.ILong -> (Signed, I32)
  | C.IULong -> (Unsigned, I32)
  | C.ILongLong -> 
      if not !Clflags.option_flonglong then unsupported "'long long' type";
      (Signed, I32)
  | C.IULongLong ->
      if not !Clflags.option_flonglong then unsupported "'unsigned long long' type";
      (Unsigned, I32)

let convertFkind = function
  | C.FFloat -> F32
  | C.FDouble -> F64
  | C.FLongDouble ->
      if not !Clflags.option_flonglong then unsupported "'long double' type";
      F64

let convertTyp env t =

  let rec convertTyp seen t =
    match Cutil.unroll env t with
    | C.TVoid a -> Tvoid
    | C.TInt(ik, a) ->
        let (sg, sz) = convertIkind ik in Tint(sz, sg)
    | C.TFloat(fk, a) ->
        Tfloat(convertFkind fk)
    | C.TPtr(C.TStruct(id, _), _) when List.mem id seen ->
        Tcomp_ptr(intern_string ("struct " ^ id.name))
    | C.TPtr(C.TUnion(id, _), _) when List.mem id seen ->
        Tcomp_ptr(intern_string ("union " ^ id.name))
    | C.TPtr(ty, a) ->
        Tpointer(convertTyp seen ty)
    | C.TArray(ty, None, a) ->
        (* Cparser verified that the type ty[] occurs only in
           contexts that are safe for Clight, so just treat as ty[0]. *)
        (* warning "array type of unspecified size"; *)
        Tarray(convertTyp seen ty, coqint_of_camlint 0l)
    | C.TArray(ty, Some sz, a) ->
        Tarray(convertTyp seen ty, convertInt sz)
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
        Tstruct(intern_string("struct " ^ id.name), flds)
    | C.TUnion(id, a) ->
        let flds =
          try
            convertFields (id :: seen) (Env.find_union env id)
          with Env.Error e ->
            error (Env.error_message e); Fnil in
        Tunion(intern_string("union " ^ id.name), flds)

  and convertParams seen = function
    | [] -> Tnil
    | (id, ty) :: rem ->
        if Cutil.is_composite_type env ty then
          unsupported "function parameter of struct or union type";
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

(** Expressions *)

let ezero = Expr(Econst_int(coqint_of_camlint 0l), Tint(I32, Signed))

let rec convertExpr env e =
  let ty = convertTyp env e.etyp in
  match e.edesc with
  | C.EConst(C.CInt(i, _, _)) ->
      Expr(Econst_int(convertInt i), ty)
  | C.EConst(C.CFloat(f, _, _)) ->
      Expr(Econst_float f, ty)
  | C.EConst(C.CStr s) ->
      Expr(Evar(name_for_string_literal env s), typeStringLiteral s)
  | C.EConst(C.CWStr s) ->
      unsupported "wide string literal"; ezero
  | C.EConst(C.CEnum(id, i)) ->
      Expr(Econst_int(convertInt i), ty)

  | C.ESizeof ty1 ->
      Expr(Esizeof(convertTyp env ty1), ty)
  | C.EVar id ->
      Expr(Evar(intern_string id.name), ty)

  | C.EUnop(C.Oderef, e1) ->
      Expr(Ederef(convertExpr env e1), ty)
  | C.EUnop(C.Oaddrof, e1) ->
      Expr(Eaddrof(convertExpr env e1), ty)
  | C.EUnop(C.Odot id, e1) ->
      Expr(Efield(convertExpr env e1, intern_string id), ty)
  | C.EUnop(C.Oarrow id, e1) ->
      let e1' = convertExpr env e1 in
      let ty1 =
        match typeof e1' with
        | Tpointer t -> t
        | _ -> error ("wrong type for ->" ^ id ^ " access"); Tvoid in
      Expr(Efield(Expr(Ederef(convertExpr env e1), ty1),
                  intern_string id), ty)
  | C.EUnop(C.Oplus, e1) ->
      convertExpr env e1
  | C.EUnop(C.Ominus, e1) ->
      Expr(Eunop(Oneg, convertExpr env e1), ty)
  | C.EUnop(C.Olognot, e1) ->
      Expr(Eunop(Onotbool, convertExpr env e1), ty)
  | C.EUnop(C.Onot, e1) ->
      Expr(Eunop(Onotint, convertExpr env e1), ty)
  | C.EUnop(_, _) ->
      unsupported "pre/post increment/decrement operator"; ezero

  | C.EBinop(C.Oindex, e1, e2, _) ->
      Expr(Ederef(Expr(Ebinop(Oadd, convertExpr env e1, convertExpr env e2),
                       Tpointer ty)), ty)
  | C.EBinop(C.Ologand, e1, e2, _) ->
      Expr(Eandbool(convertExpr env e1, convertExpr env e2), ty)
  | C.EBinop(C.Ologor, e1, e2, _) ->
      Expr(Eorbool(convertExpr env e1, convertExpr env e2), ty)
  | C.EBinop(op, e1, e2, _) ->
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
        | C.Ocomma -> unsupported "sequence operator"; Oadd
        | _ -> unsupported "assignment operator"; Oadd in
      Expr(Ebinop(op', convertExpr env e1, convertExpr env e2), ty)
  | C.EConditional(e1, e2, e3) ->
      Expr(Econdition(convertExpr env e1, convertExpr env e2, convertExpr env e3), ty)
  | C.ECast(ty1, e1) ->
      Expr(Ecast(convertTyp env ty1, convertExpr env e1), ty)
  | C.ECall _ ->
      unsupported "function call within expression"; ezero

(* Function calls *)

let rec projFunType env ty =
  match Cutil.unroll env ty with
  | TFun(res, args, vararg, attr) -> Some(res, vararg)
  | TPtr(ty', attr) -> projFunType env ty'
  | _ -> None

let convertFuncall env lhs fn args =
  match projFunType env fn.etyp with
  | None ->
      error "wrong type for function part of a call"; Sskip
  | Some(res, false) ->
      (* Non-variadic function *)
      Scall(lhs, convertExpr env fn, List.map (convertExpr env) args)
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
      Scall(lhs,
            Expr(Evar(intern_string stub_fun_name), stub_fun_typ),
            List.map (convertExpr env) args)

(* Handling of volatile *)

let is_volatile_access env e =
  List.mem C.AVolatile (Cutil.attributes_of_type env e.etyp)
  && Cutil.is_lvalue env e

let volatile_fun_suffix_type ty =
  match ty with
  | Tint(I8, Unsigned) -> ("int8unsigned", ty)
  | Tint(I8, Signed) -> ("int8signed", ty)
  | Tint(I16, Unsigned) -> ("int16unsigned", ty)
  | Tint(I16, Signed) -> ("int16signed", ty)
  | Tint(I32, _) -> ("int32", Tint(I32, Signed))
  | Tfloat F32 -> ("float32", ty)
  | Tfloat F64 -> ("float64", ty)
  | Tpointer _ | Tarray _ | Tfunction _ | Tcomp_ptr _ ->
      ("pointer", Tpointer Tvoid)
  | _ ->
      unsupported "operation on volatile struct or union"; ("", Tvoid)

let volatile_read_fun ty =
  let (suffix, ty') = volatile_fun_suffix_type ty in
  Expr(Evar(intern_string ("__builtin_volatile_read_" ^ suffix)),
       Tfunction(Tcons(Tpointer Tvoid, Tnil), ty'))

let volatile_write_fun ty =
  let (suffix, ty') = volatile_fun_suffix_type ty in
  Expr(Evar(intern_string ("__builtin_volatile_write_" ^ suffix)),
       Tfunction(Tcons(Tpointer Tvoid, Tcons(ty', Tnil)), Tvoid))

(* Toplevel expression, argument of an Sdo *)

let convertTopExpr env e =
  match e.edesc with
  | C.EBinop(C.Oassign, lhs, {edesc = C.ECall(fn, args)}, _) ->
      convertFuncall env (Some (convertExpr env lhs)) fn args
  | C.EBinop(C.Oassign, lhs, rhs, _) ->
      if Cutil.is_composite_type env lhs.etyp then
        unsupported "assignment between structs or between unions";
      let lhs' = convertExpr env lhs
      and rhs' = convertExpr env rhs in
      begin match (is_volatile_access env lhs, is_volatile_access env rhs) with
      | true, true ->                   (* should not happen *)
          unsupported "volatile-to-volatile assignment";
          Sskip
      | false, true ->                  (* volatile read *)
          Scall(Some lhs',
                volatile_read_fun (typeof rhs'),
                [ Expr (Eaddrof rhs', Tpointer (typeof rhs')) ])
      | true, false ->                  (* volatile write *)
          Scall(None,
                volatile_write_fun (typeof lhs'),
                [ Expr(Eaddrof lhs', Tpointer (typeof lhs')); rhs' ])
      | false, false ->                 (* regular assignment *)
          Sassign(convertExpr env lhs, convertExpr env rhs)
      end
  | C.ECall(fn, args) ->
      convertFuncall env None fn args
  | _ ->
      unsupported "illegal toplevel expression"; Sskip

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
      convertTopExpr env e
  | C.Sseq(s1, s2) ->
      Ssequence(convertStmt env s1, convertStmt env s2)
  | C.Sif(e, s1, s2) ->
      Sifthenelse(convertExpr env e, convertStmt env s1, convertStmt env s2)
  | C.Swhile(e, s1) ->
      Swhile(convertExpr env e, convertStmt env s1)
  | C.Sdowhile(s1, e) ->
      Sdowhile(convertExpr env e, convertStmt env s1)
  | C.Sfor(s1, e, s2, s3) ->
      Sfor(convertStmt env s1, convertExpr env e, convertStmt env s2,
           convertStmt env s3)
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
      Sswitch(convertExpr env e, convertSwitch env cases)
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
        if Cutil.is_composite_type env ty then
          unsupported "function parameter of struct or union type";
        Datatypes.Coq_pair(intern_string id.name, convertTyp env ty))
      fd.fd_params in
  let vars =
    List.map
      (fun (sto, id, ty, init) ->
        if sto = Storage_extern || sto = Storage_static then
          unsupported "'static' or 'extern' local variable";
        if init <> None then
          unsupported "initialized local variable";
        Datatypes.Coq_pair(intern_string id.name, convertTyp env ty))
      fd.fd_locals in
  let body' = convertStmt env fd.fd_body in
  let id' = intern_string fd.fd_name.name in
  let decl =
    (fd.fd_storage, fd.fd_name, Cutil.fundef_typ fd, None) in
  Hashtbl.add decl_atom id' (env, decl);
  !define_function_hook id' decl;
  Datatypes.Coq_pair(id',
                     Internal {fn_return = ret; fn_params = params;
                               fn_vars = vars; fn_body = body'})

(** External function declaration *)

let convertFundecl env (sto, id, ty, optinit) =
  match convertTyp env ty with
  | Tfunction(args, res) ->
      let id' = intern_string id.name in
      Datatypes.Coq_pair(id', External(id', args, res))
  | _ ->
      assert false

(** Initializers *)

let init_data_of_string s =
  let id = ref [] in
  let enter_char c =
    let n = coqint_of_camlint(Int32.of_int(Char.code c)) in
    id := Init_int8 n :: !id in
  enter_char '\000';
  for i = String.length s - 1 downto 0 do enter_char s.[i] done;
  !id

let convertInit env ty init =

  let k = ref []
  and pos = ref 0 in
  let emit size datum =
    k := datum :: !k;
    pos := !pos + size in
  let emit_space size =
    emit size (Init_space (z_of_camlint (Int32.of_int size))) in
  let align size =
    let n = !pos land (size - 1) in
    if n > 0 then emit_space (size - n) in
  let check_align size =
    assert (!pos land (size - 1) = 0) in

  let rec reduceInitExpr = function
    | { edesc = C.EVar id; etyp = ty } ->
        begin match Cutil.unroll env ty with
        | C.TArray _ | C.TFun _ -> Some id
        | _ -> None
        end
    | {edesc = C.EUnop(C.Oaddrof, {edesc = C.EVar id})} -> Some id
    | {edesc = C.ECast(ty, e)} -> reduceInitExpr e
    | _ -> None in

  let rec cvtInit ty = function
  | Init_single e ->
      begin match reduceInitExpr e with
      | Some id ->
          check_align 4;
          emit 4 (Init_addrof(intern_string id.name, coqint_of_camlint 0l))
      | None ->
      match Ceval.constant_expr env ty e with
      | Some(C.CInt(v, ik, _)) ->
          begin match convertIkind ik with
          | (_, I8) ->
              emit 1 (Init_int8(convertInt v))
          | (_, I16) ->
              check_align 2;
              emit 2 (Init_int16(convertInt v))
          | (_, I32) ->
              check_align 4;
              emit 4 (Init_int32(convertInt v))
          end
      | Some(C.CFloat(v, fk, _)) ->
          begin match convertFkind fk with
          | F32 ->
              check_align 4;
              emit 4 (Init_float32 v)
          | F64 ->
              check_align 8;
              emit 8 (Init_float64 v)
          end
      | Some(C.CStr s) ->
          check_align 4;
          let id = name_for_string_literal env s in
          emit 4 (Init_addrof(id, coqint_of_camlint 0l))
      | Some(C.CWStr _) ->
          unsupported "wide character strings"
      | Some(C.CEnum _) ->
          error "enum tag after constant folding"
      | None ->
          error "initializer is not a compile-time constant"
      end
  | Init_array il ->
      let ty_elt =
        match Cutil.unroll env ty with
        | C.TArray(t, _, _) -> t
        | _ -> error "array type expected in initializer"; C.TVoid [] in
      List.iter (cvtInit ty_elt) il
  | Init_struct(_, flds) ->
      cvtPadToSizeof ty (fun () -> List.iter cvtFieldInit flds)
  | Init_union(_, fld, i) ->
      cvtPadToSizeof ty (fun () -> cvtFieldInit (fld,i))

  and cvtFieldInit (fld, i) =
    let ty' = convertTyp env fld.fld_typ in
    let al = Int32.to_int (camlint_of_z (Csyntax.alignof ty')) in
    align al;
    cvtInit fld.fld_typ i

  and cvtPadToSizeof ty fn =
    let ty' = convertTyp env ty in
    let sz = Int32.to_int (camlint_of_z (Csyntax.sizeof ty')) in
    let pos0 = !pos in
    fn();
    let pos1 = !pos in
    assert (pos1 <= pos0 + sz);
    if pos1 < pos0 + sz then emit_space (pos0 + sz - pos1)

  in cvtInit ty init; List.rev !k

(** Global variable *)

let convertGlobvar env (sto, id, ty, optinit as decl) =
  let id' = intern_string id.name in
  let ty' = convertTyp env ty in 
  let init' =
    match optinit with
    | None ->
        if sto = C.Storage_extern then [] else [Init_space(Csyntax.sizeof ty')]
    | Some i ->
        convertInit env ty i in
  Hashtbl.add decl_atom id' (env, decl);
  !define_variable_hook id' decl;
  Datatypes.Coq_pair(Datatypes.Coq_pair(id', init'), ty')

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
        | C.Gcompositedecl(su, id) ->
            Env.add_composite env id (Cutil.composite_info_decl env su)
        | C.Gcompositedef(su, id, fld) ->
            Env.add_composite env id (Cutil.composite_info_def env su fld)
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
  Hashtbl.clear stub_function_table;
  let p = Builtins.declarations() @ p in
  try
    let (funs1, vars1) =
      convertGlobdecls (translEnv Env.empty p) [] [] (cleanupGlobals p) in
    let funs2 = declare_stub_functions funs1 in
    let vars2 = globals_for_strings vars1 in
    if !numErrors > 0
    then None
    else Some { AST.prog_funct = funs2;
                AST.prog_vars = vars2;
                AST.prog_main = intern_string "main" }
  with Env.Error msg ->
    error (Env.error_message msg); None

(** ** Extracting information about global variables from their atom *)

let rec type_is_readonly env t =
  let a = Cutil.attributes_of_type env t in
  if List.mem C.AVolatile a then false else
  if List.mem C.AConst a then true else
  match Cutil.unroll env t with
  | C.TArray(t', _, _) -> type_is_readonly env t'
  | _ -> false

let atom_is_static a =
  try
    let (env, (sto, id, ty, init)) = Hashtbl.find decl_atom a in
    sto = C.Storage_static
  with Not_found ->
    false

let atom_is_readonly a =
  try
    let (env, (sto, id, ty, init)) = Hashtbl.find decl_atom a in
    type_is_readonly env ty
  with Not_found ->
    false

let atom_sizeof a =
  try
    let (env, (sto, id, ty, init)) = Hashtbl.find decl_atom a in
    Cutil.sizeof env ty
  with Not_found ->
    None

let atom_alignof a =
  try
    let (env, (sto, id, ty, init)) = Hashtbl.find decl_atom a in
    Cutil.alignof env ty
  with Not_found ->
    None

(** ** The builtin environment *)

open Cparser.Builtins

let builtins_generic = {
  typedefs = [
    (* keeps GCC-specific headers happy, harmless for others *)
    "__builtin_va_list", C.TPtr(C.TVoid [], [])
  ];
  functions = [
    (* The volatile read/volatile write functions *)
    "__builtin_volatile_read_int8unsigned",
        (TInt(IUChar, []), [TPtr(TVoid [], [])], false);
    "__builtin_volatile_read_int8signed",
        (TInt(ISChar, []), [TPtr(TVoid [], [])], false);
    "__builtin_volatile_read_int16unsigned",
        (TInt(IUShort, []), [TPtr(TVoid [], [])], false);
    "__builtin_volatile_read_int16signed",
        (TInt(IShort, []), [TPtr(TVoid [], [])], false);
    "__builtin_volatile_read_int32",
        (TInt(IInt, []), [TPtr(TVoid [], [])], false);
    "__builtin_volatile_read_float32",
        (TFloat(FFloat, []), [TPtr(TVoid [], [])], false);
    "__builtin_volatile_read_float64",
         (TFloat(FDouble, []), [TPtr(TVoid [], [])], false);
    "__builtin_volatile_read_pointer",
         (TPtr(TVoid [], []), [TPtr(TVoid [], [])], false);
    "__builtin_volatile_write_int8unsigned",
        (TVoid [], [TPtr(TVoid [], []); TInt(IUChar, [])], false);
    "__builtin_volatile_write_int8signed",
        (TVoid [], [TPtr(TVoid [], []); TInt(ISChar, [])], false);
    "__builtin_volatile_write_int16unsigned",
        (TVoid [], [TPtr(TVoid [], []); TInt(IUShort, [])], false);
    "__builtin_volatile_write_int16signed",
        (TVoid [], [TPtr(TVoid [], []); TInt(IShort, [])], false);
    "__builtin_volatile_write_int32",
        (TVoid [], [TPtr(TVoid [], []); TInt(IInt, [])], false);
    "__builtin_volatile_write_float32",
        (TVoid [], [TPtr(TVoid [], []); TFloat(FFloat, [])], false);
    "__builtin_volatile_write_float64",
         (TVoid [], [TPtr(TVoid [], []); TFloat(FDouble, [])], false);
    "__builtin_volatile_write_pointer",
         (TVoid [], [TPtr(TVoid [], []); TPtr(TVoid [], [])], false);
    (* Block copy *)
    "__builtin_memcpy",
         (TVoid [],
           [TPtr(TVoid [], []); 
            TPtr(TVoid [AConst], []); 
            TInt(Cutil.size_t_ikind, [])],
          false);
    "__builtin_memcpy_words",
         (TVoid [],
           [TPtr(TVoid [], []); 
            TPtr(TVoid [AConst], []); 
            TInt(Cutil.size_t_ikind, [])],
          false)
  ]
}

(* Add processor-dependent builtins *)

let builtins =
  { typedefs = builtins_generic.typedefs @ CBuiltins.builtins.typedefs;
    functions = builtins_generic.functions @ CBuiltins.builtins.functions }
