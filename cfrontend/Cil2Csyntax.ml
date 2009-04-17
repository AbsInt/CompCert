(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Thomas Moniot, INRIA Paris-Rocquencourt                    *)
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

(**************************************************************************
CIL -> CabsCoq translator
**************************************************************************)

open Cil
open Camlcoq
open AST
open Csyntax

(* To associate CIL varinfo to the atoms representing global variables *)

let varinfo_atom : (BinPos.positive, Cil.varinfo) Hashtbl.t =
  Hashtbl.create 103



module type TypeSpecifierTranslator =
  sig
    val convertIkind: Cil.ikind -> (intsize * signedness) option
    val convertFkind: Cil.fkind -> floatsize option
  end





module Make(TS: TypeSpecifierTranslator) = struct
(*-----------------------------------------------------------------------*)


(** Pre-defined constants *)
let constInt32 = Tint (I32, Signed)
let constInt32uns = Tint (I32, Unsigned)
let const0 = Expr (Econst_int (coqint_of_camlint Int32.zero), constInt32)


(** Global variables *)
let currentLocation = ref Cil.locUnknown
let stringNum = ref 0   (* number of next global for string literals *)
let stringTable = Hashtbl.create 47

(** ** Functions related to [struct]s and [union]s *)

(* Unroll recursion in struct or union types:
   substitute [Tcomp_ptr id] by [Tpointer compty] in [ty]. *)

let unrollType id compty ty =
  let rec unrType ty =
    match ty with
    | Tvoid -> ty
    | Tint(sz, sg) -> ty
    | Tfloat sz -> ty
    | Tpointer ty -> Tpointer (unrType ty)
    | Tarray(ty, sz) -> Tarray (unrType ty, sz)
    | Tfunction(args, res) -> Tfunction(unrTypelist args, unrType res)
    | Tstruct(id', fld) ->
        if id' = id then ty else Tstruct(id', unrFieldlist fld)
    | Tunion(id', fld) ->
        if id' = id then ty else Tunion(id', unrFieldlist fld)
    | Tcomp_ptr id' ->
        if id' = id then Tpointer compty else ty
  and unrTypelist = function
    | Tnil -> Tnil
    | Tcons(hd, tl) -> Tcons(unrType hd, unrTypelist tl)
  and unrFieldlist = function
    | Fnil -> Fnil
    | Fcons(id, ty, tl) -> Fcons(id, unrType ty, unrFieldlist tl)
  in unrType ty

(* Return the type of a [struct] field *)
let rec getFieldType f = function
  | Fnil -> raise Not_found
  | Fcons(idf, t, rem) -> if idf = f then t else getFieldType f rem

(** ** Some functions over lists *)

(** Keep the elements in a list from [elt] (included) to the end
    (used for the translation of the [switch] statement) *)
let rec keepFrom elt = function
  | [] -> []
  | (x :: l) as l' -> if x == elt then l' else keepFrom elt l

(** Keep the elements in a list before [elt'] (excluded)
    (used for the translation of the [switch] statement) *)
let rec keepUntil elt' = function
  | [] -> []
  | x :: l -> if x == elt' then [] else x :: (keepUntil elt' l)

(** Keep the elements in a list from [elt] (included) to [elt'] (excluded)
    (used for the translation of the [switch] statement) *)
let keepBetween elt elt' l =
  keepUntil elt' (keepFrom elt l)

(** ** Functions used to handle locations *)

(** Update the current location *)
let updateLoc loc =
  currentLocation := loc

(** Convert the current location into a string *)
let currentLoc() =
  match !currentLocation with { line=l; file=f } ->
    f ^ ":" ^ (if l = -1 then "?" else string_of_int l) ^ ": "

(** Exception raised when an unsupported feature is encountered *)
exception Unsupported of string
let unsupported msg =
  raise (Unsupported(currentLoc() ^ "Unsupported C feature: " ^ msg))

(** Exception raised when an internal error is encountered *)
exception Internal_error of string
let internal_error msg =
  raise (Internal_error(currentLoc() ^ "Internal error: " ^ msg))

(** Warning messages *)
let warning msg =
  prerr_string (currentLoc());
  prerr_string "Warning: ";
  prerr_endline msg

(** ** Functions used to handle string literals *)

let name_for_string_literal s =
  try
    Hashtbl.find stringTable s
  with Not_found ->
    incr stringNum;
    let name = Printf.sprintf "__stringlit_%d" !stringNum in
    let id = intern_string name in
    let v =
      makeVarinfo true s (typeAddAttributes [Attr("const",[])] charPtrType) in
    v.vstorage <- Static;
    v.vreferenced <- true;
    Hashtbl.add varinfo_atom id v;
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

(** ** Generation of temporary variable names *)

let current_function = ref (None: Cil.fundec option)

let make_temp typ =
  match !current_function with
  | None -> assert false
  | Some f ->
      let v = Cil.makeTempVar f typ in 
      intern_string v.vname

(** Detect and report GCC's __builtin_ functions *)

let check_builtin s =
  let b = "__builtin_" in
  if String.length s >= String.length b
  && String.sub s 0 (String.length b) = b
  then unsupported ("GCC `" ^ s ^ "' built-in function")

(** ** Translation functions *)

(** Convert a [Cil.ikind] into a pair [(intsize * signedness)] *)
let convertIkind ik =
  match TS.convertIkind ik with
    | Some p -> p
    | None -> unsupported "integer type specifier"


(** Convert a [Cil.fkind] into a [floatsize] *)
let convertFkind fk =
  match TS.convertFkind fk with
    | Some fs -> fs
    | None -> unsupported "floating-point type specifier"


(** Convert a [Cil.constant] into a [CabsCoq.expr] *)
let rec convertConstant = function
  | CInt64 (i64, _, _) ->
      let i = coqint_of_camlint (Int64.to_int32 i64) in
      Expr (Econst_int i, constInt32)
  | CStr s ->
      let symb = name_for_string_literal s in
      Expr (Evar symb, typeStringLiteral s)
  | CWStr _ ->
      unsupported "wide string literal"
  | CChr c  ->
      let i = coqint_of_camlint (Int32.of_int (Char.code c)) in
      Expr (Econst_int i, constInt32)
  | CReal (f, _, _) ->
      Expr (Econst_float f, Tfloat F64)
  | (CEnum (exp, str, enumInfo)) as enum ->
      (* do constant folding on an enum constant *)
      let e = Cil.constFold false (Const enum) in
      convertExp e


(** Convert a [Cil.UnOp] into a [CabsCoq.expr]
    ([t] is the type of the result of applying [uop] to [e]) *)
and convertUnop uop e t =
  let e' = convertExp e in
  let t' = convertTyp t in
  let uop' = match uop with
    | Neg -> Eunop (Oneg, e')
    | BNot -> Eunop (Onotint, e')
    | LNot -> Eunop (Onotbool, e')
  in
    Expr (uop', t')


(** Convert a [Cil.BinOp] into a [CabsCoq.expr]
    ([t] is the type of the result of applying [bop] to [(e1, e2)], every
    arithmetic conversion being made explicit by CIL for both arguments] *)
and convertBinop bop e1 e2 t =
  let e1' = convertExp e1 in
  let e2' = convertExp e2 in
  let t' = convertTyp t in
  let bop' = match bop with
    | PlusA   -> Ebinop (Oadd, e1', e2')
    | PlusPI  -> Ebinop (Oadd, e1', e2')
    | IndexPI -> Ebinop (Oadd, e1', e2')
    | MinusA  -> Ebinop (Osub, e1', e2')
    | MinusPI -> Ebinop (Osub, e1', e2')
    | MinusPP -> Ebinop (Osub, e1', e2')
    | Mult    -> Ebinop (Omul, e1', e2')
    | Div     -> Ebinop (Odiv, e1', e2')
    | Mod     -> Ebinop (Omod, e1', e2')
    | Shiftlt -> Ebinop (Oshl, e1', e2')
    | Shiftrt -> Ebinop (Oshr, e1', e2')
    | Lt      -> Ebinop (Olt, e1', e2')
    | Gt      -> Ebinop (Ogt, e1', e2')
    | Le      -> Ebinop (Ole, e1', e2')
    | Ge      -> Ebinop (Oge, e1', e2')
    | Eq      -> Ebinop (Oeq, e1', e2')
    | Ne      -> Ebinop (One, e1', e2')
    | BAnd    -> Ebinop (Oand, e1', e2')
    | BXor    -> Ebinop (Oxor, e1', e2')
    | BOr     -> Ebinop (Oor, e1', e2')
    | LAnd    -> Eandbool (e1', e2')
    | LOr     -> Eorbool (e1', e2')
  in
    Expr (bop', t')


(** Test if two types are compatible
    (in order to cast one of the types to the other) *)
and compatibleTypes t1 t2 = true
(*
  let isArithmeticType = function
    | Tint _ | Tfloat _ -> true
    | _ -> false
  in
  let isPointerType = function
    | Tpointer _ | Tarray _ -> true
    | _ -> false
  in
       (t1 = t2)
    || (isArithmeticType t1 && isArithmeticType t2)
    || match (t1, t2) with
         | (Tpointer Tvoid, t) | (t, Tpointer Tvoid) -> isPointerType t
	 | (Tint _, t) | (t, Tint _) -> isPointerType t
	 | _ -> false
*)


(** Convert a [Cil.CastE] into a [CabsCoq.expr]
    (fail if the cast is illegal) *)
and processCast t e =
  let t' = convertTyp t in
  let te = convertTyp (Cil.typeOf e) in
    if compatibleTypes t' te then
      let e' = convertExp e in
	Expr (Ecast (t', e'), t')
    else internal_error "processCast: illegal cast"


(** Convert a [Cil.exp list] into an [CamlCoq.exprlist] *)
and processParamsE = function
  | [] -> []
  | e :: l ->
      let (Expr (_, t)) as e' = convertExp e in
	match t with
	  | Tstruct _ | Tunion _ ->
              unsupported "function parameter of struct or union type"
	  | _ -> e' :: processParamsE l


(** Convert a [Cil.exp] into a [CabsCoq.expr] *)
and convertExp = function
  | Const c ->
      convertConstant c
  | Lval lv ->
      convertLval lv
  | SizeOf t ->
      Expr (Esizeof (convertTyp t), constInt32uns)
  | SizeOfE e ->
      let ty = convertTyp (Cil.typeOf e) in
      Expr (Esizeof ty, constInt32uns)
  | SizeOfStr str ->
      let n = coqint_of_camlint (Int32.of_int(String.length str)) in
      Expr (Econst_int n, constInt32uns)
  | AlignOf t ->
      unsupported "GCC `alignof' construct"
  | AlignOfE e ->
      unsupported "GCC `alignof' construct"
  | UnOp (uop, e, t) ->
      convertUnop uop e t
  | BinOp (bop, e1, e2, t) ->
      convertBinop bop e1 e2 t
  | CastE (t, e) ->
      processCast t e
  | AddrOf lv ->
      let (Expr (_, t)) as e = convertLval lv in
      Expr (Eaddrof e, Tpointer t)
  | StartOf lv ->
      (* convert an array into a pointer to the beginning of the array *)
      match Cil.unrollType (Cil.typeOfLval lv) with
	| TArray (t, _, _) ->
	    let t' = convertTyp t in
	    let tPtr = Tpointer t' in
	    let e = convertLval lv in
	      (* array A of type T replaced by (T* )A *)
	      Expr (Ecast (tPtr, e), tPtr)
	| _ -> internal_error "convertExp: StartOf applied to a \
                                         lvalue whose type is not an array"


(** Convert a [Cil.lval] into a [CabsCoq.expression] *)
and convertLval lv =
  (* convert the offset of the lvalue *)
  let rec processOffset ((Expr (_, t)) as e) = function
    | NoOffset -> e
    | Field (f, ofs) ->
	begin match t with
	  | Tstruct(id, fList) ->
	      begin try
		let idf = intern_string f.fname in
		let t' = unrollType id t (getFieldType idf fList) in
                  processOffset (Expr (Efield (e, idf), t')) ofs
	      with Not_found ->
		internal_error "processOffset: no such struct field"
	      end
	  | Tunion(id, fList) ->
	      begin try
		let idf = intern_string f.fname in
		let t' = unrollType id t (getFieldType idf fList) in
		  processOffset (Expr (Efield (e, idf), t')) ofs
	      with Not_found ->
		internal_error "processOffset: no such union field"
	      end
	  | _ ->
              internal_error "processOffset: Field on a non-struct nor union"
	end
    | Index (e', ofs) ->
	match t with
	  | Tarray (t', _) -> 
              let e'' = Ederef(Expr (Ebinop(Oadd, e, convertExp e'), t)) in
              processOffset (Expr (e'', t')) ofs
	  | _ -> internal_error "processOffset: Index on a non-array"
  in
    (* convert the lvalue *)
    match lv with
      | (Var v, ofs) ->
          check_builtin v.vname;
	  let id = intern_string v.vname in
            processOffset (Expr (Evar id, convertTyp v.vtype)) ofs
      | (Mem e, ofs) ->
	  match Cil.unrollType (Cil.typeOf e) with
	    | TPtr (t, _) -> let e' = Ederef (convertExp e) in
                               processOffset (Expr (e', convertTyp t)) ofs
	    | _ -> internal_error "convertLval: Mem on a non-pointer"
	 

(** Convert a [(Cil.string * Cil.typ * Cil.attributes)] list
    into a [typelist] *)
and processParamsT convert = function
  | [] -> Tnil
  | (_, t, _) :: l ->
      let t' = convert t in
	match t' with
	  | Tstruct _ | Tunion _ ->
              unsupported "function parameter of struct or union type"
	  | _ -> Tcons (t', processParamsT convert l)


(** Convert a [Cil.typ] into a [coq_type] *)
and convertTypGen env = function
  | TVoid _ -> Tvoid
  | TInt (k, _) -> let (x, y) = convertIkind k in Tint (x, y)
  | TFloat (k, _) -> Tfloat (convertFkind k)
  | TPtr (TComp(c, _), _) when List.mem c.ckey env ->
      Tcomp_ptr (intern_string (Cil.compFullName c))
  | TPtr (t, _) -> Tpointer (convertTypGen env t)
  | TArray (t, eOpt, _) ->
      begin match eOpt with
	| None ->
            warning "array type of unspecified size";
            Tarray (convertTypGen env t, coqint_of_camlint 0l)
	| Some e ->
            match Cil.constFold true e with
            | Const (CInt64 (i64, _, _)) ->
                Tarray (convertTypGen env t,
                        coqint_of_camlint (Int64.to_int32 i64))
            | _ -> unsupported "size of array type not an integer constant"
      end
  | TFun (t, argListOpt, vArg, _) ->
      if vArg then unsupported "variadic function type";
      let argList =
        match argListOpt with
          | None -> unsupported "un-prototyped function type"
          | Some l -> l
      in
      let t' = convertTypGen env t in
      begin match t' with
        | Tstruct _ | Tunion _ -> 
            unsupported "return type is a struct or union"
        | _ -> Tfunction (processParamsT (convertTypGen env) argList, t')
      end
  | TNamed (tinfo, _) -> convertTypGen env tinfo.ttype
  | TComp (c, _) ->
      let rec convertFieldList = function
        | [] -> Fnil
        | {fname=str; ftype=t} :: rem ->
            let idf = intern_string str in
            let t' = convertTypGen (c.ckey :: env) t in
            Fcons(idf, t', convertFieldList rem) in
      let fList = convertFieldList c.cfields in
      let id = intern_string (Cil.compFullName c) in
      if c.cstruct then Tstruct(id, fList) else Tunion(id, fList)
  | TEnum _ -> constInt32   (* enum constants are integers *)
  | TBuiltin_va_list _ -> unsupported "GCC `builtin va_list' type"

and convertTyp ty = convertTypGen [] ty

(** Convert a [Cil.varinfo] into a pair [(ident * coq_type)] *)
let convertVarinfo v =
  updateLoc(v.vdecl);
  let id = intern_string v.vname in
    Datatypes.Coq_pair (id, convertTyp v.vtype)


(** Convert a [Cil.varinfo] into a pair [(ident * coq_type)]
    (fail if the variable is of type struct or union) *)
let convertVarinfoParam v =
  updateLoc(v.vdecl);
  let id = intern_string v.vname in
  let t' = convertTyp v.vtype in
    match t' with
      | Tstruct _ | Tunion _ ->
          unsupported "function parameter of struct or union type"
      | _ -> Datatypes.Coq_pair (id, t')


(** Convert a [Cil.exp] which has a function type into a [CabsCoq.expr]
    (used only to translate function calls) *)
let convertExpFuncall e eList =
  match typeOf e with
  | TFun (res, argListOpt, vArg, _) ->
      begin match argListOpt, vArg with
      | Some argList, false ->
          (* Prototyped, non-variadic function *)
          if List.length argList <> List.length eList then
            internal_error "convertExpFuncall: wrong number of arguments";
          (convertExp e, processParamsE eList)
      | _, _ ->
          (* Variadic or unprototyped function: generate a call to
             a stub function with the appropriate number and types
             of arguments.  Works only if the function expression e
             is a global variable. *)
          let params = processParamsE eList in
          let fun_name =
            match e with
            | Lval(Var v, NoOffset) ->
                warning "working around a call to a variadic function";
                v.vname
            | _ ->
                unsupported "call to variadic function" in
          let rec typeOfExprList = function
            | [] -> Tnil
            | Expr (_, ty) :: rem -> Tcons (ty, typeOfExprList rem) in
          let targs = typeOfExprList params in
          let tres = convertTyp res in
          let (stub_fun_name, stub_fun_typ) =
            register_stub_function fun_name tres targs in
          (Expr(Evar(intern_string stub_fun_name), stub_fun_typ),
           params)
      end
  | _ -> internal_error "convertExpFuncall: not a function"

(** Auxiliaries for function calls *)

let makeFuncall1 tyfun (Expr(_, tlhs) as elhs) efun eargs =
  match tyfun with
  | TFun (t, _, _, _) ->
      let tres = convertTyp t in
      if tlhs = tres then
        Scall(Some elhs, efun, eargs)
      else begin
        let tmp = make_temp t in
        let elhs' = Expr(Evar tmp, tres) in
        Ssequence(Scall(Some elhs', efun, eargs),
                  Sassign(elhs, Expr(Ecast(tlhs, elhs'), tlhs)))
      end
  | _ -> internal_error "wrong type for function in call"

let makeFuncall2 tyfun tylhs elhs efun eargs =
  match elhs with
  | Expr(Evar _, _) ->
      makeFuncall1 tyfun elhs efun eargs
  | Expr(_, tlhs) ->
      let tmp = make_temp tylhs in
      let elhs' = Expr(Evar tmp, tlhs) in
      Ssequence(makeFuncall1 tyfun elhs' efun eargs,
                Sassign(elhs, elhs'))
                

(** Convert a [Cil.instr list] into a [CabsCoq.statement] *)
let rec processInstrList l =
  (* convert an instruction *)
  let convertInstr = function
    | Set (lv, e, loc) ->
	updateLoc(loc);
        begin match convertTyp (Cil.typeOf e) with
        | Tstruct _ | Tunion _ -> unsupported "struct or union assignment"
        | t -> Sassign (convertLval lv, convertExp e)
        end
    | Call (None, e, eList, loc) ->
	updateLoc(loc);
        let (efun, params) = convertExpFuncall e eList in
        Scall(None, efun, params)
    | Call (Some lv, e, eList, loc) ->
	updateLoc(loc);
        let (efun, params) = convertExpFuncall e eList in
        makeFuncall2 (Cil.typeOf e) (Cil.typeOfLval lv) (convertLval lv) efun params
    | Asm (_, _, _, _, _, loc) ->
	updateLoc(loc);
        unsupported "inline assembly"
  in
    (* convert a list of instructions *)
    match l with
      | [] -> Sskip
      | [s] -> convertInstr s
      | s :: l -> 
          let cs = convertInstr s in
          let cl = processInstrList l in
          Ssequence (cs, cl)


(** Convert a [Cil.stmt list] into a [CabsCoq.statement] *)
let rec processStmtList = function
  | [] -> Sskip
  | [s] -> convertStmt s
  | s :: l ->
      let cs = convertStmt s in
      let cl = processStmtList l in
      Ssequence (cs, cl)


(** Return the list of the constant expressions in a label list
    (return [None] if this is the default case)
    (fail if the constant expression is not of type integer) *)
and getCaseList lblList =
  match lblList with
    | [] -> Some []
    | Label (_, loc, _) :: l -> updateLoc(loc);  getCaseList l
    | Default loc :: _ -> updateLoc(loc);  None
    | Case (e, loc) :: l ->
	updateLoc(loc);
	begin match convertExp e with
	  | Expr (Econst_int n, _) ->
	      begin match getCaseList l with
		| None -> None
		| Some cl -> Some (n :: cl)
	      end
	  | _ -> internal_error "getCaseList: case label does not \
                                           reduce to an integer constant"
	end


(** Convert a list of integers into a [CabsCoq.lblStatementList] *)
and processCaseList cl s lrem =
  match cl with
    | [] -> internal_error "processCaseList: syntax error in switch statement"
    | [n] -> LScase (n, s, lrem)
    | n1 :: l -> LScase (n1, Sskip, processCaseList l s lrem)

      
(** Convert a [Cil.stmt list] which is the body of a Switch structure
    into a [CabsCoq.lblStatementList]
    (Pre-condition: all the Case labels are supposed to be at the same level,
    ie. no nested structures) *)
and processLblStmtList switchBody = function
  | [] -> LSdefault Sskip
  | [ls] ->
      let s = processStmtList (keepFrom ls switchBody) in
      begin match getCaseList ls.labels with
	| None -> LSdefault s
	| Some cl -> processCaseList cl s (LSdefault Sskip)
      end
  | ls :: ((ls' :: _) as l) ->
      if ls.labels = ls'.labels then processLblStmtList switchBody l
      else
	begin match getCaseList ls.labels with
	  | None -> unsupported "default case is not at the end of this `switch' statement"
	  | Some cl ->
	      let s = processStmtList (keepBetween ls ls' switchBody) in
	      let lrem = processLblStmtList switchBody l in
	        processCaseList cl s lrem
	end


(** Convert a [Cil.stmt] into a [CabsCoq.statement] *)
and convertStmt s =
  match s.skind with
    | Instr iList -> processInstrList iList
    | Return (eOpt, loc) ->
	updateLoc(loc);
        let eOpt' = match eOpt with
	  | None -> None
	  | Some e -> Some (convertExp e)
	in 
          Sreturn eOpt'
    | Goto (_, loc) ->
	updateLoc(loc);
        unsupported "`goto' statement"
    | Break loc ->
	updateLoc(loc);
	Sbreak
    | Continue loc ->
	updateLoc(loc);
	Scontinue
    | If (e, b1, b2, loc) ->
	updateLoc(loc);
        let e1 = processStmtList b1.bstmts in
        let e2 = processStmtList b2.bstmts in
	  Sifthenelse (convertExp e, e1, e2)
    | Switch (e, b, l, loc) ->
	updateLoc(loc);
        Sswitch (convertExp e, processLblStmtList b.bstmts l)
    | While (e, b, loc) ->
	updateLoc(loc);
        Swhile (convertExp e, processStmtList b.bstmts)
    | DoWhile (e, b, loc) ->
	updateLoc(loc);
        Sdowhile (convertExp e, processStmtList b.bstmts)
    | For (bInit, e, bIter, b, loc) ->
	updateLoc(loc);
	let sInit = processStmtList bInit.bstmts in
	let e' = convertExp e in
	let sIter = processStmtList bIter.bstmts in
	  Sfor (sInit, e', sIter, processStmtList b.bstmts)
    | Block b -> processStmtList b.bstmts
    | TryFinally (_, _, loc) ->
	updateLoc(loc);
        unsupported "`try'...`finally' statement"
    | TryExcept (_, _, _, loc) ->
	updateLoc(loc);
        unsupported "`try'...`except' statement"

(** Convert a [Cil.GFun] into a pair [(ident * coq_fundecl)] *)
let convertGFun fdec =
  current_function := Some fdec;
  let v = fdec.svar in
  let ret = match v.vtype with
    | TFun (t, _, vArg, _) ->
	if vArg then unsupported "variadic function";
        begin match convertTyp t with
	| Tstruct _ | Tunion _ -> 
            unsupported "return value of struct or union type"
	| t' -> t'
        end
    | _ -> internal_error "convertGFun: incorrect function type"
  in
  let s = processStmtList fdec.sbody.bstmts in   (* function body -- do it first because of generated temps *)
  let args = List.map convertVarinfoParam fdec.sformals in   (* parameters*)
  let varList = List.map convertVarinfo fdec.slocals in   (* local vars *)
  if v.vname = "main" then begin
    match ret with
    | Tint(_, _) -> ()
    | _ -> updateLoc v.vdecl;
           unsupported "the return type of main() must be an integer type"
  end;
  current_function := None;
  let id = intern_string v.vname in
  Hashtbl.add varinfo_atom id v;
  Datatypes.Coq_pair
    (id,
     Internal { fn_return=ret; fn_params=args; fn_vars=varList; fn_body=s })

(** Auxiliary for [convertInit] *)

let rec initDataLen accu = function
  | [] -> accu
  | i1 :: il ->
      let sz = match i1 with
      | Init_int8 _ -> 1l
      | Init_int16 _ -> 2l
      | Init_int32 _ -> 4l
      | Init_float32 _ -> 4l
      | Init_float64 _ -> 8l
      | Init_space n -> camlint_of_z n
      | Init_pointer _ -> 4l in
      initDataLen (Int32.add sz accu) il

(** Convert a [Cil.init] into a list of [AST.init_data] prepended to
    the given list [k].  Result is in reverse order. *)

(* Cil.constFold does not reduce floating-point operations.
   We treat here those that appear naturally in initializers. *)

type init_constant =
  | ICint of int64 * intsize
  | ICfloat of float * floatsize
  | ICstring of string
  | ICnone

let rec extract_constant e =
  match e with
  | Const (CInt64(n, ikind, _)) ->
      ICint(n, fst (convertIkind ikind))
  | Const (CReal(n, fkind, _)) ->
      ICfloat(n, convertFkind fkind)
  | Const (CStr s) ->
      ICstring s
  | CastE (ty, e1) ->
      begin match extract_constant e1, convertTyp ty with
      | ICfloat(n, _), Tfloat sz ->
          ICfloat(n, sz)
      | ICint(n, _), Tfloat sz ->
          ICfloat(Int64.to_float n, sz)
      | ICint(n, sz), Tpointer _ ->
          ICint(n, sz)
      | ICstring s, (Tint _ | Tpointer _) ->
          ICstring s
      | _, _ ->
          ICnone
      end
  | UnOp (Neg, e1, _) ->
      begin match extract_constant e1 with
      | ICfloat(n, sz) -> ICfloat(-. n, sz)
      | _ -> ICnone
      end
  | _ -> ICnone

let init_data_of_string s =
  let id = ref [] in
  let enter_char c =
    let n = coqint_of_camlint(Int32.of_int(Char.code c)) in
    id := Init_int8 n :: !id in
  enter_char '\000';
  for i = String.length s - 1 downto 0 do enter_char s.[i] done;
  !id

let convertInit init =
  let k = ref []
  and pos = ref 0 in
  let emit size datum =
    k := datum :: !k;
    pos := !pos + size in
  let emit_space size =
    emit size (Init_space (z_of_camlint (Int32.of_int size))) in
  let check_align size =
    assert (!pos land (size - 1) = 0) in
  let align size =
    let n = !pos land (size - 1) in
    if n > 0 then emit_space (size - n) in

  let rec cvtInit init =
    match init with
    | SingleInit e ->
        begin match extract_constant(Cil.constFold true e) with
        | ICint(n, I8) ->
            let n' = coqint_of_camlint (Int64.to_int32 n) in
            emit 1 (Init_int8 n')
        | ICint(n, I16) ->
            check_align 2;
            let n' = coqint_of_camlint (Int64.to_int32 n) in
            emit 2 (Init_int16 n')
        | ICint(n, I32) ->
            check_align 4;
            let n' = coqint_of_camlint (Int64.to_int32 n) in
            emit 4 (Init_int32 n')
        | ICfloat(n, F32) ->
            check_align 4;
            emit 4 (Init_float32 n)
        | ICfloat(n, F64) ->
            check_align 8;
            emit 8 (Init_float64 n)
        | ICstring s ->
            check_align 4;
            emit 4 (Init_pointer(init_data_of_string s))
        | ICnone ->
            unsupported "this kind of expression is not supported in global initializers"
      end
  | CompoundInit(ty, data) ->
      let ty' = convertTyp ty in
      let sz = Int32.to_int (camlint_of_z (Csyntax.sizeof ty')) in
      let pos0 = !pos in
      Cil.foldLeftCompoundAll
          ~doinit: cvtCompoundInit
          ~ct: ty
          ~initl: data
          ~acc: ();
      let pos1 = !pos in
      assert (pos1 <= pos0 + sz);
      if pos1 < pos0 + sz then emit_space (pos0 + sz - pos1)

  and cvtCompoundInit ofs init ty () =
    let ty' = convertTyp ty in
    let al = Int32.to_int (camlint_of_z (Csyntax.alignof ty')) in
    align al;
    cvtInit init

  in cvtInit init; List.rev !k

(** Convert a [Cil.initinfo] into a list of [AST.init_data] *)

let convertInitInfo ty info =
  match info.init with
  | None -> 
      [ Init_space(Csyntax.sizeof (convertTyp ty)) ]
  | Some init ->
      convertInit init

(** Convert a [Cil.GVar] into a global variable definition *)

let convertGVar v i =
  updateLoc(v.vdecl);
  let id = intern_string v.vname in
  Hashtbl.add varinfo_atom id v;
  Datatypes.Coq_pair (Datatypes.Coq_pair(id, convertInitInfo v.vtype i),
                      convertTyp v.vtype)


(** Convert a [Cil.GVarDecl] into a global variable declaration *)

let convertExtVar v =
  updateLoc(v.vdecl);
  let id = intern_string v.vname in
  Hashtbl.add varinfo_atom id v;
  Datatypes.Coq_pair (Datatypes.Coq_pair(id, []),
                      convertTyp v.vtype)

(** Convert a [Cil.GVarDecl] into an external function declaration *)

let convertExtFun v =
  updateLoc(v.vdecl);
  match convertTyp v.vtype with
  | Tfunction(args, res) ->
      let id = intern_string v.vname in
      Hashtbl.add varinfo_atom id v;
      Datatypes.Coq_pair (id, External(id, args, res))
  | _ ->
      assert false

(** Convert a [Cil.global list] into a pair whose first component,
    of type [(ident * coq_function) coqlist], represents the definitions of the
    functions and the second component, of type [(ident * coq_type) coqlist],
    the definitions of the global variables of the program *)
let rec processGlobals = function
  | [] -> ([], [])
  | g :: l ->
	match g with
	  | GType _ -> processGlobals l (* typedefs are unrolled... *)
	  | GCompTag _ -> processGlobals l 
	  | GCompTagDecl _ -> processGlobals l 
	  | GEnumTag _ -> processGlobals l (* enum constants are folded... *)
	  | GEnumTagDecl _ -> processGlobals l
	  | GVarDecl (v, loc) ->
	      updateLoc(loc);
              (* Functions become external declarations,
                 variadic and unprototyped functions are skipped,
                 variables become uninitialized variables *)
              begin match Cil.unrollType v.vtype with
              | TFun (tres, Some targs, false, _) ->
                  let fn = convertExtFun v in
                  let (fList, vList) = processGlobals l in
                  (fn :: fList, vList)
              | TFun (tres, _, _, _) ->
                  processGlobals l
              | _ ->
                  let var = convertExtVar v in
                  let (fList, vList) = processGlobals l in
                  (fList, var :: vList)
              end
	  | GVar (v, init, loc) ->
	      updateLoc(loc);
              let var = convertGVar v init in
              let (fList, vList) = processGlobals l in
              (fList, var :: vList)
	  | GFun (fdec, loc) ->
	      updateLoc(loc);
              let fn = convertGFun fdec in
              let (fList, vList) = processGlobals l in
              (fn :: fList, vList)
	  | GAsm (_, loc) ->
	      updateLoc(loc);
              unsupported "inline assembly"
	  | GPragma (_, loc) ->
	      updateLoc(loc);
              warning "#pragma directive ignored";
              processGlobals l
	  | GText _ -> processGlobals l (* comments are ignored *)

(** Eliminate forward declarations of globals that are defined later *)

let cleanupGlobals globs =
  let defined =
    List.fold_right
      (fun g def ->
        match g with GVar (v, init, loc) -> v.vname :: def
                   | GFun (fdec, loc) -> fdec.svar.vname :: def
                   | _ -> def)
      globs [] in
  List.filter
    (function GVarDecl(v, loc) -> not(List.mem v.vname defined)
            | g -> true)
    globs

(** Convert a [Cil.file] into a [CabsCoq.program] *)
let convertFile f =
  stringNum := 0;
  Hashtbl.clear varinfo_atom;
  Hashtbl.clear stringTable;
  Hashtbl.clear stub_function_table;
  let (funList, defList) = processGlobals (cleanupGlobals f.globals) in
  let funList' = declare_stub_functions funList in
  let funList'' = match f.globinit with
    | Some fdec -> convertGFun fdec :: funList'
    | None -> funList' in
  let defList' = globals_for_strings defList in
  { AST.prog_funct = funList'';
    AST.prog_vars = defList';
    AST.prog_main = intern_string "main" }


(*-----------------------------------------------------------------------*)
end

(* Extracting information about global variables from their atom *)

let atom_is_static a =
  try
    let v = Hashtbl.find varinfo_atom a in
    v.vstorage = Static
  with Not_found ->
    false

let atom_is_readonly a =
  try
    let v = Hashtbl.find varinfo_atom a in
    let a = typeAttrs v.vtype in
    if hasAttribute "volatile" a then false else
    if hasAttribute "const" a then true else
    match Cil.unrollType v.vtype with
    | TArray(ty, _, _) ->
        let a' = typeAttrs ty in
        hasAttribute "const" a' && not (hasAttribute "volatile" a')
    | _ -> false
  with Not_found ->
    false

