(**************************************************************************
CIL -> CabsCoq translator
**************************************************************************)

open Cil
open Camlcoq
open AST
open Csyntax




module type TypeSpecifierTranslator =
  sig
    val convertIkind: Cil.ikind -> (intsize * signedness) option
    val convertFkind: Cil.fkind -> floatsize option
  end





module Make(TS: TypeSpecifierTranslator) = struct
(*-----------------------------------------------------------------------*)


(** Exception raised when an unsupported feature is encountered *)
exception Unsupported of string


(** Pre-defined constants *)
let constInt32 = Tint (I32, Signed)
let constInt32uns = Tint (I32, Unsigned)
let const0 = Expr (Econst_int (coqint_of_camlint Int32.zero), constInt32)


(** Identifiers for struct and union fields *)
let fieldTable = Hashtbl.create 47   (* hash-table *)
let fieldNum = ref Int32.one   (* identifier of the next field *)


(** Other global variables *)
let currentLocation = ref Cil.locUnknown
let mainFound = ref false
let currentGlobalPrefix = ref ""
let stringNum = ref 0   (* number of next global for string literals *)
let stringTable = Hashtbl.create 47

(** ** Functions related to [struct]s and [union]s *)

(** Return a unique integer corresponding to a [struct] field *)
let ident_of_string str =
  try Hashtbl.find fieldTable str
  with Not_found -> let id = positive_of_camlint !fieldNum in
                      Hashtbl.add fieldTable str id;
                      fieldNum := Int32.succ !fieldNum;
                      id

(* Return the type of a [struct] field *)
let rec getFieldType f = function
  | Fnil -> raise Not_found
  | Fcons(idf, t, rem) -> if idf = f then t else getFieldType f rem



(** ** Some functions over lists *)

(** Apply [f] to each element of the OCaml list [l]
    and build a Coq list with the results returned by [f] *)
let rec map_coqlist f l = match l with
  | [] -> CList.Coq_nil
  | a :: b -> CList.Coq_cons (f a, map_coqlist f b)
  
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

(** Reverse-append over Coq lists *)

let rec revappend l1 l2 =
  match l1 with
  | CList.Coq_nil -> l2
  | CList.Coq_cons(hd, tl) -> revappend tl (CList.Coq_cons (hd, l2))

(** ** Functions used to handle locations *)

(** Update the current location *)
let updateLoc loc =
  currentLocation := loc

(** Convert the current location into a string *)
let currentLoc() =
  match !currentLocation with { line=l; file=f } ->
    f ^ ":" ^ (if l = -1 then "?" else string_of_int l) ^ ": "

(** ** Functions used to handle string literals *)
let name_for_string_literal s =
  try
    Hashtbl.find stringTable s
  with Not_found ->
    incr stringNum;
    let symbol_name =
      Printf.sprintf "_%s__stringlit_%d"
                     !currentGlobalPrefix !stringNum in
    let symbol_ident = intern_string symbol_name in
    Hashtbl.add stringTable s symbol_ident;
    symbol_ident

let typeStringLiteral s =
  Tarray(Tint(I8, Unsigned), z_of_camlint(Int32.of_int(String.length s + 1)))

let global_for_string s id =
  let init = ref CList.Coq_nil in
  let add_char c =
    init := CList.Coq_cons(
       AST.Init_int8(coqint_of_camlint(Int32.of_int(Char.code c))),
       !init) in
  add_char '\000';
  for i = String.length s - 1 downto 0 do add_char s.[i] done;
  Datatypes.Coq_pair(Datatypes.Coq_pair(id, !init), typeStringLiteral s)

let globals_for_strings globs =
  Hashtbl.fold
    (fun s id l -> CList.Coq_cons(global_for_string s id, l))
    stringTable globs

(** ** Translation functions *)

(** Convert a [Cil.ikind] into a pair [(intsize * signedness)] *)
let convertIkind ik =
  match TS.convertIkind ik with
    | Some p -> p
    | None -> raise (Unsupported (currentLoc() ^ "integer type specifier"))


(** Convert a [Cil.fkind] into a [floatsize] *)
let convertFkind fk =
  match TS.convertFkind fk with
    | Some fs -> fs
    | None -> raise (Unsupported
		       (currentLoc() ^ "floating-point type specifier"))


(** Convert a [Cil.constant] into a [CabsCoq.expr] *)
let rec convertConstant = function
  | CInt64 (i64, _, _) ->
      let i = coqint_of_camlint (Int64.to_int32 i64) in
      Expr (Econst_int i, constInt32)
  | CStr s ->
      let symb = name_for_string_literal s in
      Expr (Evar symb, typeStringLiteral s)
  | CWStr _ ->
      raise (Unsupported (currentLoc() ^ "wide string literal"))
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
    else failwith (currentLoc() ^ "processCast: illegal cast")


(** Convert a [Cil.exp list] into an [CamlCoq.exprlist] *)
and processParamsE = function
  | [] -> Enil
  | e :: l ->
      let (Expr (_, t)) as e' = convertExp e in
	match t with
	  | Tstruct _ | Tunion _ -> raise (Unsupported (currentLoc() ^ 
                                 "function parameter of type struct or union"))
	  | _ -> Econs (e', processParamsE l)


(** Convert a [Cil.exp] into a [CabsCoq.expr] *)
and convertExp = function
  | Const c                -> convertConstant c
  | Lval lv                -> convertLval lv
  | SizeOf t               -> Expr (Esizeof (convertTyp t), constInt32uns)
  | SizeOfE e              -> let ty = convertTyp (Cil.typeOf e) in
                                Expr (Esizeof ty, constInt32uns)
  | SizeOfStr str          -> raise (Unsupported
				   (currentLoc() ^ "size of a string literal"))
  | AlignOf t              -> raise (Unsupported
				    (currentLoc() ^ "GCC alignment directive"))
  | AlignOfE e             -> raise (Unsupported
				    (currentLoc() ^ "GCC alignment directive"))
  | UnOp (uop, e, t)       -> convertUnop uop e t
  | BinOp (bop, e1, e2, t) -> convertBinop bop e1 e2 t
  | CastE (t, e)           -> processCast t e
  | AddrOf lv              -> let (Expr (_, t)) as e = convertLval lv in
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
(*
	      (* array A replaced by &(A[0]) *)
	      Expr (Eaddrof (Expr (Eindex (e, const0), t')), tPtr)
*)		
	| _ -> failwith (currentLoc() ^ "convertExp: StartOf applied to a \
                                         lvalue whose type is not an array")


(** Convert a [Cil.lval] into a [CabsCoq.expression] *)
and convertLval lv =
  (* convert the offset of the lvalue *)
  let rec processOffset ((Expr (_, t)) as e) = function
    | NoOffset -> e
    | Field (f, ofs) ->
	begin match t with
	  | Tstruct fList ->
	      begin try
		let idf = ident_of_string f.fname in
		let t' = getFieldType idf fList in
                  processOffset (Expr (Efield (e, idf), t')) ofs
	      with Not_found ->
		failwith (currentLoc() ^ "processOffset: no such struct field")
	      end
	  | Tunion fList ->
	      begin try
		let idf = ident_of_string f.fname in
		let t' = getFieldType idf fList in
		  processOffset (Expr (Efield (e, idf), t')) ofs
	      with Not_found ->
		failwith (currentLoc() ^ "processOffset: no such union field")
	      end
	  | _ -> failwith
	      (currentLoc() ^ "processOffset: Field on a non-struct nor union")
	end
    | Index (e', ofs) ->
	match t with
	  | Tarray (t', _) -> let e'' = Eindex (e, convertExp e') in
                                processOffset (Expr (e'', t')) ofs
	  | _ -> failwith
	      (currentLoc() ^ "processOffset: Index on a non-array")
  in
    (* convert the lvalue *)
    match lv with
      | (Var v, ofs) ->
	  let id = intern_string v.vname in
            processOffset (Expr (Evar id, convertTyp v.vtype)) ofs
      | (Mem e, ofs) ->
	  match Cil.unrollType (Cil.typeOf e) with
	    | TPtr (t, _) -> let e' = Ederef (convertExp e) in
                               processOffset (Expr (e', convertTyp t)) ofs
	    | _ -> failwith
		(currentLoc() ^ "convertLval: Mem on a non-pointer")
	 

(** Convert a [(Cil.string * Cil.typ * Cil.attributes)] list
    into a [typelist] *)
and processParamsT convert = function
  | [] -> Tnil
  | (_, t, _) :: l ->
      let t' = convert t in
	match t' with
	  | Tstruct _ | Tunion _ -> raise (Unsupported (currentLoc() ^ 
                                 "function parameter of type struct or union"))
	  | _ -> Tcons (t', processParamsT convert l)


(** Convert a [Cil.typ] into a [coq_type] *)
and convertTyp = function
  | TVoid _ -> Tvoid
  | TInt (k, _) -> let (x,y) = convertIkind k in Tint (x, y)
  | TFloat (k, _) -> Tfloat (convertFkind k)
  | TPtr (t, _) -> Tpointer (convertTyp t)
  | TArray (t, eOpt, _) ->
      begin match eOpt with
	| Some (Const (CInt64 (i64, _, _))) ->
	    Tarray (convertTyp t, coqint_of_camlint (Int64.to_int32 i64))
	| Some _ -> raise (Unsupported
		 (currentLoc() ^ "size of array type not an integer constant"))
	| None -> raise (Unsupported
			   (currentLoc() ^ "array type of unspecified size"))
      end
  | TFun (t, argListOpt, vArg, _) ->
      (* Treat unprototyped functions as 0-argument functions,
         and treat variadic functions as fixed-arity functions.
         We will get type mismatches at applications, which we
         compensate by casting the function type to the type
         derived from the types of the actual arguments. *)
      let argList =
        match argListOpt with
          | None -> []
          | Some l -> l
      in
      let t' = convertTyp t in
        begin match t' with
          | Tstruct _ | Tunion _ -> raise (Unsupported (currentLoc() ^ 
                                     "return value of type struct or union"))
          | _ -> Tfunction (processParamsT convertTyp argList, t')
        end
  | TNamed (tinfo, _) -> convertTyp tinfo.ttype
  | TComp (c, _) ->
      let rec convertFieldList = function
        | [] -> Fnil
        | {fname=str; ftype=t} :: rem ->
            let idf = ident_of_string str in
	    let t' = convertCompositeType [c.ckey] t in
            Fcons(idf, t', convertFieldList rem) in
      let fList = convertFieldList c.cfields in
      if c.cstruct then Tstruct fList else Tunion fList
  | TEnum _ -> constInt32   (* enum constants are integers *)
  | TBuiltin_va_list _ -> raise (Unsupported
				   (currentLoc() ^ "GCC built-in function"))

(** Convert a [Cil.typ] within a composite structure into a [coq_type] *)
and convertCompositeType env = function
  | TNamed (tinfo, _) -> convertCompositeType env tinfo.ttype
  | TPtr _ -> Tpointer Tvoid
  | TArray (ta, eOpt, _) ->
      begin match eOpt with
	| Some (Const (CInt64 (i64, _, _))) ->
	    let ta' = convertCompositeType env ta in
	      Tarray (ta', coqint_of_camlint (Int64.to_int32 i64))
	| Some _ -> raise (Unsupported
		 (currentLoc() ^ "size of array type not an integer constant"))
	| None -> raise (Unsupported
			   (currentLoc() ^ "array type of unspecified size"))
      end
  | TFun (t, argListOpt, vArg, _) ->
      if vArg then raise (Unsupported (currentLoc() ^ "variadic function"))
      else
	let argList =
	  match argListOpt with
	    | None ->
		print_string ("Warning: " ^
				currentLoc() ^ "unknown function signature\n");
		[]
	    | Some l -> l
	in
        let convert = convertCompositeType env in
        let t' = convert t in
	  begin match t' with
	    | Tstruct _ | Tunion _ -> raise (Unsupported (currentLoc() ^ 
                                       "return value of type struct or union"))
	    | _ -> Tfunction (processParamsT convert argList, t')
	  end
  | TComp (c, _) ->
      if List.mem c.ckey env then
        failwith (currentLoc() ^ 
                  "convertCompositeType: illegal recursive structure");
      let rec convertFieldList = function
        | [] -> Fnil
        | {fname=str; ftype=t} :: rem ->
            let idf = ident_of_string str in
	    let t' = convertCompositeType (c.ckey :: env) t in
            Fcons(idf, t', convertFieldList rem) in
      let fList = convertFieldList c.cfields in
      if c.cstruct then Tstruct fList else Tunion fList
  | t -> convertTyp t


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
      | Tstruct _ | Tunion _ -> raise (Unsupported (currentLoc() ^ 
                                 "function parameter of type struct or union"))
      | _ -> Datatypes.Coq_pair (id, t')


(** Convert a [Cil.exp] which has a function type into a [CabsCoq.expr]
    (used only to translate function calls) *)
let convertExpFuncall e tfun eList =
  match tfun with
    | TFun (t, argListOpt, vArg, _) ->
	let params = processParamsE eList in
	let (Expr (efun, tfun)) as e' = convertExp e in
	  begin match argListOpt, vArg with
          | Some argList, false ->
              if List.length argList = List.length eList then (e', params)
              else failwith
              (currentLoc() ^ "convertExpFuncall: wrong number of arguments")
          | _, _ ->
            (* For variadic or unprototyped functions, we synthesize the
               "real" type of the function from that of the actual
               arguments, and insert a cast around e'. *)
            begin match tfun with
            | Tfunction (_, tret) ->
                let rec typeOfExprList = function
                  | Enil -> Tnil
                  | Econs (Expr (_, ty), rem) ->
                      Tcons (ty, typeOfExprList rem) in
                let tfun = Tfunction (typeOfExprList params, tret) in
                (Expr (Ecast(tfun, e'), tfun), params)
            | _ -> failwith
                  (currentLoc() ^ "convertExpFuncall: incorrect function type")
            end
	  end
    | _ -> failwith (currentLoc() ^ "convertExpFuncall: not a function")


(** Convert a [Cil.instr list] into a [CabsCoq.statement] *)
let rec processInstrList l =
  (* convert an instruction *)
  let convertInstr = function
    | Set (lv, e, loc) ->
	updateLoc(loc);
        begin match convertTyp (Cil.typeOf e) with
        | Tstruct _ | Tunion _ -> raise (Unsupported (currentLoc() ^ 
                                               "struct or union assignment"))
        | t -> Sassign (convertLval lv, convertExp e)
        end
    | Call (lvOpt, e, eList, loc) ->
	updateLoc(loc);
	begin match Cil.unrollType (Cil.typeOf e) with
	  | TFun (t, _, _, _) as tfun ->
	      let t' = convertTyp t in
	      let (efun, params) = convertExpFuncall e tfun eList in
	      let e' = Expr (Ecall (efun, params), t') in
		begin match lvOpt with
		  | None -> Sexpr e'
		  | Some lv ->
		      let (Expr (_, tlv)) as elv = convertLval lv in
			begin match tlv with
			  | Tstruct _ | Tunion _ -> raise (Unsupported
				 (currentLoc() ^ "struct or union assignment"))
			  | _ ->
			      if tlv = t' then
				Sassign (elv, e')
			      else
				(* a cast must be inserted *)
				if compatibleTypes tlv t' then
				  Sassign (elv,
				           Expr (Ecast (tlv, e'), tlv))
				else failwith
				  (currentLoc() ^ "processCast: illegal cast")
			end
		end
	  | _ -> failwith (currentLoc() ^ "convertInstr: illegal call")
	end
    | Asm (_, _, _, _, _, loc) ->
	updateLoc(loc);
        raise (Unsupported (currentLoc() ^ "inline assembly"))
  in
    (* convert a list of instructions *)
    match l with
      | [] -> Sskip
      | [s] -> convertInstr s
      | s :: l -> Ssequence (convertInstr s, processInstrList l)


(** Convert a [Cil.stmt list] into a [CabsCoq.statement] *)
let rec processStmtList = function
  | [] -> Sskip
  | [s] -> convertStmt s
  | s :: l -> Ssequence (convertStmt s, processStmtList l)


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
	  | _ -> failwith (currentLoc() ^ "getCaseList: case label does not \
                                           reduce to an integer constant")
	end


(** Convert a list of integers into a [CabsCoq.lblStatementList] *)
and processCaseList cl s lrem =
  match cl with
    | [] -> failwith
	(currentLoc() ^ "processCaseList: syntax error in switch statement")
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
	  | None -> raise (Unsupported (currentLoc() ^ 
		     "default case is not at the end of the switch structure"))
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
	  | None -> Datatypes.None
	  | Some e -> Datatypes.Some (convertExp e)
	in 
          Sreturn eOpt'
    | Goto (_, loc) ->
	updateLoc(loc);
        raise (Unsupported (currentLoc() ^ "goto statement"))
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
        raise (Unsupported (currentLoc() ^ "try...finally statement"))
    | TryExcept (_, _, _, loc) ->
	updateLoc(loc);
        raise (Unsupported (currentLoc() ^ "try...except statement"))


(** Convert a [Cil.GFun] into a pair [(ident * coq_fundecl)] *)
let convertGFun fdec =
  let v = fdec.svar in
  let ret = match v.vtype with
    | TFun (t, _, vArg, _) ->
	if vArg then raise (Unsupported (currentLoc() ^ "variadic function"))
	else
	  begin match convertTyp t with
	    | Tstruct _ | Tunion _ -> raise (Unsupported (currentLoc() ^ 
                                       "return value of type struct or union"))
	    | t' -> t'
	  end
    | _ -> failwith (currentLoc() ^ "convertGFun: incorrect function type")
  in
  let args = map_coqlist convertVarinfoParam fdec.sformals in   (* parameters*)
  let varList = map_coqlist convertVarinfo fdec.slocals in   (* local vars *)
  let s = processStmtList fdec.sbody.bstmts in   (* function body *)
    if v.vname = "main" then mainFound := true;
    Datatypes.Coq_pair
      (intern_string v.vname,
       Internal { fn_return=ret; fn_params=args; fn_vars=varList; fn_body=s })


(** Auxiliary for [convertInit] *)

let rec initDataLen accu = function
  | CList.Coq_nil -> accu
  | CList.Coq_cons(i1, il) ->
      let sz = match i1 with
      | Init_int8 _ -> 1l
      | Init_int16 _ -> 2l
      | Init_int32 _ -> 4l
      | Init_float32 _ -> 4l
      | Init_float64 _ -> 8l
      | Init_space n -> camlint_of_z n in
      initDataLen (Int32.add sz accu) il

(** Convert a [Cil.init] into a list of [AST.init_data] prepended to
    the given list [k]. *)

let rec convertInit init k =
  match init with
  | SingleInit e ->
      begin match Cil.constFold true e with
      | Const (CInt64(n, ikind, _)) ->
          begin match convertIkind ikind with
          | (I8, _) ->
               CList.Coq_cons(Init_int8 (coqint_of_camlint (Int64.to_int32 n)), k)
          | (I16, _) ->
               CList.Coq_cons(Init_int16 (coqint_of_camlint (Int64.to_int32 n)), k)
          | (I32, _) ->
               CList.Coq_cons(Init_int32 (coqint_of_camlint (Int64.to_int32 n)), k)
          end
      | Const (CReal(n, fkind, _)) ->
          begin match convertFkind fkind with
          | F32 ->
               CList.Coq_cons(Init_float32 n, k)
          | F64 ->
               CList.Coq_cons(Init_float64 n, k)
          end
      | _ ->
          raise (Unsupported (currentLoc() ^
                 "this kind of expression is not supported in global initializers"))
      end
  | CompoundInit(ty, data) ->
      let init =  (* in reverse order *)
        Cil.foldLeftCompoundAll
          ~doinit: (fun ofs init ty k -> convertInit init k)
          ~ct: ty
          ~initl: data
          ~acc: CList.Coq_nil in
      (* For struct or union, pad to size of type *)
      begin match Cil.unrollType ty with
      | TComp _ ->
          let act_len = initDataLen 0l init in
          let exp_len = camlint_of_z (Csyntax.sizeof (convertTyp ty)) in
          assert (act_len <= exp_len);
          let init' = 
            if act_len < exp_len
            then let spc = z_of_camlint (Int32.sub exp_len act_len) in
                 CList.Coq_cons(Init_space spc, init)
            else init in
          revappend init' k
      | _ ->
        revappend init k
      end

(** Convert a [Cil.initinfo] into a list of [AST.init_data] *)

let convertInitInfo ty info =
  match info.init with
  | None -> 
      CList.Coq_cons(Init_space(Csyntax.sizeof (convertTyp ty)), CList.Coq_nil)
  | Some init ->
      convertInit init CList.Coq_nil

(** Convert a [Cil.GVar] into a global variable definition *)

let convertGVar v i =
  updateLoc(v.vdecl);
  let id = intern_string v.vname in
  Datatypes.Coq_pair (Datatypes.Coq_pair(id, convertInitInfo v.vtype i),
                      convertTyp v.vtype)


(** Convert a [Cil.GVarDecl] into a global variable declaration *)

let convertExtVar v =
  updateLoc(v.vdecl);
  let id = intern_string v.vname in
  Datatypes.Coq_pair (Datatypes.Coq_pair(id, CList.Coq_nil),
                      convertTyp v.vtype)

(** Convert a [Cil.GVarDecl] into an external function declaration *)

let convertExtFun v =
  updateLoc(v.vdecl);
  match convertTyp v.vtype with
  | Tfunction(args, res) ->
      let id = intern_string v.vname in
      Datatypes.Coq_pair (id, External(id, args, res))
  | _ ->
      assert false

(** Convert a [Cil.global list] into a pair whose first component,
    of type [(ident * coq_function) coqlist], represents the definitions of the
    functions and the second component, of type [(ident * coq_type) coqlist],
    the definitions of the global variables of the program *)
let rec processGlobals = function
  | [] -> (CList.Coq_nil, CList.Coq_nil)
  | g :: l ->
      let (fList, vList) as rem = processGlobals l in
	match g with
	  | GType _ -> rem   (* typedefs are unrolled... *)
	  | GCompTag _ -> rem
	  | GCompTagDecl _ -> rem
	  | GEnumTag _ -> rem   (* enum constants are folded... *)
	  | GEnumTagDecl _ -> rem
	  | GVarDecl (v, loc) ->
	      updateLoc(loc);
              (* Functions become external declarations,
                 variables become uninitialized variables *)
              if Cil.isFunctionType v.vtype
              then (CList.Coq_cons (convertExtFun v, fList), vList)
              else (fList, CList.Coq_cons (convertExtVar v, vList))
	  | GVar (v, init, loc) ->
	      updateLoc(loc);
              (fList, CList.Coq_cons (convertGVar v init, vList))
	  | GFun (fdec, loc) ->
	      updateLoc(loc);
              (CList.Coq_cons (convertGFun fdec, fList), vList)
	  | GAsm (_, loc) ->
	      updateLoc(loc);
              raise (Unsupported (currentLoc() ^ "asm statement"))
	| GPragma (_, loc) ->
	    updateLoc(loc);
	    print_string ("Warning: " ^
			    currentLoc() ^ "pragma directive ignored\n");
	    rem
	| GText _ -> rem   (* comments are ignored *)

(** Eliminate forward declarations of globals that are defined later *)

let cleanupGlobals globs =
  let defined =
    List.fold_right
      (fun g def ->
        match g with GVar (v, init, loc) -> v.vname :: def
                   | _ -> def)
      globs [] in
  List.filter
    (function GVarDecl(v, loc) -> not(List.mem v.vname defined)
            | g -> true)
    globs

(** Convert a [Cil.file] into a [CabsCoq.program] *)
let convertFile f =
  currentGlobalPrefix :=
    Filename.chop_extension (Filename.basename f.fileName);
  stringNum := 0;
  Hashtbl.clear stringTable;
  let (funList, defList) = processGlobals (cleanupGlobals f.globals) in
  let funList' = match f.globinit with
    | Some fdec -> CList.Coq_cons (convertGFun fdec, funList)
    | None -> funList in
  let defList' = globals_for_strings defList in
(***
  if not !mainFound then   (* no main function *)
    print_string ("Warning: program has no main function! (you should \
                         probably have used ccomp's -nomain option)\n");
***)
  { AST.prog_funct = funList';
    AST.prog_vars = defList';
    AST.prog_main = intern_string "main" }


(*-----------------------------------------------------------------------*)
end

