(* MODIF: Loop constructor replaced by 3 constructors: While, DoWhile, For. *)

(* 
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)

(* A consistency checker for CIL *)
open Cil
module E = Errormsg
module H = Hashtbl
open Pretty


(* A few parameters to customize the checking *)
type checkFlags = 
    NoCheckGlobalIds   (* Do not check that the global ids have the proper 
                        * hash value *)

let checkGlobalIds = ref true

  (* Attributes must be sorted *)
type ctxAttr = 
    CALocal                             (* Attribute of a local variable *)
  | CAGlobal                            (* Attribute of a global variable *)
  | CAType                              (* Attribute of a type *)

let valid = ref true

let warn fmt =
  valid := false;
  Cil.warn fmt

let warnContext fmt =
  valid := false;
  Cil.warnContext fmt

let checkAttributes (attrs: attribute list) : unit = 
  let rec loop lastname = function
      [] -> ()
    | Attr(an, _) :: resta -> 
        if an < lastname then
          ignore (warn "Attributes not sorted");
        loop an resta
  in
  loop "" attrs


  (* Keep track of defined types *)
let typeDefs : (string, typ) H.t = H.create 117


  (* Keep track of all variables names, enum tags and type names *)
let varNamesEnv : (string, unit) H.t = H.create 117

  (* We also keep a map of variables indexed by id, to ensure that only one 
   * varinfo has a given id *)
let varIdsEnv: (int, varinfo) H.t = H.create 117

  (* And keep track of all varinfo's to check the uniqueness of the 
   * identifiers *)
let allVarIds: (int, varinfo) H.t = H.create 117

 (* Also keep a list of environments. We place an empty string in the list to 
  * mark the start of a local environment (i.e. a function) *)
let varNamesList : (string * int) list ref = ref []
let defineName s = 
  if s = "" then
    E.s (bug "Empty name\n"); 
  if H.mem varNamesEnv s then
    ignore (warn "Multiple definitions for %s\n" s);
  H.add varNamesEnv s ()

let defineVariable vi = 
  defineName vi.vname;
  varNamesList := (vi.vname, vi.vid) :: !varNamesList;
  (* Check the id *)
  if H.mem allVarIds vi.vid then
    ignore (warn "Id %d is already defined (%s)\n" vi.vid vi.vname);
  H.add allVarIds vi.vid vi;
  (* And register it in the current scope also *)
  H.add varIdsEnv vi.vid vi

(* Check that a varinfo has already been registered *)
let checkVariable vi = 
  try
    (* Check in the current scope only *)
    if vi != H.find varIdsEnv vi.vid then
      ignore (warnContext "varinfos for %s not shared\n" vi.vname);
  with Not_found -> 
    ignore (warn "Unknown id (%d) for %s\n" vi.vid vi.vname)


let startEnv () = 
  varNamesList := ("", -1) :: !varNamesList

let endEnv () = 
  let rec loop = function
      [] -> E.s (bug "Cannot find start of env")
    | ("", _) :: rest -> varNamesList := rest
    | (s, id) :: rest -> begin
        H.remove varNamesEnv s;
        H.remove varIdsEnv id;
        loop rest
    end
  in
  loop !varNamesList
    

    
(* The current function being checked *)
let currentReturnType : typ ref = ref voidType

(* A map of labels in the current function *)
let labels: (string, unit) H.t = H.create 17

(* A list of statements seen in the current function *)
let statements: stmt list ref = ref []

(* A list of the targets of Gotos *)
let gotoTargets: (string * stmt) list ref = ref []

(*** TYPES ***)
(* Cetain types can only occur in some contexts, so keep a list of context *)
type ctxType = 
    CTStruct                            (* In a composite type *)
  | CTUnion
  | CTFArg                              (* In a function argument type *)
  | CTFRes                              (* In a function result type *)
  | CTArray                             (* In an array type *)
  | CTPtr                               (* In a pointer type *)
  | CTExp                               (* In an expression, as the type of 
                                         * the result of binary operators, or 
                                         * in a cast *)
  | CTSizeof                            (* In a sizeof *)
  | CTDecl                              (* In a typedef, or a declaration *)

let d_context () = function
    CTStruct -> text "CTStruct"
  | CTUnion -> text "CTUnion"
  | CTFArg -> text "CTFArg"
  | CTFRes -> text "CTFRes"
  | CTArray -> text "CTArray"
  | CTPtr -> text "CTPtr"
  | CTExp -> text "CTExp"
  | CTSizeof -> text "CTSizeof"
  | CTDecl -> text "CTDecl"


(* Keep track of all tags that we use. For each tag remember also the info 
 * structure and a flag whether it was actually defined or just used. A 
 * forward declaration acts as a definition. *)
type defuse = 
    Defined (* We actually have seen a definition of this tag *)
  | Forward (* We have seen a forward declaration for it. This is done using 
             * a GType with an empty type name *)
  | Used    (* Only uses *)
let compUsed : (int, compinfo * defuse ref) H.t = H.create 117
let enumUsed : (string, enuminfo * defuse ref) H.t = H.create 117
let typUsed  : (string, typeinfo * defuse ref) H.t = H.create 117
 
(* For composite types we also check that the names are unique *)
let compNames : (string, unit) H.t = H.create 17
    

  (* Check a type *)
let rec checkType (t: typ) (ctx: ctxType) = 
  (* Check that it appears in the right context *)
  let rec checkContext = function
      TVoid _ -> ctx = CTPtr || ctx = CTFRes || ctx = CTDecl
    | TNamed (ti, a) -> checkContext ti.ttype
    | TArray _ -> 
        (ctx = CTStruct || ctx = CTUnion 
         || ctx = CTSizeof || ctx = CTDecl || ctx = CTArray || ctx = CTPtr)
    | TComp _ -> ctx <> CTExp 
    | _ -> true
  in
  if not (checkContext t) then 
    ignore (warn "Type (%a) used in wrong context. Expected context: %a"
              d_plaintype t d_context ctx);
  match t with
    (TVoid a | TBuiltin_va_list a) -> checkAttributes a
  | TInt (ik, a) -> checkAttributes a
  | TFloat (_, a) -> checkAttributes a
  | TPtr (t, a) -> checkAttributes a;  checkType t CTPtr

  | TNamed (ti, a) ->
      checkAttributes a;
      if ti.tname = "" then 
        ignore (warnContext "Using a typeinfo for an empty-named type\n");
      checkTypeInfo Used ti

  | TComp (comp, a) ->
      checkAttributes a;
      (* Mark it as a forward. We'll check it later. If we try to check it 
       * now we might encounter undefined types *)
      checkCompInfo Used comp


  | TEnum (enum, a) -> begin
      checkAttributes a;
      checkEnumInfo Used enum
  end

  | TArray(bt, len, a) -> 
      checkAttributes a;
      checkType bt CTArray;
      (match len with
        None -> ()
      | Some l -> begin
          let t = checkExp true l in
          match t with 
            TInt((IInt|IUInt), _) -> ()
          | _ -> E.s (bug "Type of array length is not integer")
      end)

  | TFun (rt, targs, isva, a) -> 
      checkAttributes a;
      checkType rt CTFRes;
      List.iter 
        (fun (an, at, aa) -> 
          checkType at CTFArg;
          checkAttributes aa) (argsToList targs)

(* Check that a type is a promoted integral type *)
and checkIntegralType (t: typ) = 
  checkType t CTExp;
  match unrollType t with
    TInt _ -> ()
  | _ -> ignore (warn "Non-integral type")

(* Check that a type is a promoted arithmetic type *)
and checkArithmeticType (t: typ) = 
  checkType t CTExp;
  match unrollType t with
    TInt _ | TFloat _ -> ()
  | _ -> ignore (warn "Non-arithmetic type")

(* Check that a type is a promoted boolean type *)
and checkBooleanType (t: typ) = 
  checkType t CTExp;
  match unrollType t with
    TInt _ | TFloat _ | TPtr _ -> ()
  | _ -> ignore (warn "Non-boolean type")


(* Check that a type is a pointer type *)
and checkPointerType (t: typ) = 
  checkType t CTExp;
  match unrollType t with
    TPtr _ -> ()
  | _ -> ignore (warn "Non-pointer type")


and typeMatch (t1: typ) (t2: typ) = 
  if typeSig t1 <> typeSig t2 then
    match unrollType t1, unrollType t2 with
    (* Allow free interchange of TInt and TEnum *)
      TInt (IInt, _), TEnum _ -> ()
    | TEnum _, TInt (IInt, _) -> ()

    | _, _ -> ignore (warn "Type mismatch:@!    %a@!and %a@!" 
                        d_type t1 d_type t2)

and checkCompInfo (isadef: defuse) comp = 
  let fullname = compFullName comp in
  try
    let oldci, olddef = H.find compUsed comp.ckey in
    (* Check that it is the same *)
    if oldci != comp then 
      ignore (warnContext "compinfo for %s not shared\n" fullname);
    (match !olddef, isadef with 
    | Defined, Defined -> 
        ignore (warnContext "Multiple definition of %s\n" fullname)
    | _, Defined -> olddef := Defined
    | Defined, _ -> ()
    | _, Forward -> olddef := Forward
    | _, _ -> ())
  with Not_found -> begin (* This is the first time we see it *)
    (* Check that the name is not empty *)
    if comp.cname = "" then 
      E.s (bug "Compinfo with empty name");
    (* Check that the name is unique *)
    if H.mem compNames fullname then
      ignore (warn "Duplicate name %s" fullname);
    (* Add it to the map before we go on *)
    H.add compUsed comp.ckey (comp, ref isadef);
    H.add compNames fullname ();
    (* Do not check the compinfo unless this is a definition. Otherwise you 
     * might run into undefined types. *)
    if isadef = Defined then begin
      checkAttributes comp.cattr;
      let fctx = if comp.cstruct then CTStruct else CTUnion in
      let rec checkField f =
        if not 
            (f.fcomp == comp &&  (* Each field must share the self cell of 
             * the host *)
             f.fname <> "") then
          ignore (warn "Self pointer not set in field %s of %s" 
                    f.fname fullname);
        checkType f.ftype fctx;
        (* Check the bitfields *)
        (match unrollType f.ftype, f.fbitfield with
        | TInt (ik, a), Some w -> 
            checkAttributes a;
            if w < 0 || w >= bitsSizeOf (TInt(ik, a)) then
              ignore (warn "Wrong width (%d) in bitfield" w)
        | _, Some w -> 
            ignore (E.error "Bitfield on a non integer type\n")
        | _ -> ());
        checkAttributes f.fattr
      in
      List.iter checkField comp.cfields
    end
  end


and checkEnumInfo (isadef: defuse) enum = 
  if enum.ename = "" then 
    E.s (bug "Enuminfo with empty name");
  try
    let oldei, olddef = H.find enumUsed enum.ename in
    (* Check that it is the same *)
    if oldei != enum then 
      ignore (warnContext "enuminfo for %s not shared\n" enum.ename);
    (match !olddef, isadef with 
      Defined, Defined -> 
        ignore (warnContext "Multiple definition of enum %s\n" enum.ename)
    | _, Defined -> olddef := Defined
    | Defined, _ -> ()
    | _, Forward -> olddef := Forward
    | _, _ -> ())
  with Not_found -> begin (* This is the first time we see it *)
    (* Add it to the map before we go on *)
    H.add enumUsed enum.ename (enum, ref isadef);
    checkAttributes enum.eattr;
    List.iter (fun (tn, _, _) -> defineName tn) enum.eitems;
  end

and checkTypeInfo (isadef: defuse) ti = 
  try
    let oldti, olddef = H.find typUsed ti.tname in
    (* Check that it is the same *)
    if oldti != ti then 
      ignore (warnContext "typeinfo for %s not shared\n" ti.tname);
    (match !olddef, isadef with 
      Defined, Defined -> 
        ignore (warnContext "Multiple definition of type %s\n" ti.tname)
    | Defined, Used -> ()
    | Used, Defined -> 
        ignore (warnContext "Use of type %s before its definition\n" ti.tname)
    | _, _ -> 
        ignore (warnContext "Bug in checkTypeInfo for %s\n" ti.tname))
  with Not_found -> begin (* This is the first time we see it *)
    if ti.tname = "" then
      ignore (warnContext "typeinfo with empty name");
    checkType ti.ttype CTDecl;
    (* Add it to the map before we go on *)
    H.add typUsed ti.tname (ti, ref isadef);
  end

(* Check an lvalue. If isconst then the lvalue appears in a context where 
 * only a compile-time constant can appear. Return the type of the lvalue. 
 * See the typing rule from cil.mli *)
and checkLval (isconst: bool) (lv: lval) : typ = 
  match lv with
    Var vi, off -> 
      checkVariable vi; 
      checkOffset vi.vtype off

  | Mem addr, off -> begin
      if isconst then
        ignore (warn "Memory operation in constant");
      let ta = checkExp false addr in
      match unrollType ta with
        TPtr (t, _) -> checkOffset t off
      | _ -> E.s (bug "Mem on a non-pointer")
  end

(* Check an offset. The basetype is the type of the object referenced by the 
 * base. Return the type of the lvalue constructed from a base value of right 
 * type and the offset. See the typing rules from cil.mli *)
and checkOffset basetyp : offset -> typ = function
    NoOffset -> basetyp
  | Index (ei, o) -> 
      checkExpType false ei intType; 
      begin
        match unrollType basetyp with
          TArray (t, _, _) -> checkOffset t o
        | t -> E.s (bug "typeOffset: Index on a non-array: %a" d_plaintype t)
      end

  | Field (fi, o) -> 
      (* Now check that the host is shared propertly *)
      checkCompInfo Used fi.fcomp;
      (* Check that this exact field is part of the host *)
      if not (List.exists (fun f -> f == fi) fi.fcomp.cfields) then
        ignore (warn "Field %s not part of %s" 
                  fi.fname (compFullName fi.fcomp));
      checkOffset fi.ftype o
        
and checkExpType (isconst: bool) (e: exp) (t: typ) =
  let t' = checkExp isconst e in (* compute the type *)
  if isconst then begin (* For initializers allow a string to initialize an 
                         * array of characters  *)
    if typeSig t' <> typeSig t then 
      match e, t with
      | _ -> typeMatch t' t
  end else
    typeMatch t' t

(* Check an expression. isconst specifies if the expression occurs in a 
 * context where only a compile-time constant can occur. Return the computed 
 * type of the expression *)
and checkExp (isconst: bool) (e: exp) : typ = 
  E.withContext 
    (fun _ -> dprintf "check%s: %a" 
        (if isconst then "Const" else "Exp") d_exp e)
    (fun _ ->
      match e with
      | Const(CInt64 (_, ik, _)) -> TInt(ik, [])
      | Const(CChr _) -> charType
      | Const(CStr s) -> charPtrType
      | Const(CWStr s) -> TPtr(!wcharType,[])
      | Const(CReal (_, fk, _)) -> TFloat(fk, [])
      | Const(CEnum (_, _, ei)) -> TEnum(ei, [])
      | Lval(lv) -> 
          if isconst then
            ignore (warn "Lval in constant");
          checkLval isconst lv

      | SizeOf(t) -> begin
          (* Sizeof cannot be applied to certain types *)
          checkType t CTSizeof;
          (match unrollType t with
            (TFun _ | TVoid _) -> 
              ignore (warn "Invalid operand for sizeof")
          | _ ->());
          uintType
      end
      | SizeOfE(e) ->
          (* The expression in a sizeof can be anything *)
          let te = checkExp false e in
          checkExp isconst (SizeOf(te))

      | SizeOfStr s -> uintType

      | AlignOf(t) -> begin
          (* Sizeof cannot be applied to certain types *)
          checkType t CTSizeof;
          (match unrollType t with
            (TFun _ | TVoid _) -> 
              ignore (warn "Invalid operand for sizeof")
          | _ ->());
          uintType
      end
      | AlignOfE(e) ->
          (* The expression in an AlignOfE can be anything *)
          let te = checkExp false e in
          checkExp isconst (AlignOf(te))

      | UnOp (Neg, e, tres) -> 
          checkArithmeticType tres; checkExpType isconst e tres; tres

      | UnOp (BNot, e, tres) -> 
          checkIntegralType tres; checkExpType isconst e tres; tres

      | UnOp (LNot, e, tres) -> 
          let te = checkExp isconst e in
          checkBooleanType te;
          checkIntegralType tres; (* Must check that t is well-formed *)
          typeMatch tres intType;
          tres

      | BinOp (bop, e1, e2, tres) -> begin
          let t1 = checkExp isconst e1 in
          let t2 = checkExp isconst e2 in
          match bop with
            (Mult | Div) -> 
              typeMatch t1 t2; checkArithmeticType tres; 
              typeMatch t1 tres; tres
          | (Eq|Ne|Lt|Le|Ge|Gt) -> 
              typeMatch t1 t2; checkArithmeticType t1; 
              typeMatch tres intType; tres
          | Mod|BAnd|BOr|BXor -> 
              typeMatch t1 t2; checkIntegralType tres;
              typeMatch t1 tres; tres
          | LAnd | LOr -> 
              typeMatch t1 t2; checkBooleanType tres;
              typeMatch t1 tres; tres
          | Shiftlt | Shiftrt -> 
              typeMatch t1 tres; checkIntegralType t1; 
              checkIntegralType t2; tres
          | (PlusA | MinusA) -> 
                typeMatch t1 t2; typeMatch t1 tres;
                checkArithmeticType tres; tres
          | (PlusPI | MinusPI | IndexPI) -> 
              checkPointerType tres;
              typeMatch t1 tres;
              checkIntegralType t2;
              tres
          | MinusPP  -> 
              checkPointerType t1; checkPointerType t2;
              typeMatch t1 t2;
              typeMatch tres intType;
              tres
      end
      | AddrOf (lv) -> begin
          let tlv = checkLval isconst lv in
          (* Only certain types can be in AddrOf *)
          match unrollType tlv with
          | TVoid _ -> 
              E.s (bug "AddrOf on improper type");
              
          | (TInt _ | TFloat _ | TPtr _ | TComp _ | TFun _ | TArray _ ) -> 
              TPtr(tlv, [])

          | TEnum _ -> intPtrType
          | _ -> E.s (bug "AddrOf on unknown type")
      end

      | StartOf lv -> begin
          let tlv = checkLval isconst lv in
          match unrollType tlv with
            TArray (t,_, _) -> TPtr(t, [])
          | _ -> E.s (bug "StartOf on a non-array")
      end
            
      | CastE (tres, e) -> begin
          let et = checkExp isconst e in
          checkType tres CTExp;
          (* Not all types can be cast *)
          match unrollType et with
            TArray _ -> E.s (bug "Cast of an array type")
          | TFun _ -> E.s (bug "Cast of a function type")
          | TComp _ -> E.s (bug "Cast of a composite type")
          | TVoid _ -> E.s (bug "Cast of a void type")
          | _ -> tres
      end)
    () (* The argument of withContext *)

and checkInit  (i: init) : typ = 
  E.withContext 
    (fun _ -> dprintf "checkInit: %a" d_init i)
    (fun _ ->
      match i with
        SingleInit e -> checkExp true e
(*
      | ArrayInit (bt, len, initl) -> begin
          checkType bt CTSizeof;
          if List.length initl > len then 
            ignore (warn "Too many initializers in array");
          List.iter (fun i -> checkInitType i bt) initl;
          TArray(bt, Some (integer len), [])
      end
*)
      | CompoundInit (ct, initl) -> begin
          checkType ct CTSizeof;
          (match unrollType ct with
            TArray(bt, Some (Const(CInt64(len, _, _))), _) -> 
              let rec loopIndex i = function
                  [] -> 
                    if i <> len then 
                      ignore (warn "Wrong number of initializers in array")

                | (Index(Const(CInt64(i', _, _)), NoOffset), ei) :: rest -> 
                    if i' <> i then 
                      ignore (warn "Initializer for index %s when %s was expected\n"
                                (Int64.format "%d" i') (Int64.format "%d" i));
                    checkInitType ei bt;
                    loopIndex (Int64.succ i) rest
                | _ :: rest -> 
                    ignore (warn "Malformed initializer for array element")
              in
              loopIndex Int64.zero initl
          | TArray(_, _, _) -> 
              ignore (warn "Malformed initializer for array")
          | TComp (comp, _) -> 
              if comp.cstruct then
                let rec loopFields 
                    (nextflds: fieldinfo list) 
                    (initl: (offset * init) list) : unit = 
                  match nextflds, initl with 
                    [], [] -> ()   (* We are done *)
                  | f :: restf, (Field(f', NoOffset), i) :: resti -> 
                      if f.fname <> f'.fname then 
                        ignore (warn "Expected initializer for field %s and found one for %s\n" f.fname f'.fname);
                      checkInitType i f.ftype;
                      loopFields restf resti
                  | [], _ :: _ -> 
                      ignore (warn "Too many initializers for struct")
                  | _ :: _, [] -> 
                      ignore (warn "Too few initializers for struct")
                  | _, _ -> 
                      ignore (warn "Malformed initializer for struct")
                in
                loopFields
                  (List.filter (fun f -> f.fname <> missingFieldName) 
                     comp.cfields) 
                  initl

              else (* UNION *)
                if comp.cfields == [] then begin
                  if initl != [] then 
                    ignore (warn "Initializer for empty union not empty");
                end else begin
                  match initl with 
                    [(Field(f, NoOffset), ei)] -> 
                      if f.fcomp != comp then 
                        ignore (bug "Wrong designator for union initializer");
                      if !msvcMode && f != List.hd comp.cfields then
                        ignore (warn "On MSVC you can only initialize the first field of a union");
                      checkInitType ei f.ftype
                      
                  | _ -> 
                      ignore (warn "Malformed initializer for union")
                end
          | _ -> 
              E.s (warn "Type of Compound is not array or struct or union"));
          ct
      end)
    () (* The arguments of withContext *)


and checkInitType (i: init) (t: typ) : unit = 
  let it = checkInit i in
  typeMatch it t
  
and checkStmt (s: stmt) = 
  E.withContext 
    (fun _ -> 
      (* Print context only for certain small statements *)
      match s.skind with 
        (*Loop _*) While _ | DoWhile _ | For _ | If _ | Switch _  -> nil
      | _ -> dprintf "checkStmt: %a" d_stmt s)
    (fun _ -> 
      (* Check the labels *)
      let checkLabel = function
          Label (ln, l, _) -> 
            if H.mem labels ln then
              ignore (warn "Multiply defined label %s" ln);
            H.add labels ln ()
        | Case (e, _) -> checkExpType true e intType
        | _ -> () (* Not yet implemented *)
      in
      List.iter checkLabel s.labels;
      (* See if we have seen this statement before *)
      if List.memq s !statements then 
        ignore (warn "Statement is shared");
      (* Remember that we have seen this one *)
      statements := s :: !statements;
      match s.skind with
        Break _ | Continue _ -> ()
      | Goto (gref, l) -> 
          currentLoc := l;
          (* Find a label *)
          let lab = 
            match List.filter (function Label _ -> true | _ -> false) 
                  !gref.labels with
              Label (lab, _, _) :: _ -> lab
            | _ -> 
                ignore (warn "Goto to block without a label\n");
                "<missing label>"
          in
          (* Remember it as a target *)
          gotoTargets := (lab, !gref) :: !gotoTargets
            

      | Return (re,l) -> begin
          currentLoc := l;
          match re, !currentReturnType with
            None, TVoid _  -> ()
          | _, TVoid _ -> ignore (warn "Invalid return value")
          | None, _ -> ignore (warn "Invalid return value")
          | Some re', rt' -> checkExpType false re' rt'
        end
(*
      | Loop (b, l, _, _) -> checkBlock b
*)
      | While (e, b, l) ->
          currentLoc := l;
          let te = checkExp false e in
          checkBooleanType te;
          checkBlock b;
      | DoWhile (e, b, l) ->
          currentLoc := l;
          let te = checkExp false e in
          checkBooleanType te;
          checkBlock b;
      | For (bInit, e, bIter, b, l) ->
          currentLoc := l;
	  checkBlock bInit;
	  let te = checkExp false e in
          checkBooleanType te;
	  checkBlock bIter;
          checkBlock b;
      | Block b -> checkBlock b
      | If (e, bt, bf, l) -> 
          currentLoc := l;
          let te = checkExp false e in
          checkBooleanType te;
          checkBlock bt;
          checkBlock bf
      | Switch (e, b, cases, l) -> 
          currentLoc := l;
          checkExpType false e intType;
          (* Remember the statements so far *)
          let prevStatements = !statements in
          checkBlock b;
          (* Now make sure that all the cases do occur in that block *)
          List.iter
            (fun c -> 
              if not (List.exists (function Case _ -> true | _ -> false) 
                        c.labels) then
                ignore (warn "Case in switch statment without a \"case\"\n");
              (* Make sure it is in there *)
              let rec findCase = function
                | l when l == prevStatements -> (* Not found *)
                    ignore (warnContext 
                              "Cannot find target of switch statement")
                | [] -> E.s (E.bug "Check: findCase")
                | c' :: rest when c == c' -> () (* Found *)
                | _ :: rest -> findCase rest
              in
              findCase !statements)
            cases;
      | TryFinally (b, h, l) -> 
          currentLoc := l;
          checkBlock b;
          checkBlock h

      | TryExcept (b, (il, e), h, l) -> 
          currentLoc := l;
          checkBlock b;
          List.iter checkInstr il;
          checkExpType false e intType;
          checkBlock h

      | Instr il -> List.iter checkInstr il)
    () (* argument of withContext *)

and checkBlock (b: block) : unit = 
  List.iter checkStmt b.bstmts


and checkInstr (i: instr) = 
  match i with 
  | Set (dest, e, l) -> 
      currentLoc := l;
      let t = checkLval false dest in
      (* Not all types can be assigned to *)
      (match unrollType t with
        TFun _ -> ignore (warn "Assignment to a function type")
      | TArray _ -> ignore (warn "Assignment to an array type")
      | TVoid _ -> ignore (warn "Assignment to a void type")
      | _ -> ());
      checkExpType false e t
            
  | Call(dest, what, args, l) -> 
      currentLoc := l;
      let (rt, formals, isva) = 
        match checkExp false what with
          TFun(rt, formals, isva, _) -> rt, formals, isva
        | _ -> E.s (bug "Call to a non-function")
      in
          (* Now check the return value*)
      (match dest, unrollType rt with
        None, TVoid _ -> ()
      | Some _, TVoid _ -> ignore (warn "void value is assigned")
      | None, _ -> () (* "Call of function is not assigned" *)
      | Some destlv, rt' -> 
          let desttyp = checkLval false destlv in
          if typeSig desttyp <> typeSig rt then begin
            (* Not all types can be assigned to *)
            (match unrollType desttyp with
              TFun _ -> ignore (warn "Assignment to a function type")
            | TArray _ -> ignore (warn "Assignment to an array type")
            | TVoid _ -> ignore (warn "Assignment to a void type")
            | _ -> ());
            (* Not all types can be cast *)
            (match rt' with
              TArray _ -> ignore (warn "Cast of an array type")
            | TFun _ -> ignore (warn "Cast of a function type")
            | TComp _ -> ignore (warn "Cast of a composite type")
            | TVoid _ -> ignore (warn "Cast of a void type")
                  
            | _ -> ())
          end);
          (* Now check the arguments *)
      let rec loopArgs formals args = 
        match formals, args with
          [], _ when (isva || args = []) -> ()
        | (fn,ft,_) :: formals, a :: args -> 
            checkExpType false a ft;
            loopArgs formals args
        | _, _ -> ignore (warn "Not enough arguments")
      in
      if formals = None then 
        ignore (warn "Call to function without prototype\n")
      else
        loopArgs (argsToList formals) args
        
  | Asm _ -> ()  (* Not yet implemented *)
  
let rec checkGlobal = function
    GAsm _ -> ()
  | GPragma _ -> ()
  | GText _ -> ()
  | GType (ti, l) -> 
      currentLoc := l;
      E.withContext (fun _ -> dprintf "GType(%s)" ti.tname)
        (fun _ ->
          checkTypeInfo Defined ti;
          if ti.tname <> "" then defineName ti.tname)
        ()

  | GCompTag (comp, l) -> 
      currentLoc := l;
      checkCompInfo Defined comp;

  | GCompTagDecl (comp, l) -> 
      currentLoc := l;
      checkCompInfo Forward comp;

  | GEnumTag (enum, l) -> 
      currentLoc := l;
      checkEnumInfo Defined enum

  | GEnumTagDecl (enum, l) -> 
      currentLoc := l;
      checkEnumInfo Forward enum

  | GVarDecl (vi, l) -> 
      currentLoc := l;
      (* We might have seen it already *)
      E.withContext (fun _ -> dprintf "GVarDecl(%s)" vi.vname)
        (fun _ -> 
          (* If we have seen this vid already then it must be for the exact 
           * same varinfo *)
          if H.mem varIdsEnv vi.vid then
            checkVariable vi
          else begin
            defineVariable vi; 
            checkAttributes vi.vattr;
            checkType vi.vtype CTDecl;
            if not (vi.vglob &&
                    vi.vstorage <> Register) then
              E.s (bug "Invalid declaration of %s" vi.vname)
          end)
        ()
        
  | GVar (vi, init, l) -> 
      currentLoc := l;
      (* Maybe this is the first occurrence *)
      E.withContext (fun _ -> dprintf "GVar(%s)" vi.vname)
        (fun _ -> 
          checkGlobal (GVarDecl (vi, l));
          (* Check the initializer *)
          begin match init.init with
            None -> ()
          | Some i -> ignore (checkInitType i vi.vtype)
          end;
          (* Cannot be a function *)
          if isFunctionType vi.vtype then
            E.s (bug "GVar for a function (%s)\n" vi.vname);
          )
        ()
        

  | GFun (fd, l) -> begin
      currentLoc := l;
      (* Check if this is the first occurrence *)
      let vi = fd.svar in
      let fname = vi.vname in
      E.withContext (fun _ -> dprintf "GFun(%s)" fname)
        (fun _ -> 
          checkGlobal (GVarDecl (vi, l));
          (* Check that the argument types in the type are identical to the 
           * formals *)
          let rec loopArgs targs formals = 
            match targs, formals with
              [], [] -> ()
            | (fn, ft, fa) :: targs, fo :: formals -> 
                if fn <> fo.vname || ft != fo.vtype || fa != fo.vattr then 
                  ignore (warnContext 
                            "Formal %s not shared (type + locals) in %s" 
                            fo.vname fname);
                loopArgs targs formals

            | _ -> 
                E.s (bug "Type has different number of formals for %s" 
                       fname)
          in
          begin match vi.vtype with
            TFun (rt, args, isva, a) -> begin
              currentReturnType := rt;
              loopArgs (argsToList args) fd.sformals
            end
          | _ -> E.s (bug "Function %s does not have a function type" 
                        fname)
          end;
          ignore (fd.smaxid >= 0 || E.s (bug "smaxid < 0 for %s" fname));
          (* Now start a new environment, in a finally clause *)
          begin try
            startEnv ();
            (* Do the locals *)
            let doLocal tctx v = 
              if v.vglob then
                ignore (warnContext
                          "Local %s has the vglob flag set" v.vname);
              if v.vstorage <> NoStorage && v.vstorage <> Register then
                ignore (warnContext
                          "Local %s has storage %a\n" v.vname
                          d_storage v.vstorage);
              checkType v.vtype tctx;
              checkAttributes v.vattr;
              defineVariable v
            in
            List.iter (doLocal CTFArg) fd.sformals;
            List.iter (doLocal CTDecl) fd.slocals;
            statements := [];
            gotoTargets := [];
            checkBlock fd.sbody;
            H.clear labels;
            (* Now verify that we have scanned all targets *)
            List.iter 
              (fun (lab, t) -> if not (List.memq t !statements) then 
                ignore (warnContext
                          "Target of \"goto %s\" statement does not appear in function body" lab))
              !gotoTargets;
            statements := [];
            gotoTargets := [];
            (* Done *)
            endEnv ()
          with e -> 
            endEnv ();
            raise e
          end;
          ())
        () (* final argument of withContext *)
  end


let checkFile flags fl = 
  if !E.verboseFlag then ignore (E.log "Checking file %s\n" fl.fileName);
  valid := true;
  List.iter 
    (function
        NoCheckGlobalIds -> checkGlobalIds := false)
    flags;
  iterGlobals fl (fun g -> try checkGlobal g with _ -> ());
  (* Check that for all struct/union tags there is a definition *)
  H.iter 
    (fun k (comp, isadef) -> 
      if !isadef = Used then 
	begin
	  valid := false;
          ignore (E.warn "Compinfo %s is referenced but not defined" 
                    (compFullName comp))
	end)
    compUsed;
  (* Check that for all enum tags there is a definition *)
  H.iter 
    (fun k (enum, isadef) -> 
      if !isadef = Used then 
	begin
	  valid := false;
          ignore (E.warn "Enuminfo %s is referenced but not defined" 
                    enum.ename)
	end)
    enumUsed;
  (* Clean the hashes to let the GC do its job *)
  H.clear typeDefs;
  H.clear varNamesEnv;
  H.clear varIdsEnv;
  H.clear allVarIds;
  H.clear compNames;
  H.clear compUsed;
  H.clear enumUsed;
  H.clear typUsed;
  varNamesList := [];
  if !E.verboseFlag then 
    ignore (E.log "Finished checking file %s\n" fl.fileName);
  !valid
  
