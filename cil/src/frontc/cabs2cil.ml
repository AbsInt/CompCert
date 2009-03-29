(* MODIF: allow E.Error to propagate *)

(* MODIF: for pointer comparison, avoid systematic cast to unsigned int *)

(* MODIF: Loop constructor replaced by 3 constructors: While, DoWhile, For. *)
(* MODIF: Return statement no longer added when the body of the function
          falls-through. *)

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

(* Type check and elaborate ABS to CIL *)

(* The references to ISO means ANSI/ISO 9899-1999 *)
module A = Cabs
module E = Errormsg
module H = Hashtbl
module IH = Inthash
module AL = Alpha

open Cabs
open Pretty
open Cil
open Trace


let mydebugfunction () = 
  E.s (error "mydebugfunction")

let debugGlobal = false

(** NDC added command line parameter **)
(* Turn on tranformation that forces correct parameter evaluation order *)
let forceRLArgEval = ref false

(* Leave a certain global alone. Use a negative number to disable. *)
let nocil: int ref = ref (-1)

(* Indicates whether we're allowed to duplicate small chunks. *)
let allowDuplication: bool ref = ref true

(* ---------- source error message handling ------------- *)
let lu = locUnknown
let cabslu = {lineno = -10; 
	      filename = "cabs lu"; 
	      byteno = -10;}


(** Interface to the Cprint printer *)
let withCprint (f: 'a -> unit) (x: 'a) : unit = 
  Cprint.commit (); Cprint.flush ();
  let old = !Cprint.out in
  Cprint.out := !E.logChannel;
  f x;
  Cprint.commit (); Cprint.flush ();
  flush !Cprint.out;
  Cprint.out := old


(** Keep a list of the variable ID for the variables that were created to 
 * hold the result of function calls *)
let callTempVars: unit IH.t = IH.create 13

(* Keep a list of functions that were called without a prototype. *)
let noProtoFunctions : bool IH.t = IH.create 13

(* Check that s starts with the prefix p *)
let prefix p s = 
  let lp = String.length p in
  let ls = String.length s in
  lp <= ls && String.sub s 0 lp = p

(***** COMPUTED GOTO ************)

(* The address of labels are small integers (starting from 0). A computed 
 * goto is replaced with a switch on the address of the label. We generate 
 * only one such switch and we'll jump to it from all computed gotos. To 
 * accomplish this we'll add a local variable to store the target of the 
 * goto. *)

(* The local variable in which to put the detination of the goto and the 
 * statement where to jump *) 
let gotoTargetData: (varinfo * stmt) option ref = ref None

(* The "addresses" of labels *)
let gotoTargetHash: (string, int) H.t = H.create 13
let gotoTargetNextAddr: int ref = ref 0


(********** TRANSPARENT UNION ******)
(* Check if a type is a transparent union, and return the first field if it 
 * is *)
let isTransparentUnion (t: typ) : fieldinfo option = 
  match unrollType t with 
    TComp (comp, _) when not comp.cstruct -> 
      (* Turn transparent unions into the type of their first field *)
      if hasAttribute "transparent_union" (typeAttrs t) then begin
        match comp.cfields with
          f :: _ -> Some f
        | _ -> E.s (unimp "Empty transparent union: %s" (compFullName comp))
      end else 
        None
  | _ -> None

(* When we process an argument list, remember the argument index which has a 
 * transparent union type, along with the original type. We need this to 
 * process function definitions *)
let transparentUnionArgs : (int * typ) list ref = ref []

let debugLoc = false
let convLoc (l : cabsloc) =
  if debugLoc then 
    ignore (E.log "convLoc at %s: line %d, btye %d\n" l.filename l.lineno l.byteno);
  {line = l.lineno; file = l.filename; byte = l.byteno;}


let isOldStyleVarArgName n = 
  if !msvcMode then n = "va_alist"
  else n = "__builtin_va_alist"

let isOldStyleVarArgTypeName n = 
  if !msvcMode then n = "va_list"  || n = "__ccured_va_list" 
  else n = "__builtin_va_alist_t"

(* Weimer
 * multi-character character constants
 * In MSCV, this code works:
 *
 * long l1 = 'abcd';  // note single quotes
 * char * s = "dcba";
 * long * lptr = ( long * )s;
 * long l2 = *lptr;
 * assert(l1 == l2);
 *
 * We need to change a multi-character character literal into the
 * appropriate integer constant. However, the plot sickens: we
 * must also be able to handle things like 'ab\nd' (value = * "d\nba")
 * and 'abc' (vale = *"cba"). 
 *
 * First we convert 'AB\nD' into the list [ 65 ; 66 ; 10 ; 68 ], then we
 * multiply and add to get the desired value. 
 *)

(* Given a character constant (like 'a' or 'abc') as a list of 64-bit
 * values, turn it into a CIL constant.  Multi-character constants are
 * treated as multi-digit numbers with radix given by the bit width of
 * the specified type (either char or wchar_t). *)
let reduce_multichar typ : int64 list -> int64 =
  let radix = bitsSizeOf typ in
  List.fold_left
    (fun acc -> Int64.add (Int64.shift_left acc radix))
    Int64.zero

let interpret_character_constant char_list =
  let value = reduce_multichar charType char_list in
  if value < (Int64.of_int 256) then  
    (* ISO C 6.4.4.4.10: single-character constants have type int *)
    (CChr(Char.chr (Int64.to_int value))), intType
  else begin
    let orig_rep = None (* Some("'" ^ (String.escaped str) ^ "'") *) in
    if value <= (Int64.of_int32 Int32.max_int) then
      (CInt64(value,IULong,orig_rep)),(TInt(IULong,[]))
    else 
      (CInt64(value,IULongLong,orig_rep)),(TInt(IULongLong,[]))
  end

(*** EXPRESSIONS *************)

                                        (* We collect here the program *)
let theFile : global list ref = ref []
let theFileTypes : global list ref = ref []

let initGlobals () = theFile := []; theFileTypes := []

    
let cabsPushGlobal (g: global) = 
  pushGlobal g ~types:theFileTypes ~variables:theFile

(* Keep track of some variable ids that must be turned into definitions. We 
 * do this when we encounter what appears a definition of a global but 
 * without initializer. We leave it a declaration because maybe down the road 
 * we see another definition with an initializer. But if we don't see any 
 * then we turn the last such declaration into a definition without 
 * initializer *)
let mustTurnIntoDef: bool IH.t = IH.create 117

(* Globals that have already been defined. Indexed by the variable name. *)
let alreadyDefined: (string, location) H.t = H.create 117

(* Globals that were created due to static local variables. We chose their 
 * names to be distinct from any global encountered at the time. But we might 
 * see a global with conflicting name later in the file. *)
let staticLocals: (string, varinfo) H.t = H.create 13


(* Typedefs. We chose their names to be distinct from any global encounterd 
 * at the time. But we might see a global with conflicting name later in the 
 * file *)
let typedefs: (string, typeinfo) H.t = H.create 13

let popGlobals () = 
  let rec revonto (tail: global list) = function
      [] -> tail

    | GVarDecl (vi, l) :: rest 
      when vi.vstorage != Extern && IH.mem mustTurnIntoDef vi.vid -> 
        IH.remove mustTurnIntoDef vi.vid;
        revonto (GVar (vi, {init = None}, l) :: tail) rest

    | x :: rest -> revonto (x :: tail) rest
  in
  revonto (revonto [] !theFile) !theFileTypes


(********* ENVIRONMENTS ***************)

(* The environment is kept in two distinct data structures. A hash table maps
 * each original variable name into a varinfo (for variables, or an
 * enumeration tag, or a type). (Note that the varinfo might contain an
 * alpha-converted name different from that of the lookup name.) The Ocaml
 * hash tables can keep multiple mappings for a single key. Each time the
 * last mapping is returned and upon deletion the old mapping is restored. To
 * keep track of local scopes we also maintain a list of scopes (represented
 * as lists).  *)
type envdata =
    EnvVar of varinfo                   (* The name refers to a variable
                                         * (which could also be a function) *)
  | EnvEnum of exp * typ                (* The name refers to an enumeration
                                         * tag for which we know the value
                                         * and the host type *)
  | EnvTyp of typ                       (* The name is of the form  "struct
                                         * foo", or "union foo" or "enum foo"
                                         * and refers to a type. Note that
                                         * the name of the actual type might
                                         * be different from foo due to alpha
                                         * conversion *)
  | EnvLabel of string                  (* The name refers to a label. This 
                                         * is useful for GCC's locally 
                                         * declared labels. The lookup name 
                                         * for this category is "label foo" *)

let env : (string, envdata * location) H.t = H.create 307
(* We also keep a global environment. This is always a subset of the env *)
let genv : (string, envdata * location) H.t = H.create 307

 (* In the scope we keep the original name, so we can remove them from the
  * hash table easily *)
type undoScope =
    UndoRemoveFromEnv of string
  | UndoResetAlphaCounter of location AL.alphaTableData ref * 
                             location AL.alphaTableData
  | UndoRemoveFromAlphaTable of string

let scopes :  undoScope list ref list ref = ref []

let isAtTopLevel () = 
  !scopes = []


(* When you add to env, you also add it to the current scope *)
let addLocalToEnv (n: string) (d: envdata) = 
(*  ignore (E.log "%a: adding local %s to env\n" d_loc !currentLoc n); *)
  H.add env n (d, !currentLoc);
    (* If we are in a scope, then it means we are not at top level. Add the 
     * name to the scope *)
  (match !scopes with
    [] -> begin
      match d with
        EnvVar _ -> 
          E.s (E.bug "addLocalToEnv: not in a scope when adding %s!" n)
      | _ -> () (* We might add types *)
    end
  | s :: _ -> 
      s := (UndoRemoveFromEnv n) :: !s)


let addGlobalToEnv (k: string) (d: envdata) : unit = 
(*  ignore (E.log "%a: adding global %s to env\n" d_loc !currentLoc k); *)
  H.add env k (d, !currentLoc);
  (* Also add it to the global environment *)
  H.add genv k (d, !currentLoc)
  
  

(* Create a new name based on a given name. The new name is formed from a 
 * prefix (obtained from the given name as the longest prefix that ends with 
 * a non-digit), followed by a '_' and then by a positive integer suffix. The 
 * first argument is a table mapping name prefixes with the largest suffix 
 * used so far for that prefix. The largest suffix is one when only the 
 * version without suffix has been used. *)
let alphaTable : (string, location AL.alphaTableData ref) H.t = H.create 307 
        (* vars and enum tags. For composite types we have names like "struct 
         * foo" or "union bar" *)

(* To keep different name scopes different, we add prefixes to names 
 * specifying the kind of name: the kind can be one of "" for variables or 
 * enum tags, "struct" for structures and unions (they share the name space), 
 * "enum" for enumerations, or "type" for types *)
let kindPlusName (kind: string)
                 (origname: string) : string =
  if kind = "" then origname else
  kind ^ " " ^ origname
                

let stripKind (kind: string) (kindplusname: string) : string = 
  let l = 1 + String.length kind in
  if l > 1 then 
    String.sub kindplusname l (String.length kindplusname - l)
  else
    kindplusname
   
let newAlphaName (globalscope: bool) (* The name should have global scope *)
                 (kind: string) 
                 (origname: string) : string * location = 
  let lookupname = kindPlusName kind origname in
  (* If we are in a scope then it means that we are alpha-converting a local 
   * name. Go and add stuff to reset the state of the alpha table but only to 
   * the top-most scope (that of the enclosing function) *)
  let rec findEnclosingFun = function
      [] -> (* At global scope *)()
    | [s] -> begin
        let prefix = AL.getAlphaPrefix lookupname in
        try
          let countref = H.find alphaTable prefix in
          s := (UndoResetAlphaCounter (countref, !countref)) :: !s
        with Not_found ->
          s := (UndoRemoveFromAlphaTable prefix) :: !s
    end
    | _ :: rest -> findEnclosingFun rest
  in
  if not globalscope then 
    findEnclosingFun !scopes;
  let newname, oldloc = 
           AL.newAlphaName alphaTable None lookupname !currentLoc in
  stripKind kind newname, oldloc


  

let explodeString (nullterm: bool) (s: string) : char list =  
  let rec allChars i acc = 
    if i < 0 then acc
    else allChars (i - 1) ((String.get s i) :: acc)
  in
  allChars (-1 + String.length s) 
    (if nullterm then [Char.chr 0] else [])
    
(*** In order to process GNU_BODY expressions we must record that a given 
 *** COMPUTATION is interesting *)
let gnu_body_result : (A.statement * ((exp * typ) option ref)) ref 
    = ref (A.NOP cabslu, ref None)

(*** When we do statements we need to know the current return type *)
let currentReturnType : typ ref = ref (TVoid([]))
let currentFunctionFDEC: fundec ref = ref dummyFunDec

  
let lastStructId = ref 0
let anonStructName (k: string) (suggested: string) = 
  incr lastStructId;
  "__anon" ^ k ^ (if suggested <> "" then "_"  ^ suggested else "") 
  ^ "_" ^ (string_of_int (!lastStructId))


let constrExprId = ref 0


let startFile () = 
  H.clear env;
  H.clear genv;
  H.clear alphaTable;
  lastStructId := 0



let enterScope () = 
  scopes := (ref []) :: !scopes

     (* Exit a scope and clean the environment. We do not yet delete from 
      * the name table *)
let exitScope () = 
  let this, rest = 
    match !scopes with
      car :: cdr -> car, cdr
    | [] -> E.s (error "Not in a scope")
  in
  scopes := rest;
  let rec loop = function
      [] -> ()
    | UndoRemoveFromEnv n :: t -> 
        H.remove env n; loop t
    | UndoRemoveFromAlphaTable n :: t -> H.remove alphaTable n; loop t
    | UndoResetAlphaCounter (vref, oldv) :: t -> 
        vref := oldv;
        loop t
  in
  loop !this

(* Lookup a variable name. Return also the location of the definition. Might 
 * raise Not_found  *)
let lookupVar (n: string) : varinfo * location = 
  match H.find env n with
    (EnvVar vi), loc -> vi, loc
  | _ -> raise Not_found
        
let lookupGlobalVar (n: string) : varinfo * location = 
  match H.find genv n with
    (EnvVar vi), loc -> vi, loc
  | _ -> raise Not_found
        
let docEnv () = 
  let acc : (string * (envdata * location)) list ref = ref [] in
  let doone () = function
      EnvVar vi, l -> 
        dprintf "Var(%s,global=%b) (at %a)" vi.vname vi.vglob d_loc l
    | EnvEnum (tag, typ), l -> dprintf "Enum (at %a)" d_loc l
    | EnvTyp t, l -> text "typ"
    | EnvLabel l, _ -> text ("label " ^ l)
  in
  H.iter (fun k d -> acc := (k, d) :: !acc) env;
  docList ~sep:line (fun (k, d) -> dprintf "  %s -> %a" k doone d) () !acc



(* Add a new variable. Do alpha-conversion if necessary *)
let alphaConvertVarAndAddToEnv (addtoenv: bool) (vi: varinfo) : varinfo = 
(*
  ignore (E.log "%t: alphaConvert(addtoenv=%b) %s" d_thisloc addtoenv vi.vname);
*)
  (* Announce the name to the alpha conversion table *)
  let newname, oldloc = newAlphaName (addtoenv && vi.vglob) "" vi.vname in
  (* Make a copy of the vi if the name has changed. Never change the name for 
   * global variables *)
  let newvi = 
    if vi.vname = newname then 
      vi 
    else begin
      if vi.vglob then begin
        (* Perhaps this is because we have seen a static local which happened 
         * to get the name that we later want to use for a global. *)
        try 
          let static_local_vi = H.find staticLocals vi.vname in
          H.remove staticLocals vi.vname;
          (* Use the new name for the static local *)
          static_local_vi.vname <- newname;
          (* And continue using the last one *)
          vi
        with Not_found -> begin
          (* Or perhaps we have seen a typedef which stole our name. This is 
           possible because typedefs use the same name space *)
          try
            let typedef_ti = H.find typedefs vi.vname in 
            H.remove typedefs vi.vname;
            (* Use the new name for the typedef instead *)
            typedef_ti.tname <- newname;
            (* And continue using the last name *)
            vi
          with Not_found -> 
            E.s (E.error "It seems that we would need to rename global %s (to %s) because of previous occurrence at %a" 
                   vi.vname newname d_loc oldloc);
        end
      end else begin 
        (* We have changed the name of a local variable. Can we try to detect 
         * if the other variable was also local in the same scope? Not for 
         * now. *)
        copyVarinfo vi newname
      end
    end
  in
  (* Store all locals in the slocals (in reversed order). We'll reverse them 
   * and take out the formals at the end of the function *)
  if not vi.vglob then
    !currentFunctionFDEC.slocals <- newvi :: !currentFunctionFDEC.slocals;

  (if addtoenv then 
    if vi.vglob then
      addGlobalToEnv vi.vname (EnvVar newvi)
    else
      addLocalToEnv vi.vname (EnvVar newvi));
(*
  ignore (E.log "  new=%s\n" newvi.vname);
*)
(*  ignore (E.log "After adding %s alpha table is: %a\n"
            newvi.vname docAlphaTable alphaTable); *)
  newvi


(* Strip the "const" from the type. It is unfortunate that const variables 
 * can only be set in initialization. Once we decided to move all 
 * declarations to the top of the functions, we have no way of setting a 
 * "const" variable. Furthermore, if the type of the variable is an array or 
 * a struct we must recursively strip the "const" from fields and array 
 * elements. *)
let rec stripConstLocalType (t: typ) : typ = 
  let dc a = 
    if hasAttribute "const" a then 
      dropAttribute "const" a 
    else a 
  in
  match t with 
  | TPtr (bt, a) -> 
      (* We want to be able to detect by pointer equality if the type has 
       * changed. So, don't realloc the type unless necessary. *)
      let a' = dc a in if a != a' then TPtr(bt, a') else t
  | TInt (ik, a) -> 
      let a' = dc a in if a != a' then TInt(ik, a') else t
  | TFloat(fk, a) -> 
      let a' = dc a in if a != a' then TFloat(fk, a') else t
  | TNamed (ti, a) -> 
      (* We must go and drop the consts from the typeinfo as well ! *)
      let t' = stripConstLocalType ti.ttype in
      if t != t' then begin
        (* ignore (warn "Stripping \"const\" from typedef %s\n" ti.tname); *)
        ti.ttype <- t'
      end;
      let a' = dc a in if a != a' then TNamed(ti, a') else t

  | TEnum (ei, a) -> 
      let a' = dc a in if a != a' then TEnum(ei, a') else t
      
  | TArray(bt, leno, a) -> 
      (* We never assign to the array. So, no need to change the const. But 
       * we must change it on the base type *)
      let bt' = stripConstLocalType bt in
      if bt' != bt then TArray(bt', leno, a) else t

  | TComp(ci, a) ->
      (* Must change both this structure as well as its fields *)
      List.iter
        (fun f -> 
          let t' = stripConstLocalType f.ftype in
          if t' != f.ftype then begin
            ignore (warnOpt "Stripping \"const\" from field %s of %s\n" 
                      f.fname (compFullName ci));
            f.ftype <- t'
          end)
        ci.cfields;
      let a' = dc a in if a != a' then TComp(ci, a') else t

    (* We never assign functions either *)
  | TFun(rt, args, va, a) -> t
  | TVoid _ -> E.s (bug "cabs2cil: stripConstLocalType: void")
  | TBuiltin_va_list a -> 
      let a' = dc a in if a != a' then TBuiltin_va_list a' else t


let constFoldTypeVisitor = object (self)
  inherit nopCilVisitor
  method vtype t: typ visitAction =
    match t with
      TArray(bt, Some len, a) -> 
        let len' = constFold true len in
        ChangeDoChildrenPost (
          TArray(bt, Some len', a),
          (fun x -> x)
        )
    | _ -> DoChildren
end

(* Const-fold any expressions that appear as array lengths in this type *)
let constFoldType (t:typ) : typ =
  visitCilType constFoldTypeVisitor t



(* Create a new temporary variable *)
let newTempVar typ = 
  if !currentFunctionFDEC == dummyFunDec then 
    E.s (bug "newTempVar called outside a function");
(*  ignore (E.log "stripConstLocalType(%a) for temporary\n" d_type typ); *)
  let t' = stripConstLocalType typ in
  (* Start with the name "tmp". The alpha converter will fix it *)
  let vi = makeVarinfo false "tmp" t' in
  alphaConvertVarAndAddToEnv false  vi (* Do not add to the environment *)
(*
    { vname = "tmp";  (* addNewVar will make the name fresh *)
      vid   = newVarId "tmp" false;
      vglob = false;
      vtype = t';
      vdecl = locUnknown;
      vinline = false;
      vattr = [];
      vaddrof = false;
      vreferenced = false;   (* sm *)
      vstorage = NoStorage;
    } 
*)

let mkAddrOfAndMark ((b, off) as lval) : exp = 
  (* Mark the vaddrof flag if b is a variable *)
  (match b with 
    Var vi -> vi.vaddrof <- true
  | _ -> ());
  mkAddrOf lval
  
(* Call only on arrays *)
let mkStartOfAndMark ((b, off) as lval) : exp = 
  (* Mark the vaddrof flag if b is a variable *)
  (match b with 
    Var vi -> vi.vaddrof <- true
  | _ -> ());
  let res = StartOf lval in
  res
  


   (* Keep a set of self compinfo for composite types *)
let compInfoNameEnv : (string, compinfo) H.t = H.create 113
let enumInfoNameEnv : (string, enuminfo) H.t = H.create 113


let lookupTypeNoError (kind: string) 
                      (n: string) : typ * location = 
  let kn = kindPlusName kind n in
  match H.find env kn with
    EnvTyp t, l -> t, l
  | _ -> raise Not_found

let lookupType (kind: string) 
               (n: string) : typ * location = 
  try
    lookupTypeNoError kind n
  with Not_found -> 
    E.s (error "Cannot find type %s (kind:%s)\n" n kind)

(* Create the self ref cell and add it to the map. Return also an indication 
 * if this is a new one. *)
let createCompInfo (iss: bool) (n: string) : compinfo * bool = 
  (* Add to the self cell set *)
  let key = (if iss then "struct " else "union ") ^ n in
  try
    H.find compInfoNameEnv key, false (* Only if not already in *)
  with Not_found -> begin
    (* Create a compinfo. This will have "cdefined" false. *)
    let res = mkCompInfo iss n (fun _ -> []) [] in
    H.add compInfoNameEnv key res;
    res, true
  end

(* Create the self ref cell and add it to the map. Return an indication 
 * whether this is a new one. *)
let createEnumInfo (n: string) : enuminfo * bool = 
  (* Add to the self cell set *)
  try
    H.find enumInfoNameEnv n, false (* Only if not already in *)
  with Not_found -> begin
    (* Create a enuminfo *)
    let enum = { ename = n; eitems = []; 
                 eattr = []; ereferenced = false; } in
    H.add enumInfoNameEnv n enum;
    enum, true
  end


   (* kind is either "struct" or "union" or "enum" and n is a name *)
let findCompType (kind: string) (n: string) (a: attributes) = 
  let makeForward () = 
    (* This is a forward reference, either because we have not seen this 
     * struct already or because we want to create a version with different 
     * attributes  *)
    if kind = "enum" then 
      let enum, isnew = createEnumInfo n in
      if isnew then
        cabsPushGlobal (GEnumTagDecl (enum, !currentLoc));
      TEnum (enum, a)
    else 
      let iss = if kind = "struct" then true else false in
      let self, isnew = createCompInfo iss n in
      if isnew then 
        cabsPushGlobal (GCompTagDecl (self, !currentLoc));
      TComp (self, a)
  in
  try
    let old, _ = lookupTypeNoError kind n in (* already defined  *)
    let olda = typeAttrs old in
    if Util.equals olda a then old else makeForward ()
  with Not_found -> makeForward ()
  

(* A simple visitor that searchs a statement for labels *)
class canDropStmtClass pRes = object
  inherit nopCilVisitor
        
  method vstmt s = 
    if s.labels != [] then 
      (pRes := false; SkipChildren)
    else 
      if !pRes then DoChildren else SkipChildren

  method vinst _ = SkipChildren
  method vexpr _ = SkipChildren
      
end
let canDropStatement (s: stmt) : bool = 
  let pRes = ref true in
  let vis = new canDropStmtClass pRes in
  ignore (visitCilStmt vis s);
  !pRes

(**** Occasionally we see structs with no name and no fields *)


module BlockChunk = 
  struct
    type chunk = {
        stmts: stmt list;
        postins: instr list;              (* Some instructions to append at 
                                           * the ends of statements (in 
                                           * reverse order)  *)
                                        (* A list of case statements visible at the 
                                         * outer level *)
        cases: (label * stmt) list
      } 

    let d_chunk () (c: chunk) = 
      dprintf "@[{ @[%a@] };@?%a@]"
           (docList ~sep:(chr ';') (d_stmt ())) c.stmts
           (docList ~sep:(chr ';') (d_instr ())) (List.rev c.postins)
 
    let empty = 
      { stmts = []; postins = []; cases = []; }

    let isEmpty (c: chunk) = 
      c.postins == [] && c.stmts == []

    let isNotEmpty (c: chunk) = not (isEmpty c)

    let i2c (i: instr) = 
      { empty with postins = [i] }
        
    (* Occasionally, we'll have to push postins into the statements *)
    let pushPostIns (c: chunk) : stmt list = 
      if c.postins = [] then c.stmts
      else
        let rec toLast = function
            [{skind=Instr il} as s] as stmts -> 
              s.skind <- Instr (il @ (List.rev c.postins));
              stmts

          | [] -> [mkStmt (Instr (List.rev c.postins))]

          | a :: rest -> a :: toLast rest
        in
        compactStmts (toLast c.stmts)


    let c2block (c: chunk) : block = 
      { battrs = [];
        bstmts = pushPostIns c;
      } 

    (* Add an instruction at the end. Never refer to this instruction again 
     * after you call this *)
    let (+++) (c: chunk) (i : instr) =
      {c with postins = i :: c.postins}

    (* Append two chunks. Never refer to the original chunks after you call 
     * this. And especially never share c2 with somebody else *)
    let (@@) (c1: chunk) (c2: chunk) = 
      { stmts = compactStmts (pushPostIns c1 @ c2.stmts);
        postins = c2.postins;
        cases = c1.cases @ c2.cases;
      } 

    let skipChunk = empty
        
    let returnChunk (e: exp option) (l: location) : chunk = 
      { stmts = [ mkStmt (Return(e, l)) ];
        postins = [];
        cases = []
      }

    let ifChunk (be: exp) (l: location) (t: chunk) (e: chunk) : chunk = 
      
      { stmts = [ mkStmt(If(be, c2block t, c2block e, l))];
        postins = [];
        cases = t.cases @ e.cases;
      } 

        (* We can duplicate a chunk if it has a few simple statements, and if 
         * it does not have cases *)
    let duplicateChunk (c: chunk) = (* raises Failure if you should not 
                                     * duplicate this chunk *)
      if not !allowDuplication then
        raise (Failure "cannot duplicate: disallowed by user");
      if c.cases != [] then raise (Failure "cannot duplicate: has cases") else
      let pCount = ref (List.length c.postins) in
      { stmts = 
        List.map 
          (fun s -> 
            if s.labels != [] then 
              raise (Failure "cannot duplicate: has labels");
(*
            (match s.skind with 
              If _ | Switch _ | (*Loop _*)
	       While _ | DoWhile _ | For _ | Block _ -> 
                raise (Failure "cannot duplicate: complex stmt")
            | Instr il -> 
                pCount := !pCount + List.length il
            | _ -> incr pCount);
            if !pCount > 5 then raise (Failure ("cannot duplicate: too many instr"));
*)
            (* We can just copy it because there is nothing to share here. 
             * Except maybe for the ref cell in Goto but it is Ok to share 
             * that, I think *)
            { s with sid = s.sid}) c.stmts;
        postins = c.postins; (* There is no shared stuff in instructions *)
        cases = []
      } 
(*
    let duplicateChunk (c: chunk) = 
      if isEmpty c then c else raise (Failure ("cannot duplicate: isNotEmpty"))
*)
    (* We can drop a chunk if it does not have labels inside *)
    let canDrop (c: chunk) =
      List.for_all canDropStatement c.stmts

(*
    let loopChunk (body: chunk) : chunk = 
      (* Make the statement *)
      let loop = mkStmt (Loop (c2block body, !currentLoc, None, None)) in
      { stmts = [ loop (* ; n *) ];
        postins = [];
        cases = body.cases;
      } 
*)

    let whileChunk (e: exp) (body: chunk) : chunk = 
      let loop = mkStmt (While (e, c2block body, !currentLoc)) in
	
	{ stmts = [ loop ];
          postins = [];
          cases = body.cases;
	} 

    let doWhileChunk (e: exp) (body: chunk) : chunk = 
      let loop = mkStmt (DoWhile (e, c2block body, !currentLoc)) in
	
	{ stmts = [ loop ];
          postins = [];
          cases = body.cases;
	} 
      
    let forChunk (bInit: chunk) (e: exp) (bIter: chunk)
                 (body: chunk) : chunk = 
      let loop = mkStmt (For (c2block bInit, e, c2block bIter,
			      c2block body, !currentLoc)) in
	
	{ stmts = [ loop ];
          postins = [];
          cases = body.cases;
	} 
      
    let breakChunk (l: location) : chunk = 
      { stmts = [ mkStmt (Break l) ];
        postins = [];
        cases = [];
      } 
      
    let continueChunk (l: location) : chunk = 
      { stmts = [ mkStmt (Continue l) ];
        postins = [];
        cases = []
      } 

        (* Keep track of the gotos *)
    let backPatchGotos : (string, stmt ref list ref) H.t = H.create 17
    let addGoto (lname: string) (bref: stmt ref) : unit = 
      let gotos = 
        try
          H.find backPatchGotos lname
        with Not_found -> begin
          let gotos = ref [] in
          H.add backPatchGotos lname gotos;
          gotos
        end
      in
      gotos := bref :: !gotos

        (* Keep track of the labels *)
    let labelStmt : (string, stmt) H.t = H.create 17
    let initLabels () = 
      H.clear backPatchGotos;
      H.clear labelStmt
      
    let resolveGotos () = 
      H.iter
        (fun lname gotos ->
          try
            let dest = H.find labelStmt lname in
            List.iter (fun gref -> gref := dest) !gotos
          with Not_found -> begin
            E.s (error "Label %s not found\n" lname)
          end)
        backPatchGotos

        (* Get the first statement in a chunk. Might need to change the 
         * statements in the chunk *)
    let getFirstInChunk (c: chunk) : stmt * stmt list = 
      (* Get the first statement and add the label to it *)
      match c.stmts with
        s :: _ -> s, c.stmts
      | [] -> (* Add a statement *)
          let n = mkEmptyStmt () in
          n, n :: c.stmts
      
    let consLabel (l: string) (c: chunk) (loc: location) 
				(in_original_program_text : bool) : chunk = 
      (* Get the first statement and add the label to it *)
      let labstmt, stmts' = getFirstInChunk c in
      (* Add the label *)
      labstmt.labels <- Label (l, loc, in_original_program_text) :: 
				labstmt.labels;
      H.add labelStmt l labstmt;
      if c.stmts == stmts' then c else {c with stmts = stmts'}

    let s2c (s:stmt) : chunk = 
      { stmts = [ s ];
        postins = [];
        cases = [];
      } 

    let gotoChunk (ln: string) (l: location) : chunk = 
      let gref = ref dummyStmt in
      addGoto ln gref;
      { stmts = [ mkStmt (Goto (gref, l)) ];
        postins = [];
        cases = [];
      }

    let caseRangeChunk (el: exp list) (l: location) (next: chunk) = 
      let fst, stmts' = getFirstInChunk next in
      let labels = List.map (fun e -> Case (e, l)) el in
      let cases  = List.map (fun l -> (l, fst)) labels in
      fst.labels <- labels @ fst.labels;
      { next with stmts = stmts'; cases = cases @ next.cases}
        
    let defaultChunk (l: location) (next: chunk) = 
      let fst, stmts' = getFirstInChunk next in
      let lb = Default l in
      fst.labels <- lb :: fst.labels;
      { next with stmts = stmts'; cases = (lb, fst) :: next.cases}

        
    let switchChunk (e: exp) (body: chunk) (l: location) =
      (* Make the statement *)
      let switch = mkStmt (Switch (e, c2block body, 
                                   List.map (fun (_, s) -> s) body.cases, 
                                   l)) in
      { stmts = [ switch (* ; n *) ];
        postins = [];
        cases = [];
      } 

    let mkFunctionBody (c: chunk) : block = 
      resolveGotos (); initLabels ();
      if c.cases <> [] then
        E.s (error "Switch cases not inside a switch statement\n");
      c2block c
      
  end

open BlockChunk 


(************ Labels ***********)
(*
(* Since we turn dowhile and for loops into while we need to take care in 
 * processing the continue statement. For each loop that we enter we place a 
 * marker in a list saying what kinds of loop it is. When we see a continue 
 * for a Non-while loop we must generate a label for the continue *)
type loopstate = 
    While
  | NotWhile of string ref

let continues : loopstate list ref = ref []

let startLoop iswhile = 
  continues := (if iswhile then While else NotWhile (ref "")) :: !continues
*)

(* We need to take care while processing the continue statement...
 * For each loop that we enter we place a marker in a list saying what
 * chunk of code we must duplicate before each continue statement
 * in order to preserve the semantics. *)
type loopMarker =
  | DuplicateBeforeContinue of chunk
  | ContinueUnchanged

let continues : loopMarker list ref = ref []
  
let startLoop lstate =
  continues := lstate :: !continues
  
let continueDuplicateChunk (l: location) : chunk = 
  match !continues with
    | []                             -> E.s (error "continue not in a loop")
    | DuplicateBeforeContinue c :: _ -> c @@ continueChunk l
    | ContinueUnchanged :: _         -> continueChunk l

(* Sometimes we need to create new label names *)
let newLabelName (base: string) = fst (newAlphaName false "label" base)

(*
let continueOrLabelChunk (l: location) : chunk = 
  match !continues with
    [] -> E.s (error "continue not in a loop")
  | While :: _ -> continueChunk l
  | NotWhile lr :: _ -> 
      if !lr = "" then begin
        lr := newLabelName "__Cont"
      end;
      gotoChunk !lr l

let consLabContinue (c: chunk) = 
  match !continues with
    [] -> E.s (error "labContinue not in a loop")
  | While :: rest -> c
  | NotWhile lr :: rest -> if !lr = "" then c else consLabel !lr c !currentLoc false
*)

let exitLoop () = 
  match !continues with
    [] -> E.s (error "exit Loop not in a loop")
  | _ :: rest -> continues := rest
      

(* In GCC we can have locally declared labels. *)
let genNewLocalLabel (l: string) = 
  (* Call the newLabelName to register the label name in the alpha conversion 
   * table. *)
  let l' = newLabelName l in
  (* Add it to the environment *)
  addLocalToEnv (kindPlusName "label" l) (EnvLabel l');
  l'

let lookupLabel (l: string) = 
  try 
    match H.find env (kindPlusName "label" l) with
      EnvLabel l', _ -> l'
    | _ -> raise Not_found
  with Not_found -> 
    l


(** ALLOCA ***)
let allocaFun () = 
  let name = 
    if !msvcMode then "alloca"
      (* Use __builtin_alloca where possible, because this can be used
         even when gcc is invoked with -fno-builtin *)
    else "__builtin_alloca"
  in
  let fdec = emptyFunction name in
  fdec.svar.vtype <- 
     TFun(voidPtrType, Some [ ("len", !typeOfSizeOf, []) ], false, []);
  fdec.svar
  
(* Maps local variables that are variable sized arrays to the expression that 
 * denotes their length *)
let varSizeArrays : exp IH.t = IH.create 17
  
(**** EXP actions ***)
type expAction = 
    ADrop                               (* Drop the result. Only the 
                                         * side-effect is interesting *)
  | ASet of lval * typ                  (* Put the result in a given lval, 
                                         * provided it matches the type. The 
                                         * type is the type of the lval. *)
  | AExp of typ option                  (* Return the exp as usual. 
                                         * Optionally we can specify an 
                                         * expected type. This is useful for 
                                         * constants. The expected type is 
                                         * informational only, we do not 
                                         * guarantee that the converted 
                                         * expression has that type.You must 
                                         * use a doCast afterwards to make 
                                         * sure. *)
  | AExpLeaveArrayFun                   (* Do it like an expression, but do 
                                         * not convert arrays of functions 
                                         * into pointers *)


(*** Result of compiling conditional expressions *)
type condExpRes = 
    CEExp of chunk * exp (* Do a chunk and then an expression *)
  | CEAnd of condExpRes * condExpRes
  | CEOr  of condExpRes * condExpRes
  | CENot of condExpRes

(******** CASTS *********)
let integralPromotion (t : typ) : typ = (* c.f. ISO 6.3.1.1 *)
  match unrollType t with
          (* We assume that an IInt can hold even an IUShort *)
    TInt ((IShort|IUShort|IChar|ISChar|IUChar), a) -> TInt(IInt, a)
  | TInt _ -> t
  | TEnum (_, a) -> TInt(IInt, a)
  | t -> E.s (error "integralPromotion: not expecting %a" d_type t)
  

let arithmeticConversion    (* c.f. ISO 6.3.1.8 *)
    (t1: typ)
    (t2: typ) : typ = 
  let checkToInt _ = () in  (* dummies for now *)
  let checkToFloat _ = () in
  match unrollType t1, unrollType t2 with
    TFloat(FLongDouble, _), _ -> checkToFloat t2; t1
  | _, TFloat(FLongDouble, _) -> checkToFloat t1; t2
  | TFloat(FDouble, _), _ -> checkToFloat t2; t1
  | _, TFloat (FDouble, _) -> checkToFloat t1; t2
  | TFloat(FFloat, _), _ -> checkToFloat t2; t1
  | _, TFloat (FFloat, _) -> checkToFloat t1; t2
  | _, _ -> begin
      let t1' = integralPromotion t1 in
      let t2' = integralPromotion t2 in
      match unrollType t1', unrollType t2' with
        TInt(IULongLong, _), _ -> checkToInt t2'; t1'
      | _, TInt(IULongLong, _) -> checkToInt t1'; t2'
            
      (* We assume a long long is always larger than a long  *)
      | TInt(ILongLong, _), _ -> checkToInt t2'; t1'  
      | _, TInt(ILongLong, _) -> checkToInt t1'; t2'
            
      | TInt(IULong, _), _ -> checkToInt t2'; t1'
      | _, TInt(IULong, _) -> checkToInt t1'; t2'

                    
      | TInt(ILong,_), TInt(IUInt,_) 
            when bitsSizeOf t1' <= bitsSizeOf t2' -> TInt(IULong,[])
      | TInt(IUInt,_), TInt(ILong,_) 
            when bitsSizeOf t2' <= bitsSizeOf t1' -> TInt(IULong,[])
            
      | TInt(ILong, _), _ -> checkToInt t2'; t1'
      | _, TInt(ILong, _) -> checkToInt t1'; t2'

      | TInt(IUInt, _), _ -> checkToInt t2'; t1'
      | _, TInt(IUInt, _) -> checkToInt t1'; t2'
            
      | TInt(IInt, _), TInt (IInt, _) -> t1'

      | _, _ -> E.s (error "arithmeticConversion")
  end

  
(* Specify whether the cast is from the source code *)
let rec castTo ?(fromsource=false) 
                (ot : typ) (nt : typ) (e : exp) : (typ * exp ) = 
(*
  ignore (E.log "%t: castTo:%s %a->%a\n"
            d_thisloc
            (if fromsource then "(source)" else "")
            d_type ot d_type nt);
*)
  if not fromsource && Util.equals (typeSig ot) (typeSig nt) then
    (* Do not put the cast if it is not necessary, unless it is from the 
     * source. *)
    (ot, e) 
  else begin
    let result = (nt, 
                  if !insertImplicitCasts || fromsource then mkCastT e ot nt else e) in
(*
    ignore (E.log "castTo: ot=%a nt=%a\n  result is %a\n" 
              d_type ot d_type nt
              d_plainexp (snd result));
*)
    (* Now see if we can have a cast here *)
    match ot, nt with
      TNamed(r, _), _ -> castTo ~fromsource:fromsource r.ttype nt e
    | _, TNamed(r, _) -> castTo ~fromsource:fromsource ot r.ttype e
    | TInt(ikindo,_), TInt(ikindn,_) -> 
        (* We used to ignore attributes on integer-integer casts. Not anymore *)
        (* if ikindo = ikindn then (nt, e) else *) 
        result

    | TPtr (told, _), TPtr(tnew, _) -> result
          
    | TInt _, TPtr _ -> result
          
    | TPtr _, TInt _ -> result
          
    | TArray _, TPtr _ -> result
          
    | TArray(t1,_,_), TArray(t2,None,_) when Util.equals (typeSig t1) (typeSig t2) -> (nt, e)
          
    | TPtr _, TArray(_,_,_) -> (nt, e)
          
    | TEnum _, TInt _ -> result
    | TFloat _, (TInt _|TEnum _) -> result
    | (TInt _|TEnum _), TFloat _ -> result
    | TFloat _, TFloat _ -> result
    | TInt _, TEnum _ -> result
    | TEnum _, TEnum _ -> result

    | TEnum _, TPtr _ -> result
    | TBuiltin_va_list _, (TInt _ | TPtr _) -> 
        result

    | (TInt _ | TPtr _), TBuiltin_va_list _ ->
        ignore (warnOpt "Casting %a to __builtin_va_list" d_type ot);
        result

    | TPtr _, TEnum _ -> 
        ignore (warnOpt "Casting a pointer into an enumeration type");
        result

          (* The expression is evaluated for its side-effects *)
    | (TInt _ | TEnum _ | TPtr _ ), TVoid _ -> 
        (ot, e)

          (* Even casts between structs are allowed when we are only 
           * modifying some attributes *)
    | TComp (comp1, a1), TComp (comp2, a2) when comp1.ckey = comp2.ckey -> 
        (nt, e)
          
          (** If we try to pass a transparent union value to a function 
           * expecting a transparent union argument, the argument type would 
           * have been changed to the type of the first argument, and we'll 
           * see a cast from a union to the type of the first argument. Turn 
           * that into a field access *)
    | TComp(tunion, a1), nt -> begin
        match isTransparentUnion ot with 
          None -> E.s (error "castTo %a -> %a@!" d_type ot d_type nt)
        | Some fstfield -> begin
            (* We do it now only if the expression is an lval *)
            let e' = 
              match e with 
                Lval lv -> 
                  Lval (addOffsetLval (Field(fstfield, NoOffset)) lv)
              | _ -> E.s (unimp "castTo: transparent union expression is not an lval: %a\n" d_exp e)
            in
            (* Continue casting *)
            castTo ~fromsource:fromsource fstfield.ftype nt e'
        end
    end
    | _ -> E.s (error "cabs2cil: castTo %a -> %a@!" d_type ot d_type nt)
  end


(* A cast that is used for conditional expressions. Pointers are Ok *)
let checkBool (ot : typ) (e : exp) : bool =
  match unrollType ot with
    TInt _ -> true
  | TPtr _ -> true
  | TEnum _ -> true
  | TFloat _ -> true
  |  _ -> E.s (error "castToBool %a" d_type ot)

(* Given an expression that is being coerced to bool, 
   is it a nonzero constant? *)
let rec isConstTrue (e:exp): bool =
  match e with
  | Const(CInt64 (n,_,_)) -> n <> Int64.zero
  | Const(CChr c) -> 0 <> Char.code c
  | Const(CStr _ | CWStr _) -> true
  | Const(CReal(f, _, _)) -> f <> 0.0;
  | CastE(_, e) -> isConstTrue e
  | _ -> false

(* Given an expression that is being coerced to bool, is it zero? 
   This is a more general version of Cil.isZero, which only handles integers.
   On constant expressions, either isConstTrue or isConstFalse will hold. *)
let rec isConstFalse (e:exp): bool =
  match e with
  | Const(CInt64 (n,_,_)) -> n = Int64.zero
  | Const(CChr c) -> 0 = Char.code c
  | Const(CReal(f, _, _)) -> f = 0.0;
  | CastE(_, e) -> isConstFalse e
  | _ -> false



(* We have our own version of addAttributes that does not allow duplicates *)
let cabsAddAttributes al0 (al: attributes) : attributes = 
  if al0 == [] then al else
  List.fold_left 
    (fun acc (Attr(an, _) as a) -> 
      (* See if the attribute is already in there *)
      match filterAttributes an acc with
        [] -> addAttribute a acc (* Nothing with that name *)
      | a' :: _ -> 
          if Util.equals a a' then 
            acc (* Already in *)
          else begin
            ignore (warnOpt 
                      "Duplicate attribute %a along with %a"
                      d_attr a d_attr a');
            (* let acc' = dropAttribute an acc in *)
            (** Keep both attributes *)
            addAttribute a acc
          end)
    al
    al0
      
let cabsTypeAddAttributes a0 t =
  begin
    match a0 with
    | [] ->
        (* no attributes, keep same type *)
          t
    | _ ->
        (* anything else: add a0 to existing attributes *)
          let add (a: attributes) = cabsAddAttributes a0 a in
          match t with
            TVoid a -> TVoid (add a)
          | TInt (ik, a) -> 
              (* Here we have to watch for the mode attribute *)
(* sm: This stuff is to handle a GCC extension where you can request integers*)
(* of specific widths using the "mode" attribute syntax; for example:     *)
(*   typedef int int8_t __attribute__ ((__mode__ (  __QI__ ))) ;          *)
(* The cryptic "__QI__" defines int8_t to be 8 bits wide, instead of the  *)
(* 32 bits you'd guess if you didn't know about "mode".  The relevant     *)
(* testcase is test/small2/mode_sizes.c, and it was inspired by my        *)
(* /usr/include/sys/types.h.                                              *)
(*                                                                        *)
(* A consequence of this handling is that we throw away the mode          *)
(* attribute, which we used to go out of our way to avoid printing anyway.*)  
              let ik', a0' = 
                (* Go over the list of new attributes and come back with a 
                 * filtered list and a new integer kind *)
                List.fold_left
                  (fun (ik', a0') a0one -> 
                    match a0one with 
                      Attr("mode", [ACons(mode,[])]) -> begin
                        (trace "gccwidth" (dprintf "I see mode %s applied to an int type\n"
                                             mode (* #$@!#@ ML! d_type t *) ));
                        (* the cases below encode the 32-bit assumption.. *)
                        match (ik', mode) with
                        | (IInt, "__QI__")      -> (IChar, a0')
                        | (IInt, "__byte__")    -> (IChar, a0')
                        | (IInt, "__HI__")      -> (IShort,  a0')
                        | (IInt, "__SI__")      -> (IInt, a0')   (* same as t *)
                        | (IInt, "__word__")    -> (IInt, a0')
                        | (IInt, "__pointer__") -> (IInt, a0')
                        | (IInt, "__DI__")      -> (ILongLong, a0')
                      
                        | (IUInt, "__QI__")     -> (IUChar, a0')
                        | (IUInt, "__byte__")   -> (IUChar, a0')
                        | (IUInt, "__HI__")     -> (IUShort, a0')
                        | (IUInt, "__SI__")     -> (IUInt, a0')
                        | (IUInt, "__word__")   -> (IUInt, a0')
                        | (IUInt, "__pointer__")-> (IUInt, a0')
                        | (IUInt, "__DI__")     -> (IULongLong, a0')
                              
                        | _ -> 
                            (ignore (error "GCC width mode %s applied to unexpected type, or unexpected mode"
                                       mode));
                            (ik', a0one :: a0')
 
                      end
                    | _ -> (ik', a0one :: a0'))
                  (ik, [])
                  a0
              in
              TInt (ik', cabsAddAttributes a0' a)

          | TFloat (fk, a) -> TFloat (fk, add a)
          | TEnum (enum, a) -> TEnum (enum, add a)
          | TPtr (t, a) -> TPtr (t, add a)
          | TArray (t, l, a) -> TArray (t, l, add a)
          | TFun (t, args, isva, a) -> TFun(t, args, isva, add a)
          | TComp (comp, a) -> TComp (comp, add a)
          | TNamed (t, a) -> TNamed (t, add a)
          | TBuiltin_va_list a -> TBuiltin_va_list (add a)
  end


(* Do types *)
    (* Combine the types. Raises the Failure exception with an error message. 
     * isdef says whether the new type is for a definition *)
type combineWhat = 
    CombineFundef (* The new definition is for a function definition. The old 
                   * is for a prototype *)
  | CombineFunarg (* Comparing a function argument type with an old prototype 
                   * arg *)
  | CombineFunret (* Comparing the return of a function with that from an old 
                   * prototype *)
  | CombineOther

(* We sometimes want to succeed in combining two structure types that are 
 * identical except for the names of the structs. We keep a list of types 
 * that are known to be equal *)
let isomorphicStructs : (string * string, bool) H.t = H.create 15

let rec combineTypes (what: combineWhat) (oldt: typ) (t: typ) : typ = 
  match oldt, t with
  | TVoid olda, TVoid a -> TVoid (cabsAddAttributes olda a)
  | TInt (oldik, olda), TInt (ik, a) -> 
      let combineIK oldk k = 
        if oldk = k then oldk else
        (* GCC allows a function definition to have a more precise integer 
         * type than a prototype that says "int" *)
        if not !msvcMode && oldk = IInt && bitsSizeOf t <= 32 
           && (what = CombineFunarg || what = CombineFunret) then
          k
        else
          raise (Failure "different integer types")
      in
      TInt (combineIK oldik ik, cabsAddAttributes olda a)
  | TFloat (oldfk, olda), TFloat (fk, a) -> 
      let combineFK oldk k = 
        if oldk = k then oldk else
        (* GCC allows a function definition to have a more precise integer 
         * type than a prototype that says "double" *)
        if not !msvcMode && oldk = FDouble && k = FFloat 
           && (what = CombineFunarg || what = CombineFunret) then
          k
        else
          raise (Failure "different floating point types")
      in
      TFloat (combineFK oldfk fk, cabsAddAttributes olda a)
  | TEnum (_, olda), TEnum (ei, a) -> 
      TEnum (ei, cabsAddAttributes olda a)
        
        (* Strange one. But seems to be handled by GCC *)
  | TEnum (oldei, olda) , TInt(IInt, a) -> TEnum(oldei, 
                                                 cabsAddAttributes olda a)
        (* Strange one. But seems to be handled by GCC *)
  | TInt(IInt, olda), TEnum (ei, a) -> TEnum(ei, cabsAddAttributes olda a)
        
        
  | TComp (oldci, olda) , TComp (ci, a) -> 
      if oldci.cstruct <> ci.cstruct then 
        raise (Failure "different struct/union types");
      let comb_a = cabsAddAttributes olda a in
      if oldci.cname = ci.cname then 
        TComp (oldci, comb_a)
      else 
        (* Now maybe they are actually the same *)
        if H.mem isomorphicStructs (oldci.cname, ci.cname) then 
          (* We know they are the same *)
          TComp (oldci, comb_a)
        else begin
          (* If one has 0 fields (undefined) while the other has some fields 
           * we accept it *)
          let oldci_nrfields = List.length oldci.cfields in
          let ci_nrfields = List.length ci.cfields in
          if oldci_nrfields = 0 then
            TComp (ci, comb_a)
          else if ci_nrfields = 0 then
            TComp (oldci, comb_a) 
          else begin
            (* Make sure that at least they have the same number of fields *)
            if  oldci_nrfields <> ci_nrfields then begin
(*
              ignore (E.log "different number of fields: %s had %d and %s had %d\n"
                        oldci.cname oldci_nrfields
                        ci.cname ci_nrfields);
*)
              raise (Failure "different structs(number of fields)");
            end;
            (* Assume they are the same *)
            H.add isomorphicStructs (oldci.cname, ci.cname) true;
            H.add isomorphicStructs (ci.cname, oldci.cname) true;
            (* Check that the fields are isomorphic and watch for Failure *)
            (try
              List.iter2 (fun oldf f -> 
                if oldf.fbitfield <> f.fbitfield then 
                  raise (Failure "different structs(bitfield info)");
                if oldf.fattr <> f.fattr then 
                  raise (Failure "different structs(field attributes)");
                (* Make sure the types are compatible *)
                ignore (combineTypes CombineOther oldf.ftype f.ftype);
                ) oldci.cfields ci.cfields
            with Failure _ as e -> begin 
              (* Our assumption was wrong. Forget the isomorphism *)
              ignore (E.log "\tFailed in our assumption that %s and %s are isomorphic\n"
                        oldci.cname ci.cname);
              H.remove isomorphicStructs (oldci.cname, ci.cname);
              H.remove isomorphicStructs (ci.cname, oldci.cname);
              raise e
            end);
            (* We get here if we succeeded *)
            TComp (oldci, comb_a)
          end
        end

  | TArray (oldbt, oldsz, olda), TArray (bt, sz, a) -> 
      let newbt = combineTypes CombineOther oldbt bt in
      let newsz = 
        match oldsz, sz with
          None, Some _ -> sz
        | Some _, None -> oldsz
        | None, None -> sz
        | Some oldsz', Some sz' -> 
            (* They are not structurally equal. But perhaps they are equal if 
             * we evaluate them. Check first machine independent comparison  *)
           let checkEqualSize (machdep: bool) = 
              Util.equals (constFold machdep oldsz') 
                          (constFold machdep sz') 
           in
           if checkEqualSize false then 
              oldsz
           else if checkEqualSize true then begin
              ignore (warn "Array type comparison succeeds only based on machine-dependent constant evaluation: %a and %a\n" 
                       d_exp oldsz' d_exp sz');
              oldsz
           end else
              raise (Failure "different array lengths")
           
      in
      TArray (newbt, newsz, cabsAddAttributes olda a)
        
  | TPtr (oldbt, olda), TPtr (bt, a) -> 
      TPtr (combineTypes CombineOther oldbt bt, cabsAddAttributes olda a)
        
  | TFun (_, _, _, [Attr("missingproto",_)]), TFun _ -> t
        
  | TFun (oldrt, oldargs, oldva, olda), TFun (rt, args, va, a) ->
      let newrt = combineTypes 
          (if what = CombineFundef then CombineFunret else CombineOther) 
          oldrt rt 
      in
      if oldva != va then 
        raise (Failure "diferent vararg specifiers");
      (* If one does not have arguments, believe the one with the 
      * arguments *)
      let newargs = 
        if oldargs = None then args else
        if args = None then oldargs else
        let oldargslist = argsToList oldargs in
        let argslist = argsToList args in
        if List.length oldargslist <> List.length argslist then 
          raise (Failure "different number of arguments")
        else begin
          (* Go over the arguments and update the old ones with the 
          * adjusted types *)
          Some 
            (List.map2 
               (fun (on, ot, oa) (an, at, aa) -> 
                 (* Update the names. Always prefer the new name. This is 
                  * very important if the prototype uses different names than 
                  * the function definition. *)
                 let n = if an <> "" then an else on in
                 let t = 
                   combineTypes 
                     (if what = CombineFundef then 
                       CombineFunarg else CombineOther) 
                     ot at
                 in
                 let a = addAttributes oa aa in
                 (n, t, a))
               oldargslist argslist)
        end
      in
      TFun (newrt, newargs, oldva, cabsAddAttributes olda a)
        
  | TNamed (oldt, olda), TNamed (t, a) when oldt.tname = t.tname ->
      TNamed (oldt, cabsAddAttributes olda a)
        
  | TBuiltin_va_list olda, TBuiltin_va_list a -> 
      TBuiltin_va_list (cabsAddAttributes olda a)

        (* Unroll first the new type *)
  | _, TNamed (t, a) -> 
      let res = combineTypes what oldt t.ttype in
      cabsTypeAddAttributes a res
        
        (* And unroll the old type as well if necessary *)
  | TNamed (oldt, a), _ -> 
      let res = combineTypes what oldt.ttype t in
      cabsTypeAddAttributes a res
        
  | _ -> raise (Failure "different type constructors")


(* Create and cache varinfo's for globals. Starts with a varinfo but if the 
 * global has been declared already it might come back with another varinfo. 
 * Returns the varinfo to use (might be the old one), and an indication 
 * whether the variable exists already in the environment *)
let makeGlobalVarinfo (isadef: bool) (vi: varinfo) : varinfo * bool =
  try (* See if already defined, in the global environment. We could also 
       * look it up in the whole environment but in that case we might see a 
       * local. This can happen when we declare an extern variable with 
       * global scope but we are in a local scope. *)
    let oldvi, oldloc = lookupGlobalVar vi.vname in
    (* It was already defined. We must reuse the varinfo. But clean up the 
     * storage.  *)
    let newstorage = (** See 6.2.2 *)
      match oldvi.vstorage, vi.vstorage with
        (* Extern and something else is that thing *)
      | Extern, other
      | other, Extern -> other

      | NoStorage, other
      | other, NoStorage ->  other


      | _ ->
	  if vi.vstorage != oldvi.vstorage then
            ignore (warn
		      "Inconsistent storage specification for %s. Previous declaration: %a" 
		      vi.vname d_loc oldloc);
          vi.vstorage
    in
    oldvi.vinline <- oldvi.vinline || vi.vinline;
    oldvi.vstorage <- newstorage;
    (* Union the attributes *)
    oldvi.vattr <- cabsAddAttributes oldvi.vattr vi.vattr;
    begin 
      try
        oldvi.vtype <- 
           combineTypes 
             (if isadef then CombineFundef else CombineOther) 
             oldvi.vtype vi.vtype;
      with Failure reason -> 
        ignore (E.log "old type = %a\n" d_plaintype oldvi.vtype);
        ignore (E.log "new type = %a\n" d_plaintype vi.vtype);
        E.s (error "Declaration of %s does not match previous declaration from %a (%s)." 
               vi.vname d_loc oldloc reason)
    end;
      
    (* Found an old one. Keep the location always from the definition *)
    if isadef then begin 
      oldvi.vdecl <- vi.vdecl;
    end;
    oldvi, true
      
  with Not_found -> begin (* A new one.  *)
    (* Announce the name to the alpha conversion table. This will not 
     * actually change the name of the vi. See the definition of 
     * alphaConvertVarAndAddToEnv *)
    alphaConvertVarAndAddToEnv true vi, false
  end 

let conditionalConversion (t2: typ) (t3: typ) : typ =
  let tresult =  (* ISO 6.5.15 *)
    match unrollType t2, unrollType t3 with
      (TInt _ | TEnum _ | TFloat _), 
      (TInt _ | TEnum _ | TFloat _) -> 
        arithmeticConversion t2 t3 
    | TComp (comp2,_), TComp (comp3,_) 
          when comp2.ckey = comp3.ckey -> t2 
    | TPtr(_, _), TPtr(TVoid _, _) -> t2
    | TPtr(TVoid _, _), TPtr(_, _) -> t3
    | TPtr _, TPtr _ when Util.equals (typeSig t2) (typeSig t3) -> t2
    | TPtr _, TInt _  -> t2 (* most likely comparison with 0 *)
    | TInt _, TPtr _ -> t3 (* most likely comparison with 0 *)

          (* When we compare two pointers of diffent type, we combine them 
           * using the same algorithm when combining multiple declarations of 
           * a global *)
    | (TPtr _) as t2', (TPtr _ as t3') -> begin
        try combineTypes CombineOther t2' t3' 
        with Failure msg -> begin
          ignore (warn "A.QUESTION: %a does not match %a (%s)"
                    d_type (unrollType t2) d_type (unrollType t3) msg);
          t2 (* Just pick one *)
        end
    end
    | _, _ -> E.s (error "A.QUESTION for invalid combination of types")
  in
  tresult

(* Some utilitites for doing initializers *)

let debugInit = false

type preInit = 
  | NoInitPre
  | SinglePre of exp 
  | CompoundPre of int ref (* the maximum used index *)
                 * preInit array ref (* an array with initializers *)

(* Instructions on how to handle designators *)
type handleDesignators = 
  | Handle (* Handle them yourself *)
  | DoNotHandle (* Do not handle them your self *)
  | HandleAsNext (* First behave as if you have a NEXT_INIT. Useful for going 
                  * into nested designators *)
  | HandleFirst (* Handle only the first designator *)

(* Set an initializer *)
let rec setOneInit (this: preInit)
                   (o: offset) (e: exp) : preInit = 
  match o with 
    NoOffset -> SinglePre e
  | _ -> 
      let idx, (* Index in the current comp *)
          restoff (* Rest offset *) =
        match o with 
        | Index(Const(CInt64(i,_,_)), off) -> Int64.to_int i, off
        | Field (f, off) -> 
            (* Find the index of the field *)
            let rec loop (idx: int) = function
                [] -> E.s (bug "Cannot find field %s" f.fname)
              | f' :: _ when f'.fname = f.fname -> idx
              | _ :: restf -> loop (idx + 1) restf
            in
            loop 0 f.fcomp.cfields, off
        | _ -> E.s (bug "setOneInit: non-constant index")
      in
      let pMaxIdx, pArray = 
        match this  with 
          NoInitPre  -> (* No initializer so far here *)
            ref idx, ref (Array.create (max 32 (idx + 1)) NoInitPre)
              
        | CompoundPre (pMaxIdx, pArray) -> 
            if !pMaxIdx < idx then begin 
              pMaxIdx := idx;
              (* Maybe we also need to grow the array *)
              let l = Array.length !pArray in
              if l <= idx then begin
                let growBy = max (max 32 (idx + 1 - l)) (l / 2) in
                let newarray = Array.make (growBy + idx) NoInitPre in
                Array.blit !pArray 0 newarray 0 l;
                pArray := newarray
              end
            end;
            pMaxIdx, pArray
        | SinglePre e -> 
            E.s (unimp "Index %d is already initialized" idx)
      in
      assert (idx >= 0 && idx < Array.length !pArray);
      let this' = setOneInit !pArray.(idx) restoff e in
      !pArray.(idx) <- this';
      CompoundPre (pMaxIdx, pArray)


(* collect a CIL initializer, given the original syntactic initializer
 * 'preInit'; this returns a type too, since initialization of an array
 * with unspecified size actually changes the array's type
 * (ANSI C, 6.7.8, para 22) *)
let rec collectInitializer
    (this: preInit)
    (thistype: typ) : (init * typ) =
  if this = NoInitPre then (makeZeroInit thistype), thistype
  else
    match unrollType thistype, this with 
    | _ , SinglePre e -> SingleInit e, thistype
    | TArray (bt, leno, at), CompoundPre (pMaxIdx, pArray) -> 
        let (len: int), newtype =
          (* normal case: use array's declared length, newtype=thistype *)
          match leno with 
            Some len -> begin
              match constFold true len with 
                Const(CInt64(ni, _, _)) when ni >= 0L -> 
                  (Int64.to_int ni), TArray(bt,leno,at)

              | _ -> E.s (error "Array length is not a constant expression %a"
                            d_exp len)
            end
          | _ -> 
              (* unsized array case, length comes from initializers *)
              (!pMaxIdx + 1,
               TArray (bt, Some (integer (!pMaxIdx + 1)), at))
        in
        if !pMaxIdx >= len then 
          E.s (E.bug "collectInitializer: too many initializers(%d >= %d)\n"
                 !pMaxIdx len);
        (* len could be extremely big. So omit the last initializers, if they 
         * are many (more than 16) *)
(*
        ignore (E.log "collectInitializer: len = %d, pMaxIdx= %d\n"
                  len !pMaxIdx); *)
        let endAt = 
          if len - 1 > !pMaxIdx + 16 then 
            !pMaxIdx 
          else
            len - 1
        in
        (* Make one zero initializer to be used next *)
        let oneZeroInit = makeZeroInit bt in
        let rec collect (acc: (offset * init) list) (idx: int) = 
          if idx = -1 then acc
          else
            let thisi =
              if idx > !pMaxIdx then oneZeroInit
              else (fst (collectInitializer !pArray.(idx) bt))
            in
            collect ((Index(integer idx, NoOffset), thisi) :: acc) (idx - 1)
        in
        
        CompoundInit (newtype, collect [] endAt), newtype

    | TComp (comp, _), CompoundPre (pMaxIdx, pArray) when comp.cstruct ->
        let rec collect (idx: int) = function
            [] -> []
          | f :: restf -> 
              if f.fname = missingFieldName then 
                collect (idx + 1) restf
              else 
                let thisi = 
                  if idx > !pMaxIdx then 
                    makeZeroInit f.ftype
                  else
                    collectFieldInitializer !pArray.(idx) f
                in
                (Field(f, NoOffset), thisi) :: collect (idx + 1) restf
        in
        CompoundInit (thistype, collect 0 comp.cfields), thistype

    | TComp (comp, _), CompoundPre (pMaxIdx, pArray) when not comp.cstruct ->
        (* Find the field to initialize *)
        let rec findField (idx: int) = function
            [] -> E.s (bug "collectInitializer: union")
          | _ :: rest when idx < !pMaxIdx && !pArray.(idx) = NoInitPre -> 
              findField (idx + 1) rest
          | f :: _ when idx = !pMaxIdx -> 
              Field(f, NoOffset), 
              collectFieldInitializer !pArray.(idx) f
          | _ -> E.s (error "Can initialize only one field for union")
        in
        if !msvcMode && !pMaxIdx != 0 then 
          ignore (warn "On MSVC we can initialize only the first field of a union");
        CompoundInit (thistype, [ findField 0 comp.cfields ]), thistype

    | _ -> E.s (unimp "collectInitializer")
                      
and collectFieldInitializer 
    (this: preInit)
    (f: fieldinfo) : init =
  (* collect, and rewrite type *)
  let init,newtype = (collectInitializer this f.ftype) in
  f.ftype <- newtype;
  init
            

type stackElem = 
    InArray of offset * typ * int * int ref (* offset of parent, base type, 
                                             * length, current index. If the 
                                             * array length is unspecified we 
                                             * use Int.max_int  *)
  | InComp  of offset * compinfo * fieldinfo list (* offset of parent, 
                                                   base comp, current fields *)
    

(* A subobject is given by its address. The address is read from the end of 
 * the list (the bottom of the stack), starting with the current object *)
type subobj = { mutable stack: stackElem list; (* With each stack element we 
                                                * store the offset of its 
                                                * PARENT  *)
                mutable eof: bool; (* The stack is empty and we reached the 
                                    * end *)
                mutable soTyp: typ; (* The type of the subobject. Set using 
                                     * normalSubobj after setting stack. *)
                mutable soOff: offset; (* The offset of the subobject. Set 
                                        * using normalSubobj after setting 
                                        * stack.  *)
                        curTyp: typ; (* Type of current object. See ISO for 
                                      * the definition of the current object *)
                        curOff: offset; (* The offset of the current obj *)
                        host: varinfo; (* The host that we are initializing. 
                                        * For error messages *)
              }


(* Make a subobject iterator *)  
let rec makeSubobj 
    (host: varinfo) 
    (curTyp: typ)
    (curOff: offset) = 
  let so = 
    { host = host; curTyp = curTyp; curOff = curOff; 
      stack = []; eof = false;
      (* The next are fixed by normalSubobj *)
      soTyp = voidType; soOff = NoOffset } in
  normalSubobj so;
  so

  (* Normalize a stack so the we always point to a valid subobject. Do not 
   * descend into type *)
and normalSubobj (so: subobj) : unit = 
  match so.stack with 
    [] -> so.soOff <- so.curOff; so.soTyp <- so.curTyp 
        (* The array is over *)
  | InArray (parOff, bt, leno, current) :: rest ->
      if leno = !current then begin (* The array is over *)
        if debugInit then ignore (E.log "Past the end of array\n");
        so.stack <- rest; 
        advanceSubobj so
      end else begin
        so.soTyp <- bt;
        so.soOff <- addOffset (Index(integer !current, NoOffset)) parOff
      end

        (* The fields are over *)
  | InComp (parOff, comp, nextflds) :: rest -> 
      if nextflds == [] then begin (* No more fields here *)
        if debugInit then ignore (E.log "Past the end of structure\n");
        so.stack <- rest; 
        advanceSubobj so
      end else begin
        let fst = List.hd nextflds in
        so.soTyp <- fst.ftype;
        so.soOff <- addOffset (Field(fst, NoOffset)) parOff
      end

  (* Advance to the next subobject. Always apply to a normalized object *)
and advanceSubobj (so: subobj) : unit = 
  if so.eof then E.s (bug "advanceSubobj past end");
  match so.stack with
  | [] -> if debugInit then ignore (E.log "Setting eof to true\n"); 
          so.eof <- true 
  | InArray (parOff, bt, leno, current) :: rest -> 
      if debugInit then ignore (E.log "  Advancing to [%d]\n" (!current + 1));
      (* so.stack <- InArray (parOff, bt, leno, current + 1) :: rest; *)
      incr current;
      normalSubobj so

        (* The fields are over *)
  | InComp (parOff, comp, nextflds) :: rest -> 
      if debugInit then 
        ignore (E.log "Advancing past .%s\n" (List.hd nextflds).fname);
      let flds' = try List.tl nextflds with _ -> E.s (bug "advanceSubobj") in
      so.stack <- InComp(parOff, comp, flds') :: rest;
      normalSubobj so
        
        

(* Find the fields to initialize in a composite. *)
let fieldsToInit 
    (comp: compinfo) 
    (designator: string option) 
    : fieldinfo list = 
  (* Never look at anonymous fields *)
  let flds1 = 
    List.filter (fun f -> f.fname <> missingFieldName) comp.cfields in
  let flds2 = 
    match designator with 
      None -> flds1
    | Some fn -> 
        let rec loop = function
            [] -> E.s (error "Cannot find designated field %s" fn)
          | (f :: _) as nextflds when f.fname = fn -> nextflds
          | _ :: rest -> loop rest
        in
        loop flds1
  in
  (* If it is a union we only initialize one field *)
  match flds2 with 
    [] -> []
  | (f :: rest) as toinit -> 
      if comp.cstruct then toinit else [f]
        

let integerArrayLength (leno: exp option) : int = 
  match leno with
    None -> max_int
  | Some len -> begin
      try lenOfArray leno 
      with LenOfArray -> 
        E.s (error "Initializing non-constant-length array\n  length=%a\n"
               d_exp len)
  end

(* sm: I'm sure something like this already exists, but ... *)
let isNone (o : 'a option) : bool =
  match o with
  | None -> true
  | Some _ -> false


let annonCompFieldNameId = ref 0
let annonCompFieldName = "__annonCompField"
 
                   

(* Utility ***)
let rec replaceLastInList 
    (lst: A.expression list) 
    (how: A.expression -> A.expression) : A.expression list= 
  match lst with
    [] -> []
  | [e] -> [how e]
  | h :: t -> h :: replaceLastInList t how





let convBinOp (bop: A.binary_operator) : binop =
  match bop with
    A.ADD -> PlusA
  | A.SUB -> MinusA
  | A.MUL -> Mult
  | A.DIV -> Div
  | A.MOD -> Mod
  | A.BAND -> BAnd
  | A.BOR -> BOr
  | A.XOR -> BXor
  | A.SHL -> Shiftlt
  | A.SHR -> Shiftrt
  | A.EQ -> Eq
  | A.NE -> Ne
  | A.LT -> Lt
  | A.LE -> Le
  | A.GT -> Gt
  | A.GE -> Ge
  | _ -> E.s (error "convBinOp")

(**** PEEP-HOLE optimizations ***)
let afterConversion (c: chunk) : chunk = 
  (* Now scan the statements and find Instr blocks *)

  (** We want to collapse sequences of the form "tmp = f(); v = tmp". This 
   * will help significantly with the handling of calls to malloc, where it 
   * is important to have the cast at the same place as the call *)
  let collapseCallCast = function
      Call(Some(Var vi, NoOffset), f, args, l),
      Set(destlv, CastE (newt, Lval(Var vi', NoOffset)), _) 
      when (not vi.vglob && 
            String.length vi.vname >= 3 &&
            (* Watch out for the possibility that we have an implied cast in 
             * the call *)
           (let tcallres = 
              match unrollType (typeOf f) with
                 TFun (rt, _, _, _) -> rt
               | _ -> E.s (E.bug "Function call to a non-function")
           in 
           Util.equals (typeSig tcallres) (typeSig vi.vtype) &&
           Util.equals (typeSig newt) (typeSig (typeOfLval destlv))) && 
           IH.mem callTempVars vi.vid &&
           vi' == vi) 
      -> Some [Call(Some destlv, f, args, l)]
    | i1,i2 ->  None
  in
  (* First add in the postins *)
  let sl = pushPostIns c in
  peepHole2 collapseCallCast sl;
  { c with stmts = sl; postins = [] }

(***** Try to suggest a name for the anonymous structures *)
let suggestAnonName (nl: A.name list) = 
  match nl with 
    [] -> ""
  | (n, _, _, _) :: _ -> n


(** Optional constant folding of binary operations *)
let optConstFoldBinOp (machdep: bool) (bop: binop) 
                      (e1: exp) (e2:exp) (t: typ) = 
  if !lowerConstants then 
    constFoldBinOp machdep bop e1 e2 t
  else
    BinOp(bop, e1, e2, t)
  
(****** TYPE SPECIFIERS *******)
let rec doSpecList (suggestedAnonName: string) (* This string will be part of 
                                                * the names for anonymous 
                                                * structures and enums  *)
                   (specs: A.spec_elem list) 
       (* Returns the base type, the storage, whether it is inline and the 
        * (unprocessed) attributes *)
    : typ * storage * bool * A.attribute list =
  (* Do one element and collect the type specifiers *)
  let isinline = ref false in (* If inline appears *)
  (* The storage is placed here *)
  let storage : storage ref = ref NoStorage in

  (* Collect the attributes.  Unfortunately, we cannot treat GCC
   * __attributes__ and ANSI C const/volatile the same way, since they
   * associate with structures differently.  Specifically, ANSI 
   * qualifiers never apply to structures (ISO 6.7.3), whereas GCC
   * attributes always do (GCC manual 4.30).  Therefore, they are 
   * collected and processed separately. *)
  let attrs : A.attribute list ref = ref [] in      (* __attribute__, etc. *)
  let cvattrs : A.cvspec list ref = ref [] in       (* const/volatile *)

  let doSpecElem (se: A.spec_elem)
                 (acc: A.typeSpecifier list) 
                  : A.typeSpecifier list = 
    match se with 
      A.SpecTypedef -> acc
    | A.SpecInline -> isinline := true; acc
    | A.SpecStorage st ->
        if !storage <> NoStorage then 
          E.s (error "Multiple storage specifiers");
        let sto' = 
          match st with
            A.NO_STORAGE -> NoStorage
          | A.AUTO -> NoStorage
          | A.REGISTER -> Register
          | A.STATIC -> Static
          | A.EXTERN -> Extern
        in
        storage := sto';
        acc

    | A.SpecCV cv -> cvattrs := cv :: !cvattrs; acc
    | A.SpecAttr a -> attrs := a :: !attrs; acc
    | A.SpecType ts -> ts :: acc
    | A.SpecPattern _ -> E.s (E.bug "SpecPattern in cabs2cil input")
  in
  (* Now scan the list and collect the type specifiers. Preserve the order *)
  let tspecs = List.fold_right doSpecElem specs [] in
  
  let tspecs' = 
    (* GCC allows a named type that appears first to be followed by things 
     * like "short", "signed", "unsigned" or "long". *)
    match tspecs with 
      A.Tnamed n :: (_ :: _ as rest) when not !msvcMode -> 
        (* If rest contains "short" or "long" then drop the Tnamed *)
        if List.exists (function A.Tshort -> true 
                               | A.Tlong -> true | _ -> false) rest then
          rest
        else
          tspecs

    | _ -> tspecs
  in
  (* Sort the type specifiers *)
  let sortedspecs = 
    let order = function (* Don't change this *)
      | A.Tvoid -> 0
      | A.Tsigned -> 1
      | A.Tunsigned -> 2
      | A.Tchar -> 3
      | A.Tshort -> 4
      | A.Tlong -> 5
      | A.Tint -> 6
      | A.Tint64 -> 7
      | A.Tfloat -> 8
      | A.Tdouble -> 9
      | _ -> 10 (* There should be at most one of the others *)
    in
    List.stable_sort (fun ts1 ts2 -> compare (order ts1) (order ts2)) tspecs' 
  in
  let getTypeAttrs () : A.attribute list =
    (* Partitions the attributes in !attrs.
       Type attributes are removed from attrs and returned, so that they
       can go into the type definition.  Name attributes are left in attrs,
       so they will be returned by doSpecAttr and used in the variable 
       declaration. 
       Testcase: small1/attr9.c *)
    let an, af, at = cabsPartitionAttributes ~default:AttrType !attrs in
    attrs := an;      (* Save the name attributes for later *)
    if af <> [] then
      E.s (error "Invalid position for function type attributes.");
    at
  in 

  (* And now try to make sense of it. See ISO 6.7.2 *)
  let bt = 
    match sortedspecs with
      [A.Tvoid] -> TVoid []
    | [A.Tchar] -> TInt(IChar, [])
    | [A.Tsigned; A.Tchar] -> TInt(ISChar, [])
    | [A.Tunsigned; A.Tchar] -> TInt(IUChar, [])

    | [A.Tshort] -> TInt(IShort, [])
    | [A.Tsigned; A.Tshort] -> TInt(IShort, [])
    | [A.Tshort; A.Tint] -> TInt(IShort, [])
    | [A.Tsigned; A.Tshort; A.Tint] -> TInt(IShort, [])

    | [A.Tunsigned; A.Tshort] -> TInt(IUShort, [])
    | [A.Tunsigned; A.Tshort; A.Tint] -> TInt(IUShort, [])

    | [] -> TInt(IInt, [])
    | [A.Tint] -> TInt(IInt, [])
    | [A.Tsigned] -> TInt(IInt, [])
    | [A.Tsigned; A.Tint] -> TInt(IInt, [])

    | [A.Tunsigned] -> TInt(IUInt, [])
    | [A.Tunsigned; A.Tint] -> TInt(IUInt, [])

    | [A.Tlong] -> TInt(ILong, [])
    | [A.Tsigned; A.Tlong] -> TInt(ILong, [])
    | [A.Tlong; A.Tint] -> TInt(ILong, [])
    | [A.Tsigned; A.Tlong; A.Tint] -> TInt(ILong, [])

    | [A.Tunsigned; A.Tlong] -> TInt(IULong, [])
    | [A.Tunsigned; A.Tlong; A.Tint] -> TInt(IULong, [])

    | [A.Tlong; A.Tlong] -> TInt(ILongLong, [])
    | [A.Tsigned; A.Tlong; A.Tlong] -> TInt(ILongLong, [])
    | [A.Tlong; A.Tlong; A.Tint] -> TInt(ILongLong, [])
    | [A.Tsigned; A.Tlong; A.Tlong; A.Tint] -> TInt(ILongLong, [])

    | [A.Tunsigned; A.Tlong; A.Tlong] -> TInt(IULongLong, [])
    | [A.Tunsigned; A.Tlong; A.Tlong; A.Tint] -> TInt(IULongLong, [])

    (* int64 is to support MSVC *)
    | [A.Tint64] -> TInt(ILongLong, [])
    | [A.Tsigned; A.Tint64] -> TInt(ILongLong, [])

    | [A.Tunsigned; A.Tint64] -> TInt(IULongLong, [])

    | [A.Tfloat] -> TFloat(FFloat, [])
    | [A.Tdouble] -> TFloat(FDouble, [])

    | [A.Tlong; A.Tdouble] -> TFloat(FLongDouble, [])

     (* Now the other type specifiers *)
    | [A.Tnamed n] -> begin
        if n = "__builtin_va_list" && 
          Machdep.gccHas__builtin_va_list then begin
            TBuiltin_va_list []
        end else
          let t = 
            match lookupType "type" n with 
              (TNamed _) as x, _ -> x
            | typ -> E.s (error "Named type %s is not mapped correctly\n" n)
          in
          t
    end

    | [A.Tstruct (n, None, _)] -> (* A reference to a struct *)
        if n = "" then E.s (error "Missing struct tag on incomplete struct");
        findCompType "struct" n []
    | [A.Tstruct (n, Some nglist, extraAttrs)] -> (* A definition of a struct *)
      let n' =
        if n <> "" then n else anonStructName "struct" suggestedAnonName in
      (* Use the (non-cv, non-name) attributes in !attrs now *)
      let a = extraAttrs @ (getTypeAttrs ()) in
      makeCompType true n' nglist (doAttributes a)

    | [A.Tunion (n, None, _)] -> (* A reference to a union *)
        if n = "" then E.s (error "Missing union tag on incomplete union");
        findCompType "union" n []
    | [A.Tunion (n, Some nglist, extraAttrs)] -> (* A definition of a union *)
        let n' =
          if n <> "" then n else anonStructName "union" suggestedAnonName in
        (* Use the attributes now *)
        let a = extraAttrs @ (getTypeAttrs ()) in
        makeCompType false n' nglist (doAttributes a)

    | [A.Tenum (n, None, _)] -> (* Just a reference to an enum *)
        if n = "" then E.s (error "Missing enum tag on incomplete enum");
        findCompType "enum" n []

    | [A.Tenum (n, Some eil, extraAttrs)] -> (* A definition of an enum *)
        let n' =
          if n <> "" then n else anonStructName "enum" suggestedAnonName in
        (* make a new name for this enumeration *)
        let n'', _  = newAlphaName true "enum" n' in

        (* Create the enuminfo, or use one that was created already for a
         * forward reference *)
        let enum, _ = createEnumInfo n'' in 
        let a = extraAttrs @ (getTypeAttrs ()) in 
        enum.eattr <- doAttributes a;
        let res = TEnum (enum, []) in

        (* sm: start a scope for the enum tag values, since they *
        * can refer to earlier tags *)
        enterScope ();
        
        (* as each name,value pair is determined, this is called *)
        let rec processName kname (i: exp) loc rest = begin
          (* add the name to the environment, but with a faked 'typ' field; 
           * we don't know the full type yet (since that includes all of the 
           * tag values), but we won't need them in here  *)
          addLocalToEnv kname (EnvEnum (i, res));
          
          (* add this tag to the list so that it ends up in the real 
          * environment when we're finished  *)
          let newname, _  = newAlphaName true "" kname in
          
          (kname, (newname, i, loc)) :: loop (increm i 1) rest
        end
            
        and loop i = function
            [] -> []
          | (kname, A.NOTHING, cloc) :: rest ->
              (* use the passed-in 'i' as the value, since none specified *)
              processName kname i (convLoc cloc) rest
                
          | (kname, e, cloc) :: rest ->
              (* constant-eval 'e' to determine tag value *)
              let e' = getIntConstExp e in
              let e' = 
                match isInteger (constFold true e') with 
                  Some i -> if !lowerConstants then kinteger64 IInt i else e'
                | _ -> E.s (error "Constant initializer %a not an integer" d_exp e')
              in
              processName kname e' (convLoc cloc) rest
        in
        
        (* sm: now throw away the environment we built for eval'ing the enum 
        * tags, so we can add to the new one properly  *)
        exitScope ();
        
        let fields = loop zero eil in
        (* Now set the right set of items *)
        enum.eitems <- List.map (fun (_, x) -> x) fields;
        (* Record the enum name in the environment *)
        addLocalToEnv (kindPlusName "enum" n'') (EnvTyp res);
        (* And define the tag *)
        cabsPushGlobal (GEnumTag (enum, !currentLoc));
        res
        
          
    | [A.TtypeofE e] -> 
        let (c, e', t) = doExp false e AExpLeaveArrayFun in
        let t' = 
          match e' with 
            StartOf(lv) -> typeOfLval lv
                (* If this is a string literal, then we treat it as in sizeof*)
          | Const (CStr s) -> begin
              match typeOf e' with 
                TPtr(bt, _) -> (* This is the type of array elements *)
                  TArray(bt, Some (SizeOfStr s), [])
              | _ -> E.s (bug "The typeOf a string is not a pointer type")
          end
          | _ -> t
        in
(*
        ignore (E.log "typeof(%a) = %a\n" d_exp e' d_plaintype t');
*)
        t'

    | [A.TtypeofT (specs, dt)] -> 
        let typ = doOnlyType specs dt in
        typ

    | _ -> 
        E.s (error "Invalid combination of type specifiers")
  in
  bt,!storage,!isinline,List.rev (!attrs @ (convertCVtoAttr !cvattrs))
                                                           
(* given some cv attributes, convert them into named attributes for
 * uniform processing *)
and convertCVtoAttr (src: A.cvspec list) : A.attribute list =
  match src with
  | [] -> []
  | CV_CONST    :: tl -> ("const",[])    :: (convertCVtoAttr tl)
  | CV_VOLATILE :: tl -> ("volatile",[]) :: (convertCVtoAttr tl)
  | CV_RESTRICT :: tl -> ("restrict",[]) :: (convertCVtoAttr tl)


and makeVarInfoCabs 
                ~(isformal: bool)
                ~(isglobal: bool) 
		(ldecl : location)
                (bt, sto, inline, attrs)
                (n,ndt,a) 
      : varinfo = 
  let vtype, nattr = 
    doType (AttrName false) bt (A.PARENTYPE(attrs, ndt, a)) in
  if inline && not (isFunctionType vtype) then
    ignore (error "inline for a non-function: %s" n);
  let t = 
    if not isglobal && not isformal then begin
      (* Sometimes we call this on the formal argument of a function with no 
       * arguments. Don't call stripConstLocalType in that case *)
(*      ignore (E.log "stripConstLocalType(%a) for %s\n" d_type vtype n); *)
      stripConstLocalType vtype
    end else 
      vtype
  in
  let vi = makeVarinfo isglobal n t in
  vi.vstorage <- sto;
  vi.vattr <- nattr;
  vi.vdecl <- ldecl;

  if false then 
    ignore (E.log "Created varinfo %s : %a\n" vi.vname d_type vi.vtype); 

  vi

(* Process a local variable declaration and allow variable-sized arrays *)
and makeVarSizeVarInfo (ldecl : location)
                       spec_res
                       (n,ndt,a)
   : varinfo * chunk * exp * bool = 
  if not !msvcMode then 
    match isVariableSizedArray ndt with
      None -> 
        makeVarInfoCabs ~isformal:false 
                        ~isglobal:false 
                        ldecl spec_res (n,ndt,a), empty, zero, false
    | Some (ndt', se, len) -> 
        makeVarInfoCabs ~isformal:false 
                        ~isglobal:false 
                        ldecl spec_res (n,ndt',a), se, len, true
  else
    makeVarInfoCabs ~isformal:false
                    ~isglobal:false 
                    ldecl spec_res (n,ndt,a), empty, zero, false

and doAttr (a: A.attribute) : attribute list = 
  (* Strip the leading and trailing underscore *)
  let stripUnderscore (n: string) : string = 
    let l = String.length n in
    let rec start i = 
      if i >= l then 
        E.s (error "Invalid attribute name %s" n);
      if String.get n i = '_' then start (i + 1) else i
    in
    let st = start 0 in
    let rec finish i = 
      (* We know that we will stop at >= st >= 0 *)
      if String.get n i = '_' then finish (i - 1) else i
    in
    let fin = finish (l - 1) in
    String.sub n st (fin - st + 1)
  in
  match a with
  | (s, []) -> [Attr (stripUnderscore s, [])]
  | (s, el) -> 
      
      let rec attrOfExp (strip: bool) 
                        ?(foldenum=true) 
                        (a: A.expression) : attrparam =
        match a with
          A.VARIABLE n -> begin
            let n' = if strip then stripUnderscore n else n in
            (** See if this is an enumeration *)
            try
              if not foldenum then raise Not_found;

              match H.find env n' with 
                EnvEnum (tag, _), _ -> begin
                  match isInteger (constFold true tag) with 
                    Some i64 when !lowerConstants -> AInt (Int64.to_int i64)
                  |  _ -> ACons(n', [])
                end
              | _ -> ACons (n', [])
            with Not_found -> ACons(n', [])
          end
        | A.CONSTANT (A.CONST_STRING s) -> AStr s
        | A.CONSTANT (A.CONST_INT str) -> AInt (int_of_string str)
        | A.CALL(A.VARIABLE n, args) -> begin
            let n' = if strip then stripUnderscore n else n in
            let ae' = List.map ae args in
            ACons(n', ae')
        end
        | A.EXPR_SIZEOF e -> ASizeOfE (ae e)
        | A.TYPE_SIZEOF (bt, dt) -> ASizeOf (doOnlyType bt dt)
        | A.EXPR_ALIGNOF e -> AAlignOfE (ae e)
        | A.TYPE_ALIGNOF (bt, dt) -> AAlignOf (doOnlyType bt dt)
        | A.BINARY(A.AND, aa1, aa2) -> 
            ABinOp(LAnd, ae aa1, ae aa2)
        | A.BINARY(A.OR, aa1, aa2) -> 
            ABinOp(LOr, ae aa1, ae aa2)
        | A.BINARY(abop, aa1, aa2) -> 
            ABinOp (convBinOp abop, ae aa1, ae aa2)
        | A.UNARY(A.PLUS, aa) -> ae aa
        | A.UNARY(A.MINUS, aa) -> AUnOp (Neg, ae aa)
        | A.UNARY(A.BNOT, aa) -> AUnOp(BNot, ae aa)
        | A.UNARY(A.NOT, aa) -> AUnOp(LNot, ae aa)
        | A.MEMBEROF (e, s) -> ADot (ae e, s)
        | _ -> 
            ignore (E.log "Invalid expression in attribute: ");
            withCprint Cprint.print_expression a;
            E.s (error "cabs2cil: invalid expression")

      and ae (e: A.expression) = attrOfExp false e in

      (* Sometimes we need to convert attrarg into attr *)
      let arg2attr = function
        | ACons (s, args) -> Attr (s, args)
        | a -> 
            E.s (error "Invalid form of attribute: %a"
                   d_attrparam a);
      in
      if s = "__attribute__" then (* Just a wrapper for many attributes*)
        List.map (fun e -> arg2attr (attrOfExp true ~foldenum:false e)) el
      else if s = "__blockattribute__" then (* Another wrapper *)
        List.map (fun e -> arg2attr (attrOfExp true ~foldenum:false e)) el
      else if s = "__declspec" then
        List.map (fun e -> arg2attr (attrOfExp false ~foldenum:false e)) el
      else
        [Attr(stripUnderscore s, List.map (attrOfExp ~foldenum:false false) el)]

and doAttributes (al: A.attribute list) : attribute list =
  List.fold_left (fun acc a -> cabsAddAttributes (doAttr a) acc) [] al

(* A version of Cil.partitionAttributes that works on CABS attributes.
   It would  be better to use Cil.partitionAttributes instead to avoid
   the extra doAttr conversions here, but that's hard to do in doSpecList.*)
and cabsPartitionAttributes 
    ~(default:attributeClass)  
    (attrs:  A.attribute list) :
    A.attribute list * A.attribute list * A.attribute list = 
  let rec loop (n,f,t) = function
      [] -> n, f, t
    | a :: rest -> 
        let kind = match doAttr a with 
            [] -> default
          | Attr(an, _)::_ -> 
              (try H.find attributeHash an with Not_found -> default)
        in
        match kind with 
          AttrName _ -> loop (a::n, f, t) rest
        | AttrFunType _ -> 
            loop (n, a::f, t) rest
        | AttrType -> loop (n, f, a::t) rest
  in
  loop ([], [], []) attrs



and doType (nameortype: attributeClass) (* This is AttrName if we are doing 
                                         * the type for a name, or AttrType 
                                         * if we are doing this type in a 
                                         * typedef *)
           (bt: typ)                    (* The base type *)
           (dt: A.decl_type) 
  (* Returns the new type and the accumulated name (or type attribute 
    if nameoftype =  AttrType) attributes *)
  : typ * attribute list = 

  (* Now do the declarator type. But remember that the structure of the 
   * declarator type is as printed, meaning that it is the reverse of the 
   * right one *)
  let rec doDeclType (bt: typ) (acc: attribute list) = function
      A.JUSTBASE -> bt, acc
    | A.PARENTYPE (a1, d, a2) -> 
        let a1' = doAttributes a1 in
        let a1n, a1f, a1t = partitionAttributes AttrType a1' in
        let a2' = doAttributes a2 in
        let a2n, a2f, a2t = partitionAttributes nameortype a2' in
(*
        ignore (E.log "doType: %a @[a1n=%a@!a1f=%a@!a1t=%a@!a2n=%a@!a2f=%a@!a2t=%a@]@!" d_loc !currentLoc d_attrlist a1n d_attrlist a1f d_attrlist a1t d_attrlist a2n d_attrlist a2f d_attrlist a2t);
*)
        let bt' = cabsTypeAddAttributes a1t bt in
(*
        ignore (E.log "bt' = %a\n" d_type bt');
*)
        let bt'', a1fadded = 
          match unrollType bt with 
            TFun _ -> cabsTypeAddAttributes a1f bt', true
          | _ -> bt', false
        in
        (* Now recurse *)
        let restyp, nattr = doDeclType bt'' acc d in
        (* Add some more type attributes *)
        let restyp = cabsTypeAddAttributes a2t restyp in
        (* See if we can add some more type attributes *)
        let restyp' = 
          match unrollType restyp with 
            TFun _ -> 
              if a1fadded then
                cabsTypeAddAttributes a2f restyp
              else
                cabsTypeAddAttributes a2f
                  (cabsTypeAddAttributes a1f restyp)
          | TPtr ((TFun _ as tf), ap) when not !msvcMode ->
              if a1fadded then
                TPtr(cabsTypeAddAttributes a2f tf, ap)
              else
                TPtr(cabsTypeAddAttributes a2f
                       (cabsTypeAddAttributes a1f tf), ap)
          | _ -> 
              if a1f <> [] && not a1fadded then
                E.s (error "Invalid position for (prefix) function type attributes:%a" 
                       d_attrlist a1f);
              if a2f <> [] then
                E.s (error "Invalid position for (post) function type attributes:%a"
                       d_attrlist a2f);
              restyp
        in
(*
           ignore (E.log "restyp' = %a\n" d_type restyp');
*)
        (* Now add the name attributes and return *)
        restyp', cabsAddAttributes a1n (cabsAddAttributes a2n nattr)

    | A.PTR (al, d) -> 
        let al' = doAttributes al in
        let an, af, at = partitionAttributes AttrType al' in
        (* Now recurse *)
        let restyp, nattr = doDeclType (TPtr(bt, at)) acc d in
        (* See if we can do anything with function type attributes *)
        let restyp' = 
          match unrollType restyp with
            TFun _ -> cabsTypeAddAttributes af restyp
          | TPtr((TFun _ as tf), ap) ->
              TPtr(cabsTypeAddAttributes af tf, ap)
          | _ -> 
              if af <> [] then
                E.s (error "Invalid position for function type attributes:%a"
                       d_attrlist af);
              restyp
        in
        (* Now add the name attributes and return *)
        restyp', cabsAddAttributes an nattr
              

    | A.ARRAY (d, al, len) -> 
        let lo = 
          match len with 
            A.NOTHING -> None 
          | _ -> 
              let len' = doPureExp len in
              let _, len'' = castTo (typeOf len') intType len' in
              let elsz = 
                try (bitsSizeOf bt + 7) / 8
                with _ -> 1 (** We get this if we cannot compute the size of 
                             * one element. This can happen, when we define 
                             * an extern, for example. We use 1 for now *)
              in 
              (match constFold true len' with 
                Const(CInt64(i, _, _)) ->
                  if i < 0L then 
                    E.s (error "Length of array is negative\n");
                  if Int64.mul i (Int64.of_int elsz) >= 0x80000000L then 
                    E.s (error "Length of array is too large\n")
           

                | l -> 
                    if isConstant l then 
                      (* e.g., there may be a float constant involved. 
                       * We'll leave it to the user to ensure the length is
                       * non-negative, etc.*)
                      ignore(warn "Unable to do constant-folding on array length %a.  Some CIL operations on this array may fail."
                               d_exp l)
                    else 
                      E.s (error "Length of array is not a constant: %a\n"
                             d_exp l));
              Some len''
        in
	let al' = doAttributes al in
        doDeclType (TArray(bt, lo, al')) acc d

    | A.PROTO (d, args, isva) -> 
        (* Start a scope for the parameter names *)
        enterScope ();
        (* Intercept the old-style use of varargs.h. On GCC this means that 
         * we have ellipsis and a last argument "builtin_va_alist: 
         * builtin_va_alist_t". On MSVC we do not have the ellipsis and we 
         * have a last argument "va_alist: va_list" *)
        let args', isva' = 
          if args != [] && !msvcMode = not isva then begin
            let newisva = ref isva in 
            let rec doLast = function
                [([A.SpecType (A.Tnamed atn)], (an, A.JUSTBASE, [], _))] 
                  when isOldStyleVarArgTypeName atn && 
                       isOldStyleVarArgName an -> begin
                         (* Turn it into a vararg *)
                         newisva := true;
                         (* And forget about this argument *)
                         []
                       end
                         
              | a :: rest -> a :: doLast rest
              | [] -> []
            in
            let args' = doLast args in
            (args', !newisva)
          end else (args, isva)
        in
        (* Make the argument as for a formal *)
        let doOneArg (s, (n, ndt, a, cloc)) : varinfo = 
          let s' = doSpecList n s in
          let ndt' =  match isVariableSizedArray ndt with
              None -> ndt
            | Some (ndt', se, len) -> 
                (* If this is a variable-sized array, we replace the array
                   type with a pointer type.  This is the defined behavior
                   for array parameters, so we do not need to add this to
                   varSizeArrays, fix sizeofs, etc. *)
                if isNotEmpty se then
                  E.s (error "array parameter: length not pure");
                ndt'
          in              
          let vi = makeVarInfoCabs ~isformal:true ~isglobal:false 
                     (convLoc cloc) s' (n,ndt',a) in
          (* Add the formal to the environment, so it can be referenced by
             other formals  (e.g. in an array type, although that will be
             changed to a pointer later, or though typeof).  *) 
          addLocalToEnv vi.vname (EnvVar vi);
          vi
        in
        let targs : varinfo list option = 
          match List.map doOneArg args'  with
          | [] -> None (* No argument list *)
          | [t] when isVoidType t.vtype -> 
              Some []
          | l -> Some l
        in
        exitScope ();
        (* Turn [] types into pointers in the arguments and the result type. 
         * Turn function types into pointers to respective. This simplifies 
         * our life a lot, and is what the standard requires. *)
        let rec fixupArgumentTypes (argidx: int) (args: varinfo list) : unit = 
          match args with
            [] -> ()
          | a :: args' -> 
              (match unrollType a.vtype with
                TArray(t,_,attr) -> a.vtype <- TPtr(t, attr)
              | TFun _ -> a.vtype <- TPtr(a.vtype, [])
              | TComp (comp, _) -> begin
                  match isTransparentUnion a.vtype with
                    None ->  ()
                  | Some fstfield -> 
                      transparentUnionArgs := 
                         (argidx, a.vtype) :: !transparentUnionArgs;
                      a.vtype <- fstfield.ftype;
              end
              | _ -> ());
              fixupArgumentTypes (argidx + 1) args'
        in
        let args = 
          match targs with 
            None -> None
          | Some argl -> 
              fixupArgumentTypes 0 argl;
              Some (List.map (fun a -> (a.vname, a.vtype, a.vattr)) argl)
        in
        let tres = 
          match unrollType bt with
            TArray(t,_,attr) -> TPtr(t, attr)
          | _ -> bt
        in
        doDeclType (TFun (tres, args, isva', [])) acc d

  in
  doDeclType bt [] dt

(* If this is a declarator for a variable size array then turn it into a 
   pointer type and a length *)
and isVariableSizedArray (dt: A.decl_type) 
    : (A.decl_type * chunk * exp) option = 
  let res = ref None in
  let rec findArray = function
    ARRAY (JUSTBASE, al, lo) when lo != A.NOTHING -> 
      (* Try to compile the expression to a constant *)
      let (se, e', _) = doExp true lo (AExp (Some intType)) in
      if isNotEmpty se || not (isConstant e') then begin
        res := Some (se, e');
        PTR (al, JUSTBASE)
      end else 
        ARRAY (JUSTBASE, al, lo)
    | ARRAY (dt, al, lo) -> ARRAY (findArray dt, al, lo)
    | PTR (al, dt) -> PTR (al, findArray dt)
    | JUSTBASE -> JUSTBASE
    | PARENTYPE (prea, dt, posta) -> PARENTYPE (prea, findArray dt, posta)
    | PROTO (dt, f, a) -> PROTO (findArray dt, f, a)
  in
  let dt' = findArray dt in
  match !res with 
    None -> None
  | Some (se, e) -> Some (dt', se, e)

and doOnlyType (specs: A.spec_elem list) (dt: A.decl_type) : typ = 
  let bt',sto,inl,attrs = doSpecList "" specs in
  if sto <> NoStorage || inl then
    E.s (error "Storage or inline specifier in type only");
  let tres, nattr = doType AttrType bt' (A.PARENTYPE(attrs, dt, [])) in
  if nattr <> [] then
    E.s (error "Name attributes in only_type: %a"
           d_attrlist nattr);
  tres


and makeCompType (isstruct: bool)
                 (n: string)
                 (nglist: A.field_group list) 
                 (a: attribute list) = 
  (* Make a new name for the structure *)
  let kind = if isstruct then "struct" else "union" in
  let n', _  = newAlphaName true kind n in
  (* Create the self cell for use in fields and forward references. Or maybe 
   * one exists already from a forward reference  *)
  let comp, _ = createCompInfo isstruct n' in
  let doFieldGroup ((s: A.spec_elem list), 
                    (nl: (A.name * A.expression option) list)) : 'a list =
    (* Do the specifiers exactly once *)
    let sugg = match nl with 
      [] -> ""
    | ((n, _, _, _), _) :: _ -> n
    in
    let bt, sto, inl, attrs = doSpecList sugg s in
    (* Do the fields *)
    let makeFieldInfo
        (((n,ndt,a,cloc) : A.name), (widtho : A.expression option))
      : fieldinfo = 
      if sto <> NoStorage || inl then 
        E.s (error "Storage or inline not allowed for fields");
      let ftype, nattr = 
        doType (AttrName false) bt (A.PARENTYPE(attrs, ndt, a)) in 
      (* check for fields whose type is an undefined struct.  This rules
         out circularity:
             struct C1 { struct C2 c2; };          //This line is now an error.
             struct C2 { struct C1 c1; int dummy; };
       *)
      (match unrollType ftype with
         TComp (ci',_) when not ci'.cdefined ->
           E.s (error "Type of field %s is an undefined struct.\n" n)
       | _ -> ());
      let width = 
        match widtho with 
          None -> None
        | Some w -> begin
            (match unrollType ftype with
              TInt (ikind, a) -> ()
            | TEnum _ -> ()
            | _ -> E.s (error "Base type for bitfield is not an integer type"));
            match isIntegerConstant w with
                Some n -> Some n
              | None -> E.s (error "bitfield width is not an integer constant")
	  end
      in
      (* If the field is unnamed and its type is a structure of union type 
       * then give it a distinguished name  *)
      let n' = 
        if n = missingFieldName then begin
          match unrollType ftype with 
            TComp _ -> begin
              incr annonCompFieldNameId;
              annonCompFieldName ^ (string_of_int !annonCompFieldNameId)
            end 
          | _ -> n
        end else
          n
      in
      { fcomp     =  comp;
        fname     =  n';
        ftype     =  ftype;
        fbitfield =  width;
        fattr     =  nattr;
        floc      =  convLoc cloc
      } 
    in
    List.map makeFieldInfo nl
  in


  let flds = List.concat (List.map doFieldGroup nglist) in
  if comp.cfields <> [] then begin
    (* This appears to be a multiply defined structure. This can happen from 
    * a construct like "typedef struct foo { ... } A, B;". This is dangerous 
    * because at the time B is processed some forward references in { ... } 
    * appear as backward references, which coild lead to circularity in 
    * the type structure. We do a thourough check and then we reuse the type 
    * for A *)
    let fieldsSig fs = List.map (fun f -> typeSig f.ftype) fs in 
    if not (Util.equals (fieldsSig comp.cfields) (fieldsSig flds)) then
      ignore (error "%s seems to be multiply defined" (compFullName comp))
  end else 
    comp.cfields <- flds;

(*  ignore (E.log "makeComp: %s: %a\n" comp.cname d_attrlist a); *)
  comp.cattr <- a;
  let res = TComp (comp, []) in
  (* This compinfo is defined, even if there are no fields *)
  comp.cdefined <- true;
  (* Create a typedef for this one *)
  cabsPushGlobal (GCompTag (comp, !currentLoc));

      (* There must be a self cell created for this already *)
  addLocalToEnv (kindPlusName kind n) (EnvTyp res);
  (* Now create a typedef with just this type *)
  res

and preprocessCast (specs: A.specifier) 
                   (dt: A.decl_type) 
                   (ie: A.init_expression) 
  : A.specifier * A.decl_type * A.init_expression = 
  let typ = doOnlyType specs dt in
  (* If we are casting to a union type then we have to treat this as a 
   * constructor expression. This is to handle the gcc extension that allows 
   * cast from a type of a field to the type of the union  *)
  let ie' = 
    match unrollType typ, ie with
      TComp (c, _), A.SINGLE_INIT _ when not c.cstruct -> 
        A.COMPOUND_INIT [(A.INFIELD_INIT ("___matching_field", 
                                          A.NEXT_INIT), 
                          ie)]
    | _, _ -> ie
  in
  (* Maybe specs contains an unnamed composite. Replace with the name so that 
   * when we do again the specs we get the right name  *)
  let specs1 = 
    match typ with
      TComp (ci, _) -> 
        List.map 
          (function 
              A.SpecType (A.Tstruct ("", flds, [])) -> 
                A.SpecType (A.Tstruct (ci.cname, None, []))
            | A.SpecType (A.Tunion ("", flds, [])) ->
                A.SpecType (A.Tunion (ci.cname, None, []))
            | s -> s) specs
    | _ -> specs
  in
  specs1, dt, ie' 

and getIntConstExp (aexp) : exp =
  let c, e, _ = doExp true aexp (AExp None) in 
  if not (isEmpty c) then 
    E.s (error "Constant expression %a has effects" d_exp e);
  match e with 
    (* first, filter for those Const exps that are integers *)
  | Const (CInt64 _ ) -> e
  | Const (CEnum _) -> e
  | Const (CChr i) -> Const(charConstToInt i)

        (* other Const expressions are not ok *)
  | Const _ -> E.s (error "Expected integer constant and got %a" d_exp e)
        
    (* now, anything else that 'doExp true' returned is ok (provided
       that it didn't yield side effects); this includes, in particular,
       the various sizeof and alignof expression kinds *)
  | _ -> e

(* this is like 'isIntConstExp', but retrieves the actual integer
 * the expression denotes; I have not extended it to work with
 * sizeof/alignof since (for CCured) we can't const-eval those,
 * and it's not clear whether they can be bitfield width specifiers
 * anyway (since that's where this function is used) *)
and isIntegerConstant (aexp) : int option =
  match doExp true aexp (AExp None) with
    (c, e, _) when isEmpty c -> begin
      match isInteger e with 
        Some i64 -> Some (Int64.to_int i64)
      | _ -> None
    end
  | _ -> None
        
     (* Process an expression and in the process do some type checking,
      * extract the effects as separate statements  *)
and doExp (asconst: bool)   (* This expression is used as a constant *)
          (e: A.expression) 
          (what: expAction) : (chunk * exp * typ) = 
  (* A subexpression of array type is automatically turned into StartOf(e). 
   * Similarly an expression of function type is turned into AddrOf. So 
   * essentially doExp should never return things of type TFun or TArray *)
  let processArrayFun e t = 
    match e, unrollType t with
      (Lval(lv) | CastE(_, Lval lv)), TArray(tbase, _, a) -> 
        mkStartOfAndMark lv, TPtr(tbase, a)
    | (Lval(lv) | CastE(_, Lval lv)), TFun _  -> 
        mkAddrOfAndMark lv, TPtr(t, [])
    | _, (TArray _ | TFun _) -> 
        E.s (error "Array or function expression is not lval: %a@!"
               d_plainexp e)
    | _ -> e, t
  in
  (* Before we return we call finishExp *)
  let finishExp ?(newWhat=what) 
                (se: chunk) (e: exp) (t: typ) : chunk * exp * typ = 
    match newWhat with 
      ADrop -> (se, e, t)
    | AExpLeaveArrayFun -> 
        (se, e, t) (* It is important that we do not do "processArrayFun" in 
                    * this case. We exploit this when we process the typeOf 
                    * construct *)
    | AExp _ -> 
        let (e', t') = processArrayFun e t in
(*
        ignore (E.log "finishExp: e'=%a, t'=%a\n" 
           d_exp e' d_type t');
*)
        (se, e', t')

    | ASet (lv, lvt) -> begin
        (* See if the set was done already *)
        match e with 
          Lval(lv') when lv == lv' -> 
            (se, e, t)
        | _ -> 
            let (e', t') = processArrayFun e t in
            let (t'', e'') = castTo t' lvt e' in
(*
            ignore (E.log "finishExp: e = %a\n  e'' = %a\n" d_plainexp e d_plainexp e'');
*)
            (se +++ (Set(lv, e'', !currentLoc)), e'', t'')
    end
  in
  let rec findField (n: string) (fidlist: fieldinfo list) : offset =
    (* Depth first search for the field. This appears to be what GCC does. 
     * MSVC checks that there are no ambiguous field names, so it does not 
     * matter how we search *)
    let rec search = function
        [] -> NoOffset (* Did not find *)
      | fid :: rest when fid.fname = n -> Field(fid, NoOffset)
      | fid :: rest when prefix annonCompFieldName fid.fname -> begin
          match unrollType fid.ftype with 
            TComp (ci, _) -> 
              let off = search ci.cfields in
              if off = NoOffset then 
                search rest  (* Continue searching *)
              else
                Field (fid, off)
          | _ -> E.s (bug "unnamed field type is not a struct/union")
      end
      | _ :: rest -> search rest
    in
    let off = search fidlist in
    if off = NoOffset then 
      E.s (error "Cannot find field %s" n);
    off
  in
  try
    match e with
    | A.NOTHING when what = ADrop -> finishExp empty (integer 0) intType
    | A.NOTHING ->
        let res = Const(CStr "exp_nothing") in
        finishExp empty res (typeOf res)

    (* Do the potential lvalues first *)
    | A.VARIABLE n -> begin
        (* Look up in the environment *)
        try
          let envdata = H.find env n in
          match envdata with
            EnvVar vi, _ ->
              (* if isconst && 
                 not (isFunctionType vi.vtype) && 
                 not (isArrayType vi.vtype)then
                E.s (error "variable appears in constant"); *)
              finishExp empty (Lval(var vi)) vi.vtype
          | EnvEnum (tag, typ), _ ->
              if !Cil.lowerConstants then 
                finishExp empty tag typ
              else begin
                let ei = 
                  match unrollType typ with 
                    TEnum(ei, _) -> ei
                  | _ -> assert false
                in
                finishExp empty (Const (CEnum(tag, n, ei))) typ
              end

          | _ -> raise Not_found
        with Not_found -> begin
          if isOldStyleVarArgName n then 
            E.s (error "Cannot resolve variable %s. This could be a CIL bug due to the handling of old-style variable argument functions.\n" n)
          else 
            E.s (error "Cannot resolve variable %s.\n" n)
        end
    end
    | A.INDEX (e1, e2) -> begin
        (* Recall that doExp turns arrays into StartOf pointers *)
        let (se1, e1', t1) = doExp false e1 (AExp None) in
        let (se2, e2', t2) = doExp false e2 (AExp None) in
        let se = se1 @@ se2 in
        let (e1'', t1, e2'', tresult) =
          (* Either e1 or e2 can be the pointer *)
          match unrollType t1, unrollType t2 with
            TPtr(t1e,_), (TInt _|TEnum _) -> e1', t1, e2', t1e
          | (TInt _|TEnum _), TPtr(t2e,_) -> e2', t2, e1', t2e
          | _ -> 
              E.s (error 
                     "Expecting a pointer type in index:@! t1=%a@!t2=%a@!"
                     d_plaintype t1 d_plaintype t2)
        in
        (* We have to distinguish the construction based on the type of e1'' *)
        let res = 
          match e1'' with 
            StartOf array -> (* A real array indexing operation *)
              addOffsetLval (Index(e2'', NoOffset)) array
          | _ -> (* Turn into *(e1 + e2) *)
              mkMem (BinOp(IndexPI, e1'', e2'', t1)) NoOffset
        in
        (* Do some optimization of StartOf *)
        finishExp se (Lval res) tresult

    end      
    | A.UNARY (A.MEMOF, e) -> 
        if asconst then
          ignore (warn "MEMOF in constant");
        let (se, e', t) = doExp false e (AExp None) in
        let tresult = 
          match unrollType t with
          | TPtr(te, _) -> te
          | _ -> E.s (error "Expecting a pointer type in *. Got %a@!"
                        d_plaintype t)
        in
        finishExp se 
                  (Lval (mkMem e' NoOffset))
                  tresult

           (* e.str = (& e + off(str)). If e = (be + beoff) then e.str = (be 
            * + beoff + off(str))  *)
    | A.MEMBEROF (e, str) -> 
        (* member of is actually allowed if we only take the address *)
        (* if isconst then
          E.s (error "MEMBEROF in constant");  *)
        let (se, e', t') = doExp false e (AExp None) in
        let lv = 
          match e' with 
            Lval x -> x 
          | CastE(_, Lval x) -> x
          | _ -> E.s (error "Expected an lval in MEMBEROF (field %s)" str)
        in
        let field_offset = 
          match unrollType t' with
            TComp (comp, _) -> findField str comp.cfields
          | _ -> E.s (error "expecting a struct with field %s" str)
        in
        let lv' = Lval(addOffsetLval field_offset lv) in
	let field_type = typeOf lv' in
        finishExp se lv' field_type
          
       (* e->str = * (e + off(str)) *)
    | A.MEMBEROFPTR (e, str) -> 
        if asconst then
          ignore (warn "MEMBEROFPTR in constant");
        let (se, e', t') = doExp false e (AExp None) in
        let pointedt = 
          match unrollType t' with
            TPtr(t1, _) -> t1
          | TArray(t1,_,_) -> t1
          | _ -> E.s (error "expecting a pointer to a struct")
        in
        let field_offset = 
          match unrollType pointedt with 
            TComp (comp, _) -> findField str comp.cfields
          | x -> 
              E.s (error 
                     "expecting a struct with field %s. Found %a. t1 is %a" 
                     str d_type x d_type t')
        in
	let lv' = Lval (mkMem e' field_offset) in
	let field_type = typeOf lv' in
        finishExp se lv' field_type
          
    | A.CONSTANT ct -> begin
        let hasSuffix str = 
          let l = String.length str in
          fun s -> 
            let ls = String.length s in
            l >= ls && s = String.uppercase (String.sub str (l - ls) ls)
        in
        match ct with 
          A.CONST_INT str -> begin
            let res = parseInt str in
            finishExp empty res (typeOf res)
          end

(*
        | A.CONST_WSTRING wstr ->
            let len = List.length wstr in 
            let wchar_t = !wcharType in
            (* We will make an array big enough to contain the wide 
             * characters and the wide-null terminator *)
            let ws_t = TArray(wchar_t, Some (integer len), []) in
            let ws = 
              makeGlobalVar ("wide_string" ^ string_of_int !lastStructId)
                ws_t
            in
            ws.vstorage <- Static;
            incr lastStructId;
            (* Make the initializer. Idx is a wide_char index.  *)
            let rec loop (idx: int) (s: int64 list) = 
	      match s with
		[] -> []
	      | wc::rest ->
		  let wc_cilexp = Const (CInt64(wc, IInt, None)) in
                  (Index(integer idx, NoOffset), 
                   SingleInit (mkCast wc_cilexp wchar_t))
                  :: loop (idx + 1) rest
            in
            (* Add the definition for the array *)
            cabsPushGlobal (GVar(ws, 
                                 {init = Some (CompoundInit(ws_t,
                                                            loop 0 wstr))},
                                 !currentLoc));
            finishExp empty (StartOf(Var ws, NoOffset))
              (TPtr(wchar_t, []))
              *)

        | A.CONST_WSTRING (ws: int64 list) -> 
            let res = Const(CWStr ((* intlist_to_wstring *) ws)) in
            finishExp empty res (typeOf res)

        | A.CONST_STRING s -> 
            (* Maybe we burried __FUNCTION__ in there *)
            let s' = 
              try
                let start = String.index s (Char.chr 0) in
                let l = String.length s in
                let tofind = (String.make 1 (Char.chr 0)) ^ "__FUNCTION__" in
                let past = start + String.length tofind in
                if past <= l &&
                   String.sub s start (String.length tofind) = tofind then
                  (if start > 0 then String.sub s 0 start else "") ^
                  !currentFunctionFDEC.svar.vname ^
                  (if past < l then String.sub s past (l - past) else "")
                else
                  s
              with Not_found -> s
            in
            let res = Const(CStr s') in
            finishExp empty res (typeOf res)
              
        | A.CONST_CHAR char_list ->
            let a, b = (interpret_character_constant char_list) in 
            finishExp empty (Const a) b 
              
        | A.CONST_WCHAR char_list ->
            (* matth: I can't see a reason for a list of more than one char
             * here, since the kinteger64 below will take only the lower 16
             * bits of value.  ('abc' makes sense, because CHAR constants have
             * type int, and so more than one char may be needed to represent 
             * the value.  But L'abc' has type wchar, and so is equivalent to 
             * L'c').  But gcc allows L'abc', so I'll leave this here in case
             * I'm missing some architecture dependent behavior. *)
	    let value = reduce_multichar !wcharType char_list in
	    let result = kinteger64 !wcharKind value in
            finishExp empty result (typeOf result)
              
        | A.CONST_FLOAT str -> begin
            (* Maybe it ends in U or UL. Strip those *)
            let l = String.length str in
            let hasSuffix = hasSuffix str in
            let baseint, kind = 
              if  hasSuffix "L" then
                String.sub str 0 (l - 1), FLongDouble
              else if hasSuffix "F" then
                String.sub str 0 (l - 1), FFloat
              else if hasSuffix "D" then
                String.sub str 0 (l - 1), FDouble
              else
                str, FDouble
            in
            try
              finishExp empty 
                (Const(CReal(float_of_string baseint, kind,
                             Some str)))
                (TFloat(kind,[]))
            with e -> begin
              ignore (E.log "float_of_string %s (%s)\n" str 
                        (Printexc.to_string e));
              let res = Const(CStr "booo CONS_FLOAT") in
              finishExp empty res (typeOf res)
            end
        end
    end          

    | A.TYPE_SIZEOF (bt, dt) ->
        let typ = doOnlyType bt dt in
        finishExp empty (SizeOf(typ)) !typeOfSizeOf

      (* Intercept the sizeof("string") *)
    | A.EXPR_SIZEOF (A.CONSTANT (A.CONST_STRING s)) -> begin
        (* Process the string first *)
        match doExp asconst (A.CONSTANT (A.CONST_STRING s)) (AExp None) with 
          _, Const(CStr s), _ -> 
            finishExp empty (SizeOfStr s) !typeOfSizeOf
        | _ -> E.s (bug "cabs2cil: sizeOfStr")
    end

    | A.EXPR_SIZEOF e ->
        (* Allow non-constants in sizeof *)
        (* Do not convert arrays and functions into pointers. *)
        let (se, e', t) = doExp false e AExpLeaveArrayFun in
(*
        ignore (E.log "sizeof: %a e'=%a, t=%a\n"
                  d_loc !currentLoc d_plainexp e' d_type t);
*)
        (* !!!! The book says that the expression is not evaluated, so we
           * drop the potential side-effects 
        if isNotEmpty se then
          ignore (warn "Warning: Dropping side-effect in EXPR_SIZEOF\n");
*)
        let size =
          match e' with                 (* If we are taking the sizeof an
                                         * array we must drop the StartOf  *)
            StartOf(lv) -> SizeOfE (Lval(lv))

                (* Maybe we are taking the sizeof for a CStr. In that case we 
                 * mean the pointer to the start of the string *)
          | Const(CStr _) -> SizeOf (charPtrType)

                (* Maybe we are taking the sizeof a variable-sized array *)
          | Lval (Var vi, NoOffset) -> begin
              try 
                IH.find varSizeArrays vi.vid 
              with Not_found -> SizeOfE e' 
          end
          | _ -> SizeOfE e'
        in
        finishExp empty size !typeOfSizeOf

    | A.TYPE_ALIGNOF (bt, dt) ->
        let typ = doOnlyType bt dt in
        finishExp empty (AlignOf(typ)) !typeOfSizeOf

    | A.EXPR_ALIGNOF e ->
        let (se, e', t) = doExp false e AExpLeaveArrayFun in
        (* !!!! The book says that the expression is not evaluated, so we
           * drop the potential side-effects 
        if isNotEmpty se then
          ignore (warn "Warning: Dropping side-effect in EXPR_ALIGNOF\n");
*)
        let e'' =
          match e' with                 (* If we are taking the alignof an
                                         * array we must drop the StartOf  *)
            StartOf(lv) -> Lval(lv)

          | _ -> e'
        in
        finishExp empty (AlignOfE(e'')) !typeOfSizeOf

    | A.CAST ((specs, dt), ie) ->
        let s', dt', ie' = preprocessCast specs dt ie in
        (* We know now that we can do s' and dt' many times *)
        let typ = doOnlyType s' dt' in
        let what' =
          match what with
            AExp (Some _) -> AExp (Some typ)
          | AExp None -> what
          | ADrop | AExpLeaveArrayFun -> what
          | ASet (lv, lvt) -> 
              (* If the cast from typ to lvt would be dropped, then we 
               * continue with a Set *)
              if false && Util.equals (typeSig typ) (typeSig lvt) then 
                what
              else
                AExp None (* We'll create a temporary *)
        in
        (* Remember here if we have done the Set *)
        let (se, e', t'), (needcast: bool) = 
          match ie' with
            A.SINGLE_INIT e -> doExp asconst e what', true

          | A.NO_INIT -> E.s (error "missing expression in cast")

          | A.COMPOUND_INIT _ -> begin
              (* Pretend that we are declaring and initializing a brand new 
               * variable  *)
              let newvar = "__constr_expr_" ^ string_of_int (!constrExprId) in
              incr constrExprId;
              let spec_res = doSpecList "" s' in
              let se1 = 
                if !scopes == [] then begin
                  ignore (createGlobal spec_res 
                            ((newvar, dt', [], cabslu), ie'));
                  empty
                end else
                  createLocal spec_res ((newvar, dt', [], cabslu), ie') 
              in
              (* Now pretend that e is just a reference to the newly created 
               * variable *)
              let se, e', t' = doExp asconst (A.VARIABLE newvar) what' in
              (* If typ is an array then the doExp above has already added a 
               * StartOf. We must undo that now so that it is done once by 
               * the finishExp at the end of this case *)
              let e2, t2 = 
                match unrollType typ, e' with
                  TArray _, StartOf lv -> Lval lv, typ
                | _, _ -> e', t'
              in
              (* If we are here, then the type t2 is guaranteed to match the 
               * type of the expression e2, so we do not need a cast. We have 
               * to worry about this because otherwise, we might need to cast 
               * between arrays or structures. *)
              (se1 @@ se, e2, t2), false
          end
        in
        let (t'', e'') = 
          match typ with
            TVoid _ when what' = ADrop -> (t', e') (* strange GNU thing *)
          |  _ -> 
              (* Do this to check the cast, unless we are sure that we do not 
               * need the check. *)
              let newtyp, newexp = 
                if needcast then 
                  castTo ~fromsource:true t' typ e' 
                else
                  t', e'
              in
              newtyp, newexp
        in
        finishExp se e'' t''
          
    | A.UNARY(A.MINUS, e) -> 
        let (se, e', t) = doExp asconst e (AExp None) in
        if isIntegralType t then
          let tres = integralPromotion t in
          let e'' = 
            match e' with
            | Const(CInt64(i, ik, _)) -> kinteger64 ik (Int64.neg i)
            | _ -> UnOp(Neg, mkCastT e' t tres, tres)
          in
          finishExp se e'' tres
        else
          if isArithmeticType t then
            finishExp se (UnOp(Neg,e',t)) t
          else
            E.s (error "Unary - on a non-arithmetic type")
        
    | A.UNARY(A.BNOT, e) -> 
        let (se, e', t) = doExp asconst e (AExp None) in
        if isIntegralType t then
          let tres = integralPromotion t in
          let e'' = UnOp(BNot, mkCastT e' t tres, tres) in
          finishExp se e'' tres
        else
          E.s (error "Unary ~ on a non-integral type")
          
    | A.UNARY(A.PLUS, e) -> doExp asconst e what 
          
          
    | A.UNARY(A.ADDROF, e) -> begin
        match e with 
          A.COMMA el -> (* GCC extension *)
            doExp false 
              (A.COMMA (replaceLastInList el (fun e -> A.UNARY(A.ADDROF, e))))
              what
        | A.QUESTION (e1, e2, e3) -> (* GCC extension *)
            doExp false 
              (A.QUESTION (e1, A.UNARY(A.ADDROF, e2), A.UNARY(A.ADDROF, e3)))
              what
        | A.VARIABLE s when 
            isOldStyleVarArgName s 
            && (match !currentFunctionFDEC.svar.vtype with 
                   TFun(_, _, true, _) -> true | _ -> false) ->
            (* We are in an old-style variable argument function and we are 
             * taking the address of the argument that was removed while 
             * processing the function type. We compute the address based on 
             * the address of the last real argument *)
            if !msvcMode then begin
              let rec getLast = function
                  [] -> E.s (unimp "old-style variable argument function without real arguments")
                | [a] -> a
                | _ :: rest -> getLast rest 
              in
              let last = getLast !currentFunctionFDEC.sformals in
              let res = mkAddrOfAndMark (var last) in
              let tres = typeOf res in
              let tres', res' = castTo tres (TInt(IULong, [])) res in
              (* Now we must add to this address to point to the next 
              * argument. Round up to a multiple of 4  *)
              let sizeOfLast = 
                (((bitsSizeOf last.vtype) + 31) / 32) * 4
              in
              let res'' = 
                BinOp(PlusA, res', kinteger IULong sizeOfLast, tres')
              in
              finishExp empty res'' tres'
            end else begin (* On GCC the only reliable way to do this is to 
                          * call builtin_next_arg. If we take the address of 
                          * a local we are going to get the address of a copy 
                          * of the local ! *)
                
              doExp asconst
                (A.CALL (A.VARIABLE "__builtin_next_arg", 
                         [A.CONSTANT (A.CONST_INT "0")]))
                what
            end

        | (A.VARIABLE _ | A.UNARY (A.MEMOF, _) | (* Regular lvalues *)
           A.INDEX _ | A.MEMBEROF _ | A.MEMBEROFPTR _ | 
           A.CAST (_, A.COMPOUND_INIT _)) -> begin
            let (se, e', t) = doExp false e (AExp None) in
            (* ignore (E.log "ADDROF on %a : %a\n" d_plainexp e'
                      d_plaintype t); *)
            match e' with 
             ( Lval x | CastE(_, Lval x)) -> 
               finishExp se (mkAddrOfAndMark x) (TPtr(t, []))

            | StartOf (lv) ->
                let tres = TPtr(typeOfLval lv, []) in (* pointer to array *)
                finishExp se (mkAddrOfAndMark lv) tres

              (* Function names are converted into pointers to the function. 
               * Taking the address-of again does not change things *)
            | AddrOf (Var v, NoOffset) when isFunctionType v.vtype ->
                finishExp se e' t

            | _ -> E.s (error "Expected lval for ADDROF. Got %a@!"
                          d_plainexp e')
        end
        | _ -> E.s (error "Unexpected operand for addrof")
    end
    | A.UNARY((A.PREINCR|A.PREDECR) as uop, e) -> begin
        match e with 
          A.COMMA el -> (* GCC extension *)
            doExp asconst 
              (A.COMMA (replaceLastInList el 
                          (fun e -> A.UNARY(uop, e))))
              what
        | A.QUESTION (e1, e2q, e3q) -> (* GCC extension *)
            doExp asconst 
              (A.QUESTION (e1, A.UNARY(uop, e2q), 
                           A.UNARY(uop, e3q)))
              what

        | (A.VARIABLE _ | A.UNARY (A.MEMOF, _) | (* Regular lvalues *)
           A.INDEX _ | A.MEMBEROF _ | A.MEMBEROFPTR _ |
           A.CAST _ (* A GCC extension *)) -> begin
             let uop' = if uop = A.PREINCR then PlusA else MinusA in
             if asconst then
               ignore (warn "PREINCR or PREDECR in constant");
             let (se, e', t) = doExp false e (AExp None) in
             let lv = 
               match e' with 
                 Lval x -> x
               | CastE (_, Lval x) -> x (* A GCC extension. The operation is 
                                         * done at the cast type. The result 
                                         * is also of the cast type *)
               | _ -> E.s (error "Expected lval for ++ or --")
             in
             let tresult, result = doBinOp uop' e' t one intType in
             finishExp (se +++ (Set(lv, mkCastT result tresult t, 
                                    !currentLoc)))
               e'
               tresult   (* Should this be t instead ??? *)
           end
        | _ -> E.s (error "Unexpected operand for prefix -- or ++")
    end
          
    | A.UNARY((A.POSINCR|A.POSDECR) as uop, e) -> begin
        match e with 
          A.COMMA el -> (* GCC extension *)
            doExp asconst 
              (A.COMMA (replaceLastInList el 
                          (fun e -> A.UNARY(uop, e))))
              what
        | A.QUESTION (e1, e2q, e3q) -> (* GCC extension *)
            doExp asconst 
              (A.QUESTION (e1, A.UNARY(uop, e2q), A.UNARY(uop, e3q)))
              what

        | (A.VARIABLE _ | A.UNARY (A.MEMOF, _) | (* Regular lvalues *)
           A.INDEX _ | A.MEMBEROF _ | A.MEMBEROFPTR _ | 
           A.CAST _ (* A GCC extension *) ) -> begin
             if asconst then
               ignore (warn "POSTINCR or POSTDECR in constant");
             (* If we do not drop the result then we must save the value *)
             let uop' = if uop = A.POSINCR then PlusA else MinusA in
             let (se, e', t) = doExp false e (AExp None) in
             let lv = 
               match e' with 
                 Lval x -> x
               | CastE (_, Lval x) -> x (* GCC extension. The addition must 
                                         * be be done at the cast type. The 
                                         * result of this is also of the cast 
                                         * type *)
               | _ -> E.s (error "Expected lval for ++ or --")
             in
             let tresult, opresult = doBinOp uop' e' t one intType in
             let se', result = 
               if what <> ADrop then 
                 let tmp = newTempVar t in
                 se +++ (Set(var tmp, e', !currentLoc)), Lval(var tmp)
               else
                 se, e'
             in
             finishExp 
               (se' +++ (Set(lv, mkCastT opresult tresult t, 
                             !currentLoc)))
               result
               tresult   (* Should this be t instead ??? *)
           end
        | _ -> E.s (error "Unexpected operand for suffix ++ or --")
    end
          
    | A.BINARY(A.ASSIGN, e1, e2) -> begin
        match e1 with 
          A.COMMA el -> (* GCC extension *)
            doExp asconst 
              (A.COMMA (replaceLastInList el 
                          (fun e -> A.BINARY(A.ASSIGN, e, e2))))
              what
        | A.QUESTION (e1, e2q, e3q) -> (* GCC extension *)
            doExp asconst 
              (A.QUESTION (e1, A.BINARY(A.ASSIGN, e2q, e2), 
                           A.BINARY(A.ASSIGN, e3q, e2)))
              what
        | A.CAST (t, A.SINGLE_INIT e) -> (* GCC extension *)
            doExp asconst
              (A.CAST (t, 
                       A.SINGLE_INIT (A.BINARY(A.ASSIGN, e, 
                                               A.CAST (t, A.SINGLE_INIT e2)))))
              what

        | (A.VARIABLE _ | A.UNARY (A.MEMOF, _) | (* Regular lvalues *)
           A.INDEX _ | A.MEMBEROF _ | A.MEMBEROFPTR _ ) -> begin
             if asconst then ignore (warn "ASSIGN in constant");
             let (se1, e1', lvt) = doExp false e1 (AExp None) in
             let lv = 
               match e1' with 
                 Lval x -> x
               | _ -> E.s (error "Expected lval for assignment. Got %a\n"
                             d_plainexp e1')
             in
             let (se2, e'', t'') = doExp false e2 (ASet(lv, lvt)) in
             finishExp (se1 @@ se2) e1' lvt
           end
        | _ -> E.s (error "Invalid left operand for ASSIGN")
    end
          
    | A.BINARY((A.ADD|A.SUB|A.MUL|A.DIV|A.MOD|A.BAND|A.BOR|A.XOR|
      A.SHL|A.SHR|A.EQ|A.NE|A.LT|A.GT|A.GE|A.LE) as bop, e1, e2) -> 
        let bop' = convBinOp bop in
        let (se1, e1', t1) = doExp asconst e1 (AExp None) in
        let (se2, e2', t2) = doExp asconst e2 (AExp None) in
        let tresult, result = doBinOp bop' e1' t1 e2' t2 in
        finishExp (se1 @@ se2) result tresult
          
          (* assignment operators *)
    | A.BINARY((A.ADD_ASSIGN|A.SUB_ASSIGN|A.MUL_ASSIGN|A.DIV_ASSIGN|
      A.MOD_ASSIGN|A.BAND_ASSIGN|A.BOR_ASSIGN|A.SHL_ASSIGN|
      A.SHR_ASSIGN|A.XOR_ASSIGN) as bop, e1, e2) -> begin
        match e1 with 
          A.COMMA el -> (* GCC extension *)
            doExp asconst 
              (A.COMMA (replaceLastInList el 
                          (fun e -> A.BINARY(bop, e, e2))))
              what
        | A.QUESTION (e1, e2q, e3q) -> (* GCC extension *)
            doExp asconst 
              (A.QUESTION (e1, A.BINARY(bop, e2q, e2), 
                           A.BINARY(bop, e3q, e2)))
              what

        | (A.VARIABLE _ | A.UNARY (A.MEMOF, _) | (* Regular lvalues *)
           A.INDEX _ | A.MEMBEROF _ | A.MEMBEROFPTR _ |
           A.CAST _ (* GCC extension *) ) -> begin
             if asconst then
               ignore (warn "op_ASSIGN in constant");
             let bop' = match bop with          
               A.ADD_ASSIGN -> PlusA
             | A.SUB_ASSIGN -> MinusA
             | A.MUL_ASSIGN -> Mult
             | A.DIV_ASSIGN -> Div
             | A.MOD_ASSIGN -> Mod
             | A.BAND_ASSIGN -> BAnd
             | A.BOR_ASSIGN -> BOr
             | A.XOR_ASSIGN -> BXor
             | A.SHL_ASSIGN -> Shiftlt
             | A.SHR_ASSIGN -> Shiftrt
             | _ -> E.s (error "binary +=")
             in
             let (se1, e1', t1) = doExp false e1 (AExp None) in
             let lv1 = 
               match e1' with 
                 Lval x -> x
               | CastE (_, Lval x) -> x (* GCC extension. The operation and 
                                         * the result are at the cast type  *)
               | _ -> E.s (error "Expected lval for assignment with arith")
             in
             let (se2, e2', t2) = doExp false e2 (AExp None) in
             let tresult, result = doBinOp bop' e1' t1 e2' t2 in
             (* We must cast the result to the type of the lv1, which may be 
              * different than t1 if lv1 was a Cast *)
             let _, result' = castTo tresult (typeOfLval lv1) result in
             (* The type of the result is the type of the left-hand side  *) 
             finishExp (se1 @@ se2 +++ 
                        (Set(lv1, result', !currentLoc)))
               e1'
               t1 
           end
        | _ -> E.s (error "Unexpected left operand for assignment with arith")
      end
               
          
    | A.BINARY((A.AND|A.OR), _, _) | A.UNARY(A.NOT, _) -> begin
        let ce = doCondExp asconst e in
        (* We must normalize the result to 0 or 1 *)
        match ce with
          CEExp (se, ((Const _) as c)) -> 
            finishExp se (if isConstTrue c then one else zero) intType
	| CEExp (se, (UnOp(LNot, _, _) as e)) ->
	    (* already normalized to 0 or 1 *)
	    finishExp se e intType
        | CEExp (se, e) ->
            let e' = 
              let te = typeOf e in
              let _, zte = castTo intType te zero in
              BinOp(Ne, e, zte, te)
            in
            finishExp se e' intType
        | _ -> 
            let tmp = var (newTempVar intType) in
            finishExp (compileCondExp ce
                         (empty +++ (Set(tmp, integer 1, 
                                         !currentLoc)))
                         (empty +++ (Set(tmp, integer 0, 
                                         !currentLoc))))     
              (Lval tmp)
              intType
    end

    | A.CALL(f, args) -> 
        if asconst then
          ignore (warn "CALL in constant");
        let (sf, f', ft') = 
          match f with                  (* Treat the VARIABLE case separate 
                                         * becase we might be calling a 
                                         * function that does not have a 
                                         * prototype. In that case assume it 
                                         * takes INTs as arguments  *)
            A.VARIABLE n -> begin
              try
                let vi, _ = lookupVar n in
                (empty, Lval(var vi), vi.vtype) (* Found. Do not use 
                                                 * finishExp. Simulate what = 
                                                 * AExp None  *)
              with Not_found -> begin
                ignore (warnOpt "Calling function %s without prototype." n);
                let ftype = TFun(intType, None, false, 
                                 [Attr("missingproto",[])]) in
                (* Add a prototype to the environment *)
                let proto, _ = 
                  makeGlobalVarinfo false (makeGlobalVar n ftype) in
                (* Make it EXTERN *)
                proto.vstorage <- Extern;
                IH.add noProtoFunctions proto.vid true;
                (* Add it to the file as well *)
                cabsPushGlobal (GVarDecl (proto, !currentLoc));
                (empty, Lval(var proto), ftype)
              end
            end
          | _ -> doExp false f (AExp None) 
        in
        (* Get the result type and the argument types *)
        let (resType, argTypes, isvar, f'') = 
          match unrollType ft' with
            TFun(rt,at,isvar,a) -> (rt,at,isvar,f')
          | TPtr (t, _) -> begin
              match unrollType t with 
                TFun(rt,at,isvar,a) -> (* Make the function pointer 
                                            * explicit  *)
                  let f'' = 
                    match f' with
                      AddrOf lv -> Lval(lv)
                    | _ -> Lval(mkMem f' NoOffset)
                  in
                  (rt,at,isvar, f'')
              | x -> 
                  E.s (error "Unexpected type of the called function %a: %a" 
                         d_exp f' d_type x)
          end
          | x ->  E.s (error "Unexpected type of the called function %a: %a" 
                         d_exp f' d_type x)
        in
        let argTypesList = argsToList argTypes in
        (* Drop certain qualifiers from the result type *)
        let resType' = resType in 
        (* Before we do the arguments we try to intercept a few builtins. For 
         * these we have defined then with a different type, so we do not 
         * want to give warnings. We'll just leave the arguments of these
         * functions alone*)
        let isSpecialBuiltin =  
          match f'' with 
            Lval (Var fv, NoOffset) ->
              fv.vname = "__builtin_stdarg_start" ||
              fv.vname = "__builtin_va_arg" ||
              fv.vname = "__builtin_va_start" ||
              fv.vname = "__builtin_expect" ||
              fv.vname = "__builtin_next_arg"
            | _ -> false
        in
          
        (** If the "--forceRLArgEval" flag was used, make sure
          we evaluate args right-to-left.
          Added by Nathan Cooprider. **)
        let force_right_to_left_evaluation (c, e, t) =
	  (* If chunk is empty then it is not already evaluated *)
	  (* constants don't need to be pulled out *)
          if (!forceRLArgEval && (not (isConstant e)) && 
	      (not isSpecialBuiltin)) then 
	    (* create a temporary *)
	    let tmp = newTempVar t in
	    (* create an instruction to give the e to the temporary *)
	    let i = Set(var tmp, e, !currentLoc) in 
	    (* add the instruction to the chunk *)
	    (* change the expression to be the temporary *)
	    (c +++ i, (Lval(var tmp)), t) 
          else
	    (c, e, t)
        in
        (* Do the arguments. In REVERSE order !!! Both GCC and MSVC do this *)
        let rec loopArgs 
            : (string * typ * attributes) list * A.expression list 
          -> (chunk * exp list) = function
            | ([], []) -> (empty, [])

            | args, [] -> 
                if not isSpecialBuiltin then 
                  ignore (warnOpt 
                            "Too few arguments in call to %a."
                            d_exp f');
		(empty, [])

            | ((_, at, _) :: atypes, a :: args) -> 
                let (ss, args') = loopArgs (atypes, args) in
                (* Do not cast as part of translating the argument. We let 
                 * the castTo to do this work. This was necessary for 
                 * test/small1/union5, in which a transparent union is passed 
                 * as an argument *)
                let (sa, a', att) = force_right_to_left_evaluation
                                      (doExp false a (AExp None)) in
                let (_, a'') = castTo att at a' in
                (ss @@ sa, a'' :: args')
                  
            | ([], args) -> (* No more types *)
                if not isvar && argTypes != None && not isSpecialBuiltin then 
                  (* Do not give a warning for functions without a prototype*)
                  ignore (warnOpt "Too many arguments in call to %a" d_exp f');
                let rec loop = function
                    [] -> (empty, [])
                  | a :: args -> 
                      let (ss, args') = loop args in
                      let (sa, a', at) = force_right_to_left_evaluation 
                          (doExp false a (AExp None)) in
                      (ss @@ sa, a' :: args')
                in
                loop args
        in
        let (sargs, args') = loopArgs (argTypesList, args) in
        (* Setup some pointer to the elements of the call. We may change 
         * these below *)
        let prechunk: chunk ref = ref (sf @@ sargs) in (* comes before *)

        (* Do we actually have a call, or an expression? *)
        let piscall: bool ref = ref true in 

        let pf: exp ref = ref f'' in (* function to call *)
        let pargs: exp list ref = ref args' in (* arguments *)
        let pis__builtin_va_arg: bool ref = ref false in 
        let pwhat: expAction ref = ref what in (* what to do with result *)

        let pres: exp ref = ref zero in (* If we do not have a call, this is 
                                        * the result *)
        let prestype: typ ref = ref intType in

        let rec dropCasts = function CastE (_, e) -> dropCasts e | e -> e in
        (* Get the name of the last formal *)
        let getNameLastFormal () : string = 
          match !currentFunctionFDEC.svar.vtype with
            TFun(_, Some args, true, _) -> begin
              match List.rev args with
                (last_par_name, _, _) :: _ -> last_par_name
              | _ -> ""
            end
          | _ -> ""
        in

        (* Try to intercept some builtins *)
        (match !pf with 
          Lval(Var fv, NoOffset) -> begin
            if fv.vname = "__builtin_va_arg" then begin
              match !pargs with 
                marker :: SizeOf resTyp :: _ -> begin
                  (* Make a variable of the desired type *)
                  let destlv, destlvtyp = 
                    match !pwhat with 
                      ASet (lv, lvt) -> lv, lvt
                    | _ -> var (newTempVar resTyp), resTyp
                  in
                  pwhat := (ASet (destlv, destlvtyp));
                  pargs := [marker; SizeOf resTyp; AddrOf destlv];
                  pis__builtin_va_arg := true;
                end
              | _ -> 
                  ignore (warn "Invalid call to %s\n" fv.vname);
            end else if fv.vname = "__builtin_stdarg_start" then begin
              match !pargs with 
                marker :: last :: [] -> begin
                  let isOk = 
                    match dropCasts last with 
                      Lval (Var lastv, NoOffset) -> 
                        lastv.vname = getNameLastFormal ()
                    | _ -> false
                  in
                  if not isOk then 
                    ignore (warn "The second argument in call to %s should be the last formal argument\n" fv.vname);
                  
                  (* Check that "lastv" is indeed the last variable in the 
                   * prototype and then drop it *)
                  pargs := [ marker ]
                end
              | _ -> 
                  ignore (warn "Invalid call to %s\n" fv.vname);
                  
                  (* We have to turn uses of __builtin_varargs_start into uses 
                   * of __builtin_stdarg_start (because we have dropped the 
                   * __builtin_va_alist argument from this function) *)
                  
            end else if fv.vname = "__builtin_varargs_start" then begin
              (* Lookup the prototype for the replacement *)
              let v, _  = 
                try lookupGlobalVar "__builtin_stdarg_start" 
                with Not_found -> E.s (bug "Cannot find __builtin_stdarg_start to replace %s\n" fv.vname)
              in
              pf := Lval (var v)
            end else if fv.vname = "__builtin_next_arg" then begin
              match !pargs with 
                last :: [] -> begin
                  let isOk = 
                    match dropCasts last with 
                      Lval (Var lastv, NoOffset) -> 
                        lastv.vname = getNameLastFormal ()
                    | _ -> false
                  in
                  if not isOk then 
                    ignore (warn "The argument in call to %s should be the last formal argument\n" fv.vname);
                  
                  pargs := [ ]
                end
              | _ -> 
                  ignore (warn "Invalid call to %s\n" fv.vname);
            end else if fv.vname = "__builtin_constant_p" then begin
              (* Drop the side-effects *)
              prechunk := empty;

              (* Constant-fold the argument and see if it is a constant *)
              (match !pargs with 
                [ arg ] -> begin 
                  match constFold true arg with 
                    Const _ -> piscall := false; 
                               pres := integer 1; 
                               prestype := intType

                  | _ -> piscall := false; 
                         pres := integer 0;
                         prestype := intType
                end
              | _ -> 
                  ignore (warn "Invalid call to builtin_constant_p"));
            end
          end
        | _ -> ());


        (* Now we must finish the call *)
        if !piscall then begin 
          let addCall (calldest: lval option) (res: exp) (t: typ) = 
            prechunk := !prechunk +++
                (Call(calldest, !pf, !pargs, !currentLoc));
            pres := res;
            prestype := t
          in
          match !pwhat with 
            ADrop -> addCall None zero intType
                
                (* Set to a variable of corresponding type *)
          | ASet(lv, vtype) -> 
              (* Make an exception here for __builtin_va_arg *)
              if !pis__builtin_va_arg then 
                addCall None (Lval(lv)) vtype
              else
                addCall (Some lv) (Lval(lv)) vtype
                  
          | _ -> begin
              let tmp, restyp' = 
                match !pwhat with
                  AExp (Some t) -> newTempVar t, t
                | _ -> newTempVar resType', resType'
              in
              (* Remember that this variable has been created for this 
               * specific call. We will use this in collapseCallCast and 
               * above in finishCall. *)
              IH.add callTempVars tmp.vid ();
              addCall (Some (var tmp)) (Lval(var tmp)) restyp'
          end
        end;
              
        finishExp !prechunk !pres !prestype

          
    | A.COMMA el -> 
        if asconst then 
          ignore (warn "COMMA in constant");
        let rec loop sofar = function
            [e] -> 
              let (se, e', t') = doExp false e what in (* Pass on the action *)
              (sofar @@ se, e', t')
(*
              finishExp (sofar @@ se) e' t' (* does not hurt to do it twice. 
                                             * GN: it seems it does *)
*)
          | e :: rest -> 
              let (se, _, _) = doExp false e ADrop in
              loop (sofar @@ se) rest
          | [] -> E.s (error "empty COMMA expression")
        in
        loop empty el
          
    | A.QUESTION (e1,e2,e3) when what = ADrop -> 
        if asconst then
          ignore (warn "QUESTION with ADrop in constant");
        let (se3,_,_) = doExp false e3 ADrop in
        let se2 = 
          match e2 with 
            A.NOTHING -> skipChunk
          | _ -> let (se2,_,_) = doExp false e2 ADrop in se2
        in
        finishExp (doCondition asconst e1 se2 se3) zero intType
          
    | A.QUESTION (e1, e2, e3) -> begin (* what is not ADrop *)
        (* Compile the conditional expression *)
        let ce1 = doCondExp asconst e1 in
        (* Now we must find the type of both branches, in order to compute 
         * the type of the result *)
        let se2, e2'o (* is an option. None means use e1 *), t2 = 
          match e2 with 
            A.NOTHING -> begin (* The same as the type of e1 *)
              match ce1 with
                CEExp (_, e1') -> empty, None, typeOf e1' (* Do not promote 
                                                             to bool *)
              | _ -> empty, None, intType
            end
          | _ -> 
              let se2, e2', t2 = doExp asconst e2 (AExp None) in
              se2, Some e2', t2
        in
        (* Do e3 for real *)
        let se3, e3', t3 = doExp asconst e3 (AExp None) in
        (* Compute the type of the result *)
        let tresult = conditionalConversion t2 t3 in
        match ce1 with
          CEExp (se1, e1') when isConstFalse e1' && canDrop se2 -> 
             finishExp (se1 @@ se3) (snd (castTo t3 tresult e3')) tresult
        | CEExp (se1, e1') when isConstTrue e1' && canDrop se3 -> 
           begin
             match e2'o with
               None -> (* use e1' *)
                 finishExp (se1 @@ se2) (snd (castTo t2 tresult e1')) tresult
             | Some e2' -> 
                 finishExp (se1 @@ se2) (snd (castTo t2 tresult e2')) tresult
           end

        | _ -> (* Use a conditional *) begin
            match e2 with 
              A.NOTHING -> 
                let tmp = var (newTempVar tresult) in
                let (se1, _, _) = doExp asconst e1 (ASet(tmp, tresult)) in
                let (se3, _, _) = doExp asconst e3 (ASet(tmp, tresult)) in
                finishExp (se1 @@ ifChunk (Lval(tmp)) lu
                                    skipChunk se3)
                  (Lval(tmp))
                  tresult
            | _ -> 
                let lv, lvt = 
                  match what with
                  | ASet (lv, lvt) -> lv, lvt
                  | _ -> 
                      let tmp = newTempVar tresult in
                      var tmp, tresult
                in
                (* Now do e2 and e3 for real *)
                let (se2, _, _) = doExp asconst e2 (ASet(lv, lvt)) in
                let (se3, _, _) = doExp asconst e3 (ASet(lv, lvt)) in
                finishExp (doCondition asconst e1 se2 se3) (Lval(lv)) tresult
        end

(*
        (* Do these only to collect the types  *)
        let se2, e2', t2' = 
          match e2 with 
            A.NOTHING -> (* A GNU thing. Use e1 as e2 *) 
              doExp isconst e1 (AExp None)
          | _ -> doExp isconst e2 (AExp None) in 
        (* Do e3 for real *)
        let se3, e3', t3' = doExp isconst e3 (AExp None) in
        (* Compute the type of the result *)
        let tresult = conditionalConversion e2' t2' e3' t3' in
        if     (isEmpty se2 || e2 = A.NOTHING) 
            && isEmpty se3 && isconst then begin 
          (* Use the Question. This allows Question in initializers without 
          * having to do constant folding  *)
          let se1, e1', t1 = doExp isconst e1 (AExp None) in
          ignore (checkBool t1 e1');
          let e2'' = 
            if e2 = A.NOTHING then 
              mkCastT e1' t1 tresult 
            else mkCastT e2' t2' tresult (* We know se2 is empty *)
          in
          let e3'' = mkCastT e3' t3' tresult in
          let resexp = 
            match e1' with
              Const(CInt64(i, _, _)) when i <> Int64.zero -> e2''
            | Const(CInt64(z, _, _)) when z = Int64.zero -> e3''
            | _ -> Question(e1', e2'', e3'')
          in
          finishExp se1 resexp tresult
        end else begin (* Now use a conditional *)
          match e2 with 
            A.NOTHING -> 
              let tmp = var (newTempVar tresult) in
              let (se1, _, _) = doExp isconst e1 (ASet(tmp, tresult)) in
              let (se3, _, _) = doExp isconst e3 (ASet(tmp, tresult)) in
              finishExp (se1 @@ ifChunk (Lval(tmp)) lu
                                  skipChunk se3)
                (Lval(tmp))
                tresult
          | _ -> 
              let lv, lvt = 
                match what with
                | ASet (lv, lvt) -> lv, lvt
                | _ -> 
                    let tmp = newTempVar tresult in
                    var tmp, tresult
              in
              (* Now do e2 and e3 for real *)
              let (se2, _, _) = doExp isconst e2 (ASet(lv, lvt)) in
              let (se3, _, _) = doExp isconst e3 (ASet(lv, lvt)) in
              finishExp (doCondition isconst e1 se2 se3) (Lval(lv)) tresult
        end
*)
    end

    | A.GNU_BODY b -> begin
        (* Find the last A.COMPUTATION and remember it. This one is invoked 
         * on the reversed list of statements. *)
        let rec findLastComputation = function
            s :: _  -> 
              let rec findLast = function
                  A.SEQUENCE (_, s, loc) -> findLast s
                | CASE (_, s, _) -> findLast s
                | CASERANGE (_, _, s, _) -> findLast s
                | LABEL (_, s, _) -> findLast s
                | (A.COMPUTATION _) as s -> s
                | _ -> raise Not_found
              in
              findLast s
          | [] -> raise Not_found
        in
        (* Save the previous data *)
        let old_gnu = ! gnu_body_result in
        let lastComp, isvoidbody =
          match what with 
            ADrop -> (* We are dropping the result *)
              A.NOP cabslu, true
          | _ -> 
              try findLastComputation (List.rev b.A.bstmts), false    
              with Not_found -> 
                E.s (error "Cannot find COMPUTATION in GNU.body")
                  (*                A.NOP cabslu, true *)
        in
        (* Prepare some data to be filled by doExp *)
        let data : (exp * typ) option ref = ref None in
        gnu_body_result := (lastComp, data);

        let se = doBody b in

        gnu_body_result := old_gnu;
        match !data with
          None when isvoidbody -> finishExp se zero voidType
        | None -> E.s (bug "Cannot find COMPUTATION in GNU.body")
        | Some (e, t) -> finishExp se e t
    end

    | A.LABELADDR l -> begin (* GCC's taking the address of a label *)
        let l = lookupLabel l in (* To support locallly declared labels *)
        let addrval =
          try H.find gotoTargetHash l
          with Not_found -> begin
            let res = !gotoTargetNextAddr in
            incr gotoTargetNextAddr;
            H.add gotoTargetHash l res;
            res
          end
        in
        finishExp empty (mkCast (integer addrval) voidPtrType) voidPtrType
    end

    | A.EXPR_PATTERN _ -> E.s (E.bug "EXPR_PATTERN in cabs2cil input")

  with e -> begin
    ignore (E.log "error in doExp (%s)@!" (Printexc.to_string e));
    E.hadErrors := true;
    (i2c (dInstr (dprintf "booo_exp(%t)" d_thisloc) !currentLoc),
     integer 0, intType)
  end

(* bop is always the arithmetic version. Change it to the appropriate pointer 
 * version if necessary *)
and doBinOp (bop: binop) (e1: exp) (t1: typ) (e2: exp) (t2: typ) : typ * exp =
  let doArithmetic () = 
    let tres = arithmeticConversion t1 t2 in
    (* Keep the operator since it is arithmetic *)
    tres, 
    optConstFoldBinOp false bop (mkCastT e1 t1 tres) (mkCastT e2 t2 tres) tres
  in
  let doArithmeticComp () = 
    let tres = arithmeticConversion t1 t2 in
    (* Keep the operator since it is arithemtic *)
    intType, 
    optConstFoldBinOp false bop 
      (mkCastT e1 t1 tres) (mkCastT e2 t2 tres) intType
  in
  let doIntegralArithmetic () = 
    let tres = unrollType (arithmeticConversion t1 t2) in
    match tres with
      TInt _ -> 
        tres,
        optConstFoldBinOp false bop 
          (mkCastT e1 t1 tres) (mkCastT e2 t2 tres) tres
    | _ -> E.s (error "%a operator on a non-integer type" d_binop bop)
  in
  let pointerComparison e1 t1 e2 t2 = 
    (* XL: Do not cast both sides -- what's the point? *)
    intType,
    optConstFoldBinOp false bop e1 e2 intType
  in

  match bop with
    (Mult|Div) -> doArithmetic ()
  | (Mod|BAnd|BOr|BXor) -> doIntegralArithmetic ()
  | (Shiftlt|Shiftrt) -> (* ISO 6.5.7. Only integral promotions. The result 
                          * has the same type as the left hand side *)
      if !msvcMode then
        (* MSVC has a bug. We duplicate it here *)
        doIntegralArithmetic ()
      else
        let t1' = integralPromotion t1 in
        let t2' = integralPromotion t2 in
        t1', 
        optConstFoldBinOp false bop (mkCastT e1 t1 t1') (mkCastT e2 t2 t2') t1'

  | (PlusA|MinusA) 
      when isArithmeticType t1 && isArithmeticType t2 -> doArithmetic ()
  | (Eq|Ne|Lt|Le|Ge|Gt) 
      when isArithmeticType t1 && isArithmeticType t2 -> 
        doArithmeticComp ()
  | PlusA when isPointerType t1 && isIntegralType t2 -> 
      t1, 
      optConstFoldBinOp false PlusPI e1 
        (mkCastT e2 t2 (integralPromotion t2)) t1
  | PlusA when isIntegralType t1 && isPointerType t2 -> 
      t2, 
      optConstFoldBinOp false PlusPI e2 
        (mkCastT e1 t1 (integralPromotion t1)) t2
  | MinusA when isPointerType t1 && isIntegralType t2 -> 
      t1, 
      optConstFoldBinOp false MinusPI e1 
        (mkCastT e2 t2 (integralPromotion t2)) t1
  | MinusA when isPointerType t1 && isPointerType t2 ->
      let commontype = t1 in
      intType,
      optConstFoldBinOp false MinusPP (mkCastT e1 t1 commontype) 
                                      (mkCastT e2 t2 commontype) intType
  | (Le|Lt|Ge|Gt|Eq|Ne) when isPointerType t1 && isPointerType t2 ->
      pointerComparison e1 t1 e2 t2
  | (Eq|Ne) when isPointerType t1 && isZero e2 -> 
      pointerComparison e1 t1 (mkCastT zero !upointType t1) t1
  | (Eq|Ne) when isPointerType t2 && isZero e1 -> 
      pointerComparison (mkCastT zero !upointType t2) t2 e2 t2


  | (Eq|Ne|Le|Lt|Ge|Gt) when isPointerType t1 && isArithmeticType t2 ->
      ignore (warnOpt "Comparison of pointer and non-pointer");
      (* Cast both values to void * *)
      doBinOp bop (mkCastT e1 t1 voidPtrType) voidPtrType 
                  (mkCastT e2 t2 voidPtrType) voidPtrType
  | (Eq|Ne|Le|Lt|Ge|Gt) when isArithmeticType t1 && isPointerType t2 ->
      ignore (warnOpt "Comparison of pointer and non-pointer");
      (* Cast both values to void * *)
      doBinOp bop (mkCastT e1 t1 voidPtrType) voidPtrType 
                  (mkCastT e2 t2 voidPtrType) voidPtrType

  | _ -> E.s (error "doBinOp: %a\n" d_plainexp (BinOp(bop,e1,e2,intType)))

(* Constant fold a conditional. This is because we want to avoid having 
 * conditionals in the initializers. So, we try very hard to avoid creating 
 * new statements. *)
and doCondExp (asconst: bool) (** Try to evaluate the conditional expression 
                                * to TRUE or FALSE, because it occurs in a 
                                * constant *)
              (e: A.expression) : condExpRes = 
  let rec addChunkBeforeCE (c0: chunk) = function
      CEExp (c, e) -> CEExp (c0 @@ c, e)
    | CEAnd (ce1, ce2) -> CEAnd (addChunkBeforeCE c0 ce1, ce2)
    | CEOr (ce1, ce2) -> CEOr (addChunkBeforeCE c0 ce1, ce2)
    | CENot ce1 -> CENot (addChunkBeforeCE c0 ce1)
  in
  let rec canDropCE = function
      CEExp (c, e) -> canDrop c
    | CEAnd (ce1, ce2) | CEOr (ce1, ce2) -> canDropCE ce1 && canDropCE ce2
    | CENot (ce1) -> canDropCE ce1
  in
  match e with 
    A.BINARY (A.AND, e1, e2) -> begin
      let ce1 = doCondExp asconst e1 in
      let ce2 = doCondExp asconst e2 in
      match ce1, ce2 with
        CEExp (se1, ((Const _) as ci1)), _ -> 
          if isConstTrue ci1 then 
            addChunkBeforeCE se1 ce2
          else 
            (* se2 might contain labels so we cannot always drop it *)
            if canDropCE ce2 then 
              ce1 
            else 
              CEAnd (ce1, ce2)
      | CEExp(se1, e1'), CEExp (se2, e2') when 
              !useLogicalOperators && isEmpty se1 && isEmpty se2 -> 
          CEExp (empty, BinOp(LAnd, 
                              mkCast e1' intType, 
                              mkCast e2' intType, intType))
      | _ -> CEAnd (ce1, ce2)
    end

  | A.BINARY (A.OR, e1, e2) -> begin
      let ce1 = doCondExp asconst e1 in
      let ce2 = doCondExp asconst e2 in
      match ce1, ce2 with
        CEExp (se1, (Const(CInt64 _) as ci1)), _ -> 
          if isConstFalse ci1 then 
            addChunkBeforeCE se1 ce2
          else 
            (* se2 might contain labels so we cannot drop it *)
            if canDropCE ce2 then 
              ce1 
            else 
              CEOr (ce1, ce2)

      | CEExp (se1, e1'), CEExp (se2, e2') when 
              !useLogicalOperators && isEmpty se1 && isEmpty se2 ->
          CEExp (empty, BinOp(LOr, mkCast e1' intType, 
                              mkCast e2' intType, intType))
      | _ -> CEOr (ce1, ce2)
    end

  | A.UNARY(A.NOT, e1) -> begin
      match doCondExp asconst e1 with 
        CEExp (se1, (Const _ as ci1)) -> 
          if isConstFalse ci1 then 
            CEExp (se1, one) 
          else
            CEExp (se1, zero)
      | CEExp (se1, e) when isEmpty se1 -> 
          let t = typeOf e in
          if not ((isPointerType t) || (isArithmeticType t))then
            E.s (error "Bad operand to !");
          CEExp (empty, UnOp(LNot, e, intType))

      | ce1 -> CENot ce1
  end

  | _ -> 
      let (se, e, t) = doExp asconst e (AExp None) in
      ignore (checkBool t e);
      CEExp (se, if !lowerConstants then constFold asconst e else e)

and compileCondExp (ce: condExpRes) (st: chunk) (sf: chunk) : chunk = 
  match ce with 
  | CEAnd (ce1, ce2) ->
      let (sf1, sf2) = 
        (* If sf is small then will copy it *)
        try (sf, duplicateChunk sf) 
        with Failure _ -> 
          let lab = newLabelName "_L" in
          (gotoChunk lab lu, consLabel lab sf !currentLoc false)
      in
      let st' = compileCondExp ce2 st sf1 in
      let sf' = sf2 in
      compileCondExp ce1 st' sf'
        
  | CEOr (ce1, ce2) -> 
      let (st1, st2) = 
        (* If st is small then will copy it *)
        try (st, duplicateChunk st) 
        with Failure _ -> 
          let lab = newLabelName "_L" in
          (gotoChunk lab lu, consLabel lab st !currentLoc false)
      in
      let st' = st1 in
      let sf' = compileCondExp ce2 st2 sf in
      compileCondExp ce1 st' sf'
        
  | CENot ce1 -> compileCondExp ce1 sf st
        
  | CEExp (se, e) -> begin
      match e with 
        Const(CInt64(i,_,_)) when i <> Int64.zero && canDrop sf -> se @@ st
      | Const(CInt64(z,_,_)) when z = Int64.zero && canDrop st -> se @@ sf
      | _ -> se @@ ifChunk e !currentLoc st sf
  end
 

(* A special case for conditionals *)
and doCondition (isconst: bool) (* If we are in constants, we do our best to 
                                 * eliminate the conditional *)
                (e: A.expression) 
                (st: chunk)
                (sf: chunk) : chunk = 
  compileCondExp (doCondExp isconst e) st sf


and doPureExp (e : A.expression) : exp = 
  let (se, e', _) = doExp true e (AExp None) in
  if isNotEmpty se then
   E.s (error "doPureExp: not pure");
  e'

and doInitializer
    (vi: varinfo)
    (inite: A.init_expression) 
   (* Return the accumulated chunk, the initializer and the new type (might be 
    * different for arrays) *)
  : chunk * init * typ = 

  (* Setup the pre-initializer *)
  let topPreInit = ref NoInitPre in
  if debugInit then 
    ignore (E.log "\nStarting a new initializer for %s : %a\n" 
              vi.vname d_type vi.vtype);
  let topSetupInit (o: offset) (e: exp) = 
    if debugInit then 
      ignore (E.log " set %a := %a\n"  d_lval (Var vi, o) d_exp e);
    let newinit = setOneInit !topPreInit o e in
    if newinit != !topPreInit then topPreInit := newinit
  in
  let acc, restl = 
    let so = makeSubobj vi vi.vtype NoOffset in
    doInit vi.vglob topSetupInit so empty [ (A.NEXT_INIT, inite) ] 
  in
  if restl <> [] then 
    ignore (warn "Ignoring some initializers");
  (* sm: we used to do array-size fixups here, but they only worked
   * for toplevel array types; now, collectInitializer does the job,
   * including for nested array types *)
  let typ' = unrollType vi.vtype in
  if debugInit then 
    ignore (E.log "Collecting the initializer for %s\n" vi.vname);
  let (init, typ'') = collectInitializer !topPreInit typ' in
  if debugInit then
    ignore (E.log "Finished the initializer for %s\n  init=%a\n  typ=%a\n  acc=%a\n" 
           vi.vname d_init init d_type typ' d_chunk acc);
  acc, init, typ''


  
(* Consume some initializers. Watch out here. Make sure we use only 
 * tail-recursion because these things can be big.  *)
and doInit
    (isconst: bool)  
    (setone: offset -> exp -> unit) (* Use to announce an intializer *)
    (so: subobj)
    (acc: chunk)
    (initl: (A.initwhat * A.init_expression) list)

    (* Return the resulting chunk along with some unused initializers *)
  : chunk * (A.initwhat * A.init_expression) list = 

  let whoami () = d_lval () (Var so.host, so.soOff) in
  
  let initl1 = 
    match initl with
    | (A.NEXT_INIT, 
       A.SINGLE_INIT (A.CAST ((s, dt), ie))) :: rest -> 
         let s', dt', ie' = preprocessCast s dt ie in
         (A.NEXT_INIT, A.SINGLE_INIT (A.CAST ((s', dt'), ie'))) :: rest
    | _ -> initl
  in
      (* Sometimes we have a cast in front of a compound (in GCC). This 
       * appears as a single initializer. Ignore the cast  *)
  let initl2 = 
    match initl1 with
      (what, 
       A.SINGLE_INIT (A.CAST (_, A.COMPOUND_INIT ci))) :: rest -> 
         (what, A.COMPOUND_INIT ci) :: rest
    | _ -> initl1
  in
  let allinitl = initl2 in

  if debugInit then begin
    ignore (E.log "doInit for %t %s (current %a). Looking at: " whoami
              (if so.eof then "(eof)" else "")
              d_lval (Var so.host, so.curOff));
    (match allinitl with 
      [] -> ignore (E.log "[]")
    | (what, ie) :: _ -> 
        withCprint 
          Cprint.print_init_expression (A.COMPOUND_INIT [(what, ie)]));
    ignore (E.log "\n");
  end;
  match unrollType so.soTyp, allinitl with 
    _, [] -> acc, [] (* No more initializers return *)

        (* No more subobjects *)
  | _, (A.NEXT_INIT, _) :: _ when so.eof -> acc, allinitl
    

        (* If we are at an array of characters and the initializer is a 
         * string literal (optionally enclosed in braces) then explode the 
         * string into characters *)
  | TArray(bt, leno, _), 
      (A.NEXT_INIT, 
       (A.SINGLE_INIT(A.CONSTANT (A.CONST_STRING s))|
       A.COMPOUND_INIT 
         [(A.NEXT_INIT, 
           A.SINGLE_INIT(A.CONSTANT 
                           (A.CONST_STRING s)))])) :: restil
    when (match unrollType bt with
            TInt((IChar|IUChar|ISChar), _) -> true
          | TInt _ ->
              (*Base type is a scalar other than char. Maybe a wchar_t?*)
	      E.s (error "Using a string literal to initialize something other than a character array.\n")
          | _ ->  false (* OK, this is probably an array of strings. Handle *)
         )              (* it with the other arrays below.*)
    ->
      let charinits =
	let init c = A.NEXT_INIT, A.SINGLE_INIT(A.CONSTANT (A.CONST_CHAR [c]))
	in
	let collector =
	  (* ISO 6.7.8 para 14: final NUL added only if no size specified, or
	   * if there is room for it; btw, we can't rely on zero-init of
	   * globals, since this array might be a local variable *)
          if ((isNone leno) or ((String.length s) < (integerArrayLength leno)))
            then ref [init Int64.zero]
            else ref []  
        in
	for pos = String.length s - 1 downto 0 do
	  collector := init (Int64.of_int (Char.code (s.[pos]))) :: !collector
	done;
	!collector
      in
      (* Create a separate object for the array *)
      let so' = makeSubobj so.host so.soTyp so.soOff in 
      (* Go inside the array *)
      let leno = integerArrayLength leno in
      so'.stack <- [InArray(so'.curOff, bt, leno, ref 0)];
      normalSubobj so';
      let acc', initl' = doInit isconst setone so' acc charinits in
      if initl' <> [] then 
        ignore (warn "Too many initializers for character array %t" whoami);
      (* Advance past the array *)
      advanceSubobj so;
      (* Continue *)
      let res = doInit isconst setone so acc' restil in
      res

        (* If we are at an array of WIDE characters and the initializer is a 
         * WIDE string literal (optionally enclosed in braces) then explore
         * the WIDE string into characters *)
  (* [weimer] Wed Jan 30 15:38:05 PST 2002
   * Despite what the compiler says, this match case is used and it is
   * important. *)
  | TArray(bt, leno, _), 
      (A.NEXT_INIT, 
       (A.SINGLE_INIT(A.CONSTANT (A.CONST_WSTRING s)) |
       A.COMPOUND_INIT 
         [(A.NEXT_INIT, 
           A.SINGLE_INIT(A.CONSTANT 
                           (A.CONST_WSTRING s)))])) :: restil
    when(let bt' = unrollType bt in
         match bt' with 
           (* compare bt to wchar_t, ignoring signed vs. unsigned *)
	   TInt _ when (bitsSizeOf bt') = (bitsSizeOf !wcharType) -> true
	 | TInt _ ->
              (*Base type is a scalar other than wchar_t.  Maybe a char?*)
	      E.s (error "Using a wide string literal to initialize something other than a wchar_t array.\n")
	 | _ -> false (* OK, this is probably an array of strings. Handle *)
        )             (* it with the other arrays below.*)
    -> 
      let maxWChar =  (*  (2**(bitsSizeOf !wcharType)) - 1  *)
        Int64.sub (Int64.shift_left Int64.one (bitsSizeOf !wcharType)) 
          Int64.one in
      let charinits = 
	let init c = 
	  if (compare c maxWChar > 0) then (* if c > maxWChar *)
	    E.s (error "cab2cil:doInit:character 0x%Lx too big." c);
          A.NEXT_INIT, 
          A.SINGLE_INIT(A.CONSTANT (A.CONST_INT (Int64.to_string c)))
	in
        (List.map init s) @
        (
	  (* ISO 6.7.8 para 14: final NUL added only if no size specified, or
	   * if there is room for it; btw, we can't rely on zero-init of
	   * globals, since this array might be a local variable *)
          if ((isNone leno) or ((List.length s) < (integerArrayLength leno)))
            then [init Int64.zero]
            else [])
(*
        List.map 
          (fun c -> 
	    if (compare c maxWChar > 0) then (* if c > maxWChar *)
	      E.s (error "cab2cil:doInit:character 0x%Lx too big." c)
	    else
              (A.NEXT_INIT, 
               A.SINGLE_INIT(A.CONSTANT (A.CONST_INT (Int64.to_string c)))))
      s
*)
      in
      (* Create a separate object for the array *)
      let so' = makeSubobj so.host so.soTyp so.soOff in 
      (* Go inside the array *)
      let leno = integerArrayLength leno in
      so'.stack <- [InArray(so'.curOff, bt, leno, ref 0)];
      normalSubobj so';
      let acc', initl' = doInit isconst setone so' acc charinits in
      if initl' <> [] then 
        (* sm: see above regarding ISO 6.7.8 para 14, which is not implemented
         * for wchar_t because, as far as I can tell, we don't even put in
         * the automatic NUL (!) *)
        ignore (warn "Too many initializers for wchar_t array %t" whoami);
      (* Advance past the array *)
      advanceSubobj so;
      (* Continue *)
      doInit isconst setone so acc' restil
                    
      (* If we are at an array and we see a single initializer then it must 
       * be one for the first element *)
  | TArray(bt, leno, al), (A.NEXT_INIT, A.SINGLE_INIT oneinit) :: restil  -> 
      (* Grab the length if there is one *)
      let leno = integerArrayLength leno in
      so.stack <- InArray(so.soOff, bt, leno, ref 0) :: so.stack; 
      normalSubobj so;
      (* Start over with the fields *)
      doInit isconst setone so acc allinitl

    (* If we are at a composite and we see a single initializer of the same 
     * type as the composite then grab it all. If the type is not the same 
     * then we must go on and try to initialize the fields *)
  | TComp (comp, _), (A.NEXT_INIT, A.SINGLE_INIT oneinit) :: restil -> 
      let se, oneinit', t' = doExp isconst oneinit (AExp None) in
      if (match unrollType t' with 
             TComp (comp', _) when comp'.ckey = comp.ckey -> true 
            | _ -> false) 
      then begin
        (* Initialize the whole struct *)
        setone so.soOff oneinit';
        (* Advance to the next subobject *)
        advanceSubobj so;
        doInit isconst setone so (acc @@ se) restil
      end else begin (* Try to initialize fields *)
        let toinit = fieldsToInit comp None in
        so.stack <- InComp(so.soOff, comp, toinit) :: so.stack;
        normalSubobj so;
        doInit isconst setone so acc allinitl
      end

     (* A scalar with a single initializer *)
  | _, (A.NEXT_INIT, A.SINGLE_INIT oneinit) :: restil ->  
      let se, oneinit', t' = doExp isconst oneinit (AExp(Some so.soTyp)) in
(*
      ignore (E.log "oneinit'=%a, t'=%a, so.soTyp=%a\n" 
           d_exp oneinit' d_type t' d_type so.soTyp);
*)
      setone so.soOff (mkCastT oneinit' t' so.soTyp);
      (* Move on *)
      advanceSubobj so; 
      doInit isconst setone so (acc @@ se) restil


     (* An array with a compound initializer. The initializer is for the 
      * array elements *)
  | TArray (bt, leno, _), (A.NEXT_INIT, A.COMPOUND_INIT initl) :: restil -> 
      (* Create a separate object for the array *)
      let so' = makeSubobj so.host so.soTyp so.soOff in 
      (* Go inside the array *)
      let leno = integerArrayLength leno in
      so'.stack <- [InArray(so'.curOff, bt, leno, ref 0)];
      normalSubobj so';
      let acc', initl' = doInit isconst setone so' acc initl in
      if initl' <> [] then 
        ignore (warn "Too many initializers for array %t" whoami);
      (* Advance past the array *)
      advanceSubobj so;
      (* Continue *)
      let res = doInit isconst setone so acc' restil in
      res

   (* We have a designator that tells us to select the matching union field. 
    * This is to support a GCC extension *)
  | TComp(ci, _), [(A.NEXT_INIT,
                    A.COMPOUND_INIT [(A.INFIELD_INIT ("___matching_field", 
                                                     A.NEXT_INIT), 
                                      A.SINGLE_INIT oneinit)])] 
                      when not ci.cstruct -> 
      (* Do the expression to find its type *)
      let _, _, t' = doExp isconst oneinit (AExp None) in
      let tsig = typeSigWithAttrs (fun _ -> []) t' in
      let rec findField = function
          [] -> E.s (error "Cannot find matching union field in cast")
        | fi :: rest 
           when Util.equals (typeSigWithAttrs (fun _ -> []) fi.ftype) tsig 
           -> fi
        | _ :: rest -> findField rest
      in
      let fi = findField ci.cfields in
      (* Change the designator and redo *)
      doInit isconst setone so acc [(A.INFIELD_INIT (fi.fname, A.NEXT_INIT),
                                     A.SINGLE_INIT oneinit)]
        

        (* A structure with a composite initializer. We initialize the fields*)
  | TComp (comp, _), (A.NEXT_INIT, A.COMPOUND_INIT initl) :: restil ->
      (* Create a separate subobject iterator *)
      let so' = makeSubobj so.host so.soTyp so.soOff in
      (* Go inside the comp *)
      so'.stack <- [InComp(so'.curOff, comp, fieldsToInit comp None)];
      normalSubobj so';
      let acc', initl' = doInit isconst setone so' acc initl in
      if initl' <> [] then 
        ignore (warn "Too many initializers for structure");
      (* Advance past the structure *)
      advanceSubobj so;
      (* Continue *)
      doInit isconst setone so acc' restil

        (* A scalar with a initializer surrounded by braces *)
  | _, (A.NEXT_INIT, A.COMPOUND_INIT [(A.NEXT_INIT, 
                                       A.SINGLE_INIT oneinit)]) :: restil ->
      let se, oneinit', t' = doExp isconst oneinit (AExp(Some so.soTyp)) in
      setone so.soOff (mkCastT oneinit' t' so.soTyp);
      (* Move on *)
      advanceSubobj so; 
      doInit isconst setone so (acc @@ se) restil

  | t, (A.NEXT_INIT, _) :: _ -> 
      E.s (unimp "doInit: unexpected NEXT_INIT for %a\n" d_type t);

   (* We have a designator *)        
  | _, (what, ie) :: restil when what != A.NEXT_INIT -> 
      (* Process a designator and position to the designated subobject *)
      let rec addressSubobj 
          (so: subobj) 
          (what: A.initwhat) 
          (acc: chunk) : chunk = 
        (* Always start from the current element *)
        so.stack <- []; so.eof <- false; 
        normalSubobj so;
        let rec address (what: A.initwhat) (acc: chunk)  : chunk = 
          match what with 
            A.NEXT_INIT -> acc
          | A.INFIELD_INIT (fn, whatnext) -> begin
              match unrollType so.soTyp with 
                TComp (comp, _) -> 
                  let toinit = fieldsToInit comp (Some fn) in
                  so.stack <- InComp(so.soOff, comp, toinit) :: so.stack;
                  normalSubobj so;
                  address whatnext acc
                    
              | _ -> E.s (error "Field designator %s not in a struct " fn)
          end
                
          | A.ATINDEX_INIT(idx, whatnext) -> begin
              match unrollType so.soTyp with 
                TArray (bt, leno, _) -> 
                  let ilen = integerArrayLength leno in
                  let nextidx', doidx = 
                    let (doidx, idxe', _) = 
                      doExp true idx (AExp(Some intType)) in
                    match constFold true idxe', isNotEmpty doidx with
                      Const(CInt64(x, _, _)), false -> Int64.to_int x, doidx
                    | _ -> E.s (error 
                      "INDEX initialization designator is not a constant")
                  in
                  if nextidx' < 0 || nextidx' >= ilen then
                    E.s (error "INDEX designator is outside bounds");
                  so.stack <- 
                     InArray(so.soOff, bt, ilen, ref nextidx') :: so.stack;
                  normalSubobj so;
                  address whatnext (acc @@ doidx)
                    
              | _ -> E.s (error "INDEX designator for a non-array")
          end 
                
          | A.ATINDEXRANGE_INIT _ -> 
              E.s (bug "addressSubobj: INDEXRANGE")
        in
        address what acc
      in
      (* First expand the INDEXRANGE by making copies *)
      let rec expandRange (top: A.initwhat -> A.initwhat) = function
        | A.INFIELD_INIT (fn, whatnext) -> 
            expandRange (fun what -> top (A.INFIELD_INIT(fn, what))) whatnext
        | A.ATINDEX_INIT (idx, whatnext) ->
            expandRange (fun what -> top (A.ATINDEX_INIT(idx, what))) whatnext

        | A.ATINDEXRANGE_INIT (idxs, idxe) -> 
            let (doidxs, idxs', _) = 
              doExp true idxs (AExp(Some intType)) in
            let (doidxe, idxe', _) = 
              doExp true idxe (AExp(Some intType)) in
            if isNotEmpty doidxs || isNotEmpty doidxe then 
              E.s (error "Range designators are not constants\n");
            let first, last = 
              match constFold true idxs', constFold true idxe' with
                Const(CInt64(s, _, _)), 
                Const(CInt64(e, _, _)) -> 
                  Int64.to_int s, Int64.to_int e
              | _ -> E.s (error 
                 "INDEX_RANGE initialization designator is not a constant")
            in
            if first < 0 || first > last then 
              E.s (error 
                     "start index larger than end index in range initializer");
            let rec loop (i: int) = 
              if i > last then restil
              else 
                (top (A.ATINDEX_INIT(A.CONSTANT(A.CONST_INT(string_of_int i)),
                                     A.NEXT_INIT)), ie) 
                :: loop (i + 1) 
            in
            doInit isconst setone so acc (loop first)

        | A.NEXT_INIT -> (* We have not found any RANGE *) 
            let acc' = addressSubobj so what acc in
            doInit isconst setone so (acc @@ acc') 
              ((A.NEXT_INIT, ie) :: restil)
      in
      expandRange (fun x -> x) what
  
  | t, (what, ie) :: _ -> 
      E.s (bug "doInit: cases for t=%a" d_type t) 


(* Create and add to the file (if not already added) a global. Return the 
 * varinfo *)
and createGlobal (specs : (typ * storage * bool * A.attribute list)) 
                 (((n,ndt,a,cloc), inite) : A.init_name) : varinfo = 
  try
    if debugGlobal then 
      ignore (E.log "createGlobal: %s\n" n);
            (* Make a first version of the varinfo *)
    let vi = makeVarInfoCabs ~isformal:false 
                             ~isglobal:true (convLoc cloc) specs (n,ndt,a) in
    (* Add the variable to the environment before doing the initializer 
     * because it might refer to the variable itself *)
    if isFunctionType vi.vtype then begin
      if inite != A.NO_INIT  then
        E.s (error "Function declaration with initializer (%s)\n"
               vi.vname);
      (* sm: if it's a function prototype, and the storage class *)
      (* isn't specified, make it 'extern'; this fixes a problem *)
      (* with no-storage prototype and static definition *)
      if vi.vstorage = NoStorage then 
        (*(trace "sm" (dprintf "adding extern to prototype of %s\n" n));*)
        vi.vstorage <- Extern;
    end;
    let vi, alreadyInEnv = makeGlobalVarinfo (inite != A.NO_INIT) vi in
(*
    ignore (E.log "createGlobal %a: %s type=%a\n" 
       d_loc (convLoc cloc) vi.vname d_plaintype vi.vtype);
*)
            (* Do the initializer and complete the array type if necessary *)
    let init : init option = 
      if inite = A.NO_INIT then 
        None
      else 
        let se, ie', et = doInitializer vi inite in
        (* Maybe we now have a better type *)
        vi.vtype <- et;
        if isNotEmpty se then 
          E.s (error "global initializer");
        Some ie'
    in

    try
      let oldloc = H.find alreadyDefined vi.vname in
      if init != None then begin
        E.s (error "Global %s was already defined at %a\n" 
               vi.vname d_loc oldloc);
      end;
      if debugGlobal then 
        ignore (E.log " global %s was already defined\n" vi.vname);
      (* Do not declare it again *)
      vi
    with Not_found -> begin
      (* Not already defined *)
      if debugGlobal then 
        ignore (E.log " first definition for %s\n" vi.vname);
      if init != None then begin
        (* weimer: Sat Dec  8 17:43:34  2001
         * MSVC NT Kernel headers include this lovely line:
         * extern const GUID __declspec(selectany) \
         *  MOUNTDEV_MOUNTED_DEVICE_GUID = { 0x53f5630d, 0xb6bf, 0x11d0, { \
         *  0x94, 0xf2, 0x00, 0xa0, 0xc9, 0x1e, 0xfb, 0x8b } };
         * So we allow "extern" + "initializer" if "const" is
         * around. *)
        (* sm: As I read the ISO spec, in particular 6.9.2 and 6.7.8,
         * "extern int foo = 3" is exactly equivalent to "int foo = 3";
         * that is, if you put an initializer, then it is a definition,
         * and "extern" is redundantly giving the name external linkage.
         * gcc emits a warning, I guess because it is contrary to
         * usual practice, but I think CIL warnings should be about
         * semantic rather than stylistic issues, so I see no reason to
         * even emit a warning. *)
        if vi.vstorage = Extern then
          vi.vstorage <- NoStorage;     (* equivalent and canonical *)

        H.add alreadyDefined vi.vname !currentLoc;
        IH.remove mustTurnIntoDef vi.vid;
        cabsPushGlobal (GVar(vi, {init = init}, !currentLoc));
        vi
      end else begin
        if not (isFunctionType vi.vtype) 
           && not (IH.mem mustTurnIntoDef vi.vid) then 
          begin
            IH.add mustTurnIntoDef vi.vid true
          end;
        if not alreadyInEnv then begin (* Only one declaration *)
          (* If it has function type it is a prototype *)
          cabsPushGlobal (GVarDecl (vi, !currentLoc));
          vi
        end else begin
          if debugGlobal then 
            ignore (E.log " already in env %s\n" vi.vname);
          vi
        end
      end
    end
  with e -> begin
    ignore (E.log "error in createGlobal(%s: %a): %s\n" n
              d_loc !currentLoc
              (Printexc.to_string e));
    cabsPushGlobal (dGlobal (dprintf "booo - error in global %s (%t)" 
                           n d_thisloc) !currentLoc);
    dummyFunDec.svar
  end
(*
          ignore (E.log "Env after processing global %s is:@!%t@!" 
                    n docEnv);
          ignore (E.log "Alpha after processing global %s is:@!%t@!" 
                    n docAlphaTable)
*)

(* Must catch the Static local variables. Make them global *)
and createLocal ((_, sto, _, _) as specs)
                ((((n, ndt, a, cloc) : A.name), 
                  (inite: A.init_expression)) as init_name) 
  : chunk =
  let loc = convLoc cloc in
  (* Check if we are declaring a function *)
  let rec isProto (dt: decl_type) : bool = 
    match dt with
    | PROTO (JUSTBASE, _, _) -> true
    | PROTO (x, _, _) -> isProto x
    | PARENTYPE (_, x, _) -> isProto x
    | ARRAY (x, _, _) -> isProto x
    | PTR (_, x) -> isProto x
    | _ -> false
  in
  match ndt with 
    (* Maybe we have a function prototype in local scope. Make it global. We 
     * do this even if the storage is Static *)
  | _ when isProto ndt -> 
      let vi = createGlobal specs init_name in 
      (* Add it to the environment to shadow previous decls *)
      addLocalToEnv n (EnvVar vi);
      empty
    
  | _ when sto = Static -> 
      if debugGlobal then 
        ignore (E.log "createGlobal (local static): %s\n" n);


      (* Now alpha convert it to make sure that it does not conflict with 
       * existing globals or locals from this function. *)
      let newname, _  = newAlphaName true "" n in
      (* Make it global  *)
      let vi = makeVarInfoCabs ~isformal:false
                               ~isglobal:true 
                               loc specs (newname, ndt, a) in
      (* However, we have a problem if a real global appears later with the 
       * name that we have happened to choose for this one. Remember these names 
       * for later. *)
      H.add staticLocals vi.vname vi;
      (* Add it to the environment as a local so that the name goes out of 
       * scope properly *)
      addLocalToEnv n (EnvVar vi);

      (* Maybe this is an array whose length depends on something with local 
         scope, e.g. "static char device[ sizeof(local) ]".
         Const-fold the type to fix this. *)
      vi.vtype <- constFoldType vi.vtype;

      let init : init option = 
        if inite = A.NO_INIT then 
          None
        else begin 
          let se, ie', et = doInitializer vi inite in
          (* Maybe we now have a better type *)
          vi.vtype <- et;
          if isNotEmpty se then 
            E.s (error "global static initializer");
          (* Maybe the initializer refers to the function itself. 
             Push a prototype for the function, just in case. Hopefully,
             if does not refer to the locals *)
          cabsPushGlobal (GVarDecl (!currentFunctionFDEC.svar, !currentLoc));
          Some ie'
        end
      in
      cabsPushGlobal (GVar(vi, {init = init}, !currentLoc));
      empty

  (* Maybe we have an extern declaration. Make it a global *)
  | _ when sto = Extern ->
      let vi = createGlobal specs init_name in
      (* Add it to the local environment to ensure that it shadows previous 
       * local variables *)
      addLocalToEnv n (EnvVar vi);
      empty

  | _ -> 
      (* Make a variable of potentially variable size. If se0 <> empty then 
       * it is a variable size variable *)
      let vi,se0,len,isvarsize = 
        makeVarSizeVarInfo loc specs (n, ndt, a) in

      let vi = alphaConvertVarAndAddToEnv true vi in        (* Replace vi *)
      let se1 = 
        if isvarsize then begin (* Variable-sized array *) 
          ignore (warn "Variable-sized local variable %s" vi.vname);
          (* Make a local variable to keep the length *)
          let savelen = 
            makeVarInfoCabs 
                        ~isformal:false
                        ~isglobal:false 
	                loc
                        (TInt(IUInt, []), NoStorage, false, [])
                        ("__lengthof" ^ vi.vname,JUSTBASE, []) 
          in
          (* Register it *)
          let savelen = alphaConvertVarAndAddToEnv true savelen in
          (* Compute the sizeof *)
          let sizeof = 
            BinOp(Mult, 
                  SizeOfE (Lval(Mem(Lval(var vi)), NoOffset)),
                  Lval (var savelen), !typeOfSizeOf) in
          (* Register the length *)
          IH.add varSizeArrays vi.vid sizeof;
          (* There can be no initializer for this *)
          if inite != A.NO_INIT then 
            E.s (error "Variable-sized array cannot have initializer");
          se0 +++ (Set(var savelen, len, !currentLoc)) 
            (* Initialize the variable *)
            +++ (Call(Some(var vi), Lval(var (allocaFun ())), 
                      [ sizeof  ], !currentLoc))
        end else empty
      in
      if inite = A.NO_INIT then
        se1 (* skipChunk *)
      else begin
        let se4, ie', et = doInitializer vi inite in
        (* Fix the length *)
        (match vi.vtype, ie', et with 
            (* We have a length now *)
          TArray(_,None, _), _, TArray(_, Some _, _) -> vi.vtype <- et
            (* Initializing a local array *)
        | TArray(TInt((IChar|IUChar|ISChar), _) as bt, None, a),
             SingleInit(Const(CStr s)), _ -> 
               vi.vtype <- TArray(bt, 
                                  Some (integer (String.length s + 1)),
                                  a)
        | _, _, _ -> ());

        (* Now create assignments instead of the initialization *)
        se1 @@ se4 @@ (assignInit (Var vi, NoOffset) ie' et empty)
      end
          
and doAliasFun vtype (thisname:string) (othername:string) 
  (sname:single_name) (loc: cabsloc) : unit =
  (* This prototype declares that name is an alias for 
     othername, which must be defined in this file *)
(*   E.log "%s is alias for %s at %a\n" thisname othername  *)
(*     d_loc !currentLoc; *)
  let rt, formals, isva, _ = splitFunctionType vtype in
  if isva then E.s (error "%a: alias unsupported with varargs."
                      d_loc !currentLoc);
  let args = List.map 
               (fun (n,_,_) -> A.VARIABLE n)
               (argsToList formals) in
  let call = A.CALL (A.VARIABLE othername, args) in
  let stmt = if isVoidType rt then A.COMPUTATION(call, loc)
                              else A.RETURN(call, loc)
  in
  let body = { A.blabels = []; A.battrs = []; A.bstmts = [stmt] } in
  let fdef = A.FUNDEF (sname, body, loc, loc) in
  ignore (doDecl true fdef);
  (* get the new function *)
  let v,_ = try lookupGlobalVar thisname
            with Not_found -> E.s (bug "error in doDecl") in
  v.vattr <- dropAttribute "alias" v.vattr

          
(* Do one declaration *)
and doDecl (isglobal: bool) : A.definition -> chunk = function
  | A.DECDEF ((s, nl), loc) ->
      currentLoc := convLoc(loc);
      (* Do the specifiers exactly once *)
      let sugg = 
        match nl with 
          [] -> ""
        | ((n, _, _, _), _) :: _ -> n
      in
      let spec_res = doSpecList sugg s in
      (* Do all the variables and concatenate the resulting statements *)
      let doOneDeclarator (acc: chunk) (name: init_name) = 
        let (n,ndt,a,l),_ = name in
        if isglobal then begin
          let bt,_,_,attrs = spec_res in
          let vtype, nattr = 
            doType (AttrName false) bt (A.PARENTYPE(attrs, ndt, a)) in
          (match filterAttributes "alias" nattr with
             [] -> (* ordinary prototype. *)
               ignore (createGlobal spec_res name)
              (*  E.log "%s is not aliased\n" name *)
           | [Attr("alias", [AStr othername])] ->
               if not (isFunctionType vtype) then begin
                 ignore (warn 
                   "%a: CIL only supports attribute((alias)) for functions.\n"
                   d_loc !currentLoc);
                 ignore (createGlobal spec_res name)
               end else
                 doAliasFun vtype n othername (s, (n,ndt,a,l)) loc
           | _ -> E.s (error "Bad alias attribute at %a" d_loc !currentLoc));
          acc
        end else 
          acc @@ createLocal spec_res name
      in
      let res = List.fold_left doOneDeclarator empty nl in
(*
      ignore (E.log "after doDecl %a: res=%a\n" 
           d_loc !currentLoc d_chunk res);
*)
      res



  | A.TYPEDEF (ng, loc) -> 
     currentLoc := convLoc(loc);
     doTypedef ng; empty

  | A.ONLYTYPEDEF (s, loc) -> 
      currentLoc := convLoc(loc);
      doOnlyTypedef s; empty

  | A.GLOBASM (s,loc) when isglobal ->
      currentLoc := convLoc(loc);
      cabsPushGlobal (GAsm (s, !currentLoc));
      empty
        
  | A.PRAGMA (a, loc) when isglobal -> begin
      currentLoc := convLoc(loc);
      match doAttr ("dummy", [a]) with
        [Attr("dummy", [a'])] ->
          let a'' =
            match a' with
            | ACons (s, args) -> Attr (s, args)
            | _ -> E.s (error "Unexpected attribute in #pragma")
          in
          cabsPushGlobal (GPragma (a'', !currentLoc));
          empty

      | _ -> E.s (error "Too many attributes in pragma")
  end
  | A.TRANSFORMER (_, _, _) -> E.s (E.bug "TRANSFORMER in cabs2cil input")
  | A.EXPRTRANSFORMER (_, _, _) -> 
      E.s (E.bug "EXPRTRANSFORMER in cabs2cil input")
        
  (* If there are multiple definitions of extern inline, turn all but the 
   * first into a prototype *)
  | A.FUNDEF (((specs,(n,dt,a,loc')) : A.single_name),
              (body : A.block), loc, _) 
      when isglobal && isExtern specs && isInline specs 
           && (H.mem genv (n ^ "__extinline")) -> 
       currentLoc := convLoc(loc);
       let othervi, _ = lookupVar (n ^ "__extinline") in
       if othervi.vname = n then 
         (* The previous entry in the env is also an extern inline version
            of n. *)
         ignore (warn "Duplicate extern inline definition for %s ignored" n)
       else begin
         (* Otherwise, the previous entry is an ordinary function that
            happens to be named __extinline.  Renaming n to n__extinline
            would confict with other, so report an error. *)
         E.s (unimp("Trying to rename %s to\n %s__extinline, but %s__extinline"
                     ^^ " already exists in the env.\n  \"__extinline\" is"
                     ^^ " reserved for CIL.\n") n n n)
       end;
       (* Treat it as a prototype *)
       doDecl isglobal (A.DECDEF ((specs, [((n,dt,a,loc'), A.NO_INIT)]), loc))

  | A.FUNDEF (((specs,(n,dt,a, _)) : A.single_name),
              (body : A.block), loc1, loc2) when isglobal ->
    begin
      let funloc = convLoc loc1 in
      let endloc = convLoc loc2 in
(*      ignore (E.log "Definition of %s at %a\n" n d_loc funloc); *)
      currentLoc := funloc;
      E.withContext
        (fun _ -> dprintf "2cil: %s" n)
        (fun _ ->
          try
            IH.clear callTempVars;

            (* Make the fundec right away, and we'll populate it later. We 
             * need this throughout the code to create temporaries. *)
            currentFunctionFDEC := 
               { svar     = makeGlobalVar "@tempname@" voidType;
                 slocals  = []; (* For now we'll put here both the locals and 
                                 * the formals. Then "endFunction" will 
                                 * separate them *)
                 sformals = []; (* Not final yet *)
                 smaxid   = 0;
                 sbody    = dummyFunDec.sbody; (* Not final yet *)
		 smaxstmtid = None;
                 sallstmts = [];
               };
	    !currentFunctionFDEC.svar.vdecl <- funloc;

            constrExprId := 0;
            (* Setup the environment. Add the formals to the locals. Maybe
            * they need alpha-conv  *)
            enterScope ();  (* Start the scope *)
            
            IH.clear varSizeArrays;
            
            (* Do not process transparent unions in function definitions.
            * We'll do it later *)
            transparentUnionArgs := [];

            (* Fix the NAME and the STORAGE *)
            let _ = 
              let bt,sto,inl,attrs = doSpecList n specs in
              !currentFunctionFDEC.svar.vinline <- inl;
              
              let ftyp, funattr = 
                doType (AttrName false) bt (A.PARENTYPE(attrs, dt, a)) in
              !currentFunctionFDEC.svar.vtype <- ftyp;
              !currentFunctionFDEC.svar.vattr <- funattr;

              (* If this is the definition of an extern inline then we change 
               * its name, by adding the suffix __extinline. We also make it 
               * static *)
              let n', sto' =
                let n' = n ^ "__extinline" in
                if inl && sto = Extern then 
                  n', Static
                else begin 
                  (* Maybe this is the body of a previous extern inline. Then 
                  * we must take that one out of the environment because it 
                  * is not used from here on. This will also ensure that 
                  * then we make this functions' varinfo we will not think 
                  * it is a duplicate definition *)
                  (try
                    ignore (lookupVar n'); (* if this succeeds, n' is defined*)
                    let oldvi, _ = lookupVar n in
                    if oldvi.vname = n' then begin 
                      (* oldvi is an extern inline function that has been
                         renamed to n ^ "__extinline".  Remove it from the
                         environment. *)
                      H.remove env n; H.remove genv n;
                      H.remove env n'; H.remove genv n'
                    end 
                    else
                      (* oldvi is not a renamed extern inline function, and
                         we should do nothing.  The reason the lookup
                         of n' succeeded is probably because there's
                         an ordinary function that happens to be named,
                         n ^ "__extinline", probably as a result of a previous
                         pass through CIL.   See small2/extinline.c*)
                      ()
                   with Not_found -> ());
                  n, sto 
                end
              in
              (* Now we have the name and the storage *)
              !currentFunctionFDEC.svar.vname <- n';
              !currentFunctionFDEC.svar.vstorage <- sto'
            in
              
            (* Add the function itself to the environment. Add it before 
            * you do the body because the function might be recursive. Add 
            * it also before you add the formals to the environment 
            * because there might be a formal with the same name as the 
            * function and we want it to take precedence. *)
            (* Make a variable out of it and put it in the environment *)
            !currentFunctionFDEC.svar <- 
               fst (makeGlobalVarinfo true !currentFunctionFDEC.svar);

            (* If it is extern inline then we add it to the global 
             * environment for the original name as well. This will ensure 
             * that all uses of this function will refer to the renamed 
             * function *)
            addGlobalToEnv n (EnvVar !currentFunctionFDEC.svar);

            if H.mem alreadyDefined !currentFunctionFDEC.svar.vname then
              E.s (error "There is a definition already for %s" n);

(*
            ignore (E.log "makefunvar:%s@! type=%a@! vattr=%a@!"
                        n d_type thisFunctionVI.vtype 
                        d_attrlist thisFunctionVI.vattr);
*)

            (* makeGlobalVarinfo might have changed the type of the function 
             * (when combining it with the type of the prototype). So get the 
             * type only now. *)

            (**** Process the TYPE and the FORMALS ***)
            let _ = 
              let (returnType, formals_t, isvararg, funta) =
                splitFunctionTypeVI !currentFunctionFDEC.svar 
              in
              (* Record the returnType for doStatement *)
              currentReturnType   := returnType;
              
              
              (* Create the formals and add them to the environment. *)
	      (* sfg: extract locations for the formals from dt *)
	      let doFormal (loc : location) (fn, ft, fa) =
		let f = makeVarinfo false fn ft in
		  (f.vdecl <- loc;
		   f.vattr <- fa;
		   alphaConvertVarAndAddToEnv true f)
	      in
	      let rec doFormals fl' ll' = 
		begin
		  match (fl', ll') with
		    | [], _ -> [] 
			
		    | fl, [] -> (* no more locs available *)
			  List.map (doFormal !currentLoc) fl 
			
		    | f::fl, (_,(_,_,_,l))::ll ->  
			(* sfg: these lets seem to be necessary to
			 *  force the right order of evaluation *)
			let f' = doFormal (convLoc l) f in
			let fl' = doFormals fl ll in
			  f' :: fl'
		end
	      in
	      let fmlocs = (match dt with PROTO(_, fml, _) -> fml | _ -> []) in
	      let formals = doFormals (argsToList formals_t) fmlocs in

              (* Recreate the type based on the formals. *)
              let ftype = TFun(returnType, 
                               Some (List.map (fun f -> (f.vname,
                                                         f.vtype, 
                                                         f.vattr)) formals), 
                               isvararg, funta) in
              (*
              ignore (E.log "Funtype of %s: %a\n" n' d_type ftype);
              *)
              (* Now fix the names of the formals in the type of the function 
              * as well *)
              !currentFunctionFDEC.svar.vtype <- ftype;
              !currentFunctionFDEC.sformals <- formals;
            in
            (* Now change the type of transparent union args back to what it 
             * was so that the body type checks. We must do it this late 
             * because makeGlobalVarinfo from above might choke if we give 
             * the function a type containing transparent unions  *)
            let _ =
              let rec fixbackFormals (idx: int) (args: varinfo list) : unit=
                match args with
                  [] -> ()
                | a :: args' ->
                    (* Fix the type back to a transparent union type *)
                    (try
                      let origtype = List.assq idx !transparentUnionArgs in
                      a.vtype <- origtype;
                    with Not_found -> ());
                    fixbackFormals (idx + 1) args'
              in
              fixbackFormals 0 !currentFunctionFDEC.sformals;
              transparentUnionArgs := [];
            in

            (********** Now do the BODY *************)
            let _ = 
              let stmts = doBody body in
              (* Finish everything *)
              exitScope ();

              (* Now fill in the computed goto statement with cases. Do this 
               * before mkFunctionbody which resolves the gotos *)
              (match !gotoTargetData with
                Some (switchv, switch) ->
                  let switche, l =
                    match switch.skind with
                      Switch (switche, _, _, l) -> switche, l
                    | _ -> E.s(bug "the computed goto statement not a switch")
                  in
                  (* Build a default chunk that segfaults *)
                  let default =
                    defaultChunk
                      l
                      (i2c (Set ((Mem (mkCast (integer 0) intPtrType),
                                  NoOffset),
                                 integer 0, l)))
                  in
                  let bodychunk = ref default in
                  H.iter (fun lname laddr ->
                    bodychunk :=
                       caseRangeChunk
                         [integer laddr] l
                         (gotoChunk lname l @@ !bodychunk))
                    gotoTargetHash;
                  (* Now recreate the switch *)
                  let newswitch = switchChunk switche !bodychunk l in
                  (* We must still share the old switch statement since we
                  * have already inserted the goto's *)
                  let newswitchkind =
                    match newswitch.stmts with
                      [ s]
                        when newswitch.postins == [] && newswitch.cases == []->
                          s.skind
                    | _ -> E.s (bug "Unexpected result from switchChunk")
                  in
                  switch.skind <- newswitchkind
                     
              | None -> ());
              (* Now finish the body and store it *)
              !currentFunctionFDEC.sbody <- mkFunctionBody stmts;
              (* Reset the global parameters *)
              gotoTargetData := None;
              H.clear gotoTargetHash;
              gotoTargetNextAddr := 0;
            in
            

	     
(*
              ignore (E.log "endFunction %s at %t:@! sformals=%a@!  slocals=%a@!"
              !currentFunctionFDEC.svar.vname d_thisloc
              (docList ~sep:(chr ',') (fun v -> text v.vname)) 
              !currentFunctionFDEC.sformals
              (docList ~sep:(chr ',') (fun v -> text v.vname)) 
              !currentFunctionFDEC.slocals);
*)

            let rec dropFormals formals locals = 
              match formals, locals with
                [], l -> l
              | f :: formals, l :: locals -> 
                  if f != l then 
                    E.s (bug "formal %s is not in locals (found instead %s)" 
                           f.vname l.vname);
                  dropFormals formals locals
              | _ -> E.s (bug "Too few locals")
            in
            !currentFunctionFDEC.slocals 
              <- dropFormals !currentFunctionFDEC.sformals 
                   (List.rev !currentFunctionFDEC.slocals);
            setMaxId !currentFunctionFDEC;
 
            (* Now go over the types of the formals and pull out the formals 
             * with transparent union type. Replace them with some shadow 
             * parameters and then add assignments  *)
            let _ = 
              let newformals, newbody =
                List.fold_right (* So that the formals come out in order *)
                  (fun f (accform, accbody) ->
                    match isTransparentUnion f.vtype with
                      None -> (f :: accform, accbody)
                    | Some fstfield ->
                        (* A new shadow to be placed in the formals. Use 
                         * makeTempVar to update smaxid and all others. *)
                        let shadow = 
                          makeTempVar !currentFunctionFDEC fstfield.ftype in
                        (* Now take it out of the locals and replace it with 
                        * the current formal. It is not worth optimizing this 
                        * one.  *)
                        !currentFunctionFDEC.slocals <-
                           f ::
                           (List.filter (fun x -> x.vid <> shadow.vid)
                              !currentFunctionFDEC.slocals);
                        (shadow :: accform,
                         mkStmt (Instr [Set ((Var f, Field(fstfield,
                                                           NoOffset)),
                                             Lval (var shadow),
                                             !currentLoc)]) :: accbody))
                  !currentFunctionFDEC.sformals
                  ([], !currentFunctionFDEC.sbody.bstmts)
              in
              !currentFunctionFDEC.sbody.bstmts <- newbody;
              (* To make sure sharing with the type is proper *)
              setFormals !currentFunctionFDEC newformals; 
            in

            (* Now see whether we can fall through to the end of the function 
             * *)
            (* weimer: Sat Dec 8 17:30:47 2001 MSVC NT kernel headers include 
             * functions like long convert(x) { __asm { mov eax, x \n cdq } } 
             * That set a return value via an ASM statement. As a result, I 
             * am changing this so a final ASM statement does not count as 
             * "fall through" for the purposes of this warning.  *)
            (* matth: But it's better to assume assembly will fall through,
             * since  most such blocks do.  It's probably better to print an
             * unnecessary warning than to break CIL's invariant that
             * return statements are inserted properly.  *)
            let instrFallsThrough (i : instr) = match i with
              Set _ -> true
            | Call (None, Lval (Var e, NoOffset), _, _) -> 
                (* See if this is exit, or if it has the noreturn attribute *)
                if e.vname = "exit" then false 
                else if hasAttribute "noreturn" e.vattr then false
                else true
            | Call _ -> true
            | Asm _ -> true
            in 
            let rec stmtFallsThrough (s: stmt) : bool = 
              match s.skind with
                Instr(il) -> 
                  List.fold_left (fun acc elt -> 
                                      acc && instrFallsThrough elt) true il
              | Return _ | Break _ | Continue _ -> false
              | Goto _ -> false
              | If (_, b1, b2, _) -> 
                  blockFallsThrough b1 || blockFallsThrough b2
              | Switch (e, b, targets, _) -> 
                   (* See if there is a "default" case *)
                   if not 
                      (List.exists (fun s -> 
                         List.exists (function Default _ -> true | _ -> false)
                                      s.labels)
                                   targets) then begin
(*
                      ignore (E.log "Switch falls through because no default");

*)                      true (* We fall through because there is no default *)
                   end else begin
                      (* We must examine all cases. If any falls through, 
                       * then the switch falls through. *)
                      blockFallsThrough b || blockCanBreak b
                   end
(*
              | Loop (b, _, _, _) -> 
                  (* A loop falls through if it can break. *)
                  blockCanBreak b
*)
	      | While (_, b, _) -> blockCanBreak b
	      | DoWhile (_, b, _) -> blockCanBreak b
	      | For (_, _, _, b, _) -> blockCanBreak b
              | Block b -> blockFallsThrough b
              | TryFinally (b, h, _) -> blockFallsThrough h
              | TryExcept (b, _, h, _) -> true (* Conservative *)
            and blockFallsThrough b = 
              let rec fall = function
                  [] -> true
                | s :: rest -> 
                    if stmtFallsThrough s then begin
(*
                        ignore (E.log "Stmt %a falls through\n" d_stmt s);
*)
                        fall rest
                    end else begin
(*
                        ignore (E.log "Stmt %a DOES NOT fall through\n"
                                      d_stmt s);
*)
                      (* If we are not falling thorough then maybe there 
                      * are labels who are *)
                        labels rest
                    end
              and labels = function
                  [] -> false
                    (* We have a label, perhaps we can jump here *)
                  | s :: rest when s.labels <> [] -> 
(*
                     ignore (E.log "invoking fall %a: %a\n" 
                                      d_loc !currentLoc d_stmt s);
*)
                     fall (s :: rest)
                  | _ :: rest -> labels rest
              in
              let res = fall b.bstmts in
(*
              ignore (E.log "blockFallsThrough=%b %a\n" res d_block b);
*)
              res
            (* will we leave this statement or block with a break command? *)
            and stmtCanBreak (s: stmt) : bool = 
              match s.skind with
                Instr _ | Return _ | Continue _ | Goto _ -> false
              | Break _ -> true
              | If (_, b1, b2, _) -> 
                  blockCanBreak b1 || blockCanBreak b2
              | Switch _ | (*Loop _*) While _ | DoWhile _ | For _ -> 
                  (* switches and loops catch any breaks in their bodies *)
                  false
              | Block b -> blockCanBreak b
              | TryFinally (b, h, _) -> blockCanBreak b || blockCanBreak h
              | TryExcept (b, _, h, _) -> blockCanBreak b || blockCanBreak h
            and blockCanBreak b = 
              List.exists stmtCanBreak b.bstmts
            in
            if blockFallsThrough !currentFunctionFDEC.sbody then begin
(*
              let retval = 
                match unrollType !currentReturnType with
                  TVoid _ -> None
                | (TInt _ | TEnum _ | TFloat _ | TPtr _) as rt -> 
                    ignore (warn "Body of function %s falls-through. Adding a return statement\n"  !currentFunctionFDEC.svar.vname);
                    Some (mkCastT zero intType rt)
                | _ ->
                    ignore (warn "Body of function %s falls-through and cannot find an appropriate return value\n" !currentFunctionFDEC.svar.vname);
                    None
              in
              if not (hasAttribute "noreturn" 
                        !currentFunctionFDEC.svar.vattr) then 
                !currentFunctionFDEC.sbody.bstmts <- 
                  !currentFunctionFDEC.sbody.bstmts 
                  @ [mkStmt (Return(retval, endloc))]
*)
            end;
            
            (* ignore (E.log "The env after finishing the body of %s:\n%t\n"
                        n docEnv); *)
            cabsPushGlobal (GFun (!currentFunctionFDEC, funloc));
            empty
          with E.Error as e -> raise e
             | e -> begin
            ignore (E.log "error in collectFunction %s: %s\n"
                      n (Printexc.to_string e));
            cabsPushGlobal (GAsm("error in function " ^ n, !currentLoc));
            empty
          end)
        () (* argument of E.withContext *)
    end (* FUNDEF *)

  | LINKAGE (n, loc, dl) -> 
      currentLoc := convLoc loc;
      if n <> "C" then 
        ignore (warn "Encountered linkage specification \"%s\"" n);
      if not isglobal then 
        E.s (error "Encountered linkage specification in local scope");
      (* For now drop the linkage on the floor !!! *)
      List.iter 
        (fun d -> 
          let s = doDecl isglobal d in
          if isNotEmpty s then 
            E.s (bug "doDecl returns non-empty statement for global"))
        dl;
      empty

  | _ -> E.s (error "unexpected form of declaration")

and doTypedef ((specs, nl): A.name_group) = 
  try
    (* Do the specifiers exactly once *)
    let bt, sto, inl, attrs = doSpecList (suggestAnonName nl) specs in
    if sto <> NoStorage || inl then
      E.s (error "Storage or inline specifier not allowed in typedef");
    let createTypedef ((n,ndt,a,loc) : A.name) =
      (*    E.s (error "doTypeDef") *)
      try
        let newTyp, tattr =
          doType AttrType bt (A.PARENTYPE(attrs, ndt, a))  in
        let newTyp' = cabsTypeAddAttributes tattr newTyp in
        (* Create a new name for the type. Use the same name space as that of 
        * variables to avoid confusion between variable names and types. This 
        * is actually necessary in some cases.  *)
        let n', _  = newAlphaName true "" n in
        let ti = { tname = n'; ttype = newTyp'; treferenced = false } in
        (* Since we use the same name space, we might later hit a global with 
         * the same name and we would want to change the name of the global. 
         * It is better to change the name of the type instead. So, remember 
         * all types whose names have changed *)              
        H.add typedefs n' ti;              
        let namedTyp = TNamed(ti, []) in
        (* Register the type. register it as local because we might be in a
        * local context  *)
        addLocalToEnv (kindPlusName "type" n) (EnvTyp namedTyp);
        cabsPushGlobal (GType (ti, !currentLoc))
      with E.Error as e -> raise e
         | e -> begin
        ignore (E.log "Error on A.TYPEDEF (%s)\n"
                  (Printexc.to_string e));
        cabsPushGlobal (GAsm ("booo_typedef:" ^ n, !currentLoc))
      end
    in
    List.iter createTypedef nl
  with E.Error as e -> raise e
     | e -> begin    
    ignore (E.log "Error on A.TYPEDEF (%s)\n"
              (Printexc.to_string e));
    let fstname = 
      match nl with
        [] -> "<missing name>"
      | (n, _, _, _) :: _ -> n
    in
    cabsPushGlobal (GAsm ("booo_typedef: " ^ fstname, !currentLoc))
  end

and doOnlyTypedef (specs: A.spec_elem list) : unit = 
  try
    let bt, sto, inl, attrs = doSpecList "" specs in
    if sto <> NoStorage || inl then 
      E.s (error "Storage or inline specifier not allowed in typedef");
    let restyp, nattr = doType AttrType bt (A.PARENTYPE(attrs, 
                                                        A.JUSTBASE, [])) in
    if nattr <> [] then
      ignore (warn "Ignoring identifier attribute");
           (* doSpec will register the type. *)
    (* See if we are defining a composite or enumeration type, and in that 
     * case move the attributes from the defined type into the composite type 
     * *)
    let isadef = 
      List.exists 
        (function 
            A.SpecType(A.Tstruct(_, Some _, _)) -> true
          | A.SpecType(A.Tunion(_, Some _, _)) -> true
          | A.SpecType(A.Tenum(_, Some _, _)) -> true
          | _ -> false) specs
    in
    match restyp with 
      TComp(ci, al) -> 
        if isadef then begin
          ci.cattr <- cabsAddAttributes ci.cattr al; 
          (* The GCompTag was already added *)
        end else (* Add a GCompTagDecl *)
          cabsPushGlobal (GCompTagDecl(ci, !currentLoc))
    | TEnum(ei, al) -> 
        if isadef then begin
          ei.eattr <- cabsAddAttributes ei.eattr al;
        end else
          cabsPushGlobal (GEnumTagDecl(ei, !currentLoc))
    | _ -> 
        ignore (warn "Ignoring un-named typedef that does not introduce a struct or enumeration type\n")
            
  with E.Error as e -> raise e
     | e -> begin
    ignore (E.log "Error on A.ONLYTYPEDEF (%s)\n"
              (Printexc.to_string e));
    cabsPushGlobal (GAsm ("booo_typedef", !currentLoc))
  end

and assignInit (lv: lval) 
               (ie: init) 
               (iet: typ) 
               (acc: chunk) : chunk = 
  match ie with
    SingleInit e -> 
      let (_, e'') = castTo iet (typeOfLval lv) e in 
      acc +++ (Set(lv, e'', !currentLoc))
  | CompoundInit (t, initl) -> 
      foldLeftCompound
        ~doinit:(fun off i it acc -> 
          assignInit (addOffsetLval off lv) i it acc)
        ~ct:t
        ~initl:initl
        ~acc:acc
(*
  | ArrayInit (bt, len, initl) -> 
      let idx = ref ( -1 ) in
      List.fold_left
        (fun acc i -> 
          assignInit (addOffsetLval (Index(integer !idx, NoOffset)) lv) i bt acc)
        acc
        initl
*)
  (* Now define the processors for body and statement *)
and doBody (blk: A.block) : chunk = 
  enterScope ();
  (* Rename the labels and add them to the environment *)
  List.iter (fun l -> ignore (genNewLocalLabel l)) blk.blabels;
  (* See if we have some attributes *)
  let battrs = doAttributes blk.A.battrs in

  let bodychunk = 
    afterConversion
      (List.fold_left   (* !!! @ evaluates its arguments backwards *)
         (fun prev s -> let res = doStatement s in 
                        prev @@ res)
         empty
         blk.A.bstmts)
  in
  exitScope ();


  if battrs == [] then
    bodychunk
  else begin
    let b = c2block bodychunk in
    b.battrs <- battrs;
    s2c (mkStmt (Block b))
  end
      
and doStatement (s : A.statement) : chunk = 
  try
    match s with
      A.NOP _ -> skipChunk
    | A.COMPUTATION (e, loc) ->
        currentLoc := convLoc loc;
        let (lasts, data) = !gnu_body_result in
        if lasts == s then begin      (* This is the last in a GNU_BODY *)
          let (s', e', t') = doExp false e (AExp None) in
          data := Some (e', t');      (* Record the result *)
          s'
        end else
          let (s', _, _) = doExp false e ADrop in
            (* drop the side-effect free expression *)
            (* And now do some peep-hole optimizations *)
          s'

    | A.BLOCK (b, loc) -> 
        currentLoc := convLoc loc;
        doBody b

    | A.SEQUENCE (s1, s2, loc) ->
        (doStatement s1) @@ (doStatement s2)

    | A.IF(e,st,sf,loc) ->
        let st' = doStatement st in
        let sf' = doStatement sf in
        currentLoc := convLoc loc;
        doCondition false e st' sf'

    | A.WHILE(e,s,loc) ->
(*
        startLoop true;
        let s' = doStatement s in
        exitLoop ();
        let loc' = convLoc loc in
        currentLoc := loc';
        loopChunk ((doCondition false e skipChunk
                      (breakChunk loc'))
                   @@ s')
*)
	(** We need to convert A.WHILE(e,s) where e may have side effects
	     into Cil.While(e',s') where e' is side-effect free. *)
	
	(* Let e == (sCond , eCond) with sCond a sequence of statements
	   and eCond a side-effect free expression. *)
	let (sCond, eCond, _) = doExp false e (AExp None) in
	  
	  (* Then doStatement(A.WHILE((sCond , eCond), s))
             = sCond ; Cil.While(eCond, (doStatement(s) ; sCond))
	     where doStatement(A.CONTINUE) = (sCond ; Cil.Continue). *)
	  
          startLoop (DuplicateBeforeContinue sCond);
          let s' = doStatement s in
            exitLoop ();
            let loc' = convLoc loc in
              currentLoc := loc';
              sCond @@ (whileChunk eCond (s' @@ sCond))
          
    | A.DOWHILE(e,s,loc) -> 
(*
        startLoop false;
        let s' = doStatement s in
        let loc' = convLoc loc in
        currentLoc := loc';
        let s'' = 
          consLabContinue (doCondition false e skipChunk (breakChunk loc'))
        in
        exitLoop ();
        loopChunk (s' @@ s'')
*)
	(** We need to convert A.DOWHILE(e,s) where e may have side effects
	     into Cil.DoWhile(e',s') where e' is side-effect free. *)
	
	(* Let e == (sCond , eCond) with sCond a sequence of statements
	   and eCond a side-effect free expression. *)
	let (sCond, eCond, _) = doExp false e (AExp None) in
	  
	  (* Then doStatement(A.DOWHILE((sCond , eCond), s))
             = Cil.DoWhile(eCond, (doStatement(s) ; sCond))
	     where doStatement(A.CONTINUE) = (sCond ; Cil.Continue). *)
	  
          startLoop (DuplicateBeforeContinue sCond);
          let s' = doStatement s in
            exitLoop ();
            let loc' = convLoc loc in
              currentLoc := loc';
              doWhileChunk eCond (s' @@ sCond)
          
    | A.FOR(fc1,e2,e3,s,loc) ->
(*begin
        let loc' = convLoc loc in
        currentLoc := loc';
        enterScope (); (* Just in case we have a declaration *)
        let (se1, _, _) = 
          match fc1 with 
            FC_EXP e1 -> doExp false e1 ADrop 
          | FC_DECL d1 -> (doDecl false d1, zero, voidType)
        in
        let (se3, _, _) = doExp false e3 ADrop in
        startLoop false;
        let s' = doStatement s in
        currentLoc := loc';
        let s'' = consLabContinue se3 in
        exitLoop ();
        let res = 
          match e2 with
            A.NOTHING -> (* This means true *)
              se1 @@ loopChunk (s' @@ s'')
          | _ -> 
              se1 @@ loopChunk ((doCondition false e2 skipChunk (breakChunk loc'))
                                @@ s' @@ s'')
        in
        exitScope ();
        res
    end
*)
	(** We need to convert A.FOR(e1,e2,e3,s) where e1, e2 and e3 may
	     have side effects into Cil.For(bInit,e2',bIter,s') where e2'
	     is side-effect free. **)
	
	(* Let e1 == bInit be a block of statements
	   Let e2 == (bCond , eCond) with bCond a block of statements
	   and eCond a side-effect free expression
	   Let e3 == bIter be a sequence of statements. *)
	let (bInit, _, _) = match fc1 with 
          | FC_EXP e1 -> doExp false e1 ADrop 
          | FC_DECL d1 -> (doDecl false d1, zero, voidType) in
	let (bCond, eCond, _) = doExp false e2 (AExp None) in
	let eCond' = match eCond with
	  | Const(CStr "exp_nothing") -> Cil.one
	  | _                         -> eCond in
	let (bIter, _, _) = doExp false e3 ADrop in
	  
	(* Then doStatement(A.FOR(bInit, (bCond , eCond), bIter, s))
           = Cil.For({bInit; bCond}, eCond', {bIter; bCond}, {doStatement(s)})
	   where doStatement(A.CONTINUE) = Cil.Continue. *)
	  
	  startLoop ContinueUnchanged;
          let s' = doStatement s in
            exitLoop ();
            let loc' = convLoc loc in
              currentLoc := loc';
              (forChunk (bInit @@ bCond) eCond' (bIter @@ bCond) s')

    | A.BREAK loc -> 
        let loc' = convLoc loc in
        currentLoc := loc';
        breakChunk loc'

    | A.CONTINUE loc -> 
        let loc' = convLoc loc in
        currentLoc := loc';
(*
        continueOrLabelChunk loc'
*)
	continueDuplicateChunk loc'

    | A.RETURN (A.NOTHING, loc) -> 
        let loc' = convLoc loc in
        currentLoc := loc';
        if not (isVoidType !currentReturnType) then
          ignore (warn "Return statement without a value in function returning %a\n" d_type !currentReturnType);
        returnChunk None loc'

    | A.RETURN (e, loc) ->
        let loc' = convLoc loc in
        currentLoc := loc';
        (* Sometimes we return the result of a void function call *)
        if isVoidType !currentReturnType then begin
          ignore (warn "Return statement with a value in function returning void");
          let (se, _, _) = doExp false e ADrop in
          se @@ returnChunk None loc'
        end else begin
          let (se, e', et) = 
            doExp false e (AExp (Some !currentReturnType)) in
          let (et'', e'') = castTo et (!currentReturnType) e' in
          se @@ (returnChunk (Some e'') loc')
        end
               
    | A.SWITCH (e, s, loc) -> 
        let loc' = convLoc loc in
        currentLoc := loc';
        let (se, e', et) = doExp false e (AExp (Some intType)) in
        let (et'', e'') = castTo et intType e' in
        let s' = doStatement s in
        se @@ (switchChunk e'' s' loc')
               
    | A.CASE (e, s, loc) -> 
        let loc' = convLoc loc in
        currentLoc := loc';
        let (se, e', et) = doExp true e (AExp None) in
        if isNotEmpty se then
          E.s (error "Case statement with a non-constant");
        caseRangeChunk [if !lowerConstants then constFold false e' else e'] 
          loc' (doStatement s)
            
    | A.CASERANGE (el, eh, s, loc) -> 
        let loc' = convLoc loc in
        currentLoc := loc';
        let (sel, el', etl) = doExp false el (AExp None) in
        let (seh, eh', etl) = doExp false eh (AExp None) in
        if isNotEmpty sel || isNotEmpty seh then
          E.s (error "Case statement with a non-constant");
        let il, ih = 
          match constFold true el', constFold true eh' with
            Const(CInt64(il, _, _)), Const(CInt64(ih, _, _)) -> 
              Int64.to_int il, Int64.to_int ih
          | _ -> E.s (unimp "Cannot understand the constants in case range")
        in
        if il > ih then 
          E.s (error "Empty case range");
        let rec mkAll (i: int) = 
          if i > ih then [] else integer i :: mkAll (i + 1)
        in
        caseRangeChunk (mkAll il) loc' (doStatement s)
        

    | A.DEFAULT (s, loc) -> 
        let loc' = convLoc loc in
        currentLoc := loc';
        defaultChunk loc' (doStatement s)
                     
    | A.LABEL (l, s, loc) -> 
        let loc' = convLoc loc in
        currentLoc := loc';
        (* Lookup the label because it might have been locally defined *)
        consLabel (lookupLabel l) (doStatement s) loc' true
                     
    | A.GOTO (l, loc) -> 
        let loc' = convLoc loc in
        currentLoc := loc';
        (* Maybe we need to rename this label *)
        gotoChunk (lookupLabel l) loc'

    | A.COMPGOTO (e, loc) -> begin
        let loc' = convLoc loc in
        currentLoc := loc';
        (* Do the expression *)
        let se, e', t' = doExp false e (AExp (Some voidPtrType)) in
        match !gotoTargetData with
          Some (switchv, switch) -> (* We have already generated this one  *)
            se 
            @@ i2c(Set (var switchv, mkCast e' uintType, loc'))
            @@ s2c(mkStmt(Goto (ref switch, loc')))

        | None -> begin
            (* Make a temporary variable *)
            let vchunk = createLocal 
                (TInt(IUInt, []), NoStorage, false, [])
                (("__compgoto", A.JUSTBASE, [], loc), A.NO_INIT) 
            in
            if not (isEmpty vchunk) then 
              E.s (unimp "Non-empty chunk in creating temporary for goto *");
            let switchv, _ = 
              try lookupVar "__compgoto" 
              with Not_found -> E.s (bug "Cannot find temporary for goto *");
            in
            (* Make a switch statement. We'll fill in the statements at the 
            * end of the function *)
            let switch = mkStmt (Switch (Lval(var switchv), 
                                         mkBlock [], [], loc')) in
            (* And make a label for it since we'll goto it *)
            switch.labels <- [Label ("__docompgoto", loc', false)];
            gotoTargetData := Some (switchv, switch);
            se @@ i2c (Set(var switchv, mkCast e' uintType, loc')) @@
            s2c switch
        end
      end

    | A.DEFINITION d ->
        let s = doDecl false d  in 
(*
        ignore (E.log "Def at %a: %a\n" d_loc !currentLoc d_chunk s);
*)
        s



    | A.ASM (asmattr, tmpls, details, loc) -> 
        (* Make sure all the outs are variables *)
        let loc' = convLoc loc in
        let attr' = doAttributes asmattr in
        currentLoc := loc';
        let stmts : chunk ref = ref empty in
	let (tmpls', outs', ins', clobs') =
	  match details with
	  | None ->
	      let tmpls' =
		if !msvcMode then
		  tmpls
		else
		  let pattern = Str.regexp "%" in
		  let escape = Str.global_replace pattern "%%" in
		  List.map escape tmpls
	      in
	      (tmpls', [], [], [])
	  | Some { aoutputs = outs; ainputs = ins; aclobbers = clobs } ->
              let outs' =
		List.map
		  (fun (c, e) ->
		    let (se, e', t) = doExp false e (AExp None) in
		    let lv =
                      match e' with
		      | Lval lval
		      | StartOf lval -> lval
                      | _ -> E.s (error "Expected lval for ASM outputs")
		    in
		    stmts := !stmts @@ se;
		    (c, lv)) outs
              in
	      (* Get the side-effects out of expressions *)
              let ins' =
		List.map
		  (fun (c, e) ->
		    let (se, e', et) = doExp false e (AExp None) in
		    stmts := !stmts @@ se;
		    (c, e'))
		  ins
              in
	      (tmpls, outs', ins', clobs)
	in
        !stmts @@
        (i2c (Asm(attr', tmpls', outs', ins', clobs', loc')))

    | TRY_FINALLY (b, h, loc) -> 
        let loc' = convLoc loc in
        currentLoc := loc';
        let b': chunk = doBody b in
        let h': chunk = doBody h in
        if b'.cases <> [] || h'.cases <> [] then 
          E.s (error "Try statements cannot contain switch cases");
        
        s2c (mkStmt (TryFinally (c2block b', c2block h', loc')))
        
    | TRY_EXCEPT (b, e, h, loc) -> 
        let loc' = convLoc loc in
        currentLoc := loc';
        let b': chunk = doBody b in
        (* Now do e *)
        let ((se: chunk), e', t') = doExp false e (AExp None) in
        let h': chunk = doBody h in
        if b'.cases <> [] || h'.cases <> [] || se.cases <> [] then 
          E.s (error "Try statements cannot contain switch cases");
        (* Now take se and try to convert it to a list of instructions. This 
         * might not be always possible *)
        let il' = 
          match compactStmts se.stmts with 
            [] -> se.postins
          | [ s ] -> begin
              match s.skind with 
                Instr il -> il @ se.postins
              | _ -> E.s (error "Except expression contains unexpected statement")
            end
          | _ -> E.s (error "Except expression contains too many statements")
        in
        s2c (mkStmt (TryExcept (c2block b', (il', e'), c2block h', loc')))

  with e -> begin
    (ignore (E.log "Error in doStatement (%s)\n" (Printexc.to_string e)));
    consLabel "booo_statement" empty (convLoc (A.get_statementloc s)) false
  end


(* Translate a file *)
let convFile ((fname : string), (dl : Cabs.definition list)) : Cil.file =
  Cil.initCIL (); (* make sure we have initialized CIL *)
  (* Clean up the global types *)
  E.hadErrors := false;
  initGlobals();
  startFile ();
  IH.clear noProtoFunctions;
  H.clear compInfoNameEnv;
  H.clear enumInfoNameEnv;
  IH.clear mustTurnIntoDef;
  H.clear alreadyDefined;
  H.clear staticLocals;
  H.clear typedefs;                      
  H.clear isomorphicStructs;
  annonCompFieldNameId := 0;
  if !E.verboseFlag || !Cilutil.printStages then 
    ignore (E.log "Converting CABS->CIL\n");
  (* Setup the built-ins, but do not add their prototypes to the file *)
  let setupBuiltin name (resTyp, argTypes, isva) = 
    let v = 
      makeGlobalVar name (TFun(resTyp, 
                               Some (List.map (fun at -> ("", at, [])) 
                                       argTypes),
                               isva, [])) in
    ignore (alphaConvertVarAndAddToEnv true v)
  in
  H.iter setupBuiltin (if !msvcMode then msvcBuiltins else gccBuiltins);

  let globalidx = ref 0 in
  let doOneGlobal (d: A.definition) = 
    let s = doDecl true d in
    if isNotEmpty s then 
      E.s (bug "doDecl returns non-empty statement for global");
    (* See if this is one of the globals which we can leave alone. Increment 
     * globalidx and see if we must leave this alone. *)
    if 
      (match d with 
        A.DECDEF _ -> true
      | A.FUNDEF _ -> true
      | _ -> false) && (incr globalidx; !globalidx = !nocil) then begin
          (* Create a file where we put the CABS output *)
          let temp_cabs_name = "__temp_cabs" in
          let temp_cabs = open_out temp_cabs_name in
          (* Now print the CABS in there *)
          Cprint.commit (); Cprint.flush ();
          let old = !Cprint.out in (* Save the old output channel *)
          Cprint.out := temp_cabs;
          Cprint.print_def d;
          Cprint.commit (); Cprint.flush ();
          flush !Cprint.out;
          Cprint.out := old;
          close_out temp_cabs;
          (* Now read everythign in *and create a GText from it *)
          let temp_cabs = open_in temp_cabs_name in
          let buff = Buffer.create 1024 in
          Buffer.add_string buff "// Start of CABS form\n";
          Buffer.add_channel buff temp_cabs (in_channel_length temp_cabs);
          Buffer.add_string buff "// End of CABS form\n";
          close_in temp_cabs;
          (* Try to pop the last thing in the file *)
          (match !theFile with 
            _ :: rest -> theFile := rest
          | _ -> ());
          (* Insert in the file a GText *)
          cabsPushGlobal (GText(Buffer.contents buff))
    end 
  in
  List.iter doOneGlobal dl;
  let globals = ref (popGlobals ()) in

  IH.clear noProtoFunctions;
  IH.clear mustTurnIntoDef;  
  H.clear alreadyDefined;
  H.clear compInfoNameEnv;
  H.clear enumInfoNameEnv;
  H.clear isomorphicStructs;
  H.clear staticLocals;
  H.clear typedefs;
  H.clear env;
  H.clear genv;
  IH.clear callTempVars;

  if false then ignore (E.log "Cabs2cil converted %d globals\n" !globalidx);
  (* We are done *)
  { fileName = fname;
    globals  = !globals;
    globinit = None;
    globinitcalled = false;
  } 


    
                      
