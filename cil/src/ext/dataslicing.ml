(* MODIF: Loop constructor replaced by 3 constructors: While, DoWhile, For. *)

(*
 *
 * Copyright (c) 2004, 
 *  Jeremy Condit       <jcondit@cs.berkeley.edu>
 *  George C. Necula    <necula@cs.berkeley.edu>
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
open Cil
open Pretty
module E = Errormsg

let debug = false

let numRegions : int = 2

let newGlobals : global list ref = ref []

let curFundec : fundec ref = ref dummyFunDec
let curLocation : location ref = ref locUnknown

let applyOption (fn : 'a -> 'b) (ao : 'a option) : 'b option =
  match ao with
  | Some a -> Some (fn a)
  | None -> None

let getRegion (attrs : attributes) : int =
  try
    match List.hd (filterAttributes "region" attrs) with
    | Attr (_, [AInt i]) -> i
    | _ -> E.s (bug "bad region attribute")
  with Failure _ ->
    1

let checkRegion (i : int) (attrs : attributes) : bool =
  (getRegion attrs) = i

let regionField (i : int) : string =
  "r" ^ (string_of_int i)

let regionStruct (i : int) (name : string) : string =
  name ^ "_r" ^ (string_of_int i)

let foldRegions (fn : int -> 'a -> 'a) (base : 'a) : 'a =
  let rec helper (i : int) : 'a =
    if i <= numRegions then
      fn i (helper (i + 1))
    else
      base
  in
  helper 1

let rec getTypeName (t : typ) : string =
  match t with
  | TVoid _ -> "void"
  | TInt _ -> "int"
  | TFloat _ -> "float"
  | TComp (cinfo, _) -> "comp_" ^ cinfo.cname
  | TNamed (tinfo, _) -> "td_" ^ tinfo.tname
  | TPtr (bt, _) -> "ptr_" ^ (getTypeName bt)
  | TArray (bt, _, _) -> "array_" ^ (getTypeName bt)
  | TFun _ -> "fn"
  | _ -> E.s (unimp "typename")

let isAllocFunction (fn : exp) : bool =
  match fn with
  | Lval (Var vinfo, NoOffset) when vinfo.vname = "malloc" -> true
  | _ -> false

let isExternalFunction (fn : exp) : bool =
  match fn with
  | Lval (Var vinfo, NoOffset) when vinfo.vstorage = Extern -> true
  | _ -> false

let types : (int * typsig, typ) Hashtbl.t = Hashtbl.create 113
let typeInfos : (int * string, typeinfo) Hashtbl.t = Hashtbl.create 113
let compInfos : (int * int, compinfo) Hashtbl.t = Hashtbl.create 113
let varTypes : (typsig, typ) Hashtbl.t = Hashtbl.create 113
let varCompInfos : (typsig, compinfo) Hashtbl.t = Hashtbl.create 113

let rec sliceCompInfo (i : int) (cinfo : compinfo) : compinfo =
  try
    Hashtbl.find compInfos (i, cinfo.ckey)
  with Not_found ->
    mkCompInfo cinfo.cstruct (regionStruct i cinfo.cname)
      (fun cinfo' -> 
         Hashtbl.add compInfos (i, cinfo.ckey) cinfo';
         List.fold_right
           (fun finfo rest ->
              let t = sliceType i finfo.ftype in
              if not (isVoidType t) then
                (finfo.fname, t, finfo.fbitfield,
                 finfo.fattr, finfo.floc) :: rest
              else
                rest)
           cinfo.cfields [])
      cinfo.cattr

and sliceTypeInfo (i : int) (tinfo : typeinfo) : typeinfo =
  try
    Hashtbl.find typeInfos (i, tinfo.tname)
  with Not_found ->
    let result =
      { tinfo with tname = regionStruct i tinfo.tname;
                   ttype = sliceType i tinfo.ttype; }
    in
    Hashtbl.add typeInfos (i, tinfo.tname) result;
    result

and sliceType (i : int) (t : typ) : typ =
  let ts = typeSig t in
  try
    Hashtbl.find types (i, ts)
  with Not_found ->
    let result =
      match t with
      | TVoid _ -> t
      | TInt (_, attrs) -> if checkRegion i attrs then t else TVoid []
      | TFloat (_, attrs) -> if checkRegion i attrs then t else TVoid []
      | TComp (cinfo, attrs) -> TComp (sliceCompInfo i cinfo, attrs)
      | TNamed (tinfo, attrs) -> TNamed (sliceTypeInfo i tinfo, attrs)
      | TPtr (TVoid _, _) -> t (* Avoid discarding void*. *)
      | TPtr (bt, attrs) ->
          let bt' = sliceType i bt in
          if not (isVoidType bt') then TPtr (bt', attrs) else TVoid []
      | TArray (bt, eo, attrs) ->
          TArray (sliceType i bt, applyOption (sliceExp 1) eo, attrs)
      | TFun (ret, args, va, attrs) ->
          if checkRegion i attrs then
            TFun (sliceTypeAll ret,
                  applyOption
                    (List.map (fun (aname, atype, aattrs) ->
                               (aname, sliceTypeAll atype, aattrs)))
                    args,
                  va, attrs)
          else
            TVoid []
      | TBuiltin_va_list _ -> t
      | _ -> E.s (unimp "type %a" d_type t)
    in
    Hashtbl.add types (i, ts) result;
    result

and sliceTypeAll (t : typ) : typ =
  begin
  match t with
  | TComp (cinfo, _) when hasAttribute "var_type_sliced" cinfo.cattr ->
      E.s (bug "tried to slice twice")
  | _ -> ()
  end;
  let ts = typeSig t in
  try
    Hashtbl.find varTypes ts
  with Not_found ->
    let cinfo =
      let name = ("var_" ^ (getTypeName t)) in
      if debug then ignore (E.log "creating %s\n" name);
      try
        Hashtbl.find varCompInfos ts
      with Not_found ->
        mkCompInfo true name
          (fun cinfo ->
             Hashtbl.add varCompInfos ts cinfo;
             foldRegions
               (fun i rest ->
                  let t' = sliceType i t in
                  if not (isVoidType t') then
                    (regionField i, t', None, [], !curLocation) :: rest
                  else
                    rest)
             [])
          [Attr ("var_type_sliced", [])]
    in
    let t' =
      if List.length cinfo.cfields > 1 then
        begin
        newGlobals := GCompTag (cinfo, !curLocation) :: !newGlobals;
        TComp (cinfo, [])
        end
      else
        t
    in
    Hashtbl.add varTypes ts t';
    t'

and sliceLval (i : int) (lv : lval) : lval =
  if debug then ignore (E.log "lval %a\n" d_lval lv);
  let lh, offset = lv in
  match lh with
  | Var vinfo ->
      let t = sliceTypeAll vinfo.vtype in
      let offset' =
        match t with
        | TComp (cinfo, _) when hasAttribute "var_type_sliced" cinfo.cattr ->
            Field (getCompField cinfo (regionField i), offset)
        | _ -> offset
      in
      Var vinfo, offset'
  | Mem e ->
      Mem (sliceExp i e), offset

and sliceExp (i : int) (e : exp) : exp =
  if debug then ignore (E.log "exp %a\n" d_exp e);
  match e with
  | Const c -> Const c
  | Lval lv -> Lval (sliceLval i lv)
  | UnOp (op, e1, t) -> UnOp (op, sliceExp i e1, sliceType i t)
  | BinOp (op, e1, e2, t) -> BinOp (op, sliceExp i e1, sliceExp i e2,
                                    sliceType i t)
  | CastE (t, e) -> sliceCast i t e
  | AddrOf lv -> AddrOf (sliceLval i lv)
  | StartOf lv -> StartOf (sliceLval i lv)
  | SizeOf t -> SizeOf (sliceTypeAll t)
  | _ -> E.s (unimp "exp %a" d_exp e)

and sliceCast (i : int) (t : typ) (e : exp) : exp =
  let te = typeOf e in
  match t, te with
  | TInt (k1, _), TInt (k2, attrs2) when k1 = k2 ->
      (* Note: We strip off integer cast operations. *)
      sliceExp (getRegion attrs2) e
  | TInt (k1, _), TPtr _ ->
      (* Note: We strip off integer cast operations. *)
      sliceExp i e
  | TPtr _, _ when isZero e ->
      CastE (sliceType i t, sliceExp i e)
  | TPtr (bt1, _), TPtr (bt2, _) when (typeSig bt1) = (typeSig bt2) ->
      CastE (sliceType i t, sliceExp i e)
  | _ ->
      E.s (unimp "sketchy cast (%a) -> (%a)\n" d_type te d_type t)

and sliceExpAll (e : exp) (l : location) : instr list * exp =
  let t = typeOf e in
  let t' = sliceTypeAll t in
  match t' with
  | TComp (cinfo, _) when hasAttribute "var_type_sliced" cinfo.cattr ->
      let vinfo = makeTempVar !curFundec t in
      let instrs =
        foldRegions
          (fun i rest ->
             try
               let finfo = getCompField cinfo (regionField i) in
               if not (isVoidType finfo.ftype) then
                 Set ((Var vinfo, Field (finfo, NoOffset)),
                      sliceExp i e, l) :: rest
               else
                 rest
             with Not_found ->
               rest)
          []
      in
      instrs, Lval (var vinfo)
  | _ -> [], sliceExp 1 e

let sliceVar (vinfo : varinfo) : unit =
  if hasAttribute "var_sliced" vinfo.vattr then
    E.s (bug "tried to slice a var twice");
  let t = sliceTypeAll vinfo.vtype in
  if debug then ignore (E.log "setting %s type to %a\n" vinfo.vname d_type t);
  vinfo.vattr <- addAttribute (Attr ("var_sliced", [])) vinfo.vattr;
  vinfo.vtype <- t

let sliceInstr (inst : instr) : instr list =
  match inst with
  | Set (lv, e, loc) ->
      if debug then ignore (E.log "set %a %a\n" d_lval lv d_exp e);
      let t = typeOfLval lv in
      foldRegions
        (fun i rest ->
           if not (isVoidType (sliceType i t)) then
             Set (sliceLval i lv, sliceExp i e, loc) :: rest
           else
             rest)
        []
  | Call (ret, fn, args, l) when isAllocFunction fn ->
      let lv =
        match ret with
        | Some lv -> lv
        | None -> E.s (bug "malloc call has no return lval")
      in
      let t = typeOfLval lv in
      foldRegions
        (fun i rest ->
           if not (isVoidType (sliceType i t)) then
             Call (Some (sliceLval i lv), sliceExp 1 fn,
                   List.map (sliceExp i) args, l) :: rest
           else
             rest)
        []
  | Call (ret, fn, args, l) when isExternalFunction fn ->
      [Call (applyOption (sliceLval 1) ret, sliceExp 1 fn,
             List.map (sliceExp 1) args, l)]
  | Call (ret, fn, args, l) ->
      let ret', set =
        match ret with
        | Some lv ->
            let vinfo = makeTempVar !curFundec (typeOfLval lv) in
            Some (var vinfo), [Set (lv, Lval (var vinfo), l)]
        | None ->
            None, []
      in
      let instrs, args' =
        List.fold_right
          (fun arg (restInstrs, restArgs) ->
             let instrs, arg' = sliceExpAll arg l in
             instrs @ restInstrs, (arg' :: restArgs))
          args ([], [])
      in
      instrs @ (Call (ret', sliceExp 1 fn, args', l) :: set)
  | _ -> E.s (unimp "inst %a" d_instr inst)

let sliceReturnExp (eo : exp option) (l : location) : stmtkind =
  match eo with
  | Some e ->
      begin
      match sliceExpAll e l with
      | [], e' -> Return (Some e', l)
      | instrs, e' -> Block (mkBlock [mkStmt (Instr instrs);
                                      mkStmt (Return (Some e', l))])
      end
  | None -> Return (None, l)

let rec sliceStmtKind (sk : stmtkind) : stmtkind =
  match sk with
  | Instr instrs -> Instr (List.flatten (List.map sliceInstr instrs))
  | Block b -> Block (sliceBlock b)
  | If (e, b1, b2, l) -> If (sliceExp 1 e, sliceBlock b1, sliceBlock b2, l)
  | Break l -> Break l
  | Continue l -> Continue l
  | Return (eo, l) -> sliceReturnExp eo l
  | Switch (e, b, sl, l) -> Switch (sliceExp 1 e, sliceBlock b,
                                    List.map sliceStmt sl, l)
(*
  | Loop (b, l, so1, so2) -> Loop (sliceBlock b, l,
                                   applyOption sliceStmt so1,
                                   applyOption sliceStmt so2)
*)
  | While (e, b, l) -> While (sliceExp 1 e, sliceBlock b, l)
  | DoWhile (e, b, l) -> DoWhile (sliceExp 1 e, sliceBlock b, l)
  | For (bInit, e, bIter, b, l) ->
	For (sliceBlock bInit, sliceExp 1e, sliceBlock bIter, sliceBlock b, l)
  | Goto _ -> sk
  | _ -> E.s (unimp "statement")

and sliceStmt (s : stmt) : stmt =
  (* Note: We update statements destructively so that goto/switch work. *)
  s.skind <- sliceStmtKind s.skind;
  s

and sliceBlock (b : block) : block =
  ignore (List.map sliceStmt b.bstmts);
  b

let sliceFundec (fd : fundec) (l : location) : unit =
  curFundec := fd;
  curLocation := l;
  ignore (sliceBlock fd.sbody);
  curFundec := dummyFunDec;
  curLocation := locUnknown

let sliceGlobal (g : global) : unit =
  match g with
  | GType (tinfo, l) ->
      newGlobals :=
        foldRegions (fun i rest -> GType (sliceTypeInfo i tinfo, l) :: rest)
                    !newGlobals
  | GCompTag (cinfo, l) ->
      newGlobals :=
        foldRegions (fun i rest -> GCompTag (sliceCompInfo i cinfo, l) :: rest)
                    !newGlobals
  | GCompTagDecl (cinfo, l) ->
      newGlobals :=
        foldRegions (fun i rest -> GCompTagDecl (sliceCompInfo i cinfo, l) ::
                                   rest)
                    !newGlobals
  | GFun (fd, l) ->
      sliceFundec fd l;
      newGlobals := GFun (fd, l) :: !newGlobals
  | GVarDecl _
  | GVar _ ->
      (* Defer processing of vars until end. *)
      newGlobals := g :: !newGlobals
  | _ ->
      E.s (unimp "global %a\n" d_global g)

let sliceGlobalVars (g : global) : unit =
  match g with
  | GFun (fd, l) ->
      curFundec := fd;
      curLocation := l;
      List.iter sliceVar fd.slocals;
      List.iter sliceVar fd.sformals;
      setFunctionType fd (sliceType 1 fd.svar.vtype);
      curFundec := dummyFunDec;
      curLocation := locUnknown;
  | GVar (vinfo, _, l) ->
      curLocation := l;
      sliceVar vinfo;
      curLocation := locUnknown
  | _ -> ()

class dropAttrsVisitor = object
  inherit nopCilVisitor

  method vvrbl (vinfo : varinfo) =
    vinfo.vattr <- dropAttribute "var_sliced" vinfo.vattr;
    DoChildren

  method vglob (g : global) =
    begin
    match g with
    | GCompTag (cinfo, _) ->
        cinfo.cattr <- dropAttribute "var_type_sliced" cinfo.cattr;
    | _ -> ()
    end;
    DoChildren
end

let sliceFile (f : file) : unit =
  newGlobals := [];
  List.iter sliceGlobal f.globals;
  List.iter sliceGlobalVars f.globals;
  f.globals <- List.rev !newGlobals;
  visitCilFile (new dropAttrsVisitor) f

let feature : featureDescr = 
  { fd_name = "DataSlicing";
    fd_enabled = ref false;
    fd_description = "data slicing";
    fd_extraopt = [];
    fd_doit = sliceFile;
    fd_post_check = true;
  } 
