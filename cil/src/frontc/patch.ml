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


(* patch.ml *)
(* CABS file patching *)

open Cabs
open Trace
open Pretty
open Cabsvisit

(* binding of a unification variable to a syntactic construct *)
type binding =
  | BSpecifier of string * spec_elem list
  | BName of string * string
  | BExpr of string * expression

(* thrown when unification fails *)
exception NoMatch

(* thrown when an attempt to find the associated binding fails *)
exception BadBind of string

(* trying to isolate performance problems; will hide all the *)
(* potentially expensive debugging output behind "if verbose .." *)
let verbose : bool = true


(* raise NoMatch if x and y are not equal *)
let mustEq (x : 'a) (y : 'a) : unit =
begin
  if (x <> y) then (
    if verbose then
      (trace "patchDebug" (dprintf "mismatch by structural disequality\n"));
    raise NoMatch
  )
end

(* why isn't this in the core Ocaml library? *)
let identity x = x


let isPatternVar (s : string) : bool =
begin
  ((String.length s) >= 1) && ((String.get s 0) = '@')
end

(* 's' is actually "@name(blah)"; extract the 'blah' *)
let extractPatternVar (s : string) : string =
  (*(trace "patch" (dprintf "extractPatternVar %s\n" s));*)
  (String.sub s 6 ((String.length s) - 7))


(* a few debugging printers.. *)
let printExpr (e : expression) =
begin
  if (verbose && traceActive "patchDebug") then (
    Cprint.print_expression e; Cprint.force_new_line ();
    Cprint.flush ()
  )
end

let printSpec (spec: spec_elem list) =
begin
  if (verbose && traceActive "patchDebug") then (
    Cprint.print_specifiers spec;  Cprint.force_new_line ();
    Cprint.flush ()
  )
end

let printSpecs (pat : spec_elem list) (tgt : spec_elem list) =
begin
  (printSpec pat);
  (printSpec tgt)
end

let printDecl (pat : name) (tgt : name) =
begin
  if (verbose && traceActive "patchDebug") then (
    Cprint.print_name pat;  Cprint.force_new_line ();
    Cprint.print_name tgt;  Cprint.force_new_line ();
    Cprint.flush ()
  )
end

let printDeclType (pat : decl_type) (tgt : decl_type) =
begin
  if (verbose && traceActive "patchDebug") then (
    Cprint.print_decl "__missing_field_name" pat;  Cprint.force_new_line ();
    Cprint.print_decl "__missing_field_name" tgt;  Cprint.force_new_line ();
    Cprint.flush ()
  )
end

let printDefn (d : definition) =
begin
  if (verbose && traceActive "patchDebug") then (
    Cprint.print_def d;
    Cprint.flush ()
  )
end


(* class to describe how to modify the tree for subtitution *)
class substitutor (bindings : binding list) = object(self)
  inherit nopCabsVisitor as super

  (* look in the binding list for a given name *)
  method findBinding (name : string) : binding =
  begin
    try
      (List.find
        (fun b ->
          match b with
          | BSpecifier(n, _) -> n=name
          | BName(n, _) -> n=name
          | BExpr(n, _) -> n=name)
        bindings)
    with
      Not_found -> raise (BadBind ("name not found: " ^ name))
  end

  method vexpr (e:expression) : expression visitAction =
  begin
    match e with
    | EXPR_PATTERN(name) -> (
        match (self#findBinding name) with
        | BExpr(_, expr) -> ChangeTo(expr)    (* substitute bound expression *)
        | _ -> raise (BadBind ("wrong type: " ^ name))
      )
    | _ -> DoChildren
  end
  
  (* use of a name *)
  method vvar (s:string) : string =
  begin
    if (isPatternVar s) then (
      let nameString = (extractPatternVar s) in
      match (self#findBinding nameString) with
      | BName(_, str) -> str        (* substitute *)
      | _ -> raise (BadBind ("wrong type: " ^ nameString))
    )
    else
      s
  end

  (* binding introduction of a name *)
  method vname (k: nameKind) (spec: specifier) (n: name) : name visitAction =
  begin
    match n with (s (*variable name*), dtype, attrs, loc) -> (
      let replacement = (self#vvar s) in    (* use replacer from above *)
      if (s <> replacement) then
        ChangeTo(replacement, dtype, attrs, loc)
      else
        DoChildren                          (* no replacement *)
    )
  end

  method vspec (specList: specifier) : specifier visitAction =
  begin
    if verbose then (trace "patchDebug" (dprintf "substitutor: vspec\n"));
    (printSpec specList);

    (* are any of the specifiers SpecPatterns?  we have to check the entire *)
    (* list, not just the head, because e.g. "typedef @specifier(foo)" has *)
    (* "typedef" as the head of the specifier list *)
    if (List.exists (fun elt -> match elt with
                                | SpecPattern(_) -> true
                                | _ -> false)
                    specList) then begin
      (* yes, replace the existing list with one got by *)
      (* replacing all occurrences of SpecPatterns *)
      (trace "patchDebug" (dprintf "at least one spec pattern\n"));
      ChangeTo
        (List.flatten
          (List.map
            (* for each specifier element, yield the specifier list *)
            (* to which it maps; then we'll flatten the final result *)
            (fun elt ->
              match elt with
              | SpecPattern(name) -> (
                  match (self#findBinding name) with
                  | BSpecifier(_, replacement) -> (
                      (trace "patchDebug" (dprintf "replacing pattern %s\n" name));
                      replacement                                                  
                    )
                  | _ -> raise (BadBind ("wrong type: " ^ name))
                )
              | _ -> [elt]    (* leave this one alone *)
            )
            specList
          )
        )
    end
    else
      (* none of the specifiers in specList are patterns *)
      DoChildren
  end

  method vtypespec (tspec: typeSpecifier) : typeSpecifier visitAction =
  begin
    match tspec with
    | Tnamed(str) when (isPatternVar str) ->
        ChangeTo(Tnamed(self#vvar str))
    | Tstruct(str, fields, extraAttrs) when (isPatternVar str) -> (
        (trace "patchDebug" (dprintf "substituting %s\n" str));
        ChangeDoChildrenPost(Tstruct((self#vvar str), fields, extraAttrs), identity)
      )
    | Tunion(str, fields, extraAttrs) when (isPatternVar str) ->
        (trace "patchDebug" (dprintf "substituting %s\n" str));
        ChangeDoChildrenPost(Tunion((self#vvar str), fields, extraAttrs), identity)
    | _ -> DoChildren
  end

end


(* why can't I have forward declarations in the language?!! *)
let unifyExprFwd : (expression -> expression -> binding list) ref
  = ref (fun e e -> [])


(* substitution for expressions *)
let substExpr (bindings : binding list) (expr : expression) : expression =
begin            
  if verbose then
    (trace "patchDebug" (dprintf "substExpr with %d bindings\n" (List.length bindings)));
  (printExpr expr);

  (* apply the transformation *)
  let result = (visitCabsExpression (new substitutor bindings :> cabsVisitor) expr) in
  (printExpr result);

  result
end

let d_loc (_:unit) (loc: cabsloc) : doc =
  text loc.filename ++ chr ':' ++ num loc.lineno


(* class to describe how to modify the tree when looking for places *)
(* to apply expression transformers *)
class exprTransformer (srcpattern : expression) (destpattern : expression)
                      (patchline : int) (srcloc : cabsloc) = object(self)
  inherit nopCabsVisitor as super

  method vexpr (e:expression) : expression visitAction =
  begin
    (* see if the source pattern matches this subexpression *)
    try (
      let bindings = (!unifyExprFwd srcpattern e) in

      (* match! *)
      (trace "patch" (dprintf "expr match: patch line %d, src %a\n"
                              patchline d_loc srcloc));
      ChangeTo(substExpr bindings destpattern)
    )

    with NoMatch -> (
      (* doesn't apply *)
      DoChildren
    )
  end

  (* other constructs left unchanged *)
end


let unifyList (pat : 'a list) (tgt : 'a list)
              (unifyElement : 'a -> 'a -> binding list) : binding list =
begin
  if verbose then
    (trace "patchDebug" (dprintf "unifyList (pat len %d, tgt len %d)\n"
                                 (List.length pat) (List.length tgt)));

  (* walk down the lists *)
  let rec loop pat tgt : binding list =
    match pat, tgt with
    | [], [] -> []
    | (pelt :: prest), (telt :: trest) ->
         (unifyElement pelt telt) @
         (loop prest trest)
    | _,_ -> (
        (* no match *)
        if verbose then (
          (trace "patchDebug" (dprintf "mismatching list length\n"));
        );
        raise NoMatch
     )
  in
  (loop pat tgt)
end


let gettime () : float =
  (Unix.times ()).Unix.tms_utime

let rec applyPatch (patchFile : file) (srcFile : file) : file =
begin
  let patch : definition list = (snd patchFile) in
  let srcFname : string = (fst srcFile) in
  let src : definition list = (snd srcFile) in

  (trace "patchTime" (dprintf "applyPatch start: %f\n" (gettime ())));
  if (traceActive "patchDebug") then
    Cprint.out := stdout      (* hack *)
  else ();

  (* more hackery *)
  unifyExprFwd := unifyExpr;

  (* patch a single source definition, yield transformed *)
  let rec patchDefn (patch : definition list) (d : definition) : definition list =
  begin
    match patch with
    | TRANSFORMER(srcpattern, destpattern, loc) :: rest -> (
        if verbose then
          (trace "patchDebug"
            (dprintf "considering applying defn pattern at line %d to src at %a\n"
                     loc.lineno d_loc (get_definitionloc d)));

        (* see if the source pattern matches the definition 'd' we have *)
        try (
          let bindings = (unifyDefn srcpattern d) in

          (* we have a match!  apply the substitutions *)
          (trace "patch" (dprintf "defn match: patch line %d, src %a\n"
                                  loc.lineno d_loc (get_definitionloc d)));

          (List.map (fun destElt -> (substDefn bindings destElt)) destpattern)
        )

        with NoMatch -> (
          (* no match, continue down list *)
          (*(trace "patch" (dprintf "no match\n"));*)
          (patchDefn rest d)
        )
      )

    | EXPRTRANSFORMER(srcpattern, destpattern, loc) :: rest -> (
        if verbose then
          (trace "patchDebug"
            (dprintf "considering applying expr pattern at line %d to src at %a\n"
                     loc.lineno d_loc (get_definitionloc d)));

        (* walk around in 'd' looking for expressions to modify *)
        let dList = (visitCabsDefinition
                      ((new exprTransformer srcpattern destpattern
                                            loc.lineno (get_definitionloc d))
                       :> cabsVisitor)
                      d
                    ) in

        (* recursively invoke myself to try additional patches *)
        (* since visitCabsDefinition might return a list, I'll try my *)
        (* addtional patches on every yielded definition, then collapse *)
        (* all of them into a single list *)
        (List.flatten (List.map (fun d -> (patchDefn rest d)) dList))
      )

    | _ :: rest -> (
        (* not a transformer; just keep going *)
        (patchDefn rest d)
      )
    | [] -> (
        (* reached the end of the patch file with no match *)
        [d]     (* have to wrap it in a list ... *)
      )
  end in

  (* transform all the definitions *)
  let result : definition list =
    (List.flatten (List.map (fun d -> (patchDefn patch d)) src)) in

  (*Cprint.print_defs result;*)

  if (traceActive "patchDebug") then (
    (* avoid flush bug? yes *)
    Cprint.force_new_line ();
    Cprint.flush ()
  );

  (trace "patchTime" (dprintf "applyPatch finish: %f\n" (gettime ())));
  (srcFname, result)
end


(* given a definition pattern 'pat', and a target concrete defintion 'tgt', *)
(* determine if they can be unified; if so, return the list of bindings of *)
(* unification variables in pat; otherwise raise NoMatch *)
and unifyDefn (pat : definition) (tgt : definition) : binding list =
begin
  match pat, tgt with
  | DECDEF((pspecifiers, pdeclarators), _),
    DECDEF((tspecifiers, tdeclarators), _) -> (
      if verbose then
        (trace "patchDebug" (dprintf "unifyDefn of DECDEFs\n"));
      (unifySpecifiers pspecifiers tspecifiers) @
      (unifyInitDeclarators pdeclarators tdeclarators)
    )

  | TYPEDEF((pspec, pdecl), _),
    TYPEDEF((tspec, tdecl), _) -> (
      if verbose then
        (trace "patchDebug" (dprintf "unifyDefn of TYPEDEFs\n"));
      (unifySpecifiers pspec tspec) @
      (unifyDeclarators pdecl tdecl)
    )

  | ONLYTYPEDEF(pspec, _),
    ONLYTYPEDEF(tspec, _) -> (
      if verbose then
        (trace "patchDebug" (dprintf "unifyDefn of ONLYTYPEDEFs\n"));
      (unifySpecifiers pspec tspec)
    )

  | _, _ -> (
      if verbose then
        (trace "patchDebug" (dprintf "mismatching definitions\n"));
      raise NoMatch
    )
end

and unifySpecifier (pat : spec_elem) (tgt : spec_elem) : binding list =
begin
  if verbose then
    (trace "patchDebug" (dprintf "unifySpecifier\n"));
  (printSpecs [pat] [tgt]);

  if (pat = tgt) then [] else

  match pat, tgt with
  | SpecType(tspec1), SpecType(tspec2) ->
      (unifyTypeSpecifier tspec1 tspec2)
  | SpecPattern(name), _ ->
      (* record that future occurrances of @specifier(name) will yield this specifier *)
      if verbose then
        (trace "patchDebug" (dprintf "found specifier match for %s\n" name));
      [BSpecifier(name, [tgt])]
  | _,_ -> (
      (* no match *)
      if verbose then (
        (trace "patchDebug" (dprintf "mismatching specifiers\n"));
      );
      raise NoMatch
   )
end

and unifySpecifiers (pat : spec_elem list) (tgt : spec_elem list) : binding list =
begin
  if verbose then
    (trace "patchDebug" (dprintf "unifySpecifiers\n"));
  (printSpecs pat tgt);

  (* canonicalize the specifiers by sorting them *)
  let pat' = (List.stable_sort compare pat) in
  let tgt' = (List.stable_sort compare tgt) in

  (* if they are equal, they match with no further checking *)
  if (pat' = tgt') then [] else

  (* walk down the lists; don't walk the sorted lists because the *)
  (* pattern must always be last, if it occurs *)
  let rec loop pat tgt : binding list =
    match pat, tgt with
    | [], [] -> []
    | [SpecPattern(name)], _ ->
        (* final SpecPattern matches anything which comes after *)
        (* record that future occurrences of @specifier(name) will yield this specifier *)
        if verbose then
          (trace "patchDebug" (dprintf "found specifier match for %s\n" name));
        [BSpecifier(name, tgt)]
    | (pspec :: prest), (tspec :: trest) ->
         (unifySpecifier pspec tspec) @
         (loop prest trest)
    | _,_ -> (
        (* no match *)
        if verbose then (
          (trace "patchDebug" (dprintf "mismatching specifier list length\n"));
        );
        raise NoMatch
     )
  in
  (loop pat tgt)
end

and unifyTypeSpecifier (pat: typeSpecifier) (tgt: typeSpecifier) : binding list =
begin
  if verbose then
    (trace "patchDebug" (dprintf "unifyTypeSpecifier\n"));

  if (pat = tgt) then [] else

  match pat, tgt with
  | Tnamed(s1), Tnamed(s2) -> (unifyString s1 s2)
  | Tstruct(name1, None, _), Tstruct(name2, None, _) ->
      (unifyString name1 name2)
  | Tstruct(name1, Some(fields1), _), Tstruct(name2, Some(fields2), _) ->
      (* ignoring extraAttrs b/c we're just trying to come up with a list
       * of substitutions, and there's no unify_attributes function, and
       * I don't care at this time about checking that they are equal .. *)
      (unifyString name1 name2) @
      (unifyList fields1 fields2 unifyField)
  | Tunion(name1, None, _), Tstruct(name2, None, _) ->
      (unifyString name1 name2)
  | Tunion(name1, Some(fields1), _), Tunion(name2, Some(fields2), _) ->
      (unifyString name1 name2) @
      (unifyList fields1 fields2 unifyField)
  | Tenum(name1, None, _), Tenum(name2, None, _) ->
      (unifyString name1 name2)
  | Tenum(name1, Some(items1), _), Tenum(name2, Some(items2), _) ->
      (mustEq items1 items2);    (* enum items *)
      (unifyString name1 name2)
  | TtypeofE(exp1), TtypeofE(exp2) ->
      (unifyExpr exp1 exp2)
  | TtypeofT(spec1, dtype1), TtypeofT(spec2, dtype2) ->
      (unifySpecifiers spec1 spec2) @
      (unifyDeclType dtype1 dtype2)
  | _ -> (
      if verbose then (trace "patchDebug" (dprintf "mismatching typeSpecifiers\n"));
      raise NoMatch
    )
end

and unifyField (pat : field_group) (tgt : field_group) : binding list =
begin
  match pat,tgt with (spec1, list1), (spec2, list2) -> (
    (unifySpecifiers spec1 spec2) @
    (unifyList list1 list2 unifyNameExprOpt)
  )
end

and unifyNameExprOpt (pat : name * expression option)
                     (tgt : name * expression option) : binding list =
begin
  match pat,tgt with
  | (name1, None), (name2, None) -> (unifyName name1 name2)
  | (name1, Some(exp1)), (name2, Some(exp2)) ->
      (unifyName name1 name2) @
      (unifyExpr exp1 exp2)
  | _,_ -> []
end

and unifyName (pat : name) (tgt : name) : binding list =
begin
  match pat,tgt with (pstr, pdtype, pattrs, ploc), (tstr, tdtype, tattrs, tloc) ->
    (mustEq pattrs tattrs);
    (unifyString pstr tstr) @
    (unifyDeclType pdtype tdtype)
end

and unifyInitDeclarators (pat : init_name list) (tgt : init_name list) : binding list =
begin
  (*
    if verbose then
      (trace "patchDebug" (dprintf "unifyInitDeclarators, pat %d, tgt %d\n"
                                   (List.length pat) (List.length tgt)));
  *)

  match pat, tgt with
  | ((pdecl, piexpr) :: prest),
    ((tdecl, tiexpr) :: trest) ->
      (unifyDeclarator pdecl tdecl) @
      (unifyInitExpr piexpr tiexpr) @
      (unifyInitDeclarators prest trest)
  | [], [] -> []
  | _, _ -> (
      if verbose then
        (trace "patchDebug" (dprintf "mismatching init declarators\n"));
      raise NoMatch
    )
end

and unifyDeclarators (pat : name list) (tgt : name list) : binding list =
  (unifyList pat tgt unifyDeclarator)

and unifyDeclarator (pat : name) (tgt : name) : binding list =
begin
  if verbose then
    (trace "patchDebug" (dprintf "unifyDeclarator\n"));
  (printDecl pat tgt);

  match pat, tgt with
  | (pname, pdtype, pattr, ploc),
    (tname, tdtype, tattr, tloc) ->
      (mustEq pattr tattr);
      (unifyDeclType pdtype tdtype) @
      (unifyString pname tname)
end

and unifyDeclType (pat : decl_type) (tgt : decl_type) : binding list =
begin
  if verbose then
    (trace "patchDebug" (dprintf "unifyDeclType\n"));
  (printDeclType pat tgt);

  match pat, tgt with
  | JUSTBASE, JUSTBASE -> []
  | PARENTYPE(pattr1, ptype, pattr2),
    PARENTYPE(tattr1, ttype, tattr2) ->
      (mustEq pattr1 tattr1);
      (mustEq pattr2 tattr2);
      (unifyDeclType ptype ttype)
  | ARRAY(ptype, pattr, psz),
    ARRAY(ttype, tattr, tsz) ->
      (mustEq pattr tattr);
      (unifyDeclType ptype ttype) @
      (unifyExpr psz tsz)
  | PTR(pattr, ptype),
    PTR(tattr, ttype) ->
      (mustEq pattr tattr);
      (unifyDeclType ptype ttype)
  | PROTO(ptype, pformals, pva),
    PROTO(ttype, tformals, tva) ->
      (mustEq pva tva);
      (unifyDeclType ptype ttype) @
      (unifySingleNames pformals tformals)
  | _ -> (
      if verbose then
        (trace "patchDebug" (dprintf "mismatching decl_types\n"));
      raise NoMatch
    )
end

and unifySingleNames (pat : single_name list) (tgt : single_name list) : binding list =
begin
  if verbose then
    (trace "patchDebug" (dprintf "unifySingleNames, pat %d, tgt %d\n"
                                 (List.length pat) (List.length tgt)));

  match pat, tgt with
  | [], [] -> []
  | (pspec, pdecl) :: prest,
    (tspec, tdecl) :: trest ->
      (unifySpecifiers pspec tspec) @
      (unifyDeclarator pdecl tdecl) @
      (unifySingleNames prest trest)
  | _, _ -> (
      if verbose then
        (trace "patchDebug" (dprintf "mismatching single_name lists\n"));
      raise NoMatch
    )
end

and unifyString (pat : string) (tgt : string) : binding list =
begin
  (* equal? match with no further ado *)
  if (pat = tgt) then [] else

  (* is the pattern a variable? *)
  if (isPatternVar pat) then
    (* pat is actually "@name(blah)"; extract the 'blah' *)
    let varname = (extractPatternVar pat) in

    (* when substituted, this name becomes 'tgt' *)
    if verbose then
      (trace "patchDebug" (dprintf "found name match for %s\n" varname));
    [BName(varname, tgt)]

  else (
    if verbose then
      (trace "patchDebug" (dprintf "mismatching names: %s and %s\n" pat tgt));
    raise NoMatch
  )
end

and unifyExpr (pat : expression) (tgt : expression) : binding list =
begin
  (* if they're equal, that's good enough *)
  if (pat = tgt) then [] else

  (* shorter name *)
  let ue = unifyExpr in

  (* because of the equality check above, I can omit some cases *)
  match pat, tgt with
  | UNARY(pop, pexpr),
    UNARY(top, texpr) ->
      (mustEq pop top);
      (ue pexpr texpr)
  | BINARY(pop, pexp1, pexp2),
    BINARY(top, texp1, texp2) ->
      (mustEq pop top);
      (ue pexp1 texp1) @
      (ue pexp2 texp2)
  | QUESTION(p1, p2, p3),
    QUESTION(t1, t2, t3) ->
      (ue p1 t1) @
      (ue p2 t2) @
      (ue p3 t3)
  | CAST((pspec, ptype), piexpr),
    CAST((tspec, ttype), tiexpr) ->
      (mustEq ptype ttype);
      (unifySpecifiers pspec tspec) @
      (unifyInitExpr piexpr tiexpr)
  | CALL(pfunc, pargs),
    CALL(tfunc, targs) ->
      (ue pfunc tfunc) @
      (unifyExprs pargs targs)
  | COMMA(pexprs),
    COMMA(texprs) ->
      (unifyExprs pexprs texprs)
  | EXPR_SIZEOF(pexpr),
    EXPR_SIZEOF(texpr) ->
      (ue pexpr texpr)
  | TYPE_SIZEOF(pspec, ptype),
    TYPE_SIZEOF(tspec, ttype) ->
      (mustEq ptype ttype);
      (unifySpecifiers pspec tspec)
  | EXPR_ALIGNOF(pexpr),
    EXPR_ALIGNOF(texpr) ->
      (ue pexpr texpr)
  | TYPE_ALIGNOF(pspec, ptype),
    TYPE_ALIGNOF(tspec, ttype) ->
      (mustEq ptype ttype);
      (unifySpecifiers pspec tspec)
  | INDEX(parr, pindex),
    INDEX(tarr, tindex) ->
      (ue parr tarr) @
      (ue pindex tindex)
  | MEMBEROF(pexpr, pfield),
    MEMBEROF(texpr, tfield) ->
      (mustEq pfield tfield);
      (ue pexpr texpr)
  | MEMBEROFPTR(pexpr, pfield),
    MEMBEROFPTR(texpr, tfield) ->
      (mustEq pfield tfield);
      (ue pexpr texpr)
  | GNU_BODY(pblock),
    GNU_BODY(tblock) ->
      (mustEq pblock tblock);
      []
  | EXPR_PATTERN(name), _ ->
      (* match, and contribute binding *)
      if verbose then
        (trace "patchDebug" (dprintf "found expr match for %s\n" name));
      [BExpr(name, tgt)]
  | a, b ->
      if (verbose && traceActive "patchDebug") then (
        (trace "patchDebug" (dprintf "mismatching expression\n"));
        (printExpr a);
        (printExpr b)
      );
      raise NoMatch
end

and unifyInitExpr (pat : init_expression) (tgt : init_expression) : binding list =
begin
  (*
    Cprint.print_init_expression pat;  Cprint.force_new_line ();
    Cprint.print_init_expression tgt;  Cprint.force_new_line ();
    Cprint.flush ();
  *)

  match pat, tgt with
  | NO_INIT, NO_INIT -> []
  | SINGLE_INIT(pe), SINGLE_INIT(te) ->
      (unifyExpr pe te)
  | COMPOUND_INIT(plist),
    COMPOUND_INIT(tlist) -> (
      let rec loop plist tlist =
        match plist, tlist with
        | ((pwhat, piexpr) :: prest),
          ((twhat, tiexpr) :: trest) ->
            (mustEq pwhat twhat);
            (unifyInitExpr piexpr tiexpr) @
            (loop prest trest)
        | [], [] -> []
        | _, _ -> (
            if verbose then
              (trace "patchDebug" (dprintf "mismatching compound init exprs\n"));
            raise NoMatch
          )
      in
      (loop plist tlist)
    )
  | _,_ -> (
      if verbose then
        (trace "patchDebug" (dprintf "mismatching init exprs\n"));
      raise NoMatch
    )
end

and unifyExprs (pat : expression list) (tgt : expression list) : binding list =
  (unifyList pat tgt unifyExpr)


(* given the list of bindings 'b', substitute them into 'd' to yield a new definition *)
and substDefn (bindings : binding list) (defn : definition) : definition =
begin
  if verbose then
    (trace "patchDebug" (dprintf "substDefn with %d bindings\n" (List.length bindings)));
  (printDefn defn);

  (* apply the transformation *)
  match (visitCabsDefinition (new substitutor bindings :> cabsVisitor) defn) with
  | [d] -> d    (* expect a singleton list *)
  | _ -> (failwith "didn't get a singleton list where I expected one")
end


(* end of file *)
