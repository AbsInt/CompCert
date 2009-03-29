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



(************************************************************************
 * canonicalize performs several transformations to correct differences
 * between C and C++, so that the output is (hopefully) valid C++ code.
 * This is incomplete -- certain fixes which are necessary 
 * for some programs are not yet implemented.
 * 
 * #1) C allows global variables to have multiple declarations and multiple
 *     (equivalent) definitions. This transformation removes all but one
 *     declaration and all but one definition.
 *
 * #2) Any variables that use C++ keywords as identifiers are renamed.
 *
 * #3) __inline is #defined to inline, and __restrict is #defined to nothing.
 *
 * #4) C allows function pointers with no specified arguments to be used on
 *     any argument list.  To make C++ accept this code, we insert a cast
 *     from the function pointer to a type that matches the arguments.  Of
 *     course, this does nothing to guarantee that the pointer actually has
 *     that type.
 *
 * #5) Makes casts from int to enum types explicit.  (CIL changes enum
 *     constants to int constants, but doesn't use a cast.)
 *
 ************************************************************************)

open Cil
module E = Errormsg
module H = Hashtbl

(* For transformation #1. Stores all variable definitions in the file. *)
let varDefinitions: (varinfo, global) H.t = H.create 111


class canonicalizeVisitor = object(self)
  inherit nopCilVisitor
  val mutable currentFunction: fundec = Cil.dummyFunDec;

  (* A hashtable to prevent duplicate declarations. *)
  val alreadyDeclared: (varinfo, unit) H.t = H.create 111
  val alreadyDefined: (varinfo, unit) H.t = H.create 111

  (* move variable declarations around *) 
  method vglob g = match g with 
    GVar(v, ({init = Some _} as inito), l) ->
      (* A definition.  May have been moved to an earlier position. *)
      if H.mem alreadyDefined v then begin
	ignore (E.warn "Duplicate definition of %s at %a.\n" 
		        v.vname d_loc !currentLoc);
	ChangeTo [] (* delete from here. *)
      end else begin
	H.add alreadyDefined v ();
	if H.mem alreadyDeclared v then begin
	  (* Change the earlier declaration to Extern *)
	  let oldS = v.vstorage in
	  ignore (E.log "changing storage of %s from %a\n" 
		    v.vname d_storage oldS);
	  v.vstorage <- Extern;	  
	  let newv = {v with vstorage = oldS} in
	  ChangeDoChildrenPost([GVar(newv, inito, l)], (fun g -> g) )
	end else
	  DoChildren
      end
  | GVar(v, {init=None}, l)
  | GVarDecl(v, l) when not (isFunctionType v.vtype) -> begin
      (* A declaration.  May have been moved to an earlier position. *)
      if H.mem alreadyDefined v || H.mem alreadyDeclared v then 
	ChangeTo [] (* delete from here. *)
      else begin
	H.add alreadyDeclared v ();
	DoChildren
      end
  end
  | GFun(f, l) ->
      currentFunction <- f; 
      DoChildren
  | _ ->
      DoChildren

(* #2. rename any identifiers whose names are C++ keywords *)
  method vvdec v = 
    match v.vname with
    | "bool"
    | "catch"
    | "cdecl"
    | "class"
    | "const_cast"
    | "delete"
    | "dynamic_cast"
    | "explicit"
    | "export"
    | "false"
    | "friend"
    | "mutable"
    | "namespace"
    | "new"
    | "operator"
    | "pascal"
    | "private"
    | "protected"
    | "public"
    | "register"
    | "reinterpret_cast"
    | "static_cast"
    | "template"
    | "this"
    | "throw"
    | "true"
    | "try"
    | "typeid"
    | "typename"
    | "using"
    | "virtual"
    | "wchar_t"->
	v.vname <- v.vname ^ "__cil2cpp";
	DoChildren
    | _ -> DoChildren

  method vinst i = 
(* #5. If an assignment or function call uses expressions as enum values,
   add an explicit cast. *)
    match i with 
      Set (dest, exp, l) -> begin
	let typeOfDest = typeOfLval dest in
	match unrollType typeOfDest with 
	  TEnum _ -> (* add an explicit cast *)
	    let newI = Set(dest, mkCast exp typeOfDest, l) in
	    ChangeTo [newI] 
	| _ -> SkipChildren
      end
    | Call (dest, f, args, l) -> begin
	let rt, formals, isva, attrs = splitFunctionType (typeOf f) in
	if isva then
	  SkipChildren (* ignore vararg functions *)
	else 
	  match formals with
	    Some formals' -> begin
	      let newArgs = try
		(*Iterate over the arguments, looking for formals that
		   expect enum types, and insert casts where necessary. *)
		List.map2 
		  (fun (actual: exp) (formalName, formalType, _) ->
		    match unrollType formalType with
		      TEnum _ -> mkCast actual formalType
		    | _ ->  actual)
		  args
		  formals' 	
	      with Invalid_argument _ -> 
		E.s (error "Number of arguments to %a doesn't match type.\n"
		       d_exp f)
	      in	  
	      let newI = Call(dest, f, newArgs, l) in
	      ChangeTo [newI] 
	    end
	  | None -> begin
  (* #4. No arguments were specified for this type.  To fix this, infer the
         type from the arguments that are used n this instruction, and insert
         a cast to that type.*)
	      match f with 
		Lval(Mem(fp), off) ->
		  let counter: int ref = ref 0 in
		  let newFormals = List.map
		      (fun (actual:exp) ->
			incr counter;
			let formalName = "a" ^ (string_of_int !counter) in
			(formalName, typeOf actual, []))(* (name,type,attrs) *)
			  args in
		  let newFuncPtrType =
		    TPtr((TFun (rt, Some newFormals, false, attrs)), []) in
		  let newFuncPtr = Lval(Mem(mkCast fp newFuncPtrType), off) in
		  ChangeTo [Call(dest, newFuncPtr, args, l)] 
	      | _ -> 
		  ignore (warn "cppcanon: %a has no specified arguments, but it's not a function pointer." d_exp f);
		  SkipChildren
	  end
    end
    | _ -> SkipChildren

  method vinit i = 
(* #5. If an initializer uses expressions as enum values,
   add an explicit cast. *)
    match i with 
      SingleInit e -> DoChildren (* we don't handle simple initializers here, 
				  because we don't know what type is expected.
				  This should be done in vglob if needed. *)
    | CompoundInit(t, initList) ->
	let changed: bool ref = ref false in
	let initList' = List.map
	    (* iterate over the list, adding casts for any expression that
	       is expected to be an enum type. *)
	  (function
	      (Field(fi, off), SingleInit e) -> begin
		match unrollType fi.ftype with
		  TEnum _ -> (* add an explicit cast *)
		    let newE = mkCast e fi.ftype in
		    changed := true;
		    (Field(fi, off), SingleInit newE)
		| _ -> (* not enum, no cast needed *)
		    (Field(fi, off), SingleInit e)
	      end
	    | other ->
                   (* This is a more complicated initializer, and I don't think
		      it can have type enum.  It's children might, though. *)
		other)
	    initList in
	if !changed then begin
          (* There may be other casts needed in other parts of the
	     initialization, so do the children too. *)
	  ChangeDoChildrenPost(CompoundInit(t, initList'), (fun x -> x))
	end else
	  DoChildren
   

(* #5. If a function returns an enum type, add an explicit cast to the
       return type. *)
  method vstmt stmt = 
    (match stmt.skind with
      Return (Some exp, l) -> begin
	let typeOfDest, _, _, _ = 
	  splitFunctionType currentFunction.svar.vtype in
	match unrollType typeOfDest with 
	  TEnum _ -> 
	    stmt.skind <- Return (Some (mkCast exp typeOfDest), l)
	| _ -> ()
      end
    | _ -> ());
    DoChildren
end (* class canonicalizeVisitor *)



(* Entry point for this extension *)
let canonicalize (f:file) =
  visitCilFile (new canonicalizeVisitor) f;

  (* #3. Finally, add some #defines to change C keywords to their C++ 
     equivalents: *)
  f.globals <-
    GText( "#ifdef __cplusplus\n"
	  ^" #define __restrict\n" (* "restrict" doesn't work *)
	  ^" #define __inline inline\n"
	  ^"#endif")
    ::f.globals



let feature : featureDescr = 
  { fd_name = "canonicalize";
    fd_enabled = ref false;
    fd_description = "fixing some C-isms so that the result is C++ compliant.";
    fd_extraopt = [];
    fd_doit = canonicalize;
    fd_post_check = true;
  } 
