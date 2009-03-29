(** See copyright notice at the end of this file *)

(** Add printf before each function call *)

open Pretty
open Cil
open Trace
module E = Errormsg
module H = Hashtbl

let i = ref 0
let name = ref ""

(* Switches *)
let printFunctionName = ref "printf"

let addProto = ref false

let printf: varinfo option ref = ref None
let makePrintfFunction () : varinfo = 
    match !printf with 
      Some v -> v
    | None -> begin 
        let v = makeGlobalVar !printFunctionName 
                     (TFun(voidType, Some [("format", charPtrType, [])],
                             true, [])) in
        printf := Some v;
        addProto := true;
        v
    end

let mkPrint (format: string) (args: exp list) : instr = 
  let p: varinfo = makePrintfFunction () in 
  Call(None, Lval(var p), (mkString format) :: args, !currentLoc)
  

let d_string (fmt : ('a,unit,doc,string) format4) : 'a = 
  let f (d: doc) : string = 
    Pretty.sprint 200 d
  in
  Pretty.gprintf f fmt 

let currentFunc: string ref = ref ""

class logCallsVisitorClass = object
  inherit nopCilVisitor

  (* Watch for a declaration for our printer *)
  
  method vinst i = begin
    match i with
    | Call(lo,e,al,l) ->
        let pre = mkPrint (d_string "call %a\n" d_exp e) [] in
        let post = mkPrint (d_string "return from %a\n" d_exp e) [] in
(*
      let str1 = prefix ^
        (Pretty.sprint 800 ( Pretty.dprintf "Calling %a(%a)\n"
          d_exp e
          (docList ~sep:(chr ',' ++ break ) (fun arg ->
            try
              match unrollType (typeOf arg) with
                  TInt _ | TEnum _ -> dprintf "%a = %%d" d_exp arg
                | TFloat _ -> dprintf "%a = %%g" d_exp arg
                | TVoid _ -> text "void"
                | TComp _ -> text "comp"
                | _ -> dprintf "%a = %%p" d_exp arg
            with  _ -> dprintf "%a = %%p" d_exp arg)) al)) in
      let log_args = List.filter (fun arg ->
        match unrollType (typeOf arg) with
          TVoid _ | TComp _ -> false
        | _ -> true) al in
      let str2 = prefix ^ (Pretty.sprint 800
        ( Pretty.dprintf "Returned from %a\n" d_exp e)) in
      let newinst str args = ((Call (None, Lval(var printfFun.svar),
                                ( [ (* one ; *) mkString str ] @ args),
                                locUnknown)) : instr )in
      let ilist = ([ (newinst str1 log_args) ; i ; (newinst str2 []) ] : instr list) in
 *)
    ChangeTo [ pre; i; post ] 

    | _ -> DoChildren
  end
  method vstmt (s : stmt) = begin
    match s.skind with
      Return _ -> 
        let pre = mkPrint (d_string "exit %s\n" !currentFunc) [] in 
        ChangeTo (mkStmt (Block (mkBlock [ mkStmtOneInstr pre; s ])))
    | _ -> DoChildren

(*
(Some(e),l) ->
      let str = prefix ^ Pretty.sprint 800 ( Pretty.dprintf
        "Return(%%p) from %s\n" funstr ) in
      let newinst = ((Call (None, Lval(var printfFun.svar),
                                ( [ (* one ; *) mkString str ; e ]),
                                locUnknown)) : instr )in
      let new_stmt = mkStmtOneInstr newinst in
      let slist = [ new_stmt ; s ] in
      (ChangeTo(mkStmt(Block(mkBlock slist))))
    | Return(None,l) ->
      let str = prefix ^ (Pretty.sprint 800 ( Pretty.dprintf
        "Return void from %s\n" funstr)) in
      let newinst = ((Call (None, Lval(var printfFun.svar),
                                ( [ (* one ; *) mkString str ]),
                                locUnknown)) : instr )in
      let new_stmt = mkStmtOneInstr newinst in
      let slist = [ new_stmt ; s ] in
      (ChangeTo(mkStmt(Block(mkBlock slist))))
    | _ -> DoChildren
*)
  end
end

let logCallsVisitor = new logCallsVisitorClass


let logCalls (f: file) : unit =

  let doGlobal = function
    | GVarDecl (v, _) when v.vname = !printFunctionName -> 
          if !printf = None then
             printf := Some v

    | GFun (fdec, loc) ->
        currentFunc := fdec.svar.vname;
        (* do the body *)
        ignore (visitCilFunction logCallsVisitor fdec);
        (* Now add the entry instruction *)
        let pre = mkPrint (d_string "enter %s\n" !currentFunc) [] in 
        fdec.sbody <- 
          mkBlock [ mkStmtOneInstr pre;
                    mkStmt (Block fdec.sbody) ]
(*
	(* debugging 'anagram', it's really nice to be able to see the strings *)
	(* inside fat pointers, even if it's a bit of a hassle and a hack here *)
	let isFatCharPtr (cinfo:compinfo) =
	  cinfo.cname="wildp_char" ||
	  cinfo.cname="fseqp_char" ||
	  cinfo.cname="seqp_char" in

        (* Collect expressions that denote the actual arguments *)
        let actargs =
          (* make lvals out of args which pass test below *)
          (List.map
            (fun vi -> match unrollType vi.vtype with
              | TComp(cinfo, _) when isFatCharPtr(cinfo) ->
                  (* access the _p field for these *)
                  (* luckily it's called "_p" in all three fat pointer variants *)
                  Lval(Var(vi), Field(getCompField cinfo "_p", NoOffset))
              | _ ->
                  Lval(var vi))

            (* decide which args to pass *)
            (List.filter
              (fun vi -> match unrollType vi.vtype with
                | TPtr(TInt(k, _), _) when isCharType(k) ->
                    !printPtrs || !printStrings
                | TComp(cinfo, _) when isFatCharPtr(cinfo) ->
                    !printStrings
                | TVoid _ | TComp _ -> false
                | TPtr _ | TArray _ | TFun _ -> !printPtrs
                | _ -> true)
              fdec.sformals)
          ) in

        (* make a format string for printing them *)
        (* sm: expanded width to 200 because I want one per line *)
        let formatstr = prefix ^ (Pretty.sprint 200
          (dprintf "entering %s(%a)\n" fdec.svar.vname
            (docList ~sep:(chr ',' ++ break)
              (fun vi -> match unrollType vi.vtype with
              | TInt _ | TEnum _ -> dprintf "%s = %%d" vi.vname
              | TFloat _ -> dprintf "%s = %%g" vi.vname
              | TVoid _ -> dprintf "%s = (void)" vi.vname
              | TComp(cinfo, _) -> (
                  if !printStrings && isFatCharPtr(cinfo) then
                    dprintf "%s = \"%%s\"" vi.vname
                  else
                    dprintf "%s = (comp)" vi.vname
                )
              | TPtr(TInt(k, _), _) when isCharType(k) -> (
                  if (!printStrings) then
                    dprintf "%s = \"%%s\"" vi.vname
                  else if (!printPtrs) then
                    dprintf "%s = %%p" vi.vname
                  else
                    dprintf "%s = (str)" vi.vname
                )
              | TPtr _ | TArray _ | TFun _ -> (
                  if (!printPtrs) then
                    dprintf "%s = %%p" vi.vname
                  else
                    dprintf "%s = (ptr)" vi.vname
                )
              | _ -> dprintf "%s = (?type?)" vi.vname))
            fdec.sformals)) in

        i := 0 ;
        name := fdec.svar.vname ;
        if !allInsts then (
          let thisVisitor = new verboseLogVisitor printfFun !name prefix in
          fdec.sbody <- visitCilBlock thisVisitor fdec.sbody
        );
        fdec.sbody.bstmts <-
              mkStmt (Instr [Call (None, Lval(var printfFun.svar),
                                ( (* one :: *) mkString formatstr 
                                   :: actargs),
                                loc)]) :: fdec.sbody.bstmts
 *)
    | _ -> ()
  in
  Stats.time "logCalls" (iterGlobals f) doGlobal;
  if !addProto then begin
     let p = makePrintfFunction () in 
     E.log "Adding prototype for call logging function %s\n" p.vname;
     f.globals <- GVarDecl (p, locUnknown) :: f.globals
  end  

let feature : featureDescr = 
  { fd_name = "logcalls";
    fd_enabled = Cilutil.logCalls;
    fd_description = "generation of code to log function calls";
    fd_extraopt = [
      ("--logcallprintf", Arg.String (fun s -> printFunctionName := s), 
       "the name of the printf function to use");
      ("--logcalladdproto", Arg.Unit (fun s -> addProto := true), 
       "whether to add the prototype for the printf function")
    ];
    fd_doit = logCalls;
    fd_post_check = true
  } 

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
