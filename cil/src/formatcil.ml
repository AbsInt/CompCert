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
open Cil
open Pretty
open Trace      (* sm: 'trace' function *)
module E = Errormsg
module H = Hashtbl

let noMemoize = ref false

let expMemoTable :
    (string, (((string * formatArg) list -> exp) * 
               (exp -> formatArg list option))) H.t = H.create 23

let typeMemoTable :
    (string, (((string * formatArg) list -> typ) * 
               (typ -> formatArg list option))) H.t = H.create 23

let lvalMemoTable :
    (string, (((string * formatArg) list -> lval) * 
               (lval -> formatArg list option))) H.t = H.create 23

let instrMemoTable :
    (string, ((location -> (string * formatArg) list -> instr) * 
               (instr -> formatArg list option))) H.t = H.create 23

let stmtMemoTable :
    (string, ((string -> typ -> varinfo) -> 
              location -> 
              (string * formatArg) list -> stmt)) H.t = H.create 23

let stmtsMemoTable :
    (string, ((string -> typ -> varinfo) -> 
              location -> 
              (string * formatArg) list -> stmt list)) H.t = H.create 23


let doParse (prog: string) 
            (theParser: (Lexing.lexbuf -> Formatparse.token) 
                                          -> Lexing.lexbuf -> 'a)
            (memoTable: (string, 'a) H.t) : 'a = 
  try
    if !noMemoize then raise Not_found else
    H.find memoTable prog
  with Not_found -> begin
    let lexbuf = Formatlex.init prog in
    try
      Formatparse.initialize Formatlex.initial lexbuf;
      let res = theParser Formatlex.initial lexbuf in
      H.add memoTable prog res;
      Formatlex.finish ();
      res
    with Parsing.Parse_error -> begin
      Formatlex.finish ();
      E.s (E.error "Parsing error: %s" prog)
    end
    | e -> begin
        ignore (E.log "Caught %s while parsing\n" (Printexc.to_string e));
        Formatlex.finish ();
        raise e
    end
  end
  

let cExp (prog: string) : (string * formatArg) list -> exp = 
  let cf = doParse prog Formatparse.expression expMemoTable in
  (fst cf)

let cLval (prog: string) : (string * formatArg) list -> lval = 
  let cf = doParse prog Formatparse.lval lvalMemoTable in
  (fst cf)

let cType (prog: string) : (string * formatArg) list -> typ = 
  let cf = doParse prog Formatparse.typename typeMemoTable in
  (fst cf)

let cInstr (prog: string) : location -> (string * formatArg) list -> instr = 
  let cf = doParse prog Formatparse.instr instrMemoTable in
  (fst cf)

let cStmt (prog: string) : (string -> typ -> varinfo) -> 
                           location -> (string * formatArg) list -> stmt = 
  let cf = doParse prog Formatparse.stmt stmtMemoTable in
  cf

let cStmts (prog: string) : 
    (string -> typ -> varinfo) -> 
    location -> (string * formatArg) list -> stmt list = 
  let cf = doParse prog Formatparse.stmt_list stmtsMemoTable in
  cf



(* Match an expression *)
let dExp (prog: string) : exp -> formatArg list option = 
  let df = doParse prog Formatparse.expression expMemoTable in
  (snd df)

(* Match an lvalue *)
let dLval (prog: string) : lval -> formatArg list option = 
  let df = doParse prog Formatparse.lval lvalMemoTable in
  (snd df)


(* Match a type *)
let dType (prog: string) : typ -> formatArg list option = 
  let df = doParse prog Formatparse.typename typeMemoTable in
  (snd df)



(* Match an instruction *)
let dInstr (prog: string) : instr -> formatArg list option = 
  let df = doParse prog Formatparse.instr instrMemoTable in
  (snd df)


let test () = 
  (* Construct a dummy function *)
  let func = emptyFunction "test_formatcil" in
  (* Construct a few varinfo *)
  let res = makeLocalVar func "res" (TPtr(intType, [])) in
  let fptr = makeLocalVar func "fptr" 
      (TPtr(TFun(intType, None, false, []), [])) in
  (* Construct an instruction *)
  let makeInstr () = 
    Call(Some (var res), 
         Lval (Mem (CastE(TPtr(TFun(TPtr(intType, []),
                                    Some [ ("", intType, []);
                                           ("a2", TPtr(intType, []), []);
                                           ("a3", TPtr(TPtr(intType, []),
                                                       []), []) ], 
                                    false, []), []),
                          Lval (var fptr))), 
               NoOffset),
         [  ], locUnknown) 
  in
  let times = 100000 in
  (* Make the instruction the regular way *)
  Stats.time "make instruction regular" 
    (fun _ -> for i = 0 to times do ignore (makeInstr ()) done)
    ();
  (* Now make the instruction interpreted *)
  noMemoize := true;
  Stats.time "make instruction interpreted"
    (fun _ -> for i = 0 to times do 
      let _ = 
        cInstr "%v:res = (* ((int * (*)(int, int * a2, int * * a3))%v:fptr))();"
          locUnknown [ ("res", Fv res); 
                       ("fptr", Fv fptr) ] 
      in
      ()
    done)
    ();
  (* Now make the instruction interpreted with memoization *)
  noMemoize := false;
  Stats.time "make instruction interpreted memoized"
    (fun _ -> for i = 0 to times do 
      let _ = 
        cInstr "%v:res = (* ((int * (*)(int, int * a2, int * * a3))%v:fptr))();"
          locUnknown [ ("res", Fv res); ("fptr", Fv fptr) ] 
      in
      ()
    done)
    ();
  (* Now make the instruction interpreted with partial application *)
  let partInstr = 
    cInstr "%v:res = (* ((int * (*)(int, int * a2, int * * a3))%v:fptr))();" in
  Stats.time "make instruction interpreted partial"
    (fun _ -> for i = 0 to times do 
      let _ = 
        partInstr
          locUnknown [ ("res", Fv res); ("fptr", Fv fptr) ] 
      in
      ()
    done)
    ();
    
  ()
  
  
