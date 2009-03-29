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
open Cil
module E = Errormsg
(*
 * Weimer: an AST Slicer for use in Daniel's Delta Debugging Algorithm.
 *)
let debug = ref false 

(* 
 * This type encapsulates a mapping form program locations to names
 * in our naming convention.
 *)
type enumeration_info = {
  statements : (stmt, string) Hashtbl.t ;
  instructions : (instr, string) Hashtbl.t ;
} 

(**********************************************************************
 * Enumerate 1
 *
 * Given a cil file, enumerate all of the statement names in it using
 * our naming scheme. 
 **********************************************************************)
let enumerate out (f : Cil.file) = 
  let st_ht = Hashtbl.create 32767 in
  let in_ht = Hashtbl.create 32767 in

  let emit base i ht elt =
    let str = Printf.sprintf "%s.%d" base !i in
    Printf.fprintf out "%s\n" str ;
    Hashtbl.add ht elt str ; 
    incr i
  in 
  let emit_call base i str2 ht elt =
    let str = Printf.sprintf "%s.%d" base !i in 
    Printf.fprintf out "%s - %s\n" str str2 ;
    Hashtbl.add ht elt str ; 
    incr i
  in 
  let descend base i =
    let res = (Printf.sprintf "%s.%d" base !i),(ref 0) in
    res
  in 
  let rec doBlock b base i =
    doStmtList b.bstmts base i
  and doStmtList sl base i = 
    List.iter (fun s -> match s.skind with
    | Instr(il) -> doIL il base i 
    | Return(_,_)
    | Goto(_,_)
    | Continue(_) 
    | Break(_) -> emit base i st_ht s
    | If(e,b1,b2,_) -> 
          emit base i st_ht s ; 
          decr i ; 
          Printf.fprintf out "(\n" ; 
          let base',i' = descend base i in
          doBlock b1 base' i' ;
          Printf.fprintf out ") (\n" ; 
          let base'',i'' = descend base i in
          doBlock b2 base'' i'' ;
          Printf.fprintf out ")\n" ; 
          incr i 
    | Switch(_,b,_,_) 
(*
    | Loop(b,_,_,_) 
*)
    | While(_,b,_)
    | DoWhile(_,b,_)
    | For(_,_,_,b,_)
    | Block(b) -> 
          emit base i st_ht s ; 
          decr i ; 
          let base',i' = descend base i in
          Printf.fprintf out "(\n" ; 
          doBlock b base' i' ;
          Printf.fprintf out ")\n" ; 
          incr i 
    | TryExcept _ | TryFinally _ -> 
        E.s (E.unimp "astslicer:enumerate")
    ) sl 
  and doIL il base i = 
    List.iter (fun ins -> match ins with
      | Set _  
      | Asm _ -> emit base i in_ht ins
      | Call(_,(Lval(Var(vi),NoOffset)),_,_) -> 
                 emit_call base i vi.vname in_ht ins
      | Call(_,f,_,_) -> emit_call base i "*" in_ht ins
    ) il 
  in 
  let doGlobal g = match g with 
  | GFun(fd,_) -> 
      Printf.fprintf out "%s (\n" fd.svar.vname ; 
      let cur = ref 0 in 
      doBlock fd.sbody fd.svar.vname cur ; 
      Printf.fprintf out ")\n" ; 
      ()
  | _ -> () 
  in
  List.iter doGlobal f.globals ;
  { statements = st_ht ;
    instructions = in_ht ; }

(**********************************************************************
 * Enumerate 2
 *
 * Given a cil file and some enumeration information, do a log-calls-like
 * transformation on it that prints out our names as you reach them. 
 **********************************************************************)
(* 
 * This is the visitor that handles annotations
 *)
let print_it pfun name =
  ((Call(None,Lval(Var(pfun),NoOffset),
    [mkString (name ^ "\n")],locUnknown))) 

class enumVisitor pfun st_ht in_ht = object
  inherit nopCilVisitor
  method vinst i = 
    if Hashtbl.mem in_ht i then begin
      let name = Hashtbl.find in_ht i in
      let newinst = print_it pfun name in 
      ChangeTo([newinst ; i])
    end else
      DoChildren
  method vstmt s = 
    if Hashtbl.mem st_ht s then begin
      let name = Hashtbl.find st_ht s in
      let newinst = print_it pfun name in 
      let newstmt = mkStmtOneInstr newinst in
      let newblock = mkBlock [newstmt ; s] in
      let replace_with = mkStmt (Block(newblock)) in
      ChangeDoChildrenPost(s,(fun i -> replace_with)) 
    end else
      DoChildren
  method vfunc f = 
      let newinst = print_it pfun f.svar.vname in 
      let newstmt = mkStmtOneInstr newinst in
      let new_f = { f with sbody = { f.sbody with 
        bstmts = newstmt :: f.sbody.bstmts }} in
      ChangeDoChildrenPost(new_f,(fun i -> i))
end 

let annotate (f : Cil.file) ei = begin
  (* Create a prototype for the logging function *)
  let printfFun =
    let fdec = emptyFunction "printf" in
    let argf  = makeLocalVar fdec "format" charConstPtrType in
    fdec.svar.vtype <- TFun(intType, Some [ ("format", charConstPtrType, [])],
                            true, []);
    fdec
  in
  let visitor = (new enumVisitor printfFun.svar ei.statements 
    ei.instructions) in 
  visitCilFileSameGlobals visitor f;
  f
end 

(**********************************************************************
 * STAGE 2
 *
 * Perform a transitive-closure-like operation on the parts of the program
 * that the user wants to keep. We use a CIL visitor to walk around
 * and a number of hash tables to keep track of the things we want to keep. 
 **********************************************************************)
(*
 * Hashtables: 
 * ws   - wanted stmts
 * wi   - wanted instructions
 * wt   - wanted typeinfo 
 * wc   - wanted compinfo 
 * we   - wanted enuminfo 
 * wv   - wanted varinfo 
 *)

let mode = ref false (* was our parented wanted? *)
let finished = ref true (* set to false if we update something *)

(* In the given hashtable, mark the given element was "wanted" *)
let update ht elt =
  if Hashtbl.mem ht elt && (Hashtbl.find ht elt = true) then ()
  else begin
    Hashtbl.add ht elt true ;
    finished := false 
  end

(* Handle a particular stage of the AST tree walk. Use "mode" (i.e.,
 * whether our parent was wanted) and the hashtable (which tells us whether
 * the user had any special instructions for this element) to determine
 * what do to. *)
let handle ht elt rep =
    if !mode then begin
      if Hashtbl.mem ht elt && (Hashtbl.find ht elt = false) then begin
        (* our parent is Wanted but we were told to ignore this subtree,
         * so we won't be wanted. *)
        mode := false ;
        ChangeDoChildrenPost(rep,(fun elt -> mode := true ; elt))
      end else begin  
        (* we were not told to ignore this subtree, and our parent is
         * Wanted, so we will be Wanted too! *)
        update ht elt ; 
        DoChildren
      end 
    end else if Hashtbl.mem ht elt && (Hashtbl.find ht elt = true) then begin
      (* our parent was not wanted but we were wanted, so turn the
       * mode on for now *)
      mode := true ;
      ChangeDoChildrenPost(rep,(fun elt -> mode := false ; elt))
    end else 
      DoChildren

let handle_no_default ht elt rep old_mode = 
    if Hashtbl.mem ht elt && (Hashtbl.find ht elt = true) then begin
      (* our parent was not wanted but we were wanted, so turn the
       * mode on for now *)
      mode := true ;
      ChangeDoChildrenPost(rep,(fun elt -> mode := old_mode ; elt))
    end else begin
      mode := false ;
      ChangeDoChildrenPost(rep,(fun elt -> mode := old_mode ; elt))
    end

(* 
 * This is the visitor that handles elements (marks them as wanted)
 *)
class transVisitor ws wi wt wc we wv = object
  inherit nopCilVisitor

  method vvdec vi = handle_no_default wv vi vi !mode
  method vvrbl vi = handle wv vi vi
  method vinst i = handle wi i [i] 
  method vstmt s = handle ws s s
  method vfunc f = handle wv f.svar f
  method vglob g = begin
    match g with
    | GType(ti,_) -> handle wt ti [g]
    | GCompTag(ci,_) 
    | GCompTagDecl(ci,_) -> handle wc ci [g]
    | GEnumTag(ei,_) 
    | GEnumTagDecl(ei,_) -> handle we ei [g]
    | GVarDecl(vi,_) 
    | GVar(vi,_,_) -> handle wv vi [g]
    | GFun(f,_) -> handle wv f.svar [g]
    | _ -> DoChildren
  end
  method vtype t = begin
    match t with
    | TNamed(ti,_) -> handle wt ti t
    | TComp(ci,_) -> handle wc ci t
    | TEnum(ei,_) -> handle we ei t
    | _ -> DoChildren
  end
end 

(**********************************************************************
 * STAGE 3
 *
 * Eliminate all of the elements from the program that are not marked 
 * "keep". 
 **********************************************************************)
(* 
 * This is the visitor that throws away elements 
 *)
let handle ht elt keep drop =
  if (Hashtbl.mem ht elt) && (Hashtbl.find ht elt = true) then
    (* DoChildren *) ChangeDoChildrenPost(keep,(fun a -> a)) 
  else 
    ChangeTo(drop)

class dropVisitor ws wi wt wc we wv = object
  inherit nopCilVisitor

  method vinst i = handle wi i [i] []
  method vstmt s = handle ws s s (mkStmt (Instr([])))
  method vglob g = begin
    match g with
    | GType(ti,_) -> handle wt ti [g] []
    | GCompTag(ci,_) 
    | GCompTagDecl(ci,_) -> handle wc ci [g] []
    | GEnumTag(ei,_) 
    | GEnumTagDecl(ei,_) -> handle we ei [g] []
    | GVarDecl(vi,_) 
    | GVar(vi,_,_) -> handle wv vi [g] []
    | GFun(f,l) -> 
        let new_locals = List.filter (fun vi ->
          Hashtbl.mem wv vi && (Hashtbl.find wv vi = true)) f.slocals in
        let new_fundec = { f with slocals = new_locals} in 
        handle wv f.svar [(GFun(new_fundec,l))] []
    | _ -> DoChildren
  end
end 

(**********************************************************************
 * STAGE 1
 *
 * Mark up the file with user-given information about what to keep and
 * what to drop.
 **********************************************************************)
type mark = Wanted | Unwanted | Unspecified
(* Given a cil file and a list of strings, mark all of the given ASTSlicer
 * points as wanted or unwanted. *)
let mark_file (f : Cil.file) (names : (string, mark) Hashtbl.t) = 
  let ws = Hashtbl.create 32767 in
  let wi = Hashtbl.create 32767 in
  let wt = Hashtbl.create 32767 in
  let wc = Hashtbl.create 32767 in
  let we = Hashtbl.create 32767 in
  let wv = Hashtbl.create 32767 in
  if !debug then Printf.printf "Applying user marks to file ...\n" ; 
  let descend base i =
    let res = (Printf.sprintf "%s.%d" base !i),(ref 0) in
    res
  in 
  let check base i (default : mark) =
    let str = Printf.sprintf "%s.%d" base !i in
    if !debug then Printf.printf "Looking for [%s]\n" str ; 
    try Hashtbl.find names str
    with _ -> default
  in 
  let mark ht stmt wanted = match wanted with
    Unwanted -> Hashtbl.replace ht stmt false
  | Wanted -> Hashtbl.replace ht stmt true
  | Unspecified -> () 
  in 
  let rec doBlock b base i default =
    doStmtList b.bstmts base i default
  and doStmtList sl base i default = 
    List.iter (fun s -> match s.skind with
    | Instr(il) -> doIL il base i default
    | Return(_,_) 
    | Goto(_,_) 
    | Continue(_) 
    | Break(_) -> 
        mark ws s (check base i default) ; incr i 
    | If(e,b1,b2,_) -> 
        let inside = check base i default in 
        mark ws s inside ;
        let base',i' = descend base i in
        doBlock b1 base' i' inside ;
        let base'',i'' = descend base i in
        doBlock b2 base'' i'' inside ;
        incr i
    | Switch(_,b,_,_) 
(*
    | Loop(b,_,_,_) 
*)
    | While(_,b,_)
    | DoWhile(_,b,_)
    | For(_,_,_,b,_)
    | Block(b) -> 
        let inside = check base i default in 
        mark ws s inside ;
        let base',i' = descend base i in
        doBlock b base' i' inside ;
        incr i 
    | TryExcept _ | TryFinally _ -> 
        E.s (E.unimp "astslicer: mark")
    ) sl 
  and doIL il base i default = 
    List.iter (fun ins -> mark wi ins (check base i default) ; incr i) il 
  in 
  let doGlobal g = match g with 
  | GFun(fd,_) -> 
      let cur = ref 0 in 
      if Hashtbl.mem names fd.svar.vname then begin
        if Hashtbl.find names fd.svar.vname = Wanted then begin
          Hashtbl.replace wv fd.svar true ;
          doBlock fd.sbody fd.svar.vname cur (Wanted); 
        end else begin
          Hashtbl.replace wv fd.svar false ;
          doBlock fd.sbody fd.svar.vname cur (Unspecified); 
        end
      end else begin  
        doBlock fd.sbody fd.svar.vname cur (Unspecified); 
      end 
  | _ -> () 
  in
  List.iter doGlobal f.globals ;
  if !debug then begin 
    Hashtbl.iter (fun k v -> 
      ignore (Pretty.printf "want-s %b %a\n" v d_stmt k)) ws ;
    Hashtbl.iter (fun k v -> 
      ignore (Pretty.printf "want-i %b %a\n" v d_instr k)) wi ;
    Hashtbl.iter (fun k v -> 
      ignore (Pretty.printf "want-v %b %s\n" v k.vname)) wv ;
  end ; 
  (*
   * Now repeatedly mark all other things that must be kept. 
   *)
  let visitor = (new transVisitor ws wi wt wc we wv) in 
  finished := false ;
  if !debug then  (Printf.printf "\nPerforming Transitive Closure\n\n" ); 
  while not !finished do
    finished := true ; 
    visitCilFileSameGlobals visitor f
  done  ;
  if !debug then begin 
    Hashtbl.iter (fun k v -> 
      if v then ignore (Pretty.printf "want-s %a\n" d_stmt k)) ws ;
    Hashtbl.iter (fun k v -> 
      if v then ignore (Pretty.printf "want-i %a\n" d_instr k)) wi ;
    Hashtbl.iter (fun k v -> 
      if v then ignore (Pretty.printf "want-t %s\n" k.tname)) wt ;
    Hashtbl.iter (fun k v -> 
      if v then ignore (Pretty.printf "want-c %s\n" k.cname)) wc ;
    Hashtbl.iter (fun k v -> 
      if v then ignore (Pretty.printf "want-e %s\n" k.ename)) we ;
    Hashtbl.iter (fun k v -> 
      if v then ignore (Pretty.printf "want-v %s\n" k.vname)) wv ;
  end ; 

  (*
   * Now drop everything we didn't need. 
   *)
  if !debug then  (Printf.printf "Dropping Unwanted Elements\n" ); 
  let visitor = (new dropVisitor ws wi wt wc we wv) in 
  visitCilFile visitor f 
