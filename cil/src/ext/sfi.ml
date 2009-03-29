(*
 *
 * Copyright (c) 2005, 
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

(** This is a module that inserts runtime checks for memory reads/writes and 
 * allocations *)

open Pretty
open Cil
module E = Errormsg
module H = Hashtbl

let doSfi = ref false
let doSfiReads = ref false
let doSfiWrites = ref true

(* A number of functions to be skipped *)
let skipFunctions : (string, unit) H.t = H.create 13
let mustSfiFunction (f: fundec) : bool = 
  not (H.mem skipFunctions f.svar.vname)

(** Some functions are known to be allocators *)
type dataLocation = 
    InResult  (* Interesting data is in the return value *)
  | InArg of int (* in the nth argument. Starts from 1. *)
  | InArgTimesArg of int * int (* (for size) data is the product of two 
                                * arguments *)
  | PointedToByArg of int (* pointed to by nth argument *)

(** Compute the data based on the location and the actual argument list *)
let extractData (dl: dataLocation) (args: exp list) (res: lval option) : exp = 
  let getArg (n: int) = 
    try List.nth args (n - 1) (* Args are based at 1 *)
    with _ -> E.s (E.bug "Cannot extract argument %d at %a" 
                     n d_loc !currentLoc)
  in
  match dl with 
    InResult -> begin
      match res with 
        None -> 
          E.s (E.bug "Cannot extract InResult data (at %a)" d_loc !currentLoc)
      | Some r -> Lval r
    end
  | InArg n -> getArg n
  | InArgTimesArg (n1, n2) -> 
      let a1 = getArg n1 in
      let a2 = getArg n2 in 
      BinOp(Mult, mkCast ~e:a1 ~newt:longType, 
            mkCast ~e:a2 ~newt:longType, longType)
  | PointedToByArg n -> 
      let a = getArg n in 
      Lval (mkMem a NoOffset)
      


(* for each allocator, where is the length and where is the result *)
let allocators: (string, (dataLocation * dataLocation)) H.t = H.create 13
let _ = 
  H.add allocators "malloc" (InArg 1, InResult);
  H.add allocators "calloc" (InArgTimesArg (1, 2), InResult);
  H.add allocators "realloc" (InArg 2, InResult)

(* for each deallocator, where is the data being deallocated *)
let deallocators: (string, dataLocation) H.t = H.create 13
let _= 
  H.add deallocators "free" (InArg 1);
  H.add deallocators "realloc" (InArg 1)
  
(* Returns true if the given lvalue offset ends in a bitfield access. *) 
let rec is_bitfield lo = match lo with
  | NoOffset -> false
  | Field(fi,NoOffset) -> not (fi.fbitfield = None)
  | Field(_,lo) -> is_bitfield lo
  | Index(_,lo) -> is_bitfield lo 

(* Return an expression that evaluates to the address of the given lvalue.
 * For most lvalues, this is merely AddrOf(lv). However, for bitfields
 * we do some offset gymnastics. 
 *)
let addr_of_lv (lv: lval) = 
  let lh, lo = lv in 
  if is_bitfield lo then begin
    (* we figure out what the address would be without the final bitfield
     * access, and then we add in the offset of the bitfield from the
     * beginning of its enclosing comp *) 
    let rec split_offset_and_bitfield lo = match lo with 
      | NoOffset -> failwith "logwrites: impossible" 
      | Field(fi,NoOffset) -> (NoOffset,fi)
      | Field(e,lo) ->  let a,b = split_offset_and_bitfield lo in 
                        ((Field(e,a)),b)
      | Index(e,lo) ->  let a,b = split_offset_and_bitfield lo in
                        ((Index(e,a)),b)
    in 
    let new_lv_offset, bf = split_offset_and_bitfield lo in
    let new_lv = (lh, new_lv_offset) in 
    let enclosing_type = TComp(bf.fcomp, []) in 
    let bits_offset, bits_width = 
      bitsOffset enclosing_type (Field(bf,NoOffset)) in
    let bytes_offset = bits_offset / 8 in
    let lvPtr = mkCast ~e:(mkAddrOf (new_lv)) ~newt:(charPtrType) in
    (BinOp(PlusPI, lvPtr, (integer bytes_offset), ulongType))
  end else 
    (mkAddrOf (lh,lo)) 


let mustLogLval (forwrite: bool) (lv: lval) : bool = 
  match lv with
    Var v, off -> (* Inside a variable. We assume the array offsets are fine *)
      false
  | Mem e, off -> 
      if forwrite && not !doSfiWrites then 
        false
      else if not forwrite && not !doSfiReads then 
        false

      (* If this is an lval of function type, we do not log it *) 
      else if isFunctionType (typeOfLval lv) then 
        false
      else 
        true

(* Create prototypes for the logging functions *)
let mkProto (name: string) (args: (string * typ * attributes) list) = 
  let fdec = emptyFunction name in
  fdec.svar.vtype <- TFun(voidType, 
                          Some args, false, []);
  fdec
  

let logReads = mkProto "logRead" [ ("addr", voidPtrType, []);
                                   ("what", charPtrType, []);
                                   ("file", charPtrType, []);
                                   ("line", intType, []) ]
let callLogRead (lv: lval) = 
  let what = Pretty.sprint 80 (d_lval () lv) in
  Call(None, 
       Lval(Var(logReads.svar),NoOffset), 
       [ addr_of_lv lv; mkString what; mkString !currentLoc.file;
         integer !currentLoc.line], !currentLoc )

let logWrites = mkProto "logWrite" [ ("addr", voidPtrType, []);
                                     ("what", charPtrType, []);
                                     ("file", charPtrType, []);
                                     ("line", intType, []) ]
let callLogWrite (lv: lval) = 
  let what = Pretty.sprint 80 (d_lval () lv) in
  Call(None, 
       Lval(Var(logWrites.svar), NoOffset), 
       [ addr_of_lv lv; mkString what; mkString !currentLoc.file;
         integer !currentLoc.line], !currentLoc )

let logStackFrame  = mkProto "logStackFrame" [ ("func", charPtrType, []) ]
let callLogStack (fname: string) = 
  Call(None, 
       Lval(Var(logStackFrame.svar), NoOffset), 
       [ mkString fname; ], !currentLoc )

let logAlloc = mkProto "logAlloc" [ ("addr", voidPtrType, []);
                                    ("size", intType, []);
                                    ("file", charPtrType, []);
                                    ("line", intType, []) ]
let callLogAlloc (szloc: dataLocation) 
                 (resLoc: dataLocation) 
                 (args: exp list) 
                 (res: lval option) = 
  let sz = extractData szloc args res in 
  let res = extractData resLoc args res in 
  Call(None, 
       Lval(Var(logAlloc.svar), NoOffset), 
       [ res; sz; mkString !currentLoc.file;
         integer !currentLoc.line ], !currentLoc )
    
  
let logFree = mkProto "logFree" [ ("addr", voidPtrType, []);
                                  ("file", charPtrType, []);
                                  ("line", intType, []) ]
let callLogFree  (dataloc: dataLocation) 
                 (args: exp list) 
                 (res: lval option) = 
  let data = extractData dataloc args res in 
  Call(None, 
       Lval(Var(logFree.svar), NoOffset), 
       [ data; mkString !currentLoc.file;
         integer !currentLoc.line ], !currentLoc )

class sfiVisitorClass : Cil.cilVisitor = object (self)
  inherit nopCilVisitor
      
  method vexpr (e: exp) : exp visitAction = 
    match e with 
      Lval lv when mustLogLval false lv -> (* A read *)
        self#queueInstr [ callLogRead lv ];
        DoChildren

    | _ -> DoChildren
        
    
  method vinst (i: instr) : instr list visitAction = 
    match i with 
      Set(lv, e, l) when mustLogLval true lv ->
        self#queueInstr [ callLogWrite lv ];
        DoChildren

    | Call(lvo, f, args, l) -> 
        (* Instrument the write *)
        (match lvo with 
          Some lv when mustLogLval true lv -> 
            self#queueInstr [ callLogWrite lv ]
        | _ -> ());
        (* Do the expressions in the call, and then see if we need to 
         * instrument the function call *)
        ChangeDoChildrenPost
          ([i], 
           (fun il -> 
             currentLoc := l;
             match f with 
               Lval (Var fv, NoOffset) -> begin 
                 (* Is it an allocator? *)
                 try 
                   let szloc, resloc = H.find allocators fv.vname in
                   il @ [callLogAlloc szloc resloc args lvo]
                 with Not_found -> begin
                   (* Is it a deallocator? *)
                   try 
                     let resloc = H.find deallocators fv.vname in 
                     il @ [ callLogFree resloc args lvo ]
                   with Not_found -> 
                     il
                 end
               end
             | _ -> il))

    | _ -> DoChildren

  method vfunc (fdec: fundec) = 
    (* Instead a stack log at the start of a function *)
    ChangeDoChildrenPost 
      (fdec,
       fun fdec -> 
         fdec.sbody <- 
           mkBlock 
             [ mkStmtOneInstr (callLogStack fdec.svar.vname);
               mkStmt (Block fdec.sbody) ];
         fdec)
      
end

let doit (f: file) =
  let sfiVisitor = new sfiVisitorClass in
  let compileLoc (l: location) = function
      ACons("inres", []) -> InResult
    | ACons("inarg", [AInt n]) -> InArg n
    | ACons("inargxarg", [AInt n1; AInt n2]) -> InArgTimesArg (n1, n2)
    | ACons("pointedby", [AInt n]) -> PointedToByArg n
    | _ -> E.warn "Invalid location at %a" d_loc l;
        InResult
  in
  iterGlobals f
    (fun glob -> 
      match glob with 
        GFun(fdec, _) when mustSfiFunction fdec -> 
          ignore (visitCilFunction sfiVisitor fdec)
      | GPragma(Attr("sfiignore", al), l) -> 
          List.iter 
            (function AStr fn -> H.add skipFunctions fn ()
              | _ -> E.warn "Invalid argument in \"sfiignore\" pragma at %a"
                            d_loc l)
            al

      | GPragma(Attr("sfialloc", al), l) -> begin
          match al with 
            AStr fname :: locsz :: locres :: [] -> 
              H.add allocators fname (compileLoc l locsz, compileLoc l locres)
          | _ -> E.warn "Invalid sfialloc pragma at %a" d_loc l
      end
                
      | GPragma(Attr("sfifree", al), l) -> begin
          match al with 
            AStr fname :: locwhat :: [] -> 
              H.add deallocators fname (compileLoc l locwhat)
          | _ -> E.warn "Invalid sfifree pragma at %a" d_loc l
      end
                

      | _ -> ());
  (* Now add the prototypes for the instrumentation functions *)
  f.globals <-
    GVarDecl (logReads.svar, locUnknown) ::
    GVarDecl (logWrites.svar, locUnknown) ::
    GVarDecl (logStackFrame.svar, locUnknown) ::
    GVarDecl (logAlloc.svar, locUnknown) :: 
    GVarDecl (logFree.svar, locUnknown) :: f.globals


let feature : featureDescr = 
  { fd_name = "sfi";
    fd_enabled = doSfi;
    fd_description = "instrument memory operations";
    fd_extraopt = [
    "--sfireads", Arg.Set doSfiReads, "SFI for reads";
    "--sfiwrites", Arg.Set doSfiWrites, "SFI for writes";
    ];
    fd_doit = doit;
    fd_post_check = true;
  } 

