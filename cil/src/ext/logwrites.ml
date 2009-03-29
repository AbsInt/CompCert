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

open Pretty
open Cil
module E = Errormsg
module H = Hashtbl

(* David Park at Stanford points out that you cannot take the address of a
 * bitfield in GCC. *)

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
let addr_of_lv (lh,lo) = 
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
  end else (AddrOf (lh,lo)) 

class logWriteVisitor = object
  inherit nopCilVisitor
  (* Create a prototype for the logging function, but don't put it in the 
   * file *)
  val printfFun =   
    let fdec = emptyFunction "syslog" in
    fdec.svar.vtype <- TFun(intType, 
                            Some [ ("prio", intType, []);
                                   ("format", charConstPtrType, []) ], 
                            true, []);
    fdec

  method vinst (i: instr) : instr list visitAction = 
    match i with 
      Set(lv, e, l) -> begin
        (* Check if we need to log *)
        match lv with 
          (Var(v), off) when not v.vglob -> SkipChildren
        | _ -> let str = Pretty.sprint 80 
                (Pretty.dprintf "Write %%p to 0x%%08x at %%s:%%d (%a)\n" d_lval lv)
              in 
              ChangeTo 
              [ Call((None), (Lval(Var(printfFun.svar),NoOffset)), 
                     [ one ; 
                       mkString str ; e ; addr_of_lv lv; 
                       mkString l.file; 
                       integer l.line], locUnknown);
              i]
      end 
    | Call(Some lv, f, args, l) -> begin
        (* Check if we need to log *)
        match lv with 
          (Var(v), off) when not v.vglob -> SkipChildren
        | _ -> let str = Pretty.sprint 80 
                (Pretty.dprintf "Write retval to 0x%%08x at %%s:%%d (%a)\n" d_lval lv)
              in 
              ChangeTo 
              [ Call((None), (Lval(Var(printfFun.svar),NoOffset)), 
                     [ one ; 
                       mkString str ; AddrOf lv; 
                       mkString l.file; 
                       integer l.line], locUnknown);
              i]
      end 
    | _ -> SkipChildren

end

let feature : featureDescr = 
  { fd_name = "logwrites";
    fd_enabled = Cilutil.logWrites;
    fd_description = "generation of code to log memory writes";
    fd_extraopt = [];
    fd_doit = 
    (function (f: file) -> 
      let lwVisitor = new logWriteVisitor in
      visitCilFileSameGlobals lwVisitor f);
    fd_post_check = true;
  } 

