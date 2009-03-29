(* callgraph.ml *)
(* code for callgraph.mli *)

(* see copyright notice at end of this file *)

open Cil
open Trace
open Printf
module P = Pretty
module IH = Inthash
module H = Hashtbl
module E = Errormsg

(* ------------------- interface ------------------- *)
(* a call node describes the local calling structure for a
 * single function: which functions it calls, and which
 * functions call it *)
type callnode = {
  (* An id *)
  cnid: int;
  
  (* the function this node describes *)
  cnInfo: nodeinfo;

  (* set of functions this one calls, indexed by the node id *)
  cnCallees: callnode IH.t;

  (* set of functions that call this one , indexed by the node id *)
  cnCallers: callnode IH.t;
}

and nodeinfo = 
    NIVar of varinfo * bool ref 
                         (* Node corresponding to a function. If the boolean 
                          * is true, then the function is defined, otherwise 
                          * it is external *)

  | NIIndirect of string (* Indirect nodes have a string associated to them. 
                          * These strings must be invalid function names *)
               * varinfo list ref 
                         (* A list of functions that this indirect node might 
                          * denote *)

let nodeName (n: nodeinfo) : string =
  match n with
    NIVar (v, _) -> v.vname
  | NIIndirect (n, _) -> n

(* a call graph is a hashtable, mapping a function name to
 * the node which describes that function's call structure *)
type callgraph = 
  (string, callnode) Hashtbl.t

(* given the name of a function, retrieve its callnode; this will create a 
 * node if one doesn't already exist. Will use the given nodeinfo only when 
 * creating nodes. *)
let nodeId = ref 0
let getNodeByName (cg: callgraph) (ni: nodeinfo) : callnode =
  let name = nodeName ni in
  try
    H.find cg name
  with Not_found -> (
    (* make a new node *)
    let ret:callnode = {
      cnInfo = ni;
      cnid   = !nodeId;
      cnCallees = IH.create 5;
      cnCallers = IH.create 5;
    }  
    in
    incr nodeId;
    (* add it to the table, then return it *)
    H.add cg name ret;
    ret
   )

(* Get the node for a variable *)
let getNodeForVar (cg: callgraph) (v: varinfo) : callnode = 
  getNodeByName cg (NIVar (v, ref false))

let getNodeForIndirect (cg: callgraph) (e: exp) : callnode = 
  getNodeByName cg (NIIndirect ("<indirect>", ref []))


(* Find the name of an indirect node that a function whose address is taken 
 * belongs *)
let markFunctionAddrTaken (cg: callgraph) (f: varinfo) : unit = 
  (*
  ignore (E.log "markFunctionAddrTaken %s\n" f.vname);
   *)
  let n = getNodeForIndirect cg (AddrOf (Var f, NoOffset)) in 
  match n.cnInfo with 
    NIIndirect (_, r) -> r := f :: !r
  | _ -> assert false



class cgComputer (graph: callgraph) = object(self)
  inherit nopCilVisitor

  (* the current function we're in, so when we visit a call node
   * we know who is the caller *)
  val mutable curFunc: callnode option = None


  (* begin visiting a function definition *)
  method vfunc (f:fundec) : fundec visitAction = begin 
    (trace "callgraph" (P.dprintf "entering function %s\n" f.svar.vname));
   let node =  getNodeForVar graph f.svar in 
   (match node.cnInfo with 
     NIVar (v, r) -> r := true
   | _ -> assert false);
   curFunc <- (Some node);
   DoChildren
  end

  (* visit an instruction; we're only interested in calls *)
  method vinst (i:instr) : instr list visitAction = begin 
    (*(trace "callgraph" (P.dprintf "visiting instruction: %a\n" dn_instr i));*)
    let caller : callnode = 
      match curFunc with 
        None -> assert false
      | Some c -> c
    in
    let callerName: string = nodeName caller.cnInfo in
    (match i with
      Call(_,f,_,_) -> (
        let callee: callnode = 
          match f with 
          | Lval(Var(vi),NoOffset) -> 
              (trace "callgraph" (P.dprintf "I see a call by %s to %s\n"
                                    callerName vi.vname));
              getNodeForVar graph vi

          | _ -> 
              (trace "callgraph" (P.dprintf "indirect call: %a\n"
                                  dn_instr i));
              getNodeForIndirect graph f
        in
        
        (* add one entry to each node's appropriate list *)
        IH.replace caller.cnCallees callee.cnid callee;
        IH.replace callee.cnCallers caller.cnid caller
       )    

    | _ -> ());     (* ignore other kinds instructions *)

    DoChildren
  end
      
  method vexpr (e: exp) = 
    (match e with 
      AddrOf (Var fv, NoOffset) when isFunctionType fv.vtype -> 
        markFunctionAddrTaken graph fv
    | _ -> ());
    
    DoChildren
end

let computeGraph (f:file) : callgraph = begin
  let graph = H.create 37 in 
  let obj:cgComputer = new cgComputer graph in

  (* visit the whole file, computing the graph *)
  visitCilFileSameGlobals (obj :> cilVisitor) f;


  (* return the computed graph *)
  graph
end
    
let printGraph (out:out_channel) (g:callgraph) : unit = begin 
  let printEntry _ (n:callnode) : unit =
    let name = nodeName n.cnInfo in
    (Printf.fprintf out " %s" name) 
  in
  
  let printCalls (node:callnode) : unit =
    (fprintf out "  calls:");
    (IH.iter printEntry node.cnCallees);
    (fprintf out "\n  is called by:");
    (IH.iter printEntry node.cnCallers);
    (fprintf out "\n")
  in
  
  H.iter (fun (name: string) (node: callnode) -> 
    match node.cnInfo with 
      NIVar (v, def) -> 
        (fprintf out "%s (%s):\n" 
           v.vname (if !def then "defined" else "external"));
        printCalls node

    | NIIndirect (n, funcs) -> 
        fprintf out "Indirect %s:\n" n;
        fprintf out "   possible aliases: ";
        List.iter (fun a -> fprintf out "%s " a.vname) !funcs;
        fprintf out "\n"

         )

    g
  end
    
let doCallGraph = ref false

let feature : featureDescr = 
  { fd_name = "callgraph";
    fd_enabled = doCallGraph;
    fd_description = "generation of a static call graph";
    fd_extraopt = [];
    fd_doit = 
    (function (f: file) -> 
      let graph:callgraph = computeGraph f in
      printGraph stdout graph);
    fd_post_check = false;
  } 


(*
 *
 * Copyright (c) 2001-2002 by
 *  George C. Necula	necula@cs.berkeley.edu
 *  Scott McPeak        smcpeak@cs.berkeley.edu
 *  Wes Weimer          weimer@cs.berkeley.edu
 *  Ben Liblit          liblit@cs.berkeley.edu
 *
 * All rights reserved.  Permission to use, copy, modify and distribute
 * this software for research purposes only is hereby granted, 
 * provided that the following conditions are met: 
 * 1. XSRedistributions of source code must retain the above copyright notice, 
 * this list of conditions and the following disclaimer. 
 * 2. Redistributions in binary form must reproduce the above copyright notice, 
 * this list of conditions and the following disclaimer in the documentation 
 * and/or other materials provided with the distribution. 
 * 3. The name of the authors may not be used to endorse or promote products 
 * derived from  this software without specific prior written permission. 
 *
 * DISCLAIMER:
 * THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS OR 
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES 
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. 
 * IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY DIRECT, INDIRECT, 
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, 
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS 
 * OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON 
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT 
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF 
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)
