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
(* callgraph.mli *)
(* compute a static call graph *)

(* module maintainer: scott *)
(* see copyright notice at end of this file *)


(* ------------------ types ------------------- *)
(* a call node describes the local calling structure for a
 * single function: which functions it calls, and which
 * functions call it *)
type callnode = {
  (* An id *)
  cnid: int;
  
  (* the function this node describes *)
  cnInfo: nodeinfo;

  (* set of functions this one calls, indexed by the node id *)
  cnCallees: callnode Inthash.t;

  (* set of functions that call this one , indexed by the node id *)
  cnCallers: callnode Inthash.t;
}

and nodeinfo = 
    NIVar of Cil.varinfo * bool ref 
                         (* Node corresponding to a function. If the boolean 
                          * is true, then the function is defined, otherwise 
                          * it is external *)

  | NIIndirect of string (* Indirect nodes have a string associated to them. 
                          * These strings must be invalid function names *)
               * Cil.varinfo list ref 
                         (* A list of functions that this indirect node might 
                          * denote *)


val nodeName: nodeinfo -> string

(* a call graph is a hashtable, mapping a function name to
 * the node which describes that function's call structure *)
type callgraph =
  (string, callnode) Hashtbl.t


(* ----------------- functions ------------------- *)  
(* given a CIL file, compute its static call graph *)
val computeGraph : Cil.file -> callgraph

(* print the callgraph in a human-readable format to a channel *)
val printGraph : out_channel -> callgraph -> unit


val feature: Cil.featureDescr
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
 * 1. Redistributions of source code must retain the above copyright notice, 
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
