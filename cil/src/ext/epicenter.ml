(* epicenter.ml *)
(* code for epicenter.mli *)

(* module maintainer: scott *)
(* see copyright at end of this file *)

open Callgraph
open Cil
open Trace
open Pretty
module H = Hashtbl
module IH = Inthash

let sliceFile (f:file) (epicenter:string) (maxHops:int) : unit =
  (* compute the static call graph *)
  let graph:callgraph = (computeGraph f) in

  (* will accumulate here the set of names of functions already seen *)
  let seen: (string, unit) H.t = (H.create 117) in

  (* when removing "unused" symbols, keep all seen functions *)
  let isRoot : global -> bool = function
    | GFun ({svar = {vname = vname}}, _) ->
	H.mem seen vname
    | _ ->
	false
  in

  (* recursive depth-first search through the call graph, finding
   * all nodes within 'hops' hops of 'node' and marking them to
   * to be retained *)
  let rec dfs (node:callnode) (hops:int) : unit =
    (* only recurse if we haven't already marked this node *)
    if not (H.mem seen (nodeName node.cnInfo)) then
      begin
        (* add this node *)
	H.add seen (nodeName node.cnInfo) ();
	trace "epicenter" (dprintf "will keep %s\n" (nodeName node.cnInfo));
	
        (* if we cannot do any more hops, stop *)
	if (hops > 0) then

          (* recurse on all the node's callers and callees *)
	  let recurse _ (adjacent:callnode) : unit =
	    (dfs adjacent (hops - 1)) 
          in
	  IH.iter recurse node.cnCallees;
	  IH.iter recurse node.cnCallers
      end
  in
  dfs (Hashtbl.find graph epicenter) maxHops;

  (* finally, throw away anything we haven't decided to keep *)
  Cilutil.sliceGlobal := true;
  Rmtmps.removeUnusedTemps ~isRoot:isRoot f

let doEpicenter = ref false
let epicenterName = ref ""
let epicenterHops = ref 0

let feature : featureDescr = 
  { fd_name = "epicenter";
    fd_enabled = doEpicenter;
    fd_description = "remove all functions except those within some number " ^
                     "of hops (in the call graph) from a given function";
    fd_extraopt = 
    [
    ("--epicenter-name", 
     Arg.String (fun s -> epicenterName := s),
               "<name>: do an epicenter slice starting from function <name>");
    ("--epicenter-hops", Arg.Int (fun n -> epicenterHops := n),
     "<n>: specify max # of hops for epicenter slice");
    ];

    fd_doit =
    (fun f -> 
      sliceFile f !epicenterName !epicenterHops);

    fd_post_check = true;
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
