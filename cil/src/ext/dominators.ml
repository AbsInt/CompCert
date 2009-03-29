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

(** Compute dominator information for the statements in a function *)
open Cil
open Pretty
module E = Errormsg
module H = Hashtbl 
module U = Util
module IH = Inthash

module DF = Dataflow

let debug = false

(* For each statement we maintain a set of statements that dominate it *)
module BS = Set.Make(struct 
                        type t = Cil.stmt
                        let compare v1 v2 = Pervasives.compare v1.sid v2.sid
                     end)




(** Customization module for dominators *)
module DT = struct
  let name = "dom"

  let debug = ref debug 

  type t = BS.t

   (** For each statement in a function we keep the set of dominator blocks. 
    * Indexed by statement id *)
  let stmtStartData: t IH.t = IH.create 17

  let copy (d: t) = d

  let pretty () (d: t) = 
    dprintf "{%a}" 
      (docList (fun s -> dprintf "%d" s.sid))
      (BS.elements d)

  let computeFirstPredecessor (s: stmt) (d: BS.t) : BS.t = 
    (* Make sure we add this block to the set *)
    BS.add s d

  let combinePredecessors (s: stmt) ~(old: BS.t) (d: BS.t) : BS.t option = 
    (* First, add this block to the data from the predecessor *)
    let d' = BS.add s d in
    if BS.subset old d' then 
      None
    else
      Some (BS.inter old d')

  let doInstr (i: instr) (d: t) = DF.Default

  let doStmt (s: stmt) (d: t) = DF.SDefault
  
  let doGuard condition _ = DF.GDefault


  let filterStmt _ = true
end



module Dom = DF.ForwardsDataFlow(DT)

let getStmtDominators (data: BS.t IH.t) (s: stmt) : BS.t = 
  try IH.find data s.sid
  with Not_found -> BS.empty (* Not reachable *)
  

let getIdom (idomInfo: stmt option IH.t) (s: stmt) = 
  try IH.find idomInfo s.sid
  with Not_found -> 
    E.s (E.bug "Immediate dominator information not set for statement %d" 
           s.sid)

(** Check whether one block dominates another. This assumes that the "idom" 
 * field has been computed. *)
let rec dominates (idomInfo: stmt option IH.t) (s1: stmt) (s2: stmt) = 
  s1 == s2 || 
  (let s2idom = getIdom idomInfo s2 in
  match s2idom with 
    None -> false
  | Some s2idom -> dominates idomInfo s1 s2idom)
    



let computeIDom (f: fundec) : stmt option IH.t = 
  (* We must prepare the CFG info first *)
  prepareCFG f;
  computeCFGInfo f false;

  IH.clear DT.stmtStartData;
  let idomData: stmt option IH.t = IH.create 13 in

  let _ = 
    match f.sbody.bstmts with 
      [] -> () (* function has no body *)
    | start :: _ -> begin
        (* We start with only the start block *)
        IH.add DT.stmtStartData start.sid (BS.singleton start);
        
        Dom.compute [start];
        
        (* Dump the dominators information *)
         if debug then 
           List.iter
             (fun s -> 
               let sdoms = getStmtDominators DT.stmtStartData s in
               if not (BS.mem s sdoms) then begin
                 (* It can be that the block is not reachable *)
                 if s.preds <> [] then 
                   E.s (E.bug "Statement %d is not in its list of dominators"
                          s.sid);
               end;
               ignore (E.log "Dominators for %d: %a\n" s.sid
                         DT.pretty (BS.remove s sdoms)))
             f.sallstmts;
        
        (* Now fill the immediate dominators for all nodes *)
        let rec fillOneIdom (s: stmt) = 
          try 
            ignore (IH.find idomData s.sid)
              (* Already set *)
          with Not_found -> begin
            (* Get the dominators *)
            let sdoms = getStmtDominators DT.stmtStartData s in 
            (* Fill the idom for the dominators first *)
            let idom = 
              BS.fold 
                (fun d (sofar: stmt option) -> 
                  if d.sid = s.sid then 
                    sofar (* Ignore the block itself *)
                  else begin
                    (* fill the idom information recursively *)
                    fillOneIdom d;
                    match sofar with 
                      None -> Some d
                    | Some sofar' ->
                        (* See if d is dominated by sofar. We know that the 
                         * idom information has been computed for both sofar 
                         * and for d*)
                        if dominates idomData sofar' d then 
                          Some d
                        else
                          sofar
                  end)
                sdoms
                None
            in
            IH.replace idomData s.sid idom
          end
        in
        (* Scan all blocks and compute the idom *)
        List.iter fillOneIdom f.sallstmts
    end
  in
  idomData



(** Compute the start of the natural loops. For each start, keep a list of 
 * origin of a back edge. The loop consists of the loop start and all 
 * predecessors of the origins of back edges, up to and including the loop 
 * start *)
let findNaturalLoops (f: fundec) 
                     (idomData: stmt option IH.t) : (stmt * stmt list) list = 
  let loops = 
    List.fold_left
      (fun acc b -> 
        (* Iterate over all successors, and see if they are among the 
         * dominators for this block *)
        List.fold_left
          (fun acc s -> 
            if dominates idomData s b then 
              (* s is the start of a natural loop *)
              let rec addNaturalLoop = function
                  [] -> [(s, [b])]
                | (s', backs) :: rest when s'.sid = s.sid -> 
                    (s', b :: backs) :: rest
                | l :: rest -> l :: addNaturalLoop rest
              in
              addNaturalLoop acc
            else
              acc)
          acc
          b.succs)
      []
      f.sallstmts 
  in
  
  if debug then 
    ignore (E.log "Natural loops:\n%a\n"
              (docList ~sep:line
                 (fun (s, backs) -> 
                   dprintf "    Start: %d, backs:%a"
                     s.sid
                     (docList (fun b -> num b.sid))
                     backs))
              loops);
  
  loops
