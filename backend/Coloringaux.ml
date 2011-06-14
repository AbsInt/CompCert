(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Camlcoq
open Datatypes
open BinPos
open BinInt
open AST
open Maps
open Registers
open Machregs
open Locations
open RTL
open RTLtyping
open InterfGraph
open Conventions1
open Conventions

(* George-Appel graph coloring *)

(* \subsection{Internal representation of the interference graph} *)

(* To implement George-Appel coloring, we first transform the representation
   of the interference graph, switching to the following 
   imperative representation that is well suited to the coloring algorithm. *)

(* Each node of the graph (i.e. each pseudo-register) is represented as
   follows. *)

type node =
  { ident: int;                         (*r unique identifier *)
    typ: typ;                           (*r its type *)
    regname: reg option;                (*r the RTL register it comes from *)
    regclass: int;                      (*r identifier of register class *)
    mutable accesses: int;              (*r number of defs and uses *)
    mutable spillcost: float;           (*r estimated cost of spilling *)
    mutable adjlist: node list;         (*r all nodes it interferes with *)
    mutable degree: int;                (*r number of adjacent nodes *)
    mutable movelist: move list;        (*r list of moves it is involved in *)
    mutable alias: node option;         (*r [Some n] if coalesced with [n] *)
    mutable color: loc option;          (*r chosen color *)
    mutable nstate: nodestate;          (*r in which set of nodes it is *)
    mutable nprev: node;                (*r for double linking *)
    mutable nnext: node                 (*r for double linking *)
  }

(* These are the possible states for nodes. *)

and nodestate =
  | Colored
  | Initial
  | SimplifyWorklist
  | FreezeWorklist
  | SpillWorklist
  | CoalescedNodes
  | SelectStack

(* Each move (i.e. wish to be put in the same location) is represented
   as follows. *)

and move =
  { src: node;                          (*r source of the move *)
    dst: node;                          (*r destination of the move *)
    mutable mstate: movestate;          (*r in which set of moves it is *)
    mutable mprev: move;                (*r for double linking *)
    mutable mnext: move                 (*r for double linking *)
  }

(* These are the possible states for moves *)

and movestate =
  | CoalescedMoves
  | ConstrainedMoves
  | FrozenMoves
  | WorklistMoves
  | ActiveMoves

(*i
let name_of_node n =
  match n.color, n.regname with
  | Some(R r), _ ->
      begin match Machregsaux.name_of_register r with
                | None -> "fixed-reg"
                | Some s -> s
      end
  | Some(S _), _ -> "fixed-slot"
  | None, Some r -> Printf.sprintf "x%ld" (camlint_of_positive r)
  | None, None   -> "unknown-reg"
*)

(* The algorithm manipulates partitions of the nodes and of the moves
   according to their states, frequently moving a node or a move from
   a state to another, and frequently enumerating all nodes or all moves
   of a given state.  To support these operations efficiently,
   nodes or moves having the same state are put into imperative doubly-linked
   lists, allowing for constant-time insertion and removal, and linear-time
   scanning.  We now define the operations over these doubly-linked lists. *)

module DLinkNode = struct
  type t = node
  let make state =
    let rec empty =
      { ident = 0; typ = Tint; regname = None; regclass = 0;
        adjlist = []; degree = 0; accesses = 0; spillcost = 0.0;
        movelist = []; alias = None; color = None;
        nstate = state; nprev = empty; nnext = empty }
    in empty
  let dummy = make Colored
  let clear dl = dl.nnext <- dl; dl.nprev <- dl
  let notempty dl = dl.nnext != dl
  let insert n dl =
    n.nstate <- dl.nstate;
    n.nnext <- dl.nnext; n.nprev <- dl;
    dl.nnext.nprev <- n; dl.nnext <- n
  let remove n dl =
    assert (n.nstate = dl.nstate);
    n.nnext.nprev <- n.nprev; n.nprev.nnext <- n.nnext
  let move n dl1 dl2 =
    remove n dl1; insert n dl2
  let pick dl =
    let n = dl.nnext in remove n dl; n
  let iter f dl =
    let rec iter n = if n != dl then (f n; iter n.nnext)
    in iter dl.nnext
  let fold f dl accu =
    let rec fold n accu = if n == dl then accu else fold n.nnext (f n accu)
    in fold dl.nnext accu
end

module DLinkMove = struct
  type t = move
  let make state =
    let rec empty =
      { src = DLinkNode.dummy; dst = DLinkNode.dummy; 
        mstate = state; mprev = empty; mnext = empty }
    in empty
  let dummy = make CoalescedMoves
  let clear dl = dl.mnext <- dl; dl.mprev <- dl
  let notempty dl = dl.mnext != dl
  let insert m dl =
    m.mstate <- dl.mstate;
    m.mnext <- dl.mnext; m.mprev <- dl;
    dl.mnext.mprev <- m; dl.mnext <- m
  let remove m dl =
    assert (m.mstate = dl.mstate);
    m.mnext.mprev <- m.mprev; m.mprev.mnext <- m.mnext
  let move m dl1 dl2 =
    remove m dl1; insert m dl2
  let pick dl =
    let m = dl.mnext in remove m dl; m
  let iter f dl =
    let rec iter m = if m != dl then (f m; iter m.mnext)
    in iter dl.mnext
  let fold f dl accu =
    let rec fold m accu = if m == dl then accu else fold m.mnext (f m accu)
    in fold dl.mnext accu
end

(* Auxiliary data structures *)

module IntSet = Set.Make(struct
  type t = int
  let compare (x:int) (y:int) = compare x y
end)

module IntPairSet = Set.Make(struct
  type t = int * int
  let compare ((x1, y1): (int * int)) (x2, y2) =
    if x1 < x2 then -1 else
    if x1 > x2 then 1 else
    if y1 < y2 then -1 else
    if y1 > y2 then 1 else
    0
  end)

(* Register classes *)

let class_of_type = function Tint -> 0 | Tfloat -> 1

let num_register_classes = 2

let caller_save_registers = Array.make num_register_classes [||]

let callee_save_registers = Array.make num_register_classes [||]

let num_available_registers = Array.make num_register_classes 0

let reserved_registers = ref ([]: mreg list)

let allocatable_registers = ref ([]: mreg list)

let rec remove_reserved = function
  | [] -> []
  | hd :: tl ->
      if List.mem hd !reserved_registers
      then remove_reserved tl
      else hd :: remove_reserved tl

let init_regs() =
  let int_caller_save = remove_reserved int_caller_save_regs
  and float_caller_save = remove_reserved float_caller_save_regs
  and int_callee_save = remove_reserved int_callee_save_regs
  and float_callee_save = remove_reserved float_callee_save_regs in
  allocatable_registers :=
    List.flatten [int_caller_save; float_caller_save;
                  int_callee_save; float_callee_save];
  caller_save_registers.(0) <- Array.of_list int_caller_save;
  caller_save_registers.(1) <- Array.of_list float_caller_save;
  callee_save_registers.(0) <- Array.of_list int_callee_save;
  callee_save_registers.(1) <- Array.of_list float_callee_save;
  for i = 0 to num_register_classes - 1 do
    num_available_registers.(i) <-
      Array.length caller_save_registers.(i)
      + Array.length callee_save_registers.(i)
  done

(* \subsection{The George-Appel algorithm} *)

(* Below is a straigthforward translation of the pseudo-code at the end
   of the TOPLAS article by George and Appel.  Two bugs were fixed
   and are marked as such.  Please refer to the article for explanations. *)

(* The adjacency set  *)
let adjSet = ref IntPairSet.empty

(* Low-degree, non-move-related nodes *)
let simplifyWorklist = DLinkNode.make SimplifyWorklist

(* Low-degree, move-related nodes *)
let freezeWorklist = DLinkNode.make FreezeWorklist

(* High-degree nodes *)
let spillWorklist = DLinkNode.make SpillWorklist

(* Nodes that have been coalesced *)
let coalescedNodes = DLinkNode.make CoalescedNodes

(* Moves that have been coalesced *)
let coalescedMoves = DLinkMove.make CoalescedMoves

(* Moves whose source and destination interfere *)
let constrainedMoves = DLinkMove.make ConstrainedMoves

(* Moves that will no longer be considered for coalescing *)
let frozenMoves = DLinkMove.make FrozenMoves

(* Moves enabled for possible coalescing *)
let worklistMoves = DLinkMove.make WorklistMoves

(* Moves not yet ready for coalescing *)
let activeMoves = DLinkMove.make ActiveMoves

(* To generate node identifiers *)
let nextRegIdent = ref 0

(* Initialization of all global data structures *)

let init_graph() =
  adjSet := IntPairSet.empty;
  nextRegIdent := 0;
  DLinkNode.clear simplifyWorklist;
  DLinkNode.clear freezeWorklist;
  DLinkNode.clear spillWorklist;
  DLinkNode.clear coalescedNodes;
  DLinkMove.clear coalescedMoves;
  DLinkMove.clear frozenMoves;
  DLinkMove.clear worklistMoves;
  DLinkMove.clear activeMoves

(* Determine if two nodes interfere *)

let interfere n1 n2 =
  let i1 = n1.ident and i2 = n2.ident in
  let p = if i1 < i2 then (i1, i2) else (i2, i1) in
  IntPairSet.mem p !adjSet

(* Add an edge to the graph.  Assume edge is not in graph already *)

let addEdge n1 n2 =
  (*i  Printf.printf "  %s -- %s;\n" (name_of_node n1) (name_of_node n2); *)
  assert (n1 != n2 && not (interfere n1 n2));
  let i1 = n1.ident and i2 = n2.ident in
  let p = if i1 < i2 then (i1, i2) else (i2, i1) in
  adjSet := IntPairSet.add p !adjSet;
  if n1.nstate <> Colored then begin
    n1.adjlist <- n2 :: n1.adjlist;
    n1.degree  <- 1 + n1.degree
  end;
  if n2.nstate <> Colored then begin
    n2.adjlist <- n1 :: n2.adjlist;
    n2.degree  <- 1 + n2.degree
  end

(* Apply the given function to the relevant adjacent nodes of a node *)

let iterAdjacent f n =
  List.iter
    (fun n ->
      match n.nstate with
      | SelectStack | CoalescedNodes -> ()
      | _ -> f n)
    n.adjlist

(* Determine the moves affecting a node *)

let moveIsActiveOrWorklist m =
  match m.mstate with
  | ActiveMoves | WorklistMoves -> true
  | _ -> false

let nodeMoves n =
  List.filter moveIsActiveOrWorklist n.movelist

(* Determine whether a node is involved in a move *)

let moveRelated n =
  List.exists moveIsActiveOrWorklist n.movelist

(*i
(* Check invariants *)

let name_of_node n = string_of_int n.ident

let degreeInvariant n =
  let c = ref 0 in
  iterAdjacent (fun n -> incr c) n;
  if !c <> n.degree then
    failwith("degree invariant violated by " ^ name_of_node n)

let simplifyWorklistInvariant n =
  if n.degree < num_available_registers.(n.regclass)
  && not (moveRelated n)
  then ()
  else failwith("simplify worklist invariant violated by " ^ name_of_node n)

let freezeWorklistInvariant n =
  if n.degree < num_available_registers.(n.regclass)
  && moveRelated n
  then ()
  else failwith("freeze worklist invariant violated by " ^ name_of_node n)

let spillWorklistInvariant n =
  if n.degree >= num_available_registers.(n.regclass)
  then ()
  else failwith("spill worklist invariant violated by " ^ name_of_node n)

let checkInvariants () =
  DLinkNode.iter
    (fun n -> degreeInvariant n; simplifyWorklistInvariant n)
    simplifyWorklist;
  DLinkNode.iter
    (fun n -> degreeInvariant n; freezeWorklistInvariant n)
    freezeWorklist;
  DLinkNode.iter
    (fun n -> degreeInvariant n; spillWorklistInvariant n)
    spillWorklist
*)

(* Build the internal representation of the graph *)

let nodeOfReg r typenv spillcosts =
  let ty = typenv r in
  incr nextRegIdent;
  let (acc, cost) = spillcosts r in
  { ident = !nextRegIdent; typ = ty; 
    regname = Some r; regclass = class_of_type ty;
    accesses = acc; spillcost = float cost;
    adjlist = []; degree = 0; movelist = []; alias = None;
    color = None;
    nstate = Initial;
    nprev = DLinkNode.dummy; nnext = DLinkNode.dummy }

let nodeOfMreg mr =
  let ty = mreg_type mr in
  incr nextRegIdent;
  { ident = !nextRegIdent; typ = ty; 
    regname = None; regclass = class_of_type ty;
    accesses = 0; spillcost = 0.0;
    adjlist = []; degree = 0; movelist = []; alias = None;
    color = Some (R mr);
    nstate = Colored;
    nprev = DLinkNode.dummy; nnext = DLinkNode.dummy }

let build g typenv spillcosts =
  (* Associate an internal node to each pseudo-register and each location *)
  let reg_mapping = Hashtbl.create 27
  and mreg_mapping = Hashtbl.create 27 in
  let find_reg_node r =
    try
      Hashtbl.find reg_mapping r
    with Not_found ->
      let n = nodeOfReg r typenv spillcosts in
      Hashtbl.add reg_mapping r n;
      n
  and find_mreg_node mr =
    try
      Hashtbl.find mreg_mapping mr
    with Not_found ->
      let n = nodeOfMreg mr in
      Hashtbl.add mreg_mapping mr n;
      n in
  (* Fill the adjacency set and the adjacency lists; compute the degrees. *)
  SetRegReg.fold
    (fun (Coq_pair(r1, r2)) () ->
      addEdge (find_reg_node r1) (find_reg_node r2))
    g.interf_reg_reg ();
  SetRegMreg.fold
    (fun (Coq_pair(r1, mr2)) () ->
      addEdge (find_reg_node r1) (find_mreg_node mr2))
    g.interf_reg_mreg ();
  (* Process the moves and insert them in worklistMoves *)
  let add_move n1 n2 =
    (*i Printf.printf "  %s -- %s [color=\"red\"];\n" (name_of_node n1) (name_of_node n2); *)
    let m =
      { src = n1; dst = n2; mstate = WorklistMoves;
        mnext = DLinkMove.dummy; mprev = DLinkMove.dummy } in
    n1.movelist <- m :: n1.movelist;
    n2.movelist <- m :: n2.movelist;
    DLinkMove.insert m worklistMoves in
  SetRegReg.fold
    (fun (Coq_pair(r1, r2)) () ->
      add_move (find_reg_node r1) (find_reg_node r2))
    g.pref_reg_reg ();
  SetRegMreg.fold
    (fun (Coq_pair(r1, mr2)) () ->
      let r1' = find_reg_node r1 in
      if List.mem mr2 !allocatable_registers then
        add_move r1' (find_mreg_node mr2))
    g.pref_reg_mreg ();
  (* Initial partition of nodes into spill / freeze / simplify *)
  Hashtbl.iter
    (fun r n ->
      assert (n.nstate = Initial);
      let k = num_available_registers.(n.regclass) in
      if n.degree >= k then
        DLinkNode.insert n spillWorklist
      else if moveRelated n then
        DLinkNode.insert n freezeWorklist
      else
        DLinkNode.insert n simplifyWorklist)
    reg_mapping;
  (* Return mapping from pseudo-registers to nodes *)
  reg_mapping

(* Enable moves that have become low-degree related *)

let enableMoves n =
  List.iter
    (fun m ->
      if m.mstate = ActiveMoves
      then DLinkMove.move m activeMoves worklistMoves)
    (nodeMoves n)

(* Simulate the removal of a node from the graph *)

let decrementDegree n =
  let k = num_available_registers.(n.regclass) in
  let d = n.degree in
  n.degree <- d - 1;
  if d = k then begin
    enableMoves n;
    iterAdjacent enableMoves n;
(*    if n.nstate <> Colored then begin *)
    if moveRelated n
    then DLinkNode.move n spillWorklist freezeWorklist
    else DLinkNode.move n spillWorklist simplifyWorklist
(*    end *)
  end

(* Simulate the effect of combining nodes [n1] and [n3] on [n2],
   where [n2] is a node adjacent to [n3]. *)

let combineEdge n1 n2 =
  assert (n1 != n2);
  if interfere n1 n2 then begin
    (* The two edges n2--n3 and n2--n1 become one, so degree of n2 decreases *)
    decrementDegree n2
  end else begin
    (* Add new edge *)
    let i1 = n1.ident and i2 = n2.ident in
    let p = if i1 < i2 then (i1, i2) else (i2, i1) in
    adjSet := IntPairSet.add p !adjSet;
    if n1.nstate <> Colored then begin
      n1.adjlist <- n2 :: n1.adjlist;
      n1.degree  <- 1 + n1.degree
    end;
    if n2.nstate <> Colored then begin
      n2.adjlist <- n1 :: n2.adjlist;
      (* n2's degree stays the same because the old edge n2--n3 disappears
         and becomes the new edge n2--n1 *)
    end
  end

(* Simplification of a low-degree node *)

let simplify () =
  let n = DLinkNode.pick simplifyWorklist in
  (*i Printf.printf "Simplifying %s\n" (name_of_node n); i*)
  n.nstate <- SelectStack;
  iterAdjacent decrementDegree n;
  n

(* Briggs's conservative coalescing criterion.  In the terminology of
   Hailperin, "Comparing Conservative Coalescing Criteria",
   TOPLAS 27(3) 2005, this is the full Briggs criterion, slightly
   more powerful than the one in George and Appel's paper. *)

let canCoalesceBriggs u v =
  let seen = ref IntSet.empty in
  let k = num_available_registers.(u.regclass) in
  let c = ref 0 in
  let consider other n =
    if not (IntSet.mem n.ident !seen) then begin
      seen := IntSet.add n.ident !seen;
      (* if n interferes with both u and v, its degree will decrease by one
         after coalescing *)
      let degree_after_coalescing =
        if interfere n other then n.degree - 1 else n.degree in
      if degree_after_coalescing >= k then begin
        incr c;
        if !c >= k then raise Exit
      end
    end in
  try
    iterAdjacent (consider v) u;
    iterAdjacent (consider u) v;
    (*i Printf.printf "  Briggs: OK\n"; *)
    true
  with Exit ->
    (*i Printf.printf "  Briggs: no\n"; *)
    false

(* George's conservative coalescing criterion: all high-degree neighbors
   of [v] are neighbors of [u]. *)

let canCoalesceGeorge u v =
  let k = num_available_registers.(u.regclass) in
  let isOK t =
    if t.nstate = Colored then
      if u.nstate = Colored || interfere t u then () else raise Exit
    else
      if t.degree < k || interfere t u then () else raise Exit
  in
  try
    iterAdjacent isOK v;
    (*i Printf.printf "  George: OK\n"; *)
    true
  with Exit ->
    (*i Printf.printf "  George: no\n"; *)
    false

(* The combined coalescing criterion.  [u] can be precolored, but
   [v] is not.  According to George and Appel's paper:
-  If [u] is precolored, use George's criterion.
-  If [u] is not precolored, use Briggs's criterion.

   As noted by Hailperin, for non-precolored nodes, George's criterion 
   is incomparable with Briggs's: there are cases where G says yes
   and B says no.  Typically, [u] is a long-lived variable with many 
   interferences, and [v] is a short-lived temporary copy of [u]
   that has no more interferences than [u].  Coalescing [u] and [v]
   is "weakly safe" in Hailperin's terminology: [u] is no harder to color,
   [u]'s neighbors are no harder to color either, but if we end up
   spilling [u], we'll spill [v] as well.  However, if [v] has at most
   one def and one use, CompCert generates equivalent code if
   both [u] and [v] are spilled and if [u] is spilled but not [v],
   so George's criterion is safe in this case.  
*)

let thresholdGeorge = 2               (* = 1 def + 1 use *)

let canCoalesce u v =
  if u.nstate = Colored
  then canCoalesceGeorge u v
  else canCoalesceBriggs u v
       || (v.accesses <= thresholdGeorge && canCoalesceGeorge u v)
       || (u.accesses <= thresholdGeorge && canCoalesceGeorge v u)

(* Update worklists after a move was processed *)

let addWorkList u =
  if (not (u.nstate = Colored))
  && u.degree < num_available_registers.(u.regclass)
  && (not (moveRelated u))
  then DLinkNode.move u freezeWorklist simplifyWorklist

(* Return the canonical representative of a possibly coalesced node *)

let rec getAlias n =
  match n.alias with None -> n | Some n' -> getAlias n'

(* Combine two nodes *)

let combine u v =
  (*i Printf.printf "Combining %s and %s\n" (name_of_node u) (name_of_node v);*)
  if v.nstate = FreezeWorklist
  then DLinkNode.move v freezeWorklist coalescedNodes
  else DLinkNode.move v spillWorklist coalescedNodes;
  v.alias <- Some u;
  u.movelist <- u.movelist @ v.movelist;
  u.spillcost <- u.spillcost +. v.spillcost;
  iterAdjacent (combineEdge u) v;  (*r original code using [decrementDegree] is buggy *)
  enableMoves v;                   (*r added as per Appel's book erratum *)
  if u.degree >= num_available_registers.(u.regclass)
  && u.nstate = FreezeWorklist
  then DLinkNode.move u freezeWorklist spillWorklist

(* Attempt coalescing *)

let coalesce () =
  let m = DLinkMove.pick worklistMoves in
  let x = getAlias m.src and y = getAlias m.dst in
  let (u, v) = if y.nstate = Colored then (y, x) else (x, y) in
  (*i Printf.printf "Attempt coalescing %s and %s\n" (name_of_node u) (name_of_node v); *)
  if u == v then begin
    DLinkMove.insert m coalescedMoves;
    addWorkList u
  end else if v.nstate = Colored || interfere u v then begin
    DLinkMove.insert m constrainedMoves;
    addWorkList u;
    addWorkList v
  end else if canCoalesce u v then begin
    DLinkMove.insert m coalescedMoves;
    combine u v;
    addWorkList u
  end else begin
    DLinkMove.insert m activeMoves    
  end

(* Freeze moves associated with node [u] *)

let freezeMoves u =
  let u' = getAlias u in
  let freeze m =
    let y = getAlias m.src in
    let v = if y == u' then getAlias m.dst else y in
    DLinkMove.move m activeMoves frozenMoves;
    if not (moveRelated v)
    && v.degree < num_available_registers.(v.regclass)
    && v.nstate <> Colored
    then DLinkNode.move v freezeWorklist simplifyWorklist in
  List.iter freeze (nodeMoves u)

(* Pick a move and freeze it *)

let freeze () =
  let u = DLinkNode.pick freezeWorklist in
  (*i  Printf.printf "Freezing %s\n" (name_of_node u);*)
  DLinkNode.insert u simplifyWorklist;
  freezeMoves u

(* Chaitin's cost measure *)

let spillCost n =
(*i
  Printf.printf "spillCost %s: uses = %.0f  degree = %d  cost = %f\n"
                (name_of_node n) n.spillcost n.degree (n.spillcost /. float n.degree);
*)
  n.spillcost /. float n.degree

(* Spill a node *)

let selectSpill () =
  (* Find a spillable node of minimal cost *)
  let (n, cost) =
    DLinkNode.fold
      (fun n (best_node, best_cost as best) ->
        let cost = spillCost n in
        if cost < best_cost then (n, cost) else best)
      spillWorklist (DLinkNode.dummy, infinity) in
  assert (n != DLinkNode.dummy);
  DLinkNode.remove n spillWorklist;
  (*i Printf.printf "Spilling %s\n" (name_of_node n);*)
  freezeMoves n;
  n.nstate <- SelectStack;
  iterAdjacent decrementDegree n;
  n

(* Produce the order of nodes that we'll use for coloring *)

let rec nodeOrder stack =
  (*i checkInvariants(); *)
  if DLinkNode.notempty simplifyWorklist then
    (let n = simplify() in nodeOrder (n :: stack))
  else if DLinkMove.notempty worklistMoves then
    (coalesce(); nodeOrder stack)
  else if DLinkNode.notempty freezeWorklist then
    (freeze(); nodeOrder stack)
  else if DLinkNode.notempty spillWorklist then
    (let n = selectSpill() in nodeOrder (n :: stack))
  else
    stack

(* Assign a color (i.e. a hardware register or a stack location)
   to a node.  The color is chosen among the colors that are not
   assigned to nodes with which this node interferes.  The choice
   is guided by the following heuristics: consider first caller-save
   hardware register of the correct type; second, callee-save registers;
   third, a stack location.  Callee-save registers and stack locations
   are ``expensive'' resources, so we try to minimize their number
   by picking the smallest available callee-save register or stack location.
   In contrast, caller-save registers are ``free'', so we pick an
   available one pseudo-randomly. *)

module Locset =
  Set.Make(struct type t = loc let compare = compare end)

let start_points = Array.make num_register_classes 0

let find_reg conflicts regclass =
  let rec find avail curr last =
    if curr >= last then None else begin
      let l = R avail.(curr) in
      if Locset.mem l conflicts
      then find avail (curr + 1) last
      else Some l
    end in
  let caller_save = caller_save_registers.(regclass)
  and callee_save = callee_save_registers.(regclass)
  and start = start_points.(regclass) in
  match find caller_save start (Array.length caller_save) with
  | Some _ as res ->
      start_points.(regclass) <-
        (if start + 1 < Array.length caller_save then start + 1 else 0);
      res
  | None ->
      match find caller_save 0 start with
      | Some _ as res ->
          start_points.(regclass) <-
            (if start + 1 < Array.length caller_save then start + 1 else 0);
          res
      | None ->
          find callee_save 0 (Array.length callee_save)

(* Aggressive coalescing of stack slots.  When assigning a slot,
   try first the slots assigned to the temporaries for which we
   have a preference, provided no conflict occurs. *)

let rec reuse_slot conflicts n mvlist =
  match mvlist with
  | [] -> None
  | mv :: rem ->
      let attempt_reuse n' =
        match n'.color with
        | Some(S _ as l) when not (Locset.mem l conflicts) -> Some l
        | _ -> reuse_slot conflicts n rem in
      let src = getAlias mv.src and dst = getAlias mv.dst in
      if n == src then attempt_reuse dst
      else if n == dst then attempt_reuse src
      else reuse_slot conflicts n rem (* should not happen? *)

(* If no reuse possible, assign lowest nonconflicting stack slot. *)

let find_slot conflicts typ =
  let rec find curr =
    let l = S(Local(curr, typ)) in
    if Locset.mem l conflicts then find (coq_Zsucc curr) else l
  in find Z0

let assign_color n =
  let conflicts = ref Locset.empty in
  List.iter
    (fun n' ->
      match (getAlias n').color with
      | None -> ()
      | Some l -> conflicts := Locset.add l !conflicts)
    n.adjlist;
  match find_reg !conflicts n.regclass with
  | Some loc ->
      n.color <- Some loc
  | None ->
      match reuse_slot !conflicts n n.movelist with
      | Some loc ->
          n.color <- Some loc
      | None ->
          n.color <- Some (find_slot !conflicts n.typ)

(* Extract the location of a node *)

let location_of_node n =
  match n.color with
  | None -> assert false
  | Some loc -> loc

(* Estimate spilling costs and counts the number of defs and uses.
   Currently, we charge 10 for each access and 1 for each move.
   To do: take loops into account. *)

let spill_costs f =
  let costs = ref (PMap.init (0,0)) in
  let cost r =
    PMap.get r !costs in
  let charge amount r =
    let (n, c) = cost r in
    costs := PMap.set r (n + 1, c + amount) !costs in
  let charge_list amount rl =
    List.iter (charge amount) rl in
  let charge_ros amount ros =
    match ros with Coq_inl r -> charge amount r | Coq_inr _ -> () in
  let process_instr () pc i =
    match i with
    | Inop _ -> ()
    | Iop(Op.Omove, arg::nil, res, _) -> charge 1 arg; charge 1 res
    | Iop(op, args, res, _) -> charge_list 10 args; charge 10 res
    | Iload(chunk, addr, args, dst, _) -> charge_list 10 args; charge 10 dst
    | Istore(chunk, addr, args, src, _) -> charge_list 10 args; charge 10 src
    | Icall(sg, ros, args, res, _) ->
        charge_ros 10 ros; charge_list 1 args; charge 1 res
    | Itailcall(sg, ros, args) ->
        charge_ros 10 ros; charge_list 1 args
    | Ibuiltin(EF_annot _, args, res, _) -> ()   (* not actually used *)
    | Ibuiltin(EF_annot_val _, args, res, _) -> charge_list 1 args; charge 1 res
    | Ibuiltin(ef, args, res, _) -> charge_list 10 args; charge 10 res
    | Icond(cond, args, _, _) -> charge_list 10 args
    | Ijumptable(arg, _) -> charge 10 arg
    | Ireturn(Some r) -> charge 1 r
    | Ireturn None -> () in
  charge_list 1 f.fn_params;
  PTree.fold process_instr f.fn_code ();
  (* Result is cost function reg -> (num accesses, integer cost *)
  cost

(* This is the entry point for graph coloring. *)

let graph_coloring (f: coq_function) (g: graph) (env: regenv) (regs: Regset.t)
                   : (reg -> loc) =
  init_regs();
  init_graph();
  Array.fill start_points 0 num_register_classes 0;
  (*i Printf.printf "graph G {\n"; *)
  let mapping = build g env (spill_costs f) in
  (*i Printf.printf "}\n"; *)
  List.iter assign_color (nodeOrder []);
  init_graph();  (* free data structures *)
  fun r ->
    try location_of_node (getAlias (Hashtbl.find mapping r))
    with Not_found -> R IT1 (* any location *)
