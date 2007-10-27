open BinPos
open Coqlib
open Datatypes
open LTL
open Lattice
open CList
open Maps
open Camlcoq

(* Trivial enumeration, in decreasing order of PC *)

(***
let enumerate_aux f reach =
  positive_rec
    Coq_nil
    (fun pc nodes ->
      if PMap.get pc reach
      then Coq_cons (pc, nodes)
      else nodes) 
    f.fn_nextpc
***)

(* More clever enumeration that flattens basic blocks *)

let rec int_of_pos = function
  | Coq_xI p -> (int_of_pos p lsl 1) + 1
  | Coq_xO p -> int_of_pos p lsl 1
  | Coq_xH -> 1

(* Count the reachable predecessors for each node *)

let reachable_predecessors f reach =
  let count = Array.make (int_of_pos f.fn_nextpc) 0 in
  let increment pc =
    let i = int_of_pos pc in
    count.(i) <- count.(i) + 1 in
  positive_rec
    ()
    (fun pc _ ->
      if PMap.get pc reach then coqlist_iter increment (successors f pc))
    f.fn_nextpc;
  count

(* Recognize instructions with only one successor *)

let single_successor f pc =
  match PTree.get pc f.fn_code with
    | Some i ->
        (match i with
           | Lnop s -> Some s
           | Lop (op, args, res, s) -> Some s
           | Lload (chunk, addr, args, dst, s) -> Some s
           | Lstore (chunk, addr, args, src, s) -> Some s
           | Lcall (sig0, ros, args, res, s) -> Some s
           | Ltailcall (sig0, ros, args) -> None
           | Lalloc (arg, res, s) -> Some s
           | Lcond (cond, args, ifso, ifnot) -> None
           | Lreturn optarg -> None)
    | None -> None

(* Build the enumeration *)

let enumerate_aux f reach =
  let preds = reachable_predecessors f reach in
  let enum = ref Coq_nil in
  let emitted = Array.make (int_of_pos f.fn_nextpc) false in
  let rec emit_basic_block pc =
    enum := Coq_cons(pc, !enum);
    emitted.(int_of_pos pc) <- true;
    match single_successor f pc with
    | None -> ()
    | Some pc' ->
        let npc' = int_of_pos pc' in
        if preds.(npc') <= 1 && not emitted.(npc') then emit_basic_block pc' in
  let rec emit_all pc =
    if pc <> Coq_xH then begin
      let pc = coq_Ppred pc in
      if not emitted.(int_of_pos pc) && PMap.get pc reach
      then emit_basic_block pc;
      emit_all pc
    end in
  emit_all f.fn_nextpc;
  CList.rev !enum
