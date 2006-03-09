open Camlcoq
open Datatypes
open CList
open AST
open Locations

type status = To_move | Being_moved | Moved

let parallel_move_order lsrc ldst =
  let src = array_of_coqlist lsrc
  and dst = array_of_coqlist ldst in
  let n = Array.length src in
  let status = Array.make n To_move in
  let moves = ref Coq_nil in
  let rec move_one i =
    if src.(i) <> dst.(i) then begin
      status.(i) <- Being_moved;
      for j = 0 to n - 1 do
        if src.(j) = dst.(i) then
          match status.(j) with
            To_move ->
              move_one j
          | Being_moved ->
              let tmp =
                match Loc.coq_type src.(j) with
                | Tint -> R IT2
                | Tfloat -> R FT2 in
              moves := Coq_cons (Coq_pair(src.(j), tmp), !moves);
              src.(j) <- tmp
          | Moved ->
              ()
      done;
      moves := Coq_cons(Coq_pair(src.(i), dst.(i)), !moves);
      status.(i) <- Moved
    end in
  for i = 0 to n - 1 do
    if status.(i) = To_move then move_one i
  done;
  CList.rev !moves
