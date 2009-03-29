(** Growable Arrays *)

type 'a fill =
    Elem of 'a
  | Susp of (int -> 'a)

type 'a t = {
            gaFill: 'a fill;
            (** Stuff to use to fill in the array as it grows *)

    mutable gaMaxInitIndex: int;
            (** Maximum index that was written to. -1 if no writes have 
             * been made.  *)

    mutable gaData: 'a array;
  } 

let growTheArray (ga: 'a t) (len: int) 
                 (toidx: int) (why: string) : unit = 
  if toidx >= len then begin
    (* Grow the array by 50% *)
    let newlen = toidx + 1 + len  / 2 in
(*
    ignore (E.log "growing an array to idx=%d (%s)\n" toidx why);
*)
    let data' = begin match ga.gaFill with
      Elem x ->
	let data'' = Array.create newlen x in
	Array.blit ga.gaData 0 data'' 0 len;
	data''
    | Susp f -> Array.init newlen
	  (fun i -> if i < len then ga.gaData.(i) else f i)
    end
    in
    ga.gaData <- data'
  end

let max_init_index (ga: 'a t) : int =
  ga.gaMaxInitIndex

let num_alloc_index (ga: 'a t) : int = 
  Array.length ga.gaData

let reset_max_init_index (ga: 'a t) : unit =
  ga.gaMaxInitIndex <- -1

let getg (ga: 'a t) (r: int) : 'a = 
  let len = Array.length ga.gaData in
  if r >= len then 
    growTheArray ga len r "getg";

  ga.gaData.(r)

let setg (ga: 'a t) (r: int) (what: 'a) : unit = 
  let len = Array.length ga.gaData in
  if r >= len then 
    growTheArray ga len r "setg";
  if r > max_init_index ga then ga.gaMaxInitIndex <- r;
  ga.gaData.(r) <- what

let get (ga: 'a t) (r: int) : 'a = Array.get ga.gaData r

let set (ga: 'a t) (r: int) (what: 'a) : unit = 
  if r > max_init_index ga then ga.gaMaxInitIndex <- r;
  Array.set ga.gaData r what

let make (initsz: int) (fill: 'a fill) : 'a t = 
  { gaFill = fill;
    gaMaxInitIndex = -1;
    gaData = begin match fill with
      Elem x -> Array.create initsz x
    | Susp f -> Array.init initsz f
    end; }

let clear (ga: 'a t) : unit =
  (* This assumes the user hasn't used the raw "set" on any value past
     max_init_index.  Maybe we shouldn't trust max_init_index here?? *) 
  if ga.gaMaxInitIndex >= 0 then begin
    begin match ga.gaFill with 
        Elem x -> Array.fill ga.gaData 0 (ga.gaMaxInitIndex+1) x
      | Susp f -> 
          for i = 0 to ga.gaMaxInitIndex do 
            Array.set ga.gaData i (f i)
          done
    end;
    ga.gaMaxInitIndex <- -1
  end

let copy (ga: 'a t) : 'a t = 
  { ga with gaData = Array.copy ga.gaData } 

let deep_copy (ga: 'a t) (copy: 'a -> 'a): 'a t = 
  { ga with gaData = Array.map copy ga.gaData } 

(* An accumulating for loop. Used internally. *)
let fold_for ~(init: 'a) ~(lo: int) ~(hi: int) (f: int -> 'a -> 'a) =
  let rec forloop i acc =
    if i > hi then acc
    else forloop (i+1) (f i acc)
  in
  forloop lo init

(** Iterate over the initialized elements of the array *)
let iter (f: 'a -> unit) (ga: 'a t) = 
  for i = 0 to max_init_index ga do 
    f ga.gaData.(i)
  done

(** Iterate over the initialized elements of the array *)
let iteri  (f: int -> 'a -> unit) (ga: 'a t) = 
  for i = 0 to max_init_index ga do 
    f i ga.gaData.(i)
  done

(** Iterate over the elements of 2 arrays *)
let iter2  (f: int -> 'a -> 'b -> unit) (ga1: 'a t) (ga2: 'b t) = 
  let len1 = max_init_index ga1 in
  let len2 = max_init_index ga2 in
  if len1 > -1 || len2 > -1 then begin
    let max = if len1 > len2 then begin
                  ignore(getg ga2 len1); (*grow ga2 to match ga1*)
                  len1
              end else begin
                  ignore(getg ga1 len2); (*grow ga1 to match ga2*)
                  len2
              end in
    for i = 0 to max do 
      f i ga1.gaData.(i) ga2.gaData.(i)
    done
  end

(** Fold left over the initialized elements of the array *)
let fold_left (f: 'acc -> 'a -> 'acc) (acc: 'acc) (ga: 'a t) : 'acc = 
  let rec loop (acc: 'acc) (idx: int) : 'acc = 
    if idx > max_init_index ga then 
      acc
    else
      loop (f acc ga.gaData.(idx)) (idx + 1)
  in
  loop acc 0


(** Fold left over the initialized elements of the array *)
let fold_lefti (f: 'acc -> int -> 'a -> 'acc) (acc: 'acc) (ga: 'a t) : 'acc = 
  let rec loop (acc: 'acc) (idx: int) : 'acc = 
    if idx > max_init_index ga then 
      acc
    else
      loop (f acc idx ga.gaData.(idx)) (idx + 1)
  in
  loop acc 0

(** Fold right over the initialized elements of the array *)
let fold_right (f: 'a -> 'acc -> 'acc) (ga: 'a t) (acc: 'acc) : 'acc = 
  let rec loop (acc: 'acc) (idx: int) : 'acc = 
    if idx < 0 then 
      acc
    else
      loop (f ga.gaData.(idx) acc) (idx - 1)
  in
  loop acc (max_init_index ga)

(** Document generator *)
let d_growarray (sep: Pretty.doc)
                (doit:int -> 'a -> Pretty.doc)
                ()
                (elements: 'a t) =
  Pretty.docArray ~sep:sep doit () elements.gaData

let restoreGA ?deepCopy (ga: 'a t) : (unit -> unit) = 
  let old = 
    (match deepCopy with 
         None -> copy ga
       | Some f -> deep_copy ga f)
  in
  (fun () ->
     if ga.gaFill != old.gaFill then
       Errormsg.s 
         (Errormsg.bug "restoreGA to an array with a different fill.");
     ga.gaMaxInitIndex <- old.gaMaxInitIndex;
     for i = 0 to max_init_index ga do 
       set ga i (getg old i)
     done)

let find (ga: 'a t) (fn: 'a -> bool) : int option = 
  let rec loop (i:int) : int option = 
    if i > ga.gaMaxInitIndex then None
    else if fn (get ga i) then Some i
    else loop (i + 1)
  in
  loop 0
