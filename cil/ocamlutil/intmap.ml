(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* $Id: intmap.ml,v 1.2 2005-10-04 21:30:25 necula Exp $ *)

(* specialized to integer keys by George Necula *)

type 'a t =
    Empty
  | Node of 'a t * int * 'a * 'a t * int

let height = function
    Empty -> 0
  | Node(_,_,_,_,h) -> h
        
let create l x d r =
  let hl = height l and hr = height r in
  Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

let bal l x d r =
  let hl = match l with Empty -> 0 | Node(_,_,_,_,h) -> h in
  let hr = match r with Empty -> 0 | Node(_,_,_,_,h) -> h in
  if hl > hr + 2 then begin
    match l with
      Empty -> invalid_arg "Map.bal"
    | Node(ll, lv, ld, lr, _) ->
        if height ll >= height lr then
          create ll lv ld (create lr x d r)
        else begin
          match lr with
            Empty -> invalid_arg "Map.bal"
          | Node(lrl, lrv, lrd, lrr, _)->
              create (create ll lv ld lrl) lrv lrd (create lrr x d r)
        end
  end else if hr > hl + 2 then begin
    match r with
      Empty -> invalid_arg "Map.bal"
    | Node(rl, rv, rd, rr, _) ->
        if height rr >= height rl then
          create (create l x d rl) rv rd rr
        else begin
          match rl with
            Empty -> invalid_arg "Map.bal"
          | Node(rll, rlv, rld, rlr, _) ->
              create (create l x d rll) rlv rld (create rlr rv rd rr)
        end
  end else
    Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))
      
let empty = Empty

let is_empty = function Empty -> true | _ -> false
    
let rec add x data = function
    Empty ->
      Node(Empty, x, data, Empty, 1)
  | Node(l, v, d, r, h) as t ->
      if x = v then
        Node(l, x, data, r, h)
      else if x < v then
        bal (add x data l) v d r
      else
        bal l v d (add x data r)
          
let rec find x = function
    Empty ->
      raise Not_found
  | Node(l, v, d, r, _) ->
      if x = v then d
      else find x (if x < v then l else r)
          
let rec mem x = function
    Empty ->
      false
  | Node(l, v, d, r, _) ->
      x = v || mem x (if x < v then l else r)
        
let rec min_binding = function
    Empty -> raise Not_found
  | Node(Empty, x, d, r, _) -> (x, d)
  | Node(l, x, d, r, _) -> min_binding l
        
let rec remove_min_binding = function
    Empty -> invalid_arg "Map.remove_min_elt"
  | Node(Empty, x, d, r, _) -> r
  | Node(l, x, d, r, _) -> bal (remove_min_binding l) x d r

let merge t1 t2 =
  match (t1, t2) with
    (Empty, t) -> t
  | (t, Empty) -> t
  | (_, _) ->
      let (x, d) = min_binding t2 in
      bal t1 x d (remove_min_binding t2)

let rec remove x = function
    Empty ->
      Empty
  | Node(l, v, d, r, h) as t ->
      if x = v then
        merge l r
      else if x < v then
        bal (remove x l) v d r
      else
        bal l v d (remove x r)

let rec iter f = function
    Empty -> ()
  | Node(l, v, d, r, _) ->
      iter f l; f v d; iter f r

let rec map f = function
    Empty               -> Empty
  | Node(l, v, d, r, h) -> Node(map f l, v, f d, map f r, h)

let rec mapi f = function
    Empty               -> Empty
  | Node(l, v, d, r, h) -> Node(mapi f l, v, f v d, mapi f r, h)

let rec fold f m accu =
  match m with
    Empty -> accu
  | Node(l, v, d, r, _) ->
      fold f l (f v d (fold f r accu))

type 'a enumeration = End | More of int * 'a * 'a t * 'a enumeration

let rec cons_enum m e =
  match m with
    Empty -> e
  | Node(l, v, d, r, _) -> cons_enum l (More(v, d, r, e))

let compare cmp m1 m2 =
  let rec compare_aux e1 e2 =
    match (e1, e2) with
      (End, End) -> 0
    | (End, _)  -> -1
    | (_, End) -> 1
    | (More(v1, d1, r1, e1), More(v2, d2, r2, e2)) ->
        if v1 <> v2 then if v1 < v2 then -1 else 1 else
        let c = cmp d1 d2 in
        if c <> 0 then c else
        compare_aux (cons_enum r1 e1) (cons_enum r2 e2)
in compare_aux (cons_enum m1 End) (cons_enum m2 End)

let equal cmp m1 m2 =
  let rec equal_aux e1 e2 =
    match (e1, e2) with
      (End, End) -> true
    | (End, _)  -> false
    | (_, End) -> false
    | (More(v1, d1, r1, e1), More(v2, d2, r2, e2)) ->
        v1 = v2 && cmp d1 d2 &&
        equal_aux (cons_enum r1 e1) (cons_enum r2 e2)
in equal_aux (cons_enum m1 End) (cons_enum m2 End)

(** Some definitions for ML2Coq *)
let _ = ignore "coq: 
(* Some definitions for ML2Coq *)

"
