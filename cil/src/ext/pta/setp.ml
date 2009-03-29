(*
 *
 * Copyright (c) 2001-2002, 
 *  John Kodumal        <jkodumal@eecs.berkeley.edu>
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

(* $Id: setp.ml,v 1.3 2003-02-19 19:26:31 jkodumal Exp $ *)

(* Sets over ordered types *)

module type PolyOrderedType =
  sig
    type 'a t
    val compare: 'a t -> 'a t -> int
  end

module type S =
  sig
    type 'a elt
    type 'a t
    val empty: 'a t
    val is_empty: 'a t -> bool
    val mem: 'a elt -> 'a t -> bool
    val add: 'a elt -> 'a t -> 'a t
    val singleton: 'a elt -> 'a t
    val remove: 'a elt -> 'a t -> 'a t
    val union: 'a t -> 'a t -> 'a t
    val inter: 'a t -> 'a t -> 'a t
    val diff: 'a t -> 'a t -> 'a t
    val compare: 'a t -> 'a t -> int
    val equal: 'a t -> 'a t -> bool
    val subset: 'a t -> 'a t -> bool
    val iter: ('a elt -> unit) -> 'a t -> unit
    val fold: ('a elt -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all: ('a elt -> bool) -> 'a t -> bool
    val exists: ('a elt -> bool) -> 'a t -> bool
    val filter: ('a elt -> bool) -> 'a t -> 'a t
    val partition: ('a elt -> bool) -> 'a t -> 'a t * 'a t
    val cardinal: 'a t -> int
    val elements: 'a t -> 'a elt list
    val min_elt: 'a t -> 'a elt
    val max_elt: 'a t -> 'a elt
    val choose: 'a t -> 'a elt
  end

module Make(Ord: PolyOrderedType) =
  struct
    type 'a elt = 'a Ord.t
    type 'a t = Empty | Node of 'a t * 'a elt * 'a t * int

    (* Sets are represented by balanced binary trees (the heights of the
       children differ by at most 2 *)

    let height = function
        Empty -> 0
      | Node(_, _, _, h) -> h

    (* Creates a new node with left son l, value x and right son r.
       l and r must be balanced and | height l - height r | <= 2.
       Inline expansion of height for better speed. *)

    let create l x r =
      let hl = match l with Empty -> 0 | Node(_,_,_,h) -> h in
      let hr = match r with Empty -> 0 | Node(_,_,_,h) -> h in
      Node(l, x, r, (if hl >= hr then hl + 1 else hr + 1))

    (* Same as create, but performs one step of rebalancing if necessary.
       Assumes l and r balanced.
       Inline expansion of create for better speed in the most frequent case
       where no rebalancing is required. *)

    let bal l x r =
      let hl = match l with Empty -> 0 | Node(_,_,_,h) -> h in
      let hr = match r with Empty -> 0 | Node(_,_,_,h) -> h in
      if hl > hr + 2 then begin
        match l with
          Empty -> invalid_arg "Set.bal"
        | Node(ll, lv, lr, _) ->
            if height ll >= height lr then
              create ll lv (create lr x r)
            else begin
              match lr with
                Empty -> invalid_arg "Set.bal"
              | Node(lrl, lrv, lrr, _)->
                  create (create ll lv lrl) lrv (create lrr x r)
            end
      end else if hr > hl + 2 then begin
        match r with
          Empty -> invalid_arg "Set.bal"
        | Node(rl, rv, rr, _) ->
            if height rr >= height rl then
              create (create l x rl) rv rr
            else begin
              match rl with
                Empty -> invalid_arg "Set.bal"
              | Node(rll, rlv, rlr, _) ->
                  create (create l x rll) rlv (create rlr rv rr)
            end
      end else
        Node(l, x, r, (if hl >= hr then hl + 1 else hr + 1))

    (* Same as bal, but repeat rebalancing until the final result
       is balanced. *)

    let rec join l x r =
      match bal l x r with
        Empty -> invalid_arg "Set.join"
      | Node(l', x', r', _) as t' ->
          let d = height l' - height r' in
          if d < -2 || d > 2 then join l' x' r' else t'

    (* Merge two trees l and r into one.
       All elements of l must precede the elements of r.
       Assumes | height l - height r | <= 2. *)

    let rec merge t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (Node(l1, v1, r1, h1), Node(l2, v2, r2, h2)) ->
          bal l1 v1 (bal (merge r1 l2) v2 r2)

    (* Same as merge, but does not assume anything about l and r. *)

    let rec concat t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (Node(l1, v1, r1, h1), Node(l2, v2, r2, h2)) ->
          join l1 v1 (join (concat r1 l2) v2 r2)

    (* Splitting *)

    let rec split x = function
        Empty ->
          (Empty, None, Empty)
      | Node(l, v, r, _) ->
          let c = Ord.compare x v in
          if c = 0 then (l, Some v, r)
          else if c < 0 then
            let (ll, vl, rl) = split x l in (ll, vl, join rl v r)
          else
            let (lr, vr, rr) = split x r in (join l v lr, vr, rr)

    (* Implementation of the set operations *)

    let empty = Empty

    let is_empty = function Empty -> true | _ -> false

    let rec mem x = function
        Empty -> false
      | Node(l, v, r, _) ->
          let c = Ord.compare x v in
          c = 0 || mem x (if c < 0 then l else r)

    let rec add x = function
        Empty -> Node(Empty, x, Empty, 1)
      | Node(l, v, r, _) as t ->
          let c = Ord.compare x v in
          if c = 0 then t else
          if c < 0 then bal (add x l) v r else bal l v (add x r)

    let singleton x = Node(Empty, x, Empty, 1)

    let rec remove x = function
        Empty -> Empty
      | Node(l, v, r, _) ->
          let c = Ord.compare x v in
          if c = 0 then merge l r else
          if c < 0 then bal (remove x l) v r else bal l v (remove x r)

    let rec union s1 s2 =
      match (s1, s2) with
        (Empty, t2) -> t2
      | (t1, Empty) -> t1
      | (Node(l1, v1, r1, h1), Node(l2, v2, r2, h2)) ->
          if h1 >= h2 then
            if h2 = 1 then add v2 s1 else begin
              let (l2, _, r2) = split v1 s2 in
              join (union l1 l2) v1 (union r1 r2)
            end
          else
            if h1 = 1 then add v1 s2 else begin
              let (l1, _, r1) = split v2 s1 in
              join (union l1 l2) v2 (union r1 r2)
            end

    let rec inter s1 s2 =
      match (s1, s2) with
        (Empty, t2) -> Empty
      | (t1, Empty) -> Empty
      | (Node(l1, v1, r1, _), t2) ->
          match split v1 t2 with
            (l2, None, r2) ->
              concat (inter l1 l2) (inter r1 r2)
          | (l2, Some _, r2) ->
              join (inter l1 l2) v1 (inter r1 r2)

    let rec diff s1 s2 =
      match (s1, s2) with
        (Empty, t2) -> Empty
      | (t1, Empty) -> t1
      | (Node(l1, v1, r1, _), t2) ->
          match split v1 t2 with
            (l2, None, r2) ->
              join (diff l1 l2) v1 (diff r1 r2)
          | (l2, Some _, r2) ->
              concat (diff l1 l2) (diff r1 r2)

    let rec compare_aux l1 l2 =
        match (l1, l2) with
        ([], []) -> 0
      | ([], _)  -> -1
      | (_, []) -> 1
      | (Empty :: t1, Empty :: t2) ->
          compare_aux t1 t2
      | (Node(Empty, v1, r1, _) :: t1, Node(Empty, v2, r2, _) :: t2) ->
          let c = Ord.compare v1 v2 in
          if c <> 0 then c else compare_aux (r1::t1) (r2::t2)
      | (Node(l1, v1, r1, _) :: t1, t2) ->
          compare_aux (l1 :: Node(Empty, v1, r1, 0) :: t1) t2
      | (t1, Node(l2, v2, r2, _) :: t2) ->
          compare_aux t1 (l2 :: Node(Empty, v2, r2, 0) :: t2)

    let compare s1 s2 =
      compare_aux [s1] [s2]

    let equal s1 s2 =
      compare s1 s2 = 0

    let rec subset s1 s2 =
      match (s1, s2) with
        Empty, _ ->
          true
      | _, Empty ->
          false
      | Node (l1, v1, r1, _), (Node (l2, v2, r2, _) as t2) ->
          let c = Ord.compare v1 v2 in
          if c = 0 then
            subset l1 l2 && subset r1 r2
          else if c < 0 then
            subset (Node (l1, v1, Empty, 0)) l2 && subset r1 t2
          else
            subset (Node (Empty, v1, r1, 0)) r2 && subset l1 t2

    let rec iter f = function
        Empty -> ()
      | Node(l, v, r, _) -> iter f l; f v; iter f r

    let rec fold f s accu =
      match s with
        Empty -> accu
      | Node(l, v, r, _) -> fold f l (f v (fold f r accu))

    let rec for_all p = function
        Empty -> true
      | Node(l, v, r, _) -> p v && for_all p l && for_all p r

    let rec exists p = function
        Empty -> false
      | Node(l, v, r, _) -> p v || exists p l || exists p r

    let filter p s =
      let rec filt accu = function
        | Empty -> accu
        | Node(l, v, r, _) ->
            filt (filt (if p v then add v accu else accu) l) r in
      filt Empty s

    let partition p s =
      let rec part (t, f as accu) = function
        | Empty -> accu
        | Node(l, v, r, _) ->
            part (part (if p v then (add v t, f) else (t, add v f)) l) r in
      part (Empty, Empty) s

    let rec cardinal = function
        Empty -> 0
      | Node(l, v, r, _) -> cardinal l + 1 + cardinal r

    let rec elements_aux accu = function
        Empty -> accu
      | Node(l, v, r, _) -> elements_aux (v :: elements_aux accu r) l

    let elements s =
      elements_aux [] s

    let rec min_elt = function
        Empty -> raise Not_found
      | Node(Empty, v, r, _) -> v
      | Node(l, v, r, _) -> min_elt l

    let rec max_elt = function
        Empty -> raise Not_found
      | Node(l, v, Empty, _) -> v
      | Node(l, v, r, _) -> max_elt r

    let choose = min_elt

  end
