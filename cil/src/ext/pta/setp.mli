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

(* $Id: setp.mli,v 1.3 2003-02-19 19:26:31 jkodumal Exp $ *)

(** Sets over ordered types.

   This module implements the set data structure, given a total ordering
   function over the set elements. All operations over sets
   are purely applicative (no side-effects).
   The implementation uses balanced binary trees, and is therefore
   reasonably efficient: insertion and membership take time
   logarithmic in the size of the set, for instance. 
*)

module type PolyOrderedType = 
  sig
    type 'a t
      (** The type of the set elements. *)
    val compare :  'a t -> 'a t -> int
      (** A total ordering function over the set elements.
          This is a two-argument function [f] such that
          [f e1 e2] is zero if the elements [e1] and [e2] are equal,
          [f e1 e2] is strictly negative if [e1] is smaller than [e2],
          and [f e1 e2] is strictly positive if [e1] is greater than [e2].
          Example: a suitable ordering function is
          the generic structural comparison function {!Pervasives.compare}. *)
  end
(** Input signature of the functor {!Set.Make}. *)

module type S =
  sig
    type 'a elt
    (** The type of the set elements. *)

    type 'a t
    (** The type of sets. *)

    val empty: 'a t
    (** The empty set. *)

    val is_empty: 'a t -> bool
    (** Test whether a set is empty or not. *)

    val mem: 'a elt -> 'a t -> bool
      (** [mem x s] tests whether [x] belongs to the set [s]. *)

    val add: 'a elt -> 'a t -> 'a t
    (** [add x s] returns a set containing all elements of [s],
       plus [x]. If [x] was already in [s], [s] is returned unchanged. *)

    val singleton: 'a elt -> 'a t
    (** [singleton x] returns the one-element set containing only [x]. *)

    val remove: 'a elt -> 'a t -> 'a t
    (** [remove x s] returns a set containing all elements of [s],
       except [x]. If [x] was not in [s], [s] is returned unchanged. *)

    val union: 'a t -> 'a t -> 'a t
    (** Set union. *)

    val inter: 'a t -> 'a t -> 'a t
    (** Set interseection. *)

    (** Set difference. *)
    val diff: 'a t -> 'a t -> 'a t

    val compare: 'a t -> 'a t -> int
    (** Total ordering between sets. Can be used as the ordering function
       for doing sets of sets. *)

    val equal: 'a t -> 'a t -> bool
    (** [equal s1 s2] tests whether the sets [s1] and [s2] are
       equal, that is, contain equal elements. *)

    val subset: 'a t -> 'a t -> bool
    (** [subset s1 s2] tests whether the set [s1] is a subset of
       the set [s2]. *)

    val iter: ('a elt -> unit) -> 'a t -> unit
    (** [iter f s] applies [f] in turn to all elements of [s].
       The order in which the elements of [s] are presented to [f]
       is unspecified. *)

    val fold: ('a elt -> 'b -> 'b) -> 'a t -> 'b -> 'b
    (** [fold f s a] computes [(f xN ... (f x2 (f x1 a))...)],
       where [x1 ... xN] are the elements of [s].
       The order in which elements of [s] are presented to [f] is
       unspecified. *)

    val for_all: ('a elt -> bool) -> 'a t -> bool
    (** [for_all p s] checks if all elements of the set
       satisfy the predicate [p]. *)

    val exists: ('a elt -> bool) -> 'a t -> bool
    (** [exists p s] checks if at least one element of
       the set satisfies the predicate [p]. *)
        
    val filter: ('a elt -> bool) -> 'a t -> 'a t
    (** [filter p s] returns the set of all elements in [s]
       that satisfy predicate [p]. *)

    val partition: ('a elt -> bool) -> 'a t -> 'a t * 'a t
    (** [partition p s] returns a pair of sets [(s1, s2)], where
       [s1] is the set of all the elements of [s] that satisfy the
       predicate [p], and [s2] is the set of all the elements of
       [s] that do not satisfy [p]. *)

    val cardinal: 'a t -> int
    (** Return the number of elements of a set. *)

    val elements: 'a t -> 'a elt list
    (** Return the list of all elements of the given set.
       The returned list is sorted in increasing order with respect
       to the ordering [Ord.compare], where [Ord] is the argument
       given to {!Set.Make}. *)

    val min_elt: 'a t -> 'a elt
    (** Return the smallest element of the given set
       (with respect to the [Ord.compare] ordering), or raise
       [Not_found] if the set is empty. *)

    val max_elt: 'a t -> 'a elt
    (** Same as {!Set.S.min_elt}, but returns the largest element of the
       given set. *)

    val choose: 'a t -> 'a elt
    (** Return one element of the given set, or raise [Not_found] if
       the set is empty. Which element is chosen is unspecified,
       but equal elements will be chosen for equal sets. *)
  end
(** Output signature of the functor {!Set.Make}. *)

module Make (Ord : PolyOrderedType) : S with type 'a elt = 'a Ord.t
(** Functor building an implementation of the set structure
   given a totally ordered type. *)
