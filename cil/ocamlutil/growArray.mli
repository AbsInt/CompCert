(***********************************************************************)
(* Growable Arrays                                                     *)
(*                                                                     *)
(* This a wrapper around the standard OCaml array, but will grow       *)
(* automatically on get or set outside the current size of the         *)
(* array.                                                              *)
(*                                                                     *)
(* The interface is the same as the standard OCaml array where         *)
(* applicable (and implemented).                                       *)
(***********************************************************************)

(* $Id: growArray.mli,v 1.8 2005-01-06 15:37:36 necula Exp $ *)

(** Array operations. *)

(** The type of growable arrays *)
type 'a t

(** The default value to a new element of the growable array *)
type 'a fill =
    Elem of 'a
    (* A default value *)
  | Susp of (int -> 'a)
    (* A function given an index to generate a default value *)

val make : int -> 'a fill -> 'a t
(** [GrowArray.make n x] returns a fresh growable array of size
   at least [n] with default value specified by [x].

   Raise [Invalid_argument] if [n < 0] or [n > Sys.max_array_length]. *)

val num_alloc_index: 'a t -> int
(** [GrowArray.num_alloc_index a] returns the number of allocated entries in 
 * the array **)

val max_init_index : 'a t -> int
(** [GrowArray.max_init_index a] returns the maximum index to
    which has been written.

    Returns -1 if no writes have been made. *)

val reset_max_init_index : 'a t -> unit
(** [GrowArray.reset_init a] resets the max_init_index. You should probably
   use [GrowArray.clear a] instead if you also want to delete the contents. *)

val getg : 'a t -> int -> 'a
(** [GrowArray.getg a n] returns the element number [n] of array [a].
   The first element has number 0.
   The last element has number [GrowArray.length a - 1].

   If [n] is outside the range 0 to [(GrowArray.max_init_index a)],
   then the array grows to at least [n] and yields the default value. *)

val setg : 'a t -> int -> 'a -> unit
(** [GrowArray.setg a n x] modifies array [a] in place, replacing
   element number [n] with [x].

   If [n] is outside the range 0 to [(GrowArray.max_init_index a)],
   then the array grows to at least [n] and yields the default value. *)

val get : 'a t -> int -> 'a
(** [GrowArray.get a n] returns the element number [n] of grow array [a].

   Raise [Invalid_argument "Array.get"]  if [n] is outside the range
   of the underlying array. *)

val set : 'a t -> int -> 'a -> unit
(** [GrowArray.set a n x] modifies grow array [a] in place, replacing
   element number [n] with [x].

   Raise [Invalid_argument "Array.set"] if [n] is outside the range
   of the underlying array. *)
        
val clear: 'a t -> unit 
(** [GrowArray.clear a] clears the contents of the array and sets 
   max_init_index to -1.  Suspension thunks will be rerun to regenerate the 
   initial values of the array. *)

val copy : 'a t -> 'a t
(** [GrowArray.copy a] returns a copy of [a], that is, a fresh array
   containing the same elements as [a]. *)

val deep_copy : 'a t -> ('a -> 'a) -> 'a t
(** [GrowArray.copy a f] returns a deep copy of [a] using f to
    copy elements of [a]. *)

val iter : ('a -> unit) -> 'a t -> unit
(** [GrowArray.iter f a] applies function [f] in turn to all
   the elements of [a].  It is equivalent to
   [f a.(0); f a.(1); ...; f a.(GrowArray.length a - 1); ()]. *)

val iteri : (int -> 'a -> unit) -> 'a t -> unit
(** Same as {!GrowArray.iter}, but the
   function is applied to the index of the element as first argument,
   and the element itself as second argument. *)

val iter2 : (int -> 'a -> 'b -> unit) -> 'a t -> 'b t -> unit
(** Same as {!GrowArray.iteri}, but the function is applied to two arrays.
  [iter2 f a b]  is equivalent to
  [f 0 a.(0) b.(0); f 1 a.(1) b.(1); ...;  f n a.(n) b.(n); ()]
  where n is the larger of (max_init_index a) or (max_init_index b).
  The shorter array will grow to match the longer.*)

val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
(** [GrowArray.fold_left f x a] computes
   [f (... (f (f x a.(0)) a.(1)) ...) a.(n-1)],
   where [n] is the length of the array [a]. *)

val fold_lefti : ('a -> int -> 'b -> 'a) -> 'a -> 'b t -> 'a
(** [GrowArray.fold_lefti f x a] computes
   [f (... (f (f x 0 a.(0)) 1 a.(1)) ...) (n-1) a.(n-1)],
   where [n] is the length of the array [a]. *)

val fold_right : ('b -> 'a -> 'a) -> 'b t -> 'a -> 'a
(** [GrowArray.fold_right f a x] computes
   [f a.(0) (f a.(1) ( ... (f a.(n-1) x) ...))],
   where [n] is the length of the array [a]. *)

val d_growarray : Pretty.doc -> (int -> 'a -> Pretty.doc) -> unit -> 'a t
                             -> Pretty.doc
(** [GrowArray.d_growarray sep f () a] creates a {!Pretty.doc} for growable
   array a using separator sep and element printer f. *)


val restoreGA: ?deepCopy:('a -> 'a) -> 'a t -> unit -> unit
(** Given a growable array, produce a thunk that later restores it to its
    current value *)

val find: 'a t -> ('a -> bool) -> int option
(** Returns the index of the first element in the array that satisfies the
    predicate, or None if there is no such element *)
