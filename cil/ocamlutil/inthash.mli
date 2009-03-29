type 'a t

(* These functions behave the same as Hashtbl, but the key type is
   always int.  (Specializing on int improves the performance) *)

val create: int -> 'a t
val clear: 'a t -> unit
val length : 'a t -> int

val copy: 'a t -> 'a t
val copy_into: 'a t -> 'a t -> unit

val add: 'a t -> int -> 'a -> unit
val replace: 'a t -> int -> 'a -> unit
val remove: 'a t -> int -> unit
val remove_all: 'a t -> int -> unit

val mem: 'a t -> int -> bool
val find: 'a t -> int -> 'a
val find_all: 'a t -> int -> 'a list

val iter: (int -> 'a -> unit) -> 'a t -> unit
val fold: (int -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

val memoize: 'a t -> int -> (int -> 'a) -> 'a

val tolist: 'a t -> (int * 'a) list
