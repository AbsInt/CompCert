
                              (* Imperative bitmaps *)

type t
                                        (* Create a bitmap given the number 
                                         * of bits *)
val  make : int -> t
val  init : int -> (int -> bool) -> t   (* Also initialize it *)

val  size : t -> int                    (* How much space it is reserved *)

                                        (* The cardinality of a set *)
val  card  : t -> int

                                        (* Make a copy of a bitmap *)
val  clone : t -> t 

val  cloneEmpty : t -> t                (* An empty set with the same 
                                         * dimentions *)

val  set : t -> int -> bool -> unit
val  get : t -> int -> bool
                                        (* destructive union. The first 
                                         * element is updated. Returns true 
                                         * if any change was actually 
                                         * necessary  *)
val  union  : t -> t -> bool

                                        (* accLive livein liveout def. Does 
                                         * liveIn += (liveout - def) *)
val  accLive : t -> t -> t -> bool

                                        (* Copy the second argument onto the 
                                         * first *)
val  assign : t -> t -> unit


val  inters : t -> t -> unit
val  diff   : t -> t -> unit


val  empty  : t -> bool

val  equal  : t -> t -> bool

val  toList : t -> int list

val  iter   : (int -> unit) -> t -> unit
val  fold   : ('a -> int -> 'a) -> t -> 'a -> 'a 

