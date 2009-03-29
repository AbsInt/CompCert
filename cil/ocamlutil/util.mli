(** A bunch of generally useful functions *)

exception GotSignal of int

val withTimeout : float -> (* Seconds for timeout *)
                (int -> 'b) -> (* What to do if we have a timeout. The 
                                        * argument passed is the signal number 
                                        * received. *)
                ('a -> 'b) -> (* The function to run *)
                'a -> (* And its argument *)
   'b

val docHash : ?sep:Pretty.doc -> ('a -> 'b -> Pretty.doc) -> unit -> 
  (('a, 'b) Hashtbl.t) -> Pretty.doc 


val hash_to_list: ('a, 'b) Hashtbl.t -> ('a * 'b) list

val keys: ('a, 'b) Hashtbl.t -> 'a list


(** Copy a hash table into another *)
val hash_copy_into: ('a, 'b) Hashtbl.t -> ('a, 'b) Hashtbl.t -> unit

(** First, a few utility functions I wish were in the standard prelude *)

val anticompare: 'a -> 'a -> int

val list_drop : int -> 'a list -> 'a list
val list_droptail : int -> 'a list -> 'a list
val list_span: ('a -> bool) -> ('a list) -> 'a list * 'a list
val list_insert_by: ('a -> 'a -> int) -> 'a -> 'a list -> 'a list
val list_head_default: 'a -> 'a list -> 'a
val list_iter3 : ('a -> 'b -> 'c -> unit) ->
  'a list -> 'b list -> 'c list -> unit
val get_some_option_list : 'a option list -> 'a list
val list_append: ('a list) -> ('a list) -> ('a list) (* tail-recursive append*)

(** Iterate over a list passing the index as you go *)
val list_iteri: (int -> 'a -> unit) -> 'a list -> unit
val list_mapi: (int -> 'a -> 'b) -> 'a list -> 'b list

(** Like fold_left but pass the index into the list as well *)
val list_fold_lefti: ('acc -> int -> 'a -> 'acc) -> 'acc -> 'a list -> 'acc

(** Generates the range of integers starting with a and ending with b *)
val int_range_list : int -> int -> int list

(* Create a list of length l *)
val list_init : int -> (int -> 'a) -> 'a list

(** Find the first element in a list that returns Some *)
val list_find_first: 'a list -> ('a -> 'b option) -> 'b option 

(** mapNoCopy is like map but avoid copying the list if the function does not 
 * change the elements *)

val mapNoCopy: ('a -> 'a) -> 'a list -> 'a list

val mapNoCopyList: ('a -> 'a list) -> 'a list -> 'a list

val filterNoCopy: ('a -> bool) -> 'a list -> 'a list


(** Join a list of strings *)
val joinStrings: string -> string list -> string


(**** Now in growArray.mli

(** Growable arrays *)
type 'a growArrayFill =
    Elem of 'a
  | Susp of (int -> 'a)

type 'a growArray = {
            gaFill: 'a growArrayFill;
            (** Stuff to use to fill in the array as it grows *)

    mutable gaMaxInitIndex: int;
            (** Maximum index that was written to. -1 if no writes have 
             * been made.  *)

    mutable gaData: 'a array;
  } 

val newGrowArray: int -> 'a growArrayFill -> 'a growArray
(** [newGrowArray initsz fillhow] *)

val getReg: 'a growArray -> int -> 'a
val setReg: 'a growArray -> int -> 'a -> unit
val copyGrowArray: 'a growArray -> 'a growArray
val deepCopyGrowArray: 'a growArray -> ('a -> 'a) -> 'a growArray


val growArray_iteri:  (int -> 'a -> unit) -> 'a growArray -> unit
(** Iterate over the initialized elements of the array *)

val growArray_foldl: ('acc -> 'a -> 'acc) -> 'acc ->'a growArray -> 'acc
(** Fold left over the initialized elements of the array *)

****)

(** hasPrefix prefix str returns true with str starts with prefix *)
val hasPrefix: string -> string -> bool


(** Given a ref cell, produce a thunk that later restores it to its current value *)
val restoreRef: ?deepCopy:('a -> 'a) -> 'a ref -> unit -> unit

(** Given a hash table, produce a thunk that later restores it to its current value *)
val restoreHash: ?deepCopy:('b -> 'b) -> ('a, 'b) Hashtbl.t -> unit -> unit

(** Given an integer hash table, produce a thunk that later restores it to 
 * its current value *)
val restoreIntHash: ?deepCopy:('b -> 'b) -> 'b Inthash.t -> unit -> unit

(** Given an array, produce a thunk that later restores it to its current value *)
val restoreArray: ?deepCopy:('a -> 'a) -> 'a array -> unit -> unit


(** Given a list of thunks, produce a thunk that runs them all *)
val runThunks: (unit -> unit) list -> unit -> unit


val memoize: ('a, 'b) Hashtbl.t ->
            'a ->
            ('a -> 'b) -> 'b

(** Just another name for memoize *)
val findOrAdd: ('a, 'b) Hashtbl.t ->
            'a ->
            ('a -> 'b) -> 'b

val tryFinally: 
    ('a -> 'b) -> (* The function to run *)
    ('b option -> unit) -> (* Something to run at the end. The None case is 
                          * used when an exception is thrown *)
    'a -> 'b




(** Get the value of an option.  Raises Failure if None *)
val valOf : 'a option -> 'a

(**
 * An accumulating for loop.
 *
 * Initialize the accumulator with init.  The current index and accumulator
 * from the previous iteration is passed to f.
 *)
val fold_for : init:'a -> lo:int -> hi:int -> (int -> 'a -> 'a) -> 'a

(************************************************************************)

module type STACK = sig
  type 'a t
  (** The type of stacks containing elements of type ['a]. *)

  exception Empty
  (** Raised when {!Util.Stack.pop} or {!Util.Stack.top} is applied to an 
   * empty stack. *)

  val create : unit -> 'a t


  val push : 'a -> 'a t -> unit
  (** [push x s] adds the element [x] at the top of stack [s]. *)

  val pop : 'a t -> 'a
  (** [pop s] removes and returns the topmost element in stack [s],
     or raises [Empty] if the stack is empty. *)

  val top : 'a t -> 'a
  (** [top s] returns the topmost element in stack [s],
     or raises [Empty] if the stack is empty. *)
  
  val clear : 'a t -> unit
  (** Discard all elements from a stack. *)
  
  val copy : 'a t -> 'a t
  (** Return a copy of the given stack. *)
  
  val is_empty : 'a t -> bool
  (** Return [true] if the given stack is empty, [false] otherwise. *)
  
  val length : 'a t -> int
  (** Return the number of elements in a stack. *)
  
  val iter : ('a -> unit) -> 'a t -> unit
  (** [iter f s] applies [f] in turn to all elements of [s],
     from the element at the top of the stack to the element at the
     bottom of the stack. The stack itself is unchanged. *)
end

module Stack : STACK

(************************************************************************
   Configuration 
************************************************************************)
(** The configuration data can be of several types **)
type configData = 
    ConfInt of int
  | ConfBool of bool
  | ConfFloat of float
  | ConfString of string
  | ConfList of configData list


(** Load the configuration from a file *)
val loadConfiguration: string -> unit

(** Save the configuration in a file. Overwrites the previous values *)
val saveConfiguration: string -> unit


(** Clear all configuration data *)
val clearConfiguration: unit -> unit

(** Set a configuration element, with a key. Overwrites the previous values *)
val setConfiguration: string -> configData -> unit

(** Find a configuration elements, given a key. Raises Not_found if it canont 
 * find it *)
val findConfiguration: string -> configData

(** Like findConfiguration but extracts the integer *)
val findConfigurationInt: string -> int

(** Looks for an integer configuration element, and if it is found, it uses 
 * the given function. Otherwise, does nothing *)
val useConfigurationInt: string -> (int -> unit) -> unit


val findConfigurationBool: string -> bool
val useConfigurationBool: string -> (bool -> unit) -> unit

val findConfigurationString: string -> string
val useConfigurationString: string -> (string -> unit) -> unit

val findConfigurationList: string -> configData list
val useConfigurationList: string -> (configData list -> unit) -> unit


(************************************************************************)

(** Symbols are integers that are uniquely associated with names *)
type symbol = int

(** Get the name of a symbol *)
val symbolName: symbol -> string

(** Register a symbol name and get the symbol for it *)
val registerSymbolName: string -> symbol

(** Register a number of consecutive symbol ids. The naming function will be 
 * invoked with indices from 0 to the counter - 1. Returns the id of the 
 * first symbol created. The naming function is invoked lazily, only when the 
 * name of the symbol is required. *)
val registerSymbolRange: int -> (int -> string) -> symbol


(** Make a fresh symbol. Give the name also, which ought to be distinct from 
 * existing symbols. This is different from registerSymbolName in that it 
 * always creates a new symbol. *)
val newSymbol: string -> symbol

(** Reset the state of the symbols to the program startup state *)
val resetSymbols: unit -> unit

(** Take a snapshot of the symbol state. Returns a thunk that restores the 
 * state. *)
val snapshotSymbols: unit -> unit -> unit


(** Dump the list of registered symbols *)
val dumpSymbols: unit -> unit

(************************************************************************)

(** {1 Int32 Operators} *)

module Int32Op : sig
   val (<%) : int32 -> int32 -> bool
   val (<=%) : int32 -> int32 -> bool
   val (>%) : int32 -> int32 -> bool
   val (>=%) : int32 -> int32 -> bool
   val (<>%) : int32 -> int32 -> bool
   
   val (+%) : int32 -> int32 -> int32
   val (-%) : int32 -> int32 -> int32
   val ( *% ) : int32 -> int32 -> int32
   val (/%) : int32 -> int32 -> int32
   val (~-%) : int32 -> int32

   val sll : int32 -> int32 -> int32
   val (>>%) : int32 -> int32 -> int32
   val (>>>%) : int32 -> int32 -> int32

   exception IntegerTooLarge
   val to_int : int32 -> int
end

(************************************************************************)

(** This has the semantics of (=) on OCaml 3.07 and earlier.  It can
   handle cyclic values as long as a structure in the cycle has a unique
   name or id in some field that occurs before any fields that have cyclic
   pointers. *)
val equals: 'a -> 'a -> bool
