(*
 *
 * Copyright (c) 2001 by
 *  George C. Necula	necula@cs.berkeley.edu
 *  Scott McPeak        smcpeak@cs.berkeley.edu
 *  Wes Weimer          weimer@cs.berkeley.edu
 *   
 * All rights reserved.  Permission to use, copy, modify and distribute
 * this software for research purposes only is hereby granted, 
 * provided that the following conditions are met: 
 * 1. Redistributions of source code must retain the above copyright notice, 
 * this list of conditions and the following disclaimer. 
 * 2. Redistributions in binary form must reproduce the above copyright notice, 
 * this list of conditions and the following disclaimer in the documentation 
 * and/or other materials provided with the distribution. 
 * 3. The name of the authors may not be used to endorse or promote products 
 * derived from  this software without specific prior written permission. 
 *
 * DISCLAIMER:
 * THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS OR 
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES 
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. 
 * IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY DIRECT, INDIRECT, 
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, 
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS 
 * OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON 
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT 
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF 
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)

(** Utility functions for pretty-printing. The major features provided by 
    this module are 
- An [fprintf]-style interface with support for user-defined printers
- The printout is fit to a width by selecting some of the optional newlines
- Constructs for alignment and indentation
- Print ellipsis starting at a certain nesting depth
- Constructs for printing lists and arrays

 Pretty-printing occurs in two stages:
- Construct a {!Pretty.doc} object that encodes all of the elements to be 
  printed 
  along with alignment specifiers and optional and mandatory newlines
- Format the {!Pretty.doc} to a certain width and emit it as a string, to an 
  output stream or pass it to a user-defined function

 The formatting algorithm is not optimal but it does a pretty good job while 
 still operating in linear time. The original version was based on a pretty 
 printer by Philip Wadler which turned out to not scale to large jobs. 
*)

(** API *)

(** The type of unformated documents. Elements of this type can be 
 * constructed in two ways. Either with a number of constructor shown below, 
 * or using the {!Pretty.dprintf} function with a [printf]-like interface. 
 * The {!Pretty.dprintf} method is slightly slower so we do not use it for 
 * large jobs such as the output routines for a compiler. But we use it for 
 * small jobs such as logging and error messages. *)
type doc



(** Constructors for the doc type. *)




(** Constructs an empty document *)
val nil          : doc


(** Concatenates two documents. This is an infix operator that associates to 
    the left. *)
val (++)         : doc -> doc -> doc 
val concat       : doc -> doc -> doc

(** A document that prints the given string *)
val text         : string -> doc


(** A document that prints an integer in decimal form *)
val num          : int    -> doc


(** A document that prints a real number *)
val real         : float  -> doc

(** A document that prints a character. This is just like {!Pretty.text}
    with a one-character string. *)
val chr          : char   -> doc


(** A document that consists of a mandatory newline. This is just like [(text
    "\n")]. The new line will be indented to the current indentation level,
    unless you use {!Pretty.leftflush} right after this. *)
val line         : doc

(** Use after a {!Pretty.line} to prevent the indentation. Whatever follows 
 * next will be flushed left. Indentation resumes on the next line. *)
val leftflush    : doc


(** A document that consists of either a space or a line break. Also called
    an optional line break. Such a break will be
    taken only if necessary to fit the document in a given width. If the break
    is not taken a space is printed instead. *)
val break: doc

(** Mark the current column as the current indentation level. Does not print
    anything. All taken line breaks will align to this column. The previous
    alignment level is saved on a stack. *)
val align: doc

(** Reverts to the last saved indentation level. *)
val unalign: doc


(** Mark the beginning of a markup section. The width of a markup section is 
 * considered 0 for the purpose of computing identation *)
val mark: doc

(** The end of a markup section *)
val unmark: doc

(************* Now some syntactic sugar *****************)
(** Syntactic sugar *)

(** Indents the document. Same as [((text "  ") ++ align ++ doc ++ unalign)],
    with the specified number of spaces. *)
val indent: int -> doc -> doc

(** Prints a document as markup. The marked document cannot contain line 
 * breaks or alignment constructs. *)
val markup: doc -> doc

(** Formats a sequence. [sep] is a separator, [doit] is a function that 
 * converts an element to a document. *)
val seq: sep:doc -> doit:('a ->doc) -> elements:'a list -> doc


(** An alternative function for printing a list. The [unit] argument is there 
 * to make this function more easily usable with the {!Pretty.dprintf} 
 * interface. The first argument is a separator, by default a comma. *)
val docList: ?sep:doc -> ('a -> doc) -> unit -> 'a list -> doc

(** sm: Yet another list printer.  This one accepts the same kind of
  * printing function that {!Pretty.dprintf} does, and itself works 
  * in the dprintf context.  Also accepts
  * a string as the separator since that's by far the most common.  *)
val d_list: string -> (unit -> 'a -> doc) -> unit -> 'a list -> doc

(** Formats an array. A separator and a function that prints an array
    element. The default separator is a comma. *)
val docArray: ?sep:doc -> (int -> 'a -> doc) -> unit -> 'a array -> doc

(** Prints an ['a option] with [None] or [Some] *)
val docOpt: ('a -> doc) -> unit -> 'a option -> doc


(** Print an int32 *)
val d_int32: int32 -> doc
val f_int32: unit -> int32 -> doc

val d_int64: int64 -> doc
val f_int64: unit -> int64 -> doc

(** Format maps. *)
module MakeMapPrinter :
  functor (Map: sig
                  type key
                  type 'a t
                  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
                end) ->
sig
    (** Format a map, analogous to docList. *)
    val docMap: ?sep:doc -> (Map.key -> 'a -> doc) -> unit -> 'a Map.t -> doc

    (** Format a map, analogous to d_list. *)
    val d_map: ?dmaplet:(doc -> doc -> doc)
               -> string
               -> (unit -> Map.key -> doc)
               -> (unit -> 'a -> doc)
               -> unit
               -> 'a Map.t
               -> doc
  end

(** Format sets. *)
module MakeSetPrinter :
  functor (Set: sig 
                  type elt
                  type t
                  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
                end) ->
sig
    (** Format a set, analogous to docList. *)
    val docSet: ?sep:doc -> (Set.elt -> doc) -> unit -> Set.t -> doc

    (** Format a set, analogous to d_list. *)
    val d_set: string
               -> (unit -> Set.elt -> doc)
               -> unit
               -> Set.t
               -> doc
end

(** A function that is useful with the [printf]-like interface *)
val insert: unit -> doc -> doc

val dprintf: ('a, unit, doc, doc) format4 -> 'a  
(** This function provides an alternative method for constructing 
    [doc] objects. The first argument for this function is a format string 
    argument (of type [('a, unit, doc) format]; if you insist on 
    understanding what that means see the module [Printf]). The format string 
    is like that for the [printf] function in C, except that it understands a 
    few more formatting controls, all starting with the @ character. 

    See the gprintf function if you want to pipe the result of dprintf into 
    some other functions.

 The following special formatting characters are understood (these do not 
 correspond to arguments of the function):
-  @\[ Inserts an {!Pretty.align}. Every format string must have matching 
        {!Pretty.align} and {!Pretty.unalign}. 
-  @\] Inserts an {!Pretty.unalign}.
-  @!  Inserts a {!Pretty.line}. Just like "\n"
-  @?  Inserts a {!Pretty.break}.
-  @<  Inserts a {!Pretty.mark}. 
-  @>  Inserts a {!Pretty.unmark}.
-  @^  Inserts a {!Pretty.leftflush}
       Should be used immediately after @! or "\n".
-  @@ : inserts a @ character

 In addition to the usual [printf] % formatting characters the following two 
 new characters are supported:
- %t Corresponds to an argument of type [unit -> doc]. This argument is 
     invoked to produce a document
- %a Corresponds to {b two} arguments. The first of type [unit -> 'a -> doc] 
     and the second of type ['a]. (The extra [unit] is do to the 
     peculiarities of the built-in support for format strings in Ocaml. It 
     turns out that it is not a major problem.) Here is an example of how 
     you use this:

{v dprintf "Name=%s, SSN=%7d, Children=\@\[%a\@\]\n"
             pers.name pers.ssn (docList (chr ',' ++ break) text)
             pers.children v}

 The result of [dprintf] is a {!Pretty.doc}. You can format the document and 
 emit it using the functions {!Pretty.fprint} and {!Pretty.sprint}.

*)

(** Like {!Pretty.dprintf} but more general. It also takes a function that is 
 * invoked on the constructed document but before any formatting is done. The 
 * type of the format argument means that 'a is the type of the parameters of 
 * this function, unit is the type of the first argument to %a and %t 
 * formats, doc is the type of the intermediate result, and 'b is the type of 
 * the result of gprintf. *)
val gprintf: (doc -> 'b) -> ('a, unit, doc, 'b) format4 -> 'a

(** Format the document to the given width and emit it to the given channel *)
val fprint: out_channel -> width:int -> doc -> unit

(** Format the document to the given width and emit it as a string *)
val sprint: width:int -> doc -> string

(** Like {!Pretty.dprintf} followed by {!Pretty.fprint} *)
val fprintf: out_channel -> ('a, unit, doc) format -> 'a  

(** Like {!Pretty.fprintf} applied to [stdout] *)
val printf: ('a, unit, doc) format -> 'a 

(** Like {!Pretty.fprintf} applied to [stderr] *)
val eprintf: ('a, unit, doc) format -> 'a 

                                                                     
(* sm: arg!  why can't I write this function?! *)
(* * Like {!Pretty.dprintf} but yielding a string with no newlines *)
(*val sprintf: (doc, unit, doc) format -> string*)

(* sm: different tack.. *)
(* doesn't work either.  well f it anyway *)
(*val failwithf: ('a, unit, doc) format -> 'a*)


(** Invokes a thunk, with printDepth temporarily set to the specified value *)
val withPrintDepth : int -> (unit -> unit) -> unit

(** The following variables can be used to control the operation of the printer *)

(** Specifies the nesting depth of the [align]/[unalign] pairs at which 
    everything is replaced with ellipsis *)
val printDepth   : int ref

val printIndent  : bool ref  (** If false then does not indent *)


(** If set to [true] then optional breaks are taken only when the document 
    has exceeded the given width. This means that the printout will looked 
    more ragged but it will be faster *)
val fastMode  : bool ref 

val flushOften   : bool ref  (** If true the it flushes after every print *)


(** Keep a running count of the taken newlines. You can read and write this 
  * from the client code if you want *)
val countNewLines : int ref


(** A function that when used at top-level in a module will direct 
 * the pa_prtype module generate automatically the printing functions for a 
 * type *)
val auto_printer: string -> 'b
