(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
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

(** Utilities for managing "concatenable lists" (clists). We often need to
    concatenate sequences, and using lists for this purpose is expensive. This
    module provides routines to manage such lists more efficiently. In this
    model, we never do cons or append explicitly. Instead we maintain
    the elements of the list in a special data structure. Routines are provided
    to convert to/from ordinary lists, and carry out common list operations.*)

(** The clist datatype. A clist can be an ordinary list, or a clist preceded 
    or followed by an element, or two clists implicitly appended together*)
type 'a clist = 
  | CList of 'a list             (** The only representation for the empty 
                                     list. Try to use sparingly.  *)
  | CConsL of 'a * 'a clist      (** Do not use this a lot because scanning 
                                   * it is not tail recursive *)
  | CConsR of 'a clist * 'a 
  | CSeq of 'a clist * 'a clist (** We concatenate only two of them at this
                                    time. Neither is the empty clist. To be
                                    sure always use append to make these *)


(** Convert a clist to an ordinary list *)
val toList: 'a clist -> 'a list

(** Convert an ordinary list to a clist *)  
val fromList: 'a list -> 'a clist 

(** Create a clist containing one element *)
val single: 'a -> 'a clist        

(** The empty clist *)
val empty: 'a clist               


(** Append two clists *)
val append: 'a clist -> 'a clist -> 'a clist 
                 
(** A useful check to assert before an append. It checks that the two lists 
 * are not identically the same (Except if they are both empty) *)
val checkBeforeAppend: 'a clist -> 'a clist -> bool

(** Find the length of a clist *)
val length: 'a clist -> int   

(** Map a function over a clist. Returns another clist *)
val map: ('a -> 'b) -> 'a clist -> 'b clist 


(** A version of fold_left that works on clists *)
val fold_left: ('acc -> 'a -> 'acc) -> 'acc -> 'a clist -> 'acc

(** A version of iter that works on clists *)
val iter: ('a -> unit) -> 'a clist -> unit

(** Reverse a clist. The first function reverses an element.  *)
val rev: ('a -> 'a) -> 'a clist -> 'a clist

(** A document for printing a clist (similar to [docList]) *)
val docCList: 
    Pretty.doc -> ('a -> Pretty.doc) -> unit -> 'a clist -> Pretty.doc
 
