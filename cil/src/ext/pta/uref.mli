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
type 'a uref
  
(** Union-find with union by rank and path compression 
  
  This is an implementation of Tarjan's union-find data structure using 
  generics. The interface is analagous to standard references, with the
  addition of a union operation which makes two references indistinguishable.
  
*)
  
val uref: 'a -> 'a uref 
  (** Create a new uref *)
  
val equal: 'a uref * 'a uref -> bool
  (** Test whether two urefs share the same equivalence class *)
  
val deref: 'a uref -> 'a
  (** Extract the contents of this reference *)
  
val update: 'a uref * 'a -> unit
  (** Update the value stored in this reference *)
  
val unify: ('a * 'a -> 'a) -> 'a uref * 'a uref -> unit
  (** [unify f (p,q)] unifies references [p] and [q], making them 
    indistinguishable. The contents of the reference are the result of
    [f] *)
    
val union: 'a uref * 'a uref -> unit
  (** [unify (p,q)] unifies references [p] and [q], making them
    indistinguishable. The contents of the reference are the contents of
    one of the first or second arguments (unspecified) *)
