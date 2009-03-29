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
type lvalue
type tau
type absloc

(* only for compatability with Olf *)
exception UnknownLocation

val debug : bool ref
val debug_constraints : bool ref
val debug_aliases : bool ref
val smart_aliases : bool ref
val finished_constraints : unit -> unit (* only for compatability with Olf *)
val print_constraints : bool ref
val no_flow : bool ref
val no_sub : bool ref
val analyze_mono : bool ref
val solve_constraints : unit -> unit
val rvalue : lvalue -> tau
val deref : tau -> lvalue
val join : tau -> tau -> tau
val join_inits : tau list -> tau
val address : lvalue -> tau
val instantiate : lvalue -> int -> lvalue
val assign : lvalue -> tau -> unit
val assign_ret : int -> lvalue -> tau -> unit
val apply : tau -> tau list -> (tau * int)
val apply_undefined : tau list -> (tau * int) (* only for compatability with Olf *)
val assign_undefined : lvalue -> unit (* only for compatability with Olf *)
val make_function :  string -> lvalue list -> tau -> tau
val make_lvalue : bool -> string -> (Cil.varinfo option) -> lvalue
val bottom : unit -> tau
val return : tau -> tau -> unit
val make_fresh : string -> tau
val points_to_names : lvalue -> string list
val points_to : lvalue -> Cil.varinfo list
val epoints_to : tau -> Cil.varinfo list
val string_of_lvalue : lvalue -> string
val global_lvalue : lvalue -> bool
val alias_query : bool -> lvalue list -> int * int
val alias_frequency : (lvalue * bool) list -> int * int

val may_alias : tau -> tau -> bool

val absloc_points_to : lvalue -> absloc list
val absloc_epoints_to : tau -> absloc list
val absloc_of_lvalue : lvalue -> absloc
val absloc_eq : (absloc * absloc) -> bool
val d_absloc : unit -> absloc -> Pretty.doc
val phonyAddrOf : lvalue -> lvalue
