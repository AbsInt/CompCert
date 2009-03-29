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
(* Flags                                                               *)
(*                                                                     *)
(***********************************************************************)

(** Print extra debugging info *)
val debug : bool ref

(** Debug constraints (print all constraints) *)
val debug_constraints : bool ref

(** Debug smart alias queries *)
val debug_aliases : bool ref

(** Debug may alias queries *)
val debug_may_aliases : bool ref

val smart_aliases : bool ref

(** Print out the top level constraints *)
val print_constraints : bool ref

(** Make the analysis monomorphic *)
val analyze_mono : bool ref

(** Disable subtyping *)
val no_sub : bool ref

(** Make the flow step a no-op *)
val no_flow : bool ref 

(** Show the progress of the flow step *)
val show_progress : bool ref 

(** Treat undefined functions conservatively *)
val conservative_undefineds : bool ref

(***********************************************************************)
(*                                                                     *)
(* Building the Points-to Graph                                        *)
(*                                                                     *)
(***********************************************************************)

(** Analyze a file *)
val analyze_file : Cil.file -> unit

(** Print the type of each lvalue in the program *)
val print_types : unit -> unit

(***********************************************************************)
(*                                                                     *)
(* High-level Query Interface                                          *)
(*                                                                     *)
(***********************************************************************)

(** If undefined functions are analyzed conservatively, any of the 
  high-level queries may raise this exception *)
exception UnknownLocation

val may_alias : Cil.exp -> Cil.exp -> bool

val resolve_lval : Cil.lval -> (Cil.varinfo list)

val resolve_exp : Cil.exp -> (Cil.varinfo list)

val resolve_funptr : Cil.exp -> (Cil.fundec list)

(***********************************************************************)
(*                                                                     *)
(* Low-level Query Interface                                           *)
(*                                                                     *)
(***********************************************************************)

(** type for abstract locations *)
type absloc 

(** Give an abstract location for a varinfo *)
val absloc_of_varinfo : Cil.varinfo -> absloc

(** Give an abstract location for an Cil lvalue *)
val absloc_of_lval : Cil.lval -> absloc

(** may the two abstract locations be aliased? *)
val absloc_eq : absloc -> absloc -> bool

val absloc_e_points_to  : Cil.exp -> absloc list
val absloc_e_transitive_points_to : Cil.exp -> absloc list 

val absloc_lval_aliases : Cil.lval -> absloc list

(** Print a string representing an absloc, for debugging. *)
val d_absloc : unit -> absloc -> Pretty.doc


(***********************************************************************)
(*                                                                     *)
(* Printing results                                                    *)
(*                                                                     *)
(***********************************************************************)

(** Compute points to sets for variables. If true is passed, print the sets. *)
val compute_results : bool -> unit

(*

Deprecated these. -- jk

(** Compute alias relationships. If true is passed, print all alias pairs. *)
 val compute_aliases : bool -> unit

(** Compute alias frequncy *)
val compute_alias_frequency : unit -> unit


*)

val compute_aliases : bool  -> unit


val feature: Cil.featureDescr
