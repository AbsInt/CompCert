(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

type error =
    Unbound_identifier of string
  | Unbound_tag of string * string
  | Tag_mismatch of string * string * string
  | Unbound_typedef of string
  | No_member of string * string * string
val error_message : error -> string
exception Error of error

val fresh_ident : string -> C.ident

type composite_info = {
  ci_kind: C.struct_or_union;
  ci_members: C.field list;             (* members, in order *)
  ci_alignof: int option;               (* alignment; None if incomplete *)
  ci_sizeof: int option;                (* size; None if incomplete *)
  ci_attr: C.attributes                 (* attributes, if any *)
}

type ident_info = II_ident of C.storage * C.typ | II_enum of int64

type typedef_info = C.typ

type enum_info = {
  ei_members: C.enumerator list; (* list of all members *)
  ei_attr: C.attributes        (* attributes, if any *)
}

type t

val empty : t

val new_scope : t -> t
val in_current_scope : t -> C.ident -> bool

val lookup_ident : t -> string -> C.ident * ident_info
val lookup_struct : t -> string -> C.ident * composite_info
val lookup_union : t -> string -> C.ident * composite_info
val lookup_composite : t -> string -> (C.ident * composite_info) option
val lookup_typedef : t -> string -> C.ident * typedef_info
val lookup_enum : t -> string -> C.ident * enum_info

val ident_is_bound : t -> string -> bool

val find_ident : t -> C.ident -> ident_info
val find_struct : t -> C.ident -> composite_info
val find_union : t -> C.ident -> composite_info
val find_struct_member : t -> C.ident * string -> C.field list
val find_union_member : t -> C.ident * string -> C.field list
val find_typedef : t -> C.ident -> typedef_info
val find_enum : t -> C.ident -> enum_info

val enter_ident : t -> string -> C.storage -> C.typ -> C.ident * t
val enter_composite : t -> string -> composite_info -> C.ident * t
val enter_enum_item : t -> string -> int64 -> C.ident * t
val enter_typedef : t -> string -> typedef_info -> C.ident * t
val enter_enum : t -> string -> enum_info -> C.ident * t

val add_ident : t -> C.ident -> C.storage -> C.typ -> t
val add_composite : t -> C.ident -> composite_info -> t
val add_typedef : t -> C.ident -> typedef_info -> t
val add_enum : t -> C.ident -> enum_info -> t

val add_types : t -> t -> t
