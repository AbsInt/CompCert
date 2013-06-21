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

(* Useful functions to manipulate C abstract syntax *)

open C

(* Sets and maps over identifiers *)
module IdentSet : Set.S with type elt = ident
module IdentMap : Map.S with type key = ident

(* Typedef handling *)
val unroll : Env.t -> typ -> typ
  (* Expand typedefs at head of type.  Returned type is not [TNamed]. *)

(* Attributes *)

val add_attributes : attributes -> attributes -> attributes
  (* Union of two sets of attributes *)
val remove_attributes : attributes -> attributes -> attributes
  (* Difference [attr1 \ attr2] between two sets of attributes *)
val incl_attributes : attributes -> attributes -> bool
  (* Check that first set of attributes is a subset of second set. *)
val find_custom_attributes : string list -> attributes -> attr_arg list list
  (* Extract arguments of custom [Attr] attributes whose names appear
     in the given list of names. *)
val attributes_of_type : Env.t -> typ -> attributes
  (* Return the attributes of the given type, expanding typedefs if needed. *)
val add_attributes_type : attributes -> typ -> typ
  (* Add the given set of attributes to those of the given type. *)
val remove_attributes_type : Env.t -> attributes -> typ -> typ
  (* Remove the given set of attributes to those of the given type. *)
val erase_attributes_type : Env.t -> typ -> typ
  (* Erase the attributes of the given type. *)
val attr_is_type_related: attribute -> bool
(* Is an attribute type-related (true) or variable-related (false)? *)

(* Type compatibility *)
val compatible_types : ?noattrs: bool -> Env.t -> typ -> typ -> bool
  (* Check that the two given types are compatible.  
     If [noattrs], ignore attributes (recursively). *)
val combine_types : ?noattrs: bool -> Env.t -> typ -> typ -> typ option
  (* Like [compatible_types], but if the two types are compatible,
     return the most precise type compatible with both. *)

(* Size and alignment *)

val sizeof : Env.t -> typ -> int option
  (* Return the size alignment of the given type, in bytes.
     Machine-dependent. [None] is returned if the type is incomplete. *)
val alignof : Env.t -> typ -> int option
  (* Return the natural alignment of the given type, in bytes.
     Machine-dependent. [None] is returned if the type is incomplete. *)
val sizeof_ikind: ikind -> int
  (* Return the size of the given integer kind. *)
val incomplete_type : Env.t -> typ -> bool
  (* Return true if the given type is incomplete, e.g.
     declared but not defined struct or union, or array type  without a size. *)

(* Computing composite_info records *)

val composite_info_decl:
  Env.t -> struct_or_union -> attributes -> Env.composite_info
val composite_info_def:
  Env.t -> struct_or_union -> attributes -> field list -> Env.composite_info

(* Type classification functions *)

val is_void_type : Env.t -> typ -> bool
  (* Is type [void]? *)
val is_integer_type : Env.t -> typ -> bool
  (* Is type integer? *)
val is_arith_type : Env.t -> typ -> bool
  (* Is type integer or float? *)
val is_pointer_type : Env.t -> typ -> bool
  (* Is type a pointer type? *)
val is_scalar_type : Env.t -> typ -> bool
  (* Is type integer, float or pointer? *)
val is_composite_type : Env.t -> typ -> bool
  (* Is type a struct or union? *)
val is_function_type : Env.t -> typ -> bool
  (* Is type a function type? (not pointer to function) *)
val pointer_arithmetic_ok : Env.t -> typ -> bool
  (* Is the type [*ty] appropriate for pointer arithmetic?
     [ty] must not be void, nor a function type, nor an incomplete type. *)
val is_signed_ikind : ikind -> bool
  (* Return true if the given integer kind is a signed type. *)
val unsigned_ikind_of : ikind -> ikind
  (* Return the unsigned integer kind corresponding to the given
     integer kind. *)
val signed_ikind_of : ikind -> ikind
  (* Return the signed integer kind corresponding to the given
     integer kind. *)
val integer_rank : ikind -> int
  (* Order integer kinds from smaller to bigger *)
val float_rank : fkind -> int
  (* Order float kinds from smaller to bigger *)

(* Usual conversions over types *)

val pointer_decay : Env.t -> typ -> typ
  (* Transform (decay) array and function types to pointer types. *)
val unary_conversion : Env.t -> typ -> typ
  (* The usual unary conversions:
       small integer types are promoted to [int]
       array and function types decay *)
val binary_conversion : Env.t -> typ -> typ -> typ
  (* The usual binary conversions.  Applies only to arithmetic types.
     Return the arithmetic type to which both operands of the binop
     are converted. *)
val argument_conversion : Env.t -> typ -> typ
  (* Conversion applied to the argument of a prototyped function.
     Equivalent to [pointer_decay]. *)
val default_argument_conversion : Env.t -> typ -> typ
  (* Conversion applied to the argument of a nonprototyped or variadic
     function.  Like unary conversion, plus [float] becomes [double]. *)

(* Special types *)
val enum_ikind : ikind
  (* Integer kind for enum values.  Always [IInt]. *)
val wchar_ikind : ikind
  (* Integer kind for wchar_t type.  Unsigned. *)
val size_t_ikind : ikind
  (* Integer kind for size_t type.  Unsigned. *)
val ptr_t_ikind : ikind
  (* Integer kind for ptr_t type.  Smallest unsigned kind large enough
     to contain a pointer without information loss. *)
val ptrdiff_t_ikind : ikind
  (* Integer kind for ptrdiff_t type.  Smallest signed kind large enough
     to contain the difference between two pointers. *)

(* Helpers for type-checking *)

val type_of_constant : constant -> typ
  (* Return the type of the given constant. *)
val type_of_member : Env.t -> field -> typ
  (* Return the type of accessing the given field [fld].
     Normally it's [fld.fld_type] but there is a special case for
     small unsigned bitfields. *)
val is_literal_0 : exp -> bool
  (* Is the given expression the integer literal "0"?  *)
val is_lvalue : exp -> bool
  (* Is the given expression a l-value? *)
val is_modifiable_lvalue : Env.t -> exp -> bool
  (* Is the given expression a modifiable l-value? *)
val valid_assignment : Env.t -> exp -> typ -> bool
  (* Check that an assignment of the given expression to a l-value of
     the given type is allowed. *)
val valid_cast : Env.t -> typ -> typ -> bool
  (* Check that a cast from the first type to the second is allowed. *)
val fundef_typ: fundef -> typ
  (* Return the function type for the given function definition. *)
val int_representable: int64 -> int -> bool -> bool
  (* Is the given int64 representable with the given number of bits and
     signedness? *)

(* Constructors *)

val intconst : int64 -> ikind -> exp
  (* Build expression for given integer constant. *)
val floatconst0 : exp
  (* Build expression for (double)0. *)
val nullconst : exp
  (* Expression for [(void * ) 0] *)
val eaddrof : exp -> exp
  (* Expression for [&e] *)
val ecast : typ -> exp -> exp
  (* Expression for [(ty)e] *)
val eassign : exp -> exp -> exp
  (* Expression for [e1 = e2] *)
val ecomma :  exp -> exp -> exp
  (* Expression for [e1, e2] *)
val sskip: stmt
  (* The [skip] statement.  No location. *)
val sseq : location -> stmt -> stmt -> stmt
  (* Return the statement [s1; s2], optimizing the cases 
     where [s1] or [s2] is [skip], or [s2] is a block. *)
val sassign : location -> exp -> exp -> stmt
  (* Return the statement [exp1 = exp2;] *)

(* Locations *)

val no_loc: location
  (* Denotes an unknown location. *)
val printloc: out_channel -> location -> unit
  (* Printer for locations (for Printf) *)
val formatloc: Format.formatter -> location -> unit
  (* Printer for locations (for Format) *)

