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
val alignas_attribute : attributes -> int
  (* Extract the value of the [_Alignas] and [attribute((aligned(N)))]
     attributes, if any.
     Return 0 if none, a (positive) power of two alignment if some. *)
val packing_parameters : attributes -> int * int * bool
  (* Extract the value of the [__packed__] attributes, if any.
     Return a triple
     (maximum field alignment, minimum struct alignment, byte swapping).
     Alignments of 0 mean default alignment. *)
val find_custom_attributes : string list -> attributes -> attr_arg list list
  (* Extract arguments of custom [Attr] attributes whose names appear
     in the given list of names. *)
val remove_custom_attributes : string list -> attributes -> attributes
  (* Remove all [Attr] attributes whose names appear
     in the given list of names. *)
val attributes_of_type : Env.t -> typ -> attributes
  (* Return the attributes of the given type, expanding typedefs if needed. *)
val attributes_of_type_no_expand : typ -> attributes
  (* Return the attributes of the given type, without expanding typedefs. *)
val add_attributes_type : attributes -> typ -> typ
  (* Add the given set of attributes to those of the given type. *)
val remove_attributes_type : Env.t -> attributes -> typ -> typ
  (* Remove the given set of attributes to those of the given type. *)
val erase_attributes_type : Env.t -> typ -> typ
  (* Erase the attributes of the given type. *)
val change_attributes_type : Env.t -> (attributes -> attributes) -> typ -> typ
  (* Apply the given function to the top-level attributes of the given type *)
val has_std_alignas :  Env.t -> typ -> bool
  (* Do the attributes of the type contain the C11 _Alignas attribute *)

type attribute_class =
  | Attr_object         (* Attribute applies to the object being declared
                          (function, global variable, local variable)  *)
  | Attr_name           (* Attribute applies to the name being declared
                          (object, struct/union member, struct/union/enum tag *)
  | Attr_type           (* Attribute applies to types *)
  | Attr_struct         (* Attribute applies to struct, union and enum *)
  | Attr_function       (* Attribute applies to function types and decls *)
  | Attr_unknown        (* Not a declared attribute *)

val declare_attribute: string -> attribute_class -> unit
val declare_attributes: (string * attribute_class) list -> unit
  (* Register the given custom attribute names with the given classes. *)
val class_of_attribute: attribute -> attribute_class
  (* Return the class of the given attribute.  Standard attributes
     have class [Attr_type].  Custom attributes have the class that
     was given to them using [declare_attribute], or [Attr_unknown]
     if not declared. *)
val name_of_attribute: attribute -> string
  (* Name for printing an attribute *)
val attr_inherited_by_members: attribute -> bool
  (* Is an attribute of a composite inherited by members of the composite? *)


val strip_attributes_type: typ -> attribute list -> typ
  (* Remove all attributes from the given type that are not contained in the list *)
val strip_last_attribute: typ -> attribute option * typ
  (* Remove the last top level attribute and return it *)


(* Type compatibility *)

type attr_handling =
  | AttrCompat
  | AttrIgnoreTop
  | AttrIgnoreAll

val compatible_types : attr_handling -> Env.t -> typ -> typ -> bool
  (* Check that the two given types are compatible.
     The attributes in the types are compared according to the first argument:
- [AttrCompat]: the types must have the same standard attributes
    ([const], [volatile], [restrict]) but may differ on custom attributes.
- [AttrIgnoreTop]: the top-level attributes of the two types are ignored,
    but attributes of e.g. types of pointed objects (for pointer types)
    are compared as per [AttrCompat].
- [AttrIgnoreAll]: recursively ignore the attributes in the two types. *)
val combine_types : attr_handling -> Env.t -> typ -> typ -> typ option
  (* Like [compatible_types], but if the two types are compatible,
     return the most precise type compatible with both.
     The attributes are compared according to the first argument,
     with the same meaning as for [compatible_types].
     When two sets of attributes are compatible, the result of
     [combine_types] carries the union of these two sets of attributes. *)
val equal_types : Env.t -> typ -> typ -> bool
   (* Check that the two given types are equal up to typedef use *)

(* Size and alignment *)

val sizeof : Env.t -> typ -> int option
  (* Return the size alignment of the given type, in bytes.
     Machine-dependent. [None] is returned if the type is incomplete. *)
val alignof : Env.t -> typ -> int option
  (* Return the natural alignment of the given type, in bytes.
     Machine-dependent. [None] is returned if the type is incomplete. *)
val incomplete_type : Env.t -> typ -> bool
  (* Return true if the given type is incomplete, e.g.
     declared but not defined struct or union, or array type  without a size. *)
val sizeof_ikind: ikind -> int
  (* Return the size of the given integer kind. *)
val sizeof_fkind: fkind -> int
  (* Return the size of the given float kind. *)

(* Computing composite_info records *)

val composite_info_decl:
  struct_or_union -> attributes -> Env.composite_info
val composite_info_def:
  Env.t -> struct_or_union -> attributes -> field list -> Env.composite_info
val struct_layout:
  Env.t -> attributes -> field list -> (string * int) list
val offsetof:
  Env.t -> typ -> field -> int
(* Compute the offset of a struct member *)
val cautious_mul: int64 -> int -> int option
(* Overflow-avoiding multiplication of an int64 and an int, with
   result in type int. *)

(* Type classification functions *)

val is_void_type : Env.t -> typ -> bool
  (* Is type [void]? *)
val is_integer_type : Env.t -> typ -> bool
  (* Is type integer? *)
val is_float_type : Env.t -> typ -> bool
  (* Is type float *)
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
val is_function_pointer_type : Env.t -> typ -> bool
  (* Is type a pointer to function type? *)
val is_anonymous_composite : typ -> bool
  (* Is type an anonymous composite? *)
val is_qualified_array : typ -> bool
  (* Does the type contain a qualified array type (e.g. int[const 5])? *)
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
val wchar_ikind : unit -> ikind
  (* Integer kind for wchar_t type. *)
val size_t_ikind : unit -> ikind
  (* Integer kind for size_t type.  Unsigned. *)
val ptr_t_ikind : unit -> ikind
  (* Integer kind for ptr_t type.  Smallest unsigned kind large enough
     to contain a pointer without information loss. *)
val ptrdiff_t_ikind : unit -> ikind
  (* Integer kind for ptrdiff_t type.  Smallest signed kind large enough
     to contain the difference between two pointers. *)

(* Helpers for type-checking *)

val type_of_constant : constant -> typ
  (* Return the type of the given constant. *)
val type_of_member : Env.t -> field -> typ
  (* Return the type of accessing the given field [fld].
     Normally it's [fld.fld_type] but there is a special case for
     small unsigned bitfields. *)
val is_call_to_fun : exp -> string -> bool
  (* Test whether the caller is the given function *)
val is_debug_stmt : stmt -> bool
  (* Is the given statement a call to debug builtin? *)
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
val int_pointer_conversion : Env.t -> typ -> typ -> bool
  (* Check that the cast from tfrom to tto is an integer to pointer
     conversion *)
val fundef_typ: fundef -> typ
  (* Return the function type for the given function definition. *)
val int_representable: int64 -> int -> bool -> bool
  (* Is the given int64 representable with the given number of bits and
     signedness? *)
val field_of_dot_access: Env.t -> typ -> string -> field
  (* Return the field info for a [x.field] access *)
val field_of_arrow_access: Env.t -> typ -> string -> field
  (* Return the field info for a [x->field] access *)
val valid_array_size: Env.t -> typ -> int64 -> bool
  (* Test whether the array size fits in half of the address space *)
val is_volatile_variable: Env.t -> exp -> bool
  (* Test whether the expression is an access to a volatile variable *)
val is_bitfield: Env.t -> exp -> bool
  (* Test whether the expression is a bit-field *)
val contains_flex_array_mem : Env.t  -> typ -> bool
  (* Is this a struct with a flexible array member *)

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
val ecommalist :  exp list -> exp -> exp
  (* Expression for [e1, ..., eN, e] *)
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

(* Initializers *)
exception No_default_init
  (* Raised if no default initilaizer exists *)

val default_init: Env.t -> typ -> init
  (* Return a default initializer for the given type
     (with zero numbers, null pointers, etc). *)

(* Substitution of variables by expressions *)

val subst_expr: exp IdentMap.t -> exp -> exp
val subst_init: exp IdentMap.t -> init -> init
val subst_decl: exp IdentMap.t -> decl -> decl
val subst_stmt: exp IdentMap.t -> stmt -> stmt
