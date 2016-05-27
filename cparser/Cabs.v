(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import BinPos.

(* OCaml's string type. *)
Parameter string : Type.
(* OCaml's int64 type, used to represent individual characters in literals. *)
Parameter char_code : Type.
(* Context information. *)
Parameter cabsloc : Type.

Record floatInfo := {
  isHex_FI:bool;
  integer_FI:option string;
  fraction_FI:option string;
  exponent_FI:option string;
  suffix_FI:option string
}.

Inductive structOrUnion :=
  | STRUCT | UNION.

Inductive typeSpecifier := (* Merge all specifiers into one type *)
  | Tvoid                  (* Type specifier ISO 6.7.2 *)
  | Tchar
  | Tshort
  | Tint
  | Tlong
  | Tfloat
  | Tdouble
  | Tsigned
  | Tunsigned
  | T_Bool
  | Tnamed : string -> typeSpecifier
  (* each of the following three kinds of specifiers contains a field
   * or list item iff it corresponds to a definition (as opposed to
   * a forward declaration or simple reference to the type).
   * They also have a list of __attribute__s that appeared between the
   * keyword and the type name (definitions only) *)
  | Tstruct_union : structOrUnion -> option string -> option (list field_group) -> list attribute -> typeSpecifier
  | Tenum : option string -> option (list (string * option expression * cabsloc)) -> list attribute -> typeSpecifier

with storage :=
  AUTO | STATIC | EXTERN | REGISTER | TYPEDEF

with cvspec :=
| CV_CONST | CV_VOLATILE | CV_RESTRICT
| CV_ATTR : attribute -> cvspec

with funspec :=
 INLINE | NORETURN

(* Type specifier elements. These appear at the start of a declaration *)
(* Everywhere they appear in this file, they appear as a 'list spec_elem', *)
(* which is not interpreted by cabs -- rather, this "word soup" is passed *)
(* on to the compiler.  Thus, we can represent e.g. 'int long float x' even *)
(* though the compiler will of course choke. *)
with spec_elem :=
  | SpecCV : cvspec -> spec_elem            (* const/volatile *)
  | SpecStorage : storage -> spec_elem
  | SpecFunction: funspec -> spec_elem
  | SpecType : typeSpecifier -> spec_elem

(* Declarator type. They modify the base type given in the specifier. Keep
 * them in the order as they are printed (this means that the top level
 * constructor for ARRAY and PTR is the inner-level in the meaning of the
 * declared type) *)
with decl_type :=
 | JUSTBASE
 | ARRAY : decl_type -> list cvspec -> option expression -> decl_type
 | PTR : list cvspec -> decl_type -> decl_type
(* The bool is true for variable length parameters. *)
 | PROTO : decl_type -> list parameter * bool -> decl_type
 | PROTO_OLD : decl_type -> list string -> decl_type

with parameter :=
  | PARAM : list spec_elem -> option string -> decl_type -> list attribute -> cabsloc -> parameter

(* The optional expression is the bitfield *)
with field_group :=
  | Field_group : list spec_elem -> list (option name * option expression) -> cabsloc -> field_group

(* The decl_type is in the order in which they are printed. Only the name of
 * the declared identifier is pulled out. *)
(* e.g: in "int *x", "*x" is the declarator; "x" will be pulled out as *)
(* the string, and decl_type will be PTR([], JUSTBASE) *)
with name :=
  | Name : string -> decl_type -> list attribute -> cabsloc -> name

(* A variable declarator ("name") with an initializer *)
with init_name :=
  | Init_name : name -> init_expression -> init_name

(*
** Expressions
*)
with binary_operator :=
  | ADD | SUB | MUL | DIV | MOD
  | AND | OR
  | BAND | BOR | XOR | SHL | SHR
  | EQ | NE | LT | GT | LE | GE
  | ASSIGN
  | ADD_ASSIGN | SUB_ASSIGN | MUL_ASSIGN | DIV_ASSIGN | MOD_ASSIGN
  | BAND_ASSIGN | BOR_ASSIGN | XOR_ASSIGN | SHL_ASSIGN | SHR_ASSIGN
  | COMMA

with unary_operator :=
  | MINUS | PLUS | NOT | BNOT | MEMOF | ADDROF
  | PREINCR | PREDECR | POSINCR | POSDECR

with expression :=
  | UNARY : unary_operator -> expression -> expression
  | BINARY : binary_operator -> expression -> expression -> expression
  | QUESTION : expression -> expression -> expression -> expression

    (* A CAST can actually be a constructor expression *)
  | CAST : (list spec_elem * decl_type) -> init_expression -> expression

  | CALL : expression -> list expression -> expression
  | BUILTIN_VA_ARG : expression -> list spec_elem * decl_type -> expression
  | CONSTANT : constant -> expression
  | VARIABLE : string -> expression
  | EXPR_SIZEOF : expression -> expression
  | TYPE_SIZEOF : (list spec_elem * decl_type) -> expression
  | INDEX : expression -> expression -> expression
  | MEMBEROF : expression -> string -> expression
  | MEMBEROFPTR : expression -> string -> expression

    (* Non-standard *)
  | EXPR_ALIGNOF : expression -> expression
  | TYPE_ALIGNOF : (list spec_elem * decl_type) -> expression
  | GENERIC: expression -> (list generic_association) -> expression

with constant :=
  (* The string is the textual representation of the constant in
     the source code. *)
  | CONST_INT : string -> constant
  | CONST_FLOAT : floatInfo -> constant
  | CONST_CHAR : bool -> list char_code -> constant
  | CONST_STRING : bool -> list char_code -> constant


with init_expression :=
  | NO_INIT
  | SINGLE_INIT : expression -> init_expression
  | COMPOUND_INIT : list (list initwhat * init_expression) -> init_expression

with initwhat :=
  | INFIELD_INIT : string -> initwhat
  | ATINDEX_INIT : expression -> initwhat

with attribute :=
  | GCC_ATTR : list gcc_attribute -> cabsloc -> attribute
  | PACKED_ATTR : list expression -> cabsloc -> attribute
  | ALIGNAS_ATTR : list expression -> cabsloc -> attribute

with gcc_attribute :=
  | GCC_ATTR_EMPTY
  | GCC_ATTR_NOARGS : gcc_attribute_word -> gcc_attribute
  | GCC_ATTR_ARGS : gcc_attribute_word -> list expression -> gcc_attribute

with gcc_attribute_word :=
  | GCC_ATTR_IDENT : string -> gcc_attribute_word
  | GCC_ATTR_CONST
  | GCC_ATTR_PACKED

with generic_association :=
  | GENERIC_DEFAULT: expression -> generic_association
  | GENERIC_ASSOC: (list spec_elem * decl_type) -> expression -> generic_association.

(* like name_group, except the declared variables are allowed to have initializers *)
(* e.g.: int x=1, y=2; *)
Definition init_name_group := (list spec_elem * list init_name)%type.

(* The base type and the storage are common to all names. Each name might
 * contain type or storage modifiers *)
(* e.g.: int x, y; *)
Definition name_group := (list spec_elem * list name)%type.

(* GCC extended asm *)
Inductive asm_operand :=
| ASMOPERAND: option string -> bool -> list char_code -> expression -> asm_operand.

Definition asm_flag := (bool * list char_code)%type.

(*
** Declaration definition (at toplevel)
*)
Inductive definition :=
 | FUNDEF : list spec_elem -> name -> list definition -> statement -> cabsloc -> definition
 | DECDEF : init_name_group -> cabsloc -> definition  (* global variable(s), or function prototype *)
 | PRAGMA : string -> cabsloc -> definition

(*
** statements
*)

with statement :=
 | NOP : cabsloc -> statement
 | COMPUTATION : expression -> cabsloc -> statement
 | BLOCK : list statement -> cabsloc -> statement
 | If : expression -> statement -> option statement -> cabsloc -> statement
 | WHILE : expression -> statement -> cabsloc -> statement
 | DOWHILE : expression -> statement -> cabsloc -> statement
 | FOR : option for_clause -> option expression -> option expression -> statement -> cabsloc -> statement
 | BREAK : cabsloc -> statement
 | CONTINUE : cabsloc -> statement
 | RETURN : option expression -> cabsloc -> statement
 | SWITCH : expression -> statement -> cabsloc -> statement
 | CASE : expression -> statement -> cabsloc -> statement
 | DEFAULT : statement -> cabsloc -> statement
 | LABEL : string -> statement -> cabsloc -> statement
 | GOTO : string -> cabsloc -> statement
 | ASM : list cvspec -> bool -> list char_code -> list asm_operand -> list asm_operand -> list asm_flag -> cabsloc -> statement
 | DEFINITION : definition -> statement (*definition or declaration of a variable or type*)

with for_clause :=
 | FC_EXP : expression -> for_clause
 | FC_DECL : definition -> for_clause.
