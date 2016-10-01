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

(** Abstract syntax for the Compcert C language *)

Require Import Coqlib Maps Integers Floats Errors.
Require Import AST Linking Values.
Require Import Ctypes Cop.

(** ** Expressions *)

(** Compcert C expressions are almost identical to those of C.
  The only omission is string literals.  Some operators are treated
  as derived forms: array indexing, pre-increment, pre-decrement, and
  the [&&] and [||] operators.  All expressions are annotated with
  their types. *)

Inductive expr : Type :=
  | Eval (v: val) (ty: type)                                  (**r constant *)
  | Evar (x: ident) (ty: type)                                (**r variable *)
  | Efield (l: expr) (f: ident) (ty: type)
                               (**r access to a member of a struct or union *)
  | Evalof (l: expr) (ty: type)              (**r l-value used as a r-value *)
  | Ederef (r: expr) (ty: type)        (**r pointer dereference (unary [*]) *)
  | Eaddrof (l: expr) (ty: type)            (**r address-of operators ([&]) *)
  | Eunop (op: unary_operation) (r: expr) (ty: type)
                                            (**r unary arithmetic operation *)
  | Ebinop (op: binary_operation) (r1 r2: expr) (ty: type)
                                           (**r binary arithmetic operation *)
  | Ecast (r: expr) (ty: type)                        (**r type cast [(ty)r] *)
  | Eseqand (r1 r2: expr) (ty: type)       (**r sequential "and" [r1 && r2] *)
  | Eseqor (r1 r2: expr) (ty: type)        (**r sequential "or" [r1 && r2] *)
  | Econdition (r1 r2 r3: expr) (ty: type)  (**r conditional [r1 ? r2 : r3] *)
  | Esizeof (ty': type) (ty: type)                      (**r size of a type *)
  | Ealignof (ty': type) (ty: type)        (**r natural alignment of a type *)
  | Eassign (l: expr) (r: expr) (ty: type)          (**r assignment [l = r] *)
  | Eassignop (op: binary_operation) (l: expr) (r: expr) (tyres ty: type)
                                  (**r assignment with arithmetic [l op= r] *)
  | Epostincr (id: incr_or_decr) (l: expr) (ty: type)
                         (**r post-increment [l++] and post-decrement [l--] *)
  | Ecomma (r1 r2: expr) (ty: type)       (**r sequence expression [r1, r2] *)
  | Ecall (r1: expr) (rargs: exprlist) (ty: type)
                                             (**r function call [r1(rargs)] *)
  | Ebuiltin (ef: external_function) (tyargs: typelist) (rargs: exprlist) (ty: type)
                                                 (**r builtin function call *)
  | Eloc (b: block) (ofs: ptrofs) (ty: type)
                       (**r memory location, result of evaluating a l-value *)
  | Eparen (r: expr) (tycast: type) (ty: type)   (**r marked subexpression *)

with exprlist : Type :=
  | Enil
  | Econs (r1: expr) (rl: exprlist).

(** Expressions are implicitly classified into l-values and r-values,
ranged over by [l] and [r], respectively, in the grammar above.

L-values are those expressions that can occur to the left of an assignment.
They denote memory locations.  (Indeed, the reduction semantics for
expression reduces them to [Eloc b ofs] expressions.)  L-values are
variables ([Evar]), pointer dereferences ([Ederef]), field accesses ([Efield]).
R-values are all other expressions.  They denote values, and the reduction
semantics reduces them to [Eval v] expressions.

A l-value can be used in a r-value context, but this use must be marked
explicitly with the [Evalof] operator, which is not materialized in the
concrete syntax of C but denotes a read from the location corresponding to
the l-value [l] argument of [Evalof l].

The grammar above contains some forms that cannot appear in source terms
but appear during reduction.  These forms are:
- [Eval v] where [v] is a pointer or [Vundef].  ([Eval] of an integer or
  float value can occur in a source term and represents a numeric literal.)
- [Eloc b ofs], which appears during reduction of l-values.
- [Eparen r tycast ty], which appears during reduction of conditionals
  [r1 ? r2 : r3] as well as sequential `and' / `or'.

Some C expressions are derived forms.  Array access [r1[r2]] is expressed
as [*(r1 + r2)].
*)

Definition Eindex (r1 r2: expr) (ty: type) :=
  Ederef (Ebinop Oadd r1 r2 (Tpointer ty noattr)) ty.

(** Pre-increment [++l] and pre-decrement [--l] are expressed as
    [l += 1] and [l -= 1], respectively. *)

Definition Epreincr (id: incr_or_decr) (l: expr) (ty: type) :=
  Eassignop (match id with Incr => Oadd | Decr => Osub end)
            l (Eval (Vint Int.one) type_int32s) (typeconv ty) ty.

(** Extract the type part of a type-annotated expression. *)

Definition typeof (a: expr) : type :=
  match a with
  | Eloc _ _ ty => ty
  | Evar _ ty => ty
  | Ederef _ ty => ty
  | Efield _ _ ty => ty
  | Eval _ ty => ty
  | Evalof _ ty => ty
  | Eaddrof _ ty => ty
  | Eunop _ _ ty => ty
  | Ebinop _ _ _ ty => ty
  | Ecast _ ty => ty
  | Econdition _ _ _ ty => ty
  | Eseqand _ _ ty => ty
  | Eseqor _ _ ty => ty
  | Esizeof _ ty => ty
  | Ealignof _ ty => ty
  | Eassign _ _ ty => ty
  | Eassignop _ _ _ _ ty => ty
  | Epostincr _ _ ty => ty
  | Ecomma _ _ ty => ty
  | Ecall _ _ ty => ty
  | Ebuiltin _ _ _ ty => ty
  | Eparen _ _ ty => ty
  end.

(** ** Statements *)

(** Compcert C statements are very much like those of C and include:
- empty statement [Sskip]
- evaluation of an expression for its side-effects [Sdo r]
- conditional [if (...) { ... } else { ... }]
- the three loops [while(...) { ... }] and [do { ... } while (...)]
  and [for(..., ..., ...) { ... }]
- the [switch] construct
- [break], [continue], [return] (with and without argument)
- [goto] and labeled statements.

Only structured forms of [switch] are supported; moreover,
the [default] case must occur last.  Blocks and block-scoped declarations
are not supported. *)

Definition label := ident.

Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Sdo : expr -> statement            (**r evaluate expression for side effects *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
  | Swhile : expr -> statement -> statement   (**r [while] loop *)
  | Sdowhile : expr -> statement -> statement (**r [do] loop *)
  | Sfor: statement -> expr -> statement -> statement -> statement (**r [for] loop *)
  | Sbreak : statement                      (**r [break] statement *)
  | Scontinue : statement                   (**r [continue] statement *)
  | Sreturn : option expr -> statement     (**r [return] statement *)
  | Sswitch : expr -> labeled_statements -> statement  (**r [switch] statement *)
  | Slabel : label -> statement -> statement
  | Sgoto : label -> statement

with labeled_statements : Type :=            (**r cases of a [switch] *)
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements.
                      (**r [None] is [default], [Some x] is [case x] *)
(** ** Functions *)

(** A function definition is composed of its return type ([fn_return]),
  the names and types of its parameters ([fn_params]), the names
  and types of its local variables ([fn_vars]), and the body of the
  function (a statement, [fn_body]). *)

Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_body: statement
}.

Definition var_names (vars: list(ident * type)) : list ident :=
  List.map (@fst ident type) vars.

(** Functions can either be defined ([Internal]) or declared as
  external functions ([External]). *)

Definition fundef := Ctypes.fundef function.

(** The type of a function definition. *)

Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end.

(** ** Programs and compilation units *)

(** As defined in module [Ctypes], a program, or compilation unit, is
  composed of:
- a list of definitions of functions and global variables;
- the names of functions and global variables that are public (not static);
- the name of the function that acts as entry point ("main" function).
- a list of definitions for structure and union names
- the corresponding composite environment
- a proof that this environment is consistent with the definitions. *)

Definition program := Ctypes.program function.
