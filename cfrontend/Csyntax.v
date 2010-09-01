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

Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.

(** * Abstract syntax *)

(** ** Types *)

(** Compcert C types are similar to those of C.  They include numeric types,
  pointers, arrays, function types, and composite types (struct and 
  union).  Numeric types (integers and floats) fully specify the
  bit size of the type.  An integer type is a pair of a signed/unsigned
  flag and a bit size: 8, 16 or 32 bits. *)

Inductive signedness : Type :=
  | Signed: signedness
  | Unsigned: signedness.

Inductive intsize : Type :=
  | I8: intsize
  | I16: intsize
  | I32: intsize.

(** Float types come in two sizes: 32 bits (single precision)
  and 64-bit (double precision). *)

Inductive floatsize : Type :=
  | F32: floatsize
  | F64: floatsize.

(** The syntax of type expressions.  Some points to note:
- Array types [Tarray n] carry the size [n] of the array.
  Arrays with unknown sizes are represented by pointer types.
- Function types [Tfunction targs tres] specify the number and types
  of the function arguments (list [targs]), and the type of the
  function result ([tres]).  Variadic functions and old-style unprototyped
  functions are not supported.
- In C, struct and union types are named and compared by name.
  This enables the definition of recursive struct types such as
<<
  struct s1 { int n; struct * s1 next; };
>>
  Note that recursion within types must go through a pointer type.
  For instance, the following is not allowed in C.
<<
  struct s2 { int n; struct s2 next; };
>>
  In Compcert C, struct and union types [Tstruct id fields] and
  [Tunion id fields] are compared by structure: the [fields]
  argument gives the names and types of the members.  The identifier
  [id] is a local name which can be used in conjuction with the
  [Tcomp_ptr] constructor to express recursive types.  [Tcomp_ptr id]
  stands for a pointer type to the nearest enclosing [Tstruct]
  or [Tunion] type named [id].  For instance. the structure [s1]
  defined above in C is expressed by
<<
  Tstruct "s1" (Fcons "n" (Tint I32 Signed)
               (Fcons "next" (Tcomp_ptr "s1")
               Fnil))
>>
  Note that the incorrect structure [s2] above cannot be expressed at
  all, since [Tcomp_ptr] lets us refer to a pointer to an enclosing
  structure or union, but not to the structure or union directly.
*)

Inductive type : Type :=
  | Tvoid: type                            (**r the [void] type *)
  | Tint: intsize -> signedness -> type    (**r integer types *)
  | Tfloat: floatsize -> type              (**r floating-point types *)
  | Tpointer: type -> type                 (**r pointer types ([*ty]) *)
  | Tarray: type -> Z -> type              (**r array types ([ty[len]]) *)
  | Tfunction: typelist -> type -> type    (**r function types *)
  | Tstruct: ident -> fieldlist -> type    (**r struct types *)
  | Tunion: ident -> fieldlist -> type     (**r union types *)
  | Tcomp_ptr: ident -> type               (**r pointer to named struct or union *)

with typelist : Type :=
  | Tnil: typelist
  | Tcons: type -> typelist -> typelist

with fieldlist : Type :=
  | Fnil: fieldlist
  | Fcons: ident -> type -> fieldlist -> fieldlist.

(** The usual unary conversion.  Promotes small integer types to [signed int32]
  and degrades array types and function types to pointer types. *)

Definition typeconv (ty: type) : type :=
  match ty with
  | Tint I32 Unsigned => ty
  | Tint _ _ => Tint I32 Signed
  | Tarray t sz => Tpointer t
  | Tfunction _ _ => Tpointer ty
  | _ => ty
  end.

(** ** Expressions *)

(** Arithmetic and logical operators. *)

Inductive unary_operation : Type :=
  | Onotbool : unary_operation          (**r boolean negation ([!] in C) *)
  | Onotint : unary_operation           (**r integer complement ([~] in C) *)
  | Oneg : unary_operation.             (**r opposite (unary [-]) *)

Inductive binary_operation : Type :=
  | Oadd : binary_operation             (**r addition (binary [+]) *)
  | Osub : binary_operation             (**r subtraction (binary [-]) *)
  | Omul : binary_operation             (**r multiplication (binary [*]) *)
  | Odiv : binary_operation             (**r division ([/]) *)
  | Omod : binary_operation             (**r remainder ([%]) *)
  | Oand : binary_operation             (**r bitwise and ([&]) *)
  | Oor : binary_operation              (**r bitwise or ([|]) *)
  | Oxor : binary_operation             (**r bitwise xor ([^]) *)
  | Oshl : binary_operation             (**r left shift ([<<]) *)
  | Oshr : binary_operation             (**r right shift ([>>]) *)
  | Oeq: binary_operation               (**r comparison ([==]) *)
  | One: binary_operation               (**r comparison ([!=]) *)
  | Olt: binary_operation               (**r comparison ([<]) *)
  | Ogt: binary_operation               (**r comparison ([>]) *)
  | Ole: binary_operation               (**r comparison ([<=]) *)
  | Oge: binary_operation.              (**r comparison ([>=]) *)

Inductive incr_or_decr : Type := Incr | Decr.

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
  | Econdition (r1 r2 r3: expr) (ty: type)  (**r conditional [r1 ? r2 : r3] *)
  | Esizeof (ty': type) (ty: type)                      (**r size of a type *)
  | Eassign (l: expr) (r: expr) (ty: type)          (**r assignment [l = r] *)
  | Eassignop (op: binary_operation) (l: expr) (r: expr) (tyres ty: type)
                                  (**r assignment with arithmetic [l op= r] *)
  | Epostincr (id: incr_or_decr) (l: expr) (ty: type)
                         (**r post-increment [l++] and post-decrement [l--] *)
  | Ecomma (r1 r2: expr) (ty: type)       (**r sequence expression [r1, r2] *)
  | Ecall (r1: expr) (rargs: exprlist) (ty: type)
                                             (**r function call [r1(rargs)] *)
  | Eloc (b: block) (ofs: int) (ty: type)
                       (**r memory location, result of evaluating a l-value *)
  | Eparen (r: expr) (ty: type)                   (**r marked subexpression *)

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
- [Eparen r], which appears during reduction of conditionals [r1 ? r2 : r3].

Some C expressions are derived forms.  Array access [r1[r2]] is expressed
as [*(r1 + r2)].
*)

Definition Eindex (r1 r2: expr) (ty: type) :=
  Ederef (Ebinop Oadd r1 r2 (Tpointer ty)) ty.

(** Pre-increment [++l] and pre-decrement [--l] are expressed as
    [l += 1] and [l -= 1], respectively. *)

Definition Epreincr (id: incr_or_decr) (l: expr) (ty: type) :=
  Eassignop (match id with Incr => Oadd | Decr => Osub end) 
            l (Eval (Vint Int.one) (Tint I32 Signed)) (typeconv ty) ty.

(** Sequential ``and'' [r1 && r2] is viewed as two conditionals
    [r1 ? (r2 ? 1 : 0) : 0]. *)

Definition Eseqand (r1 r2: expr) (ty: type) :=
  Econdition r1 
    (Econdition r2 (Eval (Vint Int.one) (Tint I32 Signed))
                   (Eval (Vint Int.zero) (Tint I32 Signed)) ty)
    (Eval (Vint Int.zero) (Tint I32 Signed))
    ty.
                  
(** Sequential ``or'' [r1 || r2] is viewed as two conditionals
    [r1 ? 1 : (r2 ? 1 : 0)]. *)

Definition Eseqor (r1 r2: expr) (ty: type) :=
  Econdition r1 
    (Eval (Vint Int.one) (Tint I32 Signed))
    (Econdition r2 (Eval (Vint Int.one) (Tint I32 Signed))
                   (Eval (Vint Int.zero) (Tint I32 Signed)) ty)
    ty.

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
  | Esizeof _ ty => ty
  | Eassign _ _ ty => ty
  | Eassignop _ _ _ _ ty => ty
  | Epostincr _ _ ty => ty
  | Ecomma _ _ ty => ty
  | Ecall _ _ ty => ty
  | Eparen _ ty => ty
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
  | LSdefault: statement -> labeled_statements
  | LScase: int -> statement -> labeled_statements -> labeled_statements.

(** ** Functions *)

(** A function definition is composed of its return type ([fn_return]),
  the names and types of its parameters ([fn_params]), the names
  and types of its local variables ([fn_vars]), and the body of the
  function (a statement, [fn_body]). *)

Record function : Type := mkfunction {
  fn_return: type;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_body: statement
}.

Definition var_names (vars: list(ident * type)) : list ident :=
  List.map (@fst ident type) vars.

(** Functions can either be defined ([Internal]) or declared as
  external functions ([External]). *)

Inductive fundef : Type :=
  | Internal: function -> fundef
  | External: external_function -> typelist -> type -> fundef.

(** ** Programs *)

(** A program is a collection of named functions, plus a collection
  of named global variables, carrying their types and optional initialization 
  data.  See module [AST] for more details. *)

Definition program : Type := AST.program fundef type.

(** * Operations over types *)

(** The type of a function definition. *)

Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
  end.

Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External id args res => Tfunction args res
  end.

(** Natural alignment of a type, in bytes. *)

Fixpoint alignof (t: type) : Z :=
  match t with
  | Tvoid => 1
  | Tint I8 _ => 1
  | Tint I16 _ => 2
  | Tint I32 _ => 4
  | Tfloat F32 => 4
  | Tfloat F64 => 8
  | Tpointer _ => 4
  | Tarray t' n => alignof t'
  | Tfunction _ _ => 1
  | Tstruct _ fld => alignof_fields fld
  | Tunion _ fld => alignof_fields fld
  | Tcomp_ptr _ => 4
  end

with alignof_fields (f: fieldlist) : Z :=
  match f with
  | Fnil => 1
  | Fcons id t f' => Zmax (alignof t) (alignof_fields f')
  end.

Scheme type_ind2 := Induction for type Sort Prop
  with fieldlist_ind2 := Induction for fieldlist Sort Prop.

Lemma alignof_power_of_2:
  forall t, exists n, alignof t = two_power_nat n
with alignof_fields_power_of_2:
  forall f, exists n, alignof_fields f = two_power_nat n.
Proof.
  induction t; simpl.
  exists 0%nat; auto.
  destruct i. exists 0%nat; auto. exists 1%nat; auto. exists 2%nat; auto.
  destruct f. exists 2%nat; auto. exists 3%nat; auto.
  exists 2%nat; auto.
  auto.
  exists 0%nat; auto.
  apply alignof_fields_power_of_2.
  apply alignof_fields_power_of_2.
  exists 2%nat; auto.
  induction f; simpl.
  exists 0%nat; auto.
  rewrite Zmax_spec. destruct (zlt (alignof_fields f) (alignof t)); auto.
Qed.

Lemma alignof_pos:
  forall t, alignof t > 0.
Proof.
  intros. destruct (alignof_power_of_2 t) as [p EQ]. rewrite EQ. apply two_power_nat_pos. 
Qed.

Lemma alignof_fields_pos:
  forall f, alignof_fields f > 0.
Proof.
  intros. destruct (alignof_fields_power_of_2 f) as [p EQ]. rewrite EQ. apply two_power_nat_pos. 
Qed.

(*
Fixpoint In_fieldlist (id: ident) (ty: type) (f: fieldlist) : Prop :=
  match f with
  | Fnil => False
  | Fcons id1 ty1 f1 => (id1 = id /\ ty1 = ty) \/ In_fieldlist id ty f1
  end.

Remark divides_max_pow_two:
  forall a b,
  (two_power_nat b | Zmax (two_power_nat a) (two_power_nat b)).
Proof.
  intros.
  rewrite Zmax_spec. destruct (zlt (two_power_nat b) (two_power_nat a)).
  repeat rewrite two_power_nat_two_p in *. 
  destruct (zle (Z_of_nat a) (Z_of_nat b)).
  assert (two_p (Z_of_nat a) <= two_p (Z_of_nat b)). apply two_p_monotone; omega.
  omegaContradiction.
  exists (two_p (Z_of_nat a - Z_of_nat b)). 
  rewrite <- two_p_is_exp. decEq. omega. omega. omega. 
  apply Zdivide_refl.
Qed.

Lemma alignof_each_field:
  forall f id t, In_fieldlist id t f -> (alignof t | alignof_fields f).
Proof.
  induction f; simpl; intros.
  contradiction.
  destruct (alignof_power_of_2 t) as [k1 EQ1].
  destruct (alignof_fields_power_of_2 f) as [k2 EQ2].
  destruct H as [[A B] | A]; subst; rewrite EQ1; rewrite EQ2. 
  rewrite Zmax_comm. apply divides_max_pow_two.
  eapply Zdivide_trans. eapply IHf; eauto. 
  rewrite EQ2. apply divides_max_pow_two.
Qed.
*)

(** Size of a type, in bytes. *)

Fixpoint sizeof (t: type) : Z :=
  match t with
  | Tvoid => 1
  | Tint I8 _ => 1
  | Tint I16 _ => 2
  | Tint I32 _ => 4
  | Tfloat F32 => 4
  | Tfloat F64 => 8
  | Tpointer _ => 4
  | Tarray t' n => sizeof t' * Zmax 1 n
  | Tfunction _ _ => 1
  | Tstruct _ fld => align (Zmax 1 (sizeof_struct fld 0)) (alignof t)
  | Tunion _ fld => align (Zmax 1 (sizeof_union fld)) (alignof t)
  | Tcomp_ptr _ => 4
  end

with sizeof_struct (fld: fieldlist) (pos: Z) {struct fld} : Z :=
  match fld with
  | Fnil => pos
  | Fcons id t fld' => sizeof_struct fld' (align pos (alignof t) + sizeof t)
  end

with sizeof_union (fld: fieldlist) : Z :=
  match fld with
  | Fnil => 0
  | Fcons id t fld' => Zmax (sizeof t) (sizeof_union fld')
  end.

Lemma sizeof_pos:
  forall t, sizeof t > 0.
Proof.
  intro t0.
  apply (type_ind2 (fun t => sizeof t > 0)
                   (fun f => sizeof_union f >= 0 /\ forall pos, pos >= 0 -> sizeof_struct f pos >= 0));
  intros; simpl; auto; try omega.
  destruct i; omega.
  destruct f; omega.
  apply Zmult_gt_0_compat. auto. generalize (Zmax1 1 z); omega.
  destruct H. 
  generalize (align_le (Zmax 1 (sizeof_struct f 0)) (alignof_fields f) (alignof_fields_pos f)). 
  generalize (Zmax1 1 (sizeof_struct f 0)). omega. 
  generalize (align_le (Zmax 1 (sizeof_union f)) (alignof_fields f) (alignof_fields_pos f)). 
  generalize (Zmax1 1 (sizeof_union f)). omega. 
  split. omega. auto.
  destruct H0. split; intros.
  generalize (Zmax2 (sizeof t) (sizeof_union f)). omega.
  apply H1. 
  generalize (align_le pos (alignof t) (alignof_pos t)). omega.
Qed.

Lemma sizeof_struct_incr:
  forall fld pos, pos <= sizeof_struct fld pos.
Proof.
  induction fld; intros; simpl. omega. 
  eapply Zle_trans. 2: apply IHfld.
  apply Zle_trans with (align pos (alignof t)). 
  apply align_le. apply alignof_pos. 
  assert (sizeof t > 0) by apply sizeof_pos. omega.
Qed.

Lemma sizeof_alignof_compat:
  forall t, (alignof t | sizeof t).
Proof.
  induction t; simpl; try (apply Zdivide_refl).
  apply Zdivide_mult_l. auto.
  apply align_divides. apply alignof_fields_pos.
  apply align_divides. apply alignof_fields_pos.
Qed.

(** Byte offset for a field in a struct or union.
  Field are laid out consecutively, and padding is inserted
  to align each field to the natural alignment for its type. *)

Open Local Scope string_scope.

Fixpoint field_offset_rec (id: ident) (fld: fieldlist) (pos: Z)
                              {struct fld} : res Z :=
  match fld with
  | Fnil => Error (MSG "Unknown field " :: CTX id :: nil)
  | Fcons id' t fld' =>
      if ident_eq id id'
      then OK (align pos (alignof t))
      else field_offset_rec id fld' (align pos (alignof t) + sizeof t)
  end.

Definition field_offset (id: ident) (fld: fieldlist) : res Z :=
  field_offset_rec id fld 0.

Fixpoint field_type (id: ident) (fld: fieldlist) {struct fld} : res type :=
  match fld with
  | Fnil => Error (MSG "Unknown field " :: CTX id :: nil)
  | Fcons id' t fld' => if ident_eq id id' then OK t else field_type id fld'
  end.

(** Some sanity checks about field offsets.  First, field offsets are 
  within the range of acceptable offsets. *)

Remark field_offset_rec_in_range:
  forall id ofs ty fld pos,
  field_offset_rec id fld pos = OK ofs -> field_type id fld = OK ty ->
  pos <= ofs /\ ofs + sizeof ty <= sizeof_struct fld pos.
Proof.
  intros until ty. induction fld; simpl.
  congruence.
  destruct (ident_eq id i); intros.
  inv H. inv H0. split. apply align_le. apply alignof_pos. apply sizeof_struct_incr.
  exploit IHfld; eauto. intros [A B]. split; auto. 
  eapply Zle_trans; eauto. apply Zle_trans with (align pos (alignof t)).
  apply align_le. apply alignof_pos. generalize (sizeof_pos t). omega. 
Qed.

Lemma field_offset_in_range:
  forall sid fld fid ofs ty,
  field_offset fid fld = OK ofs -> field_type fid fld = OK ty ->
  0 <= ofs /\ ofs + sizeof ty <= sizeof (Tstruct sid fld).
Proof.
  intros. exploit field_offset_rec_in_range; eauto. intros [A B].
  split. auto.  simpl. eapply Zle_trans. eauto.
  eapply Zle_trans. eapply Zle_max_r. apply align_le. apply alignof_fields_pos.
Qed.

(** Second, two distinct fields do not overlap *)

Lemma field_offset_no_overlap:
  forall id1 ofs1 ty1 id2 ofs2 ty2 fld,
  field_offset id1 fld = OK ofs1 -> field_type id1 fld = OK ty1 ->
  field_offset id2 fld = OK ofs2 -> field_type id2 fld = OK ty2 ->
  id1 <> id2 ->
  ofs1 + sizeof ty1 <= ofs2 \/ ofs2 + sizeof ty2 <= ofs1.
Proof.
  intros until ty2. intros fld0 A B C D NEQ.
  assert (forall fld pos,
  field_offset_rec id1 fld pos = OK ofs1 -> field_type id1 fld = OK ty1 ->
  field_offset_rec id2 fld pos = OK ofs2 -> field_type id2 fld = OK ty2 ->
  ofs1 + sizeof ty1 <= ofs2 \/ ofs2 + sizeof ty2 <= ofs1).
  induction fld; intro pos; simpl. congruence.
  destruct (ident_eq id1 i); destruct (ident_eq id2 i).
  congruence. 
  subst i. intros. inv H; inv H0.
  exploit field_offset_rec_in_range. eexact H1. eauto. tauto.  
  subst i. intros. inv H1; inv H2.
  exploit field_offset_rec_in_range. eexact H. eauto. tauto. 
  intros. eapply IHfld; eauto.

  apply H with fld0 0; auto.
Qed.

(** Third, if a struct is a prefix of another, the offsets of common fields
    are the same. *)

Fixpoint fieldlist_app (fld1 fld2: fieldlist) {struct fld1} : fieldlist :=
  match fld1 with
  | Fnil => fld2
  | Fcons id ty fld => Fcons id ty (fieldlist_app fld fld2)
  end.

Lemma field_offset_prefix:
  forall id ofs fld2 fld1,
  field_offset id fld1 = OK ofs ->
  field_offset id (fieldlist_app fld1 fld2) = OK ofs.
Proof.
  intros until fld2.
  assert (forall fld1 pos, 
    field_offset_rec id fld1 pos = OK ofs ->
    field_offset_rec id (fieldlist_app fld1 fld2) pos = OK ofs).
  induction fld1; intros pos; simpl. congruence.
  destruct (ident_eq id i); auto.
  intros. unfold field_offset; auto. 
Qed.

(** Fourth, the position of each field respects its alignment. *)

Lemma field_offset_aligned:
  forall id fld ofs ty,
  field_offset id fld = OK ofs -> field_type id fld = OK ty ->
  (alignof ty | ofs).
Proof.
  assert (forall id ofs ty fld pos,
          field_offset_rec id fld pos = OK ofs -> field_type id fld = OK ty ->
          (alignof ty | ofs)).
  induction fld; simpl; intros.
  discriminate.
  destruct (ident_eq id i). inv H; inv H0. 
  apply align_divides. apply alignof_pos. 
  eapply IHfld; eauto.
  intros. eapply H with (pos := 0); eauto.
Qed.

(** The [access_mode] function describes how a l-value of the given
type must be accessed:
- [By_value ch]: access by value, i.e. by loading from the address
  of the l-value using the memory chunk [ch];
- [By_reference]: access by reference, i.e. by just returning
  the address of the l-value;
- [By_nothing]: no access is possible, e.g. for the [void] type.
*)

Inductive mode: Type :=
  | By_value: memory_chunk -> mode
  | By_reference: mode
  | By_nothing: mode.

Definition access_mode (ty: type) : mode :=
  match ty with
  | Tint I8 Signed => By_value Mint8signed
  | Tint I8 Unsigned => By_value Mint8unsigned
  | Tint I16 Signed => By_value Mint16signed
  | Tint I16 Unsigned => By_value Mint16unsigned
  | Tint I32 _ => By_value Mint32
  | Tfloat F32 => By_value Mfloat32
  | Tfloat F64 => By_value Mfloat64
  | Tvoid => By_nothing
  | Tpointer _ => By_value Mint32
  | Tarray _ _ => By_reference
  | Tfunction _ _ => By_reference
  | Tstruct _ fList => By_nothing
  | Tunion _ fList => By_nothing
  | Tcomp_ptr _ => By_value Mint32
end.

(** Unroll the type of a structure or union field, substituting
    [Tcomp_ptr] by a pointer to the structure. *)

Section UNROLL_COMPOSITE.

Variable cid: ident.
Variable comp: type.

Fixpoint unroll_composite (ty: type) : type :=
  match ty with
  | Tvoid => ty
  | Tint _ _ => ty
  | Tfloat _ => ty
  | Tpointer t1 => Tpointer (unroll_composite t1)
  | Tarray t1 sz => Tarray (unroll_composite t1) sz
  | Tfunction t1 t2 => Tfunction (unroll_composite_list t1) (unroll_composite t2)
  | Tstruct id fld => if ident_eq id cid then ty else Tstruct id (unroll_composite_fields fld)
  | Tunion id fld => if ident_eq id cid then ty else Tunion id (unroll_composite_fields fld)
  | Tcomp_ptr id => if ident_eq id cid then Tpointer comp else ty
  end

with unroll_composite_list (tl: typelist) : typelist :=
  match tl with
  | Tnil => Tnil
  | Tcons t1 tl' => Tcons (unroll_composite t1) (unroll_composite_list tl')
  end

with unroll_composite_fields (fld: fieldlist) : fieldlist :=
  match fld with
  | Fnil => Fnil
  | Fcons id ty fld' => Fcons id (unroll_composite ty) (unroll_composite_fields fld')
  end.

Lemma alignof_unroll_composite:
  forall ty, alignof (unroll_composite ty) = alignof ty.
Proof.
  apply (type_ind2 (fun ty => alignof (unroll_composite ty) = alignof ty)
                   (fun fld => alignof_fields (unroll_composite_fields fld) = alignof_fields fld));
  simpl; intros; auto.
  destruct (ident_eq i cid); auto. 
  destruct (ident_eq i cid); auto. 
  destruct (ident_eq i cid); auto.
  decEq; auto.
Qed.

Lemma sizeof_unroll_composite:
  forall ty, sizeof (unroll_composite ty) = sizeof ty.
Proof.
Opaque alignof.
  apply (type_ind2 (fun ty => sizeof (unroll_composite ty) = sizeof ty)
                   (fun fld => 
                      sizeof_union (unroll_composite_fields fld) = sizeof_union fld
                   /\ forall pos,
                      sizeof_struct (unroll_composite_fields fld) pos = sizeof_struct fld pos));
  simpl; intros; auto.
  congruence.
  destruct H. rewrite <- (alignof_unroll_composite (Tstruct i f)).
  simpl. destruct (ident_eq i cid); simpl. auto. rewrite H0; auto.
  destruct H. rewrite <- (alignof_unroll_composite (Tunion i f)).
  simpl. destruct (ident_eq i cid); simpl. auto. rewrite H; auto.
  destruct (ident_eq i cid); auto.
  destruct H0. split. congruence.
  intros. rewrite alignof_unroll_composite. rewrite H1. rewrite H. auto.
Qed.

End UNROLL_COMPOSITE.

(** Classification of arithmetic operations and comparisons.
  The following [classify_] functions take as arguments the types
  of the arguments of an operation.  They return enough information
  to resolve overloading for this operator applications, such as
  ``both arguments are floats'', or ``the first is a pointer
  and the second is an integer''.  These functions are used to resolve
  overloading both in the dynamic semantics (module [Csem]), in the
  type system (module [Ctyping]), and in the compiler (module
  [Cshmgen]).
*)

Inductive classify_neg_cases : Type :=
  | neg_case_i(s: signedness)              (**r int *)
  | neg_case_f                             (**r float *)
  | neg_default.

Definition classify_neg (ty: type) : classify_neg_cases :=
  match ty with
  | Tint I32 Unsigned => neg_case_i Unsigned
  | Tint _ _ => neg_case_i Signed
  | Tfloat _ => neg_case_f
  | _ => neg_default
  end.

Inductive classify_notint_cases : Type :=
  | notint_case_i(s: signedness)              (**r int *)
  | notint_default.

Definition classify_notint (ty: type) : classify_notint_cases :=
  match ty with
  | Tint I32 Unsigned => notint_case_i Unsigned
  | Tint _ _ => notint_case_i Signed
  | _ => notint_default
  end.

(** The following describes types that can be interpreted as a boolean:
  integers, floats, pointers.  It is used for the semantics of 
  the [!] and [?] operators, as well as the [if], [while], [for] statements. *)

Inductive classify_bool_cases : Type :=
  | bool_case_ip                          (**r integer or pointer *)
  | bool_case_f                           (**r float *)
  | bool_default.

Definition classify_bool (ty: type) : classify_bool_cases :=
  match typeconv ty with
  | Tint _ _ => bool_case_ip
  | Tpointer _ => bool_case_ip
  | Tfloat _ => bool_case_f
  | _ => bool_default
  end.

Inductive classify_add_cases : Type :=
  | add_case_ii(s: signedness)         (**r int, int *)
  | add_case_ff                        (**r float, float *)
  | add_case_if(s: signedness)         (**r int, float *)
  | add_case_fi(s: signedness)         (**r float, int *)
  | add_case_pi(ty: type)              (**r pointer, int *)
  | add_case_ip(ty: type)              (**r int, pointer *)
  | add_default.

Definition classify_add (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned, Tint _ _ => add_case_ii Unsigned
  | Tint _ _, Tint I32 Unsigned => add_case_ii Unsigned
  | Tint _ _, Tint _ _ => add_case_ii Signed
  | Tfloat _, Tfloat _ => add_case_ff
  | Tint _ sg, Tfloat _ => add_case_if sg
  | Tfloat _, Tint _ sg => add_case_fi sg
  | Tpointer ty, Tint _ _ => add_case_pi ty
  | Tint _ _, Tpointer ty => add_case_ip ty
  | _, _ => add_default
  end.

Inductive classify_sub_cases : Type :=
  | sub_case_ii(s: signedness)          (**r int , int *)
  | sub_case_ff                         (**r float , float *)
  | sub_case_if(s: signedness)          (**r int, float *)
  | sub_case_fi(s: signedness)          (**r float, int *)
  | sub_case_pi(ty: type)               (**r pointer, int *)
  | sub_case_pp(ty: type)               (**r pointer, pointer *)
  | sub_default.

Definition classify_sub (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned, Tint _ _ => sub_case_ii Unsigned
  | Tint _ _, Tint I32 Unsigned => sub_case_ii Unsigned
  | Tint _ _, Tint _ _ => sub_case_ii Signed
  | Tfloat _ , Tfloat _ => sub_case_ff
  | Tint _ sg, Tfloat _ => sub_case_if sg
  | Tfloat _, Tint _ sg => sub_case_fi sg
  | Tpointer ty , Tint _ _ => sub_case_pi ty
  | Tpointer ty , Tpointer _ => sub_case_pp ty
  | _ ,_ => sub_default
  end.

Inductive classify_mul_cases : Type:=
  | mul_case_ii(s: signedness) (**r int , int *)
  | mul_case_ff                (**r float , float *)
  | mul_case_if(s: signedness) (**r int, float *)
  | mul_case_fi(s: signedness) (**r float, int *)
  | mul_default.

Definition classify_mul (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned, Tint _ _ => mul_case_ii Unsigned
  | Tint _ _, Tint I32 Unsigned => mul_case_ii Unsigned
  | Tint _ _, Tint _ _ => mul_case_ii Signed
  | Tfloat _ , Tfloat _ => mul_case_ff
  | Tint _ sg, Tfloat _ => mul_case_if sg
  | Tfloat _, Tint _ sg => mul_case_fi sg
  | _,_  => mul_default
end.

Inductive classify_div_cases : Type:=
  | div_case_ii(s: signedness) (**r int , int *)
  | div_case_ff                (**r float , float *)
  | div_case_if(s: signedness) (**r int, float *)
  | div_case_fi(s: signedness) (**r float, int *)
  | div_default.

Definition classify_div (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned, Tint _ _ => div_case_ii Unsigned
  | Tint _ _, Tint I32 Unsigned => div_case_ii Unsigned
  | Tint _ _, Tint _ _ => div_case_ii Signed
  | Tfloat _ , Tfloat _ => div_case_ff
  | Tint _ sg, Tfloat _ => div_case_if sg
  | Tfloat _, Tint _ sg => div_case_fi sg
  | _,_  => div_default
end.

(** The following is common to binary integer-only operators:
  modulus, bitwise "and", "or", and "xor". *)

Inductive classify_binint_cases : Type:=
  | binint_case_ii(s: signedness) (**r int , int *)
  | binint_default.

Definition classify_binint (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned, Tint _ _ => binint_case_ii Unsigned
  | Tint _ _, Tint I32 Unsigned => binint_case_ii Unsigned
  | Tint _ _, Tint _ _ => binint_case_ii Signed
  | _,_  => binint_default
end.

(** The following is common to shift operators [<<] and [>>]. *)

Inductive classify_shift_cases : Type:=
  | shift_case_ii(s: signedness) (**r int , int *)
  | shift_default.

Definition classify_shift (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned, Tint _ _ => shift_case_ii Unsigned
  | Tint _ _, Tint _ _ => shift_case_ii Signed
  | _,_  => shift_default
end.

Inductive classify_cmp_cases : Type:=
  | cmp_case_iiu               (**r unsigned int, unsigned int *)
  | cmp_case_ipip              (**r int-or-pointer, int-or-pointer *)
  | cmp_case_ff                (**r float , float *)
  | cmp_case_if(s: signedness) (**r int, float *)
  | cmp_case_fi(s: signedness) (**r float, int *)
  | cmp_default.

Definition classify_cmp (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with 
  | Tint I32 Unsigned , Tint _ _ => cmp_case_iiu
  | Tint _ _ , Tint I32 Unsigned => cmp_case_iiu
  | Tint _ _ , Tint _ _ => cmp_case_ipip
  | Tfloat _ , Tfloat _ => cmp_case_ff
  | Tint _ sg, Tfloat _ => cmp_case_if sg
  | Tfloat _, Tint _ sg => cmp_case_fi sg
  | Tpointer _ , Tpointer _ => cmp_case_ipip
  | Tpointer _ , Tint _ _ => cmp_case_ipip
  | Tint _ _, Tpointer _ => cmp_case_ipip
  | _ , _ => cmp_default
  end.

Inductive classify_fun_cases : Type:=
  | fun_case_f (targs: typelist) (tres: type) (**r (pointer to) function *)
  | fun_default.

Definition classify_fun (ty: type) :=
  match ty with 
  | Tfunction args res => fun_case_f args res
  | Tpointer (Tfunction args res) => fun_case_f args res
  | _ => fun_default
  end.

(** Translating C types to Cminor types, function signatures,
  and external functions. *)

Definition typ_of_type (t: type) : AST.typ :=
  match t with
  | Tfloat _ => AST.Tfloat
  | _ => AST.Tint
  end.

Definition opttyp_of_type (t: type) : option AST.typ :=
  match t with
  | Tvoid => None
  | Tfloat _ => Some AST.Tfloat
  | _ => Some AST.Tint
  end.

Fixpoint typlist_of_typelist (tl: typelist) : list AST.typ :=
  match tl with
  | Tnil => nil
  | Tcons hd tl => typ_of_type hd :: typlist_of_typelist tl
  end.

Definition signature_of_type (args: typelist) (res: type) : signature :=
  mksignature (typlist_of_typelist args) (opttyp_of_type res).
