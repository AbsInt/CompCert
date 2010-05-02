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

(** Abstract syntax for the Clight language *)

Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import AST.

(** * Abstract syntax *)

(** ** Types *)

(** Clight types are similar to those of C.  They include numeric types,
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
  In Clight, struct and union types [Tstruct id fields] and
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

(** ** Expressions *)

(** Arithmetic and logical operators. *)

Inductive unary_operation : Type :=
  | Onotbool : unary_operation          (**r boolean negation ([!] in C) *)
  | Onotint : unary_operation           (**r integer complement ([~] in C) *)
  | Oneg : unary_operation              (**r opposite (unary [-]) *)
  | Ofabs : unary_operation.            (**r floating-point absolute value *)

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

(** Clight expressions are a large subset of those of C.
  The main omissions are string literals and assignment operators
  ([=], [+=], [++], etc).  In Clight, assignment is a statement,
  not an expression.  

  All expressions are annotated with their types.  An expression
  (type [expr]) is therefore a pair of a type and an expression
  description (type [expr_descr]).
*)

Inductive expr : Type :=
  | Expr: expr_descr -> type -> expr

with expr_descr : Type :=
  | Econst_int: int -> expr_descr       (**r integer literal *)
  | Econst_float: float -> expr_descr   (**r float literal *)
  | Evar: ident -> expr_descr           (**r variable *)
  | Ederef: expr -> expr_descr          (**r pointer dereference (unary [*]) *)
  | Eaddrof: expr -> expr_descr         (**r address-of operator ([&]) *)
  | Eunop: unary_operation -> expr -> expr_descr  (**r unary operation *)
  | Ebinop: binary_operation -> expr -> expr -> expr_descr (**r binary operation *)
  | Ecast: type -> expr -> expr_descr   (**r type cast ([(ty) e]) *)
  | Econdition: expr -> expr -> expr -> expr_descr (**r conditional ([e1 ? e2 : e3]) *)
  | Eandbool: expr -> expr -> expr_descr (**r sequential and ([&&]) *)
  | Eorbool: expr -> expr -> expr_descr (**r sequential or ([||]) *)
  | Esizeof: type -> expr_descr         (**r size of a type *)
  | Efield: expr -> ident -> expr_descr. (**r access to a member of a struct or union *)

(** Extract the type part of a type-annotated Clight expression. *)

Definition typeof (e: expr) : type :=
  match e with Expr de te => te end.

(** ** Statements *)

(** Clight statements include all C statements.
  Only structured forms of [switch] are supported; moreover,
  the [default] case must occur last.  Blocks and block-scoped declarations
  are not supported. *)

Definition label := ident.

Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Sassign : expr -> expr -> statement (**r assignment [lvalue = rvalue] *)
  | Scall: option expr -> expr -> list expr -> statement (**r function call *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
  | Swhile : expr -> statement -> statement   (**r [while] loop *)
  | Sdowhile : expr -> statement -> statement (**r [do] loop *)
  | Sfor: statement -> expr -> statement -> statement -> statement (**r [for] loop *)
  | Sbreak : statement                      (**r [break] statement *)
  | Scontinue : statement                   (**r [continue] statement *)
  | Sreturn : option expr -> statement      (**r [return] statement *)
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

(** Functions can either be defined ([Internal]) or declared as
  external functions ([External]). *)

Inductive fundef : Type :=
  | Internal: function -> fundef
  | External: ident -> typelist -> type -> fundef.

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

Lemma alignof_fields_pos:
  forall f, alignof_fields f > 0.
Proof.
  induction f; simpl.
  omega.
  generalize (Zmax2 (alignof t) (alignof_fields f)). omega.
Qed.

Lemma alignof_pos:
  forall t, alignof t > 0.
Proof.
  induction t; simpl; auto; try omega.
  destruct i; omega.
  destruct f; omega.
  apply alignof_fields_pos.
  apply alignof_fields_pos.
Qed.

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
  forall id fld ofs ty,
  field_offset id fld = OK ofs -> field_type id fld = OK ty ->
  0 <= ofs /\ ofs + sizeof ty <= sizeof_struct fld 0.
Proof.
  intros. eapply field_offset_rec_in_range. unfold field_offset in H; eauto. eauto.
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

(** Third, if a struct is a prefix of another, the offsets of fields
  in common is the same. *)

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

(** The [access_mode] function describes how a variable of the given
type must be accessed:
- [By_value ch]: access by value, i.e. by loading from the address
  of the variable using the memory chunk [ch];
- [By_reference]: access by reference, i.e. by just returning
  the address of the variable;
- [By_nothing]: no access is possible, e.g. for the [void] type.

We currently do not support 64-bit integers and 128-bit floats, so these
have an access mode of [By_nothing].
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

(** Classification of arithmetic operations and comparisons.
  The following [classify_] functions take as arguments the types
  of the arguments of an operation.  They return enough information
  to resolve overloading for this operator applications, such as
  ``both arguments are floats'', or ``the first is a pointer
  and the second is an integer''.  These functions are used to resolve
  overloading both in the dynamic semantics (module [Csem]) and in the
  compiler (module [Cshmgen]).
*)

Inductive classify_add_cases : Type :=
  | add_case_ii: classify_add_cases         (**r int , int *)
  | add_case_ff: classify_add_cases         (**r float , float *)
  | add_case_pi: type -> classify_add_cases (**r ptr or array, int *)
  | add_case_ip: type -> classify_add_cases (**r int, ptr or array *)
  | add_default: classify_add_cases.        (**r other *)

Definition classify_add (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint _ _, Tint _ _ => add_case_ii
  | Tfloat _, Tfloat _ => add_case_ff
  | Tpointer ty, Tint _ _ => add_case_pi ty
  | Tint _ _, Tpointer ty => add_case_ip ty
  | _, _ => add_default
  end.

Inductive classify_sub_cases : Type :=
  | sub_case_ii: classify_sub_cases          (**r int , int *)
  | sub_case_ff: classify_sub_cases          (**r float , float *)
  | sub_case_pi: type -> classify_sub_cases  (**r ptr or array , int *)
  | sub_case_pp: type -> classify_sub_cases  (**r ptr or array , ptr or array *)
  | sub_default: classify_sub_cases .        (**r other *)

Definition classify_sub (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint _ _ , Tint _ _ => sub_case_ii
  | Tfloat _ , Tfloat _ => sub_case_ff
  | Tpointer ty , Tint _ _ => sub_case_pi ty
  | Tpointer ty , Tpointer _ => sub_case_pp ty
  | _ ,_ => sub_default
  end.

Inductive classify_mul_cases : Type:=
  | mul_case_ii: classify_mul_cases (**r int , int *)
  | mul_case_ff: classify_mul_cases (**r float , float *)
  | mul_default: classify_mul_cases . (**r other *)

Definition classify_mul (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint _ _, Tint _ _ => mul_case_ii
  | Tfloat _ , Tfloat _ => mul_case_ff
  | _,_  => mul_default
end.

Inductive classify_div_cases : Type:=
  | div_case_I32unsi: classify_div_cases (**r unsigned int32 , int *)
  | div_case_ii: classify_div_cases    (**r int , int *) 
  | div_case_ff: classify_div_cases    (**r float , float *)
  | div_default: classify_div_cases. (**r other *)

Definition classify_div (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with 
  | Tint I32 Unsigned, Tint _ _ => div_case_I32unsi 
  | Tint _ _ , Tint I32 Unsigned => div_case_I32unsi 
  | Tint _ _ , Tint _ _ => div_case_ii 
  | Tfloat _ , Tfloat _ => div_case_ff 
  | _ ,_ => div_default 
end.

Inductive classify_mod_cases : Type:=
  | mod_case_I32unsi: classify_mod_cases  (**r unsigned I32 , int *)
  | mod_case_ii: classify_mod_cases  (**r int , int *)
  | mod_default: classify_mod_cases . (**r other *)

Definition classify_mod (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned , Tint _ _ => mod_case_I32unsi 
  | Tint _ _ , Tint I32 Unsigned => mod_case_I32unsi 
  | Tint _ _ , Tint _ _ => mod_case_ii 
  | _ , _ => mod_default 
end .

Inductive classify_shr_cases :Type:=
  | shr_case_I32unsi:  classify_shr_cases (**r unsigned I32 , int *)
  | shr_case_ii :classify_shr_cases (**r int , int *)
  | shr_default : classify_shr_cases . (**r other *)

Definition classify_shr (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned , Tint _ _ => shr_case_I32unsi
  | Tint _ _ , Tint _ _ => shr_case_ii
  | _ , _ => shr_default 
  end.

Inductive classify_cmp_cases : Type:=
  | cmp_case_I32unsi: classify_cmp_cases (**r unsigned I32 , int *)
  | cmp_case_ipip: classify_cmp_cases  (**r int|ptr|array , int|ptr|array*)
  | cmp_case_ff: classify_cmp_cases  (**r float , float *)
  | cmp_default: classify_cmp_cases . (**r other *)

Definition classify_cmp (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with 
  | Tint I32 Unsigned , Tint _ _ => cmp_case_I32unsi 
  | Tint _ _ , Tint I32 Unsigned => cmp_case_I32unsi 
  | Tint _ _ , Tint _ _ => cmp_case_ipip
  | Tfloat _ , Tfloat _ => cmp_case_ff
  | Tpointer _ , Tpointer _ => cmp_case_ipip
  | Tpointer _ , Tint _ _ => cmp_case_ipip
  | Tint _ _, Tpointer _ => cmp_case_ipip
  | _ , _ => cmp_default
  end.

Inductive classify_fun_cases : Type:=
  | fun_case_f: typelist -> type -> classify_fun_cases   (**r (pointer to) function *)
  | fun_default: classify_fun_cases . (**r other *)

Definition classify_fun (ty: type) :=
  match ty with 
  | Tfunction args res => fun_case_f args res
  | Tpointer (Tfunction args res) => fun_case_f args res
  | _ => fun_default
  end.

(** Translating Clight types to Cminor types, function signatures,
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

Definition external_function
    (id: ident) (targs: typelist) (tres: type) : AST.external_function :=
  mkextfun id (signature_of_type targs tres).
