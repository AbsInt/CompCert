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

(** Type expressions for the Compcert C and Clight languages *)

Require Import Coqlib.
Require Import AST.
Require Import Errors.

(** * Syntax of types *)

(** Compcert C types are similar to those of C.  They include numeric types,
  pointers, arrays, function types, and composite types (struct and 
  union).  Numeric types (integers and floats) fully specify the
  bit size of the type.  An integer type is a pair of a signed/unsigned
  flag and a bit size: 8, 16, or 32 bits, or the special [IBool] size
  standing for the C99 [_Bool] type. *)

Inductive signedness : Type :=
  | Signed: signedness
  | Unsigned: signedness.

Inductive intsize : Type :=
  | I8: intsize
  | I16: intsize
  | I32: intsize
  | IBool: intsize.

(** Float types come in two sizes: 32 bits (single precision)
  and 64-bit (double precision). *)

Inductive floatsize : Type :=
  | F32: floatsize
  | F64: floatsize.

(** Every type carries a set of attributes.  Currently, only one
  attribute is modeled: [volatile]. *)

Record attr : Type := mk_attr {
  attr_volatile: bool
}.

Definition noattr := {| attr_volatile := false |}.

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
  | Tvoid: type                                    (**r the [void] type *)
  | Tint: intsize -> signedness -> attr -> type    (**r integer types *)
  | Tfloat: floatsize -> attr -> type              (**r floating-point types *)
  | Tpointer: type -> attr -> type                 (**r pointer types ([*ty]) *)
  | Tarray: type -> Z -> attr -> type              (**r array types ([ty[len]]) *)
  | Tfunction: typelist -> type -> type            (**r function types *)
  | Tstruct: ident -> fieldlist -> attr -> type    (**r struct types *)
  | Tunion: ident -> fieldlist -> attr -> type     (**r union types *)
  | Tcomp_ptr: ident -> attr -> type               (**r pointer to named struct or union *)

with typelist : Type :=
  | Tnil: typelist
  | Tcons: type -> typelist -> typelist

with fieldlist : Type :=
  | Fnil: fieldlist
  | Fcons: ident -> type -> fieldlist -> fieldlist.

Lemma type_eq: forall (ty1 ty2: type), {ty1=ty2} + {ty1<>ty2}
with typelist_eq: forall (tyl1 tyl2: typelist), {tyl1=tyl2} + {tyl1<>tyl2}
with fieldlist_eq: forall (fld1 fld2: fieldlist), {fld1=fld2} + {fld1<>fld2}.
Proof.
  assert (forall (x y: intsize), {x=y} + {x<>y}). decide equality.
  assert (forall (x y: signedness), {x=y} + {x<>y}). decide equality.
  assert (forall (x y: floatsize), {x=y} + {x<>y}). decide equality.
  assert (forall (x y: attr), {x=y} + {x<>y}). decide equality. apply bool_dec.
  generalize ident_eq zeq. intros E1 E2. 
  decide equality.
  decide equality.
  generalize ident_eq. intros E1.
  decide equality.
Defined.

Opaque type_eq typelist_eq fieldlist_eq.

(** Extract the attributes of a type. *)

Definition attr_of_type (ty: type) :=
  match ty with
  | Tvoid => noattr
  | Tint sz si a => a
  | Tfloat sz a => a
  | Tpointer elt a => a
  | Tarray elt sz a => a
  | Tfunction args res => noattr
  | Tstruct id fld a => a
  | Tunion id fld a => a
  | Tcomp_ptr id a => a
  end.

Definition type_int32s := Tint I32 Signed noattr.
Definition type_bool := Tint IBool Signed noattr.

(** The usual unary conversion.  Promotes small integer types to [signed int32]
  and degrades array types and function types to pointer types. *)

Definition typeconv (ty: type) : type :=
  match ty with
  | Tint I32 Unsigned _ => ty
  | Tint _ _ a          => Tint I32 Signed a
  | Tarray t sz a       => Tpointer t a
  | Tfunction _ _       => Tpointer ty noattr
  | _                   => ty
  end.

(** * Operations over types *)

(** Natural alignment of a type, in bytes. *)

Fixpoint alignof (t: type) : Z :=
  match t with
  | Tvoid => 1
  | Tint I8 _ _ => 1
  | Tint I16 _ _ => 2
  | Tint I32 _ _ => 4
  | Tint IBool _ _ => 1
  | Tfloat F32 _ => 4
  | Tfloat F64 _ => 8
  | Tpointer _ _ => 4
  | Tarray t' _ _ => alignof t'
  | Tfunction _ _ => 1
  | Tstruct _ fld _ => alignof_fields fld
  | Tunion _ fld _ => alignof_fields fld
  | Tcomp_ptr _ _ => 4
  end

with alignof_fields (f: fieldlist) : Z :=
  match f with
  | Fnil => 1
  | Fcons id t f' => Zmax (alignof t) (alignof_fields f')
  end.

Scheme type_ind2 := Induction for type Sort Prop
  with fieldlist_ind2 := Induction for fieldlist Sort Prop.

Lemma alignof_1248:
  forall t, alignof t = 1 \/ alignof t = 2 \/ alignof t = 4 \/ alignof t = 8
with alignof_fields_1248:
  forall f, alignof_fields f = 1 \/ alignof_fields f = 2 \/ alignof_fields f = 4 \/ alignof_fields f = 8.
Proof.
  induction t; simpl; auto.
  destruct i; auto.
  destruct f; auto.
  induction f; simpl; auto.
  rewrite Zmax_spec. destruct (zlt (alignof_fields f) (alignof t)); auto.
Qed.

Lemma alignof_pos:
  forall t, alignof t > 0.
Proof.
  intros. generalize (alignof_1248 t). omega.
Qed.

Lemma alignof_fields_pos:
  forall f, alignof_fields f > 0.
Proof.
  intros. generalize (alignof_fields_1248 f). omega.
Qed.

(** Size of a type, in bytes. *)

Fixpoint sizeof (t: type) : Z :=
  match t with
  | Tvoid => 1
  | Tint I8 _ _ => 1
  | Tint I16 _ _ => 2
  | Tint I32 _ _ => 4
  | Tint IBool _ _ => 1
  | Tfloat F32 _ => 4
  | Tfloat F64 _ => 8
  | Tpointer _ _ => 4
  | Tarray t' n _ => sizeof t' * Zmax 1 n
  | Tfunction _ _ => 1
  | Tstruct _ fld _ => align (Zmax 1 (sizeof_struct fld 0)) (alignof t)
  | Tunion _ fld _ => align (Zmax 1 (sizeof_union fld)) (alignof t)
  | Tcomp_ptr _ _ => 4
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
  forall sid fld a fid ofs ty,
  field_offset fid fld = OK ofs -> field_type fid fld = OK ty ->
  0 <= ofs /\ ofs + sizeof ty <= sizeof (Tstruct sid fld a).
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
  the address of the l-value (used for arrays and functions);
- [By_copy]: access is by reference, assignment is by copy
  (used for [struct] and [union] types)
- [By_nothing]: no access is possible, e.g. for the [void] type.
*)

Inductive mode: Type :=
  | By_value: memory_chunk -> mode
  | By_reference: mode
  | By_copy: mode
  | By_nothing: mode.

Definition access_mode (ty: type) : mode :=
  match ty with
  | Tint I8 Signed _ => By_value Mint8signed
  | Tint I8 Unsigned _ => By_value Mint8unsigned
  | Tint I16 Signed _ => By_value Mint16signed
  | Tint I16 Unsigned _ => By_value Mint16unsigned
  | Tint I32 _ _ => By_value Mint32
  | Tint IBool _ _ => By_value Mint8unsigned
  | Tfloat F32 _ => By_value Mfloat32
  | Tfloat F64 _ => By_value Mfloat64
  | Tvoid => By_nothing
  | Tpointer _ _ => By_value Mint32
  | Tarray _ _ _ => By_reference
  | Tfunction _ _ => By_reference
  | Tstruct _ _ _ => By_copy
  | Tunion _ _ _ => By_copy
  | Tcomp_ptr _ _ => By_nothing
end.

(** For the purposes of the semantics and the compiler, a type denotes
  a volatile access if it carries the [volatile] attribute and it is
  accessed by value. *)

Definition type_is_volatile (ty: type) : bool :=
  match access_mode ty with
  | By_value _ => attr_volatile (attr_of_type ty)
  | _          => false
  end.

(** Unroll the type of a structure or union field, substituting
    [Tcomp_ptr] by a pointer to the structure. *)

Section UNROLL_COMPOSITE.

Variable cid: ident.
Variable comp: type.

Fixpoint unroll_composite (ty: type) : type :=
  match ty with
  | Tvoid => ty
  | Tint _ _ _ => ty
  | Tfloat _ _ => ty
  | Tpointer t1 a => Tpointer (unroll_composite t1) a
  | Tarray t1 sz a => Tarray (unroll_composite t1) sz a
  | Tfunction t1 t2 => Tfunction (unroll_composite_list t1) (unroll_composite t2)
  | Tstruct id fld a => if ident_eq id cid then ty else Tstruct id (unroll_composite_fields fld) a
  | Tunion id fld a => if ident_eq id cid then ty else Tunion id (unroll_composite_fields fld) a
  | Tcomp_ptr id a => if ident_eq id cid then Tpointer comp a else ty
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
  destruct H. rewrite <- (alignof_unroll_composite (Tstruct i f a)).
  simpl. destruct (ident_eq i cid); simpl. auto. rewrite H0; auto.
  destruct H. rewrite <- (alignof_unroll_composite (Tunion i f a)).
  simpl. destruct (ident_eq i cid); simpl. auto. rewrite H; auto.
  destruct (ident_eq i cid); auto.
  destruct H0. split. congruence.
  intros. rewrite alignof_unroll_composite. rewrite H1. rewrite H. auto.
Qed.

End UNROLL_COMPOSITE.

(** Extracting a type list from a function parameter declaration. *)

Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
  end.

(** Translating C types to Cminor types and function signatures. *)

Definition typ_of_type (t: type) : AST.typ :=
  match t with
  | Tfloat _ _ => AST.Tfloat
  | _ => AST.Tint
  end.

Definition opttyp_of_type (t: type) : option AST.typ :=
  match t with
  | Tvoid => None
  | Tfloat _ _ => Some AST.Tfloat
  | _ => Some AST.Tint
  end.

Fixpoint typlist_of_typelist (tl: typelist) : list AST.typ :=
  match tl with
  | Tnil => nil
  | Tcons hd tl => typ_of_type hd :: typlist_of_typelist tl
  end.

Definition signature_of_type (args: typelist) (res: type) : signature :=
  mksignature (typlist_of_typelist args) (opttyp_of_type res).
