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
Require Archi.

(** * Syntax of types *)

(** Compcert C types are similar to those of C.  They include numeric types,
  pointers, arrays, function types, and composite types (struct and 
  union).  Numeric types (integers and floats) fully specify the
  bit size of the type.  An integer type is a pair of a signed/unsigned
  flag and a bit size: 8, 16, or 32 bits, or the special [IBool] size
  standing for the C99 [_Bool] type.  64-bit integers are treated separately. *)

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

(** Every type carries a set of attributes.  Currently, only two
  attributes are modeled: [volatile] and [_Alignas(n)] (from ISO C 2011). *)

Record attr : Type := mk_attr {
  attr_volatile: bool;
  attr_alignas: option N         (**r log2 of required alignment *)
}.

Definition noattr := {| attr_volatile := false; attr_alignas := None |}.

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
  | Tlong: signedness -> attr -> type              (**r 64-bit integer types *)
  | Tfloat: floatsize -> attr -> type              (**r floating-point types *)
  | Tpointer: type -> attr -> type                 (**r pointer types ([*ty]) *)
  | Tarray: type -> Z -> attr -> type              (**r array types ([ty[len]]) *)
  | Tfunction: typelist -> type -> calling_convention -> type    (**r function types *)
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
  assert (forall (x y: intsize), {x=y} + {x<>y}) by decide equality.
  assert (forall (x y: signedness), {x=y} + {x<>y}) by decide equality.
  assert (forall (x y: floatsize), {x=y} + {x<>y}) by decide equality.
  assert (forall (x y: attr), {x=y} + {x<>y}).
  { decide equality. decide equality. apply N.eq_dec. apply bool_dec. }
  generalize ident_eq zeq bool_dec. intros E1 E2 E3.
  decide equality.
  decide equality.
  decide equality.
  generalize ident_eq. intros E1. decide equality.
Defined.

Opaque type_eq typelist_eq fieldlist_eq.

(** Extract the attributes of a type. *)

Definition attr_of_type (ty: type) :=
  match ty with
  | Tvoid => noattr
  | Tint sz si a => a
  | Tlong si a => a
  | Tfloat sz a => a
  | Tpointer elt a => a
  | Tarray elt sz a => a
  | Tfunction args res cc => noattr
  | Tstruct id fld a => a
  | Tunion id fld a => a
  | Tcomp_ptr id a => a
  end.

(** Change the top-level attributes of a type *)

Definition change_attributes (f: attr -> attr) (ty: type) : type :=
  match ty with
  | Tvoid => ty
  | Tint sz si a => Tint sz si (f a)
  | Tlong si a => Tlong si (f a)
  | Tfloat sz a => Tfloat sz (f a)
  | Tpointer elt a => Tpointer elt (f a)
  | Tarray elt sz a => Tarray elt sz (f a)
  | Tfunction args res cc => ty
  | Tstruct id fld a => Tstruct id fld (f a)
  | Tunion id fld a => Tunion id fld (f a)
  | Tcomp_ptr id a => Tcomp_ptr id (f a)
  end.

(** Erase the top-level attributes of a type *)

Definition remove_attributes (ty: type) : type :=
  change_attributes (fun _ => noattr) ty.

(** Add extra attributes to the top-level attributes of a type *)

Definition attr_union (a1 a2: attr) : attr :=
  {| attr_volatile := a1.(attr_volatile) || a2.(attr_volatile);
     attr_alignas :=
       match a1.(attr_alignas), a2.(attr_alignas) with
       | None, al => al
       | al, None => al
       | Some n1, Some n2 => Some (N.max n1 n2)
       end 
  |}.

Definition merge_attributes (ty: type) (a: attr) : type :=
  change_attributes (attr_union a) ty.

Definition type_int32s := Tint I32 Signed noattr.
Definition type_bool := Tint IBool Signed noattr.

(** The usual unary conversion.  Promotes small integer types to [signed int32]
  and degrades array types and function types to pointer types. 
  Attributes are erased. *)

Definition typeconv (ty: type) : type :=
  match ty with
  | Tint (I8 | I16 | IBool) _ _ => Tint I32 Signed noattr
  | Tarray t sz a       => Tpointer t noattr
  | Tfunction _ _ _     => Tpointer ty noattr
  | _                   => remove_attributes ty
  end.

(** Default conversion for arguments to an unprototyped or variadic function.
  Like [typeconv] but also converts single floats to double floats. *)

Definition default_argument_conversion (ty: type) : type :=
  match ty with
  | Tint (I8 | I16 | IBool) _ _ => Tint I32 Signed noattr
  | Tfloat _ _          => Tfloat F64 noattr
  | Tarray t sz a       => Tpointer t noattr
  | Tfunction _ _ _     => Tpointer ty noattr
  | _                   => remove_attributes ty
  end.

(** * Operations over types *)

(** Alignment of a type, in bytes. *)

Fixpoint alignof (t: type) : Z :=
  match attr_alignas (attr_of_type t) with
  | Some l => two_p (Z.of_N l)
  | None =>
      match t with
      | Tvoid => 1
      | Tint I8 _ _ => 1
      | Tint I16 _ _ => 2
      | Tint I32 _ _ => 4
      | Tint IBool _ _ => 1
      | Tlong _ _ => Archi.align_int64
      | Tfloat F32 _ => 4
      | Tfloat F64 _ => Archi.align_float64
      | Tpointer _ _ => 4
      | Tarray t' _ _ => alignof t'
      | Tfunction _ _ _ => 1
      | Tstruct _ fld _ => alignof_fields fld
      | Tunion _ fld _ => alignof_fields fld
      | Tcomp_ptr _ _ => 4
      end
  end

with alignof_fields (f: fieldlist) : Z :=
  match f with
  | Fnil => 1
  | Fcons id t f' => Zmax (alignof t) (alignof_fields f')
  end.

Scheme type_ind2 := Induction for type Sort Prop
  with fieldlist_ind2 := Induction for fieldlist Sort Prop.

Lemma alignof_two_p:
  forall t, exists n, alignof t = two_power_nat n
with alignof_fields_two_p:
  forall f, exists n, alignof_fields f = two_power_nat n.
Proof.
  assert (X: forall t a,
    (exists n, a = two_power_nat n) ->
    exists n,
    match attr_alignas (attr_of_type t) with
    | Some l => two_p (Z.of_N l)
    | None => a
    end = two_power_nat n).
  {
    intros.  
    destruct (attr_alignas (attr_of_type t)).
    exists (N.to_nat n). rewrite two_power_nat_two_p. rewrite N_nat_Z. auto.
    auto.
  }
  induction t; apply X; simpl; auto.
  exists 0%nat; auto.
  destruct i.
    exists 0%nat; auto.
    exists 1%nat; auto.
    exists 2%nat; auto.
    exists 0%nat; auto.
    (exists 2%nat; reflexivity) || (exists 3%nat; reflexivity).
  destruct f.
    exists 2%nat; auto.
    (exists 2%nat; reflexivity) || (exists 3%nat; reflexivity).
  exists 2%nat; auto.
  exists 0%nat; auto.
  exists 2%nat; auto.
  induction f; simpl.
  exists 0%nat; auto.
  apply Z.max_case; auto.
Qed.

Lemma alignof_pos:
  forall t, alignof t > 0.
Proof.
  intros. destruct (alignof_two_p t) as [n EQ]. rewrite EQ. apply two_power_nat_pos.
Qed.

Lemma alignof_fields_pos:
  forall f, alignof_fields f > 0.
Proof.
  intros. destruct (alignof_fields_two_p f) as [n EQ]. rewrite EQ. apply two_power_nat_pos.
Qed.

(** Size of a type, in bytes. *)

Fixpoint sizeof (t: type) : Z :=
  match t with
  | Tvoid => 1
  | Tint I8 _ _ => 1
  | Tint I16 _ _ => 2
  | Tint I32 _ _ => 4
  | Tint IBool _ _ => 1
  | Tlong _ _ => 8
  | Tfloat F32 _ => 4
  | Tfloat F64 _ => 8
  | Tpointer _ _ => 4
  | Tarray t' n _ => sizeof t' * Zmax 0 n
  | Tfunction _ _ _ => 1
  | Tstruct _ fld _ => align (sizeof_struct fld 0) (alignof t)
  | Tunion _ fld _ => align (sizeof_union fld) (alignof t)
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
  forall t, sizeof t >= 0
with sizeof_struct_incr:
  forall fld pos, pos <= sizeof_struct fld pos.
Proof.
- Local Opaque alignof.
  assert (X: forall n t, n >= 0 -> align n (alignof t) >= 0).
  {
    intros. generalize (align_le n (alignof t) (alignof_pos t)). omega.
  }
  induction t; simpl; try xomega.
  destruct i; omega.
  destruct f; omega.
  change 0 with (0 * Z.max 0 z) at 2. apply Zmult_ge_compat_r. auto. xomega. 
  apply X. apply Zle_ge. apply sizeof_struct_incr. 
  apply X. induction f; simpl; xomega.
- induction fld; intros; simpl.
  omega. 
  eapply Zle_trans. 2: apply IHfld.
  apply Zle_trans with (align pos (alignof t)). 
  apply align_le. apply alignof_pos.
  generalize (sizeof_pos t); omega.
Qed.

Fixpoint naturally_aligned (t: type) : Prop :=
  match t with
  | Tint _ _ a | Tlong _ a | Tfloat _ a | Tpointer _ a | Tcomp_ptr _ a =>
      attr_alignas a = None
  | Tarray t' _ a =>
      attr_alignas a = None /\ naturally_aligned t'
  | Tvoid | Tfunction _ _ _ | Tstruct _ _ _ | Tunion _ _ _ =>
      True
  end.

Lemma sizeof_alignof_compat:
  forall t, naturally_aligned t -> (alignof t | sizeof t).
Proof.
Local Transparent alignof.
  induction t; simpl; intros.
- apply Zdivide_refl.
- rewrite H. destruct i; apply Zdivide_refl.
- rewrite H. exists (8 / Archi.align_int64); reflexivity. 
- rewrite H. destruct f. apply Zdivide_refl. exists (8 / Archi.align_float64); reflexivity. 
- rewrite H; apply Zdivide_refl.
- destruct H. rewrite H. apply Z.divide_mul_l; auto. 
- apply Zdivide_refl.
- change (alignof (Tstruct i f a) | align (sizeof_struct f 0) (alignof (Tstruct i f a))).
  apply align_divides. apply alignof_pos.
- change (alignof (Tunion i f a) | align (sizeof_union f) (alignof (Tunion i f a))).
  apply align_divides. apply alignof_pos.
- rewrite H; apply Zdivide_refl.
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
  split. auto.
Local Opaque alignof. 
  simpl. eapply Zle_trans; eauto. 
  apply align_le. apply alignof_pos. 
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
  | Tlong _ _ => By_value Mint64
  | Tfloat F32 _ => By_value Mfloat32
  | Tfloat F64 _ => By_value Mfloat64
  | Tvoid => By_nothing
  | Tpointer _ _ => By_value Mint32
  | Tarray _ _ _ => By_reference
  | Tfunction _ _ _ => By_reference
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
  | Tlong _ _ => ty
  | Tfloat _ _ => ty
  | Tpointer t1 a => Tpointer (unroll_composite t1) a
  | Tarray t1 sz a => Tarray (unroll_composite t1) sz a
  | Tfunction t1 t2 a => Tfunction (unroll_composite_list t1) (unroll_composite t2) a
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

Lemma attr_of_type_unroll_composite:
  forall ty, attr_of_type (unroll_composite ty) = attr_of_type ty.
Proof.
  intros. destruct ty; simpl; auto; destruct (ident_eq i cid); auto.
Qed.

Lemma alignof_unroll_composite:
  forall ty, alignof (unroll_composite ty) = alignof ty.
Proof.
Local Transparent alignof.
  apply (type_ind2 (fun ty => alignof (unroll_composite ty) = alignof ty)
                   (fun fld => alignof_fields (unroll_composite_fields fld) = alignof_fields fld));
  simpl; intros; auto.
  rewrite H; auto.
  destruct (ident_eq i cid); auto. simpl. rewrite H; auto.
  destruct (ident_eq i cid); auto. simpl. rewrite H; auto.
  destruct (ident_eq i cid); auto. congruence.
Qed.

Lemma sizeof_unroll_composite:
  forall ty, sizeof (unroll_composite ty) = sizeof ty.
Proof.
Local Opaque alignof.
  apply (type_ind2 (fun ty => sizeof (unroll_composite ty) = sizeof ty)
                   (fun fld => 
                      sizeof_union (unroll_composite_fields fld) = sizeof_union fld
                   /\ forall pos,
                      sizeof_struct (unroll_composite_fields fld) pos = sizeof_struct fld pos));
  simpl; intros; auto.
- rewrite H. auto.
- rewrite <- (alignof_unroll_composite (Tstruct i f a)). simpl.
  destruct H. destruct (ident_eq i cid). auto. simpl. rewrite H0. auto.
- rewrite <- (alignof_unroll_composite (Tunion i f a)). simpl.
  destruct H. destruct (ident_eq i cid). auto. simpl. rewrite H. auto.
- destruct (ident_eq i cid); auto. 
- destruct H0. split. 
  + congruence.
  + intros. rewrite H1. rewrite H. rewrite alignof_unroll_composite. auto.
Qed.

End UNROLL_COMPOSITE.

(** A variant of [alignof] for use in block copy operations.
  Block copy operations do not support alignments greater than 8,
  and require the size to be an integral multiple of the alignment. *)

Fixpoint alignof_blockcopy (t: type) : Z :=
  match t with
  | Tvoid => 1
  | Tint I8 _ _ => 1
  | Tint I16 _ _ => 2
  | Tint I32 _ _ => 4
  | Tint IBool _ _ => 1
  | Tlong _ _ => 8
  | Tfloat F32 _ => 4
  | Tfloat F64 _ => 8
  | Tpointer _ _ => 4
  | Tarray t' _ _ => alignof_blockcopy t'
  | Tfunction _ _ _ => 1
  | Tstruct _ fld _ => Zmin 8 (alignof t)
  | Tunion _ fld _ => Zmin 8 (alignof t)
  | Tcomp_ptr _ _ => 4
  end.

Lemma alignof_blockcopy_1248:
  forall ty, let a := alignof_blockcopy ty in a = 1 \/ a = 2 \/ a = 4 \/ a = 8.
Proof.
  assert (X: forall ty, let a := Zmin 8 (alignof ty) in
             a = 1 \/ a = 2 \/ a = 4 \/ a = 8).
  {
    intros. destruct (alignof_two_p ty) as [n EQ]. unfold a; rewrite EQ. 
    destruct n; auto.
    destruct n; auto.
    destruct n; auto.
    right; right; right. apply Z.min_l.
    rewrite two_power_nat_two_p. rewrite ! inj_S. 
    change 8 with (two_p 3). apply two_p_monotone. omega.
  }
  induction ty; simpl; auto.
  destruct i; auto.
  destruct f; auto.
Qed.

Lemma alignof_blockcopy_pos:
  forall ty, alignof_blockcopy ty > 0.
Proof.
  intros. generalize (alignof_blockcopy_1248 ty). simpl. intuition omega.
Qed.

Lemma sizeof_alignof_blockcopy_compat:
  forall ty, (alignof_blockcopy ty | sizeof ty).
Proof.
  assert (X: forall ty sz, (alignof ty | sz) -> (Zmin 8 (alignof ty) | sz)).
  {
    intros. destruct (alignof_two_p ty) as [n EQ]. rewrite EQ in *.
    destruct n; auto.
    destruct n; auto.
    destruct n; auto.
    eapply Zdivide_trans; eauto. 
    apply Z.min_case. 
    replace (two_power_nat (S(S(S n)))) with (two_p (3 + Z.of_nat n)).
    rewrite two_p_is_exp by omega. change (two_p 3) with 8.
    exists (two_p (Z.of_nat n)). ring.
    rewrite two_power_nat_two_p. rewrite !inj_S. f_equal. omega.
    apply Zdivide_refl.
  }
  Local Opaque alignof.
  induction ty; simpl.
  apply Zdivide_refl.
  destruct i; apply Zdivide_refl.
  apply Zdivide_refl.
  destruct f; apply Zdivide_refl.
  apply Zdivide_refl.
  apply Z.divide_mul_l. auto.
  apply Zdivide_refl.
  apply X. apply align_divides. apply alignof_pos.
  apply X. apply align_divides. apply alignof_pos.
  apply Zdivide_refl.
Qed.

(** Extracting a type list from a function parameter declaration. *)

Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
  end.

(** Translating C types to Cminor types and function signatures. *)

Definition typ_of_type (t: type) : AST.typ :=
  match t with
  | Tfloat F32 _ => AST.Tsingle
  | Tfloat _ _ => AST.Tfloat
  | Tlong _ _ => AST.Tlong
  | _ => AST.Tint
  end.

Definition opttyp_of_type (t: type) : option AST.typ :=
  match t with
  | Tvoid => None
  | Tfloat F32 _ => Some AST.Tsingle
  | Tfloat _ _ => Some AST.Tfloat
  | Tlong _ _ => Some AST.Tlong
  | _ => Some AST.Tint
  end.

Fixpoint typlist_of_typelist (tl: typelist) : list AST.typ :=
  match tl with
  | Tnil => nil
  | Tcons hd tl => typ_of_type hd :: typlist_of_typelist tl
  end.

Definition signature_of_type (args: typelist) (res: type) (cc: calling_convention): signature :=
  mksignature (typlist_of_typelist args) (opttyp_of_type res) cc.

