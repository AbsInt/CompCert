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
Require Import Maps.
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
*)

Inductive type : Type :=
  | Tvoid: type                                    (**r the [void] type *)
  | Tint: intsize -> signedness -> attr -> type    (**r integer types *)
  | Tlong: signedness -> attr -> type              (**r 64-bit integer types *)
  | Tfloat: floatsize -> attr -> type              (**r floating-point types *)
  | Tpointer: type -> attr -> type                 (**r pointer types ([*ty]) *)
  | Tarray: type -> Z -> attr -> type              (**r array types ([ty[len]]) *)
  | Tfunction: typelist -> type -> calling_convention -> type    (**r function types *)
  | Tstruct: ident -> attr -> type                 (**r struct types *)
  | Tunion: ident -> attr -> type                  (**r union types *)
with typelist : Type :=
  | Tnil: typelist
  | Tcons: type -> typelist -> typelist.

Lemma type_eq: forall (ty1 ty2: type), {ty1=ty2} + {ty1<>ty2}
with typelist_eq: forall (tyl1 tyl2: typelist), {tyl1=tyl2} + {tyl1<>tyl2}.
Proof.
  assert (forall (x y: intsize), {x=y} + {x<>y}) by decide equality.
  assert (forall (x y: signedness), {x=y} + {x<>y}) by decide equality.
  assert (forall (x y: floatsize), {x=y} + {x<>y}) by decide equality.
  assert (forall (x y: attr), {x=y} + {x<>y}).
  { decide equality. decide equality. apply N.eq_dec. apply bool_dec. }
  generalize ident_eq zeq bool_dec ident_eq; intros.
  decide equality.
  decide equality.
  decide equality.
Defined.

Opaque type_eq typelist_eq.

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
  | Tstruct id a => a
  | Tunion id a => a
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
  | Tstruct id a => Tstruct id (f a)
  | Tunion id a => Tunion id (f a)
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

(** Syntax for [struct] and [union] definitions.  [struct] and [union]
  are collectively called "composites".  Each compilation unit
  comes with a list of top-level definitions of composites. *)

Inductive struct_or_union : Type := Struct | Union.

Definition members : Type := list (ident * type).

Inductive composite_definition : Type :=
  Composite (id: ident) (su: struct_or_union) (m: members) (a: attr).

(** For type-checking, compilation and semantics purposes, the composite
  definitions are collected in the following [composite_env] environment.
  The [composite] record contains additional information compared with
  the [composite_definition], such as size and alignment information. *)

Record composite : Type := {
  co_su: struct_or_union;
  co_members: members;
  co_attr: attr;
  co_sizeof: Z;
  co_alignof: Z;
  co_rank: nat;
  co_sizeof_pos: co_sizeof >= 0;
  co_alignof_two_p: exists n, co_alignof = two_power_nat n;
  co_sizeof_alignof: (co_alignof | co_sizeof)
}.

Definition composite_env : Type := PTree.t composite.

(** * Operations over types *)

(** ** Conversions *)

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

(** ** Complete types *)

(** A type is complete if it fully describes an object.
  All struct and union names appearing in the type must be defined,
  unless they occur under a pointer or function type.  [void] and
  function types are incomplete types. *)

Fixpoint complete_type (env: composite_env) (t: type) : bool :=
  match t with
  | Tvoid => false
  | Tint _ _ _ => true
  | Tlong _ _ => true
  | Tfloat _ _ => true
  | Tpointer _ _ => true
  | Tarray t' _ _ => complete_type env t'
  | Tfunction _ _ _ => false
  | Tstruct id _ | Tunion id _ =>
      match env!id with Some co => true | None => false end
  end.

Definition complete_or_function_type (env: composite_env) (t: type) : bool :=
  match t with
  | Tfunction _ _ _ => true
  | _ => complete_type env t
  end.

(** ** Alignment of a type *)

(** Adjust the natural alignment [al] based on the attributes [a] attached
  to the type.  If an "alignas" attribute is given, use it as alignment
  in preference to [al]. *)

Definition align_attr (a: attr) (al: Z) : Z :=
  match attr_alignas a with
  | Some l => two_p (Z.of_N l)
  | None => al
  end.

(** In the ISO C standard, alignment is defined only for complete
  types.  However, it is convenient that [alignof] is a total
  function.  For incomplete types, it returns 1. *)

Fixpoint alignof (env: composite_env) (t: type) : Z :=
  align_attr (attr_of_type t)
   (match t with
      | Tvoid => 1
      | Tint I8 _ _ => 1
      | Tint I16 _ _ => 2
      | Tint I32 _ _ => 4
      | Tint IBool _ _ => 1
      | Tlong _ _ => Archi.align_int64
      | Tfloat F32 _ => 4
      | Tfloat F64 _ => Archi.align_float64
      | Tpointer _ _ => 4
      | Tarray t' _ _ => alignof env t'
      | Tfunction _ _ _ => 1
      | Tstruct id _ | Tunion id _ =>
          match env!id with Some co => co_alignof co | None => 1 end
    end).

Remark align_attr_two_p:
  forall al a,
  (exists n, al = two_power_nat n) ->
  (exists n, align_attr a al = two_power_nat n).
Proof.
  intros. unfold align_attr. destruct (attr_alignas a).   
  exists (N.to_nat n). rewrite two_power_nat_two_p. rewrite N_nat_Z. auto.
  auto.
Qed.

Lemma alignof_two_p:
  forall env t, exists n, alignof env t = two_power_nat n.
Proof.
  induction t; apply align_attr_two_p; simpl.
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
  apply IHt.
  exists 0%nat; auto.
  destruct (env!i). apply co_alignof_two_p. exists 0%nat; auto.
  destruct (env!i). apply co_alignof_two_p. exists 0%nat; auto.
Qed.

Lemma alignof_pos:
  forall env t, alignof env t > 0.
Proof.
  intros. destruct (alignof_two_p env t) as [n EQ]. rewrite EQ. apply two_power_nat_pos.
Qed.

(** ** Size of a type *)

(** In the ISO C standard, size is defined only for complete
  types.  However, it is convenient that [sizeof] is a total
  function.  For [void] and function types, we follow GCC and define
  their size to be 1.  For undefined structures and unions, the size is 
  arbitrarily taken to be 0.
*)

Fixpoint sizeof (env: composite_env) (t: type) : Z :=
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
  | Tarray t' n _ => sizeof env t' * Z.max 0 n
  | Tfunction _ _ _ => 1
  | Tstruct id _ | Tunion id _ =>
      match env!id with Some co => co_sizeof co | None => 0 end
  end.

Lemma sizeof_pos:
  forall env t, sizeof env t >= 0.
Proof.
  induction t; simpl; try omega.
  destruct i; omega.
  destruct f; omega.
  change 0 with (0 * Z.max 0 z) at 2. apply Zmult_ge_compat_r. auto. xomega.
  destruct (env!i). apply co_sizeof_pos. omega.
  destruct (env!i). apply co_sizeof_pos. omega.
Qed.

(** The size of a type is an integral multiple of its alignment,
  unless the alignment was artificially increased with the [__Alignas]
  attribute. *)

Fixpoint naturally_aligned (t: type) : Prop :=
  attr_alignas (attr_of_type t) = None /\
  match t with
  | Tarray t' _ _ => naturally_aligned t'
  | _ => True
  end.

Lemma sizeof_alignof_compat:
  forall env t, naturally_aligned t -> (alignof env t | sizeof env t).
Proof.
  induction t; intros [A B]; unfold alignof, align_attr; rewrite A; simpl. 
- apply Zdivide_refl.
- destruct i; apply Zdivide_refl.
- exists (8 / Archi.align_int64); reflexivity. 
- destruct f. apply Zdivide_refl. exists (8 / Archi.align_float64); reflexivity. 
- apply Zdivide_refl.
- apply Z.divide_mul_l; auto. 
- apply Zdivide_refl.
- destruct (env!i). apply co_sizeof_alignof. apply Zdivide_0. 
- destruct (env!i). apply co_sizeof_alignof. apply Zdivide_0. 
Qed.

(** ** Size and alignment for composite definitions *)

(** The alignment for a structure or union is the max of the alignment
  of its members. *)

Fixpoint alignof_composite (env: composite_env) (m: members) : Z :=
  match m with
  | nil => 1
  | (id, t) :: m' => Z.max (alignof env t) (alignof_composite env m')
  end.

(** The size of a structure corresponds to its layout: fields are
  laid out consecutively, and padding is inserted to align
  each field to the alignment for its type. *)

Fixpoint sizeof_struct (env: composite_env) (cur: Z) (m: members) : Z :=
  match m with
  | nil => cur
  | (id, t) :: m' => sizeof_struct env (align cur (alignof env t) + sizeof env t) m'
  end.

(** The size of an union is the max of the sizes of its members. *)

Fixpoint sizeof_union (env: composite_env) (m: members) : Z :=
  match m with
  | nil => 0
  | (id, t) :: m' => Z.max (sizeof env t) (sizeof_union env m')
  end.

Lemma alignof_composite_two_p:
  forall env m, exists n, alignof_composite env m = two_power_nat n.
Proof.
  induction m as [|[id t]]; simpl. 
- exists 0%nat; auto.
- apply Z.max_case; auto. apply alignof_two_p.
Qed.

Lemma alignof_composite_pos:
  forall env m a, align_attr a (alignof_composite env m) > 0.
Proof.
  intros.
  exploit align_attr_two_p. apply (alignof_composite_two_p env m). 
  instantiate (1 := a). intros [n EQ]. 
  rewrite EQ; apply two_power_nat_pos.
Qed.

Lemma sizeof_struct_incr:
  forall env m cur, cur <= sizeof_struct env cur m.
Proof.
  induction m as [|[id t]]; simpl; intros.
- omega.
- apply Zle_trans with (align cur (alignof env t)). 
  apply align_le. apply alignof_pos.
  apply Zle_trans with (align cur (alignof env t) + sizeof env t).
  generalize (sizeof_pos env t); omega. 
  apply IHm.
Qed.

Lemma sizeof_union_pos:
  forall env m, 0 <= sizeof_union env m.
Proof.
  induction m as [|[id t]]; simpl; xomega.
Qed.

(** ** Byte offset for a field of a structure *)

(** [field_offset env id fld] returns the byte offset for field [id]
  in a structure whose members are [fld].  Fields are laid out
  consecutively, and padding is inserted to align each field to the
  alignment for its type. *)

Fixpoint field_offset_rec (env: composite_env) (id: ident) (fld: members) (pos: Z)
                          {struct fld} : res Z :=
  match fld with
  | nil => Error (MSG "Unknown field " :: CTX id :: nil)
  | (id', t) :: fld' =>
      if ident_eq id id'
      then OK (align pos (alignof env t))
      else field_offset_rec env id fld' (align pos (alignof env t) + sizeof env t)
  end.

Definition field_offset (env: composite_env) (id: ident) (fld: members) : res Z :=
  field_offset_rec env id fld 0.

Fixpoint field_type (id: ident) (fld: members) {struct fld} : res type :=
  match fld with
  | nil => Error (MSG "Unknown field " :: CTX id :: nil)
  | (id', t) :: fld' => if ident_eq id id' then OK t else field_type id fld'
  end.

(** Some sanity checks about field offsets.  First, field offsets are 
  within the range of acceptable offsets. *)

Remark field_offset_rec_in_range:
  forall env id ofs ty fld pos,
  field_offset_rec env id fld pos = OK ofs -> field_type id fld = OK ty ->
  pos <= ofs /\ ofs + sizeof env ty <= sizeof_struct env pos fld.
Proof.
  intros until ty. induction fld as [|[i t]]; simpl; intros.
- discriminate.
- destruct (ident_eq id i); intros.
  inv H. inv H0. split.
  apply align_le. apply alignof_pos. apply sizeof_struct_incr.
  exploit IHfld; eauto. intros [A B]. split; auto. 
  eapply Zle_trans; eauto. apply Zle_trans with (align pos (alignof env t)).
  apply align_le. apply alignof_pos. generalize (sizeof_pos env t). omega. 
Qed.

Lemma field_offset_in_range:
  forall env fld id ofs ty,
  field_offset env id fld = OK ofs -> field_type id fld = OK ty ->
  0 <= ofs /\ ofs + sizeof env ty <= sizeof_struct env 0 fld.
Proof.
  intros. eapply field_offset_rec_in_range; eauto.
Qed.

(** Second, two distinct fields do not overlap *)

Lemma field_offset_no_overlap:
  forall env id1 ofs1 ty1 id2 ofs2 ty2 fld,
  field_offset env id1 fld = OK ofs1 -> field_type id1 fld = OK ty1 ->
  field_offset env id2 fld = OK ofs2 -> field_type id2 fld = OK ty2 ->
  id1 <> id2 ->
  ofs1 + sizeof env ty1 <= ofs2 \/ ofs2 + sizeof env ty2 <= ofs1.
Proof.
  intros until fld. unfold field_offset. generalize 0 as pos.
  induction fld as [|[i t]]; simpl; intros.
- discriminate.
- destruct (ident_eq id1 i); destruct (ident_eq id2 i).
+ congruence. 
+ subst i. inv H; inv H0.
  exploit field_offset_rec_in_range. eexact H1. eauto. tauto.  
+ subst i. inv H1; inv H2.
  exploit field_offset_rec_in_range. eexact H. eauto. tauto. 
+ eapply IHfld; eauto.
Qed.

(** Third, if a struct is a prefix of another, the offsets of common fields
    are the same. *)

Lemma field_offset_prefix:
  forall env id ofs fld2 fld1,
  field_offset env id fld1 = OK ofs ->
  field_offset env id (fld1 ++ fld2) = OK ofs.
Proof.
  intros until fld1. unfold field_offset. generalize 0 as pos. 
  induction fld1 as [|[i t]]; simpl; intros.
- discriminate.
- destruct (ident_eq id i); auto. 
Qed.

(** Fourth, the position of each field respects its alignment. *)

Lemma field_offset_aligned:
  forall env id fld ofs ty,
  field_offset env id fld = OK ofs -> field_type id fld = OK ty ->
  (alignof env ty | ofs).
Proof.
  intros until ty. unfold field_offset. generalize 0 as pos. revert fld. 
  induction fld as [|[i t]]; simpl; intros.
- discriminate.
- destruct (ident_eq id i).
+ inv H; inv H0. apply align_divides. apply alignof_pos.
+ eauto.
Qed.

(** ** Access modes *)

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
  | Tstruct _ _ => By_copy
  | Tunion _ _ => By_copy
end.

(** For the purposes of the semantics and the compiler, a type denotes
  a volatile access if it carries the [volatile] attribute and it is
  accessed by value. *)

Definition type_is_volatile (ty: type) : bool :=
  match access_mode ty with
  | By_value _ => attr_volatile (attr_of_type ty)
  | _          => false
  end.

(** ** Alignment for block copy operations *)

(** A variant of [alignof] for use in block copy operations.
  Block copy operations do not support alignments greater than 8,
  and require the size to be an integral multiple of the alignment. *)

Fixpoint alignof_blockcopy (env: composite_env) (t: type) : Z :=
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
  | Tarray t' _ _ => alignof_blockcopy env t'
  | Tfunction _ _ _ => 1
  | Tstruct id _ | Tunion id _ =>
      match env!id with
      | Some co => Z.min 8 (co_alignof co)
      | None => 1
      end
  end.

Lemma alignof_blockcopy_1248:
  forall env ty, let a := alignof_blockcopy env ty in a = 1 \/ a = 2 \/ a = 4 \/ a = 8.
Proof.
  assert (X: forall co, let a := Zmin 8 (co_alignof co) in
             a = 1 \/ a = 2 \/ a = 4 \/ a = 8).
  {
    intros. destruct (co_alignof_two_p co) as [n EQ]. unfold a; rewrite EQ. 
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
  destruct (env!i); auto. 
  destruct (env!i); auto.
Qed.

Lemma alignof_blockcopy_pos:
  forall env ty, alignof_blockcopy env ty > 0.
Proof.
  intros. generalize (alignof_blockcopy_1248 env ty). simpl. intuition omega.
Qed.

Lemma sizeof_alignof_blockcopy_compat:
  forall env ty, (alignof_blockcopy env ty | sizeof env ty).
Proof.
  assert (X: forall co, (Z.min 8 (co_alignof co) | co_sizeof co)).
  {
    intros. apply Zdivide_trans with (co_alignof co). 2: apply co_sizeof_alignof.
    destruct (co_alignof_two_p co) as [n EQ]. rewrite EQ.
    destruct n. apply Zdivide_refl.
    destruct n. apply Zdivide_refl.
    destruct n. apply Zdivide_refl.
    apply Z.min_case. 
    exists (two_p (Z.of_nat n)). 
    change 8 with (two_p 3). 
    rewrite <- two_p_is_exp by omega.
    rewrite two_power_nat_two_p. rewrite !inj_S. f_equal. omega.
    apply Zdivide_refl.
  }
  induction ty; simpl.
  apply Zdivide_refl.
  apply Zdivide_refl.
  apply Zdivide_refl.
  apply Zdivide_refl.
  apply Zdivide_refl.
  apply Z.divide_mul_l. auto.
  apply Zdivide_refl.
  destruct (env!i). apply X. apply Zdivide_0. 
  destruct (env!i). apply X. apply Zdivide_0. 
Qed.

(** Type ranks *)

(** The rank of a type is a nonnegative integer that measures the direct nesting
  of arrays, struct and union types.  It does not take into account indirect
  nesting such as a struct type that appears under a pointer or function type.
  Type ranks ensure that type expressions (ignoring pointer and function types)
  have an inductive structure. *)

Fixpoint rank_type (ce: composite_env) (t: type) : nat :=
  match t with
  | Tarray t' _ _ => S (rank_type ce t')
  | Tstruct id _ | Tunion id _ =>
      match ce!id with
      | None => O
      | Some co => S (co_rank co)
      end
  | _ => O
  end.

Fixpoint rank_members (ce: composite_env) (m: members) : nat :=
  match m with
  | nil => 0%nat
  | (id, t) :: m => Peano.max (rank_type ce t) (rank_members ce m)
  end.

(** ** C types and back-end types *)

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

(** * Construction of the composite environment *)

Definition sizeof_composite (env: composite_env) (su: struct_or_union) (m: members) : Z :=
  match su with
  | Struct => sizeof_struct env 0 m
  | Union  => sizeof_union env m
  end.

Lemma sizeof_composite_pos:
  forall env su m, 0 <= sizeof_composite env su m.
Proof.
  intros. destruct su; simpl.
  apply sizeof_struct_incr.
  apply sizeof_union_pos.
Qed.

Fixpoint complete_members (env: composite_env) (m: members) : bool :=
  match m with
  | nil => true
  | (id, t) :: m' => complete_type env t && complete_members env m'
  end.

Lemma complete_member:
  forall env id t m,
  In (id, t) m -> complete_members env m = true -> complete_type env t = true.
Proof.
  induction m as [|[id1 t1] m]; simpl; intuition auto.
  InvBooleans; inv H1; auto.
  InvBooleans; eauto.
Qed.

(** Convert a composite definition to its internal representation.
  The size and alignment of the composite are determined at this time.
  The alignment takes into account the [__Alignas] attributes
  associated with the definition.  The size is rounded up to a multiple
  of the alignment.  

  The conversion fails if a type of a member is not complete.  This rules
  out incorrect recursive definitions such as
<<
    struct s { int x; struct s next; }
>>
  Here, when we process the definition of [struct s], the identifier [s]
  is not bound yet in the composite environment, hence field [next]
  has an incomplete type.  However, recursions that go through a pointer type
  are correctly handled:
<<
    struct s { int x; struct s * next; }
>>
  Here, [next] has a pointer type, which is always complete, even though
  [s] is not yet bound to a composite.
*)

Program Definition composite_of_def
     (env: composite_env) (id: ident) (su: struct_or_union) (m: members) (a: attr)
     : res composite :=
  match env!id, complete_members env m return _ with
  | Some _, _ =>
      Error (MSG "Multiple definitions of struct or union " :: CTX id :: nil)
  | None, false =>
      Error (MSG "Incomplete struct or union " :: CTX id :: nil)
  | None, true =>
      let al := align_attr a (alignof_composite env m) in
      OK {| co_su := su;
            co_members := m;
            co_attr := a;
            co_sizeof := align (sizeof_composite env su m) al;
            co_alignof := al;
            co_rank := rank_members env m;
            co_sizeof_pos := _;
            co_alignof_two_p := _;
            co_sizeof_alignof := _ |}
  end.
Next Obligation.
  apply Zle_ge. eapply Zle_trans. eapply sizeof_composite_pos. 
  apply align_le; apply alignof_composite_pos.
Qed.
Next Obligation.
  apply align_attr_two_p. apply alignof_composite_two_p.
Qed.
Next Obligation.
  apply align_divides. apply alignof_composite_pos.
Qed.

(** The composite environment for a program is obtained by entering
  its composite definitions in sequence.  The definitions are assumed
  to be listed in dependency order: the definition of a composite
  must precede all uses of this composite, unless the use is under
  a pointer or function type. *)

Local Open Scope error_monad_scope.

Fixpoint add_composite_definitions (env: composite_env) (defs: list composite_definition) : res composite_env :=
  match defs with
  | nil => OK env
  | Composite id su m a :: defs =>
      do co <- composite_of_def env id su m a;
      add_composite_definitions (PTree.set id co env) defs
  end.

Definition build_composite_env (defs: list composite_definition) :=
  add_composite_definitions (PTree.empty _) defs.

(** Stability properties for alignments, sizes, and ranks.  If the type is
  complete in a composite environment [env], its size, alignment, and rank
  are unchanged if we add more definitions to [env]. *)

Section STABILITY.

Variables env env': composite_env.
Hypothesis extends: forall id co, env!id = Some co -> env'!id = Some co.

Lemma alignof_stable:
  forall t, complete_type env t = true -> alignof env' t = alignof env t.
Proof.
  induction t; simpl; intros; f_equal; auto.
  destruct (env!i) as [co|] eqn:E; try discriminate. 
  erewrite extends by eauto. auto.
  destruct (env!i) as [co|] eqn:E; try discriminate. 
  erewrite extends by eauto. auto.
Qed.

Lemma sizeof_stable:
  forall t, complete_type env t = true -> sizeof env' t = sizeof env t.
Proof.
  induction t; simpl; intros; auto.
  rewrite IHt by auto. auto.
  destruct (env!i) as [co|] eqn:E; try discriminate. 
  erewrite extends by eauto. auto.
  destruct (env!i) as [co|] eqn:E; try discriminate. 
  erewrite extends by eauto. auto.
Qed.

Lemma complete_type_stable:
  forall t, complete_type env t = true -> complete_type env' t = true.
Proof.
  induction t; simpl; intros; auto.
  destruct (env!i) as [co|] eqn:E; try discriminate. 
  erewrite extends by eauto. auto.
  destruct (env!i) as [co|] eqn:E; try discriminate. 
  erewrite extends by eauto. auto.
Qed.

Lemma rank_type_stable:
  forall t, complete_type env t = true -> rank_type env' t = rank_type env t.
Proof.
  induction t; simpl; intros; auto.
  destruct (env!i) as [co|] eqn:E; try discriminate. 
  erewrite extends by eauto. auto.
  destruct (env!i) as [co|] eqn:E; try discriminate. 
  erewrite extends by eauto. auto.
Qed.

Lemma alignof_composite_stable:
  forall m, complete_members env m = true -> alignof_composite env' m = alignof_composite env m.
Proof.
  induction m as [|[id t]]; simpl; intros. 
  auto.
  InvBooleans. rewrite alignof_stable by auto. rewrite IHm by auto. auto.
Qed.

Lemma sizeof_struct_stable:
  forall m pos, complete_members env m = true -> sizeof_struct env' pos m = sizeof_struct env pos m.
Proof.
  induction m as [|[id t]]; simpl; intros.
  auto.
  InvBooleans. rewrite alignof_stable by auto. rewrite sizeof_stable by auto. 
  rewrite IHm by auto. auto.
Qed.

Lemma sizeof_union_stable:
  forall m, complete_members env m = true -> sizeof_union env' m = sizeof_union env m.
Proof.
  induction m as [|[id t]]; simpl; intros.
  auto.
  InvBooleans. rewrite sizeof_stable by auto. rewrite IHm by auto. auto.
Qed.

Lemma sizeof_composite_stable:
  forall su m, complete_members env m = true -> sizeof_composite env' su m = sizeof_composite env su m.
Proof.
  intros. destruct su; simpl. 
  apply sizeof_struct_stable; auto. 
  apply sizeof_union_stable; auto.
Qed.

Lemma complete_members_stable:
  forall m, complete_members env m = true -> complete_members env' m = true.
Proof.
  induction m as [|[id t]]; simpl; intros.
  auto.
  InvBooleans. rewrite complete_type_stable by auto. rewrite IHm by auto. auto.
Qed.

Lemma rank_members_stable:
  forall m, complete_members env m = true -> rank_members env' m = rank_members env m.
Proof.
  induction m as [|[id t]]; simpl; intros.
  auto.
  InvBooleans. f_equal; auto. apply rank_type_stable; auto.
Qed.

End STABILITY.

Lemma add_composite_definitions_incr:
  forall id co defs env1 env2,
  add_composite_definitions env1 defs = OK env2 ->
  env1!id = Some co -> env2!id = Some co.
Proof.
  induction defs; simpl; intros.
- inv H; auto.
- destruct a; monadInv H. 
  eapply IHdefs; eauto. rewrite PTree.gso; auto.
  red; intros; subst id0. unfold composite_of_def in EQ. rewrite H0 in EQ; discriminate.
Qed.

(** It follows that the sizes and alignments contained in the composite
  environment produced by [build_composite_env] are consistent with
  the sizes and alignments of the members of the composite types. *)

Record composite_consistent (env: composite_env) (co: composite) : Prop := {
  co_consistent_complete:
     complete_members env (co_members co) = true;
  co_consistent_alignof:
     co_alignof co = align_attr (co_attr co) (alignof_composite env (co_members co));
  co_consistent_sizeof:
     co_sizeof co = align (sizeof_composite env (co_su co) (co_members co)) (co_alignof co);
  co_consistent_rank:
     co_rank co = rank_members env (co_members co)
}.

Definition composite_env_consistent (env: composite_env) : Prop :=
  forall id co, env!id = Some co -> composite_consistent env co.

Theorem build_composite_env_consistent:
  forall defs env, build_composite_env defs = OK env -> composite_env_consistent env.
Proof.
  cut (forall defs env0 env,
       add_composite_definitions env0 defs = OK env ->
       composite_env_consistent env0 ->
       composite_env_consistent env).
  intros. eapply H; eauto. red; intros. rewrite PTree.gempty in H1; discriminate.
  induction defs as [|d1 defs]; simpl; intros.
- inv H; auto.
- destruct d1; monadInv H.
  eapply IHdefs; eauto.
  set (env1 := PTree.set id x env0) in *.
  unfold composite_of_def in EQ.
  destruct (env0!id) eqn:E; try discriminate. 
  destruct (complete_members env0 m) eqn:C; inversion EQ; clear EQ.
  assert (forall id1 co1, env0!id1 = Some co1 -> env1!id1 = Some co1).
  { intros. unfold env1. rewrite PTree.gso; auto. congruence. }
  red; intros. unfold env1 in H2; rewrite PTree.gsspec in H2; destruct (peq id0 id).
+ subst id0. inversion H2; clear H2. subst co. 
(*
  assert (A: alignof_composite env1 m = alignof_composite env0 m)
  by (apply alignof_composite_stable; assumption).
*)
  rewrite <- H1; constructor; simpl.
* eapply complete_members_stable; eauto. 
* f_equal. symmetry. apply alignof_composite_stable; auto. 
* f_equal. symmetry. apply sizeof_composite_stable; auto. 
* symmetry. apply rank_members_stable; auto.
+ exploit H0; eauto. intros [P Q R S]. 
  constructor; intros.
* eapply complete_members_stable; eauto.
* rewrite Q. f_equal. symmetry. apply alignof_composite_stable; auto.
* rewrite R. f_equal. symmetry. apply sizeof_composite_stable; auto.
* rewrite S. symmetry; apply rank_members_stable; auto.
Qed.

(** Moreover, every composite definition is reflected in the composite environment. *)

Theorem build_composite_env_charact:
  forall id su m a defs env,
  build_composite_env defs = OK env ->
  In (Composite id su m a) defs ->
  exists co, env!id = Some co /\ co_members co = m /\ co_attr co = a /\ co_su co = su.
Proof.
  intros until defs. unfold build_composite_env. generalize (PTree.empty composite) as env0. 
  revert defs. induction defs as [|d1 defs]; simpl; intros.
- contradiction.
- destruct d1; monadInv H.
  destruct H0; [idtac|eapply IHdefs;eauto]. inv H. 
  unfold composite_of_def in EQ. 
  destruct (env0!id) eqn:E; try discriminate. 
  destruct (complete_members env0 m) eqn:C; simplify_eq EQ. clear EQ; intros EQ.
  exists x.
  split. eapply add_composite_definitions_incr; eauto. apply PTree.gss.
  subst x; auto.
Qed.

(** As a corollay, in a consistent environment, the rank of a composite type
  is strictly greater than the ranks of its member types. *)

Remark rank_type_members:
  forall ce id t m, In (id, t) m -> (rank_type ce t <= rank_members ce m)%nat.
Proof.
  induction m; simpl; intros; intuition auto.
  subst a. xomega.
  xomega.
Qed.

Lemma rank_struct_member:
  forall ce id a co id1 t1,
  composite_env_consistent ce ->
  ce!id = Some co ->
  In (id1, t1) (co_members co) ->
  (rank_type ce t1 < rank_type ce (Tstruct id a))%nat.
Proof.
  intros; simpl. rewrite H0.
  erewrite co_consistent_rank by eauto.
  exploit (rank_type_members ce); eauto.
  omega.
Qed.

Lemma rank_union_member:
  forall ce id a co id1 t1,
  composite_env_consistent ce ->
  ce!id = Some co ->
  In (id1, t1) (co_members co) ->
  (rank_type ce t1 < rank_type ce (Tunion id a))%nat.
Proof.
  intros; simpl. rewrite H0.
  erewrite co_consistent_rank by eauto.
  exploit (rank_type_members ce); eauto.
  omega.
Qed.
