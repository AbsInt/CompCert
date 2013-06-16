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

(** Arithmetic and logical operators for the Compcert C and Clight languages *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Ctypes.

(** * Syntax of operators. *)

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

(** * Type classification and semantics of operators. *)

(** Most C operators are overloaded (they apply to arguments of various
  types) and their semantics depend on the types of their arguments.
  The following [classify_*] functions take as arguments the types
  of the arguments of an operation.  They return enough information
  to resolve overloading for this operator applications, such as
  ``both arguments are floats'', or ``the first is a pointer
  and the second is an integer''.  This classification is used in the
  compiler (module [Cshmgen]) to resolve overloading statically.

  The [sem_*] functions below compute the result of an operator
  application.  Since operators are overloaded, the result depends
  both on the static types of the arguments and on their run-time values.
  The corresponding [classify_*] function is first called on the 
  types of the arguments to resolve static overloading.  It is then
  followed by a case analysis on the values of the arguments. *)

(** ** Casts and truth values *)

Inductive classify_cast_cases : Type :=
  | cast_case_neutral                   (**r int|pointer -> int32|pointer *)
  | cast_case_i2i (sz2:intsize) (si2:signedness)   (**r int -> int *)
  | cast_case_f2f (sz2:floatsize)                  (**r float -> float *)
  | cast_case_i2f (si1:signedness) (sz2:floatsize) (**r int -> float *)
  | cast_case_f2i (sz2:intsize) (si2:signedness)   (**r float -> int *)
  | cast_case_l2l                       (**r long -> long *)
  | cast_case_i2l (si1: signedness)     (**r int -> long *)
  | cast_case_l2i (sz2: intsize) (si2: signedness) (**r long -> int *)
  | cast_case_l2f (si1: signedness) (sz2: floatsize) (**r long -> float *)
  | cast_case_f2l (si2: signedness)     (**r float -> long *)
  | cast_case_f2bool                    (**r float -> bool *)
  | cast_case_l2bool                    (**r long -> bool *)
  | cast_case_p2bool                    (**r pointer -> bool *)
  | cast_case_struct (id1: ident) (fld1: fieldlist) (id2: ident) (fld2: fieldlist) (**r struct -> struct *)
  | cast_case_union (id1: ident) (fld1: fieldlist) (id2: ident) (fld2: fieldlist) (**r union -> union *)
  | cast_case_void                                 (**r any -> void *)
  | cast_case_default.

Definition classify_cast (tfrom tto: type) : classify_cast_cases :=
  match tto, tfrom with
  | Tint I32 si2 _, (Tint _ _ _ | Tpointer _ _ | Tcomp_ptr _ _ | Tarray _ _ _ | Tfunction _ _) => cast_case_neutral
  | Tint IBool _ _, Tfloat _ _ => cast_case_f2bool
  | Tint IBool _ _, (Tpointer _ _ | Tcomp_ptr _ _ | Tarray _ _ _ | Tfunction _ _) => cast_case_p2bool
  | Tint sz2 si2 _, Tint sz1 si1 _ => cast_case_i2i sz2 si2
  | Tint sz2 si2 _, Tfloat sz1 _ => cast_case_f2i sz2 si2
  | Tfloat sz2 _, Tfloat sz1 _ => cast_case_f2f sz2
  | Tfloat sz2 _, Tint sz1 si1 _ => cast_case_i2f si1 sz2
  | (Tpointer _ _ | Tcomp_ptr _ _), (Tint _ _ _ | Tpointer _ _ | Tcomp_ptr _ _ | Tarray _ _ _ | Tfunction _ _) => cast_case_neutral
  | Tlong _ _, Tlong _ _ => cast_case_l2l
  | Tlong _ _, Tint sz1 si1 _ => cast_case_i2l si1
  | Tint IBool _ _, Tlong _ _ => cast_case_l2bool
  | Tint sz2 si2 _, Tlong _ _ => cast_case_l2i sz2 si2
  | Tlong si2 _, Tfloat sz1 _ => cast_case_f2l si2
  | Tfloat sz2 _, Tlong si1 _ => cast_case_l2f si1 sz2
  | (Tpointer _ _ | Tcomp_ptr _ _), Tlong _ _ => cast_case_l2i I32 Unsigned
  | Tlong si2 _, (Tpointer _ _ | Tcomp_ptr _ _ | Tarray _ _ _ | Tfunction _ _) => cast_case_i2l si2
  | Tstruct id2 fld2 _, Tstruct id1 fld1 _ => cast_case_struct id1 fld1 id2 fld2
  | Tunion id2 fld2 _, Tunion id1 fld1 _ => cast_case_union id1 fld1 id2 fld2
  | Tvoid, _ => cast_case_void
  | _, _ => cast_case_default
  end.

(** Semantics of casts.  [sem_cast v1 t1 t2 = Some v2] if value [v1],
  viewed with static type [t1], can be cast to type [t2],
  resulting in value [v2].  *)

Definition cast_int_int (sz: intsize) (sg: signedness) (i: int) : int :=
  match sz, sg with
  | I8, Signed => Int.sign_ext 8 i
  | I8, Unsigned => Int.zero_ext 8 i
  | I16, Signed => Int.sign_ext 16 i
  | I16, Unsigned => Int.zero_ext 16 i 
  | I32, _ => i
  | IBool, _ => if Int.eq i Int.zero then Int.zero else Int.one
  end.

Definition cast_int_float (si : signedness) (i: int) : float :=
  match si with
  | Signed => Float.floatofint i
  | Unsigned => Float.floatofintu i
  end.

Definition cast_float_int (si : signedness) (f: float) : option int :=
  match si with
  | Signed => Float.intoffloat f
  | Unsigned => Float.intuoffloat f
  end.

Definition cast_float_float (sz: floatsize) (f: float) : float :=
  match sz with
  | F32 => Float.singleoffloat f
  | F64 => f
  end.

Definition cast_int_long (si: signedness) (i: int) : int64 :=
  match si with
  | Signed => Int64.repr (Int.signed i)
  | Unsigned => Int64.repr (Int.unsigned i)
  end.

Definition cast_long_float (si : signedness) (i: int64) : float :=
  match si with
  | Signed => Float.floatoflong i
  | Unsigned => Float.floatoflongu i
  end.

Definition cast_float_long (si : signedness) (f: float) : option int64 :=
  match si with
  | Signed => Float.longoffloat f
  | Unsigned => Float.longuoffloat f
  end.

Definition sem_cast (v: val) (t1 t2: type) : option val :=
  match classify_cast t1 t2 with
  | cast_case_neutral =>
      match v with
      | Vint _ | Vptr _ _ => Some v
      | _ => None
      end
  | cast_case_i2i sz2 si2 =>
      match v with
      | Vint i => Some (Vint (cast_int_int sz2 si2 i))
      | _ => None
      end
  | cast_case_f2f sz2 =>
      match v with
      | Vfloat f => Some (Vfloat (cast_float_float sz2 f))
      | _ => None
      end
  | cast_case_i2f si1 sz2 =>
      match v with
      | Vint i => Some (Vfloat (cast_float_float sz2 (cast_int_float si1 i)))
      | _ => None
      end
  | cast_case_f2i sz2 si2 =>
      match v with
      | Vfloat f =>
          match cast_float_int si2 f with
          | Some i => Some (Vint (cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end
  | cast_case_f2bool =>
      match v with
      | Vfloat f =>
          Some(Vint(if Float.cmp Ceq f Float.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_p2bool =>
      match v with
      | Vint i => Some (Vint (cast_int_int IBool Signed i))
      | Vptr _ _ => Some (Vint Int.one)
      | _ => None
      end
  | cast_case_l2l =>
      match v with
      | Vlong n => Some (Vlong n)
      | _ => None
      end
  | cast_case_i2l si =>
      match v with
      | Vint n => Some(Vlong (cast_int_long si n))
      | _ => None
      end
  | cast_case_l2i sz si =>
      match v with
      | Vlong n => Some(Vint (cast_int_int sz si (Int.repr (Int64.unsigned n))))
      | _ => None
      end
  | cast_case_l2bool =>
      match v with
      | Vlong n =>
          Some(Vint(if Int64.eq n Int64.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_l2f si1 sz2 =>
      match v with
      | Vlong i => Some (Vfloat (cast_float_float sz2 (cast_long_float si1 i)))
      | _ => None
      end
  | cast_case_f2l si2 =>
      match v with
      | Vfloat f =>
          match cast_float_long si2 f with
          | Some i => Some (Vlong i)
          | None => None
          end
      | _ => None
      end
  | cast_case_struct id1 fld1 id2 fld2 =>
      match v with
      | Vptr b ofs =>
          if ident_eq id1 id2 && fieldlist_eq fld1 fld2 then Some v else None
      | _ => None
      end
  | cast_case_union id1 fld1 id2 fld2 =>
      match v with
      | Vptr b ofs =>
          if ident_eq id1 id2 && fieldlist_eq fld1 fld2 then Some v else None
      | _ => None
      end
  | cast_case_void =>
      Some v
  | cast_case_default =>
      None
  end.

(** The following describes types that can be interpreted as a boolean:
  integers, floats, pointers.  It is used for the semantics of 
  the [!] and [?] operators, as well as the [if], [while], [for] statements. *)

Inductive classify_bool_cases : Type :=
  | bool_case_i                           (**r integer *)
  | bool_case_f                           (**r float *)
  | bool_case_p                           (**r pointer *)
  | bool_case_l                           (**r long *)
  | bool_default.

Definition classify_bool (ty: type) : classify_bool_cases :=
  match typeconv ty with
  | Tint _ _ _ => bool_case_i
  | Tpointer _ _ | Tcomp_ptr _ _ => bool_case_p
  | Tfloat _ _ => bool_case_f
  | Tlong _ _ => bool_case_l
  | _ => bool_default
  end.

(** Interpretation of values as truth values.
  Non-zero integers, non-zero floats and non-null pointers are
  considered as true.  The integer zero (which also represents
  the null pointer) and the float 0.0 are false. *)

Definition bool_val (v: val) (t: type) : option bool :=
  match classify_bool t with
  | bool_case_i =>
      match v with
      | Vint n => Some (negb (Int.eq n Int.zero))
      | _ => None
      end
  | bool_case_f =>
      match v with
      | Vfloat f => Some (negb (Float.cmp Ceq f Float.zero))
      | _ => None
      end
  | bool_case_p =>
      match v with
      | Vint n => Some (negb (Int.eq n Int.zero))
      | Vptr b ofs => Some true
      | _ => None
      end
  | bool_case_l =>
      match v with
      | Vlong n => Some (negb (Int64.eq n Int64.zero))
      | _ => None
      end
  | bool_default => None
  end.

(** Common-sense relation between Boolean value and casting to [_Bool] type. *)

Lemma cast_bool_bool_val:
  forall v t,
  sem_cast v t (Tint IBool Signed noattr) =
  match bool_val v t with None => None | Some b => Some(Val.of_bool b) end.
Proof.
  intros.
  assert (A: classify_bool t =
    match t with
    | Tint _ _ _ => bool_case_i
    | Tpointer _ _ | Tcomp_ptr _ _ | Tarray _ _ _ | Tfunction _ _ => bool_case_p
    | Tfloat _ _ => bool_case_f
    | Tlong _ _ => bool_case_l
    | _ => bool_default
    end).
  {
    unfold classify_bool; destruct t; simpl; auto. destruct i; auto.
  }
  unfold bool_val. rewrite A. unfold sem_cast. destruct t; simpl; auto; destruct v; auto.
  destruct (Int.eq i0 Int.zero); auto.
  destruct (Int64.eq i Int64.zero); auto.
  destruct (Float.cmp Ceq f0 Float.zero); auto.
  destruct (Int.eq i Int.zero); auto. 
  destruct (Int.eq i Int.zero); auto. 
  destruct (Int.eq i Int.zero); auto. 
  destruct (Int.eq i0 Int.zero); auto. 
Qed.

(** ** Unary operators *)

(** *** Boolean negation *)

Definition sem_notbool (v: val) (ty: type) : option val :=
  match classify_bool ty with
  | bool_case_i =>
      match v with
      | Vint n => Some (Val.of_bool (Int.eq n Int.zero))
      | _ => None
      end
  | bool_case_f =>
      match v with
      | Vfloat f => Some (Val.of_bool (Float.cmp Ceq f Float.zero))
      | _ => None
      end
  | bool_case_p =>
      match v with
      | Vint n => Some (Val.of_bool (Int.eq n Int.zero))
      | Vptr _ _ => Some Vfalse
      | _ => None
      end
  | bool_case_l =>
      match v with
      | Vlong n => Some (Val.of_bool (Int64.eq n Int64.zero))
      | _ => None
      end
  | bool_default => None
  end.

(** Common-sense relation between Boolean value and Boolean negation. *)

Lemma notbool_bool_val:
  forall v t,
  sem_notbool v t =
  match bool_val v t with None => None | Some b => Some(Val.of_bool (negb b)) end.
Proof.
  intros. unfold sem_notbool, bool_val. 
  destruct (classify_bool t); auto; destruct v; auto; rewrite negb_involutive; auto.
Qed.

(** *** Opposite *)

Inductive classify_neg_cases : Type :=
  | neg_case_i(s: signedness)              (**r int *)
  | neg_case_f                             (**r float *)
  | neg_case_l(s: signedness)              (**r long *)
  | neg_default.

Definition classify_neg (ty: type) : classify_neg_cases :=
  match ty with
  | Tint I32 Unsigned _ => neg_case_i Unsigned
  | Tint _ _ _ => neg_case_i Signed
  | Tfloat _ _ => neg_case_f
  | Tlong si _ => neg_case_l si
  | _ => neg_default
  end.

Definition sem_neg (v: val) (ty: type) : option val :=
  match classify_neg ty with
  | neg_case_i sg =>
      match v with
      | Vint n => Some (Vint (Int.neg n))
      | _ => None
      end
  | neg_case_f =>
      match v with
      | Vfloat f => Some (Vfloat (Float.neg f))
      | _ => None
      end
  | neg_case_l sg =>
      match v with
      | Vlong n => Some (Vlong (Int64.neg n))
      | _ => None
      end
  | neg_default => None
  end.

(** *** Bitwise complement *)

Inductive classify_notint_cases : Type :=
  | notint_case_i(s: signedness)              (**r int *)
  | notint_case_l(s: signedness)              (**r long *)
  | notint_default.

Definition classify_notint (ty: type) : classify_notint_cases :=
  match ty with
  | Tint I32 Unsigned _ => notint_case_i Unsigned
  | Tint _ _ _ => notint_case_i Signed
  | Tlong si _ => notint_case_l si
  | _ => notint_default
  end.

Definition sem_notint (v: val) (ty: type): option val :=
  match classify_notint ty with
  | notint_case_i sg =>
      match v with
      | Vint n => Some (Vint (Int.not n))
      | _ => None
      end
  | notint_case_l sg =>
      match v with
      | Vlong n => Some (Vlong (Int64.not n))
      | _ => None
      end
  | notint_default => None
  end.

(** ** Binary operators *)

(** For binary operations, the "usual binary conversions" consist in
- determining the type at which the operation is to be performed
  (a form of least upper bound of the types of the two arguments);
- casting the two arguments to this common type;
- performing the operation at that type.
*)

Inductive binarith_cases: Type :=
  | bin_case_i (s: signedness)         (**r at int type *)
  | bin_case_l (s: signedness)         (**r at long int type *)
  | bin_case_f                         (**r at float type *)
  | bin_default.                       (**r error *)

Definition classify_binarith (ty1: type) (ty2: type) : binarith_cases :=
  match ty1, ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => bin_case_i Unsigned
  | Tint _ _ _, Tint I32 Unsigned _ => bin_case_i Unsigned
  | Tint _ _ _, Tint _ _ _ => bin_case_i Signed
  | Tlong Signed _, Tlong Signed _ => bin_case_l Signed
  | Tlong _ _, Tlong _ _ => bin_case_l Unsigned
  | Tlong sg _, Tint _ _ _ => bin_case_l sg
  | Tint _ _ _, Tlong sg _ => bin_case_l sg
  | Tfloat _ _, (Tint _ _ _ | Tlong _ _ | Tfloat _ _) => bin_case_f
  | (Tint _ _ _ | Tlong _ _), Tfloat _ _ => bin_case_f
  | _, _ => bin_default
  end.

Definition binarith_type (c: binarith_cases) : type :=
  match c with
  | bin_case_i sg => Tint I32 sg noattr
  | bin_case_l sg => Tlong sg noattr
  | bin_case_f    => Tfloat F64 noattr
  | bin_default   => Tvoid
  end.

Definition sem_binarith
    (sem_int: signedness -> int -> int -> option val)
    (sem_long: signedness -> int64 -> int64 -> option val)
    (sem_float: float -> float -> option val)
    (v1: val) (t1: type) (v2: val) (t2: type) : option val :=
  let c := classify_binarith t1 t2 in
  let t := binarith_type c in
  match sem_cast v1 t1 t with
  | None => None
  | Some v1' =>
  match sem_cast v2 t2 t with
  | None => None
  | Some v2' =>
  match classify_binarith t1 t2 with
  | bin_case_i sg =>
      match v1', v2' with
      | Vint n1, Vint n2 => sem_int sg n1 n2
      | _,  _ => None
      end
  | bin_case_f =>
      match v1', v2' with
      | Vfloat n1, Vfloat n2 => sem_float n1 n2
      | _,  _ => None
      end
  | bin_case_l sg =>
      match v1', v2' with
      | Vlong n1, Vlong n2 => sem_long sg n1 n2
      | _,  _ => None
      end
  | bin_default => None
  end end end.

(** *** Addition *)

Inductive classify_add_cases : Type :=
  | add_case_pi(ty: type)(a: attr)     (**r pointer, int *)
  | add_case_ip(ty: type)(a: attr)     (**r int, pointer *)
  | add_case_pl(ty: type)(a: attr)     (**r pointer, long *)
  | add_case_lp(ty: type)(a: attr)     (**r long, pointer *)
  | add_default.                       (**r numerical type, numerical type *)

Definition classify_add (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tpointer ty a, Tint _ _ _ => add_case_pi ty a
  | Tint _ _ _, Tpointer ty a => add_case_ip ty a
  | Tpointer ty a, Tlong _ _ => add_case_pl ty a
  | Tlong _ _, Tpointer ty a => add_case_lp ty a
  | _, _ => add_default
  end.

Definition sem_add (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_add t1 t2 with 
  | add_case_pi ty _ =>                 (**r pointer plus integer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vint n2 => 
        Some (Vptr b1 (Int.add ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end   
  | add_case_ip ty _ =>                 (**r integer plus pointer *)
      match v1,v2 with
      | Vint n1, Vptr b2 ofs2 => 
        Some (Vptr b2 (Int.add ofs2 (Int.mul (Int.repr (sizeof ty)) n1)))
      | _,  _ => None
      end   
  | add_case_pl ty _ =>                 (**r pointer plus long *)
      match v1,v2 with
      | Vptr b1 ofs1, Vlong n2 => 
        let n2 := Int.repr (Int64.unsigned n2) in
        Some (Vptr b1 (Int.add ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end   
  | add_case_lp ty _ =>                 (**r long plus pointer *)
      match v1,v2 with
      | Vlong n1, Vptr b2 ofs2 => 
        let n1 := Int.repr (Int64.unsigned n1) in
        Some (Vptr b2 (Int.add ofs2 (Int.mul (Int.repr (sizeof ty)) n1)))
      | _,  _ => None
      end   
  | add_default =>
      sem_binarith
        (fun sg n1 n2 => Some(Vint(Int.add n1 n2)))
        (fun sg n1 n2 => Some(Vlong(Int64.add n1 n2)))
        (fun n1 n2 => Some(Vfloat(Float.add n1 n2)))
        v1 t1 v2 t2
  end.

(** *** Subtraction *)

Inductive classify_sub_cases : Type :=
  | sub_case_pi(ty: type)(a: attr)      (**r pointer, int *)
  | sub_case_pp(ty: type)               (**r pointer, pointer *)
  | sub_case_pl(ty: type)(a: attr)      (**r pointer, long *)
  | sub_default.                        (**r numerical type, numerical type *)

Definition classify_sub (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tpointer ty a, Tint _ _ _ => sub_case_pi ty a
  | Tpointer ty _ , Tpointer _ _ => sub_case_pp ty
  | Tpointer ty a, Tlong _ _ => sub_case_pl ty a
  | _, _ => sub_default
  end.

Definition sem_sub (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_sub t1 t2 with
  | sub_case_pi ty attr =>            (**r pointer minus integer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vint n2 => 
          Some (Vptr b1 (Int.sub ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end
  | sub_case_pl ty attr =>            (**r pointer minus long *)
      match v1,v2 with
      | Vptr b1 ofs1, Vlong n2 => 
          let n2 := Int.repr (Int64.unsigned n2) in
          Some (Vptr b1 (Int.sub ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end
  | sub_case_pp ty =>          (**r pointer minus pointer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vptr b2 ofs2 =>
          if eq_block b1 b2 then
            if Int.eq (Int.repr (sizeof ty)) Int.zero then None
            else Some (Vint (Int.divu (Int.sub ofs1 ofs2) (Int.repr (sizeof ty))))
          else None
      | _, _ => None
      end
  | sub_default =>
      sem_binarith
        (fun sg n1 n2 => Some(Vint(Int.sub n1 n2)))
        (fun sg n1 n2 => Some(Vlong(Int64.sub n1 n2)))
        (fun n1 n2 => Some(Vfloat(Float.sub n1 n2)))
        v1 t1 v2 t2
  end.
 
(** *** Multiplication, division, modulus *)

Definition sem_mul (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.mul n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.mul n1 n2)))
    (fun n1 n2 => Some(Vfloat(Float.mul n1 n2)))
    v1 t1 v2 t2.

Definition sem_div (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  sem_binarith
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some(Vint(Int.divs n1 n2))
      | Unsigned =>
          if Int.eq n2 Int.zero
          then None else Some(Vint(Int.divu n1 n2))
      end)
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int64.eq n2 Int64.zero
          || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
          then None else Some(Vlong(Int64.divs n1 n2))
      | Unsigned =>
          if Int64.eq n2 Int64.zero
          then None else Some(Vlong(Int64.divu n1 n2))
      end)
    (fun n1 n2 => Some(Vfloat(Float.div n1 n2)))
    v1 t1 v2 t2.

Definition sem_mod (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  sem_binarith
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some(Vint(Int.mods n1 n2))
      | Unsigned =>
          if Int.eq n2 Int.zero
          then None else Some(Vint(Int.modu n1 n2))
      end)
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int64.eq n2 Int64.zero
          || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
          then None else Some(Vlong(Int64.mods n1 n2))
      | Unsigned =>
          if Int64.eq n2 Int64.zero
          then None else Some(Vlong(Int64.modu n1 n2))
      end)
    (fun n1 n2 => None)
    v1 t1 v2 t2.

Definition sem_and (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.and n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.and n1 n2)))
    (fun n1 n2 => None)
    v1 t1 v2 t2.

Definition sem_or (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.or n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.or n1 n2)))
    (fun n1 n2 => None)
    v1 t1 v2 t2.

Definition sem_xor (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.xor n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.xor n1 n2)))
    (fun n1 n2 => None)
    v1 t1 v2 t2.

(** *** Shifts *)

(** Shifts do not perform the usual binary conversions.  Instead,
  each argument is converted independently, and the signedness
  of the result is always that of the first argument. *)

Inductive classify_shift_cases : Type:=
  | shift_case_ii(s: signedness)         (**r int , int *)
  | shift_case_ll(s: signedness)         (**r long, long *)
  | shift_case_il(s: signedness)         (**r int, long *)
  | shift_case_li(s: signedness)         (**r long, int *)
  | shift_default.

Definition classify_shift (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => shift_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => shift_case_ii Signed
  | Tint I32 Unsigned _, Tlong _ _ => shift_case_il Unsigned
  | Tint _ _ _, Tlong _ _ => shift_case_il Signed
  | Tlong s _, Tint _ _ _ => shift_case_li s
  | Tlong s _, Tlong _ _ => shift_case_ll s
  | _,_  => shift_default
  end.

Definition sem_shift
    (sem_int: signedness -> int -> int -> int)
    (sem_long: signedness -> int64 -> int64 -> int64)
    (v1: val) (t1: type) (v2: val) (t2: type) : option val :=
  match classify_shift t1 t2 with
  | shift_case_ii sg =>
      match v1, v2 with
      | Vint n1, Vint n2 => 
          if Int.ltu n2 Int.iwordsize
          then Some(Vint(sem_int sg n1 n2)) else None
      | _, _ => None
      end
  | shift_case_il sg =>
      match v1, v2 with
      | Vint n1, Vlong n2 => 
          if Int64.ltu n2 (Int64.repr 32)
          then Some(Vint(sem_int sg n1 (Int64.loword n2))) else None
      | _, _ => None
      end
  | shift_case_li sg =>
      match v1, v2 with
      | Vlong n1, Vint n2 => 
          if Int.ltu n2 Int64.iwordsize'
          then Some(Vlong(sem_long sg n1 (Int64.repr (Int.unsigned n2)))) else None
      | _, _ => None
      end
  | shift_case_ll sg =>
      match v1, v2 with
      | Vlong n1, Vlong n2 => 
          if Int64.ltu n2 Int64.iwordsize
          then Some(Vlong(sem_long sg n1 n2)) else None
      | _, _ => None
      end
  | shift_default => None
  end.

Definition sem_shl (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  sem_shift
    (fun sg n1 n2 => Int.shl n1 n2)
    (fun sg n1 n2 => Int64.shl n1 n2)
    v1 t1 v2 t2.

Definition sem_shr (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  sem_shift
    (fun sg n1 n2 => match sg with Signed => Int.shr n1 n2 | Unsigned => Int.shru n1 n2 end)
    (fun sg n1 n2 => match sg with Signed => Int64.shr n1 n2 | Unsigned => Int64.shru n1 n2 end)
    v1 t1 v2 t2.

(** *** Comparisons *)

Inductive classify_cmp_cases : Type :=
  | cmp_case_pp                       (**r pointer, pointer *)
  | cmp_case_pl                       (**r pointer, long *)
  | cmp_case_lp                       (**r long, pointer *)
  | cmp_default.                      (**r numerical, numerical *)

Definition classify_cmp (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with 
  | Tpointer _ _ , Tpointer _ _ => cmp_case_pp
  | Tpointer _ _ , Tint _ _ _ => cmp_case_pp
  | Tint _ _ _, Tpointer _ _ => cmp_case_pp
  | Tpointer _ _ , Tlong _ _ => cmp_case_pl
  | Tlong _ _ , Tpointer _ _ => cmp_case_lp
  | _, _ => cmp_default
  end.

Definition sem_cmp (c:comparison)
                  (v1: val) (t1: type) (v2: val) (t2: type)
                  (m: mem): option val :=
  match classify_cmp t1 t2 with
  | cmp_case_pp =>
      option_map Val.of_bool (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2)
  | cmp_case_pl =>
      match v2 with
      | Vlong n2 => 
          let n2 := Int.repr (Int64.unsigned n2) in
          option_map Val.of_bool (Val.cmpu_bool (Mem.valid_pointer m) c v1 (Vint n2))
      | _ => None
      end
  | cmp_case_lp =>
      match v1 with
      | Vlong n1 => 
          let n1 := Int.repr (Int64.unsigned n1) in
          option_map Val.of_bool (Val.cmpu_bool (Mem.valid_pointer m) c (Vint n1) v2)
      | _ => None
      end
  | cmp_default =>
      sem_binarith
        (fun sg n1 n2 =>
            Some(Val.of_bool(match sg with Signed => Int.cmp c n1 n2 | Unsigned => Int.cmpu c n1 n2 end)))
        (fun sg n1 n2 =>
            Some(Val.of_bool(match sg with Signed => Int64.cmp c n1 n2 | Unsigned => Int64.cmpu c n1 n2 end)))
        (fun n1 n2 =>
            Some(Val.of_bool(Float.cmp c n1 n2)))
        v1 t1 v2 t2
  end.

(** ** Function applications *)

Inductive classify_fun_cases : Type:=
  | fun_case_f (targs: typelist) (tres: type) (**r (pointer to) function *)
  | fun_default.

Definition classify_fun (ty: type) :=
  match ty with 
  | Tfunction args res => fun_case_f args res
  | Tpointer (Tfunction args res) _ => fun_case_f args res
  | _ => fun_default
  end.

(** * Combined semantics of unary and binary operators *)

Definition sem_unary_operation
            (op: unary_operation) (v: val) (ty: type): option val :=
  match op with
  | Onotbool => sem_notbool v ty
  | Onotint => sem_notint v ty
  | Oneg => sem_neg v ty
  end.

Definition sem_binary_operation
    (op: binary_operation)
    (v1: val) (t1: type) (v2: val) (t2:type)
    (m: mem): option val :=
  match op with
  | Oadd => sem_add v1 t1 v2 t2
  | Osub => sem_sub v1 t1 v2 t2 
  | Omul => sem_mul v1 t1 v2 t2
  | Omod => sem_mod v1 t1 v2 t2
  | Odiv => sem_div v1 t1 v2 t2 
  | Oand => sem_and v1 t1 v2 t2
  | Oor  => sem_or v1 t1 v2 t2
  | Oxor  => sem_xor v1 t1 v2 t2
  | Oshl => sem_shl v1 t1 v2 t2
  | Oshr  => sem_shr v1 t1 v2 t2   
  | Oeq => sem_cmp Ceq v1 t1 v2 t2 m
  | One => sem_cmp Cne v1 t1 v2 t2 m
  | Olt => sem_cmp Clt v1 t1 v2 t2 m
  | Ogt => sem_cmp Cgt v1 t1 v2 t2 m
  | Ole => sem_cmp Cle v1 t1 v2 t2 m
  | Oge => sem_cmp Cge v1 t1 v2 t2 m
  end.

Definition sem_incrdecr (id: incr_or_decr) (v: val) (ty: type) :=
  match id with
  | Incr => sem_add v ty (Vint Int.one) type_int32s
  | Decr => sem_sub v ty (Vint Int.one) type_int32s
  end.

(** * Compatibility with extensions and injections *)

Section GENERIC_INJECTION.

Variable f: meminj.
Variables m m': mem.

Hypothesis valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.valid_pointer m b1 (Int.unsigned ofs) = true ->
  Mem.valid_pointer m' b2 (Int.unsigned (Int.add ofs (Int.repr delta))) = true.

Hypothesis weak_valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Int.unsigned ofs) = true ->
  Mem.weak_valid_pointer m' b2 (Int.unsigned (Int.add ofs (Int.repr delta))) = true.

Hypothesis weak_valid_pointer_no_overflow:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m b1 (Int.unsigned ofs) = true ->
  0 <= Int.unsigned ofs + Int.unsigned (Int.repr delta) <= Int.max_unsigned.

Hypothesis valid_different_pointers_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m b1 (Int.unsigned ofs1) = true ->
  Mem.valid_pointer m b2 (Int.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Int.unsigned (Int.add ofs1 (Int.repr delta1)) <> Int.unsigned (Int.add ofs2 (Int.repr delta2)).

Remark val_inject_vtrue: forall f, val_inject f Vtrue Vtrue.
Proof. unfold Vtrue; auto. Qed.

Remark val_inject_vfalse: forall f, val_inject f Vfalse Vfalse.
Proof. unfold Vfalse; auto. Qed.

Remark val_inject_of_bool: forall f b, val_inject f (Val.of_bool b) (Val.of_bool b).
Proof. intros. unfold Val.of_bool. destruct b; [apply val_inject_vtrue|apply val_inject_vfalse]. 
Qed.

Hint Resolve val_inject_vtrue val_inject_vfalse val_inject_of_bool.

Ltac TrivialInject :=
  match goal with
  | |- exists v', Some ?v = Some v' /\ _ => exists v; split; auto
  | _ => idtac
  end.

Lemma sem_cast_inject:
  forall v1 ty1 ty v tv1,
  sem_cast v1 ty1 ty = Some v ->
  val_inject f v1 tv1 ->
  exists tv, sem_cast tv1 ty1 ty = Some tv /\ val_inject f v tv.
Proof.
  unfold sem_cast; intros; destruct (classify_cast ty1 ty);
  inv H0; inv H; TrivialInject.
- econstructor; eauto. 
- destruct (cast_float_int si2 f0); inv H1; TrivialInject.
- destruct (cast_float_long si2 f0); inv H1; TrivialInject.
- destruct (ident_eq id1 id2 && fieldlist_eq fld1 fld2); inv H2; TrivialInject. econstructor; eauto.
- destruct (ident_eq id1 id2 && fieldlist_eq fld1 fld2); inv H2; TrivialInject. econstructor; eauto.
- econstructor; eauto.
Qed.

Lemma sem_unary_operation_inject:
  forall op v1 ty v tv1,
  sem_unary_operation op v1 ty = Some v ->
  val_inject f v1 tv1 ->
  exists tv, sem_unary_operation op tv1 ty = Some tv /\ val_inject f v tv.
Proof.
  unfold sem_unary_operation; intros. destruct op.
  (* notbool *)
  unfold sem_notbool in *; destruct (classify_bool ty); inv H0; inv H; TrivialInject.
  (* notint *)
  unfold sem_notint in *; destruct (classify_notint ty); inv H0; inv H; TrivialInject.
  (* neg *)
  unfold sem_neg in *; destruct (classify_neg ty); inv H0; inv H; TrivialInject.
Qed.

Definition optval_self_injects (ov: option val) : Prop :=
  match ov with
  | Some (Vptr b ofs) => False
  | _ => True
  end.

Remark sem_binarith_inject:
  forall sem_int sem_long sem_float v1 t1 v2 t2 v v1' v2',
  sem_binarith sem_int sem_long sem_float v1 t1 v2 t2 = Some v ->
  val_inject f v1 v1' -> val_inject f v2 v2' ->
  (forall sg n1 n2, optval_self_injects (sem_int sg n1 n2)) ->
  (forall sg n1 n2, optval_self_injects (sem_long sg n1 n2)) ->
  (forall n1 n2, optval_self_injects (sem_float n1 n2)) ->
  exists v', sem_binarith sem_int sem_long sem_float v1' t1 v2' t2 = Some v' /\ val_inject f v v'.
Proof.
  intros. 
  assert (SELF: forall ov v, ov = Some v -> optval_self_injects ov -> val_inject f v v).
  {
    intros. subst ov; simpl in H6. destruct v0; contradiction || constructor.
  }
  unfold sem_binarith in *.
  set (c := classify_binarith t1 t2) in *.
  set (t := binarith_type c) in *.
  destruct (sem_cast v1 t1 t) as [w1|] eqn:C1; try discriminate.
  destruct (sem_cast v2 t2 t) as [w2|] eqn:C2; try discriminate.
  exploit (sem_cast_inject v1); eauto. intros (w1' & C1' & INJ1).
  exploit (sem_cast_inject v2); eauto. intros (w2' & C2' & INJ2).
  rewrite C1'; rewrite C2'.
  destruct c; inv INJ1; inv INJ2; discriminate || eauto.
Qed.

Remark sem_shift_inject:
  forall sem_int sem_long v1 t1 v2 t2 v v1' v2',
  sem_shift sem_int sem_long v1 t1 v2 t2 = Some v ->
  val_inject f v1 v1' -> val_inject f v2 v2' ->
  exists v', sem_shift sem_int sem_long v1' t1 v2' t2 = Some v' /\ val_inject f v v'.
Proof.
  intros. exists v.
  unfold sem_shift in *; destruct (classify_shift t1 t2); inv H0; inv H1; try discriminate.
  destruct (Int.ltu i0 Int.iwordsize); inv H; auto.
  destruct (Int64.ltu i0 Int64.iwordsize); inv H; auto.
  destruct (Int64.ltu i0 (Int64.repr 32)); inv H; auto.
  destruct (Int.ltu i0 Int64.iwordsize'); inv H; auto.
Qed.

Remark sem_cmp_inj:
  forall cmp v1 tv1 ty1 v2 tv2 ty2 v,
  sem_cmp cmp v1 ty1 v2 ty2 m = Some v ->
  val_inject f v1 tv1 ->
  val_inject f v2 tv2 ->
  exists tv, sem_cmp cmp tv1 ty1 tv2 ty2 m' = Some tv /\ val_inject f v tv.
Proof.
  intros.
  unfold sem_cmp in *; destruct (classify_cmp ty1 ty2).
- (* pointer - pointer *)
  destruct (Val.cmpu_bool (Mem.valid_pointer m) cmp v1 v2) as [b|] eqn:E; simpl in H; inv H.
  replace (Val.cmpu_bool (Mem.valid_pointer m') cmp tv1 tv2) with (Some b).
  simpl. TrivialInject. 
  symmetry. eapply val_cmpu_bool_inject; eauto. 
- (* pointer - long *)
  destruct v2; try discriminate. inv H1. 
  set (v2 := Vint (Int.repr (Int64.unsigned i))) in *.
  destruct (Val.cmpu_bool (Mem.valid_pointer m) cmp v1 v2) as [b|] eqn:E; simpl in H; inv H.
  replace (Val.cmpu_bool (Mem.valid_pointer m') cmp tv1 v2) with (Some b).
  simpl. TrivialInject. 
  symmetry. eapply val_cmpu_bool_inject with (v2 := v2); eauto. constructor. 
- (* long - pointer *)
  destruct v1; try discriminate. inv H0. 
  set (v1 := Vint (Int.repr (Int64.unsigned i))) in *.
  destruct (Val.cmpu_bool (Mem.valid_pointer m) cmp v1 v2) as [b|] eqn:E; simpl in H; inv H.
  replace (Val.cmpu_bool (Mem.valid_pointer m') cmp v1 tv2) with (Some b).
  simpl. TrivialInject. 
  symmetry. eapply val_cmpu_bool_inject with (v1 := v1); eauto. constructor. 
- (* numerical - numerical *)
  assert (SELF: forall b, optval_self_injects (Some (Val.of_bool b))).
  {
    destruct b; exact I.
  }
  eapply sem_binarith_inject; eauto.
Qed.

Lemma sem_binary_operation_inj:
  forall op v1 ty1 v2 ty2 v tv1 tv2,
  sem_binary_operation op v1 ty1 v2 ty2 m = Some v ->
  val_inject f v1 tv1 -> val_inject f v2 tv2 ->
  exists tv, sem_binary_operation op tv1 ty1 tv2 ty2 m' = Some tv /\ val_inject f v tv.
Proof.
  unfold sem_binary_operation; intros; destruct op.
- (* add *)
  unfold sem_add in *; destruct (classify_add ty1 ty2).
  + inv H0; inv H1; inv H. TrivialInject. 
    econstructor. eauto. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  + inv H0; inv H1; inv H. TrivialInject. 
    econstructor. eauto. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  + inv H0; inv H1; inv H. TrivialInject. 
    econstructor. eauto. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  + inv H0; inv H1; inv H. TrivialInject. 
    econstructor. eauto. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  + eapply sem_binarith_inject; eauto; intros; exact I.
- (* sub *)
  unfold sem_sub in *; destruct (classify_sub ty1 ty2).
  + inv H0; inv H1; inv H. TrivialInject.
    econstructor. eauto. rewrite Int.sub_add_l. auto.
  + inv H0; inv H1; inv H. TrivialInject.
    destruct (eq_block b1 b0); try discriminate. subst b1. 
    rewrite H0 in H2; inv H2. rewrite dec_eq_true. 
    destruct (Int.eq (Int.repr (sizeof ty)) Int.zero); inv H3.
    rewrite Int.sub_shifted. TrivialInject.
  + inv H0; inv H1; inv H. TrivialInject.
    econstructor. eauto. rewrite Int.sub_add_l. auto.
  + eapply sem_binarith_inject; eauto; intros; exact I.
- (* mul *)
  eapply sem_binarith_inject; eauto; intros; exact I.
- (* div *)
  eapply sem_binarith_inject; eauto; intros.
  destruct sg.
  destruct (Int.eq n2 Int.zero
            || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); exact I.
  destruct (Int.eq n2 Int.zero); exact I.
  destruct sg.
  destruct (Int64.eq n2 Int64.zero
            || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); exact I.
  destruct (Int64.eq n2 Int64.zero); exact I.
  exact I.
- (* mod *)
  eapply sem_binarith_inject; eauto; intros.
  destruct sg.
  destruct (Int.eq n2 Int.zero
            || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone); exact I.
  destruct (Int.eq n2 Int.zero); exact I.
  destruct sg.
  destruct (Int64.eq n2 Int64.zero
            || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone); exact I.
  destruct (Int64.eq n2 Int64.zero); exact I.
  exact I.
- (* and *)
  eapply sem_binarith_inject; eauto; intros; exact I.
- (* or *)
  eapply sem_binarith_inject; eauto; intros; exact I.
- (* xor *)
  eapply sem_binarith_inject; eauto; intros; exact I.
- (* shl *)
  eapply sem_shift_inject; eauto.
- (* shr *)
  eapply sem_shift_inject; eauto.
  (* comparisons *)
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
- eapply sem_cmp_inj; eauto.
Qed.

Lemma bool_val_inject:
  forall v ty b tv,
  bool_val v ty = Some b ->
  val_inject f v tv ->
  bool_val tv ty = Some b.
Proof.
  unfold bool_val; intros. 
  destruct (classify_bool ty); inv H0; congruence.
Qed.

End GENERIC_INJECTION.

Lemma sem_binary_operation_inject:
  forall f m m' op v1 ty1 v2 ty2 v tv1 tv2,
  sem_binary_operation op v1 ty1 v2 ty2 m = Some v ->
  val_inject f v1 tv1 -> val_inject f v2 tv2 ->
  Mem.inject f m m' ->
  exists tv, sem_binary_operation op tv1 ty1 tv2 ty2 m' = Some tv /\ val_inject f v tv.
Proof.
  intros. eapply sem_binary_operation_inj; eauto. 
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
Qed.



