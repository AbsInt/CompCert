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
  | cast_case_f2bool                    (**r float -> bool *)
  | cast_case_p2bool                    (**r pointer -> bool *)
  | cast_case_struct (id1: ident) (fld1: fieldlist) (id2: ident) (fld2: fieldlist) (**r struct -> struct *)
  | cast_case_union (id1: ident) (fld1: fieldlist) (id2: ident) (fld2: fieldlist) (**r union -> union *)
  | cast_case_void                                 (**r any -> void *)
  | cast_case_default.

Function classify_cast (tfrom tto: type) : classify_cast_cases :=
  match tto, tfrom with
  | Tint I32 si2 _, (Tint _ _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _) => cast_case_neutral
  | Tint IBool _ _, Tfloat _ _ => cast_case_f2bool
  | Tint IBool _ _, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _) => cast_case_p2bool
  | Tint sz2 si2 _, Tint sz1 si1 _ => cast_case_i2i sz2 si2
  | Tint sz2 si2 _, Tfloat sz1 _ => cast_case_f2i sz2 si2
  | Tfloat sz2 _, Tfloat sz1 _ => cast_case_f2f sz2
  | Tfloat sz2 _, Tint sz1 si1 _ => cast_case_i2f si1 sz2
  | Tpointer _ _, (Tint _ _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _) => cast_case_neutral
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

Function sem_cast (v: val) (t1 t2: type) : option val :=
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
  | cast_case_struct id1 fld1 id2 fld2 =>
      if ident_eq id1 id2 && fieldlist_eq fld1 fld2 then Some v else None
  | cast_case_union id1 fld1 id2 fld2 =>
      if ident_eq id1 id2 && fieldlist_eq fld1 fld2 then Some v else None
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
  | bool_default.

Definition classify_bool (ty: type) : classify_bool_cases :=
  match typeconv ty with
  | Tint _ _ _ => bool_case_i
  | Tpointer _ _ => bool_case_p
  | Tfloat _ _ => bool_case_f
  | _ => bool_default
  end.

(** Interpretation of values as truth values.
  Non-zero integers, non-zero floats and non-null pointers are
  considered as true.  The integer zero (which also represents
  the null pointer) and the float 0.0 are false. *)

Function bool_val (v: val) (t: type) : option bool :=
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
    | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ => bool_case_p
    | Tfloat _ _ => bool_case_f
    | _ => bool_default
    end).
  unfold classify_bool; destruct t; simpl; auto. destruct i; auto. destruct s; auto.

  unfold bool_val. rewrite A. unfold sem_cast. destruct t; simpl; auto; destruct v; auto.
  destruct (Int.eq i0 Int.zero); auto. 
  destruct (Float.cmp Ceq f0 Float.zero); auto.
  destruct (Int.eq i Int.zero); auto. 
  destruct (Int.eq i Int.zero); auto. 
  destruct (Int.eq i Int.zero); auto. 
Qed.

(** ** Unary operators *)

(** *** Boolean negation *)

Function sem_notbool (v: val) (ty: type) : option val :=
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
  | neg_default.

Definition classify_neg (ty: type) : classify_neg_cases :=
  match ty with
  | Tint I32 Unsigned _ => neg_case_i Unsigned
  | Tint _ _ _ => neg_case_i Signed
  | Tfloat _ _ => neg_case_f
  | _ => neg_default
  end.

Function sem_neg (v: val) (ty: type) : option val :=
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
  | neg_default => None
  end.

(** *** Bitwise complement *)

Inductive classify_notint_cases : Type :=
  | notint_case_i(s: signedness)              (**r int *)
  | notint_default.

Definition classify_notint (ty: type) : classify_notint_cases :=
  match ty with
  | Tint I32 Unsigned _ => notint_case_i Unsigned
  | Tint _ _ _ => notint_case_i Signed
  | _ => notint_default
  end.

Function sem_notint (v: val) (ty: type): option val :=
  match classify_notint ty with
  | notint_case_i sg =>
      match v with
      | Vint n => Some (Vint (Int.xor n Int.mone))
      | _ => None
      end
  | notint_default => None
  end.

(** ** Binary operators *)

(** For binary operations, the "usual binary conversions", adapted to a 32-bit
  platform, state that:
- If both arguments are of integer type, an integer operation is performed.
  For operations that behave differently at unsigned and signed types
  (e.g. division, modulus, comparisons), the unsigned operation is selected
  if at least one of the arguments is of type "unsigned int32", otherwise
  the signed operation is performed.
- If both arguments are of float type, a float operation is performed.
  We choose to perform all float arithmetic in double precision,
  even if both arguments are single-precision floats.
- If one argument has integer type and the other has float type,
  we convert the integer argument to float, then perform the float operation.
*)

(** *** Addition *)

Inductive classify_add_cases : Type :=
  | add_case_ii(s: signedness)         (**r int, int *)
  | add_case_ff                        (**r float, float *)
  | add_case_if(s: signedness)         (**r int, float *)
  | add_case_fi(s: signedness)         (**r float, int *)
  | add_case_pi(ty: type)(a: attr)     (**r pointer, int *)
  | add_case_ip(ty: type)(a: attr)     (**r int, pointer *)
  | add_default.

Definition classify_add (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => add_case_ii Unsigned
  | Tint _ _ _, Tint I32 Unsigned _ => add_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => add_case_ii Signed
  | Tfloat _ _, Tfloat _ _ => add_case_ff
  | Tint _ sg _, Tfloat _ _ => add_case_if sg
  | Tfloat _ _, Tint _ sg _ => add_case_fi sg
  | Tpointer ty a, Tint _ _ _ => add_case_pi ty a
  | Tint _ _ _, Tpointer ty a => add_case_ip ty a
  | _, _ => add_default
  end.

Function sem_add (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_add t1 t2 with 
  | add_case_ii sg =>                   (**r integer addition *)
      match v1, v2 with
      | Vint n1, Vint n2 => Some (Vint (Int.add n1 n2))
      | _,  _ => None
      end
  | add_case_ff =>                      (**r float addition *)
      match v1, v2 with
      | Vfloat n1, Vfloat n2 => Some (Vfloat (Float.add n1 n2))
      | _,  _ => None
      end
  | add_case_if sg =>                   (**r int plus float *)
      match v1, v2 with
      | Vint n1, Vfloat n2 => Some (Vfloat (Float.add (cast_int_float sg n1) n2))
      | _, _ => None
      end
  | add_case_fi sg =>                   (**r float plus int *)
      match v1, v2 with
      | Vfloat n1, Vint n2 => Some (Vfloat (Float.add n1 (cast_int_float sg n2)))
      | _, _ => None
      end
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
  | add_default => None
end.

(** *** Subtraction *)

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
  | Tint I32 Unsigned _, Tint _ _ _ => sub_case_ii Unsigned
  | Tint _ _ _, Tint I32 Unsigned _ => sub_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => sub_case_ii Signed
  | Tfloat _ _ , Tfloat _ _ => sub_case_ff
  | Tint _ sg _, Tfloat _ _ => sub_case_if sg
  | Tfloat _ _, Tint _ sg _ => sub_case_fi sg
  | Tpointer ty _, Tint _ _ _ => sub_case_pi ty
  | Tpointer ty _ , Tpointer _ _ => sub_case_pp ty
  | _ ,_ => sub_default
  end.

Function sem_sub (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_sub t1 t2 with
  | sub_case_ii sg =>            (**r integer subtraction *)
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Vint (Int.sub n1 n2))
      | _,  _ => None
      end 
  | sub_case_ff =>               (**r float subtraction *)
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Vfloat(Float.sub f1 f2))
      | _,  _ => None
      end
  | sub_case_if sg =>            (**r int minus float *)
      match v1, v2 with
      | Vint n1, Vfloat n2 => Some (Vfloat (Float.sub (cast_int_float sg n1) n2))
      | _, _ => None
      end
  | sub_case_fi sg =>            (**r float minus int *)
      match v1, v2 with
      | Vfloat n1, Vint n2 => Some (Vfloat (Float.sub n1 (cast_int_float sg n2)))
      | _, _ => None
      end
  | sub_case_pi ty =>            (**r pointer minus integer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vint n2 => 
            Some (Vptr b1 (Int.sub ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end
  | sub_case_pp ty =>          (**r pointer minus pointer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vptr b2 ofs2 =>
          if zeq b1 b2 then
            if Int.eq (Int.repr (sizeof ty)) Int.zero then None
            else Some (Vint (Int.divu (Int.sub ofs1 ofs2) (Int.repr (sizeof ty))))
          else None
      | _, _ => None
      end
  | sub_default => None
  end.
 
(** *** Multiplication *)

Inductive classify_mul_cases : Type:=
  | mul_case_ii(s: signedness) (**r int , int *)
  | mul_case_ff                (**r float , float *)
  | mul_case_if(s: signedness) (**r int, float *)
  | mul_case_fi(s: signedness) (**r float, int *)
  | mul_default.

Definition classify_mul (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => mul_case_ii Unsigned
  | Tint _ _ _, Tint I32 Unsigned _ => mul_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => mul_case_ii Signed
  | Tfloat _ _ , Tfloat _ _ => mul_case_ff
  | Tint _ sg _, Tfloat _ _ => mul_case_if sg
  | Tfloat _ _, Tint _ sg _ => mul_case_fi sg
  | _,_  => mul_default
end.

Function sem_mul (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
 match classify_mul t1 t2 with
  | mul_case_ii sg =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Vint (Int.mul n1 n2))
      | _,  _ => None
      end
  | mul_case_ff =>
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Vfloat (Float.mul f1 f2))
      | _,  _ => None
      end
  | mul_case_if sg =>
      match v1, v2 with
      | Vint n1, Vfloat n2 => Some (Vfloat (Float.mul (cast_int_float sg n1) n2))
      | _, _ => None
      end
  | mul_case_fi sg =>
      match v1, v2 with
      | Vfloat n1, Vint n2 => Some (Vfloat (Float.mul n1 (cast_int_float sg n2)))
      | _, _ => None
      end
  | mul_default =>
      None
end.

(** *** Division *)

Inductive classify_div_cases : Type:=
  | div_case_ii(s: signedness) (**r int , int *)
  | div_case_ff                (**r float , float *)
  | div_case_if(s: signedness) (**r int, float *)
  | div_case_fi(s: signedness) (**r float, int *)
  | div_default.

Definition classify_div (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => div_case_ii Unsigned
  | Tint _ _ _, Tint I32 Unsigned _ => div_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => div_case_ii Signed
  | Tfloat _ _ , Tfloat _ _ => div_case_ff
  | Tint _ sg _, Tfloat _ _ => div_case_if sg
  | Tfloat _ _, Tint _ sg _ => div_case_fi sg
  | _,_  => div_default
end.

Function sem_div (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
   match classify_div t1 t2 with
  | div_case_ii Unsigned =>
      match v1,v2 with
      | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero then None else Some (Vint (Int.divu n1 n2))
      | _,_ => None
      end
  | div_case_ii Signed =>
      match v1,v2 with
       | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some (Vint(Int.divs n1 n2))
      | _,_ => None
      end
  | div_case_ff =>
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Vfloat(Float.div f1 f2))
      | _,  _ => None
      end 
  | div_case_if sg =>
      match v1, v2 with
      | Vint n1, Vfloat n2 => Some (Vfloat (Float.div (cast_int_float sg n1) n2))
      | _, _ => None
      end
  | div_case_fi sg =>
      match v1, v2 with
      | Vfloat n1, Vint n2 => Some (Vfloat (Float.div n1 (cast_int_float sg n2)))
      | _, _ => None
      end
  | div_default =>
      None
end.

(** *** Integer-only binary operations: modulus, bitwise "and", "or", and "xor" *)

Inductive classify_binint_cases : Type:=
  | binint_case_ii(s: signedness) (**r int , int *)
  | binint_default.

Definition classify_binint (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => binint_case_ii Unsigned
  | Tint _ _ _, Tint I32 Unsigned _ => binint_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => binint_case_ii Signed
  | _,_  => binint_default
end.

Function sem_mod (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_binint t1 t2 with
  | binint_case_ii Unsigned =>
      match v1, v2 with
      | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero then None else Some (Vint (Int.modu n1 n2))
      | _, _ => None
      end
  | binint_case_ii Signed =>
      match v1,v2 with
      | Vint n1, Vint n2 =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some (Vint (Int.mods n1 n2))
      | _, _ => None
      end
  | binint_default =>
      None
  end.

Function sem_and (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_binint t1 t2 with
  | binint_case_ii sg =>
      match v1, v2 with
      | Vint n1, Vint n2 => Some (Vint(Int.and n1 n2))
      | _, _ => None
      end
  | binint_default => None
  end.

Function sem_or (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_binint t1 t2 with
  | binint_case_ii sg =>
      match v1, v2 with
      | Vint n1, Vint n2 => Some (Vint(Int.or n1 n2))
      | _, _ => None
      end
  | binint_default => None
  end.

Function sem_xor (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_binint t1 t2 with
  | binint_case_ii sg =>
      match v1, v2 with
      | Vint n1, Vint n2 => Some (Vint(Int.xor n1 n2))
      | _, _ => None
      end
  | binint_default => None
  end.

(** *** Shifts *)

Inductive classify_shift_cases : Type:=
  | shift_case_ii(s: signedness) (**r int , int *)
  | shift_default.

Definition classify_shift (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned _, Tint _ _ _ => shift_case_ii Unsigned
  | Tint _ _ _, Tint _ _ _ => shift_case_ii Signed
  | _,_  => shift_default
end.

Function sem_shl (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_shift t1 t2 with
  | shift_case_ii sg =>
      match v1, v2 with
      | Vint n1, Vint n2 =>
         if Int.ltu n2 Int.iwordsize then Some (Vint(Int.shl n1 n2)) else None
      | _, _ => None
      end
  | shift_default => None
  end.

Function sem_shr (v1: val) (t1: type) (v2: val) (t2: type): option val :=
  match classify_shift t1 t2 with 
  | shift_case_ii Unsigned =>
      match v1,v2 with 
      | Vint n1, Vint n2 =>
          if Int.ltu n2 Int.iwordsize then Some (Vint (Int.shru n1 n2)) else None
      | _,_ => None
      end
   | shift_case_ii Signed =>
      match v1,v2 with
      | Vint n1,  Vint n2 =>
          if Int.ltu n2 Int.iwordsize then Some (Vint (Int.shr n1 n2)) else None
      | _,  _ => None
      end
   | shift_default =>
      None
   end.

(** *** Comparisons *)

Inductive classify_cmp_cases : Type:=
  | cmp_case_ii(s: signedness) (**r int, int *)
  | cmp_case_pp                (**r pointer, pointer *)
  | cmp_case_ff                (**r float , float *)
  | cmp_case_if(s: signedness) (**r int, float *)
  | cmp_case_fi(s: signedness) (**r float, int *)
  | cmp_default.

Definition classify_cmp (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with 
  | Tint I32 Unsigned _ , Tint _ _ _ => cmp_case_ii Unsigned
  | Tint _ _ _ , Tint I32 Unsigned _ => cmp_case_ii Unsigned
  | Tint _ _ _ , Tint _ _ _ => cmp_case_ii Signed
  | Tfloat _ _ , Tfloat _ _ => cmp_case_ff
  | Tint _ sg _, Tfloat _ _ => cmp_case_if sg
  | Tfloat _ _, Tint _ sg _ => cmp_case_fi sg
  | Tpointer _ _ , Tpointer _ _ => cmp_case_pp
  | Tpointer _ _ , Tint _ _ _ => cmp_case_pp
  | Tint _ _ _, Tpointer _ _ => cmp_case_pp
  | _ , _ => cmp_default
  end.

Function sem_cmp (c:comparison)
                  (v1: val) (t1: type) (v2: val) (t2: type)
                  (m: mem): option val :=
  match classify_cmp t1 t2 with
  | cmp_case_ii Signed =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Val.of_bool (Int.cmp c n1 n2))
      | _,  _ => None
      end
  | cmp_case_ii Unsigned =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Val.of_bool (Int.cmpu c n1 n2))
      | _,  _ => None
      end
  | cmp_case_pp =>
      match v1,v2 with
      | Vint n1, Vint n2 => Some (Val.of_bool (Int.cmpu c n1 n2))
      | Vptr b1 ofs1,  Vptr b2 ofs2  =>
          if zeq b1 b2 then
            if Mem.weak_valid_pointer m b1 (Int.unsigned ofs1)
               && Mem.weak_valid_pointer m b2 (Int.unsigned ofs2)
            then Some (Val.of_bool (Int.cmpu c ofs1 ofs2))
            else None
          else
            if Mem.valid_pointer m b1 (Int.unsigned ofs1)
               && Mem.valid_pointer m b2 (Int.unsigned ofs2)
            then option_map Val.of_bool (Val.cmp_different_blocks c)
            else None
      | Vptr b ofs, Vint n =>
          if Int.eq n Int.zero
          then option_map Val.of_bool (Val.cmp_different_blocks c)
          else None
      | Vint n, Vptr b ofs =>
          if Int.eq n Int.zero
          then option_map Val.of_bool (Val.cmp_different_blocks c)
          else None
      | _,  _ => None
      end
  | cmp_case_ff =>
      match v1,v2 with
      | Vfloat f1, Vfloat f2 => Some (Val.of_bool (Float.cmp c f1 f2))  
      | _,  _ => None
      end
  | cmp_case_if sg =>
      match v1, v2 with
      | Vint n1, Vfloat n2 => Some (Val.of_bool (Float.cmp c (cast_int_float sg n1) n2))
      | _, _ => None
      end
  | cmp_case_fi sg =>
      match v1, v2 with
      | Vfloat n1, Vint n2 => Some (Val.of_bool (Float.cmp c n1 (cast_int_float sg n2)))
      | _, _ => None
      end
  | cmp_default => None
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
