(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Xavier Leroy, Collège de France and INRIA Paris             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Operators and addressing modes.  The abstract syntax and dynamic
  semantics for the CminorSel, RTL, LTL and Mach languages depend on the
  following types, defined in this library:
- [condition]:  boolean conditions for conditional branches;
- [operation]: arithmetic and logical operations;
- [addressing]: addressing modes for load and store operations.

  These types are processor-specific and correspond roughly to what the
  processor can compute in one instruction.  In other terms, these
  types reflect the state of the program after instruction selection.
  For a processor-independent set of operations, see the abstract
  syntax and dynamic semantics of the Cminor language.
*)

Require Import Axioms Coqlib BoolEqual.
Require Import AST Integers Floats Values Memory Globalenvs Events.

Set Implicit Arguments.
Local Transparent Archi.ptr64.

(** Shift amounts *)

Record amount32 : Type := {
  a32_amount :> int;
  a32_range  : Int.ltu a32_amount Int.iwordsize = true }.

Record amount64 : Type := {
  a64_amount :> int;
  a64_range  : Int.ltu a64_amount Int64.iwordsize' = true }.

(** Shifted operands *)

Inductive shift : Type :=
  | Slsl                                (**r left shift *)
  | Slsr                                (**r right unsigned shift *)
  | Sasr                                (**r right signed shift *)
  | Sror.                               (**r rotate right *)

(** Sign- or zero-extended operands *)

Inductive extension : Type :=
  | Xsgn32                              (**r from signed 32-bit integer to 64-bit integer *)
  | Xuns32.                             (**r from unsigned 32-bit integer to 64-bit integer *)

(** Conditions (boolean-valued operators). *)

Inductive condition: Type :=
(** Tests over 32-bit integers *)
  | Ccomp (c: comparison)                               (**r signed comparison *)
  | Ccompu (c: comparison)                              (**r unsigned comparison *)
  | Ccompimm (c: comparison) (n: int)                   (**r signed comparison with constant *)
  | Ccompuimm (c: comparison) (n: int)                  (**r unsigned comparison with constant *)
  | Ccompshift (c: comparison) (s: shift) (a: amount32) (**r signed comparison with shift *)
  | Ccompushift (c: comparison) (s: shift) (a: amount32)(**r unsigned comparison width shift *)
  | Cmaskzero (n: int)                                  (**r test [(arg & n) == 0] *)
  | Cmasknotzero (n: int)                               (**r test [(arg & n) != 0] *)
(** Tests over 64-bit integers *)
  | Ccompl (c: comparison)                              (**r signed comparison *)
  | Ccomplu (c: comparison)                             (**r unsigned comparison *)
  | Ccomplimm (c: comparison) (n: int64)                (**r signed comparison with constant *)
  | Ccompluimm (c: comparison) (n: int64)               (**r unsigned comparison with constant *)
  | Ccomplshift (c: comparison) (s: shift) (a: amount64)(**r signed comparison with shift *)
  | Ccomplushift (c: comparison) (s: shift) (a: amount64)(**r unsigned comparison width shift *)
  | Cmasklzero (n: int64)                               (**r test [(arg & n) == 0] *)
  | Cmasklnotzero (n: int64)                            (**r test [(arg & n) != 0] *)
(** Tests over 64-bit floating-point numbers *)
  | Ccompf (c: comparison)                              (**r FP comparison *)
  | Cnotcompf (c: comparison)                           (**r negation of an FP comparison *)
  | Ccompfzero (c: comparison)                          (**r comparison with 0.0 *)
  | Cnotcompfzero (c: comparison)                       (**r negation of comparison with 0.0 *)
(** Tests over 32-bit floating-point numbers *)
  | Ccompfs (c: comparison)                             (**r FP comparison *)
  | Cnotcompfs (c: comparison)                          (**r negation of an FP comparison *)
  | Ccompfszero (c: comparison)                         (**r equal to 0.0 *)
  | Cnotcompfszero (c: comparison).                     (**r not equal to 0.0 *)

(** Arithmetic and logical operations.  In the descriptions, [rd] is the
  result of the operation and [r1], [r2], etc, are the arguments. *)

Inductive operation : Type :=
  | Omove                                               (**r [rd = r1] *)
  | Ointconst (n: int)                                  (**r [rd] is set to the given integer constant *)
  | Olongconst (n: int64)                               (**r [rd] is set to the given integer constant *)
  | Ofloatconst (n: float)                              (**r [rd] is set to the given float constant *)
  | Osingleconst (n: float32)                           (**r [rd] is set to the given float constant *)
  | Oaddrsymbol (id: ident) (ofs: ptrofs)               (**r [rd] is set to the address of the symbol plus the given offset *)
  | Oaddrstack (ofs: ptrofs)                            (**r [rd] is set to the stack pointer plus the given offset *)
(** 32-bit integer arithmetic *)
  | Oshift (s: shift) (a: amount32)                     (**r shift or rotate by immediate quantity *)
  | Oadd                                                (**r [rd = r1 + r2] *)
  | Oaddshift (s: shift) (a: amount32)                  (**r [rd = r1 + shifted r2] *)
  | Oaddimm (n: int)                                    (**r [rd = r1 + n] *)
  | Oneg                                                (**r [rd = - r1]   *)                     
  | Onegshift (s: shift) (a: amount32)                  (**r [rd = - shifted r1] *)
  | Osub                                                (**r [rd = r1 - r2] *)
  | Osubshift (s: shift) (a: amount32)                  (**r [rd = r1 - shifted r2] *)
  | Omul                                                (**r [rd = r1 * r2] *)
  | Omuladd                                             (**r [rd = r1 + r2 * r3] *)
  | Omulsub                                             (**r [rd = r1 - r2 * r3] *)
  | Odiv                                                (**r [rd = r1 / r2] (signed) *)
  | Odivu                                               (**r [rd = r1 / r2] (unsigned) *)
  | Oand                                                (**r [rd = r1 & r2] *)
  | Oandshift (s: shift) (a: amount32)                  (**r [rd = r1 & shifted r2] *)
  | Oandimm (n: int)                                    (**r [rd = r1 & n] *)
  | Oor                                                 (**r [rd = r1 | r2] *)
  | Oorshift (s: shift) (a: amount32)                   (**r [rd = r1 | shifted r2] *)
  | Oorimm (n: int)                                     (**r [rd = r1 | n] *)
  | Oxor                                                (**r [rd = r1 ^ r2] *)
  | Oxorshift (s: shift) (a: amount32)                  (**r [rd = r1 ^ shifted r2] *)
  | Oxorimm (n: int)                                    (**r [rd = r1 ^ n] *)
  | Onot                                                (**r [rd = ~r1] *)
  | Onotshift (s: shift) (a: amount32)                  (**r [rd = ~ shifted r1] *)
  | Obic                                                (**r [rd = r1 & ~r2] *)
  | Obicshift (s: shift) (a: amount32)                  (**r [rd = r1 ^ ~ shifted r2] *)
  | Oorn                                                (**r [rd = r1 | ~r2] *)
  | Oornshift (s: shift) (a: amount32)                  (**r [rd = r1 | ~ shifted r2] *)
  | Oeqv                                                (**r [rd = r1 ^ ~r2] *)
  | Oeqvshift (s: shift) (a: amount32)                  (**r [rd = r1 | ~ shifted r2] *)
  | Oshl                                                (**r [rd = r1 << r2] *)
  | Oshr                                                (**r [rd = r1 >> r2] (signed) *)
  | Oshru                                               (**r [rd = r1 >> r2] (unsigned) *)
  | Oshrximm (n: int)                                   (**r [rd = r1 / 2^n] (signed) *)
  | Ozext (s: Z)                                        (**r [rd = zero_ext(r1,s)] *)
  | Osext (s: Z)                                        (**r [rd = sign_ext(r1,s)] *)
  | Oshlzext (s: Z) (a: amount32)                       (**r [rd = zero_ext(r1,s) << a] *)
  | Oshlsext (s: Z) (a: amount32)                       (**r [rd = sign_ext(r1,s) << a] *)
  | Ozextshr (a: amount32) (s: Z)                       (**r [rd = zero_ext(r1 >> a, s)] *)
  | Osextshr (a: amount32) (s: Z)                       (**r [rd = sign_ext(r1 >> a, s)] *)
(** 64-bit integer arithmetic *)
  | Oshiftl (s: shift) (a: amount64)                    (**r shift or rotate by immediate quantity *)
  | Oextend (x: extension) (a: amount64)                (**r convert from 32 to 64 bits and shift *)
  | Omakelong                                           (**r [rd = r1 << 32 | r2] *)
  | Olowlong                                            (**r [rd = low-word(r1)] *)
  | Ohighlong                                           (**r [rd = high-word(r1)] *)
  | Oaddl                                               (**r [rd = r1 + r2] *)
  | Oaddlshift (s: shift) (a: amount64)                 (**r [rd = r1 + shifted r2] *)
  | Oaddlext (x: extension) (a: amount64)               (**r [rd = r1 + shifted, converted r2] *)
  | Oaddlimm (n: int64)                                 (**r [rd = r1 + n] *)
  | Onegl                                               (**r [rd = - r1]   *)                     
  | Oneglshift (s: shift) (a: amount64)                 (**r [rd = - shifted r1] *)
  | Osubl                                               (**r [rd = r1 - r2] *)
  | Osublshift (s: shift) (a: amount64)                 (**r [rd = r1 - shifted r2] *)
  | Osublext (x: extension) (a: amount64)               (**r [rd = r1 - shifted, converted r2] *)
  | Omull                                               (**r [rd = r1 * r2] *)
  | Omulladd                                            (**r [rd = r1 + r2 * r3] *)
  | Omullsub                                            (**r [rd = r1 - r2 * r3] *)
  | Omullhs                                             (**r [rd = high part of r1 * r2 (signed)] *)
  | Omullhu                                             (**r [rd = high part of r1 * r2 (unsigned)] *)
  | Odivl                                               (**r [rd = r1 / r2] (signed) *)
  | Odivlu                                              (**r [rd = r1 / r2] (unsigned) *)
  | Oandl                                               (**r [rd = r1 & r2] *)
  | Oandlshift (s: shift) (a: amount64)                 (**r [rd = r1 & shifted r2] *)
  | Oandlimm (n: int64)                                 (**r [rd = r1 & n] *)
  | Oorl                                                (**r [rd = r1 | r2] *)
  | Oorlshift (s: shift) (a: amount64)                  (**r [rd = r1 | shifted r2] *)
  | Oorlimm (n: int64)                                  (**r [rd = r1 | n] *)
  | Oxorl                                               (**r [rd = r1 ^ r2] *)
  | Oxorlshift (s: shift) (a: amount64)                 (**r [rd = r1 ^ shifted r2] *)
  | Oxorlimm (n: int64)                                 (**r [rd = r1 ^ n] *)
  | Onotl                                               (**r [rd = ~r1] *)
  | Onotlshift (s: shift) (a: amount64)                 (**r [rd = ~ shifted r1] *)
  | Obicl                                               (**r [rd = r1 & ~r2] *)
  | Obiclshift (s: shift) (a: amount64)                 (**r [rd = r1 ^ ~ shifted r2] *)
  | Oornl                                               (**r [rd = r1 | ~r2] *)
  | Oornlshift (s: shift) (a: amount64)                 (**r [rd = r1 | ~ shifted r2] *)
  | Oeqvl                                               (**r [rd = r1 ^ ~r2] *)
  | Oeqvlshift (s: shift) (a: amount64)                 (**r [rd = r1 | ~ shifted r2] *)
  | Oshll                                               (**r [rd = r1 << r2] *)
  | Oshrl                                               (**r [rd = r1 >> r2] (signed) *)
  | Oshrlu                                              (**r [rd = r1 >> r2] (unsigned) *)
  | Oshrlximm (n: int)                                  (**r [rd = r1 / 2^n] (signed) *)
  | Ozextl (s: Z)                                       (**r [rd = zero_ext(r1,s)] *)
  | Osextl (s: Z)                                       (**r [rd = sign_ext(r1,s)] *)
  | Oshllzext (s: Z) (a: amount64)                      (**r [rd = zero_ext(r1,s) << a] *)
  | Oshllsext (s: Z) (a: amount64)                      (**r [rd = sign_ext(r1,s) << a] *)
  | Ozextshrl (a: amount64) (s: Z)                      (**r [rd = zero_ext(r1 >> a, s)] *)
  | Osextshrl (a: amount64) (s: Z)                      (**r [rd = sign_ext(r1 >> a, s)] *)
(** 64-bit floating-point arithmetic *)
  | Onegf                                               (**r [rd = - r1] *)
  | Oabsf                                               (**r [rd = abs(r1)] *)
  | Oaddf                                               (**r [rd = r1 + r2] *)
  | Osubf                                               (**r [rd = r1 - r2] *)
  | Omulf                                               (**r [rd = r1 * r2] *)
  | Odivf                                               (**r [rd = r1 / r2] *)
(** 32-bit floating-point arithmetic *)
  | Onegfs                                              (**r [rd = - r1] *)
  | Oabsfs                                              (**r [rd = abs(r1)] *)
  | Oaddfs                                              (**r [rd = r1 + r2] *)
  | Osubfs                                              (**r [rd = r1 - r2] *)
  | Omulfs                                              (**r [rd = r1 * r2] *)
  | Odivfs                                              (**r [rd = r1 / r2] *)
  | Osingleoffloat                                      (**r [rd] is [r1] truncated to single-precision float *)
  | Ofloatofsingle                                      (**r [rd] is [r1] extended to double-precision float *)
(** Conversions between int and float *)
  | Ointoffloat                                         (**r [rd = signed_int_of_float64(r1)] *)
  | Ointuoffloat                                        (**r [rd = unsigned_int_of_float64(r1)] *)
  | Ofloatofint                                         (**r [rd = float64_of_signed_int(r1)] *)
  | Ofloatofintu                                        (**r [rd = float64_of_unsigned_int(r1)] *)
  | Ointofsingle                                        (**r [rd = signed_int_of_float32(r1)] *)
  | Ointuofsingle                                       (**r [rd = unsigned_int_of_float32(r1)] *)
  | Osingleofint                                        (**r [rd = float32_of_signed_int(r1)] *)
  | Osingleofintu                                       (**r [rd = float32_of_unsigned_int(r1)] *)
  | Olongoffloat                                        (**r [rd = signed_long_of_float64(r1)] *)
  | Olonguoffloat                                       (**r [rd = unsigned_long_of_float64(r1)] *)
  | Ofloatoflong                                        (**r [rd = float64_of_signed_long(r1)] *)
  | Ofloatoflongu                                       (**r [rd = float64_of_unsigned_long(r1)] *)
  | Olongofsingle                                       (**r [rd = signed_long_of_float32(r1)] *)
  | Olonguofsingle                                      (**r [rd = unsigned_long_of_float32(r1)] *)
  | Osingleoflong                                       (**r [rd = float32_of_signed_long(r1)] *)
  | Osingleoflongu                                      (**r [rd = float32_of_unsigned_int(r1)] *)
(** Boolean tests *)
  | Ocmp (cond: condition)                              (**r [rd = 1] if condition holds, [rd = 0] otherwise. *)
  | Osel (cond: condition) (ty: typ).                   (**r [rd = rs1] if condition holds, [rd = rs2] otherwise. *)

(** Addressing modes.  [r1], [r2], etc, are the arguments to the addressing. *)

Inductive addressing: Type :=
  | Aindexed (ofs: int64)                               (**r Address is [r1 + offset] *)
  | Aindexed2                                           (**r Address is [r1 + r2] *)
  | Aindexed2shift (a: amount64)                        (**r Address is [r1 + r2 << a] *)
  | Aindexed2ext (x: extension) (a: amount64)           (**r Address is [r1 + sign-or-zero-ext(r2) << a] *)
  | Aglobal (id: ident) (ofs: ptrofs)                   (**r Address is [global + offset] *)
  | Ainstack (ofs: ptrofs).                             (**r Address is [stack_pointer + offset] *)

(** Comparison functions (used in modules [CSE] and [Allocation]). *)

Definition eq_amount32 (x y: amount32): {x=y} + {x<>y}.
Proof.
  destruct x as [x Px], y as [y Py].
  destruct (Int.eq_dec x y).
- subst y. assert (Px = Py) by (apply proof_irr). subst Py. left; auto.
- right; congruence.
Defined.

Definition eq_amount64 (x y: amount64): {x=y} + {x<>y}.
Proof.
  destruct x as [x Px], y as [y Py].
  destruct (Int.eq_dec x y).
- subst y. assert (Px = Py) by (apply proof_irr). subst Py. left; auto.
- right; congruence.
Defined.

Definition eq_shift (x y: shift): {x=y} + {x<>y}.
Proof.
  decide equality.
Defined.

Definition eq_extension (x y: extension): {x=y} + {x<>y}.
Proof.
  decide equality.
Defined.

Definition eq_condition (x y: condition) : {x=y} + {x<>y}.
Proof.
  assert (forall (x y: comparison), {x=y}+{x<>y}) by decide equality.
  generalize Int.eq_dec Int64.eq_dec eq_shift eq_amount32 eq_amount64; intro.
  decide equality.
Defined.

Definition eq_addressing (x y: addressing) : {x=y} + {x<>y}.
Proof.
  generalize ident_eq Int64.eq_dec Ptrofs.eq_dec eq_extension eq_amount64; intros.
  decide equality.
Defined.

Definition eq_operation: forall (x y: operation), {x=y} + {x<>y}.
Proof.
  intros.
  generalize Int.eq_dec Int64.eq_dec Ptrofs.eq_dec Float.eq_dec Float32.eq_dec
             zeq ident_eq eq_shift eq_extension eq_amount32 eq_amount64
             typ_eq eq_condition; 
  decide equality.
Defined.

(** Alternative:

Definition beq_operation: forall (x y: operation), bool.
Proof.
  generalize Int.eq_dec Int64.eq_dec Ptrofs.eq_dec Float.eq_dec Float32.eq_dec
             zeq ident_eq eq_shift eq_extension eq_amount32 eq_amount64
             eq_condition typ_eq; boolean_equality.
Defined.

Definition eq_operation: forall (x y: operation), {x=y} + {x<>y}.
Proof.
  decidable_equality_from beq_operation.
Defined.
*)

(** * Evaluation functions *)

(** Evaluation of conditions, operators and addressing modes applied
  to lists of values.  Return [None] when the computation can trigger an
  error, e.g. integer division by zero.  [eval_condition] returns a boolean,
  [eval_operation] and [eval_addressing] return a value. *)

Definition eval_shift (s: shift) (v: val) (n: amount32) : val :=
  match s with
  | Slsl => Val.shl v (Vint n)
  | Slsr => Val.shru v (Vint n)
  | Sasr => Val.shr v (Vint n)
  | Sror => Val.ror v (Vint n)
  end.

Definition eval_shiftl (s: shift) (v: val) (n: amount64) : val :=
  match s with
  | Slsl => Val.shll v (Vint n)
  | Slsr => Val.shrlu v (Vint n)
  | Sasr => Val.shrl v (Vint n)
  | Sror => Val.rorl v (Vint n)
  end.

Definition eval_extend (x: extension) (v: val) (n: amount64) : val :=
  Val.shll
    (match x with
      | Xsgn32 => Val.longofint v
      | Xuns32 => Val.longofintu v
     end)
    (Vint n).

Definition eval_condition (cond: condition) (vl: list val) (m: mem): option bool :=
  match cond, vl with
  | Ccomp c, v1 :: v2 :: nil => Val.cmp_bool c v1 v2
  | Ccompu c, v1 :: v2 :: nil => Val.cmpu_bool (Mem.valid_pointer m) c v1 v2
  | Ccompimm c n, v1 :: nil => Val.cmp_bool c v1 (Vint n)
  | Ccompuimm c n, v1 :: nil => Val.cmpu_bool (Mem.valid_pointer m) c v1 (Vint n)
  | Ccompshift c s a, v1 :: v2 :: nil => Val.cmp_bool c v1 (eval_shift s v2 a)
  | Ccompushift c s a, v1 :: v2 :: nil => Val.cmpu_bool (Mem.valid_pointer m) c v1 (eval_shift s v2 a)
  | Cmaskzero n, v1 :: nil => Val.cmp_bool Ceq (Val.and v1 (Vint n)) (Vint Int.zero)
  | Cmasknotzero n, v1 :: nil => Val.cmp_bool Cne (Val.and v1 (Vint n)) (Vint Int.zero)

  | Ccompl c, v1 :: v2 :: nil => Val.cmpl_bool c v1 v2
  | Ccomplu c, v1 :: v2 :: nil => Val.cmplu_bool (Mem.valid_pointer m) c v1 v2
  | Ccomplimm c n, v1 :: nil => Val.cmpl_bool c v1 (Vlong n)
  | Ccompluimm c n, v1 :: nil => Val.cmplu_bool (Mem.valid_pointer m) c v1 (Vlong n)
  | Ccomplshift c s a, v1 :: v2 :: nil => Val.cmpl_bool c v1 (eval_shiftl s v2 a)
  | Ccomplushift c s a, v1 :: v2 :: nil => Val.cmplu_bool (Mem.valid_pointer m) c v1 (eval_shiftl s v2 a)
  | Cmasklzero n, v1 :: nil => Val.cmpl_bool Ceq (Val.andl v1 (Vlong n)) (Vlong Int64.zero)
  | Cmasklnotzero n, v1 :: nil => Val.cmpl_bool Cne (Val.andl v1 (Vlong n)) (Vlong Int64.zero)

  | Ccompf c, v1 :: v2 :: nil => Val.cmpf_bool c v1 v2
  | Cnotcompf c, v1 :: v2 :: nil => option_map negb (Val.cmpf_bool c v1 v2)
  | Ccompfzero c, v1 :: nil => Val.cmpf_bool c v1 (Vfloat Float.zero)
  | Cnotcompfzero c, v1 :: nil => option_map negb (Val.cmpf_bool c v1 (Vfloat Float.zero))

  | Ccompfs c, v1 :: v2 :: nil => Val.cmpfs_bool c v1 v2
  | Cnotcompfs c, v1 :: v2 :: nil => option_map negb (Val.cmpfs_bool c v1 v2)
  | Ccompfszero c, v1 :: nil => Val.cmpfs_bool c v1 (Vsingle Float32.zero)
  | Cnotcompfszero c, v1 :: nil => option_map negb (Val.cmpfs_bool c v1 (Vsingle Float32.zero))

  | _, _ => None
  end.

Definition eval_operation
    (F V: Type) (genv: Genv.t F V) (sp: val)
    (op: operation) (vl: list val) (m: mem): option val :=
  match op, vl with
  | Omove, v1::nil => Some v1
  | Ointconst n, nil => Some (Vint n)
  | Olongconst n, nil => Some (Vlong n)
  | Ofloatconst n, nil => Some (Vfloat n)
  | Osingleconst n, nil => Some (Vsingle n)
  | Oaddrsymbol s ofs, nil => Some (Genv.symbol_address genv s ofs)
  | Oaddrstack ofs, nil => Some (Val.offset_ptr sp ofs)

  | Oshift s a, v1 :: nil => Some (eval_shift s v1 a)
  | Oadd, v1 :: v2 :: nil => Some (Val.add v1 v2)
  | Oaddshift s a, v1 :: v2 :: nil => Some (Val.add v1 (eval_shift s v2 a))
  | Oaddimm n, v1 :: nil => Some (Val.add v1 (Vint n))
  | Oneg, v1 :: nil => Some (Val.neg v1)
  | Onegshift s a, v1 :: nil => Some (Val.neg (eval_shift s v1 a))
  | Osub, v1 :: v2 :: nil => Some (Val.sub v1 v2)
  | Osubshift s a, v1 :: v2 :: nil => Some (Val.sub v1 (eval_shift s v2 a))
  | Omul, v1 :: v2 :: nil => Some (Val.mul v1 v2)
  | Omuladd, v1 :: v2 :: v3 :: nil => Some (Val.add v1 (Val.mul v2 v3))
  | Omulsub, v1 :: v2 :: v3 :: nil => Some (Val.sub v1 (Val.mul v2 v3))
  | Odiv, v1 :: v2 :: nil => Val.divs v1 v2
  | Odivu, v1 :: v2 :: nil => Val.divu v1 v2
  | Oand, v1 :: v2 :: nil => Some (Val.and v1 v2)
  | Oandshift s a, v1 :: v2 :: nil => Some (Val.and v1 (eval_shift s v2 a))
  | Oandimm n, v1 :: nil => Some (Val.and v1 (Vint n))
  | Oor, v1 :: v2 :: nil => Some (Val.or v1 v2)
  | Oorshift s a, v1 :: v2 :: nil => Some (Val.or v1 (eval_shift s v2 a))
  | Oorimm n, v1 :: nil => Some (Val.or v1 (Vint n))
  | Oxor, v1 :: v2 :: nil => Some (Val.xor v1 v2)
  | Oxorshift s a, v1 :: v2 :: nil => Some (Val.xor v1 (eval_shift s v2 a))
  | Oxorimm n, v1 :: nil => Some (Val.xor v1 (Vint n))
  | Onot, v1 :: nil => Some (Val.notint v1)
  | Onotshift s a, v1 :: nil => Some (Val.notint (eval_shift s v1 a))
  | Obic, v1 :: v2 :: nil => Some (Val.and v1 (Val.notint v2))
  | Obicshift s a, v1 :: v2 :: nil => Some (Val.and v1 (Val.notint (eval_shift s v2 a)))
  | Oorn, v1 :: v2 :: nil => Some (Val.or v1 (Val.notint v2))
  | Oornshift s a, v1 :: v2 :: nil => Some (Val.or v1 (Val.notint (eval_shift s v2 a)))
  | Oeqv, v1 :: v2 :: nil => Some (Val.xor v1 (Val.notint v2))
  | Oeqvshift s a, v1 :: v2 :: nil => Some (Val.xor v1 (Val.notint (eval_shift s v2 a)))
  | Oshl, v1 :: v2 :: nil => Some (Val.shl v1 v2)
  | Oshr, v1 :: v2 :: nil => Some (Val.shr v1 v2)
  | Oshru, v1 :: v2 :: nil => Some (Val.shru v1 v2)
  | Oshrximm n, v1::nil => Val.shrx v1 (Vint n)
  | Ozext s, v1 :: nil => Some (Val.zero_ext s v1)
  | Osext s, v1 :: nil => Some (Val.sign_ext s v1)
  | Oshlzext s a, v1 :: nil => Some (Val.shl (Val.zero_ext s v1) (Vint a))
  | Oshlsext s a, v1 :: nil => Some (Val.shl (Val.sign_ext s v1) (Vint a))
  | Ozextshr a s, v1 :: nil => Some (Val.zero_ext s (Val.shru v1 (Vint a)))
  | Osextshr a s, v1 :: nil => Some (Val.sign_ext s (Val.shr v1 (Vint a)))

  | Oshiftl s a, v1 :: nil => Some (eval_shiftl s v1 a)
  | Oextend x a, v1 :: nil => Some (eval_extend x v1 a)
  | Omakelong, v1::v2::nil => Some (Val.longofwords v1 v2)
  | Olowlong, v1::nil => Some (Val.loword v1)
  | Ohighlong, v1::nil => Some (Val.hiword v1)
  | Oaddl, v1 :: v2 :: nil => Some (Val.addl v1 v2)
  | Oaddlshift s a, v1 :: v2 :: nil => Some (Val.addl v1 (eval_shiftl s v2 a))
  | Oaddlext x a, v1 :: v2 :: nil => Some (Val.addl v1 (eval_extend x v2 a))
  | Oaddlimm n, v1 :: nil => Some (Val.addl v1 (Vlong n))
  | Onegl, v1 :: nil => Some (Val.negl v1)
  | Oneglshift s a, v1 :: nil => Some (Val.negl (eval_shiftl s v1 a))
  | Osubl, v1 :: v2 :: nil => Some (Val.subl v1 v2)
  | Osublshift s a, v1 :: v2 :: nil => Some (Val.subl v1 (eval_shiftl s v2 a))
  | Osublext x a, v1 :: v2 :: nil => Some (Val.subl v1 (eval_extend x v2 a))
  | Omull, v1 :: v2 :: nil => Some (Val.mull v1 v2)
  | Omulladd, v1 :: v2 :: v3 :: nil => Some (Val.addl v1 (Val.mull v2 v3))
  | Omullsub, v1 :: v2 :: v3 :: nil => Some (Val.subl v1 (Val.mull v2 v3))
  | Omullhs, v1::v2::nil => Some (Val.mullhs v1 v2)
  | Omullhu, v1::v2::nil => Some (Val.mullhu v1 v2)
  | Odivl, v1 :: v2 :: nil => Val.divls v1 v2
  | Odivlu, v1 :: v2 :: nil => Val.divlu v1 v2
  | Oandl, v1 :: v2 :: nil => Some (Val.andl v1 v2)
  | Oandlshift s a, v1 :: v2 :: nil => Some (Val.andl v1 (eval_shiftl s v2 a))
  | Oandlimm n, v1 :: nil => Some (Val.andl v1 (Vlong n))
  | Oorl, v1 :: v2 :: nil => Some (Val.orl v1 v2)
  | Oorlshift s a, v1 :: v2 :: nil => Some (Val.orl v1 (eval_shiftl s v2 a))
  | Oorlimm n, v1 :: nil => Some (Val.orl v1 (Vlong n))
  | Oxorl, v1 :: v2 :: nil => Some (Val.xorl v1 v2)
  | Oxorlshift s a, v1 :: v2 :: nil => Some (Val.xorl v1 (eval_shiftl s v2 a))
  | Oxorlimm n, v1 :: nil => Some (Val.xorl v1 (Vlong n))
  | Onotl, v1 :: nil => Some (Val.notl v1)
  | Onotlshift s a, v1 :: nil => Some (Val.notl (eval_shiftl s v1 a))
  | Obicl, v1 :: v2 :: nil => Some (Val.andl v1 (Val.notl v2))
  | Obiclshift s a, v1 :: v2 :: nil => Some (Val.andl v1 (Val.notl (eval_shiftl s v2 a)))
  | Oornl, v1 :: v2 :: nil => Some (Val.orl v1 (Val.notl v2))
  | Oornlshift s a, v1 :: v2 :: nil => Some (Val.orl v1 (Val.notl (eval_shiftl s v2 a)))
  | Oeqvl, v1 :: v2 :: nil => Some (Val.xorl v1 (Val.notl v2))
  | Oeqvlshift s a, v1 :: v2 :: nil => Some (Val.xorl v1 (Val.notl (eval_shiftl s v2 a)))
  | Oshll, v1 :: v2 :: nil => Some (Val.shll v1 v2)
  | Oshrl, v1 :: v2 :: nil => Some (Val.shrl v1 v2)
  | Oshrlu, v1 :: v2 :: nil => Some (Val.shrlu v1 v2)
  | Oshrlximm n, v1::nil => Val.shrxl v1 (Vint n)
  | Ozextl s, v1 :: nil => Some (Val.zero_ext_l s v1)
  | Osextl s, v1 :: nil => Some (Val.sign_ext_l s v1)
  | Oshllzext s a, v1 :: nil => Some (Val.shll (Val.zero_ext_l s v1) (Vint a))
  | Oshllsext s a, v1 :: nil => Some (Val.shll (Val.sign_ext_l s v1) (Vint a))
  | Ozextshrl a s, v1 :: nil => Some (Val.zero_ext_l s (Val.shrlu v1 (Vint a)))
  | Osextshrl a s, v1 :: nil => Some (Val.sign_ext_l s (Val.shrl v1 (Vint a)))

  | Onegf, v1::nil => Some (Val.negf v1)
  | Oabsf, v1::nil => Some (Val.absf v1)
  | Oaddf, v1::v2::nil => Some (Val.addf v1 v2)
  | Osubf, v1::v2::nil => Some (Val.subf v1 v2)
  | Omulf, v1::v2::nil => Some (Val.mulf v1 v2)
  | Odivf, v1::v2::nil => Some (Val.divf v1 v2)

  | Onegfs, v1::nil => Some (Val.negfs v1)
  | Oabsfs, v1::nil => Some (Val.absfs v1)
  | Oaddfs, v1::v2::nil => Some (Val.addfs v1 v2)
  | Osubfs, v1::v2::nil => Some (Val.subfs v1 v2)
  | Omulfs, v1::v2::nil => Some (Val.mulfs v1 v2)
  | Odivfs, v1::v2::nil => Some (Val.divfs v1 v2)

  | Osingleoffloat, v1::nil => Some (Val.singleoffloat v1)
  | Ofloatofsingle, v1::nil => Some (Val.floatofsingle v1)
  | Ointoffloat, v1::nil => Val.intoffloat v1
  | Ointuoffloat, v1::nil => Val.intuoffloat v1
  | Ofloatofint, v1::nil => Val.floatofint v1
  | Ofloatofintu, v1::nil => Val.floatofintu v1
  | Ointofsingle, v1::nil => Val.intofsingle v1
  | Ointuofsingle, v1::nil => Val.intuofsingle v1
  | Osingleofint, v1::nil => Val.singleofint v1
  | Osingleofintu, v1::nil => Val.singleofintu v1
  | Olongoffloat, v1::nil => Val.longoffloat v1
  | Olonguoffloat, v1::nil => Val.longuoffloat v1
  | Ofloatoflong, v1::nil => Val.floatoflong v1
  | Ofloatoflongu, v1::nil => Val.floatoflongu v1
  | Olongofsingle, v1::nil => Val.longofsingle v1
  | Olonguofsingle, v1::nil => Val.longuofsingle v1
  | Osingleoflong, v1::nil => Val.singleoflong v1
  | Osingleoflongu, v1::nil => Val.singleoflongu v1

  | Ocmp c, _ => Some (Val.of_optbool (eval_condition c vl m))
  | Osel c ty, v1::v2::vl => Some(Val.select (eval_condition c vl m) v1 v2 ty)
  | _, _ => None
  end.

Definition eval_addressing
    (F V: Type) (genv: Genv.t F V) (sp: val)
    (addr: addressing) (vl: list val) : option val :=
  match addr, vl with
  | Aindexed n, v1 :: nil => Some (Val.addl v1 (Vlong n))
  | Aindexed2, v1 :: v2 :: nil => Some (Val.addl v1 v2)
  | Aindexed2shift a, v1 :: v2 :: nil => Some (Val.addl v1 (Val.shll v2 (Vint a)))
  | Aindexed2ext x a, v1 :: v2 :: nil => Some (Val.addl v1 (eval_extend x v2 a))
  | Aglobal s ofs, nil => Some (Genv.symbol_address genv s ofs)
  | Ainstack n, nil => Some (Val.offset_ptr sp n)
  | _, _ => None
  end.

Remark eval_addressing_Ainstack:
  forall (F V: Type) (genv: Genv.t F V) sp ofs,
  eval_addressing genv sp (Ainstack ofs) nil = Some (Val.offset_ptr sp ofs).
Proof.
  intros. reflexivity.
Qed.

Remark eval_addressing_Ainstack_inv:
  forall (F V: Type) (genv: Genv.t F V) sp ofs vl v,
  eval_addressing genv sp (Ainstack ofs) vl = Some v -> vl = nil /\ v = Val.offset_ptr sp ofs.
Proof.
  unfold eval_addressing; intros; destruct vl; inv H; auto.
Qed.

Ltac FuncInv :=
  match goal with
  | H: (match ?x with nil => _ | _ :: _ => _ end = Some _) |- _ =>
      destruct x; simpl in H; FuncInv
  | H: (match ?v with Vundef => _ | Vint _ => _ | Vfloat _ => _ | Vptr _ _ => _ end = Some _) |- _ =>
      destruct v; simpl in H; FuncInv
  | H: (if Archi.ptr64 then _ else _) = Some _ |- _ =>
      change Archi.ptr64 with true in H; simpl in H; FuncInv
  | H: (Some _ = Some _) |- _ =>
      injection H; intros; clear H; FuncInv
  | H: (None = Some _) |- _ =>
      discriminate H
  | _ =>
      idtac
  end.

(** * Static typing of conditions, operators and addressing modes. *)

Definition type_of_condition (c: condition) : list typ :=
  match c with
  | Ccomp _ => Tint :: Tint :: nil
  | Ccompu _ => Tint :: Tint :: nil
  | Ccompimm _ _ => Tint :: nil
  | Ccompuimm _ _ => Tint :: nil
  | Ccompshift _ _ _ => Tint :: Tint :: nil
  | Ccompushift _ _ _ => Tint :: Tint :: nil
  | Cmaskzero _ => Tint :: nil
  | Cmasknotzero _ => Tint :: nil
  | Ccompl _ => Tlong :: Tlong :: nil
  | Ccomplu _ => Tlong :: Tlong :: nil
  | Ccomplimm _ _ => Tlong :: nil
  | Ccompluimm _ _ => Tlong :: nil
  | Ccomplshift _ _ _ => Tlong :: Tlong :: nil
  | Ccomplushift _ _ _ => Tlong :: Tlong :: nil
  | Cmasklzero _ => Tlong :: nil
  | Cmasklnotzero _ => Tlong :: nil
  | Ccompf _ => Tfloat :: Tfloat :: nil
  | Cnotcompf _ => Tfloat :: Tfloat :: nil
  | Ccompfzero _ => Tfloat :: nil
  | Cnotcompfzero _ => Tfloat :: nil
  | Ccompfs _ => Tsingle :: Tsingle :: nil
  | Cnotcompfs _ => Tsingle :: Tsingle :: nil
  | Ccompfszero _ => Tsingle :: nil
  | Cnotcompfszero _ => Tsingle :: nil
  end.

Definition type_of_operation (op: operation) : list typ * typ :=
  match op with
  | Omove => (nil, Tint)   (* treated specially *)
  | Ointconst _ => (nil, Tint)
  | Olongconst _ => (nil, Tlong)
  | Ofloatconst f => (nil, Tfloat)
  | Osingleconst f => (nil, Tsingle)
  | Oaddrsymbol _ _ => (nil, Tptr)
  | Oaddrstack _ => (nil, Tptr)

  | Oshift _ _ => (Tint :: nil, Tint)
  | Oadd => (Tint :: Tint :: nil, Tint)
  | Oaddshift _ _ => (Tint :: Tint :: nil, Tint)
  | Oaddimm _ => (Tint :: nil, Tint)
  | Oneg => (Tint :: nil, Tint)
  | Onegshift _ _ => (Tint :: nil, Tint)
  | Osub => (Tint :: Tint :: nil, Tint)
  | Osubshift _ _ => (Tint :: Tint :: nil, Tint)
  | Omul => (Tint :: Tint :: nil, Tint)
  | Omuladd => (Tint :: Tint :: Tint :: nil, Tint)
  | Omulsub => (Tint :: Tint :: Tint :: nil, Tint)
  | Odiv => (Tint :: Tint :: nil, Tint)
  | Odivu => (Tint :: Tint :: nil, Tint)
  | Oand => (Tint :: Tint :: nil, Tint)
  | Oandshift _ _ => (Tint :: Tint :: nil, Tint)
  | Oandimm _ => (Tint :: nil, Tint)
  | Oor => (Tint :: Tint :: nil, Tint)
  | Oorshift _ _ => (Tint :: Tint :: nil, Tint)
  | Oorimm _ => (Tint :: nil, Tint)
  | Oxor => (Tint :: Tint :: nil, Tint)
  | Oxorshift _ _ => (Tint :: Tint :: nil, Tint)
  | Oxorimm _ => (Tint :: nil, Tint)
  | Onot => (Tint :: nil, Tint)
  | Onotshift _ _ => (Tint :: nil, Tint)
  | Obic => (Tint :: Tint :: nil, Tint)
  | Obicshift _ _ => (Tint :: Tint :: nil, Tint)
  | Oorn => (Tint :: Tint :: nil, Tint)
  | Oornshift _ _ => (Tint :: Tint :: nil, Tint)
  | Oeqv => (Tint :: Tint :: nil, Tint)
  | Oeqvshift _ _ => (Tint :: Tint :: nil, Tint)
  | Oshl => (Tint :: Tint :: nil, Tint)
  | Oshr => (Tint :: Tint :: nil, Tint)
  | Oshru => (Tint :: Tint :: nil, Tint)
  | Oshrximm _ => (Tint :: nil, Tint)
  | Ozext _ => (Tint :: nil, Tint)
  | Osext _ => (Tint :: nil, Tint)
  | Oshlzext _ _ => (Tint :: nil, Tint)
  | Oshlsext _ _ => (Tint :: nil, Tint)
  | Ozextshr _ _ => (Tint :: nil, Tint)
  | Osextshr _ _ => (Tint :: nil, Tint)

  | Oshiftl _ _ => (Tlong :: nil, Tlong)
  | Oextend _ _ => (Tint :: nil, Tlong)
  | Omakelong => (Tint :: Tint :: nil, Tlong)
  | Olowlong => (Tlong :: nil, Tint)
  | Ohighlong => (Tlong :: nil, Tint)
  | Oaddl => (Tlong :: Tlong :: nil, Tlong)
  | Oaddlshift _ _ => (Tlong :: Tlong :: nil, Tlong) 
  | Oaddlext _ _ => (Tlong :: Tint :: nil, Tlong)
  | Oaddlimm _ => (Tlong :: nil, Tlong)
  | Onegl => (Tlong :: nil, Tlong)
  | Oneglshift _ _ => (Tlong :: nil, Tlong)
  | Osubl => (Tlong :: Tlong :: nil, Tlong)
  | Osublshift _ _ => (Tlong :: Tlong :: nil, Tlong)
  | Osublext _ _ => (Tlong :: Tint :: nil, Tlong)
  | Omull => (Tlong :: Tlong :: nil, Tlong)
  | Omulladd => (Tlong :: Tlong :: Tlong :: nil, Tlong)
  | Omullsub => (Tlong :: Tlong :: Tlong :: nil, Tlong)
  | Omullhs => (Tlong :: Tlong :: nil, Tlong)
  | Omullhu => (Tlong :: Tlong :: nil, Tlong)
  | Odivl => (Tlong :: Tlong :: nil, Tlong)
  | Odivlu => (Tlong :: Tlong :: nil, Tlong)
  | Oandl => (Tlong :: Tlong :: nil, Tlong)
  | Oandlshift _ _ => (Tlong :: Tlong :: nil, Tlong)
  | Oandlimm _ => (Tlong :: nil, Tlong)
  | Oorl => (Tlong :: Tlong :: nil, Tlong)
  | Oorlshift _ _ => (Tlong :: Tlong :: nil, Tlong)
  | Oorlimm _ => (Tlong :: nil, Tlong)
  | Oxorl => (Tlong :: Tlong :: nil, Tlong)
  | Oxorlshift _ _ => (Tlong :: Tlong :: nil, Tlong)
  | Oxorlimm _ => (Tlong :: nil, Tlong)
  | Onotl => (Tlong :: nil, Tlong)
  | Onotlshift _ _ => (Tlong :: nil, Tlong)
  | Obicl => (Tlong :: Tlong :: nil, Tlong)
  | Obiclshift _ _ => (Tlong :: Tlong :: nil, Tlong)
  | Oornl => (Tlong :: Tlong :: nil, Tlong)
  | Oornlshift _ _ => (Tlong :: Tlong :: nil, Tlong)
  | Oeqvl => (Tlong :: Tlong :: nil, Tlong)
  | Oeqvlshift _ _ => (Tlong :: Tlong :: nil, Tlong)
  | Oshll => (Tlong :: Tint :: nil, Tlong)
  | Oshrl => (Tlong :: Tint :: nil, Tlong)
  | Oshrlu => (Tlong :: Tint :: nil, Tlong)
  | Oshrlximm _ => (Tlong :: nil, Tlong)
  | Ozextl _ => (Tlong :: nil, Tlong)
  | Osextl _ => (Tlong :: nil, Tlong)
  | Oshllzext _ _ => (Tlong :: nil, Tlong)
  | Oshllsext _ _ => (Tlong :: nil, Tlong)
  | Ozextshrl _ _ => (Tlong :: nil, Tlong)
  | Osextshrl _ _ => (Tlong :: nil, Tlong)

  | Onegf => (Tfloat :: nil, Tfloat)
  | Oabsf => (Tfloat :: nil, Tfloat)
  | Oaddf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Osubf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Omulf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Odivf => (Tfloat :: Tfloat :: nil, Tfloat)

  | Onegfs => (Tsingle :: nil, Tsingle)
  | Oabsfs => (Tsingle :: nil, Tsingle)
  | Oaddfs => (Tsingle :: Tsingle :: nil, Tsingle)
  | Osubfs => (Tsingle :: Tsingle :: nil, Tsingle)
  | Omulfs => (Tsingle :: Tsingle :: nil, Tsingle)
  | Odivfs => (Tsingle :: Tsingle :: nil, Tsingle)
  | Osingleoffloat => (Tfloat :: nil, Tsingle)
  | Ofloatofsingle => (Tsingle :: nil, Tfloat)

  | Ointoffloat => (Tfloat :: nil, Tint)
  | Ointuoffloat => (Tfloat :: nil, Tint)
  | Ofloatofint => (Tint :: nil, Tfloat)
  | Ofloatofintu => (Tint :: nil, Tfloat)
  | Ointofsingle => (Tsingle :: nil, Tint)
  | Ointuofsingle => (Tsingle :: nil, Tint)
  | Osingleofint => (Tint :: nil, Tsingle)
  | Osingleofintu => (Tint :: nil, Tsingle)
  | Olongoffloat => (Tfloat :: nil, Tlong)
  | Olonguoffloat => (Tfloat :: nil, Tlong)
  | Ofloatoflong => (Tlong :: nil, Tfloat)
  | Ofloatoflongu => (Tlong :: nil, Tfloat)
  | Olongofsingle => (Tsingle :: nil, Tlong)
  | Olonguofsingle => (Tsingle :: nil, Tlong)
  | Osingleoflong => (Tlong :: nil, Tsingle)
  | Osingleoflongu => (Tlong :: nil, Tsingle)

  | Ocmp c => (type_of_condition c, Tint)
  | Osel c ty => (ty :: ty :: type_of_condition c, ty)
  end.

Definition type_of_addressing (addr: addressing) : list typ :=
  match addr with
  | Aindexed _ => Tptr :: nil
  | Aindexed2 => Tptr :: Tlong :: nil
  | Aindexed2shift _ => Tptr :: Tlong :: nil
  | Aindexed2ext _ _ => Tptr :: Tint :: nil
  | Aglobal _ _ => nil
  | Ainstack _ => nil
  end.

(** Weak type soundness results for [eval_operation]:
  the result values, when defined, are always of the type predicted
  by [type_of_operation]. *)

Section SOUNDNESS.

Variable A V: Type.
Variable genv: Genv.t A V.

Remark type_add:
  forall v1 v2, Val.has_type (Val.add v1 v2) Tint.
Proof.
  intros. unfold Val.has_type, Val.add. destruct v1, v2; simpl; auto.
Qed.

Remark type_sub:
  forall v1 v2, Val.has_type (Val.sub v1 v2) Tint.
Proof.
  intros. unfold Val.has_type, Val.add. destruct v1, v2; simpl; auto.
Qed.

Remark type_addl:
  forall v1 v2, Val.has_type (Val.addl v1 v2) Tlong.
Proof.
  intros. unfold Val.has_type, Val.addl. destruct v1, v2; simpl; auto.
Qed.

Remark type_subl:
  forall v1 v2, Val.has_type (Val.subl v1 v2) Tlong.
Proof.
  intros. unfold Val.has_type, Val.addl. destruct v1, v2; simpl; auto.
  destruct (eq_block b b0); auto.
Qed.

Lemma type_of_operation_sound:
  forall op vl sp v m,
  op <> Omove ->
  eval_operation genv sp op vl m = Some v ->
  Val.has_type v (snd (type_of_operation op)).
Proof with (try exact I; try reflexivity; auto using Val.Vptr_has_type).
  intros.
  destruct op; simpl; simpl in H0; FuncInv; subst; simpl.
  (* move *)
  - congruence.
  (* intconst, longconst, floatconst, singleconst *)
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  (* addrsymbol *)
  - unfold Genv.symbol_address. destruct (Genv.find_symbol genv id)...
  (* addrstack *)
  - destruct sp...
  (* 32-bit integer operations *)
  - destruct s, v0; try exact I; simpl; rewrite a32_range...
  - apply type_add.
  - apply type_add.
  - apply type_add.
  - destruct v0...
  - destruct (eval_shift s v0 a)...
  - apply type_sub.
  - apply type_sub.
  - destruct v0... destruct v1...
  - apply type_add.
  - apply type_sub.
  - destruct v0; destruct v1; simpl in *; inv H0.
    destruct (Int.eq i0 Int.zero || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H2...
  - destruct v0; destruct v1; simpl in *; inv H0.
    destruct (Int.eq i0 Int.zero); inv H2...
  - destruct v0... destruct v1...
  - destruct v0... destruct (eval_shift s v1 a)...
  - destruct v0...
  - destruct v0... destruct v1...
  - destruct v0... destruct (eval_shift s v1 a)...
  - destruct v0...
  - destruct v0... destruct v1...
  - destruct v0... destruct (eval_shift s v1 a)...
  - destruct v0...
  - destruct v0...
  - destruct (eval_shift s v0 a)...
  - destruct v0... destruct v1...
  - destruct v0... destruct (eval_shift s v1 a)...
  - destruct v0... destruct v1...
  - destruct v0... destruct (eval_shift s v1 a)...
  - destruct v0... destruct v1...
  - destruct v0... destruct (eval_shift s v1 a)...
  - destruct v0; destruct v1; simpl... destruct (Int.ltu i0 Int.iwordsize)...
  - destruct v0; destruct v1; simpl... destruct (Int.ltu i0 Int.iwordsize)...
  - destruct v0; destruct v1; simpl... destruct (Int.ltu i0 Int.iwordsize)...
  - destruct v0; simpl in H0; try discriminate. destruct (Int.ltu n (Int.repr 31)); inv H0...
  - destruct v0...
  - destruct v0...
  - destruct (Val.zero_ext s v0)... simpl; rewrite a32_range... 
  - destruct (Val.sign_ext s v0)... simpl; rewrite a32_range...
  - destruct (Val.shru v0 (Vint a))... 
  - destruct (Val.shr v0 (Vint a))...
  (* 64-bit integer operations *)
  - destruct s, v0; try exact I; simpl; rewrite a64_range...
  - unfold eval_extend. destruct (match x with
     | Xsgn32 => Val.longofint v0
     | Xuns32 => Val.longofintu v0
     end)...
    simpl; rewrite a64_range...
  - destruct v0... destruct v1...
  - destruct v0...
  - destruct v0...
  - apply type_addl.
  - apply type_addl.
  - apply type_addl.
  - apply type_addl.
  - destruct v0...
  - destruct (eval_shiftl s v0 a)...
  - apply type_subl.
  - apply type_subl.
  - apply type_subl.
  - destruct v0... destruct v1...
  - apply type_addl.
  - apply type_subl.
  - destruct v0... destruct v1...
  - destruct v0... destruct v1...
  - destruct v0; destruct v1; simpl in *; inv H0.
    destruct (Int64.eq i0 Int64.zero || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H2...
  - destruct v0; destruct v1; simpl in *; inv H0.
    destruct (Int64.eq i0 Int64.zero); inv H2...
  - destruct v0... destruct v1...
  - destruct v0... destruct (eval_shiftl s v1 a)...
  - destruct v0...
  - destruct v0... destruct v1...
  - destruct v0... destruct (eval_shiftl s v1 a)...
  - destruct v0...
  - destruct v0... destruct v1...
  - destruct v0... destruct (eval_shiftl s v1 a)...
  - destruct v0...
  - destruct v0...
  - destruct (eval_shiftl s v0 a)...
  - destruct v0... destruct v1...
  - destruct v0... destruct (eval_shiftl s v1 a)...
  - destruct v0... destruct v1...
  - destruct v0... destruct (eval_shiftl s v1 a)...
  - destruct v0... destruct v1...
  - destruct v0... destruct (eval_shiftl s v1 a)...
  - destruct v0; destruct v1; simpl... destruct (Int.ltu i0 Int64.iwordsize')...
  - destruct v0; destruct v1; simpl... destruct (Int.ltu i0 Int64.iwordsize')...
  - destruct v0; destruct v1; simpl... destruct (Int.ltu i0 Int64.iwordsize')...
  - destruct v0; simpl in H0; try discriminate. destruct (Int.ltu n (Int.repr 63)); inv H0...
  - destruct v0...
  - destruct v0...
  - destruct (Val.zero_ext_l s v0)... simpl; rewrite a64_range... 
  - destruct (Val.sign_ext_l s v0)... simpl; rewrite a64_range...
  - destruct (Val.shrlu v0 (Vint a))... 
  - destruct (Val.shrl v0 (Vint a))...

  (* 64-bit FP *)
  - destruct v0...
  - destruct v0...
  - destruct v0; destruct v1...
  - destruct v0; destruct v1...
  - destruct v0; destruct v1...
  - destruct v0; destruct v1...
  (* 32-bit FP *)
  - destruct v0...
  - destruct v0...
  - destruct v0; destruct v1...
  - destruct v0; destruct v1...
  - destruct v0; destruct v1...
  - destruct v0; destruct v1...
  (* singleoffloat, floatofsingle *)
  - destruct v0...
  - destruct v0...
  (* intoffloat, intuoffloat *)
  - destruct v0; simpl in H0; inv H0. destruct (Float.to_int f); inv H2...
  - destruct v0; simpl in H0; inv H0. destruct (Float.to_intu f); inv H2...
  (* floatofint, floatofintu *)
  - destruct v0; simpl in H0; inv H0...
  - destruct v0; simpl in H0; inv H0...
  (* intofsingle, intuofsingle *)
  - destruct v0; simpl in H0; inv H0. destruct (Float32.to_int f); inv H2...
  - destruct v0; simpl in H0; inv H0. destruct (Float32.to_intu f); inv H2...
  (* singleofint, singleofintu *)
  - destruct v0; simpl in H0; inv H0...
  - destruct v0; simpl in H0; inv H0...
  (* longoffloat, longuoffloat *)
  - destruct v0; simpl in H0; inv H0. destruct (Float.to_long f); inv H2...
  - destruct v0; simpl in H0; inv H0. destruct (Float.to_longu f); inv H2...
  (* floatoflong, floatoflongu *)
  - destruct v0; simpl in H0; inv H0...
  - destruct v0; simpl in H0; inv H0...
  (* longofsingle, longuofsingle *)
  - destruct v0; simpl in H0; inv H0. destruct (Float32.to_long f); inv H2...
  - destruct v0; simpl in H0; inv H0. destruct (Float32.to_longu f); inv H2...
  (* singleoflong, singleoflongu *)
  - destruct v0; simpl in H0; inv H0...
  - destruct v0; simpl in H0; inv H0...
  (* cmp *)
  - destruct (eval_condition cond vl m) as [[]|]...
  - unfold Val.select. destruct (eval_condition cond vl m). apply Val.normalize_type. exact I.
Qed.

End SOUNDNESS.

(** * Manipulating and transforming operations *)

(** Constructing shift amounts *)

Section SHIFT_AMOUNT.

Variable l: Z.
Hypothesis l_range: 0 <= l < 32.
Variable N: int.
Hypothesis N_eq: Int.unsigned N = two_p l.

Remark mk_amount_range:
  forall n, Int.ltu (Int.zero_ext l n) N = true.
Proof.
  intros; unfold Int.ltu. apply zlt_true. rewrite N_eq. apply (Int.zero_ext_range l n). assumption.
Qed.

Remark mk_amount_eq:
  forall n, Int.ltu n N = true -> Int.zero_ext l n = n.
Proof.
  intros.
  transitivity (Int.repr (Int.unsigned (Int.zero_ext l n))).
  symmetry; apply Int.repr_unsigned.
  transitivity (Int.repr (Int.unsigned n)).
  f_equal. rewrite Int.zero_ext_mod. apply Int.ltu_inv in H. rewrite N_eq in H. 
  apply Z.mod_small. assumption. assumption.
  apply Int.repr_unsigned.
Qed.

End SHIFT_AMOUNT.

Program Definition mk_amount32 (n: int): amount32 :=
  {| a32_amount := Int.zero_ext 5 n |}.
Next Obligation.
  apply mk_amount_range. omega. reflexivity.
Qed.

Lemma mk_amount32_eq: forall n,
  Int.ltu n Int.iwordsize = true -> a32_amount (mk_amount32 n) = n.
Proof.
  intros. eapply mk_amount_eq; eauto. omega. reflexivity.
Qed.

Program Definition mk_amount64 (n: int): amount64 :=
  {| a64_amount := Int.zero_ext 6 n |}.
Next Obligation.
  apply mk_amount_range. omega. reflexivity.
Qed.

Lemma mk_amount64_eq: forall n,
  Int.ltu n Int64.iwordsize' = true -> a64_amount (mk_amount64 n) = n.
Proof.
  intros. eapply mk_amount_eq; eauto. omega. reflexivity.
Qed.
 
(** Recognition of move operations. *)

Definition is_move_operation
    (A: Type) (op: operation) (args: list A) : option A :=
  match op, args with
  | Omove, arg :: nil => Some arg
  | _, _ => None
  end.

Lemma is_move_operation_correct:
  forall (A: Type) (op: operation) (args: list A) (a: A),
  is_move_operation op args = Some a ->
  op = Omove /\ args = a :: nil.
Proof.
  intros until a. unfold is_move_operation; destruct op;
  try (intros; discriminate).
  destruct args. intros; discriminate.
  destruct args. intros. intuition congruence.
  intros; discriminate.
Qed.

(** [negate_condition cond] returns a condition that is logically
  equivalent to the negation of [cond]. *)

Definition negate_condition (cond: condition): condition :=
  match cond with
  | Ccomp c => Ccomp (negate_comparison c)
  | Ccompu c => Ccompu (negate_comparison c)
  | Ccompimm c n => Ccompimm (negate_comparison c) n
  | Ccompuimm c n => Ccompuimm (negate_comparison c) n
  | Ccompshift c s a => Ccompshift (negate_comparison c) s a
  | Ccompushift c s a => Ccompushift (negate_comparison c) s a
  | Cmaskzero n => Cmasknotzero n
  | Cmasknotzero n => Cmaskzero n
  | Ccompl c => Ccompl (negate_comparison c)
  | Ccomplu c => Ccomplu (negate_comparison c)
  | Ccomplimm c n => Ccomplimm (negate_comparison c) n
  | Ccompluimm c n => Ccompluimm (negate_comparison c) n
  | Ccomplshift c s a => Ccomplshift (negate_comparison c) s a
  | Ccomplushift c s a => Ccomplushift (negate_comparison c) s a
  | Cmasklzero n => Cmasklnotzero n
  | Cmasklnotzero n => Cmasklzero n
  | Ccompf c => Cnotcompf c
  | Cnotcompf c => Ccompf c
  | Ccompfzero c => Cnotcompfzero c
  | Cnotcompfzero c => Ccompfzero c
  | Ccompfs c => Cnotcompfs c
  | Cnotcompfs c => Ccompfs c
  | Ccompfszero c => Cnotcompfszero c
  | Cnotcompfszero c => Ccompfszero c
  end.

Lemma eval_negate_condition:
  forall cond vl m,
  eval_condition (negate_condition cond) vl m = option_map negb (eval_condition cond vl m).
Proof.
  intros. destruct cond; simpl.
  repeat (destruct vl; auto). apply Val.negate_cmp_bool.
  repeat (destruct vl; auto). apply Val.negate_cmpu_bool.
  repeat (destruct vl; auto). apply Val.negate_cmp_bool.
  repeat (destruct vl; auto). apply Val.negate_cmpu_bool.
  repeat (destruct vl; auto). apply Val.negate_cmp_bool.
  repeat (destruct vl; auto). apply Val.negate_cmpu_bool.
  repeat (destruct vl; auto). apply (Val.negate_cmp_bool Ceq).
  repeat (destruct vl; auto). apply (Val.negate_cmp_bool Cne).
  repeat (destruct vl; auto). apply Val.negate_cmpl_bool.
  repeat (destruct vl; auto). apply Val.negate_cmplu_bool.
  repeat (destruct vl; auto). apply Val.negate_cmpl_bool.
  repeat (destruct vl; auto). apply Val.negate_cmplu_bool.
  repeat (destruct vl; auto). apply Val.negate_cmpl_bool.
  repeat (destruct vl; auto). apply Val.negate_cmplu_bool.
  repeat (destruct vl; auto). apply (Val.negate_cmpl_bool Ceq).
  repeat (destruct vl; auto). apply (Val.negate_cmpl_bool Cne).
  repeat (destruct vl; auto).
  repeat (destruct vl; auto). destruct (Val.cmpf_bool c v v0) as [[]|]; auto.
  repeat (destruct vl; auto).
  repeat (destruct vl; auto). destruct (Val.cmpf_bool c v (Vfloat Float.zero)) as [[]|]; auto.
  repeat (destruct vl; auto).
  repeat (destruct vl; auto). destruct (Val.cmpfs_bool c v v0) as [[]|]; auto.
  repeat (destruct vl; auto).
  repeat (destruct vl; auto). destruct (Val.cmpfs_bool c v (Vsingle Float32.zero)) as [[]|]; auto.
Qed.

(** Shifting stack-relative references.  This is used in [Stacking]. *)

Definition shift_stack_addressing (delta: Z) (addr: addressing) :=
  match addr with
  | Ainstack ofs => Ainstack (Ptrofs.add ofs (Ptrofs.repr delta))
  | _ => addr
  end.

Definition shift_stack_operation (delta: Z) (op: operation) :=
  match op with
  | Oaddrstack ofs => Oaddrstack (Ptrofs.add ofs (Ptrofs.repr delta))
  | _ => op
  end.

Lemma type_shift_stack_addressing:
  forall delta addr, type_of_addressing (shift_stack_addressing delta addr) = type_of_addressing addr.
Proof.
  intros. destruct addr; auto.
Qed.

Lemma type_shift_stack_operation:
  forall delta op, type_of_operation (shift_stack_operation delta op) = type_of_operation op.
Proof.
  intros. destruct op; auto.
Qed.

Lemma eval_shift_stack_addressing:
  forall F V (ge: Genv.t F V) sp addr vl delta,
  eval_addressing ge (Vptr sp Ptrofs.zero) (shift_stack_addressing delta addr) vl =
  eval_addressing ge (Vptr sp (Ptrofs.repr delta)) addr vl.
Proof.
  intros. destruct addr; simpl; auto. destruct vl; auto.
  rewrite Ptrofs.add_zero_l, Ptrofs.add_commut; auto.
Qed.

Lemma eval_shift_stack_operation:
  forall F V (ge: Genv.t F V) sp op vl m delta,
  eval_operation ge (Vptr sp Ptrofs.zero) (shift_stack_operation delta op) vl m =
  eval_operation ge (Vptr sp (Ptrofs.repr delta)) op vl m.
Proof.
  intros. destruct op; simpl; auto. destruct vl; auto.
  rewrite Ptrofs.add_zero_l, Ptrofs.add_commut; auto.
Qed.

(** Offset an addressing mode [addr] by a quantity [delta], so that
  it designates the pointer [delta] bytes past the pointer designated
  by [addr].  May be undefined, in which case [None] is returned. *)

Definition offset_addressing (addr: addressing) (delta: Z) : option addressing :=
  match addr with
  | Aindexed n => Some(Aindexed (Int64.add n (Int64.repr delta)))
  | Aindexed2 => None
  | Aindexed2shift _ => None
  | Aindexed2ext _ _ => None
  | Aglobal id n => Some(Aglobal id (Ptrofs.add n (Ptrofs.repr delta)))
  | Ainstack n => Some(Ainstack (Ptrofs.add n (Ptrofs.repr delta)))
  end.

Lemma eval_offset_addressing:
  forall (F V: Type) (ge: Genv.t F V) sp addr args delta addr' v,
  offset_addressing addr delta = Some addr' ->
  eval_addressing ge sp addr args = Some v ->
  Archi.ptr64 = false ->
  eval_addressing ge sp addr' args = Some(Val.add v (Vint (Int.repr delta))).
Proof.
  intros. discriminate. 
Qed.

(** Operations that are so cheap to recompute that CSE should not factor them out. *)

Definition is_trivial_op (op: operation) : bool :=
  match op with
  | Omove => true
  | Ointconst n => Int.eq (Int.sign_ext 16 n) n
  | Olongconst n => Int64.eq (Int64.sign_ext 16 n) n
  | Oaddrstack _ => true
  | _ => false
  end.

(** Operations that depend on the memory state. *)

Definition cond_depends_on_memory (c: condition) : bool :=
  match c with
  | Ccomplu _ | Ccompluimm _ _ | Ccomplushift _ _ _ => true
  | _ => false
  end.

Lemma cond_depends_on_memory_correct:
  forall c args m1 m2,
  cond_depends_on_memory c = false ->
  eval_condition c args m1 = eval_condition c args m2.
Proof.
  intros; destruct c; simpl; discriminate || reflexivity.
Qed.

Definition op_depends_on_memory (op: operation) : bool :=
  match op with
  | Ocmp c => cond_depends_on_memory c
  | Osel c yu => cond_depends_on_memory c
  | _ => false
  end.

Lemma op_depends_on_memory_correct:
  forall (F V: Type) (ge: Genv.t F V) sp op args m1 m2,
  op_depends_on_memory op = false ->
  eval_operation ge sp op args m1 = eval_operation ge sp op args m2.
Proof.
  intros. destruct op; auto.
  simpl. rewrite (cond_depends_on_memory_correct cond args m1 m2 H). auto.
  simpl. destruct args; auto. destruct args; auto.
  rewrite (cond_depends_on_memory_correct cond args m1 m2 H). auto.
Qed.

(** Global variables mentioned in an operation or addressing mode *)

Definition globals_addressing (addr: addressing) : list ident :=
  match addr with
  | Aglobal s ofs => s :: nil
  | _ => nil
  end.

Definition globals_operation (op: operation) : list ident :=
  match op with
  | Oaddrsymbol s ofs => s :: nil
  | _ => nil
  end.

(** * Invariance and compatibility properties. *)

(** [eval_operation] and [eval_addressing] depend on a global environment
  for resolving references to global symbols.  We show that they give
  the same results if a global environment is replaced by another that
  assigns the same addresses to the same symbols. *)

Section GENV_TRANSF.

Variable F1 F2 V1 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.
Hypothesis agree_on_symbols:
  forall (s: ident), Genv.find_symbol ge2 s = Genv.find_symbol ge1 s.

Lemma eval_addressing_preserved:
  forall sp addr vl,
  eval_addressing ge2 sp addr vl = eval_addressing ge1 sp addr vl.
Proof.
  intros.
  unfold eval_addressing; destruct addr; auto. destruct vl; auto. 
  unfold Genv.symbol_address. rewrite agree_on_symbols; auto.
Qed.

Lemma eval_operation_preserved:
  forall sp op vl m,
  eval_operation ge2 sp op vl m = eval_operation ge1 sp op vl m.
Proof.
  intros.
  unfold eval_operation; destruct op; auto. destruct vl; auto.
  unfold Genv.symbol_address. rewrite agree_on_symbols; auto.
Qed.

End GENV_TRANSF.

(** Compatibility of the evaluation functions with value injections. *)

Section EVAL_COMPAT.

Variable F1 F2 V1 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.
Variable f: meminj.

Variable m1: mem.
Variable m2: mem.

Hypothesis valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  Mem.valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

Hypothesis weak_valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

Hypothesis weak_valid_pointer_no_overflow:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.

Hypothesis valid_different_pointers_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m1 b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).

Ltac InvInject :=
  match goal with
  | [ H: Val.inject _ (Vint _) _ |- _ ] =>
      inv H; InvInject
  | [ H: Val.inject _ (Vfloat _) _ |- _ ] =>
      inv H; InvInject
  | [ H: Val.inject _ (Vptr _ _) _ |- _ ] =>
      inv H; InvInject
  | [ H: Val.inject_list _ nil _ |- _ ] =>
      inv H; InvInject
  | [ H: Val.inject_list _ (_ :: _) _ |- _ ] =>
      inv H; InvInject
  | _ => idtac
  end.

Lemma eval_shift_inject:
  forall v1 v2 s a,
  Val.inject f v1 v2 -> Val.inject f (eval_shift s v1 a) (eval_shift s v2 a).
Proof.
  intros; inv H; destruct s; simpl; auto; rewrite a32_range; auto.
Qed.

Lemma eval_shiftl_inject:
  forall v1 v2 s a,
  Val.inject f v1 v2 -> Val.inject f (eval_shiftl s v1 a) (eval_shiftl s v2 a).
Proof.
  intros; inv H; destruct s; simpl; auto; rewrite a64_range; auto.
Qed.

Lemma eval_extend_inject:
  forall v1 v2 x a,
  Val.inject f v1 v2 -> Val.inject f (eval_extend x v1 a) (eval_extend x v2 a).
Proof.
  unfold eval_extend; intros; inv H; destruct x; simpl; auto; rewrite a64_range; auto.
Qed.

Lemma eval_condition_inj:
  forall cond vl1 vl2 b,
  Val.inject_list f vl1 vl2 ->
  eval_condition cond vl1 m1 = Some b ->
  eval_condition cond vl2 m2 = Some b.
Proof.
  intros. destruct cond; simpl in H0; FuncInv; InvInject; simpl; auto.
(* 32-bit integers *)
- inv H3; inv H2; simpl in H0; inv H0; auto.
- eauto 3 using Val.cmpu_bool_inject, Mem.valid_pointer_implies.
- inv H3; simpl in H0; inv H0; auto.
- eauto 3 using Val.cmpu_bool_inject, Mem.valid_pointer_implies.
- revert H0. generalize (eval_shift_inject s a H2); intros J; inv H3; inv J; simpl; congruence.
- eauto 3 using Val.cmpu_bool_inject, Mem.valid_pointer_implies, eval_shift_inject.
- inv H3; inv H0; auto.
- inv H3; inv H0; auto.
(* 64-bit integers *)
- inv H3; inv H2; simpl in H0; inv H0; auto.
- eauto 3 using Val.cmplu_bool_inject, Mem.valid_pointer_implies.
- inv H3; simpl in H0; inv H0; auto.
- eauto 3 using Val.cmplu_bool_inject, Mem.valid_pointer_implies.
- revert H0. generalize (eval_shiftl_inject s a H2); intros J; inv H3; inv J; simpl; congruence.
- eauto 3 using Val.cmplu_bool_inject, Mem.valid_pointer_implies, eval_shiftl_inject.
- inv H3; inv H0; auto.
- inv H3; inv H0; auto.
(* 64-bit floats *)
- inv H3; inv H2; simpl in H0; inv H0; auto.
- inv H3; inv H2; simpl in H0; inv H0; auto.
- inv H3; simpl in H0; inv H0; auto.
- inv H3; simpl in H0; inv H0; auto.
(* 32-bit floats *)
- inv H3; inv H2; simpl in H0; inv H0; auto.
- inv H3; inv H2; simpl in H0; inv H0; auto.
- inv H3; simpl in H0; inv H0; auto.
- inv H3; simpl in H0; inv H0; auto.
Qed.

Ltac TrivialExists :=
  match goal with
  | [ |- exists v2, Some ?v1 = Some v2 /\ Val.inject _ _ v2 ] =>
      exists v1; split; auto
  | _ => idtac
  end.

Lemma eval_operation_inj:
  forall op sp1 vl1 sp2 vl2 v1,
  (forall id ofs,
      In id (globals_operation op) ->
      Val.inject f (Genv.symbol_address ge1 id ofs) (Genv.symbol_address ge2 id ofs)) ->
  Val.inject f sp1 sp2 ->
  Val.inject_list f vl1 vl2 ->
  eval_operation ge1 sp1 op vl1 m1 = Some v1 ->
  exists v2, eval_operation ge2 sp2 op vl2 m2 = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros until v1; intros GL; intros. destruct op; simpl in H1; simpl; FuncInv; InvInject; TrivialExists.
  (* addrsymbol *)
  - apply GL; simpl; auto.
  (* addrstack *)
  - apply Val.offset_ptr_inject; auto. 
  (* shift *)
  - apply eval_shift_inject; auto.
  (* add *)
  - apply Val.add_inject; auto.
  - apply Val.add_inject; auto using eval_shift_inject.
  - apply Val.add_inject; auto.
  (* neg, sub *)
  - inv H4; simpl; auto.
  - generalize (eval_shift_inject s a H4); intros J; inv J; simpl; auto.
  - apply Val.sub_inject; auto.
  - apply Val.sub_inject; auto using eval_shift_inject.
  (* mul, muladd, mulsub *)
  - inv H4; inv H2; simpl; auto.
  - apply Val.add_inject; auto. inv H2; inv H3; simpl; auto.
  - apply Val.sub_inject; auto. inv H2; inv H3; simpl; auto.
  (* div, divu *)
  - inv H4; inv H3; simpl in H1; inv H1. simpl.
    destruct (Int.eq i0 Int.zero
              || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H2.
    TrivialExists.
  - inv H4; inv H3; simpl in H1; inv H1. simpl.
    destruct (Int.eq i0 Int.zero); inv H2. TrivialExists.
  (* and*)
  - inv H4; inv H2; simpl; auto. 
  - generalize (eval_shift_inject s a H2); intros J; inv H4; inv J; simpl; auto.
  - inv H4; simpl; auto.
  (* or *)
  - inv H4; inv H2; simpl; auto. 
  - generalize (eval_shift_inject s a H2); intros J; inv H4; inv J; simpl; auto.
  - inv H4; simpl; auto.
  (* xor *)
  - inv H4; inv H2; simpl; auto. 
  - generalize (eval_shift_inject s a H2); intros J; inv H4; inv J; simpl; auto.
  - inv H4; simpl; auto.
  (* not *)
  - inv H4; simpl; auto.
  - generalize (eval_shift_inject s a H4); intros J; inv J; simpl; auto.
  (* bic *)
  - inv H4; inv H2; simpl; auto. 
  - generalize (eval_shift_inject s a H2); intros J; inv H4; inv J; simpl; auto.
  (* nor *)
  - inv H4; inv H2; simpl; auto. 
  - generalize (eval_shift_inject s a H2); intros J; inv H4; inv J; simpl; auto.
  (* eqv *)
  - inv H4; inv H2; simpl; auto. 
  - generalize (eval_shift_inject s a H2); intros J; inv H4; inv J; simpl; auto.
  (* shl *)
  - inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int.iwordsize); auto.
  (* shr *)
  - inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int.iwordsize); auto.
  (* shru *)
  - inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int.iwordsize); auto.
  (* shrx *)
  - inv H4; simpl in H1; try discriminate. simpl.
    destruct (Int.ltu n (Int.repr 31)); inv H1. TrivialExists.
  (* shift-ext *)
  - inv H4; simpl; auto.
  - inv H4; simpl; auto.
  - inv H4; simpl; auto; rewrite a32_range; auto.
  - inv H4; simpl; auto; rewrite a32_range; auto.
  - inv H4; simpl; auto; rewrite a32_range; simpl; auto.
  - inv H4; simpl; auto; rewrite a32_range; simpl; auto.

  (* shiftl *)
  - apply eval_shiftl_inject; auto.
  (* extend *)
  - apply eval_extend_inject; auto.
  (* makelong, low, high *)
  - inv H4; inv H2; simpl; auto.
  - inv H4; simpl; auto.
  - inv H4; simpl; auto.
  (* addl *)
  - apply Val.addl_inject; auto.
  - apply Val.addl_inject; auto using eval_shiftl_inject.
  - apply Val.addl_inject; auto using eval_extend_inject.
  - apply Val.addl_inject; auto.
  (* negl, subl *)
  - inv H4; simpl; auto.
  - generalize (eval_shiftl_inject s a H4); intros J; inv J; simpl; auto.
  - apply Val.subl_inject; auto.
  - apply Val.subl_inject; auto using eval_shiftl_inject.
  - apply Val.subl_inject; auto using eval_extend_inject.
  (* mull, mulladd, mullsub, mullhs, mullhu *)
  - inv H4; inv H2; simpl; auto.
  - apply Val.addl_inject; auto. inv H2; inv H3; simpl; auto.
  - apply Val.subl_inject; auto. inv H2; inv H3; simpl; auto.
  - inv H4; inv H2; simpl; auto.
  - inv H4; inv H2; simpl; auto.
  (* divl, divlu *)
  - inv H4; inv H3; simpl in H1; inv H1. simpl.
    destruct (Int64.eq i0 Int64.zero
              || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H2.
    TrivialExists.
  - inv H4; inv H3; simpl in H1; inv H1. simpl.
    destruct (Int64.eq i0 Int64.zero); inv H2. TrivialExists.
  (* andl *)
  - inv H4; inv H2; simpl; auto. 
  - generalize (eval_shiftl_inject s a H2); intros J; inv H4; inv J; simpl; auto.
  - inv H4; simpl; auto.
  (* orl *)
  - inv H4; inv H2; simpl; auto. 
  - generalize (eval_shiftl_inject s a H2); intros J; inv H4; inv J; simpl; auto.
  - inv H4; simpl; auto.
  (* xorl *)
  - inv H4; inv H2; simpl; auto. 
  - generalize (eval_shiftl_inject s a H2); intros J; inv H4; inv J; simpl; auto.
  - inv H4; simpl; auto.
  (* notl *)
  - inv H4; simpl; auto.
  - generalize (eval_shiftl_inject s a H4); intros J; inv J; simpl; auto.
  (* bicl *)
  - inv H4; inv H2; simpl; auto. 
  - generalize (eval_shiftl_inject s a H2); intros J; inv H4; inv J; simpl; auto.
  (* norl *)
  - inv H4; inv H2; simpl; auto. 
  - generalize (eval_shiftl_inject s a H2); intros J; inv H4; inv J; simpl; auto.
  (* eqvl *)
  - inv H4; inv H2; simpl; auto. 
  - generalize (eval_shiftl_inject s a H2); intros J; inv H4; inv J; simpl; auto.
  (* shll *)
  - inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int64.iwordsize'); auto.
  (* shrl *)
  - inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int64.iwordsize'); auto.
  (* shrlu *)
  - inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int64.iwordsize'); auto.
  (* shrlx *)
  - inv H4; simpl in H1; try discriminate. simpl.
    destruct (Int.ltu n (Int.repr 63)); inv H1. TrivialExists.
  (* shift-ext *)
  - inv H4; simpl; auto.
  - inv H4; simpl; auto.
  - inv H4; simpl; auto; rewrite a64_range; auto.
  - inv H4; simpl; auto; rewrite a64_range; auto.
  - inv H4; simpl; auto; rewrite a64_range; simpl; auto.
  - inv H4; simpl; auto; rewrite a64_range; simpl; auto.

  (* negf, absf *)
  - inv H4; simpl; auto.
  - inv H4; simpl; auto.
  (* addf, subf *)
  - inv H4; inv H2; simpl; auto.
  - inv H4; inv H2; simpl; auto.
  (* mulf, divf *)
  - inv H4; inv H2; simpl; auto.
  - inv H4; inv H2; simpl; auto.
  (* negfs, absfs *)
  - inv H4; simpl; auto.
  - inv H4; simpl; auto.
  (* addfs, subfs *)
  - inv H4; inv H2; simpl; auto.
  - inv H4; inv H2; simpl; auto.
  (* mulfs, divfs *)
  - inv H4; inv H2; simpl; auto.
  - inv H4; inv H2; simpl; auto.
  (* singleoffloat, floatofsingle *)
  - inv H4; simpl; auto.
  - inv H4; simpl; auto.
  (* intoffloat, intuoffloat *)
  - inv H4; simpl in H1; inv H1. simpl. destruct (Float.to_int f0); simpl in H2; inv H2.
    exists (Vint i); auto.
  - inv H4; simpl in H1; inv H1. simpl. destruct (Float.to_intu f0); simpl in H2; inv H2.
    exists (Vint i); auto.
  (* floatofint, floatofintu *)
  - inv H4; simpl in H1; inv H1. simpl. TrivialExists.
  - inv H4; simpl in H1; inv H1. simpl. TrivialExists.
  (* intofsingle, intuofsingle *)
  - inv H4; simpl in H1; inv H1. simpl. destruct (Float32.to_int f0); simpl in H2; inv H2.
    exists (Vint i); auto.
  - inv H4; simpl in H1; inv H1. simpl. destruct (Float32.to_intu f0); simpl in H2; inv H2.
    exists (Vint i); auto.
  (* singleofint, singleofintu *)
  - inv H4; simpl in H1; inv H1. simpl. TrivialExists.
  - inv H4; simpl in H1; inv H1. simpl. TrivialExists.
  (* longoffloat, longuoffloat *)
  - inv H4; simpl in H1; inv H1. simpl. destruct (Float.to_long f0); simpl in H2; inv H2.
    exists (Vlong i); auto.
  - inv H4; simpl in H1; inv H1. simpl. destruct (Float.to_longu f0); simpl in H2; inv H2.
    exists (Vlong i); auto.
  (* floatoflong, floatoflongu *)
  - inv H4; simpl in H1; inv H1. simpl. TrivialExists.
  - inv H4; simpl in H1; inv H1. simpl. TrivialExists.
  (* longofsingle, longuofsingle *)
  - inv H4; simpl in H1; inv H1. simpl. destruct (Float32.to_long f0); simpl in H2; inv H2.
    exists (Vlong i); auto.
  - inv H4; simpl in H1; inv H1. simpl. destruct (Float32.to_longu f0); simpl in H2; inv H2.
    exists (Vlong i); auto.
  (* singleoflong, singleoflongu *)
  - inv H4; simpl in H1; inv H1. simpl. TrivialExists.
  - inv H4; simpl in H1; inv H1. simpl. TrivialExists.
  (* cmp, sel *)
  - subst v1. destruct (eval_condition cond vl1 m1) eqn:?.
    exploit eval_condition_inj; eauto. intros EQ; rewrite EQ.
    destruct b; simpl; constructor.
    simpl; constructor.
  - apply Val.select_inject; auto.  
    destruct (eval_condition cond vl1 m1) eqn:?; auto.
    right; symmetry; eapply eval_condition_inj; eauto.
Qed.

Lemma eval_addressing_inj:
  forall addr sp1 vl1 sp2 vl2 v1,
  (forall id ofs,
      In id (globals_addressing addr) ->
      Val.inject f (Genv.symbol_address ge1 id ofs) (Genv.symbol_address ge2 id ofs)) ->
  Val.inject f sp1 sp2 ->
  Val.inject_list f vl1 vl2 ->
  eval_addressing ge1 sp1 addr vl1 = Some v1 ->
  exists v2, eval_addressing ge2 sp2 addr vl2 = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros. destruct addr; simpl in H2; simpl; FuncInv; InvInject; TrivialExists.
- apply Val.addl_inject; auto.
- apply Val.addl_inject; auto.
- apply Val.addl_inject; auto. inv H3; simpl; auto; rewrite a64_range; auto.
- apply Val.addl_inject; auto using eval_extend_inject.
- apply H; simpl; auto.
- apply Val.offset_ptr_inject; auto. 
Qed.

End EVAL_COMPAT.

(** Compatibility of the evaluation functions with the ``is less defined'' relation over values. *)

Section EVAL_LESSDEF.

Variable F V: Type.
Variable genv: Genv.t F V.

Remark valid_pointer_extends:
  forall m1 m2, Mem.extends m1 m2 ->
  forall b1 ofs b2 delta,
  Some(b1, 0) = Some(b2, delta) ->
  Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  Mem.valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  intros. inv H0. rewrite Ptrofs.add_zero. eapply Mem.valid_pointer_extends; eauto.
Qed.

Remark weak_valid_pointer_extends:
  forall m1 m2, Mem.extends m1 m2 ->
  forall b1 ofs b2 delta,
  Some(b1, 0) = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  intros. inv H0. rewrite Ptrofs.add_zero. eapply Mem.weak_valid_pointer_extends; eauto.
Qed.

Remark weak_valid_pointer_no_overflow_extends:
  forall m1 b1 ofs b2 delta,
  Some(b1, 0) = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  intros. inv H. rewrite Z.add_0_r. apply Ptrofs.unsigned_range_2.
Qed.

Remark valid_different_pointers_extends:
  forall m1 b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m1 b2 (Ptrofs.unsigned ofs2) = true ->
  Some(b1, 0) = Some (b1', delta1) ->
  Some(b2, 0) = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned(Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned(Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Proof.
  intros. inv H2; inv H3. auto.
Qed.

Lemma eval_condition_lessdef:
  forall cond vl1 vl2 b m1 m2,
  Val.lessdef_list vl1 vl2 ->
  Mem.extends m1 m2 ->
  eval_condition cond vl1 m1 = Some b ->
  eval_condition cond vl2 m2 = Some b.
Proof.
  intros. eapply eval_condition_inj with (f := fun b => Some(b, 0)) (m1 := m1).
  apply valid_pointer_extends; auto.
  apply weak_valid_pointer_extends; auto.
  apply weak_valid_pointer_no_overflow_extends.
  apply valid_different_pointers_extends; auto.
  rewrite <- val_inject_list_lessdef. eauto. auto.
Qed.

Lemma eval_operation_lessdef:
  forall sp op vl1 vl2 v1 m1 m2,
  Val.lessdef_list vl1 vl2 ->
  Mem.extends m1 m2 ->
  eval_operation genv sp op vl1 m1 = Some v1 ->
  exists v2, eval_operation genv sp op vl2 m2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. rewrite val_inject_list_lessdef in H.
  assert (exists v2 : val,
          eval_operation genv sp op vl2 m2 = Some v2
          /\ Val.inject (fun b => Some(b, 0)) v1 v2).
  eapply eval_operation_inj with (m1 := m1) (sp1 := sp).
  apply valid_pointer_extends; auto.
  apply weak_valid_pointer_extends; auto.
  apply weak_valid_pointer_no_overflow_extends.
  apply valid_different_pointers_extends; auto.
  intros. apply val_inject_lessdef. auto.
  apply val_inject_lessdef; auto.
  eauto.
  auto.
  destruct H2 as [v2 [A B]]. exists v2; split; auto. rewrite val_inject_lessdef; auto.
Qed.

Lemma eval_addressing_lessdef:
  forall sp addr vl1 vl2 v1,
  Val.lessdef_list vl1 vl2 ->
  eval_addressing genv sp addr vl1 = Some v1 ->
  exists v2, eval_addressing genv sp addr vl2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. rewrite val_inject_list_lessdef in H.
  assert (exists v2 : val,
          eval_addressing genv sp addr vl2 = Some v2
          /\ Val.inject (fun b => Some(b, 0)) v1 v2).
  eapply eval_addressing_inj with (sp1 := sp).
  intros. rewrite <- val_inject_lessdef; auto.
  rewrite <- val_inject_lessdef; auto.
  eauto. auto.
  destruct H1 as [v2 [A B]]. exists v2; split; auto. rewrite val_inject_lessdef; auto.
Qed.

End EVAL_LESSDEF.

(** Compatibility of the evaluation functions with memory injections. *)

Section EVAL_INJECT.

Variable F V: Type.
Variable genv: Genv.t F V.
Variable f: meminj.
Hypothesis globals: meminj_preserves_globals genv f.
Variable sp1: block.
Variable sp2: block.
Variable delta: Z.
Hypothesis sp_inj: f sp1 = Some(sp2, delta).

Remark symbol_address_inject:
  forall id ofs, Val.inject f (Genv.symbol_address genv id ofs) (Genv.symbol_address genv id ofs).
Proof.
  intros. unfold Genv.symbol_address. destruct (Genv.find_symbol genv id) eqn:?; auto.
  exploit (proj1 globals); eauto. intros.
  econstructor; eauto. rewrite Ptrofs.add_zero; auto.
Qed.

Lemma eval_condition_inject:
  forall cond vl1 vl2 b m1 m2,
  Val.inject_list f vl1 vl2 ->
  Mem.inject f m1 m2 ->
  eval_condition cond vl1 m1 = Some b ->
  eval_condition cond vl2 m2 = Some b.
Proof.
  intros. eapply eval_condition_inj with (f := f) (m1 := m1); eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
Qed.

Lemma eval_addressing_inject:
  forall addr vl1 vl2 v1,
  Val.inject_list f vl1 vl2 ->
  eval_addressing genv (Vptr sp1 Ptrofs.zero) addr vl1 = Some v1 ->
  exists v2,
     eval_addressing genv (Vptr sp2 Ptrofs.zero) (shift_stack_addressing delta addr) vl2 = Some v2
  /\ Val.inject f v1 v2.
Proof.
  intros.
  rewrite eval_shift_stack_addressing.
  eapply eval_addressing_inj with (sp1 := Vptr sp1 Ptrofs.zero); eauto.
  intros. apply symbol_address_inject.
  econstructor; eauto. rewrite Ptrofs.add_zero_l; auto. 
Qed.

Lemma eval_operation_inject:
  forall op vl1 vl2 v1 m1 m2,
  Val.inject_list f vl1 vl2 ->
  Mem.inject f m1 m2 ->
  eval_operation genv (Vptr sp1 Ptrofs.zero) op vl1 m1 = Some v1 ->
  exists v2,
     eval_operation genv (Vptr sp2 Ptrofs.zero) (shift_stack_operation delta op) vl2 m2 = Some v2
  /\ Val.inject f v1 v2.
Proof.
  intros.
  rewrite eval_shift_stack_operation. simpl.
  eapply eval_operation_inj with (sp1 := Vptr sp1 Ptrofs.zero) (m1 := m1); eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  intros. apply symbol_address_inject.
  econstructor; eauto. rewrite Ptrofs.add_zero_l; auto. 
Qed.

End EVAL_INJECT.

(** * Handling of builtin arguments *)

Definition builtin_arg_ok_1
       (A: Type) (ba: builtin_arg A) (c: builtin_arg_constraint) :=
  match c, ba with
  | OK_all, _ => true
  | OK_const, (BA_int _ | BA_long _ | BA_float _ | BA_single _) => true
  | OK_addrstack, BA_addrstack _ => true
  | OK_addressing, BA_addrstack _ => true
  | OK_addressing, BA_addptr (BA _) (BA_int _) => true
  | OK_addressing, BA_addptr (BA _) (BA_long _) => true
  | _, _ => false
  end.

Definition builtin_arg_ok
       (A: Type) (ba: builtin_arg A) (c: builtin_arg_constraint) :=
  match ba with
  | (BA _ | BA_splitlong (BA _) (BA _)) => true
  | _ => builtin_arg_ok_1 ba c
  end.  
