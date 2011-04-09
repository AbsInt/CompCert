(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
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

  These types are PowerPC-specific and correspond roughly to what the 
  processor can compute in one instruction.  In other terms, these
  types reflect the state of the program after instruction selection.
  For a processor-independent set of operations, see the abstract
  syntax and dynamic semantics of the Cminor language.
*)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memdata.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.

Set Implicit Arguments.

(** Conditions (boolean-valued operators). *)

Inductive condition : Type :=
  | Ccomp: comparison -> condition      (**r signed integer comparison *)
  | Ccompu: comparison -> condition     (**r unsigned integer comparison *)
  | Ccompimm: comparison -> int -> condition (**r signed integer comparison with a constant *)
  | Ccompuimm: comparison -> int -> condition  (**r unsigned integer comparison with a constant *)
  | Ccompf: comparison -> condition     (**r floating-point comparison *)
  | Cnotcompf: comparison -> condition  (**r negation of a floating-point comparison *)
  | Cmaskzero: int -> condition         (**r test [(arg & constant) == 0] *)
  | Cmasknotzero: int -> condition.     (**r test [(arg & constant) != 0] *)

(** Arithmetic and logical operations.  In the descriptions, [rd] is the
  result of the operation and [r1], [r2], etc, are the arguments. *)

Inductive operation : Type :=
  | Omove: operation                    (**r [rd = r1] *)
  | Ointconst: int -> operation         (**r [rd] is set to the given integer constant *)
  | Ofloatconst: float -> operation     (**r [rd] is set to the given float constant *)
  | Oaddrsymbol: ident -> int -> operation (**r [rd] is set to the the address of the symbol plus the offset *)
  | Oaddrstack: int -> operation        (**r [rd] is set to the stack pointer plus the given offset *)
(*c Integer arithmetic: *)
  | Ocast8signed: operation             (**r [rd] is 8-bit sign extension of [r1] *)
  | Ocast8unsigned: operation           (**r [rd] is 8-bit zero extension of [r1] *)
  | Ocast16signed: operation            (**r [rd] is 16-bit sign extension of [r1] *)
  | Ocast16unsigned: operation          (**r [rd] is 16-bit zero extension of [r1] *)
  | Oadd: operation                     (**r [rd = r1 + r2] *)
  | Oaddimm: int -> operation           (**r [rd = r1 + n] *)
  | Osub: operation                     (**r [rd = r1 - r2] *)
  | Osubimm: int -> operation           (**r [rd = n - r1] *)
  | Omul: operation                     (**r [rd = r1 * r2] *)
  | Omulimm: int -> operation           (**r [rd = r1 * n] *)
  | Odiv: operation                     (**r [rd = r1 / r2] (signed) *)
  | Odivu: operation                    (**r [rd = r1 / r2] (unsigned) *)
  | Oand: operation                     (**r [rd = r1 & r2] *)
  | Oandimm: int -> operation           (**r [rd = r1 & n] *)
  | Oor: operation                      (**r [rd = r1 | r2] *)
  | Oorimm: int -> operation            (**r [rd = r1 | n] *)
  | Oxor: operation                     (**r [rd = r1 ^ r2] *)
  | Oxorimm: int -> operation           (**r [rd = r1 ^ n] *)
  | Onand: operation                    (**r [rd = ~(r1 & r2)] *)
  | Onor: operation                     (**r [rd = ~(r1 | r2)] *)
  | Onxor: operation                    (**r [rd = ~(r1 ^ r2)] *)
  | Oshl: operation                     (**r [rd = r1 << r2] *)
  | Oshr: operation                     (**r [rd = r1 >> r2] (signed) *)
  | Oshrimm: int -> operation           (**r [rd = r1 >> n] (signed) *)
  | Oshrximm: int -> operation          (**r [rd = r1 / 2^n] (signed) *)
  | Oshru: operation                    (**r [rd = r1 >> r2] (unsigned) *)
  | Orolm: int -> int -> operation      (**r rotate left and mask *)
(*c Floating-point arithmetic: *)
  | Onegf: operation                    (**r [rd = - r1] *)
  | Oabsf: operation                    (**r [rd = abs(r1)] *)
  | Oaddf: operation                    (**r [rd = r1 + r2] *)
  | Osubf: operation                    (**r [rd = r1 - r2] *)
  | Omulf: operation                    (**r [rd = r1 * r2] *)
  | Odivf: operation                    (**r [rd = r1 / r2] *)
  | Omuladdf: operation                 (**r [rd = r1 * r2 + r3] *)
  | Omulsubf: operation                 (**r [rd = r1 * r2 - r3] *)
  | Osingleoffloat: operation           (**r [rd] is [r1] truncated to single-precision float *)
(*c Conversions between int and float: *)
  | Ointoffloat: operation              (**r [rd = signed_int_of_float(r1)] *)
  | Ofloatofwords: operation            (**r [rd = float_of_words(r1,r2)] *)
(*c Boolean tests: *)
  | Ocmp: condition -> operation.       (**r [rd = 1] if condition holds, [rd = 0] otherwise. *)

(** Addressing modes.  [r1], [r2], etc, are the arguments to the 
  addressing. *)

Inductive addressing: Type :=
  | Aindexed: int -> addressing         (**r Address is [r1 + offset] *)
  | Aindexed2: addressing               (**r Address is [r1 + r2] *)
  | Aglobal: ident -> int -> addressing (**r Address is [symbol + offset] *)
  | Abased: ident -> int -> addressing (**r Address is [symbol + offset + r1] *)
  | Ainstack: int -> addressing.        (**r Address is [stack_pointer + offset] *)

(** Comparison functions (used in module [CSE]). *)

Definition eq_operation (x y: operation): {x=y} + {x<>y}.
Proof.
  generalize Int.eq_dec; intro.
  generalize Float.eq_dec; intro.
  assert (forall (x y: ident), {x=y}+{x<>y}). exact peq.
  assert (forall (x y: comparison), {x=y}+{x<>y}). decide equality.
  assert (forall (x y: condition), {x=y}+{x<>y}). decide equality.
  decide equality.
Qed.

Definition eq_addressing (x y: addressing) : {x=y} + {x<>y}.
Proof.
  generalize Int.eq_dec; intro.
  assert (forall (x y: ident), {x=y}+{x<>y}). exact peq.
  decide equality.
Qed.

(** Evaluation of conditions, operators and addressing modes applied
  to lists of values.  Return [None] when the computation is undefined:
  wrong number of arguments, arguments of the wrong types, undefined 
  operations such as division by zero.  [eval_condition] returns a boolean,
  [eval_operation] and [eval_addressing] return a value. *)

Definition eval_compare_mismatch (c: comparison) : option bool :=
  match c with Ceq => Some false | Cne => Some true | _ => None end.

Definition eval_compare_null (c: comparison) (n: int) : option bool :=
  if Int.eq n Int.zero then eval_compare_mismatch c else None.

Definition eval_condition (cond: condition) (vl: list val) (m: mem):
               option bool :=
  match cond, vl with
  | Ccomp c, Vint n1 :: Vint n2 :: nil =>
      Some (Int.cmp c n1 n2)
  | Ccompu c, Vint n1 :: Vint n2 :: nil =>
      Some (Int.cmpu c n1 n2)
  | Ccompu c, Vptr b1 n1 :: Vptr b2 n2 :: nil =>
      if Mem.valid_pointer m b1 (Int.unsigned n1)
      && Mem.valid_pointer m b2 (Int.unsigned n2) then
        if eq_block b1 b2
        then Some (Int.cmpu c n1 n2)
        else eval_compare_mismatch c
      else None
  | Ccompu c, Vptr b1 n1 :: Vint n2 :: nil =>
      eval_compare_null c n2
  | Ccompu c, Vint n1 :: Vptr b2 n2 :: nil =>
      eval_compare_null c n1
  | Ccompimm c n, Vint n1 :: nil =>
      Some (Int.cmp c n1 n)
  | Ccompuimm c n, Vint n1 :: nil =>
      Some (Int.cmpu c n1 n)
  | Ccompuimm c n, Vptr b1 n1 :: nil =>
      eval_compare_null c n
  | Ccompf c, Vfloat f1 :: Vfloat f2 :: nil =>
      Some (Float.cmp c f1 f2)
  | Cnotcompf c, Vfloat f1 :: Vfloat f2 :: nil =>
      Some (negb (Float.cmp c f1 f2))
  | Cmaskzero n, Vint n1 :: nil =>
      Some (Int.eq (Int.and n1 n) Int.zero)
  | Cmasknotzero n, Vint n1 :: nil =>
      Some (negb (Int.eq (Int.and n1 n) Int.zero))
  | _, _ =>
      None
  end.

Definition offset_sp (sp: val) (delta: int) : option val :=
  match sp with
  | Vptr b n => Some (Vptr b (Int.add n delta))
  | _ => None
  end.

Definition eval_operation
    (F V: Type) (genv: Genv.t F V) (sp: val)
    (op: operation) (vl: list val) (m: mem): option val :=
  match op, vl with
  | Omove, v1::nil => Some v1
  | Ointconst n, nil => Some (Vint n)
  | Ofloatconst n, nil => Some (Vfloat n)
  | Oaddrsymbol s ofs, nil =>
      match Genv.find_symbol genv s with
      | None => None
      | Some b => Some (Vptr b ofs)
      end
  | Oaddrstack ofs, nil => offset_sp sp ofs
  | Ocast8signed, v1 :: nil => Some (Val.sign_ext 8 v1)
  | Ocast8unsigned, v1 :: nil => Some (Val.zero_ext 8 v1)
  | Ocast16signed, v1 :: nil => Some (Val.sign_ext 16 v1)
  | Ocast16unsigned, v1 :: nil => Some (Val.zero_ext 16 v1)
  | Oadd, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.add n1 n2))
  | Oadd, Vint n1 :: Vptr b2 n2 :: nil => Some (Vptr b2 (Int.add n2 n1))
  | Oadd, Vptr b1 n1 :: Vint n2 :: nil => Some (Vptr b1 (Int.add n1 n2))
  | Oaddimm n, Vint n1 :: nil => Some (Vint (Int.add n1 n))
  | Oaddimm n, Vptr b1 n1 :: nil => Some (Vptr b1 (Int.add n1 n))
  | Osub, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.sub n1 n2))
  | Osub, Vptr b1 n1 :: Vint n2 :: nil => Some (Vptr b1 (Int.sub n1 n2))
  | Osub, Vptr b1 n1 :: Vptr b2 n2 :: nil =>
      if eq_block b1 b2 then Some (Vint (Int.sub n1 n2)) else None
  | Osubimm n, Vint n1 :: nil => Some (Vint (Int.sub n n1))
  | Omul, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.mul n1 n2))
  | Omulimm n, Vint n1 :: nil => Some (Vint (Int.mul n1 n))
  | Odiv, Vint n1 :: Vint n2 :: nil =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.divs n1 n2))
  | Odivu, Vint n1 :: Vint n2 :: nil =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.divu n1 n2))
  | Oand, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.and n1 n2))
  | Oandimm n, Vint n1 :: nil => Some (Vint (Int.and n1 n))
  | Oor, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.or n1 n2))
  | Oorimm n, Vint n1 :: nil => Some (Vint (Int.or n1 n))
  | Oxor, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.xor n1 n2))
  | Oxorimm n, Vint n1 :: nil => Some (Vint (Int.xor n1 n))
  | Onand, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.not (Int.and n1 n2)))
  | Onor, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.not (Int.or n1 n2)))
  | Onxor, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.not (Int.xor n1 n2)))
  | Oshl, Vint n1 :: Vint n2 :: nil =>
      if Int.ltu n2 Int.iwordsize then Some (Vint (Int.shl n1 n2)) else None
  | Oshr, Vint n1 :: Vint n2 :: nil =>
      if Int.ltu n2 Int.iwordsize then Some (Vint (Int.shr n1 n2)) else None
  | Oshrimm n, Vint n1 :: nil =>
      if Int.ltu n Int.iwordsize then Some (Vint (Int.shr n1 n)) else None
  | Oshrximm n, Vint n1 :: nil =>
      if Int.ltu n Int.iwordsize then Some (Vint (Int.shrx n1 n)) else None
  | Oshru, Vint n1 :: Vint n2 :: nil =>
      if Int.ltu n2 Int.iwordsize then Some (Vint (Int.shru n1 n2)) else None
  | Orolm amount mask, Vint n1 :: nil =>
      Some (Vint (Int.rolm n1 amount mask))
  | Onegf, Vfloat f1 :: nil => Some (Vfloat (Float.neg f1))
  | Oabsf, Vfloat f1 :: nil => Some (Vfloat (Float.abs f1))
  | Oaddf, Vfloat f1 :: Vfloat f2 :: nil => Some (Vfloat (Float.add f1 f2))
  | Osubf, Vfloat f1 :: Vfloat f2 :: nil => Some (Vfloat (Float.sub f1 f2))
  | Omulf, Vfloat f1 :: Vfloat f2 :: nil => Some (Vfloat (Float.mul f1 f2))
  | Odivf, Vfloat f1 :: Vfloat f2 :: nil => Some (Vfloat (Float.div f1 f2))
  | Omuladdf, Vfloat f1 :: Vfloat f2 :: Vfloat f3 :: nil =>
      Some (Vfloat (Float.add (Float.mul f1 f2) f3))
  | Omulsubf, Vfloat f1 :: Vfloat f2 :: Vfloat f3 :: nil =>
      Some (Vfloat (Float.sub (Float.mul f1 f2) f3))
  | Osingleoffloat, v1 :: nil =>
      Some (Val.singleoffloat v1)
  | Ointoffloat, Vfloat f1 :: nil => 
      option_map Vint (Float.intoffloat f1)
  | Ofloatofwords, Vint i1 :: Vint i2 :: nil =>
      Some (Vfloat (Float.from_words i1 i2))
  | Ocmp c, _ =>
      match eval_condition c vl m with
      | None => None
      | Some false => Some Vfalse
      | Some true => Some Vtrue
      end
  | _, _ => None
  end.

Definition eval_addressing
    (F V: Type) (genv: Genv.t F V) (sp: val)
    (addr: addressing) (vl: list val) : option val :=
  match addr, vl with
  | Aindexed n, Vptr b1 n1 :: nil =>
      Some (Vptr b1 (Int.add n1 n))
  | Aindexed2, Vptr b1 n1 :: Vint n2 :: nil =>
      Some (Vptr b1 (Int.add n1 n2))
  | Aindexed2, Vint n1 :: Vptr b2 n2 :: nil =>
      Some (Vptr b2 (Int.add n2 n1))
  | Aglobal s ofs, nil =>
      match Genv.find_symbol genv s with
      | None => None
      | Some b => Some (Vptr b ofs)
      end
  | Abased s ofs, Vint n1 :: nil =>
      match Genv.find_symbol genv s with
      | None => None
      | Some b => Some (Vptr b (Int.add ofs n1))
      end
  | Ainstack ofs, nil =>
      offset_sp sp ofs
  | _, _ => None
  end.

Definition negate_condition (cond: condition): condition :=
  match cond with
  | Ccomp c => Ccomp(negate_comparison c)
  | Ccompu c => Ccompu(negate_comparison c)
  | Ccompimm c n => Ccompimm (negate_comparison c) n
  | Ccompuimm c n => Ccompuimm (negate_comparison c) n
  | Ccompf c => Cnotcompf c
  | Cnotcompf c => Ccompf c
  | Cmaskzero n => Cmasknotzero n
  | Cmasknotzero n => Cmaskzero n
  end.

Ltac FuncInv :=
  match goal with
  | H: (match ?x with nil => _ | _ :: _ => _ end = Some _) |- _ =>
      destruct x; simpl in H; try discriminate; FuncInv
  | H: (match ?v with Vundef => _ | Vint _ => _ | Vfloat _ => _ | Vptr _ _ => _ end = Some _) |- _ =>
      destruct v; simpl in H; try discriminate; FuncInv
  | H: (Some _ = Some _) |- _ =>
      injection H; intros; clear H; FuncInv
  | _ =>
      idtac
  end.

Remark eval_negate_compare_mismatch:
  forall c b,
  eval_compare_mismatch c = Some b ->
  eval_compare_mismatch (negate_comparison c) = Some (negb b).
Proof.
  intros until b. unfold eval_compare_mismatch.
  destruct c; intro EQ; inv EQ; auto. 
Qed.

Remark eval_negate_compare_null:
  forall c i b,
  eval_compare_null c i = Some b ->
  eval_compare_null (negate_comparison c) i = Some (negb b).
Proof.
  unfold eval_compare_null; intros.
  destruct (Int.eq i Int.zero). apply eval_negate_compare_mismatch; auto. congruence.
Qed.

Lemma eval_negate_condition:
  forall cond vl m b,
  eval_condition cond vl m = Some b ->
  eval_condition (negate_condition cond) vl m = Some (negb b).
Proof.
  intros. 
  destruct cond; simpl in H; FuncInv; try subst b; simpl.
  rewrite Int.negate_cmp. auto.
  rewrite Int.negate_cmpu. auto.
  apply eval_negate_compare_null; auto.
  apply eval_negate_compare_null; auto.
  destruct (Mem.valid_pointer m b0 (Int.unsigned i) &&
          Mem.valid_pointer m b1 (Int.unsigned i0)); try congruence.
  destruct (eq_block b0 b1). rewrite Int.negate_cmpu. congruence.
  apply eval_negate_compare_mismatch; auto. 
  rewrite Int.negate_cmp. auto.
  rewrite Int.negate_cmpu. auto.
  apply eval_negate_compare_null; auto.
  auto.
  rewrite negb_elim. auto.
  auto.
  rewrite negb_elim. auto.
Qed.

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

Lemma eval_operation_preserved:
  forall sp op vl m,
  eval_operation ge2 sp op vl m = eval_operation ge1 sp op vl m.
Proof.
  intros.
  unfold eval_operation; destruct op; try rewrite agree_on_symbols;
  reflexivity.
Qed.

Lemma eval_addressing_preserved:
  forall sp addr vl,
  eval_addressing ge2 sp addr vl = eval_addressing ge1 sp addr vl.
Proof.
  intros.
  unfold eval_addressing; destruct addr; try rewrite agree_on_symbols;
  reflexivity.
Qed.

End GENV_TRANSF.

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

(** Static typing of conditions, operators and addressing modes. *)

Definition type_of_condition (c: condition) : list typ :=
  match c with
  | Ccomp _ => Tint :: Tint :: nil
  | Ccompu _ => Tint :: Tint :: nil
  | Ccompimm _ _ => Tint :: nil
  | Ccompuimm _ _ => Tint :: nil
  | Ccompf _ => Tfloat :: Tfloat :: nil
  | Cnotcompf _ => Tfloat :: Tfloat :: nil
  | Cmaskzero _ => Tint :: nil
  | Cmasknotzero _ => Tint :: nil
  end.

Definition type_of_operation (op: operation) : list typ * typ :=
  match op with
  | Omove => (nil, Tint)   (* treated specially *)
  | Ointconst _ => (nil, Tint)
  | Ofloatconst _ => (nil, Tfloat)
  | Oaddrsymbol _ _ => (nil, Tint)
  | Oaddrstack _ => (nil, Tint)
  | Ocast8signed => (Tint :: nil, Tint)
  | Ocast8unsigned => (Tint :: nil, Tint)
  | Ocast16signed => (Tint :: nil, Tint)
  | Ocast16unsigned => (Tint :: nil, Tint)
  | Oadd => (Tint :: Tint :: nil, Tint)
  | Oaddimm _ => (Tint :: nil, Tint)
  | Osub => (Tint :: Tint :: nil, Tint)
  | Osubimm _ => (Tint :: nil, Tint)
  | Omul => (Tint :: Tint :: nil, Tint)
  | Omulimm _ => (Tint :: nil, Tint)
  | Odiv => (Tint :: Tint :: nil, Tint)
  | Odivu => (Tint :: Tint :: nil, Tint)
  | Oand => (Tint :: Tint :: nil, Tint)
  | Oandimm _ => (Tint :: nil, Tint)
  | Oor => (Tint :: Tint :: nil, Tint)
  | Oorimm _ => (Tint :: nil, Tint)
  | Oxor => (Tint :: Tint :: nil, Tint)
  | Oxorimm _ => (Tint :: nil, Tint)
  | Onand => (Tint :: Tint :: nil, Tint)
  | Onor => (Tint :: Tint :: nil, Tint)
  | Onxor => (Tint :: Tint :: nil, Tint)
  | Oshl => (Tint :: Tint :: nil, Tint)
  | Oshr => (Tint :: Tint :: nil, Tint)
  | Oshrimm _ => (Tint :: nil, Tint)
  | Oshrximm _ => (Tint :: nil, Tint)
  | Oshru => (Tint :: Tint :: nil, Tint)
  | Orolm _ _ => (Tint :: nil, Tint)
  | Onegf => (Tfloat :: nil, Tfloat)
  | Oabsf => (Tfloat :: nil, Tfloat)
  | Oaddf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Osubf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Omulf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Odivf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Omuladdf => (Tfloat :: Tfloat :: Tfloat :: nil, Tfloat)
  | Omulsubf => (Tfloat :: Tfloat :: Tfloat :: nil, Tfloat)
  | Osingleoffloat => (Tfloat :: nil, Tfloat)
  | Ointoffloat => (Tfloat :: nil, Tint)
  | Ofloatofwords => (Tint :: Tint :: nil, Tfloat)
  | Ocmp c => (type_of_condition c, Tint)
  end.

Definition type_of_addressing (addr: addressing) : list typ :=
  match addr with
  | Aindexed _ => Tint :: nil
  | Aindexed2 => Tint :: Tint :: nil
  | Aglobal _ _ => nil
  | Abased _ _ => Tint :: nil
  | Ainstack _ => nil
  end.

(** Weak type soundness results for [eval_operation]:
  the result values, when defined, are always of the type predicted
  by [type_of_operation]. *)

Section SOUNDNESS.

Variable A V: Type.
Variable genv: Genv.t A V.

Lemma type_of_operation_sound:
  forall op vl sp v m,
  op <> Omove ->
  eval_operation genv sp op vl m = Some v ->
  Val.has_type v (snd (type_of_operation op)).
Proof.
  intros.
  destruct op; simpl in H0; FuncInv; try subst v; try exact I.
  congruence.
  destruct (Genv.find_symbol genv i); simplify_eq H0; intro; subst v; exact I.
  simpl. unfold offset_sp in H0. destruct sp; try discriminate.
  inversion H0. exact I.
  destruct v0; exact I. 
  destruct v0; exact I. 
  destruct v0; exact I. 
  destruct v0; exact I. 
  destruct (eq_block b b0). injection H0; intro; subst v; exact I.
  discriminate.
  destruct (Int.eq i0 Int.zero). discriminate. 
  injection H0; intro; subst v; exact I.
  destruct (Int.eq i0 Int.zero). discriminate. 
  injection H0; intro; subst v; exact I.
  destruct (Int.ltu i0 Int.iwordsize).
  injection H0; intro; subst v; exact I. discriminate.
  destruct (Int.ltu i0 Int.iwordsize).
  injection H0; intro; subst v; exact I. discriminate.
  destruct (Int.ltu i Int.iwordsize).
  injection H0; intro; subst v; exact I. discriminate.
  destruct (Int.ltu i Int.iwordsize).
  injection H0; intro; subst v; exact I. discriminate.
  destruct (Int.ltu i0 Int.iwordsize).
  injection H0; intro; subst v; exact I. discriminate.
  destruct v0; exact I.
  destruct (Float.intoffloat f); simpl in H0; inv H0. exact I.
  destruct (eval_condition c vl). 
  destruct b; injection H0; intro; subst v; exact I.
  discriminate.
Qed.

Lemma type_of_chunk_correct:
  forall chunk m addr v,
  Mem.loadv chunk m addr = Some v ->
  Val.has_type v (type_of_chunk chunk).
Proof.
  intro chunk.
  assert (forall v, Val.has_type (Val.load_result chunk v) (type_of_chunk chunk)).
  destruct v; destruct chunk; exact I.
  intros until v. unfold Mem.loadv. 
  destruct addr; intros; try discriminate.
  eapply Mem.load_type; eauto.
Qed.

End SOUNDNESS.

(** Alternate definition of [eval_condition], [eval_op], [eval_addressing]
  as total functions that return [Vundef] when not applicable
  (instead of [None]).  Used in the proof of [PPCgen]. *)

Section EVAL_OP_TOTAL.

Variable F V: Type.
Variable genv: Genv.t F V.

Definition find_symbol_offset (id: ident) (ofs: int) : val :=
  match Genv.find_symbol genv id with
  | Some b => Vptr b ofs
  | None => Vundef
  end.

Definition eval_condition_total (cond: condition) (vl: list val) : val :=
  match cond, vl with
  | Ccomp c, v1::v2::nil => Val.cmp c v1 v2
  | Ccompu c, v1::v2::nil => Val.cmpu c v1 v2
  | Ccompimm c n, v1::nil => Val.cmp c v1 (Vint n)
  | Ccompuimm c n, v1::nil => Val.cmpu c v1 (Vint n)
  | Ccompf c, v1::v2::nil => Val.cmpf c v1 v2
  | Cnotcompf c, v1::v2::nil => Val.notbool(Val.cmpf c v1 v2)
  | Cmaskzero n, v1::nil => Val.notbool (Val.and v1 (Vint n))
  | Cmasknotzero n, v1::nil => Val.notbool(Val.notbool (Val.and v1 (Vint n)))
  | _, _ => Vundef
  end.

Definition eval_operation_total (sp: val) (op: operation) (vl: list val) : val :=
  match op, vl with
  | Omove, v1::nil => v1
  | Ointconst n, nil => Vint n
  | Ofloatconst n, nil => Vfloat n
  | Oaddrsymbol s ofs, nil => find_symbol_offset s ofs
  | Oaddrstack ofs, nil => Val.add sp (Vint ofs)
  | Ocast8signed, v1::nil => Val.sign_ext 8 v1
  | Ocast8unsigned, v1::nil => Val.zero_ext 8 v1
  | Ocast16signed, v1::nil => Val.sign_ext 16 v1
  | Ocast16unsigned, v1::nil => Val.zero_ext 16 v1
  | Oadd, v1::v2::nil => Val.add v1 v2
  | Oaddimm n, v1::nil => Val.add v1 (Vint n)
  | Osub, v1::v2::nil => Val.sub v1 v2
  | Osubimm n, v1::nil => Val.sub (Vint n) v1
  | Omul, v1::v2::nil => Val.mul v1 v2
  | Omulimm n, v1::nil => Val.mul v1 (Vint n)
  | Odiv, v1::v2::nil => Val.divs v1 v2
  | Odivu, v1::v2::nil => Val.divu v1 v2
  | Oand, v1::v2::nil => Val.and v1 v2
  | Oandimm n, v1::nil => Val.and v1 (Vint n)
  | Oor, v1::v2::nil => Val.or v1 v2
  | Oorimm n, v1::nil => Val.or v1 (Vint n)
  | Oxor, v1::v2::nil => Val.xor v1 v2
  | Oxorimm n, v1::nil => Val.xor v1 (Vint n)
  | Onand, v1::v2::nil => Val.notint(Val.and v1 v2)
  | Onor, v1::v2::nil => Val.notint(Val.or v1 v2)
  | Onxor, v1::v2::nil => Val.notint(Val.xor v1 v2)
  | Oshl, v1::v2::nil => Val.shl v1 v2
  | Oshr, v1::v2::nil => Val.shr v1 v2
  | Oshrimm n, v1::nil => Val.shr v1 (Vint n)
  | Oshrximm n, v1::nil => Val.shrx v1 (Vint n)
  | Oshru, v1::v2::nil => Val.shru v1 v2
  | Orolm amount mask, v1::nil => Val.rolm v1 amount mask
  | Onegf, v1::nil => Val.negf v1
  | Oabsf, v1::nil => Val.absf v1
  | Oaddf, v1::v2::nil => Val.addf v1 v2
  | Osubf, v1::v2::nil => Val.subf v1 v2
  | Omulf, v1::v2::nil => Val.mulf v1 v2
  | Odivf, v1::v2::nil => Val.divf v1 v2
  | Omuladdf, v1::v2::v3::nil => Val.addf (Val.mulf v1 v2) v3
  | Omulsubf, v1::v2::v3::nil => Val.subf (Val.mulf v1 v2) v3
  | Osingleoffloat, v1::nil => Val.singleoffloat v1
  | Ointoffloat, v1::nil => Val.intoffloat v1
  | Ofloatofwords, v1::v2::nil => Val.floatofwords v1 v2
  | Ocmp c, _ => eval_condition_total c vl
  | _, _ => Vundef
  end.

Definition eval_addressing_total
    (sp: val) (addr: addressing) (vl: list val) : val :=
  match addr, vl with
  | Aindexed n, v1::nil => Val.add v1 (Vint n)
  | Aindexed2, v1::v2::nil => Val.add v1 v2
  | Aglobal s ofs, nil => find_symbol_offset s ofs
  | Abased s ofs, v1::nil => Val.add (find_symbol_offset s ofs) v1
  | Ainstack ofs, nil => Val.add sp (Vint ofs)
  | _, _ => Vundef
  end.

Lemma eval_compare_mismatch_weaken:
  forall c b,
  eval_compare_mismatch c = Some b ->
  Val.cmp_mismatch c = Val.of_bool b.
Proof.
  unfold eval_compare_mismatch. intros. destruct c; inv H; auto.
Qed.

Lemma eval_compare_null_weaken:
  forall n c b,
  eval_compare_null c n = Some b ->
  (if Int.eq n Int.zero then Val.cmp_mismatch c else Vundef) = Val.of_bool b.
Proof.
  unfold eval_compare_null.
  intros. destruct (Int.eq n Int.zero). apply eval_compare_mismatch_weaken. auto.
  discriminate.
Qed.

Lemma eval_condition_weaken:
  forall c vl b m,
  eval_condition c vl m = Some b ->
  eval_condition_total c vl = Val.of_bool b.
Proof.
  intros. 
  unfold eval_condition in H; destruct c; FuncInv;
  try subst b; try reflexivity; simpl;
  try (apply eval_compare_null_weaken; auto).
  destruct (Mem.valid_pointer m b0 (Int.unsigned i) &&
            Mem.valid_pointer m b1 (Int.unsigned i0)); try congruence.
  unfold eq_block in H. destruct (zeq b0 b1).
  congruence.
  apply eval_compare_mismatch_weaken; auto.
  symmetry. apply Val.notbool_negb_1. 
  symmetry. apply Val.notbool_negb_1. 
Qed.

Lemma eval_operation_weaken:
  forall sp op vl v m,
  eval_operation genv sp op vl m = Some v ->
  eval_operation_total sp op vl = v.
Proof.
  intros.
  unfold eval_operation in H; destruct op; FuncInv;
  try subst v; try reflexivity; simpl.
  unfold find_symbol_offset. 
  destruct (Genv.find_symbol genv i); try discriminate.
  congruence.
  unfold offset_sp in H. 
  destruct sp; try discriminate. simpl. congruence.
  unfold eq_block in H. destruct (zeq b b0); congruence.
  destruct (Int.eq i0 Int.zero); congruence.
  destruct (Int.eq i0 Int.zero); congruence.
  destruct (Int.ltu i0 Int.iwordsize); congruence.
  destruct (Int.ltu i0 Int.iwordsize); congruence.
  destruct (Int.ltu i Int.iwordsize); congruence.
  destruct (Int.ltu i Int.iwordsize); congruence.
  destruct (Int.ltu i0 Int.iwordsize); congruence.
  destruct (Float.intoffloat f); inv H. auto.
  caseEq (eval_condition c vl m); intros; rewrite H0 in H.
  replace v with (Val.of_bool b).
  eapply eval_condition_weaken; eauto.
  destruct b; simpl; congruence.
  discriminate.
Qed.

Lemma eval_addressing_weaken:
  forall sp addr vl v,
  eval_addressing genv sp addr vl = Some v ->
  eval_addressing_total sp addr vl = v.
Proof.
  intros.
  unfold eval_addressing in H; destruct addr; FuncInv;
  try subst v; simpl; try reflexivity.
  unfold find_symbol_offset. 
  destruct (Genv.find_symbol genv i); congruence.
  unfold find_symbol_offset.
  destruct (Genv.find_symbol genv i); try congruence.
  inversion H. reflexivity.
  unfold offset_sp in H. destruct sp; simpl; congruence.
Qed.

Lemma eval_condition_total_is_bool:
  forall cond vl, Val.is_bool (eval_condition_total cond vl).
Proof.
  intros; destruct cond;
  destruct vl; try apply Val.undef_is_bool;
  destruct vl; try apply Val.undef_is_bool;
  try (destruct vl; try apply Val.undef_is_bool); simpl.
  apply Val.cmp_is_bool.
  apply Val.cmpu_is_bool.
  apply Val.cmp_is_bool.
  apply Val.cmpu_is_bool.
  apply Val.cmpf_is_bool.
  apply Val.notbool_is_bool.
  apply Val.notbool_is_bool.
  apply Val.notbool_is_bool.
Qed.

End EVAL_OP_TOTAL.

(** Compatibility of the evaluation functions with the
    ``is less defined'' relation over values. *)

Section EVAL_LESSDEF.

Variable F V: Type.
Variable genv: Genv.t F V.

Ltac InvLessdef :=
  match goal with
  | [ H: Val.lessdef (Vint _) _ |- _ ] =>
      inv H; InvLessdef
  | [ H: Val.lessdef (Vfloat _) _ |- _ ] =>
      inv H; InvLessdef
  | [ H: Val.lessdef (Vptr _ _) _ |- _ ] =>
      inv H; InvLessdef
  | [ H: Val.lessdef_list nil _ |- _ ] =>
      inv H; InvLessdef
  | [ H: Val.lessdef_list (_ :: _) _ |- _ ] =>
      inv H; InvLessdef
  | _ => idtac
  end.

Lemma eval_condition_lessdef:
  forall cond vl1 vl2 b m1 m2,
  Val.lessdef_list vl1 vl2 ->
  Mem.extends m1 m2 ->
  eval_condition cond vl1 m1 = Some b ->
  eval_condition cond vl2 m2 = Some b.
Proof.
  intros. destruct cond; simpl in *; FuncInv; InvLessdef; auto.
  destruct (Mem.valid_pointer m1 b0 (Int.unsigned i) &&
            Mem.valid_pointer m1 b1 (Int.unsigned i0)) as [] _eqn; try discriminate.
  destruct (andb_prop _ _ Heqb2) as [A B].
  assert (forall b ofs, Mem.valid_pointer m1 b ofs = true -> Mem.valid_pointer m2 b ofs = true).
    intros until ofs. repeat rewrite Mem.valid_pointer_nonempty_perm. 
    apply Mem.perm_extends; auto.
  rewrite (H _ _ A). rewrite (H _ _ B). auto. 
Qed.

Ltac TrivialExists :=
  match goal with
  | [ |- exists v2, Some ?v1 = Some v2 /\ Val.lessdef ?v1 v2 ] =>
      exists v1; split; [auto | constructor]
  | _ => idtac
  end.

Lemma eval_operation_lessdef:
  forall sp op vl1 vl2 v1 m1 m2,
  Val.lessdef_list vl1 vl2 ->
  Mem.extends m1 m2 ->
  eval_operation genv sp op vl1 m1 = Some v1 ->
  exists v2, eval_operation genv sp op vl2 m2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. destruct op; simpl in *; FuncInv; InvLessdef; TrivialExists.
  exists v2; auto.
  destruct (Genv.find_symbol genv i); inv H1. TrivialExists.
  exists v1; auto.
  exists (Val.sign_ext 8 v2); split. auto. apply Val.sign_ext_lessdef; auto.
  exists (Val.zero_ext 8 v2); split. auto. apply Val.zero_ext_lessdef; auto.
  exists (Val.sign_ext 16 v2); split. auto. apply Val.sign_ext_lessdef; auto.
  exists (Val.zero_ext 16 v2); split. auto. apply Val.zero_ext_lessdef; auto.
  destruct (eq_block b b0); inv H1. TrivialExists.
  destruct (Int.eq i0 Int.zero); inv H1; TrivialExists.
  destruct (Int.eq i0 Int.zero); inv H1; TrivialExists.
  destruct (Int.ltu i0 Int.iwordsize); inv H1; TrivialExists.
  destruct (Int.ltu i0 Int.iwordsize); inv H1; TrivialExists.
  destruct (Int.ltu i Int.iwordsize); inv H1; TrivialExists.
  destruct (Int.ltu i Int.iwordsize); inv H1; TrivialExists.
  destruct (Int.ltu i0 Int.iwordsize); inv H1; TrivialExists.
  exists (Val.singleoffloat v2); split. auto. apply Val.singleoffloat_lessdef; auto.
  destruct (Float.intoffloat f); simpl in *; inv H1. TrivialExists.
  caseEq (eval_condition c vl1 m1); intros. rewrite H2 in H1. 
  rewrite (eval_condition_lessdef c H H0 H2).
  destruct b; inv H1; TrivialExists.
  rewrite H2 in H1. discriminate.
Qed.

Lemma eval_addressing_lessdef:
  forall sp addr vl1 vl2 v1,
  Val.lessdef_list vl1 vl2 ->
  eval_addressing genv sp addr vl1 = Some v1 ->
  exists v2, eval_addressing genv sp addr vl2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. destruct addr; simpl in *; FuncInv; InvLessdef; TrivialExists.
  destruct (Genv.find_symbol genv i); inv H0. TrivialExists.
  destruct (Genv.find_symbol genv i); inv H0. TrivialExists.
  exists v1; auto.
Qed.

End EVAL_LESSDEF.

(** Shifting stack-relative references.  This is used in [Stacking]. *)

Definition shift_stack_addressing (delta: int) (addr: addressing) :=
  match addr with
  | Ainstack ofs => Ainstack (Int.add delta ofs)
  | _ => addr
  end.

Definition shift_stack_operation (delta: int) (op: operation) :=
  match op with
  | Oaddrstack ofs => Oaddrstack (Int.add delta ofs)
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

Ltac InvInject :=
  match goal with
  | [ H: val_inject _ (Vint _) _ |- _ ] =>
      inv H; InvInject
  | [ H: val_inject _ (Vfloat _) _ |- _ ] =>
      inv H; InvInject
  | [ H: val_inject _ (Vptr _ _) _ |- _ ] =>
      inv H; InvInject
  | [ H: val_list_inject _ nil _ |- _ ] =>
      inv H; InvInject
  | [ H: val_list_inject _ (_ :: _) _ |- _ ] =>
      inv H; InvInject
  | _ => idtac
  end.

Lemma eval_condition_inject:
  forall cond vl1 vl2 b m1 m2,
  val_list_inject f vl1 vl2 ->
  Mem.inject f m1 m2 ->
  eval_condition cond vl1 m1 = Some b ->
  eval_condition cond vl2 m2 = Some b.
Proof.
  intros. destruct cond; simpl in *; FuncInv; InvInject; auto.
  destruct (Mem.valid_pointer m1 b0 (Int.unsigned i)) as [] _eqn; try discriminate.
  destruct (Mem.valid_pointer m1 b1 (Int.unsigned i0)) as [] _eqn; try discriminate.
  simpl in H1.
  exploit Mem.valid_pointer_inject_val. eauto. eexact Heqb0. econstructor; eauto. 
  intros V1. rewrite V1.
  exploit Mem.valid_pointer_inject_val. eauto. eexact Heqb2. econstructor; eauto. 
  intros V2. rewrite V2.
  simpl. 
  destruct (eq_block b0 b1); inv H1.
  rewrite H3 in H5; inv H5. rewrite dec_eq_true.
  decEq. apply Int.translate_cmpu.
  eapply Mem.valid_pointer_inject_no_overflow; eauto.
  eapply Mem.valid_pointer_inject_no_overflow; eauto.
  exploit Mem.different_pointers_inject; eauto. intros P.
  destruct (eq_block b3 b4); auto.
  destruct P. contradiction.
  destruct c; unfold eval_compare_mismatch in *; inv H2. 
  unfold Int.cmpu. rewrite Int.eq_false; auto. congruence. 
  unfold Int.cmpu. rewrite Int.eq_false; auto. congruence.
Qed.

Ltac TrivialExists2 :=
  match goal with
  | [ |- exists v2, Some ?v1 = Some v2 /\ val_inject _ _ v2 ] =>
      exists v1; split; [auto | econstructor; eauto]
  | _ => idtac
  end.

Lemma eval_addressing_inject:
  forall addr vl1 vl2 v1,
  val_list_inject f vl1 vl2 ->
  eval_addressing genv (Vptr sp1 Int.zero) addr vl1 = Some v1 ->
  exists v2, 
     eval_addressing genv (Vptr sp2 Int.zero) (shift_stack_addressing (Int.repr delta) addr) vl2 = Some v2
  /\ val_inject f v1 v2.
Proof.
  intros. destruct addr; simpl in *; FuncInv; InvInject; TrivialExists2.
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut. 
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  destruct (Genv.find_symbol genv i) as [] _eqn; inv H0.
  TrivialExists2. eapply (proj1 globals); eauto. rewrite Int.add_zero; auto.
  destruct (Genv.find_symbol genv i) as [] _eqn; inv H0.
  TrivialExists2. eapply (proj1 globals); eauto. rewrite Int.add_zero; auto.
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
Qed.

Lemma eval_operation_inject:
  forall op vl1 vl2 v1 m1 m2,
  val_list_inject f vl1 vl2 ->
  Mem.inject f m1 m2 ->
  eval_operation genv (Vptr sp1 Int.zero) op vl1 m1 = Some v1 ->
  exists v2,
     eval_operation genv (Vptr sp2 Int.zero) (shift_stack_operation (Int.repr delta) op) vl2 m2 = Some v2
  /\ val_inject f v1 v2.
Proof.
  intros. destruct op; simpl in *; FuncInv; InvInject; TrivialExists2.
  exists v'; auto.
  destruct (Genv.find_symbol genv i) as [] _eqn; inv H1.
  TrivialExists2. eapply (proj1 globals); eauto. rewrite Int.add_zero; auto.
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  exists (Val.sign_ext 8 v'); split; auto. inv H4; simpl; auto.
  exists (Val.zero_ext 8 v'); split; auto. inv H4; simpl; auto.
  exists (Val.sign_ext 16 v'); split; auto. inv H4; simpl; auto.
  exists (Val.zero_ext 16 v'); split; auto. inv H4; simpl; auto.
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  rewrite Int.sub_add_l. auto.
  destruct (eq_block b b0); inv H1. rewrite H3 in H5; inv H5. rewrite dec_eq_true.
  rewrite Int.sub_shifted. TrivialExists2.
  destruct (Int.eq i0 Int.zero); inv H1. TrivialExists2.
  destruct (Int.eq i0 Int.zero); inv H1. TrivialExists2.
  destruct (Int.eq i0 Int.zero); inv H1. TrivialExists2.
  destruct (Int.ltu i0 Int.iwordsize); inv H2. TrivialExists2.
  destruct (Int.ltu i0 Int.iwordsize); inv H2. TrivialExists2.
  destruct (Int.ltu i0 Int.iwordsize); inv H1. TrivialExists2.
  destruct (Int.ltu i Int.iwordsize); inv H1. TrivialExists2.
  destruct (Int.ltu i (Int.repr 31)); inv H1. TrivialExists2.
  destruct (Int.ltu i Int.iwordsize); inv H2. TrivialExists2.
  destruct (Int.ltu i Int.iwordsize); inv H2. TrivialExists2.
  destruct (Int.ltu i0 Int.iwordsize); inv H1. TrivialExists2.
  exists (Val.singleoffloat v'); split; auto. inv H4; simpl; auto.
  destruct (Float.intoffloat f0); simpl in *; inv H1. TrivialExists2.
  destruct (eval_condition c vl1 m1) as [] _eqn; try discriminate.
  exploit eval_condition_inject; eauto. intros EQ; rewrite EQ. 
  destruct b; inv H1; TrivialExists2.
Qed.

End EVAL_INJECT.

(** Transformation of addressing modes with two operands or more
  into an equivalent arithmetic operation.  This is used in the [Reload]
  pass when a store instruction cannot be reloaded directly because
  it runs out of temporary registers. *)

(** For the PowerPC, there is only one binary addressing mode: [Aindexed2].
  The corresponding operation is [Oadd]. *)

Definition op_for_binary_addressing (addr: addressing) : operation := Oadd.

Lemma eval_op_for_binary_addressing:
  forall (F V: Type) (ge: Genv.t F V) sp addr args v m,
  (length args >= 2)%nat ->
  eval_addressing ge sp addr args = Some v ->
  eval_operation ge sp (op_for_binary_addressing addr) args m = Some v.
Proof.
  intros.
  unfold eval_addressing in H0; destruct addr; FuncInv; simpl in H; try omegaContradiction;
  simpl; congruence.
Qed.

Lemma type_op_for_binary_addressing:
  forall addr,
  (length (type_of_addressing addr) >= 2)%nat ->
  type_of_operation (op_for_binary_addressing addr) = (type_of_addressing addr, Tint).
Proof.
  intros. destruct addr; simpl in H; reflexivity || omegaContradiction.
Qed.

(** Two-address operations.  There are none in the PowerPC architecture. *)

Definition two_address_op (op: operation) : bool := false.

(** Operations that are so cheap to recompute that CSE should not factor them out. *)

Definition is_trivial_op (op: operation) : bool :=
  match op with
  | Omove => true
  | Ointconst _ => true
  | Oaddrsymbol _ _ => true
  | Oaddrstack _ => true
  | _ => false
  end.


(** Operations that depend on the memory state. *)

Definition op_depends_on_memory (op: operation) : bool :=
  match op with
  | Ocmp (Ccompu _) => true
  | _ => false
  end.

Lemma op_depends_on_memory_correct:
  forall (F V: Type) (ge: Genv.t F V) sp op args m1 m2,
  op_depends_on_memory op = false ->
  eval_operation ge sp op args m1 = eval_operation ge sp op args m2.
Proof.
  intros until m2. destruct op; simpl; try congruence.
  destruct c; simpl; congruence.
Qed.
