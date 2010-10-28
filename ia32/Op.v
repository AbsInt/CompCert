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

  These types are IA32-specific and correspond roughly to what the 
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

(** Addressing modes.  [r1], [r2], etc, are the arguments to the 
  addressing. *)

Inductive addressing: Type :=
  | Aindexed: int -> addressing         (**r Address is [r1 + offset] *)
  | Aindexed2: int -> addressing        (**r Address is [r1 + r2 + offset] *)
  | Ascaled: int -> int -> addressing   (**r Address is [r1 * scale + offset] *)
  | Aindexed2scaled: int -> int -> addressing
                                   (**r Address is [r1 + r2 * scale + offset] *)
  | Aglobal: ident -> int -> addressing (**r Address is [symbol + offset] *)
  | Abased: ident -> int -> addressing  (**r Address is [symbol + offset + r1] *)
  | Abasedscaled: int -> ident -> int -> addressing  (**r Address is [symbol + offset + r1 * scale] *)
  | Ainstack: int -> addressing.        (**r Address is [stack_pointer + offset] *)

(** Arithmetic and logical operations.  In the descriptions, [rd] is the
  result of the operation and [r1], [r2], etc, are the arguments. *)

Inductive operation : Type :=
  | Omove: operation                    (**r [rd = r1] *)
  | Ointconst: int -> operation         (**r [rd] is set to the given integer constant *)
  | Ofloatconst: float -> operation     (**r [rd] is set to the given float constant *)
(*c Integer arithmetic: *)
  | Ocast8signed: operation             (**r [rd] is 8-bit sign extension of [r1] *)
  | Ocast8unsigned: operation           (**r [rd] is 8-bit zero extension of [r1] *)
  | Ocast16signed: operation            (**r [rd] is 16-bit sign extension of [r1] *)
  | Ocast16unsigned: operation          (**r [rd] is 16-bit zero extension of [r1] *)
  | Oneg: operation                     (**r [rd = - r1] *)
  | Osub: operation                     (**r [rd = r1 - r2] *)
  | Omul: operation                     (**r [rd = r1 * r2] *)
  | Omulimm: int -> operation           (**r [rd = r1 * n] *)
  | Odiv: operation                     (**r [rd = r1 / r2] (signed) *)
  | Odivu: operation                    (**r [rd = r1 / r2] (unsigned) *)
  | Omod: operation                     (**r [rd = r1 % r2] (signed) *)
  | Omodu: operation                    (**r [rd = r1 % r2] (unsigned) *)
  | Oand: operation                     (**r [rd = r1 & r2] *)
  | Oandimm: int -> operation           (**r [rd = r1 & n] *)
  | Oor: operation                      (**r [rd = r1 | r2] *)
  | Oorimm: int -> operation            (**r [rd = r1 | n] *)
  | Oxor: operation                     (**r [rd = r1 ^ r2] *)
  | Oxorimm: int -> operation           (**r [rd = r1 ^ n] *)
  | Oshl: operation                     (**r [rd = r1 << r2] *)
  | Oshlimm: int -> operation           (**r [rd = r1 << n] *)
  | Oshr: operation                     (**r [rd = r1 >> r2] (signed) *)
  | Oshrimm: int -> operation           (**r [rd = r1 >> n] (signed) *)
  | Oshrximm: int -> operation          (**r [rd = r1 / 2^n] (signed) *)
  | Oshru: operation                    (**r [rd = r1 >> r2] (unsigned) *)
  | Oshruimm: int -> operation          (**r [rd = r1 >> n] (unsigned) *)
  | Ororimm: int -> operation           (**r rotate right immediate *)
  | Olea: addressing -> operation       (**r effective address *)
(*c Floating-point arithmetic: *)
  | Onegf: operation                    (**r [rd = - r1] *)
  | Oabsf: operation                    (**r [rd = abs(r1)] *)
  | Oaddf: operation                    (**r [rd = r1 + r2] *)
  | Osubf: operation                    (**r [rd = r1 - r2] *)
  | Omulf: operation                    (**r [rd = r1 * r2] *)
  | Odivf: operation                    (**r [rd = r1 / r2] *)
  | Osingleoffloat: operation           (**r [rd] is [r1] truncated to single-precision float *)
(*c Conversions between int and float: *)
  | Ointoffloat: operation              (**r [rd = signed_int_of_float(r1)] *)
  | Ofloatofint: operation              (**r [rd = float_of_signed_int(r1)] *)
(*c Boolean tests: *)
  | Ocmp: condition -> operation.       (**r [rd = 1] if condition holds, [rd = 0] otherwise. *)

(** Derived operators. *)

Definition Oaddrsymbol (id: ident) (ofs: int) : operation := Olea (Aglobal id ofs).
Definition Oaddimm (n: int) : operation := Olea (Aindexed n).

(** Comparison functions (used in module [CSE]). *)

Definition eq_addressing (x y: addressing) : {x=y} + {x<>y}.
Proof.
  generalize Int.eq_dec; intro.
  assert (forall (x y: ident), {x=y}+{x<>y}). exact peq.
  decide equality.
Qed.

Definition eq_operation (x y: operation): {x=y} + {x<>y}.
Proof.
  generalize Int.eq_dec; intro.
  generalize Float.eq_dec; intro.
  assert (forall (x y: ident), {x=y}+{x<>y}). exact peq.
  assert (forall (x y: comparison), {x=y}+{x<>y}). decide equality.
  assert (forall (x y: condition), {x=y}+{x<>y}). decide equality.
  decide equality.
  apply eq_addressing.
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

Definition eval_condition (cond: condition) (vl: list val):
               option bool :=
  match cond, vl with
  | Ccomp c, Vint n1 :: Vint n2 :: nil =>
      Some (Int.cmp c n1 n2)
  | Ccomp c, Vptr b1 n1 :: Vptr b2 n2 :: nil =>
      if eq_block b1 b2
      then Some (Int.cmp c n1 n2)
      else eval_compare_mismatch c
  | Ccomp c, Vptr b1 n1 :: Vint n2 :: nil =>
      eval_compare_null c n2
  | Ccomp c, Vint n1 :: Vptr b2 n2 :: nil =>
      eval_compare_null c n1
  | Ccompu c, Vint n1 :: Vint n2 :: nil =>
      Some (Int.cmpu c n1 n2)
  | Ccompimm c n, Vint n1 :: nil =>
      Some (Int.cmp c n1 n)
  | Ccompimm c n, Vptr b1 n1 :: nil =>
      eval_compare_null c n
  | Ccompuimm c n, Vint n1 :: nil =>
      Some (Int.cmpu c n1 n)
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

Definition eval_addressing
    (F V: Type) (genv: Genv.t F V) (sp: val)
    (addr: addressing) (vl: list val) : option val :=
  match addr, vl with
  | Aindexed n, Vint n1 :: nil =>
      Some (Vint (Int.add n1 n))
  | Aindexed n, Vptr b1 n1 :: nil =>
      Some (Vptr b1 (Int.add n1 n))
  | Aindexed2 n, Vint n1 :: Vint n2 :: nil =>
      Some (Vint (Int.add (Int.add n1 n2) n))
  | Aindexed2 n, Vptr b1 n1 :: Vint n2 :: nil =>
      Some (Vptr b1 (Int.add (Int.add n1 n2) n))
  | Aindexed2 n, Vint n1 :: Vptr b2 n2 :: nil =>
      Some (Vptr b2 (Int.add (Int.add n2 n1) n))
  | Ascaled sc ofs, Vint n1 :: nil =>
      Some (Vint (Int.add (Int.mul n1 sc) ofs))
  | Aindexed2scaled sc ofs, Vint n1 :: Vint n2 :: nil =>
      Some (Vint (Int.add n1 (Int.add (Int.mul n2 sc) ofs)))
  | Aindexed2scaled sc ofs, Vptr b1 n1 :: Vint n2 :: nil =>
      Some (Vptr b1 (Int.add n1 (Int.add (Int.mul n2 sc) ofs)))
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
  | Abasedscaled sc s ofs, Vint n1 :: nil =>
      match Genv.find_symbol genv s with
      | None => None
      | Some b => Some (Vptr b (Int.add ofs (Int.mul n1 sc)))
      end
  | Ainstack ofs, nil =>
      offset_sp sp ofs
  | _, _ => None
  end.

Definition eval_operation
    (F V: Type) (genv: Genv.t F V) (sp: val)
    (op: operation) (vl: list val): option val :=
  match op, vl with
  | Omove, v1::nil => Some v1
  | Ointconst n, nil => Some (Vint n)
  | Ofloatconst n, nil => Some (Vfloat n)
  | Ocast8signed, v1 :: nil => Some (Val.sign_ext 8 v1)
  | Ocast8unsigned, v1 :: nil => Some (Val.zero_ext 8 v1)
  | Ocast16signed, v1 :: nil => Some (Val.sign_ext 16 v1)
  | Ocast16unsigned, v1 :: nil => Some (Val.zero_ext 16 v1)
  | Oneg, Vint n1 :: nil => Some (Vint (Int.neg n1))
  | Osub, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.sub n1 n2))
  | Osub, Vptr b1 n1 :: Vint n2 :: nil => Some (Vptr b1 (Int.sub n1 n2))
  | Osub, Vptr b1 n1 :: Vptr b2 n2 :: nil =>
      if eq_block b1 b2 then Some (Vint (Int.sub n1 n2)) else None
  | Omul, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.mul n1 n2))
  | Omulimm n, Vint n1 :: nil => Some (Vint (Int.mul n1 n))
  | Odiv, Vint n1 :: Vint n2 :: nil =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.divs n1 n2))
  | Odivu, Vint n1 :: Vint n2 :: nil =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.divu n1 n2))
  | Omod, Vint n1 :: Vint n2 :: nil =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.mods n1 n2))
  | Omodu, Vint n1 :: Vint n2 :: nil =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.modu n1 n2))
  | Oand, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.and n1 n2))
  | Oandimm n, Vint n1 :: nil => Some (Vint (Int.and n1 n))
  | Oor, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.or n1 n2))
  | Oorimm n, Vint n1 :: nil => Some (Vint (Int.or n1 n))
  | Oxor, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.xor n1 n2))
  | Oxorimm n, Vint n1 :: nil => Some (Vint (Int.xor n1 n))
  | Oshl, Vint n1 :: Vint n2 :: nil =>
      if Int.ltu n2 Int.iwordsize then Some (Vint (Int.shl n1 n2)) else None
  | Oshlimm n, Vint n1 :: nil =>
      if Int.ltu n Int.iwordsize then Some (Vint (Int.shl n1 n)) else None
  | Oshr, Vint n1 :: Vint n2 :: nil =>
      if Int.ltu n2 Int.iwordsize then Some (Vint (Int.shr n1 n2)) else None
  | Oshrimm n, Vint n1 :: nil =>
      if Int.ltu n Int.iwordsize then Some (Vint (Int.shr n1 n)) else None
  | Oshrximm n, Vint n1 :: nil =>
      if Int.ltu n (Int.repr 31) then Some (Vint (Int.shrx n1 n)) else None
  | Oshru, Vint n1 :: Vint n2 :: nil =>
      if Int.ltu n2 Int.iwordsize then Some (Vint (Int.shru n1 n2)) else None
  | Oshruimm n, Vint n1 :: nil =>
      if Int.ltu n Int.iwordsize then Some (Vint (Int.shru n1 n)) else None
  | Ororimm n, Vint n1 :: nil =>
      if Int.ltu n Int.iwordsize then Some (Vint (Int.ror n1 n)) else None
  | Olea addr, _ =>
      eval_addressing genv sp addr vl
  | Onegf, Vfloat f1 :: nil => Some (Vfloat (Float.neg f1))
  | Oabsf, Vfloat f1 :: nil => Some (Vfloat (Float.abs f1))
  | Oaddf, Vfloat f1 :: Vfloat f2 :: nil => Some (Vfloat (Float.add f1 f2))
  | Osubf, Vfloat f1 :: Vfloat f2 :: nil => Some (Vfloat (Float.sub f1 f2))
  | Omulf, Vfloat f1 :: Vfloat f2 :: nil => Some (Vfloat (Float.mul f1 f2))
  | Odivf, Vfloat f1 :: Vfloat f2 :: nil => Some (Vfloat (Float.div f1 f2))
  | Osingleoffloat, v1 :: nil =>
      Some (Val.singleoffloat v1)
  | Ointoffloat, Vfloat f1 :: nil => 
      option_map Vint (Float.intoffloat f1)
  | Ofloatofint, Vint n1 :: nil => 
      Some (Vfloat (Float.floatofint n1))
  | Ocmp c, _ =>
      match eval_condition c vl with
      | None => None
      | Some false => Some Vfalse
      | Some true => Some Vtrue
      end
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
  forall (cond: condition) (vl: list val) (b: bool),
  eval_condition cond vl = Some b ->
  eval_condition (negate_condition cond) vl = Some (negb b).
Proof.
  intros. 
  destruct cond; simpl in H; FuncInv; try subst b; simpl.
  rewrite Int.negate_cmp. auto.
  apply eval_negate_compare_null; auto.
  apply eval_negate_compare_null; auto.
  destruct (eq_block b0 b1). rewrite Int.negate_cmp. congruence.
  apply eval_negate_compare_mismatch; auto. 
  rewrite Int.negate_cmpu. auto.
  rewrite Int.negate_cmp. auto.
  apply eval_negate_compare_null; auto.
  rewrite Int.negate_cmpu. auto.
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

Lemma eval_addressing_preserved:
  forall sp addr vl,
  eval_addressing ge2 sp addr vl = eval_addressing ge1 sp addr vl.
Proof.
  intros.
  unfold eval_addressing; destruct addr; try rewrite agree_on_symbols;
  reflexivity.
Qed.

Lemma eval_operation_preserved:
  forall sp op vl,
  eval_operation ge2 sp op vl = eval_operation ge1 sp op vl.
Proof.
  intros.
  unfold eval_operation; destruct op; try rewrite agree_on_symbols; auto.
  apply eval_addressing_preserved.
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

Definition type_of_addressing (addr: addressing) : list typ :=
  match addr with
  | Aindexed _ => Tint :: nil
  | Aindexed2 _ => Tint :: Tint :: nil
  | Ascaled _ _ => Tint :: nil
  | Aindexed2scaled _ _ => Tint :: Tint :: nil
  | Aglobal _ _ => nil
  | Abased _ _ => Tint :: nil
  | Abasedscaled _ _ _ => Tint :: nil
  | Ainstack _ => nil
  end.

Definition type_of_operation (op: operation) : list typ * typ :=
  match op with
  | Omove => (nil, Tint)   (* treated specially *)
  | Ointconst _ => (nil, Tint)
  | Ofloatconst _ => (nil, Tfloat)
  | Ocast8signed => (Tint :: nil, Tint)
  | Ocast8unsigned => (Tint :: nil, Tint)
  | Ocast16signed => (Tint :: nil, Tint)
  | Ocast16unsigned => (Tint :: nil, Tint)
  | Oneg => (Tint :: nil, Tint)
  | Osub => (Tint :: Tint :: nil, Tint)
  | Omul => (Tint :: Tint :: nil, Tint)
  | Omulimm _ => (Tint :: nil, Tint)
  | Odiv => (Tint :: Tint :: nil, Tint)
  | Odivu => (Tint :: Tint :: nil, Tint)
  | Omod => (Tint :: Tint :: nil, Tint)
  | Omodu => (Tint :: Tint :: nil, Tint)
  | Oand => (Tint :: Tint :: nil, Tint)
  | Oandimm _ => (Tint :: nil, Tint)
  | Oor => (Tint :: Tint :: nil, Tint)
  | Oorimm _ => (Tint :: nil, Tint)
  | Oxor => (Tint :: Tint :: nil, Tint)
  | Oxorimm _ => (Tint :: nil, Tint)
  | Oshl => (Tint :: Tint :: nil, Tint)
  | Oshlimm _ => (Tint :: nil, Tint)
  | Oshr => (Tint :: Tint :: nil, Tint)
  | Oshrimm _ => (Tint :: nil, Tint)
  | Oshrximm _ => (Tint :: nil, Tint)
  | Oshru => (Tint :: Tint :: nil, Tint)
  | Oshruimm _ => (Tint :: nil, Tint)
  | Ororimm _ => (Tint :: nil, Tint)
  | Olea addr => (type_of_addressing addr, Tint)
  | Onegf => (Tfloat :: nil, Tfloat)
  | Oabsf => (Tfloat :: nil, Tfloat)
  | Oaddf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Osubf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Omulf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Odivf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Osingleoffloat => (Tfloat :: nil, Tfloat)
  | Ointoffloat => (Tfloat :: nil, Tint)
  | Ofloatofint => (Tint :: nil, Tfloat)
  | Ocmp c => (type_of_condition c, Tint)
  end.

(** Weak type soundness results for [eval_operation]:
  the result values, when defined, are always of the type predicted
  by [type_of_operation]. *)

Section SOUNDNESS.

Variable A V: Type.
Variable genv: Genv.t A V.

Lemma type_of_addressing_sound:
  forall addr vl sp v,
  eval_addressing genv sp addr vl = Some v ->
  Val.has_type v Tint.
Proof.
  intros. destruct addr; simpl in H; FuncInv; try subst v; try exact I.
  destruct (Genv.find_symbol genv i); inv H; exact I.
  destruct (Genv.find_symbol genv i); inv H; exact I.
  destruct (Genv.find_symbol genv i0); inv H; exact I.
  unfold offset_sp in H. destruct sp; inv H; exact I.
Qed.

Lemma type_of_operation_sound:
  forall op vl sp v,
  op <> Omove ->
  eval_operation genv sp op vl = Some v ->
  Val.has_type v (snd (type_of_operation op)).
Proof.
  intros.
  destruct op; simpl in H0; FuncInv; try subst v; try exact I.
  congruence.
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
  destruct (Int.eq i0 Int.zero). discriminate. 
  injection H0; intro; subst v; exact I.
  destruct (Int.eq i0 Int.zero). discriminate. 
  injection H0; intro; subst v; exact I.
  destruct (Int.ltu i0 Int.iwordsize).
  injection H0; intro; subst v; exact I. discriminate.
  destruct (Int.ltu i Int.iwordsize).
  injection H0; intro; subst v; exact I. discriminate.
  destruct (Int.ltu i0 Int.iwordsize).
  injection H0; intro; subst v; exact I. discriminate.
  destruct (Int.ltu i Int.iwordsize).
  injection H0; intro; subst v; exact I. discriminate.
  destruct (Int.ltu i (Int.repr 31)). 
  injection H0; intro; subst v; exact I. discriminate.
  destruct (Int.ltu i0 Int.iwordsize).
  injection H0; intro; subst v; exact I. discriminate.
  destruct (Int.ltu i Int.iwordsize).
  injection H0; intro; subst v; exact I. discriminate.
  destruct (Int.ltu i Int.iwordsize).
  injection H0; intro; subst v; exact I. discriminate.
  simpl. eapply type_of_addressing_sound; eauto.
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

Definition eval_addressing_total
    (sp: val) (addr: addressing) (vl: list val) : val :=
  match addr, vl with
  | Aindexed n, v1::nil => Val.add v1 (Vint n)
  | Aindexed2 n, v1::v2::nil => Val.add (Val.add v1 v2) (Vint n)
  | Ascaled sc ofs, v1::nil => Val.add (Val.mul v1 (Vint sc)) (Vint ofs)
  | Aindexed2scaled sc ofs, v1::v2::nil =>
      Val.add v1 (Val.add (Val.mul v2 (Vint sc)) (Vint ofs))
  | Aglobal s ofs, nil => find_symbol_offset s ofs
  | Abased s ofs, v1::nil => Val.add (find_symbol_offset s ofs) v1
  | Abasedscaled sc s ofs, v1::nil => Val.add (find_symbol_offset s ofs) (Val.mul v1 (Vint sc))
  | Ainstack ofs, nil => Val.add sp (Vint ofs)
  | _, _ => Vundef
  end.

Definition eval_operation_total (sp: val) (op: operation) (vl: list val) : val :=
  match op, vl with
  | Omove, v1::nil => v1
  | Ointconst n, nil => Vint n
  | Ofloatconst n, nil => Vfloat n
  | Ocast8signed, v1::nil => Val.sign_ext 8 v1
  | Ocast8unsigned, v1::nil => Val.zero_ext 8 v1
  | Ocast16signed, v1::nil => Val.sign_ext 16 v1
  | Ocast16unsigned, v1::nil => Val.zero_ext 16 v1
  | Oneg, v1::nil => Val.neg v1
  | Osub, v1::v2::nil => Val.sub v1 v2
  | Omul, v1::v2::nil => Val.mul v1 v2
  | Omulimm n, v1::nil => Val.mul v1 (Vint n)
  | Odiv, v1::v2::nil => Val.divs v1 v2
  | Odivu, v1::v2::nil => Val.divu v1 v2
  | Omod, v1::v2::nil => Val.mods v1 v2
  | Omodu, v1::v2::nil => Val.modu v1 v2
  | Oand, v1::v2::nil => Val.and v1 v2
  | Oandimm n, v1::nil => Val.and v1 (Vint n)
  | Oor, v1::v2::nil => Val.or v1 v2
  | Oorimm n, v1::nil => Val.or v1 (Vint n)
  | Oxor, v1::v2::nil => Val.xor v1 v2
  | Oxorimm n, v1::nil => Val.xor v1 (Vint n)
  | Oshl, v1::v2::nil => Val.shl v1 v2
  | Oshlimm n, v1::nil => Val.shl v1 (Vint n)
  | Oshr, v1::v2::nil => Val.shr v1 v2
  | Oshrimm n, v1::nil => Val.shr v1 (Vint n)
  | Oshrximm n, v1::nil => Val.shrx v1 (Vint n)
  | Oshru, v1::v2::nil => Val.shru v1 v2
  | Oshruimm n, v1::nil => Val.shru v1 (Vint n)
  | Ororimm n, v1::nil => Val.ror v1 (Vint n)
  | Olea addr, _ => eval_addressing_total sp addr vl
  | Onegf, v1::nil => Val.negf v1
  | Oabsf, v1::nil => Val.absf v1
  | Oaddf, v1::v2::nil => Val.addf v1 v2
  | Osubf, v1::v2::nil => Val.subf v1 v2
  | Omulf, v1::v2::nil => Val.mulf v1 v2
  | Odivf, v1::v2::nil => Val.divf v1 v2
  | Osingleoffloat, v1::nil => Val.singleoffloat v1
  | Ointoffloat, v1::nil => Val.intoffloat v1
  | Ofloatofint, v1::nil => Val.floatofint v1
  | Ocmp c, _ => eval_condition_total c vl
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
  forall c vl b,
  eval_condition c vl = Some b ->
  eval_condition_total c vl = Val.of_bool b.
Proof.
  intros. 
  unfold eval_condition in H; destruct c; FuncInv;
  try subst b; try reflexivity; simpl;
  try (apply eval_compare_null_weaken; auto).
  unfold eq_block in H. destruct (zeq b0 b1).
  congruence.
  apply eval_compare_mismatch_weaken; auto.
  symmetry. apply Val.notbool_negb_1. 
  symmetry. apply Val.notbool_negb_1. 
Qed.

Lemma eval_addressing_weaken:
  forall sp addr vl v,
  eval_addressing genv sp addr vl = Some v ->
  eval_addressing_total sp addr vl = v.
Proof.
  intros.
  unfold eval_addressing in H; destruct addr; FuncInv;
  try subst v; simpl; try reflexivity.
  unfold find_symbol_offset. destruct (Genv.find_symbol genv i); congruence.
  unfold find_symbol_offset. destruct (Genv.find_symbol genv i); simpl; congruence.
  unfold find_symbol_offset. destruct (Genv.find_symbol genv i0); simpl; congruence.
  unfold offset_sp in H. destruct sp; simpl; congruence.
Qed.

Lemma eval_operation_weaken:
  forall sp op vl v,
  eval_operation genv sp op vl = Some v ->
  eval_operation_total sp op vl = v.
Proof.
  intros.
  unfold eval_operation in H; destruct op; FuncInv;
  try subst v; try reflexivity; simpl.
  unfold eq_block in H. destruct (zeq b b0); congruence.
  destruct (Int.eq i0 Int.zero); congruence.
  destruct (Int.eq i0 Int.zero); congruence.
  destruct (Int.eq i0 Int.zero); congruence.
  destruct (Int.eq i0 Int.zero); congruence.
  destruct (Int.ltu i0 Int.iwordsize); congruence.
  destruct (Int.ltu i Int.iwordsize); congruence.
  destruct (Int.ltu i0 Int.iwordsize); congruence.
  destruct (Int.ltu i Int.iwordsize); congruence.
  unfold Int.ltu in *. destruct (zlt (Int.unsigned i) (Int.unsigned (Int.repr 31))).
  rewrite zlt_true. congruence. eapply Zlt_trans. eauto. compute; auto.
  congruence.
  destruct (Int.ltu i0 Int.iwordsize); congruence.
  destruct (Int.ltu i Int.iwordsize); congruence.
  destruct (Int.ltu i Int.iwordsize); congruence.
  apply eval_addressing_weaken; auto.
  destruct (Float.intoffloat f); simpl in H; inv H. auto.
  caseEq (eval_condition c vl); intros; rewrite H0 in H.
  replace v with (Val.of_bool b).
  eapply eval_condition_weaken; eauto.
  destruct b; simpl; congruence.
  discriminate.
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
  forall cond vl1 vl2 b,
  Val.lessdef_list vl1 vl2 ->
  eval_condition cond vl1 = Some b ->
  eval_condition cond vl2 = Some b.
Proof.
  intros. destruct cond; simpl in *; FuncInv; InvLessdef; auto.
Qed.

Ltac TrivialExists :=
  match goal with
  | [ |- exists v2, Some ?v1 = Some v2 /\ Val.lessdef ?v1 v2 ] =>
      exists v1; split; [auto | constructor]
  | _ => idtac
  end.

Lemma eval_addressing_lessdef:
  forall sp addr vl1 vl2 v1,
  Val.lessdef_list vl1 vl2 ->
  eval_addressing genv sp addr vl1 = Some v1 ->
  exists v2, eval_addressing genv sp addr vl2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. destruct addr; simpl in *; FuncInv; InvLessdef; TrivialExists.
  destruct (Genv.find_symbol genv i); inv H0. TrivialExists.
  destruct (Genv.find_symbol genv i); inv H0. TrivialExists.
  destruct (Genv.find_symbol genv i0); inv H0. TrivialExists.
  exists v1; auto.
Qed.

Lemma eval_operation_lessdef:
  forall sp op vl1 vl2 v1,
  Val.lessdef_list vl1 vl2 ->
  eval_operation genv sp op vl1 = Some v1 ->
  exists v2, eval_operation genv sp op vl2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. destruct op; simpl in *; FuncInv; InvLessdef; TrivialExists.
  exists v2; auto.
  exists (Val.sign_ext 8 v2); split. auto. apply Val.sign_ext_lessdef; auto.
  exists (Val.zero_ext 8 v2); split. auto. apply Val.zero_ext_lessdef; auto.
  exists (Val.sign_ext 16 v2); split. auto. apply Val.sign_ext_lessdef; auto.
  exists (Val.zero_ext 16 v2); split. auto. apply Val.zero_ext_lessdef; auto.
  destruct (eq_block b b0); inv H0. TrivialExists.
  destruct (Int.eq i0 Int.zero); inv H0; TrivialExists.
  destruct (Int.eq i0 Int.zero); inv H0; TrivialExists.
  destruct (Int.eq i0 Int.zero); inv H0; TrivialExists.
  destruct (Int.eq i0 Int.zero); inv H0; TrivialExists.
  destruct (Int.ltu i0 Int.iwordsize); inv H0; TrivialExists.
  destruct (Int.ltu i Int.iwordsize); inv H0; TrivialExists.
  destruct (Int.ltu i0 Int.iwordsize); inv H0; TrivialExists.
  destruct (Int.ltu i Int.iwordsize); inv H0; TrivialExists.
  destruct (Int.ltu i (Int.repr 31)); inv H0; TrivialExists.
  destruct (Int.ltu i0 Int.iwordsize); inv H0; TrivialExists.
  destruct (Int.ltu i Int.iwordsize); inv H0; TrivialExists.
  destruct (Int.ltu i Int.iwordsize); inv H0; TrivialExists.
  eapply eval_addressing_lessdef; eauto.
  exists (Val.singleoffloat v2); split. auto. apply Val.singleoffloat_lessdef; auto.
  exists v1; split; auto. 
  caseEq (eval_condition c vl1); intros. rewrite H1 in H0. 
  rewrite (eval_condition_lessdef c H H1).
  destruct b; inv H0; TrivialExists.
  rewrite H1 in H0. discriminate.
Qed.

End EVAL_LESSDEF.

(** Transformation of addressing modes with two operands or more
  into an equivalent arithmetic operation.  This is used in the [Reload]
  pass when a store instruction cannot be reloaded directly because
  it runs out of temporary registers. *)

Definition op_for_binary_addressing (addr: addressing) : operation := Olea addr.

Lemma eval_op_for_binary_addressing:
  forall (F V: Type) (ge: Genv.t F V) sp addr args v,
  (length args >= 2)%nat ->
  eval_addressing ge sp addr args = Some v ->
  eval_operation ge sp (op_for_binary_addressing addr) args = Some v.
Proof.
  intros. simpl. auto.
Qed.

Lemma type_op_for_binary_addressing:
  forall addr,
  (length (type_of_addressing addr) >= 2)%nat ->
  type_of_operation (op_for_binary_addressing addr) = (type_of_addressing addr, Tint).
Proof.
  intros. simpl. auto.
Qed.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location. *)

Definition two_address_op (op: operation) : bool :=
  match op with
  | Omove => false
  | Ointconst _ => false
  | Ofloatconst _ => false
  | Ocast8signed => false
  | Ocast8unsigned => false
  | Ocast16signed => false
  | Ocast16unsigned => false
  | Oneg => true
  | Osub => true
  | Omul => true
  | Omulimm _ => true
  | Odiv => true
  | Odivu => true
  | Omod => true
  | Omodu => true
  | Oand => true
  | Oandimm _ => true
  | Oor => true
  | Oorimm _ => true
  | Oxor => true
  | Oxorimm _ => true
  | Oshl => true
  | Oshlimm _ => true
  | Oshr => true
  | Oshrimm _ => true
  | Oshrximm _ => true
  | Oshru => true
  | Oshruimm _ => true
  | Ororimm _ => true
  | Olea addr => false
  | Onegf => true
  | Oabsf => true
  | Oaddf => true
  | Osubf => true
  | Omulf => true
  | Odivf => true
  | Osingleoffloat => false
  | Ointoffloat => false
  | Ofloatofint => false
  | Ocmp c => false
  end.

(** Operations that are so cheap to recompute that CSE should not factor them out. *)

Definition is_trivial_op (op: operation) : bool :=
  match op with
  | Omove => true
  | Ointconst _ => true
  | Olea (Aglobal _ _) => true
  | Olea (Ainstack _) => true
  | _ => false
  end.

(** Shifting stack-relative references.  This is used in [Stacking]. *)

Definition shift_stack_addressing (delta: int) (addr: addressing) :=
  match addr with
  | Ainstack ofs => Ainstack (Int.add delta ofs)
  | _ => addr
  end.

Definition shift_stack_operation (delta: int) (op: operation) :=
  match op with
  | Olea addr => Olea (shift_stack_addressing delta addr)
  | _ => op
  end.

Lemma shift_stack_eval_addressing:
  forall (F V: Type) (ge: Genv.t F V) sp addr args delta,
  eval_addressing ge (Val.sub sp (Vint delta)) (shift_stack_addressing delta addr) args =
  eval_addressing ge sp addr args.
Proof.
  intros. destruct addr; simpl; auto. 
  destruct args; auto. unfold offset_sp. destruct sp; simpl; auto. 
  decEq. decEq. rewrite <- Int.add_assoc. decEq. 
  rewrite Int.sub_add_opp. rewrite Int.add_assoc.
  rewrite (Int.add_commut (Int.neg delta)). rewrite <- Int.sub_add_opp. 
  rewrite Int.sub_idem. apply Int.add_zero. 
Qed.

Lemma shift_stack_eval_operation:
  forall (F V: Type) (ge: Genv.t F V) sp op args delta,
  eval_operation ge (Val.sub sp (Vint delta)) (shift_stack_operation delta op) args =
  eval_operation ge sp op args.
Proof.
  intros. destruct op; simpl; auto.
  apply shift_stack_eval_addressing. 
Qed.

Lemma type_shift_stack_addressing:
  forall delta addr, type_of_addressing (shift_stack_addressing delta addr) = type_of_addressing addr.
Proof.
  intros. destruct addr; auto. 
Qed.

Lemma type_shift_stack_operation:
  forall delta op, type_of_operation (shift_stack_operation delta op) = type_of_operation op.
Proof.
  intros. destruct op; auto. simpl. decEq. apply type_shift_stack_addressing. 
Qed.



