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

  These types are processor-specific and correspond roughly to what the 
  processor can compute in one instruction.  In other terms, these
  types reflect the state of the program after instruction selection.
  For a processor-independent set of operations, see the abstract
  syntax and dynamic semantics of the Cminor language.
*)

Require Import Axioms.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.

Set Implicit Arguments.

Record shift_amount: Type := 
  { s_amount: int;
    s_range: Int.ltu s_amount Int.iwordsize = true }.

Coercion s_amount: shift_amount >-> int.

Inductive shift : Type :=
  | Slsl: shift_amount -> shift
  | Slsr: shift_amount -> shift
  | Sasr: shift_amount -> shift
  | Sror: shift_amount -> shift.

(** Conditions (boolean-valued operators). *)

Inductive condition : Type :=
  | Ccomp: comparison -> condition  (**r signed integer comparison *)
  | Ccompu: comparison -> condition (**r unsigned integer comparison *)
  | Ccompshift: comparison -> shift -> condition  (**r signed integer comparison *)
  | Ccompushift: comparison -> shift -> condition (**r unsigned integer comparison *)
  | Ccompimm: comparison -> int -> condition (**r signed integer comparison with a constant *)
  | Ccompuimm: comparison -> int -> condition (**r unsigned integer comparison with a constant *)
  | Ccompf: comparison -> condition     (**r floating-point comparison *)
  | Cnotcompf: comparison -> condition (**r negation of a floating-point comparison *)
  | Ccompfzero: comparison -> condition     (**r floating-point comparison with 0.0 *)
  | Cnotcompfzero: comparison -> condition. (**r negation of a floating-point comparison with 0.0 *)


(** Arithmetic and logical operations.  In the descriptions, [rd] is the
  result of the operation and [r1], [r2], etc, are the arguments. *)

Inductive operation : Type :=
  | Omove: operation                    (**r [rd = r1] *)
  | Ointconst: int -> operation         (**r [rd] is set to the given integer constant *)
  | Ofloatconst: float -> operation     (**r [rd] is set to the given float constant *)
  | Oaddrsymbol: ident -> int -> operation (**r [rd] is set to the the address of the symbol plus the offset *)
  | Oaddrstack: int -> operation        (**r [rd] is set to the stack pointer plus the given offset *)
(*c Integer arithmetic: *)
  | Oadd: operation                     (**r [rd = r1 + r2] *)
  | Oaddshift: shift -> operation       (**r [rd = r1 + shifted r2] *)
  | Oaddimm: int -> operation           (**r [rd = r1 + n] *)
  | Osub: operation                     (**r [rd = r1 - r2] *)
  | Osubshift: shift -> operation       (**r [rd = r1 - shifted r2] *)
  | Orsubshift: shift -> operation      (**r [rd = shifted r2 - r1] *)
  | Orsubimm: int -> operation          (**r [rd = n - r1] *)
  | Omul: operation                     (**r [rd = r1 * r2] *)
  | Odiv: operation                     (**r [rd = r1 / r2] (signed) *)
  | Odivu: operation                    (**r [rd = r1 / r2] (unsigned) *)
  | Oand: operation                     (**r [rd = r1 & r2] *)
  | Oandshift: shift -> operation       (**r [rd = r1 & shifted r2] *)
  | Oandimm: int -> operation           (**r [rd = r1 & n] *)
  | Oor: operation                      (**r [rd = r1 | r2] *)
  | Oorshift: shift -> operation        (**r [rd = r1 | shifted r2] *)
  | Oorimm: int -> operation            (**r [rd = r1 | n] *)
  | Oxor: operation                     (**r [rd = r1 ^ r2] *)
  | Oxorshift: shift -> operation       (**r [rd = r1 ^ shifted r2] *)
  | Oxorimm: int -> operation           (**r [rd = r1 ^ n] *)
  | Obic: operation                     (**r [rd = r1 & ~r2] *)
  | Obicshift: shift -> operation       (**r [rd = r1 & ~(shifted r2)] *)
  | Onot: operation                     (**r [rd = ~r1] *)
  | Onotshift: shift -> operation       (**r [rd = ~(shifted r1)] *)
  | Oshl: operation                     (**r [rd = r1 << r2] *)
  | Oshr: operation                     (**r [rd = r1 >> r2] (signed) *)
  | Oshru: operation                    (**r [rd = r1 >> r2] (unsigned) *)
  | Oshift: shift -> operation          (**r [rd = shifted r1] *)
  | Oshrximm: int -> operation          (**r [rd = r1 / 2^n] (signed) *)
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
  | Ointuoffloat: operation             (**r [rd = unsigned_int_of_float(r1)] *)
  | Ofloatofint: operation              (**r [rd = float_of_signed_int(r1)] *)
  | Ofloatofintu: operation             (**r [rd = float_of_unsigned_int(r1)] *)
(*c Boolean tests: *)
  | Ocmp: condition -> operation.       (**r [rd = 1] if condition holds, [rd = 0] otherwise. *)

(** Addressing modes.  [r1], [r2], etc, are the arguments to the 
  addressing. *)

Inductive addressing: Type :=
  | Aindexed: int -> addressing         (**r Address is [r1 + offset] *)
  | Aindexed2: addressing               (**r Address is [r1 + r2] *)
  | Aindexed2shift: shift -> addressing (**r Address is [r1 + shifted r2] *)
  | Ainstack: int -> addressing.        (**r Address is [stack_pointer + offset] *)

(** Comparison functions (used in module [CSE]). *)

Definition eq_shift (x y: shift): {x=y} + {x<>y}.
Proof.
  revert x y.
  generalize Int.eq_dec; intro.
  assert (forall (x y: shift_amount), {x=y}+{x<>y}).
  destruct x as [x Px]. destruct y as [y Py]. destruct (H x y).
  subst x. rewrite (proof_irr Px Py). left; auto.
  right. red; intro. elim n. inversion H0. auto.
  decide equality.
Qed.

Definition eq_operation (x y: operation): {x=y} + {x<>y}.
Proof.
  generalize Int.eq_dec; intro.
  generalize Float.eq_dec; intro.
  assert (forall (x y: ident), {x=y}+{x<>y}). exact peq.
  generalize eq_shift; intro.
  assert (forall (x y: comparison), {x=y}+{x<>y}). decide equality.
  assert (forall (x y: condition), {x=y}+{x<>y}). decide equality.
  decide equality.
Qed.

Definition eq_addressing (x y: addressing) : {x=y} + {x<>y}.
Proof.
  generalize Int.eq_dec; intro.
  generalize eq_shift; intro.
  decide equality.
Qed.

(** * Evaluation functions *)

Definition symbol_address (F V: Type) (genv: Genv.t F V) (id: ident) (ofs: int) : val :=
  match Genv.find_symbol genv id with
  | Some b => Vptr b ofs
  | None => Vundef
  end.

(** Evaluation of conditions, operators and addressing modes applied
  to lists of values.  Return [None] when the computation can trigger an
  error, e.g. integer division by zero.  [eval_condition] returns a boolean,
  [eval_operation] and [eval_addressing] return a value. *)

Definition eval_shift (s: shift) (v: val) : val :=
  match s with
  | Slsl x => Val.shl v (Vint x)
  | Slsr x => Val.shru v (Vint x)
  | Sasr x => Val.shr v (Vint x)
  | Sror x => Val.ror v (Vint x)
  end.

Definition eval_condition (cond: condition) (vl: list val) (m: mem):
               option bool :=
  match cond, vl with
  | Ccomp c, v1 :: v2 :: nil => Val.cmp_bool c v1 v2
  | Ccompu c, v1 :: v2 :: nil => Val.cmpu_bool (Mem.valid_pointer m) c v1 v2
  | Ccompshift c s, v1 :: v2 :: nil => Val.cmp_bool c v1 (eval_shift s v2)
  | Ccompushift c s, v1 :: v2 :: nil => Val.cmpu_bool (Mem.valid_pointer m) c v1 (eval_shift s v2)
  | Ccompimm c n, v1 :: nil => Val.cmp_bool c v1 (Vint n)
  | Ccompuimm c n, v1 :: nil => Val.cmpu_bool (Mem.valid_pointer m) c v1 (Vint n)
  | Ccompf c, v1 :: v2 :: nil => Val.cmpf_bool c v1 v2
  | Cnotcompf c, v1 :: v2 :: nil => option_map negb (Val.cmpf_bool c v1 v2)
  | Ccompfzero c, v1 :: nil => Val.cmpf_bool c v1 (Vfloat Float.zero)
  | Cnotcompfzero c, v1 :: nil => option_map negb (Val.cmpf_bool c v1 (Vfloat Float.zero))
  | _, _ => None
  end.

Definition eval_operation
    (F V: Type) (genv: Genv.t F V) (sp: val)
    (op: operation) (vl: list val) (m: mem): option val :=
  match op, vl with
  | Omove, v1::nil => Some v1
  | Ointconst n, nil => Some (Vint n)
  | Ofloatconst n, nil => Some (Vfloat n)
  | Oaddrsymbol s ofs, nil => Some (symbol_address genv s ofs)
  | Oaddrstack ofs, nil => Some (Val.add sp (Vint ofs))
  | Oadd, v1 :: v2 :: nil => Some (Val.add v1 v2)
  | Oaddshift s, v1 :: v2 :: nil => Some (Val.add v1 (eval_shift s v2))
  | Oaddimm n, v1 :: nil => Some (Val.add v1 (Vint n))
  | Osub, v1 :: v2 :: nil => Some (Val.sub v1 v2)
  | Osubshift s, v1 :: v2 :: nil => Some (Val.sub v1 (eval_shift s v2))
  | Orsubshift s, v1 :: v2 :: nil => Some (Val.sub (eval_shift s v2) v1)
  | Orsubimm n, v1 :: nil => Some (Val.sub (Vint n) v1)
  | Omul, v1 :: v2 :: nil => Some (Val.mul v1 v2)
  | Odiv, v1 :: v2 :: nil => Val.divs v1 v2
  | Odivu, v1 :: v2 :: nil => Val.divu v1 v2
  | Oand, v1 :: v2 :: nil => Some (Val.and v1 v2)
  | Oandshift s, v1 :: v2 :: nil => Some (Val.and v1 (eval_shift s v2))
  | Oandimm n, v1 :: nil => Some (Val.and v1 (Vint n))
  | Oor, v1 :: v2 :: nil => Some (Val.or v1 v2)
  | Oorshift s, v1 :: v2 :: nil => Some (Val.or v1 (eval_shift s v2))
  | Oorimm n, v1 :: nil => Some (Val.or v1 (Vint n))
  | Oxor, v1 :: v2 :: nil => Some (Val.xor v1 v2)
  | Oxorshift s, v1 :: v2 :: nil => Some (Val.xor v1 (eval_shift s v2))
  | Oxorimm n, v1 :: nil => Some (Val.xor v1 (Vint n))
  | Obic, v1 :: v2 :: nil => Some (Val.and v1 (Val.notint v2))
  | Obicshift s, v1 :: v2 :: nil => Some (Val.and v1 (Val.notint (eval_shift s v2)))
  | Onot, v1 :: nil => Some (Val.notint v1)
  | Onotshift s, v1 :: nil => Some (Val.notint (eval_shift s v1))
  | Oshl, v1 :: v2 :: nil => Some (Val.shl v1 v2)
  | Oshr, v1 :: v2 :: nil => Some (Val.shr v1 v2)
  | Oshru, v1 :: v2 :: nil => Some (Val.shru v1 v2)
  | Oshift s, v1 :: nil => Some (eval_shift s v1)
  | Oshrximm n, v1 :: nil => Val.shrx v1 (Vint n)
  | Onegf, v1::nil => Some(Val.negf v1)
  | Oabsf, v1::nil => Some(Val.absf v1)
  | Oaddf, v1::v2::nil => Some(Val.addf v1 v2)
  | Osubf, v1::v2::nil => Some(Val.subf v1 v2)
  | Omulf, v1::v2::nil => Some(Val.mulf v1 v2)
  | Odivf, v1::v2::nil => Some(Val.divf v1 v2)
  | Osingleoffloat, v1::nil => Some(Val.singleoffloat v1)
  | Ointoffloat, v1::nil => Val.intoffloat v1
  | Ointuoffloat, v1::nil => Val.intuoffloat v1
  | Ofloatofint, v1::nil => Val.floatofint v1
  | Ofloatofintu, v1::nil => Val.floatofintu v1
  | Ocmp c, _ => Some(Val.of_optbool (eval_condition c vl m))
  | _, _ => None
  end.

Definition eval_addressing
    (F V: Type) (genv: Genv.t F V) (sp: val)
    (addr: addressing) (vl: list val) : option val :=
  match addr, vl with
  | Aindexed n, v1 :: nil => Some (Val.add v1 (Vint n))
  | Aindexed2, v1 :: v2 :: nil => Some (Val.add v1 v2)
  | Aindexed2shift s, v1 :: v2 :: nil => Some (Val.add v1 (eval_shift s v2))
  | Ainstack ofs, nil => Some (Val.add sp (Vint ofs))
  | _, _ => None
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

(** * Static typing of conditions, operators and addressing modes. *)

Definition type_of_condition (c: condition) : list typ :=
  match c with
  | Ccomp _ => Tint :: Tint :: nil
  | Ccompu _ => Tint :: Tint :: nil
  | Ccompshift _ _ => Tint :: Tint :: nil
  | Ccompushift _ _ => Tint :: Tint :: nil
  | Ccompimm _ _ => Tint :: nil
  | Ccompuimm _ _ => Tint :: nil
  | Ccompf _ => Tfloat :: Tfloat :: nil
  | Cnotcompf _ => Tfloat :: Tfloat :: nil
  | Ccompfzero _ => Tfloat :: nil
  | Cnotcompfzero _ => Tfloat :: nil
  end.

Definition type_of_operation (op: operation) : list typ * typ :=
  match op with
  | Omove => (nil, Tint)   (* treated specially *)
  | Ointconst _ => (nil, Tint)
  | Ofloatconst _ => (nil, Tfloat)
  | Oaddrsymbol _ _ => (nil, Tint)
  | Oaddrstack _ => (nil, Tint)
  | Oadd => (Tint :: Tint :: nil, Tint)
  | Oaddshift _ => (Tint :: Tint :: nil, Tint)
  | Oaddimm _ => (Tint :: nil, Tint)
  | Osub => (Tint :: Tint :: nil, Tint)
  | Osubshift _ => (Tint :: Tint :: nil, Tint)
  | Orsubshift _ => (Tint :: Tint :: nil, Tint)
  | Orsubimm _ => (Tint :: nil, Tint)
  | Omul => (Tint :: Tint :: nil, Tint)
  | Odiv => (Tint :: Tint :: nil, Tint)
  | Odivu => (Tint :: Tint :: nil, Tint)
  | Oand => (Tint :: Tint :: nil, Tint)
  | Oandshift _ => (Tint :: Tint :: nil, Tint)
  | Oandimm _ => (Tint :: nil, Tint)
  | Oor => (Tint :: Tint :: nil, Tint)
  | Oorshift _ => (Tint :: Tint :: nil, Tint)
  | Oorimm _ => (Tint :: nil, Tint)
  | Oxor => (Tint :: Tint :: nil, Tint)
  | Oxorshift _ => (Tint :: Tint :: nil, Tint)
  | Oxorimm _ => (Tint :: nil, Tint)
  | Obic => (Tint :: Tint :: nil, Tint)
  | Obicshift _ => (Tint :: Tint :: nil, Tint)
  | Onot => (Tint :: nil, Tint)
  | Onotshift _ => (Tint :: nil, Tint)
  | Oshl => (Tint :: Tint :: nil, Tint)
  | Oshr => (Tint :: Tint :: nil, Tint)
  | Oshru => (Tint :: Tint :: nil, Tint)
  | Oshift _ => (Tint :: nil, Tint)
  | Oshrximm _ => (Tint :: nil, Tint)
  | Onegf => (Tfloat :: nil, Tfloat)
  | Oabsf => (Tfloat :: nil, Tfloat)
  | Oaddf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Osubf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Omulf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Odivf => (Tfloat :: Tfloat :: nil, Tfloat)
  | Osingleoffloat => (Tfloat :: nil, Tfloat)
  | Ointoffloat => (Tfloat :: nil, Tint)
  | Ointuoffloat => (Tfloat :: nil, Tint)
  | Ofloatofint => (Tint :: nil, Tfloat)
  | Ofloatofintu => (Tint :: nil, Tfloat)
  | Ocmp c => (type_of_condition c, Tint)
  end.

Definition type_of_addressing (addr: addressing) : list typ :=
  match addr with
  | Aindexed _ => Tint :: nil
  | Aindexed2 => Tint :: Tint :: nil
  | Aindexed2shift _ => Tint :: Tint :: nil
  | Ainstack _ => nil
  end.

Definition type_of_chunk (c: memory_chunk) : typ :=
  match c with
  | Mint8signed => Tint
  | Mint8unsigned => Tint
  | Mint16signed => Tint
  | Mint16unsigned => Tint
  | Mint32 => Tint
  | Mfloat32 => Tfloat
  | Mfloat64 => Tfloat
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
Proof with (try exact I).
  assert (S: forall s v, Val.has_type (eval_shift s v) Tint).
    intros. unfold eval_shift. destruct s; destruct v; simpl; auto; rewrite s_range; exact I.
  intros.
  destruct op; simpl; simpl in H0; FuncInv; try subst v...
  congruence.
  unfold symbol_address. destruct (Genv.find_symbol genv i)...
  destruct sp...
  destruct v0; destruct v1...
  generalize (S s v1). destruct v0; destruct (eval_shift s v1); simpl; tauto.
  destruct v0...
  destruct v0; destruct v1... simpl. destruct (zeq b b0)...
  generalize (S s v1). destruct v0; destruct (eval_shift s v1); simpl; intuition. destruct (zeq b b0)...
  generalize (S s v1). destruct v0; destruct (eval_shift s v1); simpl; intuition. destruct (zeq b0 b)...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0; destruct v1; simpl in H0; inv H0. destruct (Int.eq i0 Int.zero); inv H2...
  destruct v0; destruct v1; simpl in H0; inv H0. destruct (Int.eq i0 Int.zero); inv H2...
  destruct v0; destruct v1...
  generalize (S s v1). destruct v0; destruct (eval_shift s v1); simpl; tauto.
  destruct v0...
  destruct v0; destruct v1...
  generalize (S s v1). destruct v0; destruct (eval_shift s v1); simpl; tauto.
  destruct v0...
  destruct v0; destruct v1...
  generalize (S s v1). destruct v0; destruct (eval_shift s v1); simpl; tauto.
  destruct v0...
  destruct v0; destruct v1...
  generalize (S s v1). destruct v0; destruct (eval_shift s v1); simpl; tauto.
  destruct v0...
  generalize (S s v0). destruct (eval_shift s v0); simpl; tauto.
  destruct v0; destruct v1... simpl. destruct (Int.ltu i0 Int.iwordsize)...
  destruct v0; destruct v1... simpl. destruct (Int.ltu i0 Int.iwordsize)...
  destruct v0; destruct v1... simpl. destruct (Int.ltu i0 Int.iwordsize)...
  apply S.
  destruct v0; simpl in H0; inv H0. destruct (Int.ltu i (Int.repr 31)); inv H2...
  destruct v0...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0; destruct v1...
  destruct v0; destruct v1...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0; simpl in H0; inv H0. destruct (Float.intoffloat f); simpl in H2; inv H2...
  destruct v0; simpl in H0; inv H0. destruct (Float.intuoffloat f); simpl in H2; inv H2...
  destruct v0; simpl in H0; inv H0...
  destruct v0; simpl in H0; inv H0...
  destruct (eval_condition c vl m)... destruct b...
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

(** * Manipulating and transforming operations *)

(** Constructing shift amounts. *)

Program Definition mk_shift_amount (n: int) : shift_amount :=
  {| s_amount := Int.modu n Int.iwordsize; s_range := _ |}.
Next Obligation.
  assert (0 <= Zmod (Int.unsigned n) 32 < 32). apply Z_mod_lt. omega.
  unfold Int.ltu, Int.modu. change (Int.unsigned Int.iwordsize) with 32. 
  rewrite Int.unsigned_repr. apply zlt_true. omega. 
  assert (32 < Int.max_unsigned). compute; auto. omega.
Qed.

Lemma mk_shift_amount_eq:
  forall n, Int.ltu n Int.iwordsize = true -> s_amount (mk_shift_amount n) = n.
Proof.
  intros; simpl. unfold Int.modu. transitivity (Int.repr (Int.unsigned n)). 
  decEq. apply Zmod_small. apply Int.ltu_inv; auto.
  apply Int.repr_unsigned.
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
  | Ccomp c => Ccomp(negate_comparison c)
  | Ccompu c => Ccompu(negate_comparison c)
  | Ccompshift c s => Ccompshift (negate_comparison c) s
  | Ccompushift c s => Ccompushift (negate_comparison c) s
  | Ccompimm c n => Ccompimm (negate_comparison c) n
  | Ccompuimm c n => Ccompuimm (negate_comparison c) n
  | Ccompf c => Cnotcompf c
  | Cnotcompf c => Ccompf c
  | Ccompfzero c => Cnotcompfzero c
  | Cnotcompfzero c => Ccompfzero c
  end.

Lemma eval_negate_condition:
  forall (cond: condition) (vl: list val) (b: bool) (m: mem),
  eval_condition cond vl m = Some b ->
  eval_condition (negate_condition cond) vl m = Some (negb b).
Proof.
  intros. 
  destruct cond; simpl in H; FuncInv; simpl.
  rewrite Val.negate_cmp_bool; rewrite H; auto.
  rewrite Val.negate_cmpu_bool; rewrite H; auto.
  rewrite Val.negate_cmp_bool; rewrite H; auto.
  rewrite Val.negate_cmpu_bool; rewrite H; auto.
  rewrite Val.negate_cmp_bool; rewrite H; auto.
  rewrite Val.negate_cmpu_bool; rewrite H; auto.
  rewrite H; auto.
  destruct (Val.cmpf_bool c v v0); simpl in H; inv H. rewrite negb_elim; auto. 
  rewrite H; auto.
  destruct (Val.cmpf_bool c v (Vfloat Float.zero)); simpl in H; inv H. rewrite negb_elim; auto. 
Qed.

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

Lemma eval_shift_stack_addressing:
  forall F V (ge: Genv.t F V) sp addr vl delta,
  eval_addressing ge sp (shift_stack_addressing delta addr) vl =
  eval_addressing ge (Val.add sp (Vint delta)) addr vl.
Proof.
  intros. destruct addr; simpl; auto.
  rewrite Val.add_assoc. simpl. auto.
Qed.

Lemma eval_shift_stack_operation:
  forall F V (ge: Genv.t F V) sp op vl m delta,
  eval_operation ge sp (shift_stack_operation delta op) vl m =
  eval_operation ge (Val.add sp (Vint delta)) op vl m.
Proof.
  intros. destruct op; simpl; auto.
  rewrite Val.add_assoc. simpl. auto.
Qed.

(** Transformation of addressing modes with two operands or more
  into an equivalent arithmetic operation.  This is used in the [Reload]
  pass when a store instruction cannot be reloaded directly because
  it runs out of temporary registers. *)

(** For the ARM, there are only two binary addressing mode: [Aindexed2]
  and [Aindexed2shift].  The corresponding operations are [Oadd]
  and [Oaddshift]. *)

Definition op_for_binary_addressing (addr: addressing) : operation :=
  match addr with
  | Aindexed2 => Oadd
  | Aindexed2shift s => Oaddshift s
  | _ => Ointconst Int.zero (* never happens *)
  end.

Lemma eval_op_for_binary_addressing:
  forall (F V: Type) (ge: Genv.t F V) sp addr args v m,
  (length args >= 2)%nat ->
  eval_addressing ge sp addr args = Some v ->
  eval_operation ge sp (op_for_binary_addressing addr) args m = Some v.
Proof.
  intros.
  unfold eval_addressing in H0; destruct addr; FuncInv; simpl in H; try omegaContradiction; simpl.
  congruence.
  congruence.
Qed.

Lemma type_op_for_binary_addressing:
  forall addr,
  (length (type_of_addressing addr) >= 2)%nat ->
  type_of_operation (op_for_binary_addressing addr) = (type_of_addressing addr, Tint).
Proof.
  intros. destruct addr; simpl in H; reflexivity || omegaContradiction.
Qed.

(** Two-address operations.  There are none in the ARM architecture. *)

Definition two_address_op (op: operation) : bool := false.

(** Operations that are so cheap to recompute that CSE should not factor them out. *)

Definition is_trivial_op (op: operation) : bool :=
  match op with
  | Omove => true
  | Ointconst _ => true
  | Oaddrstack _ => true
  | _ => false
  end.

(** Operations that depend on the memory state. *)

Definition op_depends_on_memory (op: operation) : bool :=
  match op with
  | Ocmp (Ccompu _ | Ccompushift _ _) => true
  | _ => false
  end.

Lemma op_depends_on_memory_correct:
  forall (F V: Type) (ge: Genv.t F V) sp op args m1 m2,
  op_depends_on_memory op = false ->
  eval_operation ge sp op args m1 = eval_operation ge sp op args m2.
Proof.
  intros until m2. destruct op; simpl; try congruence.
  intros. destruct c; simpl; auto; congruence.
Qed.

(** Checking whether two addressings, applied to the same arguments, produce
  separated memory addresses.  Used in [CSE]. *)

Definition addressing_separated (chunk1: memory_chunk) (addr1: addressing)
                               (chunk2: memory_chunk) (addr2: addressing) : bool :=
  match addr1, addr2 with
  | Aindexed ofs1, Aindexed ofs2 => 
      Int.no_overlap ofs1 (size_chunk chunk1) ofs2 (size_chunk chunk2)
  | Ainstack ofs1, Ainstack ofs2 =>
      Int.no_overlap ofs1 (size_chunk chunk1) ofs2 (size_chunk chunk2)
  | _, _ => false
  end.

Lemma addressing_separated_sound:
  forall (F V: Type) (ge: Genv.t F V) sp chunk1 addr1 chunk2 addr2 vl b1 n1 b2 n2,
  addressing_separated chunk1 addr1 chunk2 addr2 = true ->
  eval_addressing ge sp addr1 vl = Some(Vptr b1 n1) ->
  eval_addressing ge sp addr2 vl = Some(Vptr b2 n2) ->
  b1 <> b2 \/ Int.unsigned n1 + size_chunk chunk1 <= Int.unsigned n2 \/ Int.unsigned n2 + size_chunk chunk2 <= Int.unsigned n1.
Proof.
  unfold addressing_separated; intros.
  generalize (size_chunk_pos chunk1) (size_chunk_pos chunk2); intros SZ1 SZ2.
  destruct addr1; destruct addr2; try discriminate; simpl in *; FuncInv.
(* Aindexed *)
  destruct v; simpl in *; inv H1; inv H2.
  right. apply Int.no_overlap_sound; auto. 
(* Ainstack *)
  destruct sp; simpl in *; inv H1; inv H2.
  right. apply Int.no_overlap_sound; auto. 
Qed.

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

Lemma eval_operation_preserved:
  forall sp op vl m,
  eval_operation ge2 sp op vl m = eval_operation ge1 sp op vl m.
Proof.
  intros.
  unfold eval_operation; destruct op; auto. 
  unfold symbol_address. rewrite agree_on_symbols; auto.
Qed.

Lemma eval_addressing_preserved:
  forall sp addr vl,
  eval_addressing ge2 sp addr vl = eval_addressing ge1 sp addr vl.
Proof.
  intros.
  assert (UNUSED: forall (s: ident), Genv.find_symbol ge2 s = Genv.find_symbol ge1 s).
  exact agree_on_symbols.
  unfold eval_addressing; destruct addr; auto.
Qed.

End GENV_TRANSF.

(** Compatibility of the evaluation functions with value injections. *)

Section EVAL_COMPAT.

Variable F V: Type.
Variable genv: Genv.t F V.
Variable f: meminj.

Hypothesis symbol_address_inj: 
  forall id ofs,
  val_inject f (symbol_address genv id ofs) (symbol_address genv id ofs).

Variable m1: mem.
Variable m2: mem.

Hypothesis valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.valid_pointer m1 b1 (Int.unsigned ofs) = true ->
  Mem.valid_pointer m2 b2 (Int.unsigned (Int.add ofs (Int.repr delta))) = true.

Hypothesis valid_pointer_no_overflow:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.valid_pointer m1 b1 (Int.unsigned ofs) = true ->
  0 <= Int.unsigned ofs + Int.unsigned (Int.repr delta) <= Int.max_unsigned.

Hypothesis valid_different_pointers_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m1 b1 (Int.unsigned ofs1) = true ->
  Mem.valid_pointer m1 b2 (Int.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Int.unsigned (Int.add ofs1 (Int.repr delta1)) <> Int.unsigned (Int.add ofs2 (Int.repr delta2)).

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

Remark val_add_inj:
  forall v1 v1' v2 v2',
  val_inject f v1 v1' -> val_inject f v2 v2' -> val_inject f (Val.add v1 v2) (Val.add v1' v2').
Proof.
  intros. inv H; inv H0; simpl; econstructor; eauto. 
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
Qed.

Remark val_sub_inj:
  forall v1 v1' v2 v2',
  val_inject f v1 v1' -> val_inject f v2 v2' -> val_inject f (Val.sub v1 v2) (Val.sub v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
  econstructor; eauto. rewrite Int.sub_add_l. auto.
  destruct (zeq b1 b0); auto. subst. rewrite H1 in H. inv H. rewrite zeq_true. 
  rewrite Int.sub_shifted. auto.
Qed.

Remark eval_shift_inj:
  forall s v v', val_inject f v v' -> val_inject f (eval_shift s v) (eval_shift s v').
Proof.
  intros. inv H; destruct s; simpl; auto; rewrite s_range; auto. 
Qed.

Lemma eval_condition_inj:
  forall cond vl1 vl2 b,
  val_list_inject f vl1 vl2 ->
  eval_condition cond vl1 m1 = Some b ->
  eval_condition cond vl2 m2 = Some b.
Proof.
Opaque Int.add.
  assert (CMP:
    forall c v1 v2 v1' v2' b,
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    Val.cmp_bool c v1 v2 = Some b ->
    Val.cmp_bool c v1' v2' = Some b).
  intros. inv H; simpl in H1; try discriminate; inv H0; simpl in H1; try discriminate; simpl; auto.

  assert (CMPU:
    forall c v1 v2 v1' v2' b,
    val_inject f v1 v1' ->
    val_inject f v2 v2' ->
    Val.cmpu_bool (Mem.valid_pointer m1) c v1 v2 = Some b ->
    Val.cmpu_bool (Mem.valid_pointer m2) c v1' v2' = Some b).
  intros. inv H; simpl in H1; try discriminate; inv H0; simpl in H1; try discriminate; simpl; auto.
  destruct (Mem.valid_pointer m1 b1 (Int.unsigned ofs1)) as []_eqn; try discriminate.
  destruct (Mem.valid_pointer m1 b0 (Int.unsigned ofs0)) as []_eqn; try discriminate.
  rewrite (valid_pointer_inj _ H2 Heqb4).
  rewrite (valid_pointer_inj _ H Heqb0). simpl.
  destruct (zeq b1 b0); simpl in H1.
  inv H1. rewrite H in H2; inv H2. rewrite zeq_true. 
  decEq. apply Int.translate_cmpu.
  eapply valid_pointer_no_overflow; eauto.
  eapply valid_pointer_no_overflow; eauto.
  exploit valid_different_pointers_inj; eauto. intros P.
  destruct (zeq b2 b3); auto.
  destruct P. congruence. 
  destruct c; simpl in H1; inv H1.
  simpl; decEq. rewrite Int.eq_false; auto. congruence.
  simpl; decEq. rewrite Int.eq_false; auto. congruence.

  intros. destruct cond; simpl in H0; FuncInv; InvInject; simpl.
  eapply CMP; eauto.
  eapply CMPU; eauto.
  eapply CMP. eauto. eapply eval_shift_inj. eauto. auto.
  eapply CMPU. eauto. eapply eval_shift_inj. eauto. auto.
  eapply CMP; eauto. 
  eapply CMPU; eauto.
  inv H3; inv H2; simpl in H0; inv H0; auto.
  inv H3; inv H2; simpl in H0; inv H0; auto.
  inv H3; simpl in H0; inv H0; auto.
  inv H3; simpl in H0; inv H0; auto.
Qed.

Ltac TrivialExists :=
  match goal with
  | [ |- exists v2, Some ?v1 = Some v2 /\ val_inject _ _ v2 ] =>
      exists v1; split; auto
  | _ => idtac
  end.

Lemma eval_operation_inj:
  forall op sp1 vl1 sp2 vl2 v1,
  val_inject f sp1 sp2 ->
  val_list_inject f vl1 vl2 ->
  eval_operation genv sp1 op vl1 m1 = Some v1 ->
  exists v2, eval_operation genv sp2 op vl2 m2 = Some v2 /\ val_inject f v1 v2.
Proof.
  intros. destruct op; simpl in H1; simpl; FuncInv; InvInject; TrivialExists.
  apply val_add_inj; auto.
  apply val_add_inj; auto.
  apply val_add_inj; auto. apply eval_shift_inj; auto.
  apply val_add_inj; auto.

  apply val_sub_inj; auto.
  apply val_sub_inj; auto. apply eval_shift_inj; auto.
  apply val_sub_inj; auto. apply eval_shift_inj; auto.
  apply (@val_sub_inj (Vint i) (Vint i) v v'); auto.

  inv H4; inv H2; simpl; auto.
  inv H4; inv H3; simpl in H1; inv H1. simpl. 
    destruct (Int.eq i0 Int.zero); inv H2. TrivialExists.
  inv H4; inv H3; simpl in H1; inv H1. simpl. 
    destruct (Int.eq i0 Int.zero); inv H2. TrivialExists.

  inv H4; inv H2; simpl; auto.
  exploit (eval_shift_inj s). eexact H2. intros IS. inv H4; inv IS; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  exploit (eval_shift_inj s). eexact H2. intros IS. inv H4; inv IS; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  exploit (eval_shift_inj s). eexact H2. intros IS. inv H4; inv IS; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  exploit (eval_shift_inj s). eexact H2. intros IS. inv H4; inv IS; simpl; auto.

  inv H4; simpl; auto.
  exploit (eval_shift_inj s). eexact H4. intros IS. inv IS; simpl; auto.

  inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int.iwordsize); auto.
  apply eval_shift_inj; auto.
  inv H4; simpl in H1; inv H1. simpl. destruct (Int.ltu i (Int.repr 31)); inv H2. TrivialExists.

  inv H4; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.

  inv H4; simpl in H1; inv H1. simpl. destruct (Float.intoffloat f0); simpl in H2; inv H2.
  exists (Vint i); auto.
  inv H4; simpl in H1; inv H1. simpl. destruct (Float.intuoffloat f0); simpl in H2; inv H2.
  exists (Vint i); auto.
  inv H4; simpl in *; inv H1. TrivialExists.
  inv H4; simpl in *; inv H1. TrivialExists.

  subst v1. destruct (eval_condition c vl1 m1) as []_eqn.
  exploit eval_condition_inj; eauto. intros EQ; rewrite EQ.
  destruct b; simpl; constructor.
  simpl; constructor.
Qed.

Lemma eval_addressing_inj:
  forall addr sp1 vl1 sp2 vl2 v1,
  val_inject f sp1 sp2 ->
  val_list_inject f vl1 vl2 ->
  eval_addressing genv sp1 addr vl1 = Some v1 ->
  exists v2, eval_addressing genv sp2 addr vl2 = Some v2 /\ val_inject f v1 v2.
Proof.
  assert (UNUSED: forall id ofs,
            val_inject f (symbol_address genv id ofs) (symbol_address genv id ofs)).
  exact symbol_address_inj.
  intros. destruct addr; simpl in H1; simpl; FuncInv; InvInject; TrivialExists.
  apply val_add_inj; auto.
  apply val_add_inj; auto.
  apply val_add_inj; auto. apply eval_shift_inj; auto.
  apply val_add_inj; auto.
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
  Mem.valid_pointer m1 b1 (Int.unsigned ofs) = true ->
  Mem.valid_pointer m2 b2 (Int.unsigned (Int.add ofs (Int.repr delta))) = true.
Proof.
  intros. inv H0. rewrite Int.add_zero. eapply Mem.valid_pointer_extends; eauto. 
Qed.

Remark valid_pointer_no_overflow_extends:
  forall m1 b1 ofs b2 delta,
  Some(b1, 0) = Some(b2, delta) ->
  Mem.valid_pointer m1 b1 (Int.unsigned ofs) = true ->
  0 <= Int.unsigned ofs + Int.unsigned (Int.repr delta) <= Int.max_unsigned.
Proof.
  intros. inv H. rewrite Zplus_0_r. apply Int.unsigned_range_2.
Qed.

Remark valid_different_pointers_extends:
  forall m1 b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m1 b1 (Int.unsigned ofs1) = true ->
  Mem.valid_pointer m1 b2 (Int.unsigned ofs2) = true ->
  Some(b1, 0) = Some (b1', delta1) ->
  Some(b2, 0) = Some (b2', delta2) ->
  b1' <> b2' \/
  Int.unsigned(Int.add ofs1 (Int.repr delta1)) <> Int.unsigned(Int.add ofs2 (Int.repr delta2)).
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
  apply valid_pointer_no_overflow_extends; auto. 
  apply valid_different_pointers_extends; auto.
  rewrite <- val_list_inject_lessdef. eauto. auto.
Qed.

Lemma eval_operation_lessdef:
  forall sp op vl1 vl2 v1 m1 m2,
  Val.lessdef_list vl1 vl2 ->
  Mem.extends m1 m2 ->
  eval_operation genv sp op vl1 m1 = Some v1 ->
  exists v2, eval_operation genv sp op vl2 m2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. rewrite val_list_inject_lessdef in H.
  assert (exists v2 : val,
          eval_operation genv sp op vl2 m2 = Some v2
          /\ val_inject (fun b => Some(b, 0)) v1 v2).
  eapply eval_operation_inj with (m1 := m1) (sp1 := sp).
  intros. rewrite <- val_inject_lessdef; auto.
  apply valid_pointer_extends; auto.
  apply valid_pointer_no_overflow_extends; auto. 
  apply valid_different_pointers_extends; auto.
  rewrite <- val_inject_lessdef; auto.
  eauto. auto. 
  destruct H2 as [v2 [A B]]. exists v2; split; auto. rewrite val_inject_lessdef; auto. 
Qed.

Lemma eval_addressing_lessdef:
  forall sp addr vl1 vl2 v1,
  Val.lessdef_list vl1 vl2 ->
  eval_addressing genv sp addr vl1 = Some v1 ->
  exists v2, eval_addressing genv sp addr vl2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. rewrite val_list_inject_lessdef in H.
  assert (exists v2 : val,
          eval_addressing genv sp addr vl2 = Some v2
          /\ val_inject (fun b => Some(b, 0)) v1 v2).
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
  forall id ofs, val_inject f (symbol_address genv id ofs) (symbol_address genv id ofs).
Proof.
  intros. unfold symbol_address. destruct (Genv.find_symbol genv id) as []_eqn; auto.
  exploit (proj1 globals); eauto. intros. 
  econstructor; eauto. rewrite Int.add_zero; auto.
Qed.

Lemma eval_condition_inject:
  forall cond vl1 vl2 b m1 m2,
  val_list_inject f vl1 vl2 ->
  Mem.inject f m1 m2 ->
  eval_condition cond vl1 m1 = Some b ->
  eval_condition cond vl2 m2 = Some b.
Proof.
  intros. eapply eval_condition_inj with (f := f) (m1 := m1); eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
Qed.

Lemma eval_addressing_inject:
  forall addr vl1 vl2 v1,
  val_list_inject f vl1 vl2 ->
  eval_addressing genv (Vptr sp1 Int.zero) addr vl1 = Some v1 ->
  exists v2, 
     eval_addressing genv (Vptr sp2 Int.zero) (shift_stack_addressing (Int.repr delta) addr) vl2 = Some v2
  /\ val_inject f v1 v2.
Proof.
  intros. 
  rewrite eval_shift_stack_addressing. simpl.
  eapply eval_addressing_inj with (sp1 := Vptr sp1 Int.zero); eauto.
  exact symbol_address_inject.
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
  intros. 
  rewrite eval_shift_stack_operation. simpl.
  eapply eval_operation_inj with (sp1 := Vptr sp1 Int.zero) (m1 := m1); eauto.
  exact symbol_address_inject.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
Qed.

End EVAL_INJECT.

