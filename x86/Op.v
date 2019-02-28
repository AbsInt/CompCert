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

  These types are X86-64-specific and correspond roughly to what the
  processor can compute in one instruction.  In other terms, these
  types reflect the state of the program after instruction selection.
  For a processor-independent set of operations, see the abstract
  syntax and dynamic semantics of the Cminor language.
*)
Require Import BoolEqual.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.

Set Implicit Arguments.

(** Conditions (boolean-valued operators). *)

Inductive condition : Type :=
  | Ccomp (c: comparison)      (**r signed integer comparison *)
  | Ccompu (c: comparison)     (**r unsigned integer comparison *)
  | Ccompimm (c: comparison) (n: int) (**r signed integer comparison with a constant *)
  | Ccompuimm (c: comparison) (n: int)  (**r unsigned integer comparison with a constant *)
  | Ccompl (c: comparison)      (**r signed 64-bit integer comparison *)
  | Ccomplu (c: comparison)     (**r unsigned 64-bit integer comparison *)
  | Ccomplimm (c: comparison) (n: int64) (**r signed 64-bit integer comparison with a constant *)
  | Ccompluimm (c: comparison) (n: int64)  (**r unsigned 64-bit integer comparison with a constant *)
  | Ccompf (c: comparison)     (**r 64-bit floating-point comparison *)
  | Cnotcompf (c: comparison)  (**r negation of a floating-point comparison *)
  | Ccompfs (c: comparison)    (**r 32-bit floating-point comparison *)
  | Cnotcompfs (c: comparison) (**r negation of a floating-point comparison *)
  | Cmaskzero (n: int)         (**r test [(arg & constant) == 0] *)
  | Cmasknotzero (n: int).     (**r test [(arg & constant) != 0] *)

(** Addressing modes.  [r1], [r2], etc, are the arguments to the
  addressing. *)

Inductive addressing: Type :=
  | Aindexed: Z -> addressing       (**r Address is [r1 + offset] *)
  | Aindexed2: Z -> addressing      (**r Address is [r1 + r2 + offset] *)
  | Ascaled: Z -> Z -> addressing   (**r Address is [r1 * scale + offset] *)
  | Aindexed2scaled: Z -> Z -> addressing
                                    (**r Address is [r1 + r2 * scale + offset] *)
  | Aglobal: ident -> ptrofs -> addressing (**r Address is [symbol + offset] *)
  | Abased: ident -> ptrofs -> addressing  (**r Address is [symbol + offset + r1] *)
  | Abasedscaled: Z -> ident -> ptrofs -> addressing  (**r Address is [symbol + offset + r1 * scale] *)
  | Ainstack: ptrofs -> addressing. (**r Address is [stack_pointer + offset] *)

(** Arithmetic and logical operations.  In the descriptions, [rd] is the
  result of the operation and [r1], [r2], etc, are the arguments. *)

Inductive operation : Type :=
  | Omove                    (**r [rd = r1] *)
  | Ointconst (n: int)       (**r [rd] is set to the given integer constant *)
  | Olongconst (n: int64)    (**r [rd] is set to the given integer constant *)
  | Ofloatconst (n: float)   (**r [rd] is set to the given float constant *)
  | Osingleconst (n: float32)(**r [rd] is set to the given float constant *)
  | Oindirectsymbol (id: ident) (**r [rd] is set to the address of the symbol *)
(*c 32-bit integer arithmetic: *)
  | Ocast8signed             (**r [rd] is 8-bit sign extension of [r1] *)
  | Ocast8unsigned           (**r [rd] is 8-bit zero extension of [r1] *)
  | Ocast16signed            (**r [rd] is 16-bit sign extension of [r1] *)
  | Ocast16unsigned          (**r [rd] is 16-bit zero extension of [r1] *)
  | Oneg                     (**r [rd = - r1] *)
  | Osub                     (**r [rd = r1 - r2] *)
  | Omul                     (**r [rd = r1 * r2] *)
  | Omulimm (n: int)         (**r [rd = r1 * n] *)
  | Omulhs                   (**r [rd = high part of r1 * r2, signed] *)
  | Omulhu                   (**r [rd = high part of r1 * r2, unsigned] *)
  | Odiv                     (**r [rd = r1 / r2] (signed) *)
  | Odivu                    (**r [rd = r1 / r2] (unsigned) *)
  | Omod                     (**r [rd = r1 % r2] (signed) *)
  | Omodu                    (**r [rd = r1 % r2] (unsigned) *)
  | Oand                     (**r [rd = r1 & r2] *)
  | Oandimm (n: int)         (**r [rd = r1 & n] *)
  | Oor                      (**r [rd = r1 | r2] *)
  | Oorimm (n: int)          (**r [rd = r1 | n] *)
  | Oxor                     (**r [rd = r1 ^ r2] *)
  | Oxorimm (n: int)         (**r [rd = r1 ^ n] *)
  | Onot                     (**r [rd = ~r1] *)
  | Oshl                     (**r [rd = r1 << r2] *)
  | Oshlimm (n: int)         (**r [rd = r1 << n] *)
  | Oshr                     (**r [rd = r1 >> r2] (signed) *)
  | Oshrimm (n: int)         (**r [rd = r1 >> n] (signed) *)
  | Oshrximm (n: int)        (**r [rd = r1 / 2^n] (signed) *)
  | Oshru                    (**r [rd = r1 >> r2] (unsigned) *)
  | Oshruimm (n: int)        (**r [rd = r1 >> n] (unsigned) *)
  | Ororimm (n: int)         (**r rotate right immediate *)
  | Oshldimm (n: int)        (**r [rd = r1 << n | r2 >> (32-n)] *)
  | Olea (a: addressing)     (**r effective address *)
(*c 64-bit integer arithmetic: *)
  | Omakelong                (**r [rd = r1 << 32 | r2] *)
  | Olowlong                 (**r [rd = low-word(r1)] *)
  | Ohighlong                (**r [rd = high-word(r1)] *)
  | Ocast32signed            (**r [rd] is 32-bit sign extension of [r1] *)
  | Ocast32unsigned          (**r [rd] is 32-bit zero extension of [r1] *)
  | Onegl                    (**r [rd = - r1] *)
  | Oaddlimm (n: int64)      (**r [rd = r1 + n] *)
  | Osubl                    (**r [rd = r1 - r2] *)
  | Omull                    (**r [rd = r1 * r2] *)
  | Omullimm (n: int64)      (**r [rd = r1 * n] *)
  | Omullhs                  (**r [rd = high part of r1 * r2, signed] *)
  | Omullhu                  (**r [rd = high part of r1 * r2, unsigned] *)
  | Odivl                    (**r [rd = r1 / r2] (signed) *)
  | Odivlu                   (**r [rd = r1 / r2] (unsigned) *)
  | Omodl                    (**r [rd = r1 % r2] (signed) *)
  | Omodlu                   (**r [rd = r1 % r2] (unsigned) *)
  | Oandl                    (**r [rd = r1 & r2] *)
  | Oandlimm (n: int64)      (**r [rd = r1 & n] *)
  | Oorl                     (**r [rd = r1 | r2] *)
  | Oorlimm (n: int64)       (**r [rd = r1 | n] *)
  | Oxorl                    (**r [rd = r1 ^ r2] *)
  | Oxorlimm (n: int64)      (**r [rd = r1 ^ n] *)
  | Onotl                    (**r [rd = ~r1] *)
  | Oshll                    (**r [rd = r1 << r2] *)
  | Oshllimm (n: int)        (**r [rd = r1 << n] *)
  | Oshrl                    (**r [rd = r1 >> r2] (signed) *)
  | Oshrlimm (n: int)        (**r [rd = r1 >> n] (signed) *)
  | Oshrxlimm (n: int)       (**r [rd = r1 / 2^n] (signed) *)
  | Oshrlu                   (**r [rd = r1 >> r2] (unsigned) *)
  | Oshrluimm (n: int)       (**r [rd = r1 >> n] (unsigned) *)
  | Ororlimm (n: int)        (**r rotate right immediate *)
  | Oleal (a: addressing)    (**r effective address *)
(*c Floating-point arithmetic: *)
  | Onegf                    (**r [rd = - r1] *)
  | Oabsf                    (**r [rd = abs(r1)] *)
  | Oaddf                    (**r [rd = r1 + r2] *)
  | Osubf                    (**r [rd = r1 - r2] *)
  | Omulf                    (**r [rd = r1 * r2] *)
  | Odivf                    (**r [rd = r1 / r2] *)
  | Onegfs                   (**r [rd = - r1] *)
  | Oabsfs                   (**r [rd = abs(r1)] *)
  | Oaddfs                   (**r [rd = r1 + r2] *)
  | Osubfs                   (**r [rd = r1 - r2] *)
  | Omulfs                   (**r [rd = r1 * r2] *)
  | Odivfs                   (**r [rd = r1 / r2] *)
  | Osingleoffloat           (**r [rd] is [r1] truncated to single-precision float *)
  | Ofloatofsingle           (**r [rd] is [r1] extended to double-precision float *)
(*c Conversions between int and float: *)
  | Ointoffloat              (**r [rd = signed_int_of_float64(r1)] *)
  | Ofloatofint              (**r [rd = float64_of_signed_int(r1)] *)
  | Ointofsingle             (**r [rd = signed_int_of_float32(r1)] *)
  | Osingleofint             (**r [rd = float32_of_signed_int(r1)] *)
  | Olongoffloat             (**r [rd = signed_long_of_float64(r1)] *)
  | Ofloatoflong             (**r [rd = float64_of_signed_long(r1)] *)
  | Olongofsingle            (**r [rd = signed_long_of_float32(r1)] *)
  | Osingleoflong            (**r [rd = float32_of_signed_long(r1)] *)
(*c Boolean tests: *)
  | Ocmp (cond: condition).  (**r [rd = 1] if condition holds, [rd = 0] otherwise. *)

(** Comparison functions (used in modules [CSE] and [Allocation]). *)

Definition eq_condition (x y: condition) : {x=y} + {x<>y}.
Proof.
  generalize Int.eq_dec Int64.eq_dec; intro.
  assert (forall (x y: comparison), {x=y}+{x<>y}). decide equality.
  decide equality.
Defined.

Definition eq_addressing (x y: addressing) : {x=y} + {x<>y}.
Proof.
  generalize ident_eq Ptrofs.eq_dec zeq; intros.
  decide equality.
Defined.

Definition beq_operation: forall (x y: operation), bool.
Proof.
  generalize Int.eq_dec Int64.eq_dec Float.eq_dec Float32.eq_dec ident_eq eq_addressing eq_condition; boolean_equality.
Defined.

Definition eq_operation: forall (x y: operation), {x=y} + {x<>y}.
Proof.
  decidable_equality_from beq_operation.
Defined.

Global Opaque eq_condition eq_addressing eq_operation.

(** In addressing modes, offsets are 32-bit signed integers, even in
    64-bit mode.  The following function checks that an addressing
    mode is valid, i.e. that the offsets are in range.
    The check always succeeds in 32-bit mode because offsets are
    always 32-bit integers and are normalized as 32-bit signed integers
    during code generation (see [Asmgen.normalize_addrmode_32]).

    Moreover, in 64-bit mode, we use RIP-relative addressing for
    access to globals.  (This is the "small code model" from the
    x86_64 ELF ABI.)  Thus, for addressing global variables,
    the offset from the variable plus the RIP-relative offset
    must fit in 32 bits.  The "small code model" guarantees that
    this will fit if the offset is between [-2^24] and [2^24-1],
    under the assumption that no global variable is bigger than
    [2^24] bytes. *)

Definition offset_in_range (n: Z) : bool := 
  zle Int.min_signed n && zle n Int.max_signed.

Definition ptroffset_min := -16777216.      (**r [-2^24] *)
Definition ptroffset_max := 16777215.       (**r [2^24 - 1] *)

Definition ptroffset_in_range (n: ptrofs) : bool := 
  let n := Ptrofs.signed n in zle ptroffset_min n && zle n ptroffset_max.

Definition addressing_valid (a: addressing) : bool :=
  if Archi.ptr64 then
    match a with
    | Aindexed n => offset_in_range n
    | Aindexed2 n => offset_in_range n
    | Ascaled sc ofs => offset_in_range ofs
    | Aindexed2scaled sc ofs => offset_in_range ofs
    | Aglobal s ofs => ptroffset_in_range ofs
    | Abased s ofs => ptroffset_in_range ofs
    | Abasedscaled sc s ofs => ptroffset_in_range ofs
    | Ainstack ofs => offset_in_range (Ptrofs.signed ofs)
    end
  else true.
  
(** * Evaluation functions *)

(** Evaluation of conditions, operators and addressing modes applied
  to lists of values.  Return [None] when the computation can trigger an
  error, e.g. integer division by zero.  [eval_condition] returns a boolean,
  [eval_operation] and [eval_addressing] return a value. *)

Definition eval_condition (cond: condition) (vl: list val) (m: mem): option bool :=
  match cond, vl with
  | Ccomp c, v1 :: v2 :: nil => Val.cmp_bool c v1 v2
  | Ccompu c, v1 :: v2 :: nil => Val.cmpu_bool (Mem.valid_pointer m) c v1 v2
  | Ccompimm c n, v1 :: nil => Val.cmp_bool c v1 (Vint n)
  | Ccompuimm c n, v1 :: nil => Val.cmpu_bool (Mem.valid_pointer m) c v1 (Vint n)
  | Ccompl c, v1 :: v2 :: nil => Val.cmpl_bool c v1 v2
  | Ccomplu c, v1 :: v2 :: nil => Val.cmplu_bool (Mem.valid_pointer m) c v1 v2
  | Ccomplimm c n, v1 :: nil => Val.cmpl_bool c v1 (Vlong n)
  | Ccompluimm c n, v1 :: nil => Val.cmplu_bool (Mem.valid_pointer m) c v1 (Vlong n)
  | Ccompf c, v1 :: v2 :: nil => Val.cmpf_bool c v1 v2
  | Cnotcompf c, v1 :: v2 :: nil => option_map negb (Val.cmpf_bool c v1 v2)
  | Ccompfs c, v1 :: v2 :: nil => Val.cmpfs_bool c v1 v2
  | Cnotcompfs c, v1 :: v2 :: nil => option_map negb (Val.cmpfs_bool c v1 v2)
  | Cmaskzero n, v1 :: nil => Val.maskzero_bool v1 n
  | Cmasknotzero n, v1 :: nil => option_map negb (Val.maskzero_bool v1 n)
  | _, _ => None
  end.

Definition eval_addressing32
    (F V: Type) (genv: Genv.t F V) (sp: val)
    (addr: addressing) (vl: list val) : option val :=
  match addr, vl with
  | Aindexed n, v1::nil =>
      Some (Val.add v1 (Vint (Int.repr n)))
  | Aindexed2 n, v1::v2::nil =>
      Some (Val.add (Val.add v1 v2) (Vint (Int.repr n)))
  | Ascaled sc ofs, v1::nil =>
      Some (Val.add (Val.mul v1 (Vint (Int.repr sc))) (Vint (Int.repr ofs)))
  | Aindexed2scaled sc ofs, v1::v2::nil =>
      Some(Val.add v1 (Val.add (Val.mul v2 (Vint (Int.repr sc))) (Vint (Int.repr ofs))))
  | Aglobal s ofs, nil =>
      if Archi.ptr64 then None else Some (Genv.symbol_address genv s ofs)
  | Abased s ofs, v1::nil =>
      if Archi.ptr64 then None else Some (Val.add (Genv.symbol_address genv s ofs) v1)
  | Abasedscaled sc s ofs, v1::nil =>
      if Archi.ptr64 then None else Some (Val.add (Genv.symbol_address genv s ofs) (Val.mul v1 (Vint (Int.repr sc))))
  | Ainstack ofs, nil =>
      if Archi.ptr64 then None else Some(Val.offset_ptr sp ofs)
  | _, _ => None
  end.

Definition eval_addressing64
    (F V: Type) (genv: Genv.t F V) (sp: val)
    (addr: addressing) (vl: list val) : option val :=
  match addr, vl with
  | Aindexed n, v1::nil =>
      Some (Val.addl v1 (Vlong (Int64.repr n)))
  | Aindexed2 n, v1::v2::nil =>
      Some (Val.addl (Val.addl v1 v2) (Vlong (Int64.repr n)))
  | Ascaled sc ofs, v1::nil =>
      Some (Val.addl (Val.mull v1 (Vlong (Int64.repr sc))) (Vlong (Int64.repr ofs)))
  | Aindexed2scaled sc ofs, v1::v2::nil =>
      Some(Val.addl v1 (Val.addl (Val.mull v2 (Vlong (Int64.repr sc))) (Vlong (Int64.repr ofs))))
  | Aglobal s ofs, nil =>
      if Archi.ptr64 then Some (Genv.symbol_address genv s ofs) else None
  | Ainstack ofs, nil =>
      if Archi.ptr64 then Some(Val.offset_ptr sp ofs) else None
  | _, _ => None
  end.

Definition eval_addressing
    (F V: Type) (genv: Genv.t F V) (sp: val)
    (addr: addressing) (vl: list val) : option val :=
  if Archi.ptr64
  then eval_addressing64 genv sp addr vl
  else eval_addressing32 genv sp addr vl.

Definition eval_operation
    (F V: Type) (genv: Genv.t F V) (sp: val)
    (op: operation) (vl: list val) (m: mem): option val :=
  match op, vl with
  | Omove, v1::nil => Some v1
  | Ointconst n, nil => Some (Vint n)
  | Olongconst n, nil => Some (Vlong n)
  | Ofloatconst n, nil => Some (Vfloat n)
  | Osingleconst n, nil => Some (Vsingle n)
  | Oindirectsymbol id, nil => Some (Genv.symbol_address genv id Ptrofs.zero)
  | Ocast8signed, v1 :: nil => Some (Val.sign_ext 8 v1)
  | Ocast8unsigned, v1 :: nil => Some (Val.zero_ext 8 v1)
  | Ocast16signed, v1 :: nil => Some (Val.sign_ext 16 v1)
  | Ocast16unsigned, v1 :: nil => Some (Val.zero_ext 16 v1)
  | Oneg, v1::nil => Some (Val.neg v1)
  | Osub, v1::v2::nil => Some (Val.sub v1 v2)
  | Omul, v1::v2::nil => Some (Val.mul v1 v2)
  | Omulimm n, v1::nil => Some (Val.mul v1 (Vint n))
  | Omulhs, v1::v2::nil => Some (Val.mulhs v1 v2)
  | Omulhu, v1::v2::nil => Some (Val.mulhu v1 v2)
  | Odiv, v1::v2::nil => Val.divs v1 v2
  | Odivu, v1::v2::nil => Val.divu v1 v2
  | Omod, v1::v2::nil => Val.mods v1 v2
  | Omodu, v1::v2::nil => Val.modu v1 v2
  | Oand, v1::v2::nil => Some(Val.and v1 v2)
  | Oandimm n, v1::nil => Some (Val.and v1 (Vint n))
  | Oor, v1::v2::nil => Some(Val.or v1 v2)
  | Oorimm n, v1::nil => Some (Val.or v1 (Vint n))
  | Oxor, v1::v2::nil => Some(Val.xor v1 v2)
  | Oxorimm n, v1::nil => Some (Val.xor v1 (Vint n))
  | Onot, v1::nil => Some(Val.notint v1)
  | Oshl, v1::v2::nil => Some (Val.shl v1 v2)
  | Oshlimm n, v1::nil => Some (Val.shl v1 (Vint n))
  | Oshr, v1::v2::nil => Some (Val.shr v1 v2)
  | Oshrimm n, v1::nil => Some (Val.shr v1 (Vint n))
  | Oshrximm n, v1::nil => Val.shrx v1 (Vint n)
  | Oshru, v1::v2::nil => Some (Val.shru v1 v2)
  | Oshruimm n, v1::nil => Some (Val.shru v1 (Vint n))
  | Ororimm n, v1::nil => Some (Val.ror v1 (Vint n))
  | Oshldimm n, v1::v2::nil => Some (Val.or (Val.shl v1 (Vint n))
                                            (Val.shru v2 (Vint (Int.sub Int.iwordsize n))))
  | Olea addr, _ => eval_addressing32 genv sp addr vl
  | Omakelong, v1::v2::nil => Some(Val.longofwords v1 v2)
  | Olowlong, v1::nil => Some(Val.loword v1)
  | Ohighlong, v1::nil => Some(Val.hiword v1)
  | Ocast32signed, v1 :: nil => Some (Val.longofint v1)
  | Ocast32unsigned, v1 :: nil => Some (Val.longofintu v1)
  | Onegl, v1::nil => Some (Val.negl v1)
  | Oaddlimm n, v1::nil => Some (Val.addl v1 (Vlong n))
  | Osubl, v1::v2::nil => Some (Val.subl v1 v2)
  | Omull, v1::v2::nil => Some (Val.mull v1 v2)
  | Omullimm n, v1::nil => Some (Val.mull v1 (Vlong n))
  | Omullhs, v1::v2::nil => Some (Val.mullhs v1 v2)
  | Omullhu, v1::v2::nil => Some (Val.mullhu v1 v2)
  | Odivl, v1::v2::nil => Val.divls v1 v2
  | Odivlu, v1::v2::nil => Val.divlu v1 v2
  | Omodl, v1::v2::nil => Val.modls v1 v2
  | Omodlu, v1::v2::nil => Val.modlu v1 v2
  | Oandl, v1::v2::nil => Some(Val.andl v1 v2)
  | Oandlimm n, v1::nil => Some (Val.andl v1 (Vlong n))
  | Oorl, v1::v2::nil => Some(Val.orl v1 v2)
  | Oorlimm n, v1::nil => Some (Val.orl v1 (Vlong n))
  | Oxorl, v1::v2::nil => Some(Val.xorl v1 v2)
  | Oxorlimm n, v1::nil => Some (Val.xorl v1 (Vlong n))
  | Onotl, v1::nil => Some(Val.notl v1)
  | Oshll, v1::v2::nil => Some (Val.shll v1 v2)
  | Oshllimm n, v1::nil => Some (Val.shll v1 (Vint n))
  | Oshrl, v1::v2::nil => Some (Val.shrl v1 v2)
  | Oshrlimm n, v1::nil => Some (Val.shrl v1 (Vint n))
  | Oshrxlimm n, v1::nil => Val.shrxl v1 (Vint n)
  | Oshrlu, v1::v2::nil => Some (Val.shrlu v1 v2)
  | Oshrluimm n, v1::nil => Some (Val.shrlu v1 (Vint n))
  | Ororlimm n, v1::nil => Some (Val.rorl v1 (Vint n))
  | Oleal addr, _ => eval_addressing64 genv sp addr vl
  | Onegf, v1::nil => Some(Val.negf v1)
  | Oabsf, v1::nil => Some(Val.absf v1)
  | Oaddf, v1::v2::nil => Some(Val.addf v1 v2)
  | Osubf, v1::v2::nil => Some(Val.subf v1 v2)
  | Omulf, v1::v2::nil => Some(Val.mulf v1 v2)
  | Odivf, v1::v2::nil => Some(Val.divf v1 v2)
  | Onegfs, v1::nil => Some(Val.negfs v1)
  | Oabsfs, v1::nil => Some(Val.absfs v1)
  | Oaddfs, v1::v2::nil => Some(Val.addfs v1 v2)
  | Osubfs, v1::v2::nil => Some(Val.subfs v1 v2)
  | Omulfs, v1::v2::nil => Some(Val.mulfs v1 v2)
  | Odivfs, v1::v2::nil => Some(Val.divfs v1 v2)
  | Osingleoffloat, v1::nil => Some(Val.singleoffloat v1)
  | Ofloatofsingle, v1::nil => Some(Val.floatofsingle v1)
  | Ointoffloat, v1::nil => Val.intoffloat v1
  | Ofloatofint, v1::nil => Val.floatofint v1
  | Ointofsingle, v1::nil => Val.intofsingle v1
  | Osingleofint, v1::nil => Val.singleofint v1
  | Olongoffloat, v1::nil => Val.longoffloat v1
  | Ofloatoflong, v1::nil => Val.floatoflong v1
  | Olongofsingle, v1::nil => Val.longofsingle v1
  | Osingleoflong, v1::nil => Val.singleoflong v1
  | Ocmp c, _ => Some(Val.of_optbool (eval_condition c vl m))
  | _, _ => None
  end.

Remark eval_addressing_Aglobal:
  forall (F V: Type) (genv: Genv.t F V) sp id ofs,
  eval_addressing genv sp (Aglobal id ofs) nil = Some (Genv.symbol_address genv id ofs).
Proof.
  intros. unfold eval_addressing, eval_addressing32, eval_addressing64; destruct Archi.ptr64; auto.
Qed.

Remark eval_addressing_Ainstack:
  forall (F V: Type) (genv: Genv.t F V) sp ofs,
  eval_addressing genv sp (Ainstack ofs) nil = Some (Val.offset_ptr sp ofs).
Proof.
  intros. unfold eval_addressing, eval_addressing32, eval_addressing64; destruct Archi.ptr64; auto.
Qed.

Remark eval_addressing_Ainstack_inv:
  forall (F V: Type) (genv: Genv.t F V) sp ofs vl v,
  eval_addressing genv sp (Ainstack ofs) vl = Some v -> vl = nil /\ v = Val.offset_ptr sp ofs.
Proof.
  unfold eval_addressing, eval_addressing32, eval_addressing64;
  intros; destruct Archi.ptr64; destruct vl; inv H; auto.
Qed.

Ltac FuncInv :=
  match goal with
  | H: (match ?x with nil => _ | _ :: _ => _ end = Some _) |- _ =>
      destruct x; simpl in H; FuncInv
  | H: (match ?v with Vundef => _ | Vint _ => _ | Vfloat _ => _ | Vptr _ _ => _ end = Some _) |- _ =>
      destruct v; simpl in H; FuncInv
  | H: (if Archi.ptr64 then _ else _) = Some _ |- _ =>
      destruct Archi.ptr64 eqn:?; FuncInv
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
  | Ccompl _ => Tlong :: Tlong :: nil
  | Ccomplu _ => Tlong :: Tlong :: nil
  | Ccomplimm _ _ => Tlong :: nil
  | Ccompluimm _ _ => Tlong :: nil
  | Ccompf _ => Tfloat :: Tfloat :: nil
  | Cnotcompf _ => Tfloat :: Tfloat :: nil
  | Ccompfs _ => Tsingle :: Tsingle :: nil
  | Cnotcompfs _ => Tsingle :: Tsingle :: nil
  | Cmaskzero _ => Tint :: nil
  | Cmasknotzero _ => Tint :: nil
  end.

Definition type_of_addressing_gen (tyA: typ) (addr: addressing): list typ :=
  match addr with
  | Aindexed _ => tyA :: nil
  | Aindexed2 _ => tyA :: tyA :: nil
  | Ascaled _ _ => tyA :: nil
  | Aindexed2scaled _ _ => tyA :: tyA :: nil
  | Aglobal _ _ => nil
  | Abased _ _ => tyA :: nil
  | Abasedscaled _ _ _ => tyA :: nil
  | Ainstack _ => nil
  end.

Definition type_of_addressing := type_of_addressing_gen Tptr.
Definition type_of_addressing32 := type_of_addressing_gen Tint.
Definition type_of_addressing64 := type_of_addressing_gen Tlong.

Definition type_of_operation (op: operation) : list typ * typ :=
  match op with
  | Omove => (nil, Tint)   (* treated specially *)
  | Ointconst _ => (nil, Tint)
  | Olongconst _ => (nil, Tlong)
  | Ofloatconst f => (nil, Tfloat)
  | Osingleconst f => (nil, Tsingle)
  | Oindirectsymbol _ => (nil, Tptr)
  | Ocast8signed => (Tint :: nil, Tint)
  | Ocast8unsigned => (Tint :: nil, Tint)
  | Ocast16signed => (Tint :: nil, Tint)
  | Ocast16unsigned => (Tint :: nil, Tint)
  | Oneg => (Tint :: nil, Tint)
  | Osub => (Tint :: Tint :: nil, Tint)
  | Omul => (Tint :: Tint :: nil, Tint)
  | Omulimm _ => (Tint :: nil, Tint)
  | Omulhs => (Tint :: Tint :: nil, Tint)
  | Omulhu => (Tint :: Tint :: nil, Tint)
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
  | Onot => (Tint :: nil, Tint)
  | Oshl => (Tint :: Tint :: nil, Tint)
  | Oshlimm _ => (Tint :: nil, Tint)
  | Oshr => (Tint :: Tint :: nil, Tint)
  | Oshrimm _ => (Tint :: nil, Tint)
  | Oshrximm _ => (Tint :: nil, Tint)
  | Oshru => (Tint :: Tint :: nil, Tint)
  | Oshruimm _ => (Tint :: nil, Tint)
  | Ororimm _ => (Tint :: nil, Tint)
  | Oshldimm _ => (Tint :: Tint :: nil, Tint)
  | Olea addr => (type_of_addressing32 addr, Tint)
  | Omakelong => (Tint :: Tint :: nil, Tlong)
  | Olowlong => (Tlong :: nil, Tint)
  | Ohighlong => (Tlong :: nil, Tint)
  | Ocast32signed => (Tint :: nil, Tlong)
  | Ocast32unsigned => (Tint :: nil, Tlong)
  | Onegl => (Tlong :: nil, Tlong)
  | Oaddlimm _ => (Tlong :: nil, Tlong)
  | Osubl => (Tlong :: Tlong :: nil, Tlong)
  | Omull => (Tlong :: Tlong :: nil, Tlong)
  | Omullimm _ => (Tlong :: nil, Tlong)
  | Omullhs => (Tlong :: Tlong :: nil, Tlong)
  | Omullhu => (Tlong :: Tlong :: nil, Tlong)
  | Odivl => (Tlong :: Tlong :: nil, Tlong)
  | Odivlu => (Tlong :: Tlong :: nil, Tlong)
  | Omodl => (Tlong :: Tlong :: nil, Tlong)
  | Omodlu => (Tlong :: Tlong :: nil, Tlong)
  | Oandl => (Tlong :: Tlong :: nil, Tlong)
  | Oandlimm _ => (Tlong :: nil, Tlong)
  | Oorl => (Tlong :: Tlong :: nil, Tlong)
  | Oorlimm _ => (Tlong :: nil, Tlong)
  | Oxorl => (Tlong :: Tlong :: nil, Tlong)
  | Oxorlimm _ => (Tlong :: nil, Tlong)
  | Onotl => (Tlong :: nil, Tlong)
  | Oshll => (Tlong :: Tint :: nil, Tlong)
  | Oshllimm _ => (Tlong :: nil, Tlong)
  | Oshrl => (Tlong :: Tint :: nil, Tlong)
  | Oshrlimm _ => (Tlong :: nil, Tlong)
  | Oshrxlimm _ => (Tlong :: nil, Tlong)
  | Oshrlu => (Tlong :: Tint :: nil, Tlong)
  | Oshrluimm _ => (Tlong :: nil, Tlong)
  | Ororlimm _ => (Tlong :: nil, Tlong)
  | Oleal addr => (type_of_addressing64 addr, Tlong)
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
  | Ofloatofint => (Tint :: nil, Tfloat)
  | Ointofsingle => (Tsingle :: nil, Tint)
  | Osingleofint => (Tint :: nil, Tsingle)
  | Olongoffloat => (Tfloat :: nil, Tlong)
  | Ofloatoflong => (Tlong :: nil, Tfloat)
  | Olongofsingle => (Tsingle :: nil, Tlong)
  | Osingleoflong => (Tlong :: nil, Tsingle)
  | Ocmp c => (type_of_condition c, Tint)
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
  intros. unfold Val.has_type, Val.add. destruct Archi.ptr64, v1, v2; auto.
Qed.

Remark type_addl:
  forall v1 v2, Val.has_type (Val.addl v1 v2) Tlong.
Proof.
  intros. unfold Val.has_type, Val.addl. destruct Archi.ptr64, v1, v2; auto.
Qed.

Lemma type_of_addressing64_sound:
  forall addr vl sp v,
  eval_addressing64 genv sp addr vl = Some v ->
  Val.has_type v Tlong.
Proof.
  intros. destruct addr; simpl in H; FuncInv; subst; simpl; auto using type_addl.
- unfold Genv.symbol_address; destruct (Genv.find_symbol genv i); simpl; auto.
- destruct sp; simpl; auto.
Qed.

Lemma type_of_addressing32_sound:
  forall addr vl sp v,
  eval_addressing32 genv sp addr vl = Some v ->
  Val.has_type v Tint.
Proof.
  intros. destruct addr; simpl in H; FuncInv; subst; simpl; auto using type_add.
- unfold Genv.symbol_address; destruct (Genv.find_symbol genv i); simpl; auto.
- destruct sp; simpl; auto.
Qed.

Corollary type_of_addressing_sound:
  forall addr vl sp v,
  eval_addressing genv sp addr vl = Some v ->
  Val.has_type v Tptr.
Proof.
  unfold eval_addressing, Tptr; intros.
  destruct Archi.ptr64; eauto using type_of_addressing64_sound, type_of_addressing32_sound.
Qed.

Lemma type_of_operation_sound:
  forall op vl sp v m,
  op <> Omove ->
  eval_operation genv sp op vl m = Some v ->
  Val.has_type v (snd (type_of_operation op)).
Proof with (try exact I; try reflexivity).
  intros.
  destruct op; simpl in H0; FuncInv; subst; simpl.
  congruence.
  exact I.
  exact I.
  exact I.
  exact I.
  unfold Genv.symbol_address; destruct (Genv.find_symbol genv id)...
  destruct v0...
  destruct v0...
  destruct v0...
  destruct v0...
  destruct v0...
  unfold Val.sub, Val.has_type; destruct Archi.ptr64, v0, v1... destruct (eq_block b b0)...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0; destruct v1...
  destruct v0; destruct v1; simpl in *; inv H0.
    destruct (Int.eq i0 Int.zero || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H2...
  destruct v0; destruct v1; simpl in *; inv H0. destruct (Int.eq i0 Int.zero); inv H2...
  destruct v0; destruct v1; simpl in *; inv H0.
    destruct (Int.eq i0 Int.zero || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H2...
  destruct v0; destruct v1; simpl in *; inv H0. destruct (Int.eq i0 Int.zero); inv H2...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0...
  destruct v0; destruct v1; simpl... destruct (Int.ltu i0 Int.iwordsize)...
  destruct v0; simpl... destruct (Int.ltu n Int.iwordsize)...
  destruct v0; destruct v1; simpl... destruct (Int.ltu i0 Int.iwordsize)...
  destruct v0; simpl... destruct (Int.ltu n Int.iwordsize)...
  destruct v0; simpl in H0; try discriminate. destruct (Int.ltu n (Int.repr 31)); inv H0...
  destruct v0; destruct v1; simpl... destruct (Int.ltu i0 Int.iwordsize)...
  destruct v0; simpl... destruct (Int.ltu n Int.iwordsize)...
  destruct v0...
  destruct v0; simpl... destruct (Int.ltu n Int.iwordsize)...
  destruct v1; simpl... destruct (Int.ltu (Int.sub Int.iwordsize n) Int.iwordsize)...
  eapply type_of_addressing32_sound; eauto.
  destruct v0; destruct v1...
  destruct v0...
  destruct v0...
  destruct v0...
  destruct v0...
  destruct v0...
  unfold Val.addl, Val.has_type; destruct Archi.ptr64, v0...
  unfold Val.subl, Val.has_type; destruct Archi.ptr64, v0, v1... destruct (eq_block b b0)...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0; destruct v1...
  destruct v0; destruct v1; simpl in *; inv H0.
    destruct (Int64.eq i0 Int64.zero || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H2...
  destruct v0; destruct v1; simpl in *; inv H0. destruct (Int64.eq i0 Int64.zero); inv H2...
  destruct v0; destruct v1; simpl in *; inv H0.
    destruct (Int64.eq i0 Int64.zero || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H2...
  destruct v0; destruct v1; simpl in *; inv H0. destruct (Int64.eq i0 Int64.zero); inv H2...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0...
  destruct v0; destruct v1; simpl... destruct (Int.ltu i0 Int64.iwordsize')...
  destruct v0; simpl... destruct (Int.ltu n Int64.iwordsize')...
  destruct v0; destruct v1; simpl... destruct (Int.ltu i0 Int64.iwordsize')...
  destruct v0; simpl... destruct (Int.ltu n Int64.iwordsize')...
  destruct v0; inv H0. destruct (Int.ltu n (Int.repr 63)); inv H2...
  destruct v0; destruct v1; simpl... destruct (Int.ltu i0 Int64.iwordsize')...
  destruct v0; simpl... destruct (Int.ltu n Int64.iwordsize')...
  destruct v0...
  eapply type_of_addressing64_sound; eauto.
  destruct v0...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0; destruct v1...
  destruct v0; destruct v1...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0...
  destruct v0; destruct v1...
  destruct v0; destruct v1...
  destruct v0; destruct v1...
  destruct v0; destruct v1...
  destruct v0...
  destruct v0...
  destruct v0; simpl in H0; inv H0. destruct (Float.to_int f); inv H2...
  destruct v0; simpl in H0; inv H0...
  destruct v0; simpl in H0; inv H0. destruct (Float32.to_int f); inv H2...
  destruct v0; simpl in H0; inv H0...
  destruct v0; simpl in H0; inv H0. destruct (Float.to_long f); inv H2...
  destruct v0; simpl in H0; inv H0...
  destruct v0; simpl in H0; inv H0. destruct (Float32.to_long f); inv H2...
  destruct v0; simpl in H0; inv H0...
  destruct (eval_condition cond vl m); simpl... destruct b...
Qed.

End SOUNDNESS.

(** * Manipulating and transforming operations *)

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
  | Ccompimm c n => Ccompimm (negate_comparison c) n
  | Ccompuimm c n => Ccompuimm (negate_comparison c) n
  | Ccompl c => Ccompl(negate_comparison c)
  | Ccomplu c => Ccomplu(negate_comparison c)
  | Ccomplimm c n => Ccomplimm (negate_comparison c) n
  | Ccompluimm c n => Ccompluimm (negate_comparison c) n
  | Ccompf c => Cnotcompf c
  | Cnotcompf c => Ccompf c
  | Ccompfs c => Cnotcompfs c
  | Cnotcompfs c => Ccompfs c
  | Cmaskzero n => Cmasknotzero n
  | Cmasknotzero n => Cmaskzero n
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
  repeat (destruct vl; auto). apply Val.negate_cmpl_bool.
  repeat (destruct vl; auto). apply Val.negate_cmplu_bool.
  repeat (destruct vl; auto). apply Val.negate_cmpl_bool.
  repeat (destruct vl; auto). apply Val.negate_cmplu_bool.
  repeat (destruct vl; auto).
  repeat (destruct vl; auto). destruct (Val.cmpf_bool c v v0) as [[]|]; auto.
  repeat (destruct vl; auto).
  repeat (destruct vl; auto). destruct (Val.cmpfs_bool c v v0) as [[]|]; auto.
  destruct vl; auto. destruct vl; auto.
  destruct vl; auto. destruct vl; auto. destruct (Val.maskzero_bool v n) as [[]|]; auto.
Qed.

(** Shifting stack-relative references.  This is used in [Stacking]. *)

Definition shift_stack_addressing (delta: Z) (addr: addressing) :=
  match addr with
  | Ainstack ofs => Ainstack (Ptrofs.add ofs (Ptrofs.repr delta))
  | _ => addr
  end.

Definition shift_stack_operation (delta: Z) (op: operation) :=
  match op with
  | Olea  addr => Olea  (shift_stack_addressing delta addr)
  | Oleal addr => Oleal (shift_stack_addressing delta addr)
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
  intros. destruct op; auto; simpl; decEq; destruct a; auto.
Qed.

Lemma eval_shift_stack_addressing32:
  forall F V (ge: Genv.t F V) sp addr vl delta,
  eval_addressing32 ge (Vptr sp Ptrofs.zero) (shift_stack_addressing delta addr) vl =
  eval_addressing32 ge (Vptr sp (Ptrofs.repr delta)) addr vl.
Proof.
  intros.
  assert (A: forall i, Ptrofs.add Ptrofs.zero (Ptrofs.add i (Ptrofs.repr delta)) = Ptrofs.add (Ptrofs.repr delta) i).
  { intros. rewrite Ptrofs.add_zero_l. apply Ptrofs.add_commut. }
  destruct addr; simpl; rewrite ?A; reflexivity.
Qed.

Lemma eval_shift_stack_addressing64:
  forall F V (ge: Genv.t F V) sp addr vl delta,
  eval_addressing64 ge (Vptr sp Ptrofs.zero) (shift_stack_addressing delta addr) vl =
  eval_addressing64 ge (Vptr sp (Ptrofs.repr delta)) addr vl.
Proof.
  intros.
  assert (A: forall i, Ptrofs.add Ptrofs.zero (Ptrofs.add i (Ptrofs.repr delta)) = Ptrofs.add (Ptrofs.repr delta) i).
  { intros. rewrite Ptrofs.add_zero_l. apply Ptrofs.add_commut. }
  destruct addr; simpl; rewrite ?A; reflexivity.
Qed.

Lemma eval_shift_stack_addressing:
  forall F V (ge: Genv.t F V) sp addr vl delta,
  eval_addressing ge (Vptr sp Ptrofs.zero) (shift_stack_addressing delta addr) vl =
  eval_addressing ge (Vptr sp (Ptrofs.repr delta)) addr vl.
Proof.
  intros. unfold eval_addressing.
  destruct Archi.ptr64; auto using eval_shift_stack_addressing32, eval_shift_stack_addressing64.
Qed.

Lemma eval_shift_stack_operation:
  forall F V (ge: Genv.t F V) sp op vl m delta,
  eval_operation ge (Vptr sp Ptrofs.zero) (shift_stack_operation delta op) vl m =
  eval_operation ge (Vptr sp (Ptrofs.repr delta)) op vl m.
Proof.
  intros. destruct op; simpl; auto using eval_shift_stack_addressing32, eval_shift_stack_addressing64.
Qed.

(** Offset an addressing mode [addr] by a quantity [delta], so that
  it designates the pointer [delta] bytes past the pointer designated
  by [addr].  This may be undefined if an offset overflows, in which case
  [None] is returned.  *)

Definition offset_addressing_total (addr: addressing) (delta: Z) : addressing :=
  match addr with
  | Aindexed n => Aindexed (n + delta)
  | Aindexed2 n => Aindexed2 (n + delta)
  | Ascaled sc n => Ascaled sc (n + delta)
  | Aindexed2scaled sc n => Aindexed2scaled sc (n + delta)
  | Aglobal s n => Aglobal s (Ptrofs.add n (Ptrofs.repr delta))
  | Abased s n => Abased s (Ptrofs.add n (Ptrofs.repr delta))
  | Abasedscaled sc s n => Abasedscaled sc s (Ptrofs.add n (Ptrofs.repr delta))
  | Ainstack n => Ainstack (Ptrofs.add n (Ptrofs.repr delta))
  end.

Definition offset_addressing (addr: addressing) (delta: Z) : option addressing :=
  let addr' := offset_addressing_total addr delta in
  if addressing_valid addr' then Some addr' else None.

Lemma eval_offset_addressing_total_32:
  forall (F V: Type) (ge: Genv.t F V) sp addr args delta v,
  eval_addressing32 ge sp addr args = Some v ->
  eval_addressing32 ge sp (offset_addressing_total addr delta) args = Some(Val.add v (Vint (Int.repr delta))).
Proof.
  assert (A: forall x y, Int.add (Int.repr x) (Int.repr y) = Int.repr (x + y)).
  { intros. apply Int.eqm_samerepr; auto with ints. }
  assert (B: forall delta, Archi.ptr64 = false -> Ptrofs.repr delta = Ptrofs.of_int (Int.repr delta)).
  { intros; symmetry; auto with ptrofs. }
  intros. destruct addr; simpl in *; FuncInv; subst; simpl.
- rewrite <- A, ! Val.add_assoc; auto.
- rewrite <- A, ! Val.add_assoc; auto.
- rewrite <- A, ! Val.add_assoc; auto.
- rewrite <- A, ! Val.add_assoc; auto.
- rewrite B, Genv.shift_symbol_address_32 by auto. auto.
- rewrite B, Genv.shift_symbol_address_32 by auto. rewrite ! Val.add_assoc. do 2 f_equal. apply Val.add_commut.
- rewrite B, Genv.shift_symbol_address_32 by auto. rewrite ! Val.add_assoc. do 2 f_equal. apply Val.add_commut.
- destruct sp; simpl; auto. rewrite Heqb. rewrite Ptrofs.add_assoc. do 4 f_equal. symmetry; auto with ptrofs.
Qed.

Lemma eval_offset_addressing_total_64:
  forall (F V: Type) (ge: Genv.t F V) sp addr args delta v,
  eval_addressing64 ge sp addr args = Some v ->
  eval_addressing64 ge sp (offset_addressing_total addr delta) args = Some(Val.addl v (Vlong (Int64.repr delta))).
Proof.
  assert (A: forall x y, Int64.add (Int64.repr x) (Int64.repr y) = Int64.repr (x + y)).
  { intros. apply Int64.eqm_samerepr; auto with ints. }
  assert (B: forall delta, Archi.ptr64 = true -> Ptrofs.repr delta = Ptrofs.of_int64 (Int64.repr delta)).
  { intros; symmetry; auto with ptrofs. }
  intros. destruct addr; simpl in *; FuncInv; subst; simpl.
- rewrite <- A, ! Val.addl_assoc; auto.
- rewrite <- A, ! Val.addl_assoc; auto.
- rewrite <- A, ! Val.addl_assoc; auto.
- rewrite <- A, ! Val.addl_assoc; auto.
- rewrite B, Genv.shift_symbol_address_64 by auto. auto.
- destruct sp; simpl; auto. rewrite Heqb. rewrite Ptrofs.add_assoc. do 4 f_equal. symmetry; auto with ptrofs.
Qed.

(** The following lemma is used only in [Allocproof] in cases where [Archi.ptr64 = false]. *)

Lemma eval_offset_addressing:
  forall (F V: Type) (ge: Genv.t F V) sp addr args delta addr' v,
  offset_addressing addr delta = Some addr' ->
  eval_addressing ge sp addr args = Some v ->
  Archi.ptr64 = false ->
  eval_addressing ge sp addr' args = Some(Val.add v (Vint (Int.repr delta))).
Proof.
  intros. unfold offset_addressing in H. destruct (addressing_valid (offset_addressing_total addr delta)); inv H.
  unfold eval_addressing in *; rewrite H1 in *. apply eval_offset_addressing_total_32; auto.
Qed.

(** Operations that are so cheap to recompute that CSE should not factor them out. *)

Definition is_trivial_op (op: operation) : bool :=
  match op with
  | Omove => true
  | Ointconst _ => true
  | Olongconst _ => true
  | Olea (Aglobal _ _) => true
  | Olea (Ainstack _) => true
  | Oleal (Aglobal _ _) => true
  | Oleal (Ainstack _) => true
  | _ => false
  end.

(** Operations that depend on the memory state. *)

Definition op_depends_on_memory (op: operation) : bool :=
  match op with
  | Ocmp (Ccompu _) => negb Archi.ptr64
  | Ocmp (Ccompuimm _ _) => negb Archi.ptr64
  | Ocmp (Ccomplu _) => Archi.ptr64
  | Ocmp (Ccompluimm _ _) => Archi.ptr64
  | _ => false
  end.

Lemma op_depends_on_memory_correct:
  forall (F V: Type) (ge: Genv.t F V) sp op args m1 m2,
  op_depends_on_memory op = false ->
  eval_operation ge sp op args m1 = eval_operation ge sp op args m2.
Proof.
  intros until m2. destruct op; simpl; try congruence.
  destruct cond; simpl; intros SF; auto; rewrite ? negb_false_iff in SF;
  unfold Val.cmpu_bool, Val.cmplu_bool; rewrite SF; reflexivity.
Qed.

(** Global variables mentioned in an operation or addressing mode *)

Definition globals_addressing (addr: addressing) : list ident :=
  match addr with
  | Aglobal s n => s :: nil
  | Abased s n => s :: nil
  | Abasedscaled sc s n => s :: nil
  | _ => nil
  end.

Definition globals_operation (op: operation) : list ident :=
  match op with
  | Oindirectsymbol s => s :: nil
  | Olea addr => globals_addressing addr
  | Oleal addr => globals_addressing addr
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

Lemma eval_addressing32_preserved:
  forall sp addr vl,
  eval_addressing32 ge2 sp addr vl = eval_addressing32 ge1 sp addr vl.
Proof.
  intros.
  unfold eval_addressing32, Genv.symbol_address; destruct addr; try rewrite agree_on_symbols;
  reflexivity.
Qed.

Lemma eval_addressing64_preserved:
  forall sp addr vl,
  eval_addressing64 ge2 sp addr vl = eval_addressing64 ge1 sp addr vl.
Proof.
  intros.
  unfold eval_addressing64, Genv.symbol_address; destruct addr; try rewrite agree_on_symbols;
  reflexivity.
Qed.

Lemma eval_addressing_preserved:
  forall sp addr vl,
  eval_addressing ge2 sp addr vl = eval_addressing ge1 sp addr vl.
Proof.
  intros.
  unfold eval_addressing; destruct Archi.ptr64; auto using eval_addressing32_preserved, eval_addressing64_preserved.
Qed.

Lemma eval_operation_preserved:
  forall sp op vl m,
  eval_operation ge2 sp op vl m = eval_operation ge1 sp op vl m.
Proof.
  intros.
  unfold eval_operation; destruct op; auto using eval_addressing32_preserved, eval_addressing64_preserved.
  unfold Genv.symbol_address. rewrite agree_on_symbols. auto.
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

Lemma eval_condition_inj:
  forall cond vl1 vl2 b,
  Val.inject_list f vl1 vl2 ->
  eval_condition cond vl1 m1 = Some b ->
  eval_condition cond vl2 m2 = Some b.
Proof.
  intros. destruct cond; simpl in H0; FuncInv; InvInject; simpl; auto.
- inv H3; inv H2; simpl in H0; inv H0; auto.
- eauto 3 using Val.cmpu_bool_inject, Mem.valid_pointer_implies.
- inv H3; simpl in H0; inv H0; auto.
- eauto 3 using Val.cmpu_bool_inject, Mem.valid_pointer_implies.
- inv H3; inv H2; simpl in H0; inv H0; auto.
- eauto 3 using Val.cmplu_bool_inject, Mem.valid_pointer_implies.
- inv H3; simpl in H0; inv H0; auto.
- eauto 3 using Val.cmplu_bool_inject, Mem.valid_pointer_implies.
- inv H3; inv H2; simpl in H0; inv H0; auto.
- inv H3; inv H2; simpl in H0; inv H0; auto.
- inv H3; inv H2; simpl in H0; inv H0; auto.
- inv H3; inv H2; simpl in H0; inv H0; auto.
- inv H3; try discriminate; auto.
- inv H3; try discriminate; auto.
Qed.

Ltac TrivialExists :=
  match goal with
  | [ |- exists v2, Some ?v1 = Some v2 /\ Val.inject _ _ v2 ] =>
      exists v1; split; auto
  | _ => idtac
  end.

Lemma eval_addressing32_inj:
  forall addr sp1 vl1 sp2 vl2 v1,
  (forall id ofs,
      In id (globals_addressing addr) ->
      Val.inject f (Genv.symbol_address ge1 id ofs) (Genv.symbol_address ge2 id ofs)) ->
  Val.inject f sp1 sp2 ->
  Val.inject_list f vl1 vl2 ->
  eval_addressing32 ge1 sp1 addr vl1 = Some v1 ->
  exists v2, eval_addressing32 ge2 sp2 addr vl2 = Some v2 /\ Val.inject f v1 v2.
Proof.
  assert (A: forall v1 v2 v1' v2', Val.inject f v1 v1' -> Val.inject f v2 v2' -> Val.inject f (Val.mul v1 v2) (Val.mul v1' v2')).
  { intros. inv H; simpl; auto. inv H0; auto. }
  intros. destruct addr; simpl in *; FuncInv; InvInject; TrivialExists; eauto using Val.add_inject, Val.offset_ptr_inject with coqlib.
Qed.

Lemma eval_addressing64_inj:
  forall addr sp1 vl1 sp2 vl2 v1,
  (forall id ofs,
      In id (globals_addressing addr) ->
      Val.inject f (Genv.symbol_address ge1 id ofs) (Genv.symbol_address ge2 id ofs)) ->
  Val.inject f sp1 sp2 ->
  Val.inject_list f vl1 vl2 ->
  eval_addressing64 ge1 sp1 addr vl1 = Some v1 ->
  exists v2, eval_addressing64 ge2 sp2 addr vl2 = Some v2 /\ Val.inject f v1 v2.
Proof.
  assert (A: forall v1 v2 v1' v2', Val.inject f v1 v1' -> Val.inject f v2 v2' -> Val.inject f (Val.mull v1 v2) (Val.mull v1' v2')).
  { intros. inv H; simpl; auto. inv H0; auto. }
  intros. destruct addr; simpl in *; FuncInv; InvInject; TrivialExists; eauto using Val.addl_inject, Val.offset_ptr_inject with coqlib.
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
  unfold eval_addressing; intros. destruct Archi.ptr64; eauto using eval_addressing32_inj, eval_addressing64_inj.
Qed.

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
  apply GL; simpl; auto.
  inv H4; simpl; auto.
  inv H4; simpl; auto.
  inv H4; simpl; auto.
  inv H4; simpl; auto.
  inv H4; simpl; auto.
  apply Val.sub_inject; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H3; simpl in H1; inv H1. simpl.
    destruct (Int.eq i0 Int.zero || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H2. TrivialExists.
  inv H4; inv H3; simpl in H1; inv H1. simpl.
    destruct (Int.eq i0 Int.zero); inv H2. TrivialExists.
  inv H4; inv H3; simpl in H1; inv H1. simpl.
    destruct (Int.eq i0 Int.zero || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H2. TrivialExists.
  inv H4; inv H3; simpl in H1; inv H1. simpl.
    destruct (Int.eq i0 Int.zero); inv H2. TrivialExists.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H4; simpl; auto. destruct (Int.ltu n Int.iwordsize); auto.
  inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H4; simpl; auto. destruct (Int.ltu n Int.iwordsize); auto.
  inv H4; simpl in H1; try discriminate. simpl.
  destruct (Int.ltu n (Int.repr 31)); inv H1. TrivialExists.
  inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H4; simpl; auto. destruct (Int.ltu n Int.iwordsize); auto.
  inv H4; simpl; auto.
  inv H4; simpl; auto. destruct (Int.ltu n Int.iwordsize); auto.
  inv H2; simpl; auto. destruct (Int.ltu (Int.sub Int.iwordsize n) Int.iwordsize); auto.
  eapply eval_addressing32_inj; eauto.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.
  inv H4; simpl; auto.
  inv H4; simpl; auto.
  inv H4; simpl; auto.
  inv H4; simpl; auto.
  apply Val.addl_inject; auto.
  apply Val.subl_inject; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H3; simpl in H1; inv H1. simpl.
    destruct (Int64.eq i0 Int64.zero || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H2. TrivialExists.
  inv H4; inv H3; simpl in H1; inv H1. simpl.
    destruct (Int64.eq i0 Int64.zero); inv H2. TrivialExists.
  inv H4; inv H3; simpl in H1; inv H1. simpl.
    destruct (Int64.eq i0 Int64.zero || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H2. TrivialExists.
  inv H4; inv H3; simpl in H1; inv H1. simpl.
    destruct (Int64.eq i0 Int64.zero); inv H2. TrivialExists.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int64.iwordsize'); auto.
  inv H4; simpl; auto. destruct (Int.ltu n Int64.iwordsize'); auto.
  inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int64.iwordsize'); auto.
  inv H4; simpl; auto. destruct (Int.ltu n Int64.iwordsize'); auto.
  inv H4; simpl in H1; try discriminate. simpl. destruct (Int.ltu n (Int.repr 63)); inv H1. TrivialExists.
  inv H4; inv H2; simpl; auto. destruct (Int.ltu i0 Int64.iwordsize'); auto.
  inv H4; simpl; auto. destruct (Int.ltu n Int64.iwordsize'); auto.
  inv H4; simpl; auto.
  eapply eval_addressing64_inj; eauto.
  inv H4; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.
  inv H4; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; inv H2; simpl; auto.
  inv H4; simpl; auto.
  inv H4; simpl; auto.
  inv H4; simpl in H1; inv H1. simpl. destruct (Float.to_int f0); simpl in H2; inv H2.
  exists (Vint i); auto.
  inv H4; simpl in H1; inv H1. simpl. TrivialExists.
  inv H4; simpl in H1; inv H1. simpl. destruct (Float32.to_int f0); simpl in H2; inv H2.
  exists (Vint i); auto.
  inv H4; simpl in H1; inv H1. simpl. TrivialExists.
  inv H4; simpl in H1; inv H1. simpl. destruct (Float.to_long f0); simpl in H2; inv H2.
  exists (Vlong i); auto.
  inv H4; simpl in H1; inv H1. simpl. TrivialExists.
  inv H4; simpl in H1; inv H1. simpl. destruct (Float32.to_long f0); simpl in H2; inv H2.
  exists (Vlong i); auto.
  inv H4; simpl in H1; inv H1. simpl. TrivialExists.
  subst v1. destruct (eval_condition cond vl1 m1) eqn:?.
  exploit eval_condition_inj; eauto. intros EQ; rewrite EQ.
  destruct b; simpl; constructor.
  simpl; constructor.
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
  | OK_addressing, BA_addrglobal _ _ => true
  | OK_addressing, BA_addptr (BA _) (BA_int _ | BA_long _) => true
  | _, _ => false
  end.

Definition builtin_arg_ok
       (A: Type) (ba: builtin_arg A) (c: builtin_arg_constraint) :=
  match ba with
  | (BA _ | BA_splitlong (BA _) (BA _)) => true
  | _ => builtin_arg_ok_1 ba c
  end.  
