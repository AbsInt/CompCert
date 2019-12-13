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

(** Abstract syntax and semantics for AArch64 assembly language *)

Require Import Coqlib Zbits Maps.
Require Import AST Integers Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Locations Conventions.
Require Stacklayout.

(** * Abstract syntax *)

(** Integer registers, floating-point registers. *)

(** In assembly files, [Xn] denotes the full 64-bit register
    and [Wn] the low 32 bits of [Xn]. *)

Inductive ireg: Type :=
  | X0  | X1  | X2  | X3  | X4  | X5  |  X6  | X7
  | X8  | X9  | X10 | X11 | X12 | X13 |  X14 | X15
  | X16 | X17 | X18 | X19 | X20 | X21 |  X22 | X23
  | X24 | X25 | X26 | X27 | X28 | X29 |  X30.

Inductive ireg0: Type :=
  | RR0 (r: ireg) | XZR.

Inductive iregsp: Type :=
  | RR1 (r: ireg) | XSP.

Coercion RR0: ireg >-> ireg0.
Coercion RR1: ireg >-> iregsp.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(** In assembly files, [Dn] denotes the low 64-bit of a vector register,
    and [Sn] the low 32 bits. *)

Inductive freg: Type :=
  | D0  | D1  | D2  | D3  | D4  | D5  |  D6  | D7
  | D8  | D9  | D10 | D11 | D12 | D13 |  D14 | D15
  | D16 | D17 | D18 | D19 | D20 | D21 |  D22 | D23
  | D24 | D25 | D26 | D27 | D28 | D29 |  D30 | D31.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(** Bits in the condition register. *)

Inductive crbit: Type :=
  | CN: crbit    (**r negative *)
  | CZ: crbit    (**r zero *)
  | CC: crbit    (**r carry *)
  | CV: crbit.   (**r overflow *)

Lemma crbit_eq: forall (x y: crbit), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(** We model the following registers of the ARM architecture. *)

Inductive preg: Type :=
  | IR: ireg -> preg   (**r 64- or 32-bit integer registers *)
  | FR: freg -> preg   (**r double- or single-precision float registers *)
  | CR: crbit -> preg  (**r bits in the condition register *)
  | SP: preg           (**r register X31 used as stack pointer *)
  | PC: preg.          (**r program counter *)

Coercion IR: ireg >-> preg.
Coercion FR: freg >-> preg.
Coercion CR: crbit >-> preg.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. apply freg_eq. apply crbit_eq. Defined.

Module PregEq.
  Definition t := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

Definition preg_of_iregsp (r: iregsp) : preg :=
  match r with RR1 r => IR r | XSP => SP end.

Coercion preg_of_iregsp: iregsp >-> preg.

(** Conventional name for return address ([RA]) *)

Notation "'RA'" := X30 (only parsing) : asm.

(** The instruction set.  Most instructions correspond exactly to
  actual AArch64 instructions. See the ARM reference manuals for more
  details.  Some instructions, described below, are
  pseudo-instructions: they expand to canned instruction sequences
  during the printing of the assembly code.  *)

Definition label := positive.

Inductive isize: Type :=
  | W                                                (**r 32-bit integer operation *)
  | X.                                               (**r 64-bit integer operation *)

Inductive fsize: Type :=
  | S                                                (**r 32-bit, single-precision FP operation *)
  | D.                                               (**r 64-bit, double-precision FP operation *)

Inductive testcond : Type :=
  | TCeq: testcond    (**r equal *)
  | TCne: testcond    (**r not equal *)
  | TChs: testcond    (**r unsigned higher or same *)
  | TClo: testcond    (**r unsigned lower *)
  | TCmi: testcond    (**r negative *)
  | TCpl: testcond    (**r positive *)
  | TChi: testcond    (**r unsigned higher *)
  | TCls: testcond    (**r unsigned lower or same *)
  | TCge: testcond    (**r signed greater or equal *)
  | TClt: testcond    (**r signed less than *)
  | TCgt: testcond    (**r signed greater *)
  | TCle: testcond.   (**r signed less than or equal *)

Inductive addressing: Type :=
  | ADimm (base: iregsp) (n: int64)                  (**r base plus immediate offset *)
  | ADreg (base: iregsp) (r: ireg)                   (**r base plus reg *)
  | ADlsl (base: iregsp) (r: ireg) (n: int)          (**r base plus reg LSL n *)
  | ADsxt (base: iregsp) (r: ireg) (n: int)          (**r base plus SIGN-EXT(reg) LSL n *)
  | ADuxt (base: iregsp) (r: ireg) (n: int)          (**r base plus ZERO-EXT(reg) LSL n *)
  | ADadr (base: iregsp) (id: ident) (ofs: ptrofs)   (**r base plus low address of [id + ofs] *)
  | ADpostincr (base: iregsp) (n: int64).            (**r base plus offset; base is updated after *)

Inductive shift_op: Type :=
  | SOnone
  | SOlsl (n: int)
  | SOlsr (n: int)
  | SOasr (n: int)
  | SOror (n: int).

Inductive extend_op: Type :=
  | EOsxtb (n: int)
  | EOsxth (n: int)
  | EOsxtw (n: int)
  | EOuxtb (n: int)
  | EOuxth (n: int)
  | EOuxtw (n: int)
  | EOuxtx (n: int).

Inductive instruction: Type :=
  (** Branches *)
  | Pb (lbl: label)                                                   (**r branch *)
  | Pbc (c: testcond) (lbl: label)                                    (**r conditional branch *)
  | Pbl (id: ident) (sg: signature)                                   (**r jump to function and link *)
  | Pbs (id: ident) (sg: signature)                                   (**r jump to function *)
  | Pblr (r: ireg) (sg: signature)                                    (**r indirect jump and link *)
  | Pbr (r: ireg) (sg: signature)                                     (**r indirect jump *)
  | Pret (r: ireg)                                                    (**r return *)
  | Pcbnz (sz: isize) (r: ireg) (lbl: label)                          (**r branch if not zero *)
  | Pcbz (sz: isize) (r: ireg) (lbl: label)                           (**r branch if zero *)
  | Ptbnz (sz: isize) (r: ireg) (n: int) (lbl: label)                 (**r branch if bit n is not zero *)
  | Ptbz (sz: isize) (r: ireg) (n: int) (lbl: label)                  (**r branch if bit n is zero *)
  (** Memory loads and stores *)
  | Pldrw (rd: ireg) (a: addressing)                                  (**r load int32 *)
  | Pldrw_a (rd: ireg) (a: addressing)                                (**r load int32 as any32 *)
  | Pldrx (rd: ireg) (a: addressing)                                  (**r load int64 *)
  | Pldrx_a (rd: ireg) (a: addressing)                                (**r load int64 as any64 *)
  | Pldrb (sz: isize) (rd: ireg) (a: addressing)                      (**r load int8, zero-extend *)
  | Pldrsb (sz: isize) (rd: ireg) (a: addressing)                     (**r load int8, sign-extend *)
  | Pldrh (sz: isize) (rd: ireg) (a: addressing)                      (**r load int16, zero-extend *)
  | Pldrsh (sz: isize) (rd: ireg) (a: addressing)                     (**r load int16, sign-extend *)
  | Pldrzw (rd: ireg) (a: addressing)                                 (**r load int32, zero-extend to int64 *)
  | Pldrsw (rd: ireg) (a: addressing)                                 (**r load int32, sign-extend to int64 *)
  | Pldp (rd1 rd2: ireg) (a: addressing)                               (**r load two int64 *)
  | Pstrw (rs: ireg) (a: addressing)                                  (**r store int32 *)
  | Pstrw_a (rs: ireg) (a: addressing)                                (**r store int32 as any32 *)
  | Pstrx (rs: ireg) (a: addressing)                                  (**r store int64 *)
  | Pstrx_a (rs: ireg) (a: addressing)                                (**r store int64 as any64 *)
  | Pstrb (rs: ireg) (a: addressing)                                  (**r store int8 *)
  | Pstrh (rs: ireg) (a: addressing)                                  (**r store int16 *)
  | Pstp (rs1 rs2: ireg) (a: addressing)                              (**r store two int64 *)
  (** Integer arithmetic, immediate *)
  | Paddimm (sz: isize) (rd: iregsp) (r1: iregsp) (n: Z)              (**r addition *)
  | Psubimm (sz: isize) (rd: iregsp) (r1: iregsp) (n: Z)              (**r subtraction *)
  | Pcmpimm (sz: isize) (r1: ireg) (n: Z)                             (**r compare *)
  | Pcmnimm (sz: isize) (r1: ireg) (n: Z)                             (**r compare negative *)
  (** Move integer register *)
  | Pmov (rd: iregsp) (r1: iregsp)
  (** Logical, immediate *)
  | Pandimm (sz: isize) (rd: ireg) (r1: ireg0) (n: Z)                 (**r and *)
  | Peorimm (sz: isize) (rd: ireg) (r1: ireg0) (n: Z)                 (**r xor *)
  | Porrimm (sz: isize) (rd: ireg) (r1: ireg0) (n: Z)                 (**r or *)
  | Ptstimm (sz: isize) (r1: ireg) (n: Z)                             (**r and, then set flags *)
  (** Move wide immediate *)
  | Pmovz (sz: isize) (rd: ireg) (n: Z) (pos: Z)                      (**r move [n << pos] to [rd] *)
  | Pmovn (sz: isize) (rd: ireg) (n: Z) (pos: Z)                      (**r move [NOT(n << pos)] to [rd] *)
  | Pmovk (sz: isize) (rd: ireg) (n: Z) (pos: Z)                      (**r insert 16 bits of [n] at [pos] in rd *)
  (** PC-relative addressing *)
  | Padrp (rd: ireg) (id: ident) (ofs: ptrofs)                        (**r set [rd] to high address of [id + ofs] *)
  | Paddadr (rd: ireg) (r1: ireg) (id: ident) (ofs: ptrofs)           (**r add the low address of [id + ofs] *)
  (** Bit-field operations *)
  | Psbfiz (sz: isize) (rd: ireg) (r1: ireg) (r: int) (s: Z)          (**r sign extend and shift left *)
  | Psbfx (sz: isize) (rd: ireg) (r1: ireg) (r: int) (s: Z)           (**r shift right and sign extend *)
  | Pubfiz (sz: isize) (rd: ireg) (r1: ireg) (r: int) (s: Z)          (**r zero extend and shift left *)
  | Pubfx (sz: isize) (rd: ireg) (r1: ireg) (r: int) (s: Z)           (**r shift right and zero extend *)
  (** Integer arithmetic, shifted register *)
  | Padd (sz: isize) (rd: ireg) (r1: ireg0) (r2: ireg) (s: shift_op)  (**r addition *)
  | Psub (sz: isize) (rd: ireg) (r1: ireg0) (r2: ireg) (s: shift_op)  (**r subtraction *)
  | Pcmp (sz: isize) (r1: ireg0) (r2: ireg) (s: shift_op)             (**r compare *)
  | Pcmn (sz: isize) (r1: ireg0) (r2: ireg) (s: shift_op)             (**r compare negative *)
  (** Integer arithmetic, extending register *)
  | Paddext (rd: iregsp) (r1: iregsp) (r2: ireg) (x: extend_op)       (**r int64-int32 add *)
  | Psubext (rd: iregsp) (r1: iregsp) (r2: ireg) (x: extend_op)       (**r int64-int32 sub *)
  | Pcmpext (r1: ireg) (r2: ireg) (x: extend_op)                      (**r int64-int32 cmp *)
  | Pcmnext (r1: ireg) (r2: ireg) (x: extend_op)                      (**r int64-int32 cmn *)
  (** Logical, shifted register *)
  | Pand (sz: isize) (rd: ireg) (r1: ireg0) (r2: ireg) (s: shift_op)  (**r and *)
  | Pbic (sz: isize) (rd: ireg) (r1: ireg0) (r2: ireg) (s: shift_op)  (**r and-not *)
  | Peon (sz: isize) (rd: ireg) (r1: ireg0) (r2: ireg) (s: shift_op)  (**r xor-not *)
  | Peor (sz: isize) (rd: ireg) (r1: ireg0) (r2: ireg) (s: shift_op)  (**r xor *)
  | Porr (sz: isize) (rd: ireg) (r1: ireg0) (r2: ireg) (s: shift_op)  (**r or *)
  | Porn (sz: isize) (rd: ireg) (r1: ireg0) (r2: ireg) (s: shift_op)  (**r or-not *)
  | Ptst (sz: isize) (r1: ireg0) (r2: ireg) (s: shift_op)             (**r and, then set flags *)
  (** Variable shifts *)
  | Pasrv (sz: isize) (rd: ireg) (r1 r2: ireg)                        (**r arithmetic right shift *)
  | Plslv (sz: isize) (rd: ireg) (r1 r2: ireg)                        (**r left shift *)
  | Plsrv (sz: isize) (rd: ireg) (r1 r2: ireg)                        (**r logical right shift *)
  | Prorv (sz: isize) (rd: ireg) (r1 r2: ireg)                        (**r rotate right *)
  (** Bit operations *)
  | Pcls (sz: isize) (rd r1: ireg)                                    (**r count leading sign bits *)
  | Pclz (sz: isize) (rd r1: ireg)                                    (**r count leading zero bits *)
  | Prev (sz: isize) (rd r1: ireg)                                    (**r reverse bytes *)
  | Prev16 (sz: isize) (rd r1: ireg)                                  (**r reverse bytes in each 16-bit word *)
  (** Conditional data processing *)
  | Pcsel (rd: ireg) (r1 r2: ireg) (c: testcond)                      (**r int conditional move *)
  | Pcset (rd: ireg) (c: testcond)                                    (**r set to 1/0 if cond is true/false *)
(*
  | Pcsetm (rd: ireg) (c: testcond)                                   (**r set to -1/0 if cond is true/false *)
*)
  (** Integer multiply/divide *)
  | Pmadd (sz: isize) (rd: ireg) (r1 r2: ireg) (r3: ireg0)            (**r multiply-add *)
  | Pmsub (sz: isize) (rd: ireg) (r1 r2: ireg) (r3: ireg0)            (**r multiply-sub *)
  | Psmulh (rd: ireg) (r1 r2: ireg)                                   (**r signed multiply high *)
  | Pumulh (rd: ireg) (r1 r2: ireg)                                   (**r unsigned multiply high *)
  | Psdiv (sz: isize) (rd: ireg) (r1 r2: ireg)                        (**r signed division *)
  | Pudiv (sz: isize) (rd: ireg) (r1 r2: ireg)                        (**r unsigned division *)
  (** Floating-point loads and stores *)
  | Pldrs (rd: freg) (a: addressing)                                  (**r load float32 (single precision) *)
  | Pldrd (rd: freg) (a: addressing)                                  (**r load float64 (double precision) *)
  | Pldrd_a (rd: freg) (a: addressing)                                (**r load float64 as any64 *)
  | Pstrs (rs: freg) (a: addressing)                                  (**r store float32 *)
  | Pstrd (rs: freg) (a: addressing)                                  (**r store float64 *)
  | Pstrd_a (rs: freg) (a: addressing)                                (**r store float64 as any64 *)
  (** Floating-point move *)
  | Pfmov (rd r1: freg)
  | Pfmovimms (rd: freg) (f: float32)                                 (**r load float32 constant *)
  | Pfmovimmd (rd: freg) (f: float)                                   (**r load float64 constant *)
  | Pfmovi (fsz: fsize) (rd: freg) (r1: ireg0)                        (**r copy int reg to FP reg *)
  (** Floating-point conversions *)
  | Pfcvtds (rd r1: freg)                                             (**r convert float32 to float64 *)
  | Pfcvtsd (rd r1: freg)                                             (**r convert float64 to float32 *)
  | Pfcvtzs (isz: isize) (fsz: fsize) (rd: ireg) (r1: freg)           (**r convert float to signed int *)
  | Pfcvtzu (isz: isize) (fsz: fsize) (rd: ireg) (r1: freg)           (**r convert float to unsigned int *)
  | Pscvtf (fsz: fsize) (isz: isize) (rd: freg) (r1: ireg)            (**r convert signed int to float *)
  | Pucvtf (fsz: fsize) (isz: isize) (rd: freg) (r1: ireg)            (**r convert unsigned int to float *)
  (** Floating-point arithmetic *)
  | Pfabs (sz: fsize) (rd r1: freg)                                   (**r absolute value *)
  | Pfneg (sz: fsize) (rd r1: freg)                                   (**r negation *)
  | Pfsqrt (sz: fsize) (rd r1: freg)                                  (**r square root *)
  | Pfadd (sz: fsize) (rd r1 r2: freg)                                (**r addition *)
  | Pfdiv (sz: fsize) (rd r1 r2: freg)                                (**r division *)
  | Pfmul (sz: fsize) (rd r1 r2: freg)                                (**r multiplication *)
  | Pfnmul (sz: fsize) (rd r1 r2: freg)                               (**r multiply-negate *)
  | Pfsub (sz: fsize) (rd r1 r2: freg)                                (**r subtraction *)
  | Pfmadd (sz: fsize) (rd r1 r2 r3: freg)                            (**r [rd = r3 + r1 * r2] *)
  | Pfmsub (sz: fsize) (rd r1 r2 r3: freg)                            (**r [rd = r3 - r1 * r2] *)
  | Pfnmadd (sz: fsize) (rd r1 r2 r3: freg)                           (**r [rd = - r3 - r1 * r2] *)
  | Pfnmsub (sz: fsize) (rd r1 r2 r3: freg)                           (**r [rd = - r3 + r1 * r2] *)
  (** Floating-point comparison *)
  | Pfcmp (sz: fsize) (r1 r2: freg)                                   (**r compare [r1] and [r2] *)
  | Pfcmp0 (sz: fsize) (r1: freg)                                     (**r compare [r1] and [+0.0] *)
  (** Floating-point conditional select *)
  | Pfsel (rd r1 r2: freg) (cond: testcond)
  (** Pseudo-instructions *)
  | Pallocframe (sz: Z) (linkofs: ptrofs)                             (**r allocate new stack frame *)
  | Pfreeframe (sz: Z) (linkofs: ptrofs)                              (**r deallocate stack frame and restore previous frame *)
  | Plabel (lbl: label)                                               (**r define a code label *)
  | Ploadsymbol (rd: ireg) (id: ident)                                (**r load the address of [id] *)
  | Pcvtsw2x (rd: ireg) (r1: ireg)                                    (**r sign-extend 32-bit int to 64-bit *)
  | Pcvtuw2x (rd: ireg) (r1: ireg)                                    (**r zero-extend 32-bit int to 64-bit *)
  | Pcvtx2w (rd: ireg)                                                (**r retype a 64-bit int as a 32-bit int *)
  | Pbtbl (r1: ireg) (tbl: list label)                                (**r N-way branch through a jump table *)
  | Pbuiltin (ef: external_function)
             (args: list (builtin_arg preg)) (res: builtin_res preg)  (**r built-in function (pseudo) *)
  | Pcfi_adjust (ofs: int)                                            (**r .cfi_adjust debug directive *)
  | Pcfi_rel_offset (ofs: int)                                        (**r .cfi_rel_offset debug directive *)
.

Definition code := list instruction.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain (but do not enforce)
  the convention that integer registers are mapped to values of
  type [Tint], float registers to values of type [Tfloat],
  and condition bits to either [Vzero] or [Vone]. *)

Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef unit.

(** The value of an [ireg0] is either the value of the integer register,
    or 0. *)

Definition ir0w (rs: regset) (r: ireg0) : val :=
  match r with RR0 r => rs (IR r) | XZR => Vint Int.zero end.
Definition ir0x (rs: regset) (r: ireg0) : val :=
  match r with RR0 r => rs (IR r) | XZR => Vlong Int64.zero end.

(** Concise notations for accessing and updating the values of registers. *)

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm.
Notation "a ## b" := (ir0w a b) (at level 1, only parsing) : asm.
Notation "a ### b" := (ir0x a b) (at level 1, only parsing) : asm.

Open Scope asm.

(** Undefining some registers *)

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.

(** Undefining the condition codes *)

Definition undef_flags (rs: regset) : regset :=
  fun r => match r with CR _ => Vundef | _ => rs r end.

(** Assigning a register pair *)

Definition set_pair (p: rpair preg) (v: val) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

(** Assigning the result of a builtin *)

Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

(** The two functions below axiomatize how the linker processes
  symbolic references [symbol + offset].  It computes the
  difference between the address and the PC, and splits it into:
  - 12 low bits usable as an offset in an addressing mode;
  - 21 high bits usable as argument to the ADRP instruction.

  In CompCert's model, we cannot really describe PC-relative addressing,
  but we can claim that the address of [symbol + offset] decomposes
  as the sum of
  - a low part, usable as an offset in an addressing mode;
  - a high part, usable as argument to the ADRP instruction. *)

Parameter symbol_low: genv -> ident -> ptrofs -> val.
Parameter symbol_high: genv -> ident -> ptrofs -> val.

Axiom symbol_high_low:
  forall (ge: genv) (id: ident) (ofs: ptrofs),
  Val.addl (symbol_high ge id ofs) (symbol_low ge id ofs) = Genv.symbol_address ge id ofs.

Section RELSEM.

Variable ge: genv.

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate. destruct (peq lbl lbl0); congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome: Type :=
  | Next: regset -> mem -> outcome
  | Stuck: outcome.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]). *)

Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.offset_ptr rs#PC Ptrofs.one).

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _ => Stuck
    end
  end.

(** Testing a condition *)

Definition eval_testcond (c: testcond) (rs: regset) : option bool :=
  match c with
  | TCeq =>                             (**r equal *)
      match rs#CZ with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | TCne =>                             (**r not equal *)
      match rs#CZ with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | TClo =>                             (**r unsigned less than  *)
      match rs#CC with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | TCls =>                             (**r unsigned less or equal *)
      match rs#CC, rs#CZ with
      | Vint c, Vint z => Some (Int.eq c Int.zero || Int.eq z Int.one)
      | _, _ => None
      end
  | TChs =>                             (**r unsigned greater or equal *)
      match rs#CC with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | TChi =>                             (**r unsigned greater *)
      match rs#CC, rs#CZ with
      | Vint c, Vint z => Some (Int.eq c Int.one && Int.eq z Int.zero)
      | _, _ => None
      end
  | TClt =>                             (**r signed less than *)
      match rs#CV, rs#CN with
      | Vint o, Vint s => Some (Int.eq (Int.xor o s) Int.one)
      | _, _ => None
      end
  | TCle =>                             (**r signed less or equal *)
      match rs#CV, rs#CN, rs#CZ with
      | Vint o, Vint s, Vint z => Some (Int.eq (Int.xor o s) Int.one || Int.eq z Int.one)
      | _, _, _ => None
      end
  | TCge =>                             (**r signed greater or equal *)
      match rs#CV, rs#CN with
      | Vint o, Vint s => Some (Int.eq (Int.xor o s) Int.zero)
      | _, _ => None
      end
  | TCgt =>                             (**r signed greater *)
      match rs#CV, rs#CN, rs#CZ with
      | Vint o, Vint s, Vint z => Some (Int.eq (Int.xor o s) Int.zero && Int.eq z Int.zero)
      | _, _, _ => None
      end
  | TCpl =>                             (**r positive *)
      match rs#CN with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | TCmi =>                             (**r negative *)
      match rs#CN with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  end.

(** Integer "is zero?" test *)

Definition eval_testzero (sz: isize) (v: val) (m: mem): option bool :=
  match sz with
  | W => Val.cmpu_bool (Mem.valid_pointer m) Ceq v (Vint Int.zero)
  | X => Val.cmplu_bool (Mem.valid_pointer m) Ceq v (Vlong Int64.zero)
  end.

(** Integer "bit is set?" test *)

Definition eval_testbit (sz: isize) (v: val) (n: int): option bool :=
  match sz with
  | W => Val.cmp_bool Cne (Val.and v (Vint (Int.shl Int.one n))) (Vint Int.zero)
  | X => Val.cmpl_bool Cne (Val.andl v (Vlong (Int64.shl' Int64.one n))) (Vlong Int64.zero)
  end.

(** Evaluating an addressing mode *)

Definition eval_addressing (a: addressing) (rs: regset): val :=
  match a with
  | ADimm base n => Val.addl rs#base (Vlong n)
  | ADreg base r => Val.addl rs#base rs#r
  | ADlsl base r n => Val.addl rs#base (Val.shll rs#r (Vint n))
  | ADsxt base r n => Val.addl rs#base (Val.shll (Val.longofint rs#r) (Vint n))
  | ADuxt base r n => Val.addl rs#base (Val.shll (Val.longofintu rs#r) (Vint n))
  | ADadr base id ofs => Val.addl rs#base (symbol_low ge id ofs)
  | ADpostincr base n => Vundef (* not modeled yet *)
  end.

(** Auxiliaries for memory accesses *)

Definition exec_load (chunk: memory_chunk) (transf: val -> val)
                     (a: addressing) (r: preg) (rs: regset) (m: mem) :=
  match Mem.loadv chunk m (eval_addressing a rs) with
  | None => Stuck
  | Some v => Next (nextinstr (rs#r <- (transf v))) m
  end.

Definition exec_store (chunk: memory_chunk)
                      (a: addressing) (v: val)
                      (rs: regset) (m: mem) :=
  match Mem.storev chunk m (eval_addressing a rs) v with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

(** Comparisons *)

Definition compare_int (rs: regset) (v1 v2: val) (m: mem) :=
  rs#CN <- (Val.negative (Val.sub v1 v2))
    #CZ <- (Val.cmpu (Mem.valid_pointer m) Ceq v1 v2)
    #CC <- (Val.cmpu (Mem.valid_pointer m) Cge v1 v2)
    #CV <- (Val.sub_overflow v1 v2).

Definition compare_long (rs: regset) (v1 v2: val) (m: mem) :=
  rs#CN <- (Val.negativel (Val.subl v1 v2))
    #CZ <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Ceq v1 v2))
    #CC <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Cge v1 v2))
    #CV <- (Val.subl_overflow v1 v2).

(** Semantics of [fcmp] instructions:
<<
==	N=0 Z=1 C=1 V=0
<	N=1 Z=0 C=0 V=0
>	N=0 Z=0 C=1 V=0
unord	N=0 Z=0 C=1 V=1
>>
*)

Definition compare_float (rs: regset) (v1 v2: val) :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 =>
      rs#CN <- (Val.of_bool (Float.cmp Clt f1 f2))
        #CZ <- (Val.of_bool (Float.cmp Ceq f1 f2))
        #CC <- (Val.of_bool (negb (Float.cmp Clt f1 f2)))
        #CV <- (Val.of_bool (negb (Float.ordered f1 f2)))
  | _, _ =>
      rs#CN <- Vundef
        #CZ <- Vundef
        #CC <- Vundef
        #CV <- Vundef
  end.

Definition compare_single (rs: regset) (v1 v2: val) :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 =>
      rs#CN <- (Val.of_bool (Float32.cmp Clt f1 f2))
        #CZ <- (Val.of_bool (Float32.cmp Ceq f1 f2))
        #CC <- (Val.of_bool (negb (Float32.cmp Clt f1 f2)))
        #CV <- (Val.of_bool (negb (Float32.ordered f1 f2)))
  | _, _ =>
      rs#CN <- Vundef
        #CZ <- Vundef
        #CC <- Vundef
        #CV <- Vundef
  end.

(** Insertion of bits into an integer *)

Definition insert_in_int (x: val) (y: Z) (pos: Z) (len: Z) : val :=
  match x with
  | Vint n => Vint (Int.repr (Zinsert (Int.unsigned n) y pos len))
  | _ => Vundef
  end.

Definition insert_in_long (x: val) (y: Z) (pos: Z) (len: Z) : val :=
  match x with
  | Vlong n => Vlong (Int64.repr (Zinsert (Int64.unsigned n) y pos len))
  | _ => Vundef
  end.

(** Evaluation of shifted operands *)

Definition eval_shift_op_int (v: val) (s: shift_op): val :=
  match s with
  | SOnone => v
  | SOlsl n => Val.shl v (Vint n)
  | SOlsr n => Val.shru v (Vint n)
  | SOasr n => Val.shr v (Vint n)
  | SOror n => Val.ror v (Vint n)
  end.

Definition eval_shift_op_long (v: val) (s: shift_op): val :=
  match s with
  | SOnone => v
  | SOlsl n => Val.shll v (Vint n)
  | SOlsr n => Val.shrlu v (Vint n)
  | SOasr n => Val.shrl v (Vint n)
  | SOror n => Val.rorl v (Vint n)
  end.

(** Evaluation of sign- or zero- extended operands *)

Definition eval_extend (v: val) (x: extend_op): val :=
  match x with
  | EOsxtb n => Val.shll (Val.longofint (Val.sign_ext 8 v)) (Vint n)
  | EOsxth n => Val.shll (Val.longofint (Val.sign_ext 16 v)) (Vint n)
  | EOsxtw n => Val.shll (Val.longofint v) (Vint n)
  | EOuxtb n => Val.shll (Val.longofintu (Val.zero_ext 8 v)) (Vint n)
  | EOuxth n => Val.shll (Val.longofintu (Val.zero_ext 16 v)) (Vint n)
  | EOuxtw n => Val.shll (Val.longofintu v) (Vint n)
  | EOuxtx n => Val.shll v (Vint n)
  end.

(** Bit-level conversion from integers to FP numbers *)

Definition float32_of_bits (v: val): val :=
  match v with
  | Vint n => Vsingle (Float32.of_bits n)
  | _ => Vundef
  end.

Definition float64_of_bits (v: val): val :=
  match v with
  | Vlong n => Vfloat (Float.of_bits n)
  | _ => Vundef
  end.

(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual AArch64 instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the ARMv8 reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above.

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the code we
    generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction.
*)

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  (** Branches *)
  | Pb lbl =>
      goto_label f lbl rs m
  | Pbc cond lbl =>
      match eval_testcond cond rs with
      | Some true => goto_label f lbl rs m
      | Some false => Next (nextinstr rs) m
      | None => Stuck
      end
  | Pbl id sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pbs id sg =>
      Next (rs#PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pblr r sg =>
      Next (rs#RA <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (rs#r)) m
  | Pbr r sg =>
      Next (rs#PC <- (rs#r)) m
  | Pret r =>
      Next (rs#PC <- (rs#r)) m
  | Pcbnz sz r lbl =>
      match eval_testzero sz rs#r m with
      | Some true => Next (nextinstr rs) m
      | Some false => goto_label f lbl rs m
      | None => Stuck
      end
  | Pcbz sz r lbl =>
      match eval_testzero sz rs#r m with
      | Some true => goto_label f lbl rs m
      | Some false => Next (nextinstr rs) m
      | None => Stuck
      end
  | Ptbnz sz r n lbl =>
      match eval_testbit sz rs#r n with
      | Some true => goto_label f lbl rs m
      | Some false => Next (nextinstr rs) m
      | None => Stuck
      end
  | Ptbz sz r n lbl =>
      match eval_testbit sz rs#r n with
      | Some true => Next (nextinstr rs) m
      | Some false => goto_label f lbl rs m
      | None => Stuck
      end
  (** Memory loads and stores *)
  | Pldrw rd a =>
      exec_load Mint32 (fun v => v) a rd rs m
  | Pldrw_a rd a =>
      exec_load Many32 (fun v => v) a rd rs m
  | Pldrx rd a =>
      exec_load Mint64 (fun v => v) a rd rs m
  | Pldrx_a rd a =>
      exec_load Many64 (fun v => v) a rd rs m
  | Pldrb W rd a =>
      exec_load Mint8unsigned (fun v => v) a rd rs m
  | Pldrb X rd a =>
      exec_load Mint8unsigned Val.longofintu a rd rs m
  | Pldrsb W rd a =>
      exec_load Mint8signed (fun v => v) a rd rs m
  | Pldrsb X rd a =>
      exec_load Mint8signed Val.longofint a rd rs m
  | Pldrh W rd a =>
      exec_load Mint16unsigned (fun v => v) a rd rs m
  | Pldrh X rd a =>
      exec_load Mint16unsigned Val.longofintu a rd rs m
  | Pldrsh W rd a =>
      exec_load Mint16signed (fun v => v) a rd rs m
  | Pldrsh X rd a =>
      exec_load Mint16signed Val.longofint a rd rs m
  | Pldrzw rd a =>
      exec_load Mint32 Val.longofintu a rd rs m
  | Pldrsw rd a =>
      exec_load Mint32 Val.longofint a rd rs m
  | Pstrw r a =>
      exec_store Mint32 a rs#r rs m
  | Pstrw_a r a =>
      exec_store Many32 a rs#r rs m
  | Pstrx r a =>
      exec_store Mint64 a rs#r rs m
  | Pstrx_a r a =>
      exec_store Many64 a rs#r rs m
  | Pstrb r a =>
      exec_store Mint8unsigned a rs#r rs m
  | Pstrh r a =>
      exec_store Mint16unsigned a rs#r rs m
  (** Integer arithmetic, immediate *)
  | Paddimm W rd r1 n =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 (Vint (Int.repr n))))) m
  | Paddimm X rd r1 n =>
      Next (nextinstr (rs#rd <- (Val.addl rs#r1 (Vlong (Int64.repr n))))) m
  | Psubimm W rd r1 n =>
      Next (nextinstr (rs#rd <- (Val.sub rs#r1 (Vint (Int.repr n))))) m
  | Psubimm X rd r1 n =>
      Next (nextinstr (rs#rd <- (Val.subl rs#r1 (Vlong (Int64.repr n))))) m
  | Pcmpimm W r1 n =>
      Next (nextinstr (compare_int rs rs#r1 (Vint (Int.repr n)) m)) m
  | Pcmpimm X r1 n =>
      Next (nextinstr (compare_long rs rs#r1 (Vlong (Int64.repr n)) m)) m
  | Pcmnimm W r1 n =>
      Next (nextinstr (compare_int rs rs#r1 (Vint (Int.neg (Int.repr n))) m)) m
  | Pcmnimm X r1 n =>
      Next (nextinstr (compare_long rs rs#r1 (Vlong (Int64.neg (Int64.repr n))) m)) m
  (** Move integer register *)
  | Pmov rd r1 =>
      Next (nextinstr (rs#rd <- (rs#r1))) m
  (** Logical, immediate *)
  | Pandimm W rd r1 n =>
      Next (nextinstr (rs#rd <- (Val.and rs##r1 (Vint (Int.repr n))))) m
  | Pandimm X rd r1 n =>
      Next (nextinstr (rs#rd <- (Val.andl rs###r1 (Vlong (Int64.repr n))))) m
  | Peorimm W rd r1 n =>
      Next (nextinstr (rs#rd <- (Val.xor rs##r1 (Vint (Int.repr n))))) m
  | Peorimm X rd r1 n =>
      Next (nextinstr (rs#rd <- (Val.xorl rs###r1 (Vlong (Int64.repr n))))) m
  | Porrimm W rd r1 n =>
      Next (nextinstr (rs#rd <- (Val.or rs##r1 (Vint (Int.repr n))))) m
  | Porrimm X rd r1 n =>
      Next (nextinstr (rs#rd <- (Val.orl rs###r1 (Vlong (Int64.repr n))))) m
  | Ptstimm W r1 n =>
      Next (nextinstr (compare_int rs (Val.and rs#r1 (Vint (Int.repr n))) (Vint Int.zero) m)) m
  | Ptstimm X r1 n =>
      Next (nextinstr (compare_long rs (Val.andl rs#r1 (Vlong (Int64.repr n))) (Vlong Int64.zero) m)) m
  (** Move wide immediate *)
  | Pmovz W rd n pos =>
      Next (nextinstr (rs#rd <- (Vint (Int.repr (Z.shiftl n pos))))) m
  | Pmovz X rd n pos =>
      Next (nextinstr (rs#rd <- (Vlong (Int64.repr (Z.shiftl n pos))))) m
  | Pmovn W rd n pos =>
      Next (nextinstr (rs#rd <- (Vint (Int.repr (Z.lnot (Z.shiftl n pos)))))) m
  | Pmovn X rd n pos =>
      Next (nextinstr (rs#rd <- (Vlong (Int64.repr (Z.lnot (Z.shiftl n pos)))))) m
  | Pmovk W rd n pos =>
      Next (nextinstr (rs#rd <- (insert_in_int rs#rd n pos 16))) m
  | Pmovk X rd n pos =>
      Next (nextinstr (rs#rd <- (insert_in_long rs#rd n pos 16))) m
  (** PC-relative addressing *)
  | Padrp rd id ofs =>
      Next (nextinstr (rs#rd <- (symbol_high ge id ofs))) m
  | Paddadr rd r1 id ofs =>
      Next (nextinstr (rs#rd <- (Val.addl rs#r1 (symbol_low ge id ofs)))) m
  (** Bit-field operations *)
  | Psbfiz W rd r1 r s =>
      Next (nextinstr (rs#rd <- (Val.shl (Val.sign_ext s rs#r1) (Vint r)))) m
  | Psbfiz X rd r1 r s =>
      Next (nextinstr (rs#rd <- (Val.shll (Val.sign_ext_l s rs#r1) (Vint r)))) m
  | Psbfx W rd r1 r s =>
      Next (nextinstr (rs#rd <- (Val.sign_ext s (Val.shr rs#r1 (Vint r))))) m
  | Psbfx X rd r1 r s =>
      Next (nextinstr (rs#rd <- (Val.sign_ext_l s (Val.shrl rs#r1 (Vint r))))) m
  | Pubfiz W rd r1 r s =>
      Next (nextinstr (rs#rd <- (Val.shl (Val.zero_ext s rs#r1) (Vint r)))) m
  | Pubfiz X rd r1 r s =>
      Next (nextinstr (rs#rd <- (Val.shll (Val.zero_ext_l s rs#r1) (Vint r)))) m
  | Pubfx W rd r1 r s =>
      Next (nextinstr (rs#rd <- (Val.zero_ext s (Val.shru rs#r1 (Vint r))))) m
  | Pubfx X rd r1 r s =>
      Next (nextinstr (rs#rd <- (Val.zero_ext_l s (Val.shrlu rs#r1 (Vint r))))) m
  (** Integer arithmetic, shifted register *)
  | Padd W rd r1 r2 s =>
      Next (nextinstr (rs#rd <- (Val.add rs##r1 (eval_shift_op_int rs#r2 s)))) m
  | Padd X rd r1 r2 s =>
      Next (nextinstr (rs#rd <- (Val.addl rs###r1 (eval_shift_op_long rs#r2 s)))) m
  | Psub W rd r1 r2 s =>
      Next (nextinstr (rs#rd <- (Val.sub rs##r1 (eval_shift_op_int rs#r2 s)))) m
  | Psub X rd r1 r2 s =>
      Next (nextinstr (rs#rd <- (Val.subl rs###r1 (eval_shift_op_long rs#r2 s)))) m
  | Pcmp W r1 r2 s =>
      Next (nextinstr (compare_int rs rs##r1 (eval_shift_op_int rs#r2 s) m)) m
  | Pcmp X r1 r2 s =>
      Next (nextinstr (compare_long rs rs###r1 (eval_shift_op_long rs#r2 s) m)) m
  | Pcmn W r1 r2 s =>
      Next (nextinstr (compare_int rs rs##r1 (Val.neg (eval_shift_op_int rs#r2 s)) m)) m
  | Pcmn X r1 r2 s =>
      Next (nextinstr (compare_long rs rs###r1 (Val.negl (eval_shift_op_long rs#r2 s)) m)) m
  (** Integer arithmetic, extending register *)
  | Paddext rd r1 r2 x =>
      Next (nextinstr (rs#rd <- (Val.addl rs#r1 (eval_extend rs#r2 x)))) m
  | Psubext rd r1 r2 x =>
      Next (nextinstr (rs#rd <- (Val.subl rs#r1 (eval_extend rs#r2 x)))) m
  | Pcmpext r1 r2 x =>
      Next (nextinstr (compare_long rs rs#r1 (eval_extend rs#r2 x) m)) m
  | Pcmnext r1 r2 x =>
      Next (nextinstr (compare_long rs rs#r1 (Val.negl (eval_extend rs#r2 x)) m)) m
  (** Logical, shifted register *)
  | Pand W rd r1 r2 s =>
      Next (nextinstr (rs#rd <- (Val.and rs##r1 (eval_shift_op_int rs#r2 s)))) m
  | Pand X rd r1 r2 s =>
      Next (nextinstr (rs#rd <- (Val.andl rs###r1 (eval_shift_op_long rs#r2 s)))) m
  | Pbic W rd r1 r2 s =>
      Next (nextinstr (rs#rd <- (Val.and rs##r1 (Val.notint (eval_shift_op_int rs#r2 s))))) m
  | Pbic X rd r1 r2 s =>
      Next (nextinstr (rs#rd <- (Val.andl rs###r1 (Val.notl (eval_shift_op_long rs#r2 s))))) m
  | Peon W rd r1 r2 s =>
      Next (nextinstr (rs#rd <- (Val.xor rs##r1 (Val.notint (eval_shift_op_int rs#r2 s))))) m
  | Peon X rd r1 r2 s =>
      Next (nextinstr (rs#rd <- (Val.xorl rs###r1 (Val.notl (eval_shift_op_long rs#r2 s))))) m
  | Peor W rd r1 r2 s =>
      Next (nextinstr (rs#rd <- (Val.xor rs##r1 (eval_shift_op_int rs#r2 s)))) m
  | Peor X rd r1 r2 s =>
      Next (nextinstr (rs#rd <- (Val.xorl rs###r1 (eval_shift_op_long rs#r2 s)))) m
  | Porr W rd r1 r2 s =>
      Next (nextinstr (rs#rd <- (Val.or rs##r1 (eval_shift_op_int rs#r2 s)))) m
  | Porr X rd r1 r2 s =>
      Next (nextinstr (rs#rd <- (Val.orl rs###r1 (eval_shift_op_long rs#r2 s)))) m
  | Porn W rd r1 r2 s =>
      Next (nextinstr (rs#rd <- (Val.or rs##r1 (Val.notint (eval_shift_op_int rs#r2 s))))) m
  | Porn X rd r1 r2 s =>
      Next (nextinstr (rs#rd <- (Val.orl rs###r1 (Val.notl (eval_shift_op_long rs#r2 s))))) m
  | Ptst W r1 r2 s =>
      Next (nextinstr (compare_int rs (Val.and rs##r1 (eval_shift_op_int rs#r2 s)) (Vint Int.zero) m)) m
  | Ptst X r1 r2 s =>
      Next (nextinstr (compare_long rs (Val.andl rs###r1 (eval_shift_op_long rs#r2 s)) (Vlong Int64.zero) m)) m
  (** Variable shifts *)
  | Pasrv W rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shr rs#r1 rs#r2))) m
  | Pasrv X rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shrl rs#r1 rs#r2))) m
  | Plslv W rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shl rs#r1 rs#r2))) m
  | Plslv X rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shll rs#r1 rs#r2))) m
  | Plsrv W rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shru rs#r1 rs#r2))) m
  | Plsrv X rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shrlu rs#r1 rs#r2))) m
  | Prorv W rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.ror rs#r1 rs#r2))) m
  | Prorv X rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.rorl rs#r1 rs#r2))) m
  (** Conditional data processing *)
  | Pcsel rd r1 r2 cond =>
      let v :=
        match eval_testcond cond rs with
        | Some true => rs#r1
        | Some false => rs#r2
        | None => Vundef
        end in
      Next (nextinstr (rs#rd <- v)) m
  | Pcset rd cond =>
      let v :=
        match eval_testcond cond rs with
        | Some true => Vint Int.one
        | Some false => Vint Int.zero
        | None => Vundef
        end in
      Next (nextinstr (rs#rd <- v)) m
  (** Integer multiply/divide *)
  | Pmadd W rd r1 r2 r3 =>
      Next (nextinstr (rs#rd <- (Val.add rs##r3 (Val.mul rs#r1 rs#r2)))) m
  | Pmadd X rd r1 r2 r3 =>
      Next (nextinstr (rs#rd <- (Val.addl rs###r3 (Val.mull rs#r1 rs#r2)))) m
  | Pmsub W rd r1 r2 r3 =>
      Next (nextinstr (rs#rd <- (Val.sub rs##r3 (Val.mul rs#r1 rs#r2)))) m
  | Pmsub X rd r1 r2 r3 =>
      Next (nextinstr (rs#rd <- (Val.subl rs###r3 (Val.mull rs#r1 rs#r2)))) m
  | Psmulh rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mullhs rs#r1 rs#r2))) m
  | Pumulh rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mullhu rs#r1 rs#r2))) m
  | Psdiv W rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.divs rs#r1 rs#r2)))) m
  | Psdiv X rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.divls rs#r1 rs#r2)))) m
  | Pudiv W rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.divu rs#r1 rs#r2)))) m
  | Pudiv X rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.divlu rs#r1 rs#r2)))) m
  (** Floating-point loads and stores *)
  | Pldrs rd a =>
      exec_load Mfloat32 (fun v => v) a rd rs m
  | Pldrd rd a =>
      exec_load Mfloat64 (fun v => v) a rd rs m
  | Pldrd_a rd a =>
      exec_load Many64 (fun v => v) a rd rs m
  | Pstrs r a =>
      exec_store Mfloat32 a rs#r rs m
  | Pstrd r a =>
      exec_store Mfloat64 a rs#r rs m
  | Pstrd_a r a =>
      exec_store Many64 a rs#r rs m
  (** Floating-point move *)
  | Pfmov rd r1 =>
      Next (nextinstr (rs#rd <- (rs#r1))) m
  | Pfmovimms rd f =>
      Next (nextinstr (rs#rd <- (Vsingle f))) m
  | Pfmovimmd rd f =>
      Next (nextinstr (rs#rd <- (Vfloat f))) m
  | Pfmovi S rd r1 =>
      Next (nextinstr (rs#rd <- (float32_of_bits rs##r1))) m
  | Pfmovi D rd r1 =>
      Next (nextinstr (rs#rd <- (float64_of_bits rs###r1))) m
  (** Floating-point conversions *)
  | Pfcvtds rd r1 =>
      Next (nextinstr (rs#rd <- (Val.floatofsingle rs#r1))) m
  | Pfcvtsd rd r1 =>
      Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1))) m
  | Pfcvtzs W S rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intofsingle rs#r1)))) m
  | Pfcvtzs W D rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intoffloat rs#r1)))) m
  | Pfcvtzs X S rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longofsingle rs#r1)))) m
  | Pfcvtzs X D rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longoffloat rs#r1)))) m
  | Pfcvtzu W S rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intuofsingle rs#r1)))) m
  | Pfcvtzu W D rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intuoffloat rs#r1)))) m
  | Pfcvtzu X S rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longuofsingle rs#r1)))) m
  | Pfcvtzu X D rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longuoffloat rs#r1)))) m
  | Pscvtf S W rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofint rs#r1)))) m
  | Pscvtf D W rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatofint rs#r1)))) m
  | Pscvtf S X rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleoflong rs#r1)))) m
  | Pscvtf D X rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatoflong rs#r1)))) m
  | Pucvtf S W rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofintu rs#r1)))) m
  | Pucvtf D W rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatofintu rs#r1)))) m
  | Pucvtf S X rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleoflongu rs#r1)))) m
  | Pucvtf D X rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatoflongu rs#r1)))) m
  (** Floating-point arithmetic *)
  | Pfabs S rd r1 =>
      Next (nextinstr (rs#rd <- (Val.absfs rs#r1))) m
  | Pfabs D rd r1 =>
      Next (nextinstr (rs#rd <- (Val.absf rs#r1))) m
  | Pfneg S rd r1 =>
      Next (nextinstr (rs#rd <- (Val.negfs rs#r1))) m
  | Pfneg D rd r1 =>
      Next (nextinstr (rs#rd <- (Val.negf rs#r1))) m
  | Pfadd S rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.addfs rs#r1 rs#r2))) m
  | Pfadd D rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.addf rs#r1 rs#r2))) m
  | Pfdiv S rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.divfs rs#r1 rs#r2))) m
  | Pfdiv D rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.divf rs#r1 rs#r2))) m
  | Pfmul S rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mulfs rs#r1 rs#r2))) m
  | Pfmul D rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mulf rs#r1 rs#r2))) m
  | Pfnmul S rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.negfs (Val.mulfs rs#r1 rs#r2)))) m
  | Pfnmul D rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.negf (Val.mulf rs#r1 rs#r2)))) m
  | Pfsub S rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.subfs rs#r1 rs#r2))) m
  | Pfsub D rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.subf rs#r1 rs#r2))) m
  (** Floating-point comparison *)
  | Pfcmp S r1 r2 =>
      Next (nextinstr (compare_single rs rs#r1 rs#r2)) m
  | Pfcmp D r1 r2 =>
      Next (nextinstr (compare_float rs rs#r1 rs#r2)) m
  | Pfcmp0 S r1 =>
      Next (nextinstr (compare_single rs rs#r1 (Vsingle Float32.zero))) m
  | Pfcmp0 D r1 =>
      Next (nextinstr (compare_float rs rs#r1 (Vfloat Float.zero))) m
  (** Floating-point conditional select *)
  | Pfsel rd r1 r2 cond =>
      let v :=
        match eval_testcond cond rs with
        | Some true => rs#r1
        | Some false => rs#r2
        | None => Vundef
        end in
      Next (nextinstr (rs#rd <- v)) m
  (** Pseudo-instructions *)
  | Pallocframe sz pos =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := (Vptr stk Ptrofs.zero) in
      match Mem.storev Mint64 m1 (Val.offset_ptr sp pos) rs#SP with
      | None => Stuck
      | Some m2 => Next (nextinstr (rs #X29 <- (rs#SP) #SP <- sp #X16 <- Vundef)) m2
      end
  | Pfreeframe sz pos =>
      match Mem.loadv Mint64 m (Val.offset_ptr rs#SP pos) with
      | None => Stuck
      | Some v =>
          match rs#SP with
          | Vptr stk ofs =>
              match Mem.free m stk 0 sz with
              | None => Stuck
              | Some m' => Next (nextinstr (rs#SP <- v #X16 <- Vundef)) m'
              end
          | _ => Stuck
          end
      end
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Ploadsymbol rd id =>
      Next (nextinstr (rs#rd <- (Genv.symbol_address ge id Ptrofs.zero))) m
  | Pcvtsw2x rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofint rs#r1))) m
  | Pcvtuw2x rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofintu rs#r1))) m
  | Pcvtx2w rd =>
      Next (nextinstr (rs#rd <- (Val.loword rs#rd))) m
  | Pbtbl r tbl =>
      match (rs#X16 <- Vundef)#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs#X16 <- Vundef #X17 <- Vundef) m
          end
      | _ => Stuck
      end
  | Pbuiltin ef args res => Stuck    (**r treated specially below *)
  (** The following instructions and directives are not generated directly
      by Asmgen, so we do not model them. *)
  | Pldp _ _ _
  | Pstp _ _ _
  | Pcls _ _ _
  | Pclz _ _ _
  | Prev _ _ _
  | Prev16 _ _ _
  | Pfsqrt _ _ _
  | Pfmadd _ _ _ _ _
  | Pfmsub _ _ _ _ _
  | Pfnmadd _ _ _ _ _
  | Pfnmsub _ _ _ _ _
  | Pcfi_adjust _
  | Pcfi_rel_offset _ =>
      Stuck
  end.

(** Translation of the LTL/Linear/Mach view of machine registers
  to the AArch64 view.  Note that no LTL register maps to [X16],
  [X18], nor [X30].
  [X18] is reserved as the platform register and never used by the
  code generated by CompCert.
  [X30] is used for the return address, and can also be used as temporary.
  [X16] can be used as temporary. *)

Definition preg_of (r: mreg) : preg :=
  match r with
  | R0 => X0   | R1 => X1   | R2 => X2   | R3 => X3
  | R4 => X4   | R5 => X5   | R6 => X6   | R7 => X7
  | R8 => X8   | R9 => X9   | R10 => X10 | R11 => X11
  | R12 => X12 | R13 => X13 | R14 => X14 | R15 => X15
  | R17 => X17 | R19 => X19
  | R20 => X20 | R21 => X21 | R22 => X22 | R23 => X23
  | R24 => X24 | R25 => X25 | R26 => X26 | R27 => X27
  | R28 => X28 | R29 => X29
  | F0 => D0   | F1 => D1   | F2 => D2   | F3 => D3
  | F4 => D4   | F5 => D5   | F6 => D6   | F7 => D7
  | F8 => D8   | F9 => D9   | F10 => D10 | F11 => D11
  | F12 => D12 | F13 => D13 | F14 => D14 | F15 => D15
  | F16 => D16 | F17 => D17 | F18 => D18 | F19 => D19
  | F20 => D20 | F21 => D21 | F22 => D22 | F23 => D23
  | F24 => D24 | F25 => D25 | F26 => D26 | F27 => D27
  | F28 => D28 | F29 => D29 | F30 => D30 | F31 => D31
  end.

(** Undefine all registers except SP and callee-save registers *)

Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r =>
    if preg_eq r SP
    || In_dec preg_eq r (List.map preg_of (List.filter is_callee_save all_mregs))
    then rs r
    else Vundef.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use AArch64 registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr rs#SP (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (Locations.S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: mem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m) (loc_arguments sg) args.

Definition loc_external_result (sg: signature) : rpair preg :=
  map_rpair preg_of (loc_result sg).

(** Execution of the instruction at [rs#PC]. *)

Inductive state: Type :=
  | State: regset -> mem -> state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs rs#SP m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextinstr
              (set_res res vres
                (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs)) #PC <- (rs RA) ->
      step (State rs m) t (State rs' m').

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      Genv.init_mem p = Some m0 ->
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # RA <- Vnullptr
        # SP <- Vnullptr in
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vnullptr ->
      rs#X0 = Vint r ->
      final_state (State rs m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             extcall_arg rs m l v1 -> extcall_arg rs m l v2 -> v1 = v2).
  { intros. inv H; inv H0; congruence. }
  assert (B: forall p v1 v2,
             extcall_arg_pair rs m p v1 -> extcall_arg_pair rs m p v2 -> v1 = v2).
  { intros. inv H; inv H0.
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m) ll vl1 ->
             forall vl2, list_forall2 (extcall_arg_pair rs m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities.
  split. constructor. auto.
  discriminate.
  discriminate.
  assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
  assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H3. eexact H8. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros. inv H; simpl.
  omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. f_equal. congruence.
- (* final no step *)
  inv H. red; intros; red; intros. inv H; rewrite H0 in *; discriminate.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | IR X16 => false
  | IR X30 => false
  | IR _ => true
  | FR _ => true
  | CR _ => false
  | SP => true
  | PC => false
  end.
