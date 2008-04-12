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

(** Abstract syntax and semantics for PowerPC assembly language *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.

(** * Abstract syntax *)

(** Integer registers, floating-point registers. *)

Inductive ireg: Set :=
  | GPR0: ireg  | GPR1: ireg  | GPR2: ireg  | GPR3: ireg
  | GPR4: ireg  | GPR5: ireg  | GPR6: ireg  | GPR7: ireg
  | GPR8: ireg  | GPR9: ireg  | GPR10: ireg | GPR11: ireg
  | GPR12: ireg | GPR13: ireg | GPR14: ireg | GPR15: ireg
  | GPR16: ireg | GPR17: ireg | GPR18: ireg | GPR19: ireg
  | GPR20: ireg | GPR21: ireg | GPR22: ireg | GPR23: ireg
  | GPR24: ireg | GPR25: ireg | GPR26: ireg | GPR27: ireg
  | GPR28: ireg | GPR29: ireg | GPR30: ireg | GPR31: ireg.

Inductive freg: Set :=
  | FPR0: freg  | FPR1: freg  | FPR2: freg  | FPR3: freg
  | FPR4: freg  | FPR5: freg  | FPR6: freg  | FPR7: freg
  | FPR8: freg  | FPR9: freg  | FPR10: freg | FPR11: freg
  | FPR12: freg | FPR13: freg | FPR14: freg | FPR15: freg
  | FPR16: freg | FPR17: freg | FPR18: freg | FPR19: freg
  | FPR20: freg | FPR21: freg | FPR22: freg | FPR23: freg
  | FPR24: freg | FPR25: freg | FPR26: freg | FPR27: freg
  | FPR28: freg | FPR29: freg | FPR30: freg | FPR31: freg.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(** Symbolic constants.  Immediate operands to an arithmetic instruction
  or an indexed memory access can be either integer literals
  or the low or high 16 bits of a symbolic reference (the address
  of a symbol plus a displacement).  These symbolic references are
  resolved later by the linker.
*)

Inductive constant: Set :=
  | Cint: int -> constant
  | Csymbol_low: ident -> int -> constant
  | Csymbol_high: ident -> int -> constant.

(** A note on constants: while immediate operands to PowerPC
  instructions must be representable in 16 bits (with
  sign extension or left shift by 16 positions for some instructions),
  we do not attempt to capture these restrictions in the 
  abstract syntax nor in the semantics.  The assembler will
  emit an error if immediate operands exceed the representable
  range.  Of course, our PPC generator (file [PPCgen]) is
  careful to respect this range. *)

(** Bits in the condition register.  We are only interested in the
  first 4 bits. *)

Inductive crbit: Set :=
  | CRbit_0: crbit
  | CRbit_1: crbit
  | CRbit_2: crbit
  | CRbit_3: crbit.

(** The instruction set.  Most instructions correspond exactly to
  actual instructions of the PowerPC processor. See the PowerPC
  reference manuals for more details.  Some instructions,
  described below, are pseudo-instructions: they expand to
  canned instruction sequences during the printing of the assembly
  code. *)

Definition label := positive.

Inductive instruction : Set :=
  | Padd: ireg -> ireg -> ireg -> instruction                 (**r integer addition *)
  | Paddi: ireg -> ireg -> constant -> instruction            (**r add immediate *)
  | Paddis: ireg -> ireg -> constant -> instruction           (**r add immediate high *)
  | Paddze: ireg -> ireg -> instruction                       (**r add Carry bit *)
  | Pallocblock: instruction                                  (**r allocate new heap block *)
  | Pallocframe: Z -> Z -> int -> instruction                 (**r allocate new stack frame *)
  | Pand_: ireg -> ireg -> ireg -> instruction                (**r bitwise and *)
  | Pandc: ireg -> ireg -> ireg -> instruction                (**r bitwise and-complement *)
  | Pandi_: ireg -> ireg -> constant -> instruction           (**r and immediate and set conditions *)
  | Pandis_: ireg -> ireg -> constant -> instruction          (**r and immediate high and set conditions *)
  | Pb: label -> instruction                                  (**r unconditional branch *)
  | Pbctr: instruction                                        (**r branch to contents of register CTR *)
  | Pbctrl: instruction                                       (**r branch to contents of CTR and link *)
  | Pbf: crbit -> label -> instruction                        (**r branch if false *)
  | Pbl: ident -> instruction                                 (**r branch and link *)
  | Pbs: ident -> instruction                                 (**r branch to symbol *)
  | Pblr: instruction                                         (**r branch to contents of register LR *)
  | Pbt: crbit -> label -> instruction                        (**r branch if true *)
  | Pcmplw: ireg -> ireg -> instruction                       (**r unsigned integer comparison *)
  | Pcmplwi: ireg -> constant -> instruction                  (**r same, with immediate argument *)
  | Pcmpw: ireg -> ireg -> instruction                        (**r signed integer comparison *)
  | Pcmpwi: ireg -> constant -> instruction                   (**r same, with immediate argument *)
  | Pcror: crbit -> crbit -> crbit -> instruction             (**r or between condition bits *)
  | Pdivw: ireg -> ireg -> ireg -> instruction                (**r signed division *)
  | Pdivwu: ireg -> ireg -> ireg -> instruction               (**r unsigned division *)
  | Peqv: ireg -> ireg -> ireg -> instruction                 (**r bitwise not-xor *)
  | Pextsb: ireg -> ireg -> instruction                       (**r 8-bit sign extension *)
  | Pextsh: ireg -> ireg -> instruction                       (**r 16-bit sign extension *)
  | Pfreeframe: int -> instruction                            (**r deallocate stack frame and restore previous frame *)
  | Pfabs: freg -> freg -> instruction                        (**r float absolute value *)
  | Pfadd: freg -> freg -> freg -> instruction                (**r float addition *)
  | Pfcmpu: freg -> freg -> instruction                       (**r float comparison *)
  | Pfcti: ireg -> freg -> instruction                        (**r float-to-int conversion *)
  | Pfdiv: freg -> freg -> freg -> instruction                (**r float division *)
  | Pfmadd: freg -> freg -> freg -> freg -> instruction       (**r float multiply-add *)
  | Pfmr: freg -> freg -> instruction                         (**r float move *)
  | Pfmsub: freg -> freg -> freg -> freg -> instruction       (**r float multiply-sub *)
  | Pfmul: freg -> freg -> freg -> instruction                (**r float multiply *)
  | Pfneg: freg -> freg -> instruction                        (**r float negation *)
  | Pfrsp: freg -> freg -> instruction                        (**r float round to single precision *)
  | Pfsub: freg -> freg -> freg -> instruction                (**r float subtraction *)
  | Pictf: freg -> ireg -> instruction                        (**r int-to-float conversion *)
  | Piuctf: freg -> ireg -> instruction                       (**r unsigned int-to-float conversion *)
  | Plbz: ireg -> constant -> ireg -> instruction             (**r load 8-bit unsigned int *)
  | Plbzx: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Plfd: freg -> constant -> ireg -> instruction             (**r load 64-bit float *)
  | Plfdx: freg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Plfs: freg -> constant -> ireg -> instruction             (**r load 32-bit float *)
  | Plfsx: freg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Plha: ireg -> constant -> ireg -> instruction             (**r load 16-bit signed int *)
  | Plhax: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Plhz: ireg -> constant -> ireg -> instruction             (**r load 16-bit unsigned int *)
  | Plhzx: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Plfi: freg -> float -> instruction                        (**r load float constant *)
  | Plwz: ireg -> constant -> ireg -> instruction             (**r load 32-bit int *)
  | Plwzx: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Pmfcrbit: ireg -> crbit -> instruction                    (**r move condition bit to reg *)
  | Pmflr: ireg -> instruction                                (**r move LR to reg *)
  | Pmr: ireg -> ireg -> instruction                          (**r integer move *)
  | Pmtctr: ireg -> instruction                               (**r move ireg to CTR *)
  | Pmtlr: ireg -> instruction                                (**r move ireg to LR *)
  | Pmulli: ireg -> ireg -> constant -> instruction           (**r integer multiply immediate *)
  | Pmullw: ireg -> ireg -> ireg -> instruction               (**r integer multiply *)
  | Pnand: ireg -> ireg -> ireg -> instruction                (**r bitwise not-and *)
  | Pnor: ireg -> ireg -> ireg -> instruction                 (**r bitwise not-or *)
  | Por: ireg -> ireg -> ireg -> instruction                  (**r bitwise or *)
  | Porc: ireg -> ireg -> ireg -> instruction                 (**r bitwise or-complement *)
  | Pori: ireg -> ireg -> constant -> instruction             (**r or with immediate *)
  | Poris: ireg -> ireg -> constant -> instruction            (**r or with immediate high *)
  | Prlwinm: ireg -> ireg -> int -> int -> instruction        (**r rotate and mask *)
  | Pslw: ireg -> ireg -> ireg -> instruction                 (**r shift left *)
  | Psraw: ireg -> ireg -> ireg -> instruction                (**r shift right signed *)
  | Psrawi: ireg -> ireg -> int -> instruction                (**r shift right signed immediate *)
  | Psrw: ireg -> ireg -> ireg -> instruction                 (**r shift right unsigned *)
  | Pstb: ireg -> constant -> ireg -> instruction             (**r store 8-bit int *)
  | Pstbx: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Pstfd: freg -> constant -> ireg -> instruction            (**r store 64-bit float *)
  | Pstfdx: freg -> ireg -> ireg -> instruction               (**r same, with 2 index regs *)
  | Pstfs: freg -> constant -> ireg -> instruction            (**r store 32-bit float *)
  | Pstfsx: freg -> ireg -> ireg -> instruction               (**r same, with 2 index regs *)
  | Psth: ireg -> constant -> ireg -> instruction             (**r store 16-bit int *)
  | Psthx: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Pstw: ireg -> constant -> ireg -> instruction             (**r store 32-bit int *)
  | Pstwx: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Psubfc: ireg -> ireg -> ireg -> instruction               (**r reversed integer subtraction *)
  | Psubfic: ireg -> ireg -> constant -> instruction          (**r integer subtraction from immediate *)
  | Pxor: ireg -> ireg -> ireg -> instruction                 (**r bitwise xor *)
  | Pxori: ireg -> ireg -> constant -> instruction            (**r bitwise xor with immediate *)
  | Pxoris: ireg -> ireg -> constant -> instruction           (**r bitwise xor with immediate high *)
  | Plabel: label -> instruction.                             (**r define a code label *)

(** The pseudo-instructions are the following:

- [Plabel]: define a code label at the current program point
- [Plfi]: load a floating-point constant in a float register.
  Expands to a float load [lfd] from an address in the constant data section
  initialized with the floating-point constant:
<<
        addis   r2, 0, ha16(lbl)
        lfd     rdst, lo16(lbl)(r2)
        .const_data
lbl:    .double floatcst
        .text
>>
  Initialized data in the constant data section are not modeled here,
  which is why we use a pseudo-instruction for this purpose.
- [Pfcti]: convert a float to an integer.  This requires a transfer
  via memory of a 32-bit integer from a float register to an int register,
  which our memory model cannot express.  Expands to:
<<
        fctiwz  f13, rsrc
        stfdu   f13, -8(r1)
        lwz     rdst, 4(r1)
        addi    r1, r1, 8
>>
- [Pictf]: convert a signed integer to a float.  This requires complicated
  bit-level manipulations of IEEE floats through mixed float and integer 
  arithmetic over a memory word, which our memory model and axiomatization
  of floats cannot express.  Expands to:
<<
        addis   r2, 0, 0x4330
        stwu    r2, -8(r1)
        addis   r2, rsrc, 0x8000
        stw     r2, 4(r1)
        addis   r2, 0, ha16(lbl)
        lfd     f13, lo16(lbl)(r2)
        lfd     rdst, 0(r1)
        addi    r1, r1, 8
        fsub    rdst, rdst, f13
        .const_data
lbl:    .long   0x43300000, 0x80000000
        .text
>>
  (Don't worry if you do not understand this instruction sequence: intimate
  knowledge of IEEE float arithmetic is necessary.)
- [Piuctf]: convert an unsigned integer to a float.  The expansion is close
  to that [Pictf], and equally obscure.
<<
        addis   r2, 0, 0x4330
        stwu    r2, -8(r1)
        stw     rsrc, 4(r1)
        addis   r2, 0, ha16(lbl)
        lfd     f13, lo16(lbl)(r2)
        lfd     rdst, 0(r1)
        addi    r1, r1, 8
        fsub    rdst, rdst, f13
        .const_data
lbl:    .long   0x43300000, 0x00000000
        .text
>>
- [Pallocframe lo hi ofs]: in the formal semantics, this pseudo-instruction
  allocates a memory block with bounds [lo] and [hi], stores the value
  of register [r1] (the stack pointer, by convention) at offset [ofs]
  in this block, and sets [r1] to a pointer to the bottom of this
  block.  In the printed PowerPC assembly code, this allocation
  is just a store-decrement of register [r1], assuming that [ofs = 0]:
<<
        stwu    r1, (lo - hi)(r1)
>>
  This cannot be expressed in our memory model, which does not reflect
  the fact that stack frames are adjacent and allocated/freed
  following a stack discipline.
- [Pfreeframe ofs]: in the formal semantics, this pseudo-instruction
  reads the word at offset [ofs] in the block pointed by [r1] (the
  stack pointer), frees this block, and sets [r1] to the value of the
  word at offset [ofs].  In the printed PowerPC assembly code, this
  freeing is just a load of register [r1] relative to [r1] itself:
<<
        lwz     r1, ofs(r1)
>>
  Again, our memory model cannot comprehend that this operation
  frees (logically) the current stack frame.
- [Pallocheap]: in the formal semantics, this pseudo-instruction
  allocates a heap block of size the contents of [GPR3], and leaves
  a pointer to this block in [GPR3].  In the generated assembly code,
  it is turned into a call to the allocation function of the run-time
  system.
*)

Definition code := list instruction.
Definition fundef := AST.fundef code.
Definition program := AST.program fundef unit.

(** * Operational semantics *)

(** The PowerPC has a great many registers, some general-purpose, some very
  specific.  We model only the following registers: *)

Inductive preg: Set :=
  | IR: ireg -> preg                    (**r integer registers *)
  | FR: freg -> preg                    (**r float registers *)
  | PC: preg                            (**r program counter *)
  | LR: preg                            (**r link register (return address) *)
  | CTR: preg                           (**r count register, used for some branches *)
  | CARRY: preg                         (**r carry bit of the status register *)
  | CR0_0: preg                         (**r bit 0 of the condition register  *)
  | CR0_1: preg                         (**r bit 1 of the condition register  *)
  | CR0_2: preg                         (**r bit 2 of the condition register  *)
  | CR0_3: preg.                        (**r bit 3 of the condition register  *)

Coercion IR: ireg >-> preg.
Coercion FR: freg >-> preg.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. apply freg_eq. Defined.

Module PregEq.
  Definition t := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain (but do not enforce)
  the convention that integer registers are mapped to values of
  type [Tint], float registers to values of type [Tfloat],
  and boolean registers ([CARRY], [CR0_0], etc) to either
  [Vzero] or [Vone]. *)
  
Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef.

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).

Section RELSEM.

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
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

(** Some PowerPC instructions treat register GPR0 as the integer literal 0
  when that register is used in argument position. *)

Definition gpr_or_zero (rs: regset) (r: ireg) :=
  if ireg_eq r GPR0 then Vzero else rs#r.

Variable ge: genv.

Definition symbol_offset (id: ident) (ofs: int) : val :=
  match Genv.find_symbol ge id with
  | Some b => Vptr b ofs
  | None => Vundef
  end.

(** The four functions below axiomatize how the linker processes
  symbolic references [symbol + offset] and splits their
  actual values into two 16-bit halves. *)

Parameter low_half: val -> val.
Parameter high_half: val -> val.

(** The fundamental property of these operations is that, when applied
  to the address of a symbol, their results can be recombined by
  addition, rebuilding the original address. *)

Axiom low_high_half:
  forall id ofs,
  Val.add (low_half (symbol_offset id ofs)) (high_half (symbol_offset id ofs))
  = symbol_offset id ofs.

(** The other axioms we take is that the results of
  the [low_half] and [high_half] functions are of type [Tint],
  i.e. either integers, pointers or undefined values. *)

Axiom low_half_type: 
  forall v, Val.has_type (low_half v) Tint.
Axiom high_half_type: 
  forall v, Val.has_type (high_half v) Tint.
 
(** Armed with the [low_half] and [high_half] functions,
  we can define the evaluation of a symbolic constant.
  Note that for [const_high], integer constants
  are shifted left by 16 bits, but not symbol addresses:
  we assume (as in the [low_high_half] axioms above)
  that the results of [high_half] are already shifted
  (their 16 low bits are equal to 0). *)

Definition const_low (c: constant) :=
  match c with
  | Cint n => Vint n
  | Csymbol_low id ofs => low_half (symbol_offset id ofs)
  | Csymbol_high id ofs => Vundef
  end.

Definition const_high (c: constant) :=
  match c with
  | Cint n => Vint (Int.shl n (Int.repr 16))
  | Csymbol_low id ofs => Vundef
  | Csymbol_high id ofs => high_half (symbol_offset id ofs)
  end.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [OK rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Error] if the processor is stuck. *)

Inductive outcome: Set :=
  | OK: regset -> mem -> outcome
  | Error: outcome.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]). *)

Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.add rs#PC Vone).

Definition goto_label (c: code) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 c with
  | None => Error
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => OK (rs#PC <- (Vptr b (Int.repr pos))) m
      | _ => Error
    end
  end.

(** Auxiliaries for memory accesses, in two forms: one operand
  (plus constant offset) or two operands. *)

Definition load1 (chunk: memory_chunk) (rd: preg)
                 (cst: constant) (r1: ireg) (rs: regset) (m: mem) :=
  match Mem.loadv chunk m (Val.add (gpr_or_zero rs r1) (const_low cst)) with
  | None => Error
  | Some v => OK (nextinstr (rs#rd <- v)) m
  end.

Definition load2 (chunk: memory_chunk) (rd: preg) (r1 r2: ireg)
                 (rs: regset) (m: mem) :=
  match Mem.loadv chunk m (Val.add rs#r1 rs#r2) with
  | None => Error
  | Some v => OK (nextinstr (rs#rd <- v)) m
  end.

Definition store1 (chunk: memory_chunk) (r: preg)
                  (cst: constant) (r1: ireg) (rs: regset) (m: mem) :=
  match Mem.storev chunk m (Val.add (gpr_or_zero rs r1) (const_low cst)) (rs#r) with
  | None => Error
  | Some m' => OK (nextinstr rs) m'
  end.

Definition store2 (chunk: memory_chunk) (r: preg) (r1 r2: ireg)
                  (rs: regset) (m: mem) :=
  match Mem.storev chunk m (Val.add rs#r1 rs#r2) (rs#r) with
  | None => Error
  | Some m' => OK (nextinstr rs) m'
  end.

(** Operations over condition bits. *)

Definition reg_of_crbit (bit: crbit) :=
  match bit with
  | CRbit_0 => CR0_0
  | CRbit_1 => CR0_1
  | CRbit_2 => CR0_2
  | CRbit_3 => CR0_3
  end.

Definition compare_sint (rs: regset) (v1 v2: val) :=
  rs#CR0_0 <- (Val.cmp Clt v1 v2)
    #CR0_1 <- (Val.cmp Cgt v1 v2)
    #CR0_2 <- (Val.cmp Ceq v1 v2)
    #CR0_3 <- Vundef.

Definition compare_uint (rs: regset) (v1 v2: val) :=
  rs#CR0_0 <- (Val.cmpu Clt v1 v2)
    #CR0_1 <- (Val.cmpu Cgt v1 v2)
    #CR0_2 <- (Val.cmpu Ceq v1 v2)
    #CR0_3 <- Vundef.

Definition compare_float (rs: regset) (v1 v2: val) :=
  rs#CR0_0 <- (Val.cmpf Clt v1 v2)
    #CR0_1 <- (Val.cmpf Cgt v1 v2)
    #CR0_2 <- (Val.cmpf Ceq v1 v2)
    #CR0_3 <- Vundef.

Definition val_cond_reg (rs: regset) :=
  Val.or (Val.shl rs#CR0_0 (Vint (Int.repr 31)))
  (Val.or (Val.shl rs#CR0_1 (Vint (Int.repr 30)))
   (Val.or (Val.shl rs#CR0_2 (Vint (Int.repr 29)))
            (Val.shl rs#CR0_3 (Vint (Int.repr 28))))).

(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual PowerPC instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the PowerPC reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above.  Note that
    we set to [Vundef] the registers used as temporaries by the
    expansions of the pseudo-instructions, so that the PPC code
    we generate cannot use those registers to hold values that
    must survive the execution of the pseudo-instruction.
*)

Definition exec_instr (c: code) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  | Padd rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.add rs#r1 rs#r2))) m
  | Paddi rd r1 cst =>
      OK (nextinstr (rs#rd <- (Val.add (gpr_or_zero rs r1) (const_low cst)))) m
  | Paddis rd r1 cst =>
      OK (nextinstr (rs#rd <- (Val.add (gpr_or_zero rs r1) (const_high cst)))) m
  | Paddze rd r1 =>
      OK (nextinstr (rs#rd <- (Val.add rs#r1 rs#CARRY))) m
  | Pallocblock =>
      match rs#GPR3 with
      | Vint n =>
          let (m', b) := Mem.alloc m 0 (Int.signed n) in
          OK (nextinstr (rs#GPR3 <- (Vptr b Int.zero)
                           #LR <- (Val.add rs#PC Vone))) m'
      | _ => Error
      end
  | Pallocframe lo hi ofs =>
      let (m1, stk) := Mem.alloc m lo hi in
      let sp := Vptr stk (Int.repr lo) in
      match Mem.storev Mint32 m1 (Val.add sp (Vint ofs)) rs#GPR1 with
      | None => Error
      | Some m2 => OK (nextinstr (rs#GPR1 <- sp #GPR2 <- Vundef)) m2
      end
  | Pand_ rd r1 r2 =>
      let v := Val.and rs#r1 rs#r2 in
      OK (nextinstr (compare_sint (rs#rd <- v) v Vzero)) m
  | Pandc rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.and rs#r1 (Val.notint rs#r2)))) m
  | Pandi_ rd r1 cst =>
      let v := Val.and rs#r1 (const_low cst) in
      OK (nextinstr (compare_sint (rs#rd <- v) v Vzero)) m
  | Pandis_ rd r1 cst =>
      let v := Val.and rs#r1 (const_high cst) in
      OK (nextinstr (compare_sint (rs#rd <- v) v Vzero)) m
  | Pb lbl =>
      goto_label c lbl rs m
  | Pbctr =>
      OK (rs#PC <- (rs#CTR)) m
  | Pbctrl =>
      OK (rs#LR <- (Val.add rs#PC Vone) #PC <- (rs#CTR)) m
  | Pbf bit lbl =>
      match rs#(reg_of_crbit bit) with
      | Vint n => if Int.eq n Int.zero then goto_label c lbl rs m else OK (nextinstr rs) m
      | _ => Error
      end
  | Pbl ident =>
      OK (rs#LR <- (Val.add rs#PC Vone) #PC <- (symbol_offset ident Int.zero)) m
  | Pbs ident =>
      OK (rs#PC <- (symbol_offset ident Int.zero)) m
  | Pblr =>
      OK (rs#PC <- (rs#LR)) m
  | Pbt bit lbl =>
      match rs#(reg_of_crbit bit) with
      | Vint n => if Int.eq n Int.zero then OK (nextinstr rs) m else goto_label c lbl rs m
      | _ => Error
      end
  | Pcmplw r1 r2 =>
      OK (nextinstr (compare_uint rs rs#r1 rs#r2)) m
  | Pcmplwi r1 cst =>
      OK (nextinstr (compare_uint rs rs#r1 (const_low cst))) m
  | Pcmpw r1 r2 =>
      OK (nextinstr (compare_sint rs rs#r1 rs#r2)) m
  | Pcmpwi r1 cst =>
      OK (nextinstr (compare_sint rs rs#r1 (const_low cst))) m
  | Pcror bd b1 b2 =>
      OK (nextinstr (rs#(reg_of_crbit bd) <- (Val.or rs#(reg_of_crbit b1) rs#(reg_of_crbit b2)))) m
  | Pdivw rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.divs rs#r1 rs#r2))) m
  | Pdivwu rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.divu rs#r1 rs#r2))) m
  | Peqv rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.notint (Val.xor rs#r1 rs#r2)))) m
  | Pextsb rd r1 =>
      OK (nextinstr (rs#rd <- (Val.cast8signed rs#r1))) m
  | Pextsh rd r1 =>
      OK (nextinstr (rs#rd <- (Val.cast16signed rs#r1))) m
  | Pfreeframe ofs =>
      match Mem.loadv Mint32 m (Val.add rs#GPR1 (Vint ofs)) with
      | None => Error
      | Some v =>
          match rs#GPR1 with
          | Vptr stk ofs => OK (nextinstr (rs#GPR1 <- v)) (Mem.free m stk)
          | _ => Error
          end
      end
  | Pfabs rd r1 =>
      OK (nextinstr (rs#rd <- (Val.absf rs#r1))) m
  | Pfadd rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.addf rs#r1 rs#r2))) m
  | Pfcmpu r1 r2 =>
      OK (nextinstr (compare_float rs rs#r1 rs#r2)) m
  | Pfcti rd r1 =>
      OK (nextinstr (rs#rd <- (Val.intoffloat rs#r1) #FPR13 <- Vundef)) m
  | Pfdiv rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.divf rs#r1 rs#r2))) m
  | Pfmadd rd r1 r2 r3 =>
      OK (nextinstr (rs#rd <- (Val.addf (Val.mulf rs#r1 rs#r2) rs#r3))) m
  | Pfmr rd r1 =>
      OK (nextinstr (rs#rd <- (rs#r1))) m
  | Pfmsub rd r1 r2 r3 =>
      OK (nextinstr (rs#rd <- (Val.subf (Val.mulf rs#r1 rs#r2) rs#r3))) m
  | Pfmul rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.mulf rs#r1 rs#r2))) m
  | Pfneg rd r1 =>
      OK (nextinstr (rs#rd <- (Val.negf rs#r1))) m
  | Pfrsp rd r1 =>
      OK (nextinstr (rs#rd <- (Val.singleoffloat rs#r1))) m
  | Pfsub rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.subf rs#r1 rs#r2))) m
  | Pictf rd r1 =>
      OK (nextinstr (rs#rd <- (Val.floatofint rs#r1) #GPR2 <- Vundef #FPR13 <- Vundef)) m
  | Piuctf rd r1 =>
      OK (nextinstr (rs#rd <- (Val.floatofintu rs#r1) #GPR2 <- Vundef #FPR13 <- Vundef)) m
  | Plbz rd cst r1 =>
      load1 Mint8unsigned rd cst r1 rs m
  | Plbzx rd r1 r2 =>
      load2 Mint8unsigned rd r1 r2 rs m
  | Plfd rd cst r1 =>
      load1 Mfloat64 rd cst r1 rs m
  | Plfdx rd r1 r2 =>
      load2 Mfloat64 rd r1 r2 rs m
  | Plfs rd cst r1 =>
      load1 Mfloat32 rd cst r1 rs m
  | Plfsx rd r1 r2 =>
      load2 Mfloat32 rd r1 r2 rs m
  | Plha rd cst r1 =>
      load1 Mint16signed rd cst r1 rs m
  | Plhax rd r1 r2 =>
      load2 Mint16signed rd r1 r2 rs m
  | Plhz rd cst r1 =>
      load1 Mint16unsigned rd cst r1 rs m
  | Plhzx rd r1 r2 =>
      load2 Mint16unsigned rd r1 r2 rs m
  | Plfi rd f =>
      OK (nextinstr (rs#rd <- (Vfloat f) #GPR2 <- Vundef)) m
  | Plwz rd cst r1 =>
      load1 Mint32 rd cst r1 rs m
  | Plwzx rd r1 r2 =>
      load2 Mint32 rd r1 r2 rs m
  | Pmfcrbit rd bit =>
      OK (nextinstr (rs#rd <- (rs#(reg_of_crbit bit)))) m
  | Pmflr rd =>
      OK (nextinstr (rs#rd <- (rs#LR))) m
  | Pmr rd r1 =>
      OK (nextinstr (rs#rd <- (rs#r1))) m
  | Pmtctr r1 =>
      OK (nextinstr (rs#CTR <- (rs#r1))) m
  | Pmtlr r1 =>
      OK (nextinstr (rs#LR <- (rs#r1))) m
  | Pmulli rd r1 cst =>
      OK (nextinstr (rs#rd <- (Val.mul rs#r1 (const_low cst)))) m
  | Pmullw rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.mul rs#r1 rs#r2))) m
  | Pnand rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.notint (Val.and rs#r1 rs#r2)))) m
  | Pnor rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.notint (Val.or rs#r1 rs#r2)))) m
  | Por rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.or rs#r1 rs#r2))) m
  | Porc rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.or rs#r1 (Val.notint rs#r2)))) m
  | Pori rd r1 cst =>
      OK (nextinstr (rs#rd <- (Val.or rs#r1 (const_low cst)))) m
  | Poris rd r1 cst =>
      OK (nextinstr (rs#rd <- (Val.or rs#r1 (const_high cst)))) m
  | Prlwinm rd r1 amount mask =>
      OK (nextinstr (rs#rd <- (Val.rolm rs#r1 amount mask))) m
  | Pslw rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.shl rs#r1 rs#r2))) m
  | Psraw rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.shr rs#r1 rs#r2) #CARRY <- (Val.shr_carry rs#r1 rs#r2))) m
  | Psrawi rd r1 n =>
      OK (nextinstr (rs#rd <- (Val.shr rs#r1 (Vint n)) #CARRY <- (Val.shr_carry rs#r1 (Vint n)))) m
  | Psrw rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.shru rs#r1 rs#r2))) m
  | Pstb rd cst r1 =>
      store1 Mint8unsigned rd cst r1 rs m
  | Pstbx rd r1 r2 =>
      store2 Mint8unsigned rd r1 r2 rs m
  | Pstfd rd cst r1 =>
      store1 Mfloat64 rd cst r1 rs m
  | Pstfdx rd r1 r2 =>
      store2 Mfloat64 rd r1 r2 rs m
  | Pstfs rd cst r1 =>
      store1 Mfloat32 rd cst r1 rs m
  | Pstfsx rd r1 r2 =>
      store2 Mfloat32 rd r1 r2 rs m
  | Psth rd cst r1 =>
      store1 Mint16unsigned rd cst r1 rs m
  | Psthx rd r1 r2 =>
      store2 Mint16unsigned rd r1 r2 rs m
  | Pstw rd cst r1 =>
      store1 Mint32 rd cst r1 rs m
  | Pstwx rd r1 r2 =>
      store2 Mint32 rd r1 r2 rs m
  | Psubfc rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.sub rs#r2 rs#r1) #CARRY <- Vundef)) m
  | Psubfic rd r1 cst =>
      OK (nextinstr (rs#rd <- (Val.sub (const_low cst) rs#r1) #CARRY <- Vundef)) m
  | Pxor rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.xor rs#r1 rs#r2))) m
  | Pxori rd r1 cst =>
      OK (nextinstr (rs#rd <- (Val.xor rs#r1 (const_low cst)))) m
  | Pxoris rd r1 cst =>
      OK (nextinstr (rs#rd <- (Val.xor rs#r1 (const_high cst)))) m
  | Plabel lbl =>
      OK (nextinstr rs) m
  end.

(** Calling conventions for external functions.  These are compatible with
    the calling conventions in module [Conventions], except that
    we use PPC registers instead of locations. *)

Inductive extcall_args (rs: regset) (m: mem):
      list typ -> list ireg -> list freg -> Z -> list val -> Prop :=
  | extcall_args_nil: forall irl frl ofs,
      extcall_args rs m nil irl frl ofs nil
  | extcall_args_int_reg: forall tyl ir1 irl frl ofs v1 vl,
      v1 = rs (IR ir1) ->
      extcall_args rs m tyl irl frl ofs vl ->
      extcall_args rs m (Tint :: tyl) (ir1 :: irl) frl ofs (v1 :: vl)
  | extcall_args_int_stack: forall tyl frl ofs v1 vl,
      Mem.loadv Mint32 m (Val.add (rs (IR GPR1)) (Vint (Int.repr ofs))) = Some v1 ->
      extcall_args rs m tyl nil frl (ofs + 4) vl ->
      extcall_args rs m (Tint :: tyl) nil frl ofs (v1 :: vl)
  | extcall_args_float_reg: forall tyl irl fr1 frl ofs v1 vl,
      v1 = rs (FR fr1) ->
      extcall_args rs m tyl (list_drop2 irl) frl ofs vl ->
      extcall_args rs m (Tfloat :: tyl) irl (fr1 :: frl) ofs (v1 :: vl)
  | extcall_args_float_stack: forall tyl irl ofs v1 vl,
      Mem.loadv Mfloat64 m (Val.add (rs (IR GPR1)) (Vint (Int.repr ofs))) = Some v1 ->
      extcall_args rs m tyl irl nil (ofs + 8) vl ->
      extcall_args rs m (Tfloat :: tyl) irl nil ofs (v1 :: vl).

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  extcall_args rs m
    sg.(sig_args)
    (GPR3 :: GPR4 :: GPR5 :: GPR6 :: GPR7 :: GPR8 :: GPR9 :: GPR10 :: nil)
    (FPR1 :: FPR2 :: FPR3 :: FPR4 :: FPR5 :: FPR6 :: FPR7 :: FPR8 :: FPR9 :: FPR10 :: nil)
    56 args.

Definition loc_external_result (s: signature) : preg :=
  match s.(sig_res) with
  | None => GPR3
  | Some Tint => GPR3
  | Some Tfloat => FPR1
  end.

(** Execution of the instruction at [rs#PC]. *)

Inductive state: Set :=
  | State: regset -> mem -> state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs c i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal c) ->
      find_instr (Int.unsigned ofs) c = Some i ->
      exec_instr c i rs m = OK rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs',
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      event_match ef args t res ->
      extcall_arguments rs m ef.(ef_sig) args ->
      rs' = (rs#(loc_external_result ef.(ef_sig)) <- res
               #PC <- (rs LR)) ->
      step (State rs m) t (State rs' m).

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro:
      let ge := Genv.globalenv p in
      let m0 := Genv.init_mem p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (symbol_offset ge p.(prog_main) Int.zero)
        # LR <- Vzero
        # GPR1 <- (Vptr Mem.nullptr Int.zero) in
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vzero ->
      rs#GPR3 = Vint r ->
      final_state (State rs m) r.
      
Definition exec_program (p: program) (beh: program_behavior) : Prop :=
  program_behaves step (initial_state p) final_state (Genv.globalenv p) beh.

