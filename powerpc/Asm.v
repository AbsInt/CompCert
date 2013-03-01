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
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Stacklayout.
Require Import Conventions.

(** * Abstract syntax *)

(** Integer registers, floating-point registers. *)

Inductive ireg: Type :=
  | GPR0: ireg  | GPR1: ireg  | GPR2: ireg  | GPR3: ireg
  | GPR4: ireg  | GPR5: ireg  | GPR6: ireg  | GPR7: ireg
  | GPR8: ireg  | GPR9: ireg  | GPR10: ireg | GPR11: ireg
  | GPR12: ireg | GPR13: ireg | GPR14: ireg | GPR15: ireg
  | GPR16: ireg | GPR17: ireg | GPR18: ireg | GPR19: ireg
  | GPR20: ireg | GPR21: ireg | GPR22: ireg | GPR23: ireg
  | GPR24: ireg | GPR25: ireg | GPR26: ireg | GPR27: ireg
  | GPR28: ireg | GPR29: ireg | GPR30: ireg | GPR31: ireg.

Inductive freg: Type :=
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

(** The PowerPC has a great many registers, some general-purpose, some very
  specific.  We model only the following registers: *)

Inductive preg: Type :=
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

(** Conventional names for stack pointer ([SP]) and return address ([RA]) *)

Notation "'SP'" := GPR1 (only parsing).
Notation "'RA'" := LR (only parsing).

(** Symbolic constants.  Immediate operands to an arithmetic instruction
  or an indexed memory access can be either integer literals,
  or the low or high 16 bits of a symbolic reference (the address
  of a symbol plus a displacement), or a 16-bit offset from the
  small data area register.  These symbolic references are
  resolved later by the linker.
*)

Inductive constant: Type :=
  | Cint: int -> constant
  | Csymbol_low: ident -> int -> constant
  | Csymbol_high: ident -> int -> constant
  | Csymbol_sda: ident -> int -> constant.

(** A note on constants: while immediate operands to PowerPC
  instructions must be representable in 16 bits (with
  sign extension or left shift by 16 positions for some instructions),
  we do not attempt to capture these restrictions in the 
  abstract syntax nor in the semantics.  The assembler will
  emit an error if immediate operands exceed the representable
  range.  Of course, our PPC generator (file [Asmgen]) is
  careful to respect this range. *)

(** Bits in the condition register.  We are only interested in the
  first 4 bits. *)

Inductive crbit: Type :=
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

Inductive instruction : Type :=
  | Padd: ireg -> ireg -> ireg -> instruction                 (**r integer addition *)
  | Padde: ireg -> ireg -> ireg -> instruction                 (**r integer addition with carry *)
  | Paddi: ireg -> ireg -> constant -> instruction            (**r add immediate *)
  | Paddic: ireg -> ireg -> constant -> instruction            (**r add immediate and set carry *)
  | Paddis: ireg -> ireg -> constant -> instruction           (**r add immediate high *)
  | Paddze: ireg -> ireg -> instruction                       (**r add carry *)
  | Pallocframe: Z -> int -> instruction                      (**r allocate new stack frame *)
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
  | Pbtbl: ireg -> list label -> instruction                  (**r N-way branch through a jump table *)
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
  | Pfreeframe: Z -> int -> instruction                       (**r deallocate stack frame and restore previous frame *)
  | Pfabs: freg -> freg -> instruction                        (**r float absolute value *)
  | Pfadd: freg -> freg -> freg -> instruction                (**r float addition *)
  | Pfcmpu: freg -> freg -> instruction                       (**r float comparison *)
  | Pfcti: ireg -> freg -> instruction                        (**r float-to-signed-int conversion *)
  | Pfdiv: freg -> freg -> freg -> instruction                (**r float division *)
  | Pfmake: freg -> ireg -> ireg -> instruction               (**r build a float from 2 ints *)
  | Pfmr: freg -> freg -> instruction                         (**r float move *)
  | Pfmul: freg -> freg -> freg -> instruction                (**r float multiply *)
  | Pfneg: freg -> freg -> instruction                        (**r float negation *)
  | Pfrsp: freg -> freg -> instruction                        (**r float round to single precision *)
  | Pfsub: freg -> freg -> freg -> instruction                (**r float subtraction *)
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
  | Prlwimi: ireg -> ireg -> int -> int -> instruction        (**r rotate and insert *)
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
  | Psubfe: ireg -> ireg -> ireg -> instruction               (**r reversed integer subtraction with carry *)
  | Psubfic: ireg -> ireg -> constant -> instruction          (**r integer subtraction from immediate *)
  | Pxor: ireg -> ireg -> ireg -> instruction                 (**r bitwise xor *)
  | Pxori: ireg -> ireg -> constant -> instruction            (**r bitwise xor with immediate *)
  | Pxoris: ireg -> ireg -> constant -> instruction           (**r bitwise xor with immediate high *)
  | Plabel: label -> instruction                              (**r define a code label *)
  | Pbuiltin: external_function -> list preg -> preg -> instruction (**r built-in function *)
  | Pannot: external_function -> list annot_param -> instruction (**r annotation statement *)

with annot_param : Type :=
  | APreg: preg -> annot_param
  | APstack: memory_chunk -> Z -> annot_param.

(** The pseudo-instructions are the following:

- [Plabel]: define a code label at the current program point
- [Plfi]: load a floating-point constant in a float register.
  Expands to a float load [lfd] from an address in the constant data section
  initialized with the floating-point constant:
<<
        addis   r12, 0, ha16(lbl)
        lfd     rdst, lo16(lbl)(r12)
        .const_data
lbl:    .double floatcst
        .text
>>
  Initialized data in the constant data section are not modeled here,
  which is why we use a pseudo-instruction for this purpose.
- [Pfcti]: convert a float to a signed integer.  This requires a transfer
  via memory of a 32-bit integer from a float register to an int register.
  Expands to:
<<
        fctiwz  f13, rsrc
        stfdu   f13, -8(r1)
        lwz     rdst, 4(r1)
        addi    r1, r1, 8
>>
- [Pfmake]: build a double float from two 32-bit integers.  This also
  requires a transfer via memory.  Expands to:
<<
        stwu    rsrc1, -8(r1)
        stw     rsrc2, 4(r1)
        lfd     rdst, 0(r1)
        addi    r1, r1, 8
>>
- [Pallocframe sz ofs]: in the formal semantics, this pseudo-instruction
  allocates a memory block with bounds [0] and [sz], stores the value
  of register [r1] (the stack pointer, by convention) at offset [ofs]
  in this block, and sets [r1] to a pointer to the bottom of this
  block.  In the printed PowerPC assembly code, this allocation
  is just a store-decrement of register [r1], assuming that [ofs = 0]:
<<
        stwu    r1, -sz(r1)
>>
  This cannot be expressed in our memory model, which does not reflect
  the fact that stack frames are adjacent and allocated/freed
  following a stack discipline.
- [Pfreeframe sz ofs]: in the formal semantics, this pseudo-instruction
  reads the word at offset [ofs] in the block pointed by [r1] (the
  stack pointer), frees this block, and sets [r1] to the value of the
  word at offset [ofs].  In the printed PowerPC assembly code, this
  freeing is just a load of register [r1] relative to [r1] itself:
<<
        lwz     r1, ofs(r1)
>>
  Again, our memory model cannot comprehend that this operation
  frees (logically) the current stack frame.
- [Pbtbl reg table]: this is a N-way branch, implemented via a jump table
  as follows:
<<
        addis   r12, reg, ha16(lbl)
        lwz     r12, lo16(lbl)(r12)
        mtctr   r12
        bctr    r12
lbl:    .long   table[0], table[1], ...
>>
  Note that [reg] contains 4 times the index of the desired table entry.
*)

Definition code := list instruction.
Definition function := code.
Definition fn_code (f: function) : code := f.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain (but do not enforce)
  the convention that integer registers are mapped to values of
  type [Tint], float registers to values of type [Tfloat],
  and boolean registers ([CARRY], [CR0_0], etc) to either
  [Vzero] or [Vone]. *)
  
Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef unit.

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).

(** Undefining some registers *)

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.

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

(** The two functions below axiomatize how the linker processes
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
 
(** We also axiomatize the small data area.  For simplicity, we
  claim that small data symbols can be accessed by absolute 16-bit
  offsets, that is, relative to [GPR0].  In reality, the linker
  rewrites the object code, transforming [symb@sdarx(r0)] addressings
  into [offset(rN)] addressings, where [rN] is the reserved
  register pointing to the base of the small data area containing
  symbol [symb].  We leave this transformation up to the linker. *)

Parameter symbol_is_small_data: ident -> int -> bool.
Parameter small_data_area_offset: genv -> ident -> int -> val.

Axiom small_data_area_addressing:
  forall id ofs,
  symbol_is_small_data id ofs = true ->
  small_data_area_offset ge id ofs = symbol_offset id ofs.

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
  | Csymbol_sda id ofs => small_data_area_offset ge id ofs
  end.

Definition const_high (c: constant) :=
  match c with
  | Cint n => Vint (Int.shl n (Int.repr 16))
  | Csymbol_low id ofs => Vundef
  | Csymbol_high id ofs => high_half (symbol_offset id ofs)
  | Csymbol_sda id ofs => Vundef
  end.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [OK rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Error] if the processor is stuck. *)

Inductive outcome: Type :=
  | Next: regset -> mem -> outcome
  | Stuck: outcome.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]). *)

Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.add rs#PC Vone).

Definition goto_label (c: code) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 c with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Int.repr pos))) m
      | _ => Stuck
    end
  end.

(** Auxiliaries for memory accesses, in two forms: one operand
  (plus constant offset) or two operands. *)

Definition load1 (chunk: memory_chunk) (rd: preg)
                 (cst: constant) (r1: ireg) (rs: regset) (m: mem) :=
  match Mem.loadv chunk m (Val.add (gpr_or_zero rs r1) (const_low cst)) with
  | None => Stuck
  | Some v => Next (nextinstr (rs#rd <- v)) m
  end.

Definition load2 (chunk: memory_chunk) (rd: preg) (r1 r2: ireg)
                 (rs: regset) (m: mem) :=
  match Mem.loadv chunk m (Val.add rs#r1 rs#r2) with
  | None => Stuck
  | Some v => Next (nextinstr (rs#rd <- v)) m
  end.

Definition store1 (chunk: memory_chunk) (r: preg)
                  (cst: constant) (r1: ireg) (rs: regset) (m: mem) :=
  match Mem.storev chunk m (Val.add (gpr_or_zero rs r1) (const_low cst)) (rs#r) with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

Definition store2 (chunk: memory_chunk) (r: preg) (r1 r2: ireg)
                  (rs: regset) (m: mem) :=
  match Mem.storev chunk m (Val.add rs#r1 rs#r2) (rs#r) with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
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

Definition compare_uint (rs: regset) (m: mem) (v1 v2: val) :=
  rs#CR0_0 <- (Val.cmpu (Mem.valid_pointer m) Clt v1 v2)
    #CR0_1 <- (Val.cmpu (Mem.valid_pointer m) Cgt v1 v2)
    #CR0_2 <- (Val.cmpu (Mem.valid_pointer m) Ceq v1 v2)
    #CR0_3 <- Vundef.

Definition compare_float (rs: regset) (v1 v2: val) :=
  rs#CR0_0 <- (Val.cmpf Clt v1 v2)
    #CR0_1 <- (Val.cmpf Cgt v1 v2)
    #CR0_2 <- (Val.cmpf Ceq v1 v2)
    #CR0_3 <- Vundef.

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
      Next (nextinstr (rs#rd <- (Val.add rs#r1 rs#r2))) m
  | Padde rd r1 r2 =>
      Next (nextinstr (rs #rd <- (Val.add (Val.add rs#r1 rs#r2) rs#CARRY)
                        #CARRY <- (Val.add_carry rs#r1 rs#r2 rs#CARRY))) m
  | Paddi rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.add (gpr_or_zero rs r1) (const_low cst)))) m
  | Paddic rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.add (gpr_or_zero rs r1) (const_low cst))
                       #CARRY <- (Val.add_carry (gpr_or_zero rs r1) (const_low cst) Vzero))) m
  | Paddis rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.add (gpr_or_zero rs r1) (const_high cst)))) m
  | Paddze rd r1 =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 rs#CARRY)
                       #CARRY <- (Val.add_carry rs#r1 Vzero rs#CARRY))) m
  | Pallocframe sz ofs =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := Vptr stk Int.zero in
      match Mem.storev Mint32 m1 (Val.add sp (Vint ofs)) rs#GPR1 with
      | None => Stuck
      | Some m2 => Next (nextinstr (rs#GPR1 <- sp #GPR0 <- Vundef)) m2
      end
  | Pand_ rd r1 r2 =>
      let v := Val.and rs#r1 rs#r2 in
      Next (nextinstr (compare_sint (rs#rd <- v) v Vzero)) m
  | Pandc rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.and rs#r1 (Val.notint rs#r2)))) m
  | Pandi_ rd r1 cst =>
      let v := Val.and rs#r1 (const_low cst) in
      Next (nextinstr (compare_sint (rs#rd <- v) v Vzero)) m
  | Pandis_ rd r1 cst =>
      let v := Val.and rs#r1 (const_high cst) in
      Next (nextinstr (compare_sint (rs#rd <- v) v Vzero)) m
  | Pb lbl =>
      goto_label c lbl rs m
  | Pbctr =>
      Next (rs#PC <- (rs#CTR)) m
  | Pbctrl =>
      Next (rs#LR <- (Val.add rs#PC Vone) #PC <- (rs#CTR)) m
  | Pbf bit lbl =>
      match rs#(reg_of_crbit bit) with
      | Vint n => if Int.eq n Int.zero then goto_label c lbl rs m else Next (nextinstr rs) m
      | _ => Stuck
      end
  | Pbl ident =>
      Next (rs#LR <- (Val.add rs#PC Vone) #PC <- (symbol_offset ident Int.zero)) m
  | Pbs ident =>
      Next (rs#PC <- (symbol_offset ident Int.zero)) m
  | Pblr =>
      Next (rs#PC <- (rs#LR)) m
  | Pbt bit lbl =>
      match rs#(reg_of_crbit bit) with
      | Vint n => if Int.eq n Int.zero then Next (nextinstr rs) m else goto_label c lbl rs m
      | _ => Stuck
      end
  | Pbtbl r tbl =>
      match rs r with
      | Vint n => 
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label c lbl (rs #GPR12 <- Vundef #CTR <- Vundef) m
          end
      | _ => Stuck
      end
  | Pcmplw r1 r2 =>
      Next (nextinstr (compare_uint rs m rs#r1 rs#r2)) m
  | Pcmplwi r1 cst =>
      Next (nextinstr (compare_uint rs m rs#r1 (const_low cst))) m
  | Pcmpw r1 r2 =>
      Next (nextinstr (compare_sint rs rs#r1 rs#r2)) m
  | Pcmpwi r1 cst =>
      Next (nextinstr (compare_sint rs rs#r1 (const_low cst))) m
  | Pcror bd b1 b2 =>
      Next (nextinstr (rs#(reg_of_crbit bd) <- (Val.or rs#(reg_of_crbit b1) rs#(reg_of_crbit b2)))) m
  | Pdivw rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.divs rs#r1 rs#r2)))) m
  | Pdivwu rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.divu rs#r1 rs#r2)))) m
  | Peqv rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.notint (Val.xor rs#r1 rs#r2)))) m
  | Pextsb rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1))) m
  | Pextsh rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1))) m
  | Pfreeframe sz ofs =>
      match Mem.loadv Mint32 m (Val.add rs#GPR1 (Vint ofs)) with
      | None => Stuck
      | Some v =>
          match rs#GPR1 with
          | Vptr stk ofs =>
              match Mem.free m stk 0 sz with
              | None => Stuck
              | Some m' => Next (nextinstr (rs#GPR1 <- v)) m'
              end
          | _ => Stuck
          end
      end
  | Pfabs rd r1 =>
      Next (nextinstr (rs#rd <- (Val.absf rs#r1))) m
  | Pfadd rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.addf rs#r1 rs#r2))) m
  | Pfcmpu r1 r2 =>
      Next (nextinstr (compare_float rs rs#r1 rs#r2)) m
  | Pfcti rd r1 =>
      Next (nextinstr (rs#FPR13 <- Vundef #rd <- (Val.maketotal (Val.intoffloat rs#r1)))) m
  | Pfdiv rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.divf rs#r1 rs#r2))) m
  | Pfmake rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.floatofwords rs#r1 rs#r2))) m
  | Pfmr rd r1 =>
      Next (nextinstr (rs#rd <- (rs#r1))) m
  | Pfmul rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mulf rs#r1 rs#r2))) m
  | Pfneg rd r1 =>
      Next (nextinstr (rs#rd <- (Val.negf rs#r1))) m
  | Pfrsp rd r1 =>
      Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1))) m
  | Pfsub rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.subf rs#r1 rs#r2))) m
  | Plbz rd cst r1 =>
      load1 Mint8unsigned rd cst r1 rs m
  | Plbzx rd r1 r2 =>
      load2 Mint8unsigned rd r1 r2 rs m
  | Plfd rd cst r1 =>
      load1 Mfloat64al32 rd cst r1 rs m
  | Plfdx rd r1 r2 =>
      load2 Mfloat64al32 rd r1 r2 rs m
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
      Next (nextinstr (rs #GPR12 <- Vundef #rd <- (Vfloat f))) m
  | Plwz rd cst r1 =>
      load1 Mint32 rd cst r1 rs m
  | Plwzx rd r1 r2 =>
      load2 Mint32 rd r1 r2 rs m
  | Pmfcrbit rd bit =>
      Next (nextinstr (rs#rd <- (rs#(reg_of_crbit bit)))) m
  | Pmflr rd =>
      Next (nextinstr (rs#rd <- (rs#LR))) m
  | Pmr rd r1 =>
      Next (nextinstr (rs#rd <- (rs#r1))) m
  | Pmtctr r1 =>
      Next (nextinstr (rs#CTR <- (rs#r1))) m
  | Pmtlr r1 =>
      Next (nextinstr (rs#LR <- (rs#r1))) m
  | Pmulli rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.mul rs#r1 (const_low cst)))) m
  | Pmullw rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mul rs#r1 rs#r2))) m
  | Pnand rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.notint (Val.and rs#r1 rs#r2)))) m
  | Pnor rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.notint (Val.or rs#r1 rs#r2)))) m
  | Por rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.or rs#r1 rs#r2))) m
  | Porc rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.or rs#r1 (Val.notint rs#r2)))) m
  | Pori rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.or rs#r1 (const_low cst)))) m
  | Poris rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.or rs#r1 (const_high cst)))) m
  | Prlwinm rd r1 amount mask =>
      Next (nextinstr (rs#rd <- (Val.rolm rs#r1 amount mask))) m
  | Prlwimi rd r1 amount mask =>
      Next (nextinstr (rs#rd <- (Val.or (Val.and rs#rd (Vint (Int.not mask)))
                                     (Val.rolm rs#r1 amount mask)))) m
  | Pslw rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shl rs#r1 rs#r2))) m
  | Psraw rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shr rs#r1 rs#r2) #CARRY <- (Val.shr_carry rs#r1 rs#r2))) m
  | Psrawi rd r1 n =>
      Next (nextinstr (rs#rd <- (Val.shr rs#r1 (Vint n)) #CARRY <- (Val.shr_carry rs#r1 (Vint n)))) m
  | Psrw rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shru rs#r1 rs#r2))) m
  | Pstb rd cst r1 =>
      store1 Mint8unsigned rd cst r1 rs m
  | Pstbx rd r1 r2 =>
      store2 Mint8unsigned rd r1 r2 rs m
  | Pstfd rd cst r1 =>
      store1 Mfloat64al32 rd cst r1 rs m
  | Pstfdx rd r1 r2 =>
      store2 Mfloat64al32 rd r1 r2 rs m
  | Pstfs rd cst r1 =>
      match store1 Mfloat32 rd cst r1 rs m with
      | Next rs' m' => Next (rs'#FPR13 <- Vundef) m'
      | Stuck => Stuck
      end
  | Pstfsx rd r1 r2 =>
      match store2 Mfloat32 rd r1 r2 rs m with
      | Next rs' m' => Next (rs'#FPR13 <- Vundef) m'
      | Stuck => Stuck
      end
  | Psth rd cst r1 =>
      store1 Mint16unsigned rd cst r1 rs m
  | Psthx rd r1 r2 =>
      store2 Mint16unsigned rd r1 r2 rs m
  | Pstw rd cst r1 =>
      store1 Mint32 rd cst r1 rs m
  | Pstwx rd r1 r2 =>
      store2 Mint32 rd r1 r2 rs m
  | Psubfc rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.sub rs#r2 rs#r1)
                       #CARRY <- (Val.add_carry rs#r2 (Val.notint rs#r1) Vone))) m
  | Psubfe rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.add (Val.add rs#r2 (Val.notint rs#r1)) rs#CARRY)
                       #CARRY <- (Val.add_carry rs#r2 (Val.notint rs#r1) rs#CARRY))) m
  | Psubfic rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.sub (const_low cst) rs#r1)
                       #CARRY <- (Val.add_carry (const_low cst) (Val.notint rs#r1) Vone))) m
  | Pxor rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.xor rs#r1 rs#r2))) m
  | Pxori rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.xor rs#r1 (const_low cst)))) m
  | Pxoris rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.xor rs#r1 (const_high cst)))) m
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Pbuiltin ef args res =>
      Stuck    (**r treated specially below *)
  | Pannot ef args =>
      Stuck    (**r treated specially below *)
  end.

(** Translation of the LTL/Linear/Mach view of machine registers
  to the PPC view.  Note that no LTL register maps to [GPR0].
  This register is reserved as a temporary to be used
  by the generated PPC code.  *)

Definition preg_of (r: mreg) : preg :=
  match r with
  | R3 => GPR3  | R4 => GPR4  | R5 => GPR5  | R6 => GPR6
  | R7 => GPR7  | R8 => GPR8  | R9 => GPR9  | R10 => GPR10
  | R14 => GPR14 | R15 => GPR15 | R16 => GPR16
  | R17 => GPR17 | R18 => GPR18 | R19 => GPR19 | R20 => GPR20
  | R21 => GPR21 | R22 => GPR22 | R23 => GPR23 | R24 => GPR24
  | R25 => GPR25 | R26 => GPR26 | R27 => GPR27 | R28 => GPR28
  | R29 => GPR29 | R30 => GPR30 | R31 => GPR31
  | IT1 => GPR11 | IT2 => GPR12
  | F1 => FPR1  | F2 => FPR2  | F3 => FPR3  | F4 => FPR4
  | F5 => FPR5  | F6 => FPR6  | F7 => FPR7  | F8 => FPR8
  | F9 => FPR9  | F10 => FPR10 | F11 => FPR11
  | F14 => FPR14 | F15 => FPR15
  | F16 => FPR16 | F17 => FPR17 | F18 => FPR18 | F19 => FPR19
  | F20 => FPR20 | F21 => FPR21 | F22 => FPR22 | F23 => FPR23
  | F24 => FPR24 | F25 => FPR25 | F26 => FPR26 | F27 => FPR27
  | F28 => FPR28 | F29 => FPR29 | F30 => FPR30 | F31 => FPR31
  | FT1 => FPR0 | FT2 => FPR12 | FT3 => FPR13
  end.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use PPC registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_int_stack: forall ofs bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv Mint32 m (Val.add (rs (IR GPR1)) (Vint (Int.repr bofs))) = Some v ->
      extcall_arg rs m (S (Outgoing ofs Tint)) v
  | extcall_arg_float_stack: forall ofs bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv Mfloat64al32 m (Val.add (rs (IR GPR1)) (Vint (Int.repr bofs))) = Some v ->
      extcall_arg rs m (S (Outgoing ofs Tfloat)) v.

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg rs m) (loc_arguments sg) args.

Definition loc_external_result (sg: signature) : preg :=
  preg_of (loc_result sg).

(** Extract the values of the arguments of an annotation. *)

Inductive annot_arg (rs: regset) (m: mem): annot_param -> val -> Prop :=
  | annot_arg_reg: forall r,
      annot_arg rs m (APreg r) (rs r)
  | annot_arg_stack: forall chunk ofs stk base v,
      rs (IR GPR1) = Vptr stk base ->
      Mem.load chunk m stk (Int.unsigned base + ofs) = Some v ->
      annot_arg rs m (APstack chunk ofs) v.

Definition annot_arguments
    (rs: regset) (m: mem) (params: list annot_param) (args: list val) : Prop :=
  list_forall2 (annot_arg rs m) params args.

(** Execution of the instruction at [rs#PC]. *)

Inductive state: Type :=
  | State: regset -> mem -> state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs c i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal c) ->
      find_instr (Int.unsigned ofs) c = Some i ->
      exec_instr c i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs c ef args res rs m t v m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal c) ->
      find_instr (Int.unsigned ofs) c = Some (Pbuiltin ef args res) ->
      external_call ef ge (map rs args) m t v m' ->
      step (State rs m) t
           (State (nextinstr(rs #GPR11 <- Vundef #GPR12 <- Vundef
                                #FPR12 <- Vundef #FPR13 <- Vundef
                                #FPR0 <- Vundef #CTR <- Vundef
                                #res <- v)) m')
  | exec_step_annot:
      forall b ofs c ef args rs m vargs t v m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal c) ->
      find_instr (Int.unsigned ofs) c = Some (Pannot ef args) ->
      annot_arguments rs m args vargs ->
      external_call ef ge vargs m t v m' ->
      step (State rs m) t
           (State (nextinstr rs) m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (rs#(loc_external_result (ef_sig ef)) <- res
               #PC <- (rs LR)) ->
      step (State rs m) t (State rs' m').

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      Genv.init_mem p = Some m0 ->
      let ge := Genv.globalenv p in
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
      
Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (forall ll vl1, list_forall2 (extcall_arg rs m) ll vl1 ->
          forall vl2, list_forall2 (extcall_arg rs m) ll vl2 -> vl1 = vl2).
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; auto. 
    inv H; inv H3; congruence.
  intros. red in H0; red in H1. eauto. 
Qed.

Remark annot_arguments_determ:
  forall rs m params args1 args2,
  annot_arguments rs m params args1 -> annot_arguments rs m params args2 -> args1 = args2.
Proof.
  unfold annot_arguments. intros. revert params args1 H args2 H0. 
  induction 1; intros. 
  inv H0; auto.
  inv H1. decEq; eauto. inv H; inv H4. auto. congruence. 
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
(* determ *)
  inv H; inv H0; Equalities.
  split. constructor. auto.
  discriminate.
  discriminate.
  inv H11. 
  exploit external_call_determ. eexact H4. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
  inv H12.
  assert (vargs0 = vargs) by (eapply annot_arguments_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H13. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
  assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H3. eexact H8. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
(* trace length *)
  red; intros. inv H; simpl.
  omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
(* initial states *)
  inv H; inv H0. f_equal. congruence.
(* final no step *)
  inv H. unfold Vzero in H0. red; intros; red; intros. inv H; congruence.
(* final states *)
  inv H; inv H0. congruence.
Qed.

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | IR GPR0 => false
  | PC => false    | LR => false    | CTR => false
  | CR0_0 => false | CR0_1 => false | CR0_2 => false | CR0_3 => false
  | CARRY => false
  | _ => true
  end.

Definition nontemp_preg (r: preg) : bool :=
  match r with
  | IR GPR0 => false | IR GPR11 => false | IR GPR12 => false
  | FR FPR0 => false | FR FPR12 => false | FR FPR13 => false
  | PC => false      | LR => false       | CTR => false
  | CR0_0 => false   | CR0_1 => false    | CR0_2 => false    | CR0_3 => false
  | CARRY => false
  | _ => true
  end.

