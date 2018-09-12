
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

(** Abstract syntax and semantics for ARM assembly language *)

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
  | IR0: ireg  | IR1: ireg  | IR2: ireg  | IR3: ireg
  | IR4: ireg  | IR5: ireg  | IR6: ireg  | IR7: ireg
  | IR8: ireg  | IR9: ireg  | IR10: ireg | IR11: ireg
  | IR12: ireg | IR13: ireg | IR14: ireg.

Inductive freg: Type :=
  | FR0: freg  | FR1: freg  | FR2: freg  | FR3: freg
  | FR4: freg  | FR5: freg  | FR6: freg  | FR7: freg
  | FR8: freg  | FR9: freg  | FR10: freg  | FR11: freg
  | FR12: freg  | FR13: freg  | FR14: freg  | FR15: freg.

Inductive sreg: Type :=
  | SR0: sreg  | SR1: sreg  | SR2: sreg  | SR3: sreg
  | SR4: sreg  | SR5: sreg  | SR6: sreg  | SR7: sreg
  | SR8: sreg  | SR9: sreg  | SR10: sreg  | SR11: sreg
  | SR12: sreg  | SR13: sreg  | SR14: sreg  | SR15: sreg
  | SR16: sreg  | SR17: sreg  | SR18: sreg  | SR19: sreg
  | SR20: sreg  | SR21: sreg  | SR22: sreg  | SR23: sreg
  | SR24: sreg  | SR25: sreg  | SR26: sreg  | SR27: sreg
  | SR28: sreg  | SR29: sreg  | SR30: sreg  | SR31: sreg.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

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
  | IR: ireg -> preg                    (**r integer registers *)
  | FR: freg -> preg                    (**r double-precision VFP float registers *)
  | CR: crbit -> preg                   (**r bits in the condition register *)
  | PC: preg.                           (**r program counter *)

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

(** Conventional names for stack pointer ([SP]) and return address ([RA]) *)

Notation "'SP'" := IR13 (only parsing) : asm.
Notation "'RA'" := IR14 (only parsing) : asm.

(** The instruction set.  Most instructions correspond exactly to
  actual instructions of the ARM processor. See the ARM
  reference manuals for more details.  Some instructions,
  described below, are pseudo-instructions: they expand to
  canned instruction sequences during the printing of the assembly
  code.  Most instructions are common to Thumb2 and ARM classic.
  We use a few Thumb2-specific instructions when available, and avoid
  to use ARM classic features that are not in Thumb2. *)

Definition label := positive.

Inductive shift_op : Type :=
  | SOimm: int -> shift_op
  | SOreg: ireg -> shift_op
  | SOlsl: ireg -> int -> shift_op
  | SOlsr: ireg -> int -> shift_op
  | SOasr: ireg -> int -> shift_op
  | SOror: ireg -> int -> shift_op.

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

Inductive code_constant: Type :=
| Float32 : label -> float32 -> code_constant
| Float64 : label -> float -> code_constant
| Symbol : label -> ident -> ptrofs -> code_constant.

Inductive instruction : Type :=
  (* Core instructions *)
  | Padd: ireg -> ireg -> shift_op -> instruction (**r integer addition *)
  | Pand: ireg -> ireg -> shift_op -> instruction (**r bitwise and *)
  | Pasr: ireg -> ireg -> ireg -> instruction     (**r arithmetic shift right *)
  | Pb: label -> instruction                      (**r branch to label *)
  | Pbc: testcond -> label -> instruction            (**r conditional branch to label *)
  | Pbsymb: ident -> signature -> instruction                  (**r branch to symbol *)
  | Pbreg: ireg -> signature -> instruction                    (**r computed branch *)
  | Pblsymb: ident -> signature -> instruction                 (**r branch and link to symbol *)
  | Pblreg: ireg -> signature -> instruction                   (**r computed branch and link *)
  | Pbic: ireg -> ireg -> shift_op -> instruction (**r bitwise bit-clear *)
  | Pcmp: ireg -> shift_op -> instruction         (**r integer comparison *)
  | Pcmn: ireg -> shift_op -> instruction         (**r integer comparison with opposite *)
  | Peor: ireg -> ireg -> shift_op -> instruction (**r bitwise exclusive or *)
  | Pldr: ireg -> ireg -> shift_op -> instruction (**r int32 load *)
  | Pldr_a: ireg -> ireg -> shift_op -> instruction (**r any32 load to int register *)
  | Pldrb: ireg -> ireg -> shift_op -> instruction (**r unsigned int8 load *)
  | Pldrh: ireg -> ireg -> shift_op -> instruction (**r unsigned int16 load *)
  | Pldrsb: ireg -> ireg -> shift_op -> instruction (**r signed int8 load *)
  | Pldrsh: ireg -> ireg -> shift_op -> instruction (**r unsigned int16 load *)
  | Plsl: ireg -> ireg -> ireg -> instruction       (**r shift left *)
  | Plsr: ireg -> ireg -> ireg -> instruction       (**r logical shift right *)
  | Pmla: ireg -> ireg -> ireg -> ireg -> instruction      (**r integer multiply-add *)
  | Pmov: ireg -> shift_op -> instruction          (**r integer move *)
  | Pmovw: ireg -> int -> instruction              (**r move 16-bit immediate *)
  | Pmovt: ireg -> int -> instruction              (**r set high 16 bits *)
  | Pmul: ireg -> ireg -> ireg -> instruction      (**r integer multiplication *)
  | Pmvn: ireg -> shift_op -> instruction          (**r integer complement *)
  | Porr: ireg -> ireg -> shift_op -> instruction  (**r bitwise or *)
  | Ppush: list ireg -> instruction (** push registers on the stack instruction *)
  | Prsb: ireg -> ireg -> shift_op -> instruction  (**r integer reverse subtraction *)
  | Psbfx: ireg -> ireg -> int -> int -> instruction (**r signed bitfield extract *)
  | Pstr: ireg -> ireg -> shift_op -> instruction (**r int32 store *)
  | Pstr_a: ireg -> ireg -> shift_op -> instruction (**r any32 store from int register *)
  | Pstrb: ireg -> ireg -> shift_op -> instruction (**r int8 store *)
  | Pstrh: ireg -> ireg -> shift_op -> instruction (**r int16 store *)
  | Psdiv: instruction                              (**r signed division *)
  | Psmull: ireg -> ireg -> ireg -> ireg -> instruction (**r signed multiply long *)
  | Psub: ireg -> ireg -> shift_op -> instruction  (**r integer subtraction *)
  | Pudiv: instruction                             (**r unsigned division *)
  | Pumull: ireg -> ireg -> ireg -> ireg -> instruction (**r unsigned multiply long *)
  (* Floating-point coprocessor instructions (VFP double scalar operations) *)
  | Pfcpyd: freg -> freg -> instruction             (**r float move *)
  | Pfabsd: freg -> freg -> instruction             (**r float absolute value *)
  | Pfnegd: freg -> freg -> instruction             (**r float opposite *)
  | Pfaddd: freg -> freg -> freg -> instruction     (**r float addition *)
  | Pfdivd: freg -> freg -> freg -> instruction     (**r float division *)
  | Pfmuld: freg -> freg -> freg -> instruction     (**r float multiplication *)
  | Pfsubd: freg -> freg -> freg -> instruction     (**r float subtraction *)
  | Pflid: freg -> float -> instruction             (**r load float constant *)
  | Pfcmpd: freg -> freg -> instruction             (**r float comparison *)
  | Pfcmpzd: freg -> instruction                    (**r float comparison with 0.0 *)
  | Pfsitod: freg -> ireg -> instruction            (**r signed int to float *)
  | Pfuitod: freg -> ireg -> instruction            (**r unsigned int to float *)
  | Pftosizd: ireg -> freg -> instruction           (**r float to signed int *)
  | Pftouizd: ireg -> freg -> instruction           (**r float to unsigned int *)
  | Pfabss: freg -> freg -> instruction             (**r float absolute value *)
  | Pfnegs: freg -> freg -> instruction             (**r float opposite *)
  | Pfadds: freg -> freg -> freg -> instruction     (**r float addition *)
  | Pfdivs: freg -> freg -> freg -> instruction     (**r float division *)
  | Pfmuls: freg -> freg -> freg -> instruction     (**r float multiplication *)
  | Pfsubs: freg -> freg -> freg -> instruction     (**r float subtraction *)
  | Pflis: freg -> float32 -> instruction           (**r load float constant *)
  | Pfcmps: freg -> freg -> instruction             (**r float comparison *)
  | Pfcmpzs: freg -> instruction                    (**r float comparison with 0.0 *)
  | Pfsitos: freg -> ireg -> instruction            (**r signed int to float *)
  | Pfuitos: freg -> ireg -> instruction            (**r unsigned int to float *)
  | Pftosizs: ireg -> freg -> instruction           (**r float to signed int *)
  | Pftouizs: ireg -> freg -> instruction           (**r float to unsigned int *)
  | Pfcvtsd: freg -> freg -> instruction            (**r round to single precision *)
  | Pfcvtds: freg -> freg -> instruction            (**r expand to double precision *)
  | Pfldd: freg -> ireg -> int -> instruction       (**r float64 load *)
  | Pfldd_a: freg -> ireg -> int -> instruction     (**r any64 load to FP reg *)
  | Pflds: freg -> ireg -> int -> instruction       (**r float32 load *)
  | Pfstd: freg -> ireg -> int -> instruction       (**r float64 store *)
  | Pfstd_a: freg -> ireg -> int -> instruction     (**r any64 store from FP reg *)
  | Pfsts: freg -> ireg -> int -> instruction       (**r float32 store *)

  (* Pseudo-instructions *)
  | Pallocframe: Z -> ptrofs -> instruction         (**r allocate new stack frame *)
  | Pfreeframe: Z -> ptrofs -> instruction          (**r deallocate stack frame and restore previous frame *)
  | Plabel: label -> instruction                    (**r define a code label *)
  | Ploadsymbol: ireg -> ident -> ptrofs -> instruction (**r load the address of a symbol *)
  | Pmovite: testcond -> ireg -> shift_op -> shift_op -> instruction (**r integer conditional move *)
  | Pbtbl: ireg -> list label -> instruction       (**r N-way branch through a jump table *)
  | Pbuiltin: external_function -> list (builtin_arg preg) -> builtin_res preg -> instruction (**r built-in function (pseudo) *)
  | Padc: ireg -> ireg -> shift_op -> instruction     (**r add with carry *)
  | Pcfi_adjust: int -> instruction                   (**r .cfi_adjust debug directive *)
  | Pcfi_rel_offset: int -> instruction               (**r .cfi_rel_offset debug directive *)
  | Pclz: ireg -> ireg -> instruction                 (**r count leading zeros. *)
  | Pfsqrt: freg -> freg -> instruction               (**r floating-point square root. *)
  | Prev: ireg -> ireg -> instruction                 (**r reverse bytes and reverse bits. *)
  | Prev16: ireg -> ireg -> instruction               (**r reverse bytes and reverse bits. *)
  | Prsc: ireg -> ireg -> shift_op -> instruction     (**r reverse subtract without carry. *)
  | Psbc: ireg -> ireg -> shift_op -> instruction     (**r add with carry *)
  | Pnop : instruction                                (**r nop instruction *)
  (* Add, sub, rsb versions with s suffix *)
  | Padds: ireg -> ireg -> shift_op -> instruction    (**r integer addition with update of condition flags *)
  | Psubs: ireg -> ireg -> shift_op -> instruction    (**r integer subtraction with update of condition flags *)
  | Prsbs: ireg -> ireg -> shift_op -> instruction    (**r integer reverse subtraction with update of condition flags *)
  | Pdmb: instruction                                 (**r data memory barrier *)
  | Pdsb: instruction                                 (**r data synchronization barrier *)
  | Pisb: instruction                                 (**r instruction synchronization barrier *)
  | Pbne: label -> instruction                        (**r branch if negative macro *)
  | Pldr_p: ireg -> ireg -> shift_op -> instruction   (**r int32 load with post increment *)
  | Pldrb_p: ireg -> ireg -> shift_op -> instruction  (**r unsigned int8 load with post increment *)
  | Pldrh_p: ireg -> ireg -> shift_op -> instruction  (**r unsigned int16 load with post increment *)
  | Pstr_p: ireg -> ireg -> shift_op -> instruction   (**r int32 store with post increment *)
  | Pstrb_p: ireg -> ireg -> shift_op -> instruction  (**r unsigned int8 store with post increment *)
  | Pstrh_p: ireg -> ireg -> shift_op -> instruction  (**r unsigned int16 store with post increment *)

  (* Instructions for fixup of calling conventions *)
  | Pfcpy_fs: freg -> sreg -> instruction            (**r single precision float move for incoming arguments *)
  | Pfcpy_sf: sreg -> freg -> instruction            (**r single precision float move for outgoing arguments *)
  | Pfcpy_fii: freg -> ireg -> ireg -> instruction    (**r copy integer register pair to double fp-register  *)
  | Pfcpy_fi: freg -> ireg -> instruction            (**r copy integer register to single fp-register *)
  | Pfcpy_iif: ireg -> ireg -> freg -> instruction    (**r copy double fp-register to integer register pair *)
  | Pfcpy_if: ireg -> freg -> instruction            (**r copy single fp-register to integer register *)

  (* Instructions for the emitting of constants *)
  | Pconstants: list code_constant -> instruction   (**r constants in code*)
  | Ploadsymbol_imm: ireg -> ident -> ptrofs -> instruction (**r move symbol address in register *)
  | Pflid_lbl: freg -> label -> float -> instruction (**r load float64 from label *)
  | Pflis_lbl: freg -> label -> float32 -> instruction (**r load float32 from label *)
  | Pflid_imm: freg -> float -> instruction          (**r move float64 into register *)
  | Pflis_imm: freg -> float32 -> instruction        (**r move float32 into register *)
  | Ploadsymbol_lbl: ireg -> label -> ident -> ptrofs -> instruction. (**r load symbol address from label *)

(** The pseudo-instructions are the following:

- [Plabel]: define a code label at the current program point.
- [Ploadsymbol]: load the address of a symbol in an integer register.
  Expands to a load from an address in the constant data section
  initialized with the symbol value:
<<
        ldr     rdst, lbl
        .const_data
lbl:    .word   symbol
        .text
>>
  Initialized data in the constant data section are not modeled here,
  which is why we use a pseudo-instruction for this purpose.
- [Pallocframe sz pos]: in the formal semantics, this pseudo-instruction
  allocates a memory block with bounds [0] and [sz], stores the value
  of the stack pointer at offset [pos] in this block, and sets the
  stack pointer to the address of the bottom of this block.
  In the printed ASM assembly code, this allocation is:
<<
        mov     r10, sp
        sub     sp, sp, #sz
        str     r10, [sp, #pos]
>>
  This cannot be expressed in our memory model, which does not reflect
  the fact that stack frames are adjacent and allocated/freed
  following a stack discipline.
- [Pfreeframe sz pos]: in the formal semantics, this pseudo-instruction
  reads the word at [pos] of the block pointed by the stack pointer,
  frees this block, and sets the stack pointer to the value read.
  In the printed ASM assembly code, this freeing
  is just a load of register [sp] relative to [sp] itself:
<<
        ldr     sp, [sp, #pos]
>>
  Again, our memory model cannot comprehend that this operation
  frees (logically) the current stack frame.
- [Pbtbl reg table]: this is a N-way branch, implemented via a jump table
  as follows:
<<
        ldr     pc, [pc, reg]
        mov     r0, r0          (* no-op *)
        .word   table[0], table[1], ...
>>
  Note that [reg] contains 4 times the index of the desired table entry.
*)

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

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm.

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

Variable ge: genv.

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

Definition nextinstr_nf (rs: regset) :=
  nextinstr (undef_flags rs).

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _ => Stuck
    end
  end.

(** Evaluation of [shift_op] operands *)

Definition eval_shift_op (so: shift_op) (rs: regset) :=
  match so with
  | SOimm n => Vint n
  | SOreg r => rs r
  | SOlsl r n => Val.shl (rs r) (Vint n)
  | SOlsr r n => Val.shru (rs r) (Vint n)
  | SOasr r n => Val.shr (rs r) (Vint n)
  | SOror r n => Val.ror (rs r) (Vint n)
  end.

(** Auxiliaries for memory accesses *)

Definition exec_load (chunk: memory_chunk) (addr: val) (r: preg)
                     (rs: regset) (m: mem) :=
  match Mem.loadv chunk m addr with
  | None => Stuck
  | Some v => Next (nextinstr (rs#r <- v)) m
  end.

Definition exec_store (chunk: memory_chunk) (addr: val) (r: preg)
                      (rs: regset) (m: mem) :=
  match Mem.storev chunk m addr (rs r) with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

(** Comparisons. *)

Definition compare_int (rs: regset) (v1 v2: val) (m: mem) :=
  rs#CN <- (Val.negative (Val.sub v1 v2))
    #CZ <- (Val.cmpu (Mem.valid_pointer m) Ceq v1 v2)
    #CC <- (Val.cmpu (Mem.valid_pointer m) Cge v1 v2)
    #CV <- (Val.sub_overflow v1 v2).

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
        #CV <- (Val.of_bool (negb (Float.cmp Ceq f1 f2 || Float.cmp Clt f1 f2 || Float.cmp Cgt f1 f2)))
  | _, _ =>
      rs#CN <- Vundef
        #CZ <- Vundef
        #CC <- Vundef
        #CV <- Vundef
  end.

Definition compare_float32 (rs: regset) (v1 v2: val) :=
  match v1, v2 with
  | Vsingle f1, Vsingle f2 =>
      rs#CN <- (Val.of_bool (Float32.cmp Clt f1 f2))
        #CZ <- (Val.of_bool (Float32.cmp Ceq f1 f2))
        #CC <- (Val.of_bool (negb (Float32.cmp Clt f1 f2)))
        #CV <- (Val.of_bool (negb (Float32.cmp Ceq f1 f2 || Float32.cmp Clt f1 f2 || Float32.cmp Cgt f1 f2)))
  | _, _ =>
      rs#CN <- Vundef
        #CZ <- Vundef
        #CC <- Vundef
        #CV <- Vundef
  end.

(** Testing a condition *)

Definition eval_testcond (c: testcond) (rs: regset) : option bool :=
  match c with
  | TCeq =>                             (**r equal *)
      match rs CZ with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | TCne =>                             (**r not equal *)
      match rs CZ with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | TClo =>                             (**r unsigned less than  *)
      match rs CC with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | TCls =>                             (**r unsigned less or equal *)
      match rs CC, rs CZ with
      | Vint c, Vint z => Some (Int.eq c Int.zero || Int.eq z Int.one)
      | _, _ => None
      end
  | TChs =>                             (**r unsigned greater or equal *)
      match rs CC with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | TChi =>                             (**r unsigned greater *)
      match rs CC, rs CZ with
      | Vint c, Vint z => Some (Int.eq c Int.one && Int.eq z Int.zero)
      | _, _ => None
      end
  | TClt =>                             (**r signed less than *)
      match rs CV, rs CN with
      | Vint o, Vint s => Some (Int.eq (Int.xor o s) Int.one)
      | _, _ => None
      end
  | TCle =>                             (**r signed less or equal *)
      match rs CV, rs CN, rs CZ with
      | Vint o, Vint s, Vint z => Some (Int.eq (Int.xor o s) Int.one || Int.eq z Int.one)
      | _, _, _ => None
      end
  | TCge =>                             (**r signed greater or equal *)
      match rs CV, rs CN with
      | Vint o, Vint s => Some (Int.eq (Int.xor o s) Int.zero)
      | _, _ => None
      end
  | TCgt =>                             (**r signed greater *)
      match rs CV, rs CN, rs CZ with
      | Vint o, Vint s, Vint z => Some (Int.eq (Int.xor o s) Int.zero && Int.eq z Int.zero)
      | _, _, _ => None
      end
  | TCpl =>                             (**r positive *)
      match rs CN with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | TCmi =>                             (**r negative *)
      match rs CN with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  end.

(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual ARM instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the ARM reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above.

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the ARM code we
    generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction.

    Likewise, for several instructions we set the condition flags
    to [Vundef], so that we can expand them later to the S form
    or to the non-S form, whichever is more compact in Thumb2.
*)

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  | Padd r1 r2 so =>
      Next (nextinstr_nf (rs#r1 <- (Val.add rs#r2 (eval_shift_op so rs)))) m
  | Pand r1 r2 so =>
      Next (nextinstr_nf (rs#r1 <- (Val.and rs#r2 (eval_shift_op so rs)))) m
  | Pasr r1 r2 r3 =>
      Next (nextinstr_nf (rs#r1 <- (Val.shr rs#r2 rs#r3))) m
  | Pb lbl =>
      goto_label f lbl rs m
  | Pbc cond lbl =>
      match eval_testcond cond rs with
      | Some true => goto_label f lbl rs m
      | Some false => Next (nextinstr rs) m
      | None => Stuck
      end
  | Pbsymb id sg =>
      Next (rs#PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pbreg r sg =>
      Next (rs#PC <- (rs#r)) m
  | Pblsymb id sg =>
      Next (rs#IR14 <- (Val.add rs#PC Vone) #PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pblreg r sg =>
      Next (rs#IR14 <- (Val.add rs#PC Vone) #PC <- (rs#r)) m
  | Pbic r1 r2 so =>
      Next (nextinstr_nf (rs#r1 <- (Val.and rs#r2 (Val.notint (eval_shift_op so rs))))) m
  | Pcmp r1 so =>
      Next (nextinstr (compare_int rs rs#r1 (eval_shift_op so rs) m)) m
  | Pcmn r1 so =>
      Next (nextinstr (compare_int rs rs#r1 (Val.neg (eval_shift_op so rs)) m)) m
  | Peor r1 r2 so =>
      Next (nextinstr_nf (rs#r1 <- (Val.xor rs#r2 (eval_shift_op so rs)))) m
  | Pldr r1 r2 sa =>
      exec_load Mint32 (Val.add rs#r2 (eval_shift_op sa rs)) r1 rs m
  | Pldr_a r1 r2 sa =>
      exec_load Many32 (Val.add rs#r2 (eval_shift_op sa rs)) r1 rs m
  | Pldrb r1 r2 sa =>
      exec_load Mint8unsigned (Val.add rs#r2 (eval_shift_op sa rs)) r1 rs m
  | Pldrh r1 r2 sa =>
      exec_load Mint16unsigned (Val.add rs#r2 (eval_shift_op sa rs)) r1 rs m
  | Pldrsb r1 r2 sa =>
      exec_load Mint8signed (Val.add rs#r2 (eval_shift_op sa rs)) r1 rs m
  | Pldrsh r1 r2 sa =>
      exec_load Mint16signed (Val.add rs#r2 (eval_shift_op sa rs)) r1 rs m
  | Plsl r1 r2 r3 =>
      Next (nextinstr_nf (rs#r1 <- (Val.shl rs#r2 rs#r3))) m
  | Plsr r1 r2 r3 =>
      Next (nextinstr_nf (rs#r1 <- (Val.shru rs#r2 rs#r3))) m
  | Pmla r1 r2 r3 r4 =>
      Next (nextinstr (rs#r1 <- (Val.add (Val.mul rs#r2 rs#r3) rs#r4))) m
  | Pmov r1 so =>
      Next (nextinstr_nf (rs#r1 <- (eval_shift_op so rs))) m
  | Pmovw r n =>
      Next (nextinstr (rs#r <- (Vint n))) m
  | Pmovt r n =>
      Next (nextinstr (rs#r <- (Val.or (Val.and rs#r (Vint (Int.repr 65535)))
                                       (Vint (Int.shl n (Int.repr 16)))))) m
  | Pmul r1 r2 r3 =>
      Next (nextinstr (rs#r1 <- (Val.mul rs#r2 rs#r3))) m
  | Pmvn r1 so =>
      Next (nextinstr_nf (rs#r1 <- (Val.notint (eval_shift_op so rs)))) m
  | Porr r1 r2 so =>
      Next (nextinstr_nf (rs#r1 <- (Val.or rs#r2 (eval_shift_op so rs)))) m
  | Prsb r1 r2 so =>
      Next (nextinstr_nf (rs#r1 <- (Val.sub (eval_shift_op so rs) rs#r2))) m
  | Pstr r1 r2 sa =>
      exec_store Mint32 (Val.add rs#r2 (eval_shift_op sa rs)) r1 rs m
  | Pstr_a r1 r2 sa =>
      exec_store Many32 (Val.add rs#r2 (eval_shift_op sa rs)) r1 rs m
  | Pstrb r1 r2 sa =>
      exec_store Mint8unsigned (Val.add rs#r2 (eval_shift_op sa rs)) r1 rs m
  | Pstrh r1 r2 sa =>
      exec_store Mint16unsigned (Val.add rs#r2 (eval_shift_op sa rs)) r1 rs m
  | Psdiv =>
      match Val.divs rs#IR0 rs#IR1 with
      | Some v => Next (nextinstr (rs#IR0 <- v
                                     #IR1 <- Vundef #IR2 <- Vundef
                                     #IR3 <- Vundef #IR12 <- Vundef)) m
      | None => Stuck
      end
  | Psbfx r1 r2 lsb sz =>
      Next (nextinstr (rs#r1 <- (Val.sign_ext (Int.unsigned sz) (Val.shru rs#r2 (Vint lsb))))) m
  | Psmull rdl rdh r1 r2 =>
      Next (nextinstr (rs#rdl <- (Val.mul rs#r1 rs#r2)
                         #rdh <- (Val.mulhs rs#r1 rs#r2))) m
  | Psub r1 r2 so =>
      Next (nextinstr_nf (rs#r1 <- (Val.sub rs#r2 (eval_shift_op so rs)))) m
  | Pudiv =>
      match Val.divu rs#IR0 rs#IR1 with
      | Some v => Next (nextinstr (rs#IR0 <- v
                                     #IR1 <- Vundef #IR2 <- Vundef
                                     #IR3 <- Vundef #IR12 <- Vundef)) m
      | None => Stuck
      end
  | Pumull rdl rdh r1 r2 =>
      Next (nextinstr (rs#rdl <- (Val.mul rs#r1 rs#r2)
                         #rdh <- (Val.mulhu rs#r1 rs#r2))) m
  (* Floating-point coprocessor instructions *)
  | Pfcpyd r1 r2 =>
      Next (nextinstr (rs#r1 <- (rs#r2))) m
  | Pfabsd r1 r2 =>
      Next (nextinstr (rs#r1 <- (Val.absf rs#r2))) m
  | Pfnegd r1 r2 =>
      Next (nextinstr (rs#r1 <- (Val.negf rs#r2))) m
  | Pfaddd r1 r2 r3 =>
      Next (nextinstr (rs#r1 <- (Val.addf rs#r2 rs#r3))) m
  | Pfdivd r1 r2 r3 =>
      Next (nextinstr (rs#r1 <- (Val.divf rs#r2 rs#r3))) m
  | Pfmuld r1 r2 r3 =>
      Next (nextinstr (rs#r1 <- (Val.mulf rs#r2 rs#r3))) m
  | Pfsubd r1 r2 r3 =>
      Next (nextinstr (rs#r1 <- (Val.subf rs#r2 rs#r3))) m
  | Pflid r1 f =>
      Next (nextinstr (rs#r1 <- (Vfloat f))) m
  | Pfcmpd r1 r2 =>
      Next (nextinstr (compare_float rs rs#r1 rs#r2)) m
  | Pfcmpzd r1 =>
      Next (nextinstr (compare_float rs rs#r1 (Vfloat Float.zero))) m
  | Pfsitod r1 r2 =>
      Next (nextinstr (rs#r1 <- (Val.maketotal (Val.floatofint rs#r2)))) m
  | Pfuitod r1 r2 =>
      Next (nextinstr (rs#r1 <- (Val.maketotal (Val.floatofintu rs#r2)))) m
  | Pftosizd r1 r2 =>
      Next (nextinstr (rs #FR6 <- Vundef #r1 <- (Val.maketotal (Val.intoffloat rs#r2)))) m
  | Pftouizd r1 r2 =>
      Next (nextinstr (rs #FR6 <- Vundef #r1 <- (Val.maketotal (Val.intuoffloat rs#r2)))) m
  | Pfabss r1 r2 =>
      Next (nextinstr (rs#r1 <- (Val.absfs rs#r2))) m
  | Pfnegs r1 r2 =>
      Next (nextinstr (rs#r1 <- (Val.negfs rs#r2))) m
  | Pfadds r1 r2 r3 =>
      Next (nextinstr (rs#r1 <- (Val.addfs rs#r2 rs#r3))) m
  | Pfdivs r1 r2 r3 =>
      Next (nextinstr (rs#r1 <- (Val.divfs rs#r2 rs#r3))) m
  | Pfmuls r1 r2 r3 =>
      Next (nextinstr (rs#r1 <- (Val.mulfs rs#r2 rs#r3))) m
  | Pfsubs r1 r2 r3 =>
      Next (nextinstr (rs#r1 <- (Val.subfs rs#r2 rs#r3))) m
  | Pflis r1 f =>
      Next (nextinstr (rs#r1 <- (Vsingle f))) m
  | Pfcmps r1 r2 =>
      Next (nextinstr (compare_float32 rs rs#r1 rs#r2)) m
  | Pfcmpzs r1 =>
      Next (nextinstr (compare_float32 rs rs#r1 (Vsingle Float32.zero))) m
  | Pfsitos r1 r2 =>
      Next (nextinstr (rs#r1 <- (Val.maketotal (Val.singleofint rs#r2)))) m
  | Pfuitos r1 r2 =>
      Next (nextinstr (rs#r1 <- (Val.maketotal (Val.singleofintu rs#r2)))) m
  | Pftosizs r1 r2 =>
      Next (nextinstr (rs #FR6 <- Vundef #r1 <- (Val.maketotal (Val.intofsingle rs#r2)))) m
  | Pftouizs r1 r2 =>
      Next (nextinstr (rs #FR6 <- Vundef #r1 <- (Val.maketotal (Val.intuofsingle rs#r2)))) m
  | Pfcvtsd r1 r2 =>
      Next (nextinstr (rs#r1 <- (Val.singleoffloat rs#r2))) m
  | Pfcvtds r1 r2 =>
      Next (nextinstr (rs#r1 <- (Val.floatofsingle rs#r2))) m
  | Pfldd r1 r2 n =>
      exec_load Mfloat64 (Val.add rs#r2 (Vint n)) r1 rs m
  | Pfldd_a r1 r2 n =>
      exec_load Many64 (Val.add rs#r2 (Vint n)) r1 rs m
  | Pflds r1 r2 n =>
      exec_load Mfloat32 (Val.add rs#r2 (Vint n)) r1 rs m
  | Pfstd r1 r2 n =>
      exec_store Mfloat64 (Val.add rs#r2 (Vint n)) r1 rs m
  | Pfstd_a r1 r2 n =>
      exec_store Many64 (Val.add rs#r2 (Vint n)) r1 rs m
  | Pfsts r1 r2 n =>
      exec_store Mfloat32 (Val.add rs#r2 (Vint n)) r1 rs m
  (* Pseudo-instructions *)
  | Pallocframe sz pos =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := (Vptr stk Ptrofs.zero) in
      match Mem.storev Mint32 m1 (Val.offset_ptr sp pos) rs#IR13 with
      | None => Stuck
      | Some m2 => Next (nextinstr (rs #IR12 <- (rs#IR13) #IR13 <- sp)) m2
      end
  | Pfreeframe sz pos =>
      match Mem.loadv Mint32 m (Val.offset_ptr rs#IR13 pos) with
      | None => Stuck
      | Some v =>
          match rs#IR13 with
          | Vptr stk ofs =>
              match Mem.free m stk 0 sz with
              | None => Stuck
              | Some m' => Next (nextinstr (rs#IR13 <- v)) m'
              end
          | _ => Stuck
          end
      end
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Ploadsymbol r1 lbl ofs =>
      Next (nextinstr (rs#r1 <- (Genv.symbol_address ge lbl ofs))) m
  | Pmovite cond r1 ifso ifnot =>
      let v :=
        match eval_testcond cond rs with
        | Some true => eval_shift_op ifso rs
        | Some false => eval_shift_op ifnot rs
        | None => Vundef
        end in
      Next (nextinstr (rs#r1 <- v)) m
  | Pbtbl r tbl =>
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs#IR14 <- Vundef) m
          end
      | _ => Stuck
      end
  | Pcfi_rel_offset ofs =>
      Next (nextinstr rs) m
  | Pbuiltin ef args res => Stuck    (**r treated specially below *)
  (** The following instructions and directives are not generated directly by Asmgen,
      so we do not model them. *)
  | Ppush _
  | Padc _ _ _
  | Pcfi_adjust _
  | Pclz _ _
  | Prev _ _
  | Prev16 _ _
  | Pfsqrt _ _
  | Prsc _ _ _
  | Psbc _ _ _
  | Pnop
  | Padds _ _ _
  | Psubs _ _ _
  | Prsbs _ _ _
  | Pdmb
  | Pdsb
  | Pisb
  | Pbne _
  | Pldr_p _ _ _
  | Pldrb_p _ _ _
  | Pldrh_p _ _ _
  | Pstr_p _ _ _
  | Pstrb_p _ _ _
  | Pstrh_p _ _ _
  | Pfcpy_fs _ _
  | Pfcpy_sf _ _
  | Pfcpy_fii _ _ _
  | Pfcpy_fi _ _
  | Pfcpy_iif _ _ _
  | Pfcpy_if _ _
  | Pconstants _
  | Ploadsymbol_imm _ _ _
  | Pflid_lbl _ _ _
  | Pflis_lbl _ _ _
  | Pflid_imm _ _
  | Pflis_imm _ _
  | Ploadsymbol_lbl _ _ _ _
    =>
    Stuck
  end.

(** Translation of the LTL/Linear/Mach view of machine registers
  to the ARM view.  Note that no LTL register maps to [IR14].
  This register is reserved as temporary, to be used
  by the generated ARM code.  *)

Definition preg_of (r: mreg) : preg :=
  match r with
  | R0 => IR0 | R1 => IR1 | R2 => IR2 | R3 => IR3
  | R4 => IR4 | R5 => IR5 | R6 => IR6 | R7 => IR7
  | R8 => IR8 | R9 => IR9 | R10 => IR10 | R11 => IR11
  | R12 => IR12
  | F0 => FR0 | F1 => FR1 | F2 => FR2 | F3 => FR3
  | F4 => FR4 | F5 => FR5 | F6 => FR6 | F7 => FR7
  | F8 => FR8 | F9 => FR9 | F10 => FR10 | F11 => FR11
  | F12 => FR12 | F13 => FR13 | F14 => FR14 | F15 => FR15
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
    we use ARM registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr (rs (IR IR13)) (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

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
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs SP) m args vargs ->
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
      rs' = (set_pair (loc_external_result (ef_sig ef) ) res (undef_caller_save_regs rs))#PC <- (rs IR14) ->
      step (State rs m) t (State rs' m').

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # IR14 <- Vzero
        # IR13 <- Vzero in
      Genv.init_mem p = Some m0 ->
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vzero ->
      rs#IR0 = Vint r ->
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
(* determ *)
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
(* trace length *)
  red; intros; inv H; simpl.
  omega.
  inv H3; eapply external_call_trace_length; eauto.
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
  | IR IR14 => false
  | IR _ => true
  | FR _ => true
  | CR _ => false
  | PC => false
  end.

