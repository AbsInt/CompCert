(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

(** Abstract syntax and semantics for RISC-V assembly language. *)

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

(** Integer registers.  X0 is treated specially because it always reads 
  as zero and is never used as a destination of an instruction. *)

Inductive ireg: Type :=
  | X1:  ireg | X2:  ireg | X3:  ireg | X4:  ireg | X5:  ireg
  | X6:  ireg | X7:  ireg | X8:  ireg | X9:  ireg | X10: ireg
  | X11: ireg | X12: ireg | X13: ireg | X14: ireg | X15: ireg
  | X16: ireg | X17: ireg | X18: ireg | X19: ireg | X20: ireg
  | X21: ireg | X22: ireg | X23: ireg | X24: ireg | X25: ireg
  | X26: ireg | X27: ireg | X28: ireg | X29: ireg | X30: ireg
  | X31: ireg.

Inductive ireg0: Type :=
  | X0: ireg0 | X: ireg -> ireg0.

Coercion X: ireg >-> ireg0.

(** Floating-point registers *)

Inductive freg: Type :=
  | F0: freg  | F1: freg  | F2: freg  | F3: freg
  | F4: freg  | F5: freg  | F6: freg  | F7: freg
  | F8: freg  | F9: freg  | F10: freg | F11: freg
  | F12: freg | F13: freg | F14: freg | F15: freg
  | F16: freg | F17: freg | F18: freg | F19: freg
  | F20: freg | F21: freg | F22: freg | F23: freg
  | F24: freg | F25: freg | F26: freg | F27: freg
  | F28: freg | F29: freg | F30: freg | F31: freg.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma ireg0_eq: forall (x y: ireg0), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. Defined.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.
  
(** We model the following registers of the RISC-V architecture. *)

Inductive preg: Type :=
  | IR: ireg -> preg                    (**r integer registers *)
  | FR: freg -> preg                    (**r double-precision float registers *)
  | PC: preg.                           (**r program counter *)

Coercion IR: ireg >-> preg.
Coercion FR: freg >-> preg.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. apply freg_eq. Defined.

Module PregEq.
  Definition t  := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

(** Conventional names for stack pointer ([SP]) and return address ([RA]). *)

Notation "'SP'" := X2 (only parsing) : asm.
Notation "'RA'" := X1 (only parsing) : asm.

(** Offsets for load and store instructions.  An offset is either an
  immediate integer or the low part of a symbol. *)

Inductive offset : Type :=
  | Ofsimm (ofs: ptrofs)
  | Ofslow (id: ident) (ofs: ptrofs).

(** The RISC-V instruction set is composed of several subsets.  We model
  the "32I" (32-bit integers), "64I" (64-bit integers),
  "M" (multiplication and division), 
  "F" (single-precision floating-point)
  and "D" (double-precision floating-point) subsets.  

  For 32- and 64-bit integer arithmetic, the RISC-V instruction set comprises
  generic integer operations such as ADD that operate over the full width
  of an integer register (either 32 or 64 bit), plus specific instructions
  such as ADDW that normalize their results to signed 32-bit integers.
  Other instructions such as AND work equally well over 32- and 64-bit
  integers, with the convention that 32-bit integers are represented
  sign-extended in 64-bit registers.

  This clever design is challenging to formalize in the CompCert value
  model.  As a first step, we follow a more traditional approach,
  also used in the x86 port, whereas we have two sets of (pseudo-)
  instructions, one for 32-bit integer arithmetic, with suffix W,
  the other for 64-bit integer arithmetic, with suffix L.  The mapping
  to actual instructions is done when printing assembly code, as follows:
  - In 32-bit mode:
    ADDW becomes ADD, ADDL is an error, ANDW becomes AND, ANDL is an error.
  - In 64-bit mode:
    ADDW becomes ADDW, ADDL becomes ADD, ANDW and ANDL both become AND.
*)

Definition label := positive.

(** A note on immediates: there are various constraints on immediate
  operands to RISC-V instructions.  We do not attempt to capture these
  restrictions in the abstract syntax nor in the semantics.  The
  assembler will emit an error if immediate operands exceed the
  representable range.  Of course, our RISC-V generator (file
  [Asmgen]) is careful to respect this range. *)

Inductive instruction : Type :=
  | Pmv     (rd: ireg) (rs: ireg)                    (**r integer move *)

(** 32-bit integer register-immediate instructions *)
  | Paddiw  (rd: ireg) (rs: ireg0) (imm: int)        (**r add immediate *)
  | Psltiw  (rd: ireg) (rs: ireg0) (imm: int)        (**r set-less-than immediate *)
  | Psltiuw (rd: ireg) (rs: ireg0) (imm: int)        (**r set-less-than unsigned immediate *)
  | Pandiw  (rd: ireg) (rs: ireg0) (imm: int)        (**r and immediate *)
  | Poriw   (rd: ireg) (rs: ireg0) (imm: int)        (**r or immediate *)
  | Pxoriw  (rd: ireg) (rs: ireg0) (imm: int)        (**r xor immediate *)
  | Pslliw  (rd: ireg) (rs: ireg0) (imm: int)        (**r shift-left-logical immediate *)
  | Psrliw  (rd: ireg) (rs: ireg0) (imm: int)        (**r shift-right-logical immediate *)
  | Psraiw  (rd: ireg) (rs: ireg0) (imm: int)        (**r shift-right-arith immediate *)
  | Pluiw   (rd: ireg)             (imm: int)        (**r load upper-immediate *)
(** 32-bit integer register-register instructions *)
  | Paddw   (rd: ireg) (rs1 rs2: ireg0)              (**r integer addition *)
  | Psubw   (rd: ireg) (rs1 rs2: ireg0)              (**r integer subtraction *)

  | Pmulw   (rd: ireg) (rs1 rs2: ireg0)              (**r integer multiply low *)
  | Pmulhw  (rd: ireg) (rs1 rs2: ireg0)              (**r integer multiply high signed *)
  | Pmulhuw (rd: ireg) (rs1 rs2: ireg0)              (**r integer multiply high unsigned *)
  | Pdivw   (rd: ireg) (rs1 rs2: ireg0)              (**r integer division *)
  | Pdivuw  (rd: ireg) (rs1 rs2: ireg0)              (**r unsigned integer division *)
  | Premw   (rd: ireg) (rs1 rs2: ireg0)              (**r integer remainder *)
  | Premuw  (rd: ireg) (rs1 rs2: ireg0)              (**r unsigned integer remainder *)
  | Psltw   (rd: ireg) (rs1 rs2: ireg0)              (**r set-less-than *)
  | Psltuw  (rd: ireg) (rs1 rs2: ireg0)              (**r set-less-than unsigned *)
  | Pseqw   (rd: ireg) (rs1 rs2: ireg0)              (**r [rd <- rs1 == rs2] (pseudo) *)
  | Psnew   (rd: ireg) (rs1 rs2: ireg0)              (**r [rd <- rs1 != rs2] (pseudo) *)
  | Pandw   (rd: ireg) (rs1 rs2: ireg0)              (**r bitwise and *)
  | Porw    (rd: ireg) (rs1 rs2: ireg0)              (**r bitwise or *)
  | Pxorw   (rd: ireg) (rs1 rs2: ireg0)              (**r bitwise xor *)
  | Psllw   (rd: ireg) (rs1 rs2: ireg0)              (**r shift-left-logical *)
  | Psrlw   (rd: ireg) (rs1 rs2: ireg0)              (**r shift-right-logical *)
  | Psraw   (rd: ireg) (rs1 rs2: ireg0)              (**r shift-right-arith *)

(** 64-bit integer register-immediate instructions *)
  | Paddil  (rd: ireg) (rs: ireg0) (imm: int64)      (**r add immediate *)
  | Psltil  (rd: ireg) (rs: ireg0) (imm: int64)      (**r set-less-than immediate *)
  | Psltiul (rd: ireg) (rs: ireg0) (imm: int64)      (**r set-less-than unsigned immediate *)
  | Pandil  (rd: ireg) (rs: ireg0) (imm: int64)      (**r and immediate *)
  | Poril   (rd: ireg) (rs: ireg0) (imm: int64)      (**r or immediate *)
  | Pxoril  (rd: ireg) (rs: ireg0) (imm: int64)      (**r xor immediate *)
  | Psllil  (rd: ireg) (rs: ireg0) (imm: int)        (**r shift-left-logical immediate *)
  | Psrlil  (rd: ireg) (rs: ireg0) (imm: int)        (**r shift-right-logical immediate *)
  | Psrail  (rd: ireg) (rs: ireg0) (imm: int)        (**r shift-right-arith immediate *)
  | Pluil   (rd: ireg)             (imm: int64)      (**r load upper-immediate *)
(** 64-bit integer register-register instructions *)
  | Paddl   (rd: ireg) (rs1 rs2: ireg0)              (**r integer addition *)
  | Psubl   (rd: ireg) (rs1 rs2: ireg0)              (**r integer subtraction *)

  | Pmull   (rd: ireg) (rs1 rs2: ireg0)              (**r integer multiply low *)
  | Pmulhl  (rd: ireg) (rs1 rs2: ireg0)              (**r integer multiply high signed *)
  | Pmulhul (rd: ireg) (rs1 rs2: ireg0)              (**r integer multiply high unsigned *)
  | Pdivl   (rd: ireg) (rs1 rs2: ireg0)              (**r integer division *)
  | Pdivul  (rd: ireg) (rs1 rs2: ireg0)              (**r unsigned integer division *)
  | Preml   (rd: ireg) (rs1 rs2: ireg0)              (**r integer remainder *)
  | Premul  (rd: ireg) (rs1 rs2: ireg0)              (**r unsigned integer remainder *)
  | Psltl   (rd: ireg) (rs1 rs2: ireg0)              (**r set-less-than *)
  | Psltul  (rd: ireg) (rs1 rs2: ireg0)              (**r set-less-than unsigned *)
  | Pseql   (rd: ireg) (rs1 rs2: ireg0)              (**r [rd <- rs1 == rs2] (pseudo) *)
  | Psnel   (rd: ireg) (rs1 rs2: ireg0)              (**r [rd <- rs1 != rs2] (pseudo) *)
  | Pandl   (rd: ireg) (rs1 rs2: ireg0)              (**r bitwise and *)
  | Porl    (rd: ireg) (rs1 rs2: ireg0)              (**r bitwise or *)
  | Pxorl   (rd: ireg) (rs1 rs2: ireg0)              (**r bitwise xor *)
  | Pslll   (rd: ireg) (rs1 rs2: ireg0)              (**r shift-left-logical *)
  | Psrll   (rd: ireg) (rs1 rs2: ireg0)              (**r shift-right-logical *)
  | Psral   (rd: ireg) (rs1 rs2: ireg0)              (**r shift-right-arith *)

  | Pcvtl2w (rd: ireg) (rs: ireg0)                   (**r int64->int32 (pseudo) *)
  | Pcvtw2l (r: ireg)                                (**r int32 signed -> int64 (pseudo) *)

  (* Unconditional jumps.  Links are always to X1/RA. *)
  | Pj_l    (l: label)                              (**r jump to label *)
  | Pj_s    (symb: ident) (sg: signature)           (**r jump to symbol *)
  | Pj_r    (r: ireg)     (sg: signature)           (**r jump register *)
  | Pjal_s  (symb: ident) (sg: signature)           (**r jump-and-link symbol *)
  | Pjal_r  (r: ireg)     (sg: signature)           (**r jump-and-link register *)

  (* Conditional branches, 32-bit comparisons *)
  | Pbeqw   (rs1 rs2: ireg0) (l: label)             (**r branch-if-equal *)
  | Pbnew   (rs1 rs2: ireg0) (l: label)             (**r branch-if-not-equal signed *)
  | Pbltw   (rs1 rs2: ireg0) (l: label)             (**r branch-if-less signed *)
  | Pbltuw  (rs1 rs2: ireg0) (l: label)             (**r branch-if-less unsigned *)
  | Pbgew   (rs1 rs2: ireg0) (l: label)             (**r branch-if-greater-or-equal signed *)
  | Pbgeuw  (rs1 rs2: ireg0) (l: label)             (**r branch-if-greater-or-equal unsigned *)

  (* Conditional branches, 64-bit comparisons *)
  | Pbeql   (rs1 rs2: ireg0) (l: label)             (**r branch-if-equal *)
  | Pbnel   (rs1 rs2: ireg0) (l: label)             (**r branch-if-not-equal signed *)
  | Pbltl   (rs1 rs2: ireg0) (l: label)             (**r branch-if-less signed *)
  | Pbltul  (rs1 rs2: ireg0) (l: label)             (**r branch-if-less unsigned *)
  | Pbgel   (rs1 rs2: ireg0) (l: label)             (**r branch-if-greater-or-equal signed *)
  | Pbgeul  (rs1 rs2: ireg0) (l: label)             (**r branch-if-greater-or-equal unsigned *)

  (* Loads and stores *)
  | Plb     (rd: ireg) (ra: ireg) (ofs: offset)     (**r load signed int8 *)
  | Plbu    (rd: ireg) (ra: ireg) (ofs: offset)     (**r load unsigned int8 *)
  | Plh     (rd: ireg) (ra: ireg) (ofs: offset)     (**r load signed int16 *)
  | Plhu    (rd: ireg) (ra: ireg) (ofs: offset)     (**r load unsigned int16 *)
  | Plw     (rd: ireg) (ra: ireg) (ofs: offset)     (**r load int32 *)
  | Plw_a   (rd: ireg) (ra: ireg) (ofs: offset)     (**r load any32 *)
  | Pld     (rd: ireg) (ra: ireg) (ofs: offset)     (**r load int64 *)
  | Pld_a   (rd: ireg) (ra: ireg) (ofs: offset)     (**r load any64 *)

  | Psb     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int8 *)
  | Psh     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int16 *)
  | Psw     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int32 *)
  | Psw_a   (rs: ireg) (ra: ireg) (ofs: offset)     (**r store any32 *)
  | Psd     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int64 *)
  | Psd_a   (rs: ireg) (ra: ireg) (ofs: offset)     (**r store any64 *)

  (* Synchronization *)
  | Pfence                                          (**r fence *)

  (* floating point register move *)
  | Pfmv     (rd: freg) (rs: freg)                  (**r move *)
  | Pfmvxs   (rd: ireg) (rs: freg)                  (**r move FP single to integer register *)
  | Pfmvxd   (rd: ireg) (rs: freg)                  (**r move FP double to integer register *)

  (* 32-bit (single-precision) floating point *)
  | Pfls     (rd: freg) (ra: ireg) (ofs: offset)    (**r load float *)
  | Pfss     (rs: freg) (ra: ireg) (ofs: offset)    (**r store float *)

  | Pfnegs   (rd: freg) (rs: freg)                  (**r negation *)
  | Pfabss   (rd: freg) (rs: freg)                  (**r absolute value *)

  | Pfadds   (rd: freg) (rs1 rs2: freg)             (**r addition *)
  | Pfsubs   (rd: freg) (rs1 rs2: freg)             (**r subtraction *)
  | Pfmuls   (rd: freg) (rs1 rs2: freg)             (**r multiplication *)
  | Pfdivs   (rd: freg) (rs1 rs2: freg)             (**r division *)
  | Pfmins   (rd: freg) (rs1 rs2: freg)             (**r minimum *)
  | Pfmaxs   (rd: freg) (rs1 rs2: freg)             (**r maximum *)

  | Pfeqs    (rd: ireg) (rs1 rs2: freg)             (**r compare equal *)
  | Pflts    (rd: ireg) (rs1 rs2: freg)             (**r compare less-than *)
  | Pfles    (rd: ireg) (rs1 rs2: freg)             (**r compare less-than/equal *)

  | Pfsqrts  (rd: freg) (rs: freg)                  (**r square-root *)

  | Pfmadds  (rd: freg) (rs1 rs2 rs3: freg)         (**r fused multiply-add *)
  | Pfmsubs  (rd: freg) (rs1 rs2 rs3: freg)         (**r fused multiply-sub *)
  | Pfnmadds (rd: freg) (rs1 rs2 rs3: freg)         (**r fused negated multiply-add *)
  | Pfnmsubs (rd: freg) (rs1 rs2 rs3: freg)         (**r fused negated multiply-sub *)

  | Pfcvtws  (rd: ireg) (rs: freg)                  (**r float32 -> int32 conversion *)
  | Pfcvtwus (rd: ireg) (rs: freg)                  (**r float32 -> unsigned int32 conversion *)
  | Pfcvtsw  (rd: freg) (rs: ireg0)                 (**r int32 -> float32 conversion *)
  | Pfcvtswu (rd: freg) (rs: ireg0)                 (**r unsigned int32 -> float32 conversion *)

  | Pfcvtls  (rd: ireg) (rs: freg)                  (**r float32 -> int64 conversion *)
  | Pfcvtlus (rd: ireg) (rs: freg)                  (**r float32 -> unsigned int64 conversion *)
  | Pfcvtsl  (rd: freg) (rs: ireg0)                 (**r int64 -> float32 conversion *)
  | Pfcvtslu (rd: freg) (rs: ireg0)                 (**r unsigned int 64-> float32 conversion *)

  (* 64-bit (double-precision) floating point *)
  | Pfld     (rd: freg) (ra: ireg) (ofs: offset)    (**r load 64-bit float *)
  | Pfld_a   (rd: freg) (ra: ireg) (ofs: offset)    (**r load any64 *)
  | Pfsd     (rd: freg) (ra: ireg) (ofs: offset)    (**r store 64-bit float *)
  | Pfsd_a   (rd: freg) (ra: ireg) (ofs: offset)    (**r store any64 *)

  | Pfnegd   (rd: freg) (rs: freg)                  (**r negation *)
  | Pfabsd   (rd: freg) (rs: freg)                  (**r absolute value *)

  | Pfaddd   (rd: freg) (rs1 rs2: freg)             (**r addition *)
  | Pfsubd   (rd: freg) (rs1 rs2: freg)             (**r subtraction *)
  | Pfmuld   (rd: freg) (rs1 rs2: freg)             (**r multiplication *)
  | Pfdivd   (rd: freg) (rs1 rs2: freg)             (**r division *)
  | Pfmind   (rd: freg) (rs1 rs2: freg)             (**r minimum *)
  | Pfmaxd   (rd: freg) (rs1 rs2: freg)             (**r maximum *)

  | Pfeqd    (rd: ireg) (rs1 rs2: freg)             (**r compare equal *)
  | Pfltd    (rd: ireg) (rs1 rs2: freg)             (**r compare less-than *)
  | Pfled    (rd: ireg) (rs1 rs2: freg)             (**r compare less-than/equal *)

  | Pfsqrtd  (rd: freg) (rs: freg)                  (**r square-root *)

  | Pfmaddd  (rd: freg) (rs1 rs2 rs3: freg)         (**r fused multiply-add *)
  | Pfmsubd  (rd: freg) (rs1 rs2 rs3: freg)         (**r fused multiply-sub *)
  | Pfnmaddd (rd: freg) (rs1 rs2 rs3: freg)         (**r fused negated multiply-add *)
  | Pfnmsubd (rd: freg) (rs1 rs2 rs3: freg)         (**r fused negated multiply-sub *)

  | Pfcvtwd  (rd: ireg) (rs: freg)                  (**r float -> int32 conversion *)
  | Pfcvtwud (rd: ireg) (rs: freg)                  (**r float -> unsigned int32 conversion *)
  | Pfcvtdw  (rd: freg) (rs: ireg0)                 (**r int32 -> float conversion *)
  | Pfcvtdwu (rd: freg) (rs: ireg0)                 (**r unsigned int32 -> float conversion *)

  | Pfcvtld  (rd: ireg) (rs: freg)                  (**r float -> int64 conversion *)
  | Pfcvtlud (rd: ireg) (rs: freg)                  (**r float -> unsigned int64 conversion *)
  | Pfcvtdl  (rd: freg) (rs: ireg0)                 (**r int64 -> float conversion *)
  | Pfcvtdlu (rd: freg) (rs: ireg0)                 (**r unsigned int64 -> float conversion *)

  | Pfcvtds  (rd: freg) (rs: freg)                  (**r float32 -> float   *)
  | Pfcvtsd  (rd: freg) (rs: freg)                  (**r float   -> float32 *)

  (* Pseudo-instructions *)
  | Pallocframe (sz: Z) (pos: ptrofs)               (**r allocate new stack frame *)
  | Pfreeframe  (sz: Z) (pos: ptrofs)               (**r deallocate stack frame and restore previous frame *)
  | Plabel  (lbl: label)                            (**r define a code label *)
  | Ploadsymbol (rd: ireg) (id: ident) (ofs: ptrofs) (**r load the address of a symbol *)
  | Ploadsymbol_high (rd: ireg) (id: ident) (ofs: ptrofs) (**r load the high part of the address of a symbol *)
  | Ploadli (rd: ireg) (i: int64)                   (**r load an immediate int64 *)
  | Ploadfi (rd: freg) (f: float)                   (**r load an immediate float *)
  | Ploadsi (rd: freg) (f: float32)                 (**r load an immediate single *)
  | Pbtbl   (r: ireg)  (tbl: list label)            (**r N-way branch through a jump table *)
  | Pbuiltin: external_function -> list (builtin_arg preg)
              -> builtin_res preg -> instruction    (**r built-in function (pseudo) *)
  | Pnop : instruction.                             (**r nop instruction *)


(** The pseudo-instructions are the following:

- [Plabel]: define a code label at the current program point.

- [Ploadsymbol]: load the address of a symbol in an integer register.
  Expands to the [la] assembler pseudo-instruction, which does the right
  thing even if we are in PIC mode.

- [Ploadli rd ival]: load an immediate 64-bit integer into an integer
  register rd.  Expands to a load from an address in the constant data section,
  using the integer register x31 as temporary:
<<
        lui x31, %hi(lbl)
        ld rd, %lo(lbl)(x31)
lbl:
        .quad ival
>>

- [Ploadfi rd fval]: similar to [Ploadli] but loads a double FP constant fval
  into a float register rd.

- [Ploadsi rd fval]: similar to [Ploadli] but loads a single FP constant fval
  into a float register rd.

- [Pallocframe sz pos]: in the formal semantics, this
  pseudo-instruction allocates a memory block with bounds [0] and
  [sz], stores the value of the stack pointer at offset [pos] in this
  block, and sets the stack pointer to the address of the bottom of
  this block.
  In the printed ASM assembly code, this allocation is:
<<
        mv      x30, sp
        sub     sp,  sp, #sz
        sw      x30, #pos(sp)
>>
  This cannot be expressed in our memory model, which does not reflect
  the fact that stack frames are adjacent and allocated/freed
  following a stack discipline.

- [Pfreeframe sz pos]: in the formal semantics, this pseudo-instruction
  reads the word at [pos] of the block pointed by the stack pointer,
  frees this block, and sets the stack pointer to the value read.
  In the printed ASM assembly code, this freeing is just an increment of [sp]:
<<
        add     sp,  sp, #sz
>>
  Again, our memory model cannot comprehend that this operation
  frees (logically) the current stack frame.

- [Pbtbl reg table]: this is a N-way branch, implemented via a jump table
  as follows:
<<
        la      x31, table
        add     x31, x31, reg
        jr      x31
table:  .long   table[0], table[1], ...
>>
  Note that [reg] contains 4 times the index of the desired table entry.

- [Pseq rd rs1 rs2]: since unsigned comparisons have particular
  semantics for pointers, we cannot encode equality directly using
  xor/sub etc, which have only integer semantics.
<<
        xor     rd, rs1, rs2
        sltiu   rd, rd, 1
>>
  The [xor] is omitted if one of [rs1] and [rs2] is [x0].

- [Psne rd rs1 rs2]: similarly for unsigned inequality.
<<
        xor     rd, rs1, rs2
        sltu    rd, x0, rd
>>
*)

Definition code := list instruction.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain
  the convention that integer registers are mapped to values of
  type [Tint] or [Tlong] (in 64 bit mode),
  and float registers to values of type [Tsingle] or [Tfloat]. *)

Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef unit.

Definition get0w (rs: regset) (r: ireg0) : val :=
  match r with
  | X0 => Vint Int.zero
  | X r => rs r
  end.

Definition get0l (rs: regset) (r: ireg0) : val :=
  match r with
  | X0 => Vlong Int64.zero
  | X r => rs r
  end.

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a ## b" := (get0w a b) (at level 1) : asm.
Notation "a ### b" := (get0l a b) (at level 1) : asm.
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm.

Open Scope asm.

(** Undefining some registers *)

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.

(** Assigning a register pair *)

Definition set_pair (p: rpair preg) (v: val) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

(** Assigning multiple registers *)

Fixpoint set_regs (rl: list preg) (vl: list val) (rs: regset) : regset :=
  match rl, vl with
  | r1 :: rl', v1 :: vl' => set_regs rl' vl' (rs#r1 <- v1)
  | _, _ => rs
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
  case (peq lbl lbl0); intro; congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

Variable ge: genv.

(** The two functions below axiomatize how the linker processes
  symbolic references [symbol + offset)] and splits their
  actual values into a 20-bit high part [%hi(symbol + offset)] and 
  a 12-bit low part [%lo(symbol + offset)]. *)

Parameter low_half: genv -> ident -> ptrofs -> ptrofs.
Parameter high_half: genv -> ident -> ptrofs -> val.

(** The fundamental property of these operations is that, when applied
  to the address of a symbol, their results can be recombined by
  addition, rebuilding the original address. *)

Axiom low_high_half:
  forall id ofs,
  Val.offset_ptr (high_half ge id ofs) (low_half ge id ofs) = Genv.symbol_address ge id ofs.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome: Type :=
  | Next:  regset -> mem -> outcome
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
      | _          => Stuck
      end
  end.

(** Auxiliaries for memory accesses *)

Definition eval_offset (ofs: offset) : ptrofs :=
  match ofs with
  | Ofsimm n => n
  | Ofslow id delta => low_half ge id delta
  end.

Definition exec_load (chunk: memory_chunk) (rs: regset) (m: mem)
                     (d: preg) (a: ireg) (ofs: offset) :=
  match Mem.loadv chunk m (Val.offset_ptr (rs a) (eval_offset ofs)) with
  | None => Stuck
  | Some v => Next (nextinstr (rs#d <- v)) m
  end.

Definition exec_store (chunk: memory_chunk) (rs: regset) (m: mem)
                      (s: preg) (a: ireg) (ofs: offset) :=
  match Mem.storev chunk m (Val.offset_ptr (rs a) (eval_offset ofs)) (rs s) with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

(** Evaluating a branch *)

Definition eval_branch (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) : outcome :=
  match res with
    | Some true  => goto_label f l rs m
    | Some false => Next (nextinstr rs) m
    | None => Stuck
  end.

(** Execution of a single instruction [i] in initial state [rs] and
    [m].  Return updated state.  For instructions that correspond to
    actual RISC-V instructions, the cases are straightforward
    transliterations of the informal descriptions given in the RISC-V
    user-mode specification.  For pseudo-instructions, refer to the
    informal descriptions given above.

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the RISC-V code
    we generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction. *)

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  | Pmv d s =>
      Next (nextinstr (rs#d <- (rs#s))) m

(** 32-bit integer register-immediate instructions *)
  | Paddiw d s i =>
      Next (nextinstr (rs#d <- (Val.add rs##s (Vint i)))) m
  | Psltiw d s i =>
      Next (nextinstr (rs#d <- (Val.cmp Clt rs##s (Vint i)))) m
  | Psltiuw d s i =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs##s (Vint i)))) m
  | Pandiw d s i =>
      Next (nextinstr (rs#d <- (Val.and rs##s (Vint i)))) m
  | Poriw d s i =>
      Next (nextinstr (rs#d <- (Val.or rs##s (Vint i)))) m
  | Pxoriw d s i =>
      Next (nextinstr (rs#d <- (Val.xor rs##s (Vint i)))) m
  | Pslliw d s i =>
      Next (nextinstr (rs#d <- (Val.shl rs##s (Vint i)))) m
  | Psrliw d s i =>
      Next (nextinstr (rs#d <- (Val.shru rs##s (Vint i)))) m
  | Psraiw d s i =>
      Next (nextinstr (rs#d <- (Val.shr rs##s (Vint i)))) m
  | Pluiw d i =>
      Next (nextinstr (rs#d <- (Vint (Int.shl i (Int.repr 12))))) m

(** 32-bit integer register-register instructions *)
  | Paddw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.add rs##s1 rs##s2))) m
  | Psubw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.sub rs##s1 rs##s2))) m
  | Pmulw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mul rs##s1 rs##s2))) m
  | Pmulhw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulhs rs##s1 rs##s2))) m
  | Pmulhuw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulhu rs##s1 rs##s2))) m
  | Pdivw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divs rs##s1 rs##s2)))) m
  | Pdivuw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divu rs##s1 rs##s2)))) m
  | Premw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.mods rs##s1 rs##s2)))) m
  | Premuw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.modu rs##s1 rs##s2)))) m
  | Psltw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmp Clt rs##s1 rs##s2))) m
  | Psltuw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs##s1 rs##s2))) m
  | Pseqw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Ceq rs##s1 rs##s2))) m
  | Psnew d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Cne rs##s1 rs##s2))) m
  | Pandw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.and rs##s1 rs##s2))) m
  | Porw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.or rs##s1 rs##s2))) m
  | Pxorw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.xor rs##s1 rs##s2))) m
  | Psllw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shl rs##s1 rs##s2))) m
  | Psrlw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shru rs##s1 rs##s2))) m
  | Psraw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shr rs##s1 rs##s2))) m

(** 64-bit integer register-immediate instructions *)
  | Paddil d s i =>
      Next (nextinstr (rs#d <- (Val.addl rs###s (Vlong i)))) m
  | Psltil d s i =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmpl Clt rs###s (Vlong i))))) m
  | Psltiul d s i =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt rs###s (Vlong i))))) m
  | Pandil d s i =>
      Next (nextinstr (rs#d <- (Val.andl rs###s (Vlong i)))) m
  | Poril d s i =>
      Next (nextinstr (rs#d <- (Val.orl rs###s (Vlong i)))) m
  | Pxoril d s i =>
      Next (nextinstr (rs#d <- (Val.xorl rs###s (Vlong i)))) m
  | Psllil d s i =>
      Next (nextinstr (rs#d <- (Val.shll rs###s (Vint i)))) m
  | Psrlil d s i =>
      Next (nextinstr (rs#d <- (Val.shrlu rs###s (Vint i)))) m
  | Psrail d s i =>
      Next (nextinstr (rs#d <- (Val.shrl rs###s (Vint i)))) m
  | Pluil d i =>
      Next (nextinstr (rs#d <- (Vlong (Int64.sign_ext 32 (Int64.shl i (Int64.repr 12)))))) m

(** 64-bit integer register-register instructions *)
  | Paddl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.addl rs###s1 rs###s2))) m
  | Psubl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.subl rs###s1 rs###s2))) m
  | Pmull d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mull rs###s1 rs###s2))) m
  | Pmulhl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mullhs rs###s1 rs###s2))) m
  | Pmulhul d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mullhu rs###s1 rs###s2))) m
  | Pdivl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divls rs###s1 rs###s2)))) m
  | Pdivul d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divlu rs###s1 rs###s2)))) m
  | Preml d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.modls rs###s1 rs###s2)))) m
  | Premul d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.modlu rs###s1 rs###s2)))) m
  | Psltl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmpl Clt rs###s1 rs###s2)))) m
  | Psltul d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt rs###s1 rs###s2)))) m
  | Pseql d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Ceq rs###s1 rs###s2)))) m
  | Psnel d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Cne rs###s1 rs###s2)))) m
  | Pandl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.andl rs###s1 rs###s2))) m
  | Porl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.orl rs###s1 rs###s2))) m
  | Pxorl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.xorl rs###s1 rs###s2))) m
  | Pslll d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shll rs###s1 rs###s2))) m
  | Psrll d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shrlu rs###s1 rs###s2))) m
  | Psral d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shrl rs###s1 rs###s2))) m

  | Pcvtl2w d s =>
      Next (nextinstr (rs#d <- (Val.loword rs##s))) m
  | Pcvtw2l r =>
      Next (nextinstr (rs#r <- (Val.longofint rs#r))) m

(** Unconditional jumps.  Links are always to X1/RA. *)
  | Pj_l l =>
      goto_label f l rs m
  | Pj_s s sg =>
      Next (rs#PC <- (Genv.symbol_address ge s Ptrofs.zero)) m
  | Pj_r r sg =>
      Next (rs#PC <- (rs#r)) m
  | Pjal_s s sg =>
      Next (rs#PC <- (Genv.symbol_address ge s Ptrofs.zero)
              #RA <- (Val.offset_ptr rs#PC Ptrofs.one)
           ) m
  | Pjal_r r sg =>
      Next (rs#PC <- (rs#r)
              #RA <- (Val.offset_ptr rs#PC Ptrofs.one)
           ) m
(** Conditional branches, 32-bit comparisons *)
  | Pbeqw s1 s2 l =>
      eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Ceq rs##s1 rs##s2)
  | Pbnew s1 s2 l =>
      eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Cne rs##s1 rs##s2)
  | Pbltw s1 s2 l =>
      eval_branch f l rs m (Val.cmp_bool Clt rs##s1 rs##s2)
  | Pbltuw s1 s2 l =>
      eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Clt rs##s1 rs##s2)
  | Pbgew s1 s2 l =>
      eval_branch f l rs m (Val.cmp_bool Cge rs##s1 rs##s2)
  | Pbgeuw s1 s2 l =>
      eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Cge rs##s1 rs##s2)

(** Conditional branches, 64-bit comparisons *)
  | Pbeql s1 s2 l =>
      eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Ceq rs###s1 rs###s2)
  | Pbnel s1 s2 l =>
      eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Cne rs###s1 rs###s2)
  | Pbltl s1 s2 l =>
      eval_branch f l rs m (Val.cmpl_bool Clt rs###s1 rs###s2)
  | Pbltul s1 s2 l =>
      eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Clt rs###s1 rs###s2)
  | Pbgel s1 s2 l =>
      eval_branch f l rs m (Val.cmpl_bool Cge rs###s1 rs###s2)
  | Pbgeul s1 s2 l =>
      eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Cge rs###s1 rs###s2)

(** Loads and stores *)
  | Plb d a ofs =>
      exec_load Mint8signed rs m d a ofs
  | Plbu d a ofs =>
      exec_load Mint8unsigned rs m d a ofs
  | Plh d a ofs =>
      exec_load Mint16signed rs m d a ofs
  | Plhu d a ofs =>
      exec_load Mint16unsigned rs m d a ofs
  | Plw d a ofs =>
      exec_load Mint32 rs m d a ofs
  | Plw_a d a ofs =>
      exec_load Many32 rs m d a ofs
  | Pld d a ofs =>
      exec_load Mint64 rs m d a ofs
  | Pld_a d a ofs =>
      exec_load Many64 rs m d a ofs
  | Psb s a ofs =>
      exec_store Mint8unsigned rs m s a ofs
  | Psh s a ofs =>
      exec_store Mint16unsigned rs m s a ofs
  | Psw s a ofs =>
      exec_store Mint32 rs m s a ofs
  | Psw_a s a ofs =>
      exec_store Many32 rs m s a ofs
  | Psd s a ofs =>
      exec_store Mint64 rs m s a ofs
  | Psd_a s a ofs =>
      exec_store Many64 rs m s a ofs

(** Floating point register move *)
  | Pfmv d s =>
      Next (nextinstr (rs#d <- (rs#s))) m

(** 32-bit (single-precision) floating point *)
  | Pfls d a ofs =>
      exec_load Mfloat32 rs m d a ofs
  | Pfss s a ofs =>
      exec_store Mfloat32 rs m s a ofs

  | Pfnegs d s =>
      Next (nextinstr (rs#d <- (Val.negfs rs#s))) m
  | Pfabss d s =>
      Next (nextinstr (rs#d <- (Val.absfs rs#s))) m

  | Pfadds d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.addfs rs#s1 rs#s2))) m
  | Pfsubs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.subfs rs#s1 rs#s2))) m
  | Pfmuls d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulfs rs#s1 rs#s2))) m
  | Pfdivs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.divfs rs#s1 rs#s2))) m
  | Pfeqs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Ceq rs#s1 rs#s2))) m
  | Pflts d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Clt rs#s1 rs#s2))) m
  | Pfles d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Cle rs#s1 rs#s2))) m

  | Pfcvtws d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intofsingle rs#s)))) m
  | Pfcvtwus d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intuofsingle rs#s)))) m
  | Pfcvtsw d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleofint rs##s)))) m
  | Pfcvtswu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleofintu rs##s)))) m

  | Pfcvtls d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.longofsingle rs#s)))) m
  | Pfcvtlus d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.longuofsingle rs#s)))) m
  | Pfcvtsl d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleoflong rs###s)))) m
  | Pfcvtslu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleoflongu rs###s)))) m

(** 64-bit (double-precision) floating point *)
  | Pfld d a ofs =>
      exec_load Mfloat64 rs m d a ofs
  | Pfld_a d a ofs =>
      exec_load Many64 rs m d a ofs
  | Pfsd s a ofs =>
      exec_store Mfloat64 rs m s a ofs
  | Pfsd_a s a ofs =>
      exec_store Many64 rs m s a ofs

  | Pfnegd d s =>
      Next (nextinstr (rs#d <- (Val.negf rs#s))) m
  | Pfabsd d s =>
      Next (nextinstr (rs#d <- (Val.absf rs#s))) m

  | Pfaddd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.addf rs#s1 rs#s2))) m
  | Pfsubd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.subf rs#s1 rs#s2))) m
  | Pfmuld d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulf rs#s1 rs#s2))) m
  | Pfdivd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.divf rs#s1 rs#s2))) m
  | Pfeqd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Ceq rs#s1 rs#s2))) m
  | Pfltd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Clt rs#s1 rs#s2))) m
  | Pfled d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Cle rs#s1 rs#s2))) m

  | Pfcvtwd d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intoffloat rs#s)))) m
  | Pfcvtwud d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intuoffloat rs#s)))) m
  | Pfcvtdw d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatofint rs##s)))) m
  | Pfcvtdwu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatofintu rs##s)))) m

  | Pfcvtld d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.longoffloat rs#s)))) m
  | Pfcvtlud d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.longuoffloat rs#s)))) m
  | Pfcvtdl d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatoflong rs###s)))) m
  | Pfcvtdlu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatoflongu rs###s)))) m

  | Pfcvtds d s =>
      Next (nextinstr (rs#d <- (Val.floatofsingle rs#s))) m
  | Pfcvtsd d s =>
      Next (nextinstr (rs#d <- (Val.singleoffloat rs#s))) m

(** Pseudo-instructions *)
  | Pallocframe sz pos =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := (Vptr stk Ptrofs.zero) in
      match Mem.storev Mptr m1 (Val.offset_ptr sp pos) rs#SP with
      | None => Stuck
      | Some m2 => Next (nextinstr (rs #X30 <- (rs SP) #SP <- sp #X31 <- Vundef)) m2
      end
  | Pfreeframe sz pos =>
      match Mem.loadv Mptr m (Val.offset_ptr rs#SP pos) with
      | None => Stuck
      | Some v =>
          match rs SP with
          | Vptr stk ofs =>
              match Mem.free m stk 0 sz with
              | None => Stuck
              | Some m' => Next (nextinstr (rs#SP <- v #X31 <- Vundef)) m'
              end
          | _ => Stuck
          end
      end
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Ploadsymbol rd s ofs =>
      Next (nextinstr (rs#rd <- (Genv.symbol_address ge s ofs))) m
  | Ploadsymbol_high rd s ofs =>
      Next (nextinstr (rs#rd <- (high_half ge s ofs))) m
  | Ploadli rd i =>
      Next (nextinstr (rs#X31 <- Vundef #rd <- (Vlong i))) m
  | Ploadfi rd f =>
      Next (nextinstr (rs#X31 <- Vundef #rd <- (Vfloat f))) m
  | Ploadsi rd f =>
      Next (nextinstr (rs#X31 <- Vundef #rd <- (Vsingle f))) m
  | Pbtbl r tbl =>
      match rs r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs#X5 <- Vundef #X31 <- Vundef) m
          end
      | _ => Stuck
      end
  | Pbuiltin ef args res =>
      Stuck (**r treated specially below *)

  (** The following instructions and directives are not generated directly by Asmgen,
      so we do not model them. *)
  | Pfence

  | Pfmvxs _ _
  | Pfmvxd _ _

  | Pfmins _ _ _
  | Pfmaxs _ _ _
  | Pfsqrts _ _
  | Pfmadds _ _ _ _
  | Pfmsubs _ _ _ _
  | Pfnmadds _ _ _ _
  | Pfnmsubs _ _ _ _

  | Pfmind _ _ _
  | Pfmaxd _ _ _
  | Pfsqrtd _ _
  | Pfmaddd _ _ _ _
  | Pfmsubd _ _ _ _
  | Pfnmaddd _ _ _ _
  | Pfnmsubd _ _ _ _
  | Pnop
    => Stuck
  end.

(** Translation of the LTL/Linear/Mach view of machine registers to
  the RISC-V view.  Note that no LTL register maps to [X31].  This
  register is reserved as temporary, to be used by the generated RV32G
  code.  *)

Definition preg_of (r: mreg) : preg :=
  match r with
               | R5  => X5  | R6  => X6  | R7  => X7
  | R8  => X8  | R9  => X9  | R10 => X10 | R11 => X11
  | R12 => X12 | R13 => X13 | R14 => X14 | R15 => X15
  | R16 => X16 | R17 => X17 | R18 => X18 | R19 => X19
  | R20 => X20 | R21 => X21 | R22 => X22 | R23 => X23
  | R24 => X24 | R25 => X25 | R26 => X26 | R27 => X27
  | R28 => X28 | R29 => X29 | R30 => X30

  | Machregs.F0  => F0  | Machregs.F1  => F1  | Machregs.F2  => F2  | Machregs.F3  => F3
  | Machregs.F4  => F4  | Machregs.F5  => F5  | Machregs.F6  => F6  | Machregs.F7  => F7
  | Machregs.F8  => F8  | Machregs.F9  => F9  | Machregs.F10 => F10 | Machregs.F11 => F11
  | Machregs.F12 => F12 | Machregs.F13 => F13 | Machregs.F14 => F14 | Machregs.F15 => F15
  | Machregs.F16 => F16 | Machregs.F17 => F17 | Machregs.F18 => F18 | Machregs.F19 => F19
  | Machregs.F20 => F20 | Machregs.F21 => F21 | Machregs.F22 => F22 | Machregs.F23 => F23
  | Machregs.F24 => F24 | Machregs.F25 => F25 | Machregs.F26 => F26 | Machregs.F27 => F27
  | Machregs.F28 => F28 | Machregs.F29 => F29 | Machregs.F30 => F30 | Machregs.F31 => F31
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
    we use RISC-V registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr rs#SP (Ptrofs.repr bofs)) = Some v ->
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

(** Execution of the instruction at [rs PC]. *)

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
                (undef_regs (map preg_of (destroyed_by_builtin ef))
                   (rs#X31 <- Vundef))) ->
      step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (set_pair (loc_external_result (ef_sig ef) ) res (undef_caller_save_regs rs))#PC <- (rs RA) ->
      step (State rs m) t (State rs' m').

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # SP <- Vnullptr
        # RA <- Vnullptr in
      Genv.init_mem p = Some m0 ->
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs PC = Vnullptr ->
      rs X10 = Vint r ->
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
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. unfold Vzero in H0. red; intros; red; intros.
  inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | IR RA  => false
  | IR X31 => false
  | IR _   => true
  | FR _   => true
  | PC     => false
  end.
