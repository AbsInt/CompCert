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
Require Import Stacklayout.
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
  | CR0_3: preg                         (**r bit 3 of the condition register  *)
  | CR1_2: preg.                        (**r bit 6 of the condition register  *)

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

Notation "'SP'" := GPR1 (only parsing) : asm.
Notation "'RA'" := LR (only parsing) : asm.

(** Symbolic constants.  Immediate operands to an arithmetic instruction
  or an indexed memory access can be either integer literals,
  or the low or high 16 bits of a symbolic reference (the address
  of a symbol plus a displacement), or a 16-bit offset from the
  small data area register.  These symbolic references are
  resolved later by the linker.
*)

Inductive constant: Type :=
  | Cint: int -> constant
  | Csymbol_low: ident -> ptrofs -> constant
  | Csymbol_high: ident -> ptrofs -> constant
  | Csymbol_sda: ident -> ptrofs -> constant
  | Csymbol_rel_low: ident -> ptrofs -> constant
  | Csymbol_rel_high: ident -> ptrofs -> constant.

(** A note on constants: while immediate operands to PowerPC
  instructions must be representable in 16 bits (with
  sign extension or left shift by 16 positions for some instructions),
  we do not attempt to capture these restrictions in the
  abstract syntax nor in the semantics.  The assembler will
  emit an error if immediate operands exceed the representable
  range.  Of course, our PPC generator (file [Asmgen]) is
  careful to respect this range. *)

(** Bits in the condition register.  We are only interested in bits
  0, 1, 2, 3 and 6. *)

Inductive crbit: Type :=
  | CRbit_0: crbit
  | CRbit_1: crbit
  | CRbit_2: crbit
  | CRbit_3: crbit
  | CRbit_6: crbit.

(** The instruction set.  Most instructions correspond exactly to
  actual instructions of the PowerPC processor. See the PowerPC
  reference manuals for more details.  Some instructions,
  described below, are pseudo-instructions: they expand to
  canned instruction sequences during the printing of the assembly
  code. *)

Definition label := positive.

Inductive instruction : Type :=
  | Padd: ireg -> ireg -> ireg -> instruction                 (**r integer addition *)
  | Padd64: ireg -> ireg -> ireg -> instruction               (**r integer addition (PPC64) *)
  | Paddc: ireg -> ireg -> ireg -> instruction                (**r integer addition and set carry *)
  | Padde: ireg -> ireg -> ireg -> instruction                (**r integer addition with carry *)
  | Paddi: ireg -> ireg -> constant -> instruction            (**r add immediate *)
  | Paddi64: ireg -> ireg -> int64 -> instruction             (**r add immediate (PPC64) *)
  | Paddic: ireg -> ireg -> constant -> instruction           (**r add immediate and set carry *)
  | Paddis: ireg -> ireg -> constant -> instruction           (**r add immediate high *)
  | Paddis64: ireg -> ireg -> int64 -> instruction            (**r add immediate high (PPC64) *)
  | Paddze: ireg -> ireg -> instruction                       (**r add carry *)
  | Paddze64: ireg -> ireg -> instruction                     (**r add carry (PPC64) *)
  | Pallocframe: Z -> ptrofs -> ptrofs -> instruction         (**r allocate new stack frame (pseudo) *)
  | Pand_: ireg -> ireg -> ireg -> instruction                (**r bitwise and *)
  | Pand_64: ireg -> ireg -> ireg -> instruction              (**r bitwise and (PPC64) *)
  | Pandc: ireg -> ireg -> ireg -> instruction                (**r bitwise and-complement *)
  | Pandi_: ireg -> ireg -> constant -> instruction           (**r and immediate and set conditions *)
  | Pandi_64: ireg -> ireg -> int64 -> instruction            (**r and immediate and set conditions (PPC64) *)
  | Pandis_: ireg -> ireg -> constant -> instruction          (**r and immediate high and set conditions *)
  | Pandis_64: ireg -> ireg -> int64 -> instruction           (**r and immediate high and set conditions (PPC64) *)
  | Pb: label -> instruction                                  (**r unconditional branch *)
  | Pbctr: signature -> instruction                           (**r branch to contents of register CTR *)
  | Pbctrl: signature -> instruction                          (**r branch to contents of CTR and link *)
  | Pbdnz: label -> instruction                               (**r decrement CTR and branch if not zero *)
  | Pbf: crbit -> label -> instruction                        (**r branch if false *)
  | Pbl: ident -> signature -> instruction                    (**r branch and link *)
  | Pbs: ident -> signature -> instruction                    (**r branch to symbol *)
  | Pblr: instruction                                         (**r branch to contents of register LR *)
  | Pbt: crbit -> label -> instruction                        (**r branch if true *)
  | Pbtbl: ireg -> list label -> instruction                  (**r N-way branch through a jump table (pseudo) *)
  | Pcmpb: ireg -> ireg -> ireg -> instruction                (**r compare bytes *)
  | Pcmpld: ireg -> ireg -> instruction                       (**r unsigned integer comparison (PPC64) *)
  | Pcmpldi: ireg -> int64 -> instruction                     (**r same, with immediate argument (PPC64) *)
  | Pcmplw: ireg -> ireg -> instruction                       (**r unsigned integer comparison *)
  | Pcmplwi: ireg -> constant -> instruction                  (**r same, with immediate argument *)
  | Pcmpd: ireg -> ireg -> instruction                        (**r signed integer comparison (PPC64) *)
  | Pcmpdi: ireg -> int64 -> instruction                      (**r same, with immediate argument (PPC64) *)
  | Pcmpw: ireg -> ireg -> instruction                        (**r signed integer comparison *)
  | Pcmpwi: ireg -> constant -> instruction                   (**r same, with immediate argument *)
  | Pcntlzd: ireg -> ireg -> instruction                      (**r count leading zeros (PPC64) *)
  | Pcntlzw: ireg -> ireg -> instruction                      (**r count leading zeros *)
  | Pcreqv: crbit -> crbit -> crbit -> instruction            (**r not-xor between condition bits *)
  | Pcror: crbit -> crbit -> crbit -> instruction             (**r or between condition bits *)
  | Pcrxor: crbit -> crbit -> crbit -> instruction            (**r xor between condition bits *)
  | Pdcbf: ireg -> ireg -> instruction                        (**r data cache flush *)
  | Pdcbi: ireg -> ireg -> instruction                        (**r data cache invalidate *)
  | Pdcbt: int -> ireg -> ireg -> instruction                 (**r data cache block touch *)
  | Pdcbtst: int -> ireg -> ireg -> instruction               (**r data cache block touch *)
  | Pdcbtls: int -> ireg -> ireg -> instruction               (**r data cache block touch and lock *)
  | Pdcbz: ireg -> ireg -> instruction                        (**r data cache block zero *)
  | Pdivw: ireg -> ireg -> ireg -> instruction                (**r signed division *)
  | Pdivd: ireg -> ireg -> ireg -> instruction                (**r signed division (PPC64) *)
  | Pdivwu: ireg -> ireg -> ireg -> instruction               (**r unsigned division *)
  | Pdivdu: ireg -> ireg -> ireg -> instruction               (**r unsigned division (PPC64) *)
  | Peieio: instruction                                       (**r EIEIO barrier *)
  | Peqv: ireg -> ireg -> ireg -> instruction                 (**r bitwise not-xor *)
  | Pextsb: ireg -> ireg -> instruction                       (**r 8-bit sign extension *)
  | Pextsh: ireg -> ireg -> instruction                       (**r 16-bit sign extension *)
  | Pextsw: ireg -> ireg -> instruction                       (**r 64-bit sign extension (PPC64) *)
  | Pextzw: ireg -> ireg -> instruction                       (**r 64-bit zero extension (pseudo, PPC64) *)
  | Pfreeframe: Z -> ptrofs -> instruction                    (**r deallocate stack frame and restore previous frame (pseudo) *)
  | Pfabs: freg -> freg -> instruction                        (**r float absolute value *)
  | Pfabss: freg -> freg -> instruction                       (**r float absolute value *)
  | Pfadd: freg -> freg -> freg -> instruction                (**r float addition *)
  | Pfadds: freg -> freg -> freg -> instruction               (**r float addition *)
  | Pfcmpu: freg -> freg -> instruction                       (**r float comparison *)
  | Pfcfi: freg -> ireg -> instruction                        (**r signed-int-to-float conversion (pseudo, PPC64) *)
  | Pfcfl: freg -> ireg -> instruction                        (**r signed-long-to-float conversion (pseudo, PPC64) *)
  | Pfcfiu: freg -> ireg -> instruction                       (**r unsigned-int-to-float conversion (pseudo, PPC64) *)
  | Pfcfid: freg -> freg -> instruction                       (**r signed-long-to-float conversion (PPC64) *)
  | Pfcti: ireg -> freg -> instruction                        (**r float-to-signed-int conversion, round towards 0 (pseudo) *)
  | Pfctiu: ireg -> freg -> instruction                       (**r float-to-unsigned-int conversion, round towards 0 (pseudo, PPC64) *)
  | Pfctid: ireg -> freg -> instruction                       (**r float-to-signed-int conversion, round towards 0 (pseudo, PPC64) *)
  | Pfctidz: freg -> freg -> instruction                      (**r float-to-signed-long conversion, round towards 0 (PPC64) *)
  | Pfctiw: freg -> freg -> instruction                       (**r float-to-signed-int conversion, round by default *)
  | Pfctiwz: freg -> freg -> instruction                      (**r float-to-signed-int conversion, round towards 0 *)
  | Pfdiv: freg -> freg -> freg -> instruction                (**r float division *)
  | Pfdivs: freg -> freg -> freg -> instruction               (**r float division *)
  | Pfmake: freg -> ireg -> ireg -> instruction               (**r build a float from 2 ints (pseudo) *)
  | Pfmr: freg -> freg -> instruction                         (**r float move *)
  | Pfmul: freg -> freg -> freg -> instruction                (**r float multiply *)
  | Pfmuls: freg -> freg -> freg -> instruction               (**r float multiply *)
  | Pfneg: freg -> freg -> instruction                        (**r float negation *)
  | Pfnegs: freg -> freg -> instruction                       (**r float negation *)
  | Pfrsp: freg -> freg -> instruction                        (**r float round to single precision *)
  | Pfxdp: freg -> freg -> instruction                        (**r float extend to double precision (pseudo) *)
  | Pfsub: freg -> freg -> freg -> instruction                (**r float subtraction *)
  | Pfsubs: freg -> freg -> freg -> instruction               (**r float subtraction *)
  | Pfmadd: freg -> freg -> freg -> freg -> instruction       (**r fused multiply-add *)
  | Pfmsub: freg -> freg -> freg -> freg -> instruction       (**r fused multiply-sub *)
  | Pfnmadd: freg -> freg -> freg -> freg -> instruction      (**r fused neg-multiply-add *)
  | Pfnmsub: freg -> freg -> freg -> freg -> instruction      (**r fused neg-multiply-sub *)
  | Pfsqrt: freg -> freg -> instruction                       (**r square root *)
  | Pfrsqrte: freg -> freg -> instruction                     (**r approximate reciprocal of square root *)
  | Pfres: freg -> freg -> instruction                        (**r approximate inverse *)
  | Pfsel: freg -> freg -> freg -> freg -> instruction        (**r FP conditional move *)
  | Pisel: ireg -> ireg -> ireg -> crbit -> instruction       (**r integer select *)
  | Pisync: instruction                                       (**r ISYNC barrier *)
  | Picbi: ireg -> ireg -> instruction                        (**r instruction cache invalidate *)
  | Picbtls: int -> ireg -> ireg -> instruction               (**r instruction cache block touch and lock set *)
  | Plbz: ireg -> constant -> ireg -> instruction             (**r load 8-bit unsigned int *)
  | Plbzx: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Pld: ireg -> constant -> ireg -> instruction              (**r load 64-bit int (PPC64) *)
  | Pldx: ireg -> ireg -> ireg -> instruction                 (**r same, with 2 index regs *)
  | Pld_a: ireg -> constant -> ireg -> instruction            (**r load 64-bit quantity to int reg (PPC64) *)
  | Pldbrx: ireg -> ireg -> ireg -> instruction               (**r load 64-bit int and reverse endianness (PPC64) *)
  | Pldx_a: ireg -> ireg -> ireg -> instruction               (**r same, with 2 index regs *)
  | Plfd: freg -> constant -> ireg -> instruction             (**r load 64-bit float *)
  | Plfdx: freg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Plfd_a: freg -> constant -> ireg -> instruction           (**r load 64-bit quantity to float reg *)
  | Plfdx_a: freg -> ireg -> ireg -> instruction              (**r same, with 2 index regs *)
  | Plfs: freg -> constant -> ireg -> instruction             (**r load 32-bit float *)
  | Plfsx: freg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Plha: ireg -> constant -> ireg -> instruction             (**r load 16-bit signed int *)
  | Plhax: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Plhbrx: ireg -> ireg -> ireg -> instruction               (**r load 16-bit int and reverse endianness *)
  | Plhz: ireg -> constant -> ireg -> instruction             (**r load 16-bit unsigned int *)
  | Plhzx: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Pldi: ireg -> int64 -> instruction                        (**r load 64-bit int constant (PPC64) *)
  | Plmake: ireg -> ireg -> ireg -> instruction               (**r build an int64 from 2 ints (pseudo, PPC64) *)
  | Pllo: ireg -> instruction                                 (**r extract low 32 bits of an int64 (pseudo, PPC64) *)
  | Plhi: ireg -> ireg -> instruction                         (**r extract high 32 bits of an int64 (pseudo, PPC64) *)
  | Plfi: freg -> float -> instruction                        (**r load float constant *)
  | Plfis: freg -> float32 -> instruction                     (**r load float constant *)
  | Plwz: ireg -> constant -> ireg -> instruction             (**r load 32-bit int *)
  | Plwzu: ireg -> constant -> ireg -> instruction            (**r load 32-bit int with update *)
  | Plwzx: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Plwz_a: ireg -> constant -> ireg -> instruction           (**r load 32-bit quantity to int reg *)
  | Plwzx_a: ireg -> ireg -> ireg -> instruction              (**r same, with 2 index regs *)
  | Plwarx: ireg -> ireg -> ireg -> instruction               (**r load with reservation *)
  | Plwbrx: ireg -> ireg -> ireg -> instruction               (**r load 32-bit int and reverse endianness *)
  | Pmbar: int -> instruction                                 (**r memory barrier *)
  | Pmfcr: ireg -> instruction                                (**r move condition register to reg *)
  | Pmfcrbit: ireg -> crbit -> instruction                    (**r move condition bit to reg (pseudo) *)
  | Pmflr: ireg -> instruction                                (**r move LR to reg *)
  | Pmr: ireg -> ireg -> instruction                          (**r integer move *)
  | Pmtctr: ireg -> instruction                               (**r move ireg to CTR *)
  | Pmtlr: ireg -> instruction                                (**r move ireg to LR *)
  | Pmfspr: ireg -> int -> instruction                        (**r move from special register *)
  | Pmtspr: int -> ireg -> instruction                        (**r move to special register *)
  | Pmulli: ireg -> ireg -> constant -> instruction           (**r integer multiply immediate *)
  | Pmullw: ireg -> ireg -> ireg -> instruction               (**r integer multiply *)
  | Pmulld: ireg -> ireg -> ireg -> instruction               (**r integer multiply (PPC64) *)
  | Pmulhw: ireg -> ireg -> ireg -> instruction               (**r multiply high signed *)
  | Pmulhwu: ireg -> ireg -> ireg -> instruction              (**r multiply high signed *)
  | Pmulhd: ireg -> ireg -> ireg -> instruction               (**r multiply high double word signed (PPC64) *)
  | Pmulhdu: ireg -> ireg -> ireg -> instruction              (**r multiply high double word unsigned (PPC64) *)
  | Pnand: ireg -> ireg -> ireg -> instruction                (**r bitwise not-and *)
  | Pnor: ireg -> ireg -> ireg -> instruction                 (**r bitwise not-or *)
  | Pnor64: ireg -> ireg -> ireg -> instruction               (**r bitwise not-or (PPC64) *)
  | Por: ireg -> ireg -> ireg -> instruction                  (**r bitwise or *)
  | Por64: ireg -> ireg -> ireg -> instruction                (**r bitwise or (PPC64) *)
  | Porc: ireg -> ireg -> ireg -> instruction                 (**r bitwise or-complement *)
  | Pori: ireg -> ireg -> constant -> instruction             (**r or with immediate *)
  | Pori64: ireg -> ireg -> int64 -> instruction              (**r or with immediate (PPC64) *)
  | Poris: ireg -> ireg -> constant -> instruction            (**r or with immediate high *)
  | Poris64: ireg -> ireg -> int64 -> instruction             (**r or with immediate high (PPC64) *)
  | Prldicl: ireg -> ireg -> int -> int -> instruction        (**r rotate and mask left (PPC64) *)
  | Prldinm: ireg -> ireg -> int -> int64 -> instruction      (**r rotate and mask (PPC64) *)
  | Prldimi: ireg -> ireg -> int -> int64 -> instruction      (**r rotate and insert (PPC64) *)
  | Prlwinm: ireg -> ireg -> int -> int -> instruction        (**r rotate and mask *)
  | Prlwimi: ireg -> ireg -> int -> int -> instruction        (**r rotate and insert *)
  | Psld: ireg -> ireg -> ireg -> instruction                 (**r shift left 64 bits (PPC64) *)
  | Pslw: ireg -> ireg -> ireg -> instruction                 (**r shift left *)
  | Psrad: ireg -> ireg -> ireg -> instruction                (**r shift right signed 64 bits (PPC64) *)
  | Psradi: ireg -> ireg -> int -> instruction                (**r shift right signed immediate 64 bits (PPC64) *)
  | Psraw: ireg -> ireg -> ireg -> instruction                (**r shift right signed *)
  | Psrawi: ireg -> ireg -> int -> instruction                (**r shift right signed immediate *)
  | Psrd: ireg -> ireg -> ireg -> instruction                 (**r shift right unsigned 64 bits (PPC64) *)
  | Psrw: ireg -> ireg -> ireg -> instruction                 (**r shift right unsigned *)
  | Pstb: ireg -> constant -> ireg -> instruction             (**r store 8-bit int *)
  | Pstbx: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Pstd: ireg -> constant -> ireg -> instruction             (**r store 64-bit integer (PPC64) *)
  | Pstdx: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs (PPC64) *)
  | Pstdbrx: ireg -> ireg -> ireg -> instruction              (**r store 64-bit int with reverse endianness (PPC64) *)
  | Pstdu: ireg -> constant -> ireg -> instruction            (**r store 64-bit integer with update (PPC64) *)
  | Pstd_a: ireg -> constant -> ireg -> instruction           (**r store 64-bit quantity from int reg (PPC64) *)
  | Pstdx_a: ireg -> ireg -> ireg -> instruction              (**r same, with 2 index regs (PPC64) *)
  | Pstfd: freg -> constant -> ireg -> instruction            (**r store 64-bit float *)
  | Pstfdu: freg -> constant -> ireg -> instruction           (**r store 64-bit float with update *)
  | Pstfdx: freg -> ireg -> ireg -> instruction               (**r same, with 2 index regs *)
  | Pstfd_a: freg -> constant -> ireg -> instruction          (**r store 64-bit quantity from float reg *)
  | Pstfdx_a: freg -> ireg -> ireg -> instruction             (**r same, with 2 index regs *)
  | Pstfs: freg -> constant -> ireg -> instruction            (**r store 32-bit float *)
  | Pstfsx: freg -> ireg -> ireg -> instruction               (**r same, with 2 index regs *)
  | Psth: ireg -> constant -> ireg -> instruction             (**r store 16-bit int *)
  | Psthx: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Psthbrx: ireg -> ireg -> ireg -> instruction              (**r store 16-bit int with reverse endianness *)
  | Pstw: ireg -> constant -> ireg -> instruction             (**r store 32-bit int *)
  | Pstwu: ireg -> constant -> ireg -> instruction            (**r store 32-bit int with update *)
  | Pstwx: ireg -> ireg -> ireg -> instruction                (**r same, with 2 index regs *)
  | Pstwux: ireg -> ireg -> ireg -> instruction               (**r same, with 2 index regs and update *)
  | Pstw_a: ireg -> constant -> ireg -> instruction           (**r store 32-bit quantity from int reg *)
  | Pstwx_a: ireg -> ireg -> ireg -> instruction              (**r same, with 2 index regs *)
  | Pstwbrx: ireg -> ireg -> ireg -> instruction              (**r store 32-bit int with reverse endianness *)
  | Pstwcx_: ireg -> ireg -> ireg -> instruction              (**r store conditional *)
  | Psubfc: ireg -> ireg -> ireg -> instruction               (**r reversed integer subtraction *)
  | Psubfc64: ireg -> ireg -> ireg -> instruction             (**r reversed integer subtraction (PPC64) *)
  | Psubfe: ireg -> ireg -> ireg -> instruction               (**r reversed integer subtraction with carry *)
  | Psubfze: ireg -> ireg -> instruction                      (**r integer opposite with carry *)
  | Psubfic: ireg -> ireg -> constant -> instruction          (**r integer subtraction from immediate *)
  | Psubfic64: ireg -> ireg -> int64 -> instruction           (**r integer subtraction from immediate (PPC64) *)
  | Psync: instruction                                        (**r SYNC barrier *)
  | Plwsync: instruction                                      (**r LWSYNC barrier *)
  | Ptrap: instruction                                        (**r unconditional trap *)
  | Pxor: ireg -> ireg -> ireg -> instruction                 (**r bitwise xor *)
  | Pxor64: ireg -> ireg -> ireg -> instruction               (**r bitwise xor (PPC64) *)
  | Pxori: ireg -> ireg -> constant -> instruction            (**r bitwise xor with immediate *)
  | Pxori64: ireg -> ireg -> int64 -> instruction             (**r bitwise xor with immediate (PPC64) *)
  | Pxoris: ireg -> ireg -> constant -> instruction           (**r bitwise xor with immediate high *)
  | Pxoris64: ireg -> ireg -> int64 -> instruction            (**r bitwise xor with immediate high (PPC64) *)
  | Plabel: label -> instruction                              (**r define a code label *)
  | Pbuiltin: external_function -> list (builtin_arg preg) -> builtin_res preg -> instruction (**r built-in function (pseudo) *)
  | Pcfi_adjust: int -> instruction                           (**r .cfi_adjust debug directive *)
  | Pcfi_rel_offset: int -> instruction.                      (**r .cfi_rel_offset lr debug directive *)

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
- [Pallocframe sz ofs retofs]: in the formal semantics, this pseudo-instruction
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
Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
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

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
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

(** Some PowerPC instructions treat register GPR0 as the integer literal 0
  when that register is used in argument position. *)

Definition gpr_or_zero (rs: regset) (r: ireg) :=
  if ireg_eq r GPR0 then Vint Int.zero else rs#r.

Definition gpr_or_zero_l (rs: regset) (r: ireg) :=
  if ireg_eq r GPR0 then Vlong Int64.zero else rs#r.

Variable ge: genv.

(** The two functions below axiomatize how the linker processes
  symbolic references [symbol + offset] and splits their
  actual values into two 16-bit halves. *)

Parameter low_half: genv -> ident -> ptrofs -> val.
Parameter high_half: genv -> ident -> ptrofs -> val.

(** The fundamental property of these operations is that, when applied
  to the address of a symbol, their results can be recombined by
  addition, rebuilding the original address. *)

Axiom low_high_half:
  forall id ofs,
  Val.add (high_half ge id ofs) (low_half ge id ofs) = Genv.symbol_address ge id ofs.

(** We also axiomatize the small data area.  For simplicity, we
  claim that small data symbols can be accessed by absolute 16-bit
  offsets, that is, relative to [GPR0].  In reality, the linker
  rewrites the object code, transforming [symb@sdarx(r0)] addressings
  into [offset(rN)] addressings, where [rN] is the reserved
  register pointing to the base of the small data area containing
  symbol [symb].  We leave this transformation up to the linker. *)

Parameter symbol_is_small_data: ident -> ptrofs -> bool.
Parameter small_data_area_offset: genv -> ident -> ptrofs -> val.

Axiom small_data_area_addressing:
  forall id ofs,
  symbol_is_small_data id ofs = true ->
  small_data_area_offset ge id ofs = Genv.symbol_address ge id ofs.

Parameter symbol_is_rel_data: ident -> ptrofs -> bool.

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
  | Csymbol_low id ofs => low_half ge id ofs
  | Csymbol_high id ofs => Vundef
  | Csymbol_sda id ofs => small_data_area_offset ge id ofs
  | Csymbol_rel_low id ofs => low_half ge id ofs
  | Csymbol_rel_high id ofs => Vundef
  end.

Definition const_high (c: constant) :=
  match c with
  | Cint n => Vint (Int.shl n (Int.repr 16))
  | Csymbol_low id ofs => Vundef
  | Csymbol_high id ofs => high_half ge id ofs
  | Csymbol_sda id ofs => Vundef
  | Csymbol_rel_low id ofs => Vundef
  | Csymbol_rel_high id ofs => high_half ge id ofs
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
  match Mem.loadv chunk m (Val.add (gpr_or_zero rs r1) rs#r2) with
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
  match Mem.storev chunk m (Val.add (gpr_or_zero rs r1) rs#r2) (rs#r) with
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
  | CRbit_6 => CR1_2
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

Definition compare_slong (rs: regset) (v1 v2: val) :=
  rs#CR0_0 <- (Val.of_optbool (Val.cmpl_bool Clt v1 v2))
    #CR0_1 <- (Val.of_optbool (Val.cmpl_bool Cgt v1 v2))
    #CR0_2 <- (Val.of_optbool (Val.cmpl_bool Ceq v1 v2))
    #CR0_3 <- Vundef.

Definition compare_ulong (rs: regset) (m: mem) (v1 v2: val) :=
  rs#CR0_0 <- (Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Clt v1 v2))
    #CR0_1 <- (Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Cgt v1 v2))
    #CR0_2 <- (Val.of_optbool (Val.cmplu_bool (Mem.valid_pointer m) Ceq v1 v2))
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

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  | Padd rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 rs#r2))) m
  | Padd64 rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.addl rs#r1 rs#r2))) m
  | Paddc rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 rs#r2)
                        #CARRY <- (Val.add_carry rs#r1 rs#r2 Vzero))) m
  | Padde rd r1 r2 =>
      Next (nextinstr (rs #rd <- (Val.add (Val.add rs#r1 rs#r2) rs#CARRY)
                        #CARRY <- (Val.add_carry rs#r1 rs#r2 rs#CARRY))) m
  | Paddi rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.add (gpr_or_zero rs r1) (const_low cst)))) m
  | Paddi64 rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.addl (gpr_or_zero_l rs r1) (Vlong cst)))) m
  | Paddic rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.add (gpr_or_zero rs r1) (const_low cst))
                       #CARRY <- (Val.add_carry (gpr_or_zero rs r1) (const_low cst) Vzero))) m
  | Paddis rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.add (gpr_or_zero rs r1) (const_high cst)))) m
  | Paddis64 rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.addl (gpr_or_zero_l rs r1) (Vlong (Int64.shl cst (Int64.repr 16)))))) m
  | Paddze rd r1 =>
      Next (nextinstr (rs#rd <- (Val.add rs#r1 rs#CARRY)
                       #CARRY <- (Val.add_carry rs#r1 Vzero rs#CARRY))) m
  | Paddze64 rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addl rs#r1 rs#CARRY)
                       #CARRY <- (Val.addl_carry rs#r1 (Vlong Int64.zero) rs#CARRY))) m
  | Pallocframe sz ofs _ =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := Vptr stk Ptrofs.zero in
      match Mem.storev Mint32 m1 (Val.offset_ptr sp ofs) rs#GPR1 with
      | None => Stuck
      | Some m2 => Next (nextinstr (rs#GPR1 <- sp #GPR0 <- Vundef)) m2
      end
  | Pand_ rd r1 r2 =>
      let v := Val.and rs#r1 rs#r2 in
      Next (nextinstr (compare_sint (rs#rd <- v) v Vzero)) m
  | Pand_64 rd r1 r2 =>
      let v := Val.andl rs#r1 rs#r2 in
      Next (nextinstr (compare_slong (rs#rd <- v) v (Vlong Int64.zero))) m
  | Pandc rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.and rs#r1 (Val.notint rs#r2)))) m
  | Pandi_ rd r1 cst =>
      let v := Val.and rs#r1 (const_low cst) in
      Next (nextinstr (compare_sint (rs#rd <- v) v Vzero)) m
  | Pandi_64 rd r1 cst =>
      let v := Val.andl rs#r1 (Vlong cst) in
      Next (nextinstr (compare_slong (rs#rd <- v) v (Vlong Int64.zero))) m
  | Pandis_ rd r1 cst =>
      let v := Val.and rs#r1 (const_high cst) in
      Next (nextinstr (compare_sint (rs#rd <- v) v Vzero)) m
  | Pandis_64 rd r1 cst =>
      let v := Val.andl rs#r1 (Vlong (Int64.shl cst (Int64.repr 16))) in
      Next (nextinstr (compare_slong (rs#rd <- v) v (Vlong Int64.zero))) m
  | Pb lbl =>
      goto_label f lbl rs m
  | Pbctr sg =>
      Next (rs#PC <- (rs#CTR)) m
  | Pbctrl sg =>
      Next (rs#LR <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (rs#CTR)) m
  | Pbf bit lbl =>
      match rs#(reg_of_crbit bit) with
      | Vint n => if Int.eq n Int.zero then goto_label f lbl rs m else Next (nextinstr rs) m
      | _ => Stuck
      end
  | Pbl ident sg =>
      Next (rs#LR <- (Val.offset_ptr rs#PC Ptrofs.one) #PC <- (Genv.symbol_address ge ident Ptrofs.zero)) m
  | Pbs ident sg =>
      Next (rs#PC <- (Genv.symbol_address ge ident Ptrofs.zero)) m
  | Pblr =>
      Next (rs#PC <- (rs#LR)) m
  | Pbt bit lbl =>
      match rs#(reg_of_crbit bit) with
      | Vint n => if Int.eq n Int.zero then Next (nextinstr rs) m else goto_label f lbl rs m
      | _ => Stuck
      end
  | Pbtbl r tbl =>
      match rs r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs #GPR12 <- Vundef #CTR <- Vundef) m
          end
      | _ => Stuck
      end
  | Pcmpld r1 r2 =>
      Next (nextinstr (compare_ulong rs m rs#r1 rs#r2)) m
  | Pcmpldi r1 cst =>
      Next (nextinstr (compare_ulong rs m rs#r1 (Vlong cst))) m
  | Pcmplw r1 r2 =>
      Next (nextinstr (compare_uint rs m rs#r1 rs#r2)) m
  | Pcmplwi r1 cst =>
      Next (nextinstr (compare_uint rs m rs#r1 (const_low cst))) m
  | Pcmpd r1 r2 =>
      Next (nextinstr (compare_slong rs rs#r1 rs#r2)) m
  | Pcmpdi r1 cst =>
      Next (nextinstr (compare_slong rs rs#r1 (Vlong cst))) m
  | Pcmpw r1 r2 =>
      Next (nextinstr (compare_sint rs rs#r1 rs#r2)) m
  | Pcmpwi r1 cst =>
      Next (nextinstr (compare_sint rs rs#r1 (const_low cst))) m
  | Pcror bd b1 b2 =>
      Next (nextinstr (rs#(reg_of_crbit bd) <- (Val.or rs#(reg_of_crbit b1) rs#(reg_of_crbit b2)))) m
  | Pdivw rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.divs rs#r1 rs#r2)))) m
  | Pdivd rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.divls rs#r1 rs#r2)))) m
  | Pdivwu rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.divu rs#r1 rs#r2)))) m
  | Pdivdu rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.divlu rs#r1 rs#r2)))) m
  | Peqv rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.notint (Val.xor rs#r1 rs#r2)))) m
  | Pextsb rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1))) m
  | Pextsh rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1))) m
  | Pextsw rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofint rs#r1))) m
  | Pextzw rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofintu rs#r1))) m
  | Pfreeframe sz ofs =>
      match Mem.loadv Mint32 m (Val.offset_ptr rs#GPR1 ofs) with
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
  | Pfabss rd r1 =>
      Next (nextinstr (rs#rd <- (Val.absfs rs#r1))) m
  | Pfadd rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.addf rs#r1 rs#r2))) m
  | Pfadds rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.addfs rs#r1 rs#r2))) m
  | Pfcmpu r1 r2 =>
      Next (nextinstr (compare_float rs rs#r1 rs#r2)) m
  | Pfcfi rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatofint rs#r1)))) m
  | Pfcfl rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatoflong rs#r1)))) m
  | Pfcfiu rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatofintu rs#r1)))) m
  | Pfcti rd r1 =>
      Next (nextinstr (rs#FPR13 <- Vundef #rd <- (Val.maketotal (Val.intoffloat rs#r1)))) m
  | Pfctiu rd r1 =>
      Next (nextinstr (rs#FPR13 <- Vundef #rd <- (Val.maketotal (Val.intuoffloat rs#r1)))) m
  | Pfctid rd r1 =>
      Next (nextinstr (rs#FPR13 <- Vundef #rd <- (Val.maketotal (Val.longoffloat rs#r1)))) m
  | Pfdiv rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.divf rs#r1 rs#r2))) m
  | Pfdivs rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.divfs rs#r1 rs#r2))) m
  | Pfmake rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.floatofwords rs#r1 rs#r2))) m
  | Pfmr rd r1 =>
      Next (nextinstr (rs#rd <- (rs#r1))) m
  | Pfmul rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mulf rs#r1 rs#r2))) m
  | Pfmuls rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mulfs rs#r1 rs#r2))) m
  | Pfneg rd r1 =>
      Next (nextinstr (rs#rd <- (Val.negf rs#r1))) m
  | Pfnegs rd r1 =>
      Next (nextinstr (rs#rd <- (Val.negfs rs#r1))) m
  | Pfrsp rd r1 =>
      Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1))) m
  | Pfxdp rd r1 =>
      Next (nextinstr (rs#rd <- (Val.floatofsingle rs#r1))) m
  | Pfsub rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.subf rs#r1 rs#r2))) m
  | Pfsubs rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.subfs rs#r1 rs#r2))) m
  | Plbz rd cst r1 =>
      load1 Mint8unsigned rd cst r1 rs m
  | Plbzx rd r1 r2 =>
      load2 Mint8unsigned rd r1 r2 rs m
  | Pld rd cst r1 =>
      load1 Mint64 rd cst r1 rs m
  | Pldx rd r1 r2 =>
      load2 Mint64 rd r1 r2 rs m
  | Pld_a rd cst r1 =>
      load1 Many64 rd cst r1 rs m
  | Pldx_a rd r1 r2 =>
      load2 Many64 rd r1 r2 rs m
  | Plfd rd cst r1 =>
      load1 Mfloat64 rd cst r1 rs m
  | Plfd_a rd cst r1 =>
      load1 Many64 rd cst r1 rs m
  | Plfdx rd r1 r2 =>
      load2 Mfloat64 rd r1 r2 rs m
  | Plfdx_a rd r1 r2 =>
      load2 Many64 rd r1 r2 rs m
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
  | Pldi rd i =>
       Next (nextinstr (rs #GPR12 <- Vundef #rd <- (Vlong i))) m
  | Plmake rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.longofwords rs#r1 rs#r2))) m
  | Pllo rd =>
      Next (nextinstr (rs#rd <- (Val.loword rs#rd))) m
  | Plhi rd r1 =>
      Next (nextinstr (rs#rd <- (Val.hiword rs#r1))) m
  | Plfi rd f =>
      Next (nextinstr (rs #GPR12 <- Vundef #rd <- (Vfloat f))) m
  | Plfis rd f =>
      Next (nextinstr (rs #GPR12 <- Vundef #rd <- (Vsingle f))) m
  | Plwz rd cst r1 =>
      load1 Mint32 rd cst r1 rs m
  | Plwzx rd r1 r2 =>
      load2 Mint32 rd r1 r2 rs m
  | Plwz_a rd cst r1 =>
      load1 Many32 rd cst r1 rs m
  | Plwzx_a rd r1 r2 =>
      load2 Many32 rd r1 r2 rs m
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
  | Pmulld rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mull rs#r1 rs#r2))) m
  | Pmulhw rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mulhs rs#r1 rs#r2))) m
  | Pmulhwu rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mulhu rs#r1 rs#r2))) m
  | Pmulhd rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mullhs rs#r1 rs#r2))) m
  | Pmulhdu rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.mullhu rs#r1 rs#r2))) m
  | Pnand rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.notint (Val.and rs#r1 rs#r2)))) m
  | Pnor rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.notint (Val.or rs#r1 rs#r2)))) m
  | Pnor64 rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.notl (Val.orl rs#r1 rs#r2)))) m
  | Por rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.or rs#r1 rs#r2))) m
  | Por64 rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.orl rs#r1 rs#r2))) m
  | Porc rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.or rs#r1 (Val.notint rs#r2)))) m
  | Pori rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.or rs#r1 (const_low cst)))) m
  | Pori64 rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.orl rs#r1 (Vlong cst)))) m
  | Poris rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.or rs#r1 (const_high cst)))) m
  | Poris64 rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.orl rs#r1 (Vlong (Int64.shl cst (Int64.repr 16)))))) m
  | Prldinm rd r1 amount mask =>
      Next (nextinstr (rs#rd <- (Val.rolml rs#r1 amount mask))) m
  | Prlwinm rd r1 amount mask =>
      Next (nextinstr (rs#rd <- (Val.rolm rs#r1 amount mask))) m
  | Prlwimi rd r1 amount mask =>
      Next (nextinstr (rs#rd <- (Val.or (Val.and rs#rd (Vint (Int.not mask)))
                                     (Val.rolm rs#r1 amount mask)))) m
  | Psld rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shll rs#r1 rs#r2))) m
  | Pslw rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shl rs#r1 rs#r2))) m
  | Psrad rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shrl rs#r1 rs#r2) #CARRY <- (Val.shrl_carry rs#r1 rs#r2))) m
  | Psradi rd r1 n =>
      Next (nextinstr (rs#rd <- (Val.shrl rs#r1 (Vint n)) #CARRY <- (Val.shrl_carry rs#r1 (Vint n)))) m
  | Psraw rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shr rs#r1 rs#r2) #CARRY <- (Val.shr_carry rs#r1 rs#r2))) m
  | Psrawi rd r1 n =>
      Next (nextinstr (rs#rd <- (Val.shr rs#r1 (Vint n)) #CARRY <- (Val.shr_carry rs#r1 (Vint n)))) m
  | Psrd rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shrlu rs#r1 rs#r2))) m
  | Psrw rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.shru rs#r1 rs#r2))) m
  | Pstb rd cst r1 =>
      store1 Mint8unsigned rd cst r1 rs m
  | Pstbx rd r1 r2 =>
      store2 Mint8unsigned rd r1 r2 rs m
  | Pstd rd cst r1 =>
      store1 Mint64 rd cst r1 rs m
  | Pstdx rd r1 r2 =>
      store2 Mint64 rd r1 r2 rs m
  | Pstd_a rd cst r1 =>
      store1 Many64 rd cst r1 rs m
  | Pstdx_a rd r1 r2 =>
      store2 Many64 rd r1 r2 rs m
  | Pstfd rd cst r1 =>
      store1 Mfloat64 rd cst r1 rs m
  | Pstfdx rd r1 r2 =>
      store2 Mfloat64 rd r1 r2 rs m
  | Pstfd_a rd cst r1 =>
      store1 Many64 rd cst r1 rs m
  | Pstfdx_a rd r1 r2 =>
      store2 Many64 rd r1 r2 rs m
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
  | Pstw_a rd cst r1 =>
      store1 Many32 rd cst r1 rs m
  | Pstwx_a rd r1 r2 =>
      store2 Many32 rd r1 r2 rs m
  | Psubfc rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.sub rs#r2 rs#r1)
                       #CARRY <- (Val.add_carry rs#r2 (Val.notint rs#r1) Vone))) m
  | Psubfc64 rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.subl rs#r2 rs#r1) #CARRY <- Vundef)) m
  | Psubfe rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.add (Val.add rs#r2 (Val.notint rs#r1)) rs#CARRY)
                       #CARRY <- (Val.add_carry rs#r2 (Val.notint rs#r1) rs#CARRY))) m
  | Psubfic rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.sub (const_low cst) rs#r1)
                       #CARRY <- (Val.add_carry (const_low cst) (Val.notint rs#r1) Vone))) m
  | Psubfic64 rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.subl (Vlong cst) rs#r1) #CARRY <- Vundef)) m
  | Pxor rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.xor rs#r1 rs#r2))) m
  | Pxor64 rd r1 r2 =>
      Next (nextinstr (rs#rd <- (Val.xorl rs#r1 rs#r2))) m
  | Pxori rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.xor rs#r1 (const_low cst)))) m
  | Pxori64 rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.xorl rs#r1 (Vlong cst)))) m
  | Pxoris rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.xor rs#r1 (const_high cst)))) m
  | Pxoris64 rd r1 cst =>
      Next (nextinstr (rs#rd <- (Val.xorl rs#r1 (Vlong (Int64.shl cst (Int64.repr 16)))))) m
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Pcfi_rel_offset ofs =>
      Next (nextinstr rs) m
  | Pbuiltin ef args res =>
      Stuck    (**r treated specially below *)
  (** The following instructions and directives are not generated
      directly by [Asmgen], so we do not model them. *)
  | Pbdnz _
  | Pcmpb _ _ _
  | Pcntlzd _ _
  | Pcntlzw _ _
  | Pcreqv _ _ _
  | Pcrxor _ _ _
  | Pdcbf _ _
  | Pdcbi _ _
  | Pdcbt _ _ _
  | Pdcbtst _ _ _
  | Pdcbtls _ _ _
  | Pdcbz _ _
  | Peieio
  | Pfcfid _ _
  | Pfctidz _ _
  | Pfctiw _ _
  | Pfctiwz _ _
  | Pfmadd _ _ _ _
  | Pfmsub _ _ _ _
  | Pfnmadd _ _ _ _
  | Pfnmsub _ _ _ _
  | Pfsqrt _ _
  | Pfrsqrte _ _
  | Pfres _ _
  | Pfsel _ _ _ _
  | Pisel _ _ _ _
  | Plwarx _ _ _
  | Plwbrx _ _ _
  | Picbi _ _
  | Picbtls _ _ _
  | Pisync
  | Pldbrx _ _ _
  | Plwsync
  | Plhbrx _ _ _
  | Plwzu _ _ _
  | Pmbar _
  | Pmfcr _
  | Pmfspr _ _
  | Pmtspr _ _
  | Prldicl _ _ _ _
  | Prldimi _ _ _ _
  | Pstdbrx _ _ _
  | Pstdu _ _ _
  | Pstwbrx _ _ _
  | Pstwcx_ _ _ _
  | Pstfdu _ _ _
  | Psthbrx _ _ _
  | Pstwu _ _ _
  | Pstwux _ _ _
  | Psubfze _ _
  | Psync
  | Ptrap
  | Pcfi_adjust _ =>
      Stuck
  end.

(** Translation of the LTL/Linear/Mach view of machine registers
  to the PPC view.  Note that no LTL register maps to [GPR0].
  This register is reserved as a temporary to be used
  by the generated PPC code.  *)

Definition preg_of (r: mreg) : preg :=
  match r with
  | R3 => GPR3  | R4 => GPR4  | R5 => GPR5  | R6 => GPR6
  | R7 => GPR7  | R8 => GPR8  | R9 => GPR9  | R10 => GPR10
  | R11 => GPR11 | R12 => GPR12
  | R14 => GPR14 | R15 => GPR15 | R16 => GPR16
  | R17 => GPR17 | R18 => GPR18 | R19 => GPR19 | R20 => GPR20
  | R21 => GPR21 | R22 => GPR22 | R23 => GPR23 | R24 => GPR24
  | R25 => GPR25 | R26 => GPR26 | R27 => GPR27 | R28 => GPR28
  | R29 => GPR29 | R30 => GPR30 | R31 => GPR31
  | F0 => FPR0
  | F1 => FPR1  | F2 => FPR2  | F3 => FPR3  | F4 => FPR4
  | F5 => FPR5  | F6 => FPR6  | F7 => FPR7  | F8 => FPR8
  | F9 => FPR9  | F10 => FPR10 | F11 => FPR11 | F12 => FPR12
  | F13 => FPR13 | F14 => FPR14 | F15 => FPR15
  | F16 => FPR16 | F17 => FPR17 | F18 => FPR18 | F19 => FPR19
  | F20 => FPR20 | F21 => FPR21 | F22 => FPR22 | F23 => FPR23
  | F24 => FPR24 | F25 => FPR25 | F26 => FPR26 | F27 => FPR27
  | F28 => FPR28 | F29 => FPR29 | F30 => FPR30 | F31 => FPR31
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
    we use PPC registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr (rs (IR GPR1)) (Ptrofs.repr bofs)) = Some v ->
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
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs GPR1) m args vargs ->
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
        # LR <- Vnullptr
        # GPR1 <- Vnullptr in
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vnullptr ->
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
  red; intros. inv H; simpl.
  omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
(* initial states *)
  inv H; inv H0. f_equal. congruence.
(* final no step *)
  inv H. red; intros; red; intros. inv H; rewrite H0 in *; discriminate.
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
