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

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(** Bits in the condition register. *)

Inductive crbit: Type :=
  | CReq: crbit    (**r equal *)
  | CRne: crbit    (**r not equal *)
  | CRhs: crbit    (**r unsigned higher or same *)
  | CRlo: crbit    (**r unsigned lower *)
  | CRmi: crbit    (**r negative *)
  | CRpl: crbit    (**r positive *)
  | CRhi: crbit    (**r unsigned higher *)
  | CRls: crbit    (**r unsigned lower or same *)
  | CRge: crbit    (**r signed greater or equal *)
  | CRlt: crbit    (**r signed less than *)
  | CRgt: crbit    (**r signed greater *)
  | CRle: crbit.   (**r signed less than or equal *)

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

Notation "'SP'" := IR13 (only parsing).
Notation "'RA'" := IR14 (only parsing).

(** The instruction set.  Most instructions correspond exactly to
  actual instructions of the ARM processor. See the ARM
  reference manuals for more details.  Some instructions,
  described below, are pseudo-instructions: they expand to
  canned instruction sequences during the printing of the assembly
  code. *)

Definition label := positive.

Inductive shift_op : Type :=
  | SOimm: int -> shift_op
  | SOreg: ireg -> shift_op
  | SOlslimm: ireg -> int -> shift_op
  | SOlslreg: ireg -> ireg -> shift_op
  | SOlsrimm: ireg -> int -> shift_op
  | SOlsrreg: ireg -> ireg -> shift_op
  | SOasrimm: ireg -> int -> shift_op
  | SOasrreg: ireg -> ireg -> shift_op
  | SOrorimm: ireg -> int -> shift_op
  | SOrorreg: ireg -> ireg -> shift_op.

Inductive shift_addr : Type :=
  | SAimm: int -> shift_addr
  | SAreg: ireg -> shift_addr
  | SAlsl: ireg -> int -> shift_addr
  | SAlsr: ireg -> int -> shift_addr
  | SAasr: ireg -> int -> shift_addr
  | SAror: ireg -> int -> shift_addr.

Inductive instruction : Type :=
  (* Core instructions *)
  | Padd: ireg -> ireg -> shift_op -> instruction (**r integer addition *)
  | Pand: ireg -> ireg -> shift_op -> instruction (**r bitwise and *)
  | Pb: label -> instruction                      (**r branch to label *)
  | Pbc: crbit -> label -> instruction            (**r conditional branch to label *)
  | Pbsymb: ident -> signature -> instruction                  (**r branch to symbol *)
  | Pbreg: ireg -> signature -> instruction                    (**r computed branch *)
  | Pblsymb: ident -> signature -> instruction                 (**r branch and link to symbol *)
  | Pblreg: ireg -> signature -> instruction                   (**r computed branch and link *)
  | Pbic: ireg -> ireg -> shift_op -> instruction (**r bitwise bit-clear *)
  | Pcmp: ireg -> shift_op -> instruction         (**r integer comparison *)
  | Peor: ireg -> ireg -> shift_op -> instruction (**r bitwise exclusive or *)
  | Pldr: ireg -> ireg -> shift_addr -> instruction (**r int32 load *)
  | Pldrb: ireg -> ireg -> shift_addr -> instruction (**r unsigned int8 load *)
  | Pldrh: ireg -> ireg -> shift_addr -> instruction (**r unsigned int16 load *)
  | Pldrsb: ireg -> ireg -> shift_addr -> instruction (**r signed int8 load *)
  | Pldrsh: ireg -> ireg -> shift_addr -> instruction (**r unsigned int16 load *)
  | Pmov: ireg -> shift_op -> instruction          (**r integer move *)
  | Pmovc: crbit -> ireg -> shift_op -> instruction (**r integer conditional move *)
  | Pmul: ireg -> ireg -> ireg -> instruction      (**r integer multiplication *)
  | Pmvn: ireg -> shift_op -> instruction          (**r integer complement *)
  | Porr: ireg -> ireg -> shift_op -> instruction  (**r bitwise or *)
  | Prsb: ireg -> ireg -> shift_op -> instruction  (**r integer reverse subtraction *)
  | Pstr: ireg -> ireg -> shift_addr -> instruction (**r int32 store *)
  | Pstrb: ireg -> ireg -> shift_addr -> instruction (**r int8 store *)
  | Pstrh: ireg -> ireg -> shift_addr -> instruction (**r int16 store *)
  | Psdiv: ireg -> ireg -> ireg -> instruction      (**r signed division *)
  | Psub: ireg -> ireg -> shift_op -> instruction  (**r integer subtraction *)
  | Pudiv: ireg -> ireg -> ireg -> instruction      (**r unsigned division *)
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
  | Pfcmpzd: freg -> instruction             (**r float comparison with 0.0 *)
  | Pfsitod: freg -> ireg -> instruction            (**r signed int to float *)
  | Pfuitod: freg -> ireg -> instruction            (**r unsigned int to float *)
  | Pftosizd: ireg -> freg -> instruction           (**r float to signed int *)
  | Pftouizd: ireg -> freg -> instruction           (**r float to unsigned int *)
  | Pfcvtsd: freg -> freg -> instruction            (**r round to singled precision *)
  | Pfldd: freg -> ireg -> int -> instruction       (**r float64 load *)
  | Pflds: freg -> ireg -> int -> instruction       (**r float32 load *)
  | Pfstd: freg -> ireg -> int -> instruction       (**r float64 store *)
  | Pfsts: freg -> ireg -> int -> instruction       (**r float32 store *)

  (* Pseudo-instructions *)
  | Pallocframe: Z -> int -> instruction      (**r allocate new stack frame *)
  | Pfreeframe: Z -> int -> instruction       (**r deallocate stack frame and restore previous frame *)
  | Plabel: label -> instruction                   (**r define a code label *)
  | Ploadsymbol: ireg -> ident -> int -> instruction (**r load the address of a symbol *)
  | Pbtbl: ireg -> list label -> instruction       (**r N-way branch through a jump table *)
  | Pbuiltin: external_function -> list preg -> preg -> instruction  (**r built-in function *)
  | Pannot: external_function -> list annot_param -> instruction (**r annotation statement *)

with annot_param : Type :=
  | APreg: preg -> annot_param
  | APstack: memory_chunk -> Z -> annot_param.

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
  rs#PC <- (Val.add rs#PC Vone).

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Int.repr pos))) m
      | _ => Stuck
    end
  end.

(** Evaluation of [shift_op] operands *)

Definition eval_shift_op (so: shift_op) (rs: regset) :=
  match so with
  | SOimm n => Vint n
  | SOreg r => rs r
  | SOlslimm r n => Val.shl (rs r) (Vint n)
  | SOlslreg r r' => Val.shl (rs r) (rs r')
  | SOlsrimm r n => Val.shru (rs r) (Vint n)
  | SOlsrreg r r' => Val.shru (rs r) (rs r')
  | SOasrimm r n => Val.shr (rs r) (Vint n)
  | SOasrreg r r' => Val.shr (rs r) (rs r')
  | SOrorimm r n => Val.ror (rs r) (Vint n)
  | SOrorreg r r' => Val.ror (rs r) (rs r')
  end.

(** Evaluation of [shift_addr] operands *)

Definition eval_shift_addr (sa: shift_addr) (rs: regset) :=
  match sa with
  | SAimm n => Vint n
  | SAreg r => rs r
  | SAlsl r n => Val.shl (rs r) (Vint n)
  | SAlsr r n => Val.shru (rs r) (Vint n)
  | SAasr r n => Val.shr (rs r) (Vint n)
  | SAror r n => Val.ror (rs r) (Vint n)
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

(** Operations over condition bits. *)

Definition compare_int (rs: regset) (v1 v2: val) (m: mem) :=
  rs#CReq <- (Val.cmpu (Mem.valid_pointer m) Ceq v1 v2)
    #CRne <- (Val.cmpu (Mem.valid_pointer m) Cne v1 v2)
    #CRhs <- (Val.cmpu (Mem.valid_pointer m) Cge v1 v2)
    #CRlo <- (Val.cmpu (Mem.valid_pointer m) Clt v1 v2)
    #CRmi <- Vundef
    #CRpl <- Vundef
    #CRhi <- (Val.cmpu (Mem.valid_pointer m) Cgt v1 v2)
    #CRls <- (Val.cmpu (Mem.valid_pointer m) Cle v1 v2)
    #CRge <- (Val.cmp Cge v1 v2)
    #CRlt <- (Val.cmp Clt v1 v2)
    #CRgt <- (Val.cmp Cgt v1 v2)
    #CRle <- (Val.cmp Cle v1 v2).

(** Semantics of [fcmpd] instruction:
<<
==	EQ=1 NE=0 HS=1 LO=0 MI=0 PL=1 VS=0 VC=1 HI=0 LS=1 GE=1 LT=0 GT=0 LE=1 
<	EQ=0 NE=1 HS=0 LO=1 MI=1 PL=0 VS=0 VC=1 HI=0 LS=1 GE=0 LT=1 GT=0 LE=1 
>	EQ=0 NE=1 HS=1 LO=0 MI=0 PL=1 VS=0 VC=1 HI=1 LS=0 GE=1 LT=0 GT=1 LE=0 
unord	EQ=0 NE=1 HS=1 LO=0 MI=0 PL=1 VS=1 VC=0 HI=1 LS=0 GE=0 LT=1 GT=0 LE=1 
>>
*)

Definition compare_float (rs: regset) (v1 v2: val) :=
  rs#CReq <- (Val.cmpf Ceq v1 v2)
    #CRne <- (Val.cmpf Cne v1 v2)
    #CRhs <- (Val.notbool (Val.cmpf Clt v1 v2))      (**r not lt *)
    #CRlo <- (Val.cmpf Clt v1 v2)                    (**r lt *)
    #CRmi <- (Val.cmpf Clt v1 v2)                    (**r lt *)
    #CRpl <- (Val.notbool (Val.cmpf Clt v1 v2))      (**r not lt *)
    #CRhi <- (Val.notbool (Val.cmpf Cle v1 v2))      (**r not le *)
    #CRls <- (Val.cmpf Cle v1 v2)                    (**r le *)
    #CRge <- (Val.cmpf Cge v1 v2)                    (**r ge *)
    #CRlt <- (Val.notbool (Val.cmpf Cge v1 v2))      (**r not ge *)
    #CRgt <- (Val.cmpf Cgt v1 v2)                    (**r gt *)
    #CRle <- (Val.notbool (Val.cmpf Cgt v1 v2)).     (**r not gt *)

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

Definition symbol_offset (id: ident) (ofs: int) : val :=
  match Genv.find_symbol ge id with
  | Some b => Vptr b ofs
  | None => Vundef
  end.

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  | Padd r1 r2 so => 
      Next (nextinstr (rs#r1 <- (Val.add rs#r2 (eval_shift_op so rs)))) m
  | Pand r1 r2 so => 
      Next (nextinstr (rs#r1 <- (Val.and rs#r2 (eval_shift_op so rs)))) m
  | Pb lbl =>                      
      goto_label f lbl rs m
  | Pbc bit lbl =>            
      match rs#bit with
      | Vint n => if Int.eq n Int.zero then Next (nextinstr rs) m else goto_label f lbl rs m
      | _ => Stuck
      end
  | Pbsymb id sg =>                  
      Next (rs#PC <- (symbol_offset id Int.zero)) m
  | Pbreg r sg =>                    
      Next (rs#PC <- (rs#r)) m
  | Pblsymb id sg =>                 
      Next (rs#IR14 <- (Val.add rs#PC Vone) #PC <- (symbol_offset id Int.zero)) m
  | Pblreg r sg =>                   
      Next (rs#IR14 <- (Val.add rs#PC Vone) #PC <- (rs#r)) m
  | Pbic r1 r2 so => 
      Next (nextinstr (rs#r1 <- (Val.and rs#r2 (Val.notint (eval_shift_op so rs))))) m
  | Pcmp r1 so => 
      Next (nextinstr (compare_int rs rs#r1 (eval_shift_op so rs) m)) m
  | Peor r1 r2 so => 
      Next (nextinstr (rs#r1 <- (Val.xor rs#r2 (eval_shift_op so rs)))) m
  | Pldr r1 r2 sa => 
      exec_load Mint32 (Val.add rs#r2 (eval_shift_addr sa rs)) r1 rs m
  | Pldrb r1 r2 sa => 
      exec_load Mint8unsigned (Val.add rs#r2 (eval_shift_addr sa rs)) r1 rs m
  | Pldrh r1 r2 sa => 
      exec_load Mint16unsigned (Val.add rs#r2 (eval_shift_addr sa rs)) r1 rs m
  | Pldrsb r1 r2 sa => 
      exec_load Mint8signed (Val.add rs#r2 (eval_shift_addr sa rs)) r1 rs m
  | Pldrsh r1 r2 sa => 
      exec_load Mint16signed (Val.add rs#r2 (eval_shift_addr sa rs)) r1 rs m
  | Pmov r1 so =>          
      Next (nextinstr (rs#r1 <- (eval_shift_op so rs))) m
  | Pmovc bit r1 so =>          
      match rs#bit with
      | Vint n => if Int.eq n Int.zero 
                  then Next (nextinstr rs) m
                  else Next (nextinstr (rs#r1 <- (eval_shift_op so rs))) m
      | _ => Next (nextinstr (rs#r1 <- Vundef)) m
      end
  | Pmul r1 r2 r3 =>      
      Next (nextinstr (rs#r1 <- (Val.mul rs#r2 rs#r3))) m
  | Pmvn r1 so =>          
      Next (nextinstr (rs#r1 <- (Val.notint (eval_shift_op so rs)))) m
  | Porr r1 r2 so =>  
      Next (nextinstr (rs#r1 <- (Val.or rs#r2 (eval_shift_op so rs)))) m
  | Prsb r1 r2 so =>  
      Next (nextinstr (rs#r1 <- (Val.sub (eval_shift_op so rs) rs#r2))) m
  | Pstr r1 r2 sa => 
      exec_store Mint32 (Val.add rs#r2 (eval_shift_addr sa rs)) r1 rs m
  | Pstrb r1 r2 sa => 
      exec_store Mint8unsigned (Val.add rs#r2 (eval_shift_addr sa rs)) r1 rs m
  | Pstrh r1 r2 sa => 
      exec_store Mint16unsigned (Val.add rs#r2 (eval_shift_addr sa rs)) r1 rs m
  | Psdiv rd r1 r2 =>
      match Val.divs rs#r1 rs#r2 with
      | Some v => Next (nextinstr (rs#rd <- v)) m
      | None => Stuck
      end
  | Psub r1 r2 so =>  
      Next (nextinstr (rs#r1 <- (Val.sub rs#r2 (eval_shift_op so rs)))) m
  | Pudiv rd r1 r2 =>
      match Val.divu rs#r1 rs#r2 with
      | Some v => Next (nextinstr (rs#rd <- v)) m
      | None => Stuck
      end
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
      Next (nextinstr (rs#r1 <- (Val.maketotal (Val.intoffloat rs#r2)))) m
  | Pftouizd r1 r2 =>
      Next (nextinstr (rs#r1 <- (Val.maketotal (Val.intuoffloat rs#r2)))) m
  | Pfcvtsd r1 r2 =>
      Next (nextinstr (rs#r1 <- (Val.singleoffloat rs#r2))) m
  | Pfldd r1 r2 n =>
      exec_load Mfloat64al32 (Val.add rs#r2 (Vint n)) r1 rs m
  | Pflds r1 r2 n =>
      exec_load Mfloat32 (Val.add rs#r2 (Vint n)) r1 rs m
  | Pfstd r1 r2 n =>      
      exec_store Mfloat64al32 (Val.add rs#r2 (Vint n)) r1 rs m
  | Pfsts r1 r2 n =>
      match exec_store Mfloat32 (Val.add rs#r2 (Vint n)) r1 rs m with
      | Next rs' m' => Next (rs'#FR7 <- Vundef) m'
      | Stuck => Stuck
      end
  (* Pseudo-instructions *)
  | Pallocframe sz pos =>             
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := (Vptr stk Int.zero) in
      match Mem.storev Mint32 m1 (Val.add sp (Vint pos)) rs#IR13 with
      | None => Stuck
      | Some m2 => Next (nextinstr (rs #IR10 <- (rs#IR13) #IR13 <- sp)) m2
      end
  | Pfreeframe sz pos =>
      match Mem.loadv Mint32 m (Val.add rs#IR13 (Vint pos)) with
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
      Next (nextinstr (rs#r1 <- (symbol_offset lbl ofs))) m
  | Pbtbl r tbl =>
      match rs#r with
      | Vint n => 
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs#IR14 <- Vundef) m
          end
      | _ => Stuck
      end
  | Pbuiltin ef args res => Stuck    (**r treated specially below *)
  | Pannot ef args => Stuck          (**r treated specially below *)
  end.

(** Translation of the LTL/Linear/Mach view of machine registers
  to the ARM view.  Note that no LTL register maps to [IR14].
  This register is reserved as temporary, to be used
  by the generated ARM code.  *)

Definition preg_of (r: mreg) : preg :=
  match r with
  | R0 => IR0 | R1 => IR1 | R2 => IR2 | R3 => IR3
  | R4 => IR4 | R5 => IR5 | R6 => IR6 | R7 => IR7
  | R8 => IR8 | R9 => IR9 | R11 => IR11
  | IT1 => IR10 | IT2 => IR12
  | F0 => FR0 | F1 => FR1 | F2 => FR2 | F3 => FR3
  | F4 => FR4 | F5 => FR5
  | F8 => FR8 | F9 => FR9 | F10 => FR10 | F11 => FR11
  | F12 => FR12 | F13 => FR13 | F14 => FR14 | F15 => FR15
  | FT1 => FR6 | FT2 => FR7
  end.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use ARM registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_int_stack: forall ofs bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv Mint32 m (Val.add (rs (IR IR13)) (Vint (Int.repr bofs))) = Some v ->
      extcall_arg rs m (S (Outgoing ofs Tint)) v
  | extcall_arg_float_stack: forall ofs bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv Mfloat64al32 m (Val.add (rs (IR IR13)) (Vint (Int.repr bofs))) = Some v ->
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
      rs (IR IR13) = Vptr stk base ->
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
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m t v m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some (Pbuiltin ef args res) ->
      external_call ef ge (map rs args) m t v m' ->
      step (State rs m) t (State (nextinstr(rs # res <- v)) m')
  | exec_step_annot:
      forall b ofs f ef args rs m vargs t v m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some (Pannot ef args) ->
      annot_arguments rs m args vargs ->
      external_call ef ge vargs m t v m' ->
      step (State rs m) t (State (nextinstr rs) m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (rs#(loc_external_result (ef_sig ef)) <- res
               #PC <- (rs IR14)) ->
      step (State rs m) t (State rs' m').

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (symbol_offset ge p.(prog_main) Int.zero)
        # IR14 <- Vzero
        # IR13 <- (Vptr Mem.nullptr Int.zero) in
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
  red; intros; inv H; simpl.
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
  | IR IR14 => false
  | IR _ => true
  | FR _ => true
  | CR _ => false
  | PC => false
  end.

Definition nontemp_preg (r: preg) : bool :=
  match r with
  | IR IR14 => false
  | IR IR10 => false
  | IR IR12 => false
  | IR _ => true
  | FR FR6 => false
  | FR FR7 => false
  | FR _ => true
  | CR _ => false
  | PC => false
  end.
