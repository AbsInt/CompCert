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
  | FR4: freg  | FR5: freg  | FR6: freg  | FR7: freg.

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
  | FR: freg -> preg                    (**r float registers *)
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

(** The instruction set.  Most instructions correspond exactly to
  actual instructions of the PowerPC processor. See the PowerPC
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
  | Pbsymb: ident -> instruction                  (**r branch to symbol *)
  | Pbreg: ireg -> instruction                    (**r computed branch *)
  | Pblsymb: ident -> instruction                 (**r branch and link to symbol *)
  | Pblreg: ireg -> instruction                   (**r computed branch and link *)
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
  (* Floating-point coprocessor instructions *)
  | Pabsd: freg -> freg -> instruction             (**r float absolute value *)
  | Padfd: freg -> freg -> freg -> instruction     (**r float addition *)
  | Pcmf: freg -> freg -> instruction              (**r float comparison *)
  | Pdvfd: freg -> freg -> freg -> instruction     (**r float division *)
  | Pfixz: ireg -> freg -> instruction             (**r float to signed int *)
  | Pfltd: freg -> ireg -> instruction             (**r signed int to float *)
  | Pldfd: freg -> ireg -> int -> instruction      (**r float64 load *)
  | Pldfs: freg -> ireg -> int -> instruction      (**r float32 load *)
  | Plifd: freg -> float -> instruction            (**r load float constant *)
  | Pmnfd: freg -> freg -> instruction             (**r float opposite *)
  | Pmvfd: freg -> freg -> instruction             (**r float move *)
  | Pmvfs: freg -> freg -> instruction             (**r float move single precision *)
  | Pmufd: freg -> freg -> freg -> instruction     (**r float multiplication *)
  | Pstfd: freg -> ireg -> int -> instruction      (**r float64 store *)
  | Pstfs: freg -> ireg -> int -> instruction      (**r float32 store *)
  | Psufd: freg -> freg -> freg -> instruction     (**r float subtraction *)

  (* Pseudo-instructions *)
  | Pallocframe: Z -> Z -> int -> instruction      (**r allocate new stack frame *)
  | Pfreeframe: Z -> Z -> int -> instruction       (**r deallocate stack frame and restore previous frame *)
  | Plabel: label -> instruction                   (**r define a code label *)
  | Ploadsymbol: ireg -> ident -> int -> instruction (**r load the address of a symbol *)
  | Pbtbl: ireg -> list label -> instruction       (**r N-way branch through a jump table *)
  | Pbuiltin: external_function -> list preg -> preg -> instruction. (**r built-in *)

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
- [Pallocframe lo hi pos]: in the formal semantics, this pseudo-instruction
  allocates a memory block with bounds [lo] and [hi], stores the value
  of the stack pointer at offset [pos] in this block, and sets the
  stack pointer to the address of the bottom of this block.
  In the printed ASM assembly code, this allocation is:
<<
        mov     r12, sp
        sub     sp, sp, #(hi - lo)
        str     r12, [sp, #pos]
>>
  This cannot be expressed in our memory model, which does not reflect
  the fact that stack frames are adjacent and allocated/freed
  following a stack discipline.
- [Pfreeframe pos]: in the formal semantics, this pseudo-instruction
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
Definition fundef := AST.fundef code.
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
  to either [OK rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Error] if the processor is stuck. *)

Inductive outcome: Type :=
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
  | None => Error
  | Some v => OK (nextinstr (rs#r <- v)) m
  end.

Definition exec_store (chunk: memory_chunk) (addr: val) (r: preg)
                      (rs: regset) (m: mem) :=
  match Mem.storev chunk m addr (rs r) with
  | None => Error
  | Some m' => OK (nextinstr rs) m'
  end.

(** Operations over condition bits. *)

Definition compare_int (rs: regset) (v1 v2: val) :=
  rs#CReq <- (Val.cmp Ceq v1 v2)
    #CRne <- (Val.cmp Cne v1 v2)
    #CRhs <- (Val.cmpu Cge v1 v2)
    #CRlo <- (Val.cmpu Clt v1 v2)
    #CRmi <- Vundef
    #CRpl <- Vundef
    #CRhi <- (Val.cmpu Cgt v1 v2)
    #CRls <- (Val.cmpu Cle v1 v2)
    #CRge <- (Val.cmp Cge v1 v2)
    #CRlt <- (Val.cmp Clt v1 v2)
    #CRgt <- (Val.cmp Cgt v1 v2)
    #CRle <- (Val.cmp Cle v1 v2).

Definition compare_float (rs: regset) (v1 v2: val) :=
  rs#CReq <- (Val.cmpf Ceq v1 v2)
    #CRne <- (Val.cmpf Cne v1 v2)
    #CRhs <- Vundef
    #CRlo <- Vundef
    #CRmi <- (Val.cmpf Clt v1 v2)                    (* lt *)
    #CRpl <- (Val.notbool (Val.cmpf Clt v1 v2))      (* not lt *)
    #CRhi <- (Val.notbool (Val.cmpf Cle v1 v2))      (* not le *)
    #CRls <- (Val.cmpf Cle v1 v2)                    (* le *)
    #CRge <- (Val.cmpf Cge v1 v2)                    (* ge *)
    #CRlt <- (Val.notbool (Val.cmpf Cge v1 v2))      (* not ge *)
    #CRgt <- (Val.cmpf Cgt v1 v2)                    (* gt *)
    #CRle <- (Val.notbool (Val.cmpf Cgt v1 v2)).     (* not gt *)

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

Definition exec_instr (c: code) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  | Padd r1 r2 so => 
      OK (nextinstr (rs#r1 <- (Val.add rs#r2 (eval_shift_op so rs)))) m
  | Pand r1 r2 so => 
      OK (nextinstr (rs#r1 <- (Val.and rs#r2 (eval_shift_op so rs)))) m
  | Pb lbl =>                      
      goto_label c lbl rs m
  | Pbc bit lbl =>            
      match rs#bit with
      | Vint n => if Int.eq n Int.zero then OK (nextinstr rs) m else goto_label c lbl rs m
      | _ => Error
      end
  | Pbsymb id =>                  
      OK (rs#PC <- (symbol_offset id Int.zero)) m
  | Pbreg r =>                    
      OK (rs#PC <- (rs#r)) m
  | Pblsymb id =>                 
      OK (rs#IR14 <- (Val.add rs#PC Vone) #PC <- (symbol_offset id Int.zero)) m
  | Pblreg r =>                   
      OK (rs#IR14 <- (Val.add rs#PC Vone) #PC <- (rs#r)) m
  | Pbic r1 r2 so => 
      OK (nextinstr (rs#r1 <- (Val.and rs#r2 (Val.notint (eval_shift_op so rs))))) m
  | Pcmp r1 so => 
      OK (nextinstr (compare_int rs rs#r1 (eval_shift_op so rs))) m
  | Peor r1 r2 so => 
      OK (nextinstr (rs#r1 <- (Val.xor rs#r2 (eval_shift_op so rs)))) m
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
      OK (nextinstr (rs#r1 <- (eval_shift_op so rs))) m
  | Pmovc bit r1 so =>          
      match rs#bit with
      | Vint n => if Int.eq n Int.zero 
                  then OK (nextinstr rs) m
                  else OK (nextinstr (rs#r1 <- (eval_shift_op so rs))) m
      | _ => Error
      end
  | Pmul r1 r2 r3 =>      
      OK (nextinstr (rs#r1 <- (Val.mul rs#r2 rs#r3))) m
  | Pmvn r1 so =>          
      OK (nextinstr (rs#r1 <- (Val.notint (eval_shift_op so rs)))) m
  | Porr r1 r2 so =>  
      OK (nextinstr (rs#r1 <- (Val.or rs#r2 (eval_shift_op so rs)))) m
  | Prsb r1 r2 so =>  
      OK (nextinstr (rs#r1 <- (Val.sub (eval_shift_op so rs) rs#r2))) m
  | Pstr r1 r2 sa => 
      exec_store Mint32 (Val.add rs#r2 (eval_shift_addr sa rs)) r1 rs m
  | Pstrb r1 r2 sa => 
      exec_store Mint8unsigned (Val.add rs#r2 (eval_shift_addr sa rs)) r1 rs m
  | Pstrh r1 r2 sa => 
      exec_store Mint16unsigned (Val.add rs#r2 (eval_shift_addr sa rs)) r1 rs m
  | Psdiv rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.divs rs#r1 rs#r2))) m
  | Psub r1 r2 so =>  
      OK (nextinstr (rs#r1 <- (Val.sub rs#r2 (eval_shift_op so rs)))) m
  | Pudiv rd r1 r2 =>
      OK (nextinstr (rs#rd <- (Val.divu rs#r1 rs#r2))) m
  (* Floating-point coprocessor instructions *)
  | Pabsd r1 r2 => 
      OK (nextinstr (rs#r1 <- (Val.absf rs#r2))) m
  | Padfd r1 r2 r3 =>     
      OK (nextinstr (rs#r1 <- (Val.addf rs#r2 rs#r3))) m
  | Pcmf r1 r2 =>              
      OK (nextinstr (compare_float rs rs#r1 rs#r2)) m
  | Pdvfd r1 r2 r3 =>     
      OK (nextinstr (rs#r1 <- (Val.divf rs#r2 rs#r3))) m
  | Pfixz r1 r2 =>
      OK (nextinstr (rs#r1 <- (Val.intoffloat rs#r2))) m
  | Pfltd r1 r2 =>
      OK (nextinstr (rs#r1 <- (Val.floatofint rs#r2))) m
  | Pldfd r1 r2 n =>
      exec_load Mfloat64 (Val.add rs#r2 (Vint n)) r1 rs m
  | Pldfs r1 r2 n =>
      exec_load Mfloat32 (Val.add rs#r2 (Vint n)) r1 rs m
  | Plifd r1 f =>            
      OK (nextinstr (rs#r1 <- (Vfloat f))) m
  | Pmnfd r1 r2 => 
      OK (nextinstr (rs#r1 <- (Val.negf rs#r2))) m
  | Pmvfd r1 r2 =>
      OK (nextinstr (rs#r1 <- (rs#r2))) m
  | Pmvfs r1 r2 =>
      OK (nextinstr (rs#r1 <- (Val.singleoffloat rs#r2))) m
  | Pmufd r1 r2 r3 =>     
      OK (nextinstr (rs#r1 <- (Val.mulf rs#r2 rs#r3))) m
  | Pstfd r1 r2 n =>      
      exec_store Mfloat64 (Val.add rs#r2 (Vint n)) r1 rs m
  | Pstfs r1 r2 n =>
      match exec_store Mfloat32 (Val.add rs#r2 (Vint n)) r1 rs m with
      | OK rs' m' => OK (rs'#FR3 <- Vundef) m'
      | Error => Error
      end
  | Psufd r1 r2 r3 =>     
      OK (nextinstr (rs#r1 <- (Val.subf rs#r2 rs#r3))) m
  (* Pseudo-instructions *)
  | Pallocframe lo hi pos =>             
      let (m1, stk) := Mem.alloc m lo hi in
      let sp := (Vptr stk (Int.repr lo)) in
      match Mem.storev Mint32 m1 (Val.add sp (Vint pos)) rs#IR13 with
      | None => Error
      | Some m2 => OK (nextinstr (rs#IR13 <- sp)) m2
      end
  | Pfreeframe lo hi pos =>
      match Mem.loadv Mint32 m (Val.add rs#IR13 (Vint pos)) with
      | None => Error
      | Some v =>
          match rs#IR13 with
          | Vptr stk ofs =>
              match Mem.free m stk lo hi with
              | None => Error
              | Some m' => OK (nextinstr (rs#IR13 <- v)) m'
              end
          | _ => Error
          end
      end
  | Plabel lbl =>
      OK (nextinstr rs) m
  | Ploadsymbol r1 lbl ofs =>
      OK (nextinstr (rs#r1 <- (symbol_offset lbl ofs))) m
  | Pbtbl r tbl =>
      match rs#r with
      | Vint n => 
          let pos := Int.signed n in
          if zeq (Zmod pos 4) 0 then
            match list_nth_z tbl (pos / 4) with
            | None => Error
            | Some lbl => goto_label c lbl rs m
            end
          else Error
      | _ => Error
      end
  | Pbuiltin ef args res => Error    (**r treated specially below *)
  end.

(** Translation of the LTL/Linear/Mach view of machine registers
  to the ARM view.  ARM has two different types for registers
  (integer and float) while LTL et al have only one.  The
  [ireg_of] and [freg_of] are therefore partial in principle.
  To keep things simpler, we make them return nonsensical
  results when applied to a LTL register of the wrong type.
  The proof in [ARMgenproof] will show that this never happens.

  Note that no LTL register maps to [IR14].
  This register is reserved as temporary, to be used
  by the generated ARM code.  *)

Definition ireg_of (r: mreg) : ireg :=
  match r with
  | R0 => IR0 | R1 => IR1 | R2 => IR2 | R3 => IR3
  | R4 => IR4 | R5 => IR5 | R6 => IR6 | R7 => IR7
  | R8 => IR8 | R9 => IR9 | R11 => IR11
  | IT1 => IR10 | IT2 => IR12
  | _ => IR0  (* should not happen *)
  end.

Definition freg_of (r: mreg) : freg :=
  match r with
  | F0 => FR0 | F1 => FR1
  | F4 => FR4 | F5 => FR5 | F6 => FR6 | F7 => FR7
  | FT1 => FR2 | FT2 => FR3
  | _ => FR0  (* should not happen *)
  end.

Definition preg_of (r: mreg) :=
  match mreg_type r with
  | Tint => IR (ireg_of r)
  | Tfloat => FR (freg_of r)
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
      Mem.loadv Mfloat64 m (Val.add (rs (IR IR13)) (Vint (Int.repr bofs))) = Some v ->
      extcall_arg rs m (S (Outgoing ofs Tfloat)) v.

Inductive extcall_args (rs: regset) (m: mem): list loc -> list val -> Prop :=
  | extcall_args_nil:
      extcall_args rs m nil nil
  | extcall_args_cons: forall l1 ll v1 vl,
      extcall_arg rs m l1 v1 -> extcall_args rs m ll vl ->
      extcall_args rs m (l1 :: ll) (v1 :: vl).

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  extcall_args rs m (loc_arguments sg) args.

Definition loc_external_result (sg: signature) : preg :=
  preg_of (loc_result sg).

(** Execution of the instruction at [rs#PC]. *)

Inductive state: Type :=
  | State: regset -> mem -> state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs c i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal c) ->
      find_instr (Int.unsigned ofs) c = Some i ->
      exec_instr c i rs m = OK rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs c ef args res rs m t v m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal c) ->
      find_instr (Int.unsigned ofs) c = Some (Pbuiltin ef args res) ->
      external_call ef ge (map rs args) m t v m' ->
      step (State rs m) t (State (nextinstr(rs # res <- v)) m')
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
      
Definition exec_program (p: program) (beh: program_behavior) : Prop :=
  program_behaves step (initial_state p) final_state (Genv.globalenv p) beh.
