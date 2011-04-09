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

(** ** Registers. *)

(** Integer registers. *)

Inductive ireg: Type :=
  | EAX: ireg  | EBX: ireg  | ECX: ireg  | EDX: ireg
  | ESI: ireg  | EDI: ireg  | EBP: ireg  | ESP: ireg.

(** Floating-point registers, i.e. SSE2 registers *)

Inductive freg: Type :=
  | XMM0: freg  | XMM1: freg  | XMM2: freg  | XMM3: freg
  | XMM4: freg  | XMM5: freg  | XMM6: freg  | XMM7: freg.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(** Bits of the flags register.  [SOF] is a pseudo-bit representing
  the "xor" of the [OF] and [SF] bits. *)

Inductive crbit: Type := 
  | ZF | CF | PF | SOF.

(** All registers modeled here. *)

Inductive preg: Type :=
  | PC: preg                            (**r program counter *)
  | IR: ireg -> preg                    (**r integer register *)
  | FR: freg -> preg                    (**r XMM register *)
  | ST0: preg                           (**r top of FP stack *)
  | CR: crbit -> preg                   (**r bit of the flags register *)
  | RA: preg.                   (**r pseudo-reg representing return address *)

Coercion IR: ireg >-> preg.
Coercion FR: freg >-> preg.
Coercion CR: crbit >-> preg.

(** ** Instruction set. *)

Definition label := positive.

(** General form of an addressing mode. *)

Inductive addrmode: Type :=
  | Addrmode (base: option ireg)
             (ofs: option (ireg * int))
             (const: int + ident * int).

(** Testable conditions (for conditional jumps and more). *)

Inductive testcond: Type :=
  | Cond_e | Cond_ne
  | Cond_b | Cond_be | Cond_ae | Cond_a
  | Cond_l | Cond_le | Cond_ge | Cond_g
  | Cond_p | Cond_np
  | Cond_nep                            (**r synthetic: P or (not Z) *)
  | Cond_enp.                           (**r synthetic: (not P) and Z *)

(** Instructions.  IA32 instructions accept many combinations of
  registers, memory references and immediate constants as arguments.
  Here, we list only the combinations that we actually use.

  Naming conventions:
- [r]: integer register operand
- [f]: XMM register operand
- [m]: memory operand
- [i]: immediate integer operand
- [s]: immediate symbol operand
- [l]: immediate label operand
- [cl]: the [CL] register

  For two-operand instructions, the first suffix describes the result
  (and first argument), the second suffix describes the second argument.
*)

Inductive instruction: Type :=
  (** Moves *)
  | Pmov_rr (rd: ireg) (r1: ireg)       (**r [mov] (32-bit int) *)
  | Pmov_ri (rd: ireg) (n: int)
  | Pmov_rm (rd: ireg) (a: addrmode)
  | Pmov_mr (a: addrmode) (rs: ireg)
  | Pmovd_fr (rd: freg) (r1: ireg)      (**r [movd] (32-bit int) *)
  | Pmovd_rf (rd: ireg) (rd: freg)
  | Pmovsd_ff (rd: freg) (r1: freg)     (**r [movsd] (single 64-bit float) *)
  | Pmovsd_fi (rd: freg) (n: float)     (**r (pseudo-instruction) *)
  | Pmovsd_fm (rd: freg) (a: addrmode)
  | Pmovsd_mf (a: addrmode) (r1: freg)
  | Pfld_f (r1: freg)                   (**r [fld] from XMM register (pseudo) *)
  | Pfld_m (a: addrmode)                (**r [fld] from memory *)
  | Pfstp_f (rd: freg)                  (**r [fstp] to XMM register (pseudo) *)
  | Pfstp_m (a: addrmode)               (**r [fstp] to memory *)
  (** Moves with conversion *)
  | Pmovb_mr (a: addrmode) (rs: ireg)   (**r [mov] (8-bit int) *)
  | Pmovw_mr (a: addrmode) (rs: ireg)   (**r [mov] (16-bit int) *)
  | Pmovzb_rr (rd: ireg) (rs: ireg)    (**r [movzb] (8-bit zero-extension) *)
  | Pmovzb_rm (rd: ireg) (a: addrmode)
  | Pmovsb_rr (rd: ireg) (rs: ireg)    (**r [movsb] (8-bit sign-extension) *)
  | Pmovsb_rm (rd: ireg) (a: addrmode)
  | Pmovzw_rr (rd: ireg) (rs: ireg)    (**r [movzw] (16-bit zero-extension) *)
  | Pmovzw_rm (rd: ireg) (a: addrmode)
  | Pmovsw_rr (rd: ireg) (rs: ireg)    (**r [movsw] (16-bit sign-extension) *)
  | Pmovsw_rm (rd: ireg) (a: addrmode)
  | Pcvtss2sd_fm (rd: freg) (a: addrmode) (**r [cvtss2sd] (single float load) *)
  | Pcvtsd2ss_ff (rd: freg) (r1: freg) (**r pseudo (single conversion) *)
  | Pcvtsd2ss_mf (a: addrmode) (r1: freg) (**r [cvtsd2ss] (single float store *)
  | Pcvttsd2si_rf (rd: ireg) (r1: freg) (**r double to signed int *)
  | Pcvtsi2sd_fr (rd: freg) (r1: ireg)  (**r signed int to double *)
  (** Integer arithmetic *)
  | Plea (rd: ireg) (a: addrmode)
  | Pneg (rd: ireg)
  | Psub_rr (rd: ireg) (r1: ireg)
  | Pimul_rr (rd: ireg) (r1: ireg)
  | Pimul_ri (rd: ireg) (n: int)
  | Pdiv (r1: ireg)
  | Pidiv (r1: ireg)
  | Pand_rr (rd: ireg) (r1: ireg)
  | Pand_ri (rd: ireg) (n: int)
  | Por_rr (rd: ireg) (r1: ireg)
  | Por_ri (rd: ireg) (n: int)
  | Pxor_rr (rd: ireg) (r1: ireg)
  | Pxor_ri (rd: ireg) (n: int)
  | Psal_rcl (rd: ireg)
  | Psal_ri (rd: ireg) (n: int)
  | Pshr_rcl (rd: ireg)
  | Pshr_ri (rd: ireg) (n: int)
  | Psar_rcl (rd: ireg)
  | Psar_ri (rd: ireg) (n: int)
  | Pror_ri (rd: ireg) (n: int)
  | Pcmp_rr (r1 r2: ireg) 
  | Pcmp_ri (r1: ireg) (n: int)
  | Ptest_rr (r1 r2: ireg)
  | Ptest_ri (r1: ireg) (n: int)
  | Pcmov (c: testcond) (rd: ireg) (r1: ireg)
  | Psetcc (c: testcond) (rd: ireg)
  (** Floating-point arithmetic *)
  | Paddd_ff (rd: freg) (r1: freg)
  | Psubd_ff (rd: freg) (r1: freg)
  | Pmuld_ff (rd: freg) (r1: freg)
  | Pdivd_ff (rd: freg) (r1: freg)
  | Pnegd (rd: freg)
  | Pabsd (rd: freg)
  | Pcomisd_ff (r1 r2: freg)
  (** Branches and calls *)
  | Pjmp_l (l: label)
  | Pjmp_s (symb: ident)
  | Pjmp_r (r: ireg)
  | Pjcc (c: testcond)(l: label)
  | Pjmptbl (r: ireg) (tbl: list label) (**r pseudo *)
  | Pcall_s (symb: ident)
  | Pcall_r (r: ireg)
  | Pret
  (** Pseudo-instructions *)
  | Plabel(l: label)
  | Pallocframe(sz: Z)(ofs_ra ofs_link: int)
  | Pfreeframe(sz: Z)(ofs_ra ofs_link: int)
  | Pbuiltin(ef: external_function)(args: list preg)(res: preg).

Definition code := list instruction.
Definition fundef := AST.fundef code.
Definition program := AST.program fundef unit.

(** * Operational semantics *)

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. apply freg_eq. decide equality. Defined.

Module PregEq.
  Definition t := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

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

Definition symbol_offset (id: ident) (ofs: int) : val :=
  match Genv.find_symbol ge id with
  | Some b => Vptr b ofs
  | None => Vundef
  end.

(** Evaluating an addressing mode *)

Definition eval_addrmode (a: addrmode) (rs: regset) : val :=
  match a with Addrmode base ofs const =>
    Val.add (match base with
              | None => Vzero
              | Some r => rs r
             end)
    (Val.add (match ofs with
              | None => Vzero
              | Some(r, sc) =>
                  if Int.eq sc Int.one then rs r else Val.mul (rs r) (Vint sc)
              end)
             (match const with
              | inl ofs => Vint ofs
              | inr(id, ofs) => symbol_offset id ofs
              end))
  end.

(** Performing a comparison *)

(** Integer comparison between x and y:
-       ZF = 1 if x = y, 0 if x != y
-       CF = 1 if x <u y, 0 if x >=u y
-       SOF = 1 if x <s y, 0 if x >=s y
-       PF is undefined

SOF is (morally) the XOR of the SF and OF flags of the processor. *)

Definition compare_ints (x y: val) (rs: regset) : regset :=
  rs #ZF  <- (Val.cmp Ceq x y)
     #CF  <- (Val.cmpu Clt x y)
     #SOF <- (Val.cmp Clt x y)
     #PF  <- Vundef.

(** Floating-point comparison between x and y:
-       ZF = 1 if x=y or unordered, 0 if x<>y
-       CF = 1 if x<y or unordered, 0 if x>=y
-       PF = 1 if unordered, 0 if ordered.
-       SOF is undefined
*)

Definition compare_floats (vx vy: val) (rs: regset) : regset :=
  match vx, vy with
  | Vfloat x, Vfloat y =>
      rs #ZF  <- (Val.of_bool (negb (Float.cmp Cne x y)))
         #CF  <- (Val.of_bool (negb (Float.cmp Cge x y)))
         #PF  <- (Val.of_bool (negb (Float.cmp Ceq x y || Float.cmp Clt x y || Float.cmp Cgt x y)))
         #SOF <- Vundef
  | _, _ =>
      undef_regs (CR ZF :: CR CF :: CR PF :: CR SOF :: nil) rs
  end.

(** Testing a condition *)

Definition eval_testcond (c: testcond) (rs: regset) : option bool :=
  match c with
  | Cond_e =>
      match rs ZF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | Cond_ne =>
      match rs ZF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | Cond_b =>
      match rs CF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | Cond_be =>
      match rs CF, rs ZF with
      | Vint c, Vint z => Some (Int.eq c Int.one || Int.eq z Int.one)
      | _, _ => None
      end
  | Cond_ae =>
      match rs CF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | Cond_a =>
      match rs CF, rs ZF with
      | Vint c, Vint z => Some (Int.eq c Int.zero && Int.eq z Int.zero)
      | _, _ => None
      end
  | Cond_l =>
      match rs SOF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | Cond_le =>
      match rs SOF, rs ZF with
      | Vint s, Vint z => Some (Int.eq s Int.one || Int.eq z Int.one)
      | _, _ => None
      end
  | Cond_ge =>
      match rs SOF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | Cond_g =>
      match rs SOF, rs ZF with
      | Vint s, Vint z => Some (Int.eq s Int.zero && Int.eq z Int.zero)
      | _, _ => None
      end
  | Cond_p =>
      match rs PF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | Cond_np =>
      match rs PF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | Cond_nep =>
      match rs PF, rs ZF with
      | Vint p, Vint z => Some (Int.eq p Int.one || Int.eq z Int.zero)
      | _, _ => None
      end
  | Cond_enp =>
      match rs PF, rs ZF with
      | Vint p, Vint z => Some (Int.eq p Int.zero && Int.eq z Int.one)
      | _, _ => None
      end
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
  rs#PC <- (Val.add rs#PC Vone).

Definition nextinstr_nf (rs: regset) : regset :=
  nextinstr (undef_regs (CR ZF :: CR CF :: CR PF :: CR SOF :: nil) rs).

Definition goto_label (c: code) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 c with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Int.repr pos))) m
      | _ => Stuck
    end
  end.

(** Auxiliaries for memory accesses. *)

Definition exec_load (chunk: memory_chunk) (m: mem)
                     (a: addrmode) (rs: regset) (rd: preg) :=
  match Mem.loadv chunk m (eval_addrmode a rs) with
  | Some v => Next (nextinstr_nf (rs#rd <- v)) m
  | None => Stuck
  end.

Definition exec_store (chunk: memory_chunk) (m: mem)
                      (a: addrmode) (rs: regset) (r1: preg) :=
  match Mem.storev chunk m (eval_addrmode a rs) (rs r1) with
  | Some m' => Next (nextinstr_nf rs) m'
  | None => Stuck
  end.

(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual IA32 instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the IA32 reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above.  Note that
    we set to [Vundef] the registers used as temporaries by the
    expansions of the pseudo-instructions, so that the IA32 code
    we generate cannot use those registers to hold values that
    must survive the execution of the pseudo-instruction.
*)

Definition exec_instr (c: code) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  (** Moves *)
  | Pmov_rr rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmov_ri rd n =>
      Next (nextinstr (rs#rd <- (Vint n))) m
  | Pmov_rm rd a =>
      exec_load Mint32 m a rs rd
  | Pmov_mr a r1 =>
      exec_store Mint32 m a rs r1
  | Pmovd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmovd_rf rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmovsd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmovsd_fi rd n =>
      Next (nextinstr (rs#rd <- (Vfloat n))) m
  | Pmovsd_fm rd a =>
      exec_load Mfloat64 m a rs rd
  | Pmovsd_mf a r1 =>
      exec_store Mfloat64 m a rs r1
  | Pfld_f r1 =>
      Next (nextinstr (rs#ST0 <- (rs r1))) m
  | Pfld_m a =>
      exec_load Mfloat64 m a rs ST0
  | Pfstp_f rd =>
      Next (nextinstr (rs#rd <- (rs ST0))) m
  | Pfstp_m a =>
      exec_store Mfloat64 m a rs ST0
  (** Moves with conversion *)
  | Pmovb_mr a r1 =>
      exec_store Mint8unsigned m a rs r1
  | Pmovw_mr a r1 =>
      exec_store Mint16unsigned m a rs r1
  | Pmovzb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1))) m
  | Pmovzb_rm rd a =>
      exec_load Mint8unsigned m a rs rd
  | Pmovsb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1))) m
  | Pmovsb_rm rd a =>
      exec_load Mint8signed m a rs rd
  | Pmovzw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1))) m
  | Pmovzw_rm rd a =>
      exec_load Mint16unsigned m a rs rd
  | Pmovsw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1))) m
  | Pmovsw_rm rd a =>
      exec_load Mint16signed m a rs rd
  | Pcvtss2sd_fm rd a =>
      exec_load Mfloat32 m a rs rd
  | Pcvtsd2ss_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1))) m
  | Pcvtsd2ss_mf a r1 =>
      exec_store Mfloat32 m a rs r1
  | Pcvttsd2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.intoffloat rs#r1))) m
  | Pcvtsi2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.floatofint rs#r1))) m
  (** Integer arithmetic *)
  | Plea rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode a rs))) m
  | Pneg rd =>
      Next (nextinstr_nf (rs#rd <- (Val.neg rs#rd))) m
  | Psub_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd rs#r1))) m
  | Pimul_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd rs#r1))) m
  | Pimul_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd (Vint n)))) m
  | Pdiv r1 =>
      Next (nextinstr_nf (rs#EAX <- (Val.divu rs#EAX (rs#EDX <- Vundef)#r1)
                            #EDX <- (Val.modu rs#EAX (rs#EDX <- Vundef)#r1))) m
  | Pidiv r1 =>
      Next (nextinstr_nf (rs#EAX <- (Val.divs rs#EAX (rs#EDX <- Vundef)#r1)
                            #EDX <- (Val.mods rs#EAX (rs#EDX <- Vundef)#r1))) m
  | Pand_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd rs#r1))) m
  | Pand_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd (Vint n)))) m
  | Por_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd rs#r1))) m
  | Por_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd (Vint n)))) m
  | Pxor_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd rs#r1))) m
  | Pxor_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd (Vint n)))) m
  | Psal_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd rs#ECX))) m
  | Psal_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd (Vint n)))) m
  | Pshr_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd rs#ECX))) m
  | Pshr_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd (Vint n)))) m
  | Psar_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd rs#ECX))) m
  | Psar_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd (Vint n)))) m
  | Pror_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.ror rs#rd (Vint n)))) m
  | Pcmp_rr r1 r2 =>
      Next (nextinstr (compare_ints (rs r1) (rs r2) rs)) m
  | Pcmp_ri r1 n =>
      Next (nextinstr (compare_ints (rs r1) (Vint n) rs)) m
  | Ptest_rr r1 r2 =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (rs r2)) Vzero rs)) m
  | Ptest_ri r1 n =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (Vint n)) Vzero rs)) m
  | Pcmov c rd r1 =>
      match eval_testcond c rs with
      | Some true => Next (nextinstr (rs#rd <- (rs#r1))) m
      | Some false => Next (nextinstr rs) m
      | None => Stuck
      end
  | Psetcc c rd =>
      match eval_testcond c rs with
      | Some true => Next (nextinstr (rs#ECX <- Vundef #EDX <- Vundef #rd <- Vtrue)) m
      | Some false => Next (nextinstr (rs#ECX <- Vundef #EDX <- Vundef #rd <- Vfalse)) m
      | None => Stuck
      end
  (** Arithmetic operations over floats *)
  | Paddd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addf rs#rd rs#r1))) m
  | Psubd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subf rs#rd rs#r1))) m
  | Pmuld_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulf rs#rd rs#r1))) m
  | Pdivd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divf rs#rd rs#r1))) m
  | Pnegd rd =>
      Next (nextinstr (rs#rd <- (Val.negf rs#rd))) m
  | Pabsd rd =>
      Next (nextinstr (rs#rd <- (Val.absf rs#rd))) m
  | Pcomisd_ff r1 r2 =>
      Next (nextinstr (compare_floats (rs r1) (rs r2) rs)) m
  (** Branches and calls *)
  | Pjmp_l lbl =>
      goto_label c lbl rs m
  | Pjmp_s id =>
      Next (rs#PC <- (symbol_offset id Int.zero)) m
  | Pjmp_r r =>
      Next (rs#PC <- (rs r)) m
  | Pjcc cond lbl =>
      match eval_testcond cond rs with
      | Some true => goto_label c lbl rs m
      | Some false => Next (nextinstr rs) m
      | None => Stuck
      end
  | Pjmptbl r tbl =>
      match rs#r with
      | Vint n => 
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label c lbl (rs #ECX <- Vundef #EDX <- Vundef) m
          end
      | _ => Stuck
      end
  | Pcall_s id =>
      Next (rs#RA <- (Val.add rs#PC Vone) #PC <- (symbol_offset id Int.zero)) m
  | Pcall_r r =>
      Next (rs#RA <- (Val.add rs#PC Vone) #PC <- (rs r)) m
  | Pret =>
      Next (rs#PC <- (rs#RA)) m
  (** Pseudo-instructions *)
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Pallocframe sz ofs_ra ofs_link =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := Vptr stk Int.zero in
      match Mem.storev Mint32 m1 (Val.add sp (Vint ofs_link)) rs#ESP with
      | None => Stuck
      | Some m2 =>
          match Mem.storev Mint32 m2 (Val.add sp (Vint ofs_ra)) rs#RA with
          | None => Stuck
          | Some m3 => Next (nextinstr (rs #EDX <- (rs#ESP) #ESP <- sp)) m3
          end
      end
  | Pfreeframe sz ofs_ra ofs_link =>
      match Mem.loadv Mint32 m (Val.add rs#ESP (Vint ofs_ra)) with
      | None => Stuck
      | Some ra =>
          match Mem.loadv Mint32 m (Val.add rs#ESP (Vint ofs_link)) with
          | None => Stuck
          | Some sp =>
              match rs#ESP with
              | Vptr stk ofs =>
                  match Mem.free m stk 0 sz with
                  | None => Stuck
                  | Some m' => Next (nextinstr (rs#ESP <- sp #RA <- ra)) m'
                  end
              | _ => Stuck
              end
          end
      end
  | Pbuiltin ef args res =>
      Stuck                             (**r treated specially below *)
  end.

(** Translation of the LTL/Linear/Mach view of machine registers
  to the Asm view.  *)

Definition preg_of (r: mreg) : preg :=
  match r with
  | AX => IR EAX
  | BX => IR EBX
  | SI => IR ESI
  | DI => IR EDI
  | BP => IR EBP
  | X0 => FR XMM0
  | X1 => FR XMM1
  | X2 => FR XMM2
  | X3 => FR XMM3
  | X4 => FR XMM4
  | X5 => FR XMM5
  | IT1 => IR EDX
  | IT2 => IR ECX
  | FT1 => FR XMM6
  | FT2 => FR XMM7
  | FP0 => ST0
  end.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use machine registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_int_stack: forall ofs bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv Mint32 m (Val.add (rs (IR ESP)) (Vint (Int.repr bofs))) = Some v ->
      extcall_arg rs m (S (Outgoing ofs Tint)) v
  | extcall_arg_float_stack: forall ofs bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv Mfloat64 m (Val.add (rs (IR ESP)) (Vint (Int.repr bofs))) = Some v ->
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
      exec_instr c i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs c ef args res rs m t v m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal c) ->
      find_instr (Int.unsigned ofs) c = Some (Pbuiltin ef args res) ->
      external_call ef ge (map rs args) m t v m' ->
      step (State rs m) t
           (State (nextinstr_nf(rs #EDX <- Vundef #ECX <- Vundef
                                #XMM6 <- Vundef #XMM7 <- Vundef
                                #ST0 <- Vundef
                                #res <- v)) m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments rs m ef.(ef_sig) args ->
      rs' = (rs#(loc_external_result ef.(ef_sig)) <- res
               #PC <- (rs RA)) ->
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
        # RA <- Vzero
        # ESP <- (Vptr Mem.nullptr Int.zero) in
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vzero ->
      rs#EAX = Vint r ->
      final_state (State rs m) r.
      
Definition exec_program (p: program) (beh: program_behavior) : Prop :=
  program_behaves step (initial_state p) final_state (Genv.globalenv p) beh.

