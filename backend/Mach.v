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

(** The Mach intermediate language: abstract syntax.

  Mach is the last intermediate language before generation of assembly
  code.  
*)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.

(** * Abstract syntax *)

(** Like Linear, the Mach language is organized as lists of instructions
  operating over machine registers, with default fall-through behaviour
  and explicit labels and branch instructions.  

  The main difference with Linear lies in the instructions used to
  access the activation record.  Mach has three such instructions:
  [Mgetstack] and [Msetstack] to read and write within the activation
  record for the current function, at a given word offset and with a
  given type; and [Mgetparam], to read within the activation record of
  the caller. 

  These instructions implement a more concrete view of the activation
  record than the the [Lgetstack] and [Lsetstack] instructions of
  Linear: actual offsets are used instead of abstract stack slots, and the
  distinction between the caller's frame and the callee's frame is
  made explicit. *)

Definition label := positive.

Inductive instruction: Type :=
  | Mgetstack: int -> typ -> mreg -> instruction
  | Msetstack: mreg -> int -> typ -> instruction
  | Mgetparam: int -> typ -> mreg -> instruction
  | Mop: operation -> list mreg -> mreg -> instruction
  | Mload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Mstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Mcall: signature -> mreg + ident -> instruction
  | Mtailcall: signature -> mreg + ident -> instruction
  | Mbuiltin: external_function -> list mreg -> mreg -> instruction
  | Mannot: external_function -> list annot_param -> instruction
  | Mlabel: label -> instruction
  | Mgoto: label -> instruction
  | Mcond: condition -> list mreg -> label -> instruction
  | Mjumptable: mreg -> list label -> instruction
  | Mreturn: instruction

with annot_param: Type :=
  | APreg: mreg -> annot_param
  | APstack: memory_chunk -> Z -> annot_param.

Definition code := list instruction.

Record function: Type := mkfunction
  { fn_sig: signature;
    fn_code: code;
    fn_stacksize: Z;
    fn_link_ofs: int;
    fn_retaddr_ofs: int }.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Definition genv := Genv.t fundef unit.

(** * Elements of dynamic semantics *)

(** The operational semantics is in module [Machsem]. *)

Definition chunk_of_type (ty: typ) :=
  match ty with Tint => Mint32 | Tfloat => Mfloat64al32 end.

Module RegEq.
  Definition t := mreg.
  Definition eq := mreg_eq.
End RegEq.

Module Regmap := EMap(RegEq).

Definition regset := Regmap.t val.

Notation "a ## b" := (List.map a b) (at level 1).
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level).

Fixpoint undef_regs (rl: list mreg) (rs: regset) {struct rl} : regset :=
  match rl with
  | nil => rs
  | r1 :: rl' => undef_regs rl' (Regmap.set r1 Vundef rs)
  end.

Lemma undef_regs_other:
  forall r rl rs, ~In r rl -> undef_regs rl rs r = rs r.
Proof.
  induction rl; simpl; intros. auto. rewrite IHrl. apply Regmap.gso. intuition. intuition.
Qed.

Lemma undef_regs_same:
  forall r rl rs, In r rl \/ rs r = Vundef -> undef_regs rl rs r = Vundef.
Proof.
  induction rl; simpl; intros. tauto.
  destruct H. destruct H. apply IHrl. right. subst; apply Regmap.gss.
  auto.
  apply IHrl. right. unfold Regmap.set. destruct (RegEq.eq r a); auto. 
Qed.

Definition undef_temps (rs: regset) := 
  undef_regs temporary_regs rs.

Definition undef_move (rs: regset) := 
  undef_regs destroyed_at_move_regs rs.

Definition undef_op (op: operation) (rs: regset) :=
  match op with
  | Omove => undef_move rs
  | _ => undef_temps rs
  end.

Definition undef_setstack (rs: regset) := undef_move rs.

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Mlabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Mlabel lbl else instr <> Mlabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
  end.

Lemma find_label_incl:
  forall lbl c c', find_label lbl c = Some c' -> incl c' c.
Proof.
  induction c; simpl; intros. discriminate.
  destruct (is_label lbl a). inv H. auto with coqlib. eauto with coqlib. 
Qed.

Definition find_function_ptr
        (ge: genv) (ros: mreg + ident) (rs: regset) : option block :=
  match ros with
  | inl r =>
      match rs r with
      | Vptr b ofs => if Int.eq ofs Int.zero then Some b else None
      | _ => None
      end
  | inr symb =>
      Genv.find_symbol ge symb
  end.

