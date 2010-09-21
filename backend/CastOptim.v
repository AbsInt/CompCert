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

(** Elimination of redundant conversions to small numerical types. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Lattice.
Require Import Kildall.

(** * Static analysis *)

(** Compile-time approximations *)

Inductive approx : Type :=
  | Unknown               (**r any value *)
  | Int7                  (**r [[0,127]] *)
  | Int8s                 (**r [[-128,127]] *)
  | Int8u                 (**r [[0,255]] *)
  | Int15                 (**r [[0,32767]] *)
  | Int16s                (**r [[-32768,32767]] *)
  | Int16u                (**r [[0,65535]] *)
  | Single                (**r single-precision float *)
  | Novalue.              (**r empty *)

(** We equip this type of approximations with a semi-lattice structure.
  The ordering is inclusion between the sets of values denoted by
  the approximations. *)

Module Approx <: SEMILATTICE_WITH_TOP.
  Definition t := approx.
  Definition eq (x y: t) := (x = y).
  Definition eq_refl: forall x, eq x x := (@refl_equal t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@sym_equal t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@trans_equal t).
  Lemma eq_dec: forall (x y: t), {x=y} + {x<>y}.
  Proof.
    decide equality.
  Qed.
  Definition beq (x y: t) := if eq_dec x y then true else false.
  Lemma beq_correct: forall x y, beq x y = true -> x = y.
  Proof.
    unfold beq; intros.  destruct (eq_dec x y). auto. congruence.
  Qed.
  Definition ge (x y: t) : Prop :=
    match x, y with
    | Unknown, _ => True
    | _, Novalue => True
    | Int7, Int7 => True
    | Int8s, (Int7 | Int8s) => True
    | Int8u, (Int7 | Int8u) => True
    | Int15, (Int7 | Int8u | Int15) => True
    | Int16s, (Int7 | Int8s | Int8u | Int15 | Int16s) => True
    | Int16u, (Int7 | Int8u | Int15 | Int16u) => True
    | Single, Single => True
    | _, _ => False
    end.
  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold eq, ge; intros. subst y. destruct x; auto.
  Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge; intros.
    destruct x; auto; (destruct y; auto; try contradiction; destruct z; auto).
  Qed.
  Lemma ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
  Proof.
    unfold eq; intros. congruence.
  Qed.
  Definition bge (x y: t) : bool :=
    match x, y with
    | Unknown, _ => true
    | _, Novalue => true
    | Int7, Int7 => true
    | Int8s, (Int7 | Int8s) => true
    | Int8u, (Int7 | Int8u) => true
    | Int15, (Int7 | Int8u | Int15) => true
    | Int16s, (Int7 | Int8s | Int8u | Int15 | Int16s) => true
    | Int16u, (Int7 | Int8u | Int15 | Int16u) => true
    | Single, Single => true
    | _, _ => false
    end.
  Lemma bge_correct: forall x y, bge x y = true -> ge x y.
  Proof.
    destruct x; destruct y; simpl; auto || congruence.
  Qed.
  Definition bot := Novalue.
  Definition top := Unknown.
  Lemma ge_bot: forall x, ge x bot.
  Proof.
    unfold ge, bot. destruct x; auto. 
  Qed.
  Lemma ge_top: forall x, ge top x.
  Proof.
    unfold ge, top. auto.
  Qed.
  Definition lub (x y: t) : t :=
    match x, y with
    | Novalue, _ => y
    | _, Novalue => x
    | Int7, Int7 => Int7
    | Int7, Int8u => Int8u
    | Int7, Int8s => Int8s
    | Int7, Int15 => Int15
    | Int7, Int16u => Int16u
    | Int7, Int16s => Int16s
    | Int8u, (Int7|Int8u) => Int8u
    | Int8u, Int15 => Int15
    | Int8u, Int16u => Int16u
    | Int8u, Int16s => Int16s
    | Int8s, (Int7|Int8s) => Int8s
    | Int8s, (Int15|Int16s) => Int16s
    | Int15, (Int7|Int8u|Int15) => Int15
    | Int15, Int16u => Int16u
    | Int15, (Int8s|Int16s) => Int16s
    | Int16u, (Int7|Int8u|Int15|Int16u) => Int16u
    | Int16s, (Int7|Int8u|Int8s|Int15|Int16s) => Int16s
    | Single, Single => Single
    | _, _ => Unknown
    end.
  Lemma lub_commut: forall x y, eq (lub x y) (lub y x).
  Proof.
    unfold lub, eq; intros.
    destruct x; destruct y; auto.
  Qed.
  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold lub, ge; intros.
    destruct x; destruct y; auto. 
  Qed.
End Approx.

Module D := LPMap Approx.

(** Abstract interpretation of operators *)

Definition approx_bitwise_op (v1 v2: approx) : approx :=
  if Approx.bge Int8u v1 && Approx.bge Int8u v2 then Int8u
  else if Approx.bge Int16u v1 && Approx.bge Int16u v2 then Int16u
  else Unknown.

Function approx_operation (op: operation) (vl: list approx) : approx :=
  match op, vl with
  | Omove, v1 :: nil => v1
  | Ointconst n, _ =>
      if Int.eq_dec n (Int.zero_ext 7 n) then Int7
      else if Int.eq_dec n (Int.zero_ext 8 n) then Int8u
      else if Int.eq_dec n (Int.sign_ext 8 n) then Int8s
      else if Int.eq_dec n (Int.zero_ext 15 n) then Int15
      else if Int.eq_dec n (Int.zero_ext 16 n) then Int16u
      else if Int.eq_dec n (Int.sign_ext 16 n) then Int16s
      else Unknown
  | Ofloatconst n, _ =>
      if Float.eq_dec n (Float.singleoffloat n) then Single else Unknown
  | Ocast8signed, _ => Int8s
  | Ocast8unsigned, _ => Int8u
  | Ocast16signed, _ => Int16s
  | Ocast16unsigned, _ => Int16u
  | Osingleoffloat, _ => Single
  | Oand, v1 :: v2 :: nil => approx_bitwise_op v1 v2
  | Oor, v1 :: v2 :: nil => approx_bitwise_op v1 v2
  | Oxor, v1 :: v2 :: nil => approx_bitwise_op v1 v2
  (* Problem: what about and/or/xor immediate? and other
     machine-specific operators? *)
  | Ocmp c, _ => Int7
  | _, _ => Unknown
  end.

Definition approx_of_chunk (chunk: memory_chunk) :=
  match chunk with
  | Mint8signed => Int8s
  | Mint8unsigned => Int8u
  | Mint16signed => Int16s
  | Mint16unsigned => Int16u
  | Mint32 => Unknown
  | Mfloat32 => Single
  | Mfloat64 => Unknown
  end.

(** Transfer function for the analysis *)

Definition approx_reg (app: D.t) (r: reg) := 
  D.get r app.

Definition approx_regs (app: D.t) (rl: list reg):=
  List.map (approx_reg app) rl.

Definition transfer (f: function) (pc: node) (before: D.t) :=
  match f.(fn_code)!pc with
  | None => before
  | Some i =>
      match i with
      | Iop op args res s =>
          let a := approx_operation op (approx_regs before args) in
          D.set res a before
      | Iload chunk addr args dst s =>
          D.set dst (approx_of_chunk chunk) before
      | Icall sig ros args res s =>
          D.set res Unknown before
      | Ibuiltin ef args res s =>
          D.set res Unknown before
      | _ =>
          before
      end
  end.

(** The static analysis is a forward dataflow analysis. *)

Module DS := Dataflow_Solver(D)(NodeSetForward).

Definition analyze (f: RTL.function): PMap.t D.t :=
  match DS.fixpoint (successors f) (transfer f) 
                    ((f.(fn_entrypoint), D.top) :: nil) with
  | None => PMap.init D.top
  | Some res => res
  end.

(** * Code transformation *)

(** Cast operations that have no effect (because the argument is already
    in the right range) are turned into moves. *)

Function transf_operation (op: operation) (vl: list approx) : operation :=
  match op, vl with
  | Ocast8signed, v :: nil => if Approx.bge Int8s v then Omove else op
  | Ocast8unsigned, v :: nil => if Approx.bge Int8u v then Omove else op
  | Ocast16signed, v :: nil => if Approx.bge Int16s v then Omove else op
  | Ocast16unsigned, v :: nil => if Approx.bge Int16u v then Omove else op
  | Osingleoffloat, v :: nil => if Approx.bge Single v then Omove else op
  | _, _ => op
  end.

Definition transf_instr (app: D.t) (instr: instruction) :=
  match instr with
  | Iop op args res s =>
      let op' := transf_operation op (approx_regs app args) in
      Iop op' args res s
  | _ =>
      instr
  end.

Definition transf_code (approxs: PMap.t D.t) (instrs: code) : code :=
  PTree.map (fun pc instr => transf_instr approxs!!pc instr) instrs.

Definition transf_function (f: function) : function :=
  let approxs := analyze f in
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (transf_code approxs f.(fn_code))
    f.(fn_entrypoint).

Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
