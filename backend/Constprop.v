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

(** Constant propagation over RTL.  This is one of the optimizations
  performed at RTL level.  It proceeds by a standard dataflow analysis
  and the corresponding code rewriting. *)

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
Require Import ConstpropOp.

(** * Static analysis *)

(** The type [approx] of compile-time approximations of values is
  defined in the machine-dependent part [ConstpropOp]. *)

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
    apply Int.eq_dec.
    apply Float.eq_dec.
    apply Int.eq_dec.
    apply ident_eq.
  Qed.
  Definition beq (x y: t) := if eq_dec x y then true else false.
  Lemma beq_correct: forall x y, beq x y = true -> x = y.
  Proof.
    unfold beq; intros.  destruct (eq_dec x y). auto. congruence.
  Qed.
  Definition ge (x y: t) : Prop :=
    x = Unknown \/ y = Novalue \/ x = y.
  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    unfold eq, ge; tauto.
  Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    unfold ge; intuition congruence.
  Qed.
  Lemma ge_compat: forall x x' y y', eq x x' -> eq y y' -> ge x y -> ge x' y'.
  Proof.
    unfold eq, ge; intros; congruence.
  Qed.
  Definition bot := Novalue.
  Definition top := Unknown.
  Lemma ge_bot: forall x, ge x bot.
  Proof.
    unfold ge, bot; tauto.
  Qed.
  Lemma ge_top: forall x, ge top x.
  Proof.
    unfold ge, bot; tauto.
  Qed.
  Definition lub (x y: t) : t :=
    if eq_dec x y then x else
    match x, y with
    | Novalue, _ => y
    | _, Novalue => x
    | _, _ => Unknown
    end.
  Lemma lub_commut: forall x y, eq (lub x y) (lub y x).
  Proof.
    unfold lub, eq; intros.
    case (eq_dec x y); case (eq_dec y x); intros; try congruence.
    destruct x; destruct y; auto.
  Qed.
  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold lub; intros.
    case (eq_dec x y); intro.
    apply ge_refl. apply eq_refl.
    destruct x; destruct y; unfold ge; tauto.
  Qed.
End Approx.

Module D := LPMap Approx.

(** The transfer function for the dataflow analysis is straightforward:
  for [Iop] instructions, we set the approximation of the destination
  register to the result of executing abstractly the operation;
  for [Iload] and [Icall], we set the approximation of the destination
  to [Unknown]. *)

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
          let a := eval_static_operation op (approx_regs before args) in
          D.set res a before
      | Iload chunk addr args dst s =>
          D.set dst Unknown before
      | Icall sig ros args res s =>
          D.set res Unknown before
      | Ibuiltin ef args res s =>
          D.set res Unknown before
      | _ =>
          before
      end
  end.

(** The static analysis itself is then an instantiation of Kildall's
  generic solver for forward dataflow inequations. [analyze f]
  returns a mapping from program points to mappings of pseudo-registers
  to approximations.  It can fail to reach a fixpoint in a reasonable
  number of iterations, in which case [None] is returned. *)

Module DS := Dataflow_Solver(D)(NodeSetForward).

Definition analyze (f: RTL.function): PMap.t D.t :=
  match DS.fixpoint (successors f) (transfer f) 
                    ((f.(fn_entrypoint), D.top) :: nil) with
  | None => PMap.init D.top
  | Some res => res
  end.

(** * Code transformation *)

(** The code transformation proceeds instruction by instruction.
    Operators whose arguments are all statically known are turned
    into ``load integer constant'', ``load float constant'' or
    ``load symbol address'' operations.  Operators for which some
    but not all arguments are known are subject to strength reduction,
    and similarly for the addressing modes of load and store instructions.
    Other instructions are unchanged. *)

Definition transf_ros (app: D.t) (ros: reg + ident) : reg + ident :=
  match ros with
  | inl r =>
      match D.get r app with
      | S symb ofs => if Int.eq ofs Int.zero then inr _ symb else ros
      | _ => ros
      end
  | inr s => ros
  end.

Definition transf_instr (app: D.t) (instr: instruction) :=
  match instr with
  | Iop op args res s =>
      match eval_static_operation op (approx_regs app args) with
      | I n =>
          Iop (Ointconst n) nil res s
      | F n =>
          Iop (Ofloatconst n) nil res s
      | S symb ofs =>
          Iop (Oaddrsymbol symb ofs) nil res s
      | _ =>
          let (op', args') := op_strength_reduction (approx_reg app) op args in
          Iop op' args' res s
      end
  | Iload chunk addr args dst s =>
      let (addr', args') := addr_strength_reduction (approx_reg app) addr args in
      Iload chunk addr' args' dst s      
  | Istore chunk addr args src s =>
      let (addr', args') := addr_strength_reduction (approx_reg app) addr args in
      Istore chunk addr' args' src s      
  | Icall sig ros args res s =>
      Icall sig (transf_ros app ros) args res s
  | Itailcall sig ros args =>
      Itailcall sig (transf_ros app ros) args
  | Icond cond args s1 s2 =>
      match eval_static_condition cond (approx_regs app args) with
      | Some b =>
          if b then Inop s1 else Inop s2
      | None =>
          let (cond', args') := cond_strength_reduction (approx_reg app) cond args in
          Icond cond' args' s1 s2
      end
  | Ijumptable arg tbl =>
      match intval (approx_reg app) arg with
      | Some n =>
          match list_nth_z tbl (Int.signed n) with
          | Some s => Inop s
          | None => instr
          end
      | None => instr
      end
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
