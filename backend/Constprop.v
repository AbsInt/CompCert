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
    apply Int.eq_dec.
  Qed.
  Definition beq (x y: t) := if eq_dec x y then true else false.
  Lemma beq_correct: forall x y, beq x y = true -> x = y.
  Proof.
    unfold beq; intros.  destruct (eq_dec x y). auto. congruence.
  Qed.

  Definition ge (x y: t) : Prop := x = Unknown \/ y = Novalue \/ x = y.

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
  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    unfold lub; intros.
    case (eq_dec x y); intro.
    apply ge_refl. apply eq_refl.
    destruct x; destruct y; unfold ge; tauto.
  Qed.
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    unfold lub; intros.
    case (eq_dec x y); intro.
    apply ge_refl. subst. apply eq_refl.
    destruct x; destruct y; unfold ge; tauto.
  Qed.
End Approx.

Module D := LPMap Approx.

(** We keep track of read-only global variables (i.e. "const" global
  variables in C) as a map from their names to their initialization
  data. *)

Definition global_approx : Type := PTree.t (list init_data).

(** Given some initialization data and a byte offset, compute a static
  approximation of the result of a memory load from a memory block
  initialized with this data. *)

Fixpoint eval_load_init (chunk: memory_chunk) (pos: Z) (il: list init_data): approx :=
  match il with
  | nil => Unknown
  | Init_int8 n :: il' =>
      if zeq pos 0 then
        match chunk with
        | Mint8unsigned => I (Int.zero_ext 8 n)
        | Mint8signed => I (Int.sign_ext 8 n)
        | _ => Unknown
        end
      else eval_load_init chunk (pos - 1) il'
  | Init_int16 n :: il' =>
      if zeq pos 0 then
        match chunk with
        | Mint16unsigned => I (Int.zero_ext 16 n)
        | Mint16signed => I (Int.sign_ext 16 n)
        | _ => Unknown
        end
      else eval_load_init chunk (pos - 2) il'
  | Init_int32 n :: il' =>
      if zeq pos 0 
      then match chunk with Mint32 => I n | _ => Unknown end
      else eval_load_init chunk (pos - 4) il'
  | Init_float32 n :: il' =>
      if zeq pos 0
      then match chunk with 
           | Mfloat32 => if propagate_float_constants tt then F (Float.singleoffloat n) else Unknown
           | _ => Unknown
           end
      else eval_load_init chunk (pos - 4) il'
  | Init_float64 n :: il' =>
      if zeq pos 0 
      then match chunk with
           | Mfloat64 => if propagate_float_constants tt then F n else Unknown
           | _ => Unknown
           end
      else eval_load_init chunk (pos - 8) il'
  | Init_addrof symb ofs :: il' =>
      if zeq pos 0
      then match chunk with Mint32 => G symb ofs | _ => Unknown end
      else eval_load_init chunk (pos - 4) il'
  | Init_space n :: il' =>
      eval_load_init chunk (pos - Zmax n 0) il'
  end.

(** Compute a static approximation for the result of a load at an address whose
  approximation is known.  If the approximation points to a global variable,
  and this global variable is read-only, we use its initialization data
  to determine a static approximation.  Otherwise, [Unknown] is returned. *)

Definition eval_static_load (gapp: global_approx) (chunk: memory_chunk) (addr: approx) : approx :=
  match addr with
  | G symb ofs =>
      match gapp!symb with
      | None => Unknown
      | Some il => eval_load_init chunk (Int.unsigned ofs) il
      end
  | _ => Unknown
  end.

(** The transfer function for the dataflow analysis is straightforward.
  For [Iop] instructions, we set the approximation of the destination
  register to the result of executing abstractly the operation.
  For [Iload] instructions, we set the approximation of the destination
  register to the result of [eval_static_load].
  For [Icall] and [Ibuiltin], the destination register becomes [Unknown].
  Other instructions keep the approximations unchanged, as they preserve
  the values of all registers. *)

Definition approx_reg (app: D.t) (r: reg) := 
  D.get r app.

Definition approx_regs (app: D.t) (rl: list reg):=
  List.map (approx_reg app) rl.

Definition transfer (gapp: global_approx) (f: function) (pc: node) (before: D.t) :=
  match f.(fn_code)!pc with
  | None => before
  | Some i =>
      match i with
      | Iop op args res s =>
          let a := eval_static_operation op (approx_regs before args) in
          D.set res a before
      | Iload chunk addr args dst s =>
          let a := eval_static_load gapp chunk
                     (eval_static_addressing addr (approx_regs before args)) in
          D.set dst a before
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
  number of iterations, in which case we use the trivial mapping
  (program point -> [D.top]) instead. *)

Module DS := Dataflow_Solver(D)(NodeSetForward).

Definition analyze (gapp: global_approx) (f: RTL.function): PMap.t D.t :=
  match DS.fixpoint (successors f) (transfer gapp f) 
                    ((f.(fn_entrypoint), D.top) :: nil) with
  | None => PMap.init D.top
  | Some res => res
  end.

(** * Code transformation *)

(** The code transformation proceeds instruction by instruction.
    Operators whose arguments are all statically known are turned
    into ``load integer constant'', ``load float constant'' or
    ``load symbol address'' operations.  Likewise for loads whose
    result can be statically predicted.  Operators for which some
    but not all arguments are known are subject to strength reduction,
    and similarly for the addressing modes of load and store instructions.
    Conditional branches and multi-way branches are statically resolved
    into [Inop] instructions if possible. Other instructions are unchanged. *)

Definition transf_ros (app: D.t) (ros: reg + ident) : reg + ident :=
  match ros with
  | inl r =>
      match D.get r app with
      | G symb ofs => if Int.eq ofs Int.zero then inr _ symb else ros
      | _ => ros
      end
  | inr s => ros
  end.

Parameter generate_float_constants : unit -> bool.

Definition const_for_result (a: approx) : option operation :=
  match a with
  | I n => Some(Ointconst n)
  | F n => if generate_float_constants tt then Some(Ofloatconst n) else None
  | G symb ofs => Some(Oaddrsymbol symb ofs)
  | S ofs => Some(Oaddrstack ofs)
  | _ => None
  end.

Definition transf_instr (gapp: global_approx) (app: D.t) (instr: instruction) :=
  match instr with
  | Iop op args res s =>
      let a := eval_static_operation op (approx_regs app args) in
      match const_for_result a with
      | Some cop =>
          Iop cop nil res s
      | None =>
          let (op', args') := op_strength_reduction op args (approx_regs app args) in
          Iop op' args' res s
      end
  | Iload chunk addr args dst s =>
      let a := eval_static_load gapp chunk
                  (eval_static_addressing addr (approx_regs app args)) in
      match const_for_result a with
      | Some cop =>
          Iop cop nil dst s
      | None =>
          let (addr', args') := addr_strength_reduction addr args (approx_regs app args) in
          Iload chunk addr' args' dst s      
      end
  | Istore chunk addr args src s =>
      let (addr', args') := addr_strength_reduction addr args (approx_regs app args) in
      Istore chunk addr' args' src s      
  | Icall sig ros args res s =>
      Icall sig (transf_ros app ros) args res s
  | Itailcall sig ros args =>
      Itailcall sig (transf_ros app ros) args
  | Ibuiltin ef args res s =>
      let (ef', args') := builtin_strength_reduction ef args (approx_regs app args) in
      Ibuiltin ef' args' res s
  | Icond cond args s1 s2 =>
      match eval_static_condition cond (approx_regs app args) with
      | Some b =>
          if b then Inop s1 else Inop s2
      | None =>
          let (cond', args') := cond_strength_reduction cond args (approx_regs app args) in
          Icond cond' args' s1 s2
      end
  | Ijumptable arg tbl =>
      match approx_reg app arg with
      | I n =>
          match list_nth_z tbl (Int.unsigned n) with
          | Some s => Inop s
          | None => instr
          end
      | _ => instr
      end
  | _ =>
      instr
  end.

Definition transf_code (gapp: global_approx) (app: PMap.t D.t) (instrs: code) : code :=
  PTree.map (fun pc instr => transf_instr gapp app!!pc instr) instrs.

Definition transf_function (gapp: global_approx) (f: function) : function :=
  let approxs := analyze gapp f in
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (transf_code gapp approxs f.(fn_code))
    f.(fn_entrypoint).

Definition transf_fundef (gapp: global_approx) (fd: fundef) : fundef :=
  AST.transf_fundef (transf_function gapp) fd.

Fixpoint make_global_approx (gapp: global_approx) (vars: list (ident * globvar unit)) : global_approx :=
  match vars with
  | nil => gapp
  | (id, gv) :: vars' =>
      let gapp1 :=
        if gv.(gvar_readonly) && negb gv.(gvar_volatile)
        then PTree.set id gv.(gvar_init) gapp
        else PTree.remove id gapp in
      make_global_approx gapp1 vars'
  end.

Definition transf_program (p: program) : program :=
  let gapp := make_global_approx (PTree.empty _) p.(prog_vars) in
  transform_program (transf_fundef gapp) p.
