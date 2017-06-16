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

Require Import Coqlib Maps Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Compopts Machregs.
Require Import Op Registers RTL.
Require Import Liveness ValueDomain ValueAOp ValueAnalysis.
Require Import ConstpropOp.

(** The code transformation builds on the results of the static analysis
  of values from module [ValueAnalysis].  It proceeds instruction by
  instruction.
- Operators whose arguments are all statically known are turned into
  ``load integer constant'', ``load float constant'' or ``load
  symbol address'' operations.  Likewise for loads whose result can
  be statically predicted.
- Operators for which some but not all arguments are known are subject
  to strength reduction (replacement by cheaper operators) and
  similarly for the addressing modes of load and store instructions.
- Cast operators that have no effect (because their arguments are
  already normalized to the destination type) are removed.
- Conditional branches and multi-way branches are statically resolved
  into [Inop] instructions when possible.
- Other instructions are unchanged.

  In addition, we try to jump over conditionals whose condition can
  be statically resolved based on the abstract state "after" the
  instruction that branches to the conditional.  A typical example is:
<<
          1: x := 0 and goto 2
          2: if (x == 0) goto 3 else goto 4
>>
    where other instructions branch into 2 with different abstract values
    for [x].  We transform this code into:
<<
          1: x := 0 and goto 3
          2: if (x == 0) goto 3 else goto 4
>>
*)

Definition transf_ros (ae: AE.t) (ros: reg + ident) : reg + ident :=
  match ros with
  | inl r =>
      match areg ae r with
      | Ptr(Gl symb ofs) => if Ptrofs.eq ofs Ptrofs.zero then inr _ symb else ros
      | _ => ros
      end
  | inr s => ros
  end.

Fixpoint successor_rec (n: nat) (f: function) (ae: AE.t) (pc: node) : node :=
  match n with
  | O => pc
  | S n' =>
      match f.(fn_code)!pc with
      | Some (Inop s) =>
          successor_rec n' f ae s
      | Some (Icond cond args s1 s2) =>
          match resolve_branch (eval_static_condition cond (aregs ae args)) with
          | Some b => successor_rec n' f ae (if b then s1 else s2)
          | None => pc
          end
      | _ => pc
      end
  end.

Definition num_iter := 10%nat.

Definition successor (f: function) (ae: AE.t) (pc: node) : node :=
  successor_rec num_iter f ae pc.

Fixpoint builtin_arg_reduction (ae: AE.t) (a: builtin_arg reg) :=
  match a with
  | BA r =>
      match areg ae r with
      | I n => BA_int n
      | L n => BA_long n
      | F n => if Compopts.generate_float_constants tt then BA_float n else a
      | FS n => if Compopts.generate_float_constants tt then BA_single n else a
      | _ => a
      end
  | BA_splitlong hi lo =>
      match builtin_arg_reduction ae hi, builtin_arg_reduction ae lo with
      | BA_int nhi, BA_int nlo => BA_long (Int64.ofwords nhi nlo)
      | hi', lo' => BA_splitlong hi' lo'
      end
  | BA_addptr a1 a2 =>
      BA_addptr (builtin_arg_reduction ae a1) (builtin_arg_reduction ae a2)
  | _ => a
  end.

Definition builtin_arg_strength_reduction
      (ae: AE.t) (a: builtin_arg reg) (c: builtin_arg_constraint) :=
  let a' := builtin_arg_reduction ae a in
  if builtin_arg_ok a' c then a' else a.

Fixpoint builtin_args_strength_reduction
      (ae: AE.t) (al: list (builtin_arg reg)) (cl: list builtin_arg_constraint) :=
  match al with
  | nil => nil
  | a :: al =>
      builtin_arg_strength_reduction ae a (List.hd OK_default cl)
      :: builtin_args_strength_reduction ae al (List.tl cl)
  end.

(** For debug annotations, add constant values to the original info
    instead of replacing it. *)

Fixpoint debug_strength_reduction (ae: AE.t) (al: list (builtin_arg reg)) :=
  match al with
  | nil => nil
  | a :: al =>
      let a' := builtin_arg_reduction ae a in
      let al' := a :: debug_strength_reduction ae al in
      match a, a' with
      | BA _, (BA_int _ | BA_long _ | BA_float _ | BA_single _) => a' :: al'
      | _, _ => al'
      end
  end.

Definition builtin_strength_reduction
             (ae: AE.t) (ef: external_function) (al: list (builtin_arg reg)) :=
  match ef with
  | EF_debug _ _ _ => debug_strength_reduction ae al
  | _ => builtin_args_strength_reduction ae al (Machregs.builtin_constraints ef)
  end.

Definition transf_instr (f: function) (an: PMap.t VA.t) (rm: romem)
                        (pc: node) (instr: instruction) :=
  match an!!pc with
  | VA.Bot =>
      instr
  | VA.State ae am =>
      match instr with
      | Iop op args res s =>
          let aargs := aregs ae args in
          let a := eval_static_operation op aargs in
          let s' := successor f (AE.set res a ae) s in
          match const_for_result a with
          | Some cop =>
              Iop cop nil res s'
          | None =>
              let (op', args') := op_strength_reduction op args aargs in
              Iop op' args' res s'
          end
      | Iload chunk addr args dst s =>
          let aargs := aregs ae args in
          let a := ValueDomain.loadv chunk rm am (eval_static_addressing addr aargs) in
          match const_for_result a with
          | Some cop =>
              Iop cop nil dst s
          | None =>
              let (addr', args') := addr_strength_reduction addr args aargs in
              Iload chunk addr' args' dst s
          end
      | Istore chunk addr args src s =>
          let aargs := aregs ae args in
          let (addr', args') := addr_strength_reduction addr args aargs in
          Istore chunk addr' args' src s
      | Icall sig ros args res s =>
          Icall sig (transf_ros ae ros) args res s
      | Itailcall sig ros args =>
          Itailcall sig (transf_ros ae ros) args
      | Ibuiltin ef args res s =>
          Ibuiltin ef (builtin_strength_reduction ae ef args) res s
      | Icond cond args s1 s2 =>
          let aargs := aregs ae args in
          match resolve_branch (eval_static_condition cond aargs) with
          | Some b =>
              if b then Inop s1 else Inop s2
          | None =>
              let (cond', args') := cond_strength_reduction cond args aargs in
              Icond cond' args' s1 s2
          end
      | Ijumptable arg tbl =>
          match areg ae arg with
          | I n =>
              match list_nth_z tbl (Int.unsigned n) with
              | Some s => Inop s
              | None => instr
              end
          | _ => instr
          end
      | _ =>
          instr
      end
  end.

Definition transf_function (rm: romem) (f: function) : function :=
  let an := ValueAnalysis.analyze rm f in
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (PTree.map (transf_instr f an rm) f.(fn_code))
    f.(fn_entrypoint).

Definition transf_fundef (rm: romem) (fd: fundef) : fundef :=
  AST.transf_fundef (transf_function rm) fd.

Definition transf_program (p: program) : program :=
  let rm := romem_for p in
  transform_program (transf_fundef rm) p.
