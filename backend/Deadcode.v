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

(** Elimination of unneeded computations over RTL. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Memory.
Require Import Registers.
Require Import Op.
Require Import RTL.
Require Import Lattice.
Require Import Kildall.
Require Import ValueDomain.
Require Import ValueAnalysis.
Require Import NeedDomain.
Require Import NeedOp.

(** * Part 1: the static analysis *)

Definition add_need_all (r: reg) (ne: nenv) : nenv :=
  NE.set r All ne.

Definition add_need (r: reg) (nv: nval) (ne: nenv) : nenv :=
  NE.set r (nlub nv (NE.get r ne)) ne.

Fixpoint add_needs_all (rl: list reg) (ne: nenv) : nenv :=
  match rl with
  | nil => ne
  | r1 :: rs => add_need_all r1 (add_needs_all rs ne)
  end.

Fixpoint add_needs (rl: list reg) (nvl: list nval) (ne: nenv) : nenv :=
  match rl, nvl with
  | nil, _ => ne
  | r1 :: rs, nil => add_needs_all rl ne
  | r1 :: rs, nv1 :: nvs => add_need r1 nv1 (add_needs rs nvs ne)
  end.

Definition add_ros_need_all (ros: reg + ident) (ne: nenv) : nenv :=
  match ros with
  | inl r => add_need_all r ne
  | inr s => ne
  end.

Definition add_opt_need_all (or: option reg) (ne: nenv) : nenv :=
  match or with
  | Some r => add_need_all r ne
  | None => ne
  end.

Definition kill (r: reg) (ne: nenv) : nenv := NE.set r Nothing ne.

Definition is_dead (v: nval) :=
  match v with Nothing => true | _ => false end.

Definition is_int_zero (v: nval) :=
  match v with I n => Int.eq n Int.zero | _ => false end.

Function transfer_builtin (app: VA.t) (ef: external_function) (args: list reg) (res: reg)
                          (ne: NE.t) (nm: nmem) : NA.t :=
  match ef, args with
  | EF_vload chunk, a1::nil =>
      (add_needs_all args (kill res ne),
       nmem_add nm (aaddr app a1) (size_chunk chunk))
  | EF_vload_global chunk id ofs, nil =>
      (add_needs_all args (kill res ne),
       nmem_add nm (Gl id ofs) (size_chunk chunk))
  | EF_vstore chunk, a1::a2::nil =>
      (add_need_all a1 (add_need a2 (store_argument chunk) (kill res ne)), nm)
  | EF_vstore_global chunk id ofs, a1::nil =>
      (add_need a1 (store_argument chunk) (kill res ne), nm)
  | EF_memcpy sz al, dst::src::nil =>
      if nmem_contains nm (aaddr app dst) sz then
       (add_needs_all args (kill res ne),
        nmem_add (nmem_remove nm (aaddr app dst) sz) (aaddr app src) sz)
      else (ne, nm)
  | EF_annot txt targs, _ =>
      (add_needs_all args (kill res ne), nm)
  | EF_annot_val txt targ, _ =>
      (add_needs_all args (kill res ne), nm)
  | _, _ =>
      (add_needs_all args (kill res ne), nmem_all) 
  end.

Definition transfer (f: function) (approx: PMap.t VA.t)
                    (pc: node) (after: NA.t) : NA.t :=
  let (ne, nm) := after in
  match f.(fn_code)!pc with
  | None =>
      NA.bot
  | Some (Inop s) =>
      after
  | Some (Iop op args res s) =>
      let nres := nreg ne res in
      if is_dead nres then after
      else if is_int_zero nres then (kill res ne, nm)
      else (add_needs args (needs_of_operation op nres) (kill res ne), nm)
  | Some (Iload chunk addr args dst s) =>
      let ndst := nreg ne dst in
      if is_dead ndst then after
      else if is_int_zero ndst then (kill dst ne, nm)
      else (add_needs_all args (kill dst ne),
            nmem_add nm (aaddressing approx!!pc addr args) (size_chunk chunk))
  | Some (Istore chunk addr args src s) =>
      let p := aaddressing approx!!pc addr args in
      if nmem_contains nm p (size_chunk chunk)
      then (add_needs_all args (add_need src (store_argument chunk) ne),
            nmem_remove nm p (size_chunk chunk))
      else after
  | Some(Icall sig ros args res s) =>
      (add_needs_all args (add_ros_need_all ros (kill res ne)), nmem_all)
  | Some(Itailcall sig ros args) =>
      (add_needs_all args (add_ros_need_all ros NE.bot),
       nmem_dead_stack f.(fn_stacksize))
  | Some(Ibuiltin ef args res s) =>
      transfer_builtin approx!!pc ef args res ne nm
  | Some(Icond cond args s1 s2) =>
      (add_needs args (needs_of_condition cond) ne, nm)
  | Some(Ijumptable arg tbl) =>
      (add_need_all arg ne, nm)
  | Some(Ireturn optarg) =>
      (add_opt_need_all optarg ne, nmem_dead_stack f.(fn_stacksize))
  end.

Module DS := Backward_Dataflow_Solver(NA)(NodeSetBackward).

Definition analyze (approx: PMap.t VA.t) (f: function): option (PMap.t NA.t) :=
  DS.fixpoint f.(fn_code) successors_instr
              (transfer f approx).

(** * Part 2: the code transformation *)

Definition transf_instr (approx: PMap.t VA.t) (an: PMap.t NA.t) 
                        (pc: node) (instr: instruction) :=
  match instr with
  | Iop op args res s =>
      let nres := nreg (fst an!!pc) res in
      if is_dead nres then
        Inop s
      else if is_int_zero nres then
        Iop (Ointconst Int.zero) nil res s
      else if operation_is_redundant op nres then 
        match args with
        | arg :: _ => Iop Omove (arg :: nil) res s
        | nil => instr
        end
      else
        instr
  | Iload chunk addr args dst s =>
      let ndst := nreg (fst an!!pc) dst in
      if is_dead ndst then
        Inop s
      else if is_int_zero ndst then
        Iop (Ointconst Int.zero) nil dst s
      else
        instr
  | Istore chunk addr args src s =>
      let p := aaddressing approx!!pc addr args in
      if nmem_contains (snd an!!pc) p (size_chunk chunk)
      then instr
      else Inop s
  | Ibuiltin (EF_memcpy sz al) (dst :: src :: nil) res s =>
      if nmem_contains (snd an!!pc) (aaddr approx!!pc dst) sz
      then instr
      else Inop s
  | _ =>
      instr
  end.

Definition vanalyze := ValueAnalysis.analyze.

Definition transf_function (rm: romem) (f: function) : res function :=
  let approx := vanalyze rm f in
  match analyze approx f with
  | Some an =>
      OK {| fn_sig := f.(fn_sig);
            fn_params := f.(fn_params);
            fn_stacksize := f.(fn_stacksize);
            fn_code := PTree.map (transf_instr approx an) f.(fn_code);
            fn_entrypoint := f.(fn_entrypoint) |}
  | None =>
      Error (msg "Neededness analysis failed")
  end.


Definition transf_fundef (rm: romem) (fd: fundef) : res fundef :=
  AST.transf_partial_fundef (transf_function rm) fd.

Definition transf_program (p: program) : res program :=
  transform_partial_program (transf_fundef (romem_for_program p)) p.

