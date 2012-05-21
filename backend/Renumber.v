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

(** Postorder renumbering of RTL control-flow graphs. *)

Require Import Coqlib.
Require Import Maps.
Require Import Postorder.
Require Import AST.
Require Import RTL.

(** CompCert's dataflow analyses (module [Kildall]) are more precise
  and run faster when the sequence [1, 2, 3, ...]  is a postorder
  enumeration of the nodes of the control-flow graph.  This property
  can be guaranteed when generating the CFG (module [RTLgen]), but
  is, however, invalidated by further RTL optimization passes such as
  [Inlining].  

  In this module, we renumber the nodes of RTL control-flow graphs
  to restore the postorder property given above.  In passing,
  we also eliminate CFG nodes that are not reachable from the entry point:
  these nodes are dead code. *)

Section RENUMBER.

Variable pnum: PTree.t positive.   (**r a postorder numbering *)

Definition renum_pc (pc: node) : node :=
  match pnum!pc with
  | Some pc' => pc'
  | None => 1%positive          (**r impossible case, never exercised *)
  end.

Definition renum_instr (i: instruction) : instruction :=
  match i with
  | Inop s => Inop (renum_pc s)
  | Iop op args res s => Iop op args res (renum_pc s)
  | Iload chunk addr args res s => Iload chunk addr args res (renum_pc s)
  | Istore chunk addr args src s => Istore chunk addr args src (renum_pc s)
  | Icall sg ros args res s => Icall sg ros args res (renum_pc s)
  | Itailcall sg ros args => i
  | Ibuiltin ef args res s => Ibuiltin ef args res (renum_pc s)
  | Icond cond args s1 s2 => Icond cond args (renum_pc s1) (renum_pc s2)
  | Ijumptable arg tbl => Ijumptable arg (List.map renum_pc tbl)
  | Ireturn or => i
  end.

Definition renum_node (c': code) (pc: node) (i: instruction) : code :=
  match pnum!pc with
  | None => c'
  | Some pc' => PTree.set pc' (renum_instr i) c'
  end.

Definition renum_cfg (c: code) : code :=
  PTree.fold renum_node c (PTree.empty instruction).

End RENUMBER.

Definition transf_function (f: function) : function :=
  let pnum := postorder (successors f) f.(fn_entrypoint) in
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (renum_cfg pnum f.(fn_code))
    (renum_pc pnum f.(fn_entrypoint)).

Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  AST.transform_program transf_fundef p.
