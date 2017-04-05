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

(** Branch tunneling (optimization of branches to branches). *)

Require Import Coqlib Maps UnionFind.
Require Import AST.
Require Import LTL.

(** Branch tunneling shortens sequences of branches (with no intervening
  computations) by rewriting the branch and conditional branch instructions
  so that they jump directly to the end of the branch sequence.
  For example:
<<
     L1: nop L2;                          L1: nop L3;
     L2; nop L3;               becomes    L2: nop L3;
     L3: instr;                           L3: instr;
     L4: if (cond) goto L1;               L4: if (cond) goto L3;
>>
  This optimization can be applied to several of our intermediate
  languages.  We choose to perform it on the [LTL] language,
  after register allocation but before code linearization.
  Register allocation can delete instructions (such as dead
  computations or useless moves), therefore there are more
  opportunities for tunneling after allocation than before.
  Symmetrically, prior tunneling helps linearization to produce
  better code, e.g. by revealing that some [nop] instructions are
  dead code (as the "nop L3" in the example above).
*)

(** The naive implementation of branch tunneling would replace
  any branch to a node [pc] by a branch to the node
  [branch_target f pc], defined as follows:
<<
  branch_target f pc = branch_target f pc'  if f(pc) = nop pc'
                     = pc                   otherwise
>>
  However, this definition can fail to terminate if
  the program can contain loops consisting only of branches, as in
<<
     L1: nop L1;
>>
  or
<<   L1: nop L2;
     L2: nop L1;
>>
  Coq warns us of this fact by not accepting the definition
  of [branch_target] above.

  To handle this problem, we proceed in two passes.  The first pass
  populates a union-find data structure, adding equalities [pc = pc']
  for every instruction [pc: nop pc'] in the function. *)

Module U := UnionFind.UF(PTree).

Definition record_goto (uf: U.t) (pc: node) (b: bblock) : U.t :=
  match b with
  | Lbranch s :: _ => U.union uf pc s
  | _ => uf
  end.

Definition record_gotos (f: LTL.function) : U.t :=
  PTree.fold record_goto f.(fn_code) U.empty.

(** The second pass rewrites all LTL instructions, replacing every
  successor [s] of every instruction by the canonical representative
  of its equivalence class in the union-find data structure. *)

Definition tunnel_instr (uf: U.t) (i: instruction) : instruction :=
  match i with
  | Lbranch s => Lbranch (U.repr uf s)
  | Lcond cond args s1 s2 =>
      let s1' := U.repr uf s1 in let s2' := U.repr uf s2 in
      if peq s1' s2'
      then Lbranch s1'
      else Lcond cond args s1' s2'
  | Ljumptable arg tbl => Ljumptable arg (List.map (U.repr uf) tbl)
  | _ => i
  end.

Definition tunnel_block (uf: U.t) (b: bblock) : bblock :=
  List.map (tunnel_instr uf) b.

Definition tunnel_function (f: LTL.function) : LTL.function :=
  let uf := record_gotos f in
  mkfunction
    (fn_sig f)
    (fn_stacksize f)
    (PTree.map1 (tunnel_block uf) (fn_code f))
    (U.repr uf (fn_entrypoint f)).

Definition tunnel_fundef (f: LTL.fundef) : LTL.fundef :=
  transf_fundef tunnel_function f.

Definition tunnel_program (p: LTL.program) : LTL.program :=
  transform_program tunnel_fundef p.
