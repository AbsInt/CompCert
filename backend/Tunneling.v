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

Require Import FunInd.
Require Import Coqlib Maps UnionFind.
Require Import AST.
Require Import LTL.

(** Branch tunneling shortens sequences of branches (with no intervening
  computations) by rewriting the branch and conditional branch instructions
  so that they jump directly to the end of the branch sequence.
  For example:
<<
     L1: branch L2;                       L1: branch L3;
     L2; branch L3;            becomes    L2: branch L3;
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
  better code, e.g. by revealing that some [branch] instructions are
  dead code (as the "branch L3" in the example above).
*)

(** The naive implementation of branch tunneling would replace
  any branch to a node [pc] by a branch to the node
  [branch_target f pc], defined as follows:
<<
  branch_target f pc = branch_target f pc'  if f(pc) = branch pc'
                     = pc                   otherwise
>>
  However, this definition can fail to terminate if
  the program can contain loops consisting only of branches, as in
<<
     L1: branch L1;
>>
  or
<<
     L1: branch L2;
     L2: branch L1;
>>
  Coq warns us of this fact by not accepting the definition
  of [branch_target] above.

  To handle this problem, we proceed in two passes:

- The first pass populates a union-find data structure, adding equalities
  between PCs of blocks that are connected by branches and no other
  computation.

- The second pass rewrites the code, replacing every branch to a node [pc]
  by a branch to the canonical representative of the equivalence class of [pc].
*)

(** * Construction of the union-find data structure *)

Module U := UnionFind.UF(PTree).

(** We start populating the union-find data structure by adding
    equalities [pc = pc'] for every block [pc: branch pc'] in the function. *)

Definition record_branch (uf: U.t) (pc: node) (b: bblock) : U.t :=
  match b with
  | Lbranch s :: _ => U.union uf pc s
  | _ => uf
  end.

Definition record_branches (f: LTL.function) : U.t :=
  PTree.fold record_branch f.(fn_code) U.empty.

(** An additional optimization opportunity comes from conditional branches.
    Consider a block [pc: cond ifso ifnot].  If the [ifso] case
    and the [ifnot] case jump to the same block [pc']
    (modulo intermediate branches), the block can be simplified into
    [pc: branch pc'], and the equality [pc = pc'] can be added to the
    union-find data structure. *)

(** In rare cases, the extra equation [pc = pc'] introduced by the
    simplification of a conditional branch can trigger further simplifications
    of other conditional branches.  We therefore iterate the analysis
    until no optimizable conditional branch remains. *)

(** The code [c] (first component of the [st] triple) starts identical
    to the code [fn.(fn_code)] of the current function, but each time
    conditional branch at [pc] is optimized, we remove the block at
    [pc] from the code [c].  This guarantees termination of the
    iteration. *)

Definition record_cond (st: code * U.t * bool) (pc: node) (b: bblock) : code * U.t * bool :=
   match b with
  | Lcond cond args s1 s2 :: _ =>
      let '(c, u, _) := st in
      if peq (U.repr u s1) (U.repr u s2)
      then (PTree.remove pc c, U.union u pc s1, true)
      else st
  | _ =>
      st
  end.

Definition record_conds_1 (cu: code * U.t) : code * U.t * bool :=
  let (c, u) := cu in PTree.fold record_cond c (c, u, false).

Definition measure_state (cu: code * U.t) : nat :=
  PTree_Properties.cardinal (fst cu).

Function record_conds (cu: code * U.t) {measure measure_state cu} : U.t :=
  let (cu', changed) := record_conds_1 cu in
  if changed then record_conds cu' else snd cu.
Proof.
  intros [c0 u0] [c1 u1].
  set (P := fun (c: code) (s: code * U.t * bool) =>
              (forall pc, c!pc = None -> (fst (fst s))!pc = c0!pc) /\
              (PTree_Properties.cardinal (fst (fst s))
               + (if snd s then 1 else 0)
               <= PTree_Properties.cardinal c0)%nat).
  assert (A: P c0 (PTree.fold record_cond c0 (c0, u0, false))).
  { apply PTree_Properties.fold_rec; unfold P.
  - intros. destruct H0; split; auto. intros. rewrite <- H in H2. auto.
  - simpl; split; intros. auto.  simpl; lia.
  - intros cd [[c u] changed] pc b NONE SOME [HR1 HR2]. simpl. split.
    + intros p EQ. rewrite PTree.gsspec in EQ. destruct (peq p pc); try discriminate.
      unfold record_cond. destruct b as [ | [] b ]; auto.
      destruct (peq (U.repr u s1) (U.repr u s2)); auto.
      simpl. rewrite PTree.gro by auto. auto.
    + unfold record_cond. destruct b as [ | [] b ]; auto.
      destruct (peq (U.repr u s1) (U.repr u s2)); auto.
      simpl in *.
      assert (SOME': c!pc = Some (Lcond cond args s1 s2 :: b)).
      { rewrite HR1 by auto. auto. } 
      generalize (PTree_Properties.cardinal_remove SOME').
      destruct changed; lia.
  }
  unfold record_conds_1, measure_state; intros. 
  destruct A as [_ A]. rewrite teq in A. simpl in *.
  lia.
Qed.

Definition record_gotos (f: LTL.function) : U.t :=
  record_conds (f.(fn_code), record_branches f).

(** * Code transformation *)

(** The code transformation rewrites all LTL instruction, replacing every
  successor [s] of every instruction by the canonical representative
  of its equivalence class in the union-find data structure.
  Additionally, [Lcond] conditional branches are turned into [Lbranch]
  unconditional branches whenever possible. *)

Definition tunnel_instr (u: U.t) (i: instruction) : instruction :=
  match i with
  | Lbranch s => Lbranch (U.repr u s)
  | Lcond cond args s1 s2 =>
      let s1' := U.repr u s1 in let s2' := U.repr u s2 in
      if peq s1' s2'
      then Lbranch s1'
      else Lcond cond args s1' s2'
  | Ljumptable arg tbl => Ljumptable arg (List.map (U.repr u) tbl)
  | _ => i
  end.

Definition tunnel_block (u: U.t) (b: bblock) : bblock :=
  List.map (tunnel_instr u) b.

Definition tunnel_function (f: LTL.function) : LTL.function :=
  let u := record_gotos f in
  mkfunction
    (fn_sig f)
    (fn_stacksize f)
    (PTree.map1 (tunnel_block u) (fn_code f))
    (U.repr u (fn_entrypoint f)).

Definition tunnel_fundef (f: LTL.fundef) : LTL.fundef :=
  transf_fundef tunnel_function f.

Definition tunnel_program (p: LTL.program) : LTL.program :=
  transform_program tunnel_fundef p.
