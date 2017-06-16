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

(** Linearization of the control-flow graph: translation from LTL to Linear *)

Require Import FSets FSetAVL.
Require Import Coqlib Maps Ordered Errors Lattice Kildall.
Require Import AST Op Locations LTL Linear.

Open Scope error_monad_scope.

(** To translate from LTL to Linear, we must lay out the nodes
  of the LTL control-flow graph in some linear order, and insert
  explicit branches and conditional branches to make sure that
  each node jumps to its successors as prescribed by the
  LTL control-flow graph.  However, branches are not necessary
  if the fall-through behaviour of LTLin instructions already
  implements the desired flow of control.  For instance,
  consider the two LTL blocks
<<
    L1: Lop op args res; Lbranch L2
    L2: ...
>>
  If the instructions [L1] and [L2] are laid out consecutively in the LTLin
  code, we can generate the following Linear code:
<<
    L1: Lop op args res
    L2: ...
>>
  However, if this is not possible, an explicit [Lgoto] is needed:
<<
    L1: Lop op args res
        Lgoto L2
        ...
    L2: ...
>>
  The main challenge in code linearization is therefore to pick a
  ``good'' order for the nodes that exploits well the
  fall-through behavior.  Many clever trace picking heuristics
  have been developed for this purpose.

  In this file, we present linearization in a way that clearly
  separates the heuristic part (choosing an order for the basic blocks)
  from the actual code transformation parts.  We proceed in two passes:
- Choosing an order for the nodes.  This returns an enumeration of CFG
  nodes stating that they must be laid out in the order shown in the
  list.
- Generate Linear code where each node branches explicitly to its
  successors, except if one of these successors is the immediately
  following instruction.

  The beauty of this approach is that correct code is generated
  under surprisingly weak hypotheses on the enumeration of
  CFG nodes: it suffices that every reachable instruction occurs
  exactly once in the enumeration.  We therefore follow an approach
  based on validation a posteriori: a piece of untrusted Caml code
  implements the node enumeration heuristics, and the resulting
  enumeration is checked for correctness by Coq functions that are
  proved to be sound.
*)

(** * Determination of the order of basic blocks *)

(** We first compute a mapping from CFG nodes to booleans,
  indicating whether a CFG instruction is reachable or not.
  This computation is a trivial forward dataflow analysis
  where the transfer function is the identity: the successors
  of a reachable instruction are reachable, by the very
  definition of reachability. *)

Module DS := Dataflow_Solver(LBoolean)(NodeSetForward).

Definition reachable_aux (f: LTL.function) : option (PMap.t bool) :=
  DS.fixpoint
    (LTL.fn_code f) successors_block
    (fun pc r => r)
    f.(fn_entrypoint) true.

Definition reachable (f: LTL.function) : PMap.t bool :=
  match reachable_aux f with
  | None => PMap.init true
  | Some rs => rs
  end.

(** We then enumerate the nodes of reachable blocks.
  This task is performed by external, untrusted Caml code. *)

Parameter enumerate_aux: LTL.function -> PMap.t bool -> list node.

(** Now comes the a posteriori validation of a node enumeration. *)

Module Nodeset := FSetAVL.Make(OrderedPositive).

(** Build a [Nodeset.t] from a list of nodes, checking that the list
  contains no duplicates. *)

Fixpoint nodeset_of_list (l: list node) (s: Nodeset.t)
                         {struct l}: res Nodeset.t :=
  match l with
  | nil => OK s
  | hd :: tl =>
      if Nodeset.mem hd s
      then Error (msg "Linearize: duplicates in enumeration")
      else nodeset_of_list tl (Nodeset.add hd s)
  end.

Definition check_reachable_aux
     (reach: PMap.t bool) (s: Nodeset.t)
     (ok: bool) (pc: node) (bb: LTL.bblock) : bool :=
  if reach!!pc then ok && Nodeset.mem pc s else ok.

Definition check_reachable
     (f: LTL.function) (reach: PMap.t bool) (s: Nodeset.t) : bool :=
  PTree.fold (check_reachable_aux reach s) f.(LTL.fn_code) true.

Definition enumerate (f: LTL.function) : res (list node) :=
  let reach := reachable f in
  let enum := enumerate_aux f reach in
  do s <- nodeset_of_list enum Nodeset.empty;
  if check_reachable f reach s
  then OK enum
  else Error (msg "Linearize: wrong enumeration").

(** * Translation from LTL to Linear *)

(** We now flatten the structure of the CFG graph, laying out
  LTL blocks consecutively in the order computed by [enumerate],
  and inserting branches to the labels of sucessors if necessary.
  Whether to insert a branch or not is determined by
  the [starts_with] function below.

  For LTL conditional branches [Lcond cond args s1 s2],
  we have two possible translations:
<<
      Lcond cond args s1;       or     Lcond (not cond) args s2;
      Lgoto s2                         Lgoto s1
>>
  We favour the first translation if [s2] is the label of the
  next instruction, and the second if [s1] is the label of the
  next instruction, thus avoiding the insertion of a redundant [Lgoto]
  instruction. *)

Fixpoint starts_with (lbl: label) (k: code) {struct k} : bool :=
  match k with
  | Llabel lbl' :: k' => if peq lbl lbl' then true else starts_with lbl k'
  | _ => false
  end.

Definition add_branch (s: label) (k: code) : code :=
  if starts_with s k then k else Lgoto s :: k.

Fixpoint linearize_block (b: LTL.bblock) (k: code) : code :=
  match b with
  | nil => k
  | LTL.Lop op args res :: b' =>
      Lop op args res :: linearize_block b' k
  | LTL.Lload chunk addr args dst :: b' =>
      Lload chunk addr args dst :: linearize_block b' k
  | LTL.Lgetstack sl ofs ty dst :: b' =>
      Lgetstack sl ofs ty dst :: linearize_block b' k
  | LTL.Lsetstack src sl ofs ty :: b' =>
      Lsetstack src sl ofs ty :: linearize_block b' k
  | LTL.Lstore chunk addr args src :: b' =>
      Lstore chunk addr args src :: linearize_block b' k
  | LTL.Lcall sig ros :: b' =>
      Lcall sig ros :: linearize_block b' k
  | LTL.Ltailcall sig ros :: b' =>
      Ltailcall sig ros :: k
  | LTL.Lbuiltin ef args res :: b' =>
      Lbuiltin ef args res :: linearize_block b' k
  | LTL.Lbranch s :: b' =>
      add_branch s k
  | LTL.Lcond cond args s1 s2 :: b' =>
      if starts_with s1 k then
        Lcond (negate_condition cond) args s2 :: add_branch s1 k
      else
        Lcond cond args s1 :: add_branch s2 k
  | LTL.Ljumptable arg tbl :: b' =>
      Ljumptable arg tbl :: k
  | LTL.Lreturn :: b' =>
      Lreturn :: k
  end.

(** Linearize a function body according to an enumeration of its nodes.  *)

Definition linearize_node (f: LTL.function) (pc: node) (k: code) : code :=
  match f.(LTL.fn_code)!pc with
  | None => k
  | Some b => Llabel pc :: linearize_block b k
  end.

Definition linearize_body (f: LTL.function) (enum: list node) : code :=
  list_fold_right (linearize_node f) enum nil.

(** * Entry points for code linearization *)

Definition transf_function (f: LTL.function) : res Linear.function :=
  do enum <- enumerate f;
  OK (mkfunction
       (LTL.fn_sig f)
       (LTL.fn_stacksize f)
       (add_branch (LTL.fn_entrypoint f) (linearize_body f enum))).

Definition transf_fundef (f: LTL.fundef) : res Linear.fundef :=
  AST.transf_partial_fundef transf_function f.

Definition transf_program (p: LTL.program) : res Linear.program :=
  transform_partial_program transf_fundef p.
