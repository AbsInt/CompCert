(** Linearization of the control-flow graph: 
    translation from LTL to Linear *)

Require Import Coqlib.
Require Import Maps.
Require Import Sets.
Require Import AST.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import Linear.
Require Import Kildall.
Require Import Lattice.

(** To translate from LTL to Linear, we must layout the basic blocks
  of the LTL control-flow graph in some linear order, and insert
  explicit branches and conditional branches to make sure that
  each basic block jumps to its successors as prescribed by the
  LTL control-flow graph.  However, branches are not necessary
  if the fall-through behaviour of Linear instructions already
  implements the desired flow of control.  For instance,
  consider the two LTL basic blocks
<<
    L1: Bop op args res (Bgoto L2)
    L2: ...
>>
  If the blocks [L1] and [L2] are laid out consecutively in the Linear
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
  ``good'' order for the basic blocks that exploits well the
  fall-through behavior.  Many clever trace picking heuristics
  have been developed for this purpose.  

  In this file, we present linearization in a way that clearly
  separates the heuristic part (choosing an order for the basic blocks)
  from the actual code transformation parts.  We proceed in three passes:
- Choosing an order for the basic blocks.  This returns an enumeration
  of CFG nodes stating that the basic blocks must be laid out in
  the order shown in the list.
- Generate naive Linear code where each basic block branches explicitly
  to its successors, even if one of these successors is the next basic
  block.
- Simplify the naive Linear code, removing unconditional branches to
  a label that immediately follows:
<<
          ...                                  ...
          Igoto L1;           becomes      L1: ...
      L1: ...
>>
  The beauty of this approach is that correct code is generated
  under surprisingly weak hypotheses on the enumeration of
  CFG nodes: it suffices that every reachable basic block occurs
  exactly once in the enumeration.  While the enumeration heuristic we use
  is quite trivial, it is easy to implement more sophisticated
  trace picking heuristics: as long as they satisfy the property above,
  we do not need to re-do the proof of semantic preservation.
  The enumeration could even be performed by external, untrusted
  Caml code, then verified (for the property above) by certified Coq code.
*)

(** * Determination of the order of basic blocks *)

(** We first compute a mapping from CFG nodes to booleans,
  indicating whether a CFG basic block is reachable or not.
  This computation is a trivial forward dataflow analysis
  where the transfer function is the identity: the successors
  of a reachable block are reachable, by the very
  definition of reachability. *)

Module DS := Dataflow_Solver(LBoolean).

Definition reachable_aux (f: LTL.function) : option (PMap.t bool) :=
  DS.fixpoint
    (successors f)
    (Psucc f.(fn_entrypoint))
    (fun pc r => r)
    ((f.(fn_entrypoint), true) :: nil).

Definition reachable (f: LTL.function) : PMap.t bool :=
  match reachable_aux f with  
  | None => PMap.init true
  | Some rs => rs
  end.

(** We then enumerate the nodes of reachable basic blocks.  The heuristic
  we take is trivial: nodes are enumerated in decreasing numerical
  order.  Remember that CFG nodes are positive integers, and that
  the [RTLgen] pass allocated fresh nodes 1, 2, 3, ..., but generated
  instructions in roughly reverse control-flow order: often,
  a basic block at label [n] has [n-1] as its only successor.
  Therefore, by enumerating reachable nodes in decreasing order,
  we recover a reasonable layout of basic blocks that globally respects
  the structure of the original Cminor code. *)

Definition enumerate (f: LTL.function) : list node :=
  let reach := reachable f in
  positive_rec (list node) nil
    (fun pc nodes => if reach!!pc then pc :: nodes else nodes)
    (Psucc f.(fn_entrypoint)).

(** * Translation from LTL to Linear *)

(** We now flatten the structure of the CFG graph, laying out
  basic blocks consecutively in the order computed by [enumerate],
  and inserting a branch at the end of every basic block.

  For blocks ending in a conditional branch [Bcond cond args s1 s2],
  we have two possible translations:
<<
      Lcond cond args s1;       or     Lcond (not cond) args s2;
      Lgoto s2                         Lgoto s1
>>
  We favour the first translation if [s2] is the label of the
  next instruction, and the second if [s1] is the label of the
  next instruction, thus exhibiting more opportunities for
  fall-through optimization later. *)

Fixpoint starts_with (lbl: label) (k: code) {struct k} : bool :=
  match k with
  | Llabel lbl' :: k' => if peq lbl lbl' then true else starts_with lbl k'
  | _ => false
  end.

Fixpoint linearize_block (b: block) (k: code) {struct b} : code :=
  match b with
  | Bgetstack s r b =>
      Lgetstack s r :: linearize_block b k
  | Bsetstack r s b =>
      Lsetstack r s :: linearize_block b k
  | Bop op args res b =>
      Lop op args res :: linearize_block b k
  | Bload chunk addr args dst b =>
      Lload chunk addr args dst :: linearize_block b k
  | Bstore chunk addr args src b =>
      Lstore chunk addr args src :: linearize_block b k
  | Bcall sig ros b =>
      Lcall sig ros :: linearize_block b k
  | Balloc b =>
      Lalloc :: linearize_block b k
  | Bgoto s =>
      Lgoto s :: k
  | Bcond cond args s1 s2 =>
      if starts_with s1 k then
        Lcond (negate_condition cond) args s2 :: Lgoto s1 :: k
      else
        Lcond cond args s1 :: Lgoto s2 :: k
  | Breturn =>
      Lreturn :: k
  end.

(* Linearize a function body according to an enumeration of its
   nodes.  *)

Fixpoint linearize_body (f: LTL.function) (enum: list node)
                        {struct enum} : code :=
  match enum with
  | nil => nil
  | pc :: rem =>
      match f.(LTL.fn_code)!pc with
      | None => linearize_body f rem
      | Some b => Llabel pc :: linearize_block b (linearize_body f rem)
      end
  end.

Definition linearize_function (f: LTL.function) : Linear.function :=
  mkfunction
    (LTL.fn_sig f)
    (LTL.fn_stacksize f)
    (linearize_body f (enumerate f)).

(** * Cleanup of the linearized code *)

(** We now eliminate [Lgoto] instructions that branch to an
  immediately following label: these are redundant, as the fall-through
  behaviour obtained by removing the [Lgoto] instruction is
  semantically equivalent. *)

Fixpoint cleanup_code (c: code) {struct c} : code :=
  match c with
  | nil => nil
  | Lgoto lbl :: c' => 
      if starts_with lbl c'
      then cleanup_code c'
      else Lgoto lbl :: cleanup_code c'
  | i :: c' =>
      i :: cleanup_code c'
  end.

Definition cleanup_function (f: Linear.function) : Linear.function :=
  mkfunction
    (fn_sig f)
    (fn_stacksize f)
    (cleanup_code f.(fn_code)).

(** * Entry points for code linearization *)

Definition transf_function (f: LTL.function) : Linear.function :=
  cleanup_function (linearize_function f).

Definition transf_fundef (f: LTL.fundef) : Linear.fundef :=
  AST.transf_fundef transf_function f.

Definition transf_program (p: LTL.program) : Linear.program :=
  transform_program transf_fundef p.
