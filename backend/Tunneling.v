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

Require Import Coqlib.
Require Import Maps.
Require Import UnionFind.
Require Import AST.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import LTL.

(** Branch tunneling shortens sequences of branches (with no intervening
  computations) by rewriting the branch and conditional branch instructions
  so that they jump directly to the end of the branch sequence.
  For example:
<<
     L1: goto L2;                          L1: goto L3;
     L2; goto L3;               becomes    L2: goto L3;
     L3: instr;                            L3: instr;
     L4: if (cond) goto L1;                L4: if (cond) goto L3;
>>
  This optimization can be applied to several of our intermediate
  languages.  We choose to perform it on the [LTL] language,
  after register allocation but before code linearization.
  Register allocation can delete instructions (such as dead
  computations or useless moves), therefore there are more
  opportunities for tunneling after allocation than before.
  Symmetrically, prior tunneling helps linearization to produce
  better code, e.g. by revealing that some [goto] instructions are
  dead code (as the "goto L3" in the example above).
*)

(** [branch_target f pc] returns the node of the CFG that is at
  the end of the branch sequence starting at [pc].  If the instruction
  at [pc] is not a [goto], [pc] itself is returned.
  The naive definition of [branch_target] is:
<<
  branch_target f pc = branch_target f pc'  if f(pc) = goto pc'
                     = pc                   otherwise
>>
  However, this definition can fail to terminate if
  the program can contain loops consisting only of branches, as in
<<
     L1: goto L1;
>>
  or
<<   L1: goto L2;
     L2: goto L1;
>>
  Coq warns us of this fact by not accepting the definition 
  of [branch_target] above.

  The proper way to handle this problem is to detect [goto] cycles
  in the control-flow graph.  For simplicity, we just bound arbitrarily
  the number of iterations performed by [branch_target],
  never chasing more than 10 [goto] instructions.  (This many
  consecutive branches is rarely, if even, encountered.)  

  For a sequence of more than 10 [goto] instructions, we can return
  (as branch target) any of the labels of the [goto] instructions.
  This is semantically correct in any case.  However, the proof
  is simpler if we return the label of the first [goto] in the sequence.
*)

Module U := UnionFind.UF(PTree).

Definition record_goto (uf: U.t) (pc: node) (i: instruction) : U.t :=
  match i with
  | Lnop s => U.union uf pc s
  | _ => uf
  end.

Definition record_gotos (f: LTL.function) : U.t :=
  PTree.fold record_goto f.(fn_code) U.empty.

(** The tunneling optimization simply rewrites all LTL basic blocks,
  replacing the destinations of the [Bgoto] and [Bcond] instructions
  with their final target, as computed by [branch_target]. *)

Definition tunnel_instr (uf: U.t) (b: instruction) : instruction :=
  match b with
  | Lnop s =>
      Lnop (U.repr uf s)
  | Lop op args res s =>
      Lop op args res (U.repr uf s)
  | Lload chunk addr args dst s =>
      Lload chunk addr args dst (U.repr uf s)
  | Lstore chunk addr args src s =>
      Lstore chunk addr args src (U.repr uf s)
  | Lcall sig ros args res s =>
      Lcall sig ros args res (U.repr uf s)
  | Ltailcall sig ros args =>
      Ltailcall sig ros args
  | Lbuiltin ef args res s =>
      Lbuiltin ef args res (U.repr uf s)
  | Lcond cond args s1 s2 =>
      Lcond cond args (U.repr uf s1) (U.repr uf s2)
  | Ljumptable arg tbl =>
      Ljumptable arg (List.map (U.repr uf) tbl)
  | Lreturn or =>
      Lreturn or
  end.

Definition tunnel_function (f: LTL.function) : LTL.function :=
  let uf := record_gotos f in
  mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (PTree.map (fun pc b => tunnel_instr uf b) (fn_code f))
    (U.repr uf (fn_entrypoint f)).

Definition tunnel_fundef (f: LTL.fundef) : LTL.fundef :=
  transf_fundef tunnel_function f.

Definition tunnel_program (p: LTL.program) : LTL.program :=
  transform_program tunnel_fundef p.

