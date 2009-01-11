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

Definition is_goto_instr (b: option instruction) : option node :=
  match b with Some (Lnop s) => Some s | _ => None end.

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

Fixpoint branch_target_rec (f: LTL.function) (pc: node) (count: nat)
                           {struct count} : option node :=
  match count with
  | Datatypes.O => None
  | Datatypes.S count' =>
      match is_goto_instr f.(fn_code)!pc with
      | Some s => branch_target_rec f s count'
      | None => Some pc
      end
  end.

Definition branch_target (f: LTL.function) (pc: node) :=
  match branch_target_rec f pc 10%nat with
  | Some pc' => pc'
  | None => pc
  end.

(** The tunneling optimization simply rewrites all LTL basic blocks,
  replacing the destinations of the [Bgoto] and [Bcond] instructions
  with their final target, as computed by [branch_target]. *)

Definition tunnel_instr (f: LTL.function) (b: instruction) : instruction :=
  match b with
  | Lnop s =>
      Lnop (branch_target f s)
  | Lop op args res s =>
      Lop op args res (branch_target f s)
  | Lload chunk addr args dst s =>
      Lload chunk addr args dst (branch_target f s)
  | Lstore chunk addr args src s =>
      Lstore chunk addr args src (branch_target f s)
  | Lcall sig ros args res s =>
      Lcall sig ros args res (branch_target f s)
  | Ltailcall sig ros args =>
      Ltailcall sig ros args
  | Lcond cond args s1 s2 =>
      Lcond cond args (branch_target f s1) (branch_target f s2)
  | Lreturn or =>
      Lreturn or
  end.

Lemma wf_tunneled_code:
  forall (f: LTL.function),
  let tc := PTree.map (fun pc b => tunnel_instr f b) (fn_code f) in
  forall (pc: node), Plt pc (fn_nextpc f) \/ tc!pc = None.
Proof.
  intros. elim (fn_code_wf f pc); intro.
  left; auto. right; unfold tc.
  rewrite PTree.gmap; unfold option_map; rewrite H; auto.
Qed.

Definition tunnel_function (f: LTL.function) : LTL.function :=
  mkfunction
    (fn_sig f)
    (fn_params f)
    (fn_stacksize f)
    (PTree.map (fun pc b => tunnel_instr f b) (fn_code f))
    (branch_target f (fn_entrypoint f))
    (fn_nextpc f)
    (wf_tunneled_code f).

Definition tunnel_fundef (f: LTL.fundef) : LTL.fundef :=
  transf_fundef tunnel_function f.

Definition tunnel_program (p: LTL.program) : LTL.program :=
  transform_program tunnel_fundef p.

