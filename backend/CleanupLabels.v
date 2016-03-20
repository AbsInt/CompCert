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

(** Removal of useless labels introduced by the linearization pass.

  The linearization pass introduces one label for each node of the
  control-flow graph.  Many of these labels are never branched to,
  which can complicate further optimizations over linearized code.
  (There are no such optimizations yet.)  In preparation for these
  further optimizations, and to make the generated Linear code
  better-looking, the present pass removes labels that cannot be
  branched to. *)

Require Import FSets FSetAVL.
Require Import Coqlib Ordered.
Require Import Linear.

Module Labelset := FSetAVL.Make(OrderedPositive).

(** Compute the set of labels that are mentioned in branch instructions. *)

Definition add_label_branched_to (ls: Labelset.t) (i: instruction) :=
  match i with
  | Lgoto lbl => Labelset.add lbl ls
  | Lcond cond args lbl => Labelset.add lbl ls
  | Ljumptable arg tbl => List.fold_right Labelset.add ls tbl
  | _ => ls
  end.

Definition labels_branched_to (c: code) : Labelset.t :=
  List.fold_left add_label_branched_to c Labelset.empty.

(** Remove label declarations for labels that are not in
    the [bto] (branched-to) set. *)

Definition remove_unused (bto: Labelset.t) (i: instruction) (k: code) : code :=
  match i with
  | Llabel lbl =>
      if Labelset.mem lbl bto then i :: k else k
  | _ =>
      i :: k
  end.

Definition remove_unused_labels (bto: Labelset.t) (c: code) : code :=
  list_fold_right (remove_unused bto) c nil.

Definition cleanup_labels (c: code) :=
  remove_unused_labels (labels_branched_to c) c.

(** Entry points *)

Definition transf_function (f: function) : function :=
  mkfunction
     (fn_sig f)
     (fn_stacksize f)
     (cleanup_labels (fn_code f)).

Definition transf_fundef (f: fundef) : fundef :=
  AST.transf_fundef transf_function f.

Definition transf_program (p: program) : program :=
  AST.transform_program transf_fundef p.
