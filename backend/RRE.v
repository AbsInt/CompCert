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

(** Redundant Reloads Elimination *)

Require Import Coqlib.
Require Import AST.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Import Linear.

(** * Equations between slots and machine registers *)

(** The RRE pass keeps track of which register holds the value of which
  stack slot, using sets of equations like the following. *)

Record equation := mkeq { e_reg: mreg; e_slot: slot }.

Definition equations : Type := list equation.

Fixpoint find_reg_containing (s: slot) (eqs: equations) : option mreg :=
  match eqs with
  | nil => None
  | e :: eqs' => if slot_eq (e_slot e) s then Some (e_reg e) else find_reg_containing s eqs'
  end.

Definition eq_equation (eq1 eq2: equation) : {eq1=eq2} + {eq1<>eq2}.
Proof.
  generalize slot_eq mreg_eq. decide equality.
Defined.

Definition contains_equation (s: slot) (r: mreg) (eqs: equations) : bool :=
  In_dec eq_equation (mkeq r s) eqs.

(** Remove equations that are invalidated by an assignment to location [l]. *)

Fixpoint kill_loc (l: loc) (eqs: equations) : equations :=
  match eqs with
  | nil => nil
  | e :: eqs' =>
      if Loc.diff_dec (S (e_slot e)) l && Loc.diff_dec (R (e_reg e)) l
      then e :: kill_loc l eqs'
      else kill_loc l eqs'
  end.

(** Same, for a list of locations [ll]. *)

Definition kill_locs (ll: list loc) (eqs: equations) : equations :=
  List.fold_left (fun eqs l => kill_loc l eqs) ll eqs.

Definition kill_temps (eqs: equations) : equations :=
  kill_locs temporaries eqs.

Definition kill_at_move (eqs: equations) : equations :=
  kill_locs destroyed_at_move eqs.

Definition kill_op (op: operation) (eqs: equations) : equations :=
  match op with Omove => kill_at_move eqs | _ => kill_temps eqs end.

(** * Safety criterion *)

Definition is_incoming (s: slot) : bool :=
  match s with
  | Incoming _ _ => true
  | _ => false
  end.

(** Turning a [Lgetstack] into a register-to-register move is not always
  safe: at least on x86, the move destroys some registers 
  (those from [destroyed_at_move] list) while the [Lgetstack] does not.
  Therefore, we perform this transformation only if the destroyed
  registers are not used before being destroyed by a later
  [Lop], [Lload], [Lstore], [Lbuiltin], [Lcond] or [Ljumptable] operation. *)

Fixpoint safe_move_insertion (c: code) : bool :=
  match c with
  | Lgetstack s r :: c' =>
      negb(In_dec mreg_eq r destroyed_at_move_regs) && safe_move_insertion c'
  | Lsetstack r s :: c' =>
      negb(In_dec mreg_eq r destroyed_at_move_regs)
  | Lop op args res :: c' =>
      list_disjoint_dec mreg_eq args destroyed_at_move_regs
  | Lload chunk addr args res :: c' =>
      list_disjoint_dec mreg_eq args destroyed_at_move_regs
  | Lstore chunk addr args src :: c' =>
      list_disjoint_dec mreg_eq (src :: args) destroyed_at_move_regs
  | Lbuiltin ef args res :: c' =>
      list_disjoint_dec mreg_eq args destroyed_at_move_regs
  | Lcond cond args lbl :: c' =>
      list_disjoint_dec mreg_eq args destroyed_at_move_regs
  | Ljumptable arg tbl :: c' =>
      negb(In_dec mreg_eq arg destroyed_at_move_regs)
  | _ => false
  end.

(** * Code transformation *)

(** The following function eliminates [Lgetstack] instructions or turn them
  into register-to-register move whenever possible.  Simultaneously,
  it propagates valid (register, slot) equations across basic blocks. *)

(** [transf_code] is written in accumulator-passing style so that it runs
  in constant stack space.  The [k] parameter accumulates the instructions
  to be generated, in reverse order, and is then reversed at the end *)

Fixpoint transf_code (eqs: equations) (c: code) (k: code) : code :=
  match c with
  | nil => List.rev' k
  | Lgetstack s r :: c =>
      if is_incoming s then
        transf_code (kill_loc (R r) (kill_loc (R IT1) eqs)) c (Lgetstack s r :: k)
      else if contains_equation s r eqs then
        transf_code eqs c k
      else 
        match find_reg_containing s eqs with
        | Some r' => 
            if safe_move_insertion c then
              transf_code (kill_at_move (mkeq r s :: kill_loc (R r) eqs)) c (Lop Omove (r' :: nil) r :: k)
            else
              transf_code (mkeq r s :: kill_loc (R r) eqs) c (Lgetstack s r :: k)
        | None =>
            transf_code (mkeq r s :: kill_loc (R r) eqs) c (Lgetstack s r :: k)
        end
  | Lsetstack r s :: c =>
      transf_code (kill_at_move (mkeq r s :: kill_loc (S s) eqs)) c (Lsetstack r s :: k)
  | Lop op args res :: c =>
      transf_code (kill_loc (R res) (kill_op op eqs)) c (Lop op args res :: k)
  | Lload chunk addr args res :: c =>
      transf_code (kill_loc (R res) (kill_temps eqs)) c (Lload chunk addr args res :: k)
  | Lstore chunk addr args src :: c =>
      transf_code (kill_temps eqs) c (Lstore chunk addr args src :: k)
  | Lcall sg ros :: c =>
      transf_code nil c (Lcall sg ros :: k)
  | Ltailcall sg ros :: c =>
      transf_code nil c (Ltailcall sg ros :: k)
  | Lbuiltin ef args res :: c =>
      transf_code (kill_loc (R res) (kill_temps eqs)) c (Lbuiltin ef args res :: k)
  | Lannot ef args :: c =>
      transf_code eqs c (Lannot ef args :: k)
  | Llabel lbl :: c =>
      transf_code nil c (Llabel lbl :: k)
  | Lgoto lbl :: c =>
      transf_code nil c (Lgoto lbl :: k)
  | Lcond cond args lbl :: c =>
      transf_code (kill_temps eqs) c (Lcond cond args lbl :: k)
  | Ljumptable arg lbls :: c =>
      transf_code nil c (Ljumptable arg lbls :: k)
  | Lreturn :: c =>
      transf_code nil c (Lreturn :: k)
  end.

Definition transf_function (f: function) : function :=
  mkfunction
    (fn_sig f)
    (fn_stacksize f)
    (transf_code nil (fn_code f) nil).

Definition transf_fundef (fd: fundef) : fundef :=
  transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.

