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
Require Import Maps.
Require Import AST.
Require Import Values.
Require Import Globalenvs.
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
Qed.

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

Fixpoint transf_code (eqs: equations) (c: code) : code :=
  match c with
  | nil => nil
  | Lgetstack s r :: c =>
      if is_incoming s then
        Lgetstack s r :: transf_code (kill_loc (R r) (kill_loc (R IT1) eqs)) c
      else if contains_equation s r eqs then
        transf_code eqs c
      else 
        match find_reg_containing s eqs with
        | Some r' => 
            if safe_move_insertion c then
              Lop Omove (r' :: nil) r :: transf_code (kill_at_move (mkeq r s :: kill_loc (R r) eqs)) c
            else
              Lgetstack s r:: transf_code (mkeq r s :: kill_loc (R r) eqs) c
        | None =>
            Lgetstack s r:: transf_code (mkeq r s :: kill_loc (R r) eqs) c
        end
  | Lsetstack r s :: c =>
      Lsetstack r s :: transf_code (kill_at_move (mkeq r s :: kill_loc (S s) eqs)) c
  | Lop op args res :: c =>
      Lop op args res :: transf_code (kill_loc (R res) (kill_op op eqs)) c
  | Lload chunk addr args res :: c =>
      Lload chunk addr args res :: transf_code (kill_loc (R res) (kill_temps eqs)) c
  | Lstore chunk addr args src :: c =>
      Lstore chunk addr args src :: transf_code (kill_temps eqs) c
  | Lcall sg ros :: c =>
      Lcall sg ros :: transf_code nil c
  | Ltailcall sg ros :: c =>
      Ltailcall sg ros :: transf_code nil c
  | Lbuiltin ef args res :: c =>
      Lbuiltin ef args res :: transf_code (kill_loc (R res) (kill_temps eqs)) c
  | Lannot ef args :: c =>
      Lannot ef args :: transf_code eqs c
  | Llabel lbl :: c =>
      Llabel lbl :: transf_code nil c
  | Lgoto lbl :: c =>
      Lgoto lbl :: transf_code nil c
  | Lcond cond args lbl :: c =>
      Lcond cond args lbl :: transf_code (kill_temps eqs) c
  | Ljumptable arg lbls :: c =>
      Ljumptable arg lbls :: transf_code nil c
  | Lreturn :: c =>
      Lreturn :: transf_code nil c
  end.

Definition transf_function (f: function) : function :=
  mkfunction
    (fn_sig f)
    (fn_stacksize f)
    (transf_code nil (fn_code f)).

Definition transf_fundef (fd: fundef) : fundef :=
  transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.

