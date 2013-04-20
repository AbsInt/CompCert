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

(** Computation of resource bounds for Linear code. *)

Require Import Coqlib.
Require Import AST.
Require Import Op.
Require Import Locations.
Require Import Linear.
Require Import Conventions.

(** * Resource bounds for a function *)

(** The [bounds] record capture how many local and outgoing stack slots
  and callee-save registers are used by a function. *)

(** We demand that all bounds are positive or null.
  These properties are used later to reason about the layout of
  the activation record. *)

Record bounds : Type := mkbounds {
  bound_local: Z;
  bound_int_callee_save: Z;
  bound_float_callee_save: Z;
  bound_outgoing: Z;
  bound_stack_data: Z;
  bound_local_pos: bound_local >= 0;
  bound_int_callee_save_pos: bound_int_callee_save >= 0;
  bound_float_callee_save_pos: bound_float_callee_save >= 0;
  bound_outgoing_pos: bound_outgoing >= 0;
  bound_stack_data_pos: bound_stack_data >= 0
}.

(** The following predicates define the correctness of a set of bounds
    for the code of a function. *)

Section WITHIN_BOUNDS.

Variable b: bounds.

Definition mreg_within_bounds (r: mreg) :=
  index_int_callee_save r < bound_int_callee_save b
  /\ index_float_callee_save r < bound_float_callee_save b.

Definition slot_within_bounds (sl: slot) (ofs: Z) (ty: typ) :=
  match sl with
  | Local => ofs + typesize ty <= bound_local b
  | Outgoing => ofs + typesize ty <= bound_outgoing b
  | Incoming => True
  end.

Definition instr_within_bounds (i: instruction) :=
  match i with
  | Lgetstack sl ofs ty r => slot_within_bounds sl ofs ty /\ mreg_within_bounds r
  | Lsetstack r sl ofs ty => slot_within_bounds sl ofs ty
  | Lop op args res => mreg_within_bounds res
  | Lload chunk addr args dst => mreg_within_bounds dst
  | Lcall sig ros => size_arguments sig <= bound_outgoing b
  | Lbuiltin ef args res =>
      forall r, In r res \/ In r (destroyed_by_builtin ef) -> mreg_within_bounds r
  | Lannot ef args =>
      forall sl ofs ty, In (S sl ofs ty) args -> slot_within_bounds sl ofs ty
  | _ => True
  end.

End WITHIN_BOUNDS.

Definition function_within_bounds (f: function) (b: bounds) : Prop :=
  forall instr, In instr f.(fn_code) -> instr_within_bounds b instr.

(** * Inference of resource bounds for a function *)

(** The resource bounds for a function are computed by a linear scan
  of its instructions. *)

Section BOUNDS.

Variable f: function.

(** In the proof of the [Stacking] pass, we only need to bound the
  registers written by an instruction.  Therefore, this function
  returns these registers, ignoring registers used only as
  arguments. *)

Definition regs_of_instr (i: instruction) : list mreg :=
  match i with
  | Lgetstack sl ofs ty r => r :: nil
  | Lsetstack r sl ofs ty => r :: nil
  | Lop op args res => res :: nil
  | Lload chunk addr args dst => dst :: nil
  | Lstore chunk addr args src => nil
  | Lcall sig ros => nil
  | Ltailcall sig ros => nil
  | Lbuiltin ef args res => res ++ destroyed_by_builtin ef
  | Lannot ef args => nil
  | Llabel lbl => nil
  | Lgoto lbl => nil
  | Lcond cond args lbl => nil
  | Ljumptable arg tbl => nil
  | Lreturn => nil
  end.

Fixpoint slots_of_locs (l: list loc) : list (slot * Z * typ) :=
  match l with
  | nil => nil
  | S sl ofs ty :: l' => (sl, ofs, ty) :: slots_of_locs l'
  | R r :: l' => slots_of_locs l'
  end.

Definition slots_of_instr (i: instruction) : list (slot * Z * typ) :=
  match i with
  | Lgetstack sl ofs ty r => (sl, ofs, ty) :: nil
  | Lsetstack r sl ofs ty => (sl, ofs, ty) :: nil
  | Lannot ef args => slots_of_locs args
  | _ => nil
  end.

Definition max_over_list {A: Type} (valu: A -> Z) (l: list A) : Z :=
  List.fold_left (fun m l => Zmax m (valu l)) l 0.

Definition max_over_instrs (valu: instruction -> Z) : Z :=
  max_over_list valu f.(fn_code).

Definition max_over_regs_of_instr (valu: mreg -> Z) (i: instruction) : Z :=
  max_over_list valu (regs_of_instr i).

Definition max_over_slots_of_instr (valu: slot * Z * typ -> Z) (i: instruction) : Z :=
  max_over_list valu (slots_of_instr i).

Definition max_over_regs_of_funct (valu: mreg -> Z) : Z :=
  max_over_instrs (max_over_regs_of_instr valu).

Definition max_over_slots_of_funct (valu: slot * Z * typ -> Z) : Z :=
  max_over_instrs (max_over_slots_of_instr valu).

Definition int_callee_save (r: mreg) := 1 + index_int_callee_save r.

Definition float_callee_save (r: mreg) := 1 + index_float_callee_save r.

Definition local_slot (s: slot * Z * typ) :=
  match s with (Local, ofs, ty) => ofs + typesize ty | _ => 0 end.

Definition outgoing_slot (s: slot * Z * typ) :=
  match s with (Outgoing, ofs, ty) => ofs + typesize ty | _ => 0 end.

Definition outgoing_space (i: instruction) :=
  match i with Lcall sig _ => size_arguments sig | _ => 0 end.

Lemma max_over_list_pos:
  forall (A: Type) (valu: A -> Z) (l: list A),
  max_over_list valu l >= 0.
Proof.
  intros until valu. unfold max_over_list.
  assert (forall l z, fold_left (fun x y => Zmax x (valu y)) l z >= z).
  induction l; simpl; intros.
  omega. apply Zge_trans with (Zmax z (valu a)). 
  auto. apply Zle_ge. apply Zmax1. auto.
Qed.

Lemma max_over_slots_of_funct_pos:
  forall (valu: slot * Z * typ -> Z), max_over_slots_of_funct valu >= 0.
Proof.
  intros. unfold max_over_slots_of_funct.
  unfold max_over_instrs. apply max_over_list_pos.
Qed.

Lemma max_over_regs_of_funct_pos:
  forall (valu: mreg -> Z), max_over_regs_of_funct valu >= 0.
Proof.
  intros. unfold max_over_regs_of_funct.
  unfold max_over_instrs. apply max_over_list_pos.
Qed.

Program Definition function_bounds :=
  mkbounds
    (max_over_slots_of_funct local_slot)
    (max_over_regs_of_funct int_callee_save)
    (max_over_regs_of_funct float_callee_save)
    (Zmax (max_over_instrs outgoing_space)
          (max_over_slots_of_funct outgoing_slot))
    (Zmax f.(fn_stacksize) 0)
    (max_over_slots_of_funct_pos local_slot)
    (max_over_regs_of_funct_pos int_callee_save)
    (max_over_regs_of_funct_pos float_callee_save)
    _ _.
Next Obligation.
  apply Zle_ge. eapply Zle_trans. 2: apply Zmax2.
  apply Zge_le. apply max_over_slots_of_funct_pos.  
Qed.
Next Obligation.
  apply Zle_ge. apply Zmax2.
Qed.

(** We now show the correctness of the inferred bounds. *)

Lemma max_over_list_bound:
  forall (A: Type) (valu: A -> Z) (l: list A) (x: A),
  In x l -> valu x <= max_over_list valu l.
Proof.
  intros until x. unfold max_over_list.
  assert (forall c z,
            let f := fold_left (fun x y => Zmax x (valu y)) c z in
            z <= f /\ (In x c -> valu x <= f)).
    induction c; simpl; intros.
    split. omega. tauto.
    elim (IHc (Zmax z (valu a))); intros. 
    split. apply Zle_trans with (Zmax z (valu a)). apply Zmax1. auto. 
    intro H1; elim H1; intro. 
    subst a. apply Zle_trans with (Zmax z (valu x)). 
    apply Zmax2. auto. auto.
  intro. elim (H l 0); intros. auto.
Qed.

Lemma max_over_instrs_bound:
  forall (valu: instruction -> Z) i,
  In i f.(fn_code) -> valu i <= max_over_instrs valu.
Proof.
  intros. unfold max_over_instrs. apply max_over_list_bound; auto.
Qed.

Lemma max_over_regs_of_funct_bound:
  forall (valu: mreg -> Z) i r,
  In i f.(fn_code) -> In r (regs_of_instr i) ->
  valu r <= max_over_regs_of_funct valu.
Proof.
  intros. unfold max_over_regs_of_funct. 
  apply Zle_trans with (max_over_regs_of_instr valu i).
  unfold max_over_regs_of_instr. apply max_over_list_bound. auto.
  apply max_over_instrs_bound. auto.
Qed.

Lemma max_over_slots_of_funct_bound:
  forall (valu: slot * Z * typ -> Z) i s,
  In i f.(fn_code) -> In s (slots_of_instr i) ->
  valu s <= max_over_slots_of_funct valu.
Proof.
  intros. unfold max_over_slots_of_funct. 
  apply Zle_trans with (max_over_slots_of_instr valu i).
  unfold max_over_slots_of_instr. apply max_over_list_bound. auto.
  apply max_over_instrs_bound. auto.
Qed.

Lemma int_callee_save_bound:
  forall i r,
  In i f.(fn_code) -> In r (regs_of_instr i) ->
  index_int_callee_save r < bound_int_callee_save function_bounds.
Proof.
  intros. apply Zlt_le_trans with (int_callee_save r).
  unfold int_callee_save. omega.
  unfold function_bounds, bound_int_callee_save. 
  eapply max_over_regs_of_funct_bound; eauto.
Qed.

Lemma float_callee_save_bound:
  forall i r,
  In i f.(fn_code) -> In r (regs_of_instr i) ->
  index_float_callee_save r < bound_float_callee_save function_bounds.
Proof.
  intros. apply Zlt_le_trans with (float_callee_save r).
  unfold float_callee_save. omega.
  unfold function_bounds, bound_float_callee_save. 
  eapply max_over_regs_of_funct_bound; eauto.
Qed.

Lemma local_slot_bound:
  forall i ofs ty,
  In i f.(fn_code) -> In (Local, ofs, ty) (slots_of_instr i) ->
  ofs + typesize ty <= bound_local function_bounds.
Proof.
  intros.
  unfold function_bounds, bound_local.
  change (ofs + typesize ty) with (local_slot (Local, ofs, ty)).
  eapply max_over_slots_of_funct_bound; eauto.
Qed.

Lemma outgoing_slot_bound:
  forall i ofs ty,
  In i f.(fn_code) -> In (Outgoing, ofs, ty) (slots_of_instr i) ->
  ofs + typesize ty <= bound_outgoing function_bounds.
Proof.
  intros. change (ofs + typesize ty) with (outgoing_slot (Outgoing, ofs, ty)).
  unfold function_bounds, bound_outgoing.
  apply Zmax_bound_r. eapply max_over_slots_of_funct_bound; eauto.
Qed.

Lemma size_arguments_bound:
  forall sig ros,
  In (Lcall sig ros) f.(fn_code) ->
  size_arguments sig <= bound_outgoing function_bounds.
Proof.
  intros. change (size_arguments sig) with (outgoing_space (Lcall sig ros)).
  unfold function_bounds, bound_outgoing.
  apply Zmax_bound_l. apply max_over_instrs_bound; auto.
Qed.

(** Consequently, all machine registers or stack slots mentioned by one
  of the instructions of function [f] are within bounds. *)

Lemma mreg_is_within_bounds:
  forall i, In i f.(fn_code) ->
  forall r, In r (regs_of_instr i) ->
  mreg_within_bounds function_bounds r.
Proof.
  intros. unfold mreg_within_bounds. split.
  eapply int_callee_save_bound; eauto.
  eapply float_callee_save_bound; eauto.
Qed.

Lemma slot_is_within_bounds:
  forall i, In i f.(fn_code) -> 
  forall sl ty ofs, In (sl, ofs, ty) (slots_of_instr i) ->
  slot_within_bounds function_bounds sl ofs ty.
Proof.
  intros. unfold slot_within_bounds. 
  destruct sl.
  eapply local_slot_bound; eauto.
  auto.
  eapply outgoing_slot_bound; eauto.
Qed.

Lemma slots_of_locs_charact:
  forall sl ofs ty l, In (sl, ofs, ty) (slots_of_locs l) <-> In (S sl ofs ty) l.
Proof.
  induction l; simpl; intros. 
  tauto.
  destruct a; simpl; intuition congruence.
Qed.

(** It follows that every instruction in the function is within bounds, 
    in the sense of the [instr_within_bounds] predicate. *)

Lemma instr_is_within_bounds:
  forall i,
  In i f.(fn_code) ->
  instr_within_bounds function_bounds i.
Proof.
  intros; 
  destruct i;
  generalize (mreg_is_within_bounds _ H); generalize (slot_is_within_bounds _ H); 
  simpl; intros; auto.
(* call *)
  eapply size_arguments_bound; eauto.
(* builtin *)
  apply H1. apply in_or_app; auto. 
(* annot *)
  apply H0. rewrite slots_of_locs_charact; auto. 
Qed.

Lemma function_is_within_bounds:
  function_within_bounds f function_bounds.
Proof.
  intros; red; intros. apply instr_is_within_bounds; auto.
Qed.

End BOUNDS.

