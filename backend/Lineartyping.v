(** Typing rules and computation of stack bounds for Linear. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import RTL.
Require Import Locations.
Require Import Linear.
Require Import Conventions.

(** * Resource bounds for a function *)

(** The [bounds] record capture how many local and outgoing stack slots
  and callee-save registers are used by a function. *)

Record bounds : Set := mkbounds {
  bound_int_local: Z;
  bound_float_local: Z;
  bound_int_callee_save: Z;
  bound_float_callee_save: Z;
  bound_outgoing: Z
}.

(** The resource bounds for a function are computed by a linear scan
  of its instructions. *)

Section BOUNDS.

Variable f: function.

Definition regs_of_instr (i: instruction) : list mreg :=
  match i with
  | Lgetstack s r => r :: nil
  | Lsetstack r s => r :: nil
  | Lop op args res => res :: args
  | Lload chunk addr args dst => dst :: args
  | Lstore chunk addr args src => src :: args
  | Lcall sig (inl fn) => fn :: nil
  | Lcall sig (inr _) => nil
  | Lalloc => nil
  | Llabel lbl => nil
  | Lgoto lbl => nil
  | Lcond cond args lbl => args
  | Lreturn => nil
  end.

Definition slots_of_instr (i: instruction) : list slot :=
  match i with
  | Lgetstack s r => s :: nil
  | Lsetstack r s => s :: nil
  | _ => nil
  end.

Definition max_over_list (A: Set) (valu: A -> Z) (l: list A) : Z :=
  List.fold_left (fun m l => Zmax m (valu l)) l 0.

Definition max_over_instrs (valu: instruction -> Z) : Z :=
  max_over_list instruction valu f.(fn_code).

Definition max_over_regs_of_instr (valu: mreg -> Z) (i: instruction) : Z :=
  max_over_list mreg valu (regs_of_instr i).

Definition max_over_slots_of_instr (valu: slot -> Z) (i: instruction) : Z :=
  max_over_list slot valu (slots_of_instr i).

Definition max_over_regs_of_funct (valu: mreg -> Z) : Z :=
  max_over_instrs (max_over_regs_of_instr valu).

Definition max_over_slots_of_funct (valu: slot -> Z) : Z :=
  max_over_instrs (max_over_slots_of_instr valu).

Definition int_callee_save (r: mreg) := 1 + index_int_callee_save r.

Definition float_callee_save (r: mreg) := 1 + index_float_callee_save r.

Definition int_local (s: slot) :=
  match s with Local ofs Tint => 1 + ofs | _ => 0 end.

Definition float_local (s: slot) :=
  match s with Local ofs Tfloat => 1 + ofs | _ => 0 end.

Definition outgoing_slot (s: slot) :=
  match s with Outgoing ofs ty => ofs + typesize ty | _ => 0 end.

Definition outgoing_space (i: instruction) :=
  match i with Lcall sig _ => size_arguments sig | _ => 0 end.

Definition function_bounds :=
  mkbounds
    (max_over_slots_of_funct int_local)
    (max_over_slots_of_funct float_local)
    (max_over_regs_of_funct int_callee_save)
    (max_over_regs_of_funct float_callee_save)
    (Zmax 6
          (Zmax (max_over_instrs outgoing_space)
                (max_over_slots_of_funct outgoing_slot))).

(** We show that bounds computed by [function_bounds] are all positive
  or null, and moreiver [bound_outgoing] is greater or equal to 6.
  These properties are used later to reason about the layout of
  the activation record. *)

Lemma max_over_list_pos:
  forall (A: Set) (valu: A -> Z) (l: list A),
  max_over_list A valu l >= 0.
Proof.
  intros until valu. unfold max_over_list.
  assert (forall l z, fold_left (fun x y => Zmax x (valu y)) l z >= z).
  induction l; simpl; intros.
  omega. apply Zge_trans with (Zmax z (valu a)). 
  auto. apply Zle_ge. apply Zmax1. auto.
Qed.

Lemma max_over_slots_of_funct_pos:
  forall (valu: slot -> Z), max_over_slots_of_funct valu >= 0.
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

Lemma bound_int_local_pos:
  bound_int_local function_bounds >= 0.
Proof.
  simpl. apply max_over_slots_of_funct_pos.
Qed.

Lemma bound_float_local_pos:
  bound_float_local function_bounds >= 0.
Proof.
  simpl. apply max_over_slots_of_funct_pos.
Qed.

Lemma bound_int_callee_save_pos:
  bound_int_callee_save function_bounds >= 0.
Proof.
  simpl. apply max_over_regs_of_funct_pos.
Qed.

Lemma bound_float_callee_save_pos:
  bound_float_callee_save function_bounds >= 0.
Proof.
  simpl. apply max_over_regs_of_funct_pos.
Qed.

Lemma bound_outgoing_pos:
  bound_outgoing function_bounds >= 6.
Proof.
  simpl. apply Zle_ge. apply Zmax_bound_l. omega.
Qed.

End BOUNDS.

(** * Typing rules for Linear *)

(** The typing rules for Linear are similar to those for LTL: we check
  that instructions receive the right number of arguments,
  and that the types of the argument and result registers agree
  with what the instruction expects.  Moreover, we state that references
  to callee-save registers and to stack slots are within the bounds
  computed by [function_bounds].  This is true by construction of
  [function_bounds], and is proved in [Linearizetyping], but it
  is convenient to integrate this property within the typing judgement.
*)

Section WT_INSTR.

Variable funct: function.
Let b := function_bounds funct.

Definition mreg_bounded (r: mreg) :=
  match mreg_type r with
  | Tint => index_int_callee_save r < bound_int_callee_save b
  | Tfloat => index_float_callee_save r < bound_float_callee_save b
  end.

Definition slot_bounded (s: slot) :=
  match s with
  | Local ofs Tint => 0 <= ofs < bound_int_local b
  | Local ofs Tfloat => 0 <= ofs < bound_float_local b
  | Outgoing ofs ty => 6 <= ofs /\ ofs + typesize ty <= bound_outgoing b
  | Incoming ofs ty => 6 <= ofs /\ ofs + typesize ty <= size_arguments funct.(fn_sig)
  end.

Inductive wt_instr : instruction -> Prop :=
  | wt_Lgetstack:
      forall s r,
      slot_type s = mreg_type r ->
      slot_bounded s -> mreg_bounded r ->
      wt_instr (Lgetstack s r)
  | wt_Lsetstack:
      forall s r,
      match s with Incoming _ _ => False | _ => True end ->
      slot_type s = mreg_type r ->
      slot_bounded s ->
      wt_instr (Lsetstack r s)
  | wt_Lopmove:
      forall r1 r,
      mreg_type r1 = mreg_type r ->
      mreg_bounded r ->
      wt_instr (Lop Omove (r1 :: nil) r)
  | wt_Lopundef:
      forall r,
      mreg_bounded r ->
      wt_instr (Lop Oundef nil r)
  | wt_Lop:
      forall op args res,
      op <> Omove -> op <> Oundef ->
      (List.map mreg_type args, mreg_type res) = type_of_operation op ->
      mreg_bounded res ->
      wt_instr (Lop op args res)
  | wt_Lload:
      forall chunk addr args dst,
      List.map mreg_type args = type_of_addressing addr ->
      mreg_type dst = type_of_chunk chunk ->
      mreg_bounded dst ->
      wt_instr (Lload chunk addr args dst)
  | wt_Lstore:
      forall chunk addr args src,
      List.map mreg_type args = type_of_addressing addr ->
      mreg_type src = type_of_chunk chunk ->
      wt_instr (Lstore chunk addr args src)
  | wt_Lcall:
      forall sig ros,
      size_arguments sig <= bound_outgoing b ->
      match ros with inl r => mreg_type r = Tint | _ => True end ->
      wt_instr (Lcall sig ros)
  | wt_Lalloc:
      wt_instr Lalloc
  | wt_Llabel:
      forall lbl,
      wt_instr (Llabel lbl)
  | wt_Lgoto:
      forall lbl,
      wt_instr (Lgoto lbl)
  | wt_Lcond:
      forall cond args lbl,
      List.map mreg_type args = type_of_condition cond ->
      wt_instr (Lcond cond args lbl)
  | wt_Lreturn: 
      wt_instr (Lreturn).

End WT_INSTR.

Definition wt_function (f: function) : Prop :=
  forall instr, In instr f.(fn_code) -> wt_instr f instr.

Inductive wt_fundef: fundef -> Prop :=
  | wt_fundef_external: forall ef,
      Conventions.sig_external_ok ef.(ef_sig) ->
      wt_fundef (External ef)
  | wt_function_internal: forall f,
      wt_function f ->
      wt_fundef (Internal f).

Definition wt_program (p: program) : Prop :=
  forall i f, In (i, f) (prog_funct p) -> wt_fundef f.

