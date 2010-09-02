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

(** Correctness proof for the translation from Linear to Mach. *)

(** This file proves semantic preservation for the [Stacking] pass.
  For the target language Mach, we use the abstract semantics
  given in file [Machabstr], where a part of the activation record
  is not resident in memory.  Combined with the semantic equivalence
  result between the two Mach semantics (see file [Machabstr2concr]),
  the proof in this file also shows semantic preservation with
  respect to the concrete Mach semantics. *)

Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Op.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require LTL.
Require Import Linear.
Require Import Lineartyping.
Require Import Mach.
Require Import Machabstr.
Require Import Bounds.
Require Import Conventions.
Require Import Stacklayout.
Require Import Stacking.

(** * Properties of frames and frame accesses *)

(** ``Good variable'' properties for frame accesses. *)

Lemma typesize_typesize:
  forall ty, AST.typesize ty = 4 * Locations.typesize ty.
Proof.
  destruct ty; auto.
Qed.

Section PRESERVATION.

Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: transf_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.


Section FRAME_PROPERTIES.

Variable stack: list Machabstr.stackframe.
Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable tf: Mach.function.
Hypothesis TRANSF_F: transf_function f = OK tf.

Lemma unfold_transf_function:
  tf = Mach.mkfunction
         f.(Linear.fn_sig)
         (transl_body f fe)
         f.(Linear.fn_stacksize)
         fe.(fe_size)
         (Int.repr fe.(fe_ofs_link))
         (Int.repr fe.(fe_ofs_retaddr)).
Proof.
  generalize TRANSF_F. unfold transf_function.
  case (zlt (Linear.fn_stacksize f) 0). intros; discriminate.
  case (zlt (- Int.min_signed) (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe. unfold b. congruence.
Qed.

Lemma size_no_overflow: fe.(fe_size) <= -Int.min_signed.
Proof.
  generalize TRANSF_F. unfold transf_function.
  case (zlt (Linear.fn_stacksize f) 0). intros; discriminate.
  case (zlt (- Int.min_signed) (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe, b. omega.
Qed.

(** A frame index is valid if it lies within the resource bounds
  of the current function. *)

Definition index_valid (idx: frame_index) :=
  match idx with
  | FI_link => True
  | FI_retaddr => True
  | FI_local x Tint => 0 <= x < b.(bound_int_local)
  | FI_local x Tfloat => 0 <= x < b.(bound_float_local)
  | FI_arg x ty => 0 <= x /\ x + typesize ty <= b.(bound_outgoing)
  | FI_saved_int x => 0 <= x < b.(bound_int_callee_save)
  | FI_saved_float x => 0 <= x < b.(bound_float_callee_save)
  end.

Definition type_of_index (idx: frame_index) :=
  match idx with
  | FI_link => Tint
  | FI_retaddr => Tint
  | FI_local x ty => ty
  | FI_arg x ty => ty
  | FI_saved_int x => Tint
  | FI_saved_float x => Tfloat
  end.

(** Non-overlap between the memory areas corresponding to two
  frame indices. *)

Definition index_diff (idx1 idx2: frame_index) : Prop :=
  match idx1, idx2 with
  | FI_link, FI_link => False
  | FI_retaddr, FI_retaddr => False
  | FI_local x1 ty1, FI_local x2 ty2 =>
      x1 <> x2 \/ ty1 <> ty2
  | FI_arg x1 ty1, FI_arg x2 ty2 =>
      x1 + typesize ty1 <= x2 \/ x2 + typesize ty2 <= x1
  | FI_saved_int x1, FI_saved_int x2 => x1 <> x2
  | FI_saved_float x1, FI_saved_float x2 => x1 <> x2
  | _, _ => True
  end.

Ltac AddPosProps :=
  generalize (bound_int_local_pos b); intro;
  generalize (bound_float_local_pos b); intro;
  generalize (bound_int_callee_save_pos b); intro;
  generalize (bound_float_callee_save_pos b); intro;
  generalize (bound_outgoing_pos b); intro;
  generalize (align_float_part b); intro.

Lemma size_pos: fe.(fe_size) >= 0.
Proof.
  AddPosProps.
  unfold fe, make_env, fe_size. omega.
Qed.

Opaque function_bounds.

Lemma offset_of_index_disj:
  forall idx1 idx2,
  index_valid idx1 -> index_valid idx2 ->
  index_diff idx1 idx2 ->
  offset_of_index fe idx1 + 4 * typesize (type_of_index idx1) <= offset_of_index fe idx2 \/
  offset_of_index fe idx2 + 4 * typesize (type_of_index idx2) <= offset_of_index fe idx1.
Proof.
  AddPosProps.
  intros.
  destruct idx1; destruct idx2;
  try (destruct t); try (destruct t0);
  unfold offset_of_index, fe, make_env,
    fe_size, fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save,
    fe_ofs_link, fe_ofs_retaddr, fe_ofs_arg,
    type_of_index, typesize;
  simpl in H5; simpl in H6; simpl in H7;
  try omega.
  assert (z <> z0). intuition auto. omega.
  assert (z <> z0). intuition auto. omega.
Qed.

Remark aligned_4_4x: forall x, (4 | 4 * x).
Proof. intro. exists x; ring. Qed.

Remark aligned_4_8x: forall x, (4 | 8 * x).
Proof. intro. exists (x * 2); ring. Qed.

Remark aligned_4_align8: forall x, (4 | align x 8).
Proof. 
  intro. apply Zdivides_trans with 8. exists 2; auto. apply align_divides. omega.
Qed.

Hint Resolve Zdivide_0 Zdivide_refl Zdivide_plus_r
             aligned_4_4x aligned_4_8x aligned_4_align8: align_4.

Hint Extern 4 (?X | ?Y) => (exists (Y/X); reflexivity) : align_4.

Lemma offset_of_index_aligned:
  forall idx, (4 | offset_of_index fe idx).
Proof.
  intros.
  destruct idx;
  unfold offset_of_index, fe, make_env,
    fe_size, fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save,
    fe_ofs_link, fe_ofs_retaddr, fe_ofs_arg;
  auto with align_4.
  destruct t; auto with align_4.
Qed.

Lemma frame_size_aligned:
  (4 | fe_size fe).
Proof.
  unfold offset_of_index, fe, make_env,
    fe_size, fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save,
    fe_ofs_link, fe_ofs_retaddr, fe_ofs_arg;
  auto with align_4.
Qed.

(** The following lemmas give sufficient conditions for indices
  of various kinds to be valid. *)

Lemma index_local_valid:
  forall ofs ty,
  slot_within_bounds f b (Local ofs ty) ->
  index_valid (FI_local ofs ty).
Proof.
  unfold slot_within_bounds, index_valid. auto.
Qed.

Lemma index_arg_valid:
  forall ofs ty,
  slot_within_bounds f b (Outgoing ofs ty) ->
  index_valid (FI_arg ofs ty).
Proof.
  unfold slot_within_bounds, index_valid. auto.
Qed.

Lemma index_saved_int_valid:
  forall r,
  In r int_callee_save_regs ->
  index_int_callee_save r < b.(bound_int_callee_save) ->
  index_valid (FI_saved_int (index_int_callee_save r)).
Proof.
  intros. red. split. 
  apply Zge_le. apply index_int_callee_save_pos; auto. 
  auto.
Qed.

Lemma index_saved_float_valid:
  forall r,
  In r float_callee_save_regs ->
  index_float_callee_save r < b.(bound_float_callee_save) ->
  index_valid (FI_saved_float (index_float_callee_save r)).
Proof.
  intros. red. split. 
  apply Zge_le. apply index_float_callee_save_pos; auto. 
  auto.
Qed.

Hint Resolve index_local_valid index_arg_valid
             index_saved_int_valid index_saved_float_valid: stacking.

(** The offset of a valid index lies within the bounds of the frame. *)

Lemma offset_of_index_valid:
  forall idx,
  index_valid idx ->
  0 <= offset_of_index fe idx /\
  offset_of_index fe idx + 4 * typesize (type_of_index idx) <= fe.(fe_size).
Proof.
  AddPosProps.
  intros.
  destruct idx; try destruct t;
  unfold offset_of_index, fe, make_env,
    fe_size, fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save,
    fe_ofs_link, fe_ofs_retaddr, fe_ofs_arg,
    type_of_index, typesize;
  unfold index_valid in H5; simpl typesize in H5;
  omega.
Qed. 

(** Offsets for valid index are representable as signed machine integers
  without loss of precision. *)

Lemma offset_of_index_no_overflow:
  forall idx,
  index_valid idx ->
  Int.signed (Int.repr (offset_of_index fe idx)) = offset_of_index fe idx.
Proof.
  intros.
  generalize (offset_of_index_valid idx H). intros [A B].
  apply Int.signed_repr.
  split. apply Zle_trans with 0; auto. compute; intro; discriminate.
  assert (offset_of_index fe idx < fe_size fe).
    generalize (typesize_pos (type_of_index idx)); intro. omega.
  apply Zlt_succ_le. 
  change (Zsucc Int.max_signed) with (- Int.min_signed).
  generalize size_no_overflow. omega. 
Qed.

(** Characterization of the [get_slot] and [set_slot]
  operations in terms of the following [index_val] and [set_index_val]
  frame access functions. *)

Definition index_val (idx: frame_index) (fr: frame) :=
  fr (type_of_index idx) (offset_of_index fe idx - tf.(fn_framesize)).

Definition set_index_val (idx: frame_index) (v: val) (fr: frame) :=
  update (type_of_index idx) (offset_of_index fe idx - tf.(fn_framesize)) v fr.

Lemma slot_valid_index:
  forall idx,
  index_valid idx -> idx <> FI_link -> idx <> FI_retaddr ->
  slot_valid tf (type_of_index idx) (offset_of_index fe idx).
Proof.
  intros.
  destruct (offset_of_index_valid idx H) as [A B].
  rewrite <- typesize_typesize in B.
  rewrite unfold_transf_function; constructor.
  auto. unfold fn_framesize. auto.
  unfold fn_link_ofs. change (fe_ofs_link fe) with (offset_of_index fe FI_link).
  rewrite offset_of_index_no_overflow.
  exploit (offset_of_index_disj idx FI_link).
    auto. exact I. red. destruct idx; auto || congruence.
  intro. rewrite typesize_typesize. assumption.
  exact I.
  unfold fn_retaddr_ofs. change (fe_ofs_retaddr fe) with (offset_of_index fe FI_retaddr).
  rewrite offset_of_index_no_overflow.
  exploit (offset_of_index_disj idx FI_retaddr).
    auto. exact I. red. destruct idx; auto || congruence.
  intro. rewrite typesize_typesize. assumption.
  exact I.
  apply offset_of_index_aligned.
Qed.

Lemma get_slot_index:
  forall fr idx ty v,
  index_valid idx -> idx <> FI_link -> idx <> FI_retaddr ->
  ty = type_of_index idx ->
  v = index_val idx fr ->
  get_slot tf fr ty (Int.signed (Int.repr (offset_of_index fe idx))) v.
Proof.
  intros. subst v; subst ty. rewrite offset_of_index_no_overflow; auto.
  unfold index_val. apply get_slot_intro; auto.
  apply slot_valid_index; auto.
Qed.

Lemma set_slot_index:
  forall fr idx v,
  index_valid idx -> idx <> FI_link -> idx <> FI_retaddr ->
  set_slot tf fr (type_of_index idx) (Int.signed (Int.repr (offset_of_index fe idx)))
                 v (set_index_val idx v fr).
Proof.
  intros.  rewrite offset_of_index_no_overflow; auto.
  apply set_slot_intro. 
  apply slot_valid_index; auto.
  unfold set_index_val. auto.
Qed.

(** ``Good variable'' properties for [index_val] and [set_index_val]. *)

Lemma get_set_index_val_same:
  forall fr idx v,
  index_val idx (set_index_val idx v fr) = v.
Proof.
  intros. unfold index_val, set_index_val. apply update_same. 
Qed.

Lemma get_set_index_val_other:
  forall fr idx idx' v,
  index_valid idx -> index_valid idx' -> index_diff idx idx' ->
  index_val idx' (set_index_val idx v fr) = index_val idx' fr.
Proof.
  intros. unfold index_val, set_index_val. apply update_other.
  repeat rewrite typesize_typesize. 
  exploit (offset_of_index_disj idx idx'); auto. omega.
Qed.

Lemma get_set_index_val_overlap:
  forall ofs1 ty1 ofs2 ty2 v fr,
  S (Outgoing ofs1 ty1) <> S (Outgoing ofs2 ty2) ->
  Loc.overlap (S (Outgoing ofs1 ty1)) (S (Outgoing ofs2 ty2)) = true ->
  index_val (FI_arg ofs2 ty2) (set_index_val (FI_arg ofs1 ty1) v fr) = Vundef.
Proof.
  intros. unfold index_val, set_index_val, offset_of_index, type_of_index.
  assert (~(ofs1 + typesize ty1 <= ofs2 \/ ofs2 + typesize ty2 <= ofs1)).
  destruct (orb_prop _ _ H0). apply Loc.overlap_aux_true_1. auto. 
  apply Loc.overlap_aux_true_2. auto.
  unfold update. 
  destruct (zeq (fe_ofs_arg + 4 * ofs1 - fn_framesize tf)
                (fe_ofs_arg + 4 * ofs2 - fn_framesize tf)).
  destruct (typ_eq ty1 ty2). 
  elim H. decEq. decEq. omega. auto.
  auto.
  repeat rewrite typesize_typesize.
  rewrite zle_false. apply zle_false. omega. omega.
Qed.

(** Accessing stack-based arguments in the caller's frame. *)

Definition get_parent_slot (cs: list stackframe) (ofs: Z) (ty: typ) (v: val) : Prop :=
  get_slot (parent_function cs) (parent_frame cs)
           ty (Int.signed (Int.repr (fe_ofs_arg + 4 * ofs))) v.

(** * Agreement between location sets and Mach environments *)

(** The following [agree] predicate expresses semantic agreement between:
- on the Linear side, the current location set [ls] and the location
  set of the caller [ls0];
- on the Mach side, a register set [rs], a frame [fr] and a call stack [cs].
*)

Record agree (ls ls0: locset) (rs: regset) (fr: frame) (cs: list stackframe): Prop :=
  mk_agree {
    (** Machine registers have the same values on the Linear and Mach sides. *)
    agree_reg:
      forall r, ls (R r) = rs r;

    (** Machine registers outside the bounds of the current function
        have the same values they had at function entry.  In other terms,
        these registers are never assigned. *)
    agree_unused_reg:
      forall r, ~(mreg_within_bounds b r) -> rs r = ls0 (R r);

    (** Local and outgoing stack slots (on the Linear side) have
        the same values as the one loaded from the current Mach frame 
        at the corresponding offsets. *)
    agree_locals:
      forall ofs ty, 
      slot_within_bounds f b (Local ofs ty) ->
      ls (S (Local ofs ty)) = index_val (FI_local ofs ty) fr;
    agree_outgoing:
      forall ofs ty, 
      slot_within_bounds f b (Outgoing ofs ty) ->
      ls (S (Outgoing ofs ty)) = index_val (FI_arg ofs ty) fr;

    (** Incoming stack slots (on the Linear side) have
        the same values as the one loaded from the parent Mach frame 
        at the corresponding offsets. *)
    agree_incoming:
      forall ofs ty,
      In (S (Incoming ofs ty)) (loc_parameters f.(Linear.fn_sig)) ->
      get_parent_slot cs ofs ty (ls (S (Incoming ofs ty)));

    (** The areas of the frame reserved for saving used callee-save
        registers always contain the values that those registers had
        on function entry. *)
    agree_saved_int:
      forall r,
      In r int_callee_save_regs ->
      index_int_callee_save r < b.(bound_int_callee_save) ->
      index_val (FI_saved_int (index_int_callee_save r)) fr = ls0 (R r);
    agree_saved_float:
      forall r,
      In r float_callee_save_regs ->
      index_float_callee_save r < b.(bound_float_callee_save) ->
      index_val (FI_saved_float (index_float_callee_save r)) fr = ls0 (R r)
  }.

Hint Resolve agree_reg agree_unused_reg 
             agree_locals agree_outgoing agree_incoming
             agree_saved_int agree_saved_float: stacking.

(** Values of registers and register lists. *)

Lemma agree_eval_reg:
  forall ls ls0 rs fr cs r,
  agree ls ls0 rs fr cs -> rs r = ls (R r).
Proof.
  intros. symmetry. eauto with stacking.
Qed.

Lemma agree_eval_regs:
  forall ls ls0 rs fr cs rl,
  agree ls ls0 rs cs fr -> rs##rl = reglist ls rl.
Proof.
  induction rl; simpl; intros.
  auto. f_equal. eapply agree_eval_reg; eauto. auto.
Qed.

Hint Resolve agree_eval_reg agree_eval_regs: stacking.

(** Preservation of agreement under various assignments:
  of machine registers, of local slots, of outgoing slots. *)

Lemma agree_set_reg:
  forall ls ls0 rs fr cs r v,
  agree ls ls0 rs fr cs ->
  mreg_within_bounds b r ->
  agree (Locmap.set (R r) v ls) ls0 (Regmap.set r v rs) fr cs.
Proof.
  intros. constructor; eauto with stacking.
  intros. case (mreg_eq r r0); intro.
  subst r0. rewrite Locmap.gss; rewrite Regmap.gss; auto.
  rewrite Locmap.gso. rewrite Regmap.gso. eauto with stacking.
  auto. red. auto.
  intros. rewrite Regmap.gso. eauto with stacking. 
  red; intro; subst r0. contradiction.
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
Qed.

Lemma agree_set_local:
  forall ls ls0 rs fr cs v ofs ty,
  agree ls ls0 rs fr cs ->
  slot_within_bounds f b (Local ofs ty) ->
  exists fr',
    set_slot tf fr ty (Int.signed (Int.repr (offset_of_index fe (FI_local ofs ty)))) v fr' /\
    agree (Locmap.set (S (Local ofs ty)) v ls) ls0 rs fr' cs.
Proof.
  intros.
  exists (set_index_val (FI_local ofs ty) v fr); split.
  set (idx := FI_local ofs ty). 
  change ty with (type_of_index idx).
  apply set_slot_index; unfold idx. auto with stacking. congruence. congruence.
  constructor; eauto with stacking.
  (* agree_reg *)
  intros. rewrite Locmap.gso. eauto with stacking. red; auto.
  (* agree_local *)
  intros. case (slot_eq (Local ofs ty) (Local ofs0 ty0)); intro.
  rewrite <- e. rewrite Locmap.gss. 
  replace (FI_local ofs0 ty0) with (FI_local ofs ty).
  symmetry. apply get_set_index_val_same. congruence.
  assert (ofs <> ofs0 \/ ty <> ty0).
    case (zeq ofs ofs0); intro. compare ty ty0; intro.
    congruence. tauto.  tauto. 
  rewrite Locmap.gso. rewrite get_set_index_val_other; eauto with stacking.
  red. auto.
  (* agree_outgoing *)
  intros. rewrite Locmap.gso. rewrite get_set_index_val_other; eauto with stacking.
  red; auto. red; auto.
  (* agree_incoming *)
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
  (* agree_saved_int *)
  intros. rewrite get_set_index_val_other; eauto with stacking.
  red; auto.
  (* agree_saved_float *)
  intros. rewrite get_set_index_val_other; eauto with stacking.
  red; auto.
Qed.

Lemma agree_set_outgoing:
  forall ls ls0 rs fr cs v ofs ty,
  agree ls ls0 rs fr cs ->
  slot_within_bounds f b (Outgoing ofs ty) ->
  exists fr',
    set_slot tf fr ty (Int.signed (Int.repr (offset_of_index fe (FI_arg ofs ty)))) v fr' /\
    agree (Locmap.set (S (Outgoing ofs ty)) v ls) ls0 rs fr' cs.
Proof.
  intros.
  exists (set_index_val (FI_arg ofs ty) v fr); split.
  set (idx := FI_arg ofs ty). 
  change ty with (type_of_index idx).
  apply set_slot_index; unfold idx. auto with stacking. congruence. congruence.
  constructor; eauto with stacking.
  (* agree_reg *)
  intros. rewrite Locmap.gso. eauto with stacking. red; auto.
  (* agree_local *)
  intros. rewrite Locmap.gso. rewrite get_set_index_val_other; eauto with stacking.
  red; auto. red; auto.
  (* agree_outgoing *)
  intros. unfold Locmap.set. 
  case (Loc.eq (S (Outgoing ofs ty)) (S (Outgoing ofs0 ty0))); intro.
  (* same location *)
  replace ofs0 with ofs by congruence. replace ty0 with ty by congruence.
  symmetry. apply get_set_index_val_same.
  (* overlapping locations *)
  caseEq (Loc.overlap (S (Outgoing ofs ty)) (S (Outgoing ofs0 ty0))); intros.
  symmetry. apply get_set_index_val_overlap; auto.
  (* disjoint locations *)
  rewrite get_set_index_val_other; eauto with stacking.
  red. eapply Loc.overlap_aux_false_1; eauto.
  (* agree_incoming *)
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
  (* saved ints *)
  intros. rewrite get_set_index_val_other; eauto with stacking. red; auto.
  (* saved floats *)
  intros. rewrite get_set_index_val_other; eauto with stacking. red; auto.
Qed.

Lemma agree_undef_regs:
  forall rl ls ls0 rs fr cs,
  agree ls ls0 rs fr cs ->
  (forall r, In r rl -> In (R r) temporaries) ->
  agree (Locmap.undef (List.map R rl) ls) ls0 (undef_regs rl rs) fr cs.
Proof.
  induction rl; intros; simpl.
  auto.
  eapply IHrl; eauto. 
  apply agree_set_reg; auto with coqlib.
  assert (In (R a) temporaries) by auto with coqlib.
  red. destruct (mreg_type a).
  destruct (zlt (index_int_callee_save a) 0). 
  generalize (bound_int_callee_save_pos b). omega. 
  elim (int_callee_save_not_destroyed a). auto. apply index_int_callee_save_pos2; auto.
  destruct (zlt (index_float_callee_save a) 0). 
  generalize (bound_float_callee_save_pos b). omega. 
  elim (float_callee_save_not_destroyed a). auto. apply index_float_callee_save_pos2; auto.
  intros. apply H0. auto with coqlib.
Qed.

Lemma agree_undef_temps:
  forall ls ls0 rs fr cs,
  agree ls ls0 rs fr cs ->
  agree (LTL.undef_temps ls) ls0 (Mach.undef_temps rs) fr cs.
Proof.
  intros. unfold undef_temps, LTL.undef_temps. 
  change temporaries with (List.map R (int_temporaries ++ float_temporaries)).
  apply agree_undef_regs; auto.
  intros. 
  change temporaries with (List.map R (int_temporaries ++ float_temporaries)).
  apply List.in_map. auto. 
Qed.

Lemma agree_undef_op:
  forall op env ls ls0 rs fr cs,
  agree ls ls0 rs fr cs ->
  agree (Linear.undef_op op ls) ls0 (Mach.undef_op (transl_op env op) rs) fr cs.
Proof.
  intros. exploit agree_undef_temps; eauto. intro. 
  destruct op; simpl; auto.
Qed.

Lemma agree_undef_getparam:
  forall ls ls0 rs fr cs,
  agree ls ls0 rs fr cs ->
  agree (Locmap.set (R IT1) Vundef ls) ls0 (rs#IT1 <- Vundef) fr cs.
Proof.
  intros. exploit (agree_undef_regs (IT1 :: nil)); eauto.
  simpl; intros. intuition congruence. 
Qed.

Lemma agree_return_regs:
  forall ls ls0 rs fr cs rs',
  agree ls ls0 rs fr cs ->
  (forall r,
    ~In r int_callee_save_regs -> ~In r float_callee_save_regs ->
    rs' r = rs r) ->
  (forall r,
    In r int_callee_save_regs \/ In r float_callee_save_regs ->
    rs' r = ls0 (R r)) ->
  (forall r, return_regs ls0 ls (R r) = rs' r).
Proof.
  intros; unfold return_regs.
  case (In_dec Loc.eq (R r) temporaries); intro.
  rewrite H0. eapply agree_reg; eauto. 
    apply int_callee_save_not_destroyed; auto.
    apply float_callee_save_not_destroyed; auto.
  case (In_dec Loc.eq (R r) destroyed_at_call); intro.
  rewrite H0. eapply agree_reg; eauto.
    apply int_callee_save_not_destroyed; auto.
    apply float_callee_save_not_destroyed; auto.
  symmetry; apply H1.
  generalize (register_classification r); tauto.
Qed.

(** Agreement over callee-save registers and stack locations *)

Definition agree_callee_save (ls1 ls2: locset) : Prop :=
  forall l,
  match l with
  | R r => In r int_callee_save_regs \/ In r float_callee_save_regs
  | S s => True
  end ->
  ls2 l = ls1 l.

Remark mreg_not_within_bounds:
  forall r,
  ~mreg_within_bounds b r -> In r int_callee_save_regs \/ In r float_callee_save_regs.
Proof.
  intro r; unfold mreg_within_bounds.
  destruct (mreg_type r); intro.
  left. apply index_int_callee_save_pos2. 
  generalize (bound_int_callee_save_pos b). omega.
  right. apply index_float_callee_save_pos2. 
  generalize (bound_float_callee_save_pos b). omega.
Qed.

Lemma agree_callee_save_agree:
  forall ls ls1 ls2 rs fr cs,
  agree ls ls1 rs fr cs ->
  agree_callee_save ls1 ls2 ->
  agree ls ls2 rs fr cs.
Proof.
  intros. inv H. constructor; auto.
  intros. rewrite agree_unused_reg0; auto.
  symmetry. apply H0. apply mreg_not_within_bounds; auto.
  intros. rewrite (H0 (R r)); auto. 
  intros. rewrite (H0 (R r)); auto. 
Qed.

Lemma agree_callee_save_return_regs:
  forall ls1 ls2,
  agree_callee_save (return_regs ls1 ls2) ls1.
Proof.
  intros; red; intros.
  unfold return_regs. destruct l; auto.
  generalize (int_callee_save_not_destroyed m); intro.
  generalize (float_callee_save_not_destroyed m); intro.
  destruct (In_dec Loc.eq (R m) temporaries). tauto.
  destruct (In_dec Loc.eq (R m) destroyed_at_call). tauto.
  auto.
Qed.

Lemma agree_callee_save_set_result:
  forall ls1 ls2 v sg,
  agree_callee_save ls1 ls2 ->
  agree_callee_save (Locmap.set (R (loc_result sg)) v ls1) ls2.
Proof.
  intros; red; intros. rewrite H; auto. 
  symmetry; apply Locmap.gso. destruct l; simpl; auto.
  red; intro. subst m. elim (loc_result_not_callee_save _ H0).
Qed.

(** A variant of [agree] used for return frames. *)

Definition agree_frame (ls ls0: locset) (fr: frame) (cs: list stackframe): Prop :=
  exists rs, agree ls ls0 rs fr cs.

Lemma agree_frame_agree:
  forall ls1 ls2 rs fr cs ls0,
  agree_frame ls1 ls0 fr cs ->
  agree_callee_save ls2 ls1 ->
  (forall r, rs r = ls2 (R r)) ->
  agree ls2 ls0 rs fr cs.
Proof.
  intros. destruct H as [rs' AG]. inv AG.
  constructor; auto.
  intros. rewrite <- agree_unused_reg0; auto.
  rewrite <- agree_reg0. rewrite H1. symmetry; apply H0.
  apply mreg_not_within_bounds; auto.
  intros. rewrite <- H0; auto.
  intros. rewrite <- H0; auto.
  intros. rewrite <- H0; auto.
Qed.

(** * Correctness of saving and restoring of callee-save registers *)

(** The following lemmas show the correctness of the register saving
  code generated by [save_callee_save]: after this code has executed,
  the register save areas of the current frame do contain the
  values of the callee-save registers used by the function. *)

Section SAVE_CALLEE_SAVE.

Variable bound: frame_env -> Z.
Variable number: mreg -> Z.
Variable mkindex: Z -> frame_index.
Variable ty: typ.
Variable sp: val.
Variable csregs: list mreg.

Hypothesis number_inj: 
  forall r1 r2, In r1 csregs -> In r2 csregs -> r1 <> r2 -> number r1 <> number r2.
Hypothesis mkindex_valid:
  forall r, In r csregs -> number r < bound fe -> index_valid (mkindex (number r)).
Hypothesis mkindex_not_link:
  forall z, mkindex z <> FI_link.
Hypothesis mkindex_not_retaddr:
  forall z, mkindex z <> FI_retaddr.
Hypothesis mkindex_typ:
  forall z, type_of_index (mkindex z) = ty.
Hypothesis mkindex_inj:
  forall z1 z2, z1 <> z2 -> mkindex z1 <> mkindex z2.
Hypothesis mkindex_diff:
  forall r idx,
  idx <> mkindex (number r) -> index_diff (mkindex (number r)) idx.

Lemma save_callee_save_regs_correct:
  forall l k rs fr m,
  incl l csregs ->
  list_norepet l ->
  exists fr',
    star step tge 
       (State stack tf sp
         (save_callee_save_regs bound number mkindex ty fe l k) rs fr m)
    E0 (State stack tf sp k rs fr' m)
  /\ (forall r,
       In r l -> number r < bound fe ->
       index_val (mkindex (number r)) fr' = rs r)
  /\ (forall idx,
       index_valid idx ->
       (forall r,
         In r l -> number r < bound fe -> idx <> mkindex (number r)) ->
       index_val idx fr' = index_val idx fr).
Proof.
  induction l; intros; simpl save_callee_save_regs.
  (* base case *)
  exists fr. split. apply star_refl.
  split. intros. elim H1.
  auto.
  (* inductive case *)
  set (k1 := save_callee_save_regs bound number mkindex ty fe l k).
  assert (R1: incl l csregs). eauto with coqlib.
  assert (R2: list_norepet l). inversion H0; auto.
  unfold save_callee_save_reg.
  destruct (zlt (number a) (bound fe)).
  (* a store takes place *)
  set (fr1 := set_index_val (mkindex (number a)) (rs a) fr).
  exploit (IHl k rs fr1 m); auto. 
  fold k1. intros [fr' [A [B C]]].
  exists fr'.
  split. eapply star_left. 
  apply exec_Msetstack. instantiate (1 := fr1). 
  unfold fr1. rewrite <- (mkindex_typ (number a)).
  eapply set_slot_index; eauto with coqlib.
  eexact A.
  traceEq.
  split. intros. simpl in H1. destruct H1. subst r.
    rewrite C. unfold fr1. apply get_set_index_val_same.
    apply mkindex_valid; auto with coqlib.
    intros. apply mkindex_inj. apply number_inj; auto with coqlib.
    inversion H0. congruence.
    apply B; auto.
  intros. rewrite C; auto with coqlib. 
    unfold fr1. apply get_set_index_val_other; auto with coqlib. 
  (* no store takes place *)
  exploit (IHl k rs fr m); auto. intros [fr' [A [B C]]].
  exists fr'.
  split. exact A.
  split. intros. simpl in H1; destruct H1. subst r. omegaContradiction.
    apply B; auto. 
  intros. apply C; auto with coqlib.
Qed.

End SAVE_CALLEE_SAVE. 

Lemma save_callee_save_int_correct:
  forall k sp rs fr m,
  exists fr',
    star step tge 
       (State stack tf sp
         (save_callee_save_int fe k) rs fr m)
    E0 (State stack tf sp k rs fr' m)
  /\ (forall r,
       In r int_callee_save_regs ->
       index_int_callee_save r < bound_int_callee_save b ->
       index_val (FI_saved_int (index_int_callee_save r)) fr' = rs r)
  /\ (forall idx,
       index_valid idx ->
       match idx with FI_saved_int _ => False | _ => True end ->
       index_val idx fr' = index_val idx fr).
Proof.
  intros.
  exploit (save_callee_save_regs_correct fe_num_int_callee_save index_int_callee_save FI_saved_int
                                         Tint sp int_callee_save_regs).
  exact index_int_callee_save_inj.
  intros. red. split; auto. generalize (index_int_callee_save_pos r H). omega.
  intro; congruence.
  intro; congruence.
  auto.
  intros; congruence.
  intros until idx. destruct idx; simpl; auto. congruence.
  apply incl_refl.
  apply int_callee_save_norepet.
  intros [fr' [A [B C]]]. 
  exists fr'; intuition. unfold save_callee_save_int; eauto. 
  apply C. auto. intros; subst idx. auto.
Qed.

Lemma save_callee_save_float_correct:
  forall k sp rs fr m,
  exists fr',
    star step tge 
       (State stack tf sp
         (save_callee_save_float fe k) rs fr m)
    E0 (State stack tf sp k rs fr' m)
  /\ (forall r,
       In r float_callee_save_regs ->
       index_float_callee_save r < bound_float_callee_save b ->
       index_val (FI_saved_float (index_float_callee_save r)) fr' = rs r)
  /\ (forall idx,
       index_valid idx ->
       match idx with FI_saved_float _ => False | _ => True end ->
       index_val idx fr' = index_val idx fr).
Proof.
  intros.
  exploit (save_callee_save_regs_correct fe_num_float_callee_save index_float_callee_save FI_saved_float
                                         Tfloat sp float_callee_save_regs).
  exact index_float_callee_save_inj.
  intros. red. split; auto. generalize (index_float_callee_save_pos r H). omega.
  intro; congruence.
  intro; congruence.
  auto.
  intros; congruence.
  intros until idx. destruct idx; simpl; auto. congruence.
  apply incl_refl.
  apply float_callee_save_norepet. eauto.
  intros [fr' [A [B C]]].
  exists fr'. split. unfold save_callee_save_float; eauto.
  split. auto. 
  intros. apply C. auto. intros; subst. red; intros; subst idx. contradiction. 
Qed.

Lemma save_callee_save_correct:
  forall sp k rs m ls cs,
  (forall r, rs r = ls (R r)) ->
  (forall ofs ty,
     In (S (Outgoing ofs ty)) (loc_arguments f.(Linear.fn_sig)) ->
     get_parent_slot cs ofs ty (ls (S (Outgoing ofs ty)))) ->
  exists fr',
    star step tge
       (State stack tf sp (save_callee_save fe k) rs empty_frame m)
    E0 (State stack tf sp k rs fr' m)
  /\ agree (call_regs ls) ls rs fr' cs.
Proof.
  intros. unfold save_callee_save.
  exploit save_callee_save_int_correct; eauto. 
  intros [fr1 [A1 [B1 C1]]].
  exploit save_callee_save_float_correct. 
  intros [fr2 [A2 [B2 C2]]].
  exists fr2.
  split. eapply star_trans. eexact A1. eexact A2. traceEq.
  constructor; unfold call_regs; auto.
  (* agree_local *)
  intros. rewrite C2; auto with stacking. 
  rewrite C1; auto with stacking. 
  (* agree_outgoing *)
  intros. rewrite C2; auto with stacking. 
  rewrite C1; auto with stacking.
  (* agree_incoming *)
  intros. apply H0. unfold loc_parameters in H1.
  exploit list_in_map_inv; eauto. intros [l [A B]].
  exploit loc_arguments_acceptable; eauto. intro C.
  destruct l; simpl in A. discriminate.
  simpl in C. destruct s; try contradiction. inv A. auto.
  (* agree_saved_int *)
  intros. rewrite C2; auto with stacking.
  rewrite B1; auto with stacking. 
  (* agree_saved_float *)
  intros. rewrite B2; auto with stacking. 
Qed.

(** The following lemmas show the correctness of the register reloading
  code generated by [reload_callee_save]: after this code has executed,
  all callee-save registers contain the same values they had at
  function entry. *)

Section RESTORE_CALLEE_SAVE.

Variable bound: frame_env -> Z.
Variable number: mreg -> Z.
Variable mkindex: Z -> frame_index.
Variable ty: typ.
Variable sp: val.
Variable csregs: list mreg.
Hypothesis mkindex_valid:
  forall r, In r csregs -> number r < bound fe -> index_valid (mkindex (number r)).
Hypothesis mkindex_not_link:
  forall z, mkindex z <> FI_link.
Hypothesis mkindex_not_retaddr:
  forall z, mkindex z <> FI_retaddr.
Hypothesis mkindex_typ:
  forall z, type_of_index (mkindex z) = ty.
Hypothesis number_within_bounds:
  forall r, In r csregs ->
  (number r < bound fe <-> mreg_within_bounds b r).
Hypothesis mkindex_val:
  forall ls ls0 rs fr cs r, 
  agree ls ls0 rs fr cs -> In r csregs -> number r < bound fe ->
  index_val (mkindex (number r)) fr = ls0 (R r).

Lemma restore_callee_save_regs_correct:
  forall k fr m ls0 l ls rs cs,
  incl l csregs ->
  list_norepet l -> 
  agree ls ls0 rs fr cs ->
  exists ls', exists rs',
    star step tge
      (State stack tf sp
        (restore_callee_save_regs bound number mkindex ty fe l k) rs fr m)
   E0 (State stack tf sp k rs' fr m)
  /\ (forall r, In r l -> rs' r = ls0 (R r))
  /\ (forall r, ~(In r l) -> rs' r = rs r)
  /\ agree ls' ls0 rs' fr cs.
Proof.
  induction l; intros; simpl restore_callee_save_regs.
  (* base case *)
  exists ls. exists rs. 
  split. apply star_refl. 
  split. intros. elim H2. 
  split. auto. auto.
  (* inductive case *)
  set (k1 := restore_callee_save_regs bound number mkindex ty fe l k).
  assert (R0: In a csregs). apply H; auto with coqlib.
  assert (R1: incl l csregs). eauto with coqlib.
  assert (R2: list_norepet l). inversion H0; auto.
  unfold restore_callee_save_reg.
  destruct (zlt (number a) (bound fe)).
  set (ls1 := Locmap.set (R a) (ls0 (R a)) ls).
  set (rs1 := Regmap.set a (ls0 (R a)) rs).
  assert (R3: agree ls1 ls0 rs1 fr cs). 
    unfold ls1, rs1. apply agree_set_reg. auto. 
    rewrite <- number_within_bounds; auto. 
  generalize (IHl ls1 rs1 cs R1 R2 R3). 
  intros [ls' [rs' [A [B [C D]]]]].
  exists ls'. exists rs'. split. 
  apply star_left with E0 (State stack tf sp k1 rs1 fr m) E0.
  unfold rs1; apply exec_Mgetstack. apply get_slot_index; auto. 
  symmetry. eapply mkindex_val; eauto.  
  auto. traceEq.
  split. intros. elim H2; intros.
  subst r. rewrite C. unfold rs1. apply Regmap.gss. inversion H0; auto.
  auto.
  split. intros. simpl in H2. rewrite C. unfold rs1. apply Regmap.gso.
  apply sym_not_eq; tauto. tauto.
  assumption.
  (* no load takes place *)
  generalize (IHl ls rs cs R1 R2 H1).  
  intros [ls' [rs' [A [B [C D]]]]].
  exists ls'; exists rs'. split. assumption.
  split. intros. elim H2; intros. 
  subst r. apply (agree_unused_reg _ _ _ _ _ D).
  rewrite <- number_within_bounds. auto. auto. auto.
  split. intros. simpl in H2. apply C. tauto.
  assumption.
Qed.

End RESTORE_CALLEE_SAVE.

Lemma restore_int_callee_save_correct:
  forall sp k fr m ls0 ls rs cs,
  agree ls ls0 rs fr cs ->
  exists ls', exists rs',
    star step tge
       (State stack tf sp
         (restore_callee_save_int fe k) rs fr m)
    E0 (State stack tf sp k rs' fr m)
  /\ (forall r, In r int_callee_save_regs -> rs' r = ls0 (R r))
  /\ (forall r, ~(In r int_callee_save_regs) -> rs' r = rs r)
  /\ agree ls' ls0 rs' fr cs.
Proof.
  intros. unfold restore_callee_save_int.
  apply restore_callee_save_regs_correct with int_callee_save_regs ls.
  intros; simpl. split; auto. generalize (index_int_callee_save_pos r H0). omega.
  intros; congruence.
  intros; congruence.
  auto.
  intros. unfold mreg_within_bounds. 
  rewrite (int_callee_save_type r H0). tauto. 
  eauto with stacking. 
  apply incl_refl.
  apply int_callee_save_norepet.
  auto.
Qed.

Lemma restore_float_callee_save_correct:
  forall sp k fr m ls0 ls rs cs,
  agree ls ls0 rs fr cs ->
  exists ls', exists rs',
    star step tge
       (State stack tf sp
          (restore_callee_save_float fe k) rs fr m)
    E0 (State stack tf sp k rs' fr m)
  /\ (forall r, In r float_callee_save_regs -> rs' r = ls0 (R r))
  /\ (forall r, ~(In r float_callee_save_regs) -> rs' r = rs r)
  /\ agree ls' ls0 rs' fr cs.
Proof.
  intros. unfold restore_callee_save_float.
  apply restore_callee_save_regs_correct with float_callee_save_regs ls.
  intros; simpl. split; auto. generalize (index_float_callee_save_pos r H0). omega.
  intros; congruence.
  intros; congruence.
  auto.
  intros. unfold mreg_within_bounds. 
  rewrite (float_callee_save_type r H0). tauto. 
  eauto with stacking. 
  apply incl_refl.
  apply float_callee_save_norepet.
  auto.
Qed.

Lemma restore_callee_save_correct:
  forall sp k fr m ls0 ls rs cs,
  agree ls ls0 rs fr cs ->
  exists rs',
    star step tge
       (State stack tf sp (restore_callee_save fe k) rs fr m)
    E0 (State stack tf sp k rs' fr m)
  /\ (forall r, 
        In r int_callee_save_regs \/ In r float_callee_save_regs -> 
        rs' r = ls0 (R r))
  /\ (forall r, 
        ~(In r int_callee_save_regs) ->
        ~(In r float_callee_save_regs) ->
        rs' r = rs r).
Proof.
  intros. unfold restore_callee_save.
  exploit restore_int_callee_save_correct; eauto.
  intros [ls1 [rs1 [A [B [C D]]]]].
  exploit restore_float_callee_save_correct. eexact D.
  intros [ls2 [rs2 [P [Q [R S]]]]].
  exists rs2. split. eapply star_trans. eexact A. eexact P. traceEq.
  split. intros. elim H0; intros.
  rewrite R. apply B. auto. apply list_disjoint_notin with int_callee_save_regs.
  apply int_float_callee_save_disjoint. auto.
  apply Q. auto.
  intros. rewrite R. apply C. auto. auto.
Qed.

End FRAME_PROPERTIES.

(** * Semantic preservation *)

(** Preservation of code labels through the translation. *)

Section LABELS.

Remark find_label_fold_right:
  forall (A: Type) (fn: A -> Mach.code -> Mach.code) lbl,
  (forall x k, Mach.find_label lbl (fn x k) = Mach.find_label lbl k) ->  forall (args: list A) k,
  Mach.find_label lbl (List.fold_right fn k args) = Mach.find_label lbl k.
Proof.
  induction args; simpl. auto. 
  intros. rewrite H. auto.
Qed.

Remark find_label_save_callee_save:
  forall fe lbl k,
  Mach.find_label lbl (save_callee_save fe k) = Mach.find_label lbl k.
Proof.
  intros. unfold save_callee_save, save_callee_save_int, save_callee_save_float, save_callee_save_regs.
  repeat rewrite find_label_fold_right. reflexivity.
  intros. unfold save_callee_save_reg. 
  case (zlt (index_float_callee_save x) (fe_num_float_callee_save fe));
  intro; reflexivity.
  intros. unfold save_callee_save_reg.  
  case (zlt (index_int_callee_save x) (fe_num_int_callee_save fe));
  intro; reflexivity.
Qed.

Remark find_label_restore_callee_save:
  forall fe lbl k,
  Mach.find_label lbl (restore_callee_save fe k) = Mach.find_label lbl k.
Proof.
  intros. unfold restore_callee_save, restore_callee_save_int, restore_callee_save_float, restore_callee_save_regs.
  repeat rewrite find_label_fold_right. reflexivity.
  intros. unfold restore_callee_save_reg. 
  case (zlt (index_float_callee_save x) (fe_num_float_callee_save fe));
  intro; reflexivity.
  intros. unfold restore_callee_save_reg. 
  case (zlt (index_int_callee_save x) (fe_num_int_callee_save fe));
  intro; reflexivity.
Qed.

Lemma find_label_transl_code:
  forall fe lbl c,
  Mach.find_label lbl (transl_code fe c) =
    option_map (transl_code fe) (Linear.find_label lbl c).
Proof.
  induction c; simpl; intros.
  auto.
  destruct a; unfold transl_instr; auto.
  destruct s; simpl; auto.
  destruct s; simpl; auto.
  rewrite find_label_restore_callee_save. auto.
  simpl. case (peq lbl l); intro. reflexivity. auto.
  rewrite find_label_restore_callee_save. auto.
Qed.

Lemma transl_find_label:
  forall f tf lbl c,
  transf_function f = OK tf ->
  Linear.find_label lbl f.(Linear.fn_code) = Some c ->
  Mach.find_label lbl tf.(Mach.fn_code) = 
    Some (transl_code (make_env (function_bounds f)) c).
Proof.
  intros. rewrite (unfold_transf_function _ _ H).  simpl. 
  unfold transl_body. rewrite find_label_save_callee_save.
  rewrite find_label_transl_code. rewrite H0. reflexivity.
Qed.

End LABELS.

(** Code inclusion property for Linear executions. *)

Lemma find_label_incl:
  forall lbl c c', 
  Linear.find_label lbl c = Some c' -> incl c' c.
Proof.
  induction c; simpl.
  intros; discriminate.
  intro c'. case (Linear.is_label lbl a); intros.
  injection H; intro; subst c'. red; intros; auto with coqlib. 
  apply incl_tl. auto.
Qed.

(** Preservation / translation of global symbols and functions. *)

Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_var_info_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof
  (Genv.find_funct_transf_partial transf_fundef _ TRANSF).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transf_fundef _ TRANSF).

Lemma sig_preserved:
  forall f tf, transf_fundef f = OK tf -> Mach.funsig tf = Linear.funsig f.
Proof.
  intros until tf; unfold transf_fundef, transf_partial_fundef.
  destruct f. unfold transf_function. 
  destruct (zlt (Linear.fn_stacksize f) 0). simpl; congruence.
  destruct (zlt (- Int.min_signed) (fe_size (make_env (function_bounds f)))). simpl; congruence.
  unfold bind. intros. inversion H; reflexivity. 
  intro. inversion H. reflexivity.
Qed.

Lemma stacksize_preserved:
  forall f tf, transf_function f = OK tf -> Mach.fn_stacksize tf = Linear.fn_stacksize f.
Proof.
  intros until tf; unfold transf_function. 
  destruct (zlt (Linear.fn_stacksize f) 0). simpl; congruence.
  destruct (zlt (- Int.min_signed) (fe_size (make_env (function_bounds f)))). simpl; congruence.
  intros. inversion H; reflexivity. 
Qed.

Lemma find_function_translated:
  forall f0 tf0 ls ls0 rs fr cs ros f,
  agree f0 tf0 ls ls0 rs fr cs ->
  Linear.find_function ge ros ls = Some f ->
  exists tf,
  find_function tge ros rs = Some tf /\ transf_fundef f = OK tf.
Proof.
  intros until f; intro AG.
  destruct ros; simpl.
  rewrite (agree_eval_reg _ _ _ _ _ _ _ m AG). intro.
  apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); try congruence.
  intro. apply function_ptr_translated; auto.
Qed.

Hypothesis wt_prog: wt_program prog.

Lemma find_function_well_typed:
  forall ros ls f,
  Linear.find_function ge ros ls = Some f -> wt_fundef f.
Proof.
  intros until f; destruct ros; simpl; unfold ge.
  intro. eapply Genv.find_funct_prop; eauto.
  destruct (Genv.find_symbol (Genv.globalenv prog) i); try congruence.
  intro. eapply Genv.find_funct_ptr_prop; eauto. 
Qed.

(** Correctness of stack pointer relocation in operations and
  addressing modes. *)

Definition shift_sp (tf: Mach.function) (sp: val) :=
  Val.add sp (Vint (Int.repr (-tf.(fn_framesize)))).

Remark shift_sp_eq:
  forall f tf sp,
  transf_function f = OK tf ->
  shift_sp tf sp = Val.sub sp (Vint (Int.repr (fe_size (make_env (function_bounds f))))).
Proof.
  intros. unfold shift_sp.
  replace (fe_size (make_env (function_bounds f))) with (fn_framesize tf).
  rewrite <- Int.neg_repr. destruct sp; simpl; auto; rewrite Int.sub_add_opp; auto.
  rewrite (unfold_transf_function _ _ H). auto.
Qed.

Lemma shift_eval_operation:
  forall f tf sp op args v,
  transf_function f = OK tf ->
  eval_operation ge sp op args = Some v ->
  eval_operation tge (shift_sp tf sp) 
                 (transl_op (make_env (function_bounds f)) op) args = Some v.
Proof.
  intros. rewrite <- H0. rewrite (shift_sp_eq f tf sp H). unfold transl_op.
  rewrite (eval_operation_preserved ge tge). 
  apply shift_stack_eval_operation.
  exact symbols_preserved.
Qed.

Lemma shift_eval_addressing:
  forall f tf sp addr args v,
  transf_function f = OK tf ->
  eval_addressing ge sp addr args = Some v ->
  eval_addressing tge (shift_sp tf sp) 
                 (transl_addr (make_env (function_bounds f)) addr) args =
  Some v.
Proof.
  intros. rewrite <- H0. rewrite (shift_sp_eq f tf sp H). unfold transl_addr.
  rewrite (eval_addressing_preserved ge tge). 
  apply shift_stack_eval_addressing.
  exact symbols_preserved.
Qed.

(** Preservation of the arguments to an external call. *)

Section EXTERNAL_ARGUMENTS.

Variable cs: list Machabstr.stackframe.
Variable ls: locset.
Variable rs: regset.
Variable sg: signature.

Hypothesis AG1: forall r, rs r = ls (R r).
Hypothesis AG2: forall (ofs : Z) (ty : typ),
      In (S (Outgoing ofs ty)) (loc_arguments sg) ->
      get_parent_slot cs ofs ty (ls (S (Outgoing ofs ty))).

Lemma transl_external_arguments_rec:
  forall locs,
  incl locs (loc_arguments sg) ->
  extcall_args (parent_function cs) rs (parent_frame cs) locs ls##locs.
Proof.
  induction locs; simpl; intros.
  constructor.
  constructor. 
  assert (loc_argument_acceptable a). 
    apply loc_arguments_acceptable with sg; auto with coqlib.
  destruct a; red in H0.
  rewrite <- AG1. constructor. 
  destruct s; try contradiction.
  constructor. change (get_parent_slot cs z t (ls (S (Outgoing z t)))).
apply AG2. auto with coqlib. 
  apply IHlocs; eauto with coqlib.
Qed.

Lemma transl_external_arguments:
  extcall_arguments (parent_function cs) rs (parent_frame cs) sg (ls ## (loc_arguments sg)).
Proof.
  unfold extcall_arguments. 
  apply transl_external_arguments_rec.
  auto with coqlib.
Qed.

End EXTERNAL_ARGUMENTS.

(** The proof of semantic preservation relies on simulation diagrams
  of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                  +|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  Matching between source and target states is defined by [match_states]
  below.  It implies:
- Agreement between, on the Linear side, the location sets [ls]
  and [parent_locset s] of the current function and its caller,
  and on the Mach side the register set [rs], the frame [fr]
  and the caller's frame [parent_frame ts].
- Inclusion between the Linear code [c] and the code of the
  function [f] being executed.
- Well-typedness of [f].
*)

Inductive match_stacks: list Linear.stackframe -> list Machabstr.stackframe -> Prop :=
  | match_stacks_nil:
      match_stacks nil nil
  | match_stacks_cons:
      forall f sp c ls tf fr s ts,
      match_stacks s ts ->
      transf_function f = OK tf ->
      wt_function f ->
      agree_frame f tf ls (parent_locset s) fr ts ->
      incl c (Linear.fn_code f) ->
      match_stacks
       (Linear.Stackframe f sp ls c :: s)
       (Machabstr.Stackframe tf (shift_sp tf sp) (transl_code (make_env (function_bounds f)) c) fr :: ts).

Inductive match_states: Linear.state -> Machabstr.state -> Prop :=
  | match_states_intro:
      forall s f sp c ls m ts tf rs fr
        (STACKS: match_stacks s ts)
        (TRANSL: transf_function f = OK tf)
        (WTF: wt_function f)
        (AG: agree f tf ls (parent_locset s) rs fr ts)
        (INCL: incl c (Linear.fn_code f)),
      match_states (Linear.State s f sp c ls m)
                   (Machabstr.State ts tf (shift_sp tf sp) (transl_code (make_env (function_bounds f)) c) rs fr m)
  | match_states_call:
      forall s f ls m ts tf rs
        (STACKS: match_stacks s ts)
        (TRANSL: transf_fundef f = OK tf)
        (WTF: wt_fundef f)
        (AG1: forall r, rs r = ls (R r))
        (AG2: forall ofs ty, 
                In (S (Outgoing ofs ty)) (loc_arguments (Linear.funsig f)) ->
                get_parent_slot ts ofs ty (ls (S (Outgoing ofs ty))))
        (AG3: agree_callee_save ls (parent_locset s)),
      match_states (Linear.Callstate s f ls m)
                   (Machabstr.Callstate ts tf rs m)
  | match_states_return:
      forall s ls m ts rs
        (STACKS: match_stacks s ts)
        (AG1: forall r, rs r = ls (R r))
        (AG2: agree_callee_save ls (parent_locset s)),
      match_states (Linear.Returnstate s ls m)
                   (Machabstr.Returnstate ts rs m).

Theorem transf_step_correct:
  forall s1 t s2, Linear.step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', plus step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  assert (RED: forall f i c,
          transl_code (make_env (function_bounds f)) (i :: c) = 
          transl_instr (make_env (function_bounds f)) i
                       (transl_code (make_env (function_bounds f)) c)).
    intros. reflexivity.
  induction 1; intros;
  try inv MS;
  try rewrite RED;
  try (generalize (WTF _ (INCL _ (in_eq _ _))); intro WTI);
  try (generalize (function_is_within_bounds f WTF _ (INCL _ (in_eq _ _)));
       intro BOUND; simpl in BOUND);
  unfold transl_instr.
  (* Lgetstack *)
  inv WTI. destruct BOUND. unfold undef_getstack; destruct sl.
  (* Lgetstack, local *)
  exists (State ts tf (shift_sp tf sp) (transl_code (make_env (function_bounds f)) b)
             (rs0#r <- (rs (S (Local z t)))) fr m); split.
  apply plus_one. apply exec_Mgetstack.
  apply get_slot_index. auto. apply index_local_valid. auto. congruence. congruence. auto.
  eapply agree_locals; eauto.
  econstructor; eauto with coqlib. 
  apply agree_set_reg; auto.
  (* Lgetstack, incoming *)
  exists (State ts tf (shift_sp tf sp) (transl_code (make_env (function_bounds f)) b)
             (rs0 # IT1 <- Vundef # r <- (rs (S (Incoming z t)))) fr m); split.
  apply plus_one. apply exec_Mgetparam.
  change (get_parent_slot ts z t (rs (S (Incoming z t)))).
  eapply agree_incoming; eauto.
  econstructor; eauto with coqlib. 
  apply agree_set_reg; auto. apply agree_undef_getparam; auto.
  (* Lgetstack, outgoing *)
  exists (State ts tf (shift_sp tf sp) (transl_code (make_env (function_bounds f)) b)
             (rs0#r <- (rs (S (Outgoing z t)))) fr m); split.
  apply plus_one. apply exec_Mgetstack.
  apply get_slot_index. auto. apply index_arg_valid. auto. congruence. congruence. auto.
  eapply agree_outgoing; eauto.
  econstructor; eauto with coqlib. 
  apply agree_set_reg; auto.

  (* Lsetstack *)
  inv WTI. destruct sl.

  (* Lsetstack, local *)
  generalize (agree_set_local _ _ TRANSL _ _ _ _ _ (rs0 r) _ _ AG BOUND).
  intros [fr' [SET AG']].
  econstructor; split.
  apply plus_one. eapply exec_Msetstack; eauto.
  econstructor; eauto with coqlib.
  replace (rs (R r)) with (rs0 r). auto.
  symmetry. eapply agree_reg; eauto.
  (* Lsetstack, incoming *)
  contradiction.
  (* Lsetstack, outgoing *)
  generalize (agree_set_outgoing _ _ TRANSL _ _ _ _ _ (rs0 r) _ _ AG BOUND).
  intros [fr' [SET AG']].
  econstructor; split.
  apply plus_one. eapply exec_Msetstack; eauto.
  econstructor; eauto with coqlib.
  replace (rs (R r)) with (rs0 r). auto.
  symmetry. eapply agree_reg; eauto.

  (* Lop *)
  set (op' := transl_op (make_env (function_bounds f)) op).
  exists (State ts tf (shift_sp tf sp) (transl_code (make_env (function_bounds f)) b) ((undef_op op' rs0)#res <- v) fr m); split.
  apply plus_one. apply exec_Mop. 
  apply shift_eval_operation. auto. 
  change mreg with RegEq.t.
  rewrite (agree_eval_regs _ _ _ _ _ _ _ args AG). auto.
  econstructor; eauto with coqlib.
  apply agree_set_reg; auto. apply agree_undef_op; auto.

  (* Lload *)
  exists (State ts tf (shift_sp tf sp) (transl_code (make_env (function_bounds f)) b) ((undef_temps rs0)#dst <- v) fr m); split.
  apply plus_one; eapply exec_Mload; eauto.
  apply shift_eval_addressing; auto. 
  change mreg with RegEq.t.
  rewrite (agree_eval_regs _ _ _ _ _ _ _ args AG). eauto.
  econstructor; eauto with coqlib.
  apply agree_set_reg; auto. apply agree_undef_temps; auto.

  (* Lstore *)
  econstructor; split.
  apply plus_one; eapply exec_Mstore; eauto.
  apply shift_eval_addressing; eauto. 
  change mreg with RegEq.t.
  rewrite (agree_eval_regs _ _ _ _ _ _ _ args AG). eauto.
  rewrite (agree_eval_reg _ _ _ _ _ _ _ src AG). eauto.
  econstructor; eauto with coqlib. apply agree_undef_temps; auto.

  (* Lcall *) 
  assert (WTF': wt_fundef f'). eapply find_function_well_typed; eauto.
  exploit find_function_translated; eauto. 
  intros [tf' [FIND' TRANSL']].
  econstructor; split.
  apply plus_one; eapply exec_Mcall; eauto.
  econstructor; eauto. 
  econstructor; eauto with coqlib.
  exists rs0; auto.
  intro. symmetry. eapply agree_reg; eauto.
  intros.
  assert (slot_within_bounds f (function_bounds f) (Outgoing ofs ty)).
  red. simpl. generalize (loc_arguments_bounded _ _ _ H0). 
  generalize (loc_arguments_acceptable _ _ H0). unfold loc_argument_acceptable. 
  omega.
  unfold get_parent_slot, parent_function, parent_frame. 
  change (fe_ofs_arg + 4 * ofs)
    with (offset_of_index (make_env (function_bounds f)) (FI_arg ofs ty)).
  apply get_slot_index. auto. apply index_arg_valid. auto. congruence. congruence. auto.
  eapply agree_outgoing; eauto.
  simpl. red; auto.

  (* Ltailcall *) 
  assert (WTF': wt_fundef f'). eapply find_function_well_typed; eauto.
  exploit find_function_translated; eauto. 
  intros [tf' [FIND' TRANSL']].
  generalize (restore_callee_save_correct ts _ _ TRANSL
               (shift_sp tf (Vptr stk Int.zero)) 
               (Mtailcall (Linear.funsig f') ros :: transl_code (make_env (function_bounds f)) b)
               _ m _ _ _ _ AG).
  intros [rs2 [A [B C]]].
  assert (FIND'': find_function tge ros rs2 = Some tf').
    rewrite <- FIND'. destruct ros; simpl; auto.
    inv WTI. rewrite C. auto. 
    simpl. intuition congruence. simpl. intuition congruence. 
  econstructor; split.
  eapply plus_right. eexact A. 
  simpl shift_sp. eapply exec_Mtailcall; eauto.
  rewrite (stacksize_preserved _ _ TRANSL); eauto.
  traceEq.
  econstructor; eauto. 
  intros; symmetry; eapply agree_return_regs; eauto.
  intros. inv WTI. generalize (H4 _ H0). tauto.
  apply agree_callee_save_return_regs.

  (* Lbuiltin *)
  econstructor; split.
  apply plus_one. apply exec_Mbuiltin.
  change mreg with RegEq.t.
  rewrite (agree_eval_regs _ _ _ _ _ _ _ args AG).
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto with coqlib.
  apply agree_set_reg; auto. apply agree_undef_temps; auto.
 
  (* Llabel *)
  econstructor; split.
  apply plus_one; apply exec_Mlabel.
  econstructor; eauto with coqlib.

  (* Lgoto *)
  econstructor; split.
  apply plus_one; apply exec_Mgoto.
  apply transl_find_label; eauto.
  econstructor; eauto. 
  eapply find_label_incl; eauto.

  (* Lcond, true *)
  econstructor; split.
  apply plus_one; apply exec_Mcond_true.
  rewrite <- (agree_eval_regs _ _ _ _ _ _ _ args AG) in H; eauto.
  apply transl_find_label; eauto.
  econstructor; eauto. apply agree_undef_temps; auto.
  eapply find_label_incl; eauto.

  (* Lcond, false *)
  econstructor; split.
  apply plus_one; apply exec_Mcond_false.
  rewrite <- (agree_eval_regs _ _ _ _ _ _ _ args AG) in H; auto.
  econstructor; eauto with coqlib. apply agree_undef_temps; auto.

  (* Ljumptable *)
  econstructor; split.
  apply plus_one; eapply exec_Mjumptable.
  rewrite <- (agree_eval_reg _ _ _ _ _ _ _ arg AG) in H; eauto.
  eauto. 
  apply transl_find_label; eauto.
  econstructor; eauto. apply agree_undef_temps; auto.
  eapply find_label_incl; eauto.

  (* Lreturn *)
  exploit restore_callee_save_correct; eauto.
  intros [ls' [A [B C]]].
  econstructor; split.
  eapply plus_right. eauto. 
  simpl shift_sp. econstructor; eauto.
  rewrite (stacksize_preserved _ _ TRANSL); eauto.
  traceEq.
  econstructor; eauto. 
  intros. symmetry. eapply agree_return_regs; eauto.
  apply agree_callee_save_return_regs.  

  (* internal function *)
  generalize TRANSL; clear TRANSL. 
  unfold transf_fundef, transf_partial_fundef.
  caseEq (transf_function f); simpl; try congruence.
  intros tfn TRANSL EQ. inversion EQ; clear EQ; subst tf.
  inversion WTF as [|f' WTFN]. subst f'.
  set (sp := Vptr stk Int.zero) in *.
  set (tsp := shift_sp tfn sp).
  set (fe := make_env (function_bounds f)).
  exploit save_callee_save_correct; eauto. 
  intros [fr [EXP AG]].
  econstructor; split.
  eapply plus_left.
  eapply exec_function_internal; eauto.
  rewrite (unfold_transf_function f tfn TRANSL); simpl; eexact H. 
  replace (Mach.fn_code tfn) with
          (transl_body f (make_env (function_bounds f))).    
  replace (Vptr stk (Int.repr (- fn_framesize tfn))) with tsp.
  unfold transl_body. eexact EXP.
  unfold tsp, shift_sp, sp. unfold Val.add. 
  rewrite Int.add_commut. rewrite Int.add_zero. auto.
  rewrite (unfold_transf_function f tfn TRANSL). simpl. auto.
  traceEq.
  unfold tsp. econstructor; eauto with coqlib.
  eapply agree_callee_save_agree; eauto. 

  (* external function *)
  simpl in TRANSL. inversion TRANSL; subst tf.
  inversion WTF. subst ef0.
  exploit transl_external_arguments; eauto. intro EXTARGS.
  econstructor; split.
  apply plus_one. eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.
  intros. unfold Regmap.set. case (RegEq.eq r (loc_result (ef_sig ef))); intro.
  rewrite e. rewrite Locmap.gss; auto. rewrite Locmap.gso; auto.
  red; auto.
  apply agree_callee_save_set_result; auto.

  (* return *)
  inv STACKS. 
  econstructor; split.
  apply plus_one. apply exec_return. 
  econstructor; eauto. simpl in AG2.  
  eapply agree_frame_agree; eauto.
Qed.

Lemma transf_initial_states:
  forall st1, Linear.initial_state prog st1 ->
  exists st2, Machabstr.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  econstructor; split.
  econstructor. 
  eapply Genv.init_mem_transf_partial; eauto.
  rewrite (transform_partial_program_main _ _ TRANSF). 
  rewrite symbols_preserved. eauto.
  eauto. 
  econstructor; eauto. constructor. 
  eapply Genv.find_funct_ptr_prop; eauto.
  intros. rewrite H3 in H5. simpl in H5. contradiction.
  simpl; red; auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> Linear.final_state st1 r -> Machabstr.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. econstructor. rewrite AG1; auto.
Qed.

Theorem transf_program_correct:
  forall (beh: program_behavior), not_wrong beh ->
  Linear.exec_program prog beh -> Machabstr.exec_program tprog beh.
Proof.
  unfold Linear.exec_program, Machabstr.exec_program; intros.
  eapply simulation_plus_preservation; eauto.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact transf_step_correct. 
Qed.

End PRESERVATION.
