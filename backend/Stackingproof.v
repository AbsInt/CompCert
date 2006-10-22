(** Correctness proof for the translation from Linear to Mach. *)

(** This file proves semantic preservation for the [Stacking] pass.
  For the target language Mach, we use the alternate semantics
  given in file [Machabstr], where a part of the activation record
  is not resident in memory.  Combined with the semantic equivalence
  result between the two Mach semantics (see file [Machabstr2mach]),
  the proof in this file also shows semantic preservation with
  respect to the standard Mach semantics. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Op.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Locations.
Require Import Mach.
Require Import Machabstr.
Require Import Linear.
Require Import Lineartyping.
Require Import Conventions.
Require Import Stacking.

(** * Properties of frames and frame accesses *)

(** ``Good variable'' properties for frame accesses. *)

Lemma get_slot_ok:
  forall fr ty ofs,
  0 <= ofs -> fr.(low) + ofs + 4 * typesize ty <= 0 ->
  exists v, get_slot fr ty ofs v.
Proof.
  intros. exists (load_contents (mem_type ty) fr.(contents) (fr.(low) + ofs)).
  constructor; auto. 
Qed.

Lemma set_slot_ok:
  forall fr ty ofs v,
  fr.(high) = 0 -> 0 <= ofs -> fr.(low) + ofs + 4 * typesize ty <= 0 ->
  exists fr', set_slot fr ty ofs v fr'.
Proof.
  intros.
  exists (mkblock fr.(low) fr.(high)
           (store_contents (mem_type ty) fr.(contents) (fr.(low) + ofs) v)
           (set_slot_undef_outside fr ty ofs v H H0 H1 fr.(undef_outside))).
  constructor; auto. 
Qed.

Lemma slot_gss: 
  forall fr1 ty ofs v fr2,
  set_slot fr1 ty ofs v fr2 ->
  get_slot fr2 ty ofs v.
Proof.
  intros. induction H. 
  constructor.
  auto.  simpl.  auto. 
  simpl. symmetry. apply load_store_contents_same. 
Qed.

Lemma slot_gso:
  forall fr1 ty ofs v fr2 ty' ofs' v',
  set_slot fr1 ty ofs v fr2 ->
  get_slot fr1 ty' ofs' v' ->
  ofs' + 4 * typesize ty' <= ofs \/ ofs + 4 * typesize ty <= ofs' ->
  get_slot fr2 ty' ofs' v'.
Proof.
  intros. induction H; inversion H0.
  constructor.
  auto.  simpl low. auto.
  simpl. rewrite H3. symmetry. apply load_store_contents_other. 
  repeat (rewrite size_mem_type). omega. 
Qed.

Lemma slot_gi:
  forall f ofs ty,
  0 <= ofs -> (init_frame f).(low) + ofs + 4 * typesize ty <= 0 ->
  get_slot (init_frame f) ty ofs Vundef.
Proof.
  intros. constructor.
  auto. auto. 
  symmetry. apply load_contents_init. 
Qed.

Section PRESERVATION.

Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: transf_program prog = Some tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Section FRAME_PROPERTIES.

Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable tf: Mach.function.
Hypothesis TRANSF_F: transf_function f = Some tf.

Lemma unfold_transf_function:
  tf = Mach.mkfunction
         f.(Linear.fn_sig)
         (transl_body f fe)
         f.(Linear.fn_stacksize)
         fe.(fe_size).
Proof.
  generalize TRANSF_F. unfold transf_function.
  case (zlt (fn_stacksize f) 0). intros; discriminate.
  case (zlt (- Int.min_signed) (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe. unfold b. congruence.
Qed.

Lemma size_no_overflow: fe.(fe_size) <= -Int.min_signed.
Proof.
  generalize TRANSF_F. unfold transf_function.
  case (zlt (fn_stacksize f) 0). intros; discriminate.
  case (zlt (- Int.min_signed) (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe, b. omega.
Qed.

(** A frame index is valid if it lies within the resource bounds
  of the current function. *)

Definition index_valid (idx: frame_index) :=
  match idx with
  | FI_local x Tint => 0 <= x < b.(bound_int_local)
  | FI_local x Tfloat => 0 <= x < b.(bound_float_local)
  | FI_arg x ty => 6 <= x /\ x + typesize ty <= b.(bound_outgoing)
  | FI_saved_int x => 0 <= x < b.(bound_int_callee_save)
  | FI_saved_float x => 0 <= x < b.(bound_float_callee_save)
  end.

Definition type_of_index (idx: frame_index) :=
  match idx with
  | FI_local x ty => ty
  | FI_arg x ty => ty
  | FI_saved_int x => Tint
  | FI_saved_float x => Tfloat
  end.

(** Non-overlap between the memory areas corresponding to two
  frame indices. *)

Definition index_diff (idx1 idx2: frame_index) : Prop :=
  match idx1, idx2 with
  | FI_local x1 ty1, FI_local x2 ty2 =>
      x1 <> x2 \/ ty1 <> ty2
  | FI_arg x1 ty1, FI_arg x2 ty2 =>
      x1 + typesize ty1 <= x2 \/ x2 + typesize ty2 <= x1
  | FI_saved_int x1, FI_saved_int x2 => x1 <> x2
  | FI_saved_float x1, FI_saved_float x2 => x1 <> x2
  | _, _ => True
  end.

Remark align_float_part:
  4 * bound_outgoing b + 4 * bound_int_local b + 4 * bound_int_callee_save b <=
  align (4 * bound_outgoing b + 4 * bound_int_local b + 4 * bound_int_callee_save b) 8.
Proof.
  apply align_le. omega.
Qed.

Ltac AddPosProps :=
  assert (bound_int_local b >= 0);
  [unfold b; apply bound_int_local_pos |
  assert (bound_float_local b >= 0);
  [unfold b; apply bound_float_local_pos |
  assert (bound_int_callee_save b >= 0);
  [unfold b; apply bound_int_callee_save_pos |
  assert (bound_float_callee_save b >= 0);
  [unfold b; apply bound_float_callee_save_pos |
  assert (bound_outgoing b >= 6); 
  [unfold b; apply bound_outgoing_pos |
   generalize align_float_part; intro]]]]].

Lemma size_pos: fe.(fe_size) >= 24.
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
    type_of_index, typesize;
  simpl in H5; simpl in H6; simpl in H7;
  try omega.
  assert (z <> z0). intuition auto. omega.
  assert (z <> z0). intuition auto. omega.
Qed.

(** The following lemmas give sufficient conditions for indices
  of various kinds to be valid. *)

Lemma index_local_valid:
  forall ofs ty,
  slot_bounded f (Local ofs ty) ->
  index_valid (FI_local ofs ty).
Proof.
  unfold slot_bounded, index_valid. auto.
Qed.

Lemma index_arg_valid:
  forall ofs ty,
  slot_bounded f (Outgoing ofs ty) ->
  index_valid (FI_arg ofs ty).
Proof.
  unfold slot_bounded, index_valid, b. auto.
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
  24 <= offset_of_index fe idx /\
  offset_of_index fe idx + 4 * typesize (type_of_index idx) <= fe.(fe_size).
Proof.
  AddPosProps.
  intros.
  destruct idx; try destruct t;
  unfold offset_of_index, fe, make_env,
    fe_size, fe_ofs_int_local, fe_ofs_int_callee_save,
    fe_ofs_float_local, fe_ofs_float_callee_save,
    type_of_index, typesize;
  simpl in H5;
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
(* omega falls flat on its face... *)
  apply Int.signed_repr.
  split. apply Zle_trans with 24. compute; intro; discriminate.
  auto.
  assert (offset_of_index fe idx < fe_size fe).
    generalize (typesize_pos (type_of_index idx)); intro. omega.
  apply Zlt_succ_le. 
  change (Zsucc Int.max_signed) with (- Int.min_signed).
  generalize size_no_overflow. omega. 
Qed.

(** Admissible evaluation rules for the [Mgetstack] and [Msetstack]
  instructions, in case the offset is computed with [offset_of_index]. *)

Lemma exec_Mgetstack':
  forall sp parent idx ty c rs fr dst m v,
  index_valid idx ->
  get_slot fr ty (offset_of_index fe idx) v ->
  Machabstr.exec_instrs tge tf sp parent
    (Mgetstack (Int.repr (offset_of_index fe idx)) ty dst :: c) rs fr m
    E0 c (rs#dst <- v) fr m.
Proof.
  intros. apply Machabstr.exec_one. apply Machabstr.exec_Mgetstack.
  rewrite offset_of_index_no_overflow. auto. auto.
Qed.

Lemma exec_Msetstack':
  forall sp parent idx ty c rs fr src m fr',
  index_valid idx ->
  set_slot fr ty (offset_of_index fe idx) (rs src) fr' ->
  Machabstr.exec_instrs tge tf sp parent
    (Msetstack src (Int.repr (offset_of_index fe idx)) ty :: c) rs fr m
    E0 c rs fr' m.
Proof.
  intros. apply Machabstr.exec_one. apply Machabstr.exec_Msetstack.
  rewrite offset_of_index_no_overflow. auto. auto.
Qed.

(** An alternate characterization of the [get_slot] and [set_slot]
  operations in terms of the following [index_val] frame access
  function. *)

Definition index_val (idx: frame_index) (fr: frame) :=
  load_contents (mem_type (type_of_index idx))
                fr.(contents)
                (fr.(low) + offset_of_index fe idx).

Lemma get_slot_index:
  forall fr idx ty v,
  index_valid idx ->
  fr.(low) = - fe.(fe_size) ->
  ty = type_of_index idx ->
  v = index_val idx fr ->
  get_slot fr ty (offset_of_index fe idx) v.
Proof.
  intros. subst v; subst ty.
  generalize (offset_of_index_valid idx H); intros [A B].
  unfold index_val. apply get_slot_intro. omega. 
  rewrite H0. omega. auto.
Qed.

Lemma set_slot_index:
  forall fr idx v,
  index_valid idx ->
  fr.(high) = 0 ->
  fr.(low) = - fe.(fe_size) ->
  exists fr', set_slot fr (type_of_index idx) (offset_of_index fe idx) v fr'.
Proof.
  intros. 
  generalize (offset_of_index_valid idx H); intros [A B].
  apply set_slot_ok. auto. omega. rewrite H1; omega.
Qed.

(** Alternate ``good variable'' properties for [get_slot] and [set_slot]. *)
Lemma slot_iss:
  forall fr idx v fr',
  set_slot fr (type_of_index idx) (offset_of_index fe idx) v fr' ->
  index_val idx fr' = v.
Proof.
  intros. inversion H. subst ofs ty.
  unfold index_val; simpl. apply load_store_contents_same.
Qed.

Lemma slot_iso:
  forall fr idx v fr' idx',
  set_slot fr (type_of_index idx) (offset_of_index fe idx) v fr' ->
  index_diff idx idx' ->
  index_valid idx -> index_valid idx' ->
  index_val idx' fr' = index_val idx' fr.
Proof.
  intros. generalize (offset_of_index_disj idx idx' H1 H2 H0). intro.
  unfold index_val. inversion H. subst ofs ty. simpl. 
  apply load_store_contents_other. 
  repeat rewrite size_mem_type. omega.
Qed.

(** * Agreement between location sets and Mach environments *)

(** The following [agree] predicate expresses semantic agreement between
  a location set on the Linear side and, on the Mach side,
  a register set, plus the current and parent frames, plus the register
  set [rs0] at function entry. *)

Record agree (ls: locset) (rs: regset) (fr parent: frame) (rs0: regset) : Prop :=
  mk_agree {
    (** Machine registers have the same values on the Linear and Mach sides. *)
    agree_reg:
      forall r, ls (R r) = rs r;

    (** Machine registers outside the bounds of the current function
        have the same values they had at function entry.  In other terms,
        these registers are never assigned. *)
    agree_unused_reg:
      forall r, ~(mreg_bounded f r) -> rs r = rs0 r;

    (** The bounds of the current frame are [[- fe.(fe_size), 0]]. *)
    agree_high:
      fr.(high) = 0;
    agree_size:
      fr.(low) = - fe.(fe_size);

    (** Local and outgoing stack slots (on the Linear side) have
        the same values as the one loaded from the current Mach frame 
        at the corresponding offsets. *)

    agree_locals:
      forall ofs ty, 
      slot_bounded f (Local ofs ty) ->
      ls (S (Local ofs ty)) = index_val (FI_local ofs ty) fr;
    agree_outgoing:
      forall ofs ty, 
      slot_bounded f (Outgoing ofs ty) ->
      ls (S (Outgoing ofs ty)) = index_val (FI_arg ofs ty) fr;

    (** Incoming stack slots (on the Linear side) have
        the same values as the one loaded from the parent Mach frame 
        at the corresponding offsets. *)
    agree_incoming:
      forall ofs ty,
      slot_bounded f (Incoming ofs ty) ->
      get_slot parent ty (Int.signed (Int.repr (4 * ofs))) (ls (S (Incoming ofs ty)));

    (** The areas of the frame reserved for saving used callee-save
        registers always contain the values that those registers had
        on function entry. *)
    agree_saved_int:
      forall r,
      In r int_callee_save_regs ->
      index_int_callee_save r < b.(bound_int_callee_save) ->
      index_val (FI_saved_int (index_int_callee_save r)) fr = rs0 r;
    agree_saved_float:
      forall r,
      In r float_callee_save_regs ->
      index_float_callee_save r < b.(bound_float_callee_save) ->
      index_val (FI_saved_float (index_float_callee_save r)) fr = rs0 r
  }.

Hint Resolve agree_reg agree_unused_reg agree_size agree_high
             agree_locals agree_outgoing agree_incoming
             agree_saved_int agree_saved_float: stacking.

(** Values of registers and register lists. *)

Lemma agree_eval_reg:
  forall ls rs fr parent rs0 r,
  agree ls rs fr parent rs0 -> rs r = ls (R r).
Proof.
  intros. symmetry. eauto with stacking.
Qed.

Lemma agree_eval_regs:
  forall ls rs fr parent rs0 rl,
  agree ls rs fr parent rs0 -> rs##rl = LTL.reglist rl ls.
Proof.
  induction rl; simpl; intros.
  auto. apply (f_equal2 (@cons val)).
  eapply agree_eval_reg; eauto.
  auto.
Qed.

Hint Resolve agree_eval_reg agree_eval_regs: stacking.

(** Preservation of agreement under various assignments:
  of machine registers, of local slots, of outgoing slots. *)

Lemma agree_set_reg:
  forall ls rs fr parent rs0 r v,
  agree ls rs fr parent rs0 ->
  mreg_bounded f r ->
  agree (Locmap.set (R r) v ls) (Regmap.set r v rs) fr parent rs0.
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
  forall ls rs fr parent rs0 v ofs ty,
  agree ls rs fr parent rs0 ->
  slot_bounded f (Local ofs ty) ->
  exists fr',
    set_slot fr ty (offset_of_index fe (FI_local ofs ty)) v fr' /\
    agree (Locmap.set (S (Local ofs ty)) v ls) rs fr' parent rs0.
Proof.
  intros.
  generalize (set_slot_index fr _ v (index_local_valid _ _ H0) 
                (agree_high _ _ _ _ _ H)
                (agree_size _ _ _ _ _ H)).
  intros [fr' SET].
  exists fr'. split. auto. constructor; eauto with stacking.
  (* agree_reg *)
  intros. rewrite Locmap.gso. eauto with stacking. red; auto.
  (* agree_high *)
  inversion SET. simpl high. eauto with stacking.
  (* agree_size *)
  inversion SET. simpl low. eauto with stacking.
  (* agree_local *)
  intros. case (slot_eq (Local ofs ty) (Local ofs0 ty0)); intro.
  rewrite <- e. rewrite Locmap.gss. 
  replace (FI_local ofs0 ty0) with (FI_local ofs ty).
  symmetry. eapply slot_iss; eauto. congruence.
  assert (ofs <> ofs0 \/ ty <> ty0).
    case (zeq ofs ofs0); intro. compare ty ty0; intro.
    congruence. tauto.  tauto. 
  rewrite Locmap.gso. transitivity (index_val (FI_local ofs0 ty0) fr).
  eauto with stacking. symmetry. eapply slot_iso; eauto.
  simpl. auto.
  (* agree_outgoing *)
  intros. rewrite Locmap.gso. transitivity (index_val (FI_arg ofs0 ty0) fr).
  eauto with stacking. symmetry. eapply slot_iso; eauto.
  red; auto. red; auto.
  (* agree_incoming *)
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
  (* agree_saved_int *)
  intros. rewrite <- (agree_saved_int _ _ _ _ _ H r H1 H2). 
  eapply slot_iso; eauto with stacking. red; auto.
  (* agree_saved_float *)
  intros. rewrite <- (agree_saved_float _ _ _ _ _ H r H1 H2). 
  eapply slot_iso; eauto with stacking. red; auto.
Qed.

Lemma agree_set_outgoing:
  forall ls rs fr parent rs0 v ofs ty,
  agree ls rs fr parent rs0 ->
  slot_bounded f (Outgoing ofs ty) ->
  exists fr',
    set_slot fr ty (offset_of_index fe (FI_arg ofs ty)) v fr' /\
    agree (Locmap.set (S (Outgoing ofs ty)) v ls) rs fr' parent rs0.
Proof.
  intros. 
  generalize (set_slot_index fr _ v (index_arg_valid _ _ H0)
                (agree_high _ _ _ _ _ H)
                (agree_size _ _ _ _ _ H)).
  intros [fr' SET].
  exists fr'. split. exact SET. constructor; eauto with stacking.
  (* agree_reg *)
  intros. rewrite Locmap.gso. eauto with stacking. red; auto.
  (* agree_high *)
  inversion SET. simpl high. eauto with stacking.
  (* agree_size *)
  inversion SET. simpl low. eauto with stacking.
  (* agree_local *)
  intros. rewrite Locmap.gso. 
  transitivity (index_val (FI_local ofs0 ty0) fr).
  eauto with stacking. symmetry. eapply slot_iso; eauto.
  red; auto. red; auto.
  (* agree_outgoing *)
  intros. unfold Locmap.set. 
  case (Loc.eq (S (Outgoing ofs ty)) (S (Outgoing ofs0 ty0))); intro.
  (* same location *)
  replace ofs0 with ofs. replace ty0 with ty. 
  symmetry. eapply slot_iss; eauto.
  congruence. congruence.
  (* overlapping locations *)
  caseEq (Loc.overlap (S (Outgoing ofs ty)) (S (Outgoing ofs0 ty0))); intros.
  inversion SET. subst ofs1 ty1.
  unfold index_val, type_of_index, offset_of_index.
  set (ofs4 := 4 * ofs). set (ofs04 := 4 * ofs0). simpl.
  unfold ofs4, ofs04. symmetry. 
  case (zeq ofs ofs0); intro.
  subst ofs0. apply load_store_contents_mismatch.
  destruct ty; destruct ty0; simpl; congruence.
  generalize (Loc.overlap_not_diff _ _ H2). intro. simpl in H4.
  apply load_store_contents_overlap. 
  omega.
  rewrite size_mem_type. omega.
  rewrite size_mem_type. omega.
  (* different locations *)
  transitivity (index_val (FI_arg ofs0 ty0) fr).
  eauto with stacking.
  symmetry. eapply slot_iso; eauto. 
  simpl. eapply Loc.overlap_aux_false_1; eauto.
  (* agree_incoming *)
  intros. rewrite Locmap.gso. eauto with stacking. red. auto.
  (* saved ints *)
  intros. rewrite <- (agree_saved_int _ _ _ _ _ H r H1 H2). 
  eapply slot_iso; eauto with stacking. red; auto.
  (* saved floats *)
  intros. rewrite <- (agree_saved_float _ _ _ _ _ H r H1 H2). 
  eapply slot_iso; eauto with stacking. red; auto.
Qed.

Lemma agree_return_regs:
  forall ls rs fr parent rs0 ls' rs',
  agree ls rs fr parent rs0 ->
  (forall r,
    In (R r) temporaries \/ In (R r) destroyed_at_call ->
    rs' r = ls' (R r)) ->
  (forall r,
    In r int_callee_save_regs \/ In r float_callee_save_regs ->
    rs' r = rs r) ->
  agree (LTL.return_regs ls ls') rs' fr parent rs0.
Proof.
  intros. constructor; unfold LTL.return_regs; eauto with stacking.
  (* agree_reg *)
  intros. case (In_dec Loc.eq (R r) temporaries); intro.
  symmetry. apply H0. tauto.
  case (In_dec Loc.eq (R r) destroyed_at_call); intro.
  symmetry. apply H0. tauto.
  rewrite H1. eauto with stacking. 
  generalize (register_classification r); tauto.
  (* agree_unused_reg *)
  intros. rewrite H1. eauto with stacking.
  generalize H2; unfold mreg_bounded; case (mreg_type r); intro.
  left. apply index_int_callee_save_pos2. 
  generalize (bound_int_callee_save_pos f); intro. omega.
  right. apply index_float_callee_save_pos2. 
  generalize (bound_float_callee_save_pos f); intro. omega.
Qed. 

(** * Correctness of saving and restoring of callee-save registers *)

(** The following lemmas show the correctness of the register saving
  code generated by [save_callee_save]: after this code has executed,
  the register save areas of the current frame do contain the
  values of the callee-save registers used by the function. *)

Lemma save_int_callee_save_correct_rec:
  forall l k sp parent rs fr m,
  incl l int_callee_save_regs ->
  list_norepet l ->
  fr.(high) = 0 ->
  fr.(low) = -fe.(fe_size) ->
  exists fr',
    Machabstr.exec_instrs tge tf sp parent
      (List.fold_right (save_int_callee_save fe) k l) rs fr m
       E0 k rs fr' m
  /\ fr'.(high) = 0
  /\ fr'.(low) = -fe.(fe_size)
  /\ (forall r,
       In r l -> index_int_callee_save r < bound_int_callee_save b ->
       index_val (FI_saved_int (index_int_callee_save r)) fr' = rs r)
  /\ (forall idx,
       index_valid idx ->
       (forall r,
         In r l -> index_int_callee_save r < bound_int_callee_save b ->
         idx <> FI_saved_int (index_int_callee_save r)) ->
       index_val idx fr' = index_val idx fr).
Proof.
  induction l.
  (* base case *)
  intros. simpl fold_right. exists fr. 
  split. apply Machabstr.exec_refl. split. auto. split. auto. 
  split. intros. elim H3. auto.
  (* inductive case *)
  intros. simpl fold_right. 
  set (k1 := fold_right (save_int_callee_save fe) k l) in *.
  assert (R1: incl l int_callee_save_regs). eauto with coqlib.
  assert (R2: list_norepet l). inversion H0; auto.
  unfold save_int_callee_save. 
  case (zlt (index_int_callee_save a) (fe_num_int_callee_save fe));
  intro;
  unfold fe_num_int_callee_save, fe, make_env in z.
  (* a store takes place *)
  assert (IDX: index_valid (FI_saved_int (index_int_callee_save a))).
    apply index_saved_int_valid. eauto with coqlib. auto.
  generalize (set_slot_index _ _ (rs a) IDX H1 H2).
  intros [fr1 SET].
  assert (R3: high fr1 = 0). inversion SET. simpl high. auto.
  assert (R4: low fr1 = -fe_size fe).  inversion SET. simpl low. auto.
  generalize (IHl k sp parent rs fr1 m R1 R2 R3 R4).
  intros [fr' [A [B [C [D E]]]]].
  exists fr'. 
  split. eapply Machabstr.exec_trans. apply exec_Msetstack'; eauto with stacking.
  eexact A. traceEq.
  split. auto.
  split. auto.
  split. intros. elim H3; intros. subst r. 
    rewrite E. eapply slot_iss; eauto. auto. 
    intros. decEq. apply index_int_callee_save_inj; auto with coqlib.
    inversion H0. red; intro; subst r; contradiction.
    apply D; auto.
  intros. transitivity (index_val idx fr1).
    apply E; auto. 
    intros. apply H4; eauto with coqlib.
    eapply slot_iso; eauto. 
    destruct idx; simpl; auto. 
    generalize (H4 a (in_eq _ _) z). congruence.
  (* no store takes place *)
  generalize (IHl k sp parent rs fr m R1 R2 H1 H2).
  intros [fr' [A [B [C [D E]]]]].
  exists fr'. split. exact A. split. exact B. split. exact C.
  split. intros. elim H3; intros. subst r. omegaContradiction.
    apply D; auto. 
  intros. apply E; auto.
    intros. apply H4; auto with coqlib.
Qed. 

Lemma save_int_callee_save_correct:
  forall k sp parent rs fr m,
  fr.(high) = 0 ->
  fr.(low) = -fe.(fe_size) ->
  exists fr',
    Machabstr.exec_instrs tge tf sp parent
      (List.fold_right (save_int_callee_save fe) k int_callee_save_regs) rs fr m
       E0 k rs fr' m
  /\ fr'.(high) = 0
  /\ fr'.(low) = -fe.(fe_size)
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
  generalize (save_int_callee_save_correct_rec
                int_callee_save_regs k sp parent rs fr m
                (incl_refl _) int_callee_save_norepet H H0).
  intros [fr' [A [B [C [D E]]]]]. 
  exists fr'. 
  split. assumption. split. assumption. split. assumption.
  split. apply D. intros. apply E. auto. 
  intros. red; intros; subst idx. contradiction.
Qed.

Lemma save_float_callee_save_correct_rec:
  forall l k sp parent rs fr m,
  incl l float_callee_save_regs ->
  list_norepet l ->
  fr.(high) = 0 ->
  fr.(low) = -fe.(fe_size) ->
  exists fr',
    Machabstr.exec_instrs tge tf sp parent
      (List.fold_right (save_float_callee_save fe) k l) rs fr m
      E0 k rs fr' m
  /\ fr'.(high) = 0
  /\ fr'.(low) = -fe.(fe_size)
  /\ (forall r,
       In r l -> index_float_callee_save r < bound_float_callee_save b ->
       index_val (FI_saved_float (index_float_callee_save r)) fr' = rs r)
  /\ (forall idx,
       index_valid idx ->
       (forall r,
         In r l -> index_float_callee_save r < bound_float_callee_save b ->
         idx <> FI_saved_float (index_float_callee_save r)) ->
       index_val idx fr' = index_val idx fr).
Proof.
  induction l.
  (* base case *)
  intros. simpl fold_right. exists fr. 
  split. apply Machabstr.exec_refl. split. auto. split. auto.
  split. intros. elim H3. auto.
  (* inductive case *)
  intros. simpl fold_right. 
  set (k1 := fold_right (save_float_callee_save fe) k l) in *.
  assert (R1: incl l float_callee_save_regs). eauto with coqlib.
  assert (R2: list_norepet l). inversion H0; auto.
  unfold save_float_callee_save. 
  case (zlt (index_float_callee_save a) (fe_num_float_callee_save fe));
  intro;
  unfold fe_num_float_callee_save, fe, make_env in z.
  (* a store takes place *)
  assert (IDX: index_valid (FI_saved_float (index_float_callee_save a))).
    apply index_saved_float_valid. eauto with coqlib. auto.
  generalize (set_slot_index _ _ (rs a) IDX H1 H2).
  intros [fr1 SET].
  assert (R3: high fr1 = 0).  inversion SET. simpl high. auto.
  assert (R4: low fr1 = -fe_size fe).  inversion SET. simpl low. auto.
  generalize (IHl k sp parent rs fr1 m R1 R2 R3 R4).
  intros [fr' [A [B [C [D E]]]]].
  exists fr'. 
  split. eapply Machabstr.exec_trans. apply exec_Msetstack'; eauto with stacking.
  eexact A. traceEq.
  split. auto.
  split. auto.
  split. intros. elim H3; intros. subst r. 
    rewrite E. eapply slot_iss; eauto. auto. 
    intros. decEq. apply index_float_callee_save_inj; auto with coqlib.
    inversion H0. red; intro; subst r; contradiction.
    apply D; auto.
  intros. transitivity (index_val idx fr1).
    apply E; auto. 
    intros. apply H4; eauto with coqlib.
    eapply slot_iso; eauto. 
    destruct idx; simpl; auto. 
    generalize (H4 a (in_eq _ _) z). congruence.
  (* no store takes place *)
  generalize (IHl k sp parent rs fr m R1 R2 H1 H2).
  intros [fr' [A [B [C [D E]]]]].
  exists fr'. split. exact A. split. exact B. split. exact C.
  split. intros. elim H3; intros. subst r. omegaContradiction.
    apply D; auto. 
  intros. apply E; auto.
    intros. apply H4; auto with coqlib.
Qed. 

Lemma save_float_callee_save_correct:
  forall k sp parent rs fr m,
  fr.(high) = 0 ->
  fr.(low) = -fe.(fe_size) ->
  exists fr',
    Machabstr.exec_instrs tge tf sp parent
      (List.fold_right (save_float_callee_save fe) k float_callee_save_regs) rs fr m
       E0 k rs fr' m
  /\ fr'.(high) = 0
  /\ fr'.(low) = -fe.(fe_size)
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
  generalize (save_float_callee_save_correct_rec
                float_callee_save_regs k sp parent rs fr m
                (incl_refl _) float_callee_save_norepet H H0).
  intros [fr' [A [B [C [D E]]]]]. 
  exists fr'. split. assumption. split. assumption. split. assumption.
  split. apply D. intros. apply E. auto. 
  intros. red; intros; subst idx. contradiction.
Qed.

Lemma index_val_init_frame:
  forall idx,
  index_valid idx ->
  index_val idx (init_frame tf) = Vundef.
Proof.
  intros. unfold index_val, init_frame. simpl contents.
  apply load_contents_init. 
Qed.

Lemma save_callee_save_correct:
  forall sp parent k rs fr m ls,
  (forall r, rs r = ls (R r)) ->
  (forall ofs ty, 
     6 <= ofs -> 
     ofs + typesize ty <= size_arguments f.(fn_sig) ->
     get_slot parent ty (Int.signed (Int.repr (4 * ofs))) (ls (S (Outgoing ofs ty)))) ->
  high fr = 0 ->
  low fr = -fe.(fe_size) ->
  (forall idx, index_valid idx -> index_val idx fr = Vundef) ->
  exists fr',
    Machabstr.exec_instrs tge tf sp parent
      (save_callee_save fe k) rs fr m
      E0 k rs fr' m
  /\ agree (LTL.call_regs ls) rs fr' parent rs.
Proof.
  intros. unfold save_callee_save.
  generalize (save_int_callee_save_correct
     (fold_right (save_float_callee_save fe) k float_callee_save_regs)
     sp parent rs fr m H1 H2).
  intros [fr1 [A1 [B1 [C1 [D1 E1]]]]].
  generalize (save_float_callee_save_correct k sp parent rs fr1 m B1 C1).
  intros [fr2 [A2 [B2 [C2 [D2 E2]]]]].
  exists fr2.
  split. eapply Machabstr.exec_trans. eexact A1. eexact A2. traceEq.
  constructor; unfold LTL.call_regs; auto.
  (* agree_local *)
  intros. rewrite E2; auto with stacking. 
  rewrite E1; auto with stacking. 
  symmetry. auto with stacking.
  (* agree_outgoing *)
  intros. rewrite E2; auto with stacking. 
  rewrite E1; auto with stacking. 
  symmetry. auto with stacking. 
  (* agree_incoming *)
  intros. simpl in H4. apply H0. tauto. tauto.
  (* agree_saved_int *)
  intros. rewrite E2; auto with stacking. 
Qed.

(** The following lemmas show the correctness of the register reloading
  code generated by [reload_callee_save]: after this code has executed,
  all callee-save registers contain the same values they had at
  function entry. *)

Lemma restore_int_callee_save_correct_rec:
  forall sp parent k fr m rs0 l ls rs,
  incl l int_callee_save_regs ->
  list_norepet l -> 
  agree ls rs fr parent rs0 ->
  exists ls', exists rs',
    Machabstr.exec_instrs tge tf sp parent
      (List.fold_right (restore_int_callee_save fe) k l) rs fr m
      E0 k rs' fr m
  /\ (forall r, In r l -> rs' r = rs0 r)
  /\ (forall r, ~(In r l) -> rs' r = rs r)
  /\ agree ls' rs' fr parent rs0.
Proof.
  induction l.
  (* base case *)
  intros. simpl fold_right. exists ls. exists rs. 
  split. apply Machabstr.exec_refl. 
  split. intros. elim H2. 
  split. auto. auto.
  (* inductive case *)
  intros. simpl fold_right. 
  set (k1 := fold_right (restore_int_callee_save fe) k l) in *.
  assert (R0: In a int_callee_save_regs). apply H; auto with coqlib.
  assert (R1: incl l int_callee_save_regs). eauto with coqlib.
  assert (R2: list_norepet l). inversion H0; auto.
  unfold restore_int_callee_save.
  case (zlt (index_int_callee_save a) (fe_num_int_callee_save fe));
  intro;
  unfold fe_num_int_callee_save, fe, make_env in z.
  set (ls1 := Locmap.set (R a) (rs0 a) ls).
  set (rs1 := Regmap.set a (rs0 a) rs).
  assert (R3: agree ls1 rs1 fr parent rs0). 
    unfold ls1, rs1. apply agree_set_reg. auto. 
    red. rewrite int_callee_save_type. exact z.
    apply H. auto with coqlib.
  generalize (IHl ls1 rs1 R1 R2 R3). 
  intros [ls' [rs' [A [B [C D]]]]].
  exists ls'. exists rs'. 
  split. apply Machabstr.exec_trans with E0 k1 rs1 fr m E0. 
  unfold rs1; apply exec_Mgetstack'; eauto with stacking.
  apply get_slot_index; eauto with stacking.
  symmetry. eauto with stacking. 
  eauto with stacking. traceEq.
  split. intros. elim H2; intros.
  subst r. rewrite C. unfold rs1. apply Regmap.gss. inversion H0; auto.
  auto.
  split. intros. simpl in H2. rewrite C. unfold rs1. apply Regmap.gso.
  apply sym_not_eq; tauto. tauto.
  assumption.
  (* no load takes place *)
  generalize (IHl ls rs R1 R2 H1).  
  intros [ls' [rs' [A [B [C D]]]]].
  exists ls'; exists rs'. split. assumption.
  split. intros. elim H2; intros. 
  subst r. apply (agree_unused_reg _ _ _ _ _ D).
  unfold mreg_bounded. rewrite int_callee_save_type; auto. 
  auto.
  split. intros. simpl in H2. apply C. tauto.
  assumption.
Qed.

Lemma restore_int_callee_save_correct:
  forall sp parent k fr m rs0 ls rs,
  agree ls rs fr parent rs0 ->
  exists ls', exists rs',
    Machabstr.exec_instrs tge tf sp parent
      (List.fold_right (restore_int_callee_save fe) k int_callee_save_regs) rs fr m
      E0 k rs' fr m
  /\ (forall r, In r int_callee_save_regs -> rs' r = rs0 r)
  /\ (forall r, ~(In r int_callee_save_regs) -> rs' r = rs r)
  /\ agree ls' rs' fr parent rs0.
Proof.
  intros. apply restore_int_callee_save_correct_rec with ls. 
  apply incl_refl. apply int_callee_save_norepet. auto.
Qed.

Lemma restore_float_callee_save_correct_rec:
  forall sp parent k fr m rs0 l ls rs,
  incl l float_callee_save_regs ->
  list_norepet l -> 
  agree ls rs fr parent rs0 ->
  exists ls', exists rs',
    Machabstr.exec_instrs tge tf sp parent
      (List.fold_right (restore_float_callee_save fe) k l) rs fr m
      E0 k rs' fr m
  /\ (forall r, In r l -> rs' r = rs0 r)
  /\ (forall r, ~(In r l) -> rs' r = rs r)
  /\ agree ls' rs' fr parent rs0.
Proof.
  induction l.
  (* base case *)
  intros. simpl fold_right. exists ls. exists rs. 
  split. apply Machabstr.exec_refl. 
  split. intros. elim H2. 
  split. auto. auto.
  (* inductive case *)
  intros. simpl fold_right. 
  set (k1 := fold_right (restore_float_callee_save fe) k l) in *.
  assert (R0: In a float_callee_save_regs). apply H; auto with coqlib.
  assert (R1: incl l float_callee_save_regs). eauto with coqlib.
  assert (R2: list_norepet l). inversion H0; auto.
  unfold restore_float_callee_save.
  case (zlt (index_float_callee_save a) (fe_num_float_callee_save fe));
  intro;
  unfold fe_num_float_callee_save, fe, make_env in z.
  set (ls1 := Locmap.set (R a) (rs0 a) ls).
  set (rs1 := Regmap.set a (rs0 a) rs).
  assert (R3: agree ls1 rs1 fr parent rs0). 
    unfold ls1, rs1. apply agree_set_reg. auto. 
    red. rewrite float_callee_save_type. exact z.
    apply H. auto with coqlib.
  generalize (IHl ls1 rs1 R1 R2 R3). 
  intros [ls' [rs' [A [B [C D]]]]].
  exists ls'. exists rs'. 
  split. apply Machabstr.exec_trans with E0 k1 rs1 fr m E0. 
  unfold rs1; apply exec_Mgetstack'; eauto with stacking.
  apply get_slot_index; eauto with stacking.
  symmetry. eauto with stacking. 
  exact A. traceEq.
  split. intros. elim H2; intros.
  subst r. rewrite C. unfold rs1. apply Regmap.gss. inversion H0; auto.
  auto.
  split. intros. simpl in H2. rewrite C. unfold rs1. apply Regmap.gso.
  apply sym_not_eq; tauto. tauto.
  assumption.
  (* no load takes place *)
  generalize (IHl ls rs R1 R2 H1).  
  intros [ls' [rs' [A [B [C D]]]]].
  exists ls'; exists rs'. split. assumption.
  split. intros. elim H2; intros. 
  subst r. apply (agree_unused_reg _ _ _ _ _ D).
  unfold mreg_bounded. rewrite float_callee_save_type; auto. 
  auto.
  split. intros. simpl in H2. apply C. tauto.
  assumption.
Qed.

Lemma restore_float_callee_save_correct:
  forall sp parent k fr m rs0 ls rs,
  agree ls rs fr parent rs0 ->
  exists ls', exists rs',
    Machabstr.exec_instrs tge tf sp parent
      (List.fold_right (restore_float_callee_save fe) k float_callee_save_regs) rs fr m
      E0 k rs' fr m
  /\ (forall r, In r float_callee_save_regs -> rs' r = rs0 r)
  /\ (forall r, ~(In r float_callee_save_regs) -> rs' r = rs r)
  /\ agree ls' rs' fr parent rs0.
Proof.
  intros. apply restore_float_callee_save_correct_rec with ls. 
  apply incl_refl. apply float_callee_save_norepet. auto.
Qed.

Lemma restore_callee_save_correct:
  forall sp parent k fr m rs0 ls rs,
  agree ls rs fr parent rs0 ->
  exists rs',
    Machabstr.exec_instrs tge tf sp parent
      (restore_callee_save fe k) rs fr m
      E0 k rs' fr m
  /\ (forall r, 
        In r int_callee_save_regs \/ In r float_callee_save_regs -> 
        rs' r = rs0 r)
  /\ (forall r, 
        ~(In r int_callee_save_regs) ->
        ~(In r float_callee_save_regs) ->
        rs' r = rs r).
Proof.
  intros. unfold restore_callee_save.
  generalize (restore_int_callee_save_correct sp parent
               (fold_right (restore_float_callee_save fe) k float_callee_save_regs)
               fr m rs0 ls rs H).
  intros [ls1 [rs1 [A [B [C D]]]]].
  generalize (restore_float_callee_save_correct sp parent
                k fr m rs0 ls1 rs1 D).
  intros [ls2 [rs2 [P [Q [R S]]]]].
  exists rs2. split. eapply Machabstr.exec_trans. eexact A. eexact P. traceEq.
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
  forall (A: Set) (fn: A -> Mach.code -> Mach.code) lbl,
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
  intros. unfold save_callee_save.
  repeat rewrite find_label_fold_right. reflexivity.
  intros. unfold save_float_callee_save. 
  case (zlt (index_float_callee_save x) (fe_num_float_callee_save fe));
  intro; reflexivity.
  intros. unfold save_int_callee_save. 
  case (zlt (index_int_callee_save x) (fe_num_int_callee_save fe));
  intro; reflexivity.
Qed.

Remark find_label_restore_callee_save:
  forall fe lbl k,
  Mach.find_label lbl (restore_callee_save fe k) = Mach.find_label lbl k.
Proof.
  intros. unfold restore_callee_save.
  repeat rewrite find_label_fold_right. reflexivity.
  intros. unfold restore_float_callee_save. 
  case (zlt (index_float_callee_save x) (fe_num_float_callee_save fe));
  intro; reflexivity.
  intros. unfold restore_int_callee_save. 
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
  simpl. case (peq lbl l); intro. reflexivity. auto.
  rewrite find_label_restore_callee_save. auto.
Qed.

Lemma transl_find_label:
  forall f tf lbl c,
  transf_function f = Some tf ->
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
  intro c'. case (is_label lbl a); intros.
  injection H; intro; subst c'. red; intros; auto with coqlib. 
  apply incl_tl. auto.
Qed.

Lemma exec_instr_incl:
  forall f sp c1 ls1 m1 t c2 ls2 m2,
  Linear.exec_instr ge f sp c1 ls1 m1 t c2 ls2 m2 ->
  incl c1 f.(fn_code) ->
  incl c2 f.(fn_code).
Proof.
  induction 1; intros; eauto with coqlib.
  eapply find_label_incl; eauto.
  eapply find_label_incl; eauto.
Qed.

Lemma exec_instrs_incl:
  forall f sp c1 ls1 m1 t c2 ls2 m2,
  Linear.exec_instrs ge f sp c1 ls1 m1 t c2 ls2 m2 ->
  incl c1 f.(fn_code) ->
  incl c2 f.(fn_code).
Proof.
  induction 1; intros; auto.
  eapply exec_instr_incl; eauto.
Qed.

(** Preservation / translation of global symbols and functions. *)

Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma functions_translated:
  forall f v,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = Some tf.
Proof.
  intros. 
  generalize (Genv.find_funct_transf_partial transf_fundef TRANSF H).
  case (transf_fundef f).
  intros tf [A B]. exists tf. tauto.
  intros. tauto.
Qed.

Lemma function_ptr_translated:
  forall f v,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = Some tf.
Proof.
  intros. 
  generalize (Genv.find_funct_ptr_transf_partial transf_fundef TRANSF H).
  case (transf_fundef f).
  intros tf [A B]. exists tf. tauto.
  intros. tauto.
Qed.

Lemma sig_preserved:
  forall f tf, transf_fundef f = Some tf -> Mach.funsig tf = Linear.funsig f.
Proof.
  intros until tf; unfold transf_fundef, transf_partial_fundef.
  destruct f. unfold transf_function. 
  destruct (zlt (fn_stacksize f) 0). congruence.
  destruct (zlt (- Int.min_signed) (fe_size (make_env (function_bounds f)))). congruence.
  intros. inversion H; reflexivity. 
  intro. inversion H. reflexivity.
Qed.

(** Correctness of stack pointer relocation in operations and
  addressing modes. *)

Definition shift_sp (tf: Mach.function) (sp: val) :=
  Val.add sp (Vint (Int.repr (-tf.(fn_framesize)))).

Remark shift_offset_sp:
  forall f tf sp n v,
  transf_function f = Some tf ->
  offset_sp sp n = Some v ->
  offset_sp (shift_sp tf sp)
    (Int.add (Int.repr (fe_size (make_env (function_bounds f)))) n) = Some v.
Proof.
  intros. destruct sp; try discriminate.
  unfold offset_sp in *. 
  unfold shift_sp. 
  rewrite (unfold_transf_function _ _ H). unfold fn_framesize.
  unfold Val.add. rewrite <- Int.neg_repr. 
  set (p := Int.repr (fe_size (make_env (function_bounds f)))).
  inversion H0. decEq. decEq. 
  rewrite Int.add_assoc. decEq. 
  rewrite <- Int.add_assoc. 
  rewrite (Int.add_commut (Int.neg p) p). rewrite Int.add_neg_zero. 
  rewrite Int.add_commut. apply Int.add_zero.
Qed.

Lemma shift_eval_operation:
  forall f tf sp op args v,
  transf_function f = Some tf ->
  eval_operation ge sp op args = Some v ->
  eval_operation tge (shift_sp tf sp) 
                 (transl_op (make_env (function_bounds f)) op) args =
  Some v.
Proof.
  intros until v. destruct op; intros; auto.
  simpl in *. rewrite symbols_preserved. auto.
  destruct args; auto. unfold eval_operation in *. unfold transl_op.
  apply shift_offset_sp; auto.
Qed.

Lemma shift_eval_addressing:
  forall f tf sp addr args v,
  transf_function f = Some tf ->
  eval_addressing ge sp addr args = Some v ->
  eval_addressing tge (shift_sp tf sp) 
                 (transl_addr (make_env (function_bounds f)) addr) args =
  Some v.
Proof.
  intros. destruct addr; auto.
  simpl. rewrite symbols_preserved. auto.
  simpl. rewrite symbols_preserved. auto.
  unfold transl_addr, eval_addressing in *.
  destruct args; try discriminate.
  apply shift_offset_sp; auto.
Qed.

(** Preservation of the arguments to an external call. *)

Section EXTERNAL_ARGUMENTS.

Variable ls: locset.
Variable fr: frame.
Variable rs: regset.
Variable sg: signature.
Hypothesis AG1: forall r, rs r = ls (R r).
Hypothesis AG2: forall (ofs : Z) (ty : typ),
      6 <= ofs ->
      ofs + typesize ty <= size_arguments sg ->
      get_slot fr ty (Int.signed (Int.repr (4 * ofs)))
                     (ls (S (Outgoing ofs ty))).

Lemma transl_external_arguments_rec:
  forall locs,
  (forall l, In l locs -> loc_argument_acceptable l) ->
  (forall ofs ty, In (S (Outgoing ofs ty)) locs ->
                  ofs + typesize ty <= size_arguments sg) ->
  extcall_args rs fr locs ls##locs.
Proof.
  induction locs; simpl; intros.
  constructor.
  constructor. 
  assert (loc_argument_acceptable a). apply H; auto.
  destruct a; red in H1.
  rewrite <- AG1. constructor. 
  destruct s; try contradiction.
  constructor. apply AG2. omega. apply H0. auto.
  apply IHlocs; auto.
Qed.

Lemma transl_external_arguments:
  extcall_arguments rs fr sg (ls ## (loc_arguments sg)).
Proof.
  unfold extcall_arguments. 
  apply transl_external_arguments_rec. 
  exact (Conventions.loc_arguments_acceptable sg).
  exact (Conventions.loc_arguments_bounded sg).
Qed.

End EXTERNAL_ARGUMENTS.

(** The proof of semantic preservation relies on simulation diagrams
  of the following form:
<<
        c, ls, m ------------------- T(c), rs, fr, m
            |                             |
            |                             |
            v                             v
       c', ls', m' ---------------- T(c'), rs', fr', m'
>>
  The left vertical arrow represents a transition in the
  original Linear code.  The top horizontal bar captures three preconditions:
- Agreement between [ls] on the Linear side and [rs], [fr], [rs0]
  on the Mach side.
- Inclusion between [c] and the code of the function [f] being
  translated.
- Well-typedness of [f].

  In conclusion, we want to prove the existence of [rs'], [fr'], [m']
  that satisfies the right arrow (zero, one or several transitions in
  the generated Mach code) and the postcondition (agreement between
  [ls'] and [rs'], [fr'], [rs0]).

  As usual, we capture these diagrams as predicates parameterized
  by the transition in the original Linear code. *)

Definition exec_instr_prop
      (f: function) (sp: val)
      (c: code) (ls: locset) (m: mem) (t: trace)
      (c': code) (ls': locset) (m': mem) :=
  forall tf rs fr parent rs0
     (TRANSL: transf_function f = Some tf)
     (WTF: wt_function f)
     (AG: agree f ls rs fr parent rs0)
     (INCL: incl c f.(fn_code)),
  exists rs', exists fr',
    Machabstr.exec_instrs tge tf (shift_sp tf sp) parent
       (transl_code (make_env (function_bounds f)) c) rs fr m
     t (transl_code (make_env (function_bounds f)) c') rs' fr' m'
  /\ agree f ls' rs' fr' parent rs0.

(** The simulation property for function calls has different preconditions
  (a slightly weaker notion of agreement between [ls] and the initial
  register values [rs] and caller's frame [parent]) and different
  postconditions (preservation of callee-save registers). *)

Definition exec_function_prop
      (f: fundef) 
      (ls: locset) (m: mem) (t: trace)
      (ls': locset) (m': mem) :=
  forall tf rs parent
     (TRANSL: transf_fundef f = Some tf)
     (WTF: wt_fundef f)
     (AG1: forall r, rs r = ls (R r))
     (AG2: forall ofs ty, 
             6 <= ofs -> 
             ofs + typesize ty <= size_arguments (funsig f) ->
             get_slot parent ty (Int.signed (Int.repr (4 * ofs))) (ls (S (Outgoing ofs ty)))),
  exists rs',
    Machabstr.exec_function tge tf parent rs m t rs' m'
 /\ (forall r,
        In (R r) temporaries \/ In (R r) destroyed_at_call ->
        rs' r = ls' (R r))
 /\ (forall r,
        In r int_callee_save_regs \/ In r float_callee_save_regs ->
        rs' r = rs r).

Hypothesis wt_prog: wt_program prog.

Lemma transf_function_correct:
  forall f ls m t ls' m',
  Linear.exec_function ge f ls m t ls' m' ->
  exec_function_prop f ls m t ls' m'.
Proof.
  assert (RED: forall f i c,
          transl_code (make_env (function_bounds f)) (i :: c) = 
          transl_instr (make_env (function_bounds f)) i
                       (transl_code (make_env (function_bounds f)) c)).
    intros. reflexivity.
  apply (Linear.exec_function_ind3 ge exec_instr_prop
            exec_instr_prop exec_function_prop);
  intros; red; intros; 
  try rewrite RED; 
  try (generalize (WTF _ (INCL _ (in_eq _ _))); intro WTI);
  unfold transl_instr.

  (* Lgetstack *)
  inversion WTI. exists (rs0#r <- (rs (S sl))); exists fr.
  split. destruct sl. 
  (* Lgetstack, local *)
  apply exec_Mgetstack'; auto.
  apply get_slot_index. apply index_local_valid. auto. 
  eapply agree_size; eauto. reflexivity. 
  eapply agree_locals; eauto.
  (* Lgetstack, incoming *)
  apply Machabstr.exec_one; constructor.
  unfold offset_of_index. eapply agree_incoming; eauto.
  (* Lgetstack, outgoing *)
  apply exec_Mgetstack'; auto.
  apply get_slot_index. apply index_arg_valid. auto. 
  eapply agree_size; eauto. reflexivity. 
  eapply agree_outgoing; eauto.
  (* Lgetstack, common *)
  apply agree_set_reg; auto.

  (* Lsetstack *)
  inversion WTI. destruct sl.
  (* Lsetstack, local *)
  generalize (agree_set_local _ _ _ _ _ _ (rs0 r) _ _ AG H3).
  intros [fr' [SET AG']].
  exists rs0; exists fr'. split.
  apply exec_Msetstack'; auto.
  replace (rs (R r)) with (rs0 r). auto.
  symmetry. eapply agree_reg; eauto.
  (* Lsetstack, incoming *)
  contradiction.
  (* Lsetstack, outgoing *)
  generalize (agree_set_outgoing _ _ _ _ _ _ (rs0 r) _ _ AG H3).
  intros [fr' [SET AG']].
  exists rs0; exists fr'. split.
  apply exec_Msetstack'; auto.
  replace (rs (R r)) with (rs0 r). auto.
  symmetry. eapply agree_reg; eauto.

  (* Lop *)
  assert (mreg_bounded f res). inversion WTI; auto.
  exists (rs0#res <- v); exists fr. split.
  apply Machabstr.exec_one. constructor. 
  apply shift_eval_operation. auto. 
  change mreg with RegEq.t.
  rewrite (agree_eval_regs _ _ _ _ _ _ args AG). auto.
  apply agree_set_reg; auto.

  (* Lload *)
  inversion WTI. exists (rs0#dst <- v); exists fr. split.
  apply Machabstr.exec_one; econstructor.
  apply shift_eval_addressing; auto. 
  change mreg with RegEq.t.
  rewrite (agree_eval_regs _ _ _ _ _ _ args AG). eauto.
  auto.
  apply agree_set_reg; auto.

  (* Lstore *)
  exists rs0; exists fr. split.
  apply Machabstr.exec_one; econstructor.
  apply shift_eval_addressing; auto. 
  change mreg with RegEq.t.
  rewrite (agree_eval_regs _ _ _ _ _ _ args AG). eauto.
  rewrite (agree_eval_reg _ _ _ _ _ _ src AG). auto.
  auto.

  (* Lcall *)
  inversion WTI.
  assert (WTF': wt_fundef f').
    destruct ros; simpl in H.
    apply (Genv.find_funct_prop wt_fundef wt_prog H).
    destruct (Genv.find_symbol ge i); try discriminate.
    apply (Genv.find_funct_ptr_prop wt_fundef wt_prog H).
  assert (TR: exists tf', Mach.find_function tge ros rs0 = Some tf'
                       /\ transf_fundef f' = Some tf').
    destruct ros; simpl in H; simpl.
    eapply functions_translated. 
    rewrite (agree_eval_reg _ _ _ _ _ _ m0 AG). auto. 
    rewrite symbols_preserved. 
    destruct (Genv.find_symbol ge i); try discriminate.
    apply function_ptr_translated; auto.
  elim TR;  intros tf' [FIND' TRANSL']; clear TR.
  assert (AG1: forall r, rs0 r = rs (R r)).
    intro. symmetry. eapply agree_reg; eauto.
  assert (AG2: forall ofs ty, 
             6 <= ofs -> 
             ofs + typesize ty <= size_arguments (funsig f') ->
             get_slot fr ty (Int.signed (Int.repr (4 * ofs))) (rs (S (Outgoing ofs ty)))).
    intros. 
    assert (slot_bounded f (Outgoing ofs ty)).
      red. rewrite <- H0 in H8. omega.
    change (4 * ofs) with (offset_of_index (make_env (function_bounds f)) (FI_arg ofs ty)).
    rewrite (offset_of_index_no_overflow f tf); auto. 
    apply get_slot_index. apply index_arg_valid. auto. 
    eapply agree_size; eauto. reflexivity. 
    eapply agree_outgoing; eauto. 
  generalize (H2 tf' rs0 fr TRANSL' WTF' AG1 AG2).
  intros [rs2 [EXF [REGS1 REGS2]]].
  exists rs2; exists fr. split.
  apply Machabstr.exec_one; apply Machabstr.exec_Mcall with tf'; auto.
  apply agree_return_regs with rs0; auto.

  (* Lalloc *)
  exists (rs0#loc_alloc_result <- (Vptr blk Int.zero)); exists fr. split.
  apply Machabstr.exec_one; eapply Machabstr.exec_Malloc; eauto.
  rewrite (agree_eval_reg _ _ _ _ _ _ loc_alloc_argument AG). auto.
  apply agree_set_reg; auto.
  red. simpl. generalize (max_over_regs_of_funct_pos f int_callee_save). omega.

  (* Llabel *)
  exists rs0; exists fr. split.
  apply Machabstr.exec_one; apply Machabstr.exec_Mlabel.
  auto.

  (* Lgoto *)
  exists rs0; exists fr. split.
  apply Machabstr.exec_one; apply Machabstr.exec_Mgoto.
  apply transl_find_label; auto.
  auto.

  (* Lcond, true *)
  exists rs0; exists fr. split.
  apply Machabstr.exec_one; apply Machabstr.exec_Mcond_true.
  rewrite <- (agree_eval_regs _ _ _ _ _ _ args AG) in H; auto.
  apply transl_find_label; auto.
  auto.

  (* Lcond, false *)
  exists rs0; exists fr. split.
  apply Machabstr.exec_one; apply Machabstr.exec_Mcond_false.
  rewrite <- (agree_eval_regs _ _ _ _ _ _ args AG) in H; auto.
  auto.

  (* refl *)
  exists rs0; exists fr. split. apply Machabstr.exec_refl. auto.

  (* one *)
  apply H0; auto.

  (* trans *)
  generalize (H0 tf rs fr parent rs0 TRANSL WTF AG INCL).
  intros [rs' [fr' [A B]]].
  assert (INCL': incl b2 (fn_code f)). eapply exec_instrs_incl; eauto.
  generalize (H2 tf rs' fr' parent rs0 TRANSL WTF B INCL').
  intros [rs'' [fr'' [C D]]].
  exists rs''; exists fr''. split.
  eapply Machabstr.exec_trans. eexact A. eexact C. auto.
  auto.

  (* function *)
  generalize TRANSL; clear TRANSL. 
  unfold transf_fundef, transf_partial_fundef.
  caseEq (transf_function f); try congruence.
  intros tfn TRANSL EQ. inversion EQ; clear EQ; subst tf.
  inversion WTF as [|f' WTFN]. subst f'.
  assert (X: forall link ra,
   exists rs' : regset,
   Machabstr.exec_function_body tge tfn parent link ra rs0 m t rs' (free m2 stk) /\
   (forall r : mreg,
    In (R r) temporaries \/ In (R r) destroyed_at_call -> rs' r = rs2 (R r)) /\
   (forall r : mreg,
    In r int_callee_save_regs \/ In r float_callee_save_regs -> rs' r = rs0 r)).
  intros.
  set (sp := Vptr stk Int.zero) in *.
  set (tsp := shift_sp tfn sp).
  set (fe := make_env (function_bounds f)).
  assert (low (init_frame tfn) = -fe.(fe_size)).
    simpl low. rewrite (unfold_transf_function _ _ TRANSL).
    reflexivity.
  assert (exists fr1, set_slot (init_frame tfn) Tint 0 link fr1).
    apply set_slot_ok. reflexivity. omega. rewrite H2. generalize (size_pos f). 
    unfold fe. simpl typesize. omega.
  elim H3; intros fr1 SET1; clear H3.
  assert (high fr1 = 0).
    inversion SET1. reflexivity.
  assert (low fr1 = -fe.(fe_size)).
    inversion SET1. rewrite <- H2. reflexivity.
  assert (exists fr2, set_slot fr1 Tint 12 ra fr2).
    apply set_slot_ok. auto. omega. rewrite H4. generalize (size_pos f). 
    unfold fe. simpl typesize. omega.
  elim H5; intros fr2 SET2; clear H5.
  assert (high fr2 = 0).
    inversion SET2. simpl. auto.
  assert (low fr2 = -fe.(fe_size)).
    inversion SET2. rewrite <- H4. reflexivity.
  assert (UNDEF: forall idx, index_valid f idx -> index_val f idx fr2 = Vundef).
    intros. 
    assert (get_slot fr2 (type_of_index idx) (offset_of_index fe idx) Vundef).
    generalize (offset_of_index_valid _ _ H7). fold fe. intros [XX YY].
    eapply slot_gso; eauto. 
    eapply slot_gso; eauto.
    apply slot_gi. omega. omega. 
    simpl typesize. omega. simpl typesize. omega. 
    inversion H8. symmetry. exact H11.
  generalize (save_callee_save_correct f tfn TRANSL
                tsp parent
                (transl_code (make_env (function_bounds f)) f.(fn_code))
                rs0 fr2 m1 rs AG1 AG2 H5 H6 UNDEF).
  intros [fr [EXP AG]].
  generalize (H1 tfn rs0 fr parent rs0 TRANSL WTFN AG (incl_refl _)).
  intros [rs' [fr' [EXB AG']]].
  generalize (restore_callee_save_correct f tfn TRANSL tsp parent
                (Mreturn :: transl_code (make_env (function_bounds f)) b)
                fr' m2 rs0 rs2 rs' AG').
  intros [rs'' [EXX [REGS1 REGS2]]].
  exists rs''. split. eapply Machabstr.exec_funct_body.
    rewrite (unfold_transf_function f tfn TRANSL); eexact H. 
    eexact SET1. eexact SET2. 
    replace (Mach.fn_code tfn) with
            (transl_body f (make_env (function_bounds f))).    
    replace (Vptr stk (Int.repr (- fn_framesize tfn))) with tsp.
    eapply Machabstr.exec_trans. eexact EXP. 
    eapply Machabstr.exec_trans. eexact EXB. eexact EXX. 
    reflexivity. traceEq.
    unfold tsp, shift_sp, sp. unfold Val.add. 
    rewrite Int.add_commut. rewrite Int.add_zero. auto.
    rewrite (unfold_transf_function f tfn TRANSL). simpl. auto.
  split. intros. rewrite REGS2. symmetry; eapply agree_reg; eauto.
  apply int_callee_save_not_destroyed; auto.
  apply float_callee_save_not_destroyed; auto.
  auto.
  generalize (X Vzero Vzero). intros [rs' [EX [REGS1 REGS2]]].
  exists rs'. split.
  constructor. intros.
  generalize (X link ra). intros [rs'' [EX' [REGS1' REGS2']]].
  assert (rs' = rs'').   
    apply (@Regmap.exten val). intro r. 
    elim (register_classification r); intro.
    rewrite REGS1'. apply REGS1. auto. auto.
    rewrite REGS2'. apply REGS2. auto. auto.
  rewrite H4. auto.
  split; auto.

  (* external function *)
  simpl in TRANSL. inversion TRANSL; subst tf.
  inversion WTF. subst ef0. set (sg := ef_sig ef) in *.
  exists (rs#(loc_result sg) <- res). 
  split. econstructor. eauto. 
  fold sg. rewrite H0. apply transl_external_arguments; assumption.
  reflexivity.
  split; intros. rewrite H1. 
  unfold Regmap.set. case (RegEq.eq r (loc_result sg)); intro.
  rewrite e. rewrite Locmap.gss; auto. rewrite Locmap.gso; auto.
  red; auto.
  apply Regmap.gso. red; intro; subst r.
  elim (Conventions.loc_result_not_callee_save _ H2).
Qed.

End PRESERVATION.

Theorem transl_program_correct:
  forall (p: Linear.program) (tp: Mach.program) (t: trace) (r: val),
  wt_program p ->
  transf_program p = Some tp ->
  Linear.exec_program p t r ->
  Machabstr.exec_program tp t r.
Proof.
  intros p tp t r WTP TRANSF
         [fptr [f [ls' [m [FINDSYMB [FINDFUNC [SIG [EXEC RES]]]]]]]].
  assert (WTF: wt_fundef f).
    apply (Genv.find_funct_ptr_prop wt_fundef WTP FINDFUNC).
  set (ls := Locmap.init Vundef) in *.
  set (rs := Regmap.init Vundef).
  set (fr := empty_frame).
  assert (AG1: forall r, rs r = ls (R r)).
    intros; reflexivity.
  assert (AG2: forall ofs ty, 
             6 <= ofs -> 
             ofs + typesize ty <= size_arguments (funsig f) ->
             get_slot fr ty (Int.signed (Int.repr (4 * ofs))) (ls (S (Outgoing ofs ty)))).
    rewrite SIG. unfold size_arguments, sig_args, size_arguments_rec.
    intros. generalize (typesize_pos ty). 
    intro. omegaContradiction.
  generalize (function_ptr_translated p tp TRANSF f _ FINDFUNC).
  intros [tf [TFIND TRANSL]]. 
  generalize (transf_function_correct p tp TRANSF WTP _ _ _ _ _ _ EXEC
                tf rs fr TRANSL WTF AG1 AG2).
  intros [rs' [A [B C]]].
  red. exists fptr; exists tf; exists rs'; exists m.
  split. rewrite (symbols_preserved p tp TRANSF). 
  rewrite (transform_partial_program_main transf_fundef p TRANSF).
  assumption.
  split. assumption.
  split. replace (Genv.init_mem tp) with (Genv.init_mem p).
  exact A. symmetry. apply Genv.init_mem_transf_partial with transf_fundef. 
  exact TRANSF.
  rewrite <- RES. replace R3 with (loc_result (funsig f)).
  apply B. right. apply loc_result_acceptable. 
  rewrite SIG; reflexivity.
Qed.
