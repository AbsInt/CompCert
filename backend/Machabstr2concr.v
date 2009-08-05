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

(** Simulation between the two semantics for the Mach language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Machtyping.
Require Import Machabstr.
Require Import Machconcr.
Require Import Asmgenretaddr.

(** Two semantics were defined for the Mach intermediate language:
- The concrete semantics (file [Mach]), where the whole activation
  record resides in memory and the [Mgetstack], [Msetstack] and
  [Mgetparent] are interpreted as [sp]-relative memory accesses.
- The abstract semantics (file [Machabstr]), where the activation
  record is split in two parts: the Cminor stack data, resident in
  memory, and the frame information, residing not in memory but
  in additional evaluation environments.

  In this file, we show a simulation result between these
  semantics: if a program executes with some behaviour [beh] in the
  abstract semantics, it also executes with the same behaviour in
  the concrete semantics.  This result bridges the correctness proof
  in file [Stackingproof] (which uses the abstract Mach semantics
  as output) and that in file [Asmgenproof] (which uses the concrete
  Mach semantics as input).
*)

Remark size_type_chunk:
  forall ty, size_chunk (chunk_of_type ty) = AST.typesize ty.
Proof.
  destruct ty; reflexivity.
Qed.

(** * Agreement between frames and memory-resident activation records *)

(** ** Agreement for one frame *)

Section FRAME_MATCH.

Variable f: function.
Hypothesis wt_f: wt_function f.

(** The core idea of the simulation proof is that for all active
  functions, the memory-allocated activation record, in the concrete 
  semantics, contains the same data as the Cminor stack block
  (at positive offsets) and the frame of the function (at negative
  offsets) in the abstract semantics

  This intuition (activation record = Cminor stack data + frame)
  is formalized by the following predicate [frame_match fr sp base mm ms].
  [fr] is a frame and [mm] the current memory state in the abstract
  semantics. [ms] is the current memory state in the concrete semantics.
  The stack pointer is [Vptr sp base] in both semantics. *)

Inductive frame_match (fr: frame)
                      (sp: block) (base: int) 
                      (mm ms: mem) : Prop :=
  frame_match_intro:
    valid_block ms sp ->
    low_bound mm sp = 0 ->
    low_bound ms sp = -f.(fn_framesize) ->
    high_bound ms sp >= 0 ->
    base = Int.repr (-f.(fn_framesize)) ->
    (forall ty ofs,
       -f.(fn_framesize) <= ofs -> ofs + AST.typesize ty <= 0 -> (4 | ofs) ->
       load (chunk_of_type ty) ms sp ofs = Some(fr ty ofs)) ->
    frame_match fr sp base mm ms.

(** The following two innocuous-looking lemmas are the key results
  showing that [sp]-relative memory accesses in the concrete
  semantics behave like the direct frame accesses in the abstract
  semantics.  First, a value [v] that has type [ty] is preserved
  when stored in memory with chunk [chunk_of_type ty], then read
  back with the same chunk.  The typing hypothesis is crucial here:
  for instance, a float value reads back as [Vundef] when stored
  and load with chunk [Mint32]. *)

Lemma load_result_ty:
  forall v ty,
  Val.has_type v ty -> Val.load_result (chunk_of_type ty) v = v.
Proof.
  destruct v; destruct ty; simpl; contradiction || reflexivity.
Qed.

(** Second, computations of [sp]-relative offsets using machine
  arithmetic (as done in the concrete semantics) never overflows
  and behaves identically to the offset computations using exact
  arithmetic (as done in the abstract semantics). *)

Lemma int_add_no_overflow:
  forall x y,
  Int.min_signed <= Int.signed x + Int.signed y <= Int.max_signed ->
  Int.signed (Int.add x y) = Int.signed x + Int.signed y.
Proof.
  intros. rewrite Int.add_signed. rewrite Int.signed_repr. auto. auto.
Qed.

(** Given matching frames and activation records, loading from the
  activation record (in the concrete semantics) behaves identically
  to reading the corresponding slot from the frame
  (in the abstract semantics).  *)

Lemma frame_match_load_stack:
  forall fr sp base mm ms ty ofs,
  frame_match fr sp base mm ms ->
  0 <= Int.signed ofs /\ Int.signed ofs + AST.typesize ty <= f.(fn_framesize) ->
  (4 | Int.signed ofs) ->
  load_stack ms (Vptr sp base) ty ofs = 
  Some (fr ty (Int.signed ofs - f.(fn_framesize))).
Proof.
  intros. inv H. inv wt_f.
  unfold load_stack, Val.add, loadv.
  replace (Int.signed (Int.add (Int.repr (- fn_framesize f)) ofs))
     with (Int.signed ofs - fn_framesize f).
  apply H7. omega. omega.
  apply Zdivide_minus_l; auto. 
  assert (Int.signed (Int.repr (-fn_framesize f)) = -fn_framesize f).
    apply Int.signed_repr.
    assert (0 <= Int.max_signed). compute; congruence. omega.
  rewrite int_add_no_overflow. rewrite H. omega.
  rewrite H. split. omega.
  apply Zle_trans with 0. generalize (AST.typesize_pos ty). omega. 
  compute; congruence.
Qed.

Lemma frame_match_get_slot:
  forall fr sp base mm ms ty ofs v,
  frame_match fr sp base mm ms ->
  get_slot f fr ty (Int.signed ofs) v ->
  load_stack ms (Vptr sp base) ty ofs = Some v.
Proof.
  intros. inversion H. inv H0. inv H7. eapply frame_match_load_stack; eauto.
Qed.

(** Assigning a value to a frame slot (in the abstract semantics)
  corresponds to storing this value in the activation record
  (in the concrete semantics).  Moreover, agreement between frames
  and activation records is preserved. *)

Lemma frame_match_store_stack:
  forall fr sp base mm ms ty ofs v,
  frame_match fr sp base mm ms ->
  0 <= Int.signed ofs /\ Int.signed ofs + AST.typesize ty <= f.(fn_framesize) ->
  (4 | Int.signed ofs) ->
  Val.has_type v ty ->
  Mem.extends mm ms ->
  exists ms',
    store_stack ms (Vptr sp base) ty ofs v = Some ms' /\
    frame_match (update ty (Int.signed ofs - f.(fn_framesize)) v fr) sp base mm ms' /\
    Mem.extends mm ms'.
Proof.
  intros. inv H. inv wt_f.
  unfold store_stack, Val.add, storev.
  assert (Int.signed (Int.add (Int.repr (- fn_framesize f)) ofs) =
          Int.signed ofs - fn_framesize f).
  assert (Int.signed (Int.repr (-fn_framesize f)) = -fn_framesize f).
    apply Int.signed_repr. 
    assert (0 <= Int.max_signed). compute; congruence. omega.
  rewrite int_add_no_overflow. rewrite H. omega.
  rewrite H. split. omega.
  apply Zle_trans with 0. generalize (AST.typesize_pos ty). omega. 
  compute; congruence.
  rewrite H.
  assert (exists ms', store (chunk_of_type ty) ms sp (Int.signed ofs - fn_framesize f) v = Some ms').
    apply valid_access_store. 
    constructor. auto. omega.
    rewrite size_type_chunk. omega.
    replace (align_chunk (chunk_of_type ty)) with 4.
    apply Zdivide_minus_l; auto.
    destruct ty; auto.
  destruct H8 as [ms' STORE]. 
  generalize (low_bound_store _ _ _ _ _ _ STORE sp). intro LB.
  generalize (high_bound_store _ _ _ _ _ _ STORE sp). intro HB.
  exists ms'. 
  split. exact STORE.
  (* frame match *)
  split. constructor; try congruence.
    eauto with mem. intros. unfold update.
    destruct (zeq (Int.signed ofs - fn_framesize f) ofs0). subst ofs0.
    destruct (typ_eq ty ty0). subst ty0.
    (* same *)
    transitivity (Some (Val.load_result (chunk_of_type ty) v)).
    eapply load_store_same; eauto.
    decEq. apply load_result_ty; auto.
    (* mismatch *)
    eapply load_store_mismatch'; eauto with mem.
    destruct ty; destruct ty0; simpl; congruence.
    destruct (zle (ofs0 + AST.typesize ty0) (Int.signed ofs - fn_framesize f)).
    (* disjoint *)
    rewrite <- H9; auto. eapply load_store_other; eauto.
    right; left. rewrite size_type_chunk; auto.
    destruct (zle (Int.signed ofs - fn_framesize f + AST.typesize ty)).
    rewrite <- H9; auto. eapply load_store_other; eauto.
    right; right. rewrite size_type_chunk; auto.
    (* overlap *)
    eapply load_store_overlap'; eauto with mem.
    rewrite size_type_chunk; auto. 
    rewrite size_type_chunk; auto.
  (* extends *)
  eapply store_outside_extends; eauto.
  left. rewrite size_type_chunk. omega.
Qed.

Lemma frame_match_set_slot:
  forall fr sp base mm ms ty ofs v fr',
  frame_match fr sp base mm ms ->
  set_slot f fr ty (Int.signed ofs) v fr' ->
  Val.has_type v ty ->
  Mem.extends mm ms ->
  exists ms',
    store_stack ms (Vptr sp base) ty ofs v = Some ms' /\
    frame_match fr' sp base mm ms' /\
    Mem.extends mm ms'.
Proof.
  intros. inv H0. inv H3. eapply frame_match_store_stack; eauto. 
Qed.

(** Agreement is preserved by stores within blocks other than the
  one pointed to by [sp]. *)

Lemma frame_match_store_other:
  forall fr sp base mm ms chunk b ofs v ms',
  frame_match fr sp base mm ms ->
  store chunk ms b ofs v = Some ms' ->
  sp <> b ->
  frame_match fr sp base mm ms'.
Proof.
  intros. inv H. 
  generalize (low_bound_store _ _ _ _ _ _ H0 sp). intro LB.
  generalize (high_bound_store _ _ _ _ _ _ H0 sp). intro HB.
  apply frame_match_intro; auto.
  eauto with mem. 
  congruence.
  congruence.
  intros. rewrite <- H7; auto. 
  eapply load_store_other; eauto.
Qed.

(** Agreement is preserved by parallel stores in the Machabstr
  and the Machconcr semantics. *)

Lemma frame_match_store:
  forall fr sp base mm ms chunk b ofs v mm' ms',
  frame_match fr sp base mm ms ->
  store chunk mm b ofs v = Some mm' ->
  store chunk ms b ofs v = Some ms' ->
  frame_match fr sp base mm' ms'.
Proof.
  intros. inv H.  
  generalize (low_bound_store _ _ _ _ _ _ H0 sp). intro LBm.
  generalize (low_bound_store _ _ _ _ _ _ H1 sp). intro LBs.
  generalize (high_bound_store _ _ _ _ _ _ H0 sp). intro HBm.
  generalize (high_bound_store _ _ _ _ _ _ H1 sp). intro HBs.
  apply frame_match_intro; auto.
  eauto with mem.
  congruence. congruence. congruence.
  intros. rewrite <- H7; auto. eapply load_store_other; eauto.
  destruct (zeq sp b). subst b. right. 
  rewrite size_type_chunk. 
  assert (valid_access mm chunk sp ofs) by eauto with mem.
  inv H9. left. omega.
  auto.
Qed.

(** Memory allocation of the Cminor stack data block (in the abstract
  semantics) and of the whole activation record (in the concrete
  semantics) return memory states that agree according to [frame_match].
  Moreover, [frame_match] relations over already allocated blocks
  remain true. *)

Lemma frame_match_new:
  forall mm ms mm' ms' sp sp',
  mm.(nextblock) = ms.(nextblock) ->
  alloc mm 0 f.(fn_stacksize) = (mm', sp) ->
  alloc ms (- f.(fn_framesize)) f.(fn_stacksize) = (ms', sp') ->
  sp = sp' /\
  frame_match empty_frame sp (Int.repr (-f.(fn_framesize))) mm' ms'.
Proof.
  intros. 
  assert (sp = sp').
    exploit alloc_result. eexact H0. exploit alloc_result. eexact H1. 
    congruence. 
  subst sp'. split. auto.
  generalize (low_bound_alloc_same _ _ _ _ _ H0). intro LBm.
  generalize (low_bound_alloc_same _ _ _ _ _ H1). intro LBs.
  generalize (high_bound_alloc_same _ _ _ _ _ H0). intro HBm.
  generalize (high_bound_alloc_same _ _ _ _ _ H1). intro HBs.
  inv wt_f.
  constructor; simpl; eauto with mem.
  rewrite HBs. auto.
  intros.
  eapply load_alloc_same'; eauto.  
  rewrite size_type_chunk. omega.
  replace (align_chunk (chunk_of_type ty)) with 4; auto. destruct ty; auto.
Qed.

Lemma frame_match_alloc:
  forall mm ms fr sp base lom him los his mm' ms' bm bs,
  mm.(nextblock) = ms.(nextblock) ->
  frame_match fr sp base mm ms ->
  alloc mm lom him = (mm', bm) ->
  alloc ms los his = (ms', bs) ->
  frame_match fr sp base mm' ms'.
Proof.
  intros. inversion H0.
  assert (valid_block mm sp). red. rewrite H. auto.
  exploit low_bound_alloc_other. eexact H1. eexact H9. intro LBm.
  exploit high_bound_alloc_other. eexact H1. eexact H9. intro HBm.
  exploit low_bound_alloc_other. eexact H2. eexact H3. intro LBs.
  exploit high_bound_alloc_other. eexact H2. eexact H3. intro HBs.
  apply frame_match_intro.
  eapply valid_block_alloc; eauto.
  congruence. congruence. congruence. auto. auto.
  intros. eapply load_alloc_other; eauto. 
Qed.

(** [frame_match] relations are preserved by freeing a block
  other than the one pointed to by [sp]. *)

Lemma frame_match_free:
  forall fr sp base mm ms b,
  frame_match fr sp base mm ms ->
  sp <> b ->
  frame_match fr sp base (free mm b) (free ms b).
Proof.
  intros. inversion H.
  generalize (low_bound_free mm _ _ H0); intro LBm.
  generalize (low_bound_free ms _ _ H0); intro LBs.
  generalize (high_bound_free mm _ _ H0); intro HBm.
  generalize (high_bound_free ms _ _ H0); intro HBs.
  apply frame_match_intro; auto.
  congruence. congruence. congruence.
  intros. rewrite <- H6; auto. apply load_free. auto.
Qed.

End FRAME_MATCH.

(** ** Accounting for the return address and back link *)

Section EXTEND_FRAME.

Variable f: function.
Hypothesis wt_f: wt_function f.
Variable cs: list Machconcr.stackframe.

Definition extend_frame (fr: frame) : frame :=
  update Tint (Int.signed f.(fn_retaddr_ofs) - f.(fn_framesize)) (parent_ra cs)
    (update Tint (Int.signed f.(fn_link_ofs) - f.(fn_framesize)) (parent_sp cs)
      fr).

Lemma get_slot_extends:
  forall fr ty ofs v,
  get_slot f fr ty ofs v ->
  get_slot f (extend_frame fr) ty ofs v.
Proof.
  intros. inv H. constructor. auto.
  inv H0. inv wt_f. generalize (AST.typesize_pos ty); intro.
  unfold extend_frame. rewrite update_other. rewrite update_other. auto.
  simpl; omega. simpl; omega.
Qed.

Lemma update_commut:
  forall ty1 ofs1 v1 ty2 ofs2 v2 fr,
  ofs1 + AST.typesize ty1 <= ofs2 \/
  ofs2 + AST.typesize ty2 <= ofs1 ->
  update ty1 ofs1 v1 (update ty2 ofs2 v2 fr) =
  update ty2 ofs2 v2 (update ty1 ofs1 v1 fr).
Proof.
  intros. unfold frame.
  apply extensionality. intro ty. apply extensionality. intro ofs.
  generalize (AST.typesize_pos ty1).
  generalize (AST.typesize_pos ty2).
  generalize (AST.typesize_pos ty); intros.
  unfold update.
  set (sz1 := AST.typesize ty1) in *.
  set (sz2 := AST.typesize ty2) in *.
  set (sz := AST.typesize ty) in *.
  destruct (zeq ofs1 ofs).
  rewrite zeq_false. 
  destruct (zle (ofs + sz) ofs2). auto.
  destruct (zle (ofs2 + sz2) ofs). auto.
  destruct (typ_eq ty1 ty); auto.
  replace sz with sz1 in z. omegaContradiction. unfold sz1, sz; congruence.
  omega.

  destruct (zle (ofs + sz) ofs1).
  auto.
  destruct (zle (ofs1 + sz1) ofs).
  auto.

  destruct (zeq ofs2 ofs).
  destruct (typ_eq ty2 ty); auto.
  replace sz with sz2 in z. omegaContradiction. unfold sz2, sz; congruence.
  destruct (zle (ofs + sz) ofs2); auto.
  destruct (zle (ofs2 + sz2) ofs); auto.
Qed.

Lemma set_slot_extends:
  forall fr ty ofs v fr',
  set_slot f fr ty ofs v fr' ->
  set_slot f (extend_frame fr) ty ofs v (extend_frame fr').
Proof.
  intros. inv H. constructor. auto.
  inv H0. inv wt_f. generalize (AST.typesize_pos ty); intro.
  unfold extend_frame. 
  rewrite (update_commut ty). rewrite (update_commut ty). auto.
  simpl. omega. 
  simpl. omega.
Qed.

Lemma frame_match_load_link:
  forall fr sp base mm ms,
  frame_match f (extend_frame fr) sp base mm ms ->
  load_stack ms (Vptr sp base) Tint f.(fn_link_ofs) = Some (parent_sp cs).
Proof.
  intros. inversion wt_f.
  replace (parent_sp cs) with
   (extend_frame fr Tint (Int.signed f.(fn_link_ofs) - f.(fn_framesize))).
  eapply frame_match_load_stack; eauto.
  
  unfold extend_frame. rewrite update_other. apply update_same. simpl. omega. 
Qed.

Lemma frame_match_load_retaddr:
  forall fr sp base mm ms,
  frame_match f (extend_frame fr) sp base mm ms ->
  load_stack ms (Vptr sp base) Tint f.(fn_retaddr_ofs) = Some (parent_ra cs).
Proof.
  intros. inversion wt_f.
  replace (parent_ra cs) with
   (extend_frame fr Tint (Int.signed f.(fn_retaddr_ofs) - f.(fn_framesize))).
  eapply frame_match_load_stack; eauto.
  unfold extend_frame. apply update_same.
Qed.

Lemma frame_match_function_entry:
  forall mm ms mm' ms1 sp sp',
  extends mm ms ->
  alloc mm 0 f.(fn_stacksize) = (mm', sp) ->
  alloc ms (- f.(fn_framesize)) f.(fn_stacksize) = (ms1, sp') ->
  Val.has_type (parent_sp cs) Tint ->
  Val.has_type (parent_ra cs) Tint ->
  let base := Int.repr (-f.(fn_framesize)) in
  exists ms2, exists ms3,
  sp = sp' /\
  store_stack ms1 (Vptr sp base) Tint f.(fn_link_ofs) (parent_sp cs) = Some ms2 /\
  store_stack ms2 (Vptr sp base) Tint f.(fn_retaddr_ofs) (parent_ra cs) = Some ms3 /\
  frame_match f (extend_frame empty_frame) sp base mm' ms3 /\
  extends mm' ms3.
Proof.
  intros. inversion wt_f.
  exploit alloc_extends; eauto. omega. omega. intros [A EXT0].
  exploit frame_match_new. eauto. inv H. eexact H4. eauto. eauto. eauto.
  fold base. intros [C FM0].
  destruct (frame_match_store_stack _ wt_f _ _ _ _ _ Tint _ _
              FM0 wt_function_link wt_function_link_aligned H2 EXT0)
  as [ms2 [STORE1 [FM1 EXT1]]].
  destruct (frame_match_store_stack _ wt_f _ _ _ _ _ Tint _ _
              FM1 wt_function_retaddr wt_function_retaddr_aligned H3 EXT1)
  as [ms3 [STORE2 [FM3 EXT3]]].
  exists ms2; exists ms3; auto.
Qed.

End EXTEND_FRAME.

(** ** Invariant for stacks *)

Section SIMULATION.

Variable p: program.
Let ge := Genv.globalenv p.

(** The [match_stacks] predicate relates a Machabstr call stack
  with the corresponding Machconcr stack.  In addition to enforcing
  the [frame_match] predicate for each stack frame, we also enforce:
- Proper chaining of activation record on the Machconcr side.
- Preservation of the return address stored at the bottom of the
  activation record.
- Separation between the memory blocks holding the activation records:
  their addresses increase strictly from caller to callee.
*)

Definition stack_below (ts: list Machconcr.stackframe) (b: block) : Prop :=
  match parent_sp ts with
  | Vptr sp base' => sp < b
  | _ => False
  end.

Inductive match_stacks: 
      list Machabstr.stackframe -> list Machconcr.stackframe ->
      mem -> mem -> Prop :=
  | match_stacks_nil: forall mm ms,
      match_stacks nil nil mm ms
  | match_stacks_cons: forall fb sp base c fr s f ra ts mm ms,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      wt_function f ->
      frame_match f (extend_frame f ts fr) sp base mm ms ->
      stack_below ts sp ->
      Val.has_type ra Tint ->
      match_stacks s ts mm ms ->
      match_stacks (Machabstr.Stackframe f (Vptr sp base) c fr :: s)
                   (Machconcr.Stackframe fb (Vptr sp base) ra c :: ts)
                   mm ms.

(** If [match_stacks] holds, a lookup in the parent frame in the
  Machabstr semantics corresponds to two memory loads in the
  Machconcr semantics, one to load the pointer to the parent's
  activation record, the second to read within this record. *)

Lemma match_stacks_get_parent:
  forall s ts mm ms ty ofs v,
  match_stacks s ts mm ms ->
  get_slot (parent_function s) (parent_frame s) ty (Int.signed ofs) v ->
  load_stack ms (Machconcr.parent_sp ts) ty ofs = Some v.
Proof.
  intros. inv H; simpl in H0. 
  inv H0. inv H. simpl in H1. elimtype False. generalize (AST.typesize_pos ty). omega.
  simpl. eapply frame_match_get_slot; eauto.
  eapply get_slot_extends; eauto. 
Qed.

(** Preservation of the [match_stacks] invariant
    by various kinds of memory stores. *)

Remark stack_below_trans:
  forall ts b b', 
  stack_below ts b -> b <= b' -> stack_below ts b'.
Proof.
  unfold stack_below; intros. 
  destruct (parent_sp ts); auto. omega.
Qed.

Lemma match_stacks_store_other:
  forall s ts ms mm,
  match_stacks s ts mm ms ->
  forall chunk b ofs v ms',
  store chunk ms b ofs v = Some ms' ->
  stack_below ts b ->
  match_stacks s ts mm ms'.
Proof.
  induction 1; intros.
  constructor.
  red in H6; simpl in H6. 
  econstructor; eauto.
  eapply frame_match_store_other; eauto.
  unfold block; omega.
  eapply IHmatch_stacks; eauto.
  eapply stack_below_trans; eauto. omega.
Qed.

Lemma match_stacks_store_slot:
  forall s ts ms mm,
  match_stacks s ts mm ms ->
  forall ty ofs v ms' b i,
  stack_below ts b ->
  store_stack ms (Vptr b i) ty ofs v = Some ms' ->
  match_stacks s ts mm ms'.
Proof.
  intros.
  unfold store_stack in H1. simpl in H1.
  inv H.
  constructor.
  red in H0; simpl in H0.
  econstructor; eauto.
  eapply frame_match_store_other; eauto.
  unfold block; omega.
  eapply match_stacks_store_other; eauto. 
  eapply stack_below_trans; eauto. omega.
Qed.

Lemma match_stacks_store:
  forall s ts ms mm,
  match_stacks s ts mm ms ->
  forall chunk b ofs v mm' ms',
  store chunk mm b ofs v = Some mm' ->
  store chunk ms b ofs v = Some ms' ->
  match_stacks s ts mm' ms'.
Proof.
  induction 1; intros.
  constructor.
  econstructor; eauto.
  eapply frame_match_store; eauto.
Qed.

Lemma match_stacks_alloc:
  forall s ts ms mm,
  match_stacks s ts mm ms ->
  forall lom him mm' bm los his ms' bs,
  mm.(nextblock) = ms.(nextblock) ->
  alloc mm lom him = (mm', bm) ->
  alloc ms los his = (ms', bs) ->
  match_stacks s ts mm' ms'.
Proof.
  induction 1; intros.
  constructor.
  econstructor; eauto.
  eapply frame_match_alloc; eauto.
Qed.

Lemma match_stacks_free:
  forall s ts ms mm,
  match_stacks s ts mm ms ->
  forall b,
  stack_below ts b ->
  match_stacks s ts (Mem.free mm b) (Mem.free ms b).
Proof.
  induction 1; intros.
  constructor.
  red in H5; simpl in H5.
  econstructor; eauto.
  eapply frame_match_free; eauto. unfold block; omega.
  eapply IHmatch_stacks; eauto.
  eapply stack_below_trans; eauto. omega.
Qed.

Lemma match_stacks_function_entry:
  forall s ts mm ms lom him mm' los his ms' stk,
  match_stacks s ts mm ms ->
  alloc mm lom him = (mm', stk) ->
  alloc ms los his = (ms', stk) ->
  match_stacks s ts mm' ms' /\ stack_below ts stk.
Proof.
  intros.
  assert (stk = nextblock mm). eapply Mem.alloc_result; eauto.
  assert (stk = nextblock ms). eapply Mem.alloc_result; eauto.
  split.
  eapply match_stacks_alloc; eauto. congruence.
  red. 
  inv H; simpl.
  unfold nullptr. apply Zgt_lt. apply nextblock_pos. 
  inv H6. red in H. rewrite H3. auto. 
Qed.

(** ** Invariant between states. *)

(** The [match_state] predicate relates a Machabstr state with
  a Machconcr state.  In addition to [match_stacks] between the
  stacks, we ask that
- The Machabstr frame is properly stored in the activation record,
  as characterized by [frame_match].
- The Machconcr memory state extends the Machabstr memory state,
  in the sense of the [Mem.extends] relation defined in module [Mem]. *)

Inductive match_states:
            Machabstr.state -> Machconcr.state -> Prop :=
  | match_states_intro:
      forall s f sp base c rs fr mm ts fb ms
        (STACKS: match_stacks s ts mm ms)
        (FM: frame_match f (extend_frame f ts fr) sp base mm ms)
        (BELOW: stack_below ts sp)
        (MEXT: Mem.extends mm ms)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f)),
      match_states (Machabstr.State s f (Vptr sp base) c rs fr mm)
                   (Machconcr.State ts fb (Vptr sp base) c rs ms)
  | match_states_call:
      forall s f rs mm ts fb ms
        (STACKS: match_stacks s ts mm ms)
        (MEXT: Mem.extends mm ms)
        (FIND: Genv.find_funct_ptr ge fb = Some f),
      match_states (Machabstr.Callstate s f rs mm)
                   (Machconcr.Callstate ts fb rs ms)
  | match_states_return:
      forall s rs mm ts ms
        (STACKS: match_stacks s ts mm ms)
        (MEXT: Mem.extends mm ms),
      match_states (Machabstr.Returnstate s rs mm)
                   (Machconcr.Returnstate ts rs ms).

(** * The proof of simulation *)

(** The proof of simulation relies on diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                   |t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The precondition is matching between the initial states [st1] and
  [st2], as usual, plus the fact that [st1] is well-typed
  in the sense of predicate [wt_state] from module [Machtyping].
  The postcondition is matching between the final states [st1']
  and [st2'].  The well-typedness of [st2] is not part of the
  postcondition, since it follows from that of [st1] if the
  program is well-typed.  (See the subject reduction property
  in module [Machtyping].)
*)

Lemma find_function_find_function_ptr:
  forall ros rs f',
  find_function ge ros rs = Some f' ->
  exists fb', Genv.find_funct_ptr ge fb' = Some f' /\ find_function_ptr ge ros rs = Some fb'.
Proof.
  intros until f'. destruct ros; simpl.
  intro. exploit Genv.find_funct_inv; eauto. intros [fb' EQ].
  rewrite EQ in H. rewrite Genv.find_funct_find_funct_ptr in H.
  exists fb'; split. auto. rewrite EQ. simpl. auto.
  destruct (Genv.find_symbol ge i); intro.
  exists b; auto. congruence.
Qed.

(** Preservation of arguments to external functions. *)

Lemma transl_extcall_arguments:
  forall rs s sg args ts m ms,
  Machabstr.extcall_arguments (parent_function s) rs (parent_frame s) sg args ->
  match_stacks s ts m ms ->
  extcall_arguments rs ms (parent_sp ts) sg args.
Proof.
  unfold Machabstr.extcall_arguments, extcall_arguments; intros.
  assert (forall locs vals,
    Machabstr.extcall_args (parent_function s) rs (parent_frame s) locs vals ->
    extcall_args rs ms (parent_sp ts) locs vals).
  induction locs; intros; inv H1.
  constructor.
  constructor; auto.
  inv H6. constructor. constructor. eapply match_stacks_get_parent; eauto.
  auto.
Qed.

Hypothesis wt_prog: wt_program p.

Theorem step_equiv:
  forall s1 t s2, Machabstr.step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1') (WTS: wt_state s1),
  exists s2', Machconcr.step ge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros; inv MS.

  (* Mlabel *)
  econstructor; split.
  apply exec_Mlabel; auto.
  econstructor; eauto with coqlib.

  (* Mgetstack *)
  assert (WTF: wt_function f) by (inv WTS; auto).
  exists (State ts fb (Vptr sp0 base) c (rs#dst <- v) ms); split.
  constructor; auto.
  eapply frame_match_get_slot; eauto.
  eapply get_slot_extends; eauto.
  econstructor; eauto with coqlib.

  (* Msetstack *)
  assert (WTF: wt_function f) by (inv WTS; auto).
  assert (Val.has_type (rs src) ty).
    inv WTS. 
    generalize (wt_function_instrs _ WTF _ (is_tail_in TAIL)); intro WTI.
    inv WTI. apply WTRS.
  exploit frame_match_set_slot; eauto.
    eapply set_slot_extends; eauto.
  intros [ms' [STORE [FM' EXT']]].
  exists (State ts fb (Vptr sp0 base) c rs ms'); split.
  apply exec_Msetstack; auto.
  econstructor; eauto.
  eapply match_stacks_store_slot; eauto.

  (* Mgetparam *)
  assert (WTF: wt_function f) by (inv WTS; auto).
  exists (State ts fb (Vptr sp0 base) c (rs#dst <- v) ms); split.
  eapply exec_Mgetparam; eauto.
    eapply frame_match_load_link; eauto.
    eapply match_stacks_get_parent; eauto.
  econstructor; eauto with coqlib. 
 
  (* Mop *)
  exists (State ts fb (Vptr sp0 base) c (rs#res <- v) ms); split.
  apply exec_Mop; auto.
  econstructor; eauto with coqlib.

  (* Mload *)
  exists (State ts fb (Vptr sp0 base) c (rs#dst <- v) ms); split.
  eapply exec_Mload; eauto.
  destruct a; simpl in H0; try discriminate.
  simpl. eapply Mem.load_extends; eauto.
  econstructor; eauto with coqlib.

  (* Mstore *)
  destruct a; simpl in H0; try discriminate.
  exploit Mem.store_within_extends; eauto. intros [ms' [STORE MEXT']].
  exists (State ts fb (Vptr sp0 base) c rs ms'); split.
  eapply exec_Mstore; eauto.
  econstructor; eauto with coqlib.
  eapply match_stacks_store; eauto.
  eapply frame_match_store; eauto.

  (* Mcall *)
  exploit find_function_find_function_ptr; eauto. 
  intros [fb' [FIND' FINDFUNCT]].
  assert (exists ra', return_address_offset f c ra').
    apply return_address_exists.
    inv WTS. eapply is_tail_cons_left; eauto.
  destruct H0 as [ra' RETADDR].
  econstructor; split.
  eapply exec_Mcall; eauto. 
  econstructor; eauto. 
  econstructor; eauto. inv WTS; auto. exact I.

  (* Mtailcall *)
  assert (WTF: wt_function f) by (inv WTS; auto).
  exploit find_function_find_function_ptr; eauto. 
  intros [fb' [FIND' FINDFUNCT]].
  econstructor; split.
  eapply exec_Mtailcall; eauto.
    eapply frame_match_load_link; eauto.
    eapply frame_match_load_retaddr; eauto.
  econstructor; eauto. eapply match_stacks_free; auto.
  apply free_extends; auto.

  (* Mgoto *)
  econstructor; split.
  eapply exec_Mgoto; eauto.
  econstructor; eauto.

  (* Mcond *)
  econstructor; split.
  eapply exec_Mcond_true; eauto.
  econstructor; eauto.
  econstructor; split.
  eapply exec_Mcond_false; eauto.
  econstructor; eauto.

  (* Mreturn *)
  assert (WTF: wt_function f) by (inv WTS; auto).
  econstructor; split.
  eapply exec_Mreturn; eauto.
    eapply frame_match_load_link; eauto.
    eapply frame_match_load_retaddr; eauto.
  econstructor; eauto. eapply match_stacks_free; eauto.   
  apply free_extends; auto.

  (* internal function *)
  assert (WTF: wt_function f). inv WTS. inv H5. auto.
  caseEq (alloc ms (- f.(fn_framesize)) f.(fn_stacksize)).
  intros ms' stk' ALLOC.
  assert (Val.has_type (parent_sp ts) Tint).
    inv STACKS; simpl; auto.
  assert (Val.has_type (parent_ra ts) Tint).
    inv STACKS; simpl; auto.
  destruct (frame_match_function_entry _ WTF _ _ _ _ _ _ _
              MEXT H ALLOC H0 H1)
  as [ms2 [ms3 [EQ [STORE1 [STORE2 [FM MEXT']]]]]].
  subst stk'.
  econstructor; split.
  eapply exec_function_internal; eauto.
  exploit match_stacks_function_entry; eauto. intros [STACKS' BELOW].
  econstructor; eauto.
  eapply match_stacks_store_slot with (ms := ms2); eauto.
  eapply match_stacks_store_slot with (ms := ms'); eauto.

  (* external function *)
  econstructor; split.
  eapply exec_function_external; eauto. 
  eapply transl_extcall_arguments; eauto.
  econstructor; eauto.

  (* return *)
  inv STACKS.
  econstructor; split.
  eapply exec_return. 
  econstructor; eauto.
Qed.

Lemma equiv_initial_states:
  forall st1, Machabstr.initial_state p st1 ->
  exists st2, Machconcr.initial_state p st2 /\ match_states st1 st2 /\ wt_state st1.
Proof.
  intros. inversion H.
  econstructor; split.
  econstructor. eauto. 
  split. econstructor. constructor. apply Mem.extends_refl. auto.
  econstructor. simpl; intros; contradiction.
  eapply Genv.find_funct_ptr_prop; eauto.
  red; intros; exact I.
Qed.

Lemma equiv_final_states:
  forall st1 st2 r, 
  match_states st1 st2 /\ wt_state st1 -> Machabstr.final_state st1 r -> Machconcr.final_state st2 r.
Proof.
  intros. inv H0. destruct H. inv H. inv STACKS.
  constructor; auto.
Qed.

Theorem exec_program_equiv:
  forall (beh: program_behavior), not_wrong beh ->
  Machabstr.exec_program p beh -> Machconcr.exec_program p beh.
Proof.
  unfold Machconcr.exec_program, Machabstr.exec_program; intros.
  eapply simulation_step_preservation with
    (step1 := Machabstr.step)
    (step2 := Machconcr.step)
    (match_states := fun st1 st2 => match_states st1 st2 /\ wt_state st1).
  eexact equiv_initial_states.
  eexact equiv_final_states.
  intros. destruct H2. exploit step_equiv; eauto.
  intros [st2' [A B]]. exists st2'; split. auto. split. auto.
  eapply Machtyping.subject_reduction; eauto. 
  auto. auto.
Qed.

End SIMULATION.
