(** Simulation between the two semantics for the Mach language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Machabstr.
Require Import Mach.
Require Import Machtyping.
Require Import Stackingproof.

(** Two semantics were defined for the Mach intermediate language:
- The concrete semantics (file [Mach]), where the whole activation
  record resides in memory and the [Mgetstack], [Msetstack] and
  [Mgetparent] are interpreted as [sp]-relative memory accesses.
- The abstract semantics (file [Machabstr]), where the activation
  record is split in two parts: the Cminor stack data, resident in
  memory, and the frame information, residing not in memory but
  in additional evaluation environments.

  In this file, we show a simulation result between these
  semantics: if a program executes to some result [r] in the
  abstract semantics, it also executes to the same result in
  the concrete semantics.  This result bridges the correctness proof
  in file [Stackingproof] (which uses the abstract Mach semantics
  as output) and that in file [PPCgenproof] (which uses the concrete
  Mach semantics as input).
*)

Remark align_16_top_ge:
  forall lo hi,
  hi <= align_16_top lo hi.
Proof.
  intros. unfold align_16_top. apply Zmax_bound_r. 
  assert (forall x, x <= (x + 15) / 16 * 16).
  intro. assert (16 > 0). omega.
  generalize (Z_div_mod_eq (x + 15) 16 H). intro.
  replace ((x + 15) / 16 * 16) with ((x + 15) - (x + 15) mod 16).
  generalize (Z_mod_lt (x + 15) 16 H). omega. 
  rewrite Zmult_comm. omega.
  generalize (H (hi - lo)). omega. 
Qed.

Remark align_16_top_pos:
  forall lo hi,
  0 <= align_16_top lo hi.
Proof.
  intros. unfold align_16_top. apply Zmax_bound_l. omega.
Qed.

Remark size_mem_pos:
  forall sz, size_mem sz > 0.
Proof.
  destruct sz; simpl; compute; auto.
Qed.

Remark size_type_chunk:
  forall ty, size_chunk (chunk_of_type ty) = 4 * typesize ty.
Proof.
  destruct ty; reflexivity.
Qed.

Remark mem_chunk_type:
  forall ty, mem_chunk (chunk_of_type ty) = mem_type ty.
Proof.
  destruct ty; reflexivity.
Qed.

Remark size_mem_type:
  forall ty, size_mem (mem_type ty) = 4 * typesize ty.
Proof.
  destruct ty; reflexivity.
Qed.

(** * Agreement between frames and memory-resident activation records *)

(** ** Agreement for one frame *)

(** The core idea of the simulation proof is that for all active
  functions, the memory-allocated activation record, in the concrete 
  semantics, contains the same data as the Cminor stack block
  (at positive offsets) and the frame of the function (at negative
  offsets) in the abstract semantics.

  This intuition (activation record = Cminor stack data + frame)
  is formalized by the following predicate [frame_match fr sp base mm ms].
  [fr] is a frame and [mm] the current memory state in the abstract
  semantics. [ms] is the current memory state in the concrete semantics.
  The stack pointer is [Vptr sp base] in both semantics. *)

Inductive frame_match: frame -> block -> int -> mem -> mem -> Prop :=
  frame_match_intro:
    forall fr sp base mm ms,
    valid_block ms sp ->
    low_bound mm sp = 0 ->
    low_bound ms sp = fr.(low) ->
    high_bound ms sp = align_16_top fr.(low) (high_bound mm sp) ->
    fr.(low) <= 0 ->
    Int.min_signed <= fr.(low) ->
    base = Int.repr fr.(low) ->
    block_contents_agree fr.(low) 0 fr (ms.(blocks) sp) ->
    block_contents_agree 0 (high_bound ms sp)
                         (mm.(blocks) sp) (ms.(blocks) sp) ->
    frame_match fr sp base mm ms.

(** [frame_match], while presented as a relation for convenience,
  is actually a function: it fully determines the contents of the
  activation record [ms.(blocks) sp]. *)

Lemma frame_match_exten:
  forall fr sp base mm ms1 ms2,
  frame_match fr sp base mm ms1 ->
  frame_match fr sp base mm ms2 ->
  ms1.(blocks) sp = ms2.(blocks) sp. 
Proof.
  intros. inversion H. inversion H0.
  unfold low_bound, high_bound in *.
  apply block_contents_exten.
  congruence.
  congruence.
  hnf; intros.
  elim H29. rewrite H3; rewrite H4; intros.
  case (zlt ofs 0); intro.
  assert (low fr <= ofs < 0). tauto.
  transitivity (contents fr ofs).
  symmetry. apply H8; auto.
  apply H22; auto.
  transitivity (contents (blocks mm sp) ofs).
  symmetry. apply H9. rewrite H4. omega.
  apply H23. rewrite H18. omega.
Qed.

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

Lemma frame_match_get_slot:
  forall fr sp base mm ms ty ofs v,
  frame_match fr sp base mm ms ->
  get_slot fr ty (Int.signed ofs) v ->
  Val.has_type v ty ->
  load_stack ms (Vptr sp base) ty ofs = Some v.
Proof.
  intros. inversion H. inversion H0. subst v.
  unfold load_stack, Val.add, loadv. 
  assert (Int.signed base = low fr).
    rewrite H8. apply Int.signed_repr.
    split. auto. apply Zle_trans with 0. auto. compute; congruence.
  assert (Int.signed (Int.add base ofs) = low fr + Int.signed ofs).
    rewrite int_add_no_overflow. rewrite H18. auto.
    rewrite H18. split. omega. apply Zle_trans with 0.
    generalize (typesize_pos ty). omega. compute. congruence.
  rewrite H23. 
  assert (BND1: low_bound ms sp <= low fr + Int.signed ofs). 
    omega. 
  assert (BND2: (low fr + Int.signed ofs) + size_chunk (chunk_of_type ty) <= high_bound ms sp).
    rewrite size_type_chunk. apply Zle_trans with 0.
    assumption. rewrite H5. apply align_16_top_pos.
  generalize (load_in_bounds (chunk_of_type ty) ms sp (low fr + Int.signed ofs) H2 BND1 BND2).
  intros [v' LOAD].
  generalize (load_inv _ _ _ _ _ LOAD).
  intros [A [B [C D]]].
  rewrite LOAD. rewrite <- D. 
  decEq. rewrite mem_chunk_type. 
  rewrite <- size_mem_type in H17.
  assert (low fr <= low fr + Int.signed ofs). omega.
  generalize (load_contentmap_agree _ _ _ _ _ _ H9 H24 H17).
  intro. rewrite H25.
  apply load_result_ty.
  assumption.
Qed.

(** Loads from [sp], corresponding to accesses to Cminor stack data
  in the abstract semantics, give the same results in the concrete
  semantics.  This is because the offset from [sp] must be positive or
  null for the original load to succeed, and because the part
  of the activation record at positive offsets matches the Cminor
  stack data block. *)

Lemma frame_match_load:
  forall fr sp base mm ms chunk ofs v,
  frame_match fr sp base mm ms ->
  load chunk mm sp ofs = Some v ->
  load chunk ms sp ofs = Some v.
Proof.
  intros. inversion H. 
  generalize (load_inv _ _ _ _ _ H0). intros [A [B [C D]]].
  change (low (blocks mm sp)) with (low_bound mm sp) in B.
  change (high (blocks mm sp)) with (high_bound mm sp) in C.
  unfold load. rewrite zlt_true; auto.
  rewrite in_bounds_holds. 
  rewrite <- D. decEq. decEq. eapply load_contentmap_agree.
  red in H9. eexact H9. 
  omega.
  unfold size_chunk in C. rewrite H4. 
  apply Zle_trans with (high_bound mm sp). auto. 
  apply align_16_top_ge. 
  change (low (blocks ms sp)) with (low_bound ms sp).
  rewrite H3. omega.
  change (high (blocks ms sp)) with (high_bound ms sp).
  rewrite H4. apply Zle_trans with (high_bound mm sp). auto.
  apply align_16_top_ge.
Qed.

(** Assigning a value to a frame slot (in the abstract semantics)
  corresponds to storing this value in the activation record
  (in the concrete semantics).  Moreover, agreement between frames
  and activation records is preserved. *)

Lemma frame_match_set_slot:
  forall fr sp base mm ms ty ofs v fr',
  frame_match fr sp base mm ms ->
  set_slot fr ty (Int.signed ofs) v fr' ->
  exists ms',
    store_stack ms (Vptr sp base) ty ofs v = Some ms' /\
    frame_match fr' sp base mm ms'.
Proof.
  intros. inversion H. inversion H0. subst ty0.
  unfold store_stack, Val.add, storev. 
  assert (Int.signed base = low fr).
    rewrite H7. apply Int.signed_repr.
    split. auto. apply Zle_trans with 0. auto. compute; congruence.
  assert (Int.signed (Int.add base ofs) = low fr + Int.signed ofs).
    rewrite int_add_no_overflow. rewrite H16. auto.
    rewrite H16. split. omega. apply Zle_trans with 0.
    generalize (typesize_pos ty). omega. compute. congruence.
  rewrite H20.
  assert (BND1: low_bound ms sp <= low fr + Int.signed ofs). 
    omega. 
  assert (BND2: (low fr + Int.signed ofs) + size_chunk (chunk_of_type ty) <= high_bound ms sp).
    rewrite size_type_chunk. rewrite H4.
    apply Zle_trans with 0. subst ofs0. auto. apply align_16_top_pos. 
  generalize (store_in_bounds _ _ _ _ v H1 BND1 BND2).
  intros [ms' STORE].
  generalize (store_inv _ _ _ _ _ _ STORE). intros [P [Q [R [S [x T]]]]].
  generalize (low_bound_store _ _ _ _ sp _ _ STORE). intro LB.
  generalize (high_bound_store _ _ _ _ sp _ _ STORE). intro HB.
  exists ms'. 
  split. exact STORE.
  apply frame_match_intro; auto.
  eapply valid_block_store; eauto.
  rewrite LB. auto.
  rewrite HB. auto.
  red. rewrite T; rewrite update_s; simpl. 
  rewrite mem_chunk_type. 
  subst ofs0. eapply store_contentmap_agree; eauto.
  rewrite HB; rewrite T; rewrite update_s.
  red. simpl. apply store_contentmap_outside_agree.
  assumption. left. rewrite mem_chunk_type. 
  rewrite size_mem_type. subst ofs0. auto.
Qed.

(** Agreement is preserved by stores within blocks other than the
  one pointed to by [sp]. *)

Lemma frame_match_store_stack_other:
  forall fr sp base mm ms sp' base' ty ofs v ms',
  frame_match fr sp base mm ms ->
  store_stack ms (Vptr sp' base') ty ofs v = Some ms' ->
  sp <> sp' ->
  frame_match fr sp base mm ms'.
Proof.
  unfold store_stack, Val.add, storev. intros. inversion H.
  generalize (store_inv _ _ _ _ _ _ H0). intros [P [Q [R [S [x T]]]]].
  generalize (low_bound_store _ _ _ _ sp _ _ H0). intro LB.
  generalize (high_bound_store _ _ _ _ sp _ _ H0). intro HB.
  apply frame_match_intro; auto.
  eapply valid_block_store; eauto.
  rewrite LB; auto.
  rewrite HB; auto.
  rewrite T; rewrite update_o; auto.
  rewrite HB; rewrite T; rewrite update_o; auto.
Qed.

(** Stores relative to [sp], corresponding to accesses to Cminor stack data
  in the abstract semantics, give the same results in the concrete
  semantics.  Moreover, agreement between frames and activation
  records is preserved. *)

Lemma frame_match_store_ok:
  forall fr sp base mm ms chunk ofs v mm',
  frame_match fr sp base mm ms ->
  store chunk mm sp ofs v = Some mm' ->
  exists ms', store chunk ms sp ofs v = Some ms'.
Proof.
  intros. inversion H. 
  generalize (store_inv _ _ _ _ _ _ H0). intros [P [Q [R [S [x T]]]]].
  change (low (blocks mm sp)) with (low_bound mm sp) in Q.
  change (high (blocks mm sp)) with (high_bound mm sp) in R.
  apply store_in_bounds.
  auto.
  omega. 
  apply Zle_trans with (high_bound mm sp).
    auto. rewrite H4. apply align_16_top_ge. 
Qed.

Lemma frame_match_store:
  forall fr sp base mm ms chunk b ofs v mm' ms',
  frame_match fr sp base mm ms ->
  store chunk mm b ofs v = Some mm' ->
  store chunk ms b ofs v = Some ms' ->
  frame_match fr sp base mm' ms'.
Proof.
  intros. inversion H. 
  generalize (store_inv _ _ _ _ _ _ H1). intros [A [B [C [D [x1 E]]]]].
  generalize (store_inv _ _ _ _ _ _ H0). intros [I [J [K [L [x2 M]]]]].
  generalize (low_bound_store _ _ _ _ sp _ _ H0). intro LBm.
  generalize (low_bound_store _ _ _ _ sp _ _ H1). intro LBs.
  generalize (high_bound_store _ _ _ _ sp _ _ H0). intro HBm.
  generalize (high_bound_store _ _ _ _ sp _ _ H1). intro HBs.
  apply frame_match_intro; auto.
  eapply valid_block_store; eauto.
  congruence. congruence. congruence. 
  rewrite E. unfold update. case (zeq sp b); intro.
  subst b. red; simpl.
  apply store_contentmap_outside_agree; auto.
  right. unfold low_bound in H3. omega.
  assumption.
  rewrite HBs; rewrite E; rewrite M; unfold update.
  case (zeq sp b); intro.
  subst b. red; simpl.
  apply store_contentmap_agree; auto.
  assumption.
Qed.

(** Memory allocation of the Cminor stack data block (in the abstract
  semantics) and of the whole activation record (in the concrete
  semantics) return memory states that agree according to [frame_match].
  Moreover, [frame_match] relations over already allocated blocks
  remain true. *)

Lemma frame_match_new:
  forall mm ms mm' ms' sp sp' f,
  mm.(nextblock) = ms.(nextblock) ->
  alloc mm 0 f.(fn_stacksize) = (mm', sp) ->
  alloc ms (- f.(fn_framesize)) (align_16_top (- f.(fn_framesize)) f.(fn_stacksize)) = (ms', sp') ->
  f.(fn_framesize) >= 0 ->
  f.(fn_framesize) <= -Int.min_signed ->
  frame_match (init_frame f) sp (Int.repr (-f.(fn_framesize))) mm' ms'.
Proof.
  intros. 
  injection H0; intros. injection H1; intros.
  assert (sp = sp'). congruence. rewrite <- H8 in H6. subst sp'.
  generalize (low_bound_alloc _ _ sp _ _ _ H0). rewrite zeq_true. intro LBm.
  generalize (low_bound_alloc _ _ sp _ _ _ H1). rewrite zeq_true. intro LBs.
  generalize (high_bound_alloc _ _ sp _ _ _ H0). rewrite zeq_true. intro HBm.
  generalize (high_bound_alloc _ _ sp _ _ _ H1). rewrite zeq_true. intro HBs.
  apply frame_match_intro; auto.
  eapply valid_new_block; eauto.
  simpl. congruence.
  simpl. omega.
  simpl. omega.
  rewrite <- H7. simpl. rewrite H6; simpl. rewrite update_s.
  hnf; simpl; auto.
  rewrite HBs; rewrite <- H5; simpl; rewrite H4; rewrite <- H7; simpl; rewrite H6; simpl;
  repeat (rewrite update_s).
  hnf; simpl; auto.
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
  assert (sp <> bm). 
    apply valid_not_valid_diff with mm. 
    red. rewrite H. exact H3.
    eapply fresh_block_alloc; eauto.
  assert (sp <> bs).
    apply valid_not_valid_diff with ms. auto. 
    eapply fresh_block_alloc; eauto.
  generalize (low_bound_alloc _ _ sp _ _ _  H1). 
    rewrite zeq_false; auto; intro LBm.
  generalize (low_bound_alloc _ _ sp _ _ _  H2). 
    rewrite zeq_false; auto; intro LBs.
  generalize (high_bound_alloc _ _ sp _ _ _  H1). 
    rewrite zeq_false; auto; intro HBm.
  generalize (high_bound_alloc _ _ sp _ _ _  H2). 
    rewrite zeq_false; auto; intro HBs.
  apply frame_match_intro.
  eapply valid_block_alloc; eauto.
  congruence. congruence. congruence. auto. auto. auto. 
  injection H2; intros. rewrite <- H20; simpl; rewrite H19; simpl.
    rewrite update_o; auto. 
  rewrite HBs;
  injection H2; intros. rewrite <- H20; simpl; rewrite H19; simpl.
  injection H1; intros. rewrite <- H22; simpl; rewrite H21; simpl.
  repeat (rewrite update_o; auto).
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
  unfold free; simpl. rewrite update_o; auto. 
  rewrite HBs. 
  unfold free; simpl. repeat (rewrite update_o; auto).
Qed.

(** ** Agreement for all the frames in a call stack *)

(** We need to reason about all the frames and activation records
    active at any given time during the executions: not just
    about those for the currently executing function, but also
    those for the callers.  These collections of 
    active frames are called ``call stacks''.  They are lists
    of triples representing a frame and a stack pointer
    (reference and offset) in the abstract semantics. *)

Definition callstack : Set := list (frame * block * int).

(** The correct linking of frames (each frame contains a pointer
  to the frame of its caller at the lowest offset) is captured
  by the following predicate. *)

Inductive callstack_linked: callstack -> Prop :=
  | callstack_linked_nil:
      callstack_linked nil
  | callstack_linked_one:
      forall fr1 sp1 base1,
      callstack_linked ((fr1, sp1, base1) :: nil)
  | callstack_linked_cons:
      forall fr1 sp1 base1 fr2 base2 sp2 cs,
      get_slot fr1 Tint 0 (Vptr sp2 base2) ->
      callstack_linked ((fr2, sp2, base2) :: cs) ->
      callstack_linked ((fr1, sp1, base1) :: (fr2, sp2, base2) :: cs).

(** [callstack_dom cs b] (read: call stack [cs] is ``dominated''
  by block reference [b]) means that the stack pointers in [cs]
  strictly decrease and are all below [b].  This ensures that
  the stack block for a function was allocated after that for its
  callers.  A consequence is that no two active functions share
  the same stack block. *)

Inductive callstack_dom: callstack -> block -> Prop :=
  | callstack_dom_nil:
      forall b, callstack_dom nil b
  | callstack_dom_cons:
      forall fr sp base cs b,
      sp < b ->
      callstack_dom cs sp ->
      callstack_dom ((fr, sp, base) :: cs) b.

Lemma callstack_dom_less:
  forall cs b, callstack_dom cs b ->
  forall fr sp base, In (fr, sp, base) cs -> sp < b.
Proof.
  induction 1. simpl. tauto. 
  simpl. intros fr0 sp0 base0 [A|B].
  injection A; intros; subst fr0; subst sp0; subst base0. auto.
  apply Zlt_trans with sp. eapply IHcallstack_dom; eauto. auto.
Qed.

Lemma callstack_dom_diff:
  forall cs b, callstack_dom cs b ->
  forall fr sp base, In (fr, sp, base) cs -> sp <> b.
Proof.
  intros. apply Zlt_not_eq. eapply callstack_dom_less; eauto.
Qed.

Lemma callstack_dom_incr:
  forall cs b, callstack_dom cs b ->
  forall b', b < b' -> callstack_dom cs b'.
Proof.
  induction 1; intros.
  apply callstack_dom_nil.
  apply callstack_dom_cons. omega. auto.
Qed.

(** Every block reference is either ``in'' a call stack (that is,
  refers to the stack block of one of the calls) or  ``not in''
  a call stack (that is, differs from all the stack blocks). *)

Inductive notin_callstack: block -> callstack -> Prop :=
  | notin_callstack_nil:
      forall b, notin_callstack b nil
  | notin_callstack_cons:
      forall b fr sp base cs,
      b <> sp ->
      notin_callstack b cs ->
      notin_callstack b ((fr, sp, base) :: cs).

Lemma in_or_notin_callstack:
  forall b cs,
  (exists fr, exists base, In (fr, b, base) cs) \/ notin_callstack b cs.
Proof.
  induction cs.
  right; constructor.
  elim IHcs. 
  intros [fr [base IN]]. left. exists fr; exists base; auto with coqlib.
  intro NOTIN. destruct a. destruct p. case (eq_block b b0); intro.
  left. exists f; exists i. subst b0. auto with coqlib.
  right. apply notin_callstack_cons; auto.
Qed. 

(** [callstack_invariant cs mm ms] relates the memory state [mm]
  from the abstract semantics with the memory state [ms] from the
  concrete semantics, relative to the current call stack [cs].
  Five conditions are enforced:
- All frames in [cs] agree with the corresponding activation records
  (in the sense of [frame_match]).
- The frames in the call stack are properly linked.
- Memory blocks that are not activation records for active function
  calls are exactly identical in [mm] and [ms].
- The allocation pointers are the same in [mm] and [ms].
- The call stack [cs] is ``dominated'' by this allocation pointer,
  implying that all activation records are valid, allocated blocks,
  pairwise disjoint, and they were allocated in the order implied
  by [cs]. *)

Record callstack_invariant (cs: callstack) (mm ms: mem) : Prop :=
  mk_callstack_invariant {
    cs_frame:
      forall fr sp base,
      In (fr, sp, base) cs -> frame_match fr sp base mm ms;
    cs_linked:
      callstack_linked cs;
    cs_others:
      forall b, notin_callstack b cs ->
            mm.(blocks) b = ms.(blocks) b;
    cs_next:
      mm.(nextblock) = ms.(nextblock);
    cs_dom:
      callstack_dom cs ms.(nextblock)
  }.

(** Again, while [callstack_invariant] is presented as a relation,
  it actually fully determines the concrete memory state [ms]
  from the abstract memory state [mm] and the call stack [cs]. *)

Lemma callstack_exten:
  forall cs mm ms1 ms2,
  callstack_invariant cs mm ms1 ->
  callstack_invariant cs mm ms2 ->
  ms1 = ms2.
Proof.
  intros. inversion H; inversion H0. 
  apply mem_exten.
  congruence. 
  intros. elim (in_or_notin_callstack b cs).
  intros [fr [base FM]]. apply frame_match_exten with fr base mm; auto.
  intro. transitivity (blocks mm b).
  symmetry. auto. auto.
Qed.

(** The following properties of [callstack_invariant] are the
  building blocks for the proof of simulation.  First, a [get_slot]
  operation in the abstract semantics corresponds to a [sp]-relative
  memory load in the concrete semantics. *)

Lemma callstack_get_slot:
  forall fr sp base cs mm ms ty ofs v,
  callstack_invariant ((fr, sp, base) :: cs) mm ms ->
  get_slot fr ty (Int.signed ofs) v ->
  Val.has_type v ty ->
  load_stack ms (Vptr sp base) ty ofs = Some v.
Proof.
  intros. inversion H. 
  apply frame_match_get_slot with fr mm. 
  apply cs_frame0. apply in_eq.
  auto. auto.
Qed.

(** Similarly, a [get_parent] operation corresponds to loading
  the back-link from the current activation record, then loading
  from this back-link. *)

Lemma callstack_get_parent:
  forall fr1 sp1 base1 fr2 sp2 base2 cs mm ms ty ofs v,
  callstack_invariant ((fr1, sp1, base1) :: (fr2, sp2, base2) :: cs) mm ms ->
  get_slot fr2 ty (Int.signed ofs) v ->
  Val.has_type v ty ->
  load_stack ms (Vptr sp1 base1) Tint (Int.repr 0) = Some (Vptr sp2 base2) /\
  load_stack ms (Vptr sp2 base2) ty ofs = Some v.
Proof.
  intros. inversion H. split.
  inversion cs_linked0. 
  apply frame_match_get_slot with fr1 mm.
  apply cs_frame0. auto with coqlib.
  rewrite Int.signed_repr. auto. compute. intuition congruence.
  exact I.
  apply frame_match_get_slot with fr2 mm. 
  apply cs_frame0. auto with coqlib.
  auto. auto.
Qed.

(** A memory load valid in the abstract semantics can also be performed
  in the concrete semantics. *)

Lemma callstack_load:
  forall cs chunk mm ms a v,
  callstack_invariant cs mm ms ->
  loadv chunk mm a = Some v ->
  loadv chunk ms a = Some v.
Proof.
  unfold loadv. intros. destruct a; try discriminate.
  inversion H.
  elim (in_or_notin_callstack b cs).
  intros [fr [base IN]]. apply frame_match_load with fr base mm; auto.
  intro. rewrite <- H0. unfold load. 
  rewrite (cs_others0 b H1). rewrite cs_next0. reflexivity.
Qed.

(** A [set_slot] operation in the abstract semantics corresponds
  to a [sp]-relative memory store in the concrete semantics.
  Moreover, the property [callstack_invariant] still holds for
  the final call stacks and memory states. *)

Lemma callstack_set_slot:
  forall fr sp base cs mm ms ty ofs v fr',
  callstack_invariant ((fr, sp, base) :: cs) mm ms ->
  set_slot fr ty (Int.signed ofs) v fr' ->
  4 <= Int.signed ofs ->
  exists ms',
    store_stack ms (Vptr sp base) ty ofs v = Some ms' /\
    callstack_invariant ((fr', sp, base) :: cs) mm ms'.
Proof.
  intros. inversion H.
  assert (frame_match fr sp base mm ms). apply cs_frame0. apply in_eq.
  generalize (frame_match_set_slot _ _ _ _ _ _ _ _ _ H2 H0).
  intros [ms' [SS FM]].
  generalize (store_inv _ _ _ _ _ _ SS). intros [A [B [C [D [x E]]]]].
  exists ms'.
  split. auto.
  constructor.
  (* cs_frame *)
  intros. elim H3; intros. 
  injection H4; intros; clear H4. 
  subst fr0; subst sp0; subst base0. auto.
  apply frame_match_store_stack_other with ms sp base ty ofs v.
  apply cs_frame0. auto with coqlib. auto. 
  apply callstack_dom_diff with cs fr0 base0. inversion cs_dom0; auto. auto.
  (* cs_linked *)
  inversion cs_linked0. apply callstack_linked_one.
  apply callstack_linked_cons. 
  eapply slot_gso; eauto.
  auto.
  (* cs_others *)
  intros. inversion H3. 
  rewrite E; simpl. rewrite update_o; auto. apply cs_others0.
  constructor; auto.
  (* cs_next *)
  congruence.
  (* cs_dom *)
  inversion cs_dom0. constructor. rewrite D; auto. auto.
Qed.

(** A memory store in the abstract semantics can also be performed
  in the concrete semantics.  Moreover, the property
  [callstack_invariant] is preserved. *)

Lemma callstack_store_aux:
  forall cs mm ms chunk b ofs v mm' ms',
  callstack_invariant cs mm ms ->
  store chunk mm b ofs v = Some mm' ->
  store chunk ms b ofs v = Some ms' ->
  callstack_invariant cs mm' ms'.
Proof.
  intros. inversion H.
  generalize (store_inv _ _ _ _ _ _ H0). intros [A [B [C [D [x E]]]]].
  generalize (store_inv _ _ _ _ _ _ H1). intros [P [Q [R [S [y T]]]]].
  constructor; auto.
  (* cs_frame *)
  intros. eapply frame_match_store; eauto.
  (* cs_others *)
  intros. generalize (cs_others0 b0 H2); intro.
  rewrite E; rewrite T; unfold update.
  case (zeq b0 b); intro.
  subst b0. 
  generalize x; generalize y. rewrite H3. 
  intros. replace y0 with x0. reflexivity. apply proof_irrelevance.
  auto.
  (* cs_nextblock *)
  congruence.
  (* cs_dom *)
  rewrite S. auto.
Qed.

Lemma callstack_store_ok:
  forall cs mm ms chunk b ofs v mm',
  callstack_invariant cs mm ms ->
  store chunk mm b ofs v = Some mm' ->
  exists ms', store chunk ms b ofs v = Some ms'.
Proof.
  intros. inversion H.
  elim (in_or_notin_callstack b cs).
  intros [fr [base IN]].
  apply frame_match_store_ok with fr base mm mm'; auto.
  intro. generalize (cs_others0 b H1). intro.
  generalize (store_inv _ _ _ _ _ _ H0). 
  rewrite cs_next0; rewrite H2. intros [A [B [C [D [x E]]]]].
  apply store_in_bounds; auto.
Qed.

Lemma callstack_store:
  forall cs mm ms chunk a v mm',
  callstack_invariant cs mm ms ->
  storev chunk mm a v = Some mm' ->
  exists ms',
    storev chunk ms a v = Some ms' /\
    callstack_invariant cs mm' ms'.
Proof.
  unfold storev; intros. destruct a; try discriminate.
  generalize (callstack_store_ok _ _ _ _ _ _ _ _ H H0).
  intros [ms' STORE].
  exists ms'. split. auto. eapply callstack_store_aux; eauto.
Qed.

(** Allocations of heap blocks can be performed in parallel in
    both semantics, preserving [callstack_invariant]. *)

Lemma callstack_alloc:
  forall cs mm ms lo hi mm' blk,
  callstack_invariant cs mm ms ->
  Mem.alloc mm lo hi = (mm', blk) ->
  exists ms',
    Mem.alloc ms lo hi = (ms', blk) /\
    callstack_invariant cs mm' ms'.
Proof.
  intros. inversion H. 
  caseEq (alloc ms lo hi). intros ms' blk' ALLOC'.
  injection H0; intros. injection ALLOC'; intros.
  assert (blk' = blk). congruence. rewrite H5 in H3. rewrite H5. 
  exists ms'; split. auto.
  constructor. 
  (* frame *)
  intros; eapply frame_match_alloc; eauto.
  (* linked *)
  auto.
  (* others *)
  intros. rewrite <- H2; rewrite <- H4; simpl.
  rewrite H1; rewrite H3. unfold update. case (zeq b blk); auto.
  (* next *)
  rewrite <- H2; rewrite <- H4; simpl; congruence.
  (* dom *)
  eapply callstack_dom_incr; eauto. rewrite <- H4; simpl. omega.
Qed.

(** At function entry, a new frame is pushed on the call stack,
  and memory blocks are allocated in both semantics.  Moreover,
  the back link to the caller's activation record is set up
  in the concrete semantics.  All this preserves [callstack_invariant]. *)

Lemma callstack_function_entry:
  forall fr0 sp0 base0 cs mm ms f fr mm' sp ms' sp',
  callstack_invariant ((fr0, sp0, base0) :: cs) mm ms ->
  alloc mm 0 f.(fn_stacksize) = (mm', sp) ->
  alloc ms (- f.(fn_framesize)) (align_16_top (- f.(fn_framesize)) f.(fn_stacksize)) = (ms', sp') ->
  f.(fn_framesize) >= 0 ->
  f.(fn_framesize) <= -Int.min_signed ->
  set_slot (init_frame f) Tint 0 (Vptr sp0 base0) fr ->
  let base := Int.repr (-f.(fn_framesize)) in
  exists ms'',
     store_stack ms' (Vptr sp base) Tint (Int.repr 0) (Vptr sp0 base0) = Some ms''
  /\ callstack_invariant ((fr, sp, base) :: (fr0, sp0, base0) :: cs) mm' ms''
  /\ sp' = sp.
Proof.
  assert (ZERO: 0 = Int.signed (Int.repr 0)).
    rewrite Int.signed_repr. auto. compute; intuition congruence.
  intros. inversion H.
  injection H0; intros. injection H1; intros.
  assert (sp' = sp). congruence. rewrite H9 in H7. subst sp'.
  assert (frame_match (init_frame f) sp base mm' ms').
    unfold base. eapply frame_match_new; eauto.
  rewrite ZERO in H4.
  generalize (frame_match_set_slot _ _ _ _ _ _ _ _ _ H9 H4).
  intros [ms'' [SS FM]].
  generalize (store_inv _ _ _ _ _ _ SS).  
  intros [A [B [C [D [x E]]]]].
  exists ms''. split; auto. split.
  constructor.
  (* cs_frame *)
  intros. elim H10; intro.
  injection H11; intros; clear H11.
  subst fr1; subst sp1; subst base1. auto.
  eapply frame_match_store_stack_other; eauto.
  eapply frame_match_alloc; [idtac|idtac|eexact H0|eexact H1].
  congruence. eapply cs_frame; eauto with coqlib. 
  rewrite <- H7. eapply callstack_dom_diff; eauto with coqlib.
  (* cs_linked *)
  constructor. rewrite ZERO. eapply slot_gss; eauto. auto.
  (* cs_others *)
  intros. inversion H10. 
  rewrite E; rewrite update_o; auto. 
  rewrite <- H6; rewrite <- H8; simpl; rewrite H5; rewrite H7; simpl. 
  repeat (rewrite update_o; auto). 
  (* cs_next *)
  rewrite D. rewrite <- H6; rewrite <- H8; simpl. congruence.
  (* cs_dom *)
  constructor. rewrite D; auto. rewrite <- H7. auto.
  auto.
Qed.

(** At function return, the memory blocks corresponding to Cminor
  stack data and activation record for the function are freed.
  This preserves [callstack_invariant]. *)

Lemma callstack_function_return:
  forall fr sp base cs mm ms,
  callstack_invariant ((fr, sp, base) :: cs) mm ms ->
  callstack_invariant cs (free mm sp) (free ms sp).
Proof.
  intros. inversion H. inversion cs_dom0.
  constructor.
  (* cs_frame *)
  intros. apply frame_match_free. apply cs_frame0; auto with coqlib.
  apply callstack_dom_diff with cs fr1 base1. auto. auto.
  (* cs_linked *)
  inversion cs_linked0. apply callstack_linked_nil. auto.
  (* cs_others *)
  intros. 
  unfold free; simpl; unfold update.
  case (zeq b0 sp); intro.
  auto.
  apply cs_others0. apply notin_callstack_cons; auto.
  (* cs_nextblock *)
  simpl. auto.
  (* cs_dom *)
  simpl. apply callstack_dom_incr with sp; auto.
Qed.

(** Finally, [callstack_invariant] holds for the initial memory states
  in the two semantics. *)

Lemma callstack_init:
  forall (p: program),
  callstack_invariant ((empty_frame, nullptr, Int.zero) :: nil) 
                      (Genv.init_mem p) (Genv.init_mem p).
Proof.
  intros.
  generalize (Genv.initmem_nullptr p). intros [A B].
  constructor.
  (* cs_frame *)
  intros. elim H; intro.
  injection H0; intros; subst fr; subst sp; subst base.
  constructor.
  assumption.
  unfold low_bound. rewrite B. reflexivity.
  unfold low_bound, empty_frame. rewrite B. reflexivity.
  unfold high_bound. rewrite B. reflexivity.
  simpl. omega.
  simpl. compute. intuition congruence.
  reflexivity.
  rewrite B. unfold empty_frame. simpl. hnf. auto.
  rewrite B. hnf. auto.
  elim H0.
  (* cs_linked *)
  apply callstack_linked_one.
  (* cs_others *)
  auto.
  (* cs_nextblock *)
  reflexivity.
  (* cs_dom *)
  constructor. exact A. constructor.
Qed.

(** Preservation of arguments to external functions. *)

Lemma transl_extcall_arguments:
  forall rs fr sg args stk base cs m ms,
  Machabstr.extcall_arguments rs fr sg args ->
  callstack_invariant ((fr, stk, base) :: cs) m ms ->
  wt_frame fr ->
  extcall_arguments rs ms (Vptr stk base) sg args.
Proof.
  unfold Machabstr.extcall_arguments, extcall_arguments; intros.
  assert (forall locs vals,
    Machabstr.extcall_args rs fr locs vals ->
    extcall_args rs ms (Vptr stk base) locs vals).
  induction locs; intros; inversion H2; subst; clear H2.
  constructor.
  constructor; auto.
  inversion H7; subst; clear H7. 
  constructor.
  constructor. eapply callstack_get_slot; eauto. 
  eapply wt_get_slot; eauto. 
  auto.
Qed.

(** * The proof of simulation *)

Section SIMULATION.

Variable p: program.
Hypothesis wt_p: wt_program p.
Let ge := Genv.globalenv p.

(** The proof of simulation relies on diagrams of the following form:
<<
     sp, parent, c, rs, fr, mm ----------- sp, c, rs, ms
                 |                              |
                 |                              |
                 v                              v
   sp, parent, c', rs', fr', mm' --------  sp, c', rs', ms'
>>
  The left vertical arrow is a transition in the abstract semantics.
  The right vertical arrow is a transition in the concrete semantics.
  The precondition (top horizontal line) is the appropriate
  [callstack_invariant] property between the initial memory states
  [mm] and [ms] and any call stack with [fr] as top frame and
  [parent] as second frame.  In addition, well-typedness conditions
  over the code [c], the register [rs] and the frame [fr] are demanded.
  The postcondition (bottom horizontal line) is [callstack_invariant]
  between the final memory states [mm'] and [ms'] and the final
  call stack.
*)

Definition exec_instr_prop
    (f: function) (sp: val) (parent: frame)
    (c: code) (rs: regset) (fr: frame) (mm: mem) (t: trace)
    (c': code) (rs': regset) (fr': frame) (mm': mem) : Prop :=
  forall ms stk base pstk pbase cs
         (WTF: wt_function f)
         (INCL: incl c f.(fn_code))
         (WTRS: wt_regset rs)
         (WTFR: wt_frame fr)
         (WTPA: wt_frame parent)
         (CSI: callstack_invariant ((fr, stk, base) :: (parent, pstk, pbase) :: cs) mm ms)
         (SP: sp = Vptr stk base),
  exists ms',
    exec_instr ge f sp c rs ms t c' rs' ms' /\
    callstack_invariant ((fr', stk, base) :: (parent, pstk, pbase) :: cs) mm' ms'.

Definition exec_instrs_prop
    (f: function) (sp: val) (parent: frame)
    (c: code) (rs: regset) (fr: frame) (mm: mem) (t: trace)
    (c': code) (rs': regset) (fr': frame) (mm': mem) : Prop :=
  forall ms stk base pstk pbase cs
         (WTF: wt_function f)
         (INCL: incl c f.(fn_code))
         (WTRS: wt_regset rs)
         (WTFR: wt_frame fr)
         (WTPA: wt_frame parent)
         (CSI: callstack_invariant ((fr, stk, base) :: (parent, pstk, pbase) :: cs) mm ms)
         (SP: sp = Vptr stk base),
  exists ms',
    exec_instrs ge f sp c rs ms t c' rs' ms' /\
    callstack_invariant ((fr', stk, base) :: (parent, pstk, pbase) :: cs) mm' ms'.

Definition exec_function_body_prop
    (f: function) (parent: frame) (link ra: val)
    (rs: regset) (mm: mem) (t: trace)
    (rs': regset) (mm': mem) : Prop :=
  forall ms pstk pbase cs
         (WTF: wt_function f)
         (WTRS: wt_regset rs)
         (WTPA: wt_frame parent)
         (WTRA: Val.has_type ra Tint)
         (LINK: link = Vptr pstk pbase)
         (CSI: callstack_invariant ((parent, pstk, pbase) :: cs) mm ms),
  exists ms',
    exec_function_body ge f (Vptr pstk pbase) ra rs ms t rs' ms' /\
    callstack_invariant ((parent, pstk, pbase) :: cs) mm' ms'.

Definition exec_function_prop
    (f: fundef) (parent: frame)
    (rs: regset) (mm: mem) (t: trace)
    (rs': regset) (mm': mem) : Prop :=
  forall ms pstk pbase cs
         (WTF: wt_fundef f)
         (WTRS: wt_regset rs)
         (WTPA: wt_frame parent)
         (CSI: callstack_invariant ((parent, pstk, pbase) :: cs) mm ms),
  exists ms',
    exec_function ge f (Vptr pstk pbase) rs ms t rs' ms' /\
    callstack_invariant ((parent, pstk, pbase) :: cs) mm' ms'.

Lemma exec_function_equiv:
  forall f parent rs mm t rs' mm',
  Machabstr.exec_function ge f parent rs mm t rs' mm' ->
  exec_function_prop f parent rs mm t rs' mm'.
Proof.
  apply (Machabstr.exec_function_ind4 ge
           exec_instr_prop
           exec_instrs_prop
           exec_function_body_prop
           exec_function_prop);
  intros; red; intros.

  (* Mlabel *)
  exists ms. split. constructor. auto.
  (* Mgetstack *)
  exists ms. split. 
  constructor. rewrite SP. eapply callstack_get_slot; eauto. 
  apply wt_get_slot with fr (Int.signed ofs); auto.
  auto.
  (* Msetstack *)
  generalize (wt_function_instrs f WTF _ (INCL _ (in_eq _ _))).
  intro WTI. inversion WTI.
  assert (4 <= Int.signed ofs). omega. 
  generalize (callstack_set_slot _ _ _ _ _ _ _ _ _ _ CSI H H5).
  intros [ms' [STO CSI']].
  exists ms'. split. constructor. rewrite SP. auto. auto.
  (* Mgetparam *)
  exists ms. split. 
  assert (WTV: Val.has_type v ty). eapply wt_get_slot; eauto.
  generalize (callstack_get_parent _ _ _ _ _ _ _ _ _ _ _ _
                CSI H WTV).
  intros [L1 L2].
  eapply exec_Mgetparam. rewrite SP; eexact L1. eexact L2.
  auto.
  (* Mop *)
  exists ms. split. constructor. auto. auto.
  (* Mload *)
  exists ms. split. econstructor. eauto. eapply callstack_load; eauto.
  auto.
  (* Mstore *)
  generalize (callstack_store _ _ _ _ _ _ _ CSI H0).
  intros [ms' [STO CSI']].
  exists ms'. split. econstructor. eauto. auto.
  auto. 
  (* Mcall *)
  red in H1. 
  assert (WTF': wt_fundef f').
    destruct ros; simpl in H.
    apply (Genv.find_funct_prop wt_fundef wt_p H).
    destruct (Genv.find_symbol ge i); try discriminate.
    apply (Genv.find_funct_ptr_prop wt_fundef wt_p H).
  generalize (H1 _ _ _ _ WTF' WTRS WTFR CSI). 
  intros [ms' [EXF CSI']].
  exists ms'. split. apply exec_Mcall with f'; auto. 
  rewrite SP. auto.
  auto.
  (* Malloc *)
  generalize (callstack_alloc _ _ _ _ _ _ _ CSI H0). 
  intros [ms' [ALLOC' CSI']].
  exists ms'; split.
  eapply exec_Malloc; eauto.
  auto.
  (* Mgoto *)
  exists ms. split. constructor; auto. auto.
  (* Mcond *)
  exists ms. split. apply exec_Mcond_true; auto. auto.
  exists ms. split. apply exec_Mcond_false; auto. auto.

  (* refl *)
  exists ms. split. apply exec_refl. auto.
  (* one *)
  generalize (H0 _ _ _ _ _ _ WTF INCL WTRS WTFR WTPA CSI SP).
  intros [ms' [EX CSI']].
  exists ms'. split. apply exec_one; auto. auto.
  (* trans *)
  generalize (subject_reduction_instrs p wt_p 
               _ _ _ _ _ _ _ _ _ _ _ _ H WTF INCL WTRS WTFR WTPA).
  intros [INCL2 [WTRS2 WTFR2]].
  generalize (H0 _ _ _ _ _ _ WTF INCL WTRS WTFR WTPA CSI SP).
  intros [ms1 [EX1 CSI1]].
  generalize (H2 _ _ _ _ _ _ WTF INCL2 WTRS2 WTFR2 WTPA CSI1 SP).
  intros [ms2 [EX2 CSI2]].
  exists ms2. split. eapply exec_trans; eauto. auto.

  (* function body *)
  caseEq (alloc ms (- f.(fn_framesize))
                   (align_16_top (- f.(fn_framesize)) f.(fn_stacksize))).
  intros ms1 stk1 ALL.
  subst link.
  assert (FS: f.(fn_framesize) >= 0).
    generalize (wt_function_framesize f WTF). omega.
  generalize (callstack_function_entry _ _ _ _ _ _ _ _ _ _ _ _
               CSI H ALL FS
               (wt_function_no_overflow f WTF) H0).
  intros [ms2 [STORELINK [CSI2 EQ]]].
  subst stk1.
  assert (ZERO: Int.signed (Int.repr 0) = 0). reflexivity.
  assert (TWELVE: Int.signed (Int.repr 12) = 12). reflexivity.
  assert (BND: 4 <= Int.signed (Int.repr 12)).
    rewrite TWELVE; omega.
  rewrite <- TWELVE in H1.
  generalize (callstack_set_slot _ _ _ _ _ _ _ _ _ _
               CSI2 H1 BND).
  intros [ms3 [STORERA CSI3]].
  assert (WTFR2: wt_frame fr2).
    eapply wt_set_slot; eauto. eapply wt_set_slot; eauto.
    red. intros. simpl. auto. 
    exact I. 
  red in H3.
  generalize (H3 _ _ _ _ _ _ WTF (incl_refl _) WTRS WTFR2 WTPA
                CSI3 (refl_equal _)).
  intros [ms4 [EXEC CSI4]].
  generalize (exec_instrs_link_invariant _ _ _ _ _ _ _ _ _ _ _ _ _
                H2 WTF (incl_refl _)).
  intros [INCL LINKINV].
  exists (free ms4 stk). split.
  eapply exec_funct_body; eauto.
  eapply callstack_get_slot. eexact CSI4.
  apply LINKINV. rewrite ZERO. omega. 
  eapply slot_gso; eauto. rewrite ZERO. eapply slot_gss; eauto. 
  exact I. 
  eapply callstack_get_slot. eexact CSI4.
  apply LINKINV. rewrite TWELVE. omega. eapply slot_gss; eauto. auto.
  eapply callstack_function_return; eauto.

  (* internal function *)
  inversion WTF. subst f0. 
  generalize (H0 (Vptr pstk pbase) Vzero I I
                 ms pstk pbase cs H2 WTRS WTPA I (refl_equal _) CSI).
  intros [ms' [EXEC CSI']].
  exists ms'. split. constructor. intros.
  generalize (H0 (Vptr pstk pbase) ra I H1 
                ms pstk pbase cs H2 WTRS WTPA H1 (refl_equal _) CSI).
  intros [ms1 [EXEC1 CSI1]].
  rewrite (callstack_exten _ _ _ _ CSI' CSI1). auto.
  auto.

  (* external function *)
  exists ms; split. econstructor; eauto. 
  eapply transl_extcall_arguments; eauto.
  auto.
Qed.  

End SIMULATION.

Theorem exec_program_equiv:
  forall p t r, 
  wt_program p ->
  Machabstr.exec_program p t r -> 
  Mach.exec_program p t r.
Proof.
  intros p t r WTP [fptr [f [rs [mm [FINDPTR [FINDF [EXEC RES]]]]]]].
  assert (WTF: wt_fundef f).
    apply (Genv.find_funct_ptr_prop wt_fundef WTP FINDF).
  assert (WTRS: wt_regset (Regmap.init Vundef)).
    red; intros. rewrite Regmap.gi; simpl; auto.
  assert (WTFR: wt_frame empty_frame).
    red; intros. simpl. auto.
  generalize (exec_function_equiv p WTP
                f empty_frame
                (Regmap.init Vundef) (Genv.init_mem p) t rs mm
                EXEC (Genv.init_mem p) nullptr Int.zero nil
                WTF WTRS WTFR (callstack_init p)).
  intros [ms' [EXEC' CSI]].
  red. exists fptr; exists f; exists rs; exists ms'. tauto.
Qed.
