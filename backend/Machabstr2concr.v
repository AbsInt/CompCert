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
Require Import Stackingproof.
Require Import PPCgenretaddr.

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

Remark size_type_chunk:
  forall ty, size_chunk (chunk_of_type ty) = AST.typesize ty.
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

Inductive frame_match (fr: frame) (sp: block) (base: int) 
                      (mm ms: mem) : Prop :=
  frame_match_intro:
    valid_block ms sp ->
    low_bound mm sp = 0 ->
    low_bound ms sp = fr.(fr_low) ->
    high_bound ms sp >= 0 ->
    fr.(fr_low) <= -24 ->
    Int.min_signed <= fr.(fr_low) ->
    base = Int.repr fr.(fr_low) ->
    (forall ty ofs,
       fr.(fr_low) + 24 <= ofs -> ofs + AST.typesize ty <= 0 ->
       load (chunk_of_type ty) ms sp ofs = Some(fr.(fr_contents) ty ofs)) ->
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

Lemma frame_match_get_slot:
  forall fr sp base mm ms ty ofs v,
  frame_match fr sp base mm ms ->
  get_slot fr ty (Int.signed ofs) v ->
  load_stack ms (Vptr sp base) ty ofs = Some v.
Proof.
  intros. inv H. inv H0. 
  unfold load_stack, Val.add, loadv. 
  assert (Int.signed (Int.repr (fr_low fr)) = fr_low fr).
    apply Int.signed_repr.
    split. auto. apply Zle_trans with (-24). auto. compute; congruence.
  assert (Int.signed (Int.add (Int.repr (fr_low fr)) ofs) = fr_low fr + Int.signed ofs).
    rewrite int_add_no_overflow. rewrite H0. auto.
    rewrite H0. split. omega. apply Zle_trans with 0.
    generalize (AST.typesize_pos ty). omega. compute; congruence.
  rewrite H9. apply H8. omega. auto.
Qed.

(** Assigning a value to a frame slot (in the abstract semantics)
  corresponds to storing this value in the activation record
  (in the concrete semantics).  Moreover, agreement between frames
  and activation records is preserved. *)

Lemma frame_match_set_slot:
  forall fr sp base mm ms ty ofs v fr',
  frame_match fr sp base mm ms ->
  set_slot fr ty (Int.signed ofs) v fr' ->
  Val.has_type v ty ->
  Mem.extends mm ms ->
  exists ms',
    store_stack ms (Vptr sp base) ty ofs v = Some ms' /\
    frame_match fr' sp base mm ms' /\
    Mem.extends mm ms' /\
    Int.signed base + 24 <= Int.signed (Int.add base ofs).
Proof.
  intros. inv H. inv H0.
  unfold store_stack, Val.add, storev.
  assert (Int.signed (Int.repr (fr_low fr)) = fr_low fr).
    apply Int.signed_repr.
    split. auto. apply Zle_trans with (-24). auto. compute; congruence.
  assert (Int.signed (Int.add (Int.repr (fr_low fr)) ofs) = fr_low fr + Int.signed ofs).
    rewrite int_add_no_overflow. congruence. 
    rewrite H0. split. omega. apply Zle_trans with 0.
    generalize (AST.typesize_pos ty). omega. compute; congruence.
  rewrite H11.
  assert (exists ms', store (chunk_of_type ty) ms sp (fr_low fr + Int.signed ofs) v = Some ms').
    apply valid_access_store. 
    constructor. auto. omega.
    rewrite size_type_chunk. omega.
  destruct H12 as [ms' STORE]. 
  generalize (low_bound_store _ _ _ _ _ _ STORE sp). intro LB.
  generalize (high_bound_store _ _ _ _ _ _ STORE sp). intro HB.
  exists ms'. 
  split. exact STORE.
  (* frame match *)
  split. constructor; simpl fr_low; try congruence.
    eauto with mem. intros. simpl.
    destruct (zeq (fr_low fr + Int.signed ofs) ofs0). subst ofs0.
    destruct (typ_eq ty ty0). subst ty0.
    (* same *)
    transitivity (Some (Val.load_result (chunk_of_type ty) v)).
    eapply load_store_same; eauto.
    decEq. apply load_result_ty; auto.
    (* mismatch *)
    eapply load_store_mismatch'; eauto with mem.
    destruct ty; destruct ty0; simpl; congruence.
    destruct (zle (ofs0 + AST.typesize ty0) (fr_low fr + Int.signed ofs)).
    (* disjoint *)
    rewrite <- H10; auto. eapply load_store_other; eauto.
    right; left. rewrite size_type_chunk; auto.
    destruct (zle (fr_low fr + Int.signed ofs + AST.typesize ty)).
    rewrite <- H10; auto. eapply load_store_other; eauto.
    right; right. rewrite size_type_chunk; auto.
    (* overlap *)
    eapply load_store_overlap'; eauto with mem.
    rewrite size_type_chunk; auto. 
    rewrite size_type_chunk; auto.
  (* extends *)
  split. eapply store_outside_extends; eauto.
  left. rewrite size_type_chunk. omega.
  (* bound *)
  omega.
Qed.

(** Agreement is preserved by stores within blocks other than the
  one pointed to by [sp], or to the low 24 bytes
  of the [sp] block. *)

Lemma frame_match_store_other:
  forall fr sp base mm ms chunk b ofs v ms',
  frame_match fr sp base mm ms ->
  store chunk ms b ofs v = Some ms' ->
  sp <> b \/ ofs + size_chunk chunk <= fr_low fr + 24 ->
  frame_match fr sp base mm ms'.
Proof.
  intros. inv H. 
  generalize (low_bound_store _ _ _ _ _ _ H0 sp). intro LB.
  generalize (high_bound_store _ _ _ _ _ _ H0 sp). intro HB.
  apply frame_match_intro; auto.
  eauto with mem. 
  congruence.
  congruence.
  intros. rewrite <- H9; auto. 
  eapply load_store_other; eauto.
  elim H1; intro. auto. right. rewrite size_type_chunk. omega. 
Qed.

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
  intros. rewrite <- H9; auto. eapply load_store_other; eauto.
  destruct (zeq sp b). subst b. right. 
  rewrite size_type_chunk. 
  assert (valid_access mm chunk sp ofs) by eauto with mem.
  inv H10. left. omega.
  auto.
Qed.

(** The low 24 bytes of a frame are preserved by a parallel
    store in the two memory states. *)

Lemma frame_match_store_link_invariant:
  forall fr sp base mm ms chunk b ofs v mm' ms' ofs',
  frame_match fr sp base mm ms ->
  store chunk mm b ofs v = Some mm' ->
  store chunk ms b ofs v = Some ms' ->
  ofs' <= fr_low fr + 20 -> 
  load Mint32 ms' sp ofs' = load Mint32 ms sp ofs'.
Proof.
  intros. inv H.
  eapply load_store_other; eauto.
  destruct (eq_block sp b). subst b.
  right; left. change (size_chunk Mint32) with 4. 
  assert (valid_access mm chunk sp ofs) by eauto with mem.
  inv H. omega. 
  auto.
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
  f.(fn_framesize) >= 24 ->
  f.(fn_framesize) <= -Int.min_signed ->
  sp = sp' /\
  frame_match (init_frame f) sp (Int.repr (-f.(fn_framesize))) mm' ms'.
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
  constructor; simpl; eauto with mem.
  rewrite HBs. apply Zle_ge. apply align_16_top_pos.
  omega. omega.
  intros.
  eapply load_alloc_same'; eauto. omega. 
  rewrite size_type_chunk. apply Zle_trans with 0. auto.
  apply align_16_top_pos.
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
  exploit low_bound_alloc_other. eexact H1. eexact H11. intro LBm.
  exploit high_bound_alloc_other. eexact H1. eexact H11. intro HBm.
  exploit low_bound_alloc_other. eexact H2. eexact H3. intro LBs.
  exploit high_bound_alloc_other. eexact H2. eexact H3. intro HBs.
  apply frame_match_intro.
  eapply valid_block_alloc; eauto.
  congruence. congruence. congruence. auto. auto. auto. 
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
  intros. rewrite <- H8; auto. apply load_free. auto.
Qed.

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

Inductive match_stacks: 
      list Machabstr.stackframe -> list Machconcr.stackframe ->
      block -> int -> mem -> mem -> Prop :=
  | match_stacks_nil: forall sp base mm ms,
      load Mint32 ms sp (Int.signed base) = Some (Vptr Mem.nullptr Int.zero) ->
      load Mint32 ms sp (Int.signed base + 12) = Some Vzero ->
      match_stacks nil nil sp base mm ms
  | match_stacks_cons: forall f sp' base' c fr s fb ra ts sp base mm ms,
      frame_match fr sp' base' mm ms ->
      sp' < sp ->
      load Mint32 ms sp (Int.signed base) = Some (Vptr sp' base') ->
      load Mint32 ms sp (Int.signed base + 12) = Some ra ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      match_stacks s ts sp' base' mm ms ->
      match_stacks (Machabstr.Stackframe f (Vptr sp' base') c fr :: s)
                   (Machconcr.Stackframe fb (Vptr sp' base') ra c :: ts)
                   sp base mm ms.

Remark frame_match_base_eq:
  forall fr sp base mm ms,
  frame_match fr sp base mm ms -> Int.signed base = fr_low fr.
Proof.
  intros. inv H. apply Int.signed_repr. split; auto.
  apply Zle_trans with (-24); auto. compute; congruence.
Qed.

(** If [match_stacks] holds, a lookup in the parent frame in the
  Machabstr semantics corresponds to two memory loads in the
  Machconcr semantics, one to load the pointer to the parent's
  activation record, the second to read within this record. *)

Lemma match_stacks_get_parent:
  forall s ts sp base mm ms ty ofs v,
  match_stacks s ts sp base mm ms ->
  get_slot (parent_frame s) ty (Int.signed ofs) v ->
  exists parent,
     load_stack ms (Vptr sp base) Tint (Int.repr 0) = Some parent
  /\ load_stack ms parent ty ofs = Some v.
Proof.
  intros. inv H; simpl in H0. 
  inv H0. simpl in H3. elimtype False. generalize (AST.typesize_pos ty). omega.
  exists (Vptr sp' base'); split.
  unfold load_stack. simpl. rewrite Int.add_zero. auto.
  eapply frame_match_get_slot; eauto.
Qed.

(** If [match_stacks] holds, reading memory at offsets 0 and 12
  from the stack pointer returns the stack pointer and return
  address of the caller, respectively. *)

Lemma match_stacks_load_links:
  forall fr s ts sp base mm ms,
  frame_match fr sp base mm ms ->
  match_stacks s ts sp base mm ms ->
  load_stack ms (Vptr sp base) Tint (Int.repr 0) = Some (parent_sp ts) /\
  load_stack ms (Vptr sp base) Tint (Int.repr 12) = Some (parent_ra ts).
Proof.
  intros. unfold load_stack. simpl. rewrite Int.add_zero.
  replace (Int.signed (Int.add base (Int.repr 12)))
     with (Int.signed base + 12).
  inv H0; simpl; auto.
  inv H. rewrite Int.add_signed. 
  change (Int.signed (Int.repr 12)) with 12.
  repeat rewrite Int.signed_repr. auto.
  split. omega. apply Zle_trans with (-12). omega. compute; congruence.
  split. auto. apply Zle_trans with (-24). auto. compute; congruence.
Qed.

(** The [match_stacks] invariant is preserved by memory stores
  outside the 24-byte reserved area at the bottom of activation records.
*)

Lemma match_stacks_store_other:
  forall s ts sp base ms mm,
  match_stacks s ts sp base mm ms ->
  forall chunk b ofs v ms',
  store chunk ms b ofs v = Some ms' ->
  sp < b ->
  match_stacks s ts sp base mm ms'.
Proof.
  induction 1; intros.
  assert (sp <> b). unfold block; omega.
  constructor.
  rewrite <- H. eapply load_store_other; eauto.
  rewrite <- H0. eapply load_store_other; eauto.
  assert (sp <> b). unfold block; omega.
  econstructor; eauto.
  eapply frame_match_store_other; eauto.
  left. unfold block; omega.
  rewrite <- H1. eapply load_store_other; eauto.
  rewrite <- H2. eapply load_store_other; eauto.
  eapply IHmatch_stacks; eauto. omega.
Qed.

Lemma match_stacks_store_slot:
  forall s ts sp base ms mm,
  match_stacks s ts sp base mm ms ->
  forall ty ofs v ms',
  store_stack ms (Vptr sp base) ty ofs v = Some ms' ->
  Int.signed base + 24 <= Int.signed (Int.add base ofs) ->
  match_stacks s ts sp base mm ms'.
Proof.
  intros.
  unfold store_stack in H0. simpl in H0. 
  assert (load Mint32 ms' sp (Int.signed base) = load Mint32 ms sp (Int.signed base)).
  eapply load_store_other; eauto.
  right; left. change (size_chunk Mint32) with 4; omega.
  assert (load Mint32 ms' sp (Int.signed base + 12) = load Mint32 ms sp (Int.signed base + 12)).
  eapply load_store_other; eauto.
  right; left. change (size_chunk Mint32) with 4; omega.
  inv H.
  constructor; congruence.
  constructor; auto.
  eapply frame_match_store_other; eauto.
  left; unfold block; omega.
  congruence. congruence.
  eapply match_stacks_store_other; eauto. 
Qed.

Lemma match_stacks_store:
  forall s ts sp base ms mm,
  match_stacks s ts sp base mm ms ->
  forall fr chunk b ofs v mm' ms',
  frame_match fr sp base mm ms ->
  store chunk mm b ofs v = Some mm' ->
  store chunk ms b ofs v = Some ms' ->
  match_stacks s ts sp base mm' ms'.
Proof.
  induction 1; intros.
  assert (Int.signed base = fr_low fr) by (eapply frame_match_base_eq; eauto).
  constructor.
  rewrite <- H. eapply frame_match_store_link_invariant; eauto. omega.
  rewrite <- H0. eapply frame_match_store_link_invariant; eauto. omega.
  assert (Int.signed base = fr_low fr0) by (eapply frame_match_base_eq; eauto).
  econstructor; eauto.
  eapply frame_match_store; eauto. 
  rewrite <- H1. eapply frame_match_store_link_invariant; eauto. omega.
  rewrite <- H2. eapply frame_match_store_link_invariant; eauto. omega.
Qed.

Lemma match_stacks_alloc:
  forall s ts sp base ms mm,
  match_stacks s ts sp base mm ms ->
  forall lom him mm' bm los his ms' bs,
  mm.(nextblock) = ms.(nextblock) ->
  alloc mm lom him = (mm', bm) ->
  alloc ms los his = (ms', bs) ->
  match_stacks s ts sp base mm' ms'.
Proof.
  induction 1; intros.
  constructor.
  rewrite <- H; eapply load_alloc_unchanged; eauto with mem.
  rewrite <- H0; eapply load_alloc_unchanged; eauto with mem.
  econstructor; eauto.
  eapply frame_match_alloc; eauto.
  rewrite <- H1; eapply load_alloc_unchanged; eauto with mem.
  rewrite <- H2; eapply load_alloc_unchanged; eauto with mem.
Qed.

Lemma match_stacks_free:
  forall s ts sp base ms mm,
  match_stacks s ts sp base mm ms ->
  forall b,
  sp < b ->
  match_stacks s ts sp base (Mem.free mm b) (Mem.free ms b).
Proof.
  induction 1; intros.
  assert (sp <> b). unfold block; omega.
  constructor.
  rewrite <- H. apply load_free; auto.
  rewrite <- H0. apply load_free; auto.
  assert (sp <> b). unfold block; omega.
  econstructor; eauto.
  eapply frame_match_free; eauto. unfold block; omega.
  rewrite <- H1. apply load_free; auto.
  rewrite <- H2. apply load_free; auto.
  eapply IHmatch_stacks; eauto. omega.
Qed.

(** Invocation of a function temporarily violates the [mach_stacks]
  invariant: the return address and back link are not yet stored
  in the appropriate parts of the activation record.  
  The following [match_stacks_partial] predicate is a weaker version
  of [match_stacks] that captures this situation. *)

Inductive match_stacks_partial: 
      list Machabstr.stackframe -> list Machconcr.stackframe ->
      mem -> mem -> Prop :=
  | match_stacks_partial_nil: forall mm ms,
      match_stacks_partial nil nil mm ms
  | match_stacks_partial_cons: forall f sp base c fr s fb ra ts mm ms,
      frame_match fr sp base mm ms ->
      sp < ms.(nextblock) ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      match_stacks s ts sp base mm ms ->
      Val.has_type ra Tint ->
      match_stacks_partial (Machabstr.Stackframe f (Vptr sp base) c fr :: s)
                           (Machconcr.Stackframe fb (Vptr sp base) ra c :: ts)
                           mm ms.

Lemma match_stacks_match_stacks_partial:
  forall s ts sp base mm ms,
  match_stacks s ts sp base mm ms ->
  match_stacks_partial s ts (free mm sp) (free ms sp).
Proof.
  intros. inv H. constructor.
  econstructor. 
  eapply frame_match_free; eauto. unfold block; omega.
  simpl. inv H0; auto.
  auto.
  apply match_stacks_free; auto.
  generalize (Mem.load_inv _ _ _ _ _ H3). intros [A B].
  rewrite B.
  destruct (getN (pred_size_chunk Mint32) (Int.signed base + 12)
                 (contents (blocks ms sp))); exact I.
Qed.

Lemma match_stacks_function_entry:
  forall s ts mm ms lom him mm' los his ms' stk ms'' ms''' base,
  match_stacks_partial s ts mm ms ->
  alloc mm lom him = (mm', stk) ->
  alloc ms los his = (ms', stk) ->
  store Mint32 ms' stk (Int.signed base) (parent_sp ts) = Some ms'' ->
  store Mint32 ms'' stk (Int.signed base + 12) (parent_ra ts) = Some ms''' ->
  match_stacks s ts stk base mm' ms'''.
Proof.
  intros. 
  assert (WT_SP: Val.has_type (parent_sp ts) Tint).
    inv H; simpl; auto.
  assert (WT_RA: Val.has_type (parent_ra ts) Tint).
    inv H; simpl; auto.
  assert (load Mint32 ms''' stk (Int.signed base) = Some (parent_sp ts)).
    transitivity (load Mint32 ms'' stk (Int.signed base)).
    eapply load_store_other; eauto. right; left. simpl. omega.
    transitivity (Some (Val.load_result (chunk_of_type Tint) (parent_sp ts))).
    simpl chunk_of_type. eapply load_store_same; eauto. 
    decEq. apply load_result_ty. auto.
  assert (load Mint32 ms''' stk (Int.signed base + 12) = Some (parent_ra ts)).
    transitivity (Some (Val.load_result (chunk_of_type Tint) (parent_ra ts))).
    simpl chunk_of_type. eapply load_store_same; eauto. 
    decEq. apply load_result_ty. auto.
  inv H; simpl in *.
  constructor; auto.
  assert (sp < stk). rewrite (alloc_result _ _ _ _ _ H1). auto.
  assert (sp <> stk). unfold block; omega.
  assert (nextblock mm = nextblock ms).
  rewrite <- (alloc_result _ _ _ _ _ H0). 
  rewrite <- (alloc_result _ _ _ _ _ H1). auto.
  econstructor; eauto.
  eapply frame_match_store_other; eauto. 
  eapply frame_match_store_other; eauto.
  eapply frame_match_alloc with (mm := mm) (ms := ms); eauto.
  eapply match_stacks_store_other; eauto. 
  eapply match_stacks_store_other; eauto.
  eapply match_stacks_alloc with (mm := mm) (ms := ms); eauto.
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
        (STACKS: match_stacks s ts sp base mm ms)
        (FM: frame_match fr sp base mm ms)
        (MEXT: Mem.extends mm ms)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f)),
      match_states (Machabstr.State s f (Vptr sp base) c rs fr mm)
                   (Machconcr.State ts fb (Vptr sp base) c rs ms)
  | match_states_call:
      forall s f rs mm ts fb ms
        (STACKS: match_stacks_partial s ts mm ms)
        (MEXT: Mem.extends mm ms)
        (FIND: Genv.find_funct_ptr ge fb = Some f),
      match_states (Machabstr.Callstate s f rs mm)
                   (Machconcr.Callstate ts fb rs ms)
  | match_states_return:
      forall s rs mm ts ms
        (STACKS: match_stacks_partial s ts mm ms)
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
  Machabstr.extcall_arguments rs (parent_frame s) sg args ->
  match_stacks_partial s ts m ms ->
  extcall_arguments rs ms (parent_sp ts) sg args.
Proof.
  unfold Machabstr.extcall_arguments, extcall_arguments; intros.
  assert (forall ty ofs v,
    get_slot (parent_frame s) ty (Int.signed ofs) v ->
    load_stack ms (parent_sp ts) ty ofs = Some v).
  inv H0; simpl; intros.
  inv H0. simpl in H2. elimtype False. generalize (AST.typesize_pos ty). omega.
  eapply frame_match_get_slot; eauto.
  assert (forall locs vals,
    Machabstr.extcall_args rs (parent_frame s) locs vals ->
    extcall_args rs ms (parent_sp ts) locs vals).
  induction locs; intros; inversion H2; subst; clear H2.
  constructor.
  constructor; auto.
  inversion H7; subst; clear H7. 
  constructor.
  constructor. auto.  
  auto.
Qed.

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
  exists (State ts fb (Vptr sp0 base) c (rs#dst <- v) ms); split.
  apply exec_Mgetstack; auto. eapply frame_match_get_slot; eauto.
  econstructor; eauto with coqlib.

  (* Msetstack *)
  assert (Val.has_type (rs src) ty).
    inv WTS. 
    generalize (wt_function_instrs _ WTF _ (is_tail_in TAIL)); intro WTI.
    inv WTI. apply WTRS.
  exploit frame_match_set_slot; eauto. 
  intros [ms' [STORE [FM' [EXT' BOUND]]]].
  exists (State ts fb (Vptr sp0 base) c rs ms'); split.
  apply exec_Msetstack; auto.
  econstructor; eauto.
  eapply match_stacks_store_slot; eauto.

  (* Mgetparam *)
  exploit match_stacks_get_parent; eauto. 
  intros [parent [LOAD1 LOAD2]].
  exists (State ts fb (Vptr sp0 base) c (rs#dst <- v) ms); split.
  eapply exec_Mgetparam; eauto. 
  econstructor; eauto with coqlib. 
 
  (* Mop *)
  exists (State ts fb (Vptr sp0 base) c (rs#res <- v) ms); split.
  apply exec_Mop; auto.
  eapply eval_operation_change_mem with (m := m); eauto.
  intros. eapply Mem.valid_pointer_extends; eauto.
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
  econstructor; eauto. inv FM; auto. exact I.  

  (* Mtailcall *)
  exploit find_function_find_function_ptr; eauto. 
  intros [fb' [FIND' FINDFUNCT]].
  exploit match_stacks_load_links; eauto. intros [LOAD1 LOAD2].
  econstructor; split.
  eapply exec_Mtailcall; eauto.
  econstructor; eauto.
  eapply match_stacks_match_stacks_partial; eauto. 
  apply free_extends; auto.

  (* Malloc *)
  caseEq (alloc ms 0 (Int.signed sz)). intros ms' blk' ALLOC.
  exploit alloc_extends; eauto. omega. omega. intros [EQ MEXT']. subst blk'.
  exists (State ts fb (Vptr sp0 base) c (rs#Conventions.loc_alloc_result <- (Vptr blk Int.zero)) ms'); split.
  eapply exec_Malloc; eauto.
  econstructor; eauto.
  eapply match_stacks_alloc; eauto. inv MEXT; auto. 
  eapply frame_match_alloc with (mm := m) (ms := ms); eauto. inv MEXT; auto.

  (* Mgoto *)
  econstructor; split.
  eapply exec_Mgoto; eauto.
  econstructor; eauto.

  (* Mcond *)
  econstructor; split.
  eapply exec_Mcond_true; eauto.
  eapply eval_condition_change_mem with (m := m); eauto.
  intros. eapply Mem.valid_pointer_extends; eauto.
  econstructor; eauto.
  econstructor; split.
  eapply exec_Mcond_false; eauto.
  eapply eval_condition_change_mem with (m := m); eauto.
  intros. eapply Mem.valid_pointer_extends; eauto.
  econstructor; eauto.

  (* Mreturn *)
  exploit match_stacks_load_links; eauto. intros [LOAD1 LOAD2].
  econstructor; split.
  eapply exec_Mreturn; eauto.
  econstructor; eauto.  
  eapply match_stacks_match_stacks_partial; eauto. 
  apply free_extends; auto.

  (* internal function *)
  assert (WTF: wt_function f). inv WTS. inv H5. auto. inv WTF.
  caseEq (alloc ms (- f.(fn_framesize))
                   (align_16_top (- f.(fn_framesize)) f.(fn_stacksize))).
  intros ms' stk' ALLOC.
  exploit (alloc_extends m ms m' ms' 0 (fn_stacksize f)
               (- fn_framesize f)
               (align_16_top (- fn_framesize f) (fn_stacksize f))); eauto.
  omega. apply align_16_top_ge. 
  intros [EQ EXT']. subst stk'.
  exploit (frame_match_new m ms); eauto. inv MEXT; auto.
  intros [EQ FM]. clear EQ.
  set (sp := Vptr stk (Int.repr (- fn_framesize f))).
  assert (exists ms'', store Mint32 ms' stk (- fn_framesize f) (parent_sp ts) = Some ms'').
    apply valid_access_store. constructor. 
    eauto with mem.
    rewrite (low_bound_alloc_same _ _ _ _ _ ALLOC). omega.
    rewrite (high_bound_alloc_same _ _ _ _ _ ALLOC).
    change (size_chunk Mint32) with 4. 
    apply Zle_trans with 0. omega. apply align_16_top_pos.
  destruct H0 as [ms'' STORE1].
  assert (exists ms''', store Mint32 ms'' stk (- fn_framesize f + 12) (parent_ra ts) = Some ms''').
    apply valid_access_store. constructor. 
    eauto with mem.
    rewrite (low_bound_store _ _ _ _ _ _ STORE1 stk). 
    rewrite (low_bound_alloc_same _ _ _ _ _ ALLOC). omega.
    rewrite (high_bound_store _ _ _ _ _ _ STORE1 stk). 
    rewrite (high_bound_alloc_same _ _ _ _ _ ALLOC).
    change (size_chunk Mint32) with 4. 
    apply Zle_trans with 0. omega. apply align_16_top_pos.
  destruct H0 as [ms''' STORE2].
  assert (RANGE1: Int.min_signed <= - fn_framesize f <= Int.max_signed).
  split. omega. apply Zle_trans with (-24). omega. compute;congruence.
  assert (RANGE2: Int.min_signed <= - fn_framesize f + 12 <= Int.max_signed).
  split. omega. apply Zle_trans with (-12). omega. compute;congruence.
  econstructor; split.
  eapply exec_function_internal; eauto.
  unfold store_stack. simpl. rewrite Int.add_zero. 
  rewrite Int.signed_repr. eauto. auto.
  unfold store_stack. simpl. rewrite Int.add_signed.
  change (Int.signed (Int.repr 12)) with 12.
  repeat rewrite Int.signed_repr; eauto.
  (* match states *)
  unfold sp; econstructor; eauto.
  eapply match_stacks_function_entry; eauto.
  rewrite Int.signed_repr; eauto.
  rewrite Int.signed_repr; eauto.
  eapply frame_match_store_other with (ms := ms''); eauto.
  eapply frame_match_store_other with (ms := ms'); eauto. 
  simpl. right; omega. simpl. right; omega.
  eapply store_outside_extends with (m2 := ms''); eauto.
  eapply store_outside_extends with (m2 := ms'); eauto.
  rewrite (low_bound_alloc_same _ _ _ _ _ H). simpl; omega.
  rewrite (low_bound_alloc_same _ _ _ _ _ H). simpl; omega.

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

Hypothesis wt_prog: wt_program p.

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
  forall (beh: program_behavior),
  Machabstr.exec_program p beh -> Machconcr.exec_program p beh.
Proof.
  unfold Machconcr.exec_program, Machabstr.exec_program; intros.
  eapply simulation_step_preservation with
    (step1 := Machabstr.step)
    (step2 := Machconcr.step)
    (match_states := fun st1 st2 => match_states st1 st2 /\ wt_state st1).
  eexact equiv_initial_states.
  eexact equiv_final_states.
  intros. destruct H1. exploit step_equiv; eauto.
  intros [st2' [A B]]. exists st2'; split. auto. split. auto.
  eapply Machtyping.subject_reduction; eauto. 
  auto.
Qed.

End SIMULATION.
