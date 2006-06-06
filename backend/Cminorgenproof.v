(** Correctness proof for Cminor generation. *)

Require Import Coqlib.
Require Import Maps.
Require Import Sets. 
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Globalenvs.
Require Import Csharpminor.
Require Import Op.
Require Import Cminor.
Require Cmconstr.
Require Import Cminorgen.
Require Import Cmconstrproof.

Section TRANSLATION.

Variable prog: Csharpminor.program.
Variable tprog: program.
Hypothesis TRANSL: transl_program prog = Some tprog.
Let ge : Csharpminor.genv := Genv.globalenv (program_of_program prog).
Let tge: genv := Genv.globalenv tprog.
Let gce : compilenv := build_global_compilenv prog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intro. unfold ge, tge. 
  apply Genv.find_symbol_transf_partial with (transl_function gce).
  exact TRANSL.
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: Csharpminor.function),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transl_function gce f = Some tf.
Proof.
  intros. 
  generalize 
   (Genv.find_funct_ptr_transf_partial (transl_function gce) TRANSL H).
  case (transl_function gce f).
  intros tf [A B]. exists tf. tauto.
  intros [A B]. elim B. reflexivity.
Qed.

Lemma functions_translated:
  forall (v: val) (f: Csharpminor.function),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_function gce f = Some tf.
Proof.
  intros. 
  generalize 
   (Genv.find_funct_transf_partial (transl_function gce) TRANSL H).
  case (transl_function gce f).
  intros tf [A B]. exists tf. tauto.
  intros [A B]. elim B. reflexivity.
Qed.

Definition var_info_global (id: ident) (vi: var_info) (lv: var_kind) :=
  match vi with
  | Var_global_scalar chunk => lv = Vscalar chunk
  | Var_global_array => exists sz, lv = Varray sz
  | _ => False
  end.

Lemma global_compilenv_charact:
  forall id vi, gce!id = Some vi -> 
  exists lv, (global_var_env prog)!id = Some lv /\ var_info_global id vi lv.
Proof.
  set (mkgve := fun gv vars =>
         List.fold_left
          (fun gv (id_vi: ident * var_kind) => PTree.set (fst id_vi) (snd id_vi) gv)
          vars gv).
  assert (forall vars gv ce,
            (forall id vi, ce!id = Some vi ->
             exists lv, gv!id = Some lv /\ var_info_global id vi lv) ->
            (forall id vi,
              (List.fold_left assign_global_variable vars ce)!id = Some vi ->
              exists lv, (mkgve gv vars)!id = Some lv /\ var_info_global id vi lv)).
  induction vars; simpl; intros.
  eauto.
  apply IHvars with (assign_global_variable ce a); auto.
  intros until vi0. unfold assign_global_variable. destruct a as [id1 vi1].
  simpl. destruct vi1. 
  repeat rewrite PTree.gsspec. case (peq id0 id1); intros. 
  inversion H1. exists (Vscalar m). split. auto. red; auto.
  eauto.
  repeat rewrite PTree.gsspec. case (peq id0 id1); intros. 
  inversion H1. exists (Varray z). split. auto. red. exists z; auto.
  eauto.

  intros. change (global_var_env prog) with (mkgve (PTree.empty var_kind) prog.(Csharpminor.prog_vars)).
  apply H with (PTree.empty var_info). 
  intros until vi0. rewrite PTree.gempty. congruence.
  exact H0.
Qed.

(** * Correspondence between Csharpminor's and Cminor's environments and memory states *)

(** In Csharpminor, every variable is stored in a separate memory block.
  In the corresponding Cminor code, some of these variables reside in
  the local variable environment; others are sub-blocks of the stack data 
  block.  We capture these changes in memory via a memory injection [f]:
- [f b = None] means that the Csharpminor block [b] no longer exist
  in the execution of the generated Cminor code.  This corresponds to
  a Csharpminor local variable translated to a Cminor local variable.
- [f b = Some(b', ofs)] means that Csharpminor block [b] corresponds
  to a sub-block of Cminor block [b] at offset [ofs].

  A memory injection [f] defines a relation [val_inject f] between
  values and a relation [mem_inject f] between memory states.
  These relations, defined in file [Memory], will be used intensively
  in our proof of simulation between Csharpminor and Cminor executions.

  In the remainder of this section, we define relations between
  Csharpminor and Cminor environments and call stacks. *)

(** Matching for a Csharpminor variable [id].
- If this variable is mapped to a Cminor local variable, the
  corresponding Csharpminor memory block [b] must no longer exist in
  Cminor ([f b = None]).  Moreover, the content of block [b] must
  match the value of [id] found in the Cminor local environment [te].
- If this variable is mapped to a sub-block of the Cminor stack data
  at offset [ofs], the address of this variable in Csharpminor [Vptr b
  Int.zero] must match the address of the sub-block [Vptr sp (Int.repr
  ofs)].
*)

Inductive match_var (f: meminj) (id: ident)
                    (e: Csharpminor.env) (m: mem) (te: env) (sp: block) : 
                    var_info -> Prop :=
  | match_var_local:
      forall chunk b v v',
      PTree.get id e = Some (b, Vscalar chunk) ->
      Mem.load chunk m b 0 = Some v ->
      f b = None ->
      PTree.get id te = Some v' ->
      val_inject f v v' ->
      match_var f id e m te sp (Var_local chunk)
  | match_var_stack_scalar:
      forall chunk ofs b,
      PTree.get id e = Some (b, Vscalar chunk) ->
      val_inject f (Vptr b Int.zero) (Vptr sp (Int.repr ofs)) ->
      match_var f id e m te sp (Var_stack_scalar chunk ofs)
  | match_var_stack_array:
      forall ofs sz b,
      PTree.get id e = Some (b, Varray sz) ->
      val_inject f (Vptr b Int.zero) (Vptr sp (Int.repr ofs)) ->
      match_var f id e m te sp (Var_stack_array ofs)
  | match_var_global_scalar:
      forall chunk,
      PTree.get id e = None ->
      PTree.get id (global_var_env prog) = Some (Vscalar chunk) ->
      match_var f id e m te sp (Var_global_scalar chunk)
  | match_var_global_array:
      forall sz,
      PTree.get id e = None ->
      PTree.get id (global_var_env prog) = Some (Varray sz) ->
      match_var f id e m te sp (Var_global_array).

(** Matching between a Csharpminor environment [e] and a Cminor
  environment [te].  The [lo] and [hi] parameters delimit the range
  of addresses for the blocks referenced from [te]. *)

Record match_env (f: meminj) (cenv: compilenv)
                 (e: Csharpminor.env) (m: mem) (te: env) (sp: block)
                 (lo hi: Z) : Prop :=
  mk_match_env {

(** Each variable mentioned in the compilation environment must match
  as defined above. *)
    me_vars:
      forall id vi, PTree.get id cenv = Some vi -> match_var f id e m te sp vi;

(** The range [lo, hi] must not be empty. *)
    me_low_high:
      lo <= hi;

(** Every block appearing in the Csharpminor environment [e] must be
  in the range [lo, hi]. *)
    me_bounded:
      forall id b lv, PTree.get id e = Some(b, lv) -> lo <= b < hi;

(** Distinct Csharpminor local variables must be mapped to distinct blocks. *)
    me_inj:
      forall id1 b1 lv1 id2 b2 lv2,
      PTree.get id1 e = Some(b1, lv1) ->
      PTree.get id2 e = Some(b2, lv2) ->
      id1 <> id2 -> b1 <> b2;

(** All blocks mapped to sub-blocks of the Cminor stack data must be in
  the range [lo, hi]. *)
    me_inv:
      forall b delta,
      f b = Some(sp, delta) -> lo <= b < hi;

(** All Csharpminor blocks below [lo] (i.e. allocated before the blocks
  referenced from [e]) must map to blocks that are below [sp]
  (i.e. allocated before the stack data for the current Cminor function). *)
    me_incr:
      forall b tb delta,
      f b = Some(tb, delta) -> b < lo -> tb < sp
  }.

(** Global environments match if the memory injection [f] leaves unchanged
  the references to global symbols and functions. *)

Record match_globalenvs (f: meminj) : Prop := 
  mk_match_globalenvs {
    mg_symbols:
      forall id b,
      Genv.find_symbol ge id = Some b ->
      f b = Some (b, 0) /\ Genv.find_symbol tge id = Some b;
    mg_functions:
      forall b, b < 0 -> f b = Some(b, 0)
  }.

(** Call stacks represent abstractly the execution state of the current
  Csharpminor and Cminor functions, as well as the states of the
  calling functions.  A call stack is a list of frames, each frame
  collecting information on the current execution state of a Csharpminor
  function and its Cminor translation. *)

Record frame : Set :=
  mkframe {
    fr_cenv: compilenv;
    fr_e: Csharpminor.env;
    fr_te: env;
    fr_sp: block;
    fr_low: Z;
    fr_high: Z
  }.

Definition callstack : Set := list frame.

(** Matching of call stacks imply matching of environments for each of
  the frames, plus matching of the global environments, plus disjointness
  conditions over the memory blocks allocated for local variables
  and Cminor stack data. *)

Inductive match_callstack: meminj -> callstack -> Z -> Z -> mem -> Prop :=
  | mcs_nil:
      forall f bound tbound m,
      match_globalenvs f ->
      match_callstack f nil bound tbound m
  | mcs_cons:
      forall f cenv e te sp lo hi cs bound tbound m,
      hi <= bound ->
      sp < tbound ->
      match_env f cenv e m te sp lo hi ->
      match_callstack f cs lo sp m ->
      match_callstack f (mkframe cenv e te sp lo hi :: cs) bound tbound m.

(** The remainder of this section is devoted to showing preservation
  of the [match_callstack] invariant under various assignments and memory
  stores.  First: preservation by memory stores to ``mapped'' blocks
  (block that have a counterpart in the Cminor execution). *)

Lemma match_env_store_mapped:
  forall f cenv e m1 m2 te sp lo hi chunk b ofs v,
  f b <> None ->
  store chunk m1 b ofs v = Some m2 ->
  match_env f cenv e m1 te sp lo hi ->
  match_env f cenv e m2 te sp lo hi.
Proof.
  intros. inversion H1. constructor; auto.
  (* vars *)
  intros. generalize (me_vars0 _ _ H2); intro. 
  inversion H3; econstructor; eauto.
  rewrite <- H5. eapply load_store_other; eauto. 
  left. congruence.
Qed.

Lemma match_callstack_mapped:
  forall f cs bound tbound m1,
  match_callstack f cs bound tbound m1 ->
  forall chunk b ofs v m2,
  f b <> None ->
  store chunk m1 b ofs v = Some m2 ->
  match_callstack f cs bound tbound m2.
Proof.
  induction 1; intros; econstructor; eauto.
  eapply match_env_store_mapped; eauto.
Qed.

(** Preservation by assignment to a Csharpminor variable that is 
  translated to a Cminor local variable.  The value being assigned
  must be normalized with respect to the memory chunk of the variable,
  in the following sense. *)

Definition val_normalized (chunk: memory_chunk) (v: val) : Prop :=
  exists v0, v = Val.load_result chunk v0.

Lemma load_result_idem:
  forall chunk v,
  Val.load_result chunk (Val.load_result chunk v) =
  Val.load_result chunk v.
Proof.
  destruct chunk; destruct v; simpl; auto.
  rewrite Int.cast8_signed_idem; auto.
  rewrite Int.cast8_unsigned_idem; auto.
  rewrite Int.cast16_signed_idem; auto.
  rewrite Int.cast16_unsigned_idem; auto.
  rewrite Float.singleoffloat_idem; auto.
Qed.

Lemma load_result_normalized:
  forall chunk v,
  val_normalized chunk v -> Val.load_result chunk v = v.
Proof.
  intros chunk v [v0 EQ]. rewrite EQ. apply load_result_idem. 
Qed.

Lemma match_env_store_local:
  forall f cenv e m1 m2 te sp lo hi id b chunk v tv,
  e!id = Some(b, Vscalar chunk) ->
  val_inject f v tv ->
  val_normalized chunk tv ->
  store chunk m1 b 0 v = Some m2 ->
  match_env f cenv e m1 te sp lo hi ->
  match_env f cenv e m2 (PTree.set id tv te) sp lo hi.
Proof.
  intros. inversion H3. constructor; auto.
  intros. generalize (me_vars0 _ _ H4); intro.
  inversion H5; subst.
  (* var_local *)
  case (peq id id0); intro.
    (* the stored variable *)
    subst id0. 
    change Csharpminor.var_kind with var_kind in H6. 
    rewrite H in H6. injection H6; clear H6; intros; subst b0 chunk0.
    econstructor. eauto. 
    eapply load_store_same; eauto. auto. 
    rewrite PTree.gss. reflexivity.
    replace tv with (Val.load_result chunk tv).
    apply Mem.load_result_inject. constructor; auto. 
    apply load_result_normalized; auto.    
    (* a different variable *)
    econstructor; eauto.
    rewrite <- H7. eapply load_store_other; eauto. 
    rewrite PTree.gso; auto.
  (* var_stack_scalar *)
  econstructor; eauto.
  (* var_stack_array *)
  econstructor; eauto.
  (* var_global_scalar *)
  econstructor; eauto.
  (* var_global_array *)
  econstructor; eauto.
Qed.

Lemma match_env_store_above:
  forall f cenv e m1 m2 te sp lo hi chunk b v,
  store chunk m1 b 0 v = Some m2 ->
  hi <= b ->
  match_env f cenv e m1 te sp lo hi ->
  match_env f cenv e m2 te sp lo hi.
Proof.
  intros. inversion H1; constructor; auto.
  intros. generalize (me_vars0 _ _ H2); intro.
  inversion H3; econstructor; eauto.
  rewrite <- H5. eapply load_store_other; eauto.
  left. generalize (me_bounded0 _ _ _ H4). unfold block in *. omega.
Qed.

Lemma match_callstack_store_above:
  forall f cs bound tbound m1,
  match_callstack f cs bound tbound m1 ->
  forall chunk b v m2,
  store chunk m1 b 0 v = Some m2 ->
  bound <= b ->
  match_callstack f cs bound tbound m2.
Proof.
  induction 1; intros; econstructor; eauto.
  eapply match_env_store_above with (b := b); eauto. omega.
  eapply IHmatch_callstack; eauto. 
  inversion H1. omega.
Qed.

Lemma match_callstack_store_local:
  forall f cenv e te sp lo hi cs bound tbound m1 m2 id b chunk v tv,
  e!id = Some(b, Vscalar chunk) ->
  val_inject f v tv ->
  val_normalized chunk tv ->
  store chunk m1 b 0 v = Some m2 ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) bound tbound m1 ->
  match_callstack f (mkframe cenv e (PTree.set id tv te) sp lo hi :: cs) bound tbound m2.
Proof.
  intros. inversion H3. constructor; auto.
  eapply match_env_store_local; eauto.
  eapply match_callstack_store_above; eauto.
  inversion H17. 
  generalize (me_bounded0 _ _ _ H). omega.
Qed.

(** A variant of [match_callstack_store_local] where the Cminor environment
  [te] already associates to [id] a value that matches the assigned value.
  In this case, [match_callstack] is preserved even if no assignment
  takes place on the Cminor side. *)

Lemma match_env_extensional:
  forall f cenv e m te1 sp lo hi,
  match_env f cenv e m te1 sp lo hi ->
  forall te2,
  (forall id, te2!id = te1!id) ->
  match_env f cenv e m te2 sp lo hi.
Proof.
  induction 1; intros; econstructor; eauto.
  intros. generalize (me_vars0 _ _ H0); intro. 
  inversion H1; econstructor; eauto.
  rewrite H. auto.
Qed.

Lemma match_callstack_store_local_unchanged:
  forall f cenv e te sp lo hi cs bound tbound m1 m2 id b chunk v tv,
  e!id = Some(b, Vscalar chunk) ->
  val_inject f v tv ->
  val_normalized chunk tv ->
  store chunk m1 b 0 v = Some m2 ->
  te!id = Some tv ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) bound tbound m1 ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) bound tbound m2.
Proof.
  intros. inversion H4. constructor; auto.
  apply match_env_extensional with (PTree.set id tv te).
  eapply match_env_store_local; eauto.
  intros. rewrite PTree.gsspec. 
  case (peq id0 id); intros. congruence. auto.
  eapply match_callstack_store_above; eauto.
  inversion H18. 
  generalize (me_bounded0 _ _ _ H). omega.
Qed.

(** Preservation of [match_callstack] by freeing all blocks allocated
  for local variables at function entry (on the Csharpminor side). *)

Lemma match_callstack_incr_bound:
  forall f cs bound tbound m,
  match_callstack f cs bound tbound m ->
  forall bound' tbound',
  bound <= bound' -> tbound <= tbound' ->
  match_callstack f cs bound' tbound' m.
Proof.
  intros. inversion H; constructor; auto. omega. omega.
Qed.

Lemma load_freelist:
  forall fbl chunk m b ofs,
  (forall b', In b' fbl -> b' <> b) -> 
  load chunk (free_list m fbl) b ofs = load chunk m b ofs.
Proof.
  induction fbl; simpl; intros.
  auto.
  rewrite load_free. apply IHfbl. 
  intros. apply H. tauto.
  apply sym_not_equal. apply H. tauto.
Qed.

Lemma match_env_freelist:
  forall f cenv e m te sp lo hi fbl,
  match_env f cenv e m te sp lo hi ->
  (forall b, In b fbl -> hi <= b) ->
  match_env f cenv e (free_list m fbl) te sp lo hi.
Proof.
  intros. inversion H. econstructor; eauto.
  intros. generalize (me_vars0 _ _ H1); intro. 
  inversion H2; econstructor; eauto.
  rewrite <- H4. apply load_freelist. 
  intros. generalize (H0 _ H9); intro. 
  generalize (me_bounded0 _ _ _ H3). unfold block; omega.
Qed.  

Lemma match_callstack_freelist_rec:
  forall f cs bound tbound m,
  match_callstack f cs bound tbound m ->
  forall fbl,
  (forall b, In b fbl -> bound <= b) ->
  match_callstack f cs bound tbound (free_list m fbl).
Proof.
  induction 1; intros; constructor; auto.
  eapply match_env_freelist; eauto. 
  intros. generalize (H3 _ H4). omega.
  apply IHmatch_callstack. intros. 
  generalize (H3 _ H4). inversion H1. omega. 
Qed.

Lemma match_callstack_freelist:
  forall f cenv e te sp lo hi cs bound tbound m fbl,
  (forall b, In b fbl -> lo <= b) ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) bound tbound m ->
  match_callstack f cs bound tbound (free_list m fbl).
Proof.
  intros. inversion H0. inversion H14.
  apply match_callstack_incr_bound with lo sp.
  apply match_callstack_freelist_rec. auto. 
  assumption.
  omega. omega.
Qed.

(** Preservation of [match_callstack] when allocating a block for
  a local variable on the Csharpminor side.  *)

Lemma load_from_alloc_is_undef:
  forall m1 chunk m2 b,
  alloc m1 0 (size_chunk chunk) = (m2, b) ->
  load chunk m2 b 0 = Some Vundef.
Proof.
  intros. 
  assert (valid_block m2 b). eapply valid_new_block; eauto.
  assert (low_bound m2 b <= 0). 
    generalize (low_bound_alloc _ _ b _ _ _ H). rewrite zeq_true. omega.
  assert (0 + size_chunk chunk <= high_bound m2 b).
    generalize (high_bound_alloc _ _ b _ _ _ H). rewrite zeq_true. omega.
  elim (load_in_bounds _ _ _ _ H0 H1 H2). intros v LOAD.
  assert (v = Vundef). eapply load_alloc_same; eauto.
  congruence.
Qed.

Lemma match_env_alloc_same:
  forall m1 lv m2 b info f1 cenv1 e1 te sp lo id data tv,
  alloc m1 0 (sizeof lv) = (m2, b) ->
  match info with
    | Var_local chunk => data = None /\ lv = Vscalar chunk
    | Var_stack_scalar chunk pos => data = Some(sp, pos) /\ lv = Vscalar chunk
    | Var_stack_array pos => data = Some(sp, pos) /\ exists sz, lv = Varray sz
    | Var_global_scalar chunk => False
    | Var_global_array => False
  end ->
  match_env f1 cenv1 e1 m1 te sp lo m1.(nextblock) ->
  te!id = Some tv ->
  let f2 := extend_inject b data f1 in
  let cenv2 := PTree.set id info cenv1 in
  let e2 := PTree.set id (b, lv) e1 in
  inject_incr f1 f2 ->
  match_env f2 cenv2 e2 m2 te sp lo m2.(nextblock).
Proof.
  intros. 
  assert (b = m1.(nextblock)).
    injection H; intros. auto.
  assert (m2.(nextblock) = Zsucc m1.(nextblock)).
    injection H; intros. rewrite <- H6; reflexivity.
  inversion H1. constructor.
  (* me_vars *)
  intros id0 vi. unfold cenv2. rewrite PTree.gsspec. case (peq id0 id); intros.
    (* same var *)
    subst id0. injection H6; clear H6; intro; subst vi. destruct info.
      (* info = Var_local chunk *)
      elim H0; intros.
      apply match_var_local with b Vundef tv.
      unfold e2; rewrite PTree.gss. congruence.
      eapply load_from_alloc_is_undef; eauto. 
      rewrite H7 in H. unfold sizeof in H. eauto.
      unfold f2, extend_inject, eq_block. rewrite zeq_true. auto.
      auto.
      constructor.
      (* info = Var_stack_scalar chunk ofs *)
      elim H0; intros.
      apply match_var_stack_scalar with b. 
      unfold e2; rewrite PTree.gss. congruence.
      eapply val_inject_ptr. 
      unfold f2, extend_inject, eq_block. rewrite zeq_true. eauto.
      rewrite Int.add_commut. rewrite Int.add_zero. auto.
      (* info = Var_stack_array z *)
      elim H0; intros A [sz B].
      apply match_var_stack_array with sz b.
      unfold e2; rewrite PTree.gss. congruence.
      eapply val_inject_ptr. 
      unfold f2, extend_inject, eq_block. rewrite zeq_true. eauto.
      rewrite Int.add_commut. rewrite Int.add_zero. auto.
      (* info = Var_global *)
      contradiction.
      contradiction.
    (* other vars *)
    generalize (me_vars0 _ _ H6); intros.
    inversion H7; econstructor; eauto.
    unfold e2; rewrite PTree.gso; auto. 
    unfold f2, extend_inject, eq_block; rewrite zeq_false; auto.
    generalize (me_bounded0 _ _ _ H8). unfold block in *; omega.
    unfold e2; rewrite PTree.gso; eauto. 
    unfold e2; rewrite PTree.gso; eauto. 
    unfold e2; rewrite PTree.gso; eauto. 
    unfold e2; rewrite PTree.gso; eauto. 
  (* lo <= hi *)
  unfold block in *; omega.
  (* me_bounded *)
  intros until lv0. unfold e2; rewrite PTree.gsspec. 
  case (peq id0 id); intros.
  subst id0. inversion H6. subst b0. unfold block in *; omega. 
  generalize (me_bounded0 _ _ _ H6). rewrite H5. omega.
  (* me_inj *)
  intros until lv2. unfold e2; repeat rewrite PTree.gsspec.
  case (peq id1 id); case (peq id2 id); intros.
  congruence.
  inversion H6. subst b1. rewrite H4. 
    generalize (me_bounded0 _ _ _ H7). unfold block; omega.
  inversion H7. subst b2. rewrite H4.
    generalize (me_bounded0 _ _ _ H6). unfold block; omega.
  eauto.
  (* me_inv *)
  intros until delta. unfold f2, extend_inject, eq_block.
  case (zeq b0 b); intros.
  subst b0. rewrite H4; rewrite H5. omega. 
  generalize (me_inv0 _ _ H6). rewrite H5. omega.
  (* me_incr *)
  intros until delta. unfold f2, extend_inject, eq_block.
  case (zeq b0 b); intros.
  subst b0. unfold block in *; omegaContradiction.
  eauto.
Qed.

Lemma match_env_alloc_other:
  forall f1 cenv e m1 m2 te sp lo hi chunk b data,
  alloc m1 0 (sizeof chunk) = (m2, b) ->
  match data with None => True | Some (b', delta') => sp < b' end ->
  hi <= m1.(nextblock) ->
  match_env f1 cenv e m1 te sp lo hi ->
  let f2 := extend_inject b data f1 in
  inject_incr f1 f2 ->
  match_env f2 cenv e m2 te sp lo hi.
Proof.
  intros. 
  assert (b = m1.(nextblock)). injection H; auto.
  rewrite <- H4 in H1.
  inversion H2. constructor; auto.
  (* me_vars *)
  intros. generalize (me_vars0 _ _ H5); intro. 
  inversion H6; econstructor; eauto.
  unfold f2, extend_inject, eq_block. rewrite zeq_false. auto.
  generalize (me_bounded0 _ _ _ H7). unfold block in *; omega.
  (* me_bounded *)
  intros until delta. unfold f2, extend_inject, eq_block.
  case (zeq b0 b); intros. rewrite H5 in H0. omegaContradiction.
  eauto.
  (* me_incr *)
  intros until delta. unfold f2, extend_inject, eq_block.
  case (zeq b0 b); intros. subst b0. omegaContradiction.
  eauto.
Qed.

Lemma match_callstack_alloc_other:
  forall f1 cs bound tbound m1,
  match_callstack f1 cs bound tbound m1 ->
  forall lv m2 b data,
  alloc m1 0 (sizeof lv) = (m2, b) ->
  match data with None => True | Some (b', delta') => tbound <= b' end ->
  bound <= m1.(nextblock) ->
  let f2 := extend_inject b data f1 in
  inject_incr f1 f2 ->
  match_callstack f2 cs bound tbound m2.
Proof.
  induction 1; intros.
  constructor. 
    inversion H. constructor. 
    intros. auto.
    intros. elim (mg_symbols0 _ _ H4); intros.
    split; auto. elim (H3 b0); intros; congruence.
    intros. generalize (mg_functions0 _ H4). elim (H3 b0); congruence.
  constructor. auto. auto. 
  unfold f2; eapply match_env_alloc_other; eauto. 
  destruct data; auto. destruct p. omega. omega. 
  unfold f2; eapply IHmatch_callstack; eauto. 
  destruct data; auto. destruct p. omega. 
  inversion H1; omega.
Qed.

Lemma match_callstack_alloc_left:
  forall m1 lv m2 b info f1 cenv1 e1 te sp lo id data cs tv tbound,
  alloc m1 0 (sizeof lv) = (m2, b) ->
  match info with
    | Var_local chunk => data = None /\ lv = Vscalar chunk
    | Var_stack_scalar chunk pos => data = Some(sp, pos) /\ lv = Vscalar chunk
    | Var_stack_array pos => data = Some(sp, pos) /\ exists sz, lv = Varray sz
    | Var_global_scalar chunk => False
    | Var_global_array => False
  end ->
  match_callstack f1 (mkframe cenv1 e1 te sp lo m1.(nextblock) :: cs) m1.(nextblock) tbound m1 ->
  te!id = Some tv ->
  let f2 := extend_inject b data f1 in
  let cenv2 := PTree.set id info cenv1 in
  let e2 := PTree.set id (b, lv) e1 in
  inject_incr f1 f2 ->
  match_callstack f2 (mkframe cenv2 e2 te sp lo m2.(nextblock) :: cs) m2.(nextblock) tbound m2.
Proof.
  intros. inversion H1. constructor. omega. auto.
  unfold f2, cenv2, e2. eapply match_env_alloc_same; eauto.
  unfold f2; eapply match_callstack_alloc_other; eauto. 
  destruct info.
  elim H0; intros. rewrite H19. auto.
  elim H0; intros. rewrite H19. omega.
  elim H0; intros. rewrite H19. omega.
  contradiction.
  contradiction.
  inversion H17; omega. 
Qed.

Lemma match_callstack_alloc_right:
  forall f cs bound tm1 m tm2 lo hi b,
  alloc tm1 lo hi = (tm2, b) ->
  match_callstack f cs bound tm1.(nextblock) m ->
  match_callstack f cs bound tm2.(nextblock) m.
Proof.
  intros. eapply match_callstack_incr_bound; eauto. omega.
  injection H; intros. rewrite <- H2; simpl. omega.
Qed.

(** [match_callstack] implies [match_globalenvs]. *)

Lemma match_callstack_match_globalenvs:
  forall f cs bound tbound m,
  match_callstack f cs bound tbound m ->
  match_globalenvs f.
Proof.
  induction 1; eauto.
Qed.

(** * Correctness of Cminor construction functions *)

Hint Resolve eval_negint eval_negfloat eval_absfloat eval_intoffloat
  eval_floatofint eval_floatofintu eval_notint eval_notbool
  eval_cast8signed eval_cast8unsigned eval_cast16signed
  eval_cast16unsigned eval_singleoffloat eval_add eval_add_ptr
  eval_add_ptr_2 eval_sub eval_sub_ptr_int eval_sub_ptr_ptr
  eval_mul eval_divs eval_mods eval_divu eval_modu
  eval_and eval_or eval_xor eval_shl eval_shr eval_shru 
  eval_addf eval_subf eval_mulf eval_divf
  eval_cmp eval_cmp_null_r eval_cmp_null_l eval_cmp_ptr
  eval_cmpu eval_cmpf: evalexpr.

Remark val_inject_val_of_bool:
  forall f b, val_inject f (Val.of_bool b) (Val.of_bool b).
Proof.
  intros; destruct b; unfold Val.of_bool, Vtrue, Vfalse; constructor.
Qed.

Ltac TrivialOp :=
  match goal with
  | [ |- exists x, _ /\ val_inject _ (Vint ?x) _ ] =>
      exists (Vint x); split;
      [eauto with evalexpr | constructor]
  | [ |- exists x, _ /\ val_inject _ (Vfloat ?x) _ ] =>
      exists (Vfloat x); split;
      [eauto with evalexpr | constructor]
  | [ |- exists x, _ /\ val_inject _ (Val.of_bool ?x) _ ] =>
      exists (Val.of_bool x); split;
      [eauto with evalexpr | apply val_inject_val_of_bool]
  | _ => idtac
  end.

Remark eval_compare_null_inv:
  forall c i v,
  Csharpminor.eval_compare_null c i = Some v ->
  i = Int.zero /\ (c = Ceq /\ v = Vfalse \/ c = Cne /\ v = Vtrue).
Proof.
  intros until v. unfold Csharpminor.eval_compare_null.
  predSpec Int.eq Int.eq_spec i Int.zero.
  case c; intro EQ; simplify_eq EQ; intro; subst v; tauto.
  congruence.
Qed.

(** Correctness of [make_op].  The generated Cminor code evaluates
  to a value that matches the result value of the Csharpminor operation,
  provided arguments match pairwise ([val_list_inject f] hypothesis). *)

Lemma make_op_correct:
  forall al a op vl m2 v sp le te1 tm1 te2 tm2 tvl f,
  make_op op al = Some a ->
  Csharpminor.eval_operation op vl m2 = Some v ->
  eval_exprlist tge (Vptr sp Int.zero) le te1 tm1 al te2 tm2 tvl ->
  val_list_inject f vl tvl ->
  mem_inject f m2 tm2 ->
  exists tv,
     eval_expr tge (Vptr sp Int.zero) le te1 tm1 a te2 tm2 tv
  /\ val_inject f v tv.
Proof.
  intros. 
  destruct al as [ | a1 al];
  [idtac | destruct al as [ | a2 al];
  [idtac | destruct al as [ | a3 al]]];
  simpl in H; try discriminate.
  (* Constant operators *)
  inversion H1. subst sp0 le0 e m te2 tm1 tvl.
  inversion H2. subst vl.
  destruct op; simplify_eq H; intro; subst a;
  simpl in H0; injection H0; intro; subst v.
  (* intconst *)
  TrivialOp. econstructor. constructor. reflexivity. 
  (* floatconst *)
  TrivialOp. econstructor. constructor. reflexivity.
  (* Unary operators *)
  inversion H1. subst sp0 le0 e m a0 bl e2 m0 tvl.
  inversion H14. subst sp0 le0 e m e1 m1 vl0.
  inversion H2. subst vl v' vl'. inversion H8. subst vl0.
  destruct op; simplify_eq H; intro; subst a;
  simpl in H0; destruct v1; simplify_eq H0; intro; subst v;
  inversion H7; subst v0;
  TrivialOp.
  (* Binary operations *)
  inversion H1. subst sp0 le0 e m a0 bl e2 m0 tvl.
  inversion H14. subst sp0 le0 e m a0 bl e2 m3 vl0.
  inversion H16. subst sp0 le0 e m e0 m0 vl1.
  inversion H2. subst vl v' vl'.
  inversion H8. subst vl0 v' vl'.
  inversion H12. subst vl.
  destruct op; simplify_eq H; intro; subst a;
  simpl in H0; destruct v2; destruct v3; simplify_eq H0; intro; try subst v;
  inversion H7; inversion H9; subst v0; subst v1;
  TrivialOp.
  (* add int ptr *)
  exists (Vptr b2 (Int.add ofs2 i)); split.
  eauto with evalexpr. apply val_inject_ptr with x. auto.
  subst ofs2. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  (* add ptr int *)
  exists (Vptr b2 (Int.add ofs2 i0)); split.
  eauto with evalexpr. apply val_inject_ptr with x. auto.
  subst ofs2. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  (* sub ptr int *)
  exists (Vptr b2 (Int.sub ofs2 i0)); split.
  eauto with evalexpr. apply val_inject_ptr with x. auto.
  subst ofs2. apply Int.sub_add_l. 
  (* sub ptr ptr *)
  destruct (eq_block b b0); simplify_eq H0; intro; subst v; subst b0.
  assert (b4 = b2). congruence. subst b4.
  exists (Vint (Int.sub ofs2 ofs3)); split. eauto with evalexpr.
  subst ofs2 ofs3. replace x0 with x. rewrite Int.sub_shifted. constructor.
  congruence.
  (* divs *)
  generalize (Int.eq_spec i0 Int.zero); destruct (Int.eq i0 Int.zero); intro;
  simplify_eq H0; intro; subst v. TrivialOp.
  (* divu *)
  generalize (Int.eq_spec i0 Int.zero); destruct (Int.eq i0 Int.zero); intro;
  simplify_eq H0; intro; subst v. TrivialOp.
  (* mods *)
  generalize (Int.eq_spec i0 Int.zero); destruct (Int.eq i0 Int.zero); intro;
  simplify_eq H0; intro; subst v. TrivialOp.
  (* modu *)
  generalize (Int.eq_spec i0 Int.zero); destruct (Int.eq i0 Int.zero); intro;
  simplify_eq H0; intro; subst v. TrivialOp.
  (* shl *)
  caseEq (Int.ltu i0 (Int.repr 32)); intro EQ; rewrite EQ in H0;
  simplify_eq H0; intro; subst v. TrivialOp.
  (* shr *)
  caseEq (Int.ltu i0 (Int.repr 32)); intro EQ; rewrite EQ in H0;
  simplify_eq H0; intro; subst v. TrivialOp.
  (* shru *)
  caseEq (Int.ltu i0 (Int.repr 32)); intro EQ; rewrite EQ in H0;
  simplify_eq H0; intro; subst v. TrivialOp.
  (* cmp int ptr *)
  elim (eval_compare_null_inv _ _ _ H0); intros; subst i1 i.
  exists v; split. eauto with evalexpr. 
  elim H18; intros [A B]; subst v; unfold Vtrue, Vfalse; constructor.
  (* cmp ptr int *)
  elim (eval_compare_null_inv _ _ _ H0); intros; subst i1 i0.
  exists v; split. eauto with evalexpr. 
  elim H18; intros [A B]; subst v; unfold Vtrue, Vfalse; constructor.
  (* cmp ptr ptr *)
  caseEq (valid_pointer m2 b (Int.signed i) && valid_pointer m2 b0 (Int.signed i0)); 
  intro EQ; rewrite EQ in H0; try discriminate.
  destruct (eq_block b b0); simplify_eq H0; intro; subst v b0.
  assert (b4 = b2); [congruence|subst b4].
  assert (x0 = x); [congruence|subst x0].
  elim (andb_prop _ _ EQ); intros.
  exists (Val.of_bool (Int.cmp c ofs2 ofs3)); split.
  eauto with evalexpr. 
  subst ofs2 ofs3. rewrite Int.translate_cmp. 
  apply val_inject_val_of_bool. 
  eapply valid_pointer_inject_no_overflow; eauto.
  eapply valid_pointer_inject_no_overflow; eauto.
Qed.

(** Correctness of [make_cast].  Note that the resulting Cminor value is
  normalized according to the given memory chunk. *)

Lemma make_cast_correct:
  forall f sp le te1 tm1 a te2 tm2 v chunk v' tv,
  eval_expr tge (Vptr sp Int.zero) le te1 tm1 a te2 tm2 tv ->
  cast chunk v = Some v' ->
  val_inject f v tv ->
  exists tv',
  eval_expr tge (Vptr sp Int.zero) le
            te1 tm1 (make_cast chunk a)
            te2 tm2 tv'
  /\ val_inject f v' tv'
  /\ val_normalized chunk tv'.
Proof.
  intros. destruct chunk; destruct v; simplify_eq H0; intro; subst v'; simpl;
  inversion H1; subst tv.

  exists (Vint (Int.cast8signed i)). 
  split. apply eval_cast8signed; auto. 
  split. constructor. exists (Vint i); reflexivity.

  exists (Vint (Int.cast8unsigned i)).
  split. apply eval_cast8unsigned; auto. 
  split. constructor. exists (Vint i); reflexivity.

  exists (Vint (Int.cast16signed i)). 
  split. apply eval_cast16signed; auto. 
  split. constructor. exists (Vint i); reflexivity.

  exists (Vint (Int.cast16unsigned i)).
  split. apply eval_cast16unsigned; auto. 
  split. constructor. exists (Vint i); reflexivity.

  exists (Vint i).
  split. auto. split. auto. exists (Vint i); reflexivity.

  exists (Vptr b2 ofs2).
  split. auto. split. auto. exists (Vptr b2 ofs2); reflexivity.

  exists (Vfloat (Float.singleoffloat f0)).
  split. apply eval_singleoffloat; auto. 
  split. constructor. exists (Vfloat f0); reflexivity.

  exists (Vfloat f0).
  split. auto. split. auto. exists (Vfloat f0); reflexivity.
Qed.

Lemma make_stackaddr_correct:
  forall sp le te tm ofs,
  eval_expr tge (Vptr sp Int.zero) le
            te tm (make_stackaddr ofs)
            te tm (Vptr sp (Int.repr ofs)).
Proof.
  intros; unfold make_stackaddr.
  eapply eval_Eop. econstructor. simpl. decEq. decEq.
  rewrite Int.add_commut. apply Int.add_zero.
Qed.

Lemma make_globaladdr_correct:
  forall sp le te tm id b,
  Genv.find_symbol tge id = Some b ->
  eval_expr tge (Vptr sp Int.zero) le
            te tm (make_globaladdr id)
            te tm (Vptr b Int.zero).
Proof.
  intros; unfold make_globaladdr.
  eapply eval_Eop. econstructor. simpl. rewrite H. auto.
Qed.

(** Correctness of [make_load] and [make_store]. *)

Lemma make_load_correct:
  forall sp le te1 tm1 a te2 tm2 va chunk v,
  eval_expr tge (Vptr sp Int.zero) le te1 tm1 a te2 tm2 va ->
  Mem.loadv chunk tm2 va = Some v ->
  eval_expr tge (Vptr sp Int.zero) le
            te1 tm1 (make_load chunk a)
            te2 tm2 v.
Proof.
  intros; unfold make_load.
  eapply eval_load; eauto.
Qed.

Lemma val_content_inject_cast:
  forall f chunk v1 v2 tv1,
  cast chunk v1 = Some v2 ->
  val_inject f v1 tv1 ->
  val_content_inject f (mem_chunk chunk) v2 tv1.
Proof.
  intros. destruct chunk; destruct v1; simplify_eq H; intro; subst v2;
  inversion H0; simpl.
  apply val_content_inject_8. apply Int.cast8_unsigned_signed.
  apply val_content_inject_8. apply Int.cast8_unsigned_idem.
  apply val_content_inject_16. apply Int.cast16_unsigned_signed.
  apply val_content_inject_16. apply Int.cast16_unsigned_idem.
  constructor; constructor.
  constructor; econstructor; eauto.
  apply val_content_inject_32. apply Float.singleoffloat_idem.
  constructor; constructor. 
Qed.

Lemma make_store_correct:
  forall f sp le te1 tm1 addr te2 tm2 tvaddr rhs te3 tm3 tvrhs
         chunk vrhs v m3 vaddr m4,
  eval_expr tge (Vptr sp Int.zero) le
            te1 tm1 addr te2 tm2 tvaddr ->
  eval_expr tge (Vptr sp Int.zero) le
            te2 tm2 rhs te3 tm3 tvrhs ->
  cast chunk vrhs = Some v ->
  Mem.storev chunk m3 vaddr v = Some m4 ->
  mem_inject f m3 tm3 ->
  val_inject f vaddr tvaddr ->
  val_inject f vrhs tvrhs ->
  exists tm4, exists tv,
  eval_expr tge (Vptr sp Int.zero) le
            te1 tm1 (make_store chunk addr rhs)
            te3 tm4 tv
  /\ mem_inject f m4 tm4
  /\ val_inject f v tv
  /\ nextblock tm4 = nextblock tm3.
Proof.
  intros. unfold make_store.
  assert (val_content_inject f (mem_chunk chunk) v tvrhs).
    eapply val_content_inject_cast; eauto.
  elim (storev_mapped_inject_1 _ _ _ _ _ _ _ _ _ H3 H2 H4 H6).
  intros tm4 [STORE MEMINJ].
  generalize (eval_store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H0 STORE).
  intro EVALSTORE.
  elim (make_cast_correct _ _ _ _ _ _ _ _ _ _ _ _ EVALSTORE H1 H5). 
  intros tv [EVALCAST [VALINJ VALNORM]].
  exists tm4; exists tv. intuition.
  unfold storev in STORE; destruct tvaddr; try discriminate.
  generalize (store_inv _ _ _ _ _ _ STORE). simpl. tauto.
Qed.

(** Correctness of the variable accessors [var_get], [var_set]
  and [var_addr]. *)

Lemma var_get_correct:
  forall cenv id a f e te sp lo hi m cs tm b chunk v le,
  var_get cenv id = Some a ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) m.(nextblock) tm.(nextblock) m ->
  mem_inject f m tm ->
  eval_var prog e id b (Vscalar chunk) ->
  load chunk m b 0 = Some v ->
  exists tv,
    eval_expr tge (Vptr sp Int.zero) le te tm a te tm tv /\
    val_inject f v tv.
Proof.
  unfold var_get; intros.
  caseEq (cenv!id); [intros vi EQ | intros EQ]; rewrite EQ in H; try discriminate.
  assert (match_var f id e m te sp vi).
    inversion H0. inversion H17. auto.
  caseEq vi; intros; rewrite H5 in H; simplify_eq H; clear H; intros; subst a vi.
  (* var_local *)
  inversion H4. subst m0. inversion H2. subst. 
  exists v'; split.
  apply eval_Evar. auto. 
  replace v with v0. auto. congruence.
  congruence.
  (* var_stack_scalar *)
  inversion H4. subst m0 z. inversion H2; [subst|congruence].
  inversion H7. subst.
  assert (b0 = b). congruence. subst b0.
  assert (chunk0 = chunk). congruence. subst chunk0.
  assert (loadv chunk m (Vptr b Int.zero) = Some v). assumption.
  generalize (loadv_inject _ _ _ _ _ _ _ H1 H5 H7).
  intros [tv [LOAD INJ]].
  exists tv; split. 
  eapply make_load_correct; eauto. eapply make_stackaddr_correct; eauto.
  auto.
  (* var_global_scalar *)
  inversion H4. subst m0. inversion H2; [congruence|subst]. 
  assert (match_globalenvs f). eapply match_callstack_match_globalenvs; eauto.
  inversion H9. destruct (mg_symbols0 _ _ H7) as [A B].
  assert (chunk0 = chunk). congruence. subst chunk0.
  assert (loadv chunk m (Vptr b Int.zero) = Some v). assumption.
  assert (val_inject f (Vptr b Int.zero) (Vptr b Int.zero)).
    econstructor; eauto. 
  generalize (loadv_inject _ _ _ _ _ _ _ H1 H10 H11).
  intros [tv [LOAD INJ]].
  exists tv; split. 
  eapply make_load_correct; eauto. eapply make_globaladdr_correct; eauto.
  auto.
Qed.

Lemma var_addr_correct:
  forall cenv id a f e te sp lo hi m cs tm b lv le,
  var_addr cenv id = Some a ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) m.(nextblock) tm.(nextblock) m ->
  eval_var prog e id b lv ->
  exists tv,
    eval_expr tge (Vptr sp Int.zero) le te tm a te tm tv /\
    val_inject f (Vptr b Int.zero) tv.
Proof.
  intros until le. unfold var_addr. 
  caseEq (cenv!id). 2: intros; discriminate.
  intros vi EQ. intros.
  assert (match_var f id e m te sp vi).
    inversion H0. inversion H15. auto.
  caseEq vi; intros; rewrite H3 in H; simplify_eq H; clear H; intros; subst a;
  rewrite H3 in H2; inversion H2.
  (* var_stack_scalar *)
  subst m0 z. inversion H1; [subst|congruence]. 
  exists (Vptr sp (Int.repr ofs)); split.
  eapply make_stackaddr_correct.
  replace b with b0. auto. congruence.
  (* var_stack_array *)
  subst z. inversion H1; [subst|congruence]. 
  exists (Vptr sp (Int.repr ofs)); split.
  eapply make_stackaddr_correct.
  replace b with b0. auto. congruence.
  (* var_global_scalar *)
  subst m0. inversion H1; [congruence|subst].
  assert (match_globalenvs f). eapply match_callstack_match_globalenvs; eauto.
  inversion H3. destruct (mg_symbols0 _ _ H6) as [A B].
  exists (Vptr b Int.zero); split.
  eapply make_globaladdr_correct. eauto.
  econstructor; eauto. 
  (* var_global_array *)
  inversion H1; [congruence|subst].
  assert (match_globalenvs f). eapply match_callstack_match_globalenvs; eauto.
  inversion H3. destruct (mg_symbols0 _ _ H6) as [A B].
  exists (Vptr b Int.zero); split.
  eapply make_globaladdr_correct. eauto.
  econstructor; eauto. 
Qed.

Lemma var_set_correct:
  forall cenv id rhs a f e te2 sp lo hi m2 cs tm2 le te1 tm1 vrhs b chunk v1 v2 m3,
  var_set cenv id rhs = Some a ->
  match_callstack f (mkframe cenv e te2 sp lo hi :: cs) m2.(nextblock) tm2.(nextblock) m2 ->
  eval_expr tge (Vptr sp Int.zero) le te1 tm1 rhs te2 tm2 vrhs ->
  val_inject f v1 vrhs ->
  mem_inject f m2 tm2 ->
  eval_var prog e id b (Vscalar chunk) ->
  cast chunk v1 = Some v2 ->
  store chunk m2 b 0 v2 = Some m3 ->
  exists te3, exists tm3, exists tv,
    eval_expr tge (Vptr sp Int.zero) le te1 tm1 a te3 tm3 tv /\
    val_inject f v2 tv /\
    mem_inject f m3 tm3 /\
    match_callstack f (mkframe cenv e te3 sp lo hi :: cs) m3.(nextblock) tm3.(nextblock) m3.
Proof.
  intros until m3. unfold var_set.
  caseEq (cenv!id). 2:intros;congruence. intros vi EQ; intros.
  assert (NEXTBLOCK: nextblock m3 = nextblock m2).
    generalize (store_inv _ _ _ _ _ _ H6). simpl. tauto.
  inversion H0. subst f0 cenv0 e0 te sp0 lo0 hi0 cs0 bound tbound m.
  inversion H20. 
  caseEq vi; intros; subst vi; simplify_eq H; clear H; intros; subst a.
  (* var_local *)
  generalize (me_vars0 _ _ EQ); intro. inversion H. subst chunk0.
  inversion H4; [subst|congruence]. 
  assert (b0 = b). congruence. subst b0.
  assert (m = chunk). congruence. subst m.  
  elim (make_cast_correct _ _ _ _ _ _ _ _ _ _ _ _ H1 H5 H2).
  intros tv [EVAL [INJ NORM]].
  exists (PTree.set id tv te2); exists tm2; exists tv.
  split. eapply eval_Eassign. auto. 
  split. auto.
  split. eapply store_unmapped_inject; eauto. 
  rewrite NEXTBLOCK. eapply match_callstack_store_local; eauto.
  (* var_stack_scalar *)
  generalize (me_vars0 _ _ EQ); intro. inversion H.
  subst chunk0 z. 
  inversion H4; [subst|congruence]. 
  assert (b0 = b). congruence. subst b0.
  assert (m = chunk). congruence. subst m.  
  assert (storev chunk m2 (Vptr b Int.zero) v2 = Some m3). assumption.
  generalize (make_stackaddr_correct sp le te1 tm1 ofs). intro EVALSTACKADDR.
  generalize (make_store_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 EVALSTACKADDR H1 H5 H8 H3 H10 H2).
  intros [tm3 [tv [EVAL [MEMINJ [VALINJ TNEXTBLOCK]]]]].
  exists te2; exists tm3; exists tv.
  split. auto. split. auto. split. auto. 
  rewrite NEXTBLOCK; rewrite TNEXTBLOCK.
  eapply match_callstack_mapped; eauto. 
  inversion H10; congruence.
  (* var_global_scalar *)
  generalize (me_vars0 _ _ EQ); intro. inversion H.
  subst chunk0.
  inversion H4; [congruence|subst]. 
  assert (m = chunk). congruence. subst m.  
  assert (storev chunk m2 (Vptr b Int.zero) v2 = Some m3). assumption.
  assert (match_globalenvs f). eapply match_callstack_match_globalenvs; eauto.
  inversion H13. destruct (mg_symbols0 _ _ H10) as [A B].
  assert (val_inject f (Vptr b Int.zero) (Vptr b Int.zero)). econstructor; eauto.    
  generalize (make_globaladdr_correct sp le te1 tm1 id b B). intro EVALGLOBALADDR.
  generalize (make_store_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 EVALGLOBALADDR H1 H5 H12 H3 H14 H2).
  intros [tm3 [tv [EVAL [MEMINJ [VALINJ TNEXTBLOCK]]]]].
  exists te2; exists tm3; exists tv.
  split. auto. split. auto. split. auto. 
  rewrite NEXTBLOCK; rewrite TNEXTBLOCK.
  eapply match_callstack_mapped; eauto. 
  inversion H11; congruence.
Qed.

(** * Correctness of stack allocation of local variables *)

(** This section shows the correctness of the translation of Csharpminor
  local variables, either as Cminor local variables or as sub-blocks
  of the Cminor stack data.  This is the most difficult part of the proof. *)

Remark assign_variables_incr:
  forall atk vars cenv sz cenv' sz',
  assign_variables atk vars (cenv, sz) = (cenv', sz') -> sz <= sz'.
Proof.
  induction vars; intros until sz'; simpl.
  intro. replace sz' with sz. omega. congruence.
  destruct a. destruct v. case (Identset.mem i atk); intros.
  generalize (IHvars _ _ _ _ H). 
  generalize (size_chunk_pos m). intro.
  generalize (align_le sz (size_chunk m) H0). omega.
  eauto.
  intro. generalize (IHvars _ _ _ _ H). 
  assert (8 > 0). omega. generalize (align_le sz 8 H0).
  assert (0 <= Zmax 0 z). apply Zmax_bound_l. omega.
  omega.
Qed.

Lemma match_callstack_alloc_variables_rec:
  forall tm sp cenv' sz' te lo cs atk,
  valid_block tm sp ->
  low_bound tm sp = 0 ->
  high_bound tm sp = sz' ->
  sz' <= Int.max_signed ->
  forall e m vars e' m' lb,
  alloc_variables e m vars e' m' lb ->
  forall f cenv sz,
  assign_variables atk vars (cenv, sz) = (cenv', sz') ->
  match_callstack f (mkframe cenv e te sp lo m.(nextblock) :: cs)
                    m.(nextblock) tm.(nextblock) m ->
  mem_inject f m tm ->
  0 <= sz ->
  (forall b delta, f b = Some(sp, delta) -> high_bound m b + delta <= sz) ->
  (forall id lv, In (id, lv) vars -> te!id <> None) ->
  exists f',
     inject_incr f f'
  /\ mem_inject f' m' tm
  /\ match_callstack f' (mkframe cenv' e' te sp lo m'.(nextblock) :: cs)
                        m'.(nextblock) tm.(nextblock) m'.
Proof.
  intros until atk. intros VB LB HB NOOV.
  induction 1.
  (* base case *)
  intros. simpl in H. inversion H; subst cenv sz.
  exists f. split. apply inject_incr_refl. split. auto. auto.
  (* inductive case *)
  intros until sz.
  change (assign_variables atk ((id, lv) :: vars) (cenv, sz))
  with (assign_variables atk vars (assign_variable atk (id, lv) (cenv, sz))).
  caseEq (assign_variable atk (id, lv) (cenv, sz)).
  intros cenv1 sz1 ASV1 ASVS MATCH MINJ SZPOS BOUND DEFINED.
  assert (DEFINED1: forall id0 lv0, In (id0, lv0) vars -> te!id0 <> None).
    intros. eapply DEFINED. simpl. right. eauto.
  assert (exists tv, te!id = Some tv).
    assert (te!id <> None). eapply DEFINED. simpl; left; auto.
    destruct (te!id). exists v; auto. congruence.
  elim H1; intros tv TEID; clear H1.
  generalize ASV1. unfold assign_variable.
  caseEq lv.
  (* 1. lv = LVscalar chunk *)
  intros chunk LV. case (Identset.mem id atk).
  (* 1.1 info = Var_stack_scalar chunk ... *)
    set (ofs := align sz (size_chunk chunk)).
    intro EQ; injection EQ; intros; clear EQ.
    set (f1 := extend_inject b1 (Some (sp, ofs)) f).
    generalize (size_chunk_pos chunk); intro SIZEPOS.
    generalize (align_le sz (size_chunk chunk) SIZEPOS). fold ofs. intro SZOFS.
    assert (mem_inject f1 m1 tm /\ inject_incr f f1).
      assert (Int.min_signed < 0). compute; auto.
      generalize (assign_variables_incr _ _ _ _ _ _ ASVS). intro.
      unfold f1; eapply alloc_mapped_inject; eauto.
      omega. omega. omega. omega. unfold sizeof; rewrite LV. omega. 
      intros. left. generalize (BOUND _ _ H5). omega. 
    elim H3; intros MINJ1 INCR1; clear H3.
    assert (MATCH1: match_callstack f1
             (mkframe cenv1 (PTree.set id (b1, lv) e) te sp lo (nextblock m1) :: cs)
             (nextblock m1) (nextblock tm) m1).
    unfold f1; rewrite <- H2; eapply match_callstack_alloc_left; eauto.
    assert (SZ1POS: 0 <= sz1). rewrite <- H1. omega.
    assert (BOUND1: forall b delta, f1 b = Some(sp, delta) ->
                                    high_bound m1 b + delta <= sz1).
      intros until delta; unfold f1, extend_inject, eq_block.
      rewrite (high_bound_alloc _ _ b _ _ _ H).
      case (zeq b b1); intros. 
      inversion H3. unfold sizeof; rewrite LV. omega.
      generalize (BOUND _ _ H3). omega. 
    generalize (IHalloc_variables _ _ _ ASVS MATCH1 MINJ1 SZ1POS BOUND1 DEFINED1).
    intros [f' [INCR2 [MINJ2 MATCH2]]].
    exists f'; intuition. eapply inject_incr_trans; eauto. 
  (* 1.2 info = Var_local chunk *)
    intro EQ; injection EQ; intros; clear EQ. subst sz1.
    generalize (alloc_unmapped_inject _ _ _ _ _ _ _ MINJ H).
    set (f1 := extend_inject b1 None f). intros [MINJ1 INCR1].
    assert (MATCH1: match_callstack f1
             (mkframe cenv1 (PTree.set id (b1, lv) e) te sp lo (nextblock m1) :: cs)
             (nextblock m1) (nextblock tm) m1).
    unfold f1; rewrite <- H2; eapply match_callstack_alloc_left; eauto.
    assert (BOUND1: forall b delta, f1 b = Some(sp, delta) ->
                                    high_bound m1 b + delta <= sz).
      intros until delta; unfold f1, extend_inject, eq_block.
      rewrite (high_bound_alloc _ _ b _ _ _ H).
      case (zeq b b1); intros. discriminate.
      eapply BOUND; eauto.
    generalize (IHalloc_variables _ _ _ ASVS MATCH1 MINJ1 SZPOS BOUND1 DEFINED1).
    intros [f' [INCR2 [MINJ2 MATCH2]]].
    exists f'; intuition. eapply inject_incr_trans; eauto. 
  (* 2. lv = LVarray dim, info = Var_stack_array *)
  intros dim LV EQ. injection EQ; clear EQ; intros.
  assert (0 <= Zmax 0 dim). apply Zmax1. 
  assert (8 > 0). omega.
  generalize (align_le sz 8 H4). intro.
  set (ofs := align sz 8) in *.
  set (f1 := extend_inject b1 (Some (sp, ofs)) f).
  assert (mem_inject f1 m1 tm /\ inject_incr f f1).
    assert (Int.min_signed < 0). compute; auto.
    generalize (assign_variables_incr _ _ _ _ _ _ ASVS). intro.
    unfold f1; eapply alloc_mapped_inject; eauto.
    omega. omega. omega. omega. unfold sizeof; rewrite LV. omega. 
    intros. left. generalize (BOUND _ _ H8). omega. 
    elim H6; intros MINJ1 INCR1; clear H6.
    assert (MATCH1: match_callstack f1
             (mkframe cenv1 (PTree.set id (b1, lv) e) te sp lo (nextblock m1) :: cs)
             (nextblock m1) (nextblock tm) m1).
    unfold f1; rewrite <- H2; eapply match_callstack_alloc_left; eauto.
    assert (SZ1POS: 0 <= sz1). rewrite <- H1. omega.
    assert (BOUND1: forall b delta, f1 b = Some(sp, delta) ->
                                    high_bound m1 b + delta <= sz1).
      intros until delta; unfold f1, extend_inject, eq_block.
      rewrite (high_bound_alloc _ _ b _ _ _ H).
      case (zeq b b1); intros. 
      inversion H6. unfold sizeof; rewrite LV. omega.
      generalize (BOUND _ _ H6). omega. 
    generalize (IHalloc_variables _ _ _ ASVS MATCH1 MINJ1 SZ1POS BOUND1 DEFINED1).
    intros [f' [INCR2 [MINJ2 MATCH2]]].
    exists f'; intuition. eapply inject_incr_trans; eauto. 
Qed.

Lemma set_params_defined:
  forall params args id,
  In id params -> (set_params args params)!id <> None.
Proof.
  induction params; simpl; intros.
  elim H.
  destruct args.
  rewrite PTree.gsspec. case (peq id a); intro.
  congruence. eapply IHparams. elim H; intro. congruence. auto.
  rewrite PTree.gsspec. case (peq id a); intro.
  congruence. eapply IHparams. elim H; intro. congruence. auto.
Qed.

Lemma set_locals_defined:
  forall e vars id,
  In id vars \/ e!id <> None -> (set_locals vars e)!id <> None.
Proof.
  induction vars; simpl; intros.
  tauto.
  rewrite PTree.gsspec. case (peq id a); intro.
  congruence.
  apply IHvars. assert (a <> id). congruence. tauto.
Qed.

Lemma set_locals_params_defined:
  forall args params vars id,
  In id (params ++ vars) ->
  (set_locals vars (set_params args params))!id <> None.
Proof.
  intros. apply set_locals_defined. 
  elim (in_app_or _ _ _ H); intro. 
  right. apply set_params_defined; auto.
  left; auto.
Qed.

(** Preservation of [match_callstack] by simultaneous allocation
  of Csharpminor local variables and of the Cminor stack data block. *)

Lemma match_callstack_alloc_variables:
  forall fn cenv sz m e m' lb tm tm' sp f cs targs,
  build_compilenv gce fn = (cenv, sz) ->
  sz <= Int.max_signed ->
  alloc_variables Csharpminor.empty_env m (fn_variables fn) e m' lb ->
  Mem.alloc tm 0 sz = (tm', sp) ->
  match_callstack f cs m.(nextblock) tm.(nextblock) m ->
  mem_inject f m tm ->
  let tparams := List.map (@fst ident memory_chunk) fn.(Csharpminor.fn_params) in
  let tvars := List.map (@fst ident var_kind) fn.(Csharpminor.fn_vars) in
  let te := set_locals tvars (set_params targs tparams) in
  exists f',
     inject_incr f f'
  /\ mem_inject f' m' tm'
  /\ match_callstack f' (mkframe cenv e te sp m.(nextblock) m'.(nextblock) :: cs)
                        m'.(nextblock) tm'.(nextblock) m'.
Proof.
  intros. 
  assert (SP: sp = nextblock tm). injection H2; auto.
  unfold build_compilenv in H. 
  eapply match_callstack_alloc_variables_rec with (sz' := sz); eauto.
  eapply valid_new_block; eauto.
  rewrite (low_bound_alloc _ _ sp _ _ _ H2). apply zeq_true.
  rewrite (high_bound_alloc _ _ sp _ _ _ H2). apply zeq_true. 
  (* match_callstack *)
  constructor. omega. change (valid_block tm' sp). eapply valid_new_block; eauto.
  constructor. 
    (* me_vars *)
    intros. generalize (global_compilenv_charact _ _ H5). 
    intros [lv [A B]].
    destruct vi; simpl in B; try contradiction.
    constructor.
      unfold Csharpminor.empty_env. apply PTree.gempty. 
      congruence.
    destruct B as [sz1 C].
    apply match_var_global_array with sz1.
      unfold Csharpminor.empty_env. apply PTree.gempty. 
      congruence.
    (* me_low_high *)
    omega.
    (* me_bounded *)
    intros until lv. unfold Csharpminor.empty_env. rewrite PTree.gempty. congruence.
    (* me_inj *)
    intros until lv2. unfold Csharpminor.empty_env; rewrite PTree.gempty; congruence.
    (* me_inv *)
    intros. elim (mi_mappedblocks _ _ _ H4 _ _ _ H5); intros.
    elim (fresh_block_alloc _ _ _ _ _ H2 H6).
    (* me_incr *)
    intros. elim (mi_mappedblocks _ _ _ H4 _ _ _ H5); intros.
    rewrite SP; auto.
  rewrite SP; auto.
  eapply alloc_right_inject; eauto.
  omega.
  intros. elim (mi_mappedblocks _ _ _ H4 _ _ _ H5); intros.
  unfold block in SP; omegaContradiction.
  (* defined *)
  intros. unfold te. apply set_locals_params_defined. 
  unfold tparams, tvars. unfold fn_variables in H5.
  change Csharpminor.fn_params with Csharpminor.fn_params in H5. 
  change Csharpminor.fn_vars with Csharpminor.fn_vars in H5. 
  elim (in_app_or _ _ _ H5); intros.
  elim (list_in_map_inv _ _ _ H6). intros x [A B].
  apply in_or_app; left. inversion A. apply List.in_map. auto.
  apply in_or_app; right. 
  change id with (fst (id, lv)). apply List.in_map; auto.
Qed.

(** Characterization of the range of addresses for the blocks allocated
  to hold Csharpminor local variables. *)

Lemma alloc_variables_nextblock_incr:
  forall e1 m1 vars e2 m2 lb,
  alloc_variables e1 m1 vars e2 m2 lb ->
  nextblock m1 <= nextblock m2.
Proof.
  induction 1; intros.
  omega.
  inversion H; subst m1; simpl in IHalloc_variables. omega.
Qed.

Lemma alloc_variables_list_block:
  forall e1 m1 vars e2 m2 lb,
  alloc_variables e1 m1 vars e2 m2 lb ->
  forall b, m1.(nextblock) <= b < m2.(nextblock) <-> In b lb.
Proof.
  induction 1; intros.
  simpl; split; intro. omega. contradiction.
  elim (IHalloc_variables b); intros A B.
  assert (nextblock m = b1). injection H; intros. auto.
  assert (nextblock m1 = Zsucc (nextblock m)).
    injection H; intros; subst m1; reflexivity.
  simpl; split; intro. 
  assert (nextblock m = b \/ nextblock m1 <= b < nextblock m2).
    unfold block; rewrite H2; omega.
  elim H4; intro. left; congruence. right; auto.
  elim H3; intro. subst b b1. 
  generalize (alloc_variables_nextblock_incr _ _ _ _ _ _ H0). 
  rewrite H2. omega.
  generalize (B H4). rewrite H2. omega.
Qed.

(** Correctness of the code generated by [store_parameters]
  to store in memory the values of parameters that are stack-allocated. *)

Inductive vars_vals_match:
    meminj -> list (ident * memory_chunk) -> list val -> env -> Prop :=
  | vars_vals_nil:
      forall f te,
      vars_vals_match f nil nil te
  | vars_vals_cons:
      forall f te id chunk vars v vals tv,
      te!id = Some tv ->
      val_inject f v tv ->
      vars_vals_match f vars vals te ->
      vars_vals_match f ((id, chunk) :: vars) (v :: vals) te.

Lemma vars_vals_match_extensional:
  forall f vars vals te,
  vars_vals_match f vars vals te ->
  forall te',
  (forall id lv, In (id, lv) vars -> te'!id = te!id) ->
  vars_vals_match f vars vals te'.
Proof.
  induction 1; intros.
  constructor.
  econstructor; eauto. rewrite <- H. eapply H2. left. reflexivity.
  apply IHvars_vals_match. intros. eapply H2; eauto. right. eauto.
Qed.

Lemma store_parameters_correct:
  forall e m1 params vl m2,
  bind_parameters e m1 params vl m2 ->
  forall f te1 cenv sp lo hi cs tm1,
  vars_vals_match f params vl te1 ->
  list_norepet (List.map (@fst ident memory_chunk) params) ->
  mem_inject f m1 tm1 ->
  match_callstack f (mkframe cenv e te1 sp lo hi :: cs) m1.(nextblock) tm1.(nextblock) m1 ->
  (forall id chunk, In (id, chunk) params -> cenv!id <> None) ->
  exists te2, exists tm2,
     exec_stmt tge (Vptr sp Int.zero)
                   te1 tm1 (store_parameters cenv params)
                   te2 tm2 Out_normal
  /\ mem_inject f m2 tm2
  /\ match_callstack f (mkframe cenv e te2 sp lo hi :: cs) m2.(nextblock) tm2.(nextblock) m2.
Proof.
  induction 1.
  (* base case *)
  intros; simpl. exists te1; exists tm1. split. constructor. tauto.
  (* inductive case *)
  intros until tm1.  intros VVM NOREPET MINJ MATCH. simpl.
  inversion VVM. subst f0 id0 chunk0 vars v vals te.
  inversion MATCH. subst f0 cenv0 e0 te sp0 lo0 hi0 cs0 bound tbound m0.
  inversion H19. 
  inversion NOREPET. subst hd tl.
  assert (NEXT: nextblock m1 = nextblock m).
    generalize (store_inv _ _ _ _ _ _ H1). simpl; tauto. 
  caseEq (cenv!id); intros.
  destruct v; generalize (me_vars0 _ _ H3); intro MV; inversion MV; subst.
  (* cenv!id = Some(Var_local chunk) *)
  assert (b0 = b). congruence. subst b0.
  assert (m0 = chunk). congruence. subst m0.
  assert (v' = tv). congruence. subst v'.
  assert (eval_expr tge (Vptr sp Int.zero) nil te1 tm1 (Evar id) te1 tm1 tv).
    constructor. auto.
  generalize (make_cast_correct _ _ _ _ _ _ _ _ _ _ _ _
               H7 H0 H11).
  intros [tv' [EVAL1 [VINJ1 VNORM]]].
  set (te2 := PTree.set id tv' te1).
  assert (VVM2: vars_vals_match f params vl te2).
    apply vars_vals_match_extensional with te1; auto.
    intros. unfold te2; apply PTree.gso. red; intro; subst id0.
    elim H5. change id with (fst (id, lv)). apply List.in_map; auto.
  generalize (store_unmapped_inject _ _ _ _ _ _ _ _ MINJ H1 H13); intro MINJ2.
  generalize (match_callstack_store_local _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                H VINJ1 VNORM H1 MATCH); 
  fold te2; rewrite <- NEXT; intro MATCH2.
  assert (forall id chunk, In (id, chunk) params -> cenv!id <> None). intros; eauto.
  destruct (IHbind_parameters _ _ _ _ _ _ _ _ VVM2 H6 MINJ2 MATCH2 H16)
        as [te3 [tm3 [EXEC3 [MINJ3 MATCH3]]]].
  exists te3; exists tm3. 
  (* execution *)
  split. apply exec_Sseq_continue with te2 tm1. 
  econstructor. unfold te2. constructor. assumption. 
  assumption.
  (* meminj & match_callstack *)
  tauto.

  (* cenv!!id = Some(Var_stack_scalar) *)
  assert (b0 = b). congruence. subst b0.
  assert (m0 = chunk). congruence. subst m0.
  pose (EVAL1 := make_stackaddr_correct sp nil te1 tm1 z).
  assert (EVAL2: eval_expr tge (Vptr sp Int.zero) nil te1 tm1 (Evar id) te1 tm1 tv).
    constructor. auto.
  destruct (make_store_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (Vptr b Int.zero) _
              EVAL1 EVAL2 H0 H1 MINJ H13 H11) 
  as [tm2 [tv' [EVAL3 [MINJ2 [VINJ NEXT1]]]]].
  assert (f b <> None). inversion H13. congruence.
  generalize (match_callstack_mapped _ _ _ _ _ MATCH _ _ _ _ _ H7 H1).
  rewrite <- NEXT; rewrite <- NEXT1; intro MATCH2.
  assert (forall id chunk, In (id, chunk) params -> cenv!id <> None). intros; eauto.
  destruct (IHbind_parameters _ _ _ _ _ _ _ _
              H12 H6 MINJ2 MATCH2 H8) as [te3 [tm3 [EVAL4 [MINJ3 MATCH3]]]].
  exists te3; exists tm3.
  (* execution *)
  split. apply exec_Sseq_continue with te1 tm2. 
  econstructor. eauto.
  assumption.
  (* meminj & match_callstack *)
  tauto.

  (* Impossible cases on cenv!!id *)
  congruence. 
  congruence.
  congruence.
  elim (H4 id chunk); auto.
Qed.

Lemma vars_vals_match_holds_1:
  forall f params args targs,
  list_norepet (List.map (@fst ident memory_chunk) params) ->
  List.length params = List.length args ->
  val_list_inject f args targs ->
  vars_vals_match f params args
    (set_params targs (List.map (@fst ident memory_chunk) params)).
Proof.
  induction params; destruct args; simpl; intros; try discriminate.
  constructor.
  inversion H1. subst v0 vl targs. 
  inversion H. subst hd tl.
  destruct a as [id chunk]. econstructor. 
  simpl. rewrite PTree.gss. reflexivity.
  auto. 
  apply vars_vals_match_extensional
  with (set_params vl' (map (@fst ident memory_chunk) params)).
  eapply IHparams; eauto. 
  intros. simpl. apply PTree.gso. red; intro; subst id0.
  elim H5. change (fst (id, chunk)) with (fst (id, lv)). 
  apply List.in_map; auto.
Qed.

Lemma vars_vals_match_holds:
  forall f params args targs,
  List.length params = List.length args ->
  val_list_inject f args targs ->
  forall vars,
  list_norepet (List.map (@fst ident var_kind) vars
             ++ List.map (@fst ident memory_chunk) params) ->
  vars_vals_match f params args
    (set_locals (List.map (@fst ident var_kind) vars)
      (set_params targs (List.map (@fst ident memory_chunk) params))).
Proof.
  induction vars; simpl; intros.
  eapply vars_vals_match_holds_1; eauto.
  inversion H1. subst hd tl.
  eapply vars_vals_match_extensional; eauto.
  intros. apply PTree.gso. red; intro; subst id; elim H4.
  apply in_or_app. right. change (fst a) with (fst (fst a, lv)).
  apply List.in_map; auto.
Qed.

Lemma bind_parameters_length:
  forall e m1 params args m2,
  bind_parameters e m1 params args m2 ->
  List.length params = List.length args.
Proof.
  induction 1; simpl; eauto.
Qed.

Lemma build_compilenv_domain:
  forall f id chunk,
  In (id, chunk) f.(Csharpminor.fn_params) -> 
  (fst (build_compilenv gce f))!id <> None.
Proof.
  assert (forall atk id lv cenv_sz id0,
    let cenv_sz' := assign_variable atk (id, lv) cenv_sz in
    (fst cenv_sz')!id <> None
    /\ ((fst cenv_sz)!id0 <> None -> (fst cenv_sz')!id0 <> None)).
  intros. unfold cenv_sz'. destruct cenv_sz as [cenv sz].
  unfold assign_variable. destruct lv.
  case (Identset.mem id atk); simpl. split. rewrite PTree.gss. congruence.
  rewrite PTree.gsspec. case (peq id0 id); intros. congruence. auto.
  split. rewrite PTree.gss. congruence.
  rewrite PTree.gsspec. case (peq id0 id); intros. congruence. auto.
  simpl. split. rewrite PTree.gss. congruence.
  rewrite PTree.gsspec. case (peq id0 id); intros. congruence. auto.

  assert (forall atk id_lv_list cenv_sz id lv,
    In (id, lv) id_lv_list \/ (fst cenv_sz)!id <> None ->
    (fst (assign_variables atk id_lv_list cenv_sz))!id <> None).
  induction id_lv_list; simpl; intros. 
  tauto.
  apply IHid_lv_list with lv. 
  destruct a as [id0 lv0].
  generalize (H atk id0 lv0 cenv_sz id). 
  simpl. intro. intuition. injection H0; intros; subst id0 lv0. intuition. 

  intros. unfold build_compilenv. apply H0 with (Vscalar chunk). 
  left. unfold fn_variables. apply List.in_or_app. left. 
  set (g := fun (id_chunk : ident * memory_chunk) => (fst id_chunk, Vscalar (snd id_chunk))).
  change positive with ident.
  change (id, Vscalar chunk) with (g (id, chunk)). 
  apply List.in_map. auto.
Qed.

(** The final result in this section: the behaviour of function entry
  in the generated Cminor code (allocate stack data block and store
  parameters whose address is taken) simulates what happens at function
  entry in the original Csharpminor (allocate one block per local variable
  and initialize the blocks corresponding to function parameters). *)

Lemma function_entry_ok:
  forall fn m e m1 lb vargs m2 f cs tm cenv sz tm1 sp tvargs,
  alloc_variables empty_env m (fn_variables fn) e m1 lb ->
  bind_parameters e m1 fn.(Csharpminor.fn_params) vargs m2 ->
  match_callstack f cs m.(nextblock) tm.(nextblock) m ->
  build_compilenv gce fn = (cenv, sz) ->
  sz <= Int.max_signed ->
  Mem.alloc tm 0 sz = (tm1, sp) ->
  let te :=
    set_locals (fn_vars_names fn) (set_params tvargs (fn_params_names fn)) in
  val_list_inject f vargs tvargs ->
  mem_inject f m tm ->
  list_norepet (fn_params_names fn ++ fn_vars_names fn) ->
  exists f2, exists te2, exists tm2,
     exec_stmt tge (Vptr sp Int.zero)
               te tm1 (store_parameters cenv fn.(Csharpminor.fn_params))
               te2 tm2 Out_normal
  /\ mem_inject f2 m2 tm2
  /\ inject_incr f f2
  /\ match_callstack f2
       (mkframe cenv e te2 sp m.(nextblock) m1.(nextblock) :: cs)
       m2.(nextblock) tm2.(nextblock) m2
  /\ (forall b, m.(nextblock) <= b < m1.(nextblock) <-> In b lb).
Proof.
  intros. 
  generalize (bind_parameters_length _ _ _ _ _ H0); intro LEN1.
  destruct (match_callstack_alloc_variables _ _ _ _ _ _ _ _ _ _ _ _ tvargs
              H2 H3 H H4 H1 H6)
  as [f1 [INCR1 [MINJ1 MATCH1]]].
  fold te in MATCH1. 
  assert (VLI: val_list_inject f1 vargs tvargs).
    eapply val_list_inject_incr; eauto.
  generalize (vars_vals_match_holds _ _ _ _ LEN1 VLI _ 
                (list_norepet_append_commut _ _ H7)).
  fold te. intro VVM.
  assert (NOREPET: list_norepet (List.map (@fst ident memory_chunk) fn.(Csharpminor.fn_params))).
    unfold fn_params_names in H7.
    eapply list_norepet_append_left; eauto.
  generalize (build_compilenv_domain fn). rewrite H2. intro.
  destruct (store_parameters_correct _ _ _ _ _ H0 _ _ _ _ _ _ _ _
                    VVM NOREPET MINJ1 MATCH1 H8)
  as [te2 [tm2 [EXEC [MINJ2 MATCH2]]]].
  exists f1; exists te2; exists tm2.
  split. auto. split. auto. split. auto. split. auto.
  intros; eapply alloc_variables_list_block; eauto. 
Qed.

(** * Semantic preservation for the translation *)

(** These tactics simplify hypotheses of the form [f ... = Some x]. *)

Ltac monadSimpl1 :=
  match goal with
  | [ |- (bind _ _ ?F ?G = Some ?X) -> _ ] =>
      unfold bind at 1;
      generalize (refl_equal F);
      pattern F at -1 in |- *;
      case F;
      [ (let EQ := fresh "EQ" in
          (intro; intro EQ;
           try monadSimpl1))
      | intros; discriminate ]
  | [ |- (None = Some _) -> _ ] =>
      intro; discriminate
  | [ |- (Some _ = Some _) -> _ ] =>
      let h := fresh "H" in
      (intro h; injection h; intro; clear h)
  end.

Ltac monadSimpl :=
  match goal with
  | [ |- (bind _ _ ?F ?G = Some ?X) -> _ ] => monadSimpl1
  | [ |- (None = Some _) -> _ ] => monadSimpl1
  | [ |- (Some _ = Some _) -> _ ] => monadSimpl1
  | [ |- (?F _ _ _ _ _ _ _ = Some _) -> _ ] => simpl F; monadSimpl1
  | [ |- (?F _ _ _ _ _ _ = Some _) -> _ ] => simpl F; monadSimpl1
  | [ |- (?F _ _ _ _ _ = Some _) -> _ ] => simpl F; monadSimpl1
  | [ |- (?F _ _ _ _ = Some _) -> _ ] => simpl F; monadSimpl1
  | [ |- (?F _ _ _ = Some _) -> _ ] => simpl F; monadSimpl1
  | [ |- (?F _ _ = Some _) -> _ ] => simpl F; monadSimpl1
  | [ |- (?F _ = Some _) -> _ ] => simpl F; monadSimpl1
  end.

Ltac monadInv H :=
  generalize H; monadSimpl.

(** The proof of semantic preservation uses simulation diagrams of the
  following form:
<<
     le, e, m1, a --------------- tle, sp, te1, tm1, ta
          |                                |
          |                                |
          v                                v
     le, e, m2, v --------------- tle, sp, te2, tm2, tv
>>
  where [ta] is the Cminor expression obtained by translating the
  Csharpminor expression [a].  The left vertical arrow is an evaluation
  of a Csharpminor expression.  The right vertical arrow is an evaluation
  of a Cminor expression.  The precondition (top vertical bar)
  includes a [mem_inject] relation between the memory states [m1] and [tm1],
  a [val_list_inject] relation between the let environments [le] and [tle],
  and a [match_callstack] relation for any callstack having
  [e], [te1], [sp] as top frame.  The postcondition (bottom vertical bar)
  is the existence of a memory injection [f2] that extends the injection
  [f1] we started with, preserves the [match_callstack] relation for
  the transformed callstack at the final state, and validates a
  [val_inject] relation between the result values [v] and [tv].

  We capture these diagrams by the following predicates, parameterized
  over the Csharpminor executions, which will serve as induction
  hypotheses in the proof of simulation. *)

Definition eval_expr_prop
    (le: Csharpminor.letenv) (e: Csharpminor.env) (m1: mem) (a: Csharpminor.expr) (m2: mem) (v: val) : Prop :=
  forall cenv ta f1 tle te1 tm1 sp lo hi cs
  (TR: transl_expr cenv a = Some ta)
  (LINJ: val_list_inject f1 le tle)
  (MINJ: mem_inject f1 m1 tm1)
  (MATCH: match_callstack f1
           (mkframe cenv e te1 sp lo hi :: cs)
           m1.(nextblock) tm1.(nextblock) m1),
  exists f2, exists te2, exists tm2, exists tv,
     eval_expr tge (Vptr sp Int.zero) tle te1 tm1 ta te2 tm2 tv
  /\ val_inject f2 v tv
  /\ mem_inject f2 m2 tm2
  /\ inject_incr f1 f2
  /\ match_callstack f2
        (mkframe cenv e te2 sp lo hi :: cs)
        m2.(nextblock) tm2.(nextblock) m2.

Definition eval_exprlist_prop
    (le: Csharpminor.letenv) (e: Csharpminor.env) (m1: mem) (al: Csharpminor.exprlist) (m2: mem) (vl: list val) : Prop :=
  forall cenv tal f1 tle te1 tm1 sp lo hi cs
  (TR: transl_exprlist cenv al = Some tal)
  (LINJ: val_list_inject f1 le tle)
  (MINJ: mem_inject f1 m1 tm1)
  (MATCH: match_callstack f1
           (mkframe cenv e te1 sp lo hi :: cs)
           m1.(nextblock) tm1.(nextblock) m1),
  exists f2, exists te2, exists tm2, exists tvl,
     eval_exprlist tge (Vptr sp Int.zero) tle te1 tm1 tal te2 tm2 tvl
  /\ val_list_inject f2 vl tvl
  /\ mem_inject f2 m2 tm2
  /\ inject_incr f1 f2
  /\ match_callstack f2
        (mkframe cenv e te2 sp lo hi :: cs)
        m2.(nextblock) tm2.(nextblock) m2.

Definition eval_funcall_prop
    (m1: mem) (fn: Csharpminor.function) (args: list val) (m2: mem) (res: val) : Prop :=
  forall tfn f1 tm1 cs targs
  (TR: transl_function gce fn = Some tfn)
  (MINJ: mem_inject f1 m1 tm1)
  (MATCH: match_callstack f1 cs m1.(nextblock) tm1.(nextblock) m1)
  (ARGSINJ: val_list_inject f1 args targs),
  exists f2, exists tm2, exists tres,
     eval_funcall tge tm1 tfn targs tm2 tres
  /\ val_inject f2 res tres
  /\ mem_inject f2 m2 tm2
  /\ inject_incr f1 f2
  /\ match_callstack f2 cs m2.(nextblock) tm2.(nextblock) m2.

Inductive outcome_inject (f: meminj) : Csharpminor.outcome -> outcome -> Prop :=
  | outcome_inject_normal:
      outcome_inject f Csharpminor.Out_normal Out_normal
  | outcome_inject_exit:
      forall n, outcome_inject f (Csharpminor.Out_exit n) (Out_exit n)
  | outcome_inject_return_none:
      outcome_inject f (Csharpminor.Out_return None) (Out_return None)
  | outcome_inject_return_some:
      forall v1 v2,
      val_inject f v1 v2 ->
      outcome_inject f (Csharpminor.Out_return (Some v1)) (Out_return (Some v2)).

Definition exec_stmt_prop
    (e: Csharpminor.env) (m1: mem) (s: Csharpminor.stmt) (m2: mem) (out: Csharpminor.outcome): Prop :=
  forall cenv ts f1 te1 tm1 sp lo hi cs
  (TR: transl_stmt cenv s = Some ts)
  (MINJ: mem_inject f1 m1 tm1)
  (MATCH: match_callstack f1
           (mkframe cenv e te1 sp lo hi :: cs)
           m1.(nextblock) tm1.(nextblock) m1),
  exists f2, exists te2, exists tm2, exists tout,
     exec_stmt tge (Vptr sp Int.zero) te1 tm1 ts te2 tm2 tout
  /\ outcome_inject f2 out tout
  /\ mem_inject f2 m2 tm2
  /\ inject_incr f1 f2
  /\ match_callstack f2
        (mkframe cenv e te2 sp lo hi :: cs)
        m2.(nextblock) tm2.(nextblock) m2.

(*
Check (eval_funcall_ind4 prog
     eval_expr_prop
     eval_exprlist_prop
     eval_funcall_prop
     exec_stmt_prop).
*)

(** There are as many cases in the inductive proof as there are evaluation
  rules in the Csharpminor semantics.  We treat each case as a separate
  lemma. *)

Lemma transl_expr_Evar_correct:
   forall (le : Csharpminor.letenv)
     (e : Csharpminor.env) (m : mem) (id : positive)
     (b : block) (chunk : memory_chunk) (v : val),
   eval_var prog e id b (Vscalar chunk) ->
   load chunk m b 0 = Some v ->
   eval_expr_prop le e m (Csharpminor.Evar id) m v.
Proof.
  intros; red; intros. unfold transl_expr in TR.
  generalize (var_get_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tle
               TR MATCH MINJ H H0).
  intros [tv [EVAL VINJ]].
  exists f1; exists te1; exists tm1; exists tv; intuition.
Qed.

Lemma transl_expr_Eassign_correct:
   forall (le : Csharpminor.letenv) (e : Csharpminor.env) (m : mem)
     (id : positive) (a : Csharpminor.expr) (m1 : mem) (b : block)
     (chunk : memory_chunk) (v1 v2 : val) (m2 : mem),
   Csharpminor.eval_expr prog le e m a m1 v1 ->
   eval_expr_prop le e m a m1 v1 ->
   eval_var prog e id b (Vscalar chunk) ->
   cast chunk v1 = Some v2 ->
   store chunk m1 b 0 v2 = Some m2 ->
   eval_expr_prop le e m (Csharpminor.Eassign id a) m2 v2.
Proof.
  intros; red; intros. monadInv TR; intro EQ0. 
  generalize (H0 _ _ _ _ _ _ _ _ _ _ EQ LINJ MINJ MATCH).
  intros [f2 [te2 [tm2 [tv1 [EVAL1 [VINJ1 [MINJ1 [INCR12 MATCH1]]]]]]]].
  generalize (var_set_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                EQ0 MATCH1 EVAL1 VINJ1 MINJ1 H1 H2 H3).
  intros [te3 [tm3 [tv2 [EVAL2 [VINJ2 [MINJ2 MATCH2]]]]]].
  exists f2; exists te3; exists tm3; exists tv2. tauto.
Qed.

Lemma transl_expr_Eaddrof_correct:
   forall (le : Csharpminor.letenv)
     (e : Csharpminor.env) (m : mem) (id : positive)
     (b : block) (lv : var_kind),
   eval_var prog e id b lv ->
   eval_expr_prop le e m (Eaddrof id) m (Vptr b Int.zero).
Proof.
  intros; red; intros. simpl in TR. 
  generalize (var_addr_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ tle
                TR MATCH H).
  intros [tv [EVAL VINJ]].
  exists f1; exists te1; exists tm1; exists tv. intuition.
Qed.

Lemma transl_expr_Eop_correct:
   forall (le : Csharpminor.letenv) (e : Csharpminor.env) (m : mem)
     (op : Csharpminor.operation) (al : Csharpminor.exprlist) (m1 : mem)
     (vl : list val) (v : val),
   Csharpminor.eval_exprlist prog le e m al m1 vl ->
   eval_exprlist_prop le e m al m1 vl ->
   Csharpminor.eval_operation op vl m1 = Some v ->
   eval_expr_prop le e m (Csharpminor.Eop op al) m1 v.
Proof.
  intros; red; intros. monadInv TR; intro EQ0.
  generalize (H0 _ _ _ _ _ _ _ _ _ _ EQ LINJ MINJ MATCH).
  intros [f2 [te2 [tm2 [tvl [EVAL1 [VINJ1 [MINJ1 [INCR1 MATCH1]]]]]]]].
  generalize (make_op_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 EQ0 H1 EVAL1 VINJ1 MINJ1).
  intros [tv [EVAL2 VINJ2]].
  exists f2; exists te2; exists tm2; exists tv. intuition.
Qed.

Lemma transl_expr_Eload_correct:
   forall (le : Csharpminor.letenv) (e : Csharpminor.env) (m : mem)
     (chunk : memory_chunk) (a : Csharpminor.expr) (m1 : mem)
     (v1 v : val),
   Csharpminor.eval_expr prog le e m a m1 v1 ->
   eval_expr_prop le e m a m1 v1 ->
   loadv chunk m1 v1 = Some v ->
   eval_expr_prop le e m (Csharpminor.Eload chunk a) m1 v.
Proof.
  intros; red; intros.
  monadInv TR. 
  destruct (H0 _ _ _ _ _ _ _ _ _ _ EQ LINJ MINJ MATCH)
  as [f2 [te2 [tm2 [tv1 [EVAL [VINJ1 [MINJ2 [INCR MATCH2]]]]]]]].
  destruct (loadv_inject _ _ _ _ _ _ _ MINJ2 H1 VINJ1)
  as [tv [TLOAD VINJ]].
  exists f2; exists te2; exists tm2; exists tv.
  intuition.
  subst ta. eapply make_load_correct; eauto. 
Qed.

Lemma transl_expr_Estore_correct:
   forall (le : Csharpminor.letenv) (e : Csharpminor.env) (m : mem)
     (chunk : memory_chunk) (a b : Csharpminor.expr) (m1 : mem)
     (v1 : val) (m2 : mem) (v2 : val) (m3 : mem) (v3 : val),
   Csharpminor.eval_expr prog le e m a m1 v1 ->
   eval_expr_prop le e m a m1 v1 ->
   Csharpminor.eval_expr prog le e m1 b m2 v2 ->
   eval_expr_prop le e m1 b m2 v2 ->
   cast chunk v2 = Some v3 ->
   storev chunk m2 v1 v3 = Some m3 ->
   eval_expr_prop le e m (Csharpminor.Estore chunk a b) m3 v3.
Proof.
  intros; red; intros. monadInv TR.
  destruct (H0 _ _ _ _ _ _ _ _ _ _ EQ LINJ MINJ MATCH)
  as [f2 [te2 [tm2 [tv1 [EVAL1 [VINJ1 [MINJ2 [INCR2 MATCH2]]]]]]]].
  assert (LINJ2: val_list_inject f2 le tle). eapply val_list_inject_incr; eauto.
  destruct (H2 _ _ _ _ _ _ _ _ _ _ EQ0 LINJ2 MINJ2 MATCH2)
  as [f3 [te3 [tm3 [tv2 [EVAL2 [VINJ2 [MINJ3 [INCR3 MATCH3]]]]]]]].
  assert (VINJ1': val_inject f3 v1 tv1). eapply val_inject_incr; eauto.
  destruct (make_store_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              EVAL1 EVAL2 H3 H4 MINJ3 VINJ1' VINJ2)
  as [tm4 [tv [EVAL [MINJ4 [VINJ4 NEXTBLOCK]]]]].
  exists f3; exists te3; exists tm4; exists tv.
  rewrite <- H6. intuition. 
  eapply inject_incr_trans; eauto.
  assert (val_inject f3 v1 tv1). eapply val_inject_incr; eauto.
  unfold storev in H4; destruct v1; try discriminate.
  inversion H5. 
  rewrite NEXTBLOCK. replace (nextblock m3) with (nextblock m2).
  eapply match_callstack_mapped; eauto. congruence. 
  generalize (store_inv _ _ _ _ _ _ H4). simpl; symmetry; tauto.
Qed.

Lemma sig_transl_function:
  forall f tf, transl_function gce f = Some tf -> tf.(fn_sig) = f.(Csharpminor.fn_sig).
Proof.
  intros f tf. unfold transl_function.
  destruct (build_compilenv gce f).
  case (zle z Int.max_signed); intros. 
  monadInv H. subst tf; reflexivity.
  congruence.
Qed.

Lemma transl_expr_Ecall_correct:
   forall (le : Csharpminor.letenv) (e : Csharpminor.env) (m : mem)
     (sig : signature) (a : Csharpminor.expr) (bl : Csharpminor.exprlist)
     (m1 m2 m3 : mem) (vf : val) (vargs : list val) (vres : val)
     (f : Csharpminor.function),
   Csharpminor.eval_expr prog le e m a m1 vf ->
   eval_expr_prop le e m a m1 vf ->
   Csharpminor.eval_exprlist prog le e m1 bl m2 vargs ->
   eval_exprlist_prop le e m1 bl m2 vargs ->
   Genv.find_funct ge vf = Some f ->
   Csharpminor.fn_sig f = sig ->
   Csharpminor.eval_funcall prog m2 f vargs m3 vres ->
   eval_funcall_prop m2 f vargs m3 vres ->
   eval_expr_prop le e m (Csharpminor.Ecall sig a bl) m3 vres.
Proof.
  intros;red;intros. monadInv TR. subst ta. 
  generalize (H0 _ _ _ _ _ _ _ _ _ _ EQ LINJ MINJ MATCH).
  intros [f2 [te2 [tm2 [tv1 [EVAL1 [VINJ1 [MINJ1 [INCR1 MATCH1]]]]]]]].
  assert (LINJ1: val_list_inject f2 le tle). eapply val_list_inject_incr; eauto.
  generalize (H2 _ _ _ _ _ _ _ _ _ _ EQ0 LINJ1 MINJ1 MATCH1).
  intros [f3 [te3 [tm3 [tv2 [EVAL2 [VINJ2 [MINJ2 [INCR2 MATCH2]]]]]]]].
  assert (tv1 = vf).
    elim (Genv.find_funct_inv H3). intros bf VF. rewrite VF in H3.
    rewrite Genv.find_funct_find_funct_ptr in H3. 
    generalize (Genv.find_funct_ptr_inv H3). intro.
    assert (match_globalenvs f2). eapply match_callstack_match_globalenvs; eauto.
    generalize (mg_functions _ H8 _ H7). intro.
    rewrite VF in VINJ1. inversion VINJ1. subst vf. 
    decEq. congruence. 
    subst ofs2. replace x with 0. reflexivity. congruence.
  subst tv1. elim (functions_translated _ _ H3). intros tf [FIND TRF].
  generalize (H6 _ _ _ _ _ TRF MINJ2 MATCH2 VINJ2).
  intros [f4 [tm4 [tres [EVAL3 [VINJ3 [MINJ3 [INCR3 MATCH3]]]]]]].
  exists f4; exists te3; exists tm4; exists tres. intuition.
  eapply eval_Ecall; eauto. rewrite <- H4. apply sig_transl_function; auto.
  apply inject_incr_trans with f2; auto. 
  apply inject_incr_trans with f3; auto.
Qed.

Lemma transl_expr_Econdition_true_correct:
   forall (le : Csharpminor.letenv) (e : Csharpminor.env) (m : mem)
     (a b c : Csharpminor.expr) (m1 : mem) (v1 : val) (m2 : mem)
     (v2 : val),
   Csharpminor.eval_expr prog le e m a m1 v1 ->
   eval_expr_prop le e m a m1 v1 ->
   Val.is_true v1 ->
   Csharpminor.eval_expr prog le e m1 b m2 v2 ->
   eval_expr_prop le e m1 b m2 v2 ->
   eval_expr_prop le e m (Csharpminor.Econdition a b c) m2 v2.
Proof.
  intros; red; intros. monadInv TR.
  destruct (H0 _ _ _ _ _ _ _ _ _ _ EQ LINJ MINJ MATCH)
  as [f2 [te2 [tm2 [tv1 [EVAL1 [VINJ1 [MINJ1 [INCR1 MATCH1]]]]]]]].
  assert (LINJ1: val_list_inject f2 le tle). eapply val_list_inject_incr; eauto.
  destruct (H3 _ _ _ _ _ _ _ _ _ _ EQ0 LINJ1 MINJ1 MATCH1)
  as [f3 [te3 [tm3 [tv2 [EVAL2 [VINJ2 [MINJ2 [INCR2 MATCH2]]]]]]]].
  exists f3; exists te3; exists tm3; exists tv2.
  intuition.
  rewrite <- H5. eapply eval_conditionalexpr_true; eauto. 
  inversion VINJ1; subst v1 tv1; simpl in H1; simpl; contradiction || auto.
  eapply inject_incr_trans; eauto.
Qed.

Lemma transl_expr_Econdition_false_correct:
   forall (le : Csharpminor.letenv) (e : Csharpminor.env) (m : mem)
     (a b c : Csharpminor.expr) (m1 : mem) (v1 : val) (m2 : mem)
     (v2 : val),
   Csharpminor.eval_expr prog le e m a m1 v1 ->
   eval_expr_prop le e m a m1 v1 ->
   Val.is_false v1 ->
   Csharpminor.eval_expr prog le e m1 c m2 v2 ->
   eval_expr_prop le e m1 c m2 v2 ->
   eval_expr_prop le e m (Csharpminor.Econdition a b c) m2 v2.
Proof.
  intros; red; intros. monadInv TR.
  destruct (H0 _ _ _ _ _ _ _ _ _ _ EQ LINJ MINJ MATCH)
  as [f2 [te2 [tm2 [tv1 [EVAL1 [VINJ1 [MINJ1 [INCR1 MATCH1]]]]]]]].
  assert (LINJ1: val_list_inject f2 le tle). eapply val_list_inject_incr; eauto.
  destruct (H3 _ _ _ _ _ _ _ _ _ _ EQ1 LINJ1 MINJ1 MATCH1)
  as [f3 [te3 [tm3 [tv2 [EVAL2 [VINJ2 [MINJ2 [INCR2 MATCH2]]]]]]]].
  exists f3; exists te3; exists tm3; exists tv2.
  intuition.
  rewrite <- H5. eapply eval_conditionalexpr_false; eauto. 
  inversion VINJ1; subst v1 tv1; simpl in H1; simpl; contradiction || auto.
  eapply inject_incr_trans; eauto.
Qed.

Lemma transl_expr_Elet_correct:
   forall (le : Csharpminor.letenv) (e : Csharpminor.env) (m : mem)
     (a b : Csharpminor.expr) (m1 : mem) (v1 : val) (m2 : mem) (v2 : val),
   Csharpminor.eval_expr prog le e m a m1 v1 ->
   eval_expr_prop le e m a m1 v1 ->
   Csharpminor.eval_expr prog (v1 :: le) e m1 b m2 v2 ->
   eval_expr_prop (v1 :: le) e m1 b m2 v2 ->
   eval_expr_prop le e m (Csharpminor.Elet a b) m2 v2.
Proof.
  intros; red; intros. monadInv TR.
  destruct (H0 _ _ _ _ _ _ _ _ _ _ EQ LINJ MINJ MATCH)
  as [f2 [te2 [tm2 [tv1 [EVAL1 [VINJ1 [MINJ1 [INCR1 MATCH1]]]]]]]].
  assert (LINJ1: val_list_inject f2 (v1 :: le) (tv1 :: tle)).
    constructor. auto. eapply val_list_inject_incr; eauto.
  destruct (H2 _ _ _ _ _ _ _ _ _ _ EQ0 LINJ1 MINJ1 MATCH1)
  as [f3 [te3 [tm3 [tv2 [EVAL2 [VINJ2 [MINJ2 [INCR2 MATCH2]]]]]]]].
  exists f3; exists te3; exists tm3; exists tv2.
  intuition.
  subst ta; eapply eval_Elet; eauto.
  eapply inject_incr_trans; eauto.
Qed.

Remark val_list_inject_nth:
  forall f l1 l2, val_list_inject f l1 l2 ->
  forall n v1, nth_error l1 n = Some v1 ->
  exists v2, nth_error l2 n = Some v2 /\ val_inject f v1 v2.
Proof.
  induction 1; destruct n; simpl; intros.
  discriminate. discriminate.
  injection H1; intros; subst v. exists v'; split; auto.
  eauto.
Qed.

Lemma transl_expr_Eletvar_correct:
   forall (le : list val) (e : Csharpminor.env) (m : mem) (n : nat)
     (v : val),
   nth_error le n = Some v ->
   eval_expr_prop le e m (Csharpminor.Eletvar n) m v.
Proof.
  intros; red; intros. monadInv TR.
  destruct (val_list_inject_nth _ _ _ LINJ _ _ H)
  as [tv [A B]].
  exists f1; exists te1; exists tm1; exists tv.
  intuition.
  subst ta. eapply eval_Eletvar; auto.
Qed.

Lemma transl_exprlist_Enil_correct:
   forall (le : Csharpminor.letenv) (e : Csharpminor.env) (m : mem),
   eval_exprlist_prop le e m Csharpminor.Enil m nil.
Proof.
  intros; red; intros. monadInv TR. 
  exists f1; exists te1; exists tm1; exists (@nil val).
  intuition. subst tal; constructor.
Qed.

Lemma transl_exprlist_Econs_correct:
   forall (le : Csharpminor.letenv) (e : Csharpminor.env) (m : mem)
     (a : Csharpminor.expr) (bl : Csharpminor.exprlist) (m1 : mem)
     (v : val) (m2 : mem) (vl : list val),
   Csharpminor.eval_expr prog le e m a m1 v ->
   eval_expr_prop le e m a m1 v ->
   Csharpminor.eval_exprlist prog le e m1 bl m2 vl ->
   eval_exprlist_prop le e m1 bl m2 vl ->
   eval_exprlist_prop le e m (Csharpminor.Econs a bl) m2 (v :: vl).
Proof.
  intros; red; intros. monadInv TR. 
  destruct (H0 _ _ _ _ _ _ _ _ _ _ EQ LINJ MINJ MATCH)
  as [f2 [te2 [tm2 [tv1 [EVAL1 [VINJ1 [MINJ2 [INCR2 MATCH2]]]]]]]].
  assert (LINJ2: val_list_inject f2 le tle). eapply val_list_inject_incr; eauto.
  destruct (H2 _ _ _ _ _ _ _ _ _ _ EQ0 LINJ2 MINJ2 MATCH2)
  as [f3 [te3 [tm3 [tv2 [EVAL2 [VINJ2 [MINJ3 [INCR3 MATCH3]]]]]]]].
  assert (VINJ1': val_inject f3 v tv1). eapply val_inject_incr; eauto.
  exists f3; exists te3; exists tm3; exists (tv1 :: tv2).
  intuition. subst tal; econstructor; eauto.
  eapply inject_incr_trans; eauto.
Qed.

Lemma transl_funcall_correct:
   forall (m : mem) (f : Csharpminor.function) (vargs : list val)
     (e : Csharpminor.env) (m1 : mem) (lb : list block) (m2 m3 : mem)
     (out : Csharpminor.outcome) (vres : val),
   list_norepet (fn_params_names f ++ fn_vars_names f) ->
   alloc_variables empty_env m (fn_variables f) e m1 lb ->
   bind_parameters e m1 (Csharpminor.fn_params f) vargs m2 ->
   Csharpminor.exec_stmt prog e m2 (Csharpminor.fn_body f) m3 out ->
   exec_stmt_prop e m2 (Csharpminor.fn_body f) m3 out ->
   Csharpminor.outcome_result_value out (sig_res (Csharpminor.fn_sig f)) vres ->
   eval_funcall_prop m f vargs (free_list m3 lb) vres.
Proof.
  intros; red. intros tfn f1 tm; intros.
  unfold transl_function in TR. 
  caseEq (build_compilenv gce f); intros cenv stacksize CENV.
  rewrite CENV in TR. 
  destruct (zle stacksize Int.max_signed); try discriminate.
  monadInv TR. clear TR. 
  caseEq (alloc tm 0 stacksize). intros tm1 sp ALLOC.
  destruct (function_entry_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             H0 H1 MATCH CENV z ALLOC ARGSINJ MINJ H)
  as [f2 [te2 [tm2 [STOREPARAM [MINJ2 [INCR12 [MATCH2 BLOCKS]]]]]]].
  destruct (H3 _ _ _ _ _ _ _ _ _ EQ MINJ2 MATCH2)
  as [f3 [te3 [tm3 [tout [EXECBODY [OUTINJ [MINJ3 [INCR23 MATCH3]]]]]]]].
  assert (exists tvres, 
           outcome_result_value tout f.(Csharpminor.fn_sig).(sig_res) tvres /\
           val_inject f3 vres tvres).
    generalize H4. unfold Csharpminor.outcome_result_value, outcome_result_value.
    inversion OUTINJ. 
    destruct (sig_res (Csharpminor.fn_sig f)); intro. contradiction.
      exists Vundef; split. auto. subst vres; constructor.
    tauto.
    destruct (sig_res (Csharpminor.fn_sig f)); intro. contradiction.
      exists Vundef; split. auto. subst vres; constructor.
    destruct (sig_res (Csharpminor.fn_sig f)); intro. 
      exists v2; split. auto. subst vres; auto.
      contradiction.
  elim H5; clear H5; intros tvres [TOUT VINJRES].
  exists f3; exists (Mem.free tm3 sp); exists tvres.
  (* execution *)
  split. rewrite <- H6; econstructor; simpl; eauto.
  apply exec_Sseq_continue with te2 tm2.
  exact STOREPARAM.
  eexact EXECBODY.
  (* val_inject *)
  split. assumption.
  (* mem_inject *)
  split. apply free_inject; auto. 
  intros. elim (BLOCKS b1); intros B1 B2. apply B1. inversion MATCH3. inversion H20.
  eapply me_inv0. eauto. 
  (* inject_incr *)
  split. eapply inject_incr_trans; eauto.
  (* match_callstack *)
  assert (forall bl mm, nextblock (free_list mm bl) = nextblock mm).
    induction bl; intros. reflexivity. simpl. auto.
  unfold free; simpl nextblock. rewrite H5. 
  eapply match_callstack_freelist; eauto. 
  intros. elim (BLOCKS b); intros B1 B2. generalize (B2 H7). omega.
Qed.

Lemma transl_stmt_Sskip_correct:
  forall (e : Csharpminor.env) (m : mem),
  exec_stmt_prop e m Csharpminor.Sskip m Csharpminor.Out_normal.
Proof.
  intros; red; intros. monadInv TR. 
  exists f1; exists te1; exists tm1; exists Out_normal.
  intuition. subst ts; constructor. constructor.
Qed.

Lemma transl_stmt_Sexpr_correct:
   forall (e : Csharpminor.env) (m : mem) (a : Csharpminor.expr)
     (m1 : mem) (v : val),
   Csharpminor.eval_expr prog nil e m a m1 v ->
   eval_expr_prop nil e m a m1 v ->
   exec_stmt_prop e m (Csharpminor.Sexpr a) m1 Csharpminor.Out_normal.
Proof.
  intros; red; intros. monadInv TR. 
  destruct (H0 _ _ _ _ _ _ _ _ _ _ EQ (val_nil_inject f1) MINJ MATCH)
  as [f2 [te2 [tm2 [tv1 [EVAL1 [VINJ1 [MINJ2 [INCR2 MATCH2]]]]]]]].
  exists f2; exists te2; exists tm2; exists Out_normal.
  intuition. subst ts. econstructor; eauto.
  constructor.
Qed.

Lemma transl_stmt_Sseq_continue_correct:
  forall (e : Csharpminor.env) (m : mem) (s1 s2 : Csharpminor.stmt)
         (m1 m2 : mem) (out : Csharpminor.outcome),
  Csharpminor.exec_stmt prog e m s1 m1 Csharpminor.Out_normal ->
  exec_stmt_prop e m s1 m1 Csharpminor.Out_normal ->
  Csharpminor.exec_stmt prog e m1 s2 m2 out ->
  exec_stmt_prop e m1 s2 m2 out ->
  exec_stmt_prop e m (Csharpminor.Sseq s1 s2) m2 out.
Proof.
  intros; red; intros; monadInv TR.
  destruct (H0 _ _ _ _ _ _ _ _ _ EQ MINJ MATCH)
  as [f2 [te2 [tm2 [tout1 [EXEC1 [OINJ1 [MINJ2 [INCR2 MATCH2]]]]]]]].
  destruct (H2 _ _ _ _ _ _ _ _ _ EQ0 MINJ2 MATCH2)
  as [f3 [te3 [tm3 [tout2 [EXEC2 [OINJ2 [MINJ3 [INCR3 MATCH3]]]]]]]].
  exists f3; exists te3; exists tm3; exists tout2.
  intuition. subst ts; eapply exec_Sseq_continue; eauto.
  inversion OINJ1. subst tout1. auto.
  eapply inject_incr_trans; eauto.
Qed.

Lemma transl_stmt_Sseq_stop_correct:
  forall (e : Csharpminor.env) (m : mem) (s1 s2 : Csharpminor.stmt)
         (m1 : mem) (out : Csharpminor.outcome),
  Csharpminor.exec_stmt prog e m s1 m1 out ->
  exec_stmt_prop e m s1 m1 out ->
  out <> Csharpminor.Out_normal ->
  exec_stmt_prop e m (Csharpminor.Sseq s1 s2) m1 out.
Proof.
  intros; red; intros; monadInv TR.
  destruct (H0 _ _ _ _ _ _ _ _ _ EQ MINJ MATCH)
  as [f2 [te2 [tm2 [tout1 [EXEC1 [OINJ1 [MINJ2 [INCR2 MATCH2]]]]]]]].
  exists f2; exists te2; exists tm2; exists tout1.
  intuition. subst ts; eapply exec_Sseq_stop; eauto.
  inversion OINJ1; subst out tout1; congruence.
Qed.

Lemma transl_stmt_Sifthenelse_true_correct:
   forall (e : Csharpminor.env) (m : mem) (a : Csharpminor.expr)
     (sl1 sl2 : Csharpminor.stmt) (m1 : mem) (v1 : val) (m2 : mem)
     (out : Csharpminor.outcome),
   Csharpminor.eval_expr prog nil e m a m1 v1 ->
   eval_expr_prop nil e m a m1 v1 ->
   Val.is_true v1 ->
   Csharpminor.exec_stmt prog e m1 sl1 m2 out ->
   exec_stmt_prop e m1 sl1 m2 out ->
   exec_stmt_prop e m (Csharpminor.Sifthenelse a sl1 sl2) m2 out.
Proof.
  intros; red; intros. monadInv TR.
  destruct (H0 _ _ _ _ _ _ _ _ _ _ EQ (val_nil_inject f1) MINJ MATCH)
  as [f2 [te2 [tm2 [tv1 [EVAL1 [VINJ1 [MINJ2 [INCR2 MATCH2]]]]]]]].
  destruct (H3 _ _ _ _ _ _ _ _ _ EQ0 MINJ2 MATCH2)
  as [f3 [te3 [tm3 [tout [EVAL2 [OINJ [MINJ3 [INCR3 MATCH3]]]]]]]].
  exists f3; exists te3; exists tm3; exists tout.
  intuition. 
  subst ts. eapply exec_ifthenelse_true; eauto.
  inversion VINJ1; subst v1 tv1; simpl in H1; simpl; contradiction || auto.
  eapply inject_incr_trans; eauto.
Qed.

Lemma transl_stmt_Sifthenelse_false_correct:
   forall (e : Csharpminor.env) (m : mem) (a : Csharpminor.expr)
     (sl1 sl2 : Csharpminor.stmt) (m1 : mem) (v1 : val) (m2 : mem)
     (out : Csharpminor.outcome),
   Csharpminor.eval_expr prog nil e m a m1 v1 ->
   eval_expr_prop nil e m a m1 v1 ->
   Val.is_false v1 ->
   Csharpminor.exec_stmt prog e m1 sl2 m2 out ->
   exec_stmt_prop e m1 sl2 m2 out ->
   exec_stmt_prop e m (Csharpminor.Sifthenelse a sl1 sl2) m2 out.
Proof.
  intros; red; intros. monadInv TR.
  destruct (H0 _ _ _ _ _ _ _ _ _ _ EQ (val_nil_inject f1) MINJ MATCH)
  as [f2 [te2 [tm2 [tv1 [EVAL1 [VINJ1 [MINJ2 [INCR2 MATCH2]]]]]]]].
  destruct (H3 _ _ _ _ _ _ _ _ _ EQ1 MINJ2 MATCH2)
  as [f3 [te3 [tm3 [tout [EVAL2 [OINJ [MINJ3 [INCR3 MATCH3]]]]]]]].
  exists f3; exists te3; exists tm3; exists tout.
  intuition. 
  subst ts. eapply exec_ifthenelse_false; eauto.
  inversion VINJ1; subst v1 tv1; simpl in H1; simpl; contradiction || auto.
  eapply inject_incr_trans; eauto.
Qed.

Lemma transl_stmt_Sloop_loop_correct:
   forall (e : Csharpminor.env) (m : mem) (sl : Csharpminor.stmt)
     (m1 m2 : mem) (out : Csharpminor.outcome),
   Csharpminor.exec_stmt prog e m sl m1 Csharpminor.Out_normal ->
   exec_stmt_prop e m sl m1 Csharpminor.Out_normal ->
   Csharpminor.exec_stmt prog e m1 (Csharpminor.Sloop sl) m2 out ->
   exec_stmt_prop e m1 (Csharpminor.Sloop sl) m2 out ->
   exec_stmt_prop e m (Csharpminor.Sloop sl) m2 out.
Proof.
  intros; red; intros. monadInv TR.
  destruct (H0 _ _ _ _ _ _ _ _ _ EQ MINJ MATCH)
  as [f2 [te2 [tm2 [tout1 [EVAL1 [OINJ1 [MINJ2 [INCR2 MATCH2]]]]]]]].
  destruct (H2 _ _ _ _ _ _ _ _ _ TR MINJ2 MATCH2)
  as [f3 [te3 [tm3 [tout2 [EVAL2 [OINJ2 [MINJ3 [INCR3 MATCH3]]]]]]]].
  exists f3; exists te3; exists tm3; exists tout2.
  intuition. 
  subst ts. eapply exec_Sloop_loop; eauto.
  inversion OINJ1; subst tout1; eauto.
  eapply inject_incr_trans; eauto.
Qed.


Lemma transl_stmt_Sloop_exit_correct:
   forall (e : Csharpminor.env) (m : mem) (sl : Csharpminor.stmt)
     (m1 : mem) (out : Csharpminor.outcome),
   Csharpminor.exec_stmt prog e m sl m1 out ->
   exec_stmt_prop e m sl m1 out ->
   out <> Csharpminor.Out_normal ->
   exec_stmt_prop e m (Csharpminor.Sloop sl) m1 out.
Proof.
  intros; red; intros. monadInv TR.
  destruct (H0 _ _ _ _ _ _ _ _ _ EQ MINJ MATCH)
  as [f2 [te2 [tm2 [tout1 [EVAL1 [OINJ1 [MINJ2 [INCR2 MATCH2]]]]]]]].
  exists f2; exists te2; exists tm2; exists tout1.
  intuition. subst ts; eapply exec_Sloop_stop; eauto.
  inversion OINJ1; subst out tout1; congruence.
Qed.

Lemma transl_stmt_Sblock_correct:
   forall (e : Csharpminor.env) (m : mem) (sl : Csharpminor.stmt)
     (m1 : mem) (out : Csharpminor.outcome),
   Csharpminor.exec_stmt prog e m sl m1 out ->
   exec_stmt_prop e m sl m1 out ->
   exec_stmt_prop e m (Csharpminor.Sblock sl) m1
     (Csharpminor.outcome_block out).
Proof.
  intros; red; intros. monadInv TR.
  destruct (H0 _ _ _ _ _ _ _ _ _ EQ MINJ MATCH)
  as [f2 [te2 [tm2 [tout1 [EVAL1 [OINJ1 [MINJ2 [INCR2 MATCH2]]]]]]]].
  exists f2; exists te2; exists tm2; exists (outcome_block tout1).
  intuition. subst ts; eapply exec_Sblock; eauto.
  inversion OINJ1; subst out tout1; simpl.
  constructor.
  destruct n; constructor.
  constructor.
  constructor; auto.
Qed.

Lemma transl_stmt_Sexit_correct:
   forall (e : Csharpminor.env) (m : mem) (n : nat),
   exec_stmt_prop e m (Csharpminor.Sexit n) m (Csharpminor.Out_exit n).
Proof.
  intros; red; intros. monadInv TR.
  exists f1; exists te1; exists tm1; exists (Out_exit n).
  intuition. subst ts; constructor. constructor.
Qed.

Lemma transl_stmt_Sswitch_correct:
  forall (e : Csharpminor.env) (m : mem)
         (a : Csharpminor.expr) (cases : list (int * nat)) (default : nat)
         (m1 : mem) (n : int),
  Csharpminor.eval_expr prog nil e m a m1 (Vint n) ->
  eval_expr_prop nil e m a m1 (Vint n) ->
  exec_stmt_prop e m (Csharpminor.Sswitch a cases default) m1
       (Csharpminor.Out_exit (Csharpminor.switch_target n default cases)).
Proof.
  intros; red; intros. monadInv TR.
  destruct (H0 _ _ _ _ _ _ _ _ _ _ EQ (val_nil_inject f1) MINJ MATCH)
  as [f2 [te2 [tm2 [tv1 [EVAL [VINJ1 [MINJ2 [INCR MATCH2]]]]]]]].
  exists f2; exists te2; exists tm2; 
  exists (Out_exit (switch_target n default cases)). intuition. 
  subst ts. constructor. inversion VINJ1. subst tv1. assumption.
  constructor. 
Qed.

Lemma transl_stmt_Sreturn_none_correct:
   forall (e : Csharpminor.env) (m : mem),
   exec_stmt_prop e m (Csharpminor.Sreturn None) m
     (Csharpminor.Out_return None).
Proof.
  intros; red; intros. monadInv TR.
  exists f1; exists te1; exists tm1; exists (Out_return None).
  intuition. subst ts; constructor. constructor.
Qed.

Lemma transl_stmt_Sreturn_some_correct:
   forall (e : Csharpminor.env) (m : mem) (a : Csharpminor.expr)
     (m1 : mem) (v : val),
   Csharpminor.eval_expr prog nil e m a m1 v ->
   eval_expr_prop nil e m a m1 v ->
   exec_stmt_prop e m (Csharpminor.Sreturn (Some a)) m1
     (Csharpminor.Out_return (Some v)).
Proof.
  intros; red; intros; monadInv TR.
  destruct (H0 _ _ _ _ _ _ _ _ _ _ EQ (val_nil_inject f1) MINJ MATCH)
  as [f2 [te2 [tm2 [tv1 [EVAL [VINJ1 [MINJ2 [INCR MATCH2]]]]]]]].
  exists f2; exists te2; exists tm2; exists (Out_return (Some tv1)).
  intuition. subst ts; econstructor; eauto. constructor; auto.
Qed.

(** We conclude by an induction over the structure of the Csharpminor
  evaluation derivation, using the lemmas above for each case. *)

Lemma transl_function_correct:
   forall m1 f vargs m2 vres,
   Csharpminor.eval_funcall prog m1 f vargs m2 vres ->
   eval_funcall_prop m1 f vargs m2 vres.
Proof
  (eval_funcall_ind4 prog
     eval_expr_prop
     eval_exprlist_prop
     eval_funcall_prop
     exec_stmt_prop

     transl_expr_Evar_correct
     transl_expr_Eassign_correct
     transl_expr_Eaddrof_correct
     transl_expr_Eop_correct
     transl_expr_Eload_correct
     transl_expr_Estore_correct
     transl_expr_Ecall_correct
     transl_expr_Econdition_true_correct
     transl_expr_Econdition_false_correct
     transl_expr_Elet_correct
     transl_expr_Eletvar_correct
     transl_exprlist_Enil_correct
     transl_exprlist_Econs_correct
     transl_funcall_correct
     transl_stmt_Sskip_correct
     transl_stmt_Sexpr_correct
     transl_stmt_Sseq_continue_correct
     transl_stmt_Sseq_stop_correct
     transl_stmt_Sifthenelse_true_correct
     transl_stmt_Sifthenelse_false_correct
     transl_stmt_Sloop_loop_correct
     transl_stmt_Sloop_exit_correct
     transl_stmt_Sblock_correct
     transl_stmt_Sexit_correct
     transl_stmt_Sswitch_correct
     transl_stmt_Sreturn_none_correct
     transl_stmt_Sreturn_some_correct).

(** The [match_globalenvs] relation holds for the global environments
  of the source program and the transformed program. *)

Lemma match_globalenvs_init:
  let m := Genv.init_mem (program_of_program prog) in
  let tm := Genv.init_mem tprog in
  let f := fun b => if zlt b m.(nextblock) then Some(b, 0) else None in
  match_globalenvs f.
Proof.
  intros. constructor.
  (* globalvars *)
  (* symbols *)
  intros. split.
  unfold f. rewrite zlt_true. auto. unfold m. 
  eapply Genv.find_symbol_inv; eauto.
  rewrite <- H. apply symbols_preserved.
  intros. unfold f. rewrite zlt_true. auto.
  generalize (nextblock_pos m). omega.
Qed.

(** The correctness of the translation of a whole Csharpminor program
  follows. *)

Theorem transl_program_correct:
  forall n,
  Csharpminor.exec_program prog (Vint n) ->
  exec_program tprog (Vint n).
Proof.
  intros n [b [fn [m [FINDS [FINDF [SIG EVAL]]]]]].
  elim (function_ptr_translated _ _ FINDF). intros tfn [TFIND TR].
  set (m0 := Genv.init_mem (program_of_program prog)) in *.
  set (f := fun b => if zlt b m0.(nextblock) then Some(b, 0) else None).
  assert (MINJ0: mem_inject f m0 m0).
    unfold f; constructor; intros.
    apply zlt_false; auto.
    destruct (zlt b0 (nextblock m0)); try discriminate.
    inversion H; subst b' delta. 
    split. auto. 
    constructor. compute. split; congruence. left; auto. 
    intros; omega. 
    generalize (Genv.initmem_undef (program_of_program prog) b0). fold m0. intros [lo [hi EQ]].
    rewrite EQ. simpl. constructor. 
    destruct (zlt b1 (nextblock m0)); try discriminate.
    destruct (zlt b2 (nextblock m0)); try discriminate.
    left; congruence. 
  assert (MATCH0: match_callstack f nil m0.(nextblock) m0.(nextblock) m0).
    constructor. unfold f; apply match_globalenvs_init.
  fold ge in EVAL.
  destruct (transl_function_correct _ _ _ _ _ EVAL 
                                    _ _ _ _ _ TR MINJ0 MATCH0 (val_nil_inject f))
  as [f1 [tm1 [tres [TEVAL [VINJ [MINJ1 [INCR MATCH1]]]]]]].
  exists b; exists tfn; exists tm1.
  split. fold tge. rewrite <- FINDS. 
  replace (prog_main prog) with (AST.prog_main tprog). fold ge. apply symbols_preserved.
  transitivity (AST.prog_main (program_of_program prog)).
  apply transform_partial_program_main with (transl_function gce). assumption.
  reflexivity.
  split. assumption.
  split. rewrite <- SIG. apply sig_transl_function; auto.
  rewrite (Genv.init_mem_transf_partial (transl_function gce) _ TRANSL).
  inversion VINJ; subst tres. assumption. 
Qed.

End TRANSLATION.
