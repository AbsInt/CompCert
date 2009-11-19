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

(** Correctness proof for Cminor generation. *)

Require Import FSets.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Csharpminor.
Require Import Op.
Require Import Cminor.
Require Import Cminorgen.

Open Local Scope error_monad_scope.

Section TRANSLATION.

Variable prog: Csharpminor.program.
Variable tprog: program.
Hypothesis TRANSL: transl_program prog = OK tprog.
Let ge : Csharpminor.genv := Genv.globalenv prog.
Let gvare : gvarenv := global_var_env prog.
Let gve := (ge, gvare).
Let gce : compilenv := build_global_compilenv prog.
Let tge: genv := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf_partial2 (transl_fundef gce) transl_globvar _ TRANSL).

Lemma function_ptr_translated:
  forall (b: block) (f: Csharpminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transl_fundef gce f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial2 (transl_fundef gce) transl_globvar TRANSL).


Lemma functions_translated:
  forall (v: val) (f: Csharpminor.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef gce f = OK tf.
Proof (Genv.find_funct_transf_partial2 (transl_fundef gce) transl_globvar TRANSL).

Lemma sig_preserved_body:
  forall f tf cenv size,
  transl_funbody cenv size f = OK tf -> 
  tf.(fn_sig) = f.(Csharpminor.fn_sig).
Proof.
  intros. monadInv H. reflexivity.
Qed.

Lemma sig_preserved:
  forall f tf,
  transl_fundef gce f = OK tf -> 
  Cminor.funsig tf = Csharpminor.funsig f.
Proof.
  intros until tf; destruct f; simpl.
  unfold transl_function. destruct (build_compilenv gce f).
  case (zle z Int.max_signed); simpl bind; try congruence.
  intros. monadInv H. simpl. eapply sig_preserved_body; eauto. 
  intro. inv H. reflexivity.
Qed.

Definition global_compilenv_match (ce: compilenv) (gv: gvarenv) : Prop :=
  forall id,
  match ce!!id with
  | Var_global_scalar chunk => gv!id = Some (Vscalar chunk)
  | Var_global_array => True
  | _ => False
  end.

Lemma global_compilenv_charact:
  global_compilenv_match gce gvare.
Proof.
  set (mkgve := fun gv (vars: list (ident * list init_data * var_kind)) =>
         List.fold_left
          (fun gve x => match x with (id, init, k) => PTree.set id k gve end)
          vars gv).
  assert (forall vars gv ce,
            global_compilenv_match ce gv ->
            global_compilenv_match (List.fold_left assign_global_variable vars ce)
                                   (mkgve gv vars)).
  induction vars; simpl; intros.
  auto.
  apply IHvars. intro id1. unfold assign_global_variable.
  destruct a as [[id2 init2] lv2]. destruct lv2; simpl; rewrite PMap.gsspec; rewrite PTree.gsspec.
  case (peq id1 id2); intro. auto. apply H. 
  case (peq id1 id2); intro. auto. apply H.

  change gvare with (mkgve (PTree.empty var_kind) prog.(prog_vars)).
  unfold gce, build_global_compilenv. apply H. 
  intro. rewrite PMap.gi. auto.
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
      PTree.get id gvare = Some (Vscalar chunk) ->
      match_var f id e m te sp (Var_global_scalar chunk)
  | match_var_global_array:
      PTree.get id e = None ->
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
      forall id, match_var f id e m te sp (PMap.get id cenv);

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

(** All blocks mapped to sub-blocks of the Cminor stack data must be
    images of variables from the Csharpminor environment [e] *)
    me_inv:
      forall b delta,
      f b = Some(sp, delta) ->
      exists id, exists lv, PTree.get id e = Some(b, lv);

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

Record frame : Type :=
  mkframe {
    fr_cenv: compilenv;
    fr_e: Csharpminor.env;
    fr_te: env;
    fr_sp: block;
    fr_low: Z;
    fr_high: Z
  }.

Definition callstack : Type := list frame.

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
  intros. generalize (me_vars0 id); intro. 
  inversion H2; econstructor; eauto.
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

Lemma match_env_store_local:
  forall f cenv e m1 m2 te sp lo hi id b chunk v tv,
  e!id = Some(b, Vscalar chunk) ->
  val_inject f (Val.load_result chunk v) tv ->
  store chunk m1 b 0 v = Some m2 ->
  match_env f cenv e m1 te sp lo hi ->
  match_env f cenv e m2 (PTree.set id tv te) sp lo hi.
Proof.
  intros. inversion H2. constructor; auto.
  intros. generalize (me_vars0 id0); intro.
  inversion H3; subst.
  (* var_local *)
  case (peq id id0); intro.
    (* the stored variable *)
    subst id0. 
    change Csharpminor.var_kind with var_kind in H4. 
    rewrite H in H5. injection H5; clear H5; intros; subst b0 chunk0.
    econstructor. eauto. 
    eapply load_store_same; eauto. auto. 
    rewrite PTree.gss. reflexivity.
    auto.
    (* a different variable *)
    econstructor; eauto.
    rewrite <- H6. eapply load_store_other; eauto. 
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
  intros. generalize (me_vars0 id); intro.
  inversion H2; econstructor; eauto.
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
  val_inject f (Val.load_result chunk v) tv ->
  store chunk m1 b 0 v = Some m2 ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) bound tbound m1 ->
  match_callstack f (mkframe cenv e (PTree.set id tv te) sp lo hi :: cs) bound tbound m2.
Proof.
  intros. inversion H2. constructor; auto.
  eapply match_env_store_local; eauto.
  eapply match_callstack_store_above; eauto.
  inversion H16. 
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
  intros. generalize (me_vars0 id); intro. 
  inversion H0; econstructor; eauto.
  rewrite H. auto.
Qed.

Lemma match_callstack_store_local_unchanged:
  forall f cenv e te sp lo hi cs bound tbound m1 m2 id b chunk v tv,
  e!id = Some(b, Vscalar chunk) ->
  val_inject f (Val.load_result chunk v) tv ->
  store chunk m1 b 0 v = Some m2 ->
  te!id = Some tv ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) bound tbound m1 ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) bound tbound m2.
Proof.
  intros. inversion H3. constructor; auto.
  apply match_env_extensional with (PTree.set id tv te).
  eapply match_env_store_local; eauto.
  intros. rewrite PTree.gsspec. 
  case (peq id0 id); intros. congruence. auto.
  eapply match_callstack_store_above; eauto.
  inversion H17. 
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
  intros. generalize (me_vars0 id); intro. 
  inversion H1; econstructor; eauto.
  rewrite <- H4. apply load_freelist. 
  intros. generalize (H0 _ H8); intro. 
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

Lemma blocks_of_env_charact:
  forall b e,
  In b (blocks_of_env e) <->
  exists id, exists lv, e!id = Some(b, lv).
Proof.
  unfold blocks_of_env.
  set (f := fun id_b_lv : positive * (block * var_kind) =>
      let (_, y) := id_b_lv in let (b0, _) := y in b0).
  intros; split; intros.
  exploit list_in_map_inv; eauto. intros [[id [b' lv]] [A B]].
  simpl in A. subst b'. exists id; exists lv. apply PTree.elements_complete. auto.
  destruct H as [id [lv EQ]].
  change b with (f (id, (b, lv))). apply List.in_map.
  apply PTree.elements_correct. auto.
Qed.

Lemma match_callstack_freelist:
  forall f cenv e te sp lo hi cs bound tbound m tm,
  mem_inject f m tm ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) bound tbound m ->
  match_callstack f cs bound tbound (free_list m (blocks_of_env e))
  /\ mem_inject f (free_list m (blocks_of_env e)) (free tm sp).
Proof.
  intros. inv H0. inv H14. split.
  apply match_callstack_incr_bound with lo sp.
  apply match_callstack_freelist_rec. auto.
  intros. rewrite blocks_of_env_charact in H0. 
  destruct H0 as [id [lv EQ]]. exploit me_bounded0; eauto. omega.
  omega. omega.
  apply Mem.free_inject; auto.
  intros. rewrite blocks_of_env_charact. eauto.
Qed.

(** Preservation of [match_callstack] when allocating a block for
  a local variable on the Csharpminor side.  *)

Lemma load_from_alloc_is_undef:
  forall m1 chunk m2 b,
  alloc m1 0 (size_chunk chunk) = (m2, b) ->
  load chunk m2 b 0 = Some Vundef.
Proof.
  intros.
  assert (exists v, load chunk m2 b 0 = Some v).
    apply valid_access_load.
    eapply valid_access_alloc_same; eauto. omega. omega. apply Zdivide_0.
  destruct H0 as [v LOAD]. rewrite LOAD. decEq. 
  eapply load_alloc_same; eauto.
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
  e1!id = None ->
  let f2 := extend_inject b data f1 in
  let cenv2 := PMap.set id info cenv1 in
  let e2 := PTree.set id (b, lv) e1 in
  inject_incr f1 f2 ->
  match_env f2 cenv2 e2 m2 te sp lo m2.(nextblock).
Proof.
  intros. 
  assert (b = m1.(nextblock)).
    injection H; intros. auto.
  assert (m2.(nextblock) = Zsucc m1.(nextblock)).
    injection H; intros. rewrite <- H7; reflexivity.
  inversion H1. constructor.
  (* me_vars *)
  intros id0. unfold cenv2. rewrite PMap.gsspec. case (peq id0 id); intros.
    (* same var *)
    subst id0. destruct info.
      (* info = Var_local chunk *)
      elim H0; intros.
      apply match_var_local with b Vundef tv.
      unfold e2; rewrite PTree.gss. congruence.
      eapply load_from_alloc_is_undef; eauto. 
      rewrite H8 in H. unfold sizeof in H. eauto.
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
    generalize (me_vars0 id0); intros.
    inversion H7.
    eapply match_var_local with (v := v); eauto.
      unfold e2; rewrite PTree.gso; eauto.
      eapply load_alloc_other; eauto. 
      unfold f2, extend_inject, eq_block; rewrite zeq_false; auto.
      generalize (me_bounded0 _ _ _ H9). unfold block in *; omega.
    econstructor; eauto.
      unfold e2; rewrite PTree.gso; eauto.
    econstructor; eauto. 
      unfold e2; rewrite PTree.gso; eauto. 
    econstructor; eauto.
      unfold e2; rewrite PTree.gso; eauto.
    econstructor; eauto. 
      unfold e2; rewrite PTree.gso; eauto. 
  (* lo <= hi *)
  unfold block in *; omega.
  (* me_bounded *)
  intros until lv0. unfold e2; rewrite PTree.gsspec. 
  case (peq id0 id); intros.
  subst id0. inversion H7. subst b0. unfold block in *; omega. 
  generalize (me_bounded0 _ _ _ H7). rewrite H6. omega.
  (* me_inj *)
  intros until lv2. unfold e2; repeat rewrite PTree.gsspec.
  case (peq id1 id); case (peq id2 id); intros.
  congruence.
  inversion H7. subst b1. rewrite H5. 
    generalize (me_bounded0 _ _ _ H8). unfold block; omega.
  inversion H8. subst b2. rewrite H5.
    generalize (me_bounded0 _ _ _ H7). unfold block; omega.
  eauto.
  (* me_inv *)
  intros until delta. unfold f2, extend_inject, eq_block.
  case (zeq b0 b); intros.
  subst b0. exists id; exists lv. unfold e2. apply PTree.gss.
  exploit me_inv0; eauto. intros [id' [lv' EQ]].
  exists id'; exists lv'. unfold e2. rewrite PTree.gso; auto.
  congruence.
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
  intros. generalize (me_vars0 id); intro. 
  inversion H5.
  eapply match_var_local with (v := v); eauto.
    eapply load_alloc_other; eauto.
    unfold f2, extend_inject, eq_block. rewrite zeq_false. auto.
    generalize (me_bounded0 _ _ _ H7). unfold block in *; omega.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto.
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
  e1!id = None ->
  let f2 := extend_inject b data f1 in
  let cenv2 := PMap.set id info cenv1 in
  let e2 := PTree.set id (b, lv) e1 in
  inject_incr f1 f2 ->
  match_callstack f2 (mkframe cenv2 e2 te sp lo m2.(nextblock) :: cs) m2.(nextblock) tbound m2.
Proof.
  intros. inversion H1. constructor. omega. auto.
  unfold f2, cenv2, e2. eapply match_env_alloc_same; eauto.
  unfold f2; eapply match_callstack_alloc_other; eauto. 
  destruct info.
  elim H0; intros. rewrite H20. auto.
  elim H0; intros. rewrite H20. omega.
  elim H0; intros. rewrite H20. omega.
  contradiction.
  contradiction.
  inversion H18; omega. 
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

Lemma match_env_alloc:
  forall m1 l h m2 b tm1 tm2 tb f1 ce e te sp lo hi,
  alloc m1 l h = (m2, b) ->
  alloc tm1 l h = (tm2, tb) ->
  match_env f1 ce e m1 te sp lo hi ->
  hi <= m1.(nextblock) ->
  sp < tm1.(nextblock) ->
  let f2 := extend_inject b (Some(tb, 0)) f1 in
  inject_incr f1 f2 ->
  match_env f2 ce e m2 te sp lo hi.
Proof.
  intros. 
  assert (BEQ: b = m1.(nextblock)). injection H; auto.
  assert (TBEQ: tb = tm1.(nextblock)). injection H0; auto.
  inversion H1. constructor; auto.
  (* me_vars *)
  intros. generalize (me_vars0 id); intro. inversion H5.
    (* var_local *)
    eapply match_var_local with (v := v); eauto.
    eapply load_alloc_other; eauto. 
    generalize (me_bounded0 _ _ _ H7). intro. 
    unfold f2, extend_inject. case (zeq b0 b); intro. 
    subst b0. rewrite BEQ in H12. omegaContradiction. 
    auto.
    (* var_stack_scalar *)
    econstructor; eauto.
    (* var_stack_array *)
    econstructor; eauto.
    (* var_global_scalar *)
    econstructor; eauto.
    (* var_global_array *)
    econstructor; eauto.
  (* me_bounded *)
  intros until delta. unfold f2, extend_inject. case (zeq b0 b); intro.
  intro. injection H5; clear H5; intros. 
  rewrite H6 in TBEQ. rewrite TBEQ in H3. omegaContradiction.
  eauto.
  (* me_inj *)
  intros until delta. unfold f2, extend_inject. case (zeq b0 b); intros.
  injection H5; clear H5; intros; subst b0 tb0 delta.
  rewrite BEQ in H6. omegaContradiction. 
  eauto.
Qed.

Lemma match_callstack_alloc_rec:
  forall f1 cs bound tbound m1,
  match_callstack f1 cs bound tbound m1 ->
  forall l h m2 b tm1 tm2 tb,
  alloc m1 l h = (m2, b) ->
  alloc tm1 l h = (tm2, tb) ->
  bound <= m1.(nextblock) ->
  tbound <= tm1.(nextblock) ->
  let f2 := extend_inject b (Some(tb, 0)) f1 in
  inject_incr f1 f2 ->
  match_callstack f2 cs bound tbound m2.
Proof.
  induction 1; intros.
  constructor. 
    inversion H. constructor.
    intros. elim (mg_symbols0 _ _ H5); intros.
    split; auto. elim (H4 b0); intros; congruence.
    intros. generalize (mg_functions0 _ H5). elim (H4 b0); congruence.
  constructor. auto. auto. 
  unfold f2. eapply match_env_alloc; eauto. omega. omega. 
  unfold f2; eapply IHmatch_callstack; eauto.
  inversion H1; omega.
  omega.
Qed.

Lemma match_callstack_alloc:
  forall f1 cs m1 tm1 l h m2 b tm2 tb,
  match_callstack f1 cs m1.(nextblock) tm1.(nextblock) m1 ->
  alloc m1 l h = (m2, b) ->
  alloc tm1 l h = (tm2, tb) ->
  let f2 := extend_inject b (Some(tb, 0)) f1 in
  inject_incr f1 f2 ->
  match_callstack f2 cs m2.(nextblock) tm2.(nextblock) m2.
Proof.
  intros. unfold f2 in *. 
  apply match_callstack_incr_bound with m1.(nextblock) tm1.(nextblock).
  eapply match_callstack_alloc_rec; eauto. omega. omega. 
  injection H0; intros; subst m2; simpl; omega. 
  injection H1; intros; subst tm2; simpl; omega. 
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

Remark val_inject_val_of_bool:
  forall f b, val_inject f (Val.of_bool b) (Val.of_bool b).
Proof.
  intros; destruct b; unfold Val.of_bool, Vtrue, Vfalse; constructor.
Qed.

Remark val_inject_eval_compare_mismatch:
  forall f c v,  
  eval_compare_mismatch c = Some v ->
  val_inject f v v.
Proof.
  unfold eval_compare_mismatch; intros.
  destruct c; inv H; unfold Vfalse, Vtrue; constructor.
Qed.

Remark val_inject_eval_compare_null:
  forall f i c v,  
  eval_compare_null c i = Some v ->
  val_inject f v v.
Proof.
  unfold eval_compare_null. intros. destruct (Int.eq i Int.zero). 
  eapply val_inject_eval_compare_mismatch; eauto. 
  discriminate.
Qed.

Hint Resolve eval_Econst eval_Eunop eval_Ebinop eval_Eload: evalexpr.

Ltac TrivialOp :=
  match goal with
  | [ |- exists y, _ /\ val_inject _ (Vint ?x) _ ] =>
      exists (Vint x); split;
      [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ val_inject _ (Vfloat ?x) _ ] =>
      exists (Vfloat x); split;
      [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ val_inject _ (Val.of_bool ?x) _ ] =>
      exists (Val.of_bool x); split;
      [eauto with evalexpr | apply val_inject_val_of_bool]
  | [ |- exists y, Some ?x = Some y /\ val_inject _ _ _ ] =>
      exists x; split; [auto | econstructor; eauto]
  | _ => idtac
  end.

(** Correctness of [transl_constant]. *)

Lemma transl_constant_correct:
  forall f sp cst v,
  Csharpminor.eval_constant cst = Some v ->
  exists tv,
     eval_constant tge sp (transl_constant cst) = Some tv
  /\ val_inject f v tv.
Proof.
  destruct cst; simpl; intros; inv H; TrivialOp.
Qed.

(** Compatibility of [eval_unop] with respect to [val_inject]. *)

Lemma eval_unop_compat:
  forall f op v1 tv1 v,
  eval_unop op v1 = Some v ->
  val_inject f v1 tv1 ->
  exists tv,
     eval_unop op tv1 = Some tv
  /\ val_inject f v tv.
Proof.
  destruct op; simpl; intros.
  inv H; inv H0; simpl; TrivialOp.
  inv H; inv H0; simpl; TrivialOp.
  inv H; inv H0; simpl; TrivialOp.
  inv H; inv H0; simpl; TrivialOp.
  inv H0; inv H. TrivialOp. unfold Vfalse; TrivialOp.
  inv H0; inv H. TrivialOp. unfold Vfalse; TrivialOp.
  inv H0; inv H; TrivialOp.
  inv H0; inv H; TrivialOp.
  inv H0; inv H; TrivialOp.
  inv H0; inv H; TrivialOp.
  inv H0; inv H; TrivialOp.
  inv H0; inv H; TrivialOp.
  inv H0; inv H; TrivialOp.
  inv H0; inv H; TrivialOp.
Qed.

(** Compatibility of [eval_binop] with respect to [val_inject]. *)

Lemma eval_binop_compat:
  forall f op v1 tv1 v2 tv2 v m tm,
  Csharpminor.eval_binop op v1 v2 m = Some v ->
  val_inject f v1 tv1 ->
  val_inject f v2 tv2 ->
  mem_inject f m tm ->
  exists tv,
     Cminor.eval_binop op tv1 tv2 = Some tv
  /\ val_inject f v tv.
Proof.
  destruct op; simpl; intros.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
    repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    apply Int.sub_add_l.
    destruct (eq_block b1 b0); inv H4. 
    assert (b3 = b2) by congruence. subst b3. 
    unfold eq_block; rewrite zeq_true. TrivialOp.
    replace x0 with x by congruence. decEq. decEq. 
    apply Int.sub_shifted.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    destruct (Int.eq i0 Int.zero); inv H1. TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    destruct (Int.eq i0 Int.zero); inv H1. TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    destruct (Int.eq i0 Int.zero); inv H1. TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    destruct (Int.eq i0 Int.zero); inv H1. TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    destruct (Int.ltu i0 Int.iwordsize); inv H1. TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    destruct (Int.ltu i0 Int.iwordsize); inv H1. TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    destruct (Int.ltu i0 Int.iwordsize); inv H1. TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
    exists v; split; auto. eapply val_inject_eval_compare_null; eauto.
    exists v; split; auto. eapply val_inject_eval_compare_null; eauto.
  (* cmp ptr ptr *)
  caseEq (valid_pointer m b1 (Int.signed ofs1) && valid_pointer m b0 (Int.signed ofs0)); 
  intro EQ; rewrite EQ in H4; try discriminate.
  elim (andb_prop _ _ EQ); intros.
  destruct (eq_block b1 b0); inv H4.
  (* same blocks in source *)
  assert (b3 = b2) by congruence. subst b3.
  assert (x0 = x) by congruence. subst x0.
  exists (Val.of_bool (Int.cmp c ofs1 ofs0)); split.
  unfold eq_block; rewrite zeq_true; simpl.
  decEq. decEq. rewrite Int.translate_cmp. auto. 
  eapply valid_pointer_inject_no_overflow; eauto.
  eapply valid_pointer_inject_no_overflow; eauto.
  apply val_inject_val_of_bool.
  (* different blocks in source *)
  simpl. exists v; split; [idtac | eapply val_inject_eval_compare_mismatch; eauto].
  destruct (eq_block b2 b3); auto.
  exploit different_pointers_inject; eauto. intros [A|A]. 
  congruence.
  decEq. destruct c; simpl in H6; inv H6; unfold Int.cmp.
  predSpec Int.eq Int.eq_spec (Int.add ofs1 (Int.repr x)) (Int.add ofs0 (Int.repr x0)).
  congruence. auto.
  predSpec Int.eq Int.eq_spec (Int.add ofs1 (Int.repr x)) (Int.add ofs0 (Int.repr x0)).
  congruence. auto.
  (* cmpu *)
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  (* cmpf *)
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
Qed.

(** Correctness of [make_cast].  Note that the resulting Cminor value is
  normalized according to the given memory chunk. *)

Lemma make_cast_correct:
  forall f sp te tm a v tv chunk,
  eval_expr tge sp te tm a tv ->
  val_inject f v tv ->
  exists tv',
     eval_expr tge sp te tm (make_cast chunk a) tv'
  /\ val_inject f (Val.load_result chunk v) tv'.
Proof.
  intros. destruct chunk; simpl make_cast.

  exists (Val.sign_ext 8 tv). 
  split. eauto with evalexpr. inversion H0; simpl; constructor.

  exists (Val.zero_ext 8 tv). 
  split. eauto with evalexpr. inversion H0; simpl; constructor.

  exists (Val.sign_ext 16 tv). 
  split. eauto with evalexpr. inversion H0; simpl; constructor.

  exists (Val.zero_ext 16 tv). 
  split. eauto with evalexpr. inversion H0; simpl; constructor.

  exists tv.
  split. auto. inversion H0; simpl; econstructor; eauto.

  exists (Val.singleoffloat tv). 
  split. eauto with evalexpr. inversion H0; simpl; constructor.

  exists tv.
  split. auto. inversion H0; simpl; econstructor; eauto.
Qed.

Lemma make_stackaddr_correct:
  forall sp te tm ofs,
  eval_expr tge (Vptr sp Int.zero) te tm
            (make_stackaddr ofs) (Vptr sp (Int.repr ofs)).
Proof.
  intros; unfold make_stackaddr.
  eapply eval_Econst. simpl. decEq. decEq.
  rewrite Int.add_commut. apply Int.add_zero.
Qed.

Lemma make_globaladdr_correct:
  forall sp te tm id b,
  Genv.find_symbol tge id = Some b ->
  eval_expr tge (Vptr sp Int.zero) te tm
            (make_globaladdr id) (Vptr b Int.zero).
Proof.
  intros; unfold make_globaladdr.
  eapply eval_Econst. simpl. rewrite H. auto.
Qed.

(** Correctness of [make_store]. *)

Lemma store_arg_content_inject:
  forall f sp te tm a v va chunk,
  eval_expr tge sp te tm a va ->
  val_inject f v va ->
  exists vb,
     eval_expr tge sp te tm (store_arg chunk a) vb
  /\ val_content_inject f chunk v vb.
Proof.
  intros. 
  assert (exists vb,
       eval_expr tge sp te tm a vb  
    /\ val_content_inject f chunk v vb).
  exists va; split. assumption. constructor. assumption.
  destruct a; simpl store_arg; trivial;
  destruct u; trivial;
  destruct chunk; trivial;
  inv H; simpl in H6; inv H6;
  econstructor; (split; [eauto|idtac]);
  destruct v1; simpl in H0; inv H0; try (constructor; constructor).
  apply val_content_inject_8. auto. apply Int.zero_ext_idem. compute; auto.
  apply val_content_inject_8; auto. apply Int.zero_ext_sign_ext. compute; auto.
  apply val_content_inject_16; auto. apply Int.zero_ext_idem. compute; auto.
  apply val_content_inject_16; auto. apply Int.zero_ext_sign_ext. compute; auto.
  apply val_content_inject_32. apply Float.singleoffloat_idem. 
Qed.

Lemma make_store_correct:
  forall f sp te tm addr tvaddr rhs tvrhs chunk m vaddr vrhs m' fn k,
  eval_expr tge sp te tm addr tvaddr ->
  eval_expr tge sp te tm rhs tvrhs ->
  Mem.storev chunk m vaddr vrhs = Some m' ->
  mem_inject f m tm ->
  val_inject f vaddr tvaddr ->
  val_inject f vrhs tvrhs ->
  exists tm',
  step tge (State fn (make_store chunk addr rhs) k sp te tm)
        E0 (State fn Sskip k sp te tm')
  /\ mem_inject f m' tm'
  /\ nextblock tm' = nextblock tm.
Proof.
  intros. unfold make_store.
  exploit store_arg_content_inject. eexact H0. eauto. 
  intros [tv [EVAL VCINJ]].
  exploit storev_mapped_inject_1; eauto.
  intros [tm' [STORE MEMINJ]].
  exists tm'.
  split. eapply step_store; eauto. 
  split. auto.
  unfold storev in STORE; destruct tvaddr; try discriminate.
  eapply nextblock_store; eauto.
Qed.

(** Correctness of the variable accessors [var_get], [var_addr],
  and [var_set]. *)

Lemma var_get_correct:
  forall cenv id a f e te sp lo hi m cs tm b chunk v,
  var_get cenv id = OK a ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) m.(nextblock) tm.(nextblock) m ->
  mem_inject f m tm ->
  eval_var_ref gve e id b chunk ->
  load chunk m b 0 = Some v ->
  exists tv,
    eval_expr tge (Vptr sp Int.zero) te tm a tv /\
    val_inject f v tv.
Proof.
  unfold var_get; intros.
  assert (match_var f id e m te sp cenv!!id).
    inversion H0. inversion H17. auto.
  inversion H4; subst; rewrite <- H5 in H; inversion H; subst.
  (* var_local *)
  inversion H2; [subst|congruence].
  exists v'; split.
  apply eval_Evar. auto. 
  replace v with v0. auto. congruence.
  (* var_stack_scalar *)
  inversion H2; [subst|congruence].
  assert (b0 = b). congruence. subst b0.
  assert (chunk0 = chunk). congruence. subst chunk0.
  exploit loadv_inject; eauto.
    unfold loadv. eexact H3. 
  intros [tv [LOAD INJ]].
  exists tv; split. 
  eapply eval_Eload; eauto. eapply make_stackaddr_correct; eauto.
  auto.
  (* var_global_scalar *)
  inversion H2; [congruence|subst]. simpl in H9; simpl in H10. 
  assert (match_globalenvs f). eapply match_callstack_match_globalenvs; eauto.
  inversion H11. destruct (mg_symbols0 _ _ H9) as [A B].
  assert (chunk0 = chunk). congruence. subst chunk0.
  assert (loadv chunk m (Vptr b Int.zero) = Some v). assumption.
  assert (val_inject f (Vptr b Int.zero) (Vptr b Int.zero)).
    econstructor; eauto. 
  generalize (loadv_inject _ _ _ _ _ _ _ H1 H12 H13).
  intros [tv [LOAD INJ]].
  exists tv; split. 
  eapply eval_Eload; eauto. eapply make_globaladdr_correct; eauto.
  auto.
Qed.

Lemma var_addr_correct:
  forall cenv id a f e te sp lo hi m cs tm b,
  match_callstack f (mkframe cenv e te sp lo hi :: cs) m.(nextblock) tm.(nextblock) m ->
  var_addr cenv id = OK a ->
  eval_var_addr gve e id b ->
  exists tv,
    eval_expr tge (Vptr sp Int.zero) te tm a tv /\
    val_inject f (Vptr b Int.zero) tv.
Proof.
  unfold var_addr; intros.
  assert (match_var f id e m te sp cenv!!id).
    inversion H. inversion H15. auto.
  inversion H2; subst; rewrite <- H3 in H0; inversion H0; subst; clear H0.
  (* var_stack_scalar *)
  inversion H1; [subst|congruence]. 
  exists (Vptr sp (Int.repr ofs)); split.
  eapply make_stackaddr_correct.
  replace b with b0. auto. congruence.
  (* var_stack_array *)
  inversion H1; [subst|congruence]. 
  exists (Vptr sp (Int.repr ofs)); split.
  eapply make_stackaddr_correct.
  replace b with b0. auto. congruence.
  (* var_global_scalar *)
  inversion H1; [congruence|subst].
  assert (match_globalenvs f). eapply match_callstack_match_globalenvs; eauto.
  inversion H7. destruct (mg_symbols0 _ _ H6) as [A B].
  exists (Vptr b Int.zero); split.
  eapply make_globaladdr_correct. eauto.
  econstructor; eauto. 
  (* var_global_array *)
  inversion H1; [congruence|subst].
  assert (match_globalenvs f). eapply match_callstack_match_globalenvs; eauto.
  inversion H6. destruct (mg_symbols0 _ _ H5) as [A B].
  exists (Vptr b Int.zero); split.
  eapply make_globaladdr_correct. eauto.
  econstructor; eauto. 
Qed.

Lemma var_set_correct:
  forall cenv id rhs a f e te sp lo hi m cs tm tv v m' fn k,
  var_set cenv id rhs = OK a ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) m.(nextblock) tm.(nextblock) m ->
  eval_expr tge (Vptr sp Int.zero) te tm rhs tv ->
  val_inject f v tv ->
  mem_inject f m tm ->
  exec_assign gve e m id v m' ->
  exists te', exists tm',
    step tge (State fn a k (Vptr sp Int.zero) te tm)
          E0 (State fn Sskip k (Vptr sp Int.zero) te' tm') /\
    mem_inject f m' tm' /\
    match_callstack f (mkframe cenv e te' sp lo hi :: cs) m'.(nextblock) tm'.(nextblock) m' /\
    (forall id', id' <> id -> te'!id' = te!id').
Proof.
  unfold var_set; intros.
  inv H4. 
  assert (NEXTBLOCK: nextblock m' = nextblock m).
    eapply nextblock_store; eauto.
  inversion H0; subst.
  assert (match_var f id e m te sp cenv!!id). inversion H19; auto.
  inv H4; rewrite <- H7 in H; inv H.
  (* var_local *)
  inversion H5; [subst|congruence]. 
  assert (b0 = b) by congruence. subst b0.
  assert (chunk0 = chunk) by congruence. subst chunk0.
  exploit make_cast_correct; eauto.  
  intros [tv' [EVAL INJ]].
  exists (PTree.set id tv' te); exists tm.
  split. eapply step_assign. eauto. 
  split. eapply store_unmapped_inject; eauto. 
  split. rewrite NEXTBLOCK. eapply match_callstack_store_local; eauto.
  intros. apply PTree.gso; auto.
  (* var_stack_scalar *)
  inversion H5; [subst|congruence].
  assert (b0 = b) by congruence. subst b0.
  assert (chunk0 = chunk) by congruence. subst chunk0.
  assert (storev chunk m (Vptr b Int.zero) v = Some m'). assumption.
  exploit make_store_correct.
    eapply make_stackaddr_correct.
    eauto. eauto. eauto. eauto. eauto. 
  intros [tm' [EVAL [MEMINJ TNEXTBLOCK]]].
  exists te; exists tm'.
  split. eauto. split. auto.  
  split. rewrite NEXTBLOCK; rewrite TNEXTBLOCK.
  eapply match_callstack_mapped; eauto. 
  inversion H9; congruence.
  auto.
  (* var_global_scalar *)
  inversion H5; [congruence|subst]. simpl in H4; simpl in H10. 
  assert (chunk0 = chunk) by congruence. subst chunk0.  
  assert (storev chunk m (Vptr b Int.zero) v = Some m'). assumption.
  assert (match_globalenvs f). eapply match_callstack_match_globalenvs; eauto.
  inversion H12. destruct (mg_symbols0 _ _ H4) as [A B].
  exploit make_store_correct.
    eapply make_globaladdr_correct; eauto.
    eauto. eauto. eauto. eauto. eauto. 
  intros [tm' [EVAL [MEMINJ TNEXTBLOCK]]].
  exists te; exists tm'.
  split. eauto. split. auto. 
  split. rewrite NEXTBLOCK; rewrite TNEXTBLOCK.
  eapply match_callstack_mapped; eauto. congruence.
  auto.
Qed.

Lemma match_env_extensional':
  forall f cenv e m te1 sp lo hi,
  match_env f cenv e m te1 sp lo hi ->
  forall te2,
  (forall id, 
     match cenv!!id with
     | Var_local _ => te2!id = te1!id
     | _ => True
     end) ->
  match_env f cenv e m te2 sp lo hi.
Proof.
  induction 1; intros; econstructor; eauto.
  intros. generalize (me_vars0 id); intro. 
  inversion H0; econstructor; eauto.
  generalize (H id). rewrite <- H1. congruence. 
Qed.


Lemma match_callstack_extensional:
  forall f cenv e te1 te2 sp lo hi cs bound tbound m,
  (forall id, 
     match cenv!!id with
     | Var_local _ => te2!id = te1!id
     | _ => True
     end) ->
  match_callstack f (mkframe cenv e te1 sp lo hi :: cs) bound tbound m ->
  match_callstack f (mkframe cenv e te2 sp lo hi :: cs) bound tbound m.
Proof.
  intros. inv H0. constructor; auto. 
  apply match_env_extensional' with te1; auto.
Qed.

Lemma var_set_self_correct:
  forall cenv id a f e te sp lo hi m cs tm tv v m' fn k,
  var_set cenv id (Evar id) = OK a ->
  match_callstack f (mkframe cenv e te sp lo hi :: cs) m.(nextblock) tm.(nextblock) m ->
  val_inject f v tv ->
  mem_inject f m tm ->
  exec_assign gve e m id v m' ->
  exists te', exists tm',
    step tge (State fn a k (Vptr sp Int.zero) (PTree.set id tv te) tm)
          E0 (State fn Sskip k (Vptr sp Int.zero) te' tm') /\
    mem_inject f m' tm' /\
    match_callstack f (mkframe cenv e te' sp lo hi :: cs) m'.(nextblock) tm'.(nextblock) m'.
Proof.
  unfold var_set; intros.
  inv H3. 
  assert (NEXTBLOCK: nextblock m' = nextblock m).
    eapply nextblock_store; eauto.
  inversion H0; subst.
  assert (EVAR: eval_expr tge (Vptr sp Int.zero) (PTree.set id tv te) tm (Evar id) tv).
    constructor. apply PTree.gss.
  assert (match_var f id e m te sp cenv!!id). inversion H18; auto.
  inv H3; rewrite <- H6 in H; inv H.
  (* var_local *)
  inversion H4; [subst|congruence]. 
  assert (b0 = b) by congruence. subst b0.
  assert (chunk0 = chunk) by congruence. subst chunk0.
  exploit make_cast_correct; eauto. 
  intros [tv' [EVAL INJ]].
  exists (PTree.set id tv' (PTree.set id tv te)); exists tm.
  split. eapply step_assign. eauto. 
  split. eapply store_unmapped_inject; eauto. 
  rewrite NEXTBLOCK.
  apply match_callstack_extensional with (PTree.set id tv' te).
  intros. destruct (cenv!!id0); auto. 
  repeat rewrite PTree.gsspec. destruct (peq id0 id); auto. 
  eapply match_callstack_store_local; eauto.
  (* var_stack_scalar *)
  inversion H4; [subst|congruence].
  assert (b0 = b) by congruence. subst b0.
  assert (chunk0 = chunk) by congruence. subst chunk0.
  assert (storev chunk m (Vptr b Int.zero) v = Some m'). assumption.
  exploit make_store_correct.
    eapply make_stackaddr_correct.
    eauto. eauto. eauto. eauto. eauto. 
  intros [tm' [EVAL [MEMINJ TNEXTBLOCK]]].
  exists (PTree.set id tv te); exists tm'.
  split. eauto. split. auto.  
  rewrite NEXTBLOCK; rewrite TNEXTBLOCK.
  apply match_callstack_extensional with te.
  intros. caseEq (cenv!!id0); intros; auto.
  rewrite PTree.gsspec. destruct (peq id0 id). congruence. auto.
  eapply match_callstack_mapped; eauto. 
  inversion H8; congruence.
  (* var_global_scalar *)
  inversion H4; [congruence|subst]. simpl in H3; simpl in H9.
  assert (chunk0 = chunk) by congruence. subst chunk0.  
  assert (storev chunk m (Vptr b Int.zero) v = Some m'). assumption.
  assert (match_globalenvs f). eapply match_callstack_match_globalenvs; eauto.
  inversion H11. destruct (mg_symbols0 _ _ H3) as [A B].
  exploit make_store_correct.
    eapply make_globaladdr_correct; eauto.
    eauto. eauto. eauto. eauto. eauto. 
  intros [tm' [EVAL [MEMINJ TNEXTBLOCK]]].
  exists (PTree.set id tv te); exists tm'.
  split. eauto. split. auto. 
  rewrite NEXTBLOCK; rewrite TNEXTBLOCK.
  apply match_callstack_extensional with te.
  intros. caseEq (cenv!!id0); intros; auto.
  rewrite PTree.gsspec. destruct (peq id0 id). congruence. auto.
  eapply match_callstack_mapped; eauto. congruence.
Qed.

(** * Correctness of stack allocation of local variables *)

(** This section shows the correctness of the translation of Csharpminor
  local variables, either as Cminor local variables or as sub-blocks
  of the Cminor stack data.  This is the most difficult part of the proof. *)

Remark array_alignment_pos:
  forall sz, array_alignment sz > 0.
Proof.
  unfold array_alignment; intros. 
  destruct (zlt sz 2). omega. 
  destruct (zlt sz 4). omega.
  destruct (zlt sz 8); omega.
Qed.

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
  generalize (align_le sz (array_alignment z) (array_alignment_pos z)).
  assert (0 <= Zmax 0 z). apply Zmax_bound_l. omega.
  omega.
Qed.

Remark inj_offset_aligned_array:
  forall stacksize sz,
  inj_offset_aligned (align stacksize (array_alignment sz)) sz.
Proof.
  intros; red; intros.
  apply Zdivides_trans with (array_alignment sz).
  unfold align_chunk.  unfold array_alignment.
  generalize Zone_divide; intro.
  generalize Zdivide_refl; intro.
  assert (2 | 4). exists 2; auto.
  assert (2 | 8). exists 4; auto.
  assert (4 | 8). exists 2; auto.
  destruct (zlt sz 2).
  destruct chunk; simpl in *; auto; omegaContradiction.
  destruct (zlt sz 4).
  destruct chunk; simpl in *; auto; omegaContradiction.
  destruct (zlt sz 8).
  destruct chunk; simpl in *; auto; omegaContradiction.
  destruct chunk; simpl; auto.
  apply align_divides. apply array_alignment_pos.
Qed.

Remark inj_offset_aligned_array':
  forall stacksize sz,
  inj_offset_aligned (align stacksize (array_alignment sz)) (Zmax 0 sz).
Proof.
  intros. 
  replace (array_alignment sz) with (array_alignment (Zmax 0 sz)).
  apply inj_offset_aligned_array. 
  rewrite Zmax_spec. destruct (zlt sz 0); auto.
  transitivity 1. reflexivity. unfold array_alignment. rewrite zlt_true. auto. omega.
Qed.

Remark inj_offset_aligned_var:
  forall stacksize chunk,
  inj_offset_aligned (align stacksize (size_chunk chunk)) (size_chunk chunk).
Proof.
  intros.
  replace (align stacksize (size_chunk chunk))
     with (align stacksize (array_alignment (size_chunk chunk))).
  apply inj_offset_aligned_array.
  decEq. destruct chunk; reflexivity.
Qed.

Lemma match_callstack_alloc_variables_rec:
  forall tm sp cenv' sz' te lo cs atk,
  valid_block tm sp ->
  low_bound tm sp = 0 ->
  high_bound tm sp = sz' ->
  sz' <= Int.max_signed ->
  forall e m vars e' m',
  alloc_variables e m vars e' m' ->
  forall f cenv sz,
  assign_variables atk vars (cenv, sz) = (cenv', sz') ->
  match_callstack f (mkframe cenv e te sp lo m.(nextblock) :: cs)
                    m.(nextblock) tm.(nextblock) m ->
  mem_inject f m tm ->
  0 <= sz ->
  (forall b delta, f b = Some(sp, delta) -> high_bound m b + delta <= sz) ->
  (forall id lv, In (id, lv) vars -> te!id <> None) ->
  list_norepet (List.map (@fst ident var_kind) vars) ->
  (forall id lv, In (id, lv) vars -> e!id = None) ->
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
  intros cenv1 sz1 ASV1 ASVS MATCH MINJ SZPOS BOUND DEFINED NOREPET UNDEFINED.
  assert (DEFINED1: forall id0 lv0, In (id0, lv0) vars -> te!id0 <> None).
    intros. eapply DEFINED. simpl. right. eauto.
  assert (exists tv, te!id = Some tv).
    assert (te!id <> None). eapply DEFINED. simpl; left; auto.
    destruct (te!id). exists v; auto. congruence.
  elim H1; intros tv TEID; clear H1.
  assert (UNDEFINED1: forall (id0 : ident) (lv0 : var_kind),
            In (id0, lv0) vars ->
            (PTree.set id (b1, lv) e)!id0 = None).
    intros. rewrite PTree.gso. eapply UNDEFINED; eauto with coqlib.
    simpl in NOREPET. inversion NOREPET. red; intro; subst id0.
    elim H4. change id with (fst (id, lv0)). apply List.in_map. auto.
  assert (NOREPET1: list_norepet (map (fst (A:=ident) (B:=var_kind)) vars)).
    inv NOREPET; auto.
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
      rewrite Zminus_0_r. unfold ofs. rewrite LV. simpl. 
      apply inj_offset_aligned_var. 
      intros. left. generalize (BOUND _ _ H5). omega. 
    elim H3; intros MINJ1 INCR1; clear H3.
    exploit IHalloc_variables; eauto.
      unfold f1; rewrite <- H2; eapply match_callstack_alloc_left; eauto with coqlib.
      rewrite <- H1. omega.
      intros until delta; unfold f1, extend_inject, eq_block.
      rewrite (high_bound_alloc _ _ _ _ _ H b).
      case (zeq b b1); intros. 
      inversion H3. unfold sizeof; rewrite LV. omega.
      generalize (BOUND _ _ H3). omega.
    intros [f' [INCR2 [MINJ2 MATCH2]]].
    exists f'; intuition. eapply inject_incr_trans; eauto. 
  (* 1.2 info = Var_local chunk *)
    intro EQ; injection EQ; intros; clear EQ. subst sz1.
    exploit alloc_unmapped_inject; eauto.
    set (f1 := extend_inject b1 None f). intros [MINJ1 INCR1].
    exploit IHalloc_variables; eauto.
      unfold f1; rewrite <- H2; eapply match_callstack_alloc_left; eauto with coqlib.
      intros until delta; unfold f1, extend_inject, eq_block.
      rewrite (high_bound_alloc _ _ _ _ _ H b).
      case (zeq b b1); intros. discriminate.
      eapply BOUND; eauto.
    intros [f' [INCR2 [MINJ2 MATCH2]]].
    exists f'; intuition. eapply inject_incr_trans; eauto. 
  (* 2. lv = LVarray dim, info = Var_stack_array *)
  intros dim LV EQ. injection EQ; clear EQ; intros.
  assert (0 <= Zmax 0 dim). apply Zmax1. 
  generalize (align_le sz (array_alignment dim) (array_alignment_pos dim)). intro.
  set (ofs := align sz (array_alignment dim)) in *.
  set (f1 := extend_inject b1 (Some (sp, ofs)) f).
  assert (mem_inject f1 m1 tm /\ inject_incr f f1).
    assert (Int.min_signed < 0). compute; auto.
    generalize (assign_variables_incr _ _ _ _ _ _ ASVS). intro.
    unfold f1; eapply alloc_mapped_inject; eauto.
    omega. omega. omega. omega. unfold sizeof; rewrite LV. omega.
    rewrite Zminus_0_r. unfold ofs. rewrite LV. simpl.
    apply inj_offset_aligned_array'.
    intros. left. generalize (BOUND _ _ H7). omega. 
  destruct H5 as [MINJ1 INCR1].
  exploit IHalloc_variables; eauto.  
    unfold f1; rewrite <- H2; eapply match_callstack_alloc_left; eauto with coqlib.
    rewrite <- H1. omega.
    intros until delta; unfold f1, extend_inject, eq_block.
    rewrite (high_bound_alloc _ _ _ _ _ H b).
    case (zeq b b1); intros. 
    inversion H5. unfold sizeof; rewrite LV. omega.
    generalize (BOUND _ _ H5). omega. 
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
  forall fn cenv sz m e m' tm tm' sp f cs targs body,
  build_compilenv gce fn = (cenv, sz) ->
  sz <= Int.max_signed ->
  list_norepet (fn_params_names fn ++ fn_vars_names fn) ->
  alloc_variables Csharpminor.empty_env m (fn_variables fn) e m' ->
  Mem.alloc tm 0 sz = (tm', sp) ->
  match_callstack f cs m.(nextblock) tm.(nextblock) m ->
  mem_inject f m tm ->
  let tvars := make_vars (fn_params_names fn) (fn_vars_names fn) body in
  let te := set_locals tvars (set_params targs (fn_params_names fn)) in
  exists f',
     inject_incr f f'
  /\ mem_inject f' m' tm'
  /\ match_callstack f' (mkframe cenv e te sp m.(nextblock) m'.(nextblock) :: cs)
                        m'.(nextblock) tm'.(nextblock) m'.
Proof.
  intros. 
  assert (SP: sp = nextblock tm). injection H3; auto.
  unfold build_compilenv in H. 
  eapply match_callstack_alloc_variables_rec with (sz' := sz); eauto with mem.
  eapply low_bound_alloc_same; eauto.
  eapply high_bound_alloc_same; eauto.
  (* match_callstack *)
  constructor. omega. change (valid_block tm' sp). eapply valid_new_block; eauto.
  constructor. 
    (* me_vars *)
    intros. generalize (global_compilenv_charact id).
    destruct (gce!!id); intro; try contradiction.
    constructor.
      unfold Csharpminor.empty_env. apply PTree.gempty. auto.
    constructor.
      unfold Csharpminor.empty_env. apply PTree.gempty. 
    (* me_low_high *)
    omega.
    (* me_bounded *)
    intros until lv. unfold Csharpminor.empty_env. rewrite PTree.gempty. congruence.
    (* me_inj *)
    intros until lv2. unfold Csharpminor.empty_env; rewrite PTree.gempty; congruence.
    (* me_inv *)
    intros. exploit mi_mappedblocks; eauto. intro A.
    elim (fresh_block_alloc _ _ _ _ _ H3 A).
    (* me_incr *)
    intros. exploit mi_mappedblocks; eauto. intro A.
    rewrite SP; auto.
  rewrite SP; auto.
  eapply alloc_right_inject; eauto.
  omega.
  intros. exploit mi_mappedblocks; eauto. unfold valid_block; intro.
  unfold block in SP; omegaContradiction.
  (* defined *)
  intros. unfold te. apply set_locals_params_defined.
  elim (in_app_or _ _ _ H6); intros.
  elim (list_in_map_inv _ _ _ H7). intros x [A B].
  apply in_or_app; left. inversion A. apply List.in_map. auto.
  apply in_or_app; right. unfold tvars, make_vars. apply in_or_app; left. 
  change id with (fst (id, lv)). apply List.in_map; auto.
  (* norepet *)
  unfold fn_variables. 
  rewrite List.map_app. rewrite list_map_compose. simpl. 
  assumption.
  (* undef *)
  intros. unfold empty_env. apply PTree.gempty. 
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
  forall s f te1 cenv sp lo hi cs tm1 fn k,
  vars_vals_match f params vl te1 ->
  list_norepet (List.map (@fst ident memory_chunk) params) ->
  mem_inject f m1 tm1 ->
  match_callstack f (mkframe cenv e te1 sp lo hi :: cs) m1.(nextblock) tm1.(nextblock) m1 ->
  store_parameters cenv params = OK s ->
  exists te2, exists tm2,
     star step tge (State fn s k (Vptr sp Int.zero) te1 tm1)
                E0 (State fn Sskip k (Vptr sp Int.zero) te2 tm2)
  /\ mem_inject f m2 tm2
  /\ match_callstack f (mkframe cenv e te2 sp lo hi :: cs) m2.(nextblock) tm2.(nextblock) m2.
Proof.
  induction 1.
  (* base case *)
  intros; simpl. monadInv H3.
  exists te1; exists tm1. split. constructor. tauto.
  (* inductive case *)
  intros until k.  intros VVM NOREPET MINJ MATCH STOREP.
  monadInv STOREP.
  inversion VVM. subst f0 id0 chunk0 vars v vals te.
  inversion NOREPET. subst hd tl.
  exploit var_set_correct; eauto.
    constructor; auto.
    econstructor; eauto.
    econstructor; eauto.
  intros [te2 [tm2 [EXEC1 [MINJ1 [MATCH1 UNCHANGED1]]]]].
  assert (vars_vals_match f params vl te2).
    apply vars_vals_match_extensional with te1; auto.
    intros. apply UNCHANGED1. red; intro; subst id0.
    elim H4. change id with (fst (id, lv)). apply List.in_map. auto.
  exploit IHbind_parameters; eauto.
  intros [te3 [tm3 [EXEC2 [MINJ2 MATCH2]]]].
  exists te3; exists tm3.
  split. eapply star_left. constructor. 
    eapply star_left. eexact EXEC1.
    eapply star_left. constructor. eexact EXEC2.
    reflexivity. reflexivity. reflexivity.
  auto.
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
  list_norepet (vars ++ List.map (@fst ident memory_chunk) params) ->
  vars_vals_match f params args
    (set_locals vars (set_params targs (List.map (@fst ident memory_chunk) params))).
Proof.
  induction vars; simpl; intros.
  eapply vars_vals_match_holds_1; eauto.
  inversion H1. subst hd tl.
  eapply vars_vals_match_extensional; eauto.
  intros. apply PTree.gso. red; intro; subst id; elim H4.
  apply in_or_app. right. change a with (fst (a, lv)). apply List.in_map; auto.
Qed.

Lemma bind_parameters_length:
  forall e m1 params args m2,
  bind_parameters e m1 params args m2 ->
  List.length params = List.length args.
Proof.
  induction 1; simpl; eauto.
Qed.

Remark identset_removelist_charact:
  forall l s x, Identset.In x (identset_removelist l s) <-> Identset.In x s /\ ~In x l.
Proof.
  induction l; simpl; intros. tauto.
  split; intros.
  exploit Identset.remove_3; eauto. rewrite IHl. intros [P Q].  
  split. auto. intuition. elim (Identset.remove_1 H1 H).
  destruct H as [P Q]. apply Identset.remove_2. tauto. rewrite IHl. tauto.
Qed.

Remark InA_In:
  forall (A: Type) (x: A) (l: list A),
  InA (fun (x y: A) => x = y) x l <-> In x l.
Proof.
  intros. rewrite InA_alt. split; intros. destruct H as [y [P Q]]. congruence. exists x; auto. 
Qed.

Remark NoDupA_norepet:
  forall (A: Type) (l: list A),
  NoDupA (fun (x y: A) => x = y) l -> list_norepet l.
Proof.
  induction 1. constructor. constructor; auto. red; intros; elim H.
  rewrite InA_In. auto.
Qed.

Lemma make_vars_norepet:
  forall fn body,
  list_norepet (fn_params_names fn ++ fn_vars_names fn) ->
  list_norepet (make_vars (fn_params_names fn) (fn_vars_names fn) body
                ++ fn_params_names fn).
Proof.
  intros. rewrite list_norepet_app in H. destruct H as [A [B C]]. 
  rewrite list_norepet_app. split.
  unfold make_vars. rewrite list_norepet_app. split. auto. 
  split. apply NoDupA_norepet. apply Identset.elements_3w.
  red; intros. red; intros; subst y. rewrite <- InA_In in H0. 
  exploit Identset.elements_2. eexact H0.
  rewrite identset_removelist_charact. intros [P Q]. elim Q. 
  apply in_or_app. auto. 
  split. auto. 
  red; intros. unfold make_vars in H. destruct (in_app_or _ _ _ H).
  apply sym_not_equal. apply C; auto.
  rewrite <- InA_In in H1. exploit Identset.elements_2. eexact H1. 
  rewrite identset_removelist_charact. intros [P Q]. 
  red; intros; elim Q. apply in_or_app. left; congruence. 
Qed.

(** The main result in this section: the behaviour of function entry
  in the generated Cminor code (allocate stack data block and store
  parameters whose address is taken) simulates what happens at function
  entry in the original Csharpminor (allocate one block per local variable
  and initialize the blocks corresponding to function parameters). *)

Lemma function_entry_ok:
  forall fn m e m1 vargs m2 f cs tm cenv sz tm1 sp tvargs body s fn' k,
  alloc_variables empty_env m (fn_variables fn) e m1 ->
  bind_parameters e m1 fn.(Csharpminor.fn_params) vargs m2 ->
  match_callstack f cs m.(nextblock) tm.(nextblock) m ->
  build_compilenv gce fn = (cenv, sz) ->
  sz <= Int.max_signed ->
  Mem.alloc tm 0 sz = (tm1, sp) ->
  let vars :=
    make_vars (fn_params_names fn) (fn_vars_names fn) body in
  let te :=
    set_locals vars (set_params tvargs (fn_params_names fn)) in
  val_list_inject f vargs tvargs ->
  mem_inject f m tm ->
  list_norepet (fn_params_names fn ++ fn_vars_names fn) ->
  store_parameters cenv fn.(Csharpminor.fn_params) = OK s ->
  exists f2, exists te2, exists tm2,
     star step tge (State fn' s k (Vptr sp Int.zero) te tm1)
                E0 (State fn' Sskip k (Vptr sp Int.zero) te2 tm2)
  /\ mem_inject f2 m2 tm2
  /\ inject_incr f f2
  /\ match_callstack f2
       (mkframe cenv e te2 sp m.(nextblock) m1.(nextblock) :: cs)
       m2.(nextblock) tm2.(nextblock) m2.
Proof.
  intros. 
  exploit bind_parameters_length; eauto. intro LEN1.
  exploit match_callstack_alloc_variables; eauto.
  intros [f1 [INCR1 [MINJ1 MATCH1]]].
  exploit vars_vals_match_holds.
    eauto. apply val_list_inject_incr with f. eauto. eauto.
    eapply make_vars_norepet. auto. 
  intro VVM.
  exploit store_parameters_correct.
    eauto. eauto. 
    unfold fn_params_names in H7. eapply list_norepet_append_left; eauto.
    eexact MINJ1. fold (fn_params_names fn). eexact MATCH1. eauto. 
  intros [te2 [tm2 [EXEC [MINJ2 MATCH2]]]].
  exists f1; exists te2; exists tm2.
  split. eauto. auto.
Qed.

(** * Semantic preservation for the translation *)

(** The proof of semantic preservation uses simulation diagrams of the
  following form:
<<
       e, m1, s ----------------- sp, te1, tm1, ts
          |                                |
         t|                                |t
          v                                v
       e, m2, out --------------- sp, te2, tm2, tout
>>
  where [ts] is the Cminor statement obtained by translating the
  Csharpminor statement [s].  The left vertical arrow is an execution
  of a Csharpminor statement.  The right vertical arrow is an execution
  of a Cminor statement.  The precondition (top vertical bar)
  includes a [mem_inject] relation between the memory states [m1] and [tm1],
  and a [match_callstack] relation for any callstack having
  [e], [te1], [sp] as top frame.  The postcondition (bottom vertical bar)
  is the existence of a memory injection [f2] that extends the injection
  [f1] we started with, preserves the [match_callstack] relation for
  the transformed callstack at the final state, and validates a
  [outcome_inject] relation between the outcomes [out] and [tout].
*)

(** ** Semantic preservation for expressions *)

Remark bool_of_val_inject:
  forall f v tv b,
  Val.bool_of_val v b -> val_inject f v tv -> Val.bool_of_val tv b.
Proof.
  intros. inv H0; inv H; constructor; auto.
Qed.

Lemma transl_expr_correct:
  forall f m tm cenv e te sp lo hi cs
    (MINJ: mem_inject f m tm)
    (MATCH: match_callstack f
             (mkframe cenv e te sp lo hi :: cs)
             m.(nextblock) tm.(nextblock) m),
  forall a v,
  Csharpminor.eval_expr gve e m a v ->
  forall ta
    (TR: transl_expr cenv a = OK ta),
  exists tv,
     eval_expr tge (Vptr sp Int.zero) te tm ta tv
  /\ val_inject f v tv.
Proof.
  induction 3; intros; simpl in TR; try (monadInv TR).
  (* Evar *)
  eapply var_get_correct; eauto.
  (* Eaddrof *)
  eapply var_addr_correct; eauto.
  (* Econst *)
  exploit transl_constant_correct; eauto. intros [tv [A B]].
  exists tv; split. constructor; eauto. eauto.
  (* Eunop *)
  exploit IHeval_expr; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit eval_unop_compat; eauto. intros [tv [EVAL INJ]].
  exists tv; split. econstructor; eauto. auto.
  (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit IHeval_expr2; eauto. intros [tv2 [EVAL2 INJ2]].
  exploit eval_binop_compat; eauto. intros [tv [EVAL INJ]].
  exists tv; split. econstructor; eauto. auto.
  (* Eload *)
  exploit IHeval_expr; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit loadv_inject; eauto. intros [tv [LOAD INJ]].
  exists tv; split. econstructor; eauto. auto.
  (* Econdition *)
  exploit IHeval_expr1; eauto. intros [tv1 [EVAL1 INJ1]].
  assert (transl_expr cenv (if vb1 then b else c) =
          OK (if vb1 then x0 else x1)).
    destruct vb1; auto.
  exploit IHeval_expr2; eauto. intros [tv2 [EVAL2 INJ2]].
  exists tv2; split. eapply eval_Econdition; eauto.
  eapply bool_of_val_inject; eauto. auto.
Qed.

Lemma transl_exprlist_correct:
  forall f m tm cenv e te sp lo hi cs
    (MINJ: mem_inject f m tm)
    (MATCH: match_callstack f
             (mkframe cenv e te sp lo hi :: cs)
             m.(nextblock) tm.(nextblock) m),
  forall a v,
  Csharpminor.eval_exprlist gve e m a v ->
  forall ta
    (TR: transl_exprlist cenv a = OK ta),
  exists tv,
     eval_exprlist tge (Vptr sp Int.zero) te tm ta tv
  /\ val_list_inject f v tv.
Proof.
  induction 3; intros; monadInv TR.
  exists (@nil val); split. constructor. constructor.
  exploit transl_expr_correct; eauto. intros [tv1 [EVAL1 VINJ1]].
  exploit IHeval_exprlist; eauto. intros [tv2 [EVAL2 VINJ2]].
  exists (tv1 :: tv2); split. constructor; auto. constructor; auto.
Qed.

(** ** Semantic preservation for statements and functions *)

Inductive match_cont: Csharpminor.cont -> Cminor.cont -> compilenv -> exit_env -> callstack -> Prop :=
  | match_Kstop: forall cenv xenv,
      match_cont Csharpminor.Kstop Kstop cenv xenv nil
  | match_Kseq: forall s k ts tk cenv xenv cs,
      transl_stmt cenv xenv s = OK ts ->
      match_cont k tk cenv xenv cs ->
      match_cont (Csharpminor.Kseq s k) (Kseq ts tk) cenv xenv cs
  | match_Kseq2: forall s1 s2 k ts1 tk cenv xenv cs,
      transl_stmt cenv xenv s1 = OK ts1 ->
      match_cont (Csharpminor.Kseq s2 k) tk cenv xenv cs ->
      match_cont (Csharpminor.Kseq (Csharpminor.Sseq s1 s2) k)
                 (Kseq ts1 tk) cenv xenv cs
  | match_Kblock: forall k tk cenv xenv cs,
      match_cont k tk cenv xenv cs ->
      match_cont (Csharpminor.Kblock k) (Kblock tk) cenv (true :: xenv) cs
  | match_Kblock2: forall k tk cenv xenv cs,
      match_cont k tk cenv xenv cs ->
      match_cont k (Kblock tk) cenv (false :: xenv) cs
  | match_Kcall_none: forall fn e k tfn sp te tk cenv xenv lo hi cs sz cenv',
      transl_funbody cenv sz fn = OK tfn ->
      match_cont k tk cenv xenv cs ->
      match_cont (Csharpminor.Kcall None fn e k)
                 (Kcall None tfn (Vptr sp Int.zero) te tk)
                 cenv' nil
                 (mkframe cenv e te sp lo hi :: cs)
  | match_Kcall_some: forall id fn e k tfn s sp te tk cenv xenv lo hi cs sz cenv',
      transl_funbody cenv sz fn = OK tfn ->
      var_set cenv id (Evar id) = OK s ->
      match_cont k tk cenv xenv cs ->
      match_cont (Csharpminor.Kcall (Some id) fn e k)
                 (Kcall (Some id) tfn (Vptr sp Int.zero) te (Kseq s tk))
                 cenv' nil
                 (mkframe cenv e te sp lo hi :: cs).

Inductive match_states: Csharpminor.state -> Cminor.state -> Prop :=
  | match_state:
      forall fn s k e m tfn ts tk sp te tm cenv xenv f lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt cenv xenv s = OK ts)
      (MINJ: mem_inject f m tm)
      (MCS: match_callstack f
               (mkframe cenv e te sp lo hi :: cs)
               m.(nextblock) tm.(nextblock) m)
      (MK: match_cont k tk cenv xenv cs),
      match_states (Csharpminor.State fn s k e m)
                   (State tfn ts tk (Vptr sp Int.zero) te tm)
  | match_state_seq:
      forall fn s1 s2 k e m tfn ts1 tk sp te tm cenv xenv f lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt cenv xenv s1 = OK ts1)
      (MINJ: mem_inject f m tm)
      (MCS: match_callstack f
               (mkframe cenv e te sp lo hi :: cs)
               m.(nextblock) tm.(nextblock) m)
      (MK: match_cont (Csharpminor.Kseq s2 k) tk cenv xenv cs),
      match_states (Csharpminor.State fn (Csharpminor.Sseq s1 s2) k e m)
                   (State tfn ts1 tk (Vptr sp Int.zero) te tm)
  | match_callstate:
      forall fd args k m tfd targs tk tm f cs cenv
      (TR: transl_fundef gce fd = OK tfd)
      (MINJ: mem_inject f m tm)
      (MCS: match_callstack f cs m.(nextblock) tm.(nextblock) m)
      (MK: match_cont k tk cenv nil cs)
      (ISCC: Csharpminor.is_call_cont k)
      (ARGSINJ: val_list_inject f args targs),
      match_states (Csharpminor.Callstate fd args k m)
                   (Callstate tfd targs tk tm)
  | match_returnstate:
      forall v k m tv tk tm f cs cenv
      (MINJ: mem_inject f m tm)
      (MCS: match_callstack f cs m.(nextblock) tm.(nextblock) m)
      (MK: match_cont k tk cenv nil cs)
      (RESINJ: val_inject f v tv),
      match_states (Csharpminor.Returnstate v k m)
                   (Returnstate tv tk tm).

Remark nextblock_freelist:
  forall lb m, nextblock (free_list m lb) = nextblock m.
Proof. induction lb; intros; simpl; auto. Qed. 

Remark val_inject_function_pointer:
  forall v fd f tv,
  Genv.find_funct tge v = Some fd ->
  match_globalenvs f ->
  val_inject f v tv ->
  tv = v.
Proof.
  intros. exploit Genv.find_funct_inv; eauto. intros [b EQ]. subst v.
  rewrite Genv.find_funct_find_funct_ptr in H. 
  assert (b < 0). unfold tge in H. eapply Genv.find_funct_ptr_negative; eauto.
  assert (f b = Some(b, 0)). eapply mg_functions; eauto. 
  inv H1. rewrite H3 in H6; inv H6. reflexivity.
Qed.

Lemma match_call_cont:
  forall k tk cenv xenv cs,
  match_cont k tk cenv xenv cs ->
  match_cont (Csharpminor.call_cont k) (call_cont tk) cenv nil cs.
Proof.
  induction 1; simpl; auto; econstructor; eauto.
Qed.

Lemma match_is_call_cont:
  forall tfn te sp tm k tk cenv xenv cs,
  match_cont k tk cenv xenv cs ->
  Csharpminor.is_call_cont k ->
  exists tk',
    star step tge (State tfn Sskip tk sp te tm)
               E0 (State tfn Sskip tk' sp te tm)
    /\ is_call_cont tk'
    /\ match_cont k tk' cenv nil cs.
Proof.
  induction 1; simpl; intros; try contradiction.
  econstructor; split. apply star_refl. split. exact I. econstructor; eauto.
  exploit IHmatch_cont; eauto.
  intros [tk' [A B]]. exists tk'; split.
  eapply star_left; eauto. constructor. traceEq. auto.
  econstructor; split. apply star_refl. split. exact I. econstructor; eauto.
  econstructor; split. apply star_refl. split. exact I. econstructor; eauto.
Qed.

(** Properties of [switch] compilation *)

Require Import Switch.

Remark switch_table_shift:
  forall n sl base dfl,
  switch_target n (S dfl) (switch_table sl (S base)) =
  S (switch_target n dfl (switch_table sl base)).
Proof.
  induction sl; intros; simpl. auto. destruct (Int.eq n i); auto. 
Qed.

Remark length_switch_table:
  forall sl base1 base2,
  length (switch_table sl base1) = length (switch_table sl base2).
Proof.
  induction sl; intros; simpl. auto. decEq; auto.
Qed.

Inductive transl_lblstmt_cont (cenv: compilenv) (xenv: exit_env): lbl_stmt -> cont -> cont -> Prop :=
  | tlsc_default: forall s k ts,
      transl_stmt cenv (switch_env (LSdefault s) xenv) s = OK ts ->
      transl_lblstmt_cont cenv xenv (LSdefault s) k (Kblock (Kseq ts k))
  | tlsc_case: forall i s ls k ts k',
      transl_stmt cenv (switch_env (LScase i s ls) xenv) s = OK ts ->
      transl_lblstmt_cont cenv xenv ls k k' ->
      transl_lblstmt_cont cenv xenv (LScase i s ls) k (Kblock (Kseq ts k')).

Lemma switch_descent:
  forall cenv xenv k ls body s,
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK s ->
  exists k',
  transl_lblstmt_cont cenv xenv ls k k'
  /\ (forall f sp e m,
      plus step tge (State f s k sp e m) E0 (State f body k' sp e m)).
Proof.
  induction ls; intros. 
  monadInv H. econstructor; split.
  econstructor; eauto.
  intros. eapply plus_left. constructor. apply star_one. constructor. traceEq.
  monadInv H. exploit IHls; eauto. intros [k' [A B]]. 
  econstructor; split.
  econstructor; eauto.
  intros. eapply plus_star_trans. eauto. 
  eapply star_left. constructor. apply star_one. constructor. 
  reflexivity. traceEq.
Qed.

Lemma switch_ascent:
  forall f n sp e m cenv xenv k ls k1,
  let tbl := switch_table ls O in
  let ls' := select_switch n ls in
  transl_lblstmt_cont cenv xenv ls k k1 ->
  exists k2,
  star step tge (State f (Sexit (switch_target n (length tbl) tbl)) k1 sp e m)
             E0 (State f (Sexit O) k2 sp e m)
  /\ transl_lblstmt_cont cenv xenv ls' k k2.
Proof.
  induction ls; intros; unfold tbl, ls'; simpl.
  inv H. econstructor; split. apply star_refl. econstructor; eauto.
  simpl in H. inv H. 
  rewrite Int.eq_sym. destruct (Int.eq i n).
  econstructor; split. apply star_refl. econstructor; eauto. 
  exploit IHls; eauto. intros [k2 [A B]].
  rewrite (length_switch_table ls 1%nat 0%nat). 
  rewrite switch_table_shift.
  econstructor; split. 
  eapply star_left. constructor. eapply star_left. constructor. eexact A. 
  reflexivity. traceEq.
  exact B.
Qed.

Lemma switch_match_cont:
  forall cenv xenv k cs tk ls tk',
  match_cont k tk cenv xenv cs ->
  transl_lblstmt_cont cenv xenv ls tk tk' ->
  match_cont (Csharpminor.Kseq (seq_of_lbl_stmt ls) k) tk' cenv (false :: switch_env ls xenv) cs.
Proof.
  induction ls; intros; simpl.
  inv H0. apply match_Kblock2. econstructor; eauto.
  inv H0. apply match_Kblock2. eapply match_Kseq2. auto. eauto. 
Qed.

Lemma transl_lblstmt_suffix:
  forall n cenv xenv ls body ts,
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  let ls' := select_switch n ls in
  exists body', exists ts',
  transl_lblstmt cenv (switch_env ls' xenv) ls' body' = OK ts'.
Proof.
  induction ls; simpl; intros. 
  monadInv H.
  exists body; econstructor. rewrite EQ; eauto. simpl. reflexivity.
  monadInv H.
  destruct (Int.eq i n).
  exists body; econstructor. simpl. rewrite EQ; simpl. rewrite EQ0; simpl. reflexivity.
  eauto.
Qed.

Lemma switch_match_states:
  forall fn k e m tfn ts tk sp te tm cenv xenv f lo hi cs sz ls body tk'
    (TRF: transl_funbody cenv sz fn = OK tfn)
    (TR: transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts)
    (MINJ: mem_inject f m tm)
    (MCS: match_callstack f
             (mkframe cenv e te sp lo hi :: cs)
             m.(nextblock) tm.(nextblock) m)
    (MK: match_cont k tk cenv xenv cs)
    (TK: transl_lblstmt_cont cenv xenv ls tk tk'),
  exists S,
  plus step tge (State tfn (Sexit O) tk' (Vptr sp Int.zero) te tm) E0 S
  /\ match_states (Csharpminor.State fn (seq_of_lbl_stmt ls) k e m) S.
Proof.
  intros. destruct ls; simpl.
  inv TK. econstructor; split. 
    eapply plus_left. constructor. apply star_one. constructor. traceEq.
    eapply match_state; eauto. 
  inv TK. econstructor; split.
    eapply plus_left. constructor. apply star_one. constructor. traceEq.
    eapply match_state_seq; eauto.
    simpl. eapply switch_match_cont; eauto.
Qed.

(** Commutation between [find_label] and compilation *)

Section FIND_LABEL.

Variable lbl: label.
Variable cenv: compilenv.
Variable cs: callstack.

Remark find_label_var_set:
  forall id e s k,
  var_set cenv id e = OK s ->
  find_label lbl s k = None.
Proof.
  intros. unfold var_set in H.
  destruct (cenv!!id); monadInv H; reflexivity.
Qed.

Lemma transl_lblstmt_find_label_context:
  forall cenv xenv ls body ts tk1 tk2 ts' tk',
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  transl_lblstmt_cont cenv xenv ls tk1 tk2 ->
  find_label lbl body tk2 = Some (ts', tk') ->
  find_label lbl ts tk1 = Some (ts', tk').
Proof.
  induction ls; intros.
  monadInv H. inv H0. simpl. simpl in H2. replace x with ts by congruence. rewrite H1. auto.
  monadInv H. inv H0.
  eapply IHls. eauto. eauto. simpl in H6. replace x with ts0 by congruence. simpl.
  rewrite H1. auto.
Qed.

Lemma transl_find_label:
  forall s k xenv ts tk,
  transl_stmt cenv xenv s = OK ts ->
  match_cont k tk cenv xenv cs ->
  match Csharpminor.find_label lbl s k with
  | None => find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', exists xenv',
        find_label lbl ts tk = Some(ts', tk')
     /\ transl_stmt cenv xenv' s' = OK ts'
     /\ match_cont k' tk' cenv xenv' cs
  end

with transl_lblstmt_find_label:
  forall ls xenv body k ts tk tk1,
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  match_cont k tk cenv xenv cs ->
  transl_lblstmt_cont cenv xenv ls tk tk1 ->
  find_label lbl body tk1 = None ->
  match Csharpminor.find_label_ls lbl ls k with
  | None => find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', exists xenv',
        find_label lbl ts tk = Some(ts', tk')
     /\ transl_stmt cenv xenv' s' = OK ts'
     /\ match_cont k' tk' cenv xenv' cs
  end.
Proof.
  intros. destruct s; try (monadInv H); simpl; auto.
  (* assign *)
  eapply find_label_var_set; eauto.
  (* call *)
  destruct o; monadInv H; simpl; auto.
  eapply find_label_var_set; eauto.
  (* seq *)
  exploit (transl_find_label s1). eauto. eapply match_Kseq. eexact EQ1. eauto.  
  destruct (Csharpminor.find_label lbl s1 (Csharpminor.Kseq s2 k)) as [[s' k'] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]]. 
  exists ts'; exists tk'; exists xenv'. intuition. rewrite A; auto.
  intro. rewrite H. apply transl_find_label with xenv; auto. 
  (* ifthenelse *)
  exploit (transl_find_label s1). eauto. eauto.  
  destruct (Csharpminor.find_label lbl s1 k) as [[s' k'] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]]. 
  exists ts'; exists tk'; exists xenv'. intuition. rewrite A; auto.
  intro. rewrite H. apply transl_find_label with xenv; auto. 
  (* loop *)
  apply transl_find_label with xenv. auto. econstructor; eauto. simpl. rewrite EQ; auto.
  (* block *)
  apply transl_find_label with (true :: xenv). auto. constructor; auto. 
  (* switch *)
  exploit switch_descent; eauto. intros [k' [A B]].
  eapply transl_lblstmt_find_label. eauto. eauto. eauto. reflexivity.  
  (* return *)
  destruct o; monadInv H; auto.
  (* label *)
  destruct (ident_eq lbl l).
  exists x; exists tk; exists xenv; auto.
  apply transl_find_label with xenv; auto.

  intros. destruct ls; monadInv H; simpl.
  (* default *)
  inv H1. simpl in H3. replace x with ts by congruence. rewrite H2.
  eapply transl_find_label; eauto.
  (* case *)
  inv H1. simpl in H7.
  exploit (transl_find_label s). eauto. eapply switch_match_cont; eauto. 
  destruct (Csharpminor.find_label lbl s (Csharpminor.Kseq (seq_of_lbl_stmt ls) k)) as [[s' k''] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]].
  exists ts'; exists tk'; exists xenv'; intuition. 
  eapply transl_lblstmt_find_label_context; eauto. 
  simpl. replace x with ts0 by congruence. rewrite H2. auto.
  intro.
  eapply transl_lblstmt_find_label. eauto. auto. eauto. 
  simpl. replace x with ts0 by congruence. rewrite H2. auto. 
Qed.

Remark find_label_store_parameters:
  forall vars s k,
  store_parameters cenv vars = OK s -> find_label lbl s k = None.
Proof.
  induction vars; intros.
  monadInv H. auto.
  simpl in H. destruct a as [id lv]. monadInv H.
  simpl. rewrite (find_label_var_set id (Evar id)); auto.
Qed.

End FIND_LABEL.

Lemma transl_find_label_body:
  forall cenv xenv size f tf k tk cs lbl s' k',
  transl_funbody cenv size f = OK tf ->
  match_cont k tk cenv xenv cs ->
  Csharpminor.find_label lbl f.(Csharpminor.fn_body) (Csharpminor.call_cont k) = Some (s', k') ->
  exists ts', exists tk', exists xenv',
     find_label lbl tf.(fn_body) (call_cont tk) = Some(ts', tk')
  /\ transl_stmt cenv xenv' s' = OK ts'
  /\ match_cont k' tk' cenv xenv' cs.
Proof.
  intros. monadInv H. simpl. 
  rewrite (find_label_store_parameters lbl cenv (Csharpminor.fn_params f)); auto.
  exploit transl_find_label. eexact EQ. eapply match_call_cont. eexact H0.
  instantiate (1 := lbl). rewrite H1. auto.
Qed.


Require Import Coq.Program.Equality.

Fixpoint seq_left_depth (s: Csharpminor.stmt) : nat :=
  match s with
  | Csharpminor.Sseq s1 s2 => S (seq_left_depth s1)
  | _ => O
  end.

Definition measure (S: Csharpminor.state) : nat :=
  match S with
  | Csharpminor.State fn s k e m => seq_left_depth s
  | _ => O
  end.

Lemma transl_step_correct:
  forall S1 t S2, Csharpminor.step gve S1 t S2 ->
  forall T1, match_states S1 T1 ->
  (exists T2, plus step tge T1 t T2 /\ match_states S2 T2)
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 T1)%nat.
Proof.
  induction 1; intros T1 MSTATE; inv MSTATE.

(* skip seq *)
  monadInv TR. left.
  dependent induction MK.
  econstructor; split. 
  apply plus_one. constructor.
  econstructor; eauto.
  econstructor; split.
  apply plus_one. constructor.
  eapply match_state_seq; eauto. 
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split. eapply plus_left. constructor. apply plus_star; eauto. traceEq.
  auto.
(* skip block *)
  monadInv TR. left.
  dependent induction MK.
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto.
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split. eapply plus_left. constructor. apply plus_star; eauto. traceEq.
  auto.
(* skip call *)
  monadInv TR. left.
  exploit match_is_call_cont; eauto. intros [tk' [A [B C]]]. 
  exploit match_callstack_freelist; eauto. intros [P Q].
  econstructor; split.
  eapply plus_right. eexact A. apply step_skip_call. auto.
  rewrite (sig_preserved_body _ _ _ _ TRF). auto. traceEq.
  econstructor; eauto. rewrite nextblock_freelist. simpl. eauto. 

(* assign *)
  monadInv TR. 
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  exploit var_set_correct; eauto. intros [te' [tm' [EXEC [MINJ' [MCS' OTHER]]]]].
  left; econstructor; split.
  apply plus_one. eexact EXEC.
  econstructor; eauto. 

(* store *)
  monadInv TR.
  exploit transl_expr_correct. eauto. eauto. eexact H. eauto. 
  intros [tv1 [EVAL1 VINJ1]].
  exploit transl_expr_correct. eauto. eauto. eexact H0. eauto. 
  intros [tv2 [EVAL2 VINJ2]].
  exploit make_store_correct. eexact EVAL1. eexact EVAL2. eauto. eauto. auto. auto.
  intros [tm' [EXEC [MINJ' NEXTBLOCK]]].
  left; econstructor; split.
  apply plus_one. eexact EXEC.
  unfold storev in H1; destruct vaddr; try discriminate.
  econstructor; eauto.
  replace (nextblock m') with (nextblock m). rewrite NEXTBLOCK. eauto.
  eapply match_callstack_mapped; eauto. inv VINJ1. congruence.
  symmetry. eapply nextblock_store; eauto.

(* call *)
  simpl in H1. exploit functions_translated; eauto. intros [tfd [FIND TRANS]].
  simpl in TR. destruct optid; monadInv TR.
(* with return value *)
  exploit transl_expr_correct; eauto.
  intros [tvf [EVAL1 VINJ1]].
  assert (tvf = vf).
    eapply val_inject_function_pointer; eauto.
    eapply match_callstack_match_globalenvs; eauto.
  subst tvf.
  exploit transl_exprlist_correct; eauto.
  intros [tvargs [EVAL2 VINJ2]].
  left; econstructor; split.
  eapply plus_left. constructor. apply star_one. 
  eapply step_call; eauto.
  apply sig_preserved; eauto.
  traceEq.
  econstructor; eauto.
  eapply match_Kcall_some with (cenv' := cenv); eauto.
  red; auto.
(* without return value *)
  exploit transl_expr_correct; eauto.
  intros [tvf [EVAL1 VINJ1]].
  assert (tvf = vf).
    eapply val_inject_function_pointer; eauto.
    eapply match_callstack_match_globalenvs; eauto.
  subst tvf.
  exploit transl_exprlist_correct; eauto.
  intros [tvargs [EVAL2 VINJ2]].
  left; econstructor; split.
  apply plus_one. 
  eapply step_call; eauto.
  apply sig_preserved; eauto.
  econstructor; eauto.
  eapply match_Kcall_none with (cenv' := cenv); eauto.
  red; auto.

(* seq *)
  monadInv TR. 
  left; econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto.
  econstructor; eauto.
(* seq 2 *)
  right. split. auto. split. auto. econstructor; eauto. 

(* ifthenelse *)
  monadInv TR.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  left; exists (State tfn (if b then x0 else x1) tk (Vptr sp Int.zero) te tm); split.
  apply plus_one. eapply step_ifthenelse; eauto. eapply bool_of_val_inject; eauto.
  econstructor; eauto. destruct b; auto.

(* loop *)
  monadInv TR.
  left; econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto.
  econstructor; eauto. simpl. rewrite EQ; auto. 

(* block *)
  monadInv TR.
  left; econstructor; split.
  apply plus_one. constructor. 
  econstructor; eauto.
  econstructor; eauto.

(* exit seq *)
  monadInv TR. left.
  dependent induction MK.
  econstructor; split. 
  apply plus_one. constructor.
  econstructor; eauto. simpl. auto.
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split; auto. eapply plus_left. constructor. apply plus_star; eauto. traceEq.
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split; auto. eapply plus_left.
  simpl. constructor. apply plus_star; eauto. traceEq.

(* exit block 0 *)
  monadInv TR. left.
  dependent induction MK.
  econstructor; split.
  simpl. apply plus_one. constructor. 
  econstructor; eauto.
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split; auto. simpl. 
  eapply plus_left. constructor. apply plus_star; eauto. traceEq.

(* exit block n+1 *)
  monadInv TR. left.
  dependent induction MK.
  econstructor; split.
  simpl. apply plus_one. constructor. 
  econstructor; eauto. auto. 
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split; auto. simpl. 
  eapply plus_left. constructor. apply plus_star; eauto. traceEq.

(* switch *)
  monadInv TR. left.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  inv VINJ.
  exploit switch_descent; eauto. intros [k1 [A B]].
  exploit switch_ascent; eauto. intros [k2 [C D]].
  exploit transl_lblstmt_suffix; eauto. simpl. intros [body' [ts' E]].
  exploit switch_match_states; eauto. intros [T2 [F G]].
  exists T2; split.
  eapply plus_star_trans. eapply B.  
  eapply star_left. econstructor; eauto. 
  eapply star_trans. eexact C. 
  apply plus_star. eexact F.
  reflexivity. reflexivity. traceEq.
  auto.

(* return none *)
  monadInv TR. left.
  exploit match_callstack_freelist; eauto. intros [A B].
  econstructor; split.
  apply plus_one. apply step_return_0.
(* 
  rewrite (sig_preserved_body _ _ _ _ TRF). auto.
*)
  econstructor; eauto. rewrite nextblock_freelist. simpl. eauto.
  eapply match_call_cont; eauto.

(* return some *)
  monadInv TR. left. 
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  exploit match_callstack_freelist; eauto. intros [A B].
  econstructor; split.
  apply plus_one. apply step_return_1. eauto. 
  econstructor; eauto. rewrite nextblock_freelist. simpl. eauto.
  eapply match_call_cont; eauto.

(* label *)
  monadInv TR.
  left; econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto.

(* goto *)
  monadInv TR.
  exploit transl_find_label_body; eauto. 
  intros [ts' [tk' [xenv' [A [B C]]]]].
  left; econstructor; split.
  apply plus_one. apply step_goto. eexact A. 
  econstructor; eauto.

(* internal call *)
  monadInv TR. generalize EQ; clear EQ; unfold transl_function.
  caseEq (build_compilenv gce f). intros ce sz BC.
  destruct (zle sz Int.max_signed); try congruence.
  intro TRBODY.
  generalize TRBODY; intro TMP. monadInv TMP.
  caseEq (alloc tm 0 sz). intros tm' sp ALLOC'.
  exploit function_entry_ok; eauto. 
  intros [f2 [te2 [tm2 [EXEC [MINJ2 [IINCR MCS2]]]]]].
  left; econstructor; split.
  eapply plus_left. constructor; simpl; eauto. 
  simpl. eapply star_left. constructor.
  eapply star_right. eexact EXEC. constructor.
  reflexivity. reflexivity. traceEq.
  econstructor. eexact TRBODY. eauto. eexact MINJ2. 
  eexact MCS2.
  inv MK; simpl in ISCC; contradiction || econstructor; eauto.

(* external call *)
  monadInv TR. 
  exploit event_match_inject; eauto. intros [A B].
  left; econstructor; split.
  apply plus_one. econstructor; eauto. 
  econstructor; eauto.

(* return *)
  inv MK; inv H.
  (* no argument *)
  left; econstructor; split.
  apply plus_one. econstructor; eauto. 
  simpl. econstructor; eauto. 
  (* one argument *)
  exploit var_set_self_correct; eauto.
  intros [te' [tm' [A [B C]]]].
  left; econstructor; split.
  eapply plus_left. econstructor. simpl. eapply star_left. econstructor.
  eapply star_one. eexact A.
  reflexivity. traceEq.
  econstructor; eauto. 
Qed.

Lemma match_globalenvs_init:
  let m := Genv.init_mem prog in
  match_globalenvs (meminj_init m).
Proof.
  intros. constructor.
  intros. split.
  unfold meminj_init. rewrite zlt_true. auto.
  unfold m; eapply Genv.find_symbol_not_fresh; eauto.
  rewrite <- H. apply symbols_preserved.
  intros. unfold meminj_init. rewrite zlt_true. auto.
  generalize (nextblock_pos m). omega.
Qed.

Lemma transl_initial_states:
  forall S, Csharpminor.initial_state prog S ->
  exists R, Cminor.initial_state tprog R /\ match_states S R.
Proof.
  induction 1.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  econstructor; split.
  econstructor.
  simpl. fold tge. rewrite symbols_preserved.
  replace (prog_main tprog) with (prog_main prog). eexact H.
  symmetry. unfold transl_program in TRANSL.
  eapply transform_partial_program2_main; eauto.
  eexact FIND. 
  rewrite <- H1. apply sig_preserved; auto.
  rewrite (Genv.init_mem_transf_partial2 _ _ _ TRANSL). 
  fold m0.
  eapply match_callstate with (f := meminj_init m0) (cs := @nil frame).
  auto.
  apply init_inject. unfold m0. apply Genv.initmem_inject_neutral.
  constructor. apply match_globalenvs_init. 
  instantiate (1 := gce). constructor.
  red; auto.
  constructor.
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> Csharpminor.final_state S r -> Cminor.final_state R r.
Proof.
  intros. inv H0. inv H. inv MK. inv RESINJ. constructor.
Qed.

Theorem transl_program_correct:
  forall (beh: program_behavior),
  not_wrong beh -> Csharpminor.exec_program prog beh ->
  Cminor.exec_program tprog beh.
Proof.
  unfold Csharpminor.exec_program, Cminor.exec_program; intros.
  eapply simulation_star_preservation; eauto.
  eexact transl_initial_states.
  eexact transl_final_states.
  eexact transl_step_correct. 
Qed.

End TRANSLATION.

