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

Require Import Coq.Program.Equality.
Require Import FSets.
Require Import Permutation.
Require Import Coqlib.
Require Intv.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Switch.
Require Import Csharpminor.
Require Import Cminor.
Require Import Cminorgen.

Open Local Scope error_monad_scope.

Section TRANSLATION.

Variable prog: Csharpminor.program.
Variable tprog: program.
Hypothesis TRANSL: transl_program prog = OK tprog.
Let ge : Csharpminor.genv := Genv.globalenv prog.
Let tge: genv := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf_partial transl_fundef _ TRANSL).

Lemma function_ptr_translated:
  forall (b: block) (f: Csharpminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial transl_fundef _ TRANSL).

Lemma functions_translated:
  forall (v: val) (f: Csharpminor.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial transl_fundef _ TRANSL).

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof (Genv.find_var_info_transf_partial transl_fundef _ TRANSL).

Lemma sig_preserved_body:
  forall f tf cenv size,
  transl_funbody cenv size f = OK tf -> 
  tf.(fn_sig) = Csharpminor.fn_sig f.
Proof.
  intros. unfold transl_funbody in H. monadInv H; reflexivity.
Qed.

Lemma sig_preserved:
  forall f tf,
  transl_fundef f = OK tf -> 
  Cminor.funsig tf = Csharpminor.funsig f.
Proof.
  intros until tf; destruct f; simpl.
  unfold transl_function. destruct (build_compilenv f).
  case (zle z Int.max_unsigned); simpl bind; try congruence.
  intros. monadInv H. simpl. eapply sig_preserved_body; eauto. 
  intro. inv H. reflexivity.
Qed.

(** * Derived properties of memory operations *)

Lemma load_freelist:
  forall fbl chunk m b ofs m',
  (forall b' lo hi, In (b', lo, hi) fbl -> b' <> b) -> 
  Mem.free_list m fbl = Some m' ->
  Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  induction fbl; intros.
  simpl in H0. congruence.
  destruct a as [[b' lo] hi].
  generalize H0. simpl. case_eq (Mem.free m b' lo hi); try congruence.
  intros m1 FR1 FRL. 
  transitivity (Mem.load chunk m1 b ofs).
  eapply IHfbl; eauto. intros. eapply H. eauto with coqlib. 
  eapply Mem.load_free; eauto. left. apply sym_not_equal. eapply H. auto with coqlib. 
Qed.

Lemma perm_freelist:
  forall fbl m m' b ofs k p,
  Mem.free_list m fbl = Some m' ->
  Mem.perm m' b ofs k p ->
  Mem.perm m b ofs k p.
Proof.
  induction fbl; simpl; intros until p.
  congruence.
  destruct a as [[b' lo] hi]. case_eq (Mem.free m b' lo hi); try congruence.
  intros. eauto with mem.
Qed.

Lemma nextblock_freelist:
  forall fbl m m',
  Mem.free_list m fbl = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction fbl; intros until m'; simpl.
  congruence.
  destruct a as [[b lo] hi]. 
  case_eq (Mem.free m b lo hi); intros; try congruence.
  transitivity (Mem.nextblock m0). eauto. eapply Mem.nextblock_free; eauto.
Qed.

Lemma free_list_freeable:
  forall l m m',
  Mem.free_list m l = Some m' ->
  forall b lo hi,
  In (b, lo, hi) l -> Mem.range_perm m b lo hi Cur Freeable.
Proof.
  induction l; simpl; intros.
  contradiction.
  revert H. destruct a as [[b' lo'] hi'].
  caseEq (Mem.free m b' lo' hi'); try congruence.
  intros m1 FREE1 FREE2.
  destruct H0. inv H. 
  eauto with mem.
  red; intros. eapply Mem.perm_free_3; eauto. exploit IHl; eauto.
Qed.

Lemma nextblock_storev:
  forall chunk m addr v m',
  Mem.storev chunk m addr v = Some m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  unfold Mem.storev; intros. destruct addr; try discriminate. 
  eapply Mem.nextblock_store; eauto.
Qed.

(** * Correspondence between C#minor's and Cminor's environments and memory states *)

(** In C#minor, every variable is stored in a separate memory block.
  In the corresponding Cminor code, these variables become sub-blocks
  of the stack data block.  We capture these changes in memory via a
  memory injection [f]: 
  [f b = Some(b', ofs)] means that C#minor block [b] corresponds
  to a sub-block of Cminor block [b] at offset [ofs].

  A memory injection [f] defines a relation [val_inject f] between
  values and a relation [Mem.inject f] between memory states.  These
  relations will be used intensively in our proof of simulation
  between C#minor and Cminor executions. *)

(** ** Matching between Cshaprminor's temporaries and Cminor's variables *)

Definition match_temps (f: meminj) (le: Csharpminor.temp_env) (te: env) : Prop :=
  forall id v, le!id = Some v -> exists v', te!(id) = Some v' /\ val_inject f v v'.

Lemma match_temps_invariant:
  forall f f' le te,
  match_temps f le te ->
  inject_incr f f' ->
  match_temps f' le te.
Proof.
  intros; red; intros. destruct (H _ _ H1) as [v' [A B]]. exists v'; eauto.
Qed.

Lemma match_temps_assign:
  forall f le te id v tv,
  match_temps f le te ->
  val_inject f v tv ->
  match_temps f (PTree.set id v le) (PTree.set id tv te).
Proof.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  inv H1. exists tv; auto.
  eauto.
Qed.

(** ** Matching between C#minor's variable environment and Cminor's stack pointer *)

Inductive match_var (f: meminj) (sp: block): option (block * Z) -> option Z -> Prop :=
  | match_var_local: forall b sz ofs,
      val_inject f (Vptr b Int.zero) (Vptr sp (Int.repr ofs)) ->
      match_var f sp (Some(b, sz)) (Some ofs)
  | match_var_global:
      match_var f sp None None.

(** Matching between a C#minor environment [e] and a Cminor
  stack pointer [sp]. The [lo] and [hi] parameters delimit the range
  of addresses for the blocks referenced from [te]. *)

Record match_env (f: meminj) (cenv: compilenv)
                 (e: Csharpminor.env) (sp: block)
                 (lo hi: Z) : Prop :=
  mk_match_env {

(** C#minor local variables match sub-blocks of the Cminor stack data block. *)
    me_vars:
      forall id, match_var f sp (e!id) (cenv!id);

(** [lo, hi] is a proper interval. *)
    me_low_high:
      lo <= hi;

(** Every block appearing in the C#minor environment [e] must be
  in the range [lo, hi]. *)
    me_bounded:
      forall id b sz, PTree.get id e = Some(b, sz) -> lo <= b < hi;

(** All blocks mapped to sub-blocks of the Cminor stack data must be
    images of variables from the C#minor environment [e] *)
    me_inv:
      forall b delta,
      f b = Some(sp, delta) ->
      exists id, exists sz, PTree.get id e = Some(b, sz);

(** All C#minor blocks below [lo] (i.e. allocated before the blocks
  referenced from [e]) must map to blocks that are below [sp]
  (i.e. allocated before the stack data for the current Cminor function). *)
    me_incr:
      forall b tb delta,
      f b = Some(tb, delta) -> b < lo -> tb < sp
  }.

Ltac geninv x := 
  let H := fresh in (generalize x; intro H; inv H).

Lemma match_env_invariant:
  forall f1 cenv e sp lo hi f2,
  match_env f1 cenv e sp lo hi ->
  inject_incr f1 f2 ->
  (forall b delta, f2 b = Some(sp, delta) -> f1 b = Some(sp, delta)) ->
  (forall b, b < lo -> f2 b = f1 b) ->
  match_env f2 cenv e sp lo hi.
Proof.
  intros. destruct H. constructor; auto.
(* vars *)
  intros. geninv (me_vars0 id); econstructor; eauto.
(* bounded *)
  intros. eauto. 
(* below *)
  intros. rewrite H2 in H; eauto.
Qed.

(** [match_env] and external calls *)

Remark inject_incr_separated_same:
  forall f1 f2 m1 m1',
  inject_incr f1 f2 -> inject_separated f1 f2 m1 m1' ->
  forall b, Mem.valid_block m1 b -> f2 b = f1 b.
Proof.
  intros. case_eq (f1 b).
  intros [b' delta] EQ. apply H; auto. 
  intros EQ. case_eq (f2 b).
  intros [b'1 delta1] EQ1. exploit H0; eauto. intros [C D]. contradiction.
  auto.
Qed.

Remark inject_incr_separated_same':
  forall f1 f2 m1 m1',
  inject_incr f1 f2 -> inject_separated f1 f2 m1 m1' ->
  forall b b' delta,
  f2 b = Some(b', delta) -> Mem.valid_block m1' b' -> f1 b = Some(b', delta).
Proof.
  intros. case_eq (f1 b).
  intros [b'1 delta1] EQ. exploit H; eauto. congruence.
  intros. exploit H0; eauto. intros [C D]. contradiction.
Qed.

Lemma match_env_external_call:
  forall f1 cenv e sp lo hi f2 m1 m1',
  match_env f1 cenv e sp lo hi ->
  inject_incr f1 f2 ->
  inject_separated f1 f2 m1 m1' ->
  hi <= Mem.nextblock m1 -> sp < Mem.nextblock m1' ->
  match_env f2 cenv e sp lo hi.
Proof.
  intros. apply match_env_invariant with f1; auto.
  intros. eapply inject_incr_separated_same'; eauto.
  intros. eapply inject_incr_separated_same; eauto. red. destruct H. omega. 
Qed.

(** [match_env] and allocations *)

Lemma match_env_alloc:
  forall f1 id cenv e sp lo m1 sz m2 b ofs f2,
  match_env f1 (PTree.remove id cenv) e sp lo (Mem.nextblock m1) ->
  Mem.alloc m1 0 sz = (m2, b) ->
  cenv!id = Some ofs ->
  inject_incr f1 f2 ->
  f2 b = Some(sp, ofs) ->
  (forall b', b' <> b -> f2 b' = f1 b') ->
  e!id = None ->
  match_env f2 cenv (PTree.set id (b, sz) e) sp lo (Mem.nextblock m2).
Proof.
  intros until f2; intros ME ALLOC CENV INCR SAME OTHER ENV.
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK.
  exploit Mem.alloc_result; eauto. intros RES.
  inv ME; constructor.
(* vars *)
  intros. rewrite PTree.gsspec. destruct (peq id0 id).
  (* the new var *)
  subst id0. rewrite CENV. constructor. econstructor. eauto. 
  rewrite Int.add_commut; rewrite Int.add_zero; auto.
  (* old vars *)
  generalize (me_vars0 id0). rewrite PTree.gro; auto. intros M; inv M.
  constructor; eauto.
  constructor.
(* low-high *)
  rewrite NEXTBLOCK; omega.
(* bounded *)
  intros. rewrite PTree.gsspec in H. destruct (peq id0 id).
  inv H. rewrite NEXTBLOCK; omega.
  exploit me_bounded0; eauto. rewrite NEXTBLOCK; omega.
(* inv *)
  intros. destruct (zeq b (Mem.nextblock m1)).
  subst b. rewrite SAME in H; inv H. exists id; exists sz. apply PTree.gss. 
  rewrite OTHER in H; auto. exploit me_inv0; eauto. 
  intros [id1 [sz1 EQ]]. exists id1; exists sz1. rewrite PTree.gso; auto. congruence.
(* incr *)
  intros. rewrite OTHER in H. eauto. unfold block in *; omega.
Qed.

(** The sizes of blocks appearing in [e] are respected. *)

Definition match_bounds (e: Csharpminor.env) (m: mem) : Prop :=
  forall id b sz ofs p,
  PTree.get id e = Some(b, sz) -> Mem.perm m b ofs Max p -> 0 <= ofs < sz.

Lemma match_bounds_invariant:
  forall e m1 m2,
  match_bounds e m1 ->
  (forall id b sz ofs p,
   PTree.get id e = Some(b, sz) -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  match_bounds e m2.
Proof.
  intros; red; intros. eapply H; eauto. 
Qed.

(** ** Permissions on the Cminor stack block *)

(** The parts of the Cminor stack data block that are not images of
    C#minor local variable blocks remain freeable at all times. *)

Inductive is_reachable_from_env (f: meminj) (e: Csharpminor.env) (sp: block) (ofs: Z) : Prop :=
  | is_reachable_intro: forall id b sz delta,
      e!id = Some(b, sz) ->
      f b = Some(sp, delta) ->
      delta <= ofs < delta + sz ->
      is_reachable_from_env f e sp ofs.

Definition padding_freeable (f: meminj) (e: Csharpminor.env) (tm: mem) (sp: block) (sz: Z) : Prop :=
  forall ofs, 
  0 <= ofs < sz -> Mem.perm tm sp ofs Cur Freeable \/ is_reachable_from_env f e sp ofs.

Lemma padding_freeable_invariant:
  forall f1 e tm1 sp sz cenv lo hi f2 tm2,
  padding_freeable f1 e tm1 sp sz ->
  match_env f1 cenv e sp lo hi ->
  (forall ofs, Mem.perm tm1 sp ofs Cur Freeable -> Mem.perm tm2 sp ofs Cur Freeable) ->
  (forall b, b < hi -> f2 b = f1 b) ->
  padding_freeable f2 e tm2 sp sz.
Proof.
  intros; red; intros.
  exploit H; eauto. intros [A | A].
  left; auto.
  right. inv A. exploit me_bounded; eauto. intros [D E].
  econstructor; eauto. rewrite H2; auto. 
Qed.

(** Decidability of the [is_reachable_from_env] predicate. *)

Lemma is_reachable_from_env_dec:
  forall f e sp ofs, is_reachable_from_env f e sp ofs \/ ~is_reachable_from_env f e sp ofs.
Proof.
  intros. 
  set (pred := fun id_b_sz : ident * (block * Z) =>
                 match id_b_sz with
                 | (id, (b, sz)) =>
                      match f b with
                           | None => false
                           | Some(sp', delta) =>
                               if eq_block sp sp'
                               then zle delta ofs && zlt ofs (delta + sz)
                               else false
                      end
                 end).
  destruct (List.existsb pred (PTree.elements e)) eqn:?.
  (* yes *)
  rewrite List.existsb_exists in Heqb. 
  destruct Heqb as [[id [b sz]] [A B]].
  simpl in B. destruct (f b) as [[sp' delta] |] eqn:?; try discriminate.
  destruct (eq_block sp sp'); try discriminate.
  destruct (andb_prop _ _ B).
  left. apply is_reachable_intro with id b sz delta.
  apply PTree.elements_complete; auto. 
  congruence.
  split; eapply proj_sumbool_true; eauto.
  (* no *)
  right; red; intro NE; inv NE. 
  assert (existsb pred (PTree.elements e) = true).
  rewrite List.existsb_exists. exists (id, (b, sz)); split.
  apply PTree.elements_correct; auto. 
  simpl. rewrite H0. rewrite dec_eq_true.
  unfold proj_sumbool. destruct H1. rewrite zle_true; auto. rewrite zlt_true; auto. 
  congruence.
Qed.

(** * Correspondence between global environments *)

(** Global environments match if the memory injection [f] leaves unchanged
  the references to global symbols and functions. *)

Inductive match_globalenvs (f: meminj) (bound: Z): Prop :=
  | mk_match_globalenvs
      (POS: bound > 0)
      (DOMAIN: forall b, b < bound -> f b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, f b1 = Some(b2, delta) -> b2 < bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> b < bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> b < bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> b < bound).

Remark inj_preserves_globals:
  forall f hi,
  match_globalenvs f hi ->
  meminj_preserves_globals ge f.
Proof.
  intros. inv H.
  split. intros. apply DOMAIN. eapply SYMBOLS. eauto.
  split. intros. apply DOMAIN. eapply VARINFOS. eauto. 
  intros. symmetry. eapply IMAGE; eauto. 
Qed.

(** * Invariant on abstract call stacks  *)

(** Call stacks represent abstractly the execution state of the current
  C#minor and Cminor functions, as well as the states of the
  calling functions.  A call stack is a list of frames, each frame
  collecting information on the current execution state of a C#minor
  function and its Cminor translation. *)

Inductive frame : Type :=
  Frame(cenv: compilenv)
       (tf: Cminor.function)
       (e: Csharpminor.env)
       (le: Csharpminor.temp_env)
       (te: Cminor.env)
       (sp: block)
       (lo hi: Z).

Definition callstack : Type := list frame.

(** Matching of call stacks imply:
- matching of environments for each of the frames
- matching of the global environments
- separation conditions over the memory blocks allocated for C#minor local variables;
- separation conditions over the memory blocks allocated for Cminor stack data;
- freeable permissions on the parts of the Cminor stack data blocks
  that are not images of C#minor local variable blocks.
*)

Inductive match_callstack (f: meminj) (m: mem) (tm: mem):
                          callstack -> Z -> Z -> Prop :=
  | mcs_nil:
      forall hi bound tbound,
      match_globalenvs f hi ->
      hi <= bound -> hi <= tbound ->
      match_callstack f m tm nil bound tbound 
  | mcs_cons:
      forall cenv tf e le te sp lo hi cs bound tbound
        (BOUND: hi <= bound)
        (TBOUND: sp < tbound)
        (MTMP: match_temps f le te)
        (MENV: match_env f cenv e sp lo hi)
        (BOUND: match_bounds e m)
        (PERM: padding_freeable f e tm sp tf.(fn_stackspace))
        (MCS: match_callstack f m tm cs lo sp),
      match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) bound tbound.

(** [match_callstack] implies [match_globalenvs]. *)

Lemma match_callstack_match_globalenvs:
  forall f m tm cs bound tbound,
  match_callstack f m tm cs bound tbound ->
  exists hi, match_globalenvs f hi.
Proof.
  induction 1; eauto.
Qed.

(** Invariance properties for [match_callstack]. *)

Lemma match_callstack_invariant:
  forall f1 m1 tm1 f2 m2 tm2 cs bound tbound,
  match_callstack f1 m1 tm1 cs bound tbound ->
  inject_incr f1 f2 ->
  (forall b ofs p, b < bound -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  (forall sp ofs, sp < tbound -> Mem.perm tm1 sp ofs Cur Freeable -> Mem.perm tm2 sp ofs Cur Freeable) ->
  (forall b, b < bound -> f2 b = f1 b) ->
  (forall b b' delta, f2 b = Some(b', delta) -> b' < tbound -> f1 b = Some(b', delta)) ->
  match_callstack f2 m2 tm2 cs bound tbound.
Proof.
  induction 1; intros.
  (* base case *)
  econstructor; eauto.
  inv H. constructor; intros; eauto.
  eapply IMAGE; eauto. eapply H6; eauto. omega.
  (* inductive case *)
  assert (lo <= hi) by (eapply me_low_high; eauto).
  econstructor; eauto.
  eapply match_temps_invariant; eauto.
  eapply match_env_invariant; eauto. 
    intros. apply H3. omega.
  eapply match_bounds_invariant; eauto.
    intros. eapply H1; eauto. 
    exploit me_bounded; eauto. omega. 
  eapply padding_freeable_invariant; eauto. 
    intros. apply H3. omega. 
  eapply IHmatch_callstack; eauto. 
    intros. eapply H1; eauto. omega. 
    intros. eapply H2; eauto. omega. 
    intros. eapply H3; eauto. omega.
    intros. eapply H4; eauto. omega.
Qed.

Lemma match_callstack_incr_bound:
  forall f m tm cs bound tbound bound' tbound',
  match_callstack f m tm cs bound tbound ->
  bound <= bound' -> tbound <= tbound' ->
  match_callstack f m tm cs bound' tbound'.
Proof.
  intros. inv H.
  econstructor; eauto. omega. omega. 
  constructor; auto. omega. omega.
Qed.

(** Assigning a temporary variable. *)

Lemma match_callstack_set_temp:
  forall f cenv e le te sp lo hi cs bound tbound m tm tf id v tv,
  val_inject f v tv ->
  match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) bound tbound ->
  match_callstack f m tm (Frame cenv tf e (PTree.set id v le) (PTree.set id tv te) sp lo hi :: cs) bound tbound.
Proof.
  intros. inv H0. constructor; auto.
  eapply match_temps_assign; eauto. 
Qed.

(** Preservation of [match_callstack] by freeing all blocks allocated
  for local variables at function entry (on the C#minor side)
  and simultaneously freeing the Cminor stack data block. *)

Lemma in_blocks_of_env:
  forall e id b sz,
  e!id = Some(b, sz) -> In (b, 0, sz) (blocks_of_env e).
Proof.
  unfold blocks_of_env; intros. 
  change (b, 0, sz) with (block_of_binding (id, (b, sz))).
  apply List.in_map. apply PTree.elements_correct. auto.
Qed.

Lemma in_blocks_of_env_inv:
  forall b lo hi e,
  In (b, lo, hi) (blocks_of_env e) ->
  exists id, e!id = Some(b, hi) /\ lo = 0.
Proof.
  unfold blocks_of_env; intros. 
  exploit list_in_map_inv; eauto. intros [[id [b' sz]] [A B]].
  unfold block_of_binding in A. inv A. 
  exists id; intuition. apply PTree.elements_complete. auto.
Qed.

Lemma match_callstack_freelist:
  forall f cenv tf e le te sp lo hi cs m m' tm,
  Mem.inject f m tm ->
  Mem.free_list m (blocks_of_env e) = Some m' ->
  match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  exists tm',
  Mem.free tm sp 0 tf.(fn_stackspace) = Some tm'
  /\ match_callstack f m' tm' cs (Mem.nextblock m') (Mem.nextblock tm')
  /\ Mem.inject f m' tm'.
Proof.
  intros until tm; intros INJ FREELIST MCS. inv MCS. inv MENV.
  assert ({tm' | Mem.free tm sp 0 (fn_stackspace tf) = Some tm'}).
  apply Mem.range_perm_free.
  red; intros.
  exploit PERM; eauto. intros [A | A].
  auto.
  inv A. assert (Mem.range_perm m b 0 sz Cur Freeable). 
  eapply free_list_freeable; eauto. eapply in_blocks_of_env; eauto.
  replace ofs with ((ofs - delta) + delta) by omega. 
  eapply Mem.perm_inject; eauto. apply H3. omega. 
  destruct X as  [tm' FREE].
  exploit nextblock_freelist; eauto. intro NEXT.
  exploit Mem.nextblock_free; eauto. intro NEXT'.
  exists tm'. split. auto. split.
  rewrite NEXT; rewrite NEXT'.
  apply match_callstack_incr_bound with lo sp; try omega.
  apply match_callstack_invariant with f m tm; auto.
  intros. eapply perm_freelist; eauto.
  intros. eapply Mem.perm_free_1; eauto. left; unfold block; omega.
  eapply Mem.free_inject; eauto.
  intros. exploit me_inv0; eauto. intros [id [sz A]]. 
  exists 0; exists sz; split.
  eapply in_blocks_of_env; eauto.
  eapply BOUND0; eauto. eapply Mem.perm_max. eauto. 
Qed.

(** Preservation of [match_callstack] by external calls. *)

Lemma match_callstack_external_call:
  forall f1 f2 m1 m2 m1' m2',
  mem_unchanged_on (loc_unmapped f1) m1 m2 ->
  mem_unchanged_on (loc_out_of_reach f1 m1) m1' m2' ->
  inject_incr f1 f2 ->
  inject_separated f1 f2 m1 m1' ->
  (forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  forall cs bound tbound,
  match_callstack f1 m1 m1' cs bound tbound ->
  bound <= Mem.nextblock m1 -> tbound <= Mem.nextblock m1' ->
  match_callstack f2 m2 m2' cs bound tbound.
Proof.
  intros until m2'. 
  intros UNMAPPED OUTOFREACH INCR SEPARATED MAXPERMS.
  destruct OUTOFREACH as [OUTOFREACH1 OUTOFREACH2].
  induction 1; intros.
(* base case *)
  apply mcs_nil with hi; auto.
  inv H. constructor; auto.
  intros. case_eq (f1 b1). 
  intros [b2' delta'] EQ. rewrite (INCR _ _ _ EQ) in H. inv H. eauto. 
  intro EQ. exploit SEPARATED; eauto. intros [A B]. elim B. red. omega. 
(* inductive case *)
  constructor. auto. auto. 
  eapply match_temps_invariant; eauto.
  eapply match_env_invariant; eauto. 
  red in SEPARATED. intros. destruct (f1 b) as [[b' delta']|] eqn:?. 
  exploit INCR; eauto. congruence.
  exploit SEPARATED; eauto. intros [A B]. elim B. red. omega. 
  intros. assert (lo <= hi) by (eapply me_low_high; eauto).
  destruct (f1 b) as [[b' delta']|] eqn:?. 
  apply INCR; auto. 
  destruct (f2 b) as [[b' delta']|] eqn:?; auto.
  exploit SEPARATED; eauto. intros [A B]. elim A. red. omega.
  eapply match_bounds_invariant; eauto. 
  intros. eapply MAXPERMS; eauto. red. exploit me_bounded; eauto. omega. 
  (* padding-freeable *)
  red; intros.
  destruct (is_reachable_from_env_dec f1 e sp ofs).
  inv H3. right. apply is_reachable_intro with id b sz delta; auto. 
  exploit PERM; eauto. intros [A|A]; try contradiction.
  left. apply OUTOFREACH1; auto. red; intros.
  red; intros; elim H3.
  exploit me_inv; eauto. intros [id [lv B]].
  exploit BOUND0; eauto. intros C.
  apply is_reachable_intro with id b0 lv delta; auto; omega.
  (* induction *)
  eapply IHmatch_callstack; eauto. inv MENV; omega. omega.
Qed.

(** [match_callstack] and allocations *)

Lemma match_callstack_alloc_right:
  forall f m tm cs tf tm' sp le te cenv,
  match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm', sp) ->
  Mem.inject f m tm ->
  match_temps f le te ->
  (forall id, cenv!id = None) ->
  match_callstack f m tm'
      (Frame cenv tf empty_env le te sp (Mem.nextblock m) (Mem.nextblock m) :: cs)
      (Mem.nextblock m) (Mem.nextblock tm').
Proof.
  intros.
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK.
  exploit Mem.alloc_result; eauto. intros RES.
  constructor.
  omega.
  unfold block in *; omega.
  auto.
  constructor; intros.
    rewrite H3. rewrite PTree.gempty. constructor.
    omega.
    rewrite PTree.gempty in H4; discriminate.
    eelim Mem.fresh_block_alloc; eauto. eapply Mem.valid_block_inject_2; eauto.
    rewrite RES. change (Mem.valid_block tm tb). eapply Mem.valid_block_inject_2; eauto. 
  red; intros. rewrite PTree.gempty in H4. discriminate.
  red; intros. left. eapply Mem.perm_alloc_2; eauto. 
  eapply match_callstack_invariant with (tm1 := tm); eauto. 
  rewrite RES; auto.
  intros. eapply Mem.perm_alloc_1; eauto.
Qed.

Lemma match_callstack_alloc_left:
  forall f1 m1 tm id cenv tf e le te sp lo cs sz m2 b f2 ofs,
  match_callstack f1 m1 tm
    (Frame (PTree.remove id cenv) tf e le te sp lo (Mem.nextblock m1) :: cs)
    (Mem.nextblock m1) (Mem.nextblock tm) ->
  Mem.alloc m1 0 sz = (m2, b) ->
  cenv!id = Some ofs ->
  inject_incr f1 f2 ->
  f2 b = Some(sp, ofs) ->
  (forall b', b' <> b -> f2 b' = f1 b') ->
  e!id = None ->
  match_callstack f2 m2 tm
    (Frame cenv tf (PTree.set id (b, sz) e) le te sp lo (Mem.nextblock m2) :: cs)
    (Mem.nextblock m2) (Mem.nextblock tm).
Proof.
  intros. inv H. 
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK.
  exploit Mem.alloc_result; eauto. intros RES.
  assert (LO: lo <= Mem.nextblock m1) by (eapply me_low_high; eauto). 
  constructor.
  omega.
  auto.
  eapply match_temps_invariant; eauto.
  eapply match_env_alloc; eauto.
  red; intros. rewrite PTree.gsspec in H. destruct (peq id0 id).
  inversion H. subst b0 sz0 id0. eapply Mem.perm_alloc_3; eauto.
  eapply BOUND0; eauto. eapply Mem.perm_alloc_4; eauto. 
  exploit me_bounded; eauto. unfold block in *; omega.
  red; intros. exploit PERM; eauto. intros [A|A]. auto. right. 
  inv A. apply is_reachable_intro with id0 b0 sz0 delta; auto.
  rewrite PTree.gso. auto. congruence.
  eapply match_callstack_invariant with (m1 := m1); eauto. 
  intros. eapply Mem.perm_alloc_4; eauto.
  unfold block in *; omega.
  intros. apply H4. unfold block in *; omega.
  intros. destruct (zeq b0 b). 
  subst b0. rewrite H3 in H. inv H. omegaContradiction. 
  rewrite H4 in H; auto.
Qed.

(** * Correctness of stack allocation of local variables *)

(** This section shows the correctness of the translation of Csharpminor
  local variables as sub-blocks of the Cminor stack data.  This is the most difficult part of the proof. *)

Definition cenv_remove (cenv: compilenv) (vars: list (ident * Z)) : compilenv :=
  fold_right (fun id_lv ce => PTree.remove (fst id_lv) ce) cenv vars.

Remark cenv_remove_gso:
  forall id vars cenv,
  ~In id (map fst vars) ->
  PTree.get id (cenv_remove cenv vars) = PTree.get id cenv.
Proof.
  induction vars; simpl; intros.
  auto.
  rewrite PTree.gro. apply IHvars. intuition. intuition. 
Qed. 

Remark cenv_remove_gss:
  forall id vars cenv,
  In id (map fst vars) ->
  PTree.get id (cenv_remove cenv vars) = None.
Proof.
  induction vars; simpl; intros.
  contradiction.
  rewrite PTree.grspec. destruct (PTree.elt_eq id (fst a)). auto.
  destruct H. intuition. eauto.
Qed.

Definition cenv_compat (cenv: compilenv) (vars: list (ident * Z)) (tsz: Z) : Prop :=
  forall id sz,
  In (id, sz) vars ->
  exists ofs, 
      PTree.get id cenv = Some ofs 
   /\ Mem.inj_offset_aligned ofs sz
   /\ 0 <= ofs
   /\ ofs + Zmax 0 sz <= tsz.

Definition cenv_separated (cenv: compilenv) (vars: list (ident * Z)) : Prop :=
  forall id1 sz1 ofs1 id2 sz2 ofs2,
  In (id1, sz1) vars -> In (id2, sz2) vars ->
  PTree.get id1 cenv = Some ofs1 -> PTree.get id2 cenv = Some ofs2 ->
  id1 <> id2 ->
  ofs1 + sz1 <= ofs2 \/ ofs2 + sz2 <= ofs1.

Definition cenv_mem_separated (cenv: compilenv) (vars: list (ident * Z)) (f: meminj) (sp: block) (m: mem) : Prop :=
  forall id sz ofs b delta ofs' k p,
  In (id, sz) vars -> PTree.get id cenv = Some ofs ->
  f b = Some (sp, delta) -> 
  Mem.perm m b ofs' k p ->
  ofs <= ofs' + delta < sz + ofs -> False.

Lemma match_callstack_alloc_variables_rec:
  forall tm sp tf cenv le te lo cs,
  Mem.valid_block tm sp ->
  fn_stackspace tf <= Int.max_unsigned ->
  (forall ofs k p, Mem.perm tm sp ofs k p -> 0 <= ofs < fn_stackspace tf) ->
  (forall ofs k p, 0 <= ofs < fn_stackspace tf -> Mem.perm tm sp ofs k p) ->
  forall e1 m1 vars e2 m2,
  alloc_variables e1 m1 vars e2 m2 ->
  forall f1,
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace tf) ->
  cenv_separated cenv vars ->
  cenv_mem_separated cenv vars f1 sp m1 ->
  (forall id sz, In (id, sz) vars -> e1!id = None) ->
  match_callstack f1 m1 tm
    (Frame (cenv_remove cenv vars) tf e1 le te sp lo (Mem.nextblock m1) :: cs)
    (Mem.nextblock m1) (Mem.nextblock tm) ->
  Mem.inject f1 m1 tm ->
  exists f2,
    match_callstack f2 m2 tm
      (Frame cenv tf e2 le te sp lo (Mem.nextblock m2) :: cs)
      (Mem.nextblock m2) (Mem.nextblock tm)
  /\ Mem.inject f2 m2 tm.
Proof.
  intros until cs; intros VALID REPRES STKSIZE STKPERMS.
  induction 1; intros f1 NOREPET COMPAT SEP1 SEP2 UNBOUND MCS MINJ.
  (* base case *)
  simpl in MCS. exists f1; auto. 
  (* inductive case *)
  simpl in NOREPET. inv NOREPET.
(* exploit Mem.alloc_result; eauto. intros RES.
  exploit Mem.nextblock_alloc; eauto. intros NB.*)
  exploit (COMPAT id sz). auto with coqlib. intros [ofs [CENV [ALIGNED [LOB HIB]]]].
  exploit Mem.alloc_left_mapped_inject. 
    eexact MINJ.
    eexact H.
    eexact VALID.
    instantiate (1 := ofs). zify. omega. 
    intros. exploit STKSIZE; eauto. omega. 
    intros. apply STKPERMS. zify. omega.
    replace (sz - 0) with sz by omega. auto.
    intros. eapply SEP2. eauto with coqlib. eexact CENV. eauto. eauto. omega. 
  intros [f2 [A [B [C D]]]].
  exploit (IHalloc_variables f2); eauto.
    red; intros. eapply COMPAT. auto with coqlib.
    red; intros. eapply SEP1; eauto with coqlib.
    red; intros. exploit Mem.perm_alloc_inv; eauto. destruct (zeq b b1); intros P.
    subst b. rewrite C in H5; inv H5. 
    exploit SEP1. eapply in_eq. eapply in_cons; eauto. eauto. eauto. 
    red; intros; subst id0. elim H3. change id with (fst (id, sz0)). apply in_map; auto. 
    omega.
    eapply SEP2. apply in_cons; eauto. eauto. 
    rewrite D in H5; eauto. eauto. auto. 
    intros. rewrite PTree.gso. eapply UNBOUND; eauto with coqlib. 
    red; intros; subst id0. elim H3. change id with (fst (id, sz0)). apply in_map; auto.
    eapply match_callstack_alloc_left; eauto. 
    rewrite cenv_remove_gso; auto. 
    apply UNBOUND with sz; auto with coqlib.
Qed.

Lemma match_callstack_alloc_variables:
  forall tm1 sp tm2 m1 vars e m2 cenv f1 cs fn le te,
  Mem.alloc tm1 0 (fn_stackspace fn) = (tm2, sp) ->
  fn_stackspace fn <= Int.max_unsigned ->
  alloc_variables empty_env m1 vars e m2 ->
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace fn) ->
  cenv_separated cenv vars ->
  (forall id ofs, cenv!id = Some ofs -> In id (map fst vars)) ->
  Mem.inject f1 m1 tm1 ->
  match_callstack f1 m1 tm1 cs (Mem.nextblock m1) (Mem.nextblock tm1) ->
  match_temps f1 le te ->
  exists f2,
    match_callstack f2 m2 tm2 (Frame cenv fn e le te sp (Mem.nextblock m1) (Mem.nextblock m2) :: cs)
                    (Mem.nextblock m2) (Mem.nextblock tm2)
  /\ Mem.inject f2 m2 tm2.
Proof.
  intros.
  eapply match_callstack_alloc_variables_rec; eauto.
  eapply Mem.valid_new_block; eauto.
  intros. eapply Mem.perm_alloc_3; eauto.
  intros. apply Mem.perm_implies with Freeable; auto with mem. eapply Mem.perm_alloc_2; eauto.
  instantiate (1 := f1). red; intros. eelim Mem.fresh_block_alloc; eauto.
  eapply Mem.valid_block_inject_2; eauto. 
  intros. apply PTree.gempty.
  eapply match_callstack_alloc_right; eauto. 
  intros. destruct (In_dec peq id (map fst vars)).
  apply cenv_remove_gss; auto.
  rewrite cenv_remove_gso; auto.
  destruct (cenv!id) as [ofs|] eqn:?; auto. elim n; eauto. 
  eapply Mem.alloc_right_inject; eauto. 
Qed.

(** Properties of the compilation environment produced by [build_compilenv] *)

Remark block_alignment_pos:
  forall sz, block_alignment sz > 0.
Proof.
  unfold block_alignment; intros. 
  destruct (zlt sz 2). omega. 
  destruct (zlt sz 4). omega.
  destruct (zlt sz 8); omega.
Qed.

Remark assign_variable_incr:
  forall id sz cenv stksz cenv' stksz',
  assign_variable (cenv, stksz) (id, sz) = (cenv', stksz') -> stksz <= stksz'.
Proof.
  simpl; intros. inv H. 
  generalize (align_le stksz (block_alignment sz) (block_alignment_pos sz)).
  assert (0 <= Zmax 0 sz). apply Zmax_bound_l. omega.
  omega.
Qed.

Remark assign_variables_incr:
  forall vars cenv sz cenv' sz',
  assign_variables (cenv, sz) vars = (cenv', sz') -> sz <= sz'.
Proof.
  induction vars; intros until sz'.
  simpl; intros. inv H. omega.
Opaque assign_variable.
  destruct a as [id s]. simpl. intros.
  destruct (assign_variable (cenv, sz) (id, s)) as [cenv1 sz1] eqn:?. 
  apply Zle_trans with sz1. eapply assign_variable_incr; eauto. eauto.
Transparent assign_variable.
Qed.

Remark inj_offset_aligned_block:
  forall stacksize sz,
  Mem.inj_offset_aligned (align stacksize (block_alignment sz)) sz.
Proof.
  intros; red; intros.
  apply Zdivides_trans with (block_alignment sz).
  unfold align_chunk.  unfold block_alignment.
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
  apply align_divides. apply block_alignment_pos.
Qed.

Remark inj_offset_aligned_block':
  forall stacksize sz,
  Mem.inj_offset_aligned (align stacksize (block_alignment sz)) (Zmax 0 sz).
Proof.
  intros. 
  replace (block_alignment sz) with (block_alignment (Zmax 0 sz)).
  apply inj_offset_aligned_block. 
  rewrite Zmax_spec. destruct (zlt sz 0); auto.
  transitivity 1. reflexivity. unfold block_alignment. rewrite zlt_true. auto. omega.
Qed.

Lemma assign_variable_sound:
  forall cenv1 sz1 id sz cenv2 sz2 vars,
  assign_variable (cenv1, sz1) (id, sz) = (cenv2, sz2) ->
  ~In id (map fst vars) ->
  0 <= sz1 ->
  cenv_compat cenv1 vars sz1 ->
  cenv_separated cenv1 vars ->
  cenv_compat cenv2 (vars ++ (id, sz) :: nil) sz2
  /\ cenv_separated cenv2 (vars ++ (id, sz) :: nil).
Proof.
  unfold assign_variable; intros until vars; intros ASV NOREPET POS COMPAT SEP.
  inv ASV.
  assert (LE: sz1 <= align sz1 (block_alignment sz)). apply align_le. apply block_alignment_pos.
  assert (EITHER: forall id' sz',
             In (id', sz') (vars ++ (id, sz) :: nil) ->
             In (id', sz') vars /\ id' <> id \/ (id', sz') = (id, sz)).
    intros. rewrite in_app in H. destruct H. 
    left; split; auto. red; intros; subst id'. elim NOREPET. 
    change id with (fst (id, sz')). apply in_map; auto.
    simpl in H. destruct H. auto. contradiction.
  split; red; intros.
  apply EITHER in H. destruct H as [[P Q] | P].
  exploit COMPAT; eauto. intros [ofs [A [B [C D]]]]. 
  exists ofs.
  split. rewrite PTree.gso; auto.
  split. auto. split. auto. zify; omega. 
  inv P. exists (align sz1 (block_alignment sz)).
  split. apply PTree.gss.
  split. apply inj_offset_aligned_block.
  split. omega. 
  omega.
  apply EITHER in H; apply EITHER in H0.
  destruct H as [[P Q] | P]; destruct H0 as [[R S] | R].
  rewrite PTree.gso in *; auto. eapply SEP; eauto. 
  inv R. rewrite PTree.gso in H1; auto. rewrite PTree.gss in H2; inv H2.
  exploit COMPAT; eauto. intros [ofs [A [B [C D]]]]. 
  assert (ofs = ofs1) by congruence. subst ofs. 
  left. zify; omega. 
  inv P. rewrite PTree.gso in H2; auto. rewrite PTree.gss in H1; inv H1.
  exploit COMPAT; eauto. intros [ofs [A [B [C D]]]]. 
  assert (ofs = ofs2) by congruence. subst ofs. 
  right. zify; omega.
  congruence.
Qed.

Lemma assign_variables_sound:
  forall vars' cenv1 sz1 cenv2 sz2 vars,
  assign_variables (cenv1, sz1) vars' = (cenv2, sz2) ->
  list_norepet (map fst vars' ++ map fst vars) ->
  0 <= sz1 ->
  cenv_compat cenv1 vars sz1 ->
  cenv_separated cenv1 vars ->
  cenv_compat cenv2 (vars ++ vars') sz2 /\ cenv_separated cenv2 (vars ++ vars').
Proof.
  induction vars'; simpl; intros.
  rewrite app_nil_r. inv H; auto.
  destruct a as [id sz].
  simpl in H0. inv H0. rewrite in_app in H6.
  rewrite list_norepet_app in H7. destruct H7 as [P [Q R]].
  destruct (assign_variable (cenv1, sz1) (id, sz)) as [cenv' sz'] eqn:?.
  exploit assign_variable_sound.
    eauto.
    instantiate (1 := vars). tauto.
    auto. auto. auto.
  intros [A B].
  exploit IHvars'.
    eauto.
    instantiate (1 := vars ++ ((id, sz) :: nil)).
    rewrite list_norepet_app. split. auto. 
    split. rewrite map_app. apply list_norepet_append_commut. simpl. constructor; auto. 
    rewrite map_app. simpl. red; intros. rewrite in_app in H4. destruct H4. 
    eauto. simpl in H4. destruct H4. subst y. red; intros; subst x. tauto. tauto.
    generalize (assign_variable_incr _ _ _ _ _ _ Heqp). omega.
    auto. auto.
  rewrite app_ass. auto. 
Qed.

Remark permutation_norepet:
  forall (A: Type) (l l': list A), Permutation l l' -> list_norepet l -> list_norepet l'.
Proof.
  induction 1; intros.
  constructor.
  inv H0. constructor; auto. red; intros; elim H3. apply Permutation_in with l'; auto. apply Permutation_sym; auto.
  inv H. simpl in H2. inv H3. constructor. simpl; intuition. constructor. intuition. auto.
  eauto.
Qed.

Lemma build_compilenv_sound:
  forall f cenv sz,
  build_compilenv f = (cenv, sz) ->
  list_norepet (map fst (Csharpminor.fn_vars f)) ->
  cenv_compat cenv (Csharpminor.fn_vars f) sz /\ cenv_separated cenv (Csharpminor.fn_vars f).
Proof.
  unfold build_compilenv; intros. 
  set (vars1 := Csharpminor.fn_vars f) in *.
  generalize (VarSort.Permuted_sort vars1). intros P.
  set (vars2 := VarSort.sort vars1) in *.
  assert (cenv_compat cenv vars2 sz /\ cenv_separated cenv vars2).
    change vars2 with (nil ++ vars2).
    eapply assign_variables_sound.
    eexact H.
    simpl. rewrite app_nil_r. apply permutation_norepet with (map fst vars1); auto.
    apply Permutation_map. auto.
    omega. 
    red; intros. contradiction.
    red; intros. contradiction.
  destruct H1 as [A B]. split.
  red; intros. apply A. apply Permutation_in with vars1; auto. 
  red; intros. eapply B; eauto; apply Permutation_in with vars1; auto.
Qed.

Lemma assign_variables_domain:
  forall id vars cesz,
  (fst (assign_variables cesz vars))!id <> None ->
  (fst cesz)!id <> None \/ In id (map fst vars).
Proof.
  induction vars; simpl; intros.
  auto.
  exploit IHvars; eauto. unfold assign_variable. destruct a as [id1 sz1].
  destruct cesz as [cenv stksz]. simpl. 
  rewrite PTree.gsspec. destruct (peq id id1). auto. tauto.
Qed.

Lemma build_compilenv_domain:
  forall f cenv sz id ofs,
  build_compilenv f = (cenv, sz) ->
  cenv!id = Some ofs -> In id (map fst (Csharpminor.fn_vars f)).
Proof.
  unfold build_compilenv; intros. 
  set (vars1 := Csharpminor.fn_vars f) in *.
  generalize (VarSort.Permuted_sort vars1). intros P.
  set (vars2 := VarSort.sort vars1) in *.
  generalize (assign_variables_domain id vars2 (PTree.empty Z, 0)).
  rewrite H. simpl. intros. destruct H1. congruence. 
  rewrite PTree.gempty in H1. congruence.
  apply Permutation_in with (map fst vars2); auto.
  apply Permutation_map. apply Permutation_sym; auto.
Qed.

(** Initialization of C#minor temporaries and Cminor local variables. *)

Lemma create_undef_temps_val:
  forall id v temps, (create_undef_temps temps)!id = Some v -> In id temps /\ v = Vundef.
Proof.
  induction temps; simpl; intros.
  rewrite PTree.gempty in H. congruence.
  rewrite PTree.gsspec in H. destruct (peq id a).
  split. auto. congruence.
  exploit IHtemps; eauto. tauto. 
Qed.

Fixpoint set_params' (vl: list val) (il: list ident) (te: Cminor.env) : Cminor.env :=
  match il, vl with
  | i1 :: is, v1 :: vs => set_params' vs is (PTree.set i1 v1 te)
  | i1 :: is, nil => set_params' nil is (PTree.set i1 Vundef te)
  | _, _ => te
  end.

Lemma bind_parameters_agree_rec:
  forall f vars vals tvals le1 le2 te,
  bind_parameters vars vals le1 = Some le2 ->
  val_list_inject f vals tvals ->
  match_temps f le1 te ->
  match_temps f le2 (set_params' tvals vars te).
Proof.
Opaque PTree.set.
  induction vars; simpl; intros.
  destruct vals; try discriminate. inv H. auto. 
  destruct vals; try discriminate. inv H0.
  simpl. eapply IHvars; eauto.
  red; intros. rewrite PTree.gsspec in *. destruct (peq id a). 
  inv H0. exists v'; auto.
  apply H1; auto.
Qed.

Lemma set_params'_outside:
  forall id il vl te, ~In id il -> (set_params' vl il te)!id = te!id.
Proof.
  induction il; simpl; intros. auto. 
  destruct vl; rewrite IHil.
  apply PTree.gso. intuition. intuition.
  apply PTree.gso. intuition. intuition.
Qed.

Lemma set_params'_inside:
  forall id il vl te1 te2,
  In id il ->
  (set_params' vl il te1)!id = (set_params' vl il te2)!id.
Proof.
  induction il; simpl; intros.
  contradiction.
  destruct vl; destruct (List.in_dec peq id il); auto;
  repeat rewrite set_params'_outside; auto;
  assert (a = id) by intuition; subst a; repeat rewrite PTree.gss; auto.
Qed.

Lemma set_params_set_params':
  forall il vl id,
  list_norepet il ->
  (set_params vl il)!id = (set_params' vl il (PTree.empty val))!id.
Proof.
  induction il; simpl; intros.
  auto.
  inv H. destruct vl. 
  rewrite PTree.gsspec. destruct (peq id a). 
  subst a. rewrite set_params'_outside; auto. rewrite PTree.gss; auto.
  rewrite IHil; auto.
  destruct (List.in_dec peq id il). apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto. rewrite PTree.gso; auto. 
  rewrite PTree.gsspec. destruct (peq id a). 
  subst a. rewrite set_params'_outside; auto. rewrite PTree.gss; auto.
  rewrite IHil; auto.
  destruct (List.in_dec peq id il). apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto. rewrite PTree.gso; auto. 
Qed.

Lemma set_locals_outside:
  forall e id il,
  ~In id il -> (set_locals il e)!id = e!id.
Proof.
  induction il; simpl; intros.
  auto.
  rewrite PTree.gso. apply IHil. tauto. intuition. 
Qed.

Lemma set_locals_inside:
  forall e id il,
  In id il -> (set_locals il e)!id = Some Vundef.
Proof.
  induction il; simpl; intros.
  contradiction.
  destruct H. subst a. apply PTree.gss. 
  rewrite PTree.gsspec. destruct (peq id a). auto. auto. 
Qed.

Lemma set_locals_set_params':
  forall vars vals params id,
  list_norepet params ->
  list_disjoint params vars ->
  (set_locals vars (set_params vals params)) ! id =
  (set_params' vals params (set_locals vars (PTree.empty val))) ! id.
Proof.
  intros. destruct (in_dec peq id vars).
  assert (~In id params). apply list_disjoint_notin with vars; auto. apply list_disjoint_sym; auto.
  rewrite set_locals_inside; auto. rewrite set_params'_outside; auto. rewrite set_locals_inside; auto.
  rewrite set_locals_outside; auto. rewrite set_params_set_params'; auto. 
  destruct (in_dec peq id params). 
  apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto. 
  rewrite set_locals_outside; auto. 
Qed.

Lemma bind_parameters_agree:
  forall f params temps vals tvals le,
  bind_parameters params vals (create_undef_temps temps) = Some le ->
  val_list_inject f vals tvals ->
  list_norepet params ->
  list_disjoint params temps ->
  match_temps f le (set_locals temps (set_params tvals params)).
Proof.
  intros; red; intros.
  exploit bind_parameters_agree_rec; eauto.
  instantiate (1 := set_locals temps (PTree.empty val)).
  red; intros. exploit create_undef_temps_val; eauto. intros [A B]. subst v0.
  exists Vundef; split. apply set_locals_inside; auto. auto.
  intros [v' [A B]]. exists v'; split; auto.
  rewrite <- A. apply set_locals_set_params'; auto.
Qed.

(** The main result in this section. *)

Theorem match_callstack_function_entry:
  forall fn cenv tf m e m' tm tm' sp f cs args targs le,
  build_compilenv fn = (cenv, tf.(fn_stackspace)) ->
  tf.(fn_stackspace) <= Int.max_unsigned ->
  list_norepet (map fst (Csharpminor.fn_vars fn)) ->
  list_norepet (Csharpminor.fn_params fn) ->
  list_disjoint (Csharpminor.fn_params fn) (Csharpminor.fn_temps fn) ->
  alloc_variables Csharpminor.empty_env m (Csharpminor.fn_vars fn) e m' ->
  bind_parameters (Csharpminor.fn_params fn) args (create_undef_temps fn.(fn_temps)) = Some le ->
  val_list_inject f args targs ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm', sp) ->
  match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.inject f m tm ->
  let te := set_locals (Csharpminor.fn_temps fn) (set_params targs (Csharpminor.fn_params fn)) in
  exists f',
     match_callstack f' m' tm'
                     (Frame cenv tf e le te sp (Mem.nextblock m) (Mem.nextblock m') :: cs)
                     (Mem.nextblock m') (Mem.nextblock tm')
  /\ Mem.inject f' m' tm'.
Proof.
  intros.
  exploit build_compilenv_sound; eauto. intros [C1 C2].
  eapply match_callstack_alloc_variables; eauto.
  intros. eapply build_compilenv_domain; eauto.
  eapply bind_parameters_agree; eauto. 
Qed.

(** * Properties of compile-time approximations of values *)

Definition val_match_approx (a: approx) (v: val) : Prop :=
  match a with
  | Int1 => v = Val.zero_ext 1 v
  | Int7 => v = Val.zero_ext 8 v /\ v = Val.sign_ext 8 v
  | Int8u => v = Val.zero_ext 8 v
  | Int8s => v = Val.sign_ext 8 v
  | Int15 => v = Val.zero_ext 16 v /\ v = Val.sign_ext 16 v
  | Int16u => v = Val.zero_ext 16 v
  | Int16s => v = Val.sign_ext 16 v
  | Float32 => v = Val.singleoffloat v
  | Any => True
  end.

Remark undef_match_approx: forall a, val_match_approx a Vundef.
Proof.
  destruct a; simpl; auto.
Qed.

Lemma val_match_approx_increasing:
  forall a1 a2 v,
  Approx.bge a1 a2 = true -> val_match_approx a2 v -> val_match_approx a1 v.
Proof.
  assert (A: forall v, v = Val.zero_ext 8 v -> v = Val.zero_ext 16 v).
    intros. rewrite H.
    destruct v; simpl; auto. decEq. symmetry. 
    apply Int.zero_ext_widen. omega. 
  assert (B: forall v, v = Val.sign_ext 8 v -> v = Val.sign_ext 16 v).
    intros. rewrite H.
    destruct v; simpl; auto. decEq. symmetry. 
    apply Int.sign_ext_widen. omega.
  assert (C: forall v, v = Val.zero_ext 8 v -> v = Val.sign_ext 16 v).
    intros. rewrite H.
    destruct v; simpl; auto. decEq. symmetry. 
    apply Int.sign_zero_ext_widen. omega.
  assert (D: forall v, v = Val.zero_ext 1 v -> v = Val.zero_ext 8 v).
    intros. rewrite H.
    destruct v; simpl; auto. decEq. symmetry. 
    apply Int.zero_ext_widen. omega. 
  assert (E: forall v, v = Val.zero_ext 1 v -> v = Val.sign_ext 8 v).
    intros. rewrite H.
    destruct v; simpl; auto. decEq. symmetry. 
    apply Int.sign_zero_ext_widen. omega.
  intros. 
  unfold Approx.bge in H; destruct a1; try discriminate; destruct a2; simpl in *; try discriminate; intuition.
Qed.

Lemma approx_of_int_sound:
  forall n, val_match_approx (Approx.of_int n) (Vint n).
Proof.
  unfold Approx.of_int; intros.
  destruct (Int.eq_dec n Int.zero); simpl. subst; auto. 
  destruct (Int.eq_dec n Int.one); simpl. subst; auto. 
  destruct (Int.eq_dec n (Int.zero_ext 7 n)). simpl.
    split.
    decEq. rewrite e. symmetry. apply Int.zero_ext_widen. omega.
    decEq. rewrite e. symmetry. apply Int.sign_zero_ext_widen. omega.
  destruct (Int.eq_dec n (Int.zero_ext 8 n)). simpl; congruence.
  destruct (Int.eq_dec n (Int.sign_ext 8 n)). simpl; congruence.
  destruct (Int.eq_dec n (Int.zero_ext 15 n)). simpl.
    split.
    decEq. rewrite e. symmetry. apply Int.zero_ext_widen. omega. 
    decEq. rewrite e. symmetry. apply Int.sign_zero_ext_widen. omega. 
  destruct (Int.eq_dec n (Int.zero_ext 16 n)). simpl; congruence.
  destruct (Int.eq_dec n (Int.sign_ext 16 n)). simpl; congruence.
  exact I.
Qed.

Lemma approx_of_float_sound:
  forall f, val_match_approx (Approx.of_float f) (Vfloat f).
Proof.
  unfold Approx.of_float; intros. 
  destruct (Float.eq_dec f (Float.singleoffloat f)); simpl; auto. congruence.
Qed.

Lemma approx_of_chunk_sound:
  forall chunk m b ofs v,
  Mem.load chunk m b ofs = Some v ->
  val_match_approx (Approx.of_chunk chunk) v.
Proof.
  intros. exploit Mem.load_cast; eauto. 
  destruct chunk; intros; simpl; auto.
Qed.

Lemma approx_of_unop_sound:
  forall op v1 v a1,
  eval_unop op v1 = Some v ->
  val_match_approx a1 v1 ->
  val_match_approx (Approx.unop op a1) v.
Proof.
  destruct op; simpl; intros; auto; inv H.
  destruct v1; simpl; auto. rewrite Int.zero_ext_idem; auto. omega. 
  destruct v1; simpl; auto. rewrite Int.sign_ext_idem; auto. omega. 
  destruct v1; simpl; auto. rewrite Int.zero_ext_idem; auto. omega. 
  destruct v1; simpl; auto. rewrite Int.sign_ext_idem; auto. omega. 
  destruct v1; simpl; auto. rewrite Float.singleoffloat_idem; auto.
Qed.

Lemma approx_bitwise_and_sound:
  forall a1 v1 a2 v2,
  val_match_approx a1 v1 -> val_match_approx a2 v2 ->
  val_match_approx (Approx.bitwise_and a1 a2) (Val.and v1 v2).
Proof.
  assert (X: forall v1 v2 N, 0 < N < Z_of_nat Int.wordsize ->
            v2 = Val.zero_ext N v2 ->
            Val.and v1 v2 = Val.zero_ext N (Val.and v1 v2)).
    intros. rewrite Val.zero_ext_and in *; auto. 
    rewrite Val.and_assoc. congruence. 
  assert (Y: forall v1 v2 N, 0 < N < Z_of_nat Int.wordsize ->
            v1 = Val.zero_ext N v1 ->
            Val.and v1 v2 = Val.zero_ext N (Val.and v1 v2)).
    intros. rewrite (Val.and_commut v1 v2). apply X; auto.
  assert (P: forall a v, val_match_approx a v -> Approx.bge Int8u a = true ->
               v = Val.zero_ext 8 v).
    intros. apply (val_match_approx_increasing Int8u a v); auto.
  assert (Q: forall a v, val_match_approx a v -> Approx.bge Int16u a = true ->
               v = Val.zero_ext 16 v).
    intros. apply (val_match_approx_increasing Int16u a v); auto.
  assert (R: forall a v, val_match_approx a v -> Approx.bge Int1 a = true ->
               v = Val.zero_ext 1 v).
    intros. apply (val_match_approx_increasing Int1 a v); auto.

  intros; unfold Approx.bitwise_and. 
  destruct (Approx.bge Int1 a1) eqn:?. simpl. apply Y; eauto. compute; auto.
  destruct (Approx.bge Int1 a2) eqn:?. simpl. apply X; eauto. compute; auto.
  destruct (Approx.bge Int8u a1) eqn:?. simpl. apply Y; eauto. compute; auto.
  destruct (Approx.bge Int8u a2) eqn:?. simpl. apply X; eauto. compute; auto.
  destruct (Approx.bge Int16u a1) eqn:?. simpl. apply Y; eauto. compute; auto.
  destruct (Approx.bge Int16u a2) eqn:?. simpl. apply X; eauto. compute; auto.
  simpl; auto. 
Qed.

Lemma approx_bitwise_or_sound:
  forall (sem_op: val -> val -> val) a1 v1 a2 v2,
  (forall a b c, sem_op (Val.and a (Vint c)) (Val.and b (Vint c)) =
                 Val.and (sem_op a b) (Vint c)) ->
  val_match_approx a1 v1 -> val_match_approx a2 v2 ->
  val_match_approx (Approx.bitwise_or a1 a2) (sem_op v1 v2).
Proof.
  intros.
  assert (X: forall v v' N, 0 < N < Z_of_nat Int.wordsize ->
            v = Val.zero_ext N v ->
            v' = Val.zero_ext N v' ->
            sem_op v v' = Val.zero_ext N (sem_op v v')).
    intros. rewrite Val.zero_ext_and in *; auto.
    rewrite H3; rewrite H4. rewrite H. rewrite Val.and_assoc.
    simpl. rewrite Int.and_idem. auto.

  unfold Approx.bitwise_or. 

  destruct (Approx.bge Int1 a1 && Approx.bge Int1 a2) eqn:?.
  destruct (andb_prop _ _ Heqb).
  simpl. apply X. compute; auto. 
  apply (val_match_approx_increasing Int1 a1 v1); auto.
  apply (val_match_approx_increasing Int1 a2 v2); auto.

  destruct (Approx.bge Int8u a1 && Approx.bge Int8u a2) eqn:?.
  destruct (andb_prop _ _ Heqb0).
  simpl. apply X. compute; auto. 
  apply (val_match_approx_increasing Int8u a1 v1); auto.
  apply (val_match_approx_increasing Int8u a2 v2); auto.

  destruct (Approx.bge Int16u a1 && Approx.bge Int16u a2) eqn:?.
  destruct (andb_prop _ _ Heqb1).
  simpl. apply X. compute; auto. 
  apply (val_match_approx_increasing Int16u a1 v1); auto.
  apply (val_match_approx_increasing Int16u a2 v2); auto.

  exact I.
Qed.

Lemma approx_of_binop_sound:
  forall op v1 a1 v2 a2 m v,
  eval_binop op v1 v2 m = Some v ->
  val_match_approx a1 v1 -> val_match_approx a2 v2 ->
  val_match_approx (Approx.binop op a1 a2) v.
Proof.
  assert (OB: forall ob, val_match_approx Int1 (Val.of_optbool ob)).
    destruct ob; simpl. destruct b; auto. auto.
  
  destruct op; intros; simpl Approx.binop; simpl in H; try (exact I); inv H.
  apply approx_bitwise_and_sound; auto.
  apply approx_bitwise_or_sound; auto.
    intros. destruct a; destruct b; simpl; auto.
    rewrite (Int.and_commut i c); rewrite (Int.and_commut i0 c). 
    rewrite <- Int.and_or_distrib. rewrite Int.and_commut. auto.
  apply approx_bitwise_or_sound; auto.
    intros. destruct a; destruct b; simpl; auto.
    rewrite (Int.and_commut i c); rewrite (Int.and_commut i0 c). 
    rewrite <- Int.and_xor_distrib. rewrite Int.and_commut. auto.
  apply OB.
  apply OB.
  apply OB.
Qed.

Lemma approx_unop_is_redundant_sound:
  forall op a v,
  Approx.unop_is_redundant op a = true ->
  val_match_approx a v ->
  eval_unop op v = Some v.
Proof.
  unfold Approx.unop_is_redundant; intros; destruct op; try discriminate.
(* cast8unsigned *)
  assert (V: val_match_approx Int8u v) by (eapply val_match_approx_increasing; eauto).
  simpl in *. congruence.
(* cast8signed *)
  assert (V: val_match_approx Int8s v) by (eapply val_match_approx_increasing; eauto).
  simpl in *. congruence.
(* cast16unsigned *)
  assert (V: val_match_approx Int16u v) by (eapply val_match_approx_increasing; eauto).
  simpl in *. congruence.
(* cast16signed *)
  assert (V: val_match_approx Int16s v) by (eapply val_match_approx_increasing; eauto).
  simpl in *. congruence.
(* singleoffloat *)
  assert (V: val_match_approx Float32 v) by (eapply val_match_approx_increasing; eauto).
  simpl in *. congruence.
Qed.

(** * Compatibility of evaluation functions with respect to memory injections. *)

Remark val_inject_val_of_bool:
  forall f b, val_inject f (Val.of_bool b) (Val.of_bool b).
Proof.
  intros; destruct b; constructor.
Qed.

Remark val_inject_val_of_optbool:
  forall f ob, val_inject f (Val.of_optbool ob) (Val.of_optbool ob).
Proof.
  intros; destruct ob; simpl. destruct b; constructor. constructor.
Qed.

Ltac TrivialExists :=
  match goal with
  | [ |- exists y, Some ?x = Some y /\ val_inject _ _ _ ] =>
      exists x; split; [auto | try(econstructor; eauto)]
  | [ |- exists y, _ /\ val_inject _ (Vint ?x) _ ] =>
      exists (Vint x); split; [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ val_inject _ (Vfloat ?x) _ ] =>
      exists (Vfloat x); split; [eauto with evalexpr | constructor]
  | _ => idtac
  end.

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
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.intoffloat f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.intuoffloat f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
Qed.

(** Compatibility of [eval_binop] with respect to [val_inject]. *)

Lemma eval_binop_compat:
  forall f op v1 tv1 v2 tv2 v m tm,
  eval_binop op v1 v2 m = Some v ->
  val_inject f v1 tv1 ->
  val_inject f v2 tv2 ->
  Mem.inject f m tm ->
  exists tv,
     eval_binop op tv1 tv2 tm = Some tv
  /\ val_inject f v tv.
Proof.
  destruct op; simpl; intros.
  inv H; inv H0; inv H1; TrivialExists.
    repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
    repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  inv H; inv H0; inv H1; TrivialExists.
    apply Int.sub_add_l.
    simpl. destruct (zeq b1 b0); auto.
    subst b1. rewrite H in H0; inv H0. 
    rewrite zeq_true. rewrite Int.sub_shifted. auto.
  inv H; inv H0; inv H1; TrivialExists.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *. 
    destruct (Int.eq i0 Int.zero
      || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H; TrivialExists.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *. 
    destruct (Int.eq i0 Int.zero); inv H. TrivialExists.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *. 
    destruct (Int.eq i0 Int.zero
      || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H; TrivialExists.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *. 
    destruct (Int.eq i0 Int.zero); inv H. TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists. simpl. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H; inv H0; inv H1; TrivialExists. simpl. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H; inv H0; inv H1; TrivialExists. simpl. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists. apply val_inject_val_of_optbool.
(* cmpu *)
  inv H; inv H0; inv H1; TrivialExists.
    apply val_inject_val_of_optbool.
    apply val_inject_val_of_optbool.
    apply val_inject_val_of_optbool.
Opaque Int.add.
    unfold Val.cmpu. simpl.
    destruct (zeq b1 b0); subst.
    (* same blocks *)
    rewrite H0 in H. inv H. rewrite zeq_true.
    fold (Mem.weak_valid_pointer m b0 (Int.unsigned ofs1)).
    fold (Mem.weak_valid_pointer m b0 (Int.unsigned ofs0)).
    fold (Mem.weak_valid_pointer tm b2 (Int.unsigned (Int.add ofs1 (Int.repr delta)))).
    fold (Mem.weak_valid_pointer tm b2 (Int.unsigned (Int.add ofs0 (Int.repr delta)))).
    destruct (Mem.weak_valid_pointer m b0 (Int.unsigned ofs1)) eqn:?; auto.
    destruct (Mem.weak_valid_pointer m b0 (Int.unsigned ofs0)) eqn:?; auto.
    rewrite (Mem.weak_valid_pointer_inject_val _ _ _ _ _ _ _ H2 Heqb) by eauto.
    rewrite (Mem.weak_valid_pointer_inject_val _ _ _ _ _ _ _ H2 Heqb0) by eauto.
    rewrite Int.translate_cmpu
      by eauto using Mem.weak_valid_pointer_inject_no_overflow.
    apply val_inject_val_of_optbool.
    (* different source blocks *)
    destruct (Mem.valid_pointer m b1 (Int.unsigned ofs1)) eqn:?; auto.
    destruct (Mem.valid_pointer m b0 (Int.unsigned ofs0)) eqn:?; auto.
    destruct (zeq b2 b3).
    fold (Mem.weak_valid_pointer tm b2 (Int.unsigned (Int.add ofs1 (Int.repr delta)))).
    fold (Mem.weak_valid_pointer tm b3 (Int.unsigned (Int.add ofs0 (Int.repr delta0)))).
    rewrite Mem.valid_pointer_implies
      by (eapply (Mem.valid_pointer_inject_val _ _ _ _ _ _ _ H2 Heqb); eauto).
    rewrite Mem.valid_pointer_implies
      by (eapply (Mem.valid_pointer_inject_val _ _ _ _ _ _ _ H2 Heqb0); eauto).
    exploit Mem.different_pointers_inject; eauto. intros [A|A]; [congruence |].
    destruct c; simpl; auto.
    rewrite Int.eq_false. constructor. congruence.
    rewrite Int.eq_false. constructor. congruence.
    rewrite (Mem.valid_pointer_inject_val _ _ _ _ _ _ _ H2 Heqb) by eauto.
    rewrite (Mem.valid_pointer_inject_val _ _ _ _ _ _ _ H2 Heqb0) by eauto.
    apply val_inject_val_of_optbool.
  (* cmpf *)
  inv H; inv H0; inv H1; TrivialExists. apply val_inject_val_of_optbool.
Qed.

(** * Correctness of Cminor construction functions *)

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

Inductive val_lessdef_upto (m: int): val -> val -> Prop :=
  | val_lessdef_upto_base:
      forall v1 v2, Val.lessdef v1 v2 -> val_lessdef_upto m v1 v2
  | val_lessdef_upto_int:
      forall n1 n2, Int.and n1 m = Int.and n2 m -> val_lessdef_upto m (Vint n1) (Vint n2).

Hint Resolve val_lessdef_upto_base.

Remark val_lessdef_upto_and:
  forall m v1 v2 p,
  val_lessdef_upto m v1 v2 -> Int.and p m = m ->
  val_lessdef_upto m (Val.and v1 (Vint p)) v2.
Proof.
  intros. inversion H; clear H.
  inversion H1. destruct v2; simpl; auto. 
  apply val_lessdef_upto_int. rewrite Int.and_assoc. congruence.
  simpl. auto. 
  simpl. apply val_lessdef_upto_int. rewrite Int.and_assoc. congruence. 
Qed.

Remark val_lessdef_upto_zero_ext:
  forall m v1 v2 p,
  val_lessdef_upto m v1 v2 -> Int.and (Int.repr (two_p p - 1)) m = m -> 0 < p < 32 ->
  val_lessdef_upto m (Val.zero_ext p v1) v2.
Proof.
  intros. inversion H; clear H.
  inversion H2. destruct v2; simpl; auto.
  apply val_lessdef_upto_int. rewrite Int.zero_ext_and; auto. 
  rewrite Int.and_assoc. rewrite H0. auto.
  omega.
  simpl; auto.
  simpl. apply val_lessdef_upto_int. rewrite Int.zero_ext_and; auto.
  rewrite Int.and_assoc. rewrite H0. auto. omega.
Qed.

Remark val_lessdef_upto_sign_ext:
  forall m v1 v2 p,
  val_lessdef_upto m v1 v2 -> Int.and (Int.repr (two_p p - 1)) m = m -> 0 < p < 32 ->
  val_lessdef_upto m (Val.sign_ext p v1) v2.
Proof.
  intros.
  assert (A: forall x, Int.and (Int.sign_ext p x) m = Int.and x m).
    intros. transitivity (Int.and (Int.zero_ext p (Int.sign_ext p x)) m).
    rewrite Int.zero_ext_and; auto. rewrite Int.and_assoc. congruence. omega.
    rewrite Int.zero_ext_sign_ext.
    rewrite Int.zero_ext_and; auto. rewrite Int.and_assoc. congruence. omega. omega.
  inversion H; clear H.
  inversion H2. destruct v2; simpl; auto.
  apply val_lessdef_upto_int. auto. 
  simpl; auto.
  simpl. apply val_lessdef_upto_int. rewrite A. auto. 
Qed.

Remark val_lessdef_upto_shru:
  forall m v1 v2 p,
  val_lessdef_upto (Int.shl m p) v1 v2 -> Int.shru (Int.shl m p) p = m ->
  val_lessdef_upto m (Val.shru v1 (Vint p)) (Val.shru v2 (Vint p)).
Proof.
  intros. inversion H; clear H.
  inversion H1; simpl; auto.
  simpl. destruct (Int.ltu p Int.iwordsize); auto. apply val_lessdef_upto_int.
  rewrite <- H0. repeat rewrite Int.and_shru. congruence.
Qed.

Remark val_lessdef_upto_shr:
  forall m v1 v2 p,
  val_lessdef_upto (Int.shl m p) v1 v2 -> Int.shru (Int.shl m p) p = m ->
  val_lessdef_upto m (Val.shr v1 (Vint p)) (Val.shr v2 (Vint p)).
Proof.
  intros. inversion H; clear H.
  inversion H1; simpl; auto.
  simpl. destruct (Int.ltu p Int.iwordsize); auto. apply val_lessdef_upto_int.
  repeat rewrite Int.shr_and_shru_and; auto.
  rewrite <- H0. repeat rewrite Int.and_shru. congruence.
Qed.

Lemma eval_uncast_int:
  forall m sp te tm a x,
  eval_expr tge sp te tm a x ->
  exists v, eval_expr tge sp te tm (uncast_int m a) v /\ val_lessdef_upto m x v.
Proof.
  assert (EQ: forall p q, Int.eq p q = true -> p = q).
    intros. generalize (Int.eq_spec p q). rewrite H; auto.   
  intros until a. functional induction (uncast_int m a); intros.
  (* cast8unsigned *)
  inv H. simpl in H4; inv H4. exploit IHe; eauto. intros [v [A B]].
  exists v; split; auto. apply val_lessdef_upto_zero_ext; auto. 
  compute; auto.
  exists x; auto. 
  (* cast8signed *)
  inv H. simpl in H4; inv H4. exploit IHe; eauto. intros [v [A B]].
  exists v; split; auto. apply val_lessdef_upto_sign_ext; auto. 
  compute; auto.
  exists x; auto. 
  (* cast16unsigned *)
  inv H. simpl in H4; inv H4. exploit IHe; eauto. intros [v [A B]].
  exists v; split; auto. apply val_lessdef_upto_zero_ext; auto. 
  compute; auto.
  exists x; auto. 
  (* cast16signed *)
  inv H. simpl in H4; inv H4. exploit IHe; eauto. intros [v [A B]].
  exists v; split; auto. apply val_lessdef_upto_sign_ext; auto. 
  compute; auto.
  exists x; auto. 
  (* and *)
  inv H. simpl in H6; inv H6. inv H5. simpl in H0. inv H0.
  exploit IHe; eauto. intros [v [A B]].
  exists v; split; auto. apply val_lessdef_upto_and; auto.
  exists x; auto.
  (* shru *)
  inv H. simpl in H6; inv H6. inv H5. simpl in H0. inv H0.
  exploit IHe; eauto. intros [v [A B]].
  exists (Val.shru v (Vint n)); split.
  econstructor. eauto. econstructor. simpl; reflexivity. auto. 
  apply val_lessdef_upto_shru; auto.
  exists x; auto.
  (* shr *)
  inv H. simpl in H6; inv H6. inv H5. simpl in H0. inv H0.
  exploit IHe; eauto. intros [v [A B]].
  exists (Val.shr v (Vint n)); split.
  econstructor. eauto. econstructor. simpl; reflexivity. auto. 
  apply val_lessdef_upto_shr; auto.
  exists x; auto.
  (* default *)
  exists x; split; auto.
Qed.

Inductive val_lessdef_upto_single: val -> val -> Prop :=
  | val_lessdef_upto_single_base:
      forall v1 v2, Val.lessdef v1 v2 -> val_lessdef_upto_single v1 v2
  | val_lessdef_upto_single_float:
      forall n1 n2, Float.singleoffloat n1 = Float.singleoffloat n2 -> val_lessdef_upto_single (Vfloat n1) (Vfloat n2).

Hint Resolve val_lessdef_upto_single_base.

Lemma eval_uncast_float32:
  forall sp te tm a x,
  eval_expr tge sp te tm a x ->
  exists v, eval_expr tge sp te tm (uncast_float32 a) v /\ val_lessdef_upto_single x v.
Proof.
  intros until a. functional induction (uncast_float32 a); intros.
  (* singleoffloat *)
  inv H. simpl in H4; inv H4. exploit IHe; eauto. intros [v [A B]].
  exists v; split; auto.
  inv B. inv H. destruct v; simpl; auto. 
  apply val_lessdef_upto_single_float. apply Float.singleoffloat_idem. 
  simpl; auto.
  apply val_lessdef_upto_single_float. rewrite H. apply Float.singleoffloat_idem.
  (* default *)
  exists x; auto.
Qed.

Inductive val_content_inject (f: meminj): memory_chunk -> val -> val -> Prop :=
  | val_content_inject_8_signed:
      forall n1 n2, Int.sign_ext 8 n1 = Int.sign_ext 8 n2 ->
      val_content_inject f Mint8signed (Vint n1) (Vint n2)
  | val_content_inject_8_unsigned:
      forall n1 n2, Int.zero_ext 8 n1 = Int.zero_ext 8 n2 ->
      val_content_inject f Mint8unsigned (Vint n1) (Vint n2)
  | val_content_inject_16_signed:
      forall n1 n2, Int.sign_ext 16 n1 = Int.sign_ext 16 n2 ->
      val_content_inject f Mint16signed (Vint n1) (Vint n2)
  | val_content_inject_16_unsigned:
      forall n1 n2, Int.zero_ext 16 n1 = Int.zero_ext 16 n2 ->
      val_content_inject f Mint16unsigned (Vint n1) (Vint n2)
  | val_content_inject_single:
      forall n1 n2, Float.singleoffloat n1 = Float.singleoffloat n2 ->
      val_content_inject f Mfloat32 (Vfloat n1) (Vfloat n2)
  | val_content_inject_base:
      forall chunk v1 v2, val_inject f v1 v2 ->
      val_content_inject f chunk v1 v2.

Hint Resolve val_content_inject_base.

Lemma eval_store_arg:
  forall f sp te tm a v va chunk,
  eval_expr tge sp te tm a va ->
  val_inject f v va ->
  exists vb,
     eval_expr tge sp te tm (store_arg chunk a) vb
  /\ val_content_inject f chunk v vb.
Proof.
  intros.
  assert (DFL: forall v', Val.lessdef va v' -> val_content_inject f chunk v v').
    intros. apply val_content_inject_base. inv H1. auto. inv H0. auto.
  destruct chunk; simpl.
  (* int8signed *)
  exploit (eval_uncast_int (Int.repr 255)); eauto. intros [v' [A B]].
  exists v'; split; auto.
  inv B; auto. inv H0; auto. constructor.
  apply Int.sign_ext_equal_if_zero_equal; auto. omega.
  repeat rewrite Int.zero_ext_and; auto. omega. omega.
  (* int8unsigned *)
  exploit (eval_uncast_int (Int.repr 255)); eauto. intros [v' [A B]].
  exists v'; split; auto.
  inv B; auto. inv H0; auto. constructor.
  repeat rewrite Int.zero_ext_and; auto. omega. omega.
  (* int16signed *)
  exploit (eval_uncast_int (Int.repr 65535)); eauto. intros [v' [A B]].
  exists v'; split; auto.
  inv B; auto. inv H0; auto. constructor.
  apply Int.sign_ext_equal_if_zero_equal; auto. omega.
  repeat rewrite Int.zero_ext_and; auto. omega. omega.
  (* int16unsigned *)
  exploit (eval_uncast_int (Int.repr 65535)); eauto. intros [v' [A B]].
  exists v'; split; auto.
  inv B; auto. inv H0; auto. constructor.
  repeat rewrite Int.zero_ext_and; auto. omega. omega.
  (* int32 *)
  exists va; auto.
  (* float32 *)
  exploit eval_uncast_float32; eauto. intros [v' [A B]].
  exists v'; split; auto.
  inv B; auto. inv H0; auto. constructor. auto.
  (* float64 *)
  exists va; auto.
  (* float64al32 *)
  exists va; auto.
Qed.

Lemma storev_mapped_content_inject:
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  Mem.inject f m1 m2 ->
  Mem.storev chunk m1 a1 v1 = Some n1 ->
  val_inject f a1 a2 ->
  val_content_inject f chunk v1 v2 ->
  exists n2,
    Mem.storev chunk m2 a2 v2 = Some n2 /\ Mem.inject f n1 n2.
Proof.
  intros.
  assert (forall v1',
    (forall b ofs, Mem.store chunk m1 b ofs v1 = Mem.store chunk m1 b ofs v1') ->
    Mem.storev chunk m1 a1 v1' = Some n1).
  intros. rewrite <- H0. destruct a1; simpl; auto. 
  inv H2; eapply Mem.storev_mapped_inject;
  try eapply H; try eapply H1; try apply H3; intros.
  rewrite <- Mem.store_int8_sign_ext. rewrite H4. apply Mem.store_int8_sign_ext.
  auto.
  rewrite <- Mem.store_int8_zero_ext. rewrite H4. apply Mem.store_int8_zero_ext.
  auto.
  rewrite <- Mem.store_int16_sign_ext. rewrite H4. apply Mem.store_int16_sign_ext.
  auto.
  rewrite <- Mem.store_int16_zero_ext. rewrite H4. apply Mem.store_int16_zero_ext.
  auto.
  rewrite <- Mem.store_float32_truncate. rewrite H4. apply Mem.store_float32_truncate.
  auto.
  eauto.
  auto.
Qed.

Lemma make_store_correct:
  forall f sp te tm addr tvaddr rhs tvrhs chunk m vaddr vrhs m' fn k,
  eval_expr tge sp te tm addr tvaddr ->
  eval_expr tge sp te tm rhs tvrhs ->
  Mem.storev chunk m vaddr vrhs = Some m' ->
  Mem.inject f m tm ->
  val_inject f vaddr tvaddr ->
  val_inject f vrhs tvrhs ->
  exists tm', exists tvrhs',
  step tge (State fn (make_store chunk addr rhs) k sp te tm)
        E0 (State fn Sskip k sp te tm')
  /\ Mem.storev chunk tm tvaddr tvrhs' = Some tm'
  /\ Mem.inject f m' tm'.
Proof.
  intros. unfold make_store.
  exploit eval_store_arg. eexact H0. eauto. 
  intros [tv [EVAL VCINJ]].
  exploit storev_mapped_content_inject; eauto.
  intros [tm' [STORE MEMINJ]].
  exists tm'; exists tv.
  split. eapply step_store; eauto.
  auto.
Qed.

(** Correctness of [make_unop]. *)

Lemma eval_make_unop:
  forall sp te tm a v op v',
  eval_expr tge sp te tm a v ->
  eval_unop op v = Some v' ->
  exists v'', eval_expr tge sp te tm (make_unop op a) v'' /\ Val.lessdef v' v''.
Proof.
  intros; unfold make_unop. 
  assert (DFL: exists v'', eval_expr tge sp te tm (Eunop op a) v'' /\ Val.lessdef v' v'').
    exists v'; split. econstructor; eauto. auto.
  destruct op; auto; simpl in H0; inv H0.
(* cast8unsigned *)
  exploit (eval_uncast_int (Int.repr 255)); eauto. intros [v1 [A B]].
  exists (Val.zero_ext 8 v1); split. econstructor; eauto. 
  inv B. apply Val.zero_ext_lessdef; auto. simpl.
  repeat rewrite Int.zero_ext_and; auto.
  change (two_p 8 - 1) with 255. rewrite H0. auto.
  omega. omega.
(* cast8signed *)
  exploit (eval_uncast_int (Int.repr 255)); eauto. intros [v1 [A B]].
  exists (Val.sign_ext 8 v1); split. econstructor; eauto. 
  inv B. apply Val.sign_ext_lessdef; auto. simpl.
  replace (Int.sign_ext 8 n2) with (Int.sign_ext 8 n1). auto.
  apply Int.sign_ext_equal_if_zero_equal; auto. omega.
  repeat rewrite Int.zero_ext_and; auto. omega. omega.
(* cast16unsigned *)
  exploit (eval_uncast_int (Int.repr 65535)); eauto. intros [v1 [A B]].
  exists (Val.zero_ext 16 v1); split. econstructor; eauto. 
  inv B. apply Val.zero_ext_lessdef; auto. simpl.
  repeat rewrite Int.zero_ext_and; auto.
  change (two_p 16 - 1) with 65535. rewrite H0. auto.
  omega. omega.
(* cast16signed *)
  exploit (eval_uncast_int (Int.repr 65535)); eauto. intros [v1 [A B]].
  exists (Val.sign_ext 16 v1); split. econstructor; eauto. 
  inv B. apply Val.sign_ext_lessdef; auto. simpl.
  replace (Int.sign_ext 16 n2) with (Int.sign_ext 16 n1). auto.
  apply Int.sign_ext_equal_if_zero_equal; auto. omega.
  repeat rewrite Int.zero_ext_and; auto. omega. omega.
(* singleoffloat *)
  exploit eval_uncast_float32; eauto. intros [v1 [A B]].
  exists (Val.singleoffloat v1); split. econstructor; eauto. 
  inv B. apply Val.singleoffloat_lessdef; auto. simpl. rewrite H0; auto.
Qed.

Lemma make_unop_correct:
  forall f sp te tm a v op v' tv,
  eval_expr tge sp te tm a tv ->
  eval_unop op v = Some v' ->
  val_inject f v tv ->
  exists tv', eval_expr tge sp te tm (make_unop op a) tv' /\ val_inject f v' tv'.
Proof.
  intros. exploit eval_unop_compat; eauto. intros [tv' [A B]].
  exploit eval_make_unop; eauto. intros [tv'' [C D]].
  exists tv''; split; auto. 
  inv D. auto. inv B. auto.
Qed.

(** Correctness of the variable accessor [var_addr] *)

Lemma var_addr_correct:
  forall cenv id f tf e le te sp lo hi m cs tm b,
  match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  eval_var_addr ge e id b ->
  exists tv,
     eval_expr tge (Vptr sp Int.zero) te tm (var_addr cenv id) tv
  /\ val_inject f (Vptr b Int.zero) tv.
Proof.
  unfold var_addr; intros.
  assert (match_var f sp e!id cenv!id).
    inv H. inv MENV. auto.
  inv H1; inv H0; try congruence.
  (* local *)
  exists (Vptr sp (Int.repr ofs)); split.
  eapply make_stackaddr_correct.
  congruence.
  (* global *)
  exploit match_callstack_match_globalenvs; eauto. intros [bnd MG]. inv MG.
  exists (Vptr b Int.zero); split.
  eapply make_globaladdr_correct; eauto. rewrite symbols_preserved; auto.
  econstructor; eauto.
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
  C#minor statement [s].  The left vertical arrow is an execution
  of a C#minor statement.  The right vertical arrow is an execution
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

Lemma transl_constant_correct:
  forall f sp cst v,
  Csharpminor.eval_constant cst = Some v ->
  let (tcst, a) := transl_constant cst in
  exists tv,
     eval_constant tge sp tcst = Some tv
  /\ val_inject f v tv
  /\ val_match_approx a v.
Proof.
  destruct cst; simpl; intros; inv H. 
  exists (Vint i); intuition. apply approx_of_int_sound.
  exists (Vfloat f0); intuition. apply approx_of_float_sound.
Qed.

Lemma transl_expr_correct:
  forall f m tm cenv tf e le te sp lo hi cs
    (MINJ: Mem.inject f m tm)
    (MATCH: match_callstack f m tm
             (Frame cenv tf e le te sp lo hi :: cs)
             (Mem.nextblock m) (Mem.nextblock tm)),
  forall a v,
  Csharpminor.eval_expr ge e le m a v ->
  forall ta app
    (TR: transl_expr cenv a = OK (ta, app)),
  exists tv,
     eval_expr tge (Vptr sp Int.zero) te tm ta tv
  /\ val_inject f v tv
  /\ val_match_approx app v.
Proof.
  induction 3; intros; simpl in TR; try (monadInv TR).
  (* Etempvar *)
  inv MATCH. exploit MTMP; eauto. intros [tv [A B]]. 
  exists tv; split. constructor; auto. split. auto. exact I.
  (* Eaddrof *)
  exploit var_addr_correct; eauto. intros [tv [A B]].
  exists tv; split. auto. split. auto. red. auto.
  (* Econst *)
  exploit transl_constant_correct; eauto. 
  destruct (transl_constant cst) as [tcst a]; inv TR.
  intros [tv [A [B C]]].
  exists tv; split. constructor; eauto. eauto.
  (* Eunop *)
  exploit IHeval_expr; eauto. intros [tv1 [EVAL1 [INJ1 APP1]]].
  unfold Csharpminor.eval_unop in H0. 
  destruct (Approx.unop_is_redundant op x0) eqn:?; inv EQ0.
  (* -- eliminated *)
  exploit approx_unop_is_redundant_sound; eauto. intros. 
  replace v with v1 by congruence.
  exists tv1; auto.
  (* -- preserved *)
  exploit make_unop_correct; eauto. intros [tv [A B]].
  exists tv; split. auto. split. auto. eapply approx_of_unop_sound; eauto.
  (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [tv1 [EVAL1 [INJ1 APP1]]].
  exploit IHeval_expr2; eauto. intros [tv2 [EVAL2 [INJ2 APP2]]].
  exploit eval_binop_compat; eauto. intros [tv [EVAL INJ]].
  exists tv; split. econstructor; eauto. split. auto. eapply approx_of_binop_sound; eauto.
  (* Eload *)
  exploit IHeval_expr; eauto. intros [tv1 [EVAL1 [INJ1 APP1]]].
  exploit Mem.loadv_inject; eauto. intros [tv [LOAD INJ]].
  exists tv; split. econstructor; eauto. split. auto.
  destruct v1; simpl in H0; try discriminate. eapply approx_of_chunk_sound; eauto.
Qed.

Lemma transl_exprlist_correct:
  forall f m tm cenv tf e le te sp lo hi cs
    (MINJ: Mem.inject f m tm)
    (MATCH: match_callstack f m tm
             (Frame cenv tf e le te sp lo hi :: cs)
             (Mem.nextblock m) (Mem.nextblock tm)),
  forall a v,
  Csharpminor.eval_exprlist ge e le m a v ->
  forall ta
    (TR: transl_exprlist cenv a = OK ta),
  exists tv,
     eval_exprlist tge (Vptr sp Int.zero) te tm ta tv
  /\ val_list_inject f v tv.
Proof.
  induction 3; intros; monadInv TR.
  exists (@nil val); split. constructor. constructor.
  exploit transl_expr_correct; eauto. intros [tv1 [EVAL1 [VINJ1 APP1]]].
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
  | match_Kcall: forall optid fn e le k tfn sp te tk cenv xenv lo hi cs sz cenv',
      transl_funbody cenv sz fn = OK tfn ->
      match_cont k tk cenv xenv cs ->
      match_cont (Csharpminor.Kcall optid fn e le k)
                 (Kcall optid tfn (Vptr sp Int.zero) te tk)
                 cenv' nil
                 (Frame cenv tfn e le te sp lo hi :: cs).

Inductive match_states: Csharpminor.state -> Cminor.state -> Prop :=
  | match_state:
      forall fn s k e le m tfn ts tk sp te tm cenv xenv f lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt cenv xenv s = OK ts)
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack f m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv xenv cs),
      match_states (Csharpminor.State fn s k e le m)
                   (State tfn ts tk (Vptr sp Int.zero) te tm)
  | match_state_seq:
      forall fn s1 s2 k e le m tfn ts1 tk sp te tm cenv xenv f lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt cenv xenv s1 = OK ts1)
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack f m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont (Csharpminor.Kseq s2 k) tk cenv xenv cs),
      match_states (Csharpminor.State fn (Csharpminor.Sseq s1 s2) k e le m)
                   (State tfn ts1 tk (Vptr sp Int.zero) te tm)
  | match_callstate:
      forall fd args k m tfd targs tk tm f cs cenv
      (TR: transl_fundef fd = OK tfd)
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv nil cs)
      (ISCC: Csharpminor.is_call_cont k)
      (ARGSINJ: val_list_inject f args targs),
      match_states (Csharpminor.Callstate fd args k m)
                   (Callstate tfd targs tk tm)
  | match_returnstate:
      forall v k m tv tk tm f cs cenv
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv nil cs)
      (RESINJ: val_inject f v tv),
      match_states (Csharpminor.Returnstate v k m)
                   (Returnstate tv tk tm).

Remark val_inject_function_pointer:
  forall bound v fd f tv,
  Genv.find_funct ge v = Some fd ->
  match_globalenvs f bound ->
  val_inject f v tv ->
  tv = v.
Proof.
  intros. exploit Genv.find_funct_inv; eauto. intros [b EQ]. subst v.
  rewrite Genv.find_funct_find_funct_ptr in H.
  assert (f b = Some(b, 0)). inv H0. apply DOMAIN. eapply FUNCTIONS; eauto.
  inv H1. rewrite H2 in H5; inv H5. reflexivity.
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
Qed.

(** Properties of [switch] compilation *)

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

Inductive transl_lblstmt_cont(cenv: compilenv) (xenv: exit_env): lbl_stmt -> cont -> cont -> Prop :=
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
  forall fn k e le m tfn ts tk sp te tm cenv xenv f lo hi cs sz ls body tk'
    (TRF: transl_funbody cenv sz fn = OK tfn)
    (TR: transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts)
    (MINJ: Mem.inject f m tm)
    (MCS: match_callstack f m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
    (MK: match_cont k tk cenv xenv cs)
    (TK: transl_lblstmt_cont cenv xenv ls tk tk'),
  exists S,
  plus step tge (State tfn (Sexit O) tk' (Vptr sp Int.zero) te tm) E0 S
  /\ match_states (Csharpminor.State fn (seq_of_lbl_stmt ls) k e le m) S.
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

Lemma transl_lblstmt_find_label_context:
  forall xenv ls body ts tk1 tk2 ts' tk',
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
  exploit transl_find_label. eexact EQ. eapply match_call_cont. eexact H0.
  instantiate (1 := lbl). rewrite H1. auto.
Qed.

(** The simulation diagram. *)

Fixpoint seq_left_depth (s: Csharpminor.stmt) : nat :=
  match s with
  | Csharpminor.Sseq s1 s2 => S (seq_left_depth s1)
  | _ => O
  end.

Definition measure (S: Csharpminor.state) : nat :=
  match S with
  | Csharpminor.State fn s k e le m => seq_left_depth s
  | _ => O
  end.

Lemma transl_step_correct:
  forall S1 t S2, Csharpminor.step ge S1 t S2 ->
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
  exploit match_callstack_freelist; eauto. intros [tm' [P [Q R]]].
  econstructor; split.
  eapply plus_right. eexact A. apply step_skip_call. auto. eauto. traceEq.
  econstructor; eauto.

(* set *)
  monadInv TR.
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
  left; econstructor; split.
  apply plus_one. econstructor; eauto. 
  econstructor; eauto. 
  eapply match_callstack_set_temp; eauto. 

(* store *)
  monadInv TR.
  exploit transl_expr_correct. eauto. eauto. eexact H. eauto. 
  intros [tv1 [EVAL1 [VINJ1 APP1]]].
  exploit transl_expr_correct. eauto. eauto. eexact H0. eauto. 
  intros [tv2 [EVAL2 [VINJ2 APP2]]].
  exploit make_store_correct. eexact EVAL1. eexact EVAL2. eauto. eauto. auto. auto.
  intros [tm' [tv' [EXEC [STORE' MINJ']]]].
  left; econstructor; split.
  apply plus_one. eexact EXEC.
  econstructor; eauto.
  inv VINJ1; simpl in H1; try discriminate. unfold Mem.storev in STORE'.
  rewrite (Mem.nextblock_store _ _ _ _ _ _ H1).
  rewrite (Mem.nextblock_store _ _ _ _ _ _ STORE').
  eapply match_callstack_invariant with f0 m tm; eauto.
  intros. eapply Mem.perm_store_2; eauto. 
  intros. eapply Mem.perm_store_1; eauto.

(* call *)
  simpl in H1. exploit functions_translated; eauto. intros [tfd [FIND TRANS]].
  monadInv TR.
  exploit transl_expr_correct; eauto. intros [tvf [EVAL1 [VINJ1 APP1]]].
  assert (tvf = vf).
    exploit match_callstack_match_globalenvs; eauto. intros [bnd MG].
    eapply val_inject_function_pointer; eauto.
  subst tvf.
  exploit transl_exprlist_correct; eauto.
  intros [tvargs [EVAL2 VINJ2]].
  left; econstructor; split.
  apply plus_one. eapply step_call; eauto.
  apply sig_preserved; eauto.
  econstructor; eauto.
  eapply match_Kcall with (cenv' := cenv); eauto.
  red; auto.

(* builtin *)
  monadInv TR.
  exploit transl_exprlist_correct; eauto.
  intros [tvargs [EVAL2 VINJ2]].
  exploit match_callstack_match_globalenvs; eauto. intros [hi' MG].
  exploit external_call_mem_inject; eauto. 
  eapply inj_preserves_globals; eauto.
  intros [f' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH [INCR SEPARATED]]]]]]]]].
  left; econstructor; split.
  apply plus_one. econstructor. eauto. 
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. eexact varinfo_preserved.
  assert (MCS': match_callstack f' m' tm'
                 (Frame cenv tfn e le te sp lo hi :: cs)
                 (Mem.nextblock m') (Mem.nextblock tm')).
    apply match_callstack_incr_bound with (Mem.nextblock m) (Mem.nextblock tm).
    eapply match_callstack_external_call; eauto.
    intros. eapply external_call_max_perm; eauto.
    omega. omega. 
    eapply external_call_nextblock; eauto.
    eapply external_call_nextblock; eauto.
  econstructor; eauto.
Opaque PTree.set.
  unfold set_optvar. destruct optid; simpl. 
  eapply match_callstack_set_temp; eauto. 
  auto.

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
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
  left; exists (State tfn (if b then x1 else x2) tk (Vptr sp Int.zero) te tm); split.
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
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
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
  exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  econstructor; split.
  apply plus_one. eapply step_return_0. eauto.
  econstructor; eauto. eapply match_call_cont; eauto.
  simpl; auto.

(* return some *)
  monadInv TR. left. 
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
  exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  econstructor; split.
  apply plus_one. eapply step_return_1. eauto. eauto. 
  econstructor; eauto. eapply match_call_cont; eauto.

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
  caseEq (build_compilenv f). intros ce sz BC.
  destruct (zle sz Int.max_unsigned); try congruence.
  intro TRBODY.
  generalize TRBODY; intro TMP. monadInv TMP.
  set (tf := mkfunction (Csharpminor.fn_sig f) 
                        (Csharpminor.fn_params f)
                        (Csharpminor.fn_temps f)
                        sz
                        x0) in *.
  caseEq (Mem.alloc tm 0 (fn_stackspace tf)). intros tm' sp ALLOC'.
  exploit match_callstack_function_entry; eauto. simpl; eauto. simpl; auto.
  intros [f2 [MCS2 MINJ2]].
  left; econstructor; split.
  apply plus_one. constructor; simpl; eauto. 
  econstructor. eexact TRBODY. eauto. eexact MINJ2. eexact MCS2.
  inv MK; simpl in ISCC; contradiction || econstructor; eauto.

(* external call *)
  monadInv TR. 
  exploit match_callstack_match_globalenvs; eauto. intros [hi MG].
  exploit external_call_mem_inject; eauto. 
  eapply inj_preserves_globals; eauto.
  intros [f' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH [INCR SEPARATED]]]]]]]]].
  left; econstructor; split.
  apply plus_one. econstructor.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. eexact varinfo_preserved.
  econstructor; eauto.
  apply match_callstack_incr_bound with (Mem.nextblock m) (Mem.nextblock tm).
  eapply match_callstack_external_call; eauto.
  intros. eapply external_call_max_perm; eauto.
  omega. omega.
  eapply external_call_nextblock; eauto.
  eapply external_call_nextblock; eauto.

(* return *)
  inv MK. simpl.
  left; econstructor; split.
  apply plus_one. econstructor; eauto. 
  unfold set_optvar. destruct optid; simpl; econstructor; eauto.
  eapply match_callstack_set_temp; eauto. 
Qed.

Lemma match_globalenvs_init:
  forall m,
  Genv.init_mem prog = Some m ->
  match_globalenvs (Mem.flat_inj (Mem.nextblock m)) (Mem.nextblock m).
Proof.
  intros. constructor.
  apply Mem.nextblock_pos.
  intros. unfold Mem.flat_inj. apply zlt_true; auto. 
  intros. unfold Mem.flat_inj in H0. 
  destruct (zlt b1 (Mem.nextblock m)); congruence.
  intros. eapply Genv.find_symbol_not_fresh; eauto.
  intros. eapply Genv.find_funct_ptr_not_fresh; eauto.
  intros. eapply Genv.find_var_info_not_fresh; eauto. 
Qed.

Lemma transl_initial_states:
  forall S, Csharpminor.initial_state prog S ->
  exists R, Cminor.initial_state tprog R /\ match_states S R.
Proof.
  induction 1.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  econstructor; split.
  econstructor.
  apply (Genv.init_mem_transf_partial _ _ TRANSL). eauto. 
  simpl. fold tge. rewrite symbols_preserved.
  replace (prog_main tprog) with (prog_main prog). eexact H0.
  symmetry. unfold transl_program in TRANSL.
  eapply transform_partial_program_main; eauto.
  eexact FIND. 
  rewrite <- H2. apply sig_preserved; auto.
  eapply match_callstate with (f := Mem.flat_inj (Mem.nextblock m0)) (cs := @nil frame) (cenv := PTree.empty Z).
  auto.
  eapply Genv.initmem_inject; eauto.
  apply mcs_nil with (Mem.nextblock m0). apply match_globalenvs_init; auto. omega. omega.
  constructor. red; auto.
  constructor. 
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> Csharpminor.final_state S r -> Cminor.final_state R r.
Proof.
  intros. inv H0. inv H. inv MK. inv RESINJ. constructor.
Qed.

Theorem transl_program_correct:
  forward_simulation (Csharpminor.semantics prog) (Cminor.semantics tprog).
Proof.
  eapply forward_simulation_star; eauto.
  eexact symbols_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  eexact transl_step_correct. 
Qed.

End TRANSLATION.

