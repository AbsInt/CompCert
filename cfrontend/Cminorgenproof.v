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
Require Import Coqlib.
Require Intv.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memdata.
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
Proof (Genv.find_funct_ptr_transf_partial2 (transl_fundef gce) transl_globvar _ TRANSL).

Lemma functions_translated:
  forall (v: val) (f: Csharpminor.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef gce f = OK tf.
Proof (Genv.find_funct_transf_partial2 (transl_fundef gce) transl_globvar _ TRANSL).

Lemma sig_preserved_body:
  forall f tf cenv size,
  transl_funbody cenv size f = OK tf -> 
  tf.(fn_sig) = Csharpminor.fn_sig f.
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

Definition global_compilenv_match (ce: compilenv) (ge: Csharpminor.genv) : Prop :=
  forall id,
  match ce!!id with
  | Var_global_scalar chunk =>
      forall b gv, Genv.find_symbol ge id = Some b ->
                   Genv.find_var_info ge b = Some gv ->
                   gv.(gvar_info) = Vscalar chunk
  | Var_global_array => True
  | _ => False
  end.

Lemma global_compilenv_charact:
  global_compilenv_match gce ge.
Proof.
  assert (A: forall ge, global_compilenv_match (PMap.init Var_global_array) ge).
    intros; red; intros. rewrite PMap.gi. auto.
  assert (B: forall ce ge v,
             global_compilenv_match ce ge ->
             global_compilenv_match (assign_global_variable ce v)
                                    (Genv.add_variable ge v)).
  intros; red; intros. destruct v as [id1 [info1 init1 ro1 vo1]].
  unfold assign_global_variable, Genv.find_symbol, Genv.find_var_info; simpl.
  rewrite PMap.gsspec. destruct (peq id id1). subst id.
  destruct info1; auto. 
  rewrite PTree.gss. intros. inv H0. rewrite ZMap.gss in H1. inv H1. auto. 
  generalize (H id). destruct (ce!!id); auto.
  rewrite PTree.gso; auto. intros. rewrite ZMap.gso in H2. eapply H0; eauto.
  exploit Genv.genv_symb_range; eauto. unfold block, ZIndexed.t; omega.
  assert (C: forall vl ce ge,
             global_compilenv_match ce ge ->
             global_compilenv_match (fold_left assign_global_variable vl ce)
                                    (Genv.add_variables ge vl)).
  induction vl; simpl; intros. auto. apply IHvl. apply B. auto.

  unfold gce, build_global_compilenv, ge, Genv.globalenv.
  apply C. apply A.
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
  forall fbl m m' b ofs p,
  Mem.free_list m fbl = Some m' ->
  Mem.perm m' b ofs p ->
  Mem.perm m b ofs p.
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
  In (b, lo, hi) l -> Mem.range_perm m b lo hi Freeable.
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

Lemma bounds_freelist:
  forall b l m m',
  Mem.free_list m l = Some m' -> Mem.bounds m' b = Mem.bounds m b.
Proof.
  induction l; simpl; intros.
  inv H; auto.
  revert H. destruct a as [[b' lo'] hi'].
  caseEq (Mem.free m b' lo' hi'); try congruence.
  intros m1 FREE1 FREE2.
  transitivity (Mem.bounds m1 b). eauto. eapply Mem.bounds_free; eauto.
Qed.

Lemma nextblock_storev:
  forall chunk m addr v m',
  Mem.storev chunk m addr v = Some m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  unfold Mem.storev; intros. destruct addr; try discriminate. 
  eapply Mem.nextblock_store; eauto.
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
  values and a relation [Mem.inject f] between memory states.
  These relations will be used intensively
  in our proof of simulation between Csharpminor and Cminor executions.

  In this section, we define the relation between
  Csharpminor and Cminor environments. *)

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
      PTree.get (for_var id) te = Some v' ->
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
      (forall b gv, Genv.find_symbol ge id = Some b ->
                    Genv.find_var_info ge b = Some gv ->
                    gvar_info gv = Vscalar chunk) ->
      match_var f id e m te sp (Var_global_scalar chunk)
  | match_var_global_array:
      PTree.get id e = None ->
      match_var f id e m te sp (Var_global_array).

(** Matching between a Csharpminor environment [e] and a Cminor
  environment [te].  The [lo] and [hi] parameters delimit the range
  of addresses for the blocks referenced from [te]. *)

Record match_env (f: meminj) (cenv: compilenv)
                 (e: Csharpminor.env) (le: Csharpminor.temp_env) (m: mem)
                 (te: env) (sp: block)
                 (lo hi: Z) : Prop :=
  mk_match_env {

(** Each variable mentioned in the compilation environment must match
  as defined above. *)
    me_vars:
      forall id, match_var f id e m te sp (PMap.get id cenv);

(** Temporaries match *)
    me_temps:
      forall id v, le!id = Some v ->
      exists v', te!(for_temp id) = Some v' /\ val_inject f v v';

(** [lo, hi] is a proper interval. *)
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
      f b = Some(tb, delta) -> b < lo -> tb < sp;

(** The sizes of blocks appearing in [e] agree with their types *)
    me_bounds:
      forall id b lv,
      PTree.get id e = Some(b, lv) -> Mem.bounds m b = (0, sizeof lv)
  }.

Hint Resolve me_low_high.

(** The remainder of this section is devoted to showing preservation
  of the [match_en] invariant under various assignments and memory
  stores.  First: preservation by memory stores to ``mapped'' blocks
  (block that have a counterpart in the Cminor execution). *)

Ltac geninv x := 
  let H := fresh in (generalize x; intro H; inv H).

Lemma match_env_store_mapped:
  forall f cenv e le m1 m2 te sp lo hi chunk b ofs v,
  f b <> None ->
  Mem.store chunk m1 b ofs v = Some m2 ->
  match_env f cenv e le m1 te sp lo hi ->
  match_env f cenv e le m2 te sp lo hi.
Proof.
  intros; inv H1; constructor; auto.
  (* vars *)
  intros. geninv (me_vars0 id); econstructor; eauto.
  rewrite <- H4. eapply Mem.load_store_other; eauto. 
  left. congruence.
  (* bounds *)
  intros. rewrite (Mem.bounds_store _ _ _ _ _ _ H0). eauto. 
Qed.

(** Preservation by assignment to a Csharpminor variable that is 
  translated to a Cminor local variable.  The value being assigned
  must be normalized with respect to the memory chunk of the variable. *)

Remark val_normalized_has_type:
  forall v chunk,
  val_normalized v chunk -> Val.has_type v (type_of_chunk chunk).
Proof.
  intros. red in H. rewrite <- H. 
  destruct chunk; destruct v; exact I.
Qed.

Lemma match_env_store_local:
  forall f cenv e le m1 m2 te sp lo hi id b chunk v tv,
  e!id = Some(b, Vscalar chunk) ->
  val_normalized v chunk ->
  val_inject f v tv ->
  Mem.store chunk m1 b 0 v = Some m2 ->
  match_env f cenv e le m1 te sp lo hi ->
  match_env f cenv e le m2 (PTree.set (for_var id) tv te) sp lo hi.
Proof.
  intros. inv H3. constructor; auto.
  (* vars *)
  intros. geninv (me_vars0 id0).
  (* var_local *)
  case (peq id id0); intro.
    (* the stored variable *)
    subst id0.
    assert (b0 = b) by congruence. subst.
    assert (chunk0 = chunk) by congruence. subst.
    econstructor. eauto. 
    eapply Mem.load_store_same; eauto. apply val_normalized_has_type; auto. auto. 
    rewrite PTree.gss. reflexivity.
    red in H0. rewrite H0. auto. 
    (* a different variable *)
    econstructor; eauto.
    rewrite <- H6. eapply Mem.load_store_other; eauto. 
    rewrite PTree.gso; auto. unfold for_var; congruence.
  (* var_stack_scalar *)
  econstructor; eauto.
  (* var_stack_array *)
  econstructor; eauto.
  (* var_global_scalar *)
  econstructor; eauto.
  (* var_global_array *)
  econstructor; eauto.
  (* temps *)
  intros. rewrite PTree.gso. auto. unfold for_temp, for_var; congruence. 
  (* bounds *)
  intros. rewrite (Mem.bounds_store _ _ _ _ _ _ H2). eauto. 
Qed.

(** Preservation by assignment to a Csharpminor temporary and the
  corresponding Cminor local variable. *)

Lemma match_env_set_temp:
  forall f cenv e le m te sp lo hi id v tv,
  val_inject f v tv ->
  match_env f cenv e le m te sp lo hi ->
  match_env f cenv e (PTree.set id v le) m (PTree.set (for_temp id) tv te) sp lo hi.
Proof.
  intros. inv H0. constructor; auto.
  (* vars *)
  intros. geninv (me_vars0 id0).
  (* var_local *)
  econstructor; eauto. rewrite PTree.gso. auto. unfold for_var, for_temp; congruence.
  (* var_stack_scalar *)
  econstructor; eauto.
  (* var_stack_array *)
  econstructor; eauto.
  (* var_global_scalar *)
  econstructor; eauto.
  (* var_global_array *)
  econstructor; eauto.
  (* temps *)
  intros. rewrite PTree.gsspec in H0. destruct (peq id0 id). 
  inv H0. exists tv; split; auto. apply PTree.gss.
  rewrite PTree.gso. eauto. unfold for_temp; congruence.
Qed.

(** The [match_env] relation is preserved by any memory operation
  that preserves sizes and loads from blocks in the [lo, hi] range. *)

Lemma match_env_invariant:
  forall f cenv e le m1 m2 te sp lo hi,
  (forall b ofs chunk v, 
     lo <= b < hi -> Mem.load chunk m1 b ofs = Some v ->
     Mem.load chunk m2 b ofs = Some v) ->
  (forall b,
     lo <= b < hi -> Mem.bounds m2 b = Mem.bounds m1 b) ->
  match_env f cenv e le m1 te sp lo hi ->
  match_env f cenv e le m2 te sp lo hi.
Proof.
  intros. inv H1. constructor; eauto.
  (* vars *)
  intros. geninv (me_vars0 id); econstructor; eauto.
  (* bounds *)
  intros. rewrite H0. eauto. eauto.
Qed.

(** [match_env] is insensitive to the Cminor values of stack-allocated data. *)

Lemma match_env_extensional:
  forall f cenv e le m te1 sp lo hi te2,
  match_env f cenv e le m te1 sp lo hi ->
  (forall id chunk, cenv!!id = Var_local chunk -> te2!(for_var id) = te1!(for_var id)) ->
  (forall id v, le!id = Some v -> te2!(for_temp id) = te1!(for_temp id)) ->
  match_env f cenv e le m te2 sp lo hi.
Proof.
  intros. inv H; econstructor; eauto.
  intros. geninv (me_vars0 id); econstructor; eauto. rewrite <- H6. eauto.
  intros. rewrite (H1 _ _ H). auto. 
Qed.

(** [match_env] and allocations *)

Inductive alloc_condition: var_info -> var_kind -> block -> option (block * Z) -> Prop :=
  | alloc_cond_local: forall chunk sp,
      alloc_condition (Var_local chunk) (Vscalar chunk) sp None
  | alloc_cond_stack_scalar: forall chunk pos sp,
      alloc_condition (Var_stack_scalar chunk pos) (Vscalar chunk) sp (Some(sp, pos))
  | alloc_cond_stack_array: forall pos sz sp,
      alloc_condition (Var_stack_array pos) (Varray sz) sp (Some(sp, pos)).

Lemma match_env_alloc_same:
  forall f1 cenv e le m1 te sp lo lv m2 b f2 id info tv,
  match_env f1 cenv e le m1 te sp lo (Mem.nextblock m1) ->
  Mem.alloc m1 0 (sizeof lv) = (m2, b) ->
  inject_incr f1 f2 ->
  alloc_condition info lv sp (f2 b) ->
  (forall b', b' <> b -> f2 b' = f1 b') ->
  te!(for_var id) = Some tv ->
  e!id = None ->
  match_env f2 (PMap.set id info cenv) (PTree.set id (b, lv) e) le m2 te sp lo (Mem.nextblock m2).
Proof.
  intros until tv.
  intros ME ALLOC INCR ACOND OTHER TE E.
(*
  assert (ALLOC_RES: b = Mem.nextblock m1) by eauto with mem.
  assert (ALLOC_NEXT: Mem.nextblock m2 = Zsucc(Mem.nextblock m1)) by eauto with mem.
*)
  inv ME; constructor.
(* vars *)
  intros. rewrite PMap.gsspec. destruct (peq id0 id). subst id0.
  (* the new var *)
  inv ACOND; econstructor.
    (* local *)
  rewrite PTree.gss. reflexivity. 
  eapply Mem.load_alloc_same'; eauto. omega. simpl; omega. apply Zdivide_0.
  auto. eauto. constructor. 
    (* stack scalar *)
  rewrite PTree.gss; reflexivity. 
  econstructor; eauto. rewrite Int.add_commut; rewrite Int.add_zero; auto.
    (* stack array *)
  rewrite PTree.gss; reflexivity. 
  econstructor; eauto. rewrite Int.add_commut; rewrite Int.add_zero; auto.
  (* the other vars *)
  geninv (me_vars0 id0); econstructor.
    (* local *)
  rewrite PTree.gso; eauto. eapply Mem.load_alloc_other; eauto.
  rewrite OTHER; auto.
  exploit me_bounded0; eauto. exploit Mem.alloc_result; eauto. unfold block; omega.
  eauto. eapply val_inject_incr; eauto. 
    (* stack scalar *)
  rewrite PTree.gso; eauto. eapply val_inject_incr; eauto.
    (* stack array *)
  rewrite PTree.gso; eauto. eapply val_inject_incr; eauto.
    (* global scalar *)
  rewrite PTree.gso; auto. auto. 
    (* global array *)
  rewrite PTree.gso; auto.
(* temps *)
  intros. exploit me_temps0; eauto. intros [v' [A B]]. 
  exists v'; split; auto. eapply val_inject_incr; eauto.
(* low high *)
  exploit Mem.nextblock_alloc; eauto. unfold block in *; omega.
(* bounded *)
  exploit Mem.alloc_result; eauto. intro RES.
  exploit Mem.nextblock_alloc; eauto. intro NEXT.
  intros until lv0. rewrite PTree.gsspec. destruct (peq id0 id); intro EQ.
  inv EQ. unfold block in *; omega.
  exploit me_bounded0; eauto. unfold block in *; omega.
(* inj *)
  intros until lv2. repeat rewrite PTree.gsspec. 
  exploit Mem.alloc_result; eauto. intro RES.
  destruct (peq id1 id); destruct (peq id2 id); subst; intros A1 A2 DIFF.
  congruence.
  inv A1. exploit me_bounded0; eauto. unfold block; omega.
  inv A2. exploit me_bounded0; eauto. unfold block; omega.
  eauto.
(* inv *)
  intros. destruct (zeq b0 b). 
  subst. exists id; exists lv. apply PTree.gss.
  exploit me_inv0; eauto. rewrite <- OTHER; eauto.
  intros [id' [lv' A]]. exists id'; exists lv'.
  rewrite PTree.gso; auto. congruence.
(* incr *)
  intros. eapply me_incr0; eauto. rewrite <- OTHER; eauto.
  exploit Mem.alloc_result; eauto. unfold block; omega.
(* bounds *)
  intros. rewrite PTree.gsspec in H.
  rewrite (Mem.bounds_alloc _ _ _ _ _ ALLOC). 
  destruct (peq id0 id). 
  inv H. apply dec_eq_true.
  rewrite dec_eq_false. eauto. 
  apply Mem.valid_not_valid_diff with m1.
  exploit me_bounded0; eauto. intros [A B]. auto. 
  eauto with mem.
Qed.

Lemma match_env_alloc_other:
  forall f1 cenv e le m1 te sp lo hi sz m2 b f2,
  match_env f1 cenv e le m1 te sp lo hi ->
  Mem.alloc m1 0 sz = (m2, b) ->
  inject_incr f1 f2 ->
  (forall b', b' <> b -> f2 b' = f1 b') ->
  hi <= b ->
  match f2 b with None => True | Some(b',ofs) => sp < b' end ->
  match_env f2 cenv e le m2 te sp lo hi.
Proof.
  intros until f2; intros ME ALLOC INCR OTHER BOUND TBOUND.
  inv ME.
  assert (BELOW: forall id b' lv, e!id = Some(b', lv) -> b' <> b).
    intros. exploit me_bounded0; eauto. exploit Mem.alloc_result; eauto.
    unfold block in *; omega.
  econstructor; eauto.
(* vars *)
  intros. geninv (me_vars0 id); econstructor.
    (* local *)
  eauto. eapply Mem.load_alloc_other; eauto.
  rewrite OTHER; eauto. eauto. eapply val_inject_incr; eauto. 
    (* stack scalar *)
  eauto. eapply val_inject_incr; eauto. 
    (* stack array *)
  eauto. eapply val_inject_incr; eauto. 
    (* global scalar *)
  auto. auto. 
    (* global array *)
  auto.
(* temps *)
  intros. exploit me_temps0; eauto. intros [v' [A B]]. 
  exists v'; split; auto. eapply val_inject_incr; eauto.
(* inv *)
  intros. rewrite OTHER in H. eauto. 
  red; intro; subst b0. rewrite H in TBOUND. omegaContradiction.
(* incr *)
  intros. eapply me_incr0; eauto. rewrite <- OTHER; eauto. 
  exploit Mem.alloc_result; eauto. unfold block in *; omega.
(* bounds *)
  intros. rewrite (Mem.bounds_alloc_other _ _ _ _ _ ALLOC). eauto.
  exploit me_bounded0; eauto.
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
  forall f1 cenv e le m1 te sp lo hi m2 f2 m1',
  match_env f1 cenv e le m1 te sp lo hi ->
  mem_unchanged_on (loc_unmapped f1) m1 m2 ->
  inject_incr f1 f2 ->
  inject_separated f1 f2 m1 m1' ->
  (forall b, Mem.valid_block m1 b -> Mem.bounds m2 b = Mem.bounds m1 b) ->
  hi <= Mem.nextblock m1 -> sp < Mem.nextblock m1' ->
  match_env f2 cenv e le m2 te sp lo hi.
Proof.
  intros until m1'. intros ME UNCHANGED INCR SEPARATED BOUNDS VALID VALID'.
  destruct UNCHANGED as [UNCHANGED1 UNCHANGED2].
  inversion ME. constructor; auto.
(* vars *)
  intros. geninv (me_vars0 id); try (econstructor; eauto; fail).
    (* local *)
    econstructor.
    eauto.
    apply UNCHANGED2; eauto.
    rewrite <- H3. eapply inject_incr_separated_same; eauto.
    red. exploit me_bounded0; eauto. omega. 
    eauto. eauto.
(* temps *)
  intros. exploit me_temps0; eauto. intros [v' [A B]]. 
  exists v'; split; auto. eapply val_inject_incr; eauto.
(* inv *)
  intros. apply me_inv0 with delta. eapply inject_incr_separated_same'; eauto.
(* incr *)
  intros.
  exploit inject_incr_separated_same; eauto. 
  instantiate (1 := b). red; omega. intros. 
  apply me_incr0 with b delta. congruence. auto.
(* bounds *)
  intros. rewrite BOUNDS; eauto. 
  red. exploit me_bounded0; eauto. omega.
Qed.

(** * Invariant on abstract call stacks  *)

(** Call stacks represent abstractly the execution state of the current
  Csharpminor and Cminor functions, as well as the states of the
  calling functions.  A call stack is a list of frames, each frame
  collecting information on the current execution state of a Csharpminor
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

(** Global environments match if the memory injection [f] leaves unchanged
  the references to global symbols and functions. *)

Inductive match_globalenvs (f: meminj) (bound: Z): Prop :=
  | mk_match_globalenvs
      (POS: bound > 0)
      (DOMAIN: forall b, b < bound -> f b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, f b1 = Some(b2, delta) -> b2 < bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> b < bound)
      (INFOS: forall b gv, Genv.find_var_info ge b = Some gv -> b < bound).

(** Matching of call stacks imply:
- matching of environments for each of the frames
- matching of the global environments
- separation conditions over the memory blocks allocated for C#minor local variables;
- separation conditions over the memory blocks allocated for Cminor stack data;
- freeable permissions on the parts of the Cminor stack data blocks
  that are not images of C#minor local variable blocks.
*)

Definition padding_freeable (f: meminj) (m: mem) (tm: mem) (sp: block) (sz: Z) : Prop :=
  forall ofs, 
  0 <= ofs < sz ->
  Mem.perm tm sp ofs Freeable
  \/ exists b, exists delta, 
       f b = Some(sp, delta) 
       /\ Mem.low_bound m b + delta <= ofs < Mem.high_bound m b + delta.

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
        (MENV: match_env f cenv e le m te sp lo hi)
        (PERM: padding_freeable f m tm sp tf.(fn_stackspace))
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

(** We now show invariance properties for [match_callstack] that
    generalize those for [match_env]. *)

Lemma padding_freeable_invariant:
  forall f1 m1 tm1 sp sz cenv e le te lo hi f2 m2 tm2,
  padding_freeable f1 m1 tm1 sp sz ->
  match_env f1 cenv e le m1 te sp lo hi ->
  (forall ofs, Mem.perm tm1 sp ofs Freeable -> Mem.perm tm2 sp ofs Freeable) ->
  (forall b, b < hi -> Mem.bounds m2 b = Mem.bounds m1 b) ->
  (forall b, b < hi -> f2 b = f1 b) ->
  padding_freeable f2 m2 tm2 sp sz.
Proof.
  intros; red; intros.
  exploit H; eauto. intros [A | [b [delta [A B]]]].
  left; auto. 
  exploit me_inv; eauto. intros [id [lv C]]. 
  exploit me_bounded; eauto. intros [D E]. 
  right; exists b; exists delta. split.
  rewrite H3; auto. 
  rewrite H2; auto.
Qed.

Lemma match_callstack_store_mapped:
  forall f m tm chunk b b' delta ofs ofs' v tv m' tm',
  f b = Some(b', delta) ->
  Mem.store chunk m b ofs v = Some m' ->
  Mem.store chunk tm b' ofs' tv = Some tm' ->
  forall cs lo hi,
  match_callstack f m tm cs lo hi ->
  match_callstack f m' tm' cs lo hi.
Proof.
  induction 4.
  econstructor; eauto.
  constructor; auto. 
  eapply match_env_store_mapped; eauto. congruence.
  eapply padding_freeable_invariant; eauto. 
  intros; eauto with mem.
  intros. eapply Mem.bounds_store; eauto.
Qed.

Lemma match_callstack_storev_mapped:
  forall f m tm chunk a ta v tv m' tm',
  val_inject f a ta ->
  Mem.storev chunk m a v = Some m' ->
  Mem.storev chunk tm ta tv = Some tm' ->
  forall cs lo hi,
  match_callstack f m tm cs lo hi ->
  match_callstack f m' tm' cs lo hi.
Proof.
  intros. destruct a; simpl in H0; try discriminate.
  inv H. simpl in H1. 
  eapply match_callstack_store_mapped; eauto. 
Qed.

Lemma match_callstack_invariant:
  forall f m tm cs bound tbound,
  match_callstack f m tm cs bound tbound ->
  forall m' tm',
  (forall cenv e le te sp lo hi,
    hi <= bound ->
    match_env f cenv e le m te sp lo hi ->
    match_env f cenv e le m' te sp lo hi) ->
  (forall b,
    b < bound -> Mem.bounds m' b = Mem.bounds m b) ->
  (forall b ofs p,
    b < tbound -> Mem.perm tm b ofs p -> Mem.perm tm' b ofs p) ->
  match_callstack f m' tm' cs bound tbound.
Proof.
  induction 1; intros.
  econstructor; eauto.
  constructor; auto.
  eapply padding_freeable_invariant; eauto. 
  intros. apply H1. omega.
  eapply IHmatch_callstack; eauto. 
  intros. eapply H0; eauto. inv MENV; omega.
  intros. apply H1; auto. inv MENV; omega. 
  intros. apply H2; auto. omega. 
Qed.

Lemma match_callstack_store_local:
  forall f cenv e le te sp lo hi cs bound tbound m1 m2 tm tf id b chunk v tv,
  e!id = Some(b, Vscalar chunk) ->
  val_normalized v chunk ->
  val_inject f v tv ->
  Mem.store chunk m1 b 0 v = Some m2 ->
  match_callstack f m1 tm (Frame cenv tf e le te sp lo hi :: cs) bound tbound ->
  match_callstack f m2 tm (Frame cenv tf e le (PTree.set (for_var id) tv te) sp lo hi :: cs) bound tbound.
Proof.
  intros. inv H3. constructor; auto.
  eapply match_env_store_local; eauto.
  eapply padding_freeable_invariant; eauto.
  intros. eapply Mem.bounds_store; eauto.
  eapply match_callstack_invariant; eauto.
  intros. apply match_env_invariant with m1; auto.
  intros. rewrite <- H6. eapply Mem.load_store_other; eauto. 
  left. inv MENV. exploit me_bounded0; eauto. unfold block in *; omega. 
  intros. eapply Mem.bounds_store; eauto.
  intros. eapply Mem.bounds_store; eauto.
Qed.

(** A variant of [match_callstack_store_local] where the Cminor environment
  [te] already associates to [id] a value that matches the assigned value.
  In this case, [match_callstack] is preserved even if no assignment
  takes place on the Cminor side. *)

Lemma match_callstack_store_local_unchanged:
  forall f cenv e le te sp lo hi cs bound tbound m1 m2 id b chunk v tv tf tm,
  e!id = Some(b, Vscalar chunk) ->
  val_normalized v chunk ->
  val_inject f v tv ->
  Mem.store chunk m1 b 0 v = Some m2 ->
  te!(for_var id) = Some tv ->
  match_callstack f m1 tm (Frame cenv tf e le te sp lo hi :: cs) bound tbound ->
  match_callstack f m2 tm (Frame cenv tf e le te sp lo hi :: cs) bound tbound.
Proof.
Opaque for_var.
  intros. exploit match_callstack_store_local; eauto. intro MCS.
  inv MCS. constructor; auto. eapply match_env_extensional; eauto. 
  intros. rewrite PTree.gsspec.
Transparent for_var.
  case (peq (for_var id0) (for_var id)); intros.
  unfold for_var in e0. congruence.
  auto.
  intros. rewrite PTree.gso; auto. unfold for_temp, for_var; congruence.
Qed.

Lemma match_callstack_set_temp:
  forall f cenv e le te sp lo hi cs bound tbound m tm tf id v tv,
  val_inject f v tv ->
  match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) bound tbound ->
  match_callstack f m tm (Frame cenv tf e (PTree.set id v le) (PTree.set (for_temp id) tv te) sp lo hi :: cs) bound tbound.
Proof.
  intros. inv H0. constructor; auto.
  eapply match_env_set_temp; eauto. 
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

(** Preservation of [match_callstack] by freeing all blocks allocated
  for local variables at function entry (on the Csharpminor side)
  and simultaneously freeing the Cminor stack data block. *)

Lemma in_blocks_of_env:
  forall e id b lv,
  e!id = Some(b, lv) -> In (b, 0, sizeof lv) (blocks_of_env e).
Proof.
  unfold blocks_of_env; intros. 
  change (b, 0, sizeof lv) with (block_of_binding (id, (b, lv))).
  apply List.in_map. apply PTree.elements_correct. auto.
Qed.

Lemma in_blocks_of_env_inv:
  forall b lo hi e,
  In (b, lo, hi) (blocks_of_env e) ->
  exists id, exists lv, e!id = Some(b, lv) /\ lo = 0 /\ hi = sizeof lv.
Proof.
  unfold blocks_of_env; intros. 
  exploit list_in_map_inv; eauto. intros [[id [b' lv]] [A B]].
  unfold block_of_binding in A. inv A. 
  exists id; exists lv; intuition. apply PTree.elements_complete. auto.
Qed.

(*
Lemma free_list_perm:
  forall l m m',
  Mem.free_list m l = Some m' ->
  forall b ofs p,
  Mem.perm m' b ofs p -> Mem.perm m b ofs p.
Proof.
  induction l; simpl; intros. 
  inv H; auto.
  revert H. destruct a as [[b' lo'] hi'].
  caseEq (Mem.free m b' lo' hi'); try congruence.
  intros m1 FREE1 FREE2.
  eauto with mem. 
Qed.
*)

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
  exploit PERM; eauto. intros [A | [b [delta [A B]]]].
  auto.
  exploit me_inv0; eauto. intros [id [lv C]]. 
  exploit me_bounds0; eauto. intro D. rewrite D in B; simpl in B.
  assert (Mem.range_perm m b 0 (sizeof lv) Freeable). 
  eapply free_list_freeable; eauto. eapply in_blocks_of_env; eauto.
  replace ofs with ((ofs - delta) + delta) by omega. 
  eapply Mem.perm_inject; eauto. apply H0. omega. 
  destruct X as  [tm' FREE].
  exploit nextblock_freelist; eauto. intro NEXT.
  exploit Mem.nextblock_free; eauto. intro NEXT'.
  exists tm'. split. auto. split.
  rewrite NEXT; rewrite NEXT'.
  apply match_callstack_incr_bound with lo sp; try omega.
  apply match_callstack_invariant with m tm; auto.
  intros. apply match_env_invariant with m; auto.
  intros. rewrite <- H2. eapply load_freelist; eauto. 
  intros. exploit in_blocks_of_env_inv; eauto. 
  intros [id [lv [A [B C]]]]. 
  exploit me_bounded0; eauto. unfold block; omega.
  intros. eapply bounds_freelist; eauto.
  intros. eapply bounds_freelist; eauto.
  intros. eapply Mem.perm_free_1; eauto. left; unfold block; omega.
  eapply Mem.free_inject; eauto.
  intros. exploit me_inv0; eauto. intros [id [lv A]]. 
  exists 0; exists (sizeof lv); split.
  eapply in_blocks_of_env; eauto.
  exploit me_bounds0; eauto. intro B. 
  exploit Mem.perm_in_bounds; eauto. rewrite B; simpl. auto.
Qed.

(** Preservation of [match_callstack] by allocations. *)

Lemma match_callstack_alloc_below:
  forall f1 m1 tm sz m2 b f2,
  Mem.alloc m1 0 sz = (m2, b) ->
  inject_incr f1 f2 ->
  (forall b', b' <> b -> f2 b' = f1 b') ->
  forall cs bound tbound,
  match_callstack f1 m1 tm cs bound tbound ->
  bound <= b ->
  match f2 b with None => True | Some(b',ofs) => tbound <= b' end ->
  match_callstack f2 m2 tm cs bound tbound.
Proof.
  induction 4; intros.
  apply mcs_nil with hi; auto. 
  inv H2. constructor; auto. 
  intros. destruct (eq_block b1 b). subst. rewrite H2 in H6. omegaContradiction.
  rewrite H1 in H2; eauto.
  constructor; auto.
  eapply match_env_alloc_other; eauto. omega. destruct (f2 b); auto. destruct p; omega.
  eapply padding_freeable_invariant; eauto. 
  intros. eapply Mem.bounds_alloc_other; eauto. unfold block; omega.
  intros. apply H1. unfold block; omega.
  apply IHmatch_callstack. 
  inv MENV; omega. 
  destruct (f2 b); auto. destruct p; omega. 
Qed.

Lemma match_callstack_alloc_left:
  forall f1 m1 tm cenv tf e le te sp lo cs lv m2 b f2 info id tv,
  match_callstack f1 m1 tm
    (Frame cenv tf e le te sp lo (Mem.nextblock m1) :: cs)
    (Mem.nextblock m1) (Mem.nextblock tm) ->
  Mem.alloc m1 0 (sizeof lv) = (m2, b) ->
  inject_incr f1 f2 ->
  alloc_condition info lv sp (f2 b) ->
  (forall b', b' <> b -> f2 b' = f1 b') ->
  te!(for_var id) = Some tv ->
  e!id = None ->
  match_callstack f2 m2 tm
    (Frame (PMap.set id info cenv) tf (PTree.set id (b, lv) e) le te sp lo (Mem.nextblock m2) :: cs)
    (Mem.nextblock m2) (Mem.nextblock tm).
Proof.
  intros until tv; intros MCS ALLOC INCR ACOND OTHER TE E.
  inv MCS. 
  exploit Mem.alloc_result; eauto. intro RESULT.
  exploit Mem.nextblock_alloc; eauto. intro NEXT.
  constructor.
  omega. auto. 
  eapply match_env_alloc_same; eauto.
  eapply padding_freeable_invariant; eauto. 
  intros. eapply Mem.bounds_alloc_other; eauto. unfold block in *; omega.
  intros. apply OTHER. unfold block in *; omega. 
  eapply match_callstack_alloc_below; eauto.
  inv MENV. unfold block in *; omega.
  inv ACOND. auto. omega. omega.
Qed.

Lemma match_callstack_alloc_right:
  forall f m tm cs tf sp tm' te,
  match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm', sp) ->
  Mem.inject f m tm ->
  match_callstack f m tm'
    (Frame gce tf empty_env empty_temp_env te sp (Mem.nextblock m) (Mem.nextblock m) :: cs)
    (Mem.nextblock m) (Mem.nextblock tm').
Proof.
  intros.
  exploit Mem.alloc_result; eauto. intro RES.
  exploit Mem.nextblock_alloc; eauto. intro NEXT.
  constructor. omega. unfold block in *; omega.
(* match env *) 
  constructor.
(* vars *)
  intros. generalize (global_compilenv_charact id); intro. 
  destruct (gce!!id); try contradiction. 
  constructor. apply PTree.gempty. auto.
  constructor. apply PTree.gempty.
(* temps *)
  intros. rewrite PTree.gempty in H2. congruence.  
(* low high *)
  omega.
(* bounded *)
  intros. rewrite PTree.gempty in H2. congruence.
(* inj *)
  intros. rewrite PTree.gempty in H2. congruence.
(* inv *)
  intros. 
  assert (sp <> sp). apply Mem.valid_not_valid_diff with tm.
  eapply Mem.valid_block_inject_2; eauto. eauto with mem. 
  tauto.
(* incr *)
  intros. rewrite RES. change (Mem.valid_block tm tb).
  eapply Mem.valid_block_inject_2; eauto.
(* bounds *)
  unfold empty_env; intros. rewrite PTree.gempty in H2. congruence.
(* padding freeable *)
  red; intros. left. eapply Mem.perm_alloc_2; eauto. 
(* previous call stack *)
  rewrite RES. apply match_callstack_invariant with m tm; auto.
  intros. eapply Mem.perm_alloc_1; eauto. 
Qed.

(** Decidability of the predicate "this is not a padding location" *)

Definition is_reachable (f: meminj) (m: mem) (sp: block) (ofs: Z) : Prop :=
  exists b, exists delta, 
  f b = Some(sp, delta)
  /\ Mem.low_bound m b + delta <= ofs < Mem.high_bound m b + delta.

Lemma is_reachable_dec:
  forall f cenv e le m te sp lo hi ofs,
  match_env f cenv e le m te sp lo hi ->
  {is_reachable f m sp ofs} + {~is_reachable f m sp ofs}.
Proof.
  intros.
  set (P := fun (b: block) =>
       match f b with
       | None => False
       | Some(b', delta) =>
           b' = sp /\ Mem.low_bound m b + delta <= ofs < Mem.high_bound m b + delta
       end).
  assert ({forall b, Intv.In b (lo, hi) -> ~P b} + {exists b, Intv.In b (lo, hi) /\ P b}).
  apply Intv.forall_dec. intro b. unfold P. 
  destruct (f b) as [[b' delta] | ]. 
  destruct (eq_block b' sp).
  destruct (zle (Mem.low_bound m b + delta) ofs).
  destruct (zlt ofs (Mem.high_bound m b + delta)).
  right; auto.
  left; intuition.
  left; intuition.
  left; intuition.
  left; intuition.
  inv H. destruct H0.
  right; red; intros [b [delta [A [B C]]]].
  elim (n b). 
  exploit me_inv0; eauto. intros [id [lv D]]. exploit me_bounded0; eauto. 
  red. rewrite A. auto. 
  left. destruct e0 as [b [A B]]. red in B; revert B.
  case_eq (f b). intros [b' delta] EQ [C [D E]]. subst b'. 
  exists b; exists delta. auto. 
  tauto. 
Qed.

(** Preservation of [match_callstack] by external calls. *)

Lemma match_callstack_external_call:
  forall f1 f2 m1 m2 m1' m2',
  mem_unchanged_on (loc_unmapped f1) m1 m2 ->
  mem_unchanged_on (loc_out_of_reach f1 m1) m1' m2' ->
  inject_incr f1 f2 ->
  inject_separated f1 f2 m1 m1' ->
  (forall b, Mem.valid_block m1 b -> Mem.bounds m2 b = Mem.bounds m1 b) ->
  forall cs bound tbound,
  match_callstack f1 m1 m1' cs bound tbound ->
  bound <= Mem.nextblock m1 -> tbound <= Mem.nextblock m1' ->
  match_callstack f2 m2 m2' cs bound tbound.
Proof.
  intros until m2'. 
  intros UNMAPPED OUTOFREACH INCR SEPARATED BOUNDS.
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
  eapply match_env_external_call; eauto. omega. omega. 
  (* padding-freeable *)
  red; intros.
  destruct (is_reachable_dec _ _ _ _ _ _ _ _ _ ofs MENV).
  destruct i as [b [delta [A B]]].
  right; exists b; exists delta; split.
  apply INCR; auto. rewrite BOUNDS. auto. 
  exploit me_inv; eauto. intros [id [lv C]].
  exploit me_bounded; eauto. intros. red; omega.
  exploit PERM; eauto. intros [A|A]; try contradiction. left.
  apply OUTOFREACH1; auto. red; intros. 
  assert ((ofs < Mem.low_bound m1 b0 + delta \/ ofs >= Mem.high_bound m1 b0 + delta)
          \/ Mem.low_bound m1 b0 + delta <= ofs < Mem.high_bound m1 b0 + delta)
  by omega. destruct H4; auto.
  elim n. exists b0; exists delta; auto.
  (* induction *)
  eapply IHmatch_callstack; eauto. inv MENV; omega. omega.
Qed.

Remark external_call_nextblock_incr:
  forall ef vargs m1 t vres m2,
  external_call ef ge vargs m1 t vres m2 ->
  Mem.nextblock m1 <= Mem.nextblock m2.
Proof.
  intros. 
  generalize (@external_call_valid_block _ _ _ _ _ _ _ _ _ (Mem.nextblock m1 - 1) H).
  unfold Mem.valid_block. omega. 
Qed.

Remark inj_preserves_globals:
  forall f hi,
  match_globalenvs f hi ->
  meminj_preserves_globals ge f.
Proof.
  intros. inv H.
  split. intros. apply DOMAIN. eapply SYMBOLS. eauto.
  split. intros. apply DOMAIN. eapply INFOS. eauto. 
  intros. symmetry. eapply IMAGE; eauto. 
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
  Mem.inject f m tm ->
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
    replace delta0 with delta by congruence.
    decEq. decEq. apply Int.sub_shifted.
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
  caseEq (Mem.valid_pointer m b1 (Int.signed ofs1) && Mem.valid_pointer m b0 (Int.signed ofs0)); 
  intro EQ; rewrite EQ in H4; try discriminate.
  elim (andb_prop _ _ EQ); intros.
  destruct (eq_block b1 b0); inv H4.
  (* same blocks in source *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  exists (Val.of_bool (Int.cmp c ofs1 ofs0)); split.
  unfold eq_block; rewrite zeq_true; simpl.
  decEq. decEq. rewrite Int.translate_cmp. auto. 
  eapply Mem.valid_pointer_inject_no_overflow; eauto.
  eapply Mem.valid_pointer_inject_no_overflow; eauto.
  apply val_inject_val_of_bool.
  (* different blocks in source *)
  simpl. exists v; split; [idtac | eapply val_inject_eval_compare_mismatch; eauto].
  destruct (eq_block b2 b3); auto.
  exploit Mem.different_pointers_inject; eauto. intros [A|A]. 
  congruence.
  decEq. destruct c; simpl in H6; inv H6; unfold Int.cmp.
  predSpec Int.eq Int.eq_spec (Int.add ofs1 (Int.repr delta)) (Int.add ofs0 (Int.repr delta0)).
  congruence. auto.
  predSpec Int.eq Int.eq_spec (Int.add ofs1 (Int.repr delta)) (Int.add ofs0 (Int.repr delta0)).
  congruence. auto.
  (* cmpu *)
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
  (* cmpf *)
  inv H0; try discriminate; inv H1; inv H; TrivialOp.
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

Inductive val_content_inject (f: meminj): memory_chunk -> val -> val -> Prop :=
  | val_content_inject_8_signed:
      forall n,
      val_content_inject f Mint8signed (Vint (Int.sign_ext 8 n)) (Vint n)
  | val_content_inject_8_unsigned:
      forall n,
      val_content_inject f Mint8unsigned (Vint (Int.zero_ext 8 n)) (Vint n)
  | val_content_inject_16_signed:
      forall n,
      val_content_inject f Mint16signed (Vint (Int.sign_ext 16 n)) (Vint n)
  | val_content_inject_16_unsigned:
      forall n,
      val_content_inject f Mint16unsigned (Vint (Int.zero_ext 16 n)) (Vint n)
  | val_content_inject_32:
      forall n,
      val_content_inject f Mfloat32 (Vfloat (Float.singleoffloat n)) (Vfloat n)
  | val_content_inject_base:
      forall chunk v1 v2,
      val_inject f v1 v2 ->
      val_content_inject f chunk v1 v2.

Hint Resolve val_content_inject_base.

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
  destruct v1; simpl in H0; inv H0; constructor; constructor.
Qed.

Lemma storev_mapped_inject':
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
  inv H2; (eapply Mem.storev_mapped_inject; [eauto|idtac|eauto|eauto]);
  auto; apply H3; intros.
  apply Mem.store_int8_sign_ext.
  apply Mem.store_int8_zero_ext.
  apply Mem.store_int16_sign_ext.
  apply Mem.store_int16_zero_ext.
  apply Mem.store_float32_truncate.
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
  exploit store_arg_content_inject. eexact H0. eauto. 
  intros [tv [EVAL VCINJ]].
  exploit storev_mapped_inject'; eauto.
  intros [tm' [STORE MEMINJ]].
  exists tm'; exists tv.
  split. eapply step_store; eauto.
  auto.
Qed.

(** Correctness of the variable accessors [var_get], [var_addr],
  and [var_set]. *)

Lemma var_get_correct:
  forall cenv id a f tf e le te sp lo hi m cs tm b chunk v,
  var_get cenv id = OK a ->
  match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.inject f m tm ->
  eval_var_ref ge e id b chunk ->
  Mem.load chunk m b 0 = Some v ->
  exists tv,
    eval_expr tge (Vptr sp Int.zero) te tm a tv /\
    val_inject f v tv.
Proof.
  unfold var_get; intros.
  assert (match_var f id e m te sp cenv!!id). inv H0. inv MENV. auto.
  inv H4; rewrite <- H5 in H; inv H; inv H2; try congruence.
  (* var_local *)
  exists v'; split.
  apply eval_Evar. auto.
  congruence.
  (* var_stack_scalar *)
  assert (b0 = b). congruence. subst b0.
  assert (chunk0 = chunk). congruence. subst chunk0.
  exploit Mem.loadv_inject; eauto.
    unfold Mem.loadv. eexact H3. 
  intros [tv [LOAD INJ]].
  exists tv; split. 
  eapply eval_Eload; eauto. eapply make_stackaddr_correct; eauto.
  auto.
  (* var_global_scalar *)
  simpl in *.
  exploit match_callstack_match_globalenvs; eauto. intros [bnd MG]. inv MG.
  assert (chunk0 = chunk). exploit H7; eauto. congruence. subst chunk0.
  assert (val_inject f (Vptr b Int.zero) (Vptr b Int.zero)).
    econstructor; eauto. 
  exploit Mem.loadv_inject; eauto. simpl. eauto.   
  intros [tv [LOAD INJ]].
  exists tv; split. 
  eapply eval_Eload; eauto. eapply make_globaladdr_correct; eauto.
  rewrite symbols_preserved; auto.
  auto.
Qed.

Lemma var_addr_correct:
  forall cenv id a f tf e le te sp lo hi m cs tm b,
  match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  var_addr cenv id = OK a ->
  eval_var_addr ge e id b ->
  exists tv,
    eval_expr tge (Vptr sp Int.zero) te tm a tv /\
    val_inject f (Vptr b Int.zero) tv.
Proof.
  unfold var_addr; intros.
  assert (match_var f id e m te sp cenv!!id).
    inv H. inv MENV. auto. 
  inv H2; rewrite <- H3 in H0; inv H0; inv H1; try congruence.
  (* var_stack_scalar *)
  exists (Vptr sp (Int.repr ofs)); split.
  eapply make_stackaddr_correct. congruence. 
  (* var_stack_array *)
  exists (Vptr sp (Int.repr ofs)); split.
  eapply make_stackaddr_correct. congruence.
  (* var_global_scalar *)
  exploit match_callstack_match_globalenvs; eauto. intros [bnd MG]. inv MG.
  exists (Vptr b Int.zero); split.
  eapply make_globaladdr_correct; eauto. rewrite symbols_preserved; auto.
  econstructor; eauto. 
  (* var_global_array *)
  exploit match_callstack_match_globalenvs; eauto. intros [bnd MG]. inv MG.
  exists (Vptr b Int.zero); split.
  eapply make_globaladdr_correct; eauto. rewrite symbols_preserved; auto.
  econstructor; eauto. 
Qed.

Lemma var_set_correct:
  forall cenv id rhs a f tf e le te sp lo hi m cs tm tv v m' fn k,
  var_set cenv id rhs = OK a ->
  match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  eval_expr tge (Vptr sp Int.zero) te tm rhs tv ->
  val_inject f v tv ->
  Mem.inject f m tm ->
  exec_assign ge e m id v m' ->
  exists te', exists tm',
    step tge (State fn a k (Vptr sp Int.zero) te tm)
          E0 (State fn Sskip k (Vptr sp Int.zero) te' tm') /\
    Mem.inject f m' tm' /\
    match_callstack f m' tm' (Frame cenv tf e le te' sp lo hi :: cs) (Mem.nextblock m') (Mem.nextblock tm') /\
    (forall id', id' <> for_var id -> te'!id' = te!id').
Proof.
  intros until k. 
  intros VS MCS EVAL VINJ MINJ ASG.
  unfold var_set in VS. inv ASG. 
  assert (NEXTBLOCK: Mem.nextblock m' = Mem.nextblock m).
    eapply Mem.nextblock_store; eauto.
  assert (MV: match_var f id e m te sp cenv!!id).
    inv MCS. inv MENV. auto. 
  revert VS; inv MV; intro VS; inv VS; inv H; try congruence.
  (* var_local *)
  assert (b0 = b) by congruence. subst b0.
  assert (chunk0 = chunk) by congruence. subst chunk0.
  exists (PTree.set (for_var id) tv te); exists tm.
  split. eapply step_assign. eauto. 
  split. eapply Mem.store_unmapped_inject; eauto. 
  split. rewrite NEXTBLOCK. eapply match_callstack_store_local; eauto.
  intros. apply PTree.gso; auto.
  (* var_stack_scalar *)
  assert (b0 = b) by congruence. subst b0.
  assert (chunk0 = chunk) by congruence. subst chunk0.
  assert (Mem.storev chunk m (Vptr b Int.zero) v = Some m'). assumption.
  exploit make_store_correct.
    eapply make_stackaddr_correct.
    eauto. eauto. eauto. eauto. eauto. 
  intros [tm' [tvrhs' [EVAL' [STORE' MEMINJ]]]].
  exists te; exists tm'.
  split. eauto. split. auto.  
  split. rewrite NEXTBLOCK. rewrite (nextblock_storev _ _ _ _ _ STORE'). 
  eapply match_callstack_storev_mapped; eauto.
  auto.
  (* var_global_scalar *)
  simpl in *.
  assert (chunk0 = chunk). exploit H4; eauto. congruence. subst chunk0.  
  assert (Mem.storev chunk m (Vptr b Int.zero) v = Some m'). assumption.
  exploit match_callstack_match_globalenvs; eauto. intros [bnd MG]. inv MG.
  exploit make_store_correct.
    eapply make_globaladdr_correct; eauto.
    rewrite symbols_preserved; eauto. eauto. eauto. eauto. eauto. auto.
  intros [tm' [tvrhs' [EVAL' [STORE' TNEXTBLOCK]]]].
  exists te; exists tm'.
  split. eauto. split. auto. 
  split. rewrite NEXTBLOCK. rewrite (nextblock_storev _ _ _ _ _ STORE'). 
  eapply match_callstack_store_mapped; eauto.
  auto.
Qed.

Lemma match_callstack_extensional:
  forall f cenv tf e le te1 te2 sp lo hi cs bound tbound m tm,
  (forall id chunk, cenv!!id = Var_local chunk -> te2!(for_var id) = te1!(for_var id)) ->
  (forall id v, le!id = Some v -> te2!(for_temp id) = te1!(for_temp id)) ->
  match_callstack f m tm (Frame cenv tf e le te1 sp lo hi :: cs) bound tbound ->
  match_callstack f m tm (Frame cenv tf e le te2 sp lo hi :: cs) bound tbound.
Proof.
  intros. inv H1. constructor; auto. 
  apply match_env_extensional with te1; auto.
Qed.

Lemma var_set_self_correct:
  forall cenv id ty s a f tf e le te sp lo hi m cs tm tv v m' fn k,
  var_set_self cenv id ty s = OK a ->
  match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  val_inject f v tv ->
  Mem.inject f m tm ->
  exec_assign ge e m id v m' ->
  te!(for_var id) = Some tv ->
  exists tm',
    star step tge (State fn a k (Vptr sp Int.zero) te tm)
               E0 (State fn s k (Vptr sp Int.zero) te tm') /\
    Mem.inject f m' tm' /\
    match_callstack f m' tm' (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m') (Mem.nextblock tm').
Proof.
  intros until k. 
  intros VS MCS VINJ MINJ ASG VAL.
  unfold var_set_self in VS. inv ASG. 
  assert (NEXTBLOCK: Mem.nextblock m' = Mem.nextblock m).
    eapply Mem.nextblock_store; eauto.
  assert (MV: match_var f id e m te sp cenv!!id).
    inv MCS. inv MENV. auto.
  assert (EVAR: eval_expr tge (Vptr sp Int.zero) te tm (Evar (for_var id)) tv).
    constructor. auto.
  revert VS; inv MV; intro VS; inv VS; inv H; try congruence.
  (* var_local *)
  assert (b0 = b) by congruence. subst b0.
  assert (chunk0 = chunk) by congruence. subst chunk0.
  exists tm.
  split. apply star_refl. 
  split. eapply Mem.store_unmapped_inject; eauto. 
  rewrite NEXTBLOCK. 
  apply match_callstack_extensional with (PTree.set (for_var id) tv te).
  intros. repeat rewrite PTree.gsspec.
  destruct (peq (for_var id0) (for_var id)). congruence. auto.
  intros. rewrite PTree.gso; auto. unfold for_temp, for_var; congruence.
  eapply match_callstack_store_local; eauto.
  (* var_stack_scalar *)
  assert (b0 = b) by congruence. subst b0.
  assert (chunk0 = chunk) by congruence. subst chunk0.
  assert (Mem.storev chunk m (Vptr b Int.zero) v = Some m'). assumption.
  exploit make_store_correct.
    eapply make_stackaddr_correct.
    eauto. eauto. eauto. eauto. eauto. 
  intros [tm' [tvrhs' [EVAL' [STORE' MEMINJ]]]].
  exists tm'.
  split. eapply star_three. constructor. eauto. constructor. traceEq.
  split. auto.
  rewrite NEXTBLOCK. rewrite (nextblock_storev _ _ _ _ _ STORE'). 
  eapply match_callstack_storev_mapped; eauto.
  (* var_global_scalar *)
  simpl in *.
  assert (chunk0 = chunk). exploit H4; eauto. congruence. subst chunk0.  
  assert (Mem.storev chunk m (Vptr b Int.zero) v = Some m'). assumption.
  exploit match_callstack_match_globalenvs; eauto. intros [bnd MG]. inv MG.
  exploit make_store_correct.
    eapply make_globaladdr_correct; eauto.
    rewrite symbols_preserved; eauto. eauto. eauto. eauto. eauto. eauto.
  intros [tm' [tvrhs' [EVAL' [STORE' MEMINJ]]]].
  exists tm'.
  split. eapply star_three. constructor. eauto. constructor. traceEq.
  split. auto. 
  rewrite NEXTBLOCK. rewrite (nextblock_storev _ _ _ _ _ STORE'). 
  eapply match_callstack_store_mapped; eauto.
Qed.

(*
Lemma var_set_self_correct:
  forall cenv id ty s a f tf e le te sp lo hi m cs tm tv te' v m' fn k,
  var_set_self cenv id ty s = OK a ->
  match_callstack f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  val_inject f v tv ->
  Mem.inject f m tm ->
  exec_assign ge e m id v m' ->
  te'!(for_var id) = Some tv ->
  (forall i, i <> for_var id -> te'!i = te!i) ->
  exists te'', exists tm',
    star step tge (State fn a k (Vptr sp Int.zero) te' tm)
               E0 (State fn s k (Vptr sp Int.zero) te'' tm') /\
    Mem.inject f m' tm' /\
    match_callstack f m' tm' (Frame cenv tf e le te'' sp lo hi :: cs) (Mem.nextblock m') (Mem.nextblock tm') /\
    (forall id', id' <> for_var id -> te''!id' = te'!id').
Proof.
  intros until k. 
  intros VS MCS VINJ MINJ ASG VAL OTHERS.
  unfold var_set_self in VS. inv ASG. 
  assert (NEXTBLOCK: Mem.nextblock m' = Mem.nextblock m).
    eapply Mem.nextblock_store; eauto.
  assert (MV: match_var f id e m te sp cenv!!id).
    inv MCS. inv MENV. auto.
  assert (EVAR: eval_expr tge (Vptr sp Int.zero) te' tm (Evar (for_var id)) tv).
    constructor. auto.
  revert VS; inv MV; intro VS; inv VS; inv H; try congruence.
  (* var_local *)
  assert (b0 = b) by congruence. subst b0.
  assert (chunk0 = chunk) by congruence. subst chunk0.
  exists te'; exists tm.
  split. apply star_refl. 
  split. eapply Mem.store_unmapped_inject; eauto. 
  split. rewrite NEXTBLOCK. 
  apply match_callstack_extensional with (PTree.set (for_var id) tv te).
  intros. repeat rewrite PTree.gsspec.
  destruct (peq (for_var id0) (for_var id)). congruence. auto.
  intros. assert (for_temp id0 <> for_var id). unfold for_temp, for_var; congruence.
  rewrite PTree.gso; auto. 
  eapply match_callstack_store_local; eauto.
  intros. auto. 
  (* var_stack_scalar *)
  assert (b0 = b) by congruence. subst b0.
  assert (chunk0 = chunk) by congruence. subst chunk0.
  assert (Mem.storev chunk m (Vptr b Int.zero) v = Some m'). assumption.
  exploit make_store_correct.
    eapply make_stackaddr_correct.
    eauto. eauto. eauto. eauto. eauto. 
  intros [tm' [tvrhs' [EVAL' [STORE' MEMINJ]]]].
  exists te'; exists tm'.
  split. eapply star_three. constructor. eauto. constructor. traceEq.
  split. auto.
  split. rewrite NEXTBLOCK. rewrite (nextblock_storev _ _ _ _ _ STORE'). 
  apply match_callstack_extensional with te.
  intros. apply OTHERS. unfold for_var; congruence.
  intros. apply OTHERS. unfold for_var, for_temp; congruence.
  eapply match_callstack_storev_mapped; eauto.
  auto.
  (* var_global_scalar *)
  simpl in *.
  assert (chunk0 = chunk). exploit H4; eauto. congruence. subst chunk0.  
  assert (Mem.storev chunk m (Vptr b Int.zero) v = Some m'). assumption.
  exploit match_callstack_match_globalenvs; eauto. intros [bnd MG]. inv MG.
  exploit make_store_correct.
    eapply make_globaladdr_correct; eauto.
    rewrite symbols_preserved; eauto. eauto. eauto. eauto. eauto. eauto.
  intros [tm' [tvrhs' [EVAL' [STORE' MEMINJ]]]].
  exists te'; exists tm'.
  split. eapply star_three. constructor. eauto. constructor. traceEq.
  split. auto. 
  split. rewrite NEXTBLOCK. rewrite (nextblock_storev _ _ _ _ _ STORE'). 
  apply match_callstack_extensional with te.
  intros. apply OTHERS. unfold for_var; congruence.
  intros. apply OTHERS. unfold for_var, for_temp; congruence.
  eapply match_callstack_store_mapped; eauto.
  auto.
Qed.
*)

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

Remark assign_variable_incr:
  forall atk id lv cenv sz cenv' sz',
  assign_variable atk (id, lv) (cenv, sz) = (cenv', sz') -> sz <= sz'.
Proof.
  intros until sz'; simpl.
  destruct lv. case (Identset.mem id atk); intros.
  inv H.  generalize (size_chunk_pos m). intro.
  generalize (align_le sz (size_chunk m) H). omega.
  inv H. omega.
  intros. inv H. 
  generalize (align_le sz (array_alignment z) (array_alignment_pos z)).
  assert (0 <= Zmax 0 z). apply Zmax_bound_l. omega.
  omega.
Qed.


Remark assign_variables_incr:
  forall atk vars cenv sz cenv' sz',
  assign_variables atk vars (cenv, sz) = (cenv', sz') -> sz <= sz'.
Proof.
  induction vars; intros until sz'.
  simpl; intros. replace sz' with sz. omega. congruence.
Opaque assign_variable.
  destruct a as [id lv]. simpl. 
  case_eq (assign_variable atk (id, lv) (cenv, sz)). intros cenv1 sz1 EQ1 EQ2.
  apply Zle_trans with sz1. eapply assign_variable_incr; eauto. eauto.
Transparent assign_variable.
Qed.

Remark inj_offset_aligned_array:
  forall stacksize sz,
  Mem.inj_offset_aligned (align stacksize (array_alignment sz)) sz.
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
  Mem.inj_offset_aligned (align stacksize (array_alignment sz)) (Zmax 0 sz).
Proof.
  intros. 
  replace (array_alignment sz) with (array_alignment (Zmax 0 sz)).
  apply inj_offset_aligned_array. 
  rewrite Zmax_spec. destruct (zlt sz 0); auto.
  transitivity 1. reflexivity. unfold array_alignment. rewrite zlt_true. auto. omega.
Qed.

Remark inj_offset_aligned_var:
  forall stacksize chunk,
  Mem.inj_offset_aligned (align stacksize (size_chunk chunk)) (size_chunk chunk).
Proof.
  intros.
  replace (align stacksize (size_chunk chunk))
     with (align stacksize (array_alignment (size_chunk chunk))).
  apply inj_offset_aligned_array.
  decEq. destruct chunk; reflexivity.
Qed.

Lemma match_callstack_alloc_variable:
  forall atk id lv cenv sz cenv' sz' tm sp e tf m m' b te le lo cs f tv,
  assign_variable atk (id, lv) (cenv, sz) = (cenv', sz') ->
  Mem.valid_block tm sp ->
  Mem.bounds tm sp = (0, tf.(fn_stackspace)) ->
  Mem.range_perm tm sp 0 tf.(fn_stackspace) Freeable ->
  tf.(fn_stackspace) <= Int.max_signed ->
  Mem.alloc m 0 (sizeof lv) = (m', b) ->
  match_callstack f m tm 
                  (Frame cenv tf e le te sp lo (Mem.nextblock m) :: cs)
                  (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.inject f m tm ->
  0 <= sz -> sz' <= tf.(fn_stackspace) ->
  (forall b delta, f b = Some(sp, delta) -> Mem.high_bound m b + delta <= sz) ->
  e!id = None ->
  te!(for_var id) = Some tv ->
  exists f',
     inject_incr f f'
  /\ Mem.inject f' m' tm
  /\ match_callstack f' m' tm
                     (Frame cenv' tf (PTree.set id (b, lv) e) le te sp lo (Mem.nextblock m') :: cs)
                     (Mem.nextblock m') (Mem.nextblock tm)
  /\ (forall b delta,
      f' b = Some(sp, delta) -> Mem.high_bound m' b + delta <= sz').
Proof.
  intros until tv. intros ASV VALID BOUNDS PERMS NOOV ALLOC MCS INJ LO HI RANGE E TE.
  generalize ASV. unfold assign_variable. 
  caseEq lv.
  (* 1. lv = LVscalar chunk *)
  intros chunk LV. case (Identset.mem id atk).
  (* 1.1 info = Var_stack_scalar chunk ofs *)
    set (ofs := align sz (size_chunk chunk)).
    intro EQ; injection EQ; intros; clear EQ. rewrite <- H0.
    generalize (size_chunk_pos chunk); intro SIZEPOS.
    generalize (align_le sz (size_chunk chunk) SIZEPOS). fold ofs. intro SZOFS.
    exploit Mem.alloc_left_mapped_inject.
      eauto. eauto. eauto. 
      instantiate (1 := ofs). 
      generalize Int.min_signed_neg. omega.
      right; rewrite BOUNDS; simpl. generalize Int.min_signed_neg. omega.
      intros. apply Mem.perm_implies with Freeable; auto with mem.
      apply PERMS. rewrite LV in H1. simpl in H1. omega.
      rewrite LV; simpl. rewrite Zminus_0_r. unfold ofs. 
      apply inj_offset_aligned_var.
      intros. generalize (RANGE _ _ H1). omega. 
    intros [f1 [MINJ1 [INCR1 [SAME OTHER]]]].
    exists f1; split. auto. split. auto. split. 
    eapply match_callstack_alloc_left; eauto.
    rewrite <- LV; auto. 
    rewrite SAME; constructor.
    intros. rewrite (Mem.bounds_alloc _ _ _ _ _ ALLOC). 
    destruct (eq_block b0 b); simpl.
    subst b0. assert (delta = ofs) by congruence. subst delta.  
    rewrite LV. simpl. omega.
    rewrite OTHER in H1; eauto. generalize (RANGE _ _ H1). omega. 
  (* 1.2 info = Var_local chunk *)
    intro EQ; injection EQ; intros; clear EQ. subst sz'. rewrite <- H0.
    exploit Mem.alloc_left_unmapped_inject; eauto.
    intros [f1 [MINJ1 [INCR1 [SAME OTHER]]]].
    exists f1; split. auto. split. auto. split.
    eapply match_callstack_alloc_left; eauto. 
    rewrite <- LV; auto.
    rewrite SAME; constructor.
    intros. rewrite (Mem.bounds_alloc _ _ _ _ _ ALLOC). 
    destruct (eq_block b0 b); simpl.
    subst b0. congruence.
    rewrite OTHER in H; eauto.
  (* 2 info = Var_stack_array ofs *)
  intros dim LV EQ. injection EQ; clear EQ; intros. rewrite <- H0.
  assert (0 <= Zmax 0 dim). apply Zmax1. 
  generalize (align_le sz (array_alignment dim) (array_alignment_pos dim)). intro.
  set (ofs := align sz (array_alignment dim)) in *.
  exploit Mem.alloc_left_mapped_inject. eauto. eauto. eauto. 
    instantiate (1 := ofs). 
    generalize Int.min_signed_neg. omega.
    right; rewrite BOUNDS; simpl. generalize Int.min_signed_neg. omega.
    intros. apply Mem.perm_implies with Freeable; auto with mem.
    apply PERMS. rewrite LV in H3. simpl in H3. omega.
    rewrite LV; simpl. rewrite Zminus_0_r. unfold ofs. 
    apply inj_offset_aligned_array'.
    intros. generalize (RANGE _ _ H3). omega. 
  intros [f1 [MINJ1 [INCR1 [SAME OTHER]]]].
  exists f1; split. auto. split. auto. split. 
  eapply match_callstack_alloc_left; eauto.
  rewrite <- LV; auto. 
  rewrite SAME; constructor.
  intros. rewrite (Mem.bounds_alloc _ _ _ _ _ ALLOC). 
  destruct (eq_block b0 b); simpl.
  subst b0. assert (delta = ofs) by congruence. subst delta. 
  rewrite LV. simpl. omega.
  rewrite OTHER in H3; eauto. generalize (RANGE _ _ H3). omega. 
Qed.

Lemma match_callstack_alloc_variables_rec:
  forall tm sp cenv' tf le te lo cs atk,
  Mem.valid_block tm sp ->
  Mem.bounds tm sp = (0, tf.(fn_stackspace)) ->
  Mem.range_perm tm sp 0 tf.(fn_stackspace) Freeable ->
  tf.(fn_stackspace) <= Int.max_signed ->
  forall e m vars e' m',
  alloc_variables e m vars e' m' ->
  forall f cenv sz,
  assign_variables atk vars (cenv, sz) = (cenv', tf.(fn_stackspace)) ->
  match_callstack f m tm 
                  (Frame cenv tf e le te sp lo (Mem.nextblock m) :: cs)
                  (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.inject f m tm ->
  0 <= sz ->
  (forall b delta,
     f b = Some(sp, delta) -> Mem.high_bound m b + delta <= sz) ->
  (forall id lv, In (id, lv) vars -> te!(for_var id) <> None) ->
  list_norepet (List.map (@fst ident var_kind) vars) ->
  (forall id lv, In (id, lv) vars -> e!id = None) ->
  exists f',
     inject_incr f f'
  /\ Mem.inject f' m' tm
  /\ match_callstack f' m' tm
                     (Frame cenv' tf e' le te sp lo (Mem.nextblock m') :: cs)
                     (Mem.nextblock m') (Mem.nextblock tm).
Proof.
  intros until atk. intros VALID BOUNDS PERM NOOV.
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
  assert (DEFINED1: forall id0 lv0, In (id0, lv0) vars -> te!(for_var id0) <> None).
    intros. eapply DEFINED. simpl. right. eauto.
  assert (exists tv, te!(for_var id) = Some tv).
    assert (te!(for_var id) <> None). eapply DEFINED. simpl; left; auto.
    destruct (te!(for_var id)). exists v; auto. congruence.
  destruct H1 as [tv TEID].
  assert (sz1 <= fn_stackspace tf). eapply assign_variables_incr; eauto. 
  exploit match_callstack_alloc_variable; eauto with coqlib.
  intros [f1 [INCR1 [INJ1 [MCS1 BOUND1]]]].
  exploit IHalloc_variables; eauto. 
  apply Zle_trans with sz; auto. eapply assign_variable_incr; eauto.
  inv NOREPET; auto.
  intros. rewrite PTree.gso. eapply UNDEFINED; eauto with coqlib.
  simpl in NOREPET. inversion NOREPET. red; intro; subst id0.
  elim H5. change id with (fst (id, lv0)). apply List.in_map. auto.
  intros [f2 [INCR2 [INJ2 MCS2]]].
  exists f2; intuition. eapply inject_incr_trans; eauto. 
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
  forall fn cenv tf m e m' tm tm' sp f cs targs,
  build_compilenv gce fn = (cenv, tf.(fn_stackspace)) ->
  tf.(fn_stackspace) <= Int.max_signed ->
  list_norepet (fn_params_names fn ++ fn_vars_names fn) ->
  alloc_variables Csharpminor.empty_env m (fn_variables fn) e m' ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm', sp) ->
  match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.inject f m tm ->
  let tparams := List.map for_var (fn_params_names fn) in
  let tvars := List.map for_var (fn_vars_names fn) in
  let ttemps := List.map for_temp (Csharpminor.fn_temps fn) in
  let te := set_locals (tvars ++ ttemps) (set_params targs tparams) in
  exists f',
     inject_incr f f'
  /\ Mem.inject f' m' tm'
  /\ match_callstack f' m' tm'
                     (Frame cenv tf e empty_temp_env te sp (Mem.nextblock m) (Mem.nextblock m') :: cs)
                     (Mem.nextblock m') (Mem.nextblock tm').
Proof.
  intros. 
  unfold build_compilenv in H. 
  eapply match_callstack_alloc_variables_rec; eauto with mem.
  eapply Mem.bounds_alloc_same; eauto.
  red; intros; eauto with mem.
  eapply match_callstack_alloc_right; eauto.
  eapply Mem.alloc_right_inject; eauto. omega. 
  intros. elim (Mem.valid_not_valid_diff tm sp sp); eauto with mem.
  eapply Mem.valid_block_inject_2; eauto.
  intros. unfold te. apply set_locals_params_defined.
  elim (in_app_or _ _ _ H6); intros.
  elim (list_in_map_inv _ _ _ H7). intros x [A B].
  apply in_or_app; left. unfold tparams. apply List.in_map. inversion A. apply List.in_map. auto.
  apply in_or_app; right. apply in_or_app; left. unfold tvars. apply List.in_map. 
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

Inductive vars_vals_match (f:meminj):
             list (ident * memory_chunk) -> list val -> env -> Prop :=
  | vars_vals_nil:
      forall te,
      vars_vals_match f nil nil te
  | vars_vals_cons:
      forall te id chunk vars v vals tv,
      te!(for_var id) = Some tv ->
      val_inject f v tv ->
      val_normalized v chunk ->
      vars_vals_match f vars vals te ->
      vars_vals_match f ((id, chunk) :: vars) (v :: vals) te.

Lemma vars_vals_match_extensional:
  forall f vars vals te,
  vars_vals_match f vars vals te ->
  forall te',
  (forall id lv, In (id, lv) vars -> te'!(for_var id) = te!(for_var id)) ->
  vars_vals_match f vars vals te'.
Proof.
  induction 1; intros.
  constructor.
  econstructor; eauto. 
  rewrite <- H. eauto with coqlib. 
  apply IHvars_vals_match. intros. eapply H3; eauto with coqlib.
Qed.

Lemma store_parameters_correct:
  forall e le te m1 params vl m2,
  bind_parameters e m1 params vl m2 ->
  forall s f cenv tf sp lo hi cs tm1 fn k,
  vars_vals_match f params vl te ->
  list_norepet (List.map param_name params) ->
  Mem.inject f m1 tm1 ->
  match_callstack f m1 tm1 (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m1) (Mem.nextblock tm1) ->
  store_parameters cenv params = OK s ->
  exists tm2,
     star step tge (State fn s k (Vptr sp Int.zero) te tm1)
                E0 (State fn Sskip k (Vptr sp Int.zero) te tm2)
  /\ Mem.inject f m2 tm2
  /\ match_callstack f m2 tm2 (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m2) (Mem.nextblock tm2).
Proof.
  induction 1.
  (* base case *)
  intros; simpl. monadInv H3.
  exists tm1. split. constructor. tauto.
  (* inductive case *)
  intros until k.  intros VVM NOREPET MINJ MATCH STOREP.
  monadInv STOREP.
  inv VVM. 
  inv NOREPET.
  exploit var_set_self_correct; eauto.
    econstructor; eauto. econstructor; eauto.
  intros [tm2 [EXEC1 [MINJ1 MATCH1]]].
  exploit IHbind_parameters; eauto.
  intros [tm3 [EXEC2 [MINJ2 MATCH2]]].
  exists tm3.
  split. eapply star_trans; eauto. 
  auto.
Qed.

Lemma vars_vals_match_holds_1:
  forall f params args targs,
  list_norepet (List.map param_name params) ->
  val_list_inject f args targs ->
  list_forall2 val_normalized args (List.map param_chunk params) ->
  vars_vals_match f params args
    (set_params targs (List.map for_var (List.map param_name params))).
Proof.
Opaque for_var.
  induction params; simpl; intros.
  inv H1. constructor.
  inv H. inv H1. inv H0. 
  destruct a as [id chunk]; simpl in *. econstructor.
  rewrite PTree.gss. reflexivity. 
  auto. auto.
  apply vars_vals_match_extensional
  with (set_params vl' (map for_var (map param_name params))).
  eapply IHparams; eauto. 
Transparent for_var.
  intros. apply PTree.gso. unfold for_var; red; intros. inv H0. 
  elim H4. change id with (param_name (id, lv)). apply List.in_map; auto.
Qed.

Lemma vars_vals_match_holds_2:
  forall f params args e,
  vars_vals_match f params args e ->
  forall vl,
  (forall id1 id2, In id1 (List.map param_name params) -> In id2 vl -> for_var id1 <> id2) ->
  vars_vals_match f params args (set_locals vl e).
Proof.
  induction vl; simpl; intros.
  auto.
  apply vars_vals_match_extensional with (set_locals vl e); auto. 
  intros. apply PTree.gso. apply H0. 
  change id with (param_name (id, lv)). apply List.in_map. auto.
  auto.
Qed.

Lemma vars_vals_match_holds:
  forall f params args targs vars temps,
  list_norepet (List.map param_name params ++ vars) ->
  val_list_inject f args targs ->
  list_forall2 val_normalized args (List.map param_chunk params) ->
  vars_vals_match f params args
    (set_locals (List.map for_var vars ++ List.map for_temp temps)
      (set_params targs (List.map for_var (List.map param_name params)))).
Proof.
  intros. rewrite list_norepet_app in H. destruct H as [A [B C]].
  apply vars_vals_match_holds_2; auto. apply vars_vals_match_holds_1; auto.
  intros.
  destruct (in_app_or _ _ _ H2).
  exploit list_in_map_inv. eexact H3. intros [x2 [J K]].
  subst. assert (id1 <> x2). apply C; auto. unfold for_var; congruence.
  exploit list_in_map_inv. eexact H3. intros [x2 [J K]].
  subst id2. unfold for_var, for_temp; congruence.
Qed.

Remark bind_parameters_normalized:
  forall e m params args m',
  bind_parameters e m params args m' ->
  list_forall2 val_normalized args (List.map param_chunk params).
Proof.
  induction 1; simpl.
  constructor.
  constructor; auto.
Qed.

(** The main result in this section: the behaviour of function entry
  in the generated Cminor code (allocate stack data block and store
  parameters whose address is taken) simulates what happens at function
  entry in the original Csharpminor (allocate one block per local variable
  and initialize the blocks corresponding to function parameters). *)

Lemma function_entry_ok:
  forall fn m e m1 vargs m2 f cs tm cenv tf tm1 sp tvargs s fn' k,
  list_norepet (fn_params_names fn ++ fn_vars_names fn) ->
  alloc_variables empty_env m (fn_variables fn) e m1 ->
  bind_parameters e m1 fn.(Csharpminor.fn_params) vargs m2 ->
  match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm) ->
  build_compilenv gce fn = (cenv, tf.(fn_stackspace)) ->
  tf.(fn_stackspace) <= Int.max_signed ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm1, sp) ->
  let tparams := List.map for_var (fn_params_names fn) in
  let tvars := List.map for_var (fn_vars_names fn) in
  let ttemps := List.map for_temp (Csharpminor.fn_temps fn) in
  let te := set_locals (tvars ++ ttemps) (set_params tvargs tparams) in
  val_list_inject f vargs tvargs ->
  Mem.inject f m tm ->
  store_parameters cenv fn.(Csharpminor.fn_params) = OK s ->
  exists f2, exists tm2,
     star step tge (State fn' s k (Vptr sp Int.zero) te tm1)
                E0 (State fn' Sskip k (Vptr sp Int.zero) te tm2)
  /\ Mem.inject f2 m2 tm2
  /\ inject_incr f f2
  /\ match_callstack f2 m2 tm2
       (Frame cenv tf e empty_temp_env te sp (Mem.nextblock m) (Mem.nextblock m1) :: cs)
       (Mem.nextblock m2) (Mem.nextblock tm2).
Proof.
  intros.
  exploit match_callstack_alloc_variables; eauto.
  intros [f1 [INCR1 [MINJ1 MATCH1]]].
  exploit vars_vals_match_holds.
    eexact H. 
    apply val_list_inject_incr with f. eauto. eauto.
    eapply bind_parameters_normalized; eauto.
  instantiate (1 := Csharpminor.fn_temps fn). 
  fold tvars. fold ttemps. fold (fn_params_names fn). fold tparams. fold te.   
  intro VVM.
  exploit store_parameters_correct.
    eauto. eauto. eapply list_norepet_append_left; eauto.
    eexact MINJ1. eexact MATCH1. eauto.
  intros [tm2 [EXEC [MINJ2 MATCH2]]].
  exists f1; exists tm2. eauto. 
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
  forall f m tm cenv tf e le te sp lo hi cs
    (MINJ: Mem.inject f m tm)
    (MATCH: match_callstack f m tm
             (Frame cenv tf e le te sp lo hi :: cs)
             (Mem.nextblock m) (Mem.nextblock tm)),
  forall a v,
  Csharpminor.eval_expr ge e le m a v ->
  forall ta
    (TR: transl_expr cenv a = OK ta),
  exists tv,
     eval_expr tge (Vptr sp Int.zero) te tm ta tv
  /\ val_inject f v tv.
Proof.
  induction 3; intros; simpl in TR; try (monadInv TR).
  (* Evar *)
  eapply var_get_correct; eauto.
  (* Etempvar *)
  inv MATCH. inv MENV. exploit me_temps0; eauto. intros [tv [A B]]. 
  exists tv; split; auto. constructor; auto.
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
  exploit Mem.loadv_inject; eauto. intros [tv [LOAD INJ]].
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
  exploit transl_expr_correct; eauto. intros [tv1 [EVAL1 VINJ1]].
  exploit IHeval_exprlist; eauto. intros [tv2 [EVAL2 VINJ2]].
  exists (tv1 :: tv2); split. constructor; auto. constructor; auto.
Qed.

(** ** Semantic preservation for statements and functions *)

Inductive match_cont: Csharpminor.cont -> Cminor.cont -> option typ -> compilenv -> exit_env -> callstack -> Prop :=
  | match_Kstop: forall ty cenv xenv,
      match_cont Csharpminor.Kstop Kstop ty cenv xenv nil
  | match_Kseq: forall s k ts tk ty cenv xenv cs,
      transl_stmt ty cenv xenv s = OK ts ->
      match_cont k tk ty cenv xenv cs ->
      match_cont (Csharpminor.Kseq s k) (Kseq ts tk) ty cenv xenv cs
  | match_Kseq2: forall s1 s2 k ts1 tk ty cenv xenv cs,
      transl_stmt ty cenv xenv s1 = OK ts1 ->
      match_cont (Csharpminor.Kseq s2 k) tk ty cenv xenv cs ->
      match_cont (Csharpminor.Kseq (Csharpminor.Sseq s1 s2) k)
                 (Kseq ts1 tk) ty cenv xenv cs
  | match_Kblock: forall k tk ty cenv xenv cs,
      match_cont k tk ty cenv xenv cs ->
      match_cont (Csharpminor.Kblock k) (Kblock tk) ty cenv (true :: xenv) cs
  | match_Kblock2: forall k tk ty cenv xenv cs,
      match_cont k tk ty cenv xenv cs ->
      match_cont k (Kblock tk) ty cenv (false :: xenv) cs
  | match_Kcall: forall optid fn e le k tfn sp te tk ty cenv xenv lo hi cs sz cenv',
      transl_funbody cenv sz fn = OK tfn ->
      match_cont k tk fn.(fn_return) cenv xenv cs ->
      match_cont (Csharpminor.Kcall optid fn e le k)
                 (Kcall (option_map for_temp optid) tfn (Vptr sp Int.zero) te tk)
                 ty cenv' nil
                 (Frame cenv tfn e le te sp lo hi :: cs).

Inductive match_states: Csharpminor.state -> Cminor.state -> Prop :=
  | match_state:
      forall fn s k e le m tfn ts tk sp te tm cenv xenv f lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt fn.(fn_return) cenv xenv s = OK ts)
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack f m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk fn.(fn_return) cenv xenv cs),
      match_states (Csharpminor.State fn s k e le m)
                   (State tfn ts tk (Vptr sp Int.zero) te tm)
  | match_state_seq:
      forall fn s1 s2 k e le m tfn ts1 tk sp te tm cenv xenv f lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt fn.(fn_return) cenv xenv s1 = OK ts1)
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack f m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont (Csharpminor.Kseq s2 k) tk fn.(fn_return) cenv xenv cs),
      match_states (Csharpminor.State fn (Csharpminor.Sseq s1 s2) k e le m)
                   (State tfn ts1 tk (Vptr sp Int.zero) te tm)
  | match_callstate:
      forall fd args k m tfd targs tk tm f cs cenv
      (TR: transl_fundef gce fd = OK tfd)
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk (Csharpminor.funsig fd).(sig_res) cenv nil cs)
      (ISCC: Csharpminor.is_call_cont k)
      (ARGSINJ: val_list_inject f args targs),
      match_states (Csharpminor.Callstate fd args k m)
                   (Callstate tfd targs tk tm)
  | match_returnstate:
      forall v k m tv tk tm f cs ty cenv
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack f m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk ty cenv nil cs)
      (RESINJ: val_inject f v tv),
      match_states (Csharpminor.Returnstate v k m)
                   (Returnstate tv tk tm).

Remark val_inject_function_pointer:
  forall bound v fd f tv,
  Genv.find_funct tge v = Some fd ->
  match_globalenvs f bound ->
  val_inject f v tv ->
  tv = v.
Proof.
  intros. exploit Genv.find_funct_inv; eauto. intros [b EQ]. subst v.
  rewrite Genv.find_funct_find_funct_ptr in H. 
  assert (b < 0). unfold tge in H. eapply Genv.find_funct_ptr_negative; eauto.
  assert (f b = Some(b, 0)). inv H0. apply DOMAIN. omega.  
  inv H1. rewrite H3 in H6; inv H6. reflexivity.
Qed.

Lemma match_call_cont:
  forall k tk ty cenv xenv cs,
  match_cont k tk ty cenv xenv cs ->
  match_cont (Csharpminor.call_cont k) (call_cont tk) ty cenv nil cs.
Proof.
  induction 1; simpl; auto; econstructor; eauto.
Qed.

Lemma match_is_call_cont:
  forall tfn te sp tm k tk ty cenv xenv cs,
  match_cont k tk ty cenv xenv cs ->
  Csharpminor.is_call_cont k ->
  exists tk',
    star step tge (State tfn Sskip tk sp te tm)
               E0 (State tfn Sskip tk' sp te tm)
    /\ is_call_cont tk'
    /\ match_cont k tk' ty cenv nil cs.
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

Inductive transl_lblstmt_cont (ty: option typ) (cenv: compilenv) (xenv: exit_env): lbl_stmt -> cont -> cont -> Prop :=
  | tlsc_default: forall s k ts,
      transl_stmt ty cenv (switch_env (LSdefault s) xenv) s = OK ts ->
      transl_lblstmt_cont ty cenv xenv (LSdefault s) k (Kblock (Kseq ts k))
  | tlsc_case: forall i s ls k ts k',
      transl_stmt ty cenv (switch_env (LScase i s ls) xenv) s = OK ts ->
      transl_lblstmt_cont ty cenv xenv ls k k' ->
      transl_lblstmt_cont ty cenv xenv (LScase i s ls) k (Kblock (Kseq ts k')).

Lemma switch_descent:
  forall ty cenv xenv k ls body s,
  transl_lblstmt ty cenv (switch_env ls xenv) ls body = OK s ->
  exists k',
  transl_lblstmt_cont ty cenv xenv ls k k'
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
  forall f n sp e m ty cenv xenv k ls k1,
  let tbl := switch_table ls O in
  let ls' := select_switch n ls in
  transl_lblstmt_cont ty cenv xenv ls k k1 ->
  exists k2,
  star step tge (State f (Sexit (switch_target n (length tbl) tbl)) k1 sp e m)
             E0 (State f (Sexit O) k2 sp e m)
  /\ transl_lblstmt_cont ty cenv xenv ls' k k2.
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
  forall ty cenv xenv k cs tk ls tk',
  match_cont k tk ty cenv xenv cs ->
  transl_lblstmt_cont ty cenv xenv ls tk tk' ->
  match_cont (Csharpminor.Kseq (seq_of_lbl_stmt ls) k) tk' ty cenv (false :: switch_env ls xenv) cs.
Proof.
  induction ls; intros; simpl.
  inv H0. apply match_Kblock2. econstructor; eauto.
  inv H0. apply match_Kblock2. eapply match_Kseq2. auto. eauto. 
Qed.

Lemma transl_lblstmt_suffix:
  forall n ty cenv xenv ls body ts,
  transl_lblstmt ty cenv (switch_env ls xenv) ls body = OK ts ->
  let ls' := select_switch n ls in
  exists body', exists ts',
  transl_lblstmt ty cenv (switch_env ls' xenv) ls' body' = OK ts'.
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
    (TR: transl_lblstmt (fn_return fn) cenv (switch_env ls xenv) ls body = OK ts)
    (MINJ: Mem.inject f m tm)
    (MCS: match_callstack f m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
    (MK: match_cont k tk (fn_return fn) cenv xenv cs)
    (TK: transl_lblstmt_cont (fn_return fn) cenv xenv ls tk tk'),
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
Variable ty: option typ.
Variable cenv: compilenv.
Variable cs: callstack.

Remark find_label_var_set:
  forall id e s k,
  var_set cenv id e = OK s ->
  find_label lbl s k = None.
Proof.
  intros. unfold var_set in H.
  destruct (cenv!!id); try (monadInv H; reflexivity).
Qed.

Remark find_label_var_set_self:
  forall id ty s0 s k,
  var_set_self cenv id ty s0 = OK s ->
  find_label lbl s k = find_label lbl s0 k.
Proof.
  intros. unfold var_set_self in H.
  destruct (cenv!!id); try (monadInv H; reflexivity).
Qed.

Lemma transl_lblstmt_find_label_context:
  forall xenv ls body ts tk1 tk2 ts' tk',
  transl_lblstmt ty cenv (switch_env ls xenv) ls body = OK ts ->
  transl_lblstmt_cont ty cenv xenv ls tk1 tk2 ->
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
  transl_stmt ty cenv xenv s = OK ts ->
  match_cont k tk ty cenv xenv cs ->
  match Csharpminor.find_label lbl s k with
  | None => find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', exists xenv',
        find_label lbl ts tk = Some(ts', tk')
     /\ transl_stmt ty cenv xenv' s' = OK ts'
     /\ match_cont k' tk' ty cenv xenv' cs
  end

with transl_lblstmt_find_label:
  forall ls xenv body k ts tk tk1,
  transl_lblstmt ty cenv (switch_env ls xenv) ls body = OK ts ->
  match_cont k tk ty cenv xenv cs ->
  transl_lblstmt_cont ty cenv xenv ls tk tk1 ->
  find_label lbl body tk1 = None ->
  match Csharpminor.find_label_ls lbl ls k with
  | None => find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', exists xenv',
        find_label lbl ts tk = Some(ts', tk')
     /\ transl_stmt ty cenv xenv' s' = OK ts'
     /\ match_cont k' tk' ty cenv xenv' cs
  end.
Proof.
  intros. destruct s; try (monadInv H); simpl; auto.
  (* assign *)
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
  transitivity (find_label lbl x k). eapply find_label_var_set_self; eauto. eauto.
Qed.

End FIND_LABEL.

Lemma transl_find_label_body:
  forall cenv xenv size f tf k tk cs lbl s' k',
  transl_funbody cenv size f = OK tf ->
  match_cont k tk (fn_return f) cenv xenv cs ->
  Csharpminor.find_label lbl f.(Csharpminor.fn_body) (Csharpminor.call_cont k) = Some (s', k') ->
  exists ts', exists tk', exists xenv',
     find_label lbl tf.(fn_body) (call_cont tk) = Some(ts', tk')
  /\ transl_stmt (fn_return f) cenv xenv' s' = OK ts'
  /\ match_cont k' tk' (fn_return f) cenv xenv' cs.
Proof.
  intros. monadInv H. simpl. 
  rewrite (find_label_store_parameters lbl cenv (Csharpminor.fn_params f)); auto.
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
  eapply plus_right. eexact A. apply step_skip_call. auto.
  rewrite (sig_preserved_body _ _ _ _ TRF). auto. eauto. traceEq.
  econstructor; eauto.

(* assign *)
  monadInv TR. 
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  exploit var_set_correct; eauto. 
  intros [te' [tm' [EXEC [MINJ' [MCS' OTHER]]]]].
  left; econstructor; split.
  apply plus_one. eexact EXEC.
  econstructor; eauto.

(* set *)
  monadInv TR.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  left; econstructor; split.
  apply plus_one. econstructor; eauto. 
  econstructor; eauto. 
  eapply match_callstack_set_temp; eauto. 

(* store *)
  monadInv TR.
  exploit transl_expr_correct. eauto. eauto. eexact H. eauto. 
  intros [tv1 [EVAL1 VINJ1]].
  exploit transl_expr_correct. eauto. eauto. eexact H0. eauto. 
  intros [tv2 [EVAL2 VINJ2]].
  exploit make_store_correct. eexact EVAL1. eexact EVAL2. eauto. eauto. auto. auto.
  intros [tm' [tv' [EXEC [STORE' MINJ']]]].
  left; econstructor; split.
  apply plus_one. eexact EXEC.
  econstructor; eauto.
  eapply match_callstack_storev_mapped. eexact VINJ1. eauto. eauto.
  rewrite (nextblock_storev _ _ _ _ _ H1).
  rewrite (nextblock_storev _ _ _ _ _ STORE').
  eauto. 

(* call *)
  simpl in H1. exploit functions_translated; eauto. intros [tfd [FIND TRANS]].
  monadInv TR.
  exploit transl_expr_correct; eauto. intros [tvf [EVAL1 VINJ1]].
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
  exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  econstructor; split.
  apply plus_one. eapply step_return_0. eauto.
  econstructor; eauto. eapply match_call_cont; eauto.
  simpl; auto.

(* return some *)
  monadInv TR. left. 
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
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
  caseEq (build_compilenv gce f). intros ce sz BC.
  destruct (zle sz Int.max_signed); try congruence.
  intro TRBODY.
  generalize TRBODY; intro TMP. monadInv TMP.
  set (tf := mkfunction (Csharpminor.fn_sig f) 
                        (List.map for_var (fn_params_names f))
                        (List.map for_var (fn_vars_names f)
                         ++ List.map for_temp (Csharpminor.fn_temps f))
                        sz
                        (Sseq x1 x0)) in *.
  caseEq (Mem.alloc tm 0 (fn_stackspace tf)). intros tm' sp ALLOC'.
  exploit function_entry_ok; eauto; simpl; auto.  
  intros [f2 [tm2 [EXEC [MINJ2 [IINCR MCS2]]]]].
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
  exploit match_callstack_match_globalenvs; eauto. intros [hi MG].
  exploit external_call_mem_inject; eauto. 
  eapply inj_preserves_globals; eauto.
  intros [f' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH [INCR SEPARATED]]]]]]]]].
  left; econstructor; split.
  apply plus_one. econstructor.
  eapply external_call_symbols_preserved_2; eauto.
  exact symbols_preserved.
  eexact (Genv.find_var_info_transf_partial2 (transl_fundef gce) transl_globvar _ TRANSL).
  eexact (Genv.find_var_info_rev_transf_partial2 (transl_fundef gce) transl_globvar _ TRANSL).
  econstructor; eauto.
  apply match_callstack_incr_bound with (Mem.nextblock m) (Mem.nextblock tm).
  eapply match_callstack_external_call; eauto.
  intros. eapply external_call_bounds; eauto.
  omega. omega.
  eapply external_call_nextblock_incr; eauto.
  eapply external_call_nextblock_incr; eauto.

(* return *)
  inv MK. simpl.
  left; econstructor; split.
  apply plus_one. econstructor; eauto. 
  unfold set_optvar. destruct optid; simpl option_map; econstructor; eauto.
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
  apply (Genv.init_mem_transf_partial2 _ _ _ TRANSL). eauto. 
  simpl. fold tge. rewrite symbols_preserved.
  replace (prog_main tprog) with (prog_main prog). eexact H0.
  symmetry. unfold transl_program in TRANSL.
  eapply transform_partial_program2_main; eauto.
  eexact FIND. 
  rewrite <- H2. apply sig_preserved; auto.
  eapply match_callstate with (f := Mem.flat_inj (Mem.nextblock m0)) (cs := @nil frame).
  auto.
  eapply Genv.initmem_inject; eauto.
  apply mcs_nil with (Mem.nextblock m0). apply match_globalenvs_init; auto. omega. omega.
  instantiate (1 := gce). constructor.
  red; auto. constructor. 
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

