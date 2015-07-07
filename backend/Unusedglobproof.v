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

(** Elimination of unreferenced static definitions *)

Require Import FSets.
Require Import Coqlib.
Require Import Ordered.
Require Import Maps.
Require Import Iteration.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Unusedglob.

Module ISF := FSetFacts.Facts(IS).
Module ISP := FSetProperties.Properties(IS).

(** * Properties of the analysis *)

(** Monotonic evolution of the workset. *)

Inductive workset_incl (w1 w2: workset) : Prop := 
  workset_incl_intro:
    forall (SEEN: IS.Subset w1.(w_seen) w2.(w_seen))
           (TODO: List.incl w1.(w_todo) w2.(w_todo))
           (TRACK: forall id, IS.In id w2.(w_seen) ->
                      IS.In id w1.(w_seen) \/ List.In id w2.(w_todo)),
    workset_incl w1 w2.

Lemma seen_workset_incl:
  forall w1 w2 id, workset_incl w1 w2 -> IS.In id w1 -> IS.In id w2.
Proof.
  intros. destruct H. auto.
Qed.

Lemma workset_incl_refl: forall w, workset_incl w w.
Proof.
  intros; split. red; auto. red; auto. auto. 
Qed.

Lemma workset_incl_trans:
  forall w1 w2 w3, workset_incl w1 w2 -> workset_incl w2 w3 -> workset_incl w1 w3.
Proof.
  intros. destruct H, H0; split.
  red; eauto.
  red; eauto.
  intros. edestruct TRACK0; eauto. edestruct TRACK; eauto. 
Qed.

Lemma add_workset_incl:
  forall id w, workset_incl w (add_workset id w).
Proof.
  unfold add_workset; intros. destruct (IS.mem id w) eqn:MEM.
- apply workset_incl_refl.
- split; simpl.
  + red; intros. apply IS.add_2; auto.
  + red; simpl; auto.
  + intros. destruct (ident_eq id id0); auto. apply IS.add_3 in H; auto. 
Qed.

Lemma addlist_workset_incl:
  forall l w, workset_incl w (addlist_workset l w).
Proof.
  induction l; simpl; intros. 
  apply workset_incl_refl.
  eapply workset_incl_trans. apply add_workset_incl. eauto.
Qed.

Lemma add_ref_function_incl:
  forall f w, workset_incl w (add_ref_function f w).
Proof.
  unfold add_ref_function; intros. apply PTree_Properties.fold_rec.
- auto.
- apply workset_incl_refl.
- intros. apply workset_incl_trans with a; auto. 
  unfold add_ref_instruction. apply addlist_workset_incl.
Qed.

Lemma add_ref_globvar_incl:
  forall gv w, workset_incl w (add_ref_globvar gv w).
Proof.
  unfold add_ref_globvar; intros. 
  revert w. induction (gvar_init gv); simpl; intros.
  apply workset_incl_refl.
  eapply workset_incl_trans; [ | eauto ].
  unfold add_ref_init_data.
  destruct a; (apply workset_incl_refl || apply add_workset_incl).
Qed.

Lemma add_ref_definition_incl:
  forall pm id w, workset_incl w (add_ref_definition pm id w).
Proof.
  unfold add_ref_definition; intros. 
  destruct (pm!id) as [[[] | ? ] | ].
  apply add_ref_function_incl.
  apply addlist_workset_incl. 
  apply add_ref_globvar_incl.
  apply workset_incl_refl.
Qed.

Lemma initial_workset_incl:
  forall p, workset_incl {| w_seen := IS.empty; w_todo := nil |} (initial_workset p).
Proof.
  unfold initial_workset; intros.
  eapply workset_incl_trans. 2: apply add_workset_incl. 
  generalize {| w_seen := IS.empty; w_todo := nil |}. induction (prog_public p); simpl; intros.
  apply workset_incl_refl.
  eapply workset_incl_trans. eapply add_workset_incl. eapply IHl. 
Qed.

(** Soundness properties for functions that add identifiers to the workset *)

Lemma seen_add_workset:
  forall id (w: workset), IS.In id (add_workset id w).
Proof.
  unfold add_workset; intros.
  destruct (IS.mem id w) eqn:MEM.
  apply IS.mem_2; auto.
  simpl. apply IS.add_1; auto.
Qed.

Lemma seen_addlist_workset:
  forall id l (w: workset),
  In id l -> IS.In id (addlist_workset l w).
Proof.
  induction l; simpl; intros. 
  tauto.
  destruct H. subst a.
  eapply seen_workset_incl. apply addlist_workset_incl. apply seen_add_workset.
  apply IHl; auto.
Qed.

Definition ref_function (f: function) (id: ident) : Prop :=
  exists pc i, f.(fn_code)!pc = Some i /\ In id (ref_instruction i).

Lemma seen_add_ref_function:
  forall id f w,
  ref_function f id -> IS.In id (add_ref_function f w).
Proof.
  intros until w. unfold ref_function, add_ref_function. apply PTree_Properties.fold_rec; intros.
- destruct H1 as (pc & i & A & B). apply H0; auto. exists pc, i; split; auto. rewrite H; auto.
- destruct H as (pc & i & A & B). rewrite PTree.gempty in A; discriminate.
- destruct H2 as (pc & i & A & B). rewrite PTree.gsspec in A. destruct (peq pc k).
  + inv A. unfold add_ref_instruction. apply seen_addlist_workset; auto. 
  + unfold add_ref_instruction. eapply seen_workset_incl. apply addlist_workset_incl. 
    apply H1. exists pc, i; auto. 
Qed.

Definition ref_fundef (fd: fundef) (id: ident) : Prop :=
  match fd with Internal f => ref_function f id | External ef => In id (globals_external ef) end.

Definition ref_def (gd: globdef fundef unit) (id: ident) : Prop :=
  match gd with
  | Gfun fd => ref_fundef fd id
  | Gvar gv => exists ofs, List.In (Init_addrof id ofs) gv.(gvar_init)
  end.

Lemma seen_add_ref_definition:
  forall pm id gd id' w,
  pm!id = Some gd -> ref_def gd id' -> IS.In id' (add_ref_definition pm id w).
Proof.
  unfold add_ref_definition; intros. rewrite H. red in H0; destruct gd as [[f|ef]|gv].
  apply seen_add_ref_function; auto.
  apply seen_addlist_workset; auto.
  destruct H0 as (ofs & IN).
  unfold add_ref_globvar.
  assert (forall l (w: workset),
          IS.In id' w \/ In (Init_addrof id' ofs) l ->
          IS.In id' (fold_left add_ref_init_data l w)).
  {
    induction l; simpl; intros. 
    tauto.
    apply IHl. intuition auto.
    left. destruct a; simpl; auto. eapply seen_workset_incl. apply add_workset_incl. auto. 
    subst; left; simpl. apply seen_add_workset.
  }
  apply H0; auto. 
Qed.

Lemma seen_main_initial_workset:
  forall p, IS.In p.(prog_main) (initial_workset p).
Proof.
  unfold initial_workset; intros. apply seen_add_workset. 
Qed.

Lemma seen_public_initial_workset:
  forall p id, In id p.(prog_public) -> IS.In id (initial_workset p).
Proof.
  intros. unfold initial_workset. eapply seen_workset_incl. apply add_workset_incl. 
  assert (forall l (w: workset),
          IS.In id w \/ In id l -> IS.In id (fold_left (fun w id => add_workset id w) l w)).
  {
    induction l; simpl; intros.
    tauto.
    apply IHl. intuition auto; left.
    eapply seen_workset_incl. apply add_workset_incl. auto. 
    subst a. apply seen_add_workset. 
  }
  apply H0. auto. 
Qed.

(** * Semantic preservation *)

Section SOUNDNESS.
Variable p: program.
Variable tp: program.
Hypothesis TRANSF: transform_program p = OK tp.
Let ge := Genv.globalenv p.
Let tge := Genv.globalenv tp.

Let pm := program_map p.


(** Correctness of the dependency graph traversal. *)

Definition workset_invariant (w: workset) : Prop :=
  forall id gd id',
  IS.In id w -> ~List.In id (w_todo w) -> pm!id = Some gd -> ref_def gd id' ->
  IS.In id' w.

Definition used_set_closed (u: IS.t) : Prop :=
  forall id gd id',
  IS.In id u -> pm!id = Some gd -> ref_def gd id' -> IS.In id' u.

Lemma iter_step_invariant:
  forall w,
  workset_invariant w ->
  match iter_step pm w with
  | inl u => used_set_closed u
  | inr w' => workset_invariant w'
  end.
Proof.
  unfold iter_step, workset_invariant, used_set_closed; intros. 
  destruct (w_todo w) as [ | id rem ]; intros.
- eapply H; eauto.
- set (w' := {| w_seen := w.(w_seen); w_todo := rem |}) in *.
  destruct (add_ref_definition_incl pm id w').
  destruct (ident_eq id id0).
  + subst id0. eapply seen_add_ref_definition; eauto. 
  + exploit TRACK; eauto. intros [A|A].
    * apply SEEN. eapply H; eauto. simpl. 
      assert (~ In id0 rem). 
      { change rem with (w_todo w'). red; intros. elim H1; auto. }
      tauto.
    * contradiction.
Qed.

Theorem used_globals_sound:
  forall u, used_globals p = Some u -> used_set_closed u.
Proof.
  unfold used_globals; intros. eapply PrimIter.iterate_prop with (P := workset_invariant); eauto.
- intros. apply iter_step_invariant; auto. 
- destruct (initial_workset_incl p). 
  red; intros. edestruct TRACK; eauto. 
  simpl in H4. eelim IS.empty_1; eauto. 
  contradiction.
Qed.

Theorem used_globals_incl:
  forall u, used_globals p = Some u -> IS.Subset (initial_workset p) u.
Proof.
  unfold used_globals; intros.
  eapply PrimIter.iterate_prop with (P := fun (w: workset) => IS.Subset (initial_workset p) w); eauto.
- fold pm; unfold iter_step; intros. destruct (w_todo a) as [ | id rem ].
  auto.
  destruct (add_ref_definition_incl pm id {| w_seen := a; w_todo := rem |}).
  red; auto.
- red; auto.
Qed.

Definition used: IS.t := 
  match used_globals p with Some u => u | None => IS.empty end.

Remark USED_GLOBALS: used_globals p = Some used.
Proof.
  unfold used. unfold transform_program in TRANSF. destruct (used_globals p). auto. discriminate.
Qed.

Definition kept (id: ident) : Prop := IS.In id used.

Theorem kept_closed:
  forall id gd id',
  kept id -> pm!id = Some gd -> ref_def gd id' -> kept id'.
Proof.
  intros. assert (UC: used_set_closed used) by (apply used_globals_sound; apply USED_GLOBALS).
  eapply UC; eauto.
Qed.

Theorem kept_main:
  kept p.(prog_main).
Proof.
  unfold kept. eapply used_globals_incl; eauto. apply USED_GLOBALS. apply seen_main_initial_workset.
Qed.

Theorem kept_public:
  forall id, In id p.(prog_public) -> kept id.
Proof.
  intros. unfold kept. eapply used_globals_incl; eauto. apply USED_GLOBALS. apply seen_public_initial_workset; auto.
Qed.

Remark filter_globdefs_accu:
  forall defs accu1 accu2 u,
  filter_globdefs u (accu1 ++ accu2) defs = filter_globdefs u accu1 defs ++ accu2.
Proof.
  induction defs; simpl; intros.
  auto.
  destruct a as [id gd]. destruct (IS.mem id u); auto. 
  rewrite <- IHdefs. auto.
Qed.

Remark filter_globdefs_nil:
  forall u accu defs,
  filter_globdefs u accu defs = filter_globdefs u nil defs ++ accu.
Proof.
  intros. rewrite <- filter_globdefs_accu. auto. 
Qed.

Theorem transform_program_charact:
  forall id, (program_map tp)!id = if IS.mem id used then pm!id else None.
Proof.
  intros. 
  assert (X: forall l u m1 m2,
             IS.In id u ->
             m1!id = m2!id ->
             (fold_left add_def_prog_map (filter_globdefs u nil l) m1)!id =
             (fold_left add_def_prog_map (List.rev l) m2)!id).
  {
    induction l; simpl; intros. 
    auto.
    destruct a as [id1 gd1]. rewrite fold_left_app. simpl. 
    destruct (IS.mem id1 u) eqn:MEM.
    rewrite filter_globdefs_nil. rewrite fold_left_app. simpl. 
    unfold add_def_prog_map at 1 3. simpl. 
    rewrite ! PTree.gsspec. destruct (peq id id1). auto.
    apply IHl; auto. apply IS.remove_2; auto. 
    unfold add_def_prog_map at 2. simpl. rewrite PTree.gso. apply IHl; auto. 
    red; intros; subst id1.
    assert (IS.mem id u = true) by (apply IS.mem_1; auto). congruence.
  }
  assert (Y: forall l u m1,
             IS.mem id u = false ->
             m1!id = None ->
             (fold_left add_def_prog_map (filter_globdefs u nil l) m1)!id = None).
  {
    induction l; simpl; intros.
    auto.
    destruct a as [id1 gd1].
    destruct (IS.mem id1 u) eqn:MEM.
    rewrite filter_globdefs_nil. rewrite fold_left_app. simpl. 
    unfold add_def_prog_map at 1. simpl. rewrite PTree.gso by congruence. eapply IHl; eauto.
    rewrite ISF.remove_b. rewrite H; auto. 
    eapply IHl; eauto.
  }
  unfold pm, program_map.
  unfold transform_program in TRANSF; rewrite USED_GLOBALS in TRANSF. inversion TRANSF.
  simpl. destruct (IS.mem id used) eqn: MEM.
  erewrite X. rewrite List.rev_involutive. eauto. apply IS.mem_2; auto. auto.
  apply Y. auto. apply PTree.gempty.
Qed.

(** Program map and Genv operations *)

Definition genv_progmap_match (ge: genv) (pm: prog_map) : Prop :=
  forall id,
  match Genv.find_symbol ge id with
  | None => pm!id = None
  | Some b =>
      match pm!id with
      | None => False
      | Some (Gfun fd) => Genv.find_funct_ptr ge b = Some fd
      | Some (Gvar gv) => Genv.find_var_info ge b = Some gv
      end
  end.

Lemma genv_program_map:
  forall p, genv_progmap_match (Genv.globalenv p) (program_map p).
Proof.
  intros. unfold Genv.globalenv, program_map. 
  assert (REC: forall defs g m, 
               genv_progmap_match g m ->
               genv_progmap_match (Genv.add_globals g defs) (fold_left add_def_prog_map defs m)).
  {
    induction defs; simpl; intros.
    auto.
    apply IHdefs. red; intros. specialize (H id).
    destruct a as [id1 [fd|gv]];
    unfold Genv.add_global, Genv.find_symbol, Genv.find_funct_ptr, Genv.find_var_info, add_def_prog_map in *;
    simpl.
  - rewrite PTree.gsspec. destruct (peq id id1); subst.
    + rewrite ! PTree.gss. auto.
    + destruct (Genv.genv_symb g)!id as [b|] eqn:S; rewrite PTree.gso by auto.
      * rewrite PTree.gso. auto. apply Plt_ne. eapply Genv.genv_symb_range; eauto. 
      * auto.
  - rewrite PTree.gsspec. destruct (peq id id1); subst.
    + rewrite ! PTree.gss. auto.
    + destruct (Genv.genv_symb g)!id as [b|] eqn:S; rewrite PTree.gso by auto.
      * rewrite PTree.gso. auto. apply Plt_ne. eapply Genv.genv_symb_range; eauto. 
      * auto.
  }
  apply REC. red; intros. unfold Genv.find_symbol, Genv.empty_genv; simpl. rewrite ! PTree.gempty; auto.
Qed.

Lemma transform_program_kept:
  forall id b, Genv.find_symbol tge id = Some b -> kept id.
Proof.
  intros. generalize (genv_program_map tp id). fold tge; rewrite H. 
  rewrite transform_program_charact. intros. destruct (IS.mem id used) eqn:U.
  unfold kept; apply IS.mem_2; auto.
  contradiction.
Qed.

(** Injections that preserve used globals. *)

Record meminj_preserves_globals (f: meminj) : Prop := {
  symbols_inject_1: forall id b b' delta,
    f b = Some(b', delta) -> Genv.find_symbol ge id = Some b ->
    delta = 0 /\ Genv.find_symbol tge id = Some b';
  symbols_inject_2: forall id b,
    kept id -> Genv.find_symbol ge id = Some b ->
    exists b', Genv.find_symbol tge id = Some b' /\ f b = Some(b', 0);
  symbols_inject_3: forall id b',
    Genv.find_symbol tge id = Some b' ->
    exists b, Genv.find_symbol ge id = Some b /\ f b = Some(b', 0);
  funct_ptr_inject: forall b b' delta fd,
    f b = Some(b', delta) -> Genv.find_funct_ptr ge b = Some fd ->
    Genv.find_funct_ptr tge b' = Some fd /\ delta = 0 /\
    (forall id, ref_fundef fd id -> kept id);
  var_info_inject: forall b b' delta gv,
    f b = Some(b', delta) -> Genv.find_var_info ge b = Some gv ->
    Genv.find_var_info tge b' = Some gv /\ delta = 0;
  var_info_rev_inject: forall b b' delta gv,
    f b = Some(b', delta) -> Genv.find_var_info tge b' = Some gv ->
    Genv.find_var_info ge b = Some gv /\ delta = 0
}.

Definition init_meminj : meminj :=
  fun b =>
    match Genv.invert_symbol ge b with
    | Some id => 
        match Genv.find_symbol tge id with
        | Some b' => Some (b', 0)
        | None => None
        end
    | None => None
    end.

Remark init_meminj_invert:
  forall b b' delta,
  init_meminj b = Some(b', delta) ->
  delta = 0 /\ exists id, Genv.find_symbol ge id = Some b /\ Genv.find_symbol tge id = Some b'.
Proof.
  unfold init_meminj; intros.
  destruct (Genv.invert_symbol ge b) as [id|] eqn:S; try discriminate.
  destruct (Genv.find_symbol tge id) as [b''|] eqn:F; inv H.
  split. auto. exists id. split. apply Genv.invert_find_symbol; auto. auto.
Qed. 

Lemma init_meminj_preserves_globals:
  meminj_preserves_globals init_meminj.
Proof.
  constructor; intros.
- exploit init_meminj_invert; eauto. intros (A & id1 & B & C).
  assert (id1 = id) by (eapply (Genv.genv_vars_inj ge); eauto). subst id1.
  auto.
- unfold init_meminj. erewrite Genv.find_invert_symbol by eauto. apply IS.mem_1 in H.
  generalize (genv_program_map p id) (genv_program_map tp id). fold ge; fold tge; fold pm.
  rewrite transform_program_charact. rewrite H, H0.
  destruct (Genv.find_symbol tge id) as [b'|]; intros.
  exists b'; auto. rewrite H2 in H1; contradiction.
- generalize (genv_program_map tp id). fold tge. rewrite H. intros.
  destruct (program_map tp)!id as [gd|] eqn:PM; try contradiction.
  generalize (transform_program_charact id). rewrite PM. 
  destruct (IS.mem id used) eqn:USED; intros; try discriminate.
  generalize (genv_program_map p id). fold ge; fold pm.
  destruct (Genv.find_symbol ge id) as [b|] eqn:FS; intros; try congruence.
  exists b; split; auto. unfold init_meminj. 
  erewrite Genv.find_invert_symbol by eauto. rewrite H. auto.
- exploit init_meminj_invert; eauto. intros (A & id & B & C).
  generalize (genv_program_map p id) (genv_program_map tp id). fold ge; fold tge; fold pm.
  rewrite transform_program_charact. rewrite B, C. intros.
  destruct (IS.mem id used) eqn:KEPT; try contradiction.
  destruct (pm!id) as [gd|] eqn:PM; try contradiction. 
  destruct gd as [fd'|gv'].
  + assert (fd' = fd) by congruence. subst fd'. split. auto. split. auto. 
    intros. eapply kept_closed; eauto. red; apply IS.mem_2; auto. 
  + assert (b <> b) by (eapply Genv.genv_funs_vars; eassumption). congruence.
- exploit init_meminj_invert; eauto. intros (A & id & B & C). split; auto.
  generalize (genv_program_map p id) (genv_program_map tp id). fold ge; fold tge; fold pm.
  rewrite transform_program_charact. rewrite B, C. intros.
  destruct (IS.mem id used); try contradiction.
  destruct (pm!id) as [gd|]; try contradiction. 
  destruct gd as [fd'|gv']. 
  + assert (b <> b) by (eapply Genv.genv_funs_vars; eassumption). congruence.
  + congruence.
- exploit init_meminj_invert; eauto. intros (A & id & B & C). split; auto.
  generalize (genv_program_map p id) (genv_program_map tp id). fold ge; fold tge; fold pm.
  rewrite transform_program_charact. rewrite B, C. intros.
  destruct (IS.mem id used); try contradiction.
  destruct (pm!id) as [gd|]; try contradiction. 
  destruct gd as [fd'|gv']. 
  + assert (b' <> b') by (eapply Genv.genv_funs_vars; eassumption). congruence.
  + congruence.
Qed.

Lemma globals_symbols_inject:
  forall j, meminj_preserves_globals j -> symbols_inject j ge tge.
Proof.
  intros. 
  assert (E1: Genv.genv_public ge = p.(prog_public)).
  { apply Genv.globalenv_public. }
  assert (E2: Genv.genv_public tge = p.(prog_public)).
  { unfold tge; rewrite Genv.globalenv_public. 
    unfold transform_program in TRANSF. rewrite USED_GLOBALS in TRANSF. inversion TRANSF. auto. }
  split; [|split;[|split]]; intros.
  + simpl; unfold Genv.public_symbol; rewrite E1, E2.
    destruct (Genv.find_symbol tge id) as [b'|] eqn:TFS.
    exploit symbols_inject_3; eauto. intros (b & FS & INJ). rewrite FS. auto. 
    destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
    destruct (in_dec ident_eq id (prog_public p)); simpl; auto.
    exploit symbols_inject_2; eauto. apply kept_public; auto. 
    intros (b' & TFS' & INJ). congruence.
  + eapply symbols_inject_1; eauto. 
  + simpl in *; unfold Genv.public_symbol in H0. 
    destruct (Genv.find_symbol ge id) as [b|] eqn:FS; try discriminate.
    rewrite E1 in H0. 
    destruct (in_dec ident_eq id (prog_public p)); try discriminate. inv H1.
    exploit symbols_inject_2; eauto. apply kept_public; auto. 
    intros (b' & A & B); exists b'; auto.
  + simpl. unfold Genv.block_is_volatile. 
    destruct (Genv.find_var_info ge b1) as [gv|] eqn:V1.
    exploit var_info_inject; eauto. intros [A B]. rewrite A. auto.
    destruct (Genv.find_var_info tge b2) as [gv|] eqn:V2; auto.
    exploit var_info_rev_inject; eauto. intros [A B]. congruence.
Qed.

Lemma symbol_address_inject:
  forall j id ofs, 
  meminj_preserves_globals j -> kept id ->
  Val.inject j (Genv.symbol_address ge id ofs) (Genv.symbol_address tge id ofs).
Proof.
  intros. unfold Genv.symbol_address. destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
  exploit symbols_inject_2; eauto. intros (b' & TFS & INJ). rewrite TFS. 
  econstructor; eauto. rewrite Int.add_zero; auto.
Qed. 

(** Semantic preservation *)

Definition regset_inject (f: meminj) (rs rs': regset): Prop :=
  forall r, Val.inject f rs#r rs'#r.

Lemma regs_inject:
  forall f rs rs', regset_inject f rs rs' -> forall l, Val.inject_list f rs##l rs'##l.
Proof.
  induction l; simpl. constructor. constructor; auto. 
Qed.

Lemma set_reg_inject:
  forall f rs rs' r v v',
  regset_inject f rs rs' -> Val.inject f v v' ->
  regset_inject f (rs#r <- v) (rs'#r <- v').
Proof.
  intros; red; intros. rewrite ! Regmap.gsspec. destruct (peq r0 r); auto. 
Qed.

Lemma regset_inject_incr:
  forall f f' rs rs', regset_inject f rs rs' -> inject_incr f f' -> regset_inject f' rs rs'.
Proof.
  intros; red; intros. apply val_inject_incr with f; auto. 
Qed.

Lemma regset_undef_inject:
  forall f, regset_inject f (Regmap.init Vundef) (Regmap.init Vundef).
Proof.
  intros; red; intros. rewrite Regmap.gi. auto.
Qed.

Lemma init_regs_inject:
  forall f args args', Val.inject_list f args args' ->
  forall params,
  regset_inject f (init_regs args params) (init_regs args' params).
Proof.
  induction 1; intros; destruct params; simpl; try (apply regset_undef_inject).
  apply set_reg_inject; auto. 
Qed.

Inductive match_stacks (j: meminj):
        list stackframe -> list stackframe -> block -> block -> Prop :=
  | match_stacks_nil: forall bound tbound,
      meminj_preserves_globals j ->
      Ple (Genv.genv_next ge) bound -> Ple (Genv.genv_next tge) tbound ->
      match_stacks j nil nil bound tbound
  | match_stacks_cons: forall res f sp pc rs s tsp trs ts bound tbound
         (STACKS: match_stacks j s ts sp tsp)
         (KEPT: forall id, ref_function f id -> kept id)
         (SPINJ: j sp = Some(tsp, 0))
         (REGINJ: regset_inject j rs trs)
         (BELOW: Plt sp bound)
         (TBELOW: Plt tsp tbound),
      match_stacks j (Stackframe res f (Vptr sp Int.zero) pc rs :: s)
                     (Stackframe res f (Vptr tsp Int.zero) pc trs :: ts)
                     bound tbound.

Lemma match_stacks_preserves_globals:
  forall j s ts bound tbound,
  match_stacks j s ts bound tbound ->
  meminj_preserves_globals j.
Proof.
  induction 1; auto. 
Qed.

Lemma match_stacks_incr:
  forall j j', inject_incr j j' ->
  forall s ts bound tbound, match_stacks j s ts bound tbound ->
  (forall b1 b2 delta,
      j b1 = None -> j' b1 = Some(b2, delta) -> Ple bound b1 /\ Ple tbound b2) ->
  match_stacks j' s ts bound tbound.
Proof.
  induction 2; intros.
- assert (SAME: forall b b' delta, Plt b (Genv.genv_next ge) ->
                                   j' b = Some(b', delta) -> j b = Some(b', delta)).
  { intros. destruct (j b) as [[b1 delta1] | ] eqn: J.
    exploit H; eauto. congruence. 
    exploit H3; eauto. intros [A B]. elim (Plt_strict b).
    eapply Plt_Ple_trans. eauto. eapply Ple_trans; eauto. }
  assert (SAME': forall b b' delta, Plt b' (Genv.genv_next tge) ->
                                   j' b = Some(b', delta) -> j b = Some (b', delta)).
  { intros. destruct (j b) as [[b1 delta1] | ] eqn: J.
    exploit H; eauto. congruence.
    exploit H3; eauto. intros [A B]. elim (Plt_strict b').
    eapply Plt_Ple_trans. eauto. eapply Ple_trans; eauto. }
  constructor; auto.  constructor; intros.
  + exploit symbols_inject_1; eauto. apply SAME; auto. 
    eapply Genv.genv_symb_range; eauto. 
  + exploit symbols_inject_2; eauto. intros (b' & A & B). 
    exists b'; auto.
  + exploit symbols_inject_3; eauto. intros (b & A & B).
    exists b; auto.
  + eapply funct_ptr_inject; eauto. apply SAME; auto. 
    eapply Genv.genv_funs_range; eauto.
  + eapply var_info_inject; eauto. apply SAME; auto. 
    eapply Genv.genv_vars_range; eauto.
  + eapply var_info_rev_inject; eauto. apply SAME'; auto. 
    eapply Genv.genv_vars_range; eauto.
- econstructor; eauto. 
  apply IHmatch_stacks.
  intros. exploit H1; eauto. intros [A B]. split; eapply Ple_trans; eauto.
  apply Plt_Ple; auto. apply Plt_Ple; auto.
  apply regset_inject_incr with j; auto.
Qed.

Lemma match_stacks_bound:
  forall j s ts bound tbound bound' tbound',
  match_stacks j s ts bound tbound ->
  Ple bound bound' -> Ple tbound tbound' ->
  match_stacks j s ts bound' tbound'.
Proof.
  induction 1; intros.
- constructor; auto. eapply Ple_trans; eauto. eapply Ple_trans; eauto.  
- econstructor; eauto. eapply Plt_Ple_trans; eauto. eapply Plt_Ple_trans; eauto. 
Qed.

Inductive match_states: state -> state -> Prop :=
  | match_states_regular: forall s f sp pc rs m ts tsp trs tm j
         (STACKS: match_stacks j s ts sp tsp)
         (KEPT: forall id, ref_function f id -> kept id)
         (SPINJ: j sp = Some(tsp, 0))
         (REGINJ: regset_inject j rs trs)
         (MEMINJ: Mem.inject j m tm),
      match_states (State s f (Vptr sp Int.zero) pc rs m)
                   (State ts f (Vptr tsp Int.zero) pc trs tm)
  | match_states_call: forall s fd args m ts targs tm j
         (STACKS: match_stacks j s ts (Mem.nextblock m) (Mem.nextblock tm))
         (KEPT: forall id, ref_fundef fd id -> kept id)
         (ARGINJ: Val.inject_list j args targs)
         (MEMINJ: Mem.inject j m tm),
      match_states (Callstate s fd args m)
                   (Callstate ts fd targs tm)
  | match_states_return: forall s res m ts tres tm j
         (STACKS: match_stacks j s ts (Mem.nextblock m) (Mem.nextblock tm))
         (RESINJ: Val.inject j res tres)
         (MEMINJ: Mem.inject j m tm),
      match_states (Returnstate s res m)
                   (Returnstate ts tres tm).

Lemma external_call_inject:
  forall ef vargs m1 t vres m2 f m1' vargs',
  meminj_preserves_globals f ->
  external_call ef ge vargs m1 t vres m2 ->
  (forall id, In id (globals_external ef) -> kept id) ->
  Mem.inject f m1 m1' ->
  Val.inject_list f vargs vargs' ->
  exists f', exists vres', exists m2',
    external_call ef tge vargs' m1' t vres' m2'
    /\ Val.inject f' vres vres'
    /\ Mem.inject f' m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1'.
Proof.
  intros. eapply external_call_mem_inject_gen; eauto.
- apply globals_symbols_inject; auto.
- intros. exploit symbols_inject_2; eauto. 
  intros (b' & A & B); exists b'; auto.
Qed.

Lemma find_function_inject:
  forall j ros rs fd trs,
  meminj_preserves_globals j ->
  find_function ge ros rs = Some fd ->
  match ros with inl r => regset_inject j rs trs | inr id => kept id end ->
  find_function tge ros trs = Some fd /\ (forall id, ref_fundef fd id -> kept id).
Proof.
  intros. destruct ros as [r|id]; simpl in *.
- exploit Genv.find_funct_inv; eauto. intros (b & R). rewrite R in H0. 
  rewrite Genv.find_funct_find_funct_ptr in H0. 
  specialize (H1 r). rewrite R in H1. inv H1. 
  exploit funct_ptr_inject; eauto. intros (A & B & C). 
  rewrite B; auto.
- destruct (Genv.find_symbol ge id) as [b|] eqn:FS; try discriminate.
  exploit symbols_inject_2; eauto. intros (tb & P & Q). rewrite P. 
  exploit funct_ptr_inject; eauto. intros (A & B & C). 
  auto.
Qed.

Lemma eval_annot_arg_inject:
  forall rs sp m j rs' sp' m' a v,
  eval_annot_arg ge (fun r => rs#r) (Vptr sp Int.zero) m a v ->
  j sp = Some(sp', 0) ->
  meminj_preserves_globals j ->
  regset_inject j rs rs' ->
  Mem.inject j m m' ->
  (forall id, In id (globals_of_annot_arg a) -> kept id) ->
  exists v',
     eval_annot_arg tge (fun r => rs'#r) (Vptr sp' Int.zero) m' a v'
  /\ Val.inject j v v'.
Proof.
  induction 1; intros SP GL RS MI K; simpl in K.
- exists rs'#x; split; auto. constructor. 
- econstructor; eauto with aarg.
- econstructor; eauto with aarg.
- econstructor; eauto with aarg.
- econstructor; eauto with aarg.
- simpl in H. exploit Mem.load_inject; eauto. rewrite Zplus_0_r. 
  intros (v' & A & B). exists v'; auto with aarg.
- econstructor; split; eauto with aarg. simpl. econstructor; eauto. rewrite Int.add_zero; auto.
- assert (Val.inject j (Senv.symbol_address ge id ofs) (Senv.symbol_address tge id ofs)).
  { unfold Senv.symbol_address; simpl; unfold Genv.symbol_address. 
    destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
    exploit symbols_inject_2; eauto. intros (b' & A & B). rewrite A. 
    econstructor; eauto. rewrite Int.add_zero; auto. }
  exploit Mem.loadv_inject; eauto. intros (v' & A & B). exists v'; auto with aarg.
- econstructor; split; eauto with aarg.
  unfold Senv.symbol_address; simpl; unfold Genv.symbol_address. 
  destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
  exploit symbols_inject_2; eauto. intros (b' & A & B). rewrite A. 
  econstructor; eauto. rewrite Int.add_zero; auto.
- destruct IHeval_annot_arg1 as (v1' & A1 & B1); eauto using in_or_app.
  destruct IHeval_annot_arg2 as (v2' & A2 & B2); eauto using in_or_app.
  exists (Val.longofwords v1' v2'); split; auto with aarg. 
  apply Val.longofwords_inject; auto.
Qed.

Lemma eval_annot_args_inject:
  forall rs sp m j rs' sp' m' al vl,
  eval_annot_args ge (fun r => rs#r) (Vptr sp Int.zero) m al vl ->
  j sp = Some(sp', 0) ->
  meminj_preserves_globals j ->
  regset_inject j rs rs' ->
  Mem.inject j m m' ->
  (forall id, In id (globals_of_annot_args al) -> kept id) ->
  exists vl',
     eval_annot_args tge (fun r => rs'#r) (Vptr sp' Int.zero) m' al vl'
  /\ Val.inject_list j vl vl'.
Proof.
  induction 1; intros. 
- exists (@nil val); split; constructor.
- simpl in H5. 
  exploit eval_annot_arg_inject; eauto using in_or_app. intros (v1' & A & B).
  destruct IHlist_forall2 as (vl' & C & D); eauto using in_or_app. 
  exists (v1' :: vl'); split; constructor; auto.
Qed.

Theorem step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  exists S2', step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.

- (* nop *)
  econstructor; split. 
  eapply exec_Inop; eauto. 
  econstructor; eauto. 

- (* op *)
  assert (A: exists tv, 
               eval_operation tge (Vptr tsp Int.zero) op trs##args tm = Some tv
            /\ Val.inject j v tv).
  { apply eval_operation_inj with (ge1 := ge) (m1 := m) (sp1 := Vptr sp0 Int.zero) (vl1 := rs##args). 
    intros; eapply Mem.valid_pointer_inject_val; eauto.
    intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
    intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
    intros; eapply Mem.different_pointers_inject; eauto.
    intros. apply symbol_address_inject. eapply match_stacks_preserves_globals; eauto.
    apply KEPT. red. exists pc, (Iop op args res pc'); auto.
    econstructor; eauto. 
    apply regs_inject; auto.
    assumption. }
  destruct A as (tv & B & C).
  econstructor; split. eapply exec_Iop; eauto.
  econstructor; eauto. apply set_reg_inject; auto. 

- (* load *)
  assert (A: exists ta, 
               eval_addressing tge (Vptr tsp Int.zero) addr trs##args = Some ta
            /\ Val.inject j a ta).
  { apply eval_addressing_inj with (ge1 := ge) (sp1 := Vptr sp0 Int.zero) (vl1 := rs##args). 
    intros. apply symbol_address_inject. eapply match_stacks_preserves_globals; eauto.
    apply KEPT. red. exists pc, (Iload chunk addr args dst pc'); auto.
    econstructor; eauto. 
    apply regs_inject; auto.
    assumption. }
  destruct A as (ta & B & C).
  exploit Mem.loadv_inject; eauto. intros (tv & D & E).
  econstructor; split. eapply exec_Iload; eauto.
  econstructor; eauto. apply set_reg_inject; auto.

- (* store *)
  assert (A: exists ta, 
               eval_addressing tge (Vptr tsp Int.zero) addr trs##args = Some ta
            /\ Val.inject j a ta).
  { apply eval_addressing_inj with (ge1 := ge) (sp1 := Vptr sp0 Int.zero) (vl1 := rs##args). 
    intros. apply symbol_address_inject. eapply match_stacks_preserves_globals; eauto.
    apply KEPT. red. exists pc, (Istore chunk addr args src pc'); auto.
    econstructor; eauto. 
    apply regs_inject; auto.
    assumption. }
  destruct A as (ta & B & C).
  exploit Mem.storev_mapped_inject; eauto. intros (tm' & D & E).
  econstructor; split. eapply exec_Istore; eauto.
  econstructor; eauto.

- (* call *)
  exploit find_function_inject. 
  eapply match_stacks_preserves_globals; eauto. eauto. 
  destruct ros as [r|id]. eauto. apply KEPT. red. econstructor; econstructor; split; eauto. simpl; auto.
  intros (A & B).
  econstructor; split. eapply exec_Icall; eauto. 
  econstructor; eauto. 
  econstructor; eauto.
  change (Mem.valid_block m sp0). eapply Mem.valid_block_inject_1; eauto. 
  change (Mem.valid_block tm tsp). eapply Mem.valid_block_inject_2; eauto. 
  apply regs_inject; auto.

- (* tailcall *)
  exploit find_function_inject. 
  eapply match_stacks_preserves_globals; eauto. eauto. 
  destruct ros as [r|id]. eauto. apply KEPT. red. econstructor; econstructor; split; eauto. simpl; auto.
  intros (A & B).
  exploit Mem.free_parallel_inject; eauto. rewrite ! Zplus_0_r. intros (tm' & C & D).
  econstructor; split.
  eapply exec_Itailcall; eauto. 
  econstructor; eauto. 
  apply match_stacks_bound with stk tsp; auto.
  apply Plt_Ple. 
  change (Mem.valid_block m' stk). eapply Mem.valid_block_inject_1; eauto.
  apply Plt_Ple. 
  change (Mem.valid_block tm' tsp). eapply Mem.valid_block_inject_2; eauto.
  apply regs_inject; auto.

- (* builtin *)
  exploit external_call_inject; eauto. 
  eapply match_stacks_preserves_globals; eauto.
  intros. apply KEPT. red. econstructor; econstructor; eauto. 
  apply regs_inject; eauto.
  intros (j' & tv & tm' & A & B & C & D & E & F & G).
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
  eapply match_states_regular with (j := j'); eauto. 
  apply match_stacks_incr with j; auto. 
  intros. exploit G; eauto. intros [P Q].
  assert (Mem.valid_block m sp0) by (eapply Mem.valid_block_inject_1; eauto).
  assert (Mem.valid_block tm tsp) by (eapply Mem.valid_block_inject_2; eauto).
  unfold Mem.valid_block in *; xomega.
  apply set_reg_inject; auto. apply regset_inject_incr with j; auto.

- (* annot *)
  exploit eval_annot_args_inject; eauto. 
  eapply match_stacks_preserves_globals; eauto.
  intros. apply KEPT. red. econstructor; econstructor; eauto. 
  intros (vargs' & P & Q).
  exploit external_call_inject; eauto. 
  eapply match_stacks_preserves_globals; eauto.
  destruct ef; contradiction.
  intros (j' & tv & tm' & A & B & C & D & E & F & G).
  econstructor; split.
  eapply exec_Iannot; eauto.
  eapply match_states_regular with (j := j'); eauto. 
  apply match_stacks_incr with j; auto. 
  intros. exploit G; eauto. intros [U V].
  assert (Mem.valid_block m sp0) by (eapply Mem.valid_block_inject_1; eauto).
  assert (Mem.valid_block tm tsp) by (eapply Mem.valid_block_inject_2; eauto).
  unfold Mem.valid_block in *; xomega.
  apply regset_inject_incr with j; auto.

- (* cond *)
  assert (C: eval_condition cond trs##args tm = Some b).
  { eapply eval_condition_inject; eauto. apply regs_inject; auto. }
  econstructor; split.
  eapply exec_Icond with (pc' := if b then ifso else ifnot); eauto. 
  econstructor; eauto.

- (* jumptbl *)
  generalize (REGINJ arg); rewrite H0; intros INJ; inv INJ.
  econstructor; split.
  eapply exec_Ijumptable; eauto. 
  econstructor; eauto.

- (* return *)
  exploit Mem.free_parallel_inject; eauto. rewrite ! Zplus_0_r. intros (tm' & C & D).
  econstructor; split.
  eapply exec_Ireturn; eauto. 
  econstructor; eauto. 
  apply match_stacks_bound with stk tsp; auto.
  apply Plt_Ple. 
  change (Mem.valid_block m' stk). eapply Mem.valid_block_inject_1; eauto.
  apply Plt_Ple. 
  change (Mem.valid_block tm' tsp). eapply Mem.valid_block_inject_2; eauto.
  destruct or; simpl; auto. 

- (* internal function *)
  exploit Mem.alloc_parallel_inject. eauto. eauto. apply Zle_refl. apply Zle_refl. 
  intros (j' & tm' & tstk & C & D & E & F & G).
  assert (STK: stk = Mem.nextblock m) by (eapply Mem.alloc_result; eauto). 
  assert (TSTK: tstk = Mem.nextblock tm) by (eapply Mem.alloc_result; eauto). 
  assert (STACKS': match_stacks j' s ts stk tstk).
  { rewrite STK, TSTK. 
    apply match_stacks_incr with j; auto. 
    intros. destruct (eq_block b1 stk). 
    subst b1. rewrite F in H1; inv H1. subst b2. split; apply Ple_refl. 
    rewrite G in H1 by auto. congruence. }
  econstructor; split. 
  eapply exec_function_internal; eauto.
  eapply match_states_regular with (j := j'); eauto.
  apply init_regs_inject; auto. apply val_inject_list_incr with j; auto. 

- (* external function *)
  exploit external_call_inject; eauto. 
  eapply match_stacks_preserves_globals; eauto.
  intros (j' & tres & tm' & A & B & C & D & E & F & G).
  econstructor; split.
  eapply exec_function_external; eauto.
  eapply match_states_return with (j := j'); eauto.
  apply match_stacks_bound with (Mem.nextblock m) (Mem.nextblock tm).
  apply match_stacks_incr with j; auto. 
  intros. exploit G; eauto. intros [P Q].
  unfold Mem.valid_block in *; xomega.
  eapply external_call_nextblock; eauto.
  eapply external_call_nextblock; eauto.

- (* return *)
  inv STACKS. econstructor; split.
  eapply exec_return. 
  econstructor; eauto. apply set_reg_inject; auto. 
Qed.

(** Relating initial memory states *)

Remark init_meminj_no_overlap:
  forall m, Mem.meminj_no_overlap init_meminj m.
Proof.
  intros; red; intros. 
  exploit init_meminj_invert. eexact H0. intros (A1 & id1 & B1 & C1).
  exploit init_meminj_invert. eexact H1. intros (A2 & id2 & B2 & C2).
  left; red; intros; subst b2'. 
  assert (id1 = id2) by (eapply Genv.genv_vars_inj; eauto). 
  congruence.
Qed.

Lemma store_zeros_unmapped_inj:
  forall m1 b1 i n m1',
  store_zeros m1 b1 i n = Some m1' ->
  forall m2,
  Mem.mem_inj init_meminj m1 m2 ->
  init_meminj b1 = None ->
  Mem.mem_inj init_meminj m1' m2.
Proof.
  intros until m1'. functional induction (store_zeros m1 b1 i n); intros.
  inv H. auto.
  eapply IHo; eauto. eapply Mem.store_unmapped_inj; eauto. 
  discriminate.
Qed.

Lemma store_zeros_mapped_inj:
  forall m1 b1 i n m1',
  store_zeros m1 b1 i n = Some m1' ->
  forall m2 b2,
  Mem.mem_inj init_meminj m1 m2 ->
  init_meminj b1 = Some(b2, 0) ->
  exists m2', store_zeros m2 b2 i n = Some m2' /\ Mem.mem_inj init_meminj m1' m2'.
Proof.
  intros until m1'. functional induction (store_zeros m1 b1 i n); intros.
  inv H. exists m2; split; auto. rewrite store_zeros_equation, e; auto. 
  exploit Mem.store_mapped_inj; eauto. apply init_meminj_no_overlap. instantiate (1 := Vzero); constructor. 
  intros (m2' & A & B). rewrite Zplus_0_r in A.
  exploit IHo; eauto. intros (m3' & C & D). 
  exists m3'; split; auto. rewrite store_zeros_equation, e, A, C; auto.
  discriminate.
Qed.

Lemma store_init_data_unmapped_inj:
  forall m1 b1 i id m1' m2,
  Genv.store_init_data ge m1 b1 i id = Some m1' ->
  Mem.mem_inj init_meminj m1 m2 ->
  init_meminj b1 = None ->
  Mem.mem_inj init_meminj m1' m2.
Proof.
  intros. destruct id; simpl in H; try (eapply Mem.store_unmapped_inj; now eauto). 
  inv H; auto.
  destruct (Genv.find_symbol ge i0); try discriminate. eapply Mem.store_unmapped_inj; now eauto.
Qed.

Lemma store_init_data_mapped_inj:
  forall m1 b1 i init m1' b2 m2,
  Genv.store_init_data ge m1 b1 i init = Some m1' ->
  Mem.mem_inj init_meminj m1 m2 ->
  init_meminj b1 = Some(b2, 0) ->
  (forall id ofs, init = Init_addrof id ofs -> kept id) ->
  exists m2', Genv.store_init_data tge m2 b2 i init = Some m2' /\ Mem.mem_inj init_meminj m1' m2'.
Proof.
  intros. replace i with (i + 0) by omega. pose proof (init_meminj_no_overlap m1).
  destruct init; simpl in *; try (eapply Mem.store_mapped_inj; now eauto).
  inv H. exists m2; auto.
  destruct (Genv.find_symbol ge i0) as [bi|] eqn:FS1; try discriminate.
  exploit symbols_inject_2. eapply init_meminj_preserves_globals. eapply H2; eauto. eauto. 
  intros (bi' & A & B). rewrite A. eapply Mem.store_mapped_inj; eauto. 
  econstructor; eauto. rewrite Int.add_zero; auto.
Qed.

 Lemma store_init_data_list_unmapped_inj:
  forall initlist m1 b1 i m1' m2,
  Genv.store_init_data_list ge m1 b1 i initlist = Some m1' ->
  Mem.mem_inj init_meminj m1 m2 ->
  init_meminj b1 = None ->
  Mem.mem_inj init_meminj m1' m2.
Proof.
  induction initlist; simpl; intros. 
- inv H; auto.
- destruct (Genv.store_init_data ge m1 b1 i a) as [m1''|] eqn:ST; try discriminate.
  eapply IHinitlist; eauto. eapply store_init_data_unmapped_inj; eauto.
Qed.

Lemma store_init_data_list_mapped_inj:
  forall initlist m1 b1 i m1' b2 m2,
  Genv.store_init_data_list ge m1 b1 i initlist = Some m1' ->
  Mem.mem_inj init_meminj m1 m2 ->
  init_meminj b1 = Some(b2, 0) ->
  (forall id ofs, In (Init_addrof id ofs) initlist -> kept id) ->
  exists m2', Genv.store_init_data_list tge m2 b2 i initlist = Some m2' /\ Mem.mem_inj init_meminj m1' m2'.
Proof.
  induction initlist; simpl; intros.
- inv H. exists m2; auto.
- destruct (Genv.store_init_data ge m1 b1 i a) as [m1''|] eqn:ST; try discriminate.
  exploit store_init_data_mapped_inj; eauto. intros (m2'' & A & B).
  exploit IHinitlist; eauto. intros (m2' & C & D).
  exists m2'; split; auto. rewrite A; auto. 
Qed.

Lemma alloc_global_unmapped_inj:
  forall m1 id g m1' m2,
  Genv.alloc_global ge m1 (id, g) = Some m1' ->
  Mem.mem_inj init_meminj m1 m2 ->
  init_meminj (Mem.nextblock m1) = None ->
  Mem.mem_inj init_meminj m1' m2.
Proof.
  unfold Genv.alloc_global; intros. destruct g as [fd|gv].
- destruct (Mem.alloc m1 0 1) as (m1a, b) eqn:ALLOC.
  exploit Mem.alloc_result; eauto. intros EQ. rewrite <- EQ in H1. 
  eapply Mem.drop_unmapped_inj with (m1 := m1a); eauto. 
  eapply Mem.alloc_left_unmapped_inj; eauto.
- set (sz := Genv.init_data_list_size (gvar_init gv)) in *.
  destruct (Mem.alloc m1 0 sz) as (m1a, b) eqn:ALLOC.
  destruct (store_zeros m1a b 0 sz) as [m1b|] eqn: STZ; try discriminate.
  destruct (Genv.store_init_data_list ge m1b b 0 (gvar_init gv)) as [m1c|] eqn:ST; try discriminate.
  exploit Mem.alloc_result; eauto. intros EQ. rewrite <- EQ in H1. 
  eapply Mem.drop_unmapped_inj with (m1 := m1c); eauto.
  eapply store_init_data_list_unmapped_inj with (m1 := m1b); eauto. 
  eapply store_zeros_unmapped_inj with (m1 := m1a); eauto.
  eapply Mem.alloc_left_unmapped_inj; eauto.
Qed.

Lemma alloc_global_mapped_inj:
  forall m1 id g m1' m2,
  Genv.alloc_global ge m1 (id, g) = Some m1' ->
  Mem.mem_inj init_meminj m1 m2 ->
  init_meminj (Mem.nextblock m1) = Some(Mem.nextblock m2, 0) ->
  (forall id, ref_def g id -> kept id) ->
  exists m2',
    Genv.alloc_global tge m2 (id, g) = Some m2' /\ Mem.mem_inj init_meminj m1' m2'.
Proof.
  unfold Genv.alloc_global; intros. destruct g as [fd|gv].
- destruct (Mem.alloc m1 0 1) as (m1a, b1) eqn:ALLOC.
  exploit Mem.alloc_result; eauto. intros EQ. rewrite <- EQ in H1.
  destruct (Mem.alloc m2 0 1) as (m2a, b2) eqn:ALLOC2.
  exploit Mem.alloc_result; eauto. intros EQ2. rewrite <- EQ2 in H1.
  assert (Mem.mem_inj init_meminj m1a m2a).
  { eapply Mem.alloc_left_mapped_inj with (b1 := b1) (b2 := b2) (delta := 0).
    eapply Mem.alloc_right_inj; eauto.
    eauto.
    eauto with mem. 
    red; intros; apply Z.divide_0_r.
    intros. apply Mem.perm_implies with Freeable; auto with mem. 
    eapply Mem.perm_alloc_2; eauto. omega. 
    auto.
  }
  exploit Mem.drop_mapped_inj; eauto. apply init_meminj_no_overlap.
- set (sz := Genv.init_data_list_size (gvar_init gv)) in *.
  destruct (Mem.alloc m1 0 sz) as (m1a, b1) eqn:ALLOC.
  destruct (store_zeros m1a b1 0 sz) as [m1b|] eqn: STZ; try discriminate.
  destruct (Genv.store_init_data_list ge m1b b1 0 (gvar_init gv)) as [m1c|] eqn:ST; try discriminate.
  exploit Mem.alloc_result; eauto. intros EQ. rewrite <- EQ in H1.
  destruct (Mem.alloc m2 0 sz) as (m2a, b2) eqn:ALLOC2.
  exploit Mem.alloc_result; eauto. intros EQ2. rewrite <- EQ2 in H1.
  assert (Mem.mem_inj init_meminj m1a m2a).
  { eapply Mem.alloc_left_mapped_inj with (b1 := b1) (b2 := b2) (delta := 0).
    eapply Mem.alloc_right_inj; eauto.
    eauto.
    eauto with mem. 
    red; intros; apply Z.divide_0_r.
    intros. apply Mem.perm_implies with Freeable; auto with mem. 
    eapply Mem.perm_alloc_2; eauto. omega. 
    auto.
  }
  exploit store_zeros_mapped_inj; eauto. intros (m2b & A & B).
  exploit store_init_data_list_mapped_inj; eauto. 
  intros. apply H2. red. exists ofs; auto. intros (m2c & C & D).
  exploit Mem.drop_mapped_inj; eauto. apply init_meminj_no_overlap. intros (m2' & E & F).
  exists m2'; split; auto. rewrite ! Zplus_0_r in E. rewrite A, C, E. auto.
Qed.

Lemma alloc_globals_app:
  forall F V (g: Genv.t F V) defs1 m defs2,
  Genv.alloc_globals g m (defs1 ++ defs2) =
  match Genv.alloc_globals g m defs1 with
  | None => None
  | Some m1 => Genv.alloc_globals g m1 defs2
  end.
Proof.
  induction defs1; simpl; intros. auto. 
  destruct (Genv.alloc_global g m a); auto. 
Qed.

Lemma alloc_globals_snoc:
  forall F V (g: Genv.t F V) m defs1 id_def,
  Genv.alloc_globals g m (defs1 ++ id_def :: nil) =
  match Genv.alloc_globals g m defs1 with
  | None => None
  | Some m1 => Genv.alloc_global g m1 id_def
  end.
Proof.
  intros. rewrite alloc_globals_app.
  destruct (Genv.alloc_globals g m defs1); auto. unfold Genv.alloc_globals. 
  destruct (Genv.alloc_global g m0 id_def); auto.
Qed.

Lemma alloc_globals_inj:
  forall pubs defs m1 u g1 g2,
  Genv.alloc_globals ge Mem.empty (List.rev defs) = Some m1 ->
  g1 = Genv.add_globals (Genv.empty_genv _ _ pubs) (List.rev defs) ->
  g2 = Genv.add_globals (Genv.empty_genv _ _ pubs) (filter_globdefs u nil defs) ->
  Mem.nextblock m1 = Genv.genv_next g1 ->
  (forall id, IS.In id u -> Genv.find_symbol g1 id = Genv.find_symbol ge id) ->
  (forall id, IS.In id u -> Genv.find_symbol g2 id = Genv.find_symbol tge id) ->
  (forall b id, Genv.find_symbol ge id = Some b -> Plt b (Mem.nextblock m1) -> kept id -> IS.In id u) ->
  (forall id, IS.In id u -> (fold_left add_def_prog_map (List.rev defs) (PTree.empty _))!id = pm!id) ->
  exists m2,
     Genv.alloc_globals tge Mem.empty (filter_globdefs u nil defs) = Some m2
  /\ Mem.nextblock m2 = Genv.genv_next g2
  /\ Mem.mem_inj init_meminj m1 m2.
Proof.
  induction defs; simpl; intros until g2; intros ALLOC GE1 GE2 NEXT1 SYMB1 SYMB2 SYMB3 PROGMAP.
- inv ALLOC. exists Mem.empty. intuition auto. constructor; intros.
  eelim Mem.perm_empty; eauto. 
  exploit init_meminj_invert; eauto. intros [A B]. subst delta. apply Z.divide_0_r. 
  eelim Mem.perm_empty; eauto.
- rewrite Genv.add_globals_app in GE1. simpl in GE1. 
  set (g1' := Genv.add_globals (Genv.empty_genv fundef unit pubs) (rev defs)) in *.
  rewrite alloc_globals_snoc in ALLOC.
  destruct (Genv.alloc_globals ge Mem.empty (rev defs)) as [m1'|] eqn:ALLOC1'; try discriminate.
  exploit Genv.alloc_global_nextblock; eauto. intros NEXTBLOCK1.
  assert (NEXTGE1: Genv.genv_next g1 = Pos.succ (Genv.genv_next g1')) by (rewrite GE1; reflexivity). 
  assert (NEXT1': Mem.nextblock m1' = Genv.genv_next g1') by (unfold block in *; xomega).
  rewrite fold_left_app in PROGMAP. simpl in PROGMAP.
  destruct a as [id gd]. unfold add_def_prog_map at 1 in PROGMAP. simpl in PROGMAP.
  destruct (IS.mem id u) eqn:MEM.
  + rewrite filter_globdefs_nil in *. rewrite alloc_globals_snoc. 
    rewrite Genv.add_globals_app in GE2. simpl in GE2.
    set (g2' := Genv.add_globals (Genv.empty_genv fundef unit pubs) (filter_globdefs (IS.remove id u) nil defs)) in *.
    assert (NEXTGE2: Genv.genv_next g2 = Pos.succ (Genv.genv_next g2')) by (rewrite GE2; reflexivity).
    assert (FS1: Genv.find_symbol ge id = Some (Mem.nextblock m1')).
    { rewrite <- SYMB1 by (apply IS.mem_2; auto).
      rewrite GE1. unfold Genv.find_symbol; simpl. rewrite PTree.gss. congruence. }
    exploit (IHdefs m1' (IS.remove id u) g1' g2'); eauto.
      intros. rewrite ISF.remove_iff in H; destruct H.
      rewrite <- SYMB1 by auto. rewrite GE1. unfold Genv.find_symbol; simpl. 
      rewrite PTree.gso; auto.
      intros. rewrite ISF.remove_iff in H; destruct H.
      rewrite <- SYMB2 by auto. rewrite GE2. unfold Genv.find_symbol; simpl. 
      rewrite PTree.gso; auto.
      intros. rewrite ISF.remove_iff. destruct (ident_eq id id0).
      subst id0. rewrite FS1 in H. inv H. eelim Plt_strict; eauto.
      exploit SYMB3. eexact H. unfold block in *; xomega. auto. tauto. 
      intros. rewrite ISF.remove_iff in H; destruct H. 
      rewrite <- PROGMAP by auto. rewrite PTree.gso by auto. auto.
    intros (m2' & A & B & C). fold g2' in B.
    assert (FS2: Genv.find_symbol tge id = Some (Mem.nextblock m2')).
    { rewrite <- SYMB2 by (apply IS.mem_2; auto).
      rewrite GE2. unfold Genv.find_symbol; simpl. rewrite PTree.gss. congruence. }
    assert (INJ: init_meminj (Mem.nextblock m1') = Some (Mem.nextblock m2', 0)).
    { apply Genv.find_invert_symbol in FS1. unfold init_meminj. rewrite FS1, FS2. auto. }
    exploit alloc_global_mapped_inj. eexact ALLOC. eexact C. exact INJ.
    intros. apply kept_closed with id gd. eapply transform_program_kept; eauto. 
    rewrite <- PROGMAP by (apply IS.mem_2; auto). apply PTree.gss. auto. 
    intros (m2 & D & E).
    exploit Genv.alloc_global_nextblock; eauto. intros NEXTBLOCK2. 
    exists m2; split. rewrite A, D. auto. 
    split. unfold block in *; xomega.
    auto.
  + exploit (IHdefs m1' u g1' g2); auto. 
    intros. rewrite <- SYMB1 by auto. rewrite GE1. 
    unfold Genv.find_symbol; simpl. rewrite PTree.gso; auto. 
    red; intros; subst id0. apply IS.mem_1 in H. congruence.
    intros. eapply SYMB3; eauto. unfold block in *; xomega.
    intros. rewrite <- PROGMAP by auto. rewrite PTree.gso; auto.
    apply IS.mem_1 in H. congruence.
    intros (m2 & A & B & C).
    assert (NOTINJ: init_meminj (Mem.nextblock m1') = None).
    { destruct (init_meminj (Mem.nextblock m1')) as [[b' delta]|] eqn:J; auto.
      exploit init_meminj_invert; eauto. intros (U & id1 & V & W).
      exploit SYMB3; eauto. unfold block in *; xomega.
      eapply transform_program_kept; eauto.
      intros P.
      revert V. rewrite <- SYMB1, GE1 by auto. unfold Genv.find_symbol; simpl.
      rewrite PTree.gsspec. rewrite NEXT1'. destruct (peq id1 id); intros Q. 
      subst id1. apply IS.mem_1 in P. congruence. 
      eelim Plt_strict. eapply Genv.genv_symb_range; eauto. }
    exists m2; intuition auto. eapply alloc_global_unmapped_inj; eauto.
Qed.

Theorem init_mem_inject:
  forall m,
  Genv.init_mem p = Some m ->
  exists f tm, Genv.init_mem tp = Some tm /\ Mem.inject f m tm /\ meminj_preserves_globals f.
Proof.
  intros.
  assert (AGI:=alloc_globals_inj).
  assert (IMPG:=init_meminj_preserves_globals).
  unfold transform_program in TRANSF; rewrite USED_GLOBALS in TRANSF; injection TRANSF. intros EQ.
  destruct (AGI (prog_public p) (List.rev (prog_defs p)) m used ge tge) as (tm & A & B & C).
  rewrite rev_involutive; auto. 
  rewrite rev_involutive; auto.
  unfold tge; rewrite <- EQ; auto.
  symmetry. apply Genv.init_mem_genv_next; auto. 
  auto. auto. auto.
  intros. rewrite rev_involutive. auto.
  assert (D: Genv.init_mem tp = Some tm).
  { unfold Genv.init_mem. fold tge. rewrite <- EQ. exact A. }
  exists init_meminj, tm; intuition auto.
  constructor; intros.
  + auto.
  + destruct (init_meminj b) as [[b1 delta1]|] eqn:INJ; auto.
    exploit init_meminj_invert; eauto. intros (P & id & Q & R).
    elim H0. eapply Genv.find_symbol_not_fresh; eauto.
  + exploit init_meminj_invert; eauto. intros (P & id & Q & R).
    eapply Genv.find_symbol_not_fresh; eauto.
  + apply init_meminj_no_overlap.
  + exploit init_meminj_invert; eauto. intros (P & id & Q & R). 
    split. omega. generalize (Int.unsigned_range_2 ofs). omega.
Qed.

Lemma transf_initial_states:
  forall S1, initial_state p S1 -> exists S2, initial_state tp S2 /\ match_states S1 S2.
Proof.
  intros. inv H. exploit init_mem_inject; eauto. intros (j & tm & A & B & C).
  exploit symbols_inject_2. eauto. apply kept_main. eexact H1. intros (tb & P & Q).
  exploit funct_ptr_inject. eauto. eexact Q. exact H2. 
  intros (R & S & T).
  exists (Callstate nil f nil tm); split.
  econstructor; eauto.
    fold tge. unfold transform_program in TRANSF; rewrite USED_GLOBALS in TRANSF; inversion TRANSF; auto. 
  econstructor; eauto.
  constructor. auto. 
  erewrite <- Genv.init_mem_genv_next by eauto. apply Ple_refl. 
  erewrite <- Genv.init_mem_genv_next by eauto. apply Ple_refl. 
Qed.

Lemma transf_final_states:
  forall S1 S2 r,
  match_states S1 S2 -> final_state S1 r -> final_state S2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. inv RESINJ. constructor. 
Qed.

Theorem transf_program_correct:
  forward_simulation (semantics p) (semantics tp).
Proof.
  intros. 
  eapply forward_simulation_step.
  exploit globals_symbols_inject. apply init_meminj_preserves_globals. intros [A B]. exact A.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact step_simulation.
Qed.

End SOUNDNESS.
