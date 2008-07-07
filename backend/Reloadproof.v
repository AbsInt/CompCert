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

(** Correctness proof for the [Reload] pass. *)

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
Require Import Conventions.
Require Import Allocproof.
Require Import LTLin.
Require Import LTLintyping.
Require Import Linear.
Require Import Parallelmove.
Require Import Reload.

(** * Exploitation of the typing hypothesis *)

(** Reloading is applied to LTLin code that is well-typed in
  the sense of [LTLintyping]. We exploit this hypothesis to obtain information on
  the number of arguments to operations, addressing modes and conditions. *)

Remark length_type_of_condition:
  forall (c: condition), (List.length (type_of_condition c) <= 3)%nat.
Proof.
  destruct c; unfold type_of_condition; simpl; omega.
Qed.

Remark length_type_of_operation:
  forall (op: operation), (List.length (fst (type_of_operation op)) <= 3)%nat.
Proof.
  destruct op; unfold type_of_operation; simpl; try omega.
  apply length_type_of_condition.
Qed.

Remark length_type_of_addressing:
  forall (addr: addressing), (List.length (type_of_addressing addr) <= 2)%nat.
Proof.
  destruct addr; unfold type_of_addressing; simpl; omega.
Qed.

Lemma length_op_args:
  forall (op: operation) (args: list loc) (res: loc),
  (List.map Loc.type args, Loc.type res) = type_of_operation op ->
  (List.length args <= 3)%nat.
Proof.
  intros. rewrite <- (list_length_map Loc.type). 
  generalize (length_type_of_operation op).
  rewrite <- H. simpl. auto.
Qed.

Lemma length_addr_args:
  forall (addr: addressing) (args: list loc),
  List.map Loc.type args = type_of_addressing addr ->
  (List.length args <= 2)%nat.
Proof.
  intros. rewrite <- (list_length_map Loc.type). 
  rewrite H. apply length_type_of_addressing.
Qed.

Lemma length_cond_args:
  forall (cond: condition) (args: list loc),
  List.map Loc.type args = type_of_condition cond ->
  (List.length args <= 3)%nat.
Proof.
  intros. rewrite <- (list_length_map Loc.type). 
  rewrite H. apply length_type_of_condition.
Qed.

(** * Correctness of the Linear constructors *)

(** This section proves theorems that establish the correctness of the
  Linear constructor functions such as [add_move].  The theorems are of
  the general form ``the generated Linear instructions execute and
  modify the location set in the expected way: the result location(s)
  contain the expected values; other, non-temporary locations keep
  their values''. *)

Section LINEAR_CONSTRUCTORS.

Variable ge: genv.
Variable stk: list stackframe.
Variable f: function.
Variable sp: val.

Lemma reg_for_spec:
  forall l,
  R(reg_for l) = l \/ In (R (reg_for l)) temporaries.
Proof.
  intros. unfold reg_for. destruct l. tauto.
  case (slot_type s); simpl; tauto.
Qed.

Lemma reg_for_diff:
  forall l l',
  Loc.diff l l' -> Loc.notin l' temporaries ->
  Loc.diff (R (reg_for l)) l'.
Proof.
  intros. destruct (reg_for_spec l). 
  rewrite H1; auto.
  apply Loc.diff_sym. eapply Loc.in_notin_diff; eauto.
Qed.

Lemma add_reload_correct:
  forall src dst k rs m,
  exists rs',
  star step ge (State stk f sp (add_reload src dst k) rs m)
            E0 (State stk f sp k rs' m) /\
  rs' (R dst) = rs src /\
  forall l, Loc.diff (R dst) l -> rs' l = rs l.
Proof.
  intros. unfold add_reload. destruct src.
  case (mreg_eq m0 dst); intro.
  subst dst. exists rs. split. apply star_refl. tauto.
  exists (Locmap.set (R dst) (rs (R m0)) rs).
  split. apply star_one; apply exec_Lop. reflexivity. 
  split. apply Locmap.gss. 
  intros; apply Locmap.gso; auto.
  exists (Locmap.set (R dst) (rs (S s)) rs).
  split. apply star_one; apply exec_Lgetstack. 
  split. apply Locmap.gss. 
  intros; apply Locmap.gso; auto.
Qed.

Lemma add_spill_correct:
  forall src dst k rs m,
  exists rs',
  star step ge (State stk f sp (add_spill src dst k) rs m)
            E0 (State stk f sp k rs' m) /\
  rs' dst = rs (R src) /\
  forall l, Loc.diff dst l -> rs' l = rs l.
Proof.
  intros. unfold add_spill. destruct dst.
  case (mreg_eq src m0); intro.
  subst src. exists rs. split. apply star_refl. tauto.
  exists (Locmap.set (R m0) (rs (R src)) rs).
  split. apply star_one. apply exec_Lop. reflexivity.
  split. apply Locmap.gss.
  intros; apply Locmap.gso; auto.
  exists (Locmap.set (S s) (rs (R src)) rs).
  split. apply star_one. apply exec_Lsetstack. 
  split. apply Locmap.gss.
  intros; apply Locmap.gso; auto.
Qed.

Lemma add_reloads_correct_rec:
  forall srcs itmps ftmps k rs m,
  (List.length srcs <= List.length itmps)%nat ->
  (List.length srcs <= List.length ftmps)%nat ->
  (forall r, In (R r) srcs -> In r itmps -> False) ->
  (forall r, In (R r) srcs -> In r ftmps -> False) ->
  list_disjoint itmps ftmps ->
  list_norepet itmps ->
  list_norepet ftmps ->
  exists rs',
  star step ge 
      (State stk f sp (add_reloads srcs (regs_for_rec srcs itmps ftmps) k) rs m)
   E0 (State stk f sp k rs' m) /\
  reglist rs' (regs_for_rec srcs itmps ftmps) = map rs srcs /\
  (forall r, ~(In r itmps) -> ~(In r ftmps) -> rs' (R r) = rs (R r)) /\
  (forall s, rs' (S s) = rs (S s)).
Proof.
  induction srcs; simpl; intros.
  (* base case *)
  exists rs. split. apply star_refl. tauto.
  (* inductive case *)
  destruct itmps; simpl in H. omegaContradiction.
  destruct ftmps; simpl in H0. omegaContradiction.
  assert (R1: (length srcs <= length itmps)%nat). omega.
  assert (R2: (length srcs <= length ftmps)%nat). omega.
  assert (R3: forall r, In (R r) srcs -> In r itmps -> False).
    intros. apply H1 with r. tauto. auto with coqlib. 
  assert (R4: forall r, In (R r) srcs -> In r ftmps -> False).
    intros. apply H2 with r. tauto. auto with coqlib.
  assert (R5: list_disjoint itmps ftmps).
    eapply list_disjoint_cons_left.
    eapply list_disjoint_cons_right. eauto.
  assert (R6: list_norepet itmps).
    inversion H4; auto.
  assert (R7: list_norepet ftmps).
    inversion H5; auto.
  destruct a.
  (* a is a register *)
  generalize (IHsrcs itmps ftmps k rs m R1 R2 R3 R4 R5 R6 R7).
  intros [rs' [EX [RES [OTH1 OTH2]]]].
  exists rs'. split.
  unfold add_reload. case (mreg_eq m2 m2); intro; tauto.
  split. simpl. apply (f_equal2 (@cons val)). 
  apply OTH1. 
  red; intro; apply H1 with m2. tauto. auto with coqlib.
  red; intro; apply H2 with m2. tauto. auto with coqlib.
  assumption.
  split. intros. apply OTH1. simpl in H6; tauto. simpl in H7; tauto.
  auto.
  (* a is a stack location *)
  set (tmp := match slot_type s with Tint => m0 | Tfloat => m1 end).
  assert (NI: ~(In tmp itmps)).
    unfold tmp; case (slot_type s).
    inversion H4; auto. 
    apply list_disjoint_notin with (m1 :: ftmps). 
    apply list_disjoint_sym. apply list_disjoint_cons_left with m0.
    auto. auto with coqlib.
  assert (NF: ~(In tmp ftmps)).
    unfold tmp; case (slot_type s).
    apply list_disjoint_notin with (m0 :: itmps). 
    apply list_disjoint_cons_right with m1.
    auto. auto with coqlib.
    inversion H5; auto. 
  generalize
    (add_reload_correct (S s) tmp
       (add_reloads srcs (regs_for_rec srcs itmps ftmps) k) rs m).
  intros [rs1 [EX1 [RES1 OTH]]].     
  generalize (IHsrcs itmps ftmps k rs1 m R1 R2 R3 R4 R5 R6 R7).
  intros [rs' [EX [RES [OTH1 OTH2]]]].
  exists rs'.
  split. eapply star_trans; eauto. traceEq.
  split. simpl. apply (f_equal2 (@cons val)). 
  rewrite OTH1; auto.
  rewrite RES. apply list_map_exten. intros.
  symmetry. apply OTH. 
  destruct x; try exact I. simpl. red; intro; subst m2.
  generalize H6; unfold tmp. case (slot_type s).
  intro. apply H1 with m0. tauto. auto with coqlib.
  intro. apply H2 with m1. tauto. auto with coqlib.
  split. intros. simpl in H6; simpl in H7.
  rewrite OTH1. apply OTH. 
  simpl. unfold tmp. case (slot_type s); tauto.
  tauto. tauto.
  intros. rewrite OTH2. apply OTH. exact I.
Qed.

Lemma add_reloads_correct:
  forall srcs k rs m,
  (List.length srcs <= 3)%nat ->
  Loc.disjoint srcs temporaries ->
  exists rs',
  star step ge (State stk f sp (add_reloads srcs (regs_for srcs) k) rs m)
            E0 (State stk f sp k rs' m) /\
  reglist rs' (regs_for srcs) = List.map rs srcs /\
  forall l, Loc.notin l temporaries -> rs' l = rs l.
Proof.
  intros.
  pose (itmps := IT1 :: IT2 :: IT3 :: nil).
  pose (ftmps := FT1 :: FT2 :: FT3 :: nil).
  assert (R1: (List.length srcs <= List.length itmps)%nat).
    unfold itmps; simpl; assumption.
  assert (R2: (List.length srcs <= List.length ftmps)%nat).
    unfold ftmps; simpl; assumption.
  assert (R3: forall r, In (R r) srcs -> In r itmps -> False).
    intros. assert (In (R r) temporaries). 
    simpl in H2; simpl; intuition congruence.
    generalize (H0 _ _ H1 H3). simpl. tauto.
  assert (R4: forall r, In (R r) srcs -> In r ftmps -> False).
    intros. assert (In (R r) temporaries). 
    simpl in H2; simpl; intuition congruence.
    generalize (H0 _ _ H1 H3). simpl. tauto.
  assert (R5: list_disjoint itmps ftmps).
    red; intros r1 r2; simpl; intuition congruence.
  assert (R6: list_norepet itmps).
    unfold itmps. NoRepet.
  assert (R7: list_norepet ftmps).
    unfold ftmps. NoRepet.
  generalize (add_reloads_correct_rec srcs itmps ftmps k rs m
                R1 R2 R3 R4 R5 R6 R7).
  intros [rs' [EX [RES [OTH1 OTH2]]]].
  exists rs'. split. exact EX. 
  split. exact RES.
  intros. destruct l. apply OTH1.
  generalize (Loc.notin_not_in _ _ H1). simpl. intuition congruence.
  generalize (Loc.notin_not_in _ _ H1). simpl. intuition congruence.
  apply OTH2.
Qed.

Lemma add_move_correct:
  forall src dst k rs m,
  exists rs',
  star step ge (State stk f sp (add_move src dst k) rs m)
            E0 (State stk f sp k rs' m) /\
  rs' dst = rs src /\
  forall l, Loc.diff l dst -> Loc.diff l (R IT1) -> Loc.diff l (R FT1) -> rs' l = rs l.
Proof.
  intros; unfold add_move.
  case (Loc.eq src dst); intro.
  subst dst. exists rs. split. apply star_refl. tauto.
  destruct src.
  (* src is a register *)
  generalize (add_spill_correct m0 dst k rs m); intros [rs' [EX [RES OTH]]].
  exists rs'; intuition. apply OTH; apply Loc.diff_sym; auto.
  destruct dst.
  (* src is a stack slot, dst a register *)
  generalize (add_reload_correct (S s) m0 k rs m); intros [rs' [EX [RES OTH]]].
  exists rs'; intuition. apply OTH; apply Loc.diff_sym; auto.
  (* src and dst are stack slots *)
  set (tmp := match slot_type s with Tint => IT1 | Tfloat => FT1 end).
  generalize (add_reload_correct (S s) tmp (add_spill tmp (S s0) k) rs m);
  intros [rs1 [EX1 [RES1 OTH1]]].
  generalize (add_spill_correct tmp (S s0) k rs1 m);
  intros [rs2 [EX2 [RES2 OTH2]]].
  exists rs2. split.
  eapply star_trans; eauto. traceEq.
  split. congruence.
  intros. rewrite OTH2. apply OTH1. 
  apply Loc.diff_sym. unfold tmp; case (slot_type s); auto.
  apply Loc.diff_sym; auto.
Qed.

Lemma effect_move_sequence:
  forall k moves rs m,
  let k' := List.fold_right (fun p k => add_move (fst p) (snd p) k) k moves in
  exists rs',
  star step ge (State stk f sp k' rs m)
            E0 (State stk f sp k rs' m) /\
  effect_seqmove moves rs rs'.
Proof.
  induction moves; intros until m; simpl.
  exists rs; split. constructor. constructor.
  destruct a as [src dst]; simpl.
  set (k1 := fold_right
              (fun (p : loc * loc) (k : code) => add_move (fst p) (snd p) k)
              k moves) in *.
  destruct (add_move_correct src dst k1 rs m) as [rs1 [A [B C]]].
  destruct (IHmoves rs1 m) as [rs' [D E]].
  exists rs'; split. 
  eapply star_trans; eauto. traceEq.
  econstructor; eauto. red. tauto. 
Qed.

Lemma parallel_move_correct:
  forall srcs dsts k rs m,
  List.length srcs = List.length dsts ->
  Loc.no_overlap srcs dsts ->
  Loc.norepet dsts ->
  Loc.disjoint srcs temporaries ->
  Loc.disjoint dsts temporaries ->
  exists rs',
  star step ge (State stk f sp (parallel_move srcs dsts k) rs m)
               E0 (State stk f sp k rs' m) /\
  List.map rs' dsts = List.map rs srcs /\
  rs' (R IT3) = rs (R IT3) /\
  forall l, Loc.notin l dsts -> Loc.notin l temporaries -> rs' l = rs l.
Proof.
  intros. 
  generalize (effect_move_sequence k (parmove srcs dsts) rs m).
  intros [rs' [EXEC EFFECT]].
  exists rs'. split. exact EXEC. 
  apply effect_parmove; auto.
Qed.

Lemma parallel_move_arguments_correct:
  forall args sg k rs m,
  List.map Loc.type args = sg.(sig_args) ->
  locs_acceptable args ->
  exists rs',
  star step ge (State stk f sp (parallel_move args (loc_arguments sg) k) rs m)
            E0 (State stk f sp k rs' m) /\
  List.map rs' (loc_arguments sg) = List.map rs args /\
  rs' (R IT3) = rs (R IT3) /\
  forall l, Loc.notin l (loc_arguments sg) -> Loc.notin l temporaries -> rs' l = rs l.
Proof.
  intros. apply parallel_move_correct.
  transitivity (length sg.(sig_args)).
  rewrite <- H. symmetry; apply list_length_map. 
  symmetry. apply loc_arguments_length.
  apply no_overlap_arguments; auto.
  apply loc_arguments_norepet.
  apply locs_acceptable_disj_temporaries; auto.
  apply loc_arguments_not_temporaries.
Qed.

Lemma parallel_move_parameters_correct:
  forall params sg k rs m,
  List.map Loc.type params = sg.(sig_args) ->
  locs_acceptable params ->
  Loc.norepet params ->
  exists rs',
  star step ge (State stk f sp (parallel_move (loc_parameters sg) params k) rs m)
            E0 (State stk f sp k rs' m) /\
  List.map rs' params = List.map rs (loc_parameters sg) /\
  rs' (R IT3) = rs (R IT3) /\
  forall l, Loc.notin l params -> Loc.notin l temporaries -> rs' l = rs l.
Proof.
  intros. apply parallel_move_correct.
  transitivity (length sg.(sig_args)).
  apply loc_parameters_length.
  rewrite <- H. apply list_length_map.
  apply no_overlap_parameters; auto.
  auto. apply loc_parameters_not_temporaries. 
  apply locs_acceptable_disj_temporaries; auto.
Qed.

End LINEAR_CONSTRUCTORS.

(** * Agreement between values of locations *)

(** The predicate [agree] states that two location maps
  give the same values to all acceptable locations,
  that is, non-temporary registers and [Local] stack slots. *)

Definition agree (rs1 rs2: locset) : Prop :=
  forall l, loc_acceptable l -> rs2 l = rs1 l.

Lemma agree_loc:
  forall rs1 rs2 l,
  agree rs1 rs2 -> loc_acceptable l -> rs2 l = rs1 l.
Proof.
  auto.
Qed.

Lemma agree_locs:
  forall rs1 rs2 ll,
  agree rs1 rs2 -> locs_acceptable ll -> map rs2 ll = map rs1 ll.
Proof.
  induction ll; simpl; intros.
  auto.
  f_equal. apply H. apply H0; auto with coqlib.
  apply IHll; auto. red; intros. apply H0; auto with coqlib.
Qed.

Lemma agree_exten:
  forall rs ls1 ls2,
  agree rs ls1 ->
  (forall l, Loc.notin l temporaries -> ls2 l = ls1 l) ->
  agree rs ls2.
Proof.
  intros; red; intros. rewrite H0. auto. 
  apply temporaries_not_acceptable; auto.
Qed.

Lemma agree_set:
  forall rs1 rs2 rs2' l v,
  loc_acceptable l ->
  rs2' l = v ->
  (forall l', Loc.diff l l' -> Loc.notin l' temporaries -> rs2' l' = rs2 l') ->
  agree rs1 rs2 -> agree (Locmap.set l v rs1) rs2'.
Proof.
  intros; red; intros.
  destruct (Loc.eq l l0).
  subst l0. rewrite Locmap.gss. auto.
  assert (Loc.diff l l0). eapply loc_acceptable_noteq_diff; eauto.
  rewrite Locmap.gso; auto. rewrite H1. auto. auto.
  apply temporaries_not_acceptable; auto. 
Qed.

Lemma agree_return_regs:
  forall rs1 ls1 rs2 ls2,
  agree rs1 ls1 -> agree rs2 ls2 ->
  agree (LTL.return_regs rs1 rs2) (LTL.return_regs ls1 ls2).
Proof.
  intros; red; intros. unfold LTL.return_regs.
  assert (~In l temporaries). 
  apply Loc.notin_not_in. apply temporaries_not_acceptable; auto.
  destruct l.
  destruct (In_dec Loc.eq (R m) temporaries). contradiction.
  destruct (In_dec Loc.eq (R m) destroyed_at_call); auto.
  auto.
Qed.

Lemma agree_set_result:
  forall rs1 ls1 rs2 ls2 sig res ls3,
  loc_acceptable res -> agree rs1 ls1 -> agree rs2 ls2 ->
  ls3 res = LTL.return_regs ls1 ls2 (R (loc_result sig)) ->
  (forall l : loc, Loc.diff res l -> ls3 l = LTL.return_regs ls1 ls2 l) ->
  let rs_merge := LTL.return_regs rs1 rs2 in
  agree (Locmap.set res (rs_merge (R (loc_result sig))) rs_merge) ls3.
Proof.
  intros. apply agree_set with (LTL.return_regs ls1 ls2); auto.
  rewrite H2; unfold rs_merge. 
  repeat rewrite return_regs_result. apply H1. apply loc_result_acceptable.
  unfold rs_merge. apply agree_return_regs; auto.
Qed.

(** [agree_arguments] and [agree_parameters] are two stronger
  variants of the predicate [agree].  They additionally demand
  equality of the values of locations that are arguments or parameters
  (respectively) for a call to a function of signature [sg]. *)

Definition agree_arguments (sg: signature) (rs1 rs2: locset) : Prop :=
  forall l, loc_acceptable l \/ In l (loc_arguments sg) -> rs2 l = rs1 l.

Definition agree_parameters (sg: signature) (rs1 rs2: locset) : Prop :=
  forall l, loc_acceptable l \/ In l (loc_parameters sg) -> rs2 l = rs1 l.

Remark parallel_assignment:
  forall (P: loc -> Prop) (rs1 rs2 ls1 ls2: locset) srcs dsts,
  map rs2 dsts = map rs1 srcs ->
  map ls2 dsts = map ls1 srcs ->
  (forall l, In l srcs -> P l) ->
  (forall l, P l -> ls1 l = rs1 l) ->
  (forall l, In l dsts -> ls2 l = rs2 l).
Proof.
  induction srcs; destruct dsts; simpl; intros; try congruence.
  contradiction.
  inv H; inv H0. elim H3; intro. subst l0.
  rewrite H5; rewrite H4. auto with coqlib.
  eapply IHsrcs; eauto. 
Qed.

Lemma agree_set_arguments:
  forall rs1 ls1 ls2 args sg,
  agree rs1 ls1 ->
  List.map Loc.type args = sg.(sig_args) ->
  locs_acceptable args ->
  List.map ls2 (loc_arguments sg) = map ls1 args ->
  (forall l : loc,
    Loc.notin l (loc_arguments sg) ->
    Loc.notin l temporaries -> ls2 l = ls1 l) ->
  agree_arguments sg (LTL.parmov args (loc_arguments sg) rs1) ls2.
Proof.
  intros.  
  assert (Loc.norepet (loc_arguments sg)).
    apply loc_arguments_norepet.
  assert (List.length args = List.length (loc_arguments sg)).
    rewrite loc_arguments_length. rewrite <- H0.
    symmetry. apply list_length_map.
  destruct (parmov_spec rs1 _ _ H4 H5) as [A B].
  set (rs2 := LTL.parmov args (loc_arguments sg) rs1) in *.
  assert (forall l, In l (loc_arguments sg) -> ls2 l = rs2 l).
    intros.
    eapply parallel_assignment with (P := loc_acceptable); eauto.
  red; intros. 
  destruct (In_dec Loc.eq l (loc_arguments sg)).
  auto.
  assert (loc_acceptable l) by tauto.
  assert (Loc.notin l (loc_arguments sg)).
    eapply loc_acceptable_notin_notin; eauto.
  rewrite H3; auto. rewrite B; auto. 
  apply temporaries_not_acceptable; auto.
Qed.

Lemma agree_arguments_agree:
  forall sg rs ls, agree_arguments sg rs ls -> agree rs ls.
Proof.
  intros; red; intros; auto.
Qed.

Lemma agree_arguments_locs:
  forall sg rs1 rs2,
  agree_arguments sg rs1 rs2 ->
  map rs2 (loc_arguments sg) = map rs1 (loc_arguments sg).
Proof.
  intros.
  assert (forall ll, incl ll (loc_arguments sg) -> map rs2 ll = map rs1 ll).
    induction ll; simpl; intros. auto.
    f_equal. apply H. right. apply H0. auto with coqlib.
    apply IHll. eapply incl_cons_inv; eauto.
  apply H0. apply incl_refl.
Qed.

Lemma agree_set_parameters:
  forall rs1 ls1 ls2 sg params,
  agree_parameters sg rs1 ls1 ->
  List.map Loc.type params = sg.(sig_args) ->
  locs_acceptable params ->
  Loc.norepet params ->
  List.map ls2 params = List.map ls1 (loc_parameters sg) ->
  (forall l : loc,
    Loc.notin l params ->
    Loc.notin l temporaries -> ls2 l = ls1 l) ->
  agree (LTL.parmov (loc_parameters sg) params rs1) ls2.
Proof.
  intros.
  assert (List.length (loc_parameters sg) = List.length params).
    unfold loc_parameters. rewrite list_length_map. 
    rewrite loc_arguments_length. rewrite <- H0.
    apply list_length_map.
  destruct (parmov_spec rs1 _ _ H2 H5) as [A B].
  set (rs2 := LTL.parmov (loc_parameters sg) params rs1) in *.
  red; intros.
  assert (forall l, In l params -> ls2 l = rs2 l).
    intros.
    eapply parallel_assignment with (P := fun l => In l (loc_parameters sg)); eauto.
  destruct (In_dec Loc.eq l params).
  auto.
  assert (Loc.notin l params).
    eapply loc_acceptable_notin_notin; eauto.
  rewrite B; auto. rewrite H4; auto. 
  apply temporaries_not_acceptable; auto.
Qed.

Lemma agree_call_regs:
  forall sg rs ls,
  agree_arguments sg rs ls ->
  agree_parameters sg (LTL.call_regs rs) (LTL.call_regs ls).
Proof.
  intros; red; intros. elim H0.
  destruct l; simpl; auto. destruct s; auto.
  unfold loc_parameters. intro. 
  destruct (list_in_map_inv _ _ _ H1) as [r [A B]].
  subst l. generalize (loc_arguments_acceptable _ _ B). 
  destruct r; simpl; auto. destruct s; simpl; auto.
Qed.

Lemma agree_arguments_return_regs:
  forall sg rs1 rs2 ls1 ls2,
  tailcall_possible sg ->
  agree rs1 ls1 ->
  agree_arguments sg rs2 ls2 ->
  agree_arguments sg (LTL.return_regs rs1 rs2) (LTL.return_regs ls1 ls2).
Proof.
  intros; red; intros. generalize (H1 l H2). intro.
  elim H2; intro. generalize (H0 l H4); intro. 
  unfold LTL.return_regs. destruct l; auto.
  destruct (In_dec Loc.eq (R m) temporaries); auto.
  destruct (In_dec Loc.eq (R m) destroyed_at_call); auto.
  generalize (H l H4). unfold LTL.return_regs; destruct l; intro.
  destruct (In_dec Loc.eq (R m) temporaries); auto.
  destruct (In_dec Loc.eq (R m) destroyed_at_call); auto.
  contradiction.
Qed.

(** * Preservation of labels and gotos *)

Lemma find_label_add_spill:
  forall lbl src dst k,
  find_label lbl (add_spill src dst k) = find_label lbl k.
Proof.
  intros. destruct dst; simpl; auto.
  destruct (mreg_eq src m); auto.
Qed.

Lemma find_label_add_reload:
  forall lbl src dst k,
  find_label lbl (add_reload src dst k) = find_label lbl k.
Proof.
  intros. destruct src; simpl; auto.
  destruct (mreg_eq m dst); auto.
Qed.

Lemma find_label_add_reloads:
  forall lbl srcs dsts k,
  find_label lbl (add_reloads srcs dsts k) = find_label lbl k.
Proof.
  induction srcs; intros; simpl. auto.
  destruct dsts; auto. rewrite find_label_add_reload. auto.
Qed.

Lemma find_label_add_move:
  forall lbl src dst k,
  find_label lbl (add_move src dst k) = find_label lbl k.
Proof.
  intros; unfold add_move.
  destruct (Loc.eq src dst); auto.
  destruct src. apply find_label_add_spill.
  destruct dst. apply find_label_add_reload.
  rewrite find_label_add_reload. apply find_label_add_spill.
Qed.

Lemma find_label_parallel_move:
  forall lbl srcs dsts k,
  find_label lbl (parallel_move srcs dsts k) = find_label lbl k.
Proof.
  intros. unfold parallel_move. generalize (parmove srcs dsts). 
  induction m; simpl. auto.
  rewrite find_label_add_move. auto.
Qed.

Hint Rewrite find_label_add_spill find_label_add_reload
             find_label_add_reloads find_label_add_move
             find_label_parallel_move: labels.

Opaque reg_for.

Ltac FL := simpl; autorewrite with labels; auto.

Lemma find_label_transf_instr:
  forall lbl sg instr k,
  find_label lbl (transf_instr sg instr k) =
  if LTLin.is_label lbl instr then Some k else find_label lbl k.
Proof.
  intros. destruct instr; FL.
  destruct (is_move_operation o l); FL; FL.
  FL.
  destruct s0; FL; FL; FL.
  destruct s0; FL; FL; FL.
  FL.
  destruct o; FL.
Qed.

Lemma find_label_transf_code:
  forall sg lbl c,
  find_label lbl (transf_code sg c) =
  option_map (transf_code sg) (LTLin.find_label lbl c).
Proof.
  induction c; simpl.
  auto.
  rewrite find_label_transf_instr.
  destruct (LTLin.is_label lbl a); auto.
Qed.

Lemma find_label_transf_function:
  forall lbl f c,
  LTLin.find_label lbl (LTLin.fn_code f) = Some c ->
  find_label lbl (Linear.fn_code (transf_function f)) =
  Some (transf_code f c).
Proof.
  intros. destruct f; simpl in *. FL. 
  rewrite find_label_transf_code. rewrite H; auto.
Qed.

(** * Semantic preservation *)

Section PRESERVATION.

Variable prog: LTLin.program.
Let tprog := transf_program prog.
Hypothesis WT_PROG: LTLintyping.wt_program prog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (@Genv.find_funct_transf _ _ _ transf_fundef prog).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof (@Genv.find_funct_ptr_transf _ _ _ transf_fundef prog).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (@Genv.find_symbol_transf _ _ _ transf_fundef prog).

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = LTLin.funsig f.
Proof.
  destruct f; reflexivity.
Qed.

Lemma find_function_wt:
  forall ros rs f,
  LTLin.find_function ge ros rs = Some f -> wt_fundef f.
Proof.
  intros until f. destruct ros; simpl.
  intro. eapply Genv.find_funct_prop with (p := prog); eauto. 
  caseEq (Genv.find_symbol ge i); intros. 
  eapply Genv.find_funct_ptr_prop with (p := prog); eauto. 
  congruence.
Qed.

(** The [match_state] predicate relates states in the original LTLin
  program and the transformed Linear program.  The main property
  it enforces are:
- Agreement between the values of locations in the two programs,
  according to the [agree] or [agree_arguments] predicates.
- Lists of LTLin instructions appearing in the source state
  are always suffixes of the code for the corresponding functions.
- Well-typedness of the source code, which ensures that
  only acceptable locations are accessed by this code.
*)

Inductive match_stackframes: list LTLin.stackframe -> list Linear.stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes nil nil
  | match_stackframes_cons:
      forall res f sp c rs s s' c' ls sig,
      match_stackframes s s' ->
      sig_res (LTLin.fn_sig f) = sig_res (parent_callsig s) ->
      c' = add_spill (loc_result sig) res (transf_code f c) ->      
      agree rs ls ->
      loc_acceptable res ->
      wt_function f ->
      is_tail c (LTLin.fn_code f) ->
      match_stackframes (LTLin.Stackframe sig res f sp rs c :: s)
                        (Linear.Stackframe (transf_function f) sp ls c' :: s').

Inductive match_states: LTLin.state -> Linear.state -> Prop :=
  | match_states_intro:
      forall s f sp c rs m s' ls
        (STACKS: match_stackframes s s')
        (SIG: sig_res (LTLin.fn_sig f) = sig_res (parent_callsig s))
        (AG: agree rs ls)
        (WT: wt_function f)
        (TL: is_tail c (LTLin.fn_code f)),
      match_states (LTLin.State s f sp c rs m)
                   (Linear.State s' (transf_function f) sp (transf_code f c) ls m)
  | match_states_call:
      forall s f rs m s' ls
        (STACKS: match_stackframes s s')
        (SIG: sig_res (LTLin.funsig f) = sig_res (parent_callsig s))
        (AG: agree_arguments (LTLin.funsig f) rs ls)
        (WT: wt_fundef f),
      match_states (LTLin.Callstate s f rs m)
                   (Linear.Callstate s' (transf_fundef f) ls m)
  | match_states_return:
      forall s rs m s' ls
        (STACKS: match_stackframes s s')
        (AG: agree rs ls),
      match_states (LTLin.Returnstate s rs m)
                   (Linear.Returnstate s' ls m).

Remark parent_locset_match:
  forall s s',
  match_stackframes s s' ->
  agree (LTLin.parent_locset s) (parent_locset s').
Proof.
  induction 1; simpl.
  red; intros; auto.
  auto.
Qed.
         
Ltac ExploitWT :=
  match goal with
  | [ WT: wt_function _, TL: is_tail _ _ |- _ ] =>
       generalize (wt_instrs _ WT _ (is_tail_in TL)); intro WTI
  end.

(** The proof of semantic preservation is a simulation argument
  based on diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  It is possible for the transformed code to take no transition,
  remaining in the same state; for instance, if the source transition
  corresponds to a move instruction that was eliminated.  
  To ensure that this cannot occur infinitely often in a row,
  we use the following [measure] function that just counts the 
  remaining number of instructions in the source code sequence. *)

Definition measure (st: LTLin.state) : nat :=
  match st with
  | LTLin.State s f sp c ls m => List.length c
  | LTLin.Callstate s f ls m => 0%nat
  | LTLin.Returnstate s ls m => 0%nat
  end.

Theorem transf_step_correct:
  forall s1 t s2, LTLin.step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  (exists s2', plus Linear.step tge s1' t s2' /\ match_states s2 s2')
  \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.
Proof.
  Opaque regs_for. Opaque add_reloads.
  induction 1; intros; try inv MS; simpl.

  (* Lop *)
  ExploitWT. inv WTI. 
  (* move *)
  simpl.
  destruct (add_move_correct tge s' (transf_function f) sp r1 res (transf_code f b) ls m)
        as [ls2 [A [B C]]].
  inv A. 
  right. split. omega. split. auto.
  rewrite H1. rewrite H1. econstructor; eauto with coqlib. 
  apply agree_set with ls2; auto.
  rewrite B. simpl in H; inversion H. auto.
  left; econstructor; split. eapply plus_left; eauto. 
  econstructor; eauto with coqlib. 
  apply agree_set with ls; auto.
  rewrite B. simpl in H; inversion H. auto.
  intros. simpl in H1. apply C. apply Loc.diff_sym; auto.
  simpl in H7; tauto. simpl in H7; tauto.
  (* other ops *)
  assert (is_move_operation op args = None).
    caseEq (is_move_operation op args); intros.
    destruct (is_move_operation_correct _ _ H0). congruence.
    auto.
  rewrite H0.
  exploit add_reloads_correct. 
    eapply length_op_args; eauto.
    apply locs_acceptable_disj_temporaries; auto.
  intros [ls2 [A [B C]]].
  exploit add_spill_correct.
  intros [ls3 [D [E F]]].
  left; econstructor; split.
  eapply star_plus_trans. eexact A. 
  eapply plus_left. eapply exec_Lop with (v := v).
    rewrite <- H. rewrite B. rewrite (agree_locs _ _ _ AG H5). 
    apply eval_operation_preserved. exact symbols_preserved.
  eexact D. eauto. traceEq.
  econstructor; eauto with coqlib.
  apply agree_set with ls; auto.
  rewrite E. apply Locmap.gss.
  intros. rewrite F; auto. rewrite Locmap.gso. auto. 
  apply reg_for_diff; auto.

  (* Lload *)
  ExploitWT; inv WTI.
  exploit add_reloads_correct. 
    apply le_S. eapply length_addr_args; eauto.
    apply locs_acceptable_disj_temporaries; auto.
  intros [ls2 [A [B C]]].
  exploit add_spill_correct.
  intros [ls3 [D [E F]]].
  left; econstructor; split.
  eapply star_plus_trans. eauto. 
  eapply plus_left. eapply exec_Lload; eauto.
    rewrite B. rewrite <- H. rewrite (agree_locs _ _ _ AG H7).
    apply eval_addressing_preserved. exact symbols_preserved.
  eauto. auto. traceEq.
  econstructor; eauto with coqlib.
  apply agree_set with ls; auto.
  rewrite E. apply Locmap.gss.
  intros. rewrite F; auto. rewrite Locmap.gso. auto. 
  apply reg_for_diff; auto.

  (* Lstore *)
  ExploitWT; inv WTI.
  assert (exists rsrc, exists rargs, regs_for (src :: args) = rsrc :: rargs).
    Transparent regs_for. unfold regs_for. simpl.
    destruct src. econstructor; econstructor; eauto.
    destruct (slot_type s0);  econstructor; econstructor; eauto.
  destruct H1 as [rsrc [rargs EQ]]. rewrite EQ. 
  assert (length (src :: args) <= 3)%nat. 
    simpl. apply le_n_S.
    eapply length_addr_args; eauto.
  exploit add_reloads_correct.
    eauto. apply locs_acceptable_disj_temporaries; auto.
    red; intros. elim H2; intro; auto. subst l; auto. 
  intros [ls2 [A [B C]]]. rewrite EQ in A. rewrite EQ in B.
  injection B. intros D E. 
  simpl in B.
  left; econstructor; split. 
  eapply plus_right. eauto. 
  eapply exec_Lstore with (a := a); eauto.
    rewrite D. rewrite <- H. rewrite (agree_locs _ _ _ AG H7).
    apply eval_addressing_preserved. exact symbols_preserved.
  rewrite E. rewrite (agree_loc _ _ _ AG H8). eauto.
  traceEq.
  econstructor; eauto with coqlib.
  apply agree_exten with ls; auto.

  (* Lcall *)
  inversion MS. subst s0 f0 sp0 c rs0 m0.
  simpl transf_code.
  ExploitWT. inversion WTI. subst sig0 ros0 args0 res0.
  assert (WTF': wt_fundef f'). eapply find_function_wt; eauto.
  destruct ros as [fn | id].
  (* indirect call *)
  destruct (add_reload_correct tge s' (transf_function f) sp fn IT3
              (parallel_move args (loc_arguments sig)
                (Lcall sig (inl ident IT3)
                 :: add_spill (loc_result sig) res (transf_code f b)))
              ls m)
  as [ls2 [A [B C]]].
  destruct (parallel_move_arguments_correct tge s' (transf_function f) sp 
              args sig
              (Lcall sig (inl ident IT3)
                :: add_spill (loc_result sig) res (transf_code f b))
              ls2 m H7 H10)
  as [ls3 [D [E [F G]]]].
  assert (AG_ARGS: agree_arguments (LTLin.funsig f') rs1 ls3).
    rewrite <- H0.
    unfold rs1. apply agree_set_arguments with ls; auto.
    rewrite E. apply list_map_exten; intros. symmetry. apply C.
    assert (Loc.notin x temporaries). apply temporaries_not_acceptable; auto.
    simpl in H3. apply Loc.diff_sym. tauto.
    intros. rewrite G; auto. apply C. 
    simpl in H3. apply Loc.diff_sym. tauto.
  left; econstructor; split.
  eapply star_plus_trans. eauto. eapply plus_right. eauto. 
  eapply exec_Lcall; eauto.
    simpl. rewrite F. rewrite B. 
    rewrite (agree_loc rs ls fn); auto.
    apply functions_translated. eauto.
    rewrite H0; symmetry; apply sig_preserved.
  eauto. traceEq.
  econstructor; eauto. 
  econstructor; eauto with coqlib.
  eapply agree_arguments_agree; eauto.
  simpl. congruence. 
  (* direct call *)
  destruct (parallel_move_arguments_correct tge s' (transf_function f) sp
              args sig
              (Lcall sig (inr mreg id)
                :: add_spill (loc_result sig) res (transf_code f b))
              ls m H7 H10)
  as [ls3 [D [E [F G]]]].
  assert (AG_ARGS: agree_arguments (LTLin.funsig f') rs1 ls3).
    rewrite <- H0.
    unfold rs1. apply agree_set_arguments with ls; auto.
  left; econstructor; split.
  eapply plus_right. eauto.
  eapply exec_Lcall; eauto.
    simpl. rewrite symbols_preserved. 
    generalize H; simpl. destruct (Genv.find_symbol ge id).
    apply function_ptr_translated; auto. congruence.
    rewrite H0. symmetry; apply sig_preserved.
  traceEq.
  econstructor; eauto.
  econstructor; eauto with coqlib.
  eapply agree_arguments_agree; eauto.
  simpl; congruence.

  (* Ltailcall *)
  inversion MS. subst s0 f0 sp c rs0 m0 s1'.
  simpl transf_code.
  ExploitWT. inversion WTI. subst sig0 ros0 args0.
  assert (WTF': wt_fundef f'). eapply find_function_wt; eauto.
  destruct ros as [fn | id].
  (* indirect call *)
  destruct (add_reload_correct tge s' (transf_function f) (Vptr stk Int.zero) fn IT3
              (parallel_move args (loc_arguments sig)
                (Ltailcall sig (inl ident IT3) :: transf_code f b))
              ls m)
  as [ls2 [A [B C]]].
  destruct (parallel_move_arguments_correct tge s' (transf_function f) (Vptr stk Int.zero)
              args sig
              (Ltailcall sig (inl ident IT3) :: transf_code f b)
              ls2 m H5 H7)
  as [ls3 [D [E [F G]]]].
  assert (AG_ARGS: agree_arguments (LTLin.funsig f') rs2 (LTL.return_regs (parent_locset s') ls3)).
    rewrite <- H0. unfold rs2. 
    apply agree_arguments_return_regs; auto.
    eapply parent_locset_match; eauto.  
    unfold rs1. apply agree_set_arguments with ls; auto.
    rewrite E. apply list_map_exten; intros. symmetry. apply C.
    assert (Loc.notin x temporaries). apply temporaries_not_acceptable; auto.
    simpl in H2. apply Loc.diff_sym. tauto.
    intros. rewrite G; auto. apply C. 
    simpl in H2. apply Loc.diff_sym. tauto.
  left; econstructor; split.
  eapply star_plus_trans. eauto. eapply plus_right. eauto.
  eapply exec_Ltailcall; eauto.
    simpl. rewrite F. rewrite B. 
    rewrite (agree_loc rs ls fn); auto.
    apply functions_translated. eauto.
    rewrite H0; symmetry; apply sig_preserved.
  eauto. traceEq.
  econstructor; eauto. congruence. 
 
  (* direct call *)
  destruct (parallel_move_arguments_correct tge s' (transf_function f) (Vptr stk Int.zero)
              args sig
              (Ltailcall sig (inr mreg id) :: transf_code f b)
              ls m H5 H7)
  as [ls3 [D [E [F G]]]].
  assert (AG_ARGS: agree_arguments (LTLin.funsig f') rs2 (LTL.return_regs (parent_locset s') ls3)).
    rewrite <- H0. unfold rs2. 
    apply agree_arguments_return_regs; auto.
    eapply parent_locset_match; eauto.  
    unfold rs1. apply agree_set_arguments with ls; auto.
  left; econstructor; split.
  eapply plus_right. eauto.
  eapply exec_Ltailcall; eauto.
    simpl. rewrite symbols_preserved. 
    generalize H; simpl. destruct (Genv.find_symbol ge id).
    apply function_ptr_translated; auto. congruence.
    rewrite H0. symmetry; apply sig_preserved.
  traceEq.
  econstructor; eauto. congruence.

  (* Lalloc *)
  ExploitWT; inv WTI.
  exploit add_reload_correct. intros [ls2 [A [B C]]]. 
  exploit add_spill_correct. intros [ls3 [D [E F]]].
  left; econstructor; split.
  eapply star_plus_trans. eauto. 
  eapply plus_left. eapply exec_Lalloc; eauto.
    rewrite B. rewrite <- H. apply AG. auto.
  eauto. eauto. traceEq.
  econstructor; eauto with coqlib.
  unfold rs3; apply agree_set with (Locmap.set (R loc_alloc_result) (Vptr blk Int.zero) ls2).
  auto. rewrite E. rewrite Locmap.gss. 
  unfold rs2; rewrite Locmap.gss. auto.
  auto.
  unfold rs2. apply agree_set with ls2.
  unfold loc_alloc_result; simpl; intuition congruence.
  apply Locmap.gss. intros. apply Locmap.gso; auto.
  unfold rs1. apply agree_set with ls.
  unfold loc_alloc_argument; simpl; intuition congruence.
  rewrite B. apply AG; auto. auto. auto.

  (* Llabel *)
  left; econstructor; split.
  apply plus_one. apply exec_Llabel.
  econstructor; eauto with coqlib.

  (* Lgoto *)
  left; econstructor; split.
  apply plus_one. apply exec_Lgoto. apply find_label_transf_function; eauto.
  econstructor; eauto.
  eapply LTLin.find_label_is_tail; eauto.

  (* Lcond true *)
  ExploitWT; inv WTI.
  exploit add_reloads_correct. 
    eapply length_cond_args; eauto.
    apply locs_acceptable_disj_temporaries; auto.
  intros [ls2 [A [B C]]].
  left; econstructor; split.
  eapply plus_right. eauto. eapply exec_Lcond_true; eauto.
  rewrite B. rewrite (agree_locs _ _ _ AG H5). auto.
  apply find_label_transf_function; eauto.
  traceEq.
  econstructor; eauto.
  apply agree_exten with ls; auto.
  eapply LTLin.find_label_is_tail; eauto.

  (* Lcond false *)
  ExploitWT; inv WTI.
  exploit add_reloads_correct. 
    eapply length_cond_args; eauto.
    apply locs_acceptable_disj_temporaries; auto.
  intros [ls2 [A [B C]]].
  left; econstructor; split.
  eapply plus_right. eauto. eapply exec_Lcond_false; eauto.
  rewrite B. rewrite (agree_locs _ _ _ AG H4). auto.
  traceEq.
  econstructor; eauto with coqlib.
  apply agree_exten with ls; auto.

  (* Lreturn *)
  ExploitWT; inv WTI. 
  unfold rs2, rs1; destruct or; simpl.
  (* with an argument *)
  exploit add_reload_correct.
  intros [ls2 [A [B C]]].
  left; econstructor; split.
  eapply plus_right. eauto. eapply exec_Lreturn; eauto. 
  traceEq.
  econstructor; eauto. 
  apply agree_return_regs; auto.
  eapply parent_locset_match; eauto.
  apply agree_set with ls. 
  apply loc_result_acceptable.
  rewrite B. eapply agree_loc; eauto.
  auto. auto.
  (* without an argument *)
  left; econstructor; split.
  apply plus_one. eapply exec_Lreturn; eauto.  
  econstructor; eauto.
  apply agree_return_regs; auto.
  eapply parent_locset_match; eauto.

  (* internal function *)
  simpl in WT. inversion_clear WT. inversion H0. simpl in AG.
  destruct (parallel_move_parameters_correct tge s' (transf_function f)
               (Vptr stk Int.zero) (LTLin.fn_params f) (LTLin.fn_sig f)
               (transf_code f (LTLin.fn_code f)) (LTL.call_regs ls) m'
               wt_params wt_acceptable wt_norepet)
  as [ls2 [A [B [C D]]]].
  assert (AG2: agree rs2 ls2).
    unfold rs2. eapply agree_set_parameters; eauto.
    unfold rs1. apply agree_call_regs; auto.
  left; econstructor; split.
  eapply plus_left.
  eapply exec_function_internal; eauto.
  simpl. eauto. traceEq.
  econstructor; eauto with coqlib.

  (* external function *)
  left; econstructor; split.
  apply plus_one. eapply exec_function_external; eauto. 
  unfold args. symmetry. eapply agree_arguments_locs; auto.
  econstructor; eauto.
  unfold rs1. apply agree_set with ls; auto. 
  apply loc_result_acceptable.
  apply Locmap.gss.
  intros. apply Locmap.gso; auto.
  eapply agree_arguments_agree; eauto.

  (* return *)
  inv STACKS. 
  exploit add_spill_correct. intros [ls2 [A [B C]]].
  left; econstructor; split.
  eapply plus_left. eapply exec_return; eauto.
  eauto. traceEq.
  econstructor; eauto. 
  unfold rs1. apply agree_set with ls; auto.
  rewrite B. apply AG. apply loc_result_acceptable. 
Qed.

Lemma transf_initial_states:
  forall st1, LTLin.initial_state prog st1 ->
  exists st2, Linear.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  econstructor; split.
  econstructor. 
  change (prog_main tprog) with (prog_main prog). 
  rewrite symbols_preserved. eauto.
  apply function_ptr_translated; eauto. 
  rewrite sig_preserved. auto.
  replace (Genv.init_mem tprog) with (Genv.init_mem prog).  
  econstructor; eauto. constructor. rewrite H2; auto.
  red; intros. auto.
  eapply Genv.find_funct_ptr_prop; eauto.
  symmetry. unfold tprog, transf_program. apply Genv.init_mem_transf; auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> LTLin.final_state st1 r -> Linear.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. econstructor.
  rewrite (agree_loc _ _ (R R3) AG). auto. 
  simpl. intuition congruence.
Qed.

Theorem transf_program_correct:
  forall (beh: program_behavior),
  LTLin.exec_program prog beh -> Linear.exec_program tprog beh.
Proof.
  unfold LTLin.exec_program, Linear.exec_program; intros.
  eapply simulation_star_preservation; eauto.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact transf_step_correct. 
Qed.

End PRESERVATION.
