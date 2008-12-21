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
  the number of temporaries required for reloading the arguments. *)

Fixpoint temporaries_ok_rec (tys: list typ) (itmps ftmps: list mreg)
                            {struct tys} : bool :=
  match tys with
  | nil => true
  | Tint :: ts =>
      match itmps with
      | nil => false
      | it1 :: its => temporaries_ok_rec ts its ftmps
      end
  | Tfloat :: ts =>
      match ftmps with
      | nil => false
      | ft1 :: fts => temporaries_ok_rec ts itmps fts
      end
  end.

Definition temporaries_ok (tys: list typ) :=
  temporaries_ok_rec tys int_temporaries float_temporaries.

Remark temporaries_ok_rec_incr_1:
  forall tys it itmps ftmps,
  temporaries_ok_rec tys itmps ftmps = true ->
  temporaries_ok_rec tys (it :: itmps) ftmps = true.
Proof.
  induction tys; intros until ftmps; simpl.
  tauto.
  destruct a. 
  destruct itmps. congruence. auto.
  destruct ftmps. congruence. auto.
Qed.

Remark temporaries_ok_rec_incr_2:
  forall tys ft itmps ftmps,
  temporaries_ok_rec tys itmps ftmps = true ->
  temporaries_ok_rec tys itmps (ft :: ftmps) = true.
Proof.
  induction tys; intros until ftmps; simpl.
  tauto.
  destruct a. 
  destruct itmps. congruence. auto.
  destruct ftmps. congruence. auto.
Qed.

Remark temporaries_ok_rec_decr:
  forall tys ty itmps ftmps,
  temporaries_ok_rec (ty :: tys) itmps ftmps = true ->
  temporaries_ok_rec tys itmps ftmps = true.
Proof.
  intros until ftmps. simpl. destruct ty. 
  destruct itmps. congruence. intros. apply temporaries_ok_rec_incr_1; auto.
  destruct ftmps. congruence. intros. apply temporaries_ok_rec_incr_2; auto.
Qed.

Lemma temporaries_ok_enough_rec:
  forall locs itmps ftmps,
  temporaries_ok_rec (List.map Loc.type locs) itmps ftmps = true ->
  enough_temporaries_rec locs itmps ftmps = true.
Proof.
  induction locs; intros until ftmps.
  simpl. auto.
  simpl enough_temporaries_rec. simpl map. 
  destruct a. intros. apply IHlocs. eapply temporaries_ok_rec_decr; eauto. 
  simpl. destruct (slot_type s). 
  destruct itmps; auto.
  destruct ftmps; auto.
Qed.

Lemma temporaries_ok_enough:
  forall locs,
  temporaries_ok (List.map Loc.type locs) = true ->
  enough_temporaries locs = true.
Proof.
  unfold temporaries_ok, enough_temporaries. intros. 
  apply temporaries_ok_enough_rec; auto.
Qed.

Lemma enough_temporaries_op_args:
  forall (op: operation) (args: list loc) (res: loc),
  (List.map Loc.type args, Loc.type res) = type_of_operation op ->
  enough_temporaries args = true.
Proof.
  intros. apply temporaries_ok_enough.
  replace (map Loc.type args) with (fst (type_of_operation op)).
  destruct op; try (destruct c); compute; reflexivity.
  rewrite <- H. auto.
Qed.

Lemma enough_temporaries_cond:
  forall (cond: condition) (args: list loc),
  List.map Loc.type args = type_of_condition cond ->
  enough_temporaries args = true.
Proof.
  intros. apply temporaries_ok_enough. rewrite H.
  destruct cond; compute; reflexivity.
Qed.

Lemma enough_temporaries_addr:
  forall (addr: addressing) (args: list loc),
  List.map Loc.type args = type_of_addressing addr ->
  enough_temporaries args = true.
Proof.
  intros. apply temporaries_ok_enough. rewrite H. 
  destruct addr; compute; reflexivity.
Qed.

Lemma temporaries_ok_rec_length:
  forall tys itmps ftmps,
  (length tys <= length itmps)%nat ->
  (length tys <= length ftmps)%nat ->
  temporaries_ok_rec tys itmps ftmps = true.
Proof.
  induction tys; intros until ftmps; simpl.
  auto.
  intros. destruct a.
  destruct itmps; simpl in H. omegaContradiction. apply IHtys; omega.
  destruct ftmps; simpl in H0. omegaContradiction. apply IHtys; omega.
Qed.

Lemma enough_temporaries_length:
  forall args,
  (length args <= 2)%nat -> enough_temporaries args = true.
Proof.
  intros. apply temporaries_ok_enough. unfold temporaries_ok.
  apply temporaries_ok_rec_length. 
  rewrite list_length_map. simpl. omega.
  rewrite list_length_map. simpl. omega.
Qed.

Lemma not_enough_temporaries_length:
  forall src args,
  enough_temporaries (src :: args) = false ->
  (length args >= 2)%nat.
Proof.
  intros.
  assert (length (src :: args) <= 2 \/ length (src :: args) > 2)%nat by omega.
  destruct H0.
  exploit enough_temporaries_length. eauto. congruence. 
  simpl in H0. omega.
Qed.

Lemma not_enough_temporaries_addr:
  forall (ge: genv) sp addr src args ls m v,
  enough_temporaries (src :: args) = false ->
  eval_addressing ge sp addr (List.map ls args) = Some v ->
  eval_operation ge sp (op_for_binary_addressing addr) (List.map ls args) m = Some v.
Proof.
  intros.
  apply eval_op_for_binary_addressing; auto.
  rewrite list_length_map. eapply not_enough_temporaries_length; eauto.
Qed.

(** Some additional properties of [reg_for] and [regs_for]. *)

Lemma regs_for_cons:
  forall src args,
  exists rsrc, exists rargs, regs_for (src :: args) = rsrc :: rargs.
Proof.
  intros. unfold regs_for. simpl. 
  destruct src. econstructor; econstructor; reflexivity. 
  destruct (slot_type s); econstructor; econstructor; reflexivity.
Qed.

Lemma reg_for_not_IT2:
  forall l, loc_acceptable l -> reg_for l <> IT2.
Proof.
  intros. destruct l; simpl. 
  red; intros; subst m. simpl in H. intuition congruence.
  destruct (slot_type s); congruence.
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

Lemma add_reload_correct_2:
  forall src k rs m,
  exists rs',
  star step ge (State stk f sp (add_reload src (reg_for src) k) rs m)
            E0 (State stk f sp k rs' m) /\
  rs' (R (reg_for src)) = rs src /\
  (forall l, Loc.diff (R (reg_for src)) l -> rs' l = rs l) /\
  (forall l, Loc.notin l temporaries -> rs' l = rs l).
Proof.
  intros. destruct (reg_for_spec src).
  set (rf := reg_for src) in *. 
  unfold add_reload. rewrite <- H. rewrite dec_eq_true.
  exists rs. split. constructor. auto.
  destruct (add_reload_correct src (reg_for src) k rs m)
  as [rs' [A [B C]]].
  exists rs'; intuition.
  apply C. apply Loc.diff_sym. eapply Loc.in_notin_diff; eauto. 
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
  enough_temporaries_rec srcs itmps ftmps = true ->
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
  destruct a as [r | s].
  (* a is a register *)
  simpl add_reload. rewrite dec_eq_true. 
  exploit IHsrcs; eauto.
  intros [rs' [EX [RES [OTH1 OTH2]]]].
  exists rs'. split. eauto.
  split. simpl. decEq. apply OTH1. red; intros; eauto. red; intros; eauto. auto.
  auto.
  (* a is a stack slot *)
  destruct (slot_type s).
  (* ... of integer type *)
  destruct itmps as [ | it1 itmps ]. discriminate. inv H3.
  destruct (add_reload_correct (S s) it1 (add_reloads srcs (regs_for_rec srcs itmps ftmps) k) rs m)
  as [rs1 [A [B C]]].
  exploit IHsrcs; eauto. 
  intros. apply H0 with r. tauto. simpl. tauto. eapply list_disjoint_cons_left; eauto. 
  intros [rs' [P [Q [T U]]]]. 
  exists rs'. split. eapply star_trans; eauto. 
  split. simpl. decEq. rewrite <- B. apply T. auto.
    eapply list_disjoint_notin; eauto with coqlib.
    rewrite Q. apply list_map_exten. intros. symmetry. apply C. 
    simpl. destruct x; auto. red; intro; subst m0. apply H0 with it1; auto with coqlib.
  split. simpl. intros. transitivity (rs1 (R r)).
    apply T; tauto. apply C. simpl. tauto. 
  intros. transitivity (rs1 (S s0)). auto. apply C. simpl. auto.
  (* ... of float type *)
  destruct ftmps as [ | ft1 ftmps ]. discriminate. inv H4.
  destruct (add_reload_correct (S s) ft1 (add_reloads srcs (regs_for_rec srcs itmps ftmps) k) rs m)
  as [rs1 [A [B C]]].
  exploit IHsrcs; eauto. 
  intros. apply H1 with r. tauto. simpl. tauto. eapply list_disjoint_cons_right; eauto. 
  intros [rs' [P [Q [T U]]]]. 
  exists rs'. split. eapply star_trans; eauto. 
  split. simpl. decEq. rewrite <- B. apply T; auto.
    eapply list_disjoint_notin; eauto. apply list_disjoint_sym. eauto. auto with coqlib.
    rewrite Q. apply list_map_exten. intros. symmetry. apply C. 
    simpl. destruct x; auto. red; intro; subst m0. apply H1 with ft1; auto with coqlib.
  split. simpl. intros. transitivity (rs1 (R r)).
    apply T; tauto. apply C. simpl. tauto. 
  intros. transitivity (rs1 (S s0)). auto. apply C. simpl. auto.
Qed.

Lemma add_reloads_correct:
  forall srcs k rs m,
  enough_temporaries srcs = true ->
  Loc.disjoint srcs temporaries ->
  exists rs',
  star step ge (State stk f sp (add_reloads srcs (regs_for srcs) k) rs m)
            E0 (State stk f sp k rs' m) /\
  reglist rs' (regs_for srcs) = List.map rs srcs /\
  forall l, Loc.notin l temporaries -> rs' l = rs l.
Proof.
  intros.
  unfold enough_temporaries in H.
  exploit add_reloads_correct_rec; eauto. 
    intros. exploit (H0 (R r) (R r)); auto. 
    simpl in H2. simpl. intuition congruence.
    intros. exploit (H0 (R r) (R r)); auto. 
    simpl in H2. simpl. intuition congruence.
    red; intros r1 r2; simpl. intuition congruence.
    unfold int_temporaries. NoRepet.
    unfold float_temporaries. NoRepet.
  intros [rs' [EX [RES [OTH1 OTH2]]]].
  exists rs'. split. eexact EX. 
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
  give compatible values to all acceptable locations,
  that is, non-temporary registers and [Local] stack slots.
  The notion of compatibility used is the [Val.lessdef] ordering,
  which enables a [Vundef] value in the original program to be refined
  into any value in the transformed program.  

  A typical situation where this refinement of values occurs is at
  function entry point.  In LTLin, all registers except those
  belonging to the function parameters are set to [Vundef].  In
  Linear, these registers have whatever value they had in the caller
  function.  This difference is harmless: if the original LTLin code
  does not get stuck, we know that it does not use any of these
  [Vundef] values. *)

Definition agree (rs1 rs2: locset) : Prop :=
  forall l, loc_acceptable l -> Val.lessdef (rs1 l) (rs2 l).

Lemma agree_loc:
  forall rs1 rs2 l,
  agree rs1 rs2 -> loc_acceptable l -> Val.lessdef (rs1 l) (rs2 l).
Proof.
  auto.
Qed.

Lemma agree_locs:
  forall rs1 rs2 ll,
  agree rs1 rs2 -> locs_acceptable ll -> 
  Val.lessdef_list (map rs1 ll) (map rs2 ll).
Proof.
  induction ll; simpl; intros.
  constructor.
  constructor. apply H. apply H0; auto with coqlib.
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
  Val.lessdef v (rs2' l) ->
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

Lemma agree_find_funct:
  forall (ge: Linear.genv) rs ls r f,
  Genv.find_funct ge (rs r) = Some f ->
  agree rs ls ->
  loc_acceptable r ->
  Genv.find_funct ge (ls r) = Some f.
Proof.
  intros. 
  assert (Val.lessdef (rs r) (ls r)). eapply agree_loc; eauto.
  exploit Genv.find_funct_inv; eauto. intros [b EQ]. rewrite EQ in H2.
  inv H2. rewrite <- EQ. auto.
Qed.

Lemma agree_postcall_1:
  forall rs ls,
  agree rs ls ->
  agree (LTL.postcall_locs rs) ls.
Proof.
  intros; red; intros. unfold LTL.postcall_locs.
  destruct l; auto. 
  destruct (In_dec Loc.eq (R m) temporaries). constructor.
  destruct (In_dec Loc.eq (R m) destroyed_at_call). constructor.
  auto.
Qed.

Lemma agree_postcall_2:
  forall rs ls ls',
  agree (LTL.postcall_locs rs) ls ->
  (forall l,
      loc_acceptable l -> ~In l destroyed_at_call -> ~In l temporaries ->
      ls' l = ls l) ->
  agree (LTL.postcall_locs rs) ls'.
Proof.
  intros; red; intros. generalize (H l H1). unfold LTL.postcall_locs. 
  destruct l. 
  destruct (In_dec Loc.eq (R m) temporaries). intro; constructor.
  destruct (In_dec Loc.eq (R m) destroyed_at_call). intro; constructor.
  intro. rewrite H0; auto. 
  intro. rewrite H0; auto.
  simpl. intuition congruence.
  simpl. intuition congruence.
Qed.

Lemma agree_postcall_call:
  forall rs ls ls' sig,
  agree rs ls ->
  (forall l,
     Loc.notin l (loc_arguments sig) -> Loc.notin l temporaries -> 
     ls' l = ls l) ->
  agree (LTL.postcall_locs rs) ls'.
Proof.
  intros. apply agree_postcall_2 with ls. apply agree_postcall_1; auto.
  intros. apply H0.
  apply arguments_not_preserved; auto.
  destruct l; simpl. simpl in H2. intuition congruence. 
  destruct s; tauto.
  apply temporaries_not_acceptable; auto.
Qed.

Lemma agree_postcall_alloc:
  forall rs ls ls2 v,
  agree rs ls ->
  (forall l, Loc.diff (R loc_alloc_argument) l -> ls2 l = ls l) ->
  agree (LTL.postcall_locs rs) (Locmap.set (R loc_alloc_result) v ls2).
Proof.
  intros. apply agree_postcall_2 with ls. apply agree_postcall_1; auto.
  intros. destruct (Loc.eq l (R loc_alloc_result)).
  subst l. elim H2. simpl. tauto. 
  rewrite Locmap.gso. apply H0.
  red. destruct l; auto. red; intro. subst m. elim H2.
  simpl. tauto.
  apply Loc.diff_sym. apply loc_acceptable_noteq_diff; auto. 
Qed.

Lemma agree_init_locs:
  forall ls dsts vl,
  locs_acceptable dsts ->
  Loc.norepet dsts ->
  Val.lessdef_list vl (map ls dsts) ->
  agree (LTL.init_locs vl dsts) ls.
Proof.
  induction dsts; intros; simpl.
  red; intros. unfold Locmap.init. constructor.
  simpl in H1. inv H1. inv H0. 
  apply agree_set with ls. apply H; auto with coqlib. auto. auto.
  apply IHdsts; auto. red; intros; apply H; auto with coqlib.
Qed.

Lemma call_regs_parameters:
  forall ls sig,
  map (call_regs ls) (loc_parameters sig) = map ls (loc_arguments sig).
Proof.
  intros. unfold loc_parameters. rewrite list_map_compose. 
  apply list_map_exten; intros. 
  unfold call_regs, parameter_of_argument. 
  generalize (loc_arguments_acceptable _ _ H). 
  unfold loc_argument_acceptable. 
  destruct x. auto.
  destruct s; intros; try contradiction. auto.
Qed. 

Lemma return_regs_preserve:
  forall ls1 ls2 l,
  ~ In l temporaries ->
  ~ In l destroyed_at_call ->
  return_regs ls1 ls2 l = ls1 l.
Proof.
  intros. unfold return_regs. destruct l; auto.
  destruct (In_dec Loc.eq (R m) temporaries). contradiction.
  destruct (In_dec Loc.eq (R m) destroyed_at_call). contradiction.
  auto.
Qed.

Lemma return_regs_arguments:
  forall ls1 ls2 sig,
  tailcall_possible sig ->
  map (return_regs ls1 ls2) (loc_arguments sig) = map ls2 (loc_arguments sig).
Proof.
  intros. apply list_map_exten; intros. 
  unfold return_regs. generalize (H x H0). destruct x; intros.
  destruct (In_dec Loc.eq (R m) temporaries). auto.
  destruct (In_dec Loc.eq (R m) destroyed_at_call). auto.
  elim n0. eapply arguments_caller_save; eauto.
  contradiction.
Qed.

Lemma return_regs_result:
  forall ls1 ls2 sig,
  return_regs ls1 ls2 (R (loc_result sig)) = ls2 (R (loc_result sig)).
Proof.
  intros. unfold return_regs. 
  destruct (In_dec Loc.eq (R (loc_result sig)) temporaries). auto.
  destruct (In_dec Loc.eq (R (loc_result sig)) destroyed_at_call). auto.
  elim n0. apply loc_result_caller_save.
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
  destruct (enough_temporaries (l0 :: l)).
    destruct (regs_for (l0 :: l)); FL.
    FL. FL. 
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
- Agreement between the memory states of the two programs,
  according to the [Mem.lessdef] predicate.
- Lists of LTLin instructions appearing in the source state
  are always suffixes of the code for the corresponding functions.
- Well-typedness of the source code, which ensures that
  only acceptable locations are accessed by this code.
- Agreement over return types during calls: the return type of a function
  is always equal to the return type of the signature of the corresponding
  call.  This invariant is necessary since the conventional location
  used for passing return values depend on the return type.  This invariant
  is enforced through the third parameter of the [match_stackframes]
  predicate, which is the signature of the called function.
*)

Inductive match_stackframes:
       list LTLin.stackframe -> list Linear.stackframe -> signature -> Prop :=
  | match_stackframes_nil:
      forall sig,
      sig.(sig_res) = Some Tint ->
      match_stackframes nil nil sig
  | match_stackframes_cons:
      forall res f sp c rs s s' c' ls sig,
      match_stackframes s s' (LTLin.fn_sig f) ->
      c' = add_spill (loc_result sig) res (transf_code f c) ->      
      agree (LTL.postcall_locs rs) ls ->
      loc_acceptable res ->
      wt_function f ->
      is_tail c (LTLin.fn_code f) ->
      match_stackframes
         (LTLin.Stackframe res f sp (LTL.postcall_locs rs) c :: s)
         (Linear.Stackframe (transf_function f) sp ls c' :: s')
         sig.

Inductive match_states: LTLin.state -> Linear.state -> Prop :=
  | match_states_intro:
      forall s f sp c rs m s' ls tm
        (STACKS: match_stackframes s s' (LTLin.fn_sig f))
        (AG: agree rs ls)
        (WT: wt_function f)
        (TL: is_tail c (LTLin.fn_code f))
        (MMD: Mem.lessdef m tm),
      match_states (LTLin.State s f sp c rs m)
                   (Linear.State s' (transf_function f) sp (transf_code f c) ls tm)
  | match_states_call:
      forall s f args m s' ls tm
        (STACKS: match_stackframes s s' (LTLin.funsig f))
        (AG: Val.lessdef_list args (map ls (Conventions.loc_arguments (LTLin.funsig f))))
        (PRES: forall l, ~In l temporaries -> ~In l destroyed_at_call ->
                 ls l = parent_locset s' l)
        (WT: wt_fundef f)
        (MMD: Mem.lessdef m tm),
      match_states (LTLin.Callstate s f args m)
                   (Linear.Callstate s' (transf_fundef f) ls tm)
  | match_states_return:
      forall s res m s' ls tm sig
        (STACKS: match_stackframes s s' sig)
        (AG: Val.lessdef res (ls (R (Conventions.loc_result sig))))
        (PRES: forall l, ~In l temporaries -> ~In l destroyed_at_call ->
                 ls l = parent_locset s' l)
        (MMD: Mem.lessdef m tm),
      match_states (LTLin.Returnstate s res m)
                   (Linear.Returnstate s' ls tm).

Lemma match_stackframes_change_sig:
  forall s s' sig1 sig2,
  match_stackframes s s' sig1 ->
  sig2.(sig_res) = sig1.(sig_res) ->
  match_stackframes s s' sig2.
Proof.
  intros. inv H. constructor. congruence.
  econstructor; eauto. unfold loc_result. rewrite H0. auto.
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

Axiom ADMITTED: forall (P: Prop), P.

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
  destruct (add_move_correct tge s' (transf_function f) sp r1 res (transf_code f b) ls tm)
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
  intros. apply C. apply Loc.diff_sym; auto.
  simpl in H7; tauto. simpl in H7; tauto.
  (* other ops *)
  assert (is_move_operation op args = None).
    caseEq (is_move_operation op args); intros.
    destruct (is_move_operation_correct _ _ H0). congruence.
    auto.
  rewrite H0.
  exploit add_reloads_correct. 
    eapply enough_temporaries_op_args; eauto.
    apply locs_acceptable_disj_temporaries; auto.
  intros [ls2 [A [B C]]]. instantiate (1 := ls) in B. 
  assert (exists tv, eval_operation tge sp op (reglist ls2 (regs_for args)) tm = Some tv
                     /\ Val.lessdef v tv).
    apply eval_operation_lessdef with m (map rs args); auto.
    rewrite B. eapply agree_locs; eauto. 
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  destruct H1 as [tv [P Q]].
  exploit add_spill_correct.
  intros [ls3 [D [E F]]].
  left; econstructor; split.
  eapply star_plus_trans. eexact A. 
  eapply plus_left. eapply exec_Lop with (v := tv); eauto.
  eexact D. eauto. traceEq.
  econstructor; eauto with coqlib.
  apply agree_set with ls; auto.
  rewrite E. rewrite Locmap.gss. auto.
  intros. rewrite F; auto. rewrite Locmap.gso. auto. 
  apply reg_for_diff; auto.

  (* Lload *)
  ExploitWT; inv WTI.
  exploit add_reloads_correct. 
    eapply enough_temporaries_addr; eauto.
    apply locs_acceptable_disj_temporaries; auto.
  intros [ls2 [A [B C]]].
  assert (exists ta, eval_addressing tge sp addr (reglist ls2 (regs_for args)) = Some ta
                     /\ Val.lessdef a ta).
    apply eval_addressing_lessdef with (map rs args); auto.
    rewrite B. eapply agree_locs; eauto. 
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  destruct H1 as [ta [P Q]].
  exploit Mem.loadv_lessdef; eauto. 
  intros [tv [R S]].
  exploit add_spill_correct.
  intros [ls3 [D [E F]]].
  left; econstructor; split.
  eapply star_plus_trans. eauto. 
  eapply plus_left. eapply exec_Lload; eauto.
  eauto. auto. traceEq.
  econstructor; eauto with coqlib.
  apply agree_set with ls; auto.
  rewrite E. rewrite Locmap.gss. auto.
  intros. rewrite F; auto. rewrite Locmap.gso. auto. 
  apply reg_for_diff; auto.

  (* Lstore *)
  ExploitWT; inv WTI.
  caseEq (enough_temporaries (src :: args)); intro ENOUGH. 
  destruct (regs_for_cons src args) as [rsrc [rargs EQ]]. rewrite EQ.
  exploit add_reloads_correct.
    eauto. apply locs_acceptable_disj_temporaries; auto.
    red; intros. elim H1; intro; auto. subst l; auto. 
  intros [ls2 [A [B C]]]. rewrite EQ in A. rewrite EQ in B.
  injection B. intros D E. 
  simpl in B.
  assert (exists ta, eval_addressing tge sp addr (reglist ls2 rargs) = Some ta
                     /\ Val.lessdef a ta).
    apply eval_addressing_lessdef with (map rs args); auto.
    rewrite D. eapply agree_locs; eauto. 
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  destruct H1 as [ta [P Q]].
  assert (X: Val.lessdef (rs src) (ls2 (R rsrc))).
    rewrite E. eapply agree_loc; eauto.
  exploit Mem.storev_lessdef. eexact MMD. eexact Q. eexact X. eauto. 
  intros [tm2 [Y Z]].
  left; econstructor; split. 
  eapply plus_right. eauto. 
  eapply exec_Lstore with (a := ta); eauto.
  traceEq.
  econstructor; eauto with coqlib.
  apply agree_exten with ls; auto.
  (* not enough temporaries *)
  destruct (add_reloads_correct tge s' (transf_function f) sp args
             (Lop (op_for_binary_addressing addr) (regs_for args) IT2
            :: add_reload src (reg_for src)
                 (Lstore chunk (Aindexed Int.zero) (IT2 :: nil) (reg_for src)
                  :: transf_code f b)) ls tm)
  as [ls2 [A [B C]]].
    eapply enough_temporaries_addr; eauto. 
    apply locs_acceptable_disj_temporaries; auto.
  assert (exists ta, eval_addressing tge sp addr (reglist ls2 (regs_for args)) = Some ta
                     /\ Val.lessdef a ta).
    apply eval_addressing_lessdef with (map rs args); auto.
    rewrite B. eapply agree_locs; eauto. 
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  destruct H1 as [ta [P Q]].
  set (ls3 := Locmap.set (R IT2) ta ls2).
  destruct (add_reload_correct_2 tge s' (transf_function f) sp src
              (Lstore chunk (Aindexed Int.zero) (IT2 :: nil) (reg_for src)
                  :: transf_code f b)
              ls3 tm)
  as [ls4 [D [E [F G]]]].
  assert (X: Val.lessdef (rs src) (ls4 (R (reg_for src)))).
    rewrite E. unfold ls3. rewrite Locmap.gso. eapply agree_loc; eauto. 
    eapply agree_exten; eauto. 
    apply Loc.diff_sym. apply loc_acceptable_noteq_diff. auto. 
    red; intros; subst src. simpl in H8. intuition congruence.
  exploit Mem.storev_lessdef. eexact MMD. eexact Q. eexact X. eauto. 
  intros [tm2 [Y Z]].
  left; econstructor; split.
  eapply star_plus_trans. eauto. 
  eapply plus_left. eapply exec_Lop with (v := ta). 
    rewrite B. eapply not_enough_temporaries_addr; eauto.
    rewrite <- B; auto.
  eapply star_right. eauto. 
  eapply exec_Lstore with (a := ta); eauto.
    simpl reglist. rewrite F. unfold ls3. rewrite Locmap.gss. simpl. 
    destruct ta; simpl in Y; try discriminate. rewrite Int.add_zero. auto.
    simpl. apply reg_for_not_IT2; auto. 
  reflexivity. reflexivity. traceEq. 
  econstructor; eauto with coqlib.
  apply agree_exten with ls; auto.
  intros. rewrite G; auto. unfold ls3. rewrite Locmap.gso. auto. 
  simpl. destruct l; auto. simpl in H1. intuition congruence. 

  (* Lcall *)
  ExploitWT. inversion WTI. subst ros0 args0 res0. rewrite <- H0.  
  assert (WTF': wt_fundef f'). eapply find_function_wt; eauto.
  destruct ros as [fn | id].
  (* indirect call *)
  red in H6. destruct H6 as [OK1 [OK2 OK3]].
  rewrite <- H0 in H4. rewrite <- H0 in OK3.
  destruct (parallel_move_arguments_correct tge s' (transf_function f) sp 
              args sig
              (add_reload fn (reg_for fn)
                (Lcall sig (inl ident (reg_for fn))
                  :: add_spill (loc_result sig) res (transf_code f b)))
              ls tm H4 H7)
  as [ls2 [A [B C]]].
  destruct (add_reload_correct_2 tge s' (transf_function f) sp fn
             (Lcall sig (inl ident (reg_for fn))
              :: add_spill (loc_result sig) res (transf_code f b))
             ls2 tm)
  as [ls3 [D [E [F G]]]].
  assert (ARGS: Val.lessdef_list (map rs args) 
                                 (map ls3 (loc_arguments sig))).
    replace (map ls3 (loc_arguments sig)) with (map ls2 (loc_arguments sig)).
    rewrite B. apply agree_locs; auto. 
    apply list_map_exten; intros. apply G.
    apply Loc.disjoint_notin with (loc_arguments sig).
    apply loc_arguments_not_temporaries. auto.
  left; econstructor; split.
  eapply star_plus_trans. eexact A. eapply plus_right. eexact D. 
  eapply exec_Lcall; eauto.
    simpl. rewrite E. rewrite C. eapply agree_find_funct; eauto. 
    apply functions_translated. eauto.
    apply loc_acceptable_notin_notin; auto. 
    apply temporaries_not_acceptable; auto.
    rewrite H0; symmetry; apply sig_preserved.
  eauto. traceEq.
  econstructor; eauto. 
  econstructor; eauto with coqlib.
  rewrite H0. auto.
  apply agree_postcall_call with ls sig; auto.
  intros. rewrite G; auto. congruence. 
  (* direct call *)
  rewrite <- H0 in H4.
  destruct (parallel_move_arguments_correct tge s' (transf_function f) sp
              args sig
              (Lcall sig (inr mreg id)
                :: add_spill (loc_result sig) res (transf_code f b))
              ls tm H4 H7)
  as [ls3 [D [E F]]].
  assert (ARGS: Val.lessdef_list (map rs args) (map ls3 (loc_arguments sig))).
    rewrite E. apply agree_locs; auto.
  left; econstructor; split.
  eapply plus_right. eauto.
  eapply exec_Lcall; eauto.
    simpl. rewrite symbols_preserved. 
    generalize H; simpl. destruct (Genv.find_symbol ge id).
    apply function_ptr_translated; auto. congruence.
    rewrite H0. symmetry; apply sig_preserved.
  traceEq.
  econstructor; eauto.
  econstructor; eauto with coqlib. rewrite H0; auto. 
  apply agree_postcall_call with ls sig; auto.
  congruence.

  (* Ltailcall *)
  ExploitWT. inversion WTI. subst ros0 args0.
  assert (WTF': wt_fundef f'). eapply find_function_wt; eauto.
  rewrite <- H0.
  destruct ros as [fn | id].
  (* indirect call *)
  red in H4. destruct H4 as [OK1 [OK2 OK3]].
  rewrite <- H0 in H3. rewrite <- H0 in OK3.
  destruct (parallel_move_arguments_correct tge s' (transf_function f) (Vptr stk Int.zero)
              args sig
              (add_reload fn IT1
                (Ltailcall sig (inl ident IT1) :: transf_code f b))
              ls tm H3 H5)
  as [ls2 [A [B C]]].
  destruct (add_reload_correct tge s' (transf_function f) (Vptr stk Int.zero) fn IT1
             (Ltailcall sig (inl ident IT1) :: transf_code f b)
             ls2 tm)
  as [ls3 [D [E F]]].
  assert (ARGS: Val.lessdef_list (map rs args) 
                                 (map ls3 (loc_arguments sig))).
    replace (map ls3 (loc_arguments sig)) with (map ls2 (loc_arguments sig)).
    rewrite B. apply agree_locs; auto. 
    apply list_map_exten; intros. apply F.
    apply Loc.diff_sym.
    apply (loc_arguments_not_temporaries sig x (R IT1)); simpl; auto.
  left; econstructor; split.
  eapply star_plus_trans. eexact A. eapply plus_right. eexact D. 
  eapply exec_Ltailcall; eauto.
    simpl. rewrite E. rewrite C. eapply agree_find_funct; eauto. 
    apply functions_translated. eauto.
    apply loc_acceptable_notin_notin; auto. 
    apply temporaries_not_acceptable; auto.
    rewrite H0; symmetry; apply sig_preserved.
  eauto. traceEq.
  econstructor; eauto. 
  eapply match_stackframes_change_sig; eauto.
  rewrite return_regs_arguments; auto. congruence.
  exact (return_regs_preserve (parent_locset s') ls3).
  apply Mem.free_lessdef; auto. 
  (* direct call *)
  rewrite <- H0 in H3.
  destruct (parallel_move_arguments_correct tge s' (transf_function f) (Vptr stk Int.zero)
              args sig
              (Ltailcall sig (inr mreg id) :: transf_code f b)
              ls tm H3 H5)
  as [ls3 [D [E F]]].
  assert (ARGS: Val.lessdef_list (map rs args) 
                                 (map ls3 (loc_arguments sig))).
    rewrite E. apply agree_locs. apply agree_exten with ls; auto. auto.
  left; econstructor; split.
  eapply plus_right. eauto.
  eapply exec_Ltailcall; eauto.
    simpl. rewrite symbols_preserved. 
    generalize H; simpl. destruct (Genv.find_symbol ge id).
    apply function_ptr_translated; auto. congruence.
    rewrite H0. symmetry; apply sig_preserved.
  traceEq.
  econstructor; eauto.
  eapply match_stackframes_change_sig; eauto.
  rewrite return_regs_arguments; auto. congruence.
  exact (return_regs_preserve (parent_locset s') ls3).
  apply Mem.free_lessdef; auto. 

  (* Lalloc *)
  ExploitWT; inv WTI.
  caseEq (alloc tm 0 (Int.signed sz)). intros tm' blk' TALLOC.
  assert (blk = blk' /\ Mem.lessdef m' tm'). 
    eapply Mem.alloc_lessdef; eauto.
  exploit add_reload_correct. intros [ls2 [A [B C]]]. 
  exploit add_spill_correct. intros [ls3 [D [E F]]].
  destruct H1 as [P Q]. subst blk'. 
  assert (ls arg = Vint sz).
    assert (Val.lessdef (rs arg) (ls arg)). eapply agree_loc; eauto. 
    rewrite H in H1; inversion H1; auto.
  left; econstructor; split.
  eapply star_plus_trans. eauto. 
  eapply plus_left. eapply exec_Lalloc; eauto.
    rewrite B. eauto. 
  eauto. eauto. traceEq.
  econstructor; eauto with coqlib.
  apply agree_set with (Locmap.set (R loc_alloc_result) (Vptr blk Int.zero) ls2).
  auto. rewrite E. rewrite Locmap.gss. constructor. 
  auto. 
  apply agree_postcall_alloc with ls; auto. 

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
    eapply enough_temporaries_cond; eauto.
    apply locs_acceptable_disj_temporaries; auto.
  intros [ls2 [A [B C]]].
  left; econstructor; split.
  eapply plus_right. eauto. eapply exec_Lcond_true; eauto.
  rewrite B. apply eval_condition_lessdef with m (map rs args); auto.
  eapply agree_locs; eauto. 
  apply find_label_transf_function; eauto.
  traceEq.
  econstructor; eauto.
  apply agree_exten with ls; auto.
  eapply LTLin.find_label_is_tail; eauto.

  (* Lcond false *)
  ExploitWT; inv WTI.
  exploit add_reloads_correct.
    eapply enough_temporaries_cond; eauto.
    apply locs_acceptable_disj_temporaries; auto.
  intros [ls2 [A [B C]]].
  left; econstructor; split.
  eapply plus_right. eauto. eapply exec_Lcond_false; eauto.
  rewrite B. apply eval_condition_lessdef with m (map rs args); auto.
  eapply agree_locs; eauto. 
  traceEq.
  econstructor; eauto with coqlib.
  apply agree_exten with ls; auto.

  (* Lreturn *)
  ExploitWT; inv WTI. 
  destruct or; simpl.
  (* with an argument *)
  exploit add_reload_correct.
  intros [ls2 [A [B C]]].
  left; econstructor; split.
  eapply plus_right. eauto. eapply exec_Lreturn; eauto. 
  traceEq.
  econstructor; eauto.
  rewrite return_regs_result. rewrite B. apply agree_loc; auto.
  apply return_regs_preserve.
  apply Mem.free_lessdef; auto.
  (* without an argument *)
  left; econstructor; split.
  apply plus_one. eapply exec_Lreturn; eauto.  
  econstructor; eauto.
  apply return_regs_preserve.
  apply Mem.free_lessdef; auto.

  (* internal function *)
  simpl in WT. inversion_clear WT. inversion H0. simpl in AG.
  caseEq (alloc tm 0 (LTLin.fn_stacksize f)). intros tm' tstk TALLOC.
  exploit Mem.alloc_lessdef; eauto. intros [P Q]. subst tstk.
  destruct (parallel_move_parameters_correct tge s' (transf_function f)
               (Vptr stk Int.zero) (LTLin.fn_params f) (LTLin.fn_sig f)
               (transf_code f (LTLin.fn_code f)) (call_regs ls) tm'
               wt_params wt_acceptable wt_norepet)
  as [ls2 [A [B C]]].
  assert (AG2: agree (LTL.init_locs args (fn_params f)) ls2).
    apply agree_init_locs; auto.
    rewrite B. rewrite call_regs_parameters. auto. 
  left; econstructor; split.
  eapply plus_left.
  eapply exec_function_internal; eauto.
  simpl. eauto. traceEq.
  econstructor; eauto with coqlib.

  (* external function *)
  exploit event_match_lessdef; eauto. 
  intros [res' [A B]]. 
  left; econstructor; split.
  apply plus_one. eapply exec_function_external; eauto. 
  econstructor; eauto.
  simpl. rewrite Locmap.gss. auto.
  intros. rewrite Locmap.gso. auto. 
  simpl. destruct l; auto. red; intro. elim H1. subst m0. apply loc_result_caller_save.

  (* return *)
  inv STACKS. 
  exploit add_spill_correct. intros [ls2 [A [B C]]].
  left; econstructor; split.
  eapply plus_left. eapply exec_return; eauto.
  eauto. traceEq.
  econstructor; eauto. 
  apply agree_set with ls; auto.
  rewrite B. auto.
  unfold parent_locset in PRES.
  apply agree_postcall_2 with ls0; auto. 
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
  rewrite H2. simpl. constructor.
  eapply Genv.find_funct_ptr_prop; eauto.
  apply Mem.lessdef_refl. symmetry. unfold tprog, transf_program. apply Genv.init_mem_transf; auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> LTLin.final_state st1 r -> Linear.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. econstructor.
  unfold loc_result in AG. rewrite H in AG. inv AG. auto. 
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
