(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*      Laurence Rideau, INRIA Sophia-Antipolis-M\u00e9diterran\u00e9e           *)
(*      Bernard Paul Serpette, INRIA Sophia-Antipolis-M\u00e9diterran\u00e9e     *)
(*      Xavier Leroy, INRIA Paris-Rocquencourt                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Translation of parallel moves into sequences of individual moves *)

(** The ``parallel move'' problem, also known as ``parallel assignment'',
  is the following.  We are given a list of (source, destination) pairs
  of locations.  The goal is to find a sequence of elementary
  moves ([loc <- loc] assignments) such that, at the end of the sequence,
  location [dst] contains the value of location [src] at the beginning of
  the sequence, for each ([src], [dst]) pairs in the given problem.
  Moreover, other locations should keep their values, except one register
  of each type, which can be used as temporaries in the generated sequences.

  The parallel move problem is trivial if the sources and destinations do
  not overlap.  For instance,
<<
  (R1, R2) <- (R3, R4)     becomes    R1 <- R3; R2 <- R4
>>
  However, arbitrary overlap is allowed between sources and destinations.
  This requires some care in ordering the individual moves, as in
<<
  (R1, R2) <- (R3, R1)     becomes    R2 <- R1; R1 <- R3
>>
  Worse, cycles (permutations) can require the use of temporaries, as in
<<
  (R1, R2, R3) <- (R2, R3, R1)   becomes   T <- R1; R1 <- R2; R2 <- R3; R3 <- T;
>>
  An amazing fact is that for any parallel move problem, at most one temporary
  (or in our case one integer temporary and one float temporary) is needed.

  The development in this section was designed by Laurence Rideau and
  Bernard Serpette.  It is described in the paper
  ``Tilting at windmills with Coq: Formal verification of
  a compilation algorithm for parallel moves'',
  #<A HREF="http://hal.inria.fr/inria-00176007">#
  http://hal.inria.fr/inria-00176007
  #</A>#
*)

Require Import Relations.
Require Import Axioms.
Require Import Coqlib.
Require Import Recdef.

Section PARMOV.

(** * Registers, moves, and their semantics *)

(** The development is parameterized by the type of registers,
    equipped with a decidable equality. *)

Variable reg: Type.
Variable reg_eq : forall (r1 r2: reg), {r1=r2} + {r1<>r2}.

(** The [temp] function maps every register [r] to the register that
    should be used to save the value of [r] temporarily while performing
    a cyclic assignment involving [r].  In the simplest case, there is
    only one such temporary register [rtemp] and [temp] is the constant
    function [fun r => rtemp].  In more realistic cases, different temporary
    registers can be used to hold different values.  In the case of Compcert,
    we have two temporary registers, one for integer values and the other
    for floating-point values, and [temp] returns the appropriate temporary
    depending on the type of its argument. *)

Variable temp: reg -> reg.

Definition is_temp (r: reg): Prop := exists s, r = temp s.

(** A set of moves is a list of pairs of registers, of the form
    (source, destination). *)

Definition moves := (list (reg * reg))%type.  (* src -> dst *)

Definition srcs (m: moves) := List.map (@fst reg reg) m.
Definition dests (m: moves) := List.map (@snd reg reg) m.

(** ** Semantics of moves *)

(** The dynamic  semantics of moves is given in terms of environments.
    An environment is a mapping of registers to their current values. *)

Variable val: Type.
Definition env := reg -> val.

Lemma env_ext:
  forall (e1 e2: env),
  (forall r, e1 r = e2 r) -> e1 = e2.
Proof (@extensionality reg val).

(** The main operation over environments is update: it assigns
  a value [v] to a register [r] and preserves the values of other
  registers. *)

Definition update (r: reg) (v: val) (e: env) : env :=
  fun r' => if reg_eq r' r then v else e r'.

Lemma update_s:
  forall r v e, update r v e r = v.
Proof.
  unfold update; intros. destruct (reg_eq r r). auto. congruence.
Qed.

Lemma update_o:
  forall r v e r', r' <> r -> update r v e r' =  e r'.
Proof.
  unfold update; intros. destruct (reg_eq r' r). congruence. auto.
Qed.

Lemma update_ident:
  forall r e, update r (e r) e = e.
Proof.
  intros. apply env_ext; intro. unfold update. destruct (reg_eq r0 r); congruence.
Qed.

Lemma update_commut:
  forall r1 v1 r2 v2 e,
  r1 <> r2 ->
  update r1 v1 (update r2 v2 e) = update r2 v2 (update r1 v1 e).
Proof.
  intros. apply env_ext; intro; unfold update.
  destruct (reg_eq r r1); destruct (reg_eq r r2); auto.
  congruence.
Qed.

Lemma update_twice:
  forall r v e,
  update r v (update r v e) = update r v e.
Proof.
  intros. apply env_ext; intro; unfold update.
  destruct (reg_eq r0 r); auto.
Qed.

(** A list of moves [(src1, dst1), ..., (srcN, dstN)] can be given
  three different semantics, as environment transformers.
  The first semantics corresponds to a parallel assignment:
  [dst1, ..., dstN] are set to the initial values of [src1, ..., srcN]. *)

Fixpoint exec_par (m: moves) (e: env) {struct m}: env :=
  match m with
  | nil => e
  | (s, d) :: m' => update d (e s) (exec_par m' e)
  end.

(** The second semantics corresponds to a sequence of individual
  assignments: first, [dst1] is set to the initial value of [src1];
  then, [dst2] is set to the current value of [src2] after the first
  assignment; etc. *)

Fixpoint exec_seq (m: moves) (e: env) {struct m}: env :=
  match m with
  | nil => e
  | (s, d) :: m' => exec_seq m' (update d (e s) e)
  end.

(** The third semantics is also sequential, but executes the moves
  in reverse order, starting with [srcN, dstN] and finishing with
  [src1, dst1]. *)

Fixpoint exec_seq_rev (m: moves) (e: env) {struct m}: env :=
  match m with
  | nil => e
  | (s, d) :: m' =>
      let e' := exec_seq_rev m' e in
      update d (e' s) e'
  end.

(** * Specification of the non-deterministic algorithm *)

(** Rideau and Serpette's parallel move compilation algorithm is first
   specified as a non-deterministic set of rewriting rules operating
   over triples [(mu, sigma, tau)] of moves.  We define these rules
   as an inductive predicate [transition] relating triples of moves,
   and its reflexive transitive closure [transitions]. *)

Inductive state: Type :=
  State (mu: moves) (sigma: moves) (tau: moves) : state.

Definition no_read (mu: moves) (d: reg) : Prop :=
  ~In d (srcs mu).

Inductive transition: state -> state -> Prop :=
  | tr_nop: forall mu1 r mu2 sigma tau,
      transition (State (mu1 ++ (r, r) :: mu2) sigma tau)
                 (State (mu1 ++ mu2) sigma tau)
  | tr_start: forall mu1 s d mu2 tau,
      transition (State (mu1 ++ (s, d) :: mu2) nil tau)
                 (State (mu1 ++ mu2) ((s, d) :: nil) tau)
  | tr_push: forall mu1 d r mu2 s sigma tau,
      transition (State (mu1 ++ (d, r) :: mu2) ((s, d) :: sigma) tau)
                 (State (mu1 ++ mu2) ((d, r) :: (s, d) :: sigma) tau)
  | tr_loop: forall mu sigma s d tau,
      transition (State mu (sigma ++ (s, d) :: nil) tau)
                 (State mu (sigma ++ (temp s, d) :: nil) ((s, temp s) :: tau))
  | tr_pop: forall mu s0 d0 s1 d1 sigma tau,
      no_read mu d1 -> d1 <> s0 ->
      transition (State mu ((s1, d1) :: sigma ++ (s0, d0) :: nil) tau)
                 (State mu (sigma ++ (s0, d0) :: nil) ((s1, d1) :: tau))
  | tr_last: forall mu s d tau,
      no_read mu d ->
      transition (State mu ((s, d) :: nil) tau)
                 (State mu nil ((s, d) :: tau)).

Definition transitions: state -> state -> Prop :=
  clos_refl_trans state transition.

(** ** Well-formedness properties of states *)

(** A state [mu, sigma, tau] is well-formed if the following properties hold:

- [mu] concatenated with [sigma] is a ``mill'', that is, no destination
  appears twice (predicate [is_mill] below).
- No temporary register appears in [mu] (predicate [move_no_temp]).
- No temporary register appears in [sigma] except perhaps as the source
  of the last move in [sigma] (predicate [temp_last]).
- [sigma] is a ``path'', that is, the source of a move is the destination
  of the following move.
*)

Definition is_mill (m: moves) : Prop :=
  list_norepet (dests m).

Definition is_not_temp (r: reg) : Prop :=
  forall d, r <> temp d.

Definition move_no_temp (m: moves) : Prop :=
  forall s d, In (s, d) m -> is_not_temp s /\ is_not_temp d.

Definition temp_last (m: moves) : Prop :=
  match List.rev m with
  | nil => True
  | (s, d) :: m' => is_not_temp d /\ move_no_temp m'
  end.

Definition is_first_dest (m: moves) (d: reg) : Prop :=
  match m with
  | nil => True
  | (s0, d0) :: _ => d = d0
  end.

Inductive is_path: moves -> Prop :=
  | is_path_nil:
      is_path nil
  | is_path_cons: forall s d m,
      is_first_dest m s ->
      is_path m ->
      is_path ((s, d) :: m).

Inductive state_wf: state -> Prop :=
  | state_wf_intro:
      forall mu sigma tau,
      is_mill (mu ++ sigma) ->
      move_no_temp mu ->
      temp_last sigma ->
      is_path sigma ->
      state_wf (State mu sigma tau).

(** Some trivial properties of srcs and dests. *)

Lemma dests_append:
  forall m1 m2, dests (m1 ++ m2) = dests m1 ++ dests m2.
Proof.
  intros. unfold dests. apply map_app.
Qed.

Lemma dests_decomp:
  forall m1 s d m2, dests (m1 ++ (s, d) :: m2) = dests m1 ++ d :: dests m2.
Proof.
  intros. unfold dests. rewrite map_app. reflexivity.
Qed.

Lemma srcs_append:
  forall m1 m2, srcs (m1 ++ m2) = srcs m1 ++ srcs m2.
Proof.
  intros. unfold srcs. apply map_app.
Qed.

Lemma srcs_decomp:
  forall m1 s d m2, srcs (m1 ++ (s, d) :: m2) = srcs m1 ++ s :: srcs m2.
Proof.
  intros. unfold srcs. rewrite map_app. reflexivity.
Qed.

Lemma srcs_dests_combine:
  forall s d,
  List.length s = List.length d ->
  srcs (List.combine s d) = s /\
  dests (List.combine s d) = d.
Proof.
  induction s; destruct d; simpl; intros.
  tauto.
  discriminate.
  discriminate.
  elim (IHs d); intros. split; congruence. congruence.
Qed.

(** Some properties of [is_mill] and [dests_disjoint]. *)

Definition dests_disjoint (m1 m2: moves) : Prop :=
  list_disjoint (dests m1) (dests m2).

Lemma dests_disjoint_sym:
  forall m1 m2,
  dests_disjoint m1 m2 <-> dests_disjoint m2 m1.
Proof.
  unfold dests_disjoint; intros.
  split; intros; apply list_disjoint_sym; auto.
Qed.

Lemma dests_disjoint_cons_left:
  forall m1 s d m2,
  dests_disjoint ((s, d) :: m1) m2 <->
  dests_disjoint m1 m2 /\ ~In d (dests m2).
Proof.
  unfold dests_disjoint, list_disjoint.
  simpl; intros; split; intros.
  split. auto. firstorder.
  destruct H. elim H0; intro.
  red; intro; subst. contradiction.
  apply H; auto.
Qed.

Lemma dests_disjoint_cons_right:
  forall m1 s d m2,
  dests_disjoint m1 ((s, d) :: m2) <->
  dests_disjoint m1 m2 /\ ~In d (dests m1).
Proof.
  intros. rewrite dests_disjoint_sym. rewrite dests_disjoint_cons_left.
  rewrite dests_disjoint_sym. tauto.
Qed.

Lemma dests_disjoint_append_left:
  forall m1 m2 m3,
  dests_disjoint (m1 ++ m2) m3 <->
  dests_disjoint m1 m3 /\ dests_disjoint m2 m3.
Proof.
  unfold dests_disjoint, list_disjoint.
  intros; split; intros. split; intros.
  apply H; eauto. rewrite dests_append. apply in_or_app. auto.
  apply H; eauto. rewrite dests_append. apply in_or_app. auto.
  destruct H.
  rewrite dests_append in H0. elim (in_app_or _ _ _ H0); auto.
Qed.

Lemma dests_disjoint_append_right:
  forall m1 m2 m3,
  dests_disjoint m1 (m2 ++ m3) <->
  dests_disjoint m1 m2 /\ dests_disjoint m1 m3.
Proof.
  intros. rewrite dests_disjoint_sym. rewrite dests_disjoint_append_left.
  intuition; rewrite dests_disjoint_sym; assumption.
Qed.

Lemma is_mill_cons:
  forall s d m,
  is_mill ((s, d) :: m) <->
  is_mill m /\ ~In d (dests m).
Proof.
  unfold is_mill, dests_disjoint; intros. simpl.
  split; intros.
  inversion H; tauto.
  constructor; tauto.
Qed.

Lemma is_mill_append:
  forall m1 m2,
  is_mill (m1 ++ m2) <->
  is_mill m1 /\ is_mill m2 /\ dests_disjoint m1 m2.
Proof.
  unfold is_mill, dests_disjoint; intros. rewrite dests_append.
  apply list_norepet_app.
Qed.

(** Some properties of [move_no_temp]. *)

Lemma move_no_temp_append:
  forall m1 m2,
  move_no_temp m1 -> move_no_temp m2 -> move_no_temp (m1 ++ m2).
Proof.
  intros; red; intros. elim (in_app_or _ _ _ H1); intro.
  apply H; auto. apply H0; auto.
Qed.

Lemma move_no_temp_rev:
  forall m, move_no_temp (List.rev m) -> move_no_temp m.
Proof.
  intros; red; intros. apply H. rewrite <- List.In_rev. auto.
Qed.

(** Some properties of [temp_last]. *)

Lemma temp_last_change_last_source:
  forall s d s' sigma,
  temp_last (sigma ++ (s, d) :: nil) ->
  temp_last (sigma ++ (s', d) :: nil).
Proof.
  intros until sigma. unfold temp_last.
  repeat rewrite rev_unit. auto.
Qed.

Lemma temp_last_push:
  forall s1 d1 s2 d2 sigma,
  temp_last ((s2, d2) :: sigma) ->
  is_not_temp s1 -> is_not_temp d1 ->
  temp_last ((s1, d1) :: (s2, d2) :: sigma).
Proof.
  unfold temp_last; intros. simpl. simpl in H.
  destruct (rev sigma); simpl in *.
  intuition. red; simpl; intros.
  elim H; intros. inversion H4. subst; tauto. tauto.
  destruct p as [sN dN]. intuition.
  red; intros. elim (in_app_or _ _ _ H); intros.
  apply H3; auto.
  elim H4; intros. inversion H5; subst; tauto. elim H5.
Qed.

Lemma temp_last_pop:
  forall s1 d1 sigma s2 d2,
  temp_last ((s1, d1) :: sigma ++ (s2, d2) :: nil) ->
  temp_last (sigma ++ (s2, d2) :: nil).
Proof.
  intros until d2.
  change ((s1, d1) :: sigma ++ (s2, d2) :: nil)
    with ((((s1, d1) :: nil) ++ sigma) ++ ((s2, d2) :: nil)).
  unfold temp_last. repeat rewrite rev_unit.
  intuition. simpl in H1. red; intros. apply H1.
  apply in_or_app. auto.
Qed.

(** Some properties of [is_path]. *)

Lemma is_path_pop:
  forall s d m,
  is_path ((s, d) :: m) -> is_path m.
Proof.
  intros. inversion H; subst. auto.
Qed.

Lemma is_path_change_last_source:
  forall s s' d sigma,
  is_path (sigma ++ (s, d) :: nil) ->
  is_path (sigma ++ (s', d) :: nil).
Proof.
  induction sigma; simpl; intros.
  constructor. red; auto. constructor.
  inversion H; subst; clear H.
  constructor.
  destruct sigma as [ | [s1 d1] sigma']; simpl; simpl in H2; auto.
  auto.
Qed.

Lemma path_sources_dests:
  forall s0 d0 sigma,
  is_path (sigma ++ (s0, d0) :: nil) ->
  List.incl (srcs (sigma ++ (s0, d0) :: nil))
            (s0 :: dests (sigma ++ (s0, d0) :: nil)).
Proof.
  induction sigma; simpl; intros.
  red; simpl; tauto.
  inversion H; subst; clear H. simpl.
  assert (In s (dests (sigma ++ (s0, d0) :: nil))).
    destruct sigma as [ | [s1 d1] sigma']; simpl; simpl in H2; intuition.
  apply incl_cons. simpl; tauto.
  apply incl_tran with (s0 :: dests (sigma ++ (s0, d0) :: nil)).
  eapply IHsigma; eauto.
  red; simpl; tauto.
Qed.

Lemma no_read_path:
  forall d1 sigma s0 d0,
  d1 <> s0 ->
  is_path (sigma ++ (s0, d0) :: nil) ->
  ~In d1 (dests (sigma ++ (s0, d0) :: nil)) ->
  no_read (sigma ++ (s0, d0) :: nil) d1.
Proof.
  intros.
  generalize (path_sources_dests _ _ _ H0). intro.
  intro. elim H1. elim (H2 _ H3); intro. congruence. auto.
Qed.

(** To benefit from some proof automation, we populate a rewrite database
  with some of the properties above. *)

Lemma notin_dests_cons:
  forall x s d m,
  ~In x (dests ((s, d) :: m)) <-> x <> d /\ ~In x (dests m).
Proof.
  intros. simpl. intuition auto.
Qed.

Lemma notin_dests_append:
  forall d m1 m2,
  ~In d (dests (m1 ++ m2)) <-> ~In d (dests m1) /\ ~In d (dests m2).
Proof.
  intros. rewrite dests_append. rewrite in_app. tauto.
Qed.

Hint Rewrite is_mill_cons is_mill_append
  dests_disjoint_cons_left dests_disjoint_cons_right
  dests_disjoint_append_left dests_disjoint_append_right
  notin_dests_cons notin_dests_append: pmov.

(** ** Transitions preserve well-formedness *)

Lemma transition_preserves_wf:
  forall st st',
  transition st st' -> state_wf st -> state_wf st'.
Proof.
  induction 1; intro WF; inversion WF as [mu0 sigma0 tau0 A B C D];
  subst;
  autorewrite with pmov in A; constructor; autorewrite with pmov.

  (* Nop *)
  tauto.
  red; intros. apply B. apply list_in_insert; auto.
  auto. auto.

  (* Start *)
  tauto.
  red; intros. apply B. apply list_in_insert; auto.
  red. simpl. split. elim (B s d). auto.
  apply in_or_app. right. apply in_eq.
  red; simpl; tauto.
  constructor. exact I. constructor.

  (* Push *)
  intuition.
  red; intros. apply B. apply list_in_insert; auto.
  elim (B d r). apply temp_last_push; auto.
  apply in_or_app; right; apply in_eq.
  constructor. simpl. auto. auto.

  (* Loop *)
  tauto.
  auto.
  eapply temp_last_change_last_source; eauto.
  eapply is_path_change_last_source; eauto.

  (* Pop *)
  intuition.
  auto.
  eapply temp_last_pop; eauto.
  eapply is_path_pop; eauto.

  (* Last *)
  intuition.
  auto.
  unfold temp_last. simpl. auto.
  constructor.
Qed.

Lemma transitions_preserve_wf:
  forall st st', transitions st st' -> state_wf st -> state_wf st'.
Proof.
  induction 1; intros; eauto.
  eapply transition_preserves_wf; eauto.
Qed.

(** ** Transitions preserve semantics *)

(** We define the semantics of states as follows.
  For a triple [mu, sigma, tau], we perform the moves [tau] in
  reverse sequential order, then the moves [mu ++ sigma] in parallel. *)

Definition statemove (st: state) (e: env) :=
  match st with
  | State mu sigma tau => exec_par (mu ++ sigma) (exec_seq_rev tau e)
  end.

(** In preparation to showing that transitions preserve semantics,
  we prove various properties of the parallel and sequential interpretations
  of moves. *)

Lemma exec_par_outside:
  forall m e r, ~In r (dests m) -> exec_par m e r = e r.
Proof.
  induction m; simpl; intros. auto.
  destruct a as [s d]. rewrite update_o. apply IHm. tauto.
  simpl in H. intuition.
Qed.

Lemma exec_par_lift:
  forall m1 s d m2 e,
  ~In d (dests m1) ->
  exec_par (m1 ++ (s, d) :: m2) e = exec_par ((s, d) :: m1 ++ m2) e.
Proof.
  induction m1; simpl; intros.
  auto.
  destruct a as [s0 d0]. simpl in H. rewrite IHm1. simpl.
  apply update_commut. tauto. tauto.
Qed.

Lemma exec_par_ident:
  forall m1 r m2 e,
  is_mill (m1 ++ (r, r) :: m2) ->
  exec_par (m1 ++ (r, r) :: m2) e = exec_par (m1 ++ m2) e.
Proof.
  intros. autorewrite with pmov in H.
  rewrite exec_par_lift. simpl.
  replace (e r) with (exec_par (m1 ++ m2) e r). apply update_ident.
  apply exec_par_outside. autorewrite with pmov. tauto. tauto.
Qed.

Lemma exec_seq_app:
  forall m1 m2 e,
  exec_seq (m1 ++ m2) e = exec_seq m2 (exec_seq m1 e).
Proof.
  induction m1; simpl; intros. auto.
  destruct a as [s d]. rewrite IHm1. auto.
Qed.

Lemma exec_seq_rev_app:
  forall m1 m2 e,
  exec_seq_rev (m1 ++ m2) e = exec_seq_rev m1 (exec_seq_rev m2 e).
Proof.
  induction m1; simpl; intros. auto.
  destruct a as [s d]. rewrite IHm1. auto.
Qed.

Lemma exec_seq_exec_seq_rev:
  forall m e,
  exec_seq_rev m e = exec_seq (List.rev m) e.
Proof.
  induction m; simpl; intros.
  auto.
  destruct a as [s d]. rewrite exec_seq_app. simpl. rewrite IHm. auto.
Qed.

Lemma exec_seq_rev_exec_seq:
  forall m e,
  exec_seq m e = exec_seq_rev (List.rev m) e.
Proof.
  intros. generalize (exec_seq_exec_seq_rev (List.rev m) e).
  rewrite List.rev_involutive. auto.
Qed.

Lemma exec_par_update_no_read:
  forall s d m e,
  no_read m d ->
  ~In d (dests m) ->
  exec_par m (update d (e s) e) =
  update d (e s) (exec_par m e).
Proof.
  unfold no_read; induction m; simpl; intros.
  auto.
  destruct a as [s0 d0]; simpl in *. rewrite IHm.
  rewrite update_commut. f_equal. f_equal.
  apply update_o. tauto. tauto. tauto. tauto.
Qed.

Lemma exec_par_append_eq:
  forall m1 m2 m3 e2 e3,
  exec_par m2 e2 = exec_par m3 e3 ->
  (forall r, In r (srcs m1) -> e2 r = e3 r) ->
  exec_par (m1 ++ m2) e2 = exec_par (m1 ++ m3) e3.
Proof.
  induction m1; simpl; intros.
  auto. destruct a as [s d]. f_equal; eauto.
Qed.

Lemma exec_par_combine:
  forall e sl dl,
  List.length sl = List.length dl ->
  list_norepet dl ->
  let e' := exec_par (combine sl dl) e in
  List.map e' dl = List.map e sl /\
  (forall l, ~In l dl -> e' l = e l).
Proof.
  induction sl; destruct dl; simpl; intros; try discriminate.
  split; auto.
  inversion H0; subst; clear H0.
  injection H; intro; clear H.
  destruct (IHsl dl H0 H4) as [A B].
  set (e' := exec_par (combine sl dl) e) in *.
  split.
  decEq. apply update_s.
  rewrite <- A. apply list_map_exten; intros.
  rewrite update_o. auto. congruence.
  intros. rewrite update_o. apply B. tauto. intuition.
Qed.

(** [env_equiv] is an equivalence relation between environments
  capturing the fact that two environments assign the same values to
  non-temporary registers, but can disagree on the values of temporary
  registers. *)

Definition env_equiv (e1 e2: env) : Prop :=
  forall r, is_not_temp r -> e1 r = e2 r.

Lemma env_equiv_refl:
  forall e, env_equiv e e.
Proof.
  unfold env_equiv; auto.
Qed.

Lemma env_equiv_refl':
  forall e1 e2, e1 = e2 -> env_equiv e1 e2.
Proof.
  unfold env_equiv; intros. rewrite H. auto.
Qed.

Lemma env_equiv_sym:
  forall e1 e2, env_equiv e1 e2 -> env_equiv e2 e1.
Proof.
  unfold env_equiv; intros. symmetry; auto.
Qed.

Lemma env_equiv_trans:
  forall e1 e2 e3, env_equiv e1 e2 -> env_equiv e2 e3 -> env_equiv e1 e3.
Proof.
  unfold env_equiv; intros. transitivity (e2 r); auto.
Qed.

Lemma exec_par_env_equiv:
  forall m e1 e2,
  move_no_temp m ->
  env_equiv e1 e2 ->
  env_equiv (exec_par m e1) (exec_par m e2).
Proof.
  unfold move_no_temp; induction m; simpl; intros.
  auto.
  destruct a as [s d].
  red; intros. unfold update. destruct (reg_eq r d).
  apply H0. elim (H s d); tauto.
  apply IHm; auto.
Qed.

(** The proof that transitions preserve semantics (up to the values of
  temporary registers) follows. *)

Lemma transition_preserves_semantics:
  forall st st' e,
  transition st st' -> state_wf st ->
  env_equiv (statemove st' e) (statemove st e).
Proof.
  induction 1; intro WF; inversion WF as [mu0 sigma0 tau0 A B C D]; subst; simpl.

  (* nop *)
  apply env_equiv_refl'. unfold statemove.
  repeat rewrite app_ass. simpl. symmetry. apply exec_par_ident.
  rewrite app_ass in A. exact A.

  (* start *)
  apply env_equiv_refl'. unfold statemove.
  autorewrite with pmov in A.
  rewrite exec_par_lift. repeat rewrite app_ass. simpl. rewrite exec_par_lift. reflexivity.
  tauto. autorewrite with pmov. tauto.

  (* push *)
  apply env_equiv_refl'. unfold statemove.
  autorewrite with pmov in A.
  rewrite exec_par_lift. rewrite exec_par_lift. simpl.
  rewrite exec_par_lift. repeat rewrite app_ass. simpl. rewrite exec_par_lift.
  simpl. apply update_commut. intuition.
  tauto. autorewrite with pmov; tauto.
  autorewrite with pmov; intuition.
  autorewrite with pmov; intuition.

  (* loop *)
  unfold statemove. simpl exec_seq_rev.
  set (e1 := exec_seq_rev tau e).
  autorewrite with pmov in A.
  repeat rewrite <- app_ass.
  assert (~In d (dests (mu ++ sigma))). autorewrite with pmov. tauto.
  repeat rewrite exec_par_lift; auto. simpl.
  repeat rewrite <- app_nil_end.
  assert (move_no_temp (mu ++ sigma)).
    red in C. rewrite rev_unit in C. destruct C.
    apply move_no_temp_append; auto. apply move_no_temp_rev; auto.
  set (e2 := update (temp s) (e1 s) e1).
  set (e3 := exec_par (mu ++ sigma) e1).
  set (e4 := exec_par (mu ++ sigma) e2).
  assert (env_equiv e2 e1).
    unfold e2; red; intros. apply update_o. apply H1.
  assert (env_equiv e4 e3).
    unfold e4, e3. apply exec_par_env_equiv; auto.
  red; intros. unfold update. destruct (reg_eq r d).
  unfold e2. apply update_s. apply H2. auto.

  (* pop *)
  apply env_equiv_refl'. unfold statemove. simpl exec_seq_rev.
  set (e1 := exec_seq_rev tau e).
  autorewrite with pmov in A.
  apply exec_par_append_eq. simpl.
  apply exec_par_update_no_read.
  apply no_read_path; auto. eapply is_path_pop; eauto.
  autorewrite with pmov; tauto.
  autorewrite with pmov; tauto.
  intros. apply update_o. red; intro; subst r. elim (H H1).

  (* last *)
  apply env_equiv_refl'. unfold statemove. simpl exec_seq_rev.
  set (e1 := exec_seq_rev tau e).
  apply exec_par_append_eq. simpl. auto.
  intros. apply update_o. red; intro; subst r. elim (H H0).
Qed.

Lemma transitions_preserve_semantics:
  forall st st' e,
  transitions st st' -> state_wf st ->
  env_equiv (statemove st' e) (statemove st e).
Proof.
  induction 1; intros.
  eapply transition_preserves_semantics; eauto.
  apply env_equiv_refl.
  apply env_equiv_trans with (statemove y e); auto.
  apply IHclos_refl_trans2. eapply transitions_preserve_wf; eauto.
Qed.

Lemma state_wf_start:
  forall mu,
  move_no_temp mu ->
  is_mill mu ->
  state_wf (State mu nil nil).
Proof.
  intros. constructor. rewrite <- app_nil_end. auto.
  auto.
  red. simpl. auto.
  constructor.
Qed.

(** The main correctness result in this section is the following:
  if we can transition repeatedly from an initial state [mu, nil, nil]
  to a final state [nil, nil, tau], then the sequential execution
  of the moves [rev tau] is semantically equivalent to the parallel
  execution of the moves [mu]. *)

Theorem transitions_correctness:
  forall mu tau,
  move_no_temp mu ->
  is_mill mu ->
  transitions (State mu nil nil) (State nil nil tau) ->
  forall e, env_equiv (exec_seq (List.rev tau) e) (exec_par mu e).
Proof.
  intros.
  generalize (transitions_preserve_semantics _ _ e H1
              (state_wf_start _ H H0)).
  unfold statemove. simpl. rewrite <- app_nil_end.
  rewrite exec_seq_exec_seq_rev. auto.
Qed.

(** * Determinisation of the transition relation *)

(** We now define a deterministic variant [dtransition] of the
  transition relation [transition].  [dtransition] is deterministic
  in the sense that at most one transition applies to a given state. *)

Inductive dtransition: state -> state -> Prop :=
  | dtr_nop: forall r mu tau,
      dtransition (State ((r, r) :: mu) nil tau)
                  (State mu nil tau)
  | dtr_start: forall s d mu tau,
      s <> d ->
      dtransition (State ((s, d) :: mu) nil tau)
                  (State mu ((s, d) :: nil) tau)
  | dtr_push: forall mu1 d r mu2 s sigma tau,
      no_read mu1 d ->
      dtransition (State (mu1 ++ (d, r) :: mu2) ((s, d) :: sigma) tau)
                  (State (mu1 ++ mu2) ((d, r) :: (s, d) :: sigma) tau)
  | dtr_loop_pop: forall mu s r0 d  sigma tau,
      no_read mu r0 ->
      dtransition (State mu ((s, r0) :: sigma ++ (r0, d) :: nil) tau)
                  (State mu (sigma ++ (temp r0, d) :: nil) ((s, r0) :: (r0, temp r0) :: tau))
  | dtr_pop: forall mu s0 d0 s1 d1 sigma tau,
      no_read mu d1 -> d1 <> s0 ->
      dtransition (State mu ((s1, d1) :: sigma ++ (s0, d0) :: nil) tau)
                  (State mu (sigma ++ (s0, d0) :: nil) ((s1, d1) :: tau))
  | dtr_last: forall mu s d tau,
      no_read mu d ->
      dtransition (State mu ((s, d) :: nil) tau)
                  (State mu nil ((s, d) :: tau)).

Definition dtransitions: state -> state -> Prop :=
  clos_refl_trans state dtransition.

(** Every deterministic transition corresponds to a sequence of
  non-deterministic transitions. *)

Lemma transition_determ:
  forall st st',
  dtransition st st' ->
  state_wf st ->
  transitions st st'.
Proof.
  induction 1; intro; unfold transitions.
  apply rt_step. exact (tr_nop nil r mu nil tau).
  apply rt_step. exact (tr_start nil s d mu tau).
  apply rt_step. apply tr_push.
  eapply rt_trans.
    apply rt_step.
    change ((s, r0) :: sigma ++ (r0, d) :: nil)
      with (((s, r0) :: sigma) ++ (r0, d) :: nil).
    apply tr_loop.
    apply rt_step. simpl. apply tr_pop. auto.
    inv H0.  generalize H6.
    change ((s, r0) :: sigma ++ (r0, d) :: nil)
      with (((s, r0) :: sigma) ++ (r0, d) :: nil).
    unfold temp_last; rewrite List.rev_unit. intros [E F].
    elim (F s r0). unfold is_not_temp. auto.
    rewrite <- List.In_rev. apply in_eq.
  apply rt_step. apply tr_pop. auto. auto.
  apply rt_step. apply tr_last. auto.
Qed.

Lemma transitions_determ:
  forall st st',
  dtransitions st st' ->
  state_wf st ->
  transitions st st'.
Proof.
  unfold transitions; induction 1; intros.
  eapply transition_determ; eauto.
  apply rt_refl.
  apply rt_trans with y. auto.
    apply IHclos_refl_trans2.
    apply transitions_preserve_wf with x; auto. red; auto.
Qed.

(** The semantic correctness of deterministic transitions follows. *)

Theorem dtransitions_correctness:
  forall mu tau,
  move_no_temp mu ->
  is_mill mu ->
  dtransitions (State mu nil nil) (State nil nil tau) ->
  forall e, env_equiv (exec_seq (List.rev tau) e) (exec_par mu e).
Proof.
  intros.
  eapply transitions_correctness; eauto.
  apply transitions_determ. auto. apply state_wf_start; auto.
Qed.

(** * The compilation function *)

(** We now define a function that takes a well-formed parallel move [mu]
  and returns a sequence of elementary moves [tau] that is semantically
  equivalent.  We start by defining a number of auxiliary functions. *)

Fixpoint split_move (m: moves) (r: reg) {struct m} : option (moves * reg * moves) :=
  match m with
  | nil => None
  | (s, d) :: tl =>
      if reg_eq s r
      then Some (nil, d, tl)
      else match split_move tl r with
           | None => None
           | Some (before, d', after) => Some ((s, d) :: before, d', after)
           end
  end.

Fixpoint is_last_source (r: reg) (m: moves) {struct m} : bool :=
  match m with
  | nil => false
  | (s, d) :: nil =>
      if reg_eq s r then true else false
  | (s, d) :: tl =>
      is_last_source r tl
  end.

Fixpoint replace_last_source (r: reg) (m: moves) {struct m} : moves :=
  match m with
  | nil => nil
  | (s, d) :: nil => (r, d) :: nil
  | s_d :: tl => s_d :: replace_last_source r tl
  end.

Definition final_state (st: state) : bool :=
  match st with
  | State nil nil _ => true
  | _ => false
  end.

Definition parmove_step (st: state) : state :=
  match st with
  | State nil nil _ => st
  | State ((s, d) :: tl) nil l =>
      if reg_eq s d
      then State tl nil l
      else State tl ((s, d) :: nil) l
  | State t ((s, d) :: b) l =>
      match split_move t d with
      | Some (t1, r, t2) =>
          State (t1 ++ t2) ((d, r) :: (s, d) :: b) l
      | None =>
          match b with
          | nil => State t nil ((s, d) :: l)
          | _ =>
              if is_last_source d b
              then State t (replace_last_source (temp d) b) ((s, d) :: (d, temp d) :: l)
              else State t b ((s, d) :: l)
          end
      end
  end.

(** Here are the main correctness properties of these functions. *)

Lemma split_move_charact:
  forall m r,
  match split_move m r with
  | Some (before, d, after) => m = before ++ (r, d) :: after /\ no_read before r
  | None => no_read m r
  end.
Proof.
  unfold no_read. induction m; simpl; intros.
- tauto.
- destruct a as [s d]. destruct (reg_eq s r).
  + subst s. auto.
  + specialize (IHm r). destruct (split_move m r) as [[[before d'] after] | ].
    * destruct IHm. subst m. simpl. intuition.
    * simpl; intuition.
Qed.

Lemma is_last_source_charact:
  forall r s d m,
  if is_last_source r (m ++ (s, d) :: nil)
  then s = r
  else s <> r.
Proof.
  induction m; simpl.
  destruct (reg_eq s r); congruence.
  destruct a as [s0 d0]. case_eq (m ++ (s, d) :: nil); intros.
  generalize (app_cons_not_nil m nil (s, d)). congruence.
  rewrite <- H. auto.
Qed.

Lemma replace_last_source_charact:
  forall s d s' m,
  replace_last_source s' (m ++ (s, d) :: nil) =
  m ++ (s', d) :: nil.
Proof.
  induction m; simpl.
  auto.
  destruct a as [s0 d0]. case_eq (m ++ (s, d) :: nil); intros.
  generalize (app_cons_not_nil m nil (s, d)). congruence.
  rewrite <- H. congruence.
Qed.

Lemma parmove_step_compatible:
  forall st,
  final_state st = false ->
  dtransition st (parmove_step st).
Proof.
  intros st NOTFINAL. destruct st as [mu sigma tau]. unfold parmove_step.
  case_eq mu; [intros MEQ | intros [ms md] mtl MEQ].
  case_eq sigma; [intros SEQ | intros [ss sd] stl SEQ].
  subst mu sigma. simpl in NOTFINAL. discriminate.
  simpl.
  case_eq stl; [intros STLEQ | intros xx1 xx2 STLEQ].
  apply dtr_last. red; simpl; auto.
  elim (@exists_last _ stl). 2:congruence. intros sigma1 [[ss1 sd1] SEQ2].
  rewrite <- STLEQ. clear STLEQ xx1 xx2.
  generalize (is_last_source_charact sd ss1 sd1 sigma1).
  rewrite SEQ2. destruct (is_last_source sd (sigma1 ++ (ss1, sd1) :: nil)).
  intro. subst ss1.
  rewrite replace_last_source_charact. apply dtr_loop_pop.
  red; simpl; auto.
  intro. apply dtr_pop. red; simpl; auto. auto.

  case_eq sigma; [intros SEQ | intros [ss sd] stl SEQ].
  destruct (reg_eq ms md).
  subst. apply dtr_nop.
  apply dtr_start. auto.

  generalize (split_move_charact ((ms, md) :: mtl) sd).
  case (split_move ((ms, md) :: mtl) sd); [intros [[before r] after] | idtac].
  intros [MEQ2 NOREAD].
  rewrite MEQ2. apply dtr_push. auto.
  intro NOREAD.
  case_eq stl; [intros STLEQ | intros xx1 xx2 STLEQ].
  apply dtr_last. auto.
  elim (@exists_last _ stl). 2:congruence. intros sigma1 [[ss1 sd1] SEQ2].
  rewrite <- STLEQ. clear STLEQ xx1 xx2.
  generalize (is_last_source_charact sd ss1 sd1 sigma1).
  rewrite SEQ2. destruct (is_last_source sd (sigma1 ++ (ss1, sd1) :: nil)).
  intro. subst ss1.
  rewrite replace_last_source_charact. apply dtr_loop_pop. auto.
  intro. apply dtr_pop. auto. auto.
Qed.

(** The compilation function is obtained by iterating the [parmov_step]
  function.  To show that this iteration always terminates, we introduce
  the following measure over states. *)

Open Scope nat_scope.

Definition measure (st: state) : nat :=
  match st with
  | State mu sigma tau => 2 * List.length mu + List.length sigma
  end.

Lemma measure_decreasing_1:
  forall st st',
  dtransition st st' -> measure st' < measure st.
Proof.
  induction 1; repeat (simpl; rewrite List.app_length); simpl; omega.
Qed.

Lemma measure_decreasing_2:
  forall st,
  final_state st = false ->
  measure (parmove_step st) < measure st.
Proof.
  intros. apply measure_decreasing_1. apply parmove_step_compatible; auto.
Qed.

(** Compilation function for parallel moves. *)

Function parmove_aux (st: state) {measure measure st} : moves :=
  if final_state st
  then match st with State _ _ tau => tau end
  else parmove_aux (parmove_step st).
Proof.
  intros. apply measure_decreasing_2. auto.
Qed.

Lemma parmove_aux_transitions:
  forall st,
  dtransitions st (State nil nil (parmove_aux st)).
Proof.
  unfold dtransitions. intro st. functional induction (parmove_aux st).
  destruct _x; destruct _x0; simpl in e; discriminate || apply rt_refl.
  eapply rt_trans. apply rt_step. apply parmove_step_compatible; eauto.
  auto.
Qed.

Definition parmove (mu: moves) : moves :=
  List.rev (parmove_aux (State mu nil nil)).

(** This is the main correctness theorem: the sequence of elementary
  moves [parmove mu] is semantically equivalent to the parallel move
  [mu] if the latter is well-formed. *)

Theorem parmove_correctness:
  forall mu,
  move_no_temp mu -> is_mill mu ->
  forall e,
  env_equiv (exec_seq (parmove mu) e) (exec_par mu e).
Proof.
  intros. unfold parmove. apply dtransitions_correctness; auto.
  apply parmove_aux_transitions.
Qed.

(** Here is an alternate formulation of [parmove], where the
  parallel move problem is given as two separate lists of sources
  and destinations. *)

Definition parmove2 (sl dl: list reg) : moves :=
  parmove (List.combine sl dl).

Theorem parmove2_correctness:
  forall sl dl,
  List.length sl = List.length dl ->
  list_norepet dl ->
  (forall r, In r sl -> is_not_temp r) ->
  (forall r, In r dl -> is_not_temp r) ->
  forall e,
  let e' := exec_seq (parmove2 sl dl) e in
  List.map e' dl = List.map e sl /\
  forall r, ~In r dl -> is_not_temp r -> e' r = e r.
Proof.
  intros.
  destruct (srcs_dests_combine sl dl H) as [A B].
  assert (env_equiv e' (exec_par (List.combine sl dl) e)).
    unfold e', parmove2. apply parmove_correctness.
    red; intros; split.
    apply H1. eapply List.in_combine_l; eauto.
    apply H2. eapply List.in_combine_r; eauto.
    red. rewrite B. auto.
  destruct (exec_par_combine e sl dl H H0) as [C D].
  set (e1 := exec_par (combine sl dl) e) in *.
  split. rewrite <- C. apply list_map_exten; intros.
  symmetry. apply H3. auto.
  intros. transitivity (e1 r); auto.
Qed.

(** * Additional syntactic properties *)

(** We now show an additional property of the sequence of moves
  generated by [parmove mu]: any such move [s -> d] is either
  already present in [mu], or of the form [temp s -> d] or [s -> temp s]
  for some [s -> d] in [mu].  This syntactic property is useful
  to show that [parmove] preserves register classes, for instance. *)

Section PROPERTIES.

Variable initial_move: moves.

Inductive wf_move: reg -> reg -> Prop :=
  | wf_move_same: forall s d,
      In (s, d) initial_move -> wf_move s d
  | wf_move_temp_left: forall s d,
      wf_move s d -> wf_move (temp s) d
  | wf_move_temp_right: forall s d,
      wf_move s d -> wf_move s (temp s).

Definition wf_moves (m: moves) : Prop :=
  forall s d, In (s, d) m -> wf_move s d.

Lemma wf_moves_cons: forall s d m,
  wf_moves ((s, d) :: m) <-> wf_move s d /\ wf_moves m.
Proof.
  unfold wf_moves; intros; simpl. firstorder.
  inversion H0; subst s0 d0. auto.
Qed.

Lemma wf_moves_append: forall m1 m2,
  wf_moves (m1 ++ m2) <-> wf_moves m1 /\ wf_moves m2.
Proof.
  unfold wf_moves; intros. split; intros.
  split; intros; apply H; apply in_or_app; auto.
  destruct H. elim (in_app_or _ _ _ H0); intro; auto.
Qed.

Hint Rewrite wf_moves_cons wf_moves_append: pmov.

Inductive wf_state: state -> Prop :=
  | wf_state_intro: forall mu sigma tau,
      wf_moves mu -> wf_moves sigma -> wf_moves tau ->
      wf_state (State mu sigma tau).

Lemma dtransition_preserves_wf_state:
  forall st st',
  dtransition st st' -> wf_state st -> wf_state st'.
Proof.
  induction 1; intro WF; inv WF; constructor; autorewrite with pmov in *; intuition.
  apply wf_move_temp_left; auto.
  eapply wf_move_temp_right; eauto.
Qed.

Lemma dtransitions_preserve_wf_state:
  forall st st',
  dtransitions st st' -> wf_state st -> wf_state st'.
Proof.
  induction 1; intros; eauto.
  eapply dtransition_preserves_wf_state; eauto.
Qed.

End PROPERTIES.

Lemma parmove_wf_moves:
  forall mu, wf_moves mu (parmove mu).
Proof.
  intros.
  assert (wf_state mu (State mu nil nil)).
    constructor. red; intros. apply wf_move_same. auto.
    red; simpl; tauto. red; simpl; tauto.
  generalize (dtransitions_preserve_wf_state mu
              _ _
              (parmove_aux_transitions (State mu nil nil)) H).
  intro WFS. inv WFS.
  unfold parmove. red; intros. apply H5.
  rewrite List.In_rev. auto.
Qed.

Lemma parmove2_wf_moves:
  forall sl dl, wf_moves (List.combine sl dl) (parmove2 sl dl).
Proof.
  intros. unfold parmove2. apply parmove_wf_moves.
Qed.

(** As a corollary, we show that all sources of [parmove mu]
    are sources of [mu] or temporaries,
    and likewise all destinations of [parmove mu] are destinations of [mu]
    or temporaries. *)

Remark wf_move_initial_reg_or_temp:
  forall mu s d,
  wf_move mu s d ->
  (In s (srcs mu) \/ is_temp s) /\ (In d (dests mu) \/ is_temp d).
Proof.
  induction 1.
  split; left.
  change s with (fst (s, d)). unfold srcs. apply List.in_map; auto.
  change d with (snd (s, d)). unfold dests. apply List.in_map; auto.
  split. right. exists s; auto. tauto.
  split. tauto. right. exists s; auto.
Qed.

Lemma parmove_initial_reg_or_temp:
  forall mu s d,
  In (s, d) (parmove mu) ->
  (In s (srcs mu) \/ is_temp s) /\ (In d (dests mu) \/ is_temp d).
Proof.
  intros. apply wf_move_initial_reg_or_temp. apply parmove_wf_moves. auto.
Qed.

Remark in_srcs:
  forall mu s, In s (srcs mu) -> exists d, In (s, d) mu.
Proof.
  intros. destruct (list_in_map_inv (@fst reg reg) _ _ H) as [[s' d'] [A B]].
  simpl in A. exists d'; congruence.
Qed.

Remark in_dests:
  forall mu d, In d (dests mu) -> exists s, In (s, d) mu.
Proof.
  intros. destruct (list_in_map_inv (@snd reg reg) _ _ H) as [[s' d'] [A B]].
  simpl in A. exists s'; congruence.
Qed.

Lemma parmove_srcs_initial_reg_or_temp:
  forall mu s,
  In s (srcs (parmove mu)) -> In s (srcs mu) \/ is_temp s.
Proof.
  intros. destruct (in_srcs _ _ H) as [d A].
  destruct (parmove_initial_reg_or_temp _ _ _ A). auto.
Qed.

Lemma parmove_dests_initial_reg_or_temp:
  forall mu d,
  In d (dests (parmove mu)) -> In d (dests mu) \/ is_temp d.
Proof.
  intros. destruct (in_dests _ _ H) as [s A].
  destruct (parmove_initial_reg_or_temp _ _ _ A). auto.
Qed.

(** As a second corollary, we show that [parmov] preserves register
    classes, in the sense made precise below. *)

Section REGISTER_CLASSES.

Variable class: Type.
Variable regclass: reg -> class.
Hypothesis temp_preserves_class: forall r, regclass (temp r) = regclass r.

Definition is_class_compatible (mu: moves) : Prop :=
  forall s d, In (s, d) mu -> regclass s = regclass d.

Lemma parmove_preserves_register_classes:
  forall mu,
  is_class_compatible mu ->
  is_class_compatible (parmove mu).
Proof.
  intros.
  assert (forall s d, wf_move mu s d -> regclass s = regclass d).
    induction 1.
    apply H; auto.
    rewrite temp_preserves_class. auto.
    symmetry; apply temp_preserves_class.
  red; intros. apply H0. apply parmove_wf_moves. auto.
Qed.

End REGISTER_CLASSES.

(** * Extension to partially overlapping registers *)

(** We now extend the previous results to the case where distinct
  registers can partially overlap, so that assigning to one register
  changes the value of the other.  We asuume given a disjointness relation
  [disjoint] between registers. *)

Variable disjoint: reg -> reg -> Prop.

Hypothesis disjoint_sym:
  forall r1 r2, disjoint r1 r2 -> disjoint r2 r1.

Hypothesis disjoint_not_equal:
  forall r1 r2, disjoint r1 r2 -> r1 <> r2.

(** Two registers partially overlap if they are different and not disjoint.
    For the Coq development, it is easier to define the complement:
    two registers do not partially overlap if they are identical or disjoint. *)

Definition no_overlap (r1 r2: reg) : Prop :=
  r1 = r2 \/ disjoint r1 r2.

Lemma no_overlap_sym:
  forall r1 r2, no_overlap r1 r2 -> no_overlap r2 r1.
Proof.
  intros. destruct H. left; auto. right; auto.
Qed.

(** We axiomatize the effect of assigning a value to a register over an
  execution environment.  The target register is set to the given value
  (property [weak_update_s]), and registers disjoint from the target
  keep their previous values (property [weak_update_d]).  The values of
  other registers are undefined after the assignment. *)

Variable weak_update: reg -> val -> env -> env.

Hypothesis weak_update_s:
  forall r v e, weak_update r v e r = v.

Hypothesis weak_update_d:
  forall r1 v e r2, disjoint r1 r2 -> weak_update r1 v e r2 = e r2.

Fixpoint weak_exec_seq (m: moves) (e: env) {struct m}: env :=
  match m with
  | nil => e
  | (s, d) :: m' => weak_exec_seq m' (weak_update d (e s) e)
  end.

Definition disjoint_list (r: reg) (l: list reg) : Prop :=
  forall r', In r' l -> disjoint r r'.

Inductive pairwise_disjoint: list reg -> Prop :=
  | pairwise_disjoint_nil:
      pairwise_disjoint nil
  | pairwise_disjoint_cons: forall r l,
      disjoint_list r l ->
      pairwise_disjoint l ->
      pairwise_disjoint (r :: l).

Definition disjoint_temps (r: reg) : Prop :=
  forall t, is_temp t -> disjoint r t.

Section OVERLAP.

(** We consider a parallel move problem [mu] that satisfies the following
  conditions, which are stronger, overlap-aware variants of the
  [move_no_temp mu] and [is_mill mu] conditions used previously. *)

Variable mu: moves.

(** Sources and destinations are disjoint from all temporary registers. *)

Hypothesis mu_no_temporaries_src:
  forall s, In s (srcs mu) -> disjoint_temps s.

Hypothesis mu_no_temporaries_dst:
  forall d, In d (dests mu) -> disjoint_temps d.

(** Destinations are pairwise disjoint. *)

Hypothesis mu_dest_pairwise_disjoint:
  pairwise_disjoint (dests mu).

(** Sources and destinations do not partially overlap. *)

Hypothesis mu_src_dst_no_overlap:
  forall s d, In s (srcs mu) -> In d (dests mu) -> no_overlap s d.

(** Distinct temporaries do not partially overlap. *)

Hypothesis temps_no_overlap:
  forall t1 t2, is_temp t1 -> is_temp t2 -> no_overlap t1 t2.

(** The following lemmas show that [mu] is a windmill and does not
  contain temporary registers. *)

Lemma disjoint_list_notin:
  forall r l, disjoint_list r l -> ~In r l.
Proof.
  intros. red; intro.
  assert (r <> r). apply disjoint_not_equal. apply H; auto.
  congruence.
Qed.

Lemma pairwise_disjoint_norepet:
  forall l, pairwise_disjoint l -> list_norepet l.
Proof.
  induction 1.
  constructor.
  constructor. apply disjoint_list_notin; auto. auto.
Qed.

Lemma disjoint_temps_not_temp:
  forall r, disjoint_temps r -> is_not_temp r.
Proof.
  intros; red; intros. apply disjoint_not_equal. apply H. exists d; auto.
Qed.

Lemma mu_is_mill:
  is_mill mu.
Proof.
  red. apply pairwise_disjoint_norepet. auto.
Qed.

Lemma mu_move_no_temp:
  move_no_temp mu.
Proof.
  red; intros.
  split; apply disjoint_temps_not_temp.
  apply mu_no_temporaries_src; auto.
  unfold srcs. change s with (fst (s,d)). apply List.in_map; auto.
  apply mu_no_temporaries_dst; auto.
  unfold dests. change d with (snd (s,d)). apply List.in_map; auto.
Qed.

(** We define the ``adherence'' of the problem [mu] as the set of
  registers that partially overlap with one of the registers
  possibly assigned by the parallel move: destinations and temporaries.
  Again, we define the complement of the ``adherence'' set, which is
  more convenient for Coq reasoning. *)

Definition no_adherence (r: reg) : Prop :=
  forall x, In x (dests mu) \/ is_temp x -> no_overlap x r.

(** As a consequence of the hypotheses on [mu], none of the destination
  registers, source registers, and temporaries belong to the adherence. *)

Lemma no_overlap_pairwise:
  forall r1 r2 m, pairwise_disjoint m -> In r1 m -> In r2 m -> no_overlap r1 r2.
Proof.
  induction 1; intros.
  elim H.
  simpl in *. destruct H1; destruct H2.
  left. congruence.
  subst. right. apply H. auto.
  subst. right. apply disjoint_sym. apply H. auto.
  auto.
Qed.

Lemma no_adherence_dst:
  forall d, In d (dests mu) -> no_adherence d.
Proof.
  intros; red; intros.
  destruct H0. apply no_overlap_pairwise with (dests mu); auto.
  right. apply disjoint_sym. apply mu_no_temporaries_dst; auto.
Qed.

Lemma no_adherence_src:
  forall s, In s (srcs mu) -> no_adherence s.
Proof.
  intros; red; intros.
  destruct H0.
  apply no_overlap_sym. apply mu_src_dst_no_overlap; auto.
  right. apply disjoint_sym. apply mu_no_temporaries_src; auto.
Qed.

Lemma no_adherence_tmp:
  forall t, is_temp t -> no_adherence t.
Proof.
  intros; red; intros.
  destruct H0.
  right. apply mu_no_temporaries_dst; auto.
  apply temps_no_overlap; auto.
Qed.

(** The relation [env_match] holds between two environments [e1] and [e2]
    if they assign the same values to all registers not in the adherence set. *)

Definition env_match (e1 e2: env) : Prop :=
  forall r, no_adherence r -> e1 r = e2 r.

(** The following lemmas relate the effect of executing moves
  using normal, overlap-unaware update and weak, overlap-aware update. *)

Lemma weak_update_match:
  forall e1 e2 s d,
  (In s (srcs mu) \/ is_temp s) ->
  (In d (dests mu) \/ is_temp d) ->
  env_match e1 e2 ->
  env_match (update d (e1 s) e1)
            (weak_update d (e2 s) e2).
Proof.
  intros. red; intros.
  assert (no_overlap d r). apply H2. auto.
  destruct H3.
  subst. rewrite update_s. rewrite weak_update_s. apply H1.
  destruct H. apply no_adherence_src; auto. apply no_adherence_tmp; auto.
  rewrite update_o. rewrite weak_update_d. apply H1. auto.
  auto. apply not_eq_sym. apply disjoint_not_equal. auto.
Qed.

Lemma weak_exec_seq_match:
  forall m e1 e2,
  (forall s, In s (srcs m) -> In s (srcs mu) \/ is_temp s) ->
  (forall d, In d (dests m) -> In d (dests mu) \/ is_temp d) ->
  env_match e1 e2 ->
  env_match (exec_seq m e1) (weak_exec_seq m e2).
Proof.
  induction m; intros; simpl.
  auto.
  destruct a as [s d]. simpl in H. simpl in H0.
  apply IHm; auto.
  apply weak_update_match; auto.
Qed.

End OVERLAP.

(** These lemmas imply the following correctness theorem for the [parmove2]
  function, taking partial register overlap into account. *)

Theorem parmove2_correctness_with_overlap:
  forall sl dl,
  List.length sl = List.length dl ->
  (forall r, In r sl -> disjoint_temps r) ->
  (forall r, In r dl -> disjoint_temps r) ->
  pairwise_disjoint dl ->
  (forall s d, In s sl -> In d dl -> no_overlap s d) ->
  (forall t1 t2, is_temp t1 -> is_temp t2 -> no_overlap t1 t2) ->
  forall e,
  let e' := weak_exec_seq (parmove2 sl dl) e in
  List.map e' dl = List.map e sl /\
  forall r, disjoint_list r dl -> disjoint_temps r -> e' r = e r.
Proof.
  intros.
  assert (list_norepet dl).
    apply pairwise_disjoint_norepet; auto.
  assert (forall r : reg, In r sl -> is_not_temp r).
    intros. apply disjoint_temps_not_temp; auto.
  assert (forall r : reg, In r dl -> is_not_temp r).
    intros. apply disjoint_temps_not_temp; auto.
  generalize (parmove2_correctness sl dl H H5 H6 H7 e).
  set (e1 := exec_seq (parmove2 sl dl) e). intros [A B].
  destruct (srcs_dests_combine sl dl H) as [C D].
  assert (env_match (combine sl dl) e1 e').
    unfold parmove2. unfold e1, e'.
    apply weak_exec_seq_match; try (rewrite C); try (rewrite D); auto.
    intros. rewrite <- C. apply parmove_srcs_initial_reg_or_temp. auto.
    intros. rewrite <- D. apply parmove_dests_initial_reg_or_temp. auto.
    red; auto.
  split.
  rewrite <- A.
  apply list_map_exten; intros. apply H8.
  apply no_adherence_dst. rewrite D; auto. rewrite D; auto. rewrite D; auto.
  intros. transitivity (e1 r).
  symmetry. apply H8. red. rewrite D. intros. destruct H11.
  right. apply disjoint_sym. apply H9. auto.
  right. apply disjoint_sym. apply H10. auto.
  apply B. apply disjoint_list_notin; auto. apply disjoint_temps_not_temp; auto.
Qed.

End PARMOV.
