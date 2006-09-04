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

  The development in this section was contributed by Laurence Rideau and
  Bernard Serpette.  It is described in their paper
  ``Coq à la conquête des moulins'', JFLA 2005, 
  #<A HREF="http://www-sop.inria.fr/lemme/Laurence.Rideau/RideauSerpetteJFLA05.ps">#
  http://www-sop.inria.fr/lemme/Laurence.Rideau/RideauSerpetteJFLA05.ps
  #</A>#
*)

Require Import Coqlib.
Require Recdef.

Section PARMOV.

Variable reg: Set.
Variable temp: reg -> reg.

Definition moves := (list (reg * reg))%type.  (* src -> dst *)

Definition srcs (m: moves) := List.map (@fst reg reg) m.
Definition dests (m: moves) := List.map (@snd reg reg) m.

(* Semantics of moves *)

Variable val: Set.
Definition env := reg -> val.
Variable reg_eq : forall (r1 r2: reg), {r1=r2} + {r1<>r2}.

Lemma env_ext:
  forall (e1 e2: env),
  (forall r, e1 r = e2 r) -> e1 = e2.
Proof (extensionality reg val).

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

Fixpoint exec_par (m: moves) (e: env) {struct m}: env :=
  match m with
  | nil => e
  | (s, d) :: m' => update d (e s) (exec_par m' e)
  end.

Fixpoint exec_seq (m: moves) (e: env) {struct m}: env :=
  match m with
  | nil => e
  | (s, d) :: m' => exec_seq m' (update d (e s) e)
  end.

Fixpoint exec_seq_rev (m: moves) (e: env) {struct m}: env :=
  match m with
  | nil => e
  | (s, d) :: m' => 
      let e' := exec_seq_rev m' e in
      update d (e' s) e'
  end.

(* Specification of the parallel move *)

Definition no_read (mu: moves) (d: reg) : Prop :=
  ~In d (srcs mu).

Inductive transition: moves -> moves -> moves
                   -> moves -> moves -> moves -> Prop :=
  | tr_nop: forall mu1 r mu2 sigma tau,
      transition (mu1 ++ (r, r) :: mu2) sigma tau
                 (mu1 ++ mu2) sigma tau
  | tr_start: forall mu1 s d mu2 tau,
      transition (mu1 ++ (s, d) :: mu2) nil tau
                 (mu1 ++ mu2) ((s, d) :: nil) tau
  | tr_push: forall mu1 d r mu2 s sigma tau,
      transition (mu1 ++ (d, r) :: mu2) ((s, d) :: sigma) tau
                 (mu1 ++ mu2) ((d, r) :: (s, d) :: sigma) tau
  | tr_loop: forall mu sigma s d tau,
      transition mu (sigma ++ (s, d) :: nil) tau
                 mu (sigma ++ (temp s, d) :: nil) ((s, temp s) :: tau)
  | tr_pop: forall mu s0 d0 s1 d1 sigma tau,
      no_read mu d1 -> d1 <> s0 ->
      transition mu ((s1, d1) :: sigma ++ (s0, d0) :: nil) tau
                 mu (sigma ++ (s0, d0) :: nil) ((s1, d1) :: tau)
  | tr_last: forall mu s d tau,
      no_read mu d ->
      transition mu ((s, d) :: nil) tau
                 mu nil ((s, d) :: tau).

Inductive transitions: moves -> moves -> moves
                    -> moves -> moves -> moves -> Prop :=
  | tr_refl:
      forall mu sigma tau,
      transitions mu sigma tau mu sigma tau
  | tr_one:
      forall mu1 sigma1 tau1 mu2 sigma2 tau2,
      transition mu1 sigma1 tau1 mu2 sigma2 tau2 ->
      transitions mu1 sigma1 tau1 mu2 sigma2 tau2
  | tr_trans:
      forall mu1 sigma1 tau1 mu2 sigma2 tau2 mu3 sigma3 tau3,
      transitions mu1 sigma1 tau1 mu2 sigma2 tau2 ->
      transitions mu2 sigma2 tau2 mu3 sigma3 tau3 ->
      transitions mu1 sigma1 tau1 mu3 sigma3 tau3.

(* Well-formedness properties *)

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

Definition state_wf (mu sigma tau: moves) : Prop :=
  is_mill (mu ++ sigma)
  /\ move_no_temp mu
  /\ temp_last sigma
  /\ is_path sigma.

(* Some properties of srcs and dests *)

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

(* Some properties of is_mill and dests_disjoint *)

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

(* Some properties of move_no_temp *)

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

(* Some properties of temp_last *)

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

(* Some properties of is_path *)

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

(* Populating a rewrite database. *)

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

(* Preservation of well-formedness *)

Lemma transition_preserves_wf:
  forall mu sigma tau mu' sigma' tau',
  transition mu sigma tau mu' sigma' tau' ->
  state_wf mu sigma tau -> state_wf mu' sigma' tau'.
Proof.
  induction 1; unfold state_wf; intros [A [B [C D]]];
  autorewrite with pmov in A; autorewrite with pmov.

  (* Nop *)
  split. tauto.
  split. red; intros. apply B. apply list_in_insert; auto.
  split; auto.

  (* Start *)
  split. tauto.
  split. red; intros. apply B. apply list_in_insert; auto.
  split. red. simpl. split. elim (B s d). auto. 
  apply in_or_app. right. apply in_eq. 
  red; simpl; tauto.
  constructor. exact I. constructor. 

  (* Push *)
  split. intuition.
  split. red; intros. apply B. apply list_in_insert; auto.
  split. elim (B d r). apply temp_last_push; auto. 
  apply in_or_app; right; apply in_eq.
  constructor. simpl. auto. auto.

  (* Loop *)
  split. tauto. 
  split. auto.
  split. eapply temp_last_change_last_source; eauto. 
  eapply is_path_change_last_source; eauto.

  (* Pop *)
  split. intuition.
  split. auto.
  split. eapply temp_last_pop; eauto.
  eapply is_path_pop; eauto.

  (* Last *)
  split. intuition. 
  split. auto.
  split. unfold temp_last. simpl. auto.
  constructor.
Qed.

Lemma transitions_preserve_wf:
  forall mu sigma tau mu' sigma' tau',
  transitions mu sigma tau mu' sigma' tau' ->
  state_wf mu sigma tau -> state_wf mu' sigma' tau'.
Proof.
  induction 1; intros; eauto.
  eapply transition_preserves_wf; eauto.
Qed.

(* Properties of exec_ *)

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

(* Semantics of triples (mu, sigma, tau) *)

Definition statemove (mu sigma tau: moves) (e: env) :=
  exec_par (mu ++ sigma) (exec_seq_rev tau e).

(* Equivalence over non-temp regs *)

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

(* Preservation of semantics by transformations. *)

Lemma transition_preserves_semantics:
  forall mu1 sigma1 tau1 mu2 sigma2 tau2 e,
  transition mu1 sigma1 tau1 mu2 sigma2 tau2 ->
  state_wf mu1 sigma1 tau1 ->
  env_equiv (statemove mu2 sigma2 tau2 e) (statemove mu1 sigma1 tau1 e).
Proof.
  induction 1; intros [A [B [C D]]].

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
  forall mu1 sigma1 tau1 mu2 sigma2 tau2 e,
  transitions mu1 sigma1 tau1 mu2 sigma2 tau2 ->
  state_wf mu1 sigma1 tau1 ->
  env_equiv (statemove mu2 sigma2 tau2 e) (statemove mu1 sigma1 tau1 e).
Proof.
  induction 1; intros. 
  apply env_equiv_refl. 
  eapply transition_preserves_semantics; eauto.
  apply env_equiv_trans with (statemove mu2 sigma2 tau2 e).
  apply IHtransitions2. eapply transitions_preserve_wf; eauto.
  apply IHtransitions1. auto.
Qed.

Lemma state_wf_start:
  forall mu,
  move_no_temp mu ->
  is_mill mu ->
  state_wf mu nil nil.
Proof.
  split. rewrite <- app_nil_end. auto. 
  split. auto.
  split. red. simpl. auto.
  constructor.
Qed.  

Theorem transitions_correctness:
  forall mu tau,
  move_no_temp mu ->
  is_mill mu ->
  transitions mu nil nil  nil nil tau ->
  forall e, env_equiv (exec_seq (List.rev tau) e) (exec_par mu e).
Proof.
  intros. 
  generalize (transitions_preserve_semantics _ _ _ _ _ _ e H1
              (state_wf_start _ H H0)).
  unfold statemove. simpl. rewrite <- app_nil_end. 
  rewrite exec_seq_exec_seq_rev. auto.
Qed.

(* Determinisation of the transition relation *)

Inductive dtransition: moves -> moves -> moves
                    -> moves -> moves -> moves -> Prop :=
  | dtr_nop: forall r mu tau,
      dtransition ((r, r) :: mu) nil tau
                   mu nil tau
  | dtr_start: forall s d mu tau,
      s <> d ->
      dtransition ((s, d) :: mu) nil tau
                   mu ((s, d) :: nil) tau
  | dtr_push: forall mu1 d r mu2 s sigma tau,
      no_read mu1 d ->
      dtransition (mu1 ++ (d, r) :: mu2) ((s, d) :: sigma) tau
                   (mu1 ++ mu2) ((d, r) :: (s, d) :: sigma) tau
  | dtr_loop_pop: forall mu s r0 d  sigma tau,
      no_read mu r0 ->
      dtransition mu ((s, r0) :: sigma ++ (r0, d) :: nil) tau
                   mu (sigma ++ (temp r0, d) :: nil) ((s, r0) :: (r0, temp r0) :: tau)
  | dtr_pop: forall mu s0 d0 s1 d1 sigma tau,
      no_read mu d1 -> d1 <> s0 ->
      dtransition mu ((s1, d1) :: sigma ++ (s0, d0) :: nil) tau
                   mu (sigma ++ (s0, d0) :: nil) ((s1, d1) :: tau)
  | dtr_last: forall mu s d tau,
      no_read mu d ->
      dtransition mu ((s, d) :: nil) tau
                   mu nil ((s, d) :: tau).

Inductive dtransitions: moves -> moves -> moves
                      -> moves -> moves -> moves -> Prop :=
  | dtr_refl:
      forall mu sigma tau,
      dtransitions mu sigma tau mu sigma tau
  | dtr_one:
      forall mu1 sigma1 tau1 mu2 sigma2 tau2,
      dtransition mu1 sigma1 tau1 mu2 sigma2 tau2 ->
      dtransitions mu1 sigma1 tau1 mu2 sigma2 tau2
  | dtr_trans:
      forall mu1 sigma1 tau1 mu2 sigma2 tau2 mu3 sigma3 tau3,
      dtransitions mu1 sigma1 tau1 mu2 sigma2 tau2 ->
      dtransitions mu2 sigma2 tau2 mu3 sigma3 tau3 ->
      dtransitions mu1 sigma1 tau1 mu3 sigma3 tau3.

Lemma transition_determ:
  forall mu1 sigma1 tau1 mu2 sigma2 tau2,
  dtransition mu1 sigma1 tau1 mu2 sigma2 tau2 ->
  state_wf mu1 sigma1 tau1 ->
  transitions mu1 sigma1 tau1 mu2 sigma2 tau2.
Proof.
  induction 1; intro.
  apply tr_one. exact (tr_nop nil r mu nil tau). 
  apply tr_one. exact (tr_start nil s d mu tau). 
  apply tr_one. apply tr_push. 
  eapply tr_trans.
    apply tr_one. 
    change ((s, r0) :: sigma ++ (r0, d) :: nil)
      with (((s, r0) :: sigma) ++ (r0, d) :: nil).
    apply tr_loop. 
    apply tr_one. simpl. apply tr_pop. auto. 
    destruct H0 as [A [B [C D]]]. 
    generalize C. 
    change ((s, r0) :: sigma ++ (r0, d) :: nil)
      with (((s, r0) :: sigma) ++ (r0, d) :: nil).
    unfold temp_last; rewrite List.rev_unit. intros [E F].
    elim (F s r0). unfold is_not_temp. auto. 
    rewrite <- List.In_rev. apply in_eq.
  apply tr_one. apply tr_pop. auto. auto. 
  apply tr_one. apply tr_last. auto. 
Qed.

Lemma transitions_determ:
  forall mu1 sigma1 tau1 mu2 sigma2 tau2,
  dtransitions mu1 sigma1 tau1 mu2 sigma2 tau2 ->
  state_wf mu1 sigma1 tau1 ->
  transitions mu1 sigma1 tau1 mu2 sigma2 tau2.
Proof.
  induction 1; intros.
  apply tr_refl.
  eapply transition_determ; eauto.
  eapply tr_trans.
    apply IHdtransitions1. auto.
    apply IHdtransitions2. eapply transitions_preserve_wf; eauto.
Qed.

Theorem dtransitions_correctness:
  forall mu tau,
  move_no_temp mu ->
  is_mill mu ->
  dtransitions mu nil nil  nil nil tau ->
  forall e, env_equiv (exec_seq (List.rev tau) e) (exec_par mu e).
Proof.
  intros. 
  eapply transitions_correctness; eauto.
  apply transitions_determ. auto. apply state_wf_start; auto. 
Qed.

(* Transition function *)

Function split_move (m: moves) (r: reg) {struct m} : option (moves * reg * moves) :=
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

Function is_last_source (r: reg) (m: moves) {struct m} : bool :=
  match m with
  | nil => false
  | (s, d) :: nil =>
      if reg_eq s r then true else false
  | (s, d) :: tl =>
      is_last_source r tl
  end.

Function replace_last_source (r: reg) (m: moves) {struct m} : moves :=
  match m with
  | nil => nil
  | (s, d) :: nil => (r, d) :: nil
  | s_d :: tl => s_d :: replace_last_source r tl
  end.

Inductive state : Set := State: moves -> moves -> moves -> state.

Definition final_state (st: state) : bool :=
  match st with
  | State nil nil _ => true
  | _ => false
  end.

Function parmove_step (st: state) : state :=
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

(* Correctness properties of these functions *)

Lemma split_move_charact:
  forall m r,
  match split_move m r with
  | Some (before, d, after) => m = before ++ (r, d) :: after /\ no_read before r
  | None => no_read m r
  end.
Proof.
  unfold no_read. intros m r. functional induction (split_move m r).
  red; simpl. tauto.
  rewrite _x. split. reflexivity. simpl;auto.
  rewrite e1 in IHo. simpl. intuition.
  rewrite e1 in IHo. destruct IHo. split. rewrite H. reflexivity.
  simpl. intuition.
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
  forall mu sigma tau mu' sigma' tau',
  final_state (State mu sigma tau) = false ->
  parmove_step (State mu sigma tau) = State mu' sigma' tau' ->
  dtransition mu sigma tau mu' sigma' tau'.
Proof.
  intros until tau'. intro NOTFINAL.
  unfold parmove_step. 
  case_eq mu; [intros MEQ | intros [ms md] mtl MEQ]. 
  case_eq sigma; [intros SEQ | intros [ss sd] stl SEQ]. 
  subst mu sigma. discriminate. 
  simpl. 
  case_eq stl; [intros STLEQ | intros xx1 xx2 STLEQ].
  intro R; inversion R; clear R; subst.
  apply dtr_last. red; simpl; auto.
  elim (@exists_last _ stl). 2:congruence. intros sigma1 [[ss1 sd1] SEQ2]. 
  rewrite <- STLEQ. clear STLEQ xx1 xx2. 
  generalize (is_last_source_charact sd ss1 sd1 sigma1). 
  rewrite SEQ2. destruct (is_last_source sd (sigma1 ++ (ss1, sd1) :: nil)).
  intro. subst ss1. intro R; inversion R; clear R; subst.
  rewrite replace_last_source_charact. apply dtr_loop_pop. 
  red; simpl; auto.
  intro. intro R; inversion R; clear R; subst.
  apply dtr_pop. red; simpl; auto. auto. 

  case_eq sigma; [intros SEQ | intros [ss sd] stl SEQ]. 
  destruct (reg_eq ms md); intro R; inversion R; clear R; subst.
  apply dtr_nop. 
  apply dtr_start. auto.

  generalize (split_move_charact ((ms, md) :: mtl) sd).
  case (split_move ((ms, md) :: mtl) sd); [intros [[before r] after] | idtac].
  intros [MEQ2 NOREAD]. intro R; inversion R; clear R; subst.
  rewrite MEQ2. apply dtr_push. auto.
  intro NOREAD.
  case_eq stl; [intros STLEQ | intros xx1 xx2 STLEQ].
  intro R; inversion R; clear R; subst.
  apply dtr_last. auto.
  elim (@exists_last _ stl). 2:congruence. intros sigma1 [[ss1 sd1] SEQ2]. 
  rewrite <- STLEQ. clear STLEQ xx1 xx2. 
  generalize (is_last_source_charact sd ss1 sd1 sigma1). 
  rewrite SEQ2. destruct (is_last_source sd (sigma1 ++ (ss1, sd1) :: nil)).
  intro. subst ss1. intro R; inversion R; clear R; subst.
  rewrite replace_last_source_charact. apply dtr_loop_pop. auto.
  intro. intro R; inversion R; clear R; subst.
  apply dtr_pop. auto. auto.
Qed.

(* Decreasing measure over states *)

Open Scope nat_scope.

Definition measure (st: state) : nat :=
  match st with
  | State mu sigma tau => 2 * List.length mu + List.length sigma
  end.

Lemma measure_decreasing_1:
  forall mu1 sigma1 tau1 mu2 sigma2 tau2,
  dtransition mu1 sigma1 tau1 mu2 sigma2 tau2 ->
  measure (State mu2 sigma2 tau2) < measure (State mu1 sigma1 tau1).
Proof.
  induction 1; repeat (simpl; rewrite List.app_length); simpl; omega.
Qed.

Lemma measure_decreasing_2:
  forall st,
  final_state st = false ->
  measure (parmove_step st) < measure st.
Proof.
  intros. destruct st as [mu sigma tau]. 
  case_eq (parmove_step (State mu sigma tau)). intros mu' sigma' tau' EQ.
  apply measure_decreasing_1. 
  apply parmove_step_compatible; auto.
Qed.

(* Compilation function for parallel moves *)

Function parmove_aux (st: state) {measure measure st} : moves :=
  if final_state st 
  then match st with State _ _ tau => tau end
  else parmove_aux (parmove_step st).
Proof.
  intros. apply measure_decreasing_2. auto.
Qed.

Lemma parmove_aux_transitions:
  forall mu sigma tau,
  dtransitions mu sigma tau nil nil (parmove_aux (State mu sigma tau)).
Proof.
  assert (forall st,
          match st with State mu sigma tau =>
             dtransitions mu sigma tau nil nil (parmove_aux st)
          end).
    intro st. functional induction (parmove_aux st).
    destruct _x; destruct _x0; simpl in e; discriminate || apply dtr_refl.
    case_eq (parmove_step st). intros mu' sigma' tau' PSTEP.
    destruct st as [mu sigma tau]. 
    eapply dtr_trans. apply dtr_one. apply parmove_step_compatible; eauto. 
    rewrite PSTEP in IHm. auto.

  intros. apply (H (State mu sigma tau)). 
Qed.

Definition parmove (mu: moves) : moves :=
  List.rev (parmove_aux (State mu nil nil)).

Theorem parmove_correctness:
  forall mu,
  move_no_temp mu -> is_mill mu ->
  forall e,
  env_equiv (exec_seq (parmove mu) e) (exec_par mu e).
Proof.
  intros. unfold parmove. apply dtransitions_correctness; auto.
  apply parmove_aux_transitions. 
Qed.

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

(* Additional properties on the generated sequence of moves. *)

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

Definition wf_state (mu sigma tau: moves) : Prop :=
  wf_moves mu /\ wf_moves sigma /\ wf_moves tau.

Lemma dtransition_preserves_wf_state:
  forall mu1 sigma1 tau1 mu2 sigma2 tau2,
  dtransition mu1 sigma1 tau1 mu2 sigma2 tau2 ->
  wf_state mu1 sigma1 tau1 -> wf_state mu2 sigma2 tau2.
Proof.
  induction 1; intros [A [B C]]; unfold wf_state;
  autorewrite with pmov in A; autorewrite with pmov in B; 
  autorewrite with pmov in C; autorewrite with pmov.

  tauto.

  tauto.

  tauto. 

  intuition. apply wf_move_temp_left; auto. 
  eapply wf_move_temp_right; eauto.

  intuition. 

  intuition.
Qed.

Lemma dtransitions_preserve_wf_state:
  forall mu1 sigma1 tau1 mu2 sigma2 tau2,
  dtransitions mu1 sigma1 tau1 mu2 sigma2 tau2 ->
  wf_state mu1 sigma1 tau1 -> wf_state mu2 sigma2 tau2.
Proof.
  induction 1; intros; eauto. 
  eapply dtransition_preserves_wf_state; eauto.
Qed.  

End PROPERTIES.

Lemma parmove_wf_moves:
  forall mu, wf_moves mu (parmove mu).
Proof.
  intros. 
  assert (wf_state mu mu nil nil).
    split. red; intros. apply wf_move_same. auto.
    split. red; simpl; tauto. red; simpl; tauto.
  generalize (dtransitions_preserve_wf_state mu
              _ _ _ _ _ _
              (parmove_aux_transitions mu nil nil) H).
  intros [A [B C]].
  unfold parmove. red; intros. apply C. 
  rewrite List.In_rev. auto.
Qed.

Lemma parmove2_wf_moves:
  forall sl dl, wf_moves (List.combine sl dl) (parmove2 sl dl).
Proof.
  intros. unfold parmove2. apply parmove_wf_moves. 
Qed.

End PARMOV.
