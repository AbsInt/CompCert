(** Correctness proof for the branch tunneling optimization. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import Tunneling.

(** * Properties of branch target computation *)

Lemma is_goto_block_correct:
  forall b s,
  is_goto_block b = Some s -> b = Some (Bgoto s).
Proof.
  unfold is_goto_block; intros.
  destruct b. destruct b; discriminate || congruence. 
  discriminate.
Qed. 

Lemma branch_target_rec_1:
  forall f pc n,
  branch_target_rec f pc n = Some pc
  \/ branch_target_rec f pc n = None
  \/ exists pc', f.(fn_code)!pc = Some(Bgoto pc').
Proof.
  intros. destruct n; simpl.
  right; left; auto.
  caseEq (is_goto_block f.(fn_code)!pc); intros.
  right; right. exists n0. apply is_goto_block_correct; auto.
  left; auto.
Qed.

Lemma branch_target_rec_2:
  forall f n pc1 pc2 pc3,
  f.(fn_code)!pc1 = Some (Bgoto pc2) ->
  branch_target_rec f pc1 n = Some pc3 ->
  branch_target_rec f pc2 n = Some pc3.
Proof.
  induction n. 
  simpl. intros; discriminate.
  intros pc1 pc2 pc3 ATpc1 H. simpl in H. 
  unfold is_goto_block in H; rewrite ATpc1 in H.
  simpl. caseEq (is_goto_block f.(fn_code)!pc2); intros.
  apply IHn with pc2. apply is_goto_block_correct; auto. auto.
  destruct n; simpl in H. discriminate. rewrite H0 in H. auto.
Qed.

(** The following lemma captures the property of [branch_target]
  on which the proof of semantic preservation relies. *)

Lemma branch_target_characterization:
  forall f pc,
  branch_target f pc = pc \/
  (exists pc', f.(fn_code)!pc = Some(Bgoto pc')
            /\ branch_target f pc' = branch_target f pc).
Proof.
  intros. unfold branch_target. 
  generalize (branch_target_rec_1 f pc 10%nat). 
  intros [A|[A|[pc' AT]]].
  rewrite A. left; auto.
  rewrite A. left; auto.
  caseEq (branch_target_rec f pc 10%nat). intros pcx BT.
  right. exists pc'. split. auto. 
  rewrite (branch_target_rec_2 _ _ _ _ _ AT BT). auto.
  intro. left; auto.
Qed.

(** * Preservation of semantics *)

Section PRESERVATION.

Variable p: program.
Let tp := tunnel_program p.
Let ge := Genv.globalenv p.
Let tge := Genv.globalenv tp.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (tunnel_fundef f).
Proof (@Genv.find_funct_transf _ _ tunnel_fundef p).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (tunnel_fundef f).
Proof (@Genv.find_funct_ptr_transf _ _ tunnel_fundef p).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (@Genv.find_symbol_transf _ _ tunnel_fundef p).

Lemma sig_preserved:
  forall f, funsig (tunnel_fundef f) = funsig f.
Proof.
  destruct f; reflexivity.
Qed.

(** These are inversion lemmas, characterizing what happens in the LTL
  semantics when executing [Bgoto] instructions or basic blocks. *)

Lemma exec_instrs_Bgoto_inv:
  forall sp b1 ls1 m1 t b2 ls2 m2,
  exec_instrs ge sp b1 ls1 m1 t b2 ls2 m2 ->
  forall s1,
  b1 = Bgoto s1 -> t = E0 /\ b2 = b1 /\ ls2 = ls1 /\ m2 = m1.
Proof.
  induction 1. 
  intros. tauto.
  intros. subst b1. inversion H. 
  intros. generalize (IHexec_instrs1 s1 H2). intros [A [B [C D]]].
  subst t1 b2 rs2 m2. 
  generalize (IHexec_instrs2 s1 H2). intros [A [B [C D]]].
  subst t2 b3 rs3 m3. intuition. traceEq. 
Qed.

Lemma exec_block_Bgoto_inv:
  forall sp s ls1 m1 t out ls2 m2,  
  exec_block ge sp (Bgoto s) ls1 m1 t out ls2 m2 ->
  t = E0 /\ out = Cont s /\ ls2 = ls1 /\ m2 = m1.
Proof.
  intros. inversion H;
  generalize (exec_instrs_Bgoto_inv _ _ _ _ _ _ _ _ H0 s (refl_equal _));
  intros [A [B [C D]]];
  try discriminate.
  intuition congruence.
Qed.

Lemma exec_blocks_Bgoto_inv:
  forall c sp pc1 ls1 m1 t out ls2 m2 s,
  exec_blocks ge c sp pc1 ls1 m1 t out ls2 m2 ->
  c!pc1 = Some (Bgoto s) ->
  (t = E0 /\ out = Cont pc1 /\ ls2 = ls1 /\ m2 = m1)
  \/ exec_blocks ge c sp s ls1 m1 t out ls2 m2.
Proof.
  induction 1; intros.
  left; tauto.
  assert (b = Bgoto s). congruence. subst b. 
  generalize (exec_block_Bgoto_inv _ _ _ _ _ _ _ _ H0). 
  intros [A [B [C D]]]. subst t out rs' m'.
  right. apply exec_blocks_refl.
  elim (IHexec_blocks1 H2).
  intros [A [B [C D]]]. 
  assert (pc2 = pc1). congruence. subst t1 rs2 m2 pc2.
  replace t with t2. apply IHexec_blocks2; auto. traceEq.
  intro. right. 
  eapply exec_blocks_trans; eauto. 
Qed.

(** The following [exec_*_prop] predicates state the correctness
  of the tunneling transformation: for each LTL execution
  in the original code (of an instruction, a sequence of instructions,
  a basic block, a sequence of basic blocks, etc), there exists
  a similar LTL execution in the tunneled code.  

  Note that only the control-flow is changed: the values of locations
  and the memory states are identical in the original and transformed 
  codes. *)

Definition tunnel_outcome (f: function) (out: outcome) :=
  match out with
  | Cont pc => Cont (branch_target f pc)
  | Return => Return
  end.

Definition exec_instr_prop
  (sp: val) (b1: block) (ls1: locset) (m1: mem) (t: trace)
            (b2: block) (ls2: locset) (m2: mem) : Prop :=
  forall f,
  exec_instr tge sp (tunnel_block f b1) ls1 m1
                  t (tunnel_block f b2) ls2 m2.

Definition exec_instrs_prop
  (sp: val) (b1: block) (ls1: locset) (m1: mem) (t: trace)
            (b2: block) (ls2: locset) (m2: mem) : Prop :=
  forall f,
  exec_instrs tge sp (tunnel_block f b1) ls1 m1
                   t (tunnel_block f b2) ls2 m2.

Definition exec_block_prop
  (sp: val) (b1: block) (ls1: locset) (m1: mem) (t: trace)
            (out: outcome) (ls2: locset) (m2: mem) : Prop :=
  forall f,
  exec_block tge sp (tunnel_block f b1) ls1 m1
                  t (tunnel_outcome f out) ls2 m2.

Definition tunneled_code (f: function) :=
  PTree.map (fun pc b => tunnel_block f b) (fn_code f).

Definition exec_blocks_prop
     (c: code) (sp: val)
     (pc: node) (ls1: locset) (m1: mem) (t: trace)
     (out: outcome) (ls2: locset) (m2: mem) : Prop :=
  forall f,
  f.(fn_code) = c ->
  exec_blocks tge (tunneled_code f) sp
              (branch_target f pc) ls1 m1
            t (tunnel_outcome f out) ls2 m2.

Definition exec_function_prop
    (f: fundef) (ls1: locset) (m1: mem) (t: trace)
                (ls2: locset) (m2: mem) : Prop :=
  exec_function tge (tunnel_fundef f) ls1 m1 t ls2 m2.

Scheme exec_instr_ind5 := Minimality for LTL.exec_instr Sort Prop
  with exec_instrs_ind5 := Minimality for LTL.exec_instrs Sort Prop
  with exec_block_ind5 := Minimality for LTL.exec_block Sort Prop
  with exec_blocks_ind5 := Minimality for LTL.exec_blocks Sort Prop
  with exec_function_ind5 := Minimality for LTL.exec_function Sort Prop.

(** The proof of semantic preservation is a structural induction
  over the LTL evaluation derivation of the original program,
  using the [exec_*_prop] predicates above as induction hypotheses. *)

Lemma tunnel_function_correct:
  forall f ls1 m1 t ls2 m2,
  exec_function ge f ls1 m1 t ls2 m2 ->
  exec_function_prop f ls1 m1 t ls2 m2.
Proof.
  apply (exec_function_ind5 ge
           exec_instr_prop
           exec_instrs_prop
           exec_block_prop
           exec_blocks_prop
           exec_function_prop);
  intros; red; intros; simpl.
  (* getstack *)
  constructor.
  (* setstack *)
  constructor.
  (* op *)
  constructor. rewrite <- H. apply eval_operation_preserved.
  exact symbols_preserved.
  (* load *)
  apply exec_Bload with a. rewrite <- H. 
  apply eval_addressing_preserved. exact symbols_preserved.
  auto.
  (* store *)
  apply exec_Bstore with a. rewrite <- H.
  apply eval_addressing_preserved. exact symbols_preserved.
  auto.
  (* call *)
  apply exec_Bcall with (tunnel_fundef f). 
  generalize H; unfold find_function; destruct ros.
  intro. apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  intro. apply function_ptr_translated; auto. congruence.
  generalize (sig_preserved f). congruence. 
  apply H2. 
  (* alloc *)
  eapply exec_Balloc; eauto. 
  (* instr_refl *)
  apply exec_refl.
  (* instr_one *)
  apply exec_one. apply H0.
  (* instr_trans *)
  apply exec_trans with t1 (tunnel_block f b2) rs2 m2 t2; auto.
  (* goto *)
  apply exec_Bgoto. red in H0. simpl in H0. apply H0. 
  (* cond, true *)
  eapply exec_Bcond_true. red in H0. simpl in H0. apply H0.  auto.
  (* cond, false *)
  eapply exec_Bcond_false. red in H0. simpl in H0. apply H0. auto.
  (* return *)
  apply exec_Breturn. red in H0. simpl in H0. apply H0. 
  (* block_refl *)
  apply exec_blocks_refl.
  (* block_one *)
  red in H1. 
  elim (branch_target_characterization f pc).
  intro. rewrite H3. apply exec_blocks_one with (tunnel_block f b).
  unfold tunneled_code. rewrite PTree.gmap. rewrite H2; rewrite H.
  reflexivity. apply H1.
  intros [pc' [ATpc BTS]]. 
  assert (b = Bgoto pc'). congruence. subst b.
  generalize (exec_block_Bgoto_inv _ _ _ _ _ _ _ _ H0).
  intros [A [B [C D]]]. subst t out rs' m'.
  simpl. rewrite BTS. apply exec_blocks_refl.
  (* blocks_trans *)
  apply exec_blocks_trans with t1 (branch_target f pc2) rs2 m2 t2.
  exact (H0 f H4). exact (H2 f H4). auto.
  (* internal function *)
  econstructor. eexact H. 
  change (fn_code (tunnel_function f)) with (tunneled_code f).
  simpl.
  elim (branch_target_characterization f (fn_entrypoint f)).
  intro BT. rewrite <- BT. exact (H1 f (refl_equal _)).
  intros [pc [ATpc BT]].
  apply exec_blocks_trans with 
     E0 (branch_target f (fn_entrypoint f)) (call_regs rs) m1 t.
  eapply exec_blocks_one. 
  unfold tunneled_code. rewrite PTree.gmap. rewrite ATpc.
  simpl. reflexivity. 
  apply exec_Bgoto. rewrite BT. apply exec_refl.
  exact (H1 f (refl_equal _)). traceEq.
  (* external function *)
  econstructor; eauto. 
Qed.

End PRESERVATION.

Theorem transf_program_correct:
  forall (p: program) (t: trace) (r: val),
  exec_program p t r ->
  exec_program (tunnel_program p) t r.
Proof.
  intros p t r [b [f [ls [m [FIND1 [FIND2 [SIG [EX RES]]]]]]]].
  red. exists b; exists (tunnel_fundef f); exists ls; exists m.
  split. change (prog_main (tunnel_program p)) with (prog_main p).
  rewrite <- FIND1. apply symbols_preserved.
  split. apply function_ptr_translated. assumption.
  split. generalize (sig_preserved f). congruence.
  split. apply tunnel_function_correct. 
  unfold tunnel_program. rewrite Genv.init_mem_transf. auto.
  rewrite sig_preserved. exact RES.
Qed.
