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

(** Correctness proof for PPC generation: main proof. *)

Require Import Coqlib.
Require Import Maps.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Import Mach.
Require Import Machconcr.
Require Import Machtyping.
Require Import Asm.
Require Import Asmgen.
Require Import Asmgenretaddr.
Require Import Asmgenproof1.

Section PRESERVATION.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: transf_program prog = Errors.OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_var_info_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma functions_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = Errors.OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transf_fundef _ TRANSF).

Lemma functions_transl:
  forall f b,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  Genv.find_funct_ptr tge b = Some (Internal (transl_function f)).
Proof.
  intros. 
  destruct (functions_translated _ _ H) as [tf [A B]].
  rewrite A. generalize B. unfold transf_fundef, transf_partial_fundef, transf_function.
  case (zlt Int.max_unsigned (list_length_z (transl_function f))); simpl; intro.
  congruence. intro. inv B0. auto.
Qed.

Lemma functions_transl_no_overflow:
  forall b f,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  list_length_z (transl_function f) <= Int.max_unsigned.
Proof.
  intros. 
  destruct (functions_translated _ _ H) as [tf [A B]].
  generalize B. unfold transf_fundef, transf_partial_fundef, transf_function.
  case (zlt Int.max_unsigned (list_length_z (transl_function f))); simpl; intro.
  congruence. intro; omega.
Qed.

(** * Properties of control flow *)

Lemma find_instr_in:
  forall c pos i,
  find_instr pos c = Some i -> In i c.
Proof.
  induction c; simpl. intros; discriminate.
  intros until i. case (zeq pos 0); intros.
  left; congruence. right; eauto.
Qed.

Lemma find_instr_tail:
  forall c1 i c2 pos,
  code_tail pos c1 (i :: c2) ->
  find_instr pos c1 = Some i.
Proof.
  induction c1; simpl; intros.
  inv H.
  destruct (zeq pos 0). subst pos.
  inv H. auto. generalize (code_tail_pos _ _ _ H4). intro. omegaContradiction.
  inv H. congruence. replace (pos0 + 1 - 1) with pos0 by omega.
  eauto.
Qed.

(*
Remark code_size_pos:
  forall fn, code_size fn >= 0.
Proof.
  induction fn; simpl; omega.
Qed.
*)

Remark code_tail_bounds:
  forall fn ofs i c,
  code_tail ofs fn (i :: c) -> 0 <= ofs < list_length_z fn.
Proof.
  assert (forall ofs fn c, code_tail ofs fn c ->
          forall i c', c = i :: c' -> 0 <= ofs < list_length_z fn).
  induction 1; intros; simpl. 
  rewrite H. rewrite list_length_z_cons. generalize (list_length_z_pos c'). omega.
  rewrite list_length_z_cons. generalize (IHcode_tail _ _ H0). omega.
  eauto.
Qed.

Lemma code_tail_next:
  forall fn ofs i c,
  code_tail ofs fn (i :: c) ->
  code_tail (ofs + 1) fn c.
Proof.
  assert (forall ofs fn c, code_tail ofs fn c ->
          forall i c', c = i :: c' -> code_tail (ofs + 1) fn c').
  induction 1; intros.
  subst c. constructor. constructor.
  constructor. eauto.
  eauto.
Qed.

Lemma code_tail_next_int:
  forall fn ofs i c,
  list_length_z fn <= Int.max_unsigned ->
  code_tail (Int.unsigned ofs) fn (i :: c) ->
  code_tail (Int.unsigned (Int.add ofs Int.one)) fn c.
Proof.
  intros. rewrite Int.add_unsigned.
  change (Int.unsigned Int.one) with 1.
  rewrite Int.unsigned_repr. apply code_tail_next with i; auto.
  generalize (code_tail_bounds _ _ _ _ H0). omega. 
Qed.

(** [transl_code_at_pc pc fn c] holds if the code pointer [pc] points
  within the PPC code generated by translating Mach function [fn],
  and [c] is the tail of the generated code at the position corresponding
  to the code pointer [pc]. *)

Inductive transl_code_at_pc: val -> block -> Mach.function -> Mach.code -> Prop :=
  transl_code_at_pc_intro:
    forall b ofs f c,
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    code_tail (Int.unsigned ofs) (transl_function f) (transl_code f c) ->
    transl_code_at_pc (Vptr b ofs) b f c.

(** The following lemmas show that straight-line executions
  (predicate [exec_straight]) correspond to correct PPC executions
  (predicate [exec_steps]) under adequate [transl_code_at_pc] hypotheses. *)

Lemma exec_straight_steps_1:
  forall fn c rs m c' rs' m',
  exec_straight tge fn c rs m c' rs' m' ->
  list_length_z fn <= Int.max_unsigned ->
  forall b ofs,
  rs#PC = Vptr b ofs ->
  Genv.find_funct_ptr tge b = Some (Internal fn) ->
  code_tail (Int.unsigned ofs) fn c ->
  plus step tge (State rs m) E0 (State rs' m').
Proof.
  induction 1; intros.
  apply plus_one.
  econstructor; eauto. 
  eapply find_instr_tail. eauto.
  eapply plus_left'.
  econstructor; eauto. 
  eapply find_instr_tail. eauto.
  apply IHexec_straight with b (Int.add ofs Int.one). 
  auto. rewrite H0. rewrite H3. reflexivity.
  auto. 
  apply code_tail_next_int with i; auto.
  traceEq.
Qed.
    
Lemma exec_straight_steps_2:
  forall fn c rs m c' rs' m',
  exec_straight tge fn c rs m c' rs' m' ->
  list_length_z fn <= Int.max_unsigned ->
  forall b ofs,
  rs#PC = Vptr b ofs ->
  Genv.find_funct_ptr tge b = Some (Internal fn) ->
  code_tail (Int.unsigned ofs) fn c ->
  exists ofs',
     rs'#PC = Vptr b ofs'
  /\ code_tail (Int.unsigned ofs') fn c'.
Proof.
  induction 1; intros.
  exists (Int.add ofs Int.one). split.
  rewrite H0. rewrite H2. auto.
  apply code_tail_next_int with i1; auto.
  apply IHexec_straight with (Int.add ofs Int.one).
  auto. rewrite H0. rewrite H3. reflexivity. auto. 
  apply code_tail_next_int with i; auto.
Qed.

Lemma exec_straight_exec:
  forall fb f c c' rs m rs' m',
  transl_code_at_pc (rs PC) fb f c ->
  exec_straight tge (transl_function f)
                (transl_code f c) rs m c' rs' m' ->
  plus step tge (State rs m) E0 (State rs' m').
Proof.
  intros. inversion H. subst.
  eapply exec_straight_steps_1; eauto.
  eapply functions_transl_no_overflow; eauto. 
  eapply functions_transl; eauto.
Qed.

Lemma exec_straight_at:
  forall fb f c c' rs m rs' m',
  transl_code_at_pc (rs PC) fb f c ->
  exec_straight tge (transl_function f)
                (transl_code f c) rs m (transl_code f c') rs' m' ->
  transl_code_at_pc (rs' PC) fb f c'.
Proof.
  intros. inversion H. subst. 
  generalize (functions_transl_no_overflow _ _ H2). intro.
  generalize (functions_transl _ _ H2). intro.
  generalize (exec_straight_steps_2 _ _ _ _ _ _ _
                H0 H4 _ _ (sym_equal H1) H5 H3).
  intros [ofs' [PC' CT']].
  rewrite PC'. constructor; auto.
Qed.

(** Correctness of the return addresses predicted by
    [PPCgen.return_address_offset]. *)

Remark code_tail_no_bigger:
  forall pos c1 c2, code_tail pos c1 c2 -> (length c2 <= length c1)%nat.
Proof.
  induction 1; simpl; omega.
Qed.

Remark code_tail_unique:
  forall fn c pos pos',
  code_tail pos fn c -> code_tail pos' fn c -> pos = pos'.
Proof.
  induction fn; intros until pos'; intros ITA CT; inv ITA; inv CT; auto.
  generalize (code_tail_no_bigger _ _ _ H3); simpl; intro; omega.
  generalize (code_tail_no_bigger _ _ _ H3); simpl; intro; omega.
  f_equal. eauto.
Qed.

Lemma return_address_offset_correct:
  forall b ofs fb f c ofs',
  transl_code_at_pc (Vptr b ofs) fb f c ->
  return_address_offset f c ofs' ->
  ofs' = ofs.
Proof.
  intros. inv H0. inv H. 
  generalize (code_tail_unique _ _ _ _ H1 H7). intro. rewrite H. 
  apply Int.repr_unsigned.
Qed.

(** The [find_label] function returns the code tail starting at the
  given label.  A connection with [code_tail] is then established. *)

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some c' else find_label lbl c'
  end.

Lemma label_pos_code_tail:
  forall lbl c pos c',
  find_label lbl c = Some c' ->
  exists pos',
  label_pos lbl pos c = Some pos' 
  /\ code_tail (pos' - pos) c c'
  /\ pos < pos' <= pos + list_length_z c.
Proof.
  induction c. 
  simpl; intros. discriminate.
  simpl; intros until c'.
  case (is_label lbl a).
  intro EQ; injection EQ; intro; subst c'.
  exists (pos + 1). split. auto. split.
  replace (pos + 1 - pos) with (0 + 1) by omega. constructor. constructor. 
  rewrite list_length_z_cons. generalize (list_length_z_pos c). omega. 
  intros. generalize (IHc (pos + 1) c' H). intros [pos' [A [B C]]].
  exists pos'. split. auto. split.
  replace (pos' - pos) with ((pos' - (pos + 1)) + 1) by omega.
  constructor. auto. 
  rewrite list_length_z_cons. omega.
Qed.

(** The following lemmas show that the translation from Mach to PPC
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ PPC instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- PPC instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that PPC constructor
  functions do not introduce new labels.
*)

Section TRANSL_LABEL.

Variable lbl: label.

Remark loadimm_label:
  forall r n k, find_label lbl (loadimm r n k) = find_label lbl k.
Proof.
  intros. unfold loadimm. 
  case (Int.eq (high_s n) Int.zero). reflexivity. 
  case (Int.eq (low_s n) Int.zero). reflexivity.
  reflexivity.
Qed.
Hint Rewrite loadimm_label: labels.

Remark addimm_label:
  forall r1 r2 n k, find_label lbl (addimm r1 r2 n k) = find_label lbl k.
Proof.
  intros; unfold addimm. 
  case (Int.eq (high_s n) Int.zero). reflexivity.
  case (Int.eq (low_s n) Int.zero). reflexivity. reflexivity.
Qed.
Hint Rewrite addimm_label: labels.

Remark andimm_label:
  forall r1 r2 n k, find_label lbl (andimm r1 r2 n k) = find_label lbl k.
Proof.
  intros; unfold andimm. 
  case (Int.eq (high_u n) Int.zero). reflexivity.
  case (Int.eq (low_u n) Int.zero). reflexivity.
  autorewrite with labels. reflexivity.
Qed.
Hint Rewrite andimm_label: labels.

Remark orimm_label:
  forall r1 r2 n k, find_label lbl (orimm r1 r2 n k) = find_label lbl k.
Proof.
  intros; unfold orimm. 
  case (Int.eq (high_u n) Int.zero). reflexivity.
  case (Int.eq (low_u n) Int.zero). reflexivity. reflexivity.
Qed.
Hint Rewrite orimm_label: labels.

Remark xorimm_label:
  forall r1 r2 n k, find_label lbl (xorimm r1 r2 n k) = find_label lbl k.
Proof.
  intros; unfold xorimm. 
  case (Int.eq (high_u n) Int.zero). reflexivity.
  case (Int.eq (low_u n) Int.zero). reflexivity. reflexivity.
Qed.
Hint Rewrite xorimm_label: labels.

Remark loadind_label:
  forall base ofs ty dst k, find_label lbl (loadind base ofs ty dst k) = find_label lbl k.
Proof.
  intros; unfold loadind. 
  destruct (Int.eq (high_s ofs) Int.zero); destruct ty; autorewrite with labels; auto.
Qed.
Hint Rewrite loadind_label: labels.

Remark storeind_label:
  forall base ofs ty src k, find_label lbl (storeind base src ofs ty k) = find_label lbl k.
Proof.
  intros; unfold storeind.
  destruct (Int.eq (high_s ofs) Int.zero); destruct ty; autorewrite with labels; auto.
Qed.
Hint Rewrite storeind_label: labels.

Remark floatcomp_label:
  forall cmp r1 r2 k, find_label lbl (floatcomp cmp r1 r2 k) = find_label lbl k.
Proof.
  intros; unfold floatcomp. destruct cmp; reflexivity.
Qed.

Remark transl_cond_label:
  forall cond args k, find_label lbl (transl_cond cond args k) = find_label lbl k.
Proof.
  intros; unfold transl_cond.
  destruct cond; (destruct args; 
  [try reflexivity | destruct args;
  [try reflexivity | destruct args; try reflexivity]]).
  case (Int.eq (high_s i) Int.zero). reflexivity. 
  autorewrite with labels; reflexivity.
  case (Int.eq (high_u i) Int.zero). reflexivity. 
  autorewrite with labels; reflexivity.
  apply floatcomp_label. apply floatcomp_label.
  apply andimm_label. apply andimm_label.
Qed.
Hint Rewrite transl_cond_label: labels.

Remark transl_op_cmp_label:
  forall c args r k,
  find_label lbl
    (match classify_condition c args with
     | condition_ge0 _ a _ =>
        Prlwinm (ireg_of r) (ireg_of a) Int.one Int.one
        :: Pxori (ireg_of r) (ireg_of r) (Cint Int.one) :: k
     | condition_lt0 _ a _ =>
        Prlwinm (ireg_of r) (ireg_of a) Int.one Int.one :: k
     | condition_default _ _ =>
        transl_cond c args
          (Pmfcrbit (ireg_of r) (fst (crbit_for_cond c))
           :: (if snd (crbit_for_cond c)
               then k
               else Pxori (ireg_of r) (ireg_of r) (Cint Int.one) :: k))
    end) = find_label lbl k.
Proof.
  intros. destruct (classify_condition c args); auto. 
  autorewrite with labels. 
  case (snd (crbit_for_cond c)); auto.
Qed.
Hint Rewrite transl_op_cmp_label: labels.

Remark transl_op_label:
  forall op args r k, find_label lbl (transl_op op args r k) = find_label lbl k.
Proof.
  intros; unfold transl_op;
  destruct op; destruct args; try (destruct args); try (destruct args); try (destruct args);
  try reflexivity; autorewrite with labels; try reflexivity.
  case (mreg_type m); reflexivity.
  case (Int.eq (high_s i) Int.zero); autorewrite with labels; reflexivity.
  case (Int.eq (high_s i) Int.zero); autorewrite with labels; reflexivity.
Qed.
Hint Rewrite transl_op_label: labels.

Remark transl_load_store_label:
  forall (mk1: constant -> ireg -> instruction) (mk2: ireg -> ireg -> instruction)
         addr args temp k,
  (forall c r, is_label lbl (mk1 c r) = false) ->
  (forall r1 r2, is_label lbl (mk2 r1 r2) = false) ->
  find_label lbl (transl_load_store mk1 mk2 addr args temp k) = find_label lbl k.
Proof.
  intros; unfold transl_load_store.
  destruct addr; destruct args; try (destruct args); try (destruct args);
  try reflexivity.
  destruct (Int.eq (high_s i) Int.zero); simpl; rewrite H; auto.
  simpl; rewrite H0; auto.
  destruct (symbol_is_small_data i i0); simpl; rewrite H; auto.
  simpl; rewrite H; auto.
  destruct (Int.eq (high_s i) Int.zero); simpl; rewrite H; auto.
Qed.
Hint Rewrite transl_load_store_label: labels.

Lemma transl_instr_label:
  forall f i k,
  find_label lbl (transl_instr f i k) = 
    if Mach.is_label lbl i then Some k else find_label lbl k.
Proof.
  intros. generalize (Mach.is_label_correct lbl i). 
  case (Mach.is_label lbl i); intro.
  subst i. simpl. rewrite peq_true. auto.
  destruct i; simpl; autorewrite with labels; try reflexivity.
  destruct m; rewrite transl_load_store_label; intros; reflexivity. 
  destruct m; rewrite transl_load_store_label; intros; reflexivity. 
  destruct s0; reflexivity.
  destruct s0; reflexivity.
  rewrite peq_false. auto. congruence.
  case (snd (crbit_for_cond c)); reflexivity.
Qed.

Lemma transl_code_label:
  forall f c,
  find_label lbl (transl_code f c) = 
    option_map (transl_code f) (Mach.find_label lbl c).
Proof.
  induction c; simpl; intros.
  auto. rewrite transl_instr_label.
  case (Mach.is_label lbl a). reflexivity.
  auto.
Qed.

Lemma transl_find_label:
  forall f,
  find_label lbl (transl_function f) = 
    option_map (transl_code f) (Mach.find_label lbl f.(fn_code)).
Proof.
  intros. unfold transl_function. simpl. apply transl_code_label.
Qed.

End TRANSL_LABEL.

(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated PPC code. *)

Lemma find_label_goto_label:
  forall f lbl rs m c' b ofs,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  rs PC = Vptr b ofs ->
  Mach.find_label lbl f.(fn_code) = Some c' ->
  exists rs',
    goto_label (transl_function f) lbl rs m = OK rs' m  
  /\ transl_code_at_pc (rs' PC) b f c'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. 
  generalize (transl_find_label lbl f).
  rewrite H1; simpl. intro.
  generalize (label_pos_code_tail lbl (transl_function f) 0 
                 (transl_code f c') H2).
  intros [pos' [A [B C]]].
  exists (rs#PC <- (Vptr b (Int.repr pos'))).
  split. unfold goto_label. rewrite A. rewrite H0. auto.
  split. rewrite Pregmap.gss. constructor; auto. 
  rewrite Int.unsigned_repr. replace (pos' - 0) with pos' in B.
  auto. omega. 
  generalize (functions_transl_no_overflow _ _ H). 
  omega.
  intros. apply Pregmap.gso; auto.
Qed.

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using simulation diagrams
  of the following form.
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant is the [match_states] predicate below, which includes:
- The PPC code pointed by the PC register is the translation of
  the current Mach code sequence.
- Mach register values and PPC register values agree.
*)

Inductive match_stack: list Machconcr.stackframe -> Prop :=
  | match_stack_nil:
      match_stack nil
  | match_stack_cons: forall fb sp ra c s f,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      wt_function f ->
      incl c f.(fn_code) ->
      transl_code_at_pc ra fb f c ->
      sp <> Vundef ->
      ra <> Vundef ->
      match_stack s ->
      match_stack (Stackframe fb sp ra c :: s).

Inductive match_states: Machconcr.state -> Asm.state -> Prop :=
  | match_states_intro:
      forall s fb sp c ms m rs m' f
        (STACKS: match_stack s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (WTF: wt_function f)
        (INCL: incl c f.(fn_code))
        (AT: transl_code_at_pc (rs PC) fb f c)
        (AG: agree ms sp rs)
        (MEXT: Mem.extends m m'),
      match_states (Machconcr.State s fb sp c ms m)
                   (Asm.State rs m')
  | match_states_call:
      forall s fb ms m rs m'
        (STACKS: match_stack s)
        (AG: agree ms (parent_sp s) rs)
        (MEXT: Mem.extends m m')
        (ATPC: rs PC = Vptr fb Int.zero)
        (ATLR: rs LR = parent_ra s),
      match_states (Machconcr.Callstate s fb ms m)
                   (Asm.State rs m')
  | match_states_return:
      forall s ms m rs m'
        (STACKS: match_stack s)
        (AG: agree ms (parent_sp s) rs)
        (MEXT: Mem.extends m m')
        (ATPC: rs PC = parent_ra s),
      match_states (Machconcr.Returnstate s ms m)
                   (Asm.State rs m').

Lemma exec_straight_steps:
  forall s fb sp m1' f c1 rs1 c2 m2 m2' ms2,
  match_stack s ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  wt_function f ->
  incl c2 f.(fn_code) ->
  transl_code_at_pc (rs1 PC) fb f c1 ->
  (exists rs2,
     exec_straight tge (transl_function f) (transl_code f c1) rs1 m1' (transl_code f c2) rs2 m2'
     /\ agree ms2 sp rs2) ->
  Mem.extends m2 m2' ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Machconcr.State s fb sp c2 ms2 m2) st'.
Proof.
  intros. destruct H4 as [rs2 [A B]].
  exists (State rs2 m2'); split.
  eapply exec_straight_exec; eauto.
  econstructor; eauto. eapply exec_straight_at; eauto.
Qed.

Lemma exec_straight_steps_bis:
  forall s fb sp m1' f c1 rs1 c2 m2 ms2,
  match_stack s ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  wt_function f ->
  incl c2 f.(fn_code) ->
  transl_code_at_pc (rs1 PC) fb f c1 ->
  (exists m2',
      Mem.extends m2 m2'
   /\ exists rs2,
        exec_straight tge (transl_function f) (transl_code f c1) rs1 m1' (transl_code f c2) rs2 m2'
        /\ agree ms2 sp rs2) ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Machconcr.State s fb sp c2 ms2 m2) st'.
Proof.
  intros. destruct H4 as [m2' [A B]]. 
  eapply exec_straight_steps; eauto.
Qed.

Lemma parent_sp_def: forall s, match_stack s -> parent_sp s <> Vundef.
Proof. induction 1; simpl. congruence. auto. Qed.

Lemma parent_ra_def: forall s, match_stack s -> parent_ra s <> Vundef.
Proof. induction 1; simpl. unfold Vzero. congruence. auto. Qed.

Lemma lessdef_parent_sp:
  forall s v,
  match_stack s -> Val.lessdef (parent_sp s) v -> v = parent_sp s.
Proof.
  intros. inv H0. auto. exploit parent_sp_def; eauto. tauto.
Qed.

Lemma lessdef_parent_ra:
  forall s v,
  match_stack s -> Val.lessdef (parent_ra s) v -> v = parent_ra s.
Proof.
  intros. inv H0. auto. exploit parent_ra_def; eauto. tauto.
Qed.

(** We need to show that, in the simulation diagram, we cannot
  take infinitely many Mach transitions that correspond to zero
  transitions on the PPC side.  Actually, all Mach transitions
  correspond to at least one PPC transition, except the
  transition from [Machconcr.Returnstate] to [Machconcr.State].
  So, the following integer measure will suffice to rule out
  the unwanted behaviour. *)

Definition measure (s: Machconcr.state) : nat :=
  match s with
  | Machconcr.State _ _ _ _ _ _ => 0%nat
  | Machconcr.Callstate _ _ _ _ => 0%nat
  | Machconcr.Returnstate _ _ _ => 1%nat
  end.

(** We show the simulation diagram by case analysis on the Mach transition
  on the left.  Since the proof is large, we break it into one lemma
  per transition. *)

Definition exec_instr_prop (s1: Machconcr.state) (t: trace) (s2: Machconcr.state) : Prop :=
  forall s1' (MS: match_states s1 s1'),
  (exists s2', plus step tge s1' t s2' /\ match_states s2 s2')
  \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.


Lemma exec_Mlabel_prop:
  forall (s : list stackframe) (fb : block) (sp : val)
         (lbl : Mach.label) (c : list Mach.instruction) (ms : Mach.regset)
         (m : mem),
  exec_instr_prop (Machconcr.State s fb sp (Mlabel lbl :: c) ms m) E0
                  (Machconcr.State s fb sp c ms m).
Proof.
  intros; red; intros; inv MS.
  left; eapply exec_straight_steps; eauto with coqlib.
  exists (nextinstr rs); split.
  simpl. apply exec_straight_one. reflexivity. reflexivity.
  apply agree_nextinstr; auto.
Qed.

Lemma exec_Mgetstack_prop:
  forall (s : list stackframe) (fb : block) (sp : val) (ofs : int)
         (ty : typ) (dst : mreg) (c : list Mach.instruction)
         (ms : Mach.regset) (m : mem) (v : val),
  load_stack m sp ty ofs = Some v ->
  exec_instr_prop (Machconcr.State s fb sp (Mgetstack ofs ty dst :: c) ms m) E0
                  (Machconcr.State s fb sp c (Regmap.set dst v ms) m).
Proof.
  intros; red; intros; inv MS.
  unfold load_stack in H. 
  generalize (wt_function_instrs _ WTF _ (INCL _ (in_eq _ _))).
  intro WTI. inversion WTI.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ AG) in A.
  exploit (loadind_correct tge (transl_function f) GPR1 ofs ty dst (transl_code f c) rs m' v').
  auto. auto. congruence. 
  intros [rs2 [EX [RES OTH]]].
  left; eapply exec_straight_steps; eauto with coqlib.
  simpl. exists rs2; split. auto. 
  apply agree_exten_2 with (rs#(preg_of dst) <- v').
  auto with ppcgen. 
  intros. unfold Pregmap.set. destruct (PregEq.eq r0 (preg_of dst)).
  subst r0. auto.
  apply OTH; auto.
Qed.

Lemma exec_Msetstack_prop:
  forall (s : list stackframe) (fb : block) (sp : val) (src : mreg)
         (ofs : int) (ty : typ) (c : list Mach.instruction)
         (ms : mreg -> val) (m m' : mem),
  store_stack m sp ty ofs (ms src) = Some m' ->
  exec_instr_prop (Machconcr.State s fb sp (Msetstack src ofs ty :: c) ms m) E0
                  (Machconcr.State s fb sp c ms m').
Proof.
  intros; red; intros; inv MS.
  unfold store_stack in H. 
  generalize (wt_function_instrs _ WTF _ (INCL _ (in_eq _ _))).
  intro WTI. inv WTI.
  generalize (preg_val ms sp rs src AG). intro. 
  exploit Mem.storev_extends; eauto.
  intros [m2' [A B]].
  rewrite (sp_val _ _ _ AG) in A.
  exploit (storeind_correct tge (transl_function f) GPR1 ofs (mreg_type src)
                src (transl_code f c) rs).
  eauto. auto. congruence.
  intros [rs2 [EX OTH]].
  left; eapply exec_straight_steps; eauto with coqlib.
  exists rs2; split; auto.
  apply agree_exten_2 with rs; auto.
Qed.

Lemma exec_Mgetparam_prop:
  forall (s : list stackframe) (fb : block) (f: Mach.function) (sp parent : val)
         (ofs : int) (ty : typ) (dst : mreg) (c : list Mach.instruction)
         (ms : Mach.regset) (m : mem) (v : val),
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  load_stack m sp Tint f.(fn_link_ofs) = Some parent ->
  load_stack m parent ty ofs = Some v ->
  exec_instr_prop (Machconcr.State s fb sp (Mgetparam ofs ty dst :: c) ms m) E0
                  (Machconcr.State s fb sp c (Regmap.set dst v (Regmap.set IT1 Vundef ms)) m).
Proof.
  intros; red; intros; inv MS.
  assert (f0 = f) by congruence. subst f0.
  generalize (wt_function_instrs _ WTF _ (INCL _ (in_eq _ _))).
  intro WTI. inv WTI.
  unfold load_stack in *. simpl in H0. 
  exploit Mem.loadv_extends. eauto. eexact H0. auto. 
  intros [parent' [A B]].
  exploit Mem.loadv_extends. eauto. eexact H1. 
  instantiate (1 := (Val.add parent' (Vint ofs))). 
  inv B. auto. simpl; auto.
  intros [v' [C D]].
  left; eapply exec_straight_steps; eauto with coqlib. simpl. 
  set (rs1 := nextinstr (rs#GPR11 <- parent')).
  exploit (loadind_correct tge (transl_function f) GPR11 ofs (mreg_type dst) dst (transl_code f c) rs1 m' v').
  unfold rs1. rewrite nextinstr_inv; auto with ppcgen. auto. congruence.
  intros [rs2 [U [V W]]].
  exists rs2; split.
  apply exec_straight_step with rs1 m'. 
  simpl. unfold load1. simpl. rewrite gpr_or_zero_not_zero.
  rewrite <- (sp_val _ _ _ AG). rewrite A. auto. congruence. auto. 
  auto.
  assert (agree (Regmap.set IT1 Vundef ms) sp rs1).
  unfold rs1. eauto with ppcgen.
  apply agree_exten_2 with (rs1#(preg_of dst) <- v').
  auto with ppcgen. 
  intros. unfold Pregmap.set. destruct (PregEq.eq r (preg_of dst)). 
  congruence. auto. 
Qed.

Lemma exec_Mop_prop:
  forall (s : list stackframe) (fb : block) (sp : val) (op : operation)
         (args : list mreg) (res : mreg) (c : list Mach.instruction)
         (ms : mreg -> val) (m : mem) (v : val),
  eval_operation ge sp op ms ## args = Some v ->
  exec_instr_prop (Machconcr.State s fb sp (Mop op args res :: c) ms m) E0
                  (Machconcr.State s fb sp c (Regmap.set res v (undef_op op ms)) m).
Proof.
  intros; red; intros; inv MS.
  generalize (wt_function_instrs _ WTF _ (INCL _ (in_eq _ _))).
  intro WTI.
  left; eapply exec_straight_steps; eauto with coqlib.
  simpl. eapply transl_op_correct; auto.
  rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
Qed.

Remark loadv_8_signed_unsigned:
  forall m a v,
  Mem.loadv Mint8signed m a = Some v ->
  exists v', Mem.loadv Mint8unsigned m a = Some v' /\ v = Val.sign_ext 8 v'.
Proof.
  unfold Mem.loadv; intros. destruct a; try congruence.
  generalize (Mem.load_int8_signed_unsigned m b (Int.signed i)).
  rewrite H. destruct (Mem.load Mint8unsigned m b (Int.signed i)).
  simpl; intros. exists v0; split; congruence.
  simpl; congruence.
Qed.

Lemma exec_Mload_prop:
  forall (s : list stackframe) (fb : block) (sp : val)
         (chunk : memory_chunk) (addr : addressing) (args : list mreg)
         (dst : mreg) (c : list Mach.instruction) (ms : mreg -> val)
         (m : mem) (a v : val),
  eval_addressing ge sp addr ms ## args = Some a ->
  Mem.loadv chunk m a = Some v ->
  exec_instr_prop (Machconcr.State s fb sp (Mload chunk addr args dst :: c) ms m)
               E0 (Machconcr.State s fb sp c (Regmap.set dst v (undef_temps ms)) m).
Proof.
  intros; red; intros; inv MS.
  generalize (wt_function_instrs _ WTF _ (INCL _ (in_eq _ _))).
  intro WTI; inversion WTI.
  assert (eval_addressing tge sp addr ms##args = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  left; eapply exec_straight_steps; eauto with coqlib;
  destruct chunk; simpl; simpl in H6;
  (* all cases but Mint8signed *)
  try (eapply transl_load_correct; eauto;
       intros; simpl; unfold preg_of; rewrite H6; auto).
  (* Mint8signed *)
  exploit loadv_8_signed_unsigned; eauto. intros [v' [LOAD EQ]].
  assert (X1: forall (cst : constant) (r1 : ireg) (rs1 : regset),
    exec_instr tge (transl_function f) (Plbz (ireg_of dst) cst r1) rs1 m' =
    load1 tge Mint8unsigned (preg_of dst) cst r1 rs1 m').
    intros. unfold preg_of; rewrite H6. reflexivity. 
  assert (X2: forall (r1 r2 : ireg) (rs1 : regset),
    exec_instr tge (transl_function f) (Plbzx (ireg_of dst) r1 r2) rs1 m' =
    load2 Mint8unsigned (preg_of dst) r1 r2 rs1 m').
    intros. unfold preg_of; rewrite H6. reflexivity.
  exploit transl_load_correct; eauto. 
  intros [rs2 [EX1 AG1]].
  econstructor; split. 
  eapply exec_straight_trans. eexact EX1.
  apply exec_straight_one. simpl. eauto. auto.
  apply agree_nextinstr.
  eapply agree_set_twice_mireg; eauto.
  rewrite EQ. apply Val.sign_ext_lessdef. 
  generalize (ireg_val _ _ _ dst AG1 H6). rewrite Regmap.gss. auto.
Qed.

Lemma storev_8_signed_unsigned:
  forall m a v,
  Mem.storev Mint8signed m a v = Mem.storev Mint8unsigned m a v.
Proof.
  intros. unfold Mem.storev. destruct a; auto.
  apply Mem.store_signed_unsigned_8.
Qed.

Lemma storev_16_signed_unsigned:
  forall m a v,
  Mem.storev Mint16signed m a v = Mem.storev Mint16unsigned m a v.
Proof.
  intros. unfold Mem.storev. destruct a; auto.
  apply Mem.store_signed_unsigned_16.
Qed.

Lemma exec_Mstore_prop:
  forall (s : list stackframe) (fb : block) (sp : val)
         (chunk : memory_chunk) (addr : addressing) (args : list mreg)
         (src : mreg) (c : list Mach.instruction) (ms : mreg -> val)
         (m m' : mem) (a : val),
  eval_addressing ge sp addr ms ## args = Some a ->
  Mem.storev chunk m a (ms src) = Some m' ->
  exec_instr_prop (Machconcr.State s fb sp (Mstore chunk addr args src :: c) ms m) E0
                  (Machconcr.State s fb sp c (undef_temps ms) m').
Proof.
  intros; red; intros; inv MS.
  generalize (wt_function_instrs _ WTF _ (INCL _ (in_eq _ _))).
  intro WTI; inv WTI.
  rewrite <- (eval_addressing_preserved _ _ symbols_preserved) in H.
  left; eapply exec_straight_steps_bis; eauto with coqlib.
  destruct chunk; simpl; simpl in H6;
  try (rewrite storev_8_signed_unsigned in H0);
  try (rewrite storev_16_signed_unsigned in H0);
  simpl; eapply transl_store_correct; eauto;
  (unfold preg_of; rewrite H6; intros; econstructor; eauto).
  split. simpl. rewrite H1. eauto. intros; apply Pregmap.gso; auto.
  split. simpl. rewrite H1. eauto. intros; apply Pregmap.gso; auto.
Qed.

Lemma exec_Mcall_prop:
  forall (s : list stackframe) (fb : block) (sp : val)
         (sig : signature) (ros : mreg + ident) (c : Mach.code)
         (ms : Mach.regset) (m : mem) (f : function) (f' : block)
         (ra : int),
  find_function_ptr ge ros ms = Some f' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  return_address_offset f c ra ->
  exec_instr_prop (Machconcr.State s fb sp (Mcall sig ros :: c) ms m) E0
                  (Callstate (Stackframe fb sp (Vptr fb ra) c :: s) f' ms m).
Proof.
  intros; red; intros; inv MS.
  assert (f0 = f) by congruence. subst f0.
  generalize (wt_function_instrs _ WTF _ (INCL _ (in_eq _ _))).
  intro WTI. inversion WTI.
  inv AT. 
  assert (NOOV: list_length_z (transl_function f) <= Int.max_unsigned).
    eapply functions_transl_no_overflow; eauto.
  destruct ros; simpl in H; simpl transl_code in H7.
  (* Indirect call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H7). intro CT1.
  generalize (code_tail_next_int _ _ _ _ NOOV CT1). intro CT2.
  assert (P1: ms m0 = Vptr f' Int.zero).
    destruct (ms m0); try congruence. 
    generalize H; predSpec Int.eq Int.eq_spec i Int.zero; intros; congruence.
  assert (P2: rs (ireg_of m0) = Vptr f' Int.zero).
    generalize (ireg_val _ _ _ m0 AG H3).
    rewrite P1. intro. inv H2. auto.
  set (rs2 := nextinstr (rs#CTR <- (Vptr f' Int.zero))).
  set (rs3 := rs2 #LR <- (Val.add rs2#PC Vone) #PC <- (Vptr f' Int.zero)).
  assert (ATPC: rs3 PC = Vptr f' Int.zero). reflexivity.
  exploit return_address_offset_correct; eauto. constructor; eauto. 
  intro RA_EQ.
  assert (ATLR: rs3 LR = Vptr fb ra).
    rewrite RA_EQ.
    change (rs3 LR) with (Val.add (Val.add (rs PC) Vone) Vone).
    rewrite <- H5. reflexivity. 
  assert (AG3: agree ms sp rs3). 
    unfold rs3, rs2; auto 8 with ppcgen.
  left; exists (State rs3 m'); split.
  apply plus_left with E0 (State rs2 m') E0. 
    econstructor. eauto. apply functions_transl. eexact H0. 
    eapply find_instr_tail. eauto.
    simpl. rewrite P2. auto.
  apply star_one. econstructor.
    change (rs2 PC) with (Val.add (rs PC) Vone). rewrite <- H5.
    simpl. auto.
    apply functions_transl. eexact H0.
    eapply find_instr_tail. eauto.
    simpl. reflexivity.
  traceEq.
  econstructor; eauto.
  econstructor; eauto with coqlib.
  rewrite RA_EQ. econstructor; eauto.
  eapply agree_sp_def; eauto. congruence.

  (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H7). intro CT1.
  set (rs2 := rs #LR <- (Val.add rs#PC Vone) #PC <- (symbol_offset tge i Int.zero)).
  assert (ATPC: rs2 PC = Vptr f' Int.zero).
    change (rs2 PC) with (symbol_offset tge i Int.zero).
    unfold symbol_offset. rewrite symbols_preserved. rewrite H. auto.
  exploit return_address_offset_correct; eauto. constructor; eauto. 
  intro RA_EQ.
  assert (ATLR: rs2 LR = Vptr fb ra).
    rewrite RA_EQ.
    change (rs2 LR) with (Val.add (rs PC) Vone).
    rewrite <- H5. reflexivity. 
  assert (AG2: agree ms sp rs2). 
    unfold rs2; auto 8 with ppcgen.
  left; exists (State rs2 m'); split.
  apply plus_one. econstructor. 
    eauto.
    apply functions_transl. eexact H0. 
    eapply find_instr_tail. eauto.
    simpl. reflexivity.
  econstructor; eauto with coqlib.
  econstructor; eauto with coqlib.
  rewrite RA_EQ. econstructor; eauto.
  eapply agree_sp_def; eauto. congruence.
Qed.

Lemma exec_Mtailcall_prop:
  forall (s : list stackframe) (fb stk : block) (soff : int)
         (sig : signature) (ros : mreg + ident) (c : list Mach.instruction)
         (ms : Mach.regset) (m : mem) (f: Mach.function) (f' : block) m',
  find_function_ptr ge ros ms = Some f' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  load_stack m (Vptr stk soff) Tint f.(fn_link_ofs) = Some (parent_sp s) ->
  load_stack m (Vptr stk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra s) ->
  Mem.free m stk (- f.(fn_framesize)) f.(fn_stacksize) = Some m' ->
  exec_instr_prop
          (Machconcr.State s fb (Vptr stk soff) (Mtailcall sig ros :: c) ms m) E0
          (Callstate s f' ms m').
Proof.
  intros; red; intros; inv MS.
  assert (f0 = f) by congruence. subst f0.
  generalize (wt_function_instrs _ WTF _ (INCL _ (in_eq _ _))).
  intro WTI. inversion WTI.
  inversion AT. subst b f0 c0.
  assert (NOOV: list_length_z (transl_function f) <= Int.max_unsigned).
    eapply functions_transl_no_overflow; eauto.
  exploit Mem.free_parallel_extends; eauto.
  intros [m2' [FREE' EXT']].
  unfold load_stack in *. simpl in H1; simpl in H2.
  exploit Mem.load_extends. eexact MEXT. eexact H1.
  intros [parent' [LOAD1 LD1]].
  rewrite (lessdef_parent_sp s parent' STACKS LD1) in LOAD1.
  exploit Mem.load_extends. eexact MEXT. eexact H2.
  intros [ra' [LOAD2 LD2]].
  rewrite (lessdef_parent_ra s ra' STACKS LD2) in LOAD2.
  destruct ros; simpl in H; simpl in H9.
  (* Indirect call *)
  assert (P1: ms m0 = Vptr f' Int.zero).
    destruct (ms m0); try congruence. 
    generalize H; predSpec Int.eq Int.eq_spec i Int.zero; intros; congruence.
  assert (P2: rs (ireg_of m0) = Vptr f' Int.zero).
    generalize (ireg_val _ _ _ m0 AG H7).
    rewrite P1. intro. inv H11. auto.
  set (rs2 := nextinstr (rs#CTR <- (Vptr f' Int.zero))).
  set (rs3 := nextinstr (rs2#GPR0 <- (parent_ra s))).
  set (rs4 := nextinstr (rs3#LR <- (parent_ra s))).
  set (rs5 := nextinstr (rs4#GPR1 <- (parent_sp s))).
  set (rs6 := rs5#PC <- (rs5 CTR)).
  assert (exec_straight tge (transl_function f)
            (transl_code f (Mtailcall sig (inl ident m0) :: c)) rs m'0 
            (Pbctr :: transl_code f c) rs5 m2').
  simpl. apply exec_straight_step with rs2 m'0. 
  simpl. rewrite P2. auto. auto.
  apply exec_straight_step with rs3 m'0.
  simpl. unfold load1. rewrite gpr_or_zero_not_zero. unfold const_low.
  change (rs2 GPR1) with (rs GPR1). rewrite <- (sp_val _ _ _ AG). 
  simpl. rewrite LOAD2. auto. congruence. auto. 
  apply exec_straight_step with rs4 m'0.
  simpl. reflexivity. reflexivity.
  apply exec_straight_one. 
  simpl. change (rs4 GPR1) with (rs GPR1). rewrite <- (sp_val _ _ _ AG).
  simpl. rewrite LOAD1. rewrite FREE'. reflexivity. reflexivity.
  left; exists (State rs6 m2'); split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor.
  change (rs5 PC) with (Val.add (Val.add (Val.add (Val.add (rs PC) Vone) Vone) Vone) Vone).
  rewrite <- H8; simpl. eauto.
  eapply functions_transl; eauto. 
  eapply find_instr_tail.
  repeat (eapply code_tail_next_int; auto). eauto. 
  simpl. reflexivity. traceEq.
  (* match states *)
  econstructor; eauto.
  assert (AG4: agree ms (Vptr stk soff) rs4).
    unfold rs4, rs3, rs2; auto 10 with ppcgen.
  assert (AG5: agree ms (parent_sp s) rs5).
    unfold rs5. apply agree_nextinstr.
    split. reflexivity. apply parent_sp_def; auto. 
    intros. inv AG4. rewrite Pregmap.gso; auto with ppcgen.
  unfold rs6; auto with ppcgen.
  (* direct call *)
  set (rs2 := nextinstr (rs#GPR0 <- (parent_ra s))).
  set (rs3 := nextinstr (rs2#LR <- (parent_ra s))).
  set (rs4 := nextinstr (rs3#GPR1 <- (parent_sp s))).
  set (rs5 := rs4#PC <- (Vptr f' Int.zero)).
  assert (exec_straight tge (transl_function f)
            (transl_code f (Mtailcall sig (inr mreg i) :: c)) rs m'0 
            (Pbs i :: transl_code f c) rs4 m2').
  simpl. apply exec_straight_step with rs2 m'0. 
  simpl. unfold load1. rewrite gpr_or_zero_not_zero. unfold const_low.
  rewrite <- (sp_val _ _ _ AG). 
  simpl. rewrite LOAD2. auto. discriminate. auto. 
  apply exec_straight_step with rs3 m'0.
  simpl. reflexivity. reflexivity.
  apply exec_straight_one. 
  simpl. change (rs3 GPR1) with (rs GPR1). rewrite <- (sp_val _ _ _ AG).
  simpl. rewrite LOAD1. rewrite FREE'. reflexivity. reflexivity.
  left; exists (State rs5 m2'); split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor.
  change (rs4 PC) with (Val.add (Val.add (Val.add (rs PC) Vone) Vone) Vone).
  rewrite <- H8; simpl. eauto.
  eapply functions_transl; eauto. 
  eapply find_instr_tail.
  repeat (eapply code_tail_next_int; auto). eauto. 
  simpl. unfold symbol_offset. rewrite symbols_preserved. rewrite H. 
  reflexivity. traceEq.
  (* match states *)
  econstructor; eauto.
  assert (AG3: agree ms (Vptr stk soff) rs3).
    unfold rs3, rs2; auto 10 with ppcgen.
  assert (AG4: agree ms (parent_sp s) rs4).
    unfold rs4. apply agree_nextinstr.
    split. reflexivity. 
    apply parent_sp_def; auto.
    intros. inv AG3. rewrite Pregmap.gso; auto with ppcgen.
  unfold rs5; auto with ppcgen.
Qed.

Lemma exec_Mbuiltin_prop:
  forall (s : list stackframe) (f : block) (sp : val)
         (ms : Mach.regset) (m : mem) (ef : external_function)
         (args : list mreg) (res : mreg) (b : list Mach.instruction)
         (t : trace) (v : val) (m' : mem),
  external_call ef ge ms ## args m t v m' ->
  exec_instr_prop (Machconcr.State s f sp (Mbuiltin ef args res :: b) ms m) t
                  (Machconcr.State s f sp b (Regmap.set res v (undef_temps ms)) m').
Proof.
  intros; red; intros; inv MS.
  generalize (wt_function_instrs _ WTF _ (INCL _ (in_eq _ _))).
  intro WTI. inv WTI.
  inv AT. simpl in H3.
  generalize (functions_transl _ _ FIND); intro FN.
  generalize (functions_transl_no_overflow _ _ FIND); intro NOOV.
  exploit external_call_mem_extends; eauto. eapply preg_vals; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  left. econstructor; split. apply plus_one. 
  eapply exec_step_builtin. eauto. eauto.
  eapply find_instr_tail; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto with coqlib.
  unfold nextinstr. rewrite Pregmap.gss. repeat rewrite Pregmap.gso; auto with ppcgen.
  rewrite <- H0. simpl. constructor; auto.
  eapply code_tail_next_int; eauto. 
  apply sym_not_equal. auto with ppcgen.
  apply agree_nextinstr. apply agree_set_mreg; auto. 
  eapply agree_undef_temps; eauto. 
  intros. repeat rewrite Pregmap.gso; auto. 
Qed.

Lemma exec_Mgoto_prop:
  forall (s : list stackframe) (fb : block) (f : function) (sp : val)
         (lbl : Mach.label) (c : list Mach.instruction) (ms : Mach.regset)
         (m : mem) (c' : Mach.code),
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl (fn_code f) = Some c' ->
  exec_instr_prop (Machconcr.State s fb sp (Mgoto lbl :: c) ms m) E0
                  (Machconcr.State s fb sp c' ms m).
Proof.
  intros; red; intros; inv MS.
  assert (f0 = f) by congruence. subst f0.
  inv AT. simpl in H3.
  generalize (find_label_goto_label f lbl rs m' _ _ _ FIND (sym_equal H1) H0).
  intros [rs2 [GOTO [AT2 INV]]].
  left; exists (State rs2 m'); split.
  apply plus_one. econstructor; eauto.
  apply functions_transl; eauto.
  eapply find_instr_tail; eauto.
  simpl; auto.
  econstructor; eauto.
  eapply Mach.find_label_incl; eauto.
  apply agree_exten_2 with rs; auto. 
Qed.

Lemma exec_Mcond_true_prop:
  forall (s : list stackframe) (fb : block) (f : function) (sp : val)
         (cond : condition) (args : list mreg) (lbl : Mach.label)
         (c : list Mach.instruction) (ms : mreg -> val) (m : mem)
         (c' : Mach.code),
  eval_condition cond ms ## args = Some true ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl (fn_code f) = Some c' ->
  exec_instr_prop (Machconcr.State s fb sp (Mcond cond args lbl :: c) ms m) E0
                  (Machconcr.State s fb sp c' (undef_temps ms) m).
Proof.
  intros; red; intros; inv MS. assert (f0 = f) by congruence. subst f0.
  generalize (wt_function_instrs _ WTF _ (INCL _ (in_eq _ _))).
  intro WTI. inv WTI.
  pose (k1 := 
         if snd (crbit_for_cond cond)
         then Pbt (fst (crbit_for_cond cond)) lbl :: transl_code f c
         else Pbf (fst (crbit_for_cond cond)) lbl :: transl_code f c).
  generalize (transl_cond_correct tge (transl_function f)
                cond args k1 ms sp rs m' true H3 AG H).
  simpl. intros [rs2 [EX [RES AG2]]].
  inv AT. simpl in H5.
  generalize (functions_transl _ _ H4); intro FN.
  generalize (functions_transl_no_overflow _ _ H4); intro NOOV.
  exploit exec_straight_steps_2; eauto. 
  intros [ofs' [PC2 CT2]].
  generalize (find_label_goto_label f lbl rs2 m' _ _ _ FIND PC2 H1).
  intros [rs3 [GOTO [AT3 INV3]]].
  left; exists (State rs3 m'); split.
  eapply plus_right'. 
  eapply exec_straight_steps_1; eauto.
  caseEq (snd (crbit_for_cond cond)); intro ISSET; rewrite ISSET in RES.
  econstructor; eauto.
  eapply find_instr_tail. unfold k1 in CT2; rewrite ISSET in CT2. eauto.
  simpl. rewrite RES. simpl. auto.
  econstructor; eauto.
  eapply find_instr_tail. unfold k1 in CT2; rewrite ISSET in CT2. eauto.
  simpl. rewrite RES. simpl. auto.
  traceEq.
  econstructor; eauto. 
  eapply Mach.find_label_incl; eauto.
  apply agree_exten_2 with rs2; auto with ppcgen. 
Qed.

Lemma exec_Mcond_false_prop:
  forall (s : list stackframe) (fb : block) (sp : val)
         (cond : condition) (args : list mreg) (lbl : Mach.label)
         (c : list Mach.instruction) (ms : mreg -> val) (m : mem),
  eval_condition cond ms ## args = Some false ->
  exec_instr_prop (Machconcr.State s fb sp (Mcond cond args lbl :: c) ms m) E0
                  (Machconcr.State s fb sp c (undef_temps ms) m).
Proof.
  intros; red; intros; inv MS.
  generalize (wt_function_instrs _ WTF _ (INCL _ (in_eq _ _))).
  intro WTI. inversion WTI.
  pose (k1 := 
         if snd (crbit_for_cond cond)
         then Pbt (fst (crbit_for_cond cond)) lbl :: transl_code f c
         else Pbf (fst (crbit_for_cond cond)) lbl :: transl_code f c).
  generalize (transl_cond_correct tge (transl_function f)
                cond args k1 ms sp rs m' false H1 AG H).
  simpl. intros [rs2 [EX [RES AG2]]].
  left; eapply exec_straight_steps; eauto with coqlib.
  exists (nextinstr rs2); split.
  simpl. eapply exec_straight_trans. eexact EX. 
  caseEq (snd (crbit_for_cond cond)); intro ISSET; rewrite ISSET in RES.
  unfold k1; rewrite ISSET; apply exec_straight_one. 
  simpl. rewrite RES. reflexivity.
  reflexivity.
  unfold k1; rewrite ISSET; apply exec_straight_one. 
  simpl. rewrite RES. reflexivity.
  reflexivity.
  auto with ppcgen.
Qed.

Lemma exec_Mjumptable_prop:
  forall (s : list stackframe) (fb : block) (f : function) (sp : val)
         (arg : mreg) (tbl : list Mach.label) (c : list Mach.instruction)
         (rs : mreg -> val) (m : mem) (n : int) (lbl : Mach.label)
         (c' : Mach.code),
  rs arg = Vint n ->
  list_nth_z tbl (Int.signed n) = Some lbl ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl (fn_code f) = Some c' ->
  exec_instr_prop
    (Machconcr.State s fb sp (Mjumptable arg tbl :: c) rs m) E0
    (Machconcr.State s fb sp c' (undef_temps rs) m).
Proof.
  intros; red; intros; inv MS.
  assert (f0 = f) by congruence. subst f0.
  generalize (wt_function_instrs _ WTF _ (INCL _ (in_eq _ _))).
  intro WTI. inv WTI.
  exploit list_nth_z_range; eauto. intro RANGE.
  assert (SHIFT: Int.signed (Int.rolm n (Int.repr 2) (Int.repr (-4))) = Int.signed n * 4).
    replace (Int.repr (-4)) with (Int.shl Int.mone (Int.repr 2)).
    rewrite <- Int.shl_rolm. rewrite Int.shl_mul.
    rewrite Int.mul_signed.
    apply Int.signed_repr.
    split. apply Zle_trans with 0. compute; congruence. omega. 
    omega.
    compute. reflexivity.
    apply Int.mkint_eq. compute. reflexivity.
  inv AT. simpl in H7. 
  set (k1 := Pbtbl GPR12 tbl :: transl_code f c).
  set (rs1 := nextinstr (rs0 # GPR12 <- (Vint (Int.rolm n (Int.repr 2) (Int.repr (-4)))))).
  generalize (functions_transl _ _ H4); intro FN.
  generalize (functions_transl_no_overflow _ _ H4); intro NOOV.
  assert (exec_straight tge (transl_function f)
            (Prlwinm GPR12 (ireg_of arg) (Int.repr 2) (Int.repr (-4)) :: k1) rs0 m'
            k1 rs1 m').
   apply exec_straight_one. 
   simpl. generalize (ireg_val _ _ _ arg AG H5). rewrite H. intro. inv H8. 
   reflexivity. reflexivity. 
  exploit exec_straight_steps_2; eauto. 
  intros [ofs' [PC1 CT1]].
  set (rs2 := rs1 # GPR12 <- Vundef # CTR <- Vundef).
  assert (PC2: rs2 PC = Vptr fb ofs'). rewrite <- PC1. reflexivity.
  generalize (find_label_goto_label f lbl rs2 m' _ _ _ FIND PC2 H2).
  intros [rs3 [GOTO [AT3 INV3]]].
  left; exists (State rs3 m'); split.
  eapply plus_right'. 
  eapply exec_straight_steps_1; eauto.
  econstructor; eauto. 
  eapply find_instr_tail. unfold k1 in CT1. eauto.
  unfold exec_instr.
  change (rs1 GPR12) with (Vint (Int.rolm n (Int.repr 2) (Int.repr (-4)))).
Opaque Zmod.  Opaque Zdiv.
  simpl. rewrite SHIFT. rewrite Z_mod_mult. rewrite zeq_true. 
  rewrite Z_div_mult. 
  change label with Mach.label; rewrite H0. exact GOTO. omega. traceEq.
  econstructor; eauto. 
  eapply Mach.find_label_incl; eauto.
  apply agree_exten_2 with rs2; auto. 
  unfold rs2, rs1. apply agree_set_other; auto with ppcgen.
  apply agree_undef_temps with rs0; auto.
  intros. rewrite Pregmap.gso; auto. rewrite nextinstr_inv; auto.
  rewrite Pregmap.gso; auto. 
Qed.

Lemma exec_Mreturn_prop:
  forall (s : list stackframe) (fb stk : block) (soff : int)
         (c : list Mach.instruction) (ms : Mach.regset) (m : mem) (f: Mach.function) m',
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  load_stack m (Vptr stk soff) Tint f.(fn_link_ofs) = Some (parent_sp s) ->
  load_stack m (Vptr stk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra s) ->
  Mem.free m stk (- f.(fn_framesize)) f.(fn_stacksize) = Some m' ->
  exec_instr_prop (Machconcr.State s fb (Vptr stk soff) (Mreturn :: c) ms m) E0
                  (Returnstate s ms m').
Proof.
  intros; red; intros; inv MS.
  assert (f0 = f) by congruence. subst f0.
  exploit Mem.free_parallel_extends; eauto.
  intros [m2' [FREE' EXT']].
  unfold load_stack in *. simpl in H0; simpl in H1.
  exploit Mem.load_extends. eexact MEXT. eexact H0.
  intros [parent' [LOAD1 LD1]].
  rewrite (lessdef_parent_sp s parent' STACKS LD1) in LOAD1.
  exploit Mem.load_extends. eexact MEXT. eexact H1.
  intros [ra' [LOAD2 LD2]].
  rewrite (lessdef_parent_ra s ra' STACKS LD2) in LOAD2.
  set (rs2 := nextinstr (rs#GPR0 <- (parent_ra s))).
  set (rs3 := nextinstr (rs2#LR <- (parent_ra s))).
  set (rs4 := nextinstr (rs3#GPR1 <- (parent_sp s))).
  set (rs5 := rs4#PC <- (parent_ra s)).
  assert (exec_straight tge (transl_function f)
            (transl_code f (Mreturn :: c)) rs m'0 
            (Pblr :: transl_code f c) rs4 m2').
  simpl. apply exec_straight_three with rs2 m'0 rs3 m'0.
  simpl. unfold load1. rewrite gpr_or_zero_not_zero. unfold const_low.
  rewrite <- (sp_val _ _ _ AG). simpl. rewrite LOAD2. 
  reflexivity. discriminate.
  unfold rs3. reflexivity.
  simpl. change (rs3 GPR1) with (rs GPR1). rewrite <- (sp_val _ _ _ AG).
  simpl. rewrite LOAD1. rewrite FREE'. reflexivity.
  reflexivity. reflexivity. reflexivity.
  left; exists (State rs5 m2'); split.
  (* execution *)
  apply plus_right' with E0 (State rs4 m2') E0.
  eapply exec_straight_exec; eauto.
  inv AT. econstructor.
  change (rs4 PC) with (Val.add (Val.add (Val.add (rs PC) Vone) Vone) Vone). 
  rewrite <- H4. simpl. eauto.
  apply functions_transl; eauto.
  generalize (functions_transl_no_overflow _ _ H5); intro NOOV.
  simpl in H6. eapply find_instr_tail. 
  eapply code_tail_next_int; auto.
  eapply code_tail_next_int; auto.
  eapply code_tail_next_int; eauto.
  reflexivity. traceEq.
  (* match states *)
  econstructor; eauto. 
  assert (AG3: agree ms (Vptr stk soff) rs3). 
    unfold rs3, rs2; auto 10 with ppcgen.
  assert (AG4: agree ms (parent_sp s) rs4).
    split. reflexivity. apply parent_sp_def; auto. intros. unfold rs4. 
    rewrite nextinstr_inv. rewrite Pregmap.gso.
    elim AG3; auto. auto with ppcgen. auto with ppcgen.
  unfold rs5; auto with ppcgen.
Qed.

Hypothesis wt_prog: wt_program prog.

Lemma exec_function_internal_prop:
  forall (s : list stackframe) (fb : block) (ms : Mach.regset)
         (m : mem) (f : function) (m1 m2 m3 : mem) (stk : block),
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mem.alloc m (- fn_framesize f) (fn_stacksize f) = (m1, stk) ->
  let sp := Vptr stk (Int.repr (- fn_framesize f)) in
  store_stack m1 sp Tint f.(fn_link_ofs) (parent_sp s) = Some m2 ->
  store_stack m2 sp Tint f.(fn_retaddr_ofs) (parent_ra s) = Some m3 ->
  exec_instr_prop (Machconcr.Callstate s fb ms m) E0
                  (Machconcr.State s fb sp (fn_code f) ms m3).
Proof.
  intros; red; intros; inv MS.
  assert (WTF: wt_function f).
    generalize (Genv.find_funct_ptr_prop wt_fundef _ _ wt_prog H); intro TY.
    inversion TY; auto.
  exploit functions_transl; eauto. intro TFIND.
  generalize (functions_transl_no_overflow _ _ H); intro NOOV.
  unfold store_stack in *; simpl in *.
  exploit Mem.alloc_extends; eauto. apply Zle_refl. apply Zle_refl. 
  intros [m1' [ALLOC' MEXT1]].
  exploit Mem.store_within_extends. eexact MEXT1. eexact H1. auto.
  intros [m2' [STORE2 MEXT2]].
  exploit Mem.store_within_extends. eexact MEXT2. eexact H2. auto.
  intros [m3' [STORE3 MEXT3]].
  set (rs2 := nextinstr (rs#GPR1 <- sp #GPR0 <- Vundef)).
  set (rs3 := nextinstr (rs2#GPR0 <- (parent_ra s))).
  set (rs4 := nextinstr rs3).
  (* Execution of function prologue *)
  assert (EXEC_PROLOGUE:
            exec_straight tge (transl_function f)
              (transl_function f) rs m'
              (transl_code f (fn_code f)) rs4 m3').
  unfold transl_function at 2. 
  apply exec_straight_three with rs2 m2' rs3 m2'.
  unfold exec_instr. rewrite ALLOC'. fold sp.
  rewrite <- (sp_val _ _ _ AG). unfold sp; simpl; rewrite STORE2. reflexivity.
  simpl. change (rs2 LR) with (rs LR). rewrite ATLR. reflexivity.
  simpl. unfold store1. rewrite gpr_or_zero_not_zero. 
  unfold const_low. change (rs3 GPR1) with sp. change (rs3 GPR0) with (parent_ra s).
  simpl. rewrite STORE3. reflexivity. 
  discriminate. reflexivity. reflexivity. reflexivity.
  (* Agreement at end of prologue *)
  assert (AT4: transl_code_at_pc rs4#PC fb f f.(fn_code)).
    change (rs4 PC) with (Val.add (Val.add (Val.add (rs PC) Vone) Vone) Vone).
    rewrite ATPC. simpl. constructor. auto.
    eapply code_tail_next_int; auto.
    eapply code_tail_next_int; auto.
    eapply code_tail_next_int; auto.
    change (Int.unsigned Int.zero) with 0. 
    unfold transl_function. constructor.
  assert (AG2: agree ms sp rs2).
    split. reflexivity. unfold sp. congruence. 
    intros. unfold rs2. rewrite nextinstr_inv. 
    repeat (rewrite Pregmap.gso). elim AG; auto.
    auto with ppcgen. auto with ppcgen. auto with ppcgen.
  assert (AG4: agree ms sp rs4).
    unfold rs4, rs3; auto with ppcgen.
  left; exists (State rs4 m3'); split.
  (* execution *)
  eapply exec_straight_steps_1; eauto.
  change (Int.unsigned Int.zero) with 0. constructor.
  (* match states *)
  econstructor; eauto with coqlib.
Qed.

Lemma exec_function_external_prop:
  forall (s : list stackframe) (fb : block) (ms : Mach.regset)
         (m : mem) (t0 : trace) (ms' : RegEq.t -> val)
         (ef : external_function) (args : list val) (res : val) (m': mem),
  Genv.find_funct_ptr ge fb = Some (External ef) ->
  external_call ef ge args m t0 res m' ->
  Machconcr.extcall_arguments ms m (parent_sp s) (ef_sig ef) args ->
  ms' = Regmap.set (loc_result (ef_sig ef)) res ms ->
  exec_instr_prop (Machconcr.Callstate s fb ms m)
               t0 (Machconcr.Returnstate s ms' m').
Proof.
  intros; red; intros; inv MS.
  exploit functions_translated; eauto.
  intros [tf [A B]]. simpl in B. inv B. 
  exploit extcall_arguments_match; eauto. 
  intros [args' [C D]].
  exploit external_call_mem_extends; eauto. 
  intros [res' [m2' [P [Q [R S]]]]].
  left; exists (State (rs#(loc_external_result (ef_sig ef)) <- res' #PC <- (rs LR))
                m2'); split.
  apply plus_one. eapply exec_step_external; eauto. 
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto.
  unfold loc_external_result. auto with ppcgen.
Qed.

Lemma exec_return_prop:
  forall (s : list stackframe) (fb : block) (sp ra : val)
         (c : Mach.code) (ms : Mach.regset) (m : mem),
  exec_instr_prop (Machconcr.Returnstate (Stackframe fb sp ra c :: s) ms m) E0
                  (Machconcr.State s fb sp c ms m).
Proof.
  intros; red; intros; inv MS. inv STACKS. simpl in *.
  right. split. omega. split. auto. 
  econstructor; eauto. rewrite ATPC; auto.  
Qed.

Theorem transf_instr_correct:
  forall s1 t s2, Machconcr.step ge s1 t s2 ->
  exec_instr_prop s1 t s2.
Proof
  (Machconcr.step_ind ge exec_instr_prop
           exec_Mlabel_prop
           exec_Mgetstack_prop
           exec_Msetstack_prop
           exec_Mgetparam_prop
           exec_Mop_prop
           exec_Mload_prop
           exec_Mstore_prop
           exec_Mcall_prop
           exec_Mtailcall_prop
           exec_Mbuiltin_prop
           exec_Mgoto_prop
           exec_Mcond_true_prop
           exec_Mcond_false_prop
           exec_Mjumptable_prop
           exec_Mreturn_prop
           exec_function_internal_prop
           exec_function_external_prop
           exec_return_prop).

Lemma transf_initial_states:
  forall st1, Machconcr.initial_state prog st1 ->
  exists st2, Asm.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. unfold ge0 in *.
  econstructor; split.
  econstructor.
  eapply Genv.init_mem_transf_partial; eauto.
  replace (symbol_offset (Genv.globalenv tprog) (prog_main tprog) Int.zero)
     with (Vptr fb Int.zero).
  econstructor; eauto. constructor.
  split. auto. simpl. congruence.
  intros. repeat rewrite Pregmap.gso; auto with ppcgen.
  apply Mem.extends_refl.
  unfold symbol_offset. 
  rewrite (transform_partial_program_main _ _ TRANSF). 
  rewrite symbols_preserved. unfold ge; rewrite H1. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> Machconcr.final_state st1 r -> Asm.final_state st2 r.
Proof.
  intros. inv H0. inv H. constructor. auto. 
  compute in H1.
  exploit (ireg_val _ _ _ R3 AG). auto. rewrite H1; intro. inv H. auto.
Qed.

Theorem transf_program_correct:
  forall (beh: program_behavior), not_wrong beh ->
  Machconcr.exec_program prog beh -> Asm.exec_program tprog beh.
Proof.
  unfold Machconcr.exec_program, Asm.exec_program; intros.
  eapply simulation_star_preservation with (measure := measure); eauto.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transf_instr_correct. 
Qed.

End PRESERVATION.
