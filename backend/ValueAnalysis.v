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

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Lattice.
Require Import Kildall.
Require Import Registers.
Require Import Op.
Require Import RTL.
Require Import ValueDomain.
Require Import ValueAOp.
Require Import Liveness.

(** * The dataflow analysis *)

Definition areg (ae: aenv) (r: reg) : aval := AE.get r ae.

Definition aregs (ae: aenv) (rl: list reg) : list aval := List.map (areg ae) rl.

Definition mafter_public_call : amem := mtop.

Definition mafter_private_call (am_before: amem) : amem :=
  {| am_stack := am_before.(am_stack);
     am_glob := PTree.empty _;
     am_nonstack := Nonstack;
     am_top := plub (ab_summary (am_stack am_before)) Nonstack |}.

Definition transfer_call (ae: aenv) (am: amem) (args: list reg) (res: reg) :=
  if pincl am.(am_nonstack) Nonstack
  && forallb (fun r => vpincl (areg ae r) Nonstack) args
  then
    VA.State (AE.set res (Ifptr Nonstack) ae) (mafter_private_call am)
  else
    VA.State (AE.set res Vtop ae) mafter_public_call.

Inductive builtin_kind : Type :=
  | Builtin_vload (chunk: memory_chunk) (aaddr: aval)
  | Builtin_vstore (chunk: memory_chunk) (aaddr av: aval)
  | Builtin_memcpy (sz al: Z) (adst asrc: aval)
  | Builtin_annot
  | Builtin_annot_val (av: aval)
  | Builtin_default.

Definition classify_builtin (ef: external_function) (args: list reg) (ae: aenv) :=
  match ef, args with
  | EF_vload chunk, a1::nil => Builtin_vload chunk (areg ae a1)
  | EF_vload_global chunk id ofs, nil => Builtin_vload chunk (Ptr (Gl id ofs))
  | EF_vstore chunk, a1::a2::nil => Builtin_vstore chunk (areg ae a1) (areg ae a2)
  | EF_vstore_global chunk id ofs, a1::nil => Builtin_vstore chunk (Ptr (Gl id ofs)) (areg ae a1)
  | EF_memcpy sz al, a1::a2::nil => Builtin_memcpy sz al (areg ae a1) (areg ae a2)
  | EF_annot _ _, _ => Builtin_annot
  | EF_annot_val _ _, a1::nil => Builtin_annot_val (areg ae a1)
  | _, _ => Builtin_default
  end.

Definition transfer_builtin (ae: aenv) (am: amem) (rm: romem) (ef: external_function) (args: list reg) (res: reg) :=
  match classify_builtin ef args ae with
  | Builtin_vload chunk aaddr => 
      let a :=
        if strict
        then vlub (loadv chunk rm am aaddr) (vnormalize chunk (Ifptr Glob))
        else vnormalize chunk Vtop in
      VA.State (AE.set res a ae) am
  | Builtin_vstore chunk aaddr av =>
      let am' := storev chunk am aaddr av in
      VA.State (AE.set res itop ae) (mlub am am')
  | Builtin_memcpy sz al adst asrc =>
      let p := loadbytes am rm (aptr_of_aval asrc) in
      let am' := storebytes am (aptr_of_aval adst) sz p in
      VA.State (AE.set res itop ae) am'
  | Builtin_annot =>
      VA.State (AE.set res itop ae) am
  | Builtin_annot_val av =>
      VA.State (AE.set res av ae) am
  | Builtin_default =>
      transfer_call ae am args res
  end.

Definition transfer (f: function) (rm: romem) (pc: node) (ae: aenv) (am: amem) : VA.t :=
  match f.(fn_code)!pc with
  | None =>
      VA.Bot
  | Some(Inop s) =>
      VA.State ae am
  | Some(Iop op args res s) =>
      let a := eval_static_operation op (aregs ae args) in
      VA.State (AE.set res a ae) am
  | Some(Iload chunk addr args dst s) =>
      let a := loadv chunk rm am (eval_static_addressing addr (aregs ae args)) in
      VA.State (AE.set dst a ae) am
  | Some(Istore chunk addr args src s) =>
      let am' := storev chunk am (eval_static_addressing addr (aregs ae args)) (areg ae src) in
      VA.State ae am'
  | Some(Icall sig ros args res s) =>
      transfer_call ae am args res
  | Some(Itailcall sig ros args) =>
      VA.Bot
  | Some(Ibuiltin ef args res s) =>
      transfer_builtin ae am rm ef args res
  | Some(Icond cond args s1 s2) =>
      VA.State ae am
  | Some(Ijumptable arg tbl) =>
      VA.State ae am
  | Some(Ireturn arg) =>
      VA.Bot
  end.

Definition transfer' (f: function) (lastuses: PTree.t (list reg)) (rm: romem)
                     (pc: node) (before: VA.t) : VA.t :=
  match before with
  | VA.Bot => VA.Bot
  | VA.State ae am =>
      match transfer f rm pc ae am with
      | VA.Bot => VA.Bot
      | VA.State ae' am' =>
          let ae'' :=
            match lastuses!pc with
            | None => ae'
            | Some regs => eforget regs ae'
            end in
          VA.State ae'' am'
     end
  end.

Module DS := Dataflow_Solver(VA)(NodeSetForward).

Definition mfunction_entry :=
  {| am_stack := ablock_init Pbot;
     am_glob := PTree.empty _;
     am_nonstack := Nonstack;
     am_top := Nonstack |}.

Definition analyze (rm: romem) (f: function): PMap.t VA.t :=
  let lu := Liveness.last_uses f in
  let entry := VA.State (einit_regs f.(fn_params)) mfunction_entry in
  match DS.fixpoint f.(fn_code) successors_instr (transfer' f lu rm)
                    f.(fn_entrypoint) entry with
  | None => PMap.init (VA.State AE.top mtop)
  | Some res => res
  end.

(** Constructing the approximation of read-only globals *)

Definition store_init_data (ab: ablock) (p: Z) (id: init_data) : ablock :=
  match id with
  | Init_int8 n => ablock_store Mint8unsigned ab p (I n)
  | Init_int16 n => ablock_store Mint16unsigned ab p (I n)
  | Init_int32 n => ablock_store Mint32 ab p (I n)
  | Init_int64 n => ablock_store Mint64 ab p (L n)
  | Init_float32 n => ablock_store Mfloat32 ab p
                        (if propagate_float_constants tt then F n else ftop)
  | Init_float64 n => ablock_store Mfloat64 ab p
                        (if propagate_float_constants tt then F n else ftop)
  | Init_addrof symb ofs => ablock_store Mint32 ab p (Ptr (Gl symb ofs))
  | Init_space n => ab
  end.

Fixpoint store_init_data_list (ab: ablock) (p: Z) (idl: list init_data)
                              {struct idl}: ablock :=
  match idl with
  | nil => ab
  | id :: idl' => store_init_data_list (store_init_data ab p id) (p + Genv.init_data_size id) idl'
  end.

Definition alloc_global (rm: romem) (idg: ident * globdef fundef unit): romem :=
  match idg with
  | (id, Gfun f) => 
      PTree.remove id rm
  | (id, Gvar v) =>
      if v.(gvar_readonly) && negb v.(gvar_volatile)
      then PTree.set id (store_init_data_list (ablock_init Pbot) 0 v.(gvar_init)) rm
      else PTree.remove id rm
  end.

Definition romem_for_program (p: program) : romem :=
  List.fold_left alloc_global p.(prog_defs) (PTree.empty _).

(** * Soundness proof *)

(** Properties of the dataflow solution. *)

Lemma analyze_entrypoint:
  forall rm f vl m bc,
  (forall v, In v vl -> vmatch bc v (Ifptr Nonstack)) ->
  mmatch bc m mfunction_entry ->
  exists ae am,
     (analyze rm f)!!(fn_entrypoint f) = VA.State ae am
  /\ ematch bc (init_regs vl (fn_params f)) ae
  /\ mmatch bc m am.
Proof.
  intros. 
  unfold analyze. 
  set (lu := Liveness.last_uses f).
  set (entry := VA.State (einit_regs f.(fn_params)) mfunction_entry).
  destruct (DS.fixpoint (fn_code f) successors_instr (transfer' f lu rm)
                        (fn_entrypoint f) entry) as [res|] eqn:FIX.
- assert (A: VA.ge res!!(fn_entrypoint f) entry) by (eapply DS.fixpoint_entry; eauto).
  destruct (res!!(fn_entrypoint f)) as [ | ae am ]; simpl in A. contradiction.
  destruct A as [A1 A2]. 
  exists ae, am. 
  split. auto. 
  split. eapply ematch_ge; eauto. apply ematch_init; auto. 
  auto.
- exists AE.top, mtop.
  split. apply PMap.gi. 
  split. apply ematch_ge with (einit_regs (fn_params f)). 
  apply ematch_init; auto. apply AE.ge_top. 
  eapply mmatch_top'; eauto. 
Qed.
  
Lemma analyze_successor:
  forall f n ae am instr s rm ae' am',
  (analyze rm f)!!n = VA.State ae am ->
  f.(fn_code)!n = Some instr ->
  In s (successors_instr instr) ->
  transfer f rm n ae am = VA.State ae' am' ->
  VA.ge (analyze rm f)!!s (transfer f rm n ae am).
Proof.
  unfold analyze; intros.
  set (lu := Liveness.last_uses f) in *.
  set (entry := VA.State (einit_regs f.(fn_params)) mfunction_entry) in *.
  destruct (DS.fixpoint (fn_code f) successors_instr (transfer' f lu rm)
                        (fn_entrypoint f) entry) as [res|] eqn:FIX.
- assert (A: VA.ge res!!s (transfer' f lu rm n res#n)).
  { eapply DS.fixpoint_solution; eauto with coqlib.
    intros. unfold transfer'. simpl. auto. }
  rewrite H in A. unfold transfer' in A. rewrite H2 in A. rewrite H2.  
  destruct lu!n.
  eapply VA.ge_trans. eauto. split; auto. apply eforget_ge. 
  auto.
- rewrite H2. rewrite PMap.gi. split; intros. apply AE.ge_top. eapply mmatch_top'; eauto.
Qed.

Lemma analyze_succ:
  forall e m rm f n ae am instr s ae' am' bc,
  (analyze rm f)!!n = VA.State ae am ->
  f.(fn_code)!n = Some instr ->
  In s (successors_instr instr) ->
  transfer f rm n ae am = VA.State ae' am' ->
  ematch bc e ae' ->
  mmatch bc m am' ->
  exists ae'' am'',
     (analyze rm f)!!s = VA.State ae'' am''
  /\ ematch bc e ae''
  /\ mmatch bc m am''.
Proof.
  intros. exploit analyze_successor; eauto. rewrite H2. 
  destruct (analyze rm f)#s as [ | ae'' am'']; simpl; try tauto. intros [A B].
  exists ae'', am''.
  split. auto. 
  split. eapply ematch_ge; eauto. eauto. 
Qed.

(** Classification of builtin functions *)

Lemma classify_builtin_sound:
  forall bc e ae ef (ge: genv) args m t res m',
  ematch bc e ae ->
  genv_match bc ge ->
  external_call ef ge e##args m t res m' ->
  match classify_builtin ef args ae with
  | Builtin_vload chunk aaddr =>
      exists addr,
      volatile_load_sem chunk ge (addr::nil) m t res m' /\ vmatch bc addr aaddr
  | Builtin_vstore chunk aaddr av =>
      exists addr v,
      volatile_store_sem chunk ge (addr::v::nil) m t res m'
      /\ vmatch bc addr aaddr /\ vmatch bc v av
  | Builtin_memcpy sz al adst asrc =>
      exists dst, exists src,
      extcall_memcpy_sem sz al ge (dst::src::nil) m t res m'
      /\ vmatch bc dst adst /\ vmatch bc src asrc
  | Builtin_annot => m' = m /\ res = Vundef
  | Builtin_annot_val av => m' = m /\ vmatch bc res av
  | Builtin_default => True
  end.
Proof.
  intros. unfold classify_builtin; destruct ef; auto.
- (* vload *)
  destruct args; auto. destruct args; auto.
  exists (e#p); split; eauto.
- (* vstore *)
  destruct args; auto. destruct args; auto. destruct args; auto.
  exists (e#p), (e#p0); eauto.
- (* vload global *)
  destruct args; auto. simpl in H1. 
  rewrite volatile_load_global_charact in H1. destruct H1 as (b & A & B).
  exists (Vptr b ofs); split; auto. constructor. constructor. eapply H0; eauto.
- (* vstore global *)
  destruct args; auto. destruct args; auto. simpl in H1. 
  rewrite volatile_store_global_charact in H1. destruct H1 as (b & A & B).
  exists (Vptr b ofs), (e#p); split; auto. split; eauto. constructor. constructor. eapply H0; eauto.
- (* memcpy *)
  destruct args; auto. destruct args; auto. destruct args; auto.
  exists (e#p), (e#p0); eauto.
- (* annot *)
  simpl in H1. inv H1. auto.
- (* annot val *)
  destruct args; auto. destruct args; auto.
  simpl in H1. inv H1. eauto.
Qed.

(** ** Constructing block classifications *)

Definition bc_nostack (bc: block_classification) : Prop :=
  forall b, bc b <> BCstack.

Section NOSTACK.

Variable bc: block_classification.
Hypothesis NOSTACK: bc_nostack bc.

Lemma pmatch_no_stack: forall b ofs p, pmatch bc b ofs p -> pmatch bc b ofs Nonstack.
Proof.
  intros. inv H; constructor; congruence.
Qed.

Lemma vmatch_no_stack: forall v x, vmatch bc v x -> vmatch bc v (Ifptr Nonstack).
Proof.
  induction 1; constructor; auto; eapply pmatch_no_stack; eauto. 
Qed.

Lemma smatch_no_stack: forall m b p, smatch bc m b p -> smatch bc m b Nonstack.
Proof.
  intros. destruct H as [A B]. split; intros. 
  eapply vmatch_no_stack; eauto. 
  eapply pmatch_no_stack; eauto. 
Qed.

Lemma mmatch_no_stack: forall m am astk,
  mmatch bc m am -> mmatch bc m {| am_stack := astk; am_glob := PTree.empty _; am_nonstack := Nonstack; am_top := Nonstack |}.
Proof.
  intros. destruct H. constructor; simpl; intros.
- elim (NOSTACK b); auto. 
- rewrite PTree.gempty in H0; discriminate.
- eapply smatch_no_stack; eauto. 
- eapply smatch_no_stack; eauto. 
- auto.
Qed.

End NOSTACK.

(** ** Construction 1: allocating the stack frame at function entry *)

Ltac splitall := repeat (match goal with |- _ /\ _ => split end).

Theorem allocate_stack:
  forall m sz m' sp bc ge rm am,
  Mem.alloc m 0 sz = (m', sp) ->
  genv_match bc ge ->
  romatch bc m rm ->
  mmatch bc m am ->
  bc_nostack bc ->
  exists bc',
     bc_incr bc bc'
  /\ bc' sp = BCstack
  /\ genv_match bc' ge
  /\ romatch bc' m' rm
  /\ mmatch bc' m' mfunction_entry
  /\ (forall b, Plt b sp -> bc' b = bc b)
  /\ (forall v x, vmatch bc v x -> vmatch bc' v (Ifptr Nonstack)).
Proof.
  intros until am; intros ALLOC GENV RO MM NOSTACK. 
  exploit Mem.nextblock_alloc; eauto. intros NB. 
  exploit Mem.alloc_result; eauto. intros SP.
  assert (SPINVALID: bc sp = BCinvalid).
  { rewrite SP. eapply bc_below_invalid. apply Plt_strict. eapply mmatch_below; eauto. }
(* Part 1: constructing bc' *)
  set (f := fun b => if eq_block b sp then BCstack else bc b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> b = sp).
    { unfold f; intros. destruct (eq_block b sp); auto. eelim NOSTACK; eauto. }
    intros. transitivity sp; auto. symmetry; auto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> bc b = BCglob id).
    { unfold f; intros. destruct (eq_block b sp). congruence. auto. }
    intros. eapply (bc_glob bc); eauto. 
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.
  assert (BC'EQ: forall b, bc b <> BCinvalid -> bc' b = bc b).
  { intros; simpl. apply dec_eq_false. congruence. }
  assert (INCR: bc_incr bc bc').
  { red; simpl; intros. apply BC'EQ; auto. }
(* Part 2: invariance properties *)
  assert (SM: forall b p, bc b <> BCinvalid -> smatch bc m b p -> smatch bc' m' b Nonstack).
  {
    intros. 
    apply smatch_incr with bc; auto.
    apply smatch_inv with m. 
    apply smatch_no_stack with p; auto.
    intros. eapply Mem.loadbytes_alloc_unchanged; eauto. eapply mmatch_below; eauto. 
  }
  assert (SMSTACK: smatch bc' m' sp Pbot).
  {
    split; intros. 
    exploit Mem.load_alloc_same; eauto. intros EQ. subst v. constructor.
    exploit Mem.loadbytes_alloc_same; eauto with coqlib. congruence.
  }
(* Conclusions *)
  exists bc'; splitall.
- (* incr *)
  assumption.
- (* sp is BCstack *)
  simpl; apply dec_eq_true. 
- (* genv match *)
  eapply genv_match_exten; eauto.
  simpl; intros. destruct (eq_block b sp); intuition congruence.
  simpl; intros. destruct (eq_block b sp); congruence. 
- (* romatch *)
  apply romatch_exten with bc. 
  eapply romatch_alloc; eauto. eapply mmatch_below; eauto. 
  simpl; intros. destruct (eq_block b sp); intuition. 
- (* mmatch *)
  constructor; simpl; intros.
  + (* stack *)
    apply ablock_init_sound. destruct (eq_block b sp).
    subst b. apply SMSTACK.
    elim (NOSTACK b); auto.
  + (* globals *)
    rewrite PTree.gempty in H0; discriminate.
  + (* nonstack *)
    destruct (eq_block b sp). congruence. eapply SM; auto. eapply mmatch_nonstack; eauto.
  + (* top *)
    destruct (eq_block b sp).
    subst b. apply smatch_ge with Pbot. apply SMSTACK. constructor.  
    eapply SM; auto. eapply mmatch_top; eauto.
  + (* below *)
    red; simpl; intros. rewrite NB. destruct (eq_block b sp). 
    subst b; rewrite SP; xomega. 
    exploit mmatch_below; eauto. xomega. 
- (* unchanged *)
  simpl; intros. apply dec_eq_false. apply Plt_ne. auto.
- (* values *)
  intros. apply vmatch_incr with bc; auto. eapply vmatch_no_stack; eauto. 
Qed.

(** Construction 2: turn the stack into an "other" block, at public calls or function returns *)

Theorem anonymize_stack:
  forall m sp bc ge rm am,
  genv_match bc ge ->
  romatch bc m rm ->
  mmatch bc m am ->
  bc sp = BCstack ->
  exists bc',
     bc_nostack bc'
  /\ bc' sp = BCother
  /\ (forall b, b <> sp -> bc' b = bc b)
  /\ (forall v x, vmatch bc v x -> vmatch bc' v Vtop)
  /\ genv_match bc' ge
  /\ romatch bc' m rm
  /\ mmatch bc' m mtop.
Proof.
  intros until am; intros GENV RO MM SP.
(* Part 1: constructing bc' *)
  set (f := fun b => if eq_block b sp then BCother else bc b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    unfold f; intros.
    destruct (eq_block b1 sp); try discriminate.
    destruct (eq_block b2 sp); try discriminate. 
    eapply bc_stack; eauto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    unfold f; intros.
    destruct (eq_block b1 sp); try discriminate.
    destruct (eq_block b2 sp); try discriminate. 
    eapply bc_glob; eauto. 
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.

(* Part 2: matching wrt bc' *)
  assert (PM: forall b ofs p, pmatch bc b ofs p -> pmatch bc' b ofs Ptop).
  {
    intros. assert (pmatch bc b ofs Ptop) by (eapply pmatch_top'; eauto).
    inv H0. constructor; simpl. destruct (eq_block b sp); congruence. 
  }
  assert (VM: forall v x, vmatch bc v x -> vmatch bc' v Vtop).
  {
    induction 1; constructor; eauto.
  }
  assert (SM: forall b p, smatch bc m b p -> smatch bc' m b Ptop).
  {
    intros. destruct H as [S1 S2]. split; intros.
    eapply VM. eapply S1; eauto.
    eapply PM. eapply S2; eauto.
  }
(* Conclusions *)
  exists bc'; splitall.
- (* nostack *)
  red; simpl; intros. destruct (eq_block b sp). congruence. 
  red; intros. elim n. eapply bc_stack; eauto. 
- (* bc' sp is BCother *)
  simpl; apply dec_eq_true. 
- (* other blocks *)
  intros; simpl; apply dec_eq_false; auto. 
- (* values *)
  auto.
- (* genv *)
  apply genv_match_exten with bc; auto. 
  simpl; intros. destruct (eq_block b sp); intuition congruence.
  simpl; intros. destruct (eq_block b sp); auto.
- (* romatch *)
  apply romatch_exten with bc; auto. 
  simpl; intros. destruct (eq_block b sp); intuition. 
- (* mmatch top *)
  constructor; simpl; intros. 
  + destruct (eq_block b sp). congruence. elim n. eapply bc_stack; eauto.
  + rewrite PTree.gempty in H0; discriminate.
  + destruct (eq_block b sp).
    subst b. eapply SM. eapply mmatch_stack; eauto.
    eapply SM. eapply mmatch_nonstack; eauto. 
  + destruct (eq_block b sp).
    subst b. eapply SM. eapply mmatch_stack; eauto.
    eapply SM. eapply mmatch_top; eauto.
  + red; simpl; intros. destruct (eq_block b sp). 
    subst b. eapply mmatch_below; eauto. congruence.
    eapply mmatch_below; eauto.
Qed.

(** Construction 3: turn the stack into an invalid block, at private calls *)

Theorem hide_stack:
  forall m sp bc ge rm am,
  genv_match bc ge ->
  romatch bc m rm ->
  mmatch bc m am ->
  bc sp = BCstack ->
  pge Nonstack am.(am_nonstack) ->
  exists bc',
     bc_nostack bc'
  /\ bc' sp = BCinvalid
  /\ (forall b, b <> sp -> bc' b = bc b)
  /\ (forall v x, vge (Ifptr Nonstack) x -> vmatch bc v x -> vmatch bc' v Vtop)
  /\ genv_match bc' ge
  /\ romatch bc' m rm
  /\ mmatch bc' m mtop.
Proof.
  intros until am; intros GENV RO MM SP NOLEAK.
(* Part 1: constructing bc' *)
  set (f := fun b => if eq_block b sp then BCinvalid else bc b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    unfold f; intros.
    destruct (eq_block b1 sp); try discriminate.
    destruct (eq_block b2 sp); try discriminate. 
    eapply bc_stack; eauto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    unfold f; intros.
    destruct (eq_block b1 sp); try discriminate.
    destruct (eq_block b2 sp); try discriminate. 
    eapply bc_glob; eauto. 
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.

(* Part 2: matching wrt bc' *)
  assert (PM: forall b ofs p, pge Nonstack p -> pmatch bc b ofs p -> pmatch bc' b ofs Ptop).
  {
    intros. assert (pmatch bc b ofs Nonstack) by (eapply pmatch_ge; eauto).
    inv H1. constructor; simpl; destruct (eq_block b sp); congruence. 
  }
  assert (VM: forall v x, vge (Ifptr Nonstack) x -> vmatch bc v x -> vmatch bc' v Vtop).
  {
    intros. apply vmatch_ifptr; intros. subst v. 
    inv H0; inv H; eapply PM; eauto.
  }
  assert (SM: forall b p, pge Nonstack p -> smatch bc m b p -> smatch bc' m b Ptop).
  {
    intros. destruct H0 as [S1 S2]. split; intros.
    eapply VM with (x := Ifptr p). constructor; auto. eapply S1; eauto.
    eapply PM. eauto. eapply S2; eauto.
  }
(* Conclusions *)
  exists bc'; splitall.
- (* nostack *)
  red; simpl; intros. destruct (eq_block b sp). congruence. 
  red; intros. elim n. eapply bc_stack; eauto. 
- (* bc' sp is BCinvalid *)
  simpl; apply dec_eq_true. 
- (* other blocks *)
  intros; simpl; apply dec_eq_false; auto. 
- (* values *)
  auto.
- (* genv *)
  apply genv_match_exten with bc; auto. 
  simpl; intros. destruct (eq_block b sp); intuition congruence.
  simpl; intros. destruct (eq_block b sp); congruence.
- (* romatch *)
  apply romatch_exten with bc; auto. 
  simpl; intros. destruct (eq_block b sp); intuition. 
- (* mmatch top *)
  constructor; simpl; intros. 
  + destruct (eq_block b sp). congruence. elim n. eapply bc_stack; eauto.
  + rewrite PTree.gempty in H0; discriminate.
  + destruct (eq_block b sp). congruence.
    eapply SM. eauto. eapply mmatch_nonstack; eauto. 
  + destruct (eq_block b sp). congruence.
    eapply SM. eauto. eapply mmatch_nonstack; eauto. 
    red; intros; elim n. eapply bc_stack; eauto. 
  + red; simpl; intros. destruct (eq_block b sp). congruence. 
    eapply mmatch_below; eauto.
Qed.

(** Construction 4: restore the stack after a public call *)

Theorem return_from_public_call:
  forall (caller callee: block_classification) bound sp ge e ae v m rm,
  bc_below caller bound ->
  callee sp = BCother ->
  caller sp = BCstack ->
  (forall b, Plt b bound -> b <> sp -> caller b = callee b) ->
  genv_match caller ge ->
  ematch caller e ae ->
  Ple bound (Mem.nextblock m) ->
  vmatch callee v Vtop ->
  romatch callee m rm ->
  mmatch callee m mtop ->
  genv_match callee ge ->
  bc_nostack callee ->
  exists bc,
      vmatch bc v Vtop
   /\ ematch bc e ae
   /\ romatch bc m rm
   /\ mmatch bc m mafter_public_call
   /\ genv_match bc ge
   /\ bc sp = BCstack
   /\ (forall b, Plt b sp -> bc b = caller b).
Proof.
  intros until rm; intros BELOW SP1 SP2 SAME GE1 EM BOUND RESM RM MM GE2 NOSTACK.
(* Constructing bc *)
  set (f := fun b => if eq_block b sp then BCstack else callee b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> b = sp).
    { unfold f; intros. destruct (eq_block b sp); auto. eelim NOSTACK; eauto. }
    intros. transitivity sp; auto. symmetry; auto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> callee b = BCglob id).
    { unfold f; intros. destruct (eq_block b sp). congruence. auto. }
    intros. eapply (bc_glob callee); eauto. 
  }
  set (bc := BC f F_stack F_glob). unfold f in bc.
  assert (INCR: bc_incr caller bc).
  {
    red; simpl; intros. destruct (eq_block b sp). congruence. 
    symmetry; apply SAME; auto. 
  }
(* Invariance properties *)
  assert (PM: forall b ofs p, pmatch callee b ofs p -> pmatch bc b ofs Ptop).  
  {
    intros. assert (pmatch callee b ofs Ptop) by (eapply pmatch_top'; eauto).
    inv H0. constructor; simpl. destruct (eq_block b sp); congruence.
  }
  assert (VM: forall v x, vmatch callee v x -> vmatch bc v Vtop).
  {
    intros. assert (vmatch callee v0 Vtop) by (eapply vmatch_top; eauto). 
    inv H0; constructor; eauto.
  }
  assert (SM: forall b p, smatch callee m b p -> smatch bc m b Ptop).
  {
    intros. destruct H; split; intros. eapply VM; eauto. eapply PM; eauto.
  }
(* Conclusions *)
  exists bc; splitall.
- (* result value *)
  eapply VM; eauto.
- (* environment *)
  eapply ematch_incr; eauto. 
- (* romem *)
  apply romatch_exten with callee; auto.
  intros; simpl. destruct (eq_block b sp); intuition. 
- (* mmatch *)
  constructor; simpl; intros.
  + (* stack *)
    apply ablock_init_sound. destruct (eq_block b sp).
    subst b. eapply SM. eapply mmatch_nonstack; eauto. congruence. 
    elim (NOSTACK b); auto.
  + (* globals *)
    rewrite PTree.gempty in H0; discriminate.
  + (* nonstack *)
    destruct (eq_block b sp). congruence. eapply SM; auto. eapply mmatch_nonstack; eauto.
  + (* top *)
    eapply SM. eapply mmatch_top; eauto. 
    destruct (eq_block b sp); congruence.
  + (* below *)
    red; simpl; intros. destruct (eq_block b sp). 
    subst b. eapply mmatch_below; eauto. congruence.
    eapply mmatch_below; eauto.
- (* genv *)
  eapply genv_match_exten with caller; eauto.
  simpl; intros. destruct (eq_block b sp). intuition congruence. 
  split; intros. rewrite SAME in H by eauto with va. auto.
  apply <- (proj1 GE2) in H. apply (proj1 GE1) in H. auto.
  simpl; intros. destruct (eq_block b sp). congruence. 
  rewrite <- SAME; eauto with va.
- (* sp *)
  simpl. apply dec_eq_true.
- (* unchanged *)
  simpl; intros. destruct (eq_block b sp). congruence. 
  symmetry. apply SAME; auto. eapply Plt_trans. eauto. apply BELOW. congruence.
Qed.

(** Construction 5: restore the stack after a private call *)

Theorem return_from_private_call:
  forall (caller callee: block_classification) bound sp ge e ae v m rm am,
  bc_below caller bound ->
  callee sp = BCinvalid ->
  caller sp = BCstack ->
  (forall b, Plt b bound -> b <> sp -> caller b = callee b) ->
  genv_match caller ge ->
  ematch caller e ae ->
  bmatch caller m sp am.(am_stack) ->
  Ple bound (Mem.nextblock m) ->
  vmatch callee v Vtop ->
  romatch callee m rm ->
  mmatch callee m mtop ->
  genv_match callee ge ->
  bc_nostack callee ->
  exists bc,
      vmatch bc v (Ifptr Nonstack)
   /\ ematch bc e ae
   /\ romatch bc m rm
   /\ mmatch bc m (mafter_private_call am)
   /\ genv_match bc ge
   /\ bc sp = BCstack
   /\ (forall b, Plt b sp -> bc b = caller b).
Proof.
  intros until am; intros BELOW SP1 SP2 SAME GE1 EM CONTENTS BOUND RESM RM MM GE2 NOSTACK.
(* Constructing bc *)
  set (f := fun b => if eq_block b sp then BCstack else callee b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> b = sp).
    { unfold f; intros. destruct (eq_block b sp); auto. eelim NOSTACK; eauto. }
    intros. transitivity sp; auto. symmetry; auto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> callee b = BCglob id).
    { unfold f; intros. destruct (eq_block b sp). congruence. auto. }
    intros. eapply (bc_glob callee); eauto. 
  }
  set (bc := BC f F_stack F_glob). unfold f in bc.
  assert (INCR1: bc_incr caller bc).
  {
    red; simpl; intros. destruct (eq_block b sp). congruence. 
    symmetry; apply SAME; auto. 
  }
  assert (INCR2: bc_incr callee bc).
  {
    red; simpl; intros. destruct (eq_block b sp). congruence. auto.
  }

(* Invariance properties *)
  assert (PM: forall b ofs p, pmatch callee b ofs p -> pmatch bc b ofs Nonstack).  
  {
    intros. assert (pmatch callee b ofs Ptop) by (eapply pmatch_top'; eauto).
    inv H0. constructor; simpl; destruct (eq_block b sp); congruence.
  }
  assert (VM: forall v x, vmatch callee v x -> vmatch bc v (Ifptr Nonstack)).
  {
    intros. assert (vmatch callee v0 Vtop) by (eapply vmatch_top; eauto). 
    inv H0; constructor; eauto.
  }
  assert (SM: forall b p, smatch callee m b p -> smatch bc m b Nonstack).
  {
    intros. destruct H; split; intros. eapply VM; eauto. eapply PM; eauto.
  }
  assert (BSTK: bmatch bc m sp (am_stack am)).
  {
    apply bmatch_incr with caller; eauto. 
  }
(* Conclusions *)
  exists bc; splitall.
- (* result value *)
  eapply VM; eauto.
- (* environment *)
  eapply ematch_incr; eauto. 
- (* romem *)
  apply romatch_exten with callee; auto.
  intros; simpl. destruct (eq_block b sp); intuition. 
- (* mmatch *)
  constructor; simpl; intros.
  + (* stack *)
    destruct (eq_block b sp). 
    subst b. exact BSTK.
    elim (NOSTACK b); auto.
  + (* globals *)
    rewrite PTree.gempty in H0; discriminate.
  + (* nonstack *)
    destruct (eq_block b sp). congruence. eapply SM; auto. eapply mmatch_nonstack; eauto.
  + (* top *)
    destruct (eq_block b sp). 
    subst. apply smatch_ge with (ab_summary (am_stack am)). apply BSTK. apply pge_lub_l. 
    apply smatch_ge with Nonstack. eapply SM. eapply mmatch_top; eauto. apply pge_lub_r.
  + (* below *)
    red; simpl; intros. destruct (eq_block b sp). 
    subst b. apply Plt_le_trans with bound. apply BELOW. congruence. auto. 
    eapply mmatch_below; eauto.
- (* genv *)
  eapply genv_match_exten; eauto.
  simpl; intros. destruct (eq_block b sp); intuition congruence.
  simpl; intros. destruct (eq_block b sp); congruence.
- (* sp *)
  simpl. apply dec_eq_true.
- (* unchanged *)
  simpl; intros. destruct (eq_block b sp). congruence. 
  symmetry. apply SAME; auto. eapply Plt_trans. eauto. apply BELOW. congruence.
Qed.

(** Construction 6: external call *)

Theorem external_call_match:
  forall ef (ge: genv) vargs m t vres m' bc rm am,
  external_call ef ge vargs m t vres m' ->
  genv_match bc ge ->
  (forall v, In v vargs -> vmatch bc v Vtop) ->
  romatch bc m rm ->
  mmatch bc m am ->
  bc_nostack bc ->
  exists bc',
     bc_incr bc bc'
  /\ (forall b, Plt b (Mem.nextblock m) -> bc' b = bc b)
  /\ vmatch bc' vres Vtop
  /\ genv_match bc' ge
  /\ romatch bc' m' rm
  /\ mmatch bc' m' mtop
  /\ bc_nostack bc'
  /\ (forall b ofs n, Mem.valid_block m b -> bc b = BCinvalid -> Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n).
Proof.
  intros until am; intros EC GENV ARGS RO MM NOSTACK.
  (* Part 1: using ec_mem_inject *)
  exploit (@external_call_mem_inject ef _ _ ge vargs m t vres m' (inj_of_bc bc) m vargs).
  apply inj_of_bc_preserves_globals; auto. 
  exact EC.
  eapply mmatch_inj; eauto. eapply mmatch_below; eauto.
  revert ARGS. generalize vargs. 
  induction vargs0; simpl; intros; constructor.
  eapply vmatch_inj; eauto. auto. 
  intros (j' & vres' & m'' & EC' & IRES & IMEM & UNCH1 & UNCH2 & IINCR & ISEP).
  assert (JBELOW: forall b, Plt b (Mem.nextblock m) -> j' b = inj_of_bc bc b).
  {
    intros. destruct (inj_of_bc bc b) as [[b' delta] | ] eqn:EQ.
    eapply IINCR; eauto. 
    destruct (j' b) as [[b'' delta'] | ] eqn:EQ'; auto.
    exploit ISEP; eauto. tauto. 
  }
  (* Part 2: constructing bc' from j' *)
  set (f := fun b => if plt b (Mem.nextblock m)
                     then bc b
                     else match j' b with None => BCinvalid | Some _ => BCother end).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> bc b = BCstack).
    { unfold f; intros. destruct (plt b (Mem.nextblock m)); auto. destruct (j' b); discriminate. }
    intros. apply (bc_stack bc); auto. 
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> bc b = BCglob id).
    { unfold f; intros. destruct (plt b (Mem.nextblock m)); auto. destruct (j' b); discriminate. }
    intros. eapply (bc_glob bc); eauto. 
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.
  assert (INCR: bc_incr bc bc').
  {
    red; simpl; intros. apply pred_dec_true. eapply mmatch_below; eauto.
  }
  assert (BC'INV: forall b, bc' b <> BCinvalid -> exists b' delta, j' b = Some(b', delta)).
  {
    simpl; intros. destruct (plt b (Mem.nextblock m)). 
    exists b, 0. rewrite JBELOW by auto. apply inj_of_bc_valid; auto.
    destruct (j' b) as [[b' delta] | ]. 
    exists b', delta; auto. 
    congruence.
  }

  (* Part 3: injection wrt j' implies matching with top wrt bc' *)
  assert (PMTOP: forall b b' delta ofs, j' b = Some (b', delta) -> pmatch bc' b ofs Ptop).
  {
    intros. constructor. simpl; unfold f. 
    destruct (plt b (Mem.nextblock m)).
    rewrite JBELOW in H by auto. eapply inj_of_bc_inv; eauto. 
    rewrite H; congruence.
  }
  assert (VMTOP: forall v v', val_inject j' v v' -> vmatch bc' v Vtop).
  {
    intros. inv H; constructor. eapply PMTOP; eauto. 
  }
  assert (SMTOP: forall b, bc' b <> BCinvalid -> smatch bc' m' b Ptop).
  {
    intros; split; intros.
  - exploit BC'INV; eauto. intros (b' & delta & J'). 
    exploit Mem.load_inject. eexact IMEM. eauto. eauto. intros (v' & A & B). 
    eapply VMTOP; eauto.
  - exploit BC'INV; eauto. intros (b'' & delta & J'). 
    exploit Mem.loadbytes_inject. eexact IMEM. eauto. eauto. intros (bytes & A & B).
    inv B. inv H3. eapply PMTOP; eauto. 
  }
  (* Conclusions *)
  exists bc'; splitall.
- (* incr *)
  exact INCR.
- (* unchanged *)
  simpl; intros. apply pred_dec_true; auto.
- (* vmatch res *)
  eapply VMTOP; eauto.
- (* genv match *)
  apply genv_match_exten with bc; auto.
  simpl; intros; split; intros.
  rewrite pred_dec_true by (eapply mmatch_below; eauto with va). auto.
  destruct (plt b (Mem.nextblock m)). auto. destruct (j' b); congruence.
  simpl; intros. rewrite pred_dec_true by (eapply mmatch_below; eauto with va). auto.
- (* romatch m' *)
  red; simpl; intros. destruct (plt b (Mem.nextblock m)).
  exploit RO; eauto. intros (R & P & Q).
  split; auto.
  split. apply bmatch_incr with bc; auto. apply bmatch_inv with m; auto.
  intros. eapply Mem.loadbytes_unchanged_on_1. eapply external_call_readonly; eauto. 
  auto. intros; red. apply Q. 
  intros; red; intros; elim (Q ofs). 
  eapply external_call_max_perm with (m2 := m'); eauto.
  destruct (j' b); congruence.
- (* mmatch top *)
  constructor; simpl; intros.
  + apply ablock_init_sound. apply SMTOP. simpl; congruence. 
  + rewrite PTree.gempty in H0; discriminate.
  + apply SMTOP; auto.
  + apply SMTOP; auto. 
  + red; simpl; intros. destruct (plt b (Mem.nextblock m)). 
    eapply Plt_le_trans. eauto. eapply external_call_nextblock; eauto. 
    destruct (j' b) as [[bx deltax] | ] eqn:J'. 
    eapply Mem.valid_block_inject_1; eauto. 
    congruence.
- (* nostack *)
  red; simpl; intros. destruct (plt b (Mem.nextblock m)). 
  apply NOSTACK; auto.
  destruct (j' b); congruence.
- (* unmapped blocks are invariant *)
  intros. eapply Mem.loadbytes_unchanged_on_1; auto.
  apply UNCH1; auto. intros; red. unfold inj_of_bc; rewrite H0; auto. 
Qed.

(** ** Semantic invariant *)

Section SOUNDNESS.

Variable prog: program.

Let ge : genv := Genv.globalenv prog.

Let rm := romem_for_program prog.

Inductive sound_stack: block_classification -> list stackframe -> mem -> block -> Prop :=
  | sound_stack_nil: forall bc m bound,
      sound_stack bc nil m bound
  | sound_stack_public_call:
      forall (bc: block_classification) res f sp pc e stk m bound bc' bound' ae
        (STK: sound_stack bc' stk m sp)
        (INCR: Ple bound' bound)
        (BELOW: bc_below bc' bound')
        (SP: bc sp = BCother)
        (SP': bc' sp = BCstack)
        (SAME: forall b, Plt b bound' -> b <> sp -> bc b = bc' b)
        (GE: genv_match bc' ge)
        (AN: VA.ge (analyze rm f)!!pc (VA.State (AE.set res Vtop ae) mafter_public_call))
        (EM: ematch bc' e ae),
      sound_stack bc (Stackframe res f (Vptr sp Int.zero) pc e :: stk) m bound
  | sound_stack_private_call:
     forall (bc: block_classification) res f sp pc e stk m bound bc' bound' ae am
        (STK: sound_stack bc' stk m sp)
        (INCR: Ple bound' bound)
        (BELOW: bc_below bc' bound')
        (SP: bc sp = BCinvalid)
        (SP': bc' sp = BCstack)
        (SAME: forall b, Plt b bound' -> b <> sp -> bc b = bc' b)
        (GE: genv_match bc' ge)
        (AN: VA.ge (analyze rm f)!!pc (VA.State (AE.set res (Ifptr Nonstack) ae) (mafter_private_call am)))
        (EM: ematch bc' e ae)
        (CONTENTS: bmatch bc' m sp am.(am_stack)),
      sound_stack bc (Stackframe res f (Vptr sp Int.zero) pc e :: stk) m bound.

Inductive sound_state: state -> Prop :=
  | sound_regular_state:
      forall s f sp pc e m ae am bc
        (STK: sound_stack bc s m sp)
        (AN: (analyze rm f)!!pc = VA.State ae am)
        (EM: ematch bc e ae)
        (RO: romatch bc m rm)
        (MM: mmatch bc m am)
        (GE: genv_match bc ge)
        (SP: bc sp = BCstack),
      sound_state (State s f (Vptr sp Int.zero) pc e m)
  | sound_call_state:
      forall s fd args m bc
        (STK: sound_stack bc s m (Mem.nextblock m))
        (ARGS: forall v, In v args -> vmatch bc v Vtop)
        (RO: romatch bc m rm)
        (MM: mmatch bc m mtop)
        (GE: genv_match bc ge)
        (NOSTK: bc_nostack bc),
      sound_state (Callstate s fd args m)
  | sound_return_state:
      forall s v m bc
        (STK: sound_stack bc s m (Mem.nextblock m))
        (RES: vmatch bc v Vtop)
        (RO: romatch bc m rm)
        (MM: mmatch bc m mtop)
        (GE: genv_match bc ge)
        (NOSTK: bc_nostack bc),
      sound_state (Returnstate s v m).

(** Properties of the [sound_stack] invariant on call stacks. *)

Lemma sound_stack_ext:
  forall m' bc stk m bound,
  sound_stack bc stk m bound ->
  (forall b ofs n bytes,
       Plt b bound -> bc b = BCinvalid -> n >= 0 ->
       Mem.loadbytes m' b ofs n = Some bytes ->
       Mem.loadbytes m b ofs n = Some bytes) ->
  sound_stack bc stk m' bound.
Proof.
  induction 1; intros INV.
- constructor.
- assert (Plt sp bound') by eauto with va. 
  eapply sound_stack_public_call; eauto. apply IHsound_stack; intros.
  apply INV. xomega. rewrite SAME; auto. xomega. auto. auto.
- assert (Plt sp bound') by eauto with va. 
  eapply sound_stack_private_call; eauto. apply IHsound_stack; intros.
  apply INV. xomega. rewrite SAME; auto. xomega. auto. auto.
  apply bmatch_ext with m; auto. intros. apply INV. xomega. auto. auto. auto.
Qed.

Lemma sound_stack_inv:
  forall m' bc stk m bound,
  sound_stack bc stk m bound ->
  (forall b ofs n, Plt b bound -> bc b = BCinvalid -> n >= 0 -> Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n) ->
  sound_stack bc stk m' bound.
Proof.
  intros. eapply sound_stack_ext; eauto. intros. rewrite <- H0; auto. 
Qed.

Lemma sound_stack_storev:
  forall chunk m addr v m' bc aaddr stk bound,
  Mem.storev chunk m addr v = Some m' ->
  vmatch bc addr aaddr ->
  sound_stack bc stk m bound ->
  sound_stack bc stk m' bound.
Proof.
  intros. apply sound_stack_inv with m; auto. 
  destruct addr; simpl in H; try discriminate.
  assert (A: pmatch bc b i Ptop).
  { inv H0; eapply pmatch_top'; eauto. }
  inv A. 
  intros. eapply Mem.loadbytes_store_other; eauto. left; congruence. 
Qed. 

Lemma sound_stack_storebytes:
  forall m b ofs bytes m' bc aaddr stk bound,
  Mem.storebytes m b (Int.unsigned ofs) bytes = Some m' ->
  vmatch bc (Vptr b ofs) aaddr ->
  sound_stack bc stk m bound ->
  sound_stack bc stk m' bound.
Proof.
  intros. apply sound_stack_inv with m; auto. 
  assert (A: pmatch bc b ofs Ptop).
  { inv H0; eapply pmatch_top'; eauto. }
  inv A. 
  intros. eapply Mem.loadbytes_storebytes_other; eauto. left; congruence. 
Qed. 

Lemma sound_stack_free:
  forall m b lo hi m' bc stk bound,
  Mem.free m b lo hi = Some m' ->
  sound_stack bc stk m bound ->
  sound_stack bc stk m' bound.
Proof.
  intros. eapply sound_stack_ext; eauto. intros.
  eapply Mem.loadbytes_free_2; eauto.
Qed.

Lemma sound_stack_new_bound:
  forall bc stk m bound bound',
  sound_stack bc stk m bound ->
  Ple bound bound' ->
  sound_stack bc stk m bound'.
Proof.
  intros. inv H. 
- constructor.
- eapply sound_stack_public_call with (bound' := bound'0); eauto. xomega. 
- eapply sound_stack_private_call with (bound' := bound'0); eauto. xomega. 
Qed.

Lemma sound_stack_exten:
  forall bc stk m bound (bc1: block_classification),
  sound_stack bc stk m bound ->
  (forall b, Plt b bound -> bc1 b = bc b) ->
  sound_stack bc1 stk m bound.
Proof.
  intros. inv H. 
- constructor.
- assert (Plt sp bound') by eauto with va. 
  eapply sound_stack_public_call; eauto.
  rewrite H0; auto. xomega. 
  intros. rewrite H0; auto. xomega.
- assert (Plt sp bound') by eauto with va. 
  eapply sound_stack_private_call; eauto.
  rewrite H0; auto. xomega. 
  intros. rewrite H0; auto. xomega.
Qed.

(** ** Preservation of the semantic invariant by one step of execution *)

Lemma sound_succ_state:
  forall bc pc ae am instr ae' am'  s f sp pc' e' m',
  (analyze rm f)!!pc = VA.State ae am ->
  f.(fn_code)!pc = Some instr ->
  In pc' (successors_instr instr) ->
  transfer f rm pc ae am = VA.State ae' am' ->
  ematch bc e' ae' ->
  mmatch bc m' am' ->
  romatch bc m' rm ->
  genv_match bc ge ->
  bc sp = BCstack ->
  sound_stack bc s m' sp ->
  sound_state (State s f (Vptr sp Int.zero) pc' e' m').
Proof.
  intros. exploit analyze_succ; eauto. intros (ae'' & am'' & AN & EM & MM).
  econstructor; eauto. 
Qed.

Lemma areg_sound:
  forall bc e ae r, ematch bc e ae -> vmatch bc (e#r) (areg ae r).
Proof.
  intros. apply H. 
Qed.

Lemma aregs_sound:
  forall bc e ae rl, ematch bc e ae -> list_forall2 (vmatch bc) (e##rl) (aregs ae rl).
Proof.
  induction rl; simpl; intros. constructor. constructor; auto. apply areg_sound; auto.
Qed.

Hint Resolve areg_sound aregs_sound: va.

Theorem sound_step:
  forall st t st', RTL.step ge st t st' -> sound_state st -> sound_state st'.
Proof.
  induction 1; intros SOUND; inv SOUND.

- (* nop *)
  eapply sound_succ_state; eauto. simpl; auto. 
  unfold transfer; rewrite H. auto.

- (* op *)
  eapply sound_succ_state; eauto. simpl; auto. 
  unfold transfer; rewrite H. eauto. 
  apply ematch_update; auto. eapply eval_static_operation_sound; eauto with va.

- (* load *)
  eapply sound_succ_state; eauto. simpl; auto. 
  unfold transfer; rewrite H. eauto. 
  apply ematch_update; auto. eapply loadv_sound; eauto with va. 
  eapply eval_static_addressing_sound; eauto with va.

- (* store *)
  exploit eval_static_addressing_sound; eauto with va. intros VMADDR.
  eapply sound_succ_state; eauto. simpl; auto. 
  unfold transfer; rewrite H. eauto. 
  eapply storev_sound; eauto. 
  destruct a; simpl in H1; try discriminate. eapply romatch_store; eauto. 
  eapply sound_stack_storev; eauto. 

- (* call *)
  assert (TR: transfer f rm pc ae am = transfer_call ae am args res).
  { unfold transfer; rewrite H; auto. }
  unfold transfer_call in TR. 
  destruct (pincl (am_nonstack am) Nonstack && 
            forallb (fun r : reg => vpincl (areg ae r) Nonstack) args) eqn:NOLEAK.
+ (* private call *)
  InvBooleans.
  exploit analyze_successor; eauto. simpl; eauto. rewrite TR. intros SUCC. 
  exploit hide_stack; eauto. apply pincl_ge; auto.
  intros (bc' & A & B & C & D & E & F & G).
  apply sound_call_state with bc'; auto.
  * eapply sound_stack_private_call with (bound' := Mem.nextblock m) (bc' := bc); eauto.
    apply Ple_refl.
    eapply mmatch_below; eauto.
    eapply mmatch_stack; eauto. 
  * intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v. 
    apply D with (areg ae r). 
    rewrite forallb_forall in H2. apply vpincl_ge. apply H2; auto. auto with va.
+ (* public call *)
  exploit analyze_successor; eauto. simpl; eauto. rewrite TR. intros SUCC. 
  exploit anonymize_stack; eauto. intros (bc' & A & B & C & D & E & F & G).
  apply sound_call_state with bc'; auto.
  * eapply sound_stack_public_call with (bound' := Mem.nextblock m) (bc' := bc); eauto.
    apply Ple_refl.
    eapply mmatch_below; eauto.
  * intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v. 
    apply D with (areg ae r). auto with va.

- (* tailcall *)
  exploit anonymize_stack; eauto. intros (bc' & A & B & C & D & E & F & G).
  apply sound_call_state with bc'; auto.
  erewrite Mem.nextblock_free by eauto. 
  apply sound_stack_new_bound with stk.
  apply sound_stack_exten with bc.
  eapply sound_stack_free; eauto.
  intros. apply C. apply Plt_ne; auto.
  apply Plt_Ple. eapply mmatch_below; eauto. congruence. 
  intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v. 
  apply D with (areg ae r). auto with va.
  eapply romatch_free; eauto. 
  eapply mmatch_free; eauto. 

- (* builtin *)
  assert (SPVALID: Plt sp0 (Mem.nextblock m)) by (eapply mmatch_below; eauto with va).
  assert (TR: transfer f rm pc ae am = transfer_builtin ae am rm ef args res).
  { unfold transfer; rewrite H; auto. }
  unfold transfer_builtin in TR.
  exploit classify_builtin_sound; eauto. destruct (classify_builtin ef args ae). 
+ (* volatile load *)
  intros (addr & VLOAD & VADDR). inv VLOAD.
  eapply sound_succ_state; eauto. simpl; auto.
  apply ematch_update; auto. 
  inv H2.
  * (* true volatile access *)
    assert (V: vmatch bc v0 (Ifptr Glob)).
    { inv H4; constructor. econstructor. eapply GE; eauto. }
    destruct strict. apply vmatch_lub_r. apply vnormalize_sound. auto. 
    apply vnormalize_sound. eapply vmatch_ge; eauto. constructor. constructor.
  * (* normal memory access *)
    exploit loadv_sound; eauto. simpl; eauto. intros V.
    destruct strict. 
    apply vmatch_lub_l. auto.
    eapply vnormalize_cast; eauto. eapply vmatch_top; eauto. 
+ (* volatile store *)
  intros (addr & src & VSTORE & VADDR & VSRC). inv VSTORE. inv H7.
  * (* true volatile access *)
    eapply sound_succ_state; eauto. simpl; auto.
    apply ematch_update; auto. constructor.
    apply mmatch_lub_l; auto.
  * (* normal memory access *)
    eapply sound_succ_state; eauto. simpl; auto.
    apply ematch_update; auto. constructor.
    apply mmatch_lub_r. eapply storev_sound; eauto. auto.
    eapply romatch_store; eauto.
    eapply sound_stack_storev; eauto. simpl; eauto.
+ (* memcpy *)
  intros (dst & src & MEMCPY & VDST & VSRC). inv MEMCPY.
  eapply sound_succ_state; eauto. simpl; auto. 
  apply ematch_update; auto. constructor.
  eapply storebytes_sound; eauto. 
  apply match_aptr_of_aval; auto. 
  eapply Mem.loadbytes_length; eauto. 
  intros. eapply loadbytes_sound; eauto. apply match_aptr_of_aval; auto. 
  eapply romatch_storebytes; eauto. 
  eapply sound_stack_storebytes; eauto. 
+ (* annot *)
  intros (A & B); subst. 
  eapply sound_succ_state; eauto. simpl; auto. 
  apply ematch_update; auto. constructor.
+ (* annot val *)
  intros (A & B); subst. 
  eapply sound_succ_state; eauto. simpl; auto. 
  apply ematch_update; auto.
+ (* general case *)
  intros _.
  unfold transfer_call in TR. 
  destruct (pincl (am_nonstack am) Nonstack && 
            forallb (fun r : reg => vpincl (areg ae r) Nonstack) args) eqn:NOLEAK.
* (* private builtin call *)
  InvBooleans. rewrite forallb_forall in H2.
  exploit hide_stack; eauto. apply pincl_ge; auto.
  intros (bc1 & A & B & C & D & E & F & G).
  exploit external_call_match; eauto. 
  intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v0. 
  eapply D; eauto with va. apply vpincl_ge. apply H2; auto. 
  intros (bc2 & J & K & L & M & N & O & P & Q).
  exploit (return_from_private_call bc bc2); eauto.
  eapply mmatch_below; eauto.
  rewrite K; auto.
  intros. rewrite K; auto. rewrite C; auto.
  apply bmatch_inv with m. eapply mmatch_stack; eauto. 
  intros. apply Q; auto.
  eapply external_call_nextblock; eauto. 
  intros (bc3 & U & V & W & X & Y & Z & AA).
  eapply sound_succ_state with (bc := bc3); eauto. simpl; auto. 
  apply ematch_update; auto.
  apply sound_stack_exten with bc. 
  apply sound_stack_inv with m. auto.
  intros. apply Q. red. eapply Plt_trans; eauto.
  rewrite C; auto.
  exact AA.
* (* public builtin call *)
  exploit anonymize_stack; eauto. 
  intros (bc1 & A & B & C & D & E & F & G).
  exploit external_call_match; eauto. 
  intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v0. eapply D; eauto with va.
  intros (bc2 & J & K & L & M & N & O & P & Q).
  exploit (return_from_public_call bc bc2); eauto.
  eapply mmatch_below; eauto.
  rewrite K; auto.
  intros. rewrite K; auto. rewrite C; auto.
  eapply external_call_nextblock; eauto. 
  intros (bc3 & U & V & W & X & Y & Z & AA).
  eapply sound_succ_state with (bc := bc3); eauto. simpl; auto. 
  apply ematch_update; auto.
  apply sound_stack_exten with bc. 
  apply sound_stack_inv with m. auto.
  intros. apply Q. red. eapply Plt_trans; eauto.
  rewrite C; auto.
  exact AA.

- (* cond *)
  eapply sound_succ_state; eauto. 
  simpl. destruct b; auto. 
  unfold transfer; rewrite H; auto. 

- (* jumptable *)
  eapply sound_succ_state; eauto. 
  simpl. eapply list_nth_z_in; eauto. 
  unfold transfer; rewrite H; auto.

- (* return *)
  exploit anonymize_stack; eauto. intros (bc' & A & B & C & D & E & F & G).
  apply sound_return_state with bc'; auto.
  erewrite Mem.nextblock_free by eauto. 
  apply sound_stack_new_bound with stk.
  apply sound_stack_exten with bc.
  eapply sound_stack_free; eauto.
  intros. apply C. apply Plt_ne; auto.
  apply Plt_Ple. eapply mmatch_below; eauto with va.
  destruct or; simpl. eapply D; eauto. constructor. 
  eapply romatch_free; eauto. 
  eapply mmatch_free; eauto.

- (* internal function *)
  exploit allocate_stack; eauto. 
  intros (bc' & A & B & C & D & E & F & G).
  exploit (analyze_entrypoint rm f args m' bc'); eauto. 
  intros (ae & am & AN & EM & MM').
  econstructor; eauto. 
  erewrite Mem.alloc_result by eauto. 
  apply sound_stack_exten with bc; auto.
  apply sound_stack_inv with m; auto. 
  intros. eapply Mem.loadbytes_alloc_unchanged; eauto.
  intros. apply F. erewrite Mem.alloc_result by eauto. auto.

- (* external function *)
  exploit external_call_match; eauto with va.
  intros (bc' & A & B & C & D & E & F & G & K).
  econstructor; eauto. 
  apply sound_stack_new_bound with (Mem.nextblock m).
  apply sound_stack_exten with bc; auto.
  apply sound_stack_inv with m; auto. 
  eapply external_call_nextblock; eauto.

- (* return *)
  inv STK.
  + (* from public call *)
   exploit return_from_public_call; eauto. 
   intros; rewrite SAME; auto.
   intros (bc1 & A & B & C & D & E & F & G). 
   destruct (analyze rm f)#pc as [ |ae' am'] eqn:EQ; simpl in AN; try contradiction. destruct AN as [A1 A2].
   eapply sound_regular_state with (bc := bc1); eauto.
   apply sound_stack_exten with bc'; auto.
   eapply ematch_ge; eauto. apply ematch_update. auto. auto. 
  + (* from private call *)
   exploit return_from_private_call; eauto. 
   intros; rewrite SAME; auto.
   intros (bc1 & A & B & C & D & E & F & G). 
   destruct (analyze rm f)#pc as [ |ae' am'] eqn:EQ; simpl in AN; try contradiction. destruct AN as [A1 A2].
   eapply sound_regular_state with (bc := bc1); eauto.
   apply sound_stack_exten with bc'; auto.
   eapply ematch_ge; eauto. apply ematch_update. auto. auto.
Qed.

End SOUNDNESS.

(** ** Soundness of the initial memory abstraction *)

Section INITIAL.

Variable prog: program.

Let ge := Genv.globalenv prog.

Lemma initial_block_classification:
  forall m,
  Genv.init_mem prog = Some m ->
  exists bc,
     genv_match bc ge
  /\ bc_below bc (Mem.nextblock m)
  /\ bc_nostack bc
  /\ (forall b id, bc b = BCglob id -> Genv.find_symbol ge id = Some b)
  /\ (forall b, Mem.valid_block m b -> bc b <> BCinvalid).
Proof.
  intros. 
  set (f := fun b => 
              if plt b (Genv.genv_next ge) then
                match Genv.invert_symbol ge b with None => BCother | Some id => BCglob id end
              else
                BCinvalid).
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    unfold f; intros.
    destruct (plt b1 (Genv.genv_next ge)); try discriminate.
    destruct (Genv.invert_symbol ge b1) as [id1|] eqn:I1; inv H0.
    destruct (plt b2 (Genv.genv_next ge)); try discriminate.
    destruct (Genv.invert_symbol ge b2) as [id2|] eqn:I2; inv H1.
    exploit Genv.invert_find_symbol. eexact I1. 
    exploit Genv.invert_find_symbol. eexact I2. 
    congruence.
  }
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    unfold f; intros.
    destruct (plt b1 (Genv.genv_next ge)); try discriminate.
    destruct (Genv.invert_symbol ge b1); discriminate.
  }
  set (bc := BC f F_stack F_glob). unfold f in bc.
  exists bc; splitall.
- split; simpl; intros. 
  + split; intros.
    * rewrite pred_dec_true by (eapply Genv.genv_symb_range; eauto).
      erewrite Genv.find_invert_symbol; eauto.
    * apply Genv.invert_find_symbol. 
      destruct (plt b (Genv.genv_next ge)); try discriminate.
      destruct (Genv.invert_symbol ge b); congruence.
  + rewrite ! pred_dec_true by assumption. 
    destruct (Genv.invert_symbol); split; congruence.
- red; simpl; intros. destruct (plt b (Genv.genv_next ge)); try congruence.
  erewrite <- Genv.init_mem_genv_next by eauto. auto. 
- red; simpl; intros. 
  destruct (plt b (Genv.genv_next ge)). 
  destruct (Genv.invert_symbol ge b); congruence.
  congruence.
- simpl; intros. destruct (plt b (Genv.genv_next ge)); try discriminate.
  destruct (Genv.invert_symbol ge b) as [id' | ] eqn:IS; inv H0.
  apply Genv.invert_find_symbol; auto.
- intros; simpl. unfold ge; erewrite Genv.init_mem_genv_next by eauto.
  rewrite pred_dec_true by assumption.
  destruct (Genv.invert_symbol (Genv.globalenv prog) b); congruence.
Qed.

Section INIT.

Variable bc: block_classification.
Hypothesis GMATCH: genv_match bc ge.

Lemma store_init_data_summary:
  forall ab p id,
  pge Glob (ab_summary ab) ->
  pge Glob (ab_summary (store_init_data ab p id)).
Proof.
  intros.
  assert (DFL: forall chunk av,
               vge (Ifptr Glob) av ->
               pge Glob (ab_summary (ablock_store chunk ab p av))).
  {
    intros. simpl. unfold vplub; destruct av; auto. 
    inv H0. apply plub_least; auto.
    inv H0. apply plub_least; auto.
  }
  destruct id; auto.
  simpl. destruct (propagate_float_constants tt); auto. 
  simpl. destruct (propagate_float_constants tt); auto. 
  apply DFL. constructor. constructor.
Qed.

Lemma store_init_data_list_summary:
  forall idl ab p,
  pge Glob (ab_summary ab) ->
  pge Glob (ab_summary (store_init_data_list ab p idl)).
Proof.
  induction idl; simpl; intros. auto. apply IHidl. apply store_init_data_summary; auto. 
Qed.

Lemma store_init_data_sound:
  forall m b p id m' ab,
  Genv.store_init_data ge m b p id = Some m' ->
  bmatch bc m b ab ->
  bmatch bc m' b (store_init_data ab p id).
Proof.
  intros. destruct id; try (eapply ablock_store_sound; eauto; constructor).
  simpl. destruct (propagate_float_constants tt); eapply ablock_store_sound; eauto; constructor.
  simpl. destruct (propagate_float_constants tt); eapply ablock_store_sound; eauto; constructor.
  simpl in H. inv H. auto. 
  simpl in H. destruct (Genv.find_symbol ge i) as [b'|] eqn:FS; try discriminate.
  eapply ablock_store_sound; eauto. constructor. constructor. apply GMATCH; auto.
Qed.

Lemma store_init_data_list_sound:
  forall idl m b p m' ab,
  Genv.store_init_data_list ge m b p idl = Some m' ->
  bmatch bc m b ab ->
  bmatch bc m' b (store_init_data_list ab p idl).
Proof.
  induction idl; simpl; intros.
- inv H; auto.
- destruct (Genv.store_init_data ge m b p a) as [m1|] eqn:SI; try discriminate.
  eapply IHidl; eauto. eapply store_init_data_sound; eauto. 
Qed.

Lemma store_init_data_other:
  forall m b p id m' ab b',
  Genv.store_init_data ge m b p id = Some m' ->
  b' <> b ->
  bmatch bc m b' ab ->
  bmatch bc m' b' ab.
Proof.
  intros. eapply bmatch_inv; eauto.
  intros. destruct id; try (eapply Mem.loadbytes_store_other; eauto; fail); simpl in H.
  inv H; auto. 
  destruct (Genv.find_symbol ge i); try discriminate.
  eapply Mem.loadbytes_store_other; eauto.
Qed.

Lemma store_init_data_list_other:
  forall b b' ab idl m p m',
  Genv.store_init_data_list ge m b p idl = Some m' ->
  b' <> b ->
  bmatch bc m b' ab ->
  bmatch bc m' b' ab.
Proof.
  induction idl; simpl; intros. 
  inv H; auto.
  destruct (Genv.store_init_data ge m b p a) as [m1|] eqn:SI; try discriminate.
  eapply IHidl; eauto. eapply store_init_data_other; eauto. 
Qed.

Lemma store_zeros_same:
  forall p m b pos n m',
  store_zeros m b pos n = Some m' ->
  smatch bc m b p ->
  smatch bc m' b p.
Proof.
  intros until n. functional induction (store_zeros m b pos n); intros.
- inv H. auto.
- eapply IHo; eauto. change p with (vplub (I Int.zero) p). 
  eapply smatch_store; eauto. constructor. 
- discriminate.
Qed.

Lemma store_zeros_other:
  forall b' ab m b p n m',
  store_zeros m b p n = Some m' ->
  b' <> b ->
  bmatch bc m b' ab ->
  bmatch bc m' b' ab.
Proof.
  intros until n. functional induction (store_zeros m b p n); intros.
- inv H. auto.
- eapply IHo; eauto. eapply bmatch_inv; eauto. 
  intros. eapply Mem.loadbytes_store_other; eauto. 
- discriminate.
Qed.

Definition initial_mem_match (bc: block_classification) (m: mem) (g: genv) :=
  forall b v,
  Genv.find_var_info g b = Some v ->
  v.(gvar_volatile) = false -> v.(gvar_readonly) = true ->
  bmatch bc m b (store_init_data_list (ablock_init Pbot) 0 v.(gvar_init)).

Lemma alloc_global_match:
  forall m g idg m',
  Genv.genv_next g = Mem.nextblock m ->
  initial_mem_match bc m g ->
  Genv.alloc_global ge m idg = Some m' ->
  initial_mem_match bc m' (Genv.add_global g idg).
Proof.
  intros; red; intros. destruct idg as [id [fd | gv]]; simpl in *.
- destruct (Mem.alloc m 0 1) as [m1 b1] eqn:ALLOC. 
  unfold Genv.find_var_info, Genv.add_global in H2; simpl in H2.
  assert (Plt b (Mem.nextblock m)). 
  { rewrite <- H. eapply Genv.genv_vars_range; eauto. }
  assert (b <> b1). 
  { apply Plt_ne. erewrite Mem.alloc_result by eauto. auto. }
  apply bmatch_inv with m. 
  eapply H0; eauto. 
  intros. transitivity (Mem.loadbytes m1 b ofs n). 
  eapply Mem.loadbytes_drop; eauto. 
  eapply Mem.loadbytes_alloc_unchanged; eauto.
- set (sz := Genv.init_data_list_size (gvar_init gv)) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b1] eqn:ALLOC.
  destruct (store_zeros m1 b1 0 sz) as [m2 | ] eqn:STZ; try discriminate.
  destruct (Genv.store_init_data_list ge m2 b1 0 (gvar_init gv)) as [m3 | ] eqn:SIDL; try discriminate.
  unfold Genv.find_var_info, Genv.add_global in H2; simpl in H2.
  rewrite PTree.gsspec in H2. destruct (peq b (Genv.genv_next g)).
+ inversion H2; clear H2; subst v. 
  assert (b = b1). { erewrite Mem.alloc_result by eauto. congruence. }
  clear e. subst b. 
  apply bmatch_inv with m3. 
  eapply store_init_data_list_sound; eauto. 
  apply ablock_init_sound.
  eapply store_zeros_same; eauto. 
  split; intros. 
  exploit Mem.load_alloc_same; eauto. intros EQ; subst v; constructor. 
  exploit Mem.loadbytes_alloc_same; eauto with coqlib. congruence.
  intros. eapply Mem.loadbytes_drop; eauto. 
  right; right; right. unfold Genv.perm_globvar. rewrite H3, H4. constructor. 
+ assert (Plt b (Mem.nextblock m)). 
  { rewrite <- H. eapply Genv.genv_vars_range; eauto. }
  assert (b <> b1). 
  { apply Plt_ne. erewrite Mem.alloc_result by eauto. auto. }
  apply bmatch_inv with m3.
  eapply store_init_data_list_other; eauto. 
  eapply store_zeros_other; eauto. 
  apply bmatch_inv with m. 
  eapply H0; eauto. 
  intros. eapply Mem.loadbytes_alloc_unchanged; eauto. 
  intros. eapply Mem.loadbytes_drop; eauto.
Qed.

Lemma alloc_globals_match:
  forall gl m g m',
  Genv.genv_next g = Mem.nextblock m ->
  initial_mem_match bc m g ->
  Genv.alloc_globals ge m gl = Some m' ->
  initial_mem_match bc m' (Genv.add_globals g gl).
Proof.
  induction gl; simpl; intros. 
- inv H1; auto. 
- destruct (Genv.alloc_global ge m a) as [m1|] eqn:AG; try discriminate.
  eapply IHgl; eauto. 
  erewrite Genv.alloc_global_nextblock; eauto. simpl. congruence. 
  eapply alloc_global_match; eauto. 
Qed.

Definition romem_consistent (g: genv) (rm: romem) :=
  forall id b ab,
  Genv.find_symbol g id = Some b -> rm!id = Some ab ->
  exists v,
     Genv.find_var_info g b = Some v
  /\ v.(gvar_readonly) = true
  /\ v.(gvar_volatile) = false
  /\ ab = store_init_data_list (ablock_init Pbot) 0 v.(gvar_init).

Lemma alloc_global_consistent:
  forall g rm idg,
  romem_consistent g rm ->
  romem_consistent (Genv.add_global g idg) (alloc_global rm idg).
Proof.
  intros; red; intros. destruct idg as [id1 [fd1 | v1]];
  unfold Genv.add_global, Genv.find_symbol, Genv.find_var_info, alloc_global in *; simpl in *.
- rewrite PTree.gsspec in H0. rewrite PTree.grspec in H1. unfold PTree.elt_eq in *.
  destruct (peq id id1). congruence. eapply H; eauto. 
- rewrite PTree.gsspec in H0. destruct (peq id id1).
+ inv H0. rewrite PTree.gss. 
  destruct (gvar_readonly v1 && negb (gvar_volatile v1)) eqn:RO.
  InvBooleans. rewrite negb_true_iff in H2.
  rewrite PTree.gss in H1.
  exists v1. intuition congruence. 
  rewrite PTree.grs in H1. discriminate.
+ rewrite PTree.gso. eapply H; eauto. 
  destruct (gvar_readonly v1 && negb (gvar_volatile v1)).
  rewrite PTree.gso in H1; auto. 
  rewrite PTree.gro in H1; auto. 
  apply Plt_ne. eapply Genv.genv_symb_range; eauto. 
Qed.

Lemma alloc_globals_consistent:
  forall gl g rm,
  romem_consistent g rm ->
  romem_consistent (Genv.add_globals g gl) (List.fold_left alloc_global gl rm).
Proof.
  induction gl; simpl; intros. auto. apply IHgl. apply alloc_global_consistent; auto. 
Qed.

End INIT.

Theorem initial_mem_matches:
  forall m,
  Genv.init_mem prog = Some m -> 
  exists bc,
     genv_match bc ge
  /\ bc_below bc (Mem.nextblock m)
  /\ bc_nostack bc
  /\ romatch bc m (romem_for_program prog)
  /\ (forall b, Mem.valid_block m b -> bc b <> BCinvalid).
Proof.
  intros.
  exploit initial_block_classification; eauto. intros (bc & GE & BELOW & NOSTACK & INV & VALID). 
  exists bc; splitall; auto.
  assert (A: initial_mem_match bc m ge).
  {
    apply alloc_globals_match with (m := Mem.empty); auto.
    red. unfold Genv.find_var_info; simpl. intros. rewrite PTree.gempty in H0; discriminate.
  }
  assert (B: romem_consistent ge (romem_for_program prog)).
  {
    apply alloc_globals_consistent.
    red; intros. rewrite PTree.gempty in H1; discriminate.
  }
  red; intros.
  exploit B; eauto. intros (v & FV & RO & NVOL & EQ). 
  split. subst ab. apply store_init_data_list_summary. constructor. 
  split. subst ab. eapply A; eauto. 
  unfold ge in FV; exploit Genv.init_mem_characterization; eauto. 
  intros (P & Q & R). 
  intros; red; intros. exploit Q; eauto. intros [U V]. 
  unfold Genv.perm_globvar in V; rewrite RO, NVOL in V. inv V. 
Qed.

End INITIAL. 

Require Import Axioms.

Theorem sound_initial:
  forall prog st, initial_state prog st -> sound_state prog st.
Proof.
  destruct 1. 
  exploit initial_mem_matches; eauto. intros (bc & GE & BELOW & NOSTACK & RM & VALID).
  apply sound_call_state with bc. 
- constructor. 
- simpl; tauto. 
- exact RM.
- apply mmatch_inj_top with m0.
  replace (inj_of_bc bc) with (Mem.flat_inj (Mem.nextblock m0)).
  eapply Genv.initmem_inject; eauto.
  symmetry; apply extensionality; unfold Mem.flat_inj; intros x.
  destruct (plt x (Mem.nextblock m0)). 
  apply inj_of_bc_valid; auto. 
  unfold inj_of_bc. erewrite bc_below_invalid; eauto.
- exact GE.
- exact NOSTACK.
Qed.

Hint Resolve areg_sound aregs_sound: va.

(** * Interface with other optimizations *)

Definition avalue (a: VA.t) (r: reg) : aval :=
  match a with
  | VA.Bot => Vbot
  | VA.State ae am => AE.get r ae
  end.

Lemma avalue_sound:
  forall prog s f sp pc e m r,
  sound_state prog (State s f (Vptr sp Int.zero) pc e m) ->
  exists bc,
     vmatch bc e#r (avalue (analyze (romem_for_program prog) f)!!pc r)
  /\ genv_match bc (Genv.globalenv prog)
  /\ bc sp = BCstack.
Proof.
  intros. inv H. exists bc; split; auto. rewrite AN. apply EM.
Qed. 

Definition aaddr (a: VA.t) (r: reg) : aptr :=
  match a with
  | VA.Bot => Pbot
  | VA.State ae am => aptr_of_aval (AE.get r ae)
  end.

Lemma aaddr_sound:
  forall prog s f sp pc e m r b ofs,
  sound_state prog (State s f (Vptr sp Int.zero) pc e m) ->
  e#r = Vptr b ofs ->
  exists bc,
     pmatch bc b ofs (aaddr (analyze (romem_for_program prog) f)!!pc r)
  /\ genv_match bc (Genv.globalenv prog)
  /\ bc sp = BCstack.
Proof.
  intros. inv H. exists bc; split; auto.
  unfold aaddr; rewrite AN. apply match_aptr_of_aval. rewrite <- H0. apply EM.
Qed. 

Definition aaddressing (a: VA.t) (addr: addressing) (args: list reg) : aptr :=
  match a with
  | VA.Bot => Pbot
  | VA.State ae am => aptr_of_aval (eval_static_addressing addr (aregs ae args))
  end.

Lemma aaddressing_sound:
  forall prog s f sp pc e m addr args b ofs,
  sound_state prog (State s f (Vptr sp Int.zero) pc e m) ->
  eval_addressing (Genv.globalenv prog) (Vptr sp Int.zero) addr e##args = Some (Vptr b ofs) ->
  exists bc,
     pmatch bc b ofs (aaddressing (analyze (romem_for_program prog) f)!!pc addr args)
  /\ genv_match bc (Genv.globalenv prog)
  /\ bc sp = BCstack.
Proof.
  intros. inv H. exists bc; split; auto. 
  unfold aaddressing. rewrite AN. apply match_aptr_of_aval. 
  eapply eval_static_addressing_sound; eauto with va.
Qed.


  


