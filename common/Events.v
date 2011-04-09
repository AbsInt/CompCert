(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Observable events, execution traces, and semantics of external calls. *)

Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.

(** * Events and traces *)

(** The observable behaviour of programs is stated in terms of
  input/output events, which represent the actions of the program
  that the external world can observe.  CompCert leaves much flexibility as to
  the exact content of events: the only requirement is that they
  do not expose memory states nor pointer values 
  (other than pointers to global variables), because these
  are not preserved literally during compilation.  For concreteness,
  we use the following type for events.  Each event represents either:

- A system call (e.g. an input/output operation), recording the
  name of the system call, its parameters, and its result.

- A volatile load from a global memory location, recording the chunk
  and address being read and the value just read. 

- A volatile store to a global memory location, recording the chunk
  and address being written and the value stored there. 

- An annotation, recording the text of the annotation and the values
  of the arguments.

  The values attached to these events are of the following form.
  As mentioned above, we do not expose pointer values directly.
  Pointers relative to a global variable are shown with the name
  of the variable instead of the block identifier.
*)

Inductive eventval: Type :=
  | EVint: int -> eventval
  | EVfloat: float -> eventval
  | EVptr_global: ident -> int -> eventval.

Inductive event: Type :=
  | Event_syscall: ident -> list eventval -> eventval -> event
  | Event_vload: memory_chunk -> ident -> int -> eventval -> event
  | Event_vstore: memory_chunk -> ident -> int -> eventval -> event
  | Event_annot: ident -> list eventval -> event.

(** The dynamic semantics for programs collect traces of events.
  Traces are of two kinds: finite (type [trace]) or infinite (type [traceinf]). *)

Definition trace := list event.

Definition E0 : trace := nil.

Definition Eapp (t1 t2: trace) : trace := t1 ++ t2.

CoInductive traceinf : Type :=
  | Econsinf: event -> traceinf -> traceinf.

Fixpoint Eappinf (t: trace) (T: traceinf) {struct t} : traceinf :=
  match t with
  | nil => T
  | ev :: t' => Econsinf ev (Eappinf t' T)
  end.

(** Concatenation of traces is written [**] in the finite case
  or [***] in the infinite case. *)

Infix "**" := Eapp (at level 60, right associativity).
Infix "***" := Eappinf (at level 60, right associativity).

Lemma E0_left: forall t, E0 ** t = t.
Proof. auto. Qed.

Lemma E0_right: forall t, t ** E0 = t.
Proof. intros. unfold E0, Eapp. rewrite <- app_nil_end. auto. Qed.

Lemma Eapp_assoc: forall t1 t2 t3, (t1 ** t2) ** t3 = t1 ** (t2 ** t3).
Proof. intros. unfold Eapp, trace. apply app_ass. Qed.

Lemma Eapp_E0_inv: forall t1 t2, t1 ** t2 = E0 -> t1 = E0 /\ t2 = E0.
Proof (@app_eq_nil event).
  
Lemma E0_left_inf: forall T, E0 *** T = T.
Proof. auto. Qed.

Lemma Eappinf_assoc: forall t1 t2 T, (t1 ** t2) *** T = t1 *** (t2 *** T).
Proof.
  induction t1; intros; simpl. auto. decEq; auto.
Qed.

Hint Rewrite E0_left E0_right Eapp_assoc
             E0_left_inf Eappinf_assoc: trace_rewrite.

Opaque trace E0 Eapp Eappinf.

(** The following [traceEq] tactic proves equalities between traces
  or infinite traces. *)

Ltac substTraceHyp :=
  match goal with
  | [ H: (@eq trace ?x ?y) |- _ ] =>
       subst x || clear H
  end.

Ltac decomposeTraceEq :=
  match goal with
  | [ |- (_ ** _) = (_ ** _) ] =>
      apply (f_equal2 Eapp); auto; decomposeTraceEq
  | _ =>
      auto
  end.

Ltac traceEq := 
  repeat substTraceHyp; autorewrite with trace_rewrite; decomposeTraceEq.

(** Bisimilarity between infinite traces. *)

CoInductive traceinf_sim: traceinf -> traceinf -> Prop :=
  | traceinf_sim_cons: forall e T1 T2,
      traceinf_sim T1 T2 ->
      traceinf_sim (Econsinf e T1) (Econsinf e T2).

Lemma traceinf_sim_refl:
  forall T, traceinf_sim T T.
Proof.
  cofix COINDHYP; intros.
  destruct T. constructor. apply COINDHYP.
Qed.
 
Lemma traceinf_sim_sym:
  forall T1 T2, traceinf_sim T1 T2 -> traceinf_sim T2 T1.
Proof.
  cofix COINDHYP; intros. inv H; constructor; auto.
Qed.

Lemma traceinf_sim_trans:
  forall T1 T2 T3, 
  traceinf_sim T1 T2 -> traceinf_sim T2 T3 -> traceinf_sim T1 T3.
Proof.
  cofix COINDHYP;intros. inv H; inv H0; constructor; eauto.
Qed.

CoInductive traceinf_sim': traceinf -> traceinf -> Prop :=
  | traceinf_sim'_cons: forall t T1 T2,
      t <> E0 -> traceinf_sim' T1 T2 -> traceinf_sim' (t *** T1) (t *** T2).

Lemma traceinf_sim'_sim:
  forall T1 T2, traceinf_sim' T1 T2 -> traceinf_sim T1 T2.
Proof.
  cofix COINDHYP; intros. inv H. 
  destruct t. elim H0; auto.
Transparent Eappinf.
Transparent E0.
  simpl. 
  destruct t. simpl. constructor. apply COINDHYP; auto.
  constructor. apply COINDHYP.
  constructor. unfold E0; congruence. auto.
Qed.

(** The "is prefix of" relation between a finite and an infinite trace. *)

Inductive traceinf_prefix: trace -> traceinf -> Prop :=
  | traceinf_prefix_nil: forall T,
      traceinf_prefix nil T
  | traceinf_prefix_cons: forall e t1 T2,
      traceinf_prefix t1 T2 ->
      traceinf_prefix (e :: t1) (Econsinf e T2).

Lemma traceinf_prefix_app:
  forall t1 T2 t,
  traceinf_prefix t1 T2 ->
  traceinf_prefix (t ** t1) (t *** T2).
Proof.
  induction t; simpl; intros. auto.
  change ((a :: t) ** t1) with (a :: (t ** t1)).
  change ((a :: t) *** T2) with (Econsinf a (t *** T2)).
  constructor. auto.
Qed.

(** An alternate presentation of infinite traces as
  infinite concatenations of nonempty finite traces. *)

CoInductive traceinf': Type :=
  | Econsinf': forall (t: trace) (T: traceinf'), t <> E0 -> traceinf'.

Program Definition split_traceinf' (t: trace) (T: traceinf') (NE: t <> E0): event * traceinf' :=
  match t with
  | nil => _
  | e :: nil => (e, T)
  | e :: t' => (e, Econsinf' t' T _)
  end.
Next Obligation.
  elimtype False. elim NE. auto. 
Qed.
Next Obligation.
  red; intro. elim (H e). rewrite H0. auto. 
Qed.

CoFixpoint traceinf_of_traceinf' (T': traceinf') : traceinf :=
  match T' with
  | Econsinf' t T'' NOTEMPTY =>
      let (e, tl) := split_traceinf' t T'' NOTEMPTY in
      Econsinf e (traceinf_of_traceinf' tl)
  end.

Remark unroll_traceinf':
  forall T, T = match T with Econsinf' t T' NE => Econsinf' t T' NE end.
Proof.
  intros. destruct T; auto.
Qed.

Remark unroll_traceinf:
  forall T, T = match T with Econsinf t T' => Econsinf t T' end.
Proof.
  intros. destruct T; auto.
Qed.

Lemma traceinf_traceinf'_app:
  forall t T NE,
  traceinf_of_traceinf' (Econsinf' t T NE) = t *** traceinf_of_traceinf' T.
Proof.
  induction t.
  intros. elim NE. auto.
  intros. simpl.   
  rewrite (unroll_traceinf (traceinf_of_traceinf' (Econsinf' (a :: t) T NE))).
  simpl. destruct t. auto.
Transparent Eappinf.
  simpl. f_equal. apply IHt. 
Qed.

(** * Relating values and event values *)

Set Implicit Arguments.

Section EVENTVAL.

(** Global environment used to translate between global variable names and their block identifiers. *)
Variables F V: Type.
Variable ge: Genv.t F V.

(** Translation between values and event values. *)

Inductive eventval_match: eventval -> typ -> val -> Prop :=
  | ev_match_int: forall i,
      eventval_match (EVint i) Tint (Vint i)
  | ev_match_float: forall f,
      eventval_match (EVfloat f) Tfloat (Vfloat f)
  | ev_match_ptr: forall id b ofs,
      Genv.find_symbol ge id = Some b ->
      eventval_match (EVptr_global id ofs) Tint (Vptr b ofs).

Inductive eventval_list_match: list eventval -> list typ -> list val -> Prop :=
  | evl_match_nil:
      eventval_list_match nil nil nil
  | evl_match_cons:
      forall ev1 evl ty1 tyl v1 vl,
      eventval_match ev1 ty1 v1 ->
      eventval_list_match evl tyl vl ->
      eventval_list_match (ev1::evl) (ty1::tyl) (v1::vl).

(** Some properties of these translation predicates. *)

Lemma eventval_match_type:
  forall ev ty v,
  eventval_match ev ty v -> Val.has_type v ty.
Proof.
  intros. inv H; constructor.
Qed.

Lemma eventval_list_match_length:
  forall evl tyl vl, eventval_list_match evl tyl vl -> List.length vl = List.length tyl.
Proof.
  induction 1; simpl; eauto.
Qed.

Lemma eventval_match_lessdef:
  forall ev ty v1 v2,
  eventval_match ev ty v1 -> Val.lessdef v1 v2 -> eventval_match ev ty v2.
Proof.
  intros. inv H; inv H0; constructor; auto.
Qed.

Lemma eventval_list_match_lessdef:
  forall evl tyl vl1, eventval_list_match evl tyl vl1 ->
  forall vl2, Val.lessdef_list vl1 vl2 -> eventval_list_match evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H1. constructor. eapply eventval_match_lessdef; eauto. eauto.
Qed.

(** Compatibility with memory injections *)

Variable f: block -> option (block * Z).

Definition meminj_preserves_globals : Prop :=
     (forall id b, Genv.find_symbol ge id = Some b -> f b = Some(b, 0))
  /\ (forall b gv, Genv.find_var_info ge b = Some gv -> f b = Some(b, 0))
  /\ (forall b1 b2 delta gv, Genv.find_var_info ge b2 = Some gv -> f b1 = Some(b2, delta) -> b2 = b1).

Hypothesis glob_pres: meminj_preserves_globals.

Lemma eventval_match_inject:
  forall ev ty v1 v2,
  eventval_match ev ty v1 -> val_inject f v1 v2 -> eventval_match ev ty v2.
Proof.
  intros. inv H; inv H0. constructor. constructor.
  destruct glob_pres as [A [B C]].
  exploit A; eauto. intro EQ; rewrite H3 in EQ; inv EQ.
  rewrite Int.add_zero. econstructor; eauto. 
Qed.

Lemma eventval_match_inject_2:
  forall ev ty v,
  eventval_match ev ty v -> val_inject f v v.
Proof.
  induction 1. constructor. constructor.
  destruct glob_pres as [A [B C]].
  exploit A; eauto. intro EQ.
  econstructor; eauto. rewrite Int.add_zero; auto.
Qed.

Lemma eventval_list_match_inject:
  forall evl tyl vl1, eventval_list_match evl tyl vl1 ->
  forall vl2, val_list_inject f vl1 vl2 -> eventval_list_match evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H1. constructor. eapply eventval_match_inject; eauto. eauto.
Qed.

(** Determinism *)

Lemma eventval_match_determ_1:
  forall ev ty v1 v2, eventval_match ev ty v1 -> eventval_match ev ty v2 -> v1 = v2.
Proof.
  intros. inv H; inv H0; auto. congruence.
Qed.

Lemma eventval_match_determ_2:
  forall ev1 ev2 ty v, eventval_match ev1 ty v -> eventval_match ev2 ty v -> ev1 = ev2.
Proof.
  intros. inv H; inv H0; auto.
  decEq. eapply Genv.genv_vars_inj; eauto. 
Qed.

Lemma eventval_list_match_determ_2:
  forall evl1 tyl vl, eventval_list_match evl1 tyl vl ->
  forall evl2, eventval_list_match evl2 tyl vl -> evl1 = evl2.
Proof.
  induction 1; intros. inv H. auto. inv H1. f_equal; eauto.
  eapply eventval_match_determ_2; eauto.
Qed.

End EVENTVAL.

(** Invariance under changes to the global environment *)

Section EVENTVAL_INV.

Variables F1 V1 F2 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

Lemma eventval_match_preserved:
  forall ev ty v,
  eventval_match ge1 ev ty v -> eventval_match ge2 ev ty v.
Proof.
  induction 1; constructor. rewrite symbols_preserved; auto. 
Qed.

Lemma eventval_list_match_preserved:
  forall evl tyl vl,
  eventval_list_match ge1 evl tyl vl -> eventval_list_match ge2 evl tyl vl.
Proof.
  induction 1; constructor; auto. eapply eventval_match_preserved; eauto.
Qed.

End EVENTVAL_INV.

(** * Semantics of external functions *)

(** Each external function is of one of the following kinds: *)

Inductive extfun_kind: signature -> Type :=
  | EF_syscall (name: ident) (sg: signature): extfun_kind sg
     (** A system call.  Takes representable arguments (integers, floats,
         pointers to globals), produces a representable result,
         does not modify the memory, and produces an [Event_syscall] event
         in the trace. *)
  | EF_vload (chunk: memory_chunk): extfun_kind (mksignature (Tint :: nil) (Some (type_of_chunk chunk)))
     (** A volatile read operation.  If the adress given as first argument
         points within a volatile global variable, generate an [Event_vload]
         event and return the value found in this event.  Otherwise,
         produce no event and behave like a regular memory load. *)
  | EF_vstore (chunk: memory_chunk): extfun_kind (mksignature (Tint :: type_of_chunk chunk :: nil) None)
     (** A volatile store operation.   If the adress given as first argument
         points within a volatile global variable, generate an [Event_vstore]
         event.  Otherwise, produce no event and behave like a regular memory store. *)
  | EF_malloc: extfun_kind (mksignature (Tint :: nil) (Some Tint))
     (** Dynamic memory allocation.  Takes the requested size in bytes
         as argument; returns a pointer to a fresh block of the given size.
         Produces no observable event. *)
  | EF_free: extfun_kind (mksignature (Tint :: nil) None)
     (** Dynamic memory deallocation.  Takes a pointer to a block
         allocated by an [EF_malloc] external call and frees the
         corresponding block.
         Produces no observable event. *)
  | EF_annotation (text: ident) (sg: signature): extfun_kind sg.
     (** A programmer-supplied annotation.  Takes representable arguments,
         returns its first argument as result (or [Vundef] if no arguments),
         does not modify the memory, and produces an [Event_annot]
         event in the trace. *)

Parameter classify_external_function: 
  forall (ef: external_function), extfun_kind (ef.(ef_sig)).

(** For each external function, its behavior is defined by a predicate relating:
- the global environment
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).
*)

Definition extcall_sem : Type :=
  forall (F V: Type), Genv.t F V -> list val -> mem -> trace -> val -> mem -> Prop.

(** We now specify the expected properties of this predicate. *)

Definition mem_unchanged_on (P: block -> Z -> Prop) (m_before m_after: mem): Prop :=
  (forall b ofs p,
   P b ofs -> Mem.perm m_before b ofs p -> Mem.perm m_after b ofs p)
/\(forall chunk b ofs v,
   (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
   Mem.load chunk m_before b ofs = Some v ->
   Mem.load chunk m_after b ofs = Some v).

Definition loc_out_of_bounds (m: mem) (b: block) (ofs: Z) : Prop :=
  ofs < Mem.low_bound m b \/ ofs > Mem.high_bound m b.

Definition loc_unmapped (f: meminj) (b: block) (ofs: Z): Prop :=
  f b = None.

Definition loc_out_of_reach (f: meminj) (m: mem) (b: block) (ofs: Z): Prop :=
  forall b0 delta,
  f b0 = Some(b, delta) ->
  ofs < Mem.low_bound m b0 + delta \/ ofs >= Mem.high_bound m b0 + delta.

Definition inject_separated (f f': meminj) (m1 m2: mem): Prop :=
  forall b1 b2 delta,
  f b1 = None -> f' b1 = Some(b2, delta) ->
  ~Mem.valid_block m1 b1 /\ ~Mem.valid_block m2 b2.

Fixpoint matching_traces (t1 t2: trace) {struct t1} : Prop :=
  match t1, t2 with
  | Event_syscall name1 args1 res1 :: t1', Event_syscall name2 args2 res2 :: t2' =>
      name1 = name2 /\ args1 = args2 -> res1 = res2 /\ matching_traces t1' t2'
  | Event_vload chunk1 id1 ofs1 res1 :: t1', Event_vload chunk2 id2 ofs2 res2 :: t2' =>
      chunk1 = chunk2 /\ id1 = id2 /\ ofs1 = ofs2 -> res1 = res2 /\ matching_traces t1' t2'
  | Event_vstore chunk1 id1 ofs1 arg1 :: t1', Event_vstore chunk2 id2 ofs2 arg2 :: t2' =>
      chunk1 = chunk2 /\ id1 = id2 /\ ofs1 = ofs2 /\ arg1 = arg2 -> matching_traces t1' t2'
  | Event_annot txt1 args1 :: t1', Event_annot txt2 args2 :: t2' =>
      txt1 = txt2 /\ args1 = args2 -> matching_traces t1' t2'
  | _, _ =>
      True
  end.

Definition block_is_volatile (F V: Type) (ge: Genv.t F V) (b: block) : bool :=
  match Genv.find_var_info ge b with
  | None => false
  | Some gv => gv.(gvar_volatile)
  end.

Record extcall_properties (sem: extcall_sem)
                          (sg: signature) : Prop := mk_extcall_properties {

(** The return value of an external call must agree with its signature. *)
  ec_well_typed:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2,
    sem F V ge vargs m1 t vres m2 ->
    Val.has_type vres (proj_sig_res sg);

(** The number of arguments of an external call must agree with its signature. *)
  ec_arity:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2,
    sem F V ge vargs m1 t vres m2 ->
    List.length vargs = List.length sg.(sig_args);

(** The semantics is invariant under change of global environment that preserves symbols. *)
  ec_symbols_preserved:
    forall F1 V1 (ge1: Genv.t F1 V1) F2 V2 (ge2: Genv.t F2 V2) vargs m1 t vres m2,
    (forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) ->
    (forall b, block_is_volatile ge2 b = block_is_volatile ge1 b) ->
    sem F1 V1 ge1 vargs m1 t vres m2 ->
    sem F2 V2 ge2 vargs m1 t vres m2;

(** External calls cannot invalidate memory blocks.  (Remember that
  freeing a block does not invalidate its block identifier.) *)
  ec_valid_block:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2 b,
    sem F V ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.valid_block m2 b;

(** External calls preserve the bounds of valid blocks. *)
  ec_bounds:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2 b,
    sem F V ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.bounds m2 b = Mem.bounds m1 b;

(** External calls must commute with memory extensions, in the
  following sense. *)
  ec_mem_extends:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2 m1' vargs',
    sem F V ge vargs m1 t vres m2 ->
    Mem.extends m1 m1' ->
    Val.lessdef_list vargs vargs' ->
    exists vres', exists m2',
       sem F V ge vargs' m1' t vres' m2'
    /\ Val.lessdef vres vres'
    /\ Mem.extends m2 m2'
    /\ mem_unchanged_on (loc_out_of_bounds m1) m1' m2';

(** External calls must commute with memory injections,
  in the following sense. *)
  ec_mem_inject:
    forall F V (ge: Genv.t F V) vargs m1 t vres m2 f m1' vargs',
    meminj_preserves_globals ge f ->
    sem F V ge vargs m1 t vres m2 ->
    Mem.inject f m1 m1' ->
    val_list_inject f vargs vargs' ->
    exists f', exists vres', exists m2',
       sem F V ge vargs' m1' t vres' m2'
    /\ val_inject f' vres vres'
    /\ Mem.inject f' m2 m2'
    /\ mem_unchanged_on (loc_unmapped f) m1 m2
    /\ mem_unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1';

(** External calls must be internally deterministic:
  if the observable traces match, the return states must be
  identical. *)
  ec_determ:
    forall F V ge vargs m t1 vres1 m1 t2 vres2 m2,
    sem F V ge vargs m t1 vres1 m1 -> sem F V ge vargs m t2 vres2 m2 ->
    matching_traces t1 t2 -> t1 = t2 /\ vres1 = vres2 /\ m1 = m2
}.

(** ** Semantics of volatile loads *)

Inductive volatile_load_sem (chunk: memory_chunk) (F V: Type) (ge: Genv.t F V):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_load_sem_vol: forall b ofs m id ev v,
      Genv.find_symbol ge id = Some b -> block_is_volatile ge b = true ->
      eventval_match ge ev (type_of_chunk chunk) v ->
      volatile_load_sem chunk ge
          (Vptr b ofs :: nil) m
          (Event_vload chunk id ofs ev :: nil)
          (Val.load_result chunk v) m
  | volatile_load_sem_nonvol: forall b ofs m v,
      block_is_volatile ge b = false ->
      Mem.load chunk m b (Int.unsigned ofs) = Some v ->
      volatile_load_sem chunk ge
          (Vptr b ofs :: nil) m
          E0
          v m.

Remark meminj_preserves_block_is_volatile:
  forall F V (ge: Genv.t F V) f b1 b2 delta,
  meminj_preserves_globals ge f ->
  f b1 = Some (b2, delta) ->
  block_is_volatile ge b2 = block_is_volatile ge b1.
Proof.
  intros. destruct H as [A [B C]]. unfold block_is_volatile. 
  case_eq (Genv.find_var_info ge b1); intros.
  exploit B; eauto. intro EQ; rewrite H0 in EQ; inv EQ. rewrite H; auto.
  case_eq (Genv.find_var_info ge b2); intros.
  exploit C; eauto. intro EQ. congruence.
  auto.
Qed.

Lemma volatile_load_ok:
  forall chunk,
  extcall_properties (volatile_load_sem chunk) 
                     (mksignature (Tint :: nil) (Some (type_of_chunk chunk))).
Proof.
  intros; constructor; intros.

  unfold proj_sig_res; simpl. destruct H.
  destruct chunk; destruct v; simpl; constructor.
  eapply Mem.load_type; eauto. 

  destruct H; simpl; auto.

  destruct H1. 
  econstructor; eauto. rewrite H; auto. eapply eventval_match_preserved; eauto. 
  econstructor; eauto.

  destruct H; auto.

  destruct H; auto.

  destruct H. 
  inv H1. inv H8. inv H6. 
  exists (Val.load_result chunk v); exists m1'; intuition.
  constructor; auto.
  red; auto.
  inv H1. inv H7. inv H5. 
  exploit Mem.load_extends; eauto. intros [v' [A B]]. 
  exists v'; exists m1'; intuition.
  econstructor; eauto.
  red; auto.

  destruct H0.
  inv H2. inv H9. inv H7.
  generalize H; intros [P [Q R]].
  exploit P; eauto. intro EQ; rewrite H6 in EQ; inv EQ.
  exists f; exists (Val.load_result chunk v); exists m1'; intuition.
  rewrite Int.add_zero. constructor; auto.
  apply val_load_result_inject. eapply eventval_match_inject_2; eauto.
  red; auto.
  red; auto.
  red; intros. congruence.
  inv H2. inv H8.
  exploit Mem.loadv_inject; eauto. simpl. eauto. intros [v1 [A B]].
  inv H6; simpl in *.
  exists f; exists v1; exists m1'; intuition.
  econstructor; eauto.
  rewrite <- H0. eapply meminj_preserves_block_is_volatile; eauto.
  red; auto.
  red; auto.
  red; intros. congruence.

  inv H; inv H0; try congruence.
  assert (id = id0) by (eapply Genv.genv_vars_inj; eauto). subst id0.
  assert (ev = ev0) by (red in H1; tauto). subst ev0.
  assert (v = v0) by (eapply eventval_match_determ_1; eauto). subst v0.
  auto.
  intuition congruence.
Qed.

(** ** Semantics of volatile stores *)

Inductive volatile_store_sem (chunk: memory_chunk) (F V: Type) (ge: Genv.t F V):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_store_sem_vol: forall b ofs m id ev v,
      Genv.find_symbol ge id = Some b -> block_is_volatile ge b = true ->
      eventval_match ge ev (type_of_chunk chunk) v ->
      volatile_store_sem chunk ge
          (Vptr b ofs :: v :: nil) m
          (Event_vstore chunk id ofs ev :: nil)
          Vundef m
  | volatile_store_sem_nonvol: forall b ofs m v m',
      block_is_volatile ge b = false ->
      Mem.store chunk m b (Int.unsigned ofs) v = Some m' ->
      volatile_store_sem chunk ge
          (Vptr b ofs :: v :: nil) m
          E0
          Vundef m'.

Lemma volatile_store_ok:
  forall chunk,
  extcall_properties (volatile_store_sem chunk) 
                     (mksignature (Tint :: type_of_chunk chunk :: nil) None).
Proof.
  intros; constructor; intros.

  unfold proj_sig_res; simpl. inv H; constructor.

  inv H; simpl; auto.

  inv H1. 
  constructor. rewrite H; auto. rewrite H0; auto. eapply eventval_match_preserved; eauto.
  constructor; auto. rewrite H0; auto.

  inv H. auto. eauto with mem.

  inv H. auto. eapply Mem.bounds_store; eauto.

  inv H.
  inv H1. inv H6. inv H8. inv H7.
  exists Vundef; exists m1'; intuition.
  constructor; auto. eapply eventval_match_lessdef; eauto.
  red; auto.
  inv H1. inv H5. inv H7. inv H6.
  exploit Mem.store_within_extends; eauto. intros [m' [A B]].
  exists Vundef; exists m'; intuition.
  constructor; auto.
  red; split; intros.
  eapply Mem.perm_store_1; eauto.
  rewrite <- H1. eapply Mem.load_store_other; eauto.
  destruct (eq_block b0 b); auto. subst b0; right. 
  exploit Mem.valid_access_in_bounds. 
  eapply Mem.store_valid_access_3. eexact H3.
  intros [C D].
  generalize (size_chunk_pos chunk0). intro E.
  generalize (size_chunk_pos chunk). intro G.
  apply (Intv.range_disjoint' (ofs0, ofs0 + size_chunk chunk0)
                              (Int.unsigned ofs, Int.unsigned ofs + size_chunk chunk)).
  red; intros. generalize (H x H5). unfold loc_out_of_bounds, Intv.In; simpl. omega.
  simpl; omega. simpl; omega.

  inv H0.
  inv H2. inv H7. inv H9. inv H10.
  generalize H; intros [P [Q R]].
  exploit P; eauto. intro EQ; rewrite H6 in EQ; inv EQ.
  exists f; exists Vundef; exists m1'; intuition.
  rewrite Int.add_zero. constructor; auto. 
  eapply eventval_match_inject; eauto. 
  red; auto.
  red; auto.
  red; intros; congruence.
  inv H2. inv H8. inv H9. inv H6.
  assert (Mem.storev chunk m1 (Vptr b ofs) v = Some m2). simpl; auto.
  exploit Mem.storev_mapped_inject; eauto. intros [m2' [A B]].
  inv H4. 
  exists f; exists Vundef; exists m2'; intuition.
  constructor; auto. rewrite <- H3. eapply meminj_preserves_block_is_volatile; eauto.  
  split; intros. eapply Mem.perm_store_1; eauto.
  rewrite <- H4. eapply Mem.load_store_other; eauto. 
  left. exploit (H2 ofs0). generalize (size_chunk_pos chunk0). omega. 
  unfold loc_unmapped. congruence.
  split; intros. eapply Mem.perm_store_1; eauto.
  rewrite <- H4. eapply Mem.load_store_other; eauto.
  destruct (eq_block b0 b2); auto. subst b0; right.
  assert (EQ: Int.unsigned (Int.add ofs (Int.repr delta)) = Int.unsigned ofs + delta).
    eapply Mem.address_inject; eauto with mem.
  unfold Mem.storev in A. rewrite EQ in A. rewrite EQ.
  exploit Mem.valid_access_in_bounds. 
  eapply Mem.store_valid_access_3. eexact H0.
  intros [C D].
  generalize (size_chunk_pos chunk0). intro E.
  generalize (size_chunk_pos chunk). intro G.
  apply (Intv.range_disjoint' (ofs0, ofs0 + size_chunk chunk0)
                              (Int.unsigned ofs + delta, Int.unsigned ofs + delta + size_chunk chunk)).
  red; intros. exploit (H2 x H8). eauto. unfold Intv.In; simpl. omega.
  simpl; omega. simpl; omega.
  red; intros; congruence.

  inv H; inv H0; try congruence.
  assert (id = id0) by (eapply Genv.genv_vars_inj; eauto). subst id0.
  assert (ev = ev0) by (eapply eventval_match_determ_2; eauto). subst ev0.
  auto.
  intuition congruence.
Qed.

(** ** Semantics of dynamic memory allocation (malloc) *)

Inductive extcall_malloc_sem (F V: Type) (ge: Genv.t F V):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_malloc_sem_intro: forall n m m' b m'',
      Mem.alloc m (-4) (Int.unsigned n) = (m', b) ->
      Mem.store Mint32 m' b (-4) (Vint n) = Some m'' ->
      extcall_malloc_sem ge (Vint n :: nil) m E0 (Vptr b Int.zero) m''.

Lemma extcall_malloc_ok:
  extcall_properties extcall_malloc_sem 
                     (mksignature (Tint :: nil) (Some Tint)).
Proof.
  assert (UNCHANGED:
    forall (P: block -> Z -> Prop) m n m' b m'',
    Mem.alloc m (-4) (Int.unsigned n) = (m', b) ->
    Mem.store Mint32 m' b (-4) (Vint n) = Some m'' ->
    mem_unchanged_on P m m'').
  intros; split; intros.
  eauto with mem.
  transitivity (Mem.load chunk m' b0 ofs). 
  eapply Mem.load_store_other; eauto. left. 
  apply Mem.valid_not_valid_diff with m; eauto with mem.
  eapply Mem.load_alloc_other; eauto. 

  constructor; intros.

  inv H. unfold proj_sig_res; simpl. auto.

  inv H. auto.

  inv H1; econstructor; eauto.

  inv H. eauto with mem.

  inv H. transitivity (Mem.bounds m' b).
  eapply Mem.bounds_store; eauto.
  eapply Mem.bounds_alloc_other; eauto.
  apply Mem.valid_not_valid_diff with m1; eauto with mem.

  inv H. inv H1. inv H5. inv H7. 
  exploit Mem.alloc_extends; eauto. apply Zle_refl. apply Zle_refl.
  intros [m3' [A B]].
  exploit Mem.store_within_extends. eexact B. eauto. 
  instantiate (1 := Vint n). auto. 
  intros [m2' [C D]].
  exists (Vptr b Int.zero); exists m2'; intuition.
  econstructor; eauto.
  eapply UNCHANGED; eauto.

  inv H0. inv H2. inv H6. inv H8.
  exploit Mem.alloc_parallel_inject; eauto. apply Zle_refl. apply Zle_refl. 
  intros [f' [m3' [b' [ALLOC [A [B [C D]]]]]]].
  exploit Mem.store_mapped_inject. eexact A. eauto. eauto. 
  instantiate (1 := Vint n). auto. 
  intros [m2' [E G]].
  exists f'; exists (Vptr b' Int.zero); exists m2'; intuition.
  econstructor; eauto.
  econstructor. eauto. auto.
  eapply UNCHANGED; eauto.
  eapply UNCHANGED; eauto.
  red; intros. destruct (eq_block b1 b). 
  subst b1. rewrite C in H2. inv H2. eauto with mem. 
  rewrite D in H2. congruence. auto. 

  inv H; inv H0. intuition congruence. 
Qed.

(** ** Semantics of dynamic memory deallocation (free) *)

Inductive extcall_free_sem  (F V: Type) (ge: Genv.t F V):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_free_sem_intro: forall b lo sz m m',
      Mem.load Mint32 m b (Int.unsigned lo - 4) = Some (Vint sz) ->
      Int.unsigned sz > 0 ->
      Mem.free m b (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz) = Some m' ->
      extcall_free_sem ge (Vptr b lo :: nil) m E0 Vundef m'.

Lemma extcall_free_ok:
  extcall_properties extcall_free_sem 
                     (mksignature (Tint :: nil) None).
Proof.
  assert (UNCHANGED:
    forall (P: block -> Z -> Prop) m b lo hi m',
    Mem.free m b lo hi = Some m' ->
    lo < hi ->
    (forall b' ofs, P b' ofs -> b' <> b \/ ofs < lo \/ hi <= ofs) ->
    mem_unchanged_on P m m').
  intros; split; intros.
  eapply Mem.perm_free_1; eauto.
  rewrite <- H3. eapply Mem.load_free; eauto. 
  destruct (eq_block b0 b); auto. right. right. 
  apply (Intv.range_disjoint' (ofs, ofs + size_chunk chunk) (lo, hi)).
  red; intros. apply Intv.notin_range. simpl. exploit H1; eauto. intuition. 
  simpl; generalize (size_chunk_pos chunk); omega.
  simpl; omega.

  constructor; intros.

  inv H. unfold proj_sig_res. simpl. auto.

  inv H. auto.

  inv H1; econstructor; eauto.

  inv H. eauto with mem.

  inv H. eapply Mem.bounds_free; eauto.

  inv H. inv H1. inv H8. inv H6. 
  exploit Mem.load_extends; eauto. intros [vsz [A B]]. inv B. 
  exploit Mem.free_parallel_extends; eauto. intros [m2' [C D]].
  exists Vundef; exists m2'; intuition.
  econstructor; eauto.
  eapply UNCHANGED; eauto. omega. 
  intros. destruct (eq_block b' b); auto. subst b; right.
  red in H.
  exploit Mem.range_perm_in_bounds. 
  eapply Mem.free_range_perm. eexact H4. omega. omega.

  inv H0. inv H2. inv H7. inv H9.
  exploit Mem.load_inject; eauto. intros [vsz [A B]]. inv B. 
  assert (Mem.range_perm m1 b (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz) Freeable).
    eapply Mem.free_range_perm; eauto.
  exploit Mem.address_inject; eauto. 
    apply Mem.perm_implies with Freeable; auto with mem.
    apply H0. instantiate (1 := lo). omega. 
  intro EQ.
  assert (Mem.range_perm m1' b2 (Int.unsigned lo + delta - 4) (Int.unsigned lo + delta + Int.unsigned sz) Freeable).
    red; intros. 
    replace ofs with ((ofs - delta) + delta) by omega.
    eapply Mem.perm_inject; eauto. apply H0. omega. 
  destruct (Mem.range_perm_free _ _ _ _ H2) as [m2' FREE].
  exists f; exists Vundef; exists m2'; intuition.

  econstructor.
  rewrite EQ. replace (Int.unsigned lo + delta - 4) with (Int.unsigned lo - 4 + delta) by omega.
  eauto. auto. 
  rewrite EQ. auto.
  
  assert (Mem.free_list m1 ((b, Int.unsigned lo - 4, Int.unsigned lo + Int.unsigned sz) :: nil) = Some m2).
    simpl. rewrite H5. auto.
  eapply Mem.free_inject; eauto. 
  intros. destruct (eq_block b b1).
  subst b. assert (delta0 = delta) by congruence. subst delta0. 
  exists (Int.unsigned lo - 4); exists (Int.unsigned lo + Int.unsigned sz); split.
  simpl; auto. omega.
  elimtype False.
  exploit Mem.inject_no_overlap. eauto. eauto. eauto. eauto. 
  instantiate (1 := ofs + delta0 - delta). 
  apply Mem.perm_implies with Freeable; auto with mem.
  apply H0. omega. eauto with mem.
  unfold block; omega.

  eapply UNCHANGED; eauto. omega. intros.  
  red in H7. left. congruence. 

  eapply UNCHANGED; eauto. omega. intros.
  destruct (eq_block b' b2); auto. subst b'. right. 
  red in H7. generalize (H7 _ _ H6). intros. 
  exploit Mem.range_perm_in_bounds. eexact H0. omega. intros. omega.

  red; intros. congruence.

  inv H; inv H0. intuition congruence.
Qed.

(** ** Semantics of system calls. *)

Inductive extcall_io_sem (name: ident) (sg: signature) (F V: Type) (ge: Genv.t F V):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_io_sem_intro: forall vargs m args res vres,
      eventval_list_match ge args (sig_args sg) vargs ->
      eventval_match ge res (proj_sig_res sg) vres ->
      extcall_io_sem name sg ge vargs m (Event_syscall name args res :: E0) vres m.

Lemma extcall_io_ok:
  forall name sg,
  extcall_properties (extcall_io_sem name sg) sg.
Proof.
  intros; constructor; intros.

  inv H. eapply eventval_match_type; eauto.

  inv H. eapply eventval_list_match_length; eauto.

  inv H1. econstructor; eauto. 
  eapply eventval_list_match_preserved; eauto.
  eapply eventval_match_preserved; eauto. 

  inv H; auto.

  inv H; auto.

  inv H.
  exists vres; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_lessdef; eauto.
  red; auto.

  inv H0.
  exists f; exists vres; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_inject; eauto.
  eapply eventval_match_inject_2; eauto.
  red; auto.
  red; auto.
  red; intros; congruence.

  inv H; inv H0. simpl in H1.
  assert (args = args0). eapply eventval_list_match_determ_2; eauto. subst args0.
  assert (res = res0). tauto. subst res0.
  intuition. eapply eventval_match_determ_1; eauto.
Qed.

(** ** Semantics of annotation. *)

Inductive extcall_annot_sem (text: ident) (sg: signature) (F V: Type) (ge: Genv.t F V):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_annot_sem_intro: forall vargs m args vres,
      eventval_list_match ge args (sig_args sg) vargs ->
      sig_res sg = match sig_args sg with nil => None | t1 :: _ => Some t1 end ->
      vres = match vargs with nil => Vundef | v1 :: _ => v1 end ->
      extcall_annot_sem text sg ge vargs m (Event_annot text args :: E0) vres m.

Lemma extcall_annot_ok:
  forall text sg,
  extcall_properties (extcall_annot_sem text sg) sg.
Proof.
  intros; constructor; intros.

  inv H. unfold proj_sig_res. rewrite H1. inv H0. 
  constructor.
  eapply eventval_match_type; eauto.

  inv H. eapply eventval_list_match_length; eauto.

  inv H1. econstructor; eauto. 
  eapply eventval_list_match_preserved; eauto.

  inv H; auto.

  inv H; auto.

  inv H.
  exists (match vargs' with nil => Vundef | v1 :: _ => v1 end); exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_lessdef; eauto.
  inv H1; auto.
  red; auto.

  inv H0.
  exists f; exists (match vargs' with nil => Vundef | v1 :: _ => v1 end); exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_inject; eauto.
  inv H2; auto.
  red; auto.
  red; auto.
  red; intros; congruence.

  inv H; inv H0. simpl in H1.
  assert (args = args0). eapply eventval_list_match_determ_2; eauto. subst args0.
  intuition.
Qed.

(** ** Combined semantics of external calls *)

(** Combining the semantics given above for the various kinds of external calls,
  we define the predicate [external_call] that relates:
- the external function being invoked
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).

This predicate is used in the semantics of all CompCert languages. *)

Definition external_call (ef: external_function): extcall_sem :=
  match classify_external_function ef with
  | EF_syscall name sg   => extcall_io_sem name sg
  | EF_vload chunk       => volatile_load_sem chunk
  | EF_vstore chunk      => volatile_store_sem chunk
  | EF_malloc            => extcall_malloc_sem 
  | EF_free              => extcall_free_sem
  | EF_annotation txt sg => extcall_annot_sem txt sg
  end.

Theorem external_call_spec:
  forall ef, 
  extcall_properties (external_call ef) (ef_sig ef).
Proof.
  intros. unfold external_call. destruct (classify_external_function ef). 
  apply extcall_io_ok.
  apply volatile_load_ok.
  apply volatile_store_ok.
  apply extcall_malloc_ok.
  apply extcall_free_ok.
  apply extcall_annot_ok.
Qed.

Definition external_call_well_typed ef := ec_well_typed (external_call_spec ef).
Definition external_call_arity ef := ec_arity (external_call_spec ef).
Definition external_call_symbols_preserved_gen ef := ec_symbols_preserved (external_call_spec ef).
Definition external_call_valid_block ef := ec_valid_block (external_call_spec ef).
Definition external_call_bounds ef := ec_bounds (external_call_spec ef).
Definition external_call_mem_extends ef := ec_mem_extends (external_call_spec ef).
Definition external_call_mem_inject ef := ec_mem_inject (external_call_spec ef).
Definition external_call_determ ef := ec_determ (external_call_spec ef).

(** Special cases of [external_call_symbols_preserved_gen]. *)

Lemma external_call_symbols_preserved:
  forall ef F1 F2 V (ge1: Genv.t F1 V) (ge2: Genv.t F2 V) vargs m1 t vres m2,
  external_call ef ge1 vargs m1 t vres m2 ->
  (forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) ->
  (forall b, Genv.find_var_info ge2 b = Genv.find_var_info ge1 b) ->
  external_call ef ge2 vargs m1 t vres m2.
Proof.
  intros. eapply external_call_symbols_preserved_gen; eauto.
  intros. unfold block_is_volatile. rewrite H1. auto.
Qed.

Require Import Errors.

Lemma external_call_symbols_preserved_2:
  forall ef F1 V1 F2 V2 (tvar: V1 -> res V2)
         (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) vargs m1 t vres m2,
  external_call ef ge1 vargs m1 t vres m2 ->
  (forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id) ->
  (forall b gv1, Genv.find_var_info ge1 b = Some gv1 ->
     exists gv2, Genv.find_var_info ge2 b = Some gv2 /\ transf_globvar tvar gv1 = OK gv2) ->
  (forall b gv2, Genv.find_var_info ge2 b = Some gv2 ->
     exists gv1, Genv.find_var_info ge1 b = Some gv1 /\ transf_globvar tvar gv1 = OK gv2) ->
  external_call ef ge2 vargs m1 t vres m2.
Proof.
  intros. eapply external_call_symbols_preserved_gen; eauto.
  intros. unfold block_is_volatile.
  case_eq (Genv.find_var_info ge1 b); intros.
  exploit H1; eauto. intros [g2 [A B]]. rewrite A. monadInv B. destruct g; auto.
  case_eq (Genv.find_var_info ge2 b); intros.
  exploit H2; eauto. intros [g1 [A B]]. congruence.
  auto.
Qed.

(** Corollary of [external_call_valid_block]. *)

Lemma external_call_nextblock:
  forall ef (F V : Type) (ge : Genv.t F V) vargs m1 t vres m2,
  external_call ef ge vargs m1 t vres m2 ->
  Mem.nextblock m1 <= Mem.nextblock m2.
Proof.
  intros. 
  exploit external_call_valid_block; eauto. 
  instantiate (1 := Mem.nextblock m1 - 1). red; omega.
  unfold Mem.valid_block. omega.
Qed.
