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

(** An alternate, mixed-step semantics for the RTL intermediate language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Mem.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.

Section BIGSTEP.

Variable ge: genv.

(** The dynamic semantics of RTL is a combination of small-step (transition)
  semantics and big-step semantics.  Execution of an instruction performs
  a single transition to the next instruction (small-step), except if
  the instruction is a function call.  In this case, the whole body of
  the called function is executed at once and the transition terminates
  on the instruction immediately following the call in the caller function.
  Such ``mixed-step'' semantics is convenient for reasoning over
  intra-procedural analyses and transformations.  It also dispenses us
  from making the call stack explicit in the semantics.

  The semantics is organized in three mutually inductive predicates.
  The first is [exec_instr ge c sp pc rs m pc' rs' m'].  [ge] is the
  global environment (see module [Genv]), [c] the CFG for the current
  function, and [sp] the pointer to the stack block for its
  current activation (as in Cminor).  [pc], [rs] and [m] is the 
  initial state of the transition: program point (CFG node) [pc],
  register state (mapping of pseudo-registers to values) [rs],
  and memory state [m].  The final state is [pc'], [rs'] and [m']. *)

Inductive exec_instr: code -> val ->
                      node -> regset -> mem -> trace ->
                      node -> regset -> mem -> Prop :=
  | exec_Inop:
      forall c sp pc rs m pc',
      c!pc = Some(Inop pc') ->
      exec_instr c sp  pc rs m  E0 pc' rs m
  | exec_Iop:
      forall c sp pc rs m op args res pc' v,
      c!pc = Some(Iop op args res pc') ->
      eval_operation ge sp op rs##args m = Some v ->
      exec_instr c sp  pc rs m  E0 pc' (rs#res <- v) m
  | exec_Iload:
      forall c sp pc rs m chunk addr args dst pc' a v,
      c!pc = Some(Iload chunk addr args dst pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      exec_instr c sp  pc rs m  E0 pc' (rs#dst <- v) m
  | exec_Istore:
      forall c sp pc rs m chunk addr args src pc' a m',
      c!pc = Some(Istore chunk addr args src pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      exec_instr c sp  pc rs m  E0 pc' rs m'
  | exec_Icall:
      forall c sp pc rs m sig ros args res pc' f vres m' t,
      c!pc = Some(Icall sig ros args res pc') ->
      find_function ge ros rs = Some f ->
      funsig f = sig ->
      exec_function f rs##args m t vres m' ->
      exec_instr c sp  pc rs m  t pc' (rs#res <- vres) m'
  | exec_Ialloc:
      forall c sp pc rs m pc' arg res sz m' b,
      c!pc = Some(Ialloc arg res pc') ->
      rs#arg = Vint sz ->
      Mem.alloc m 0 (Int.signed sz) = (m', b) ->
      exec_instr c sp  pc rs m E0 pc' (rs#res <- (Vptr b Int.zero)) m'
  | exec_Icond_true:
      forall c sp pc rs m cond args ifso ifnot,
      c!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition cond rs##args m = Some true ->
      exec_instr c sp  pc rs m  E0 ifso rs m
  | exec_Icond_false:
      forall c sp pc rs m cond args ifso ifnot,
      c!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition cond rs##args m = Some false ->
      exec_instr c sp  pc rs m  E0 ifnot rs m

(** [exec_body ge c sp pc rs m res m'] repeatedly executes
   instructions starting at [pc] in [c], until it
   reaches a return or tailcall instruction.  It performs
   that instruction and sets [res] to the return value
   and [m'] to the final memory state. *)

with exec_body: code -> val ->
                node -> regset -> mem -> trace ->
                val -> mem -> Prop :=
  | exec_body_step: forall c sp pc rs m t1 pc1 rs1 m1 t2 t res m2,
      exec_instr c sp  pc rs m  t1  pc1 rs1 m1 ->
      exec_body c sp  pc1 rs1 m1  t2  res m2 ->
      t = t1 ** t2 ->
      exec_body c sp  pc rs m  t  res m2
  | exec_Ireturn: forall c stk pc rs m or res,
      c!pc = Some(Ireturn or) ->
      res = regmap_optget or Vundef rs ->
      exec_body c (Vptr stk Int.zero)  pc rs m  E0  res (Mem.free m stk)
  | exec_Itailcall: forall c stk pc rs m sig ros args f t res m',
      c!pc = Some(Itailcall sig ros args) ->
      find_function ge ros rs = Some f ->
      funsig f = sig ->
      exec_function f rs##args (Mem.free m stk) t res m' ->
      exec_body c (Vptr stk Int.zero)  pc rs m  t  res m'

(** [exec_function ge f args m res m'] executes a function application.
  [f] is the called function, [args] the values of its arguments,
  and [m] the memory state at the beginning of the call.  [res] is
  the returned value: the value of [r] if the function terminates with 
  a [Ireturn (Some r)], or [Vundef] if it terminates with [Ireturn None].
  Evaluation proceeds by executing transitions from the function's entry
  point to the first [Ireturn] instruction encountered.  It is preceeded
  by the allocation of the stack activation block and the binding
  of register parameters to the provided arguments.
  (Non-parameter registers are initialized to [Vundef].)  Before returning,
  the stack activation block is freed. *)

with exec_function: fundef -> list val -> mem -> trace ->
                              val -> mem -> Prop :=
  | exec_funct_internal:
      forall f m m1 stk args t m2 vres,
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      exec_body f.(fn_code) (Vptr stk Int.zero) 
                f.(fn_entrypoint) (init_regs args f.(fn_params)) m1
                t vres m2 ->
      exec_function (Internal f) args m t vres m2
  | exec_funct_external:
      forall ef args m t res,
      event_match ef args t res ->
      exec_function (External ef) args m t res m.

Scheme exec_instr_ind_3 := Minimality for exec_instr Sort Prop
  with exec_body_ind_3 := Minimality for exec_body Sort Prop
  with exec_function_ind_3 := Minimality for exec_function Sort Prop.

(** The reflexive transitive closure of [exec_instr]. *)

Inductive exec_instrs: code -> val ->
                       node -> regset -> mem -> trace ->
                       node -> regset -> mem -> Prop :=
  | exec_refl:
      forall c sp pc rs m,
      exec_instrs c sp pc rs m E0 pc rs m
  | exec_one:
      forall c sp pc rs m t pc' rs' m',
      exec_instr c sp pc rs m t pc' rs' m' ->
      exec_instrs c sp pc rs m t pc' rs' m'
  | exec_trans:
      forall c sp pc1 rs1 m1 t1 pc2 rs2 m2 t2 pc3 rs3 m3 t3,
      exec_instrs c sp pc1 rs1 m1 t1 pc2 rs2 m2 ->
      exec_instrs c sp pc2 rs2 m2 t2 pc3 rs3 m3 ->
      t3 = t1 ** t2 ->
      exec_instrs c sp pc1 rs1 m1 t3 pc3 rs3 m3.

(** Some derived execution rules. *)

Lemma exec_instrs_exec_body:
  forall c sp pc1 rs1 m1 t1 pc2 rs2 m2,
  exec_instrs c sp pc1 rs1 m1 t1 pc2 rs2 m2 ->
  forall res t2 m3 t3,
  exec_body c sp pc2 rs2 m2 t2 res m3 ->
  t3 = t1 ** t2 ->
  exec_body c sp pc1 rs1 m1 t3 res m3.
Proof.
  induction 1; intros.
  subst t3. rewrite E0_left. auto.
  eapply exec_body_step; eauto.
  eapply IHexec_instrs1. eapply IHexec_instrs2. eauto. 
  eauto. traceEq. 
Qed.

Lemma exec_step:
  forall c sp pc1 rs1 m1 t1 pc2 rs2 m2 t2 pc3 rs3 m3 t3,
  exec_instr c sp pc1 rs1 m1 t1 pc2 rs2 m2 ->
  exec_instrs c sp pc2 rs2 m2 t2 pc3 rs3 m3 ->
  t3 = t1 ** t2 ->
  exec_instrs c sp pc1 rs1 m1 t3 pc3 rs3 m3.
Proof.
  intros. eapply exec_trans. apply exec_one. eauto. eauto. auto.
Qed.

Lemma exec_Iop':
  forall c sp pc rs m op args res pc' rs' v,
  c!pc = Some(Iop op args res pc') ->
  eval_operation ge sp op rs##args m = Some v ->
  rs' = (rs#res <- v) ->
  exec_instr c sp  pc rs m  E0 pc' rs' m.
Proof.
  intros. subst rs'. eapply exec_Iop; eauto.
Qed.

Lemma exec_Iload':
  forall c sp pc rs m chunk addr args dst pc' rs' a v,
  c!pc = Some(Iload chunk addr args dst pc') ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.loadv chunk m a = Some v ->
  rs' = (rs#dst <- v) ->
  exec_instr c sp  pc rs m E0 pc' rs' m.
Proof.
  intros. subst rs'. eapply exec_Iload; eauto.
Qed.

(** Experimental: coinductive big-step semantics for divergence. *)

CoInductive diverge_body:
      code -> val -> node -> regset -> mem -> traceinf -> Prop :=
  | diverge_step: forall c sp pc rs m t1 pc1 rs1 m1 T2 T,
      exec_instr c sp  pc rs m  t1  pc1 rs1 m1 ->
      diverge_body c sp  pc1 rs1 m1  T2 ->
      T = t1 *** T2 ->
      diverge_body c sp  pc rs m  T
  | diverge_Icall:
      forall c sp pc rs m sig ros args res pc' f T,
      c!pc = Some(Icall sig ros args res pc') ->
      find_function ge ros rs = Some f ->
      funsig f = sig ->
      diverge_function f rs##args m T ->
      diverge_body c sp  pc rs m  T
  | diverge_Itailcall: forall c stk pc rs m sig ros args f T,
      c!pc = Some(Itailcall sig ros args) ->
      find_function ge ros rs = Some f ->
      funsig f = sig ->
      diverge_function f rs##args (Mem.free m stk) T ->
      diverge_body c (Vptr stk Int.zero)  pc rs m  T

with diverge_function: fundef -> list val -> mem -> traceinf -> Prop :=
  | diverge_funct_internal:
      forall f m m1 stk args T,
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      diverge_body f.(fn_code) (Vptr stk Int.zero) 
                   f.(fn_entrypoint) (init_regs args f.(fn_params)) m1
                   T ->
      diverge_function (Internal f) args m T.

End BIGSTEP.

(** Execution of whole programs. *)

Inductive exec_program (p: program): program_behavior -> Prop :=
  | exec_program_terminates: forall b f t r m,
      let ge := Genv.globalenv p in
      let m0 := Genv.init_mem p in
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      exec_function ge f nil m0 t (Vint r) m ->
      exec_program p (Terminates t r)
  | exec_program_diverges: forall b f T,
      let ge := Genv.globalenv p in
      let m0 := Genv.init_mem p in
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      diverge_function ge f nil m0 T ->
      exec_program p (Diverges T).

(** * Equivalence with the transition semantics. *)

Section EQUIVALENCE.

Variable ge: genv.

Definition exec_instr_prop
  (c: code) (sp: val) (pc1: node) (rs1: regset) (m1: mem)
           (t: trace) (pc2: node) (rs2: regset) (m2: mem) : Prop :=
  forall s,
  plus step ge (State s c sp pc1 rs1 m1)
             t (State s c sp pc2 rs2 m2).

Definition exec_body_prop
  (c: code) (sp: val) (pc1: node) (rs1: regset) (m1: mem)
           (t: trace) (res: val) (m2: mem) : Prop :=
  forall s,
  plus step ge (State s c sp pc1 rs1 m1)
             t (Returnstate s res m2).

Definition exec_function_prop
  (f: fundef) (args: list val) (m1: mem)
  (t: trace) (res: val) (m2: mem) : Prop :=
  forall s,
  plus step ge (Callstate s f args m1)
             t (Returnstate s res m2).

Lemma exec_steps:
  (forall c sp pc1 rs1 m1 t pc2 rs2 m2,
   exec_instr ge c sp pc1 rs1 m1 t pc2 rs2 m2 ->
   exec_instr_prop c sp pc1 rs1 m1 t pc2 rs2 m2) /\
  (forall c sp pc1 rs1 m1 t res m2,
   exec_body ge c sp pc1 rs1 m1 t res m2 ->
   exec_body_prop c sp pc1 rs1 m1 t res m2) /\
  (forall f args m1 t res m2,
   exec_function ge f args m1 t res m2 ->
   exec_function_prop f args m1 t res m2).
Proof.
  set (IND := fun a b c d e f g h i j k l m =>
          conj (exec_instr_ind_3 ge exec_instr_prop exec_body_prop exec_function_prop a b c d e f g h i j k l m)
               (conj (exec_body_ind_3 ge exec_instr_prop exec_body_prop exec_function_prop a b c d e f g h i j k l m)
                     (exec_function_ind_3 ge exec_instr_prop exec_body_prop exec_function_prop a b c d e f g h i j k l m))).
  apply IND; clear IND;
  intros; red; intros.
  (* nop *)
  apply plus_one. eapply RTL.exec_Inop; eauto.
  (* op *)
  apply plus_one. eapply RTL.exec_Iop'; eauto. 
  (* load *)
  apply plus_one. eapply RTL.exec_Iload'; eauto.
  (* store *)
  apply plus_one. eapply RTL.exec_Istore; eauto.
  (* call *)
  eapply plus_left'. eapply RTL.exec_Icall; eauto.
  eapply plus_right'. apply H3. apply RTL.exec_return. 
  eauto. traceEq.
  (* alloc *)
  apply plus_one. eapply RTL.exec_Ialloc; eauto. 
  (* cond true *)
  apply plus_one. eapply RTL.exec_Icond_true; eauto.  
  (* cond false *)
  apply plus_one. eapply RTL.exec_Icond_false; eauto.
  (* body step *)
  eapply plus_trans. apply H0. apply H2. auto.
  (* body return *)
  apply plus_one. rewrite H0. eapply RTL.exec_Ireturn; eauto.
  (* body tailcall *)
  eapply plus_left'. eapply RTL.exec_Itailcall; eauto. 
  apply H3. traceEq.
  (* internal function *)
  eapply plus_left'. eapply RTL.exec_function_internal; eauto. 
  apply H1. traceEq.
  (* external function *)
  apply plus_one. eapply RTL.exec_function_external; eauto.
Qed.

Lemma diverge_function_steps:
  forall fd args m T s,
  diverge_function ge fd args m T ->
  forever step ge (Callstate s fd args m) T.
Proof.
  assert (diverge_function_steps':
          forall fd args m T s,
          diverge_function ge fd args m T ->
          forever_N step ge O (Callstate s fd args m) T).
  cofix COINDHYP1.
  assert (diverge_body_steps: forall c sp pc rs m T s,
          diverge_body ge c sp pc rs m T ->
          forever_N step ge O (State s c sp pc rs m) T).
  cofix COINDHYP2; intros.
  inv H. 
  (* step *)
  apply forever_N_plus with (State s c sp pc1 rs1 m1) O.
  destruct exec_steps as [E [F G]].
  apply E. assumption.
  apply COINDHYP2. assumption.
  (* call *)
  change T with (E0 *** T).
  apply forever_N_plus with (Callstate (Stackframe res c sp pc' rs :: s)
                                       f rs##args m) O.
  apply plus_one. eapply RTL.exec_Icall; eauto. 
  apply COINDHYP1. assumption.
  (* tailcall *)
  change T with (E0 *** T).
  apply forever_N_plus with (Callstate s f rs##args (free m stk)) O.
  apply plus_one. eapply RTL.exec_Itailcall; eauto. 
  apply COINDHYP1. assumption.
  (* internal function *)
  intros. inv H. 
  change T with (E0 *** T).
  apply forever_N_plus with
    (State s f.(fn_code) (Vptr stk Int.zero)
             f.(fn_entrypoint) (init_regs args f.(fn_params)) m1) O.
  apply plus_one. eapply RTL.exec_function_internal; eauto.
  apply diverge_body_steps. assumption.
  (* conclusion *)
  intros. eapply forever_N_forever. eauto.
Qed.

End EQUIVALENCE.

Theorem exec_program_bigstep_smallstep:
  forall p beh,
  exec_program p beh ->
  RTL.exec_program p beh.
Proof.
  intros. unfold RTL.exec_program. inv H. 
  econstructor. 
  econstructor; eauto. 
  apply plus_star.
  destruct (exec_steps (Genv.globalenv p)) as [E [F G]].
  apply (G _ _ _ _ _ _ H3).
  constructor.
  econstructor.
  econstructor; eauto.
  apply diverge_function_steps. auto. 
Qed.

