(** The LTL intermediate language: abstract syntax and semantics.

  LTL (``Location Transfer Language'') is the target language
  for register allocation and the source language for linearization. *)

Require Import Relations.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Mem.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Conventions.

(** * Abstract syntax *)

(** LTL is close to RTL, but uses locations instead of pseudo-registers,
   and basic blocks instead of single instructions as nodes of its
   control-flow graph. *)

Definition node := positive.

(** A basic block is a sequence of instructions terminated by
    a [Bgoto], [Bcond] or [Breturn] instruction.  (This invariant
    is enforced by the following inductive type definition.)
    The instructions behave like the similarly-named instructions
    of RTL.  They take machine registers (type [mreg]) as arguments
    and results.  Two new instructions are added: [Bgetstack]
    and [Bsetstack], which are ``move'' instructions between
    a machine register and a stack slot. *)

Inductive block: Set :=
  | Bgetstack: slot -> mreg -> block -> block
  | Bsetstack: mreg -> slot -> block -> block
  | Bop: operation -> list mreg -> mreg -> block -> block
  | Bload: memory_chunk -> addressing -> list mreg -> mreg -> block -> block
  | Bstore: memory_chunk -> addressing -> list mreg -> mreg -> block -> block
  | Bcall: signature -> mreg + ident -> block -> block
  | Balloc: block -> block
  | Bgoto: node -> block
  | Bcond: condition -> list mreg -> node -> node -> block
  | Breturn: block.

Definition code: Set := PTree.t block.

(** Unlike in RTL, parameter passing (passing values of the arguments
  to a function call to the parameters of the called function) is done
  via conventional locations (machine registers and stack slots).
  Consequently, the [Bcall] instruction has no list of argument registers,
  and function descriptions have no list of parameter registers. *)

Record function: Set := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node;
  fn_code_wf:
    forall (pc: node), Plt pc (Psucc fn_entrypoint) \/ fn_code!pc = None
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.

(** * Operational semantics *)

Definition genv := Genv.t fundef.
Definition locset := Locmap.t.

Section RELSEM.

(** Calling conventions are reflected at the level of location sets
  (environments mapping locations to values) by the following two 
  functions.  

  [call_regs caller] returns the location set at function entry,
  as a function of the location set [caller] of the calling function.
- Machine registers have the same values as in the caller.
- Incoming stack slots (used for parameter passing) have the same
  values as the corresponding outgoing stack slots (used for argument
  passing) in the caller.
- Local and outgoing stack slots are initialized to undefined values.
*) 

Definition call_regs (caller: locset) : locset :=
  fun (l: loc) =>
    match l with
    | R r => caller (R r)
    | S (Local ofs ty) => Vundef
    | S (Incoming ofs ty) => caller (S (Outgoing ofs ty))
    | S (Outgoing ofs ty) => Vundef
    end.

(** [return_regs caller callee] returns the location set after
  a call instruction, as a function of the location set [caller]
  of the caller before the call instruction and of the location
  set [callee] of the callee at the return instruction.
- Callee-save machine registers have the same values as in the caller
  before the call.
- Caller-save and temporary machine registers have the same values
  as in the callee at the return point.
- Stack slots have the same values as in the caller before the call.
*)

Definition return_regs (caller callee: locset) : locset :=
  fun (l: loc) =>
    match l with
    | R r =>
        if In_dec Loc.eq (R r) Conventions.temporaries then
          callee (R r)
        else if In_dec Loc.eq (R r) Conventions.destroyed_at_call then
          callee (R r)
        else
          caller (R r)
    | S s => caller (S s)
    end.

Variable ge: genv.

Definition find_function (ros: mreg + ident) (rs: locset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge (rs (R r))
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

Definition reglist (rl: list mreg) (rs: locset) : list val :=
  List.map (fun r => rs (R r)) rl.

(** The dynamic semantics of LTL, like that of RTL, is a combination
  of small-step transition semantics and big-step semantics.
  Function calls are treated in big-step style so that they appear
  as a single transition in the caller function.  Other instructions
  are treated in purely small-step style, as a single transition.

  The introduction of basic blocks increases the number of inductive
  predicates needed to express the semantics:
- [exec_instr ge sp b ls m b' ls' m'] is the execution of the first
  instruction of block [b].  [b'] is the remainder of the block.
- [exec_instrs ge sp b ls m b' ls' m'] is similar, but executes
  zero, one or several instructions at the beginning of block [b].
- [exec_block ge sp b ls m out ls' m'] executes all instructions
  of block [b].  The outcome [out] is either [Cont s], indicating
  that the block terminates by branching to block labeled [s],
  or [Return], indicating that the block terminates by returning
  from the current function.
- [exec_blocks ge code sp pc ls m out ls' m'] executes a sequence
  of zero, one or several blocks, starting at the block labeled [pc].
  [code] is the control-flow graph for the current function.
  The outcome [out] indicates how the last block in this sequence
  terminates: by branching to another block or by returning from the
  function.
- [exec_function ge f ls m ls' m'] executes the body of function [f],
  from its entry point to the first [Lreturn] instruction encountered.

  In all these predicates, [ls] and [ls'] are the location sets
  (values of locations) at the beginning and end of the transitions,
  respectively.
*)

Inductive outcome: Set :=
  | Cont: node -> outcome
  | Return: outcome.

Inductive exec_instr: val ->
                      block -> locset -> mem -> trace ->
                      block -> locset -> mem -> Prop :=
  | exec_Bgetstack:
      forall sp sl r b rs m,
      exec_instr sp (Bgetstack sl r b) rs m
                 E0 b (Locmap.set (R r) (rs (S sl)) rs) m
  | exec_Bsetstack:
      forall sp r sl b rs m,
      exec_instr sp (Bsetstack r sl b) rs m
                 E0 b (Locmap.set (S sl) (rs (R r)) rs) m
  | exec_Bop:
      forall sp op args res b rs m v,
      eval_operation ge sp op (reglist args rs) = Some v ->
      exec_instr sp (Bop op args res b) rs m
                 E0 b (Locmap.set (R res) v rs) m
  | exec_Bload:
      forall sp chunk addr args dst b rs m a v,
      eval_addressing ge sp addr (reglist args rs) = Some a ->
      loadv chunk m a = Some v ->
      exec_instr sp (Bload chunk addr args dst b) rs m
                 E0 b (Locmap.set (R dst) v rs) m
  | exec_Bstore:
      forall sp chunk addr args src b rs m m' a,
      eval_addressing ge sp addr (reglist args rs) = Some a ->
      storev chunk m a (rs (R src)) = Some m' ->
      exec_instr sp (Bstore chunk addr args src b) rs m
                 E0 b rs m'
  | exec_Bcall:
      forall sp sig ros b rs m t f rs' m',
      find_function ros rs = Some f ->
      sig = funsig f ->
      exec_function f rs m t rs' m' ->
      exec_instr sp (Bcall sig ros b) rs m
                  t b (return_regs rs rs') m'
  | exec_Balloc:
      forall sp b rs m sz m' blk,
      rs (R Conventions.loc_alloc_argument) = Vint sz ->
      Mem.alloc m 0 (Int.signed sz) = (m', blk) ->
      exec_instr sp (Balloc b) rs m E0 b
                 (Locmap.set (R Conventions.loc_alloc_result) 
                             (Vptr blk Int.zero) rs) m'

with exec_instrs: val ->
                  block -> locset -> mem -> trace ->
                  block -> locset -> mem -> Prop :=
  | exec_refl:
      forall sp b rs m,
      exec_instrs sp b rs m E0 b rs m
  | exec_one:
      forall sp b1 rs1 m1 t b2 rs2 m2,
      exec_instr sp b1 rs1 m1 t b2 rs2 m2 ->
      exec_instrs sp b1 rs1 m1 t b2 rs2 m2
  | exec_trans:
      forall sp b1 rs1 m1 t t1 b2 rs2 m2 t2 b3 rs3 m3,
      exec_instrs sp b1 rs1 m1 t1 b2 rs2 m2 ->
      exec_instrs sp b2 rs2 m2 t2 b3 rs3 m3 ->
      t = t1 ** t2 ->
      exec_instrs sp b1 rs1 m1 t b3 rs3 m3

with exec_block: val ->
                 block -> locset -> mem -> trace ->
                 outcome -> locset -> mem -> Prop :=
  | exec_Bgoto:
      forall sp b rs m t s rs' m',
      exec_instrs sp b rs m t (Bgoto s) rs' m' ->
      exec_block sp b rs m t (Cont s) rs' m'
  | exec_Bcond_true:
      forall sp b rs m t cond args ifso ifnot rs' m',
      exec_instrs sp b rs m t (Bcond cond args ifso ifnot) rs' m' ->
      eval_condition cond (reglist args rs') = Some true ->
      exec_block sp b rs m t (Cont ifso) rs' m'
  | exec_Bcond_false:
      forall sp b rs m t cond args ifso ifnot rs' m',
      exec_instrs sp b rs m t (Bcond cond args ifso ifnot) rs' m' ->
      eval_condition cond (reglist args rs') = Some false ->
      exec_block sp b rs m t (Cont ifnot) rs' m'
  | exec_Breturn:
      forall sp b rs m t rs' m',
      exec_instrs sp b rs m t Breturn rs' m' ->
      exec_block sp b rs m t Return rs' m'

with exec_blocks: code -> val ->
                  node -> locset -> mem -> trace ->
                  outcome -> locset -> mem -> Prop :=
  | exec_blocks_refl:
      forall c sp pc rs m,
      exec_blocks c sp pc rs m E0 (Cont pc) rs m
  | exec_blocks_one:
      forall c sp pc b m rs t out rs' m',
      c!pc = Some b ->
      exec_block sp b rs m t out rs' m' ->
      exec_blocks c sp pc rs m t out rs' m'
  | exec_blocks_trans:
      forall c sp pc1 rs1 m1 t t1 pc2 rs2 m2 t2 out rs3 m3,
      exec_blocks c sp pc1 rs1 m1 t1 (Cont pc2) rs2 m2 ->
      exec_blocks c sp pc2 rs2 m2 t2 out rs3 m3 ->
      t = t1 ** t2 ->
      exec_blocks c sp pc1 rs1 m1 t out rs3 m3

with exec_function: fundef -> locset -> mem -> trace ->
                                locset -> mem -> Prop :=
  | exec_funct_internal:
      forall f rs m m1 stk t rs2 m2,
      alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      exec_blocks f.(fn_code) (Vptr stk Int.zero)
                  f.(fn_entrypoint) (call_regs rs) m1 t Return rs2 m2 ->
      exec_function (Internal f) rs m t rs2 (free m2 stk)
  | exec_funct_external:
      forall ef args res rs1 rs2 m t,
      event_match ef args t res ->
      args = List.map rs1 (Conventions.loc_arguments ef.(ef_sig)) ->
      rs2 = Locmap.set (R (Conventions.loc_result ef.(ef_sig))) res rs1 ->
      exec_function (External ef) rs1 m t rs2 m.

End RELSEM.

(** Execution of a whole program boils down to invoking its main
  function.  The result of the program is the return value of the
  main function, to be found in the machine register dictated
  by the calling conventions. *)

Definition exec_program (p: program) (t: trace) (r: val) : Prop :=
  let ge := Genv.globalenv p in
  let m0 := Genv.init_mem p in
  exists b, exists f, exists rs, exists m,
  Genv.find_symbol ge p.(prog_main) = Some b /\
  Genv.find_funct_ptr ge b  = Some f /\
  funsig f = mksignature nil (Some Tint) /\
  exec_function ge f (Locmap.init Vundef) m0 t rs m /\
  rs (R (Conventions.loc_result (funsig f))) = r.

(** We remark that the [exec_blocks] relation is stable if
  the control-flow graph is extended by adding new basic blocks
  at previously unused graph nodes. *)

Section EXEC_BLOCKS_EXTENDS.

Variable ge: genv.
Variable c1 c2: code.
Hypothesis EXT: forall pc, c2!pc = c1!pc \/ c1!pc = None.

Lemma exec_blocks_extends:
  forall sp pc1 rs1 m1 t out rs2 m2,
  exec_blocks ge c1 sp pc1 rs1 m1 t out rs2 m2 ->
  exec_blocks ge c2 sp pc1 rs1 m1 t out rs2 m2.
Proof.
  induction 1. 
  apply exec_blocks_refl.
  apply exec_blocks_one with b. 
    elim (EXT pc); intro; congruence. assumption.
  eapply exec_blocks_trans; eauto.
Qed.

End EXEC_BLOCKS_EXTENDS.

(** * Operations over LTL *)

(** Computation of the possible successors of a basic block.
  This is used for dataflow analyses. *)

Fixpoint successors_aux (b: block) : list node :=
  match b with
  | Bgetstack s r b => successors_aux b
  | Bsetstack r s b => successors_aux b
  | Bop op args res b => successors_aux b
  | Bload chunk addr args dst b => successors_aux b
  | Bstore chunk addr args src b => successors_aux b
  | Bcall sig ros b => successors_aux b
  | Balloc b => successors_aux b
  | Bgoto n => n :: nil
  | Bcond cond args ifso ifnot => ifso :: ifnot :: nil
  | Breturn => nil
  end.

Definition successors (f: function) (pc: node) : list node :=
  match f.(fn_code)!pc with
  | None => nil
  | Some b => successors_aux b
  end.

Lemma successors_aux_invariant:
  forall ge sp b rs m t b' rs' m',
  exec_instrs ge sp b rs m t b' rs' m' ->
  successors_aux b = successors_aux b'.
Proof.
  induction 1; simpl; intros.
  reflexivity.
  inversion H; reflexivity.
  transitivity (successors_aux b2); auto.
Qed.

Lemma successors_correct:
  forall ge f sp pc rs m t pc' rs' m' b,
  f.(fn_code)!pc = Some b ->
  exec_block ge sp b rs m t (Cont pc') rs' m' ->
  In pc' (successors f pc).
Proof.
  intros. unfold successors. rewrite H. inversion H0.
  rewrite (successors_aux_invariant _ _ _ _ _ _ _ _ _ H7); simpl.
  tauto.
  rewrite (successors_aux_invariant _ _ _ _ _ _ _ _ _ H2); simpl.
  tauto.
  rewrite (successors_aux_invariant _ _ _ _ _ _ _ _ _ H2); simpl.
  tauto.
Qed.
