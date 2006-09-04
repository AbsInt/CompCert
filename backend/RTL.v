(** The RTL intermediate language: abstract syntax and semantics.

  RTL (``Register Transfer Language'' is the first intermediate language
  after Cminor.
*)

(*Require Import Relations.*)
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Mem.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.

(** * Abstract syntax *)

(** RTL is organized as instructions, functions and programs.
  Instructions correspond roughly to elementary instructions of the
  target processor, but take their arguments and leave their results
  in pseudo-registers (also called temporaries in textbooks).
  Infinitely many pseudo-registers are available, and each function
  has its own set of pseudo-registers, unaffected by function calls.

  Instructions are organized as a control-flow graph: a function is
  a finite map from ``nodes'' (abstract program points) to instructions,
  and each instruction lists explicitly the nodes of its successors.
*)

Definition node := positive.

Inductive instruction: Set :=
  | Inop: node -> instruction
      (** No operation -- just branch to the successor. *)
  | Iop: operation -> list reg -> reg -> node -> instruction
      (** [Iop op args dest succ] performs the arithmetic operation [op]
          over the values of registers [args], stores the result in [dest],
          and branches to [succ]. *)
  | Iload: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
      (** [Iload chunk addr args dest succ] loads a [chunk] quantity from
          the address determined by the addressing mode [addr] and the
          values of the [args] registers, stores the quantity just read
          into [dest], and branches to [succ]. *)
  | Istore: memory_chunk -> addressing -> list reg -> reg -> node -> instruction
      (** [Istore chunk addr args src succ] stores the value of register
          [src] in the [chunk] quantity at the
          the address determined by the addressing mode [addr] and the
          values of the [args] registers, then branches to [succ]. *)
  | Icall: signature -> reg + ident -> list reg -> reg -> node -> instruction
      (** [Icall sig fn args dest succ] invokes the function determined by
          [fn] (either a function pointer found in a register or a
          function name), giving it the values of registers [args] 
          as arguments.  It stores the return value in [dest] and branches
          to [succ]. *)
  | Ialloc: reg -> reg -> node -> instruction
      (** [Ialloc arg dest succ] allocates a fresh block of size
          the contents of register [arg], stores a pointer to this
          block in [dest], and branches to [succ]. *)
  | Icond: condition -> list reg -> node -> node -> instruction
      (** [Icond cond args ifso ifnot] evaluates the boolean condition
          [cond] over the values of registers [args].  If the condition
          is true, it transitions to [ifso].  If the condition is false,
          it transitions to [ifnot]. *)
  | Ireturn: option reg -> instruction.
      (** [Ireturn] terminates the execution of the current function
          (it has no successor).  It returns the value of the given
          register, or [Vundef] if none is given. *)

Definition code: Set := PTree.t instruction.

Record function: Set := mkfunction {
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node;
  fn_nextpc: node;
  fn_code_wf: forall (pc: node), Plt pc fn_nextpc \/ fn_code!pc = None
}.

(** A function description comprises a control-flow graph (CFG) [fn_code]
    (a partial finite mapping from nodes to instructions).  As in Cminor,
    [fn_sig] is the function signature and [fn_stacksize] the number of bytes
    for its stack-allocated activation record.  [fn_params] is the list
    of registers that are bound to the values of arguments at call time.
    [fn_entrypoint] is the node of the first instruction of the function
    in the CFG.  [fn_code_wf] asserts that all instructions of the function
    have nodes no greater than [fn_nextpc]. *)

Definition fundef := AST.fundef function.

Definition program := AST.program fundef.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.

(** * Operational semantics *)

Definition genv := Genv.t fundef.
Definition regset := Regmap.t val.

Fixpoint init_regs (vl: list val) (rl: list reg) {struct rl} : regset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Regmap.set r1 v1 (init_regs vs rs)
  | _, _ => Regmap.init Vundef
  end.

Section RELSEM.

Variable ge: genv.

Definition find_function
      (ros: reg + ident) (rs: regset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge rs#r
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

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
      eval_operation ge sp op rs##args = Some v ->
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
      find_function ros rs = Some f ->
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
      eval_condition cond rs##args = Some true ->
      exec_instr c sp  pc rs m  E0 ifso rs m
  | exec_Icond_false:
      forall c sp pc rs m cond args ifso ifnot,
      c!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition cond rs##args = Some false ->
      exec_instr c sp  pc rs m  E0 ifnot rs m

(** [exec_instrs ge c sp pc rs m pc' rs' m'] is the reflexive
  transitive closure of [exec_instr].  It corresponds to the execution
  of zero, one or finitely many transitions. *)

with exec_instrs: code -> val ->
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
      exec_instrs c sp pc1 rs1 m1 t3 pc3 rs3 m3

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
      forall f m m1 stk args t pc rs m2 or vres,
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      exec_instrs f.(fn_code) (Vptr stk Int.zero) 
                  f.(fn_entrypoint) (init_regs args f.(fn_params)) m1
                  t pc rs m2 ->
      f.(fn_code)!pc = Some(Ireturn or) ->
      vres = regmap_optget or Vundef rs ->
      exec_function (Internal f) args m t vres (Mem.free m2 stk)
  | exec_funct_external:
      forall ef args m t res,
      event_match ef args t res ->
      exec_function (External ef) args m t res m.

Scheme exec_instr_ind_3 := Minimality for exec_instr Sort Prop
  with exec_instrs_ind_3 := Minimality for exec_instrs Sort Prop
  with exec_function_ind_3 := Minimality for exec_function Sort Prop.

(** Some derived execution rules. *)

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
  eval_operation ge sp op rs##args = Some v ->
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

(** If a transition can take place from [pc], the instruction at [pc]
  is defined in the CFG. *)

Lemma exec_instr_present:
  forall c sp pc rs m t pc' rs' m',
  exec_instr c sp  pc rs m  t pc' rs' m' ->
  c!pc <> None.
Proof.
  induction 1; congruence.
Qed.

Lemma exec_instrs_present:
  forall c sp pc rs m t pc' rs' m',
  exec_instrs c sp  pc rs m  t pc' rs' m' ->
  c!pc' <> None -> c!pc <> None.
Proof.
  induction 1; intros.
  auto.
  eapply exec_instr_present; eauto.
  eauto.
Qed.

End RELSEM.

(** Execution of whole programs.  As in Cminor, we call the ``main'' function
  with no arguments and observe its return value. *)

Definition exec_program (p: program) (t: trace) (r: val) : Prop :=
  let ge := Genv.globalenv p in
  let m0 := Genv.init_mem p in
  exists b, exists f, exists m,
  Genv.find_symbol ge p.(prog_main) = Some b /\
  Genv.find_funct_ptr ge b = Some f /\
  funsig f = mksignature nil (Some Tint) /\
  exec_function ge f nil m0 t r m.

(** * Operations on RTL abstract syntax *)

(** Computation of the possible successors of an instruction.
  This is used in particular for dataflow analyses. *)

Definition successors (f: function) (pc: node) : list node :=
  match f.(fn_code)!pc with
  | None => nil
  | Some i =>
      match i with
      | Inop s => s :: nil
      | Iop op args res s => s :: nil
      | Iload chunk addr args dst s => s :: nil
      | Istore chunk addr args src s => s :: nil
      | Icall sig ros args res s => s :: nil
      | Ialloc arg res s => s :: nil
      | Icond cond args ifso ifnot => ifso :: ifnot :: nil
      | Ireturn optarg => nil
      end
  end.

Lemma successors_correct:
  forall ge f sp pc rs m t pc' rs' m',
  exec_instr ge f.(fn_code) sp pc rs m t pc' rs' m' ->
  In pc' (successors f pc).
Proof.
  intros ge f. unfold successors. generalize (fn_code f).
  induction 1; rewrite H; simpl; tauto.
Qed.

(** Transformation of a RTL function instruction by instruction.
  This applies a given transformation function to all instructions
  of a function and constructs a transformed function from that. *)

Section TRANSF.

Variable transf: node -> instruction -> instruction.

Lemma transf_code_wf:
  forall (c: code) (nextpc: node),
  (forall (pc: node), Plt pc nextpc \/ c!pc = None) ->
  (forall (pc: node), Plt pc nextpc \/ (PTree.map transf c)!pc = None).
Proof.
  intros. elim (H pc); intro.
  left; assumption.
  right. rewrite PTree.gmap. rewrite H0. reflexivity.
Qed.

Definition transf_function (f: function) : function :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (PTree.map transf f.(fn_code))
    f.(fn_entrypoint)
    f.(fn_nextpc)
    (transf_code_wf f.(fn_code) f.(fn_nextpc) f.(fn_code_wf)).

End TRANSF.
