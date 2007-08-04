(** The RTL intermediate language: abstract syntax and semantics.

  RTL stands for "Register Transfer Language". This is the first
  intermediate language after Cminor and CminorSel.
*)

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
  | Itailcall: signature -> reg + ident -> list reg -> instruction
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

Definition program := AST.program fundef unit.

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

Inductive stackframe : Set :=
  | Stackframe:
      forall (res: reg) (c: code) (sp: val) (pc: node) (rs: regset), 
      stackframe.

Inductive state : Set :=
  | State:
      forall (stack: list stackframe) (c: code) (sp: val) (pc: node)
             (rs: regset) (m: mem), state
  | Callstate:
      forall (stack: list stackframe) (f: fundef) (args: list val) (m: mem),
      state
  | Returnstate:
      forall (stack: list stackframe) (v: val) (m: mem),
      state.

(** The dynamic semantics of RTL is given in small-step style, as a 
  set of transitions between states.  A state captures the current
  point in the execution.  Three kinds of states appear in the transitions:

- [State cs c sp pc rs m] describes an execution point within a function.
  [c] is the code for the current function (a CFG).
  [sp] is the pointer to the stack block for its current activation
     (as in Cminor).
  [pc] is the current program point (CFG node) within the code [c].
  [rs] gives the current values for the pseudo-registers.
  [m] is the current memory state.
- [Callstate cs f args m] is an intermediate state that appears during
  function calls.
  [f] is the function definition that we are calling.
  [args] (a list of values) are the arguments for this call.
  [m] is the current memory state.
- [Returnstate cs v m] is an intermediate state that appears when a
  function terminates and returns to its caller.
  [v] is the return value and [m] the current memory state.

In all three kinds of states, the [cs] parameter represents the call stack.
It is a list of frames [Stackframe res c sp pc rs].  Each frame represents
a function call in progress.  
[res] is the pseudo-register that will receive the result of the call.
[c] is the code of the calling function.
[sp] is its stack pointer.
[pc] is the program point for the instruction that follows the call.
[rs] is the state of registers in the calling function.
*)

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

(** The transitions are presented as an inductive predicate
  [step ge st1 t st2], where [ge] is the global environment,
  [st1] the initial state, [st2] the final state, and [t] the trace
  of system calls performed during this transition. *)

Inductive step: state -> trace -> state -> Prop :=
  | exec_Inop:
      forall s c sp pc rs m pc',
      c!pc = Some(Inop pc') ->
      step (State s c sp pc rs m)
        E0 (State s c sp pc' rs m)
  | exec_Iop:
      forall s c sp pc rs m op args res pc' v,
      c!pc = Some(Iop op args res pc') ->
      eval_operation ge sp op rs##args m = Some v ->
      step (State s c sp pc rs m)
        E0 (State s c sp pc' (rs#res <- v) m)
  | exec_Iload:
      forall s c sp pc rs m chunk addr args dst pc' a v,
      c!pc = Some(Iload chunk addr args dst pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      step (State s c sp pc rs m)
        E0 (State s c sp pc' (rs#dst <- v) m)
  | exec_Istore:
      forall s c sp pc rs m chunk addr args src pc' a m',
      c!pc = Some(Istore chunk addr args src pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      step (State s c sp pc rs m)
        E0 (State s c sp pc' rs m')
  | exec_Icall:
      forall s c sp pc rs m sig ros args res pc' f,
      c!pc = Some(Icall sig ros args res pc') ->
      find_function ros rs = Some f ->
      funsig f = sig ->
      step (State s c sp pc rs m)
        E0 (Callstate (Stackframe res c sp pc' rs :: s) f rs##args m)
  | exec_Itailcall:
      forall s c stk pc rs m sig ros args f,
      c!pc = Some(Itailcall sig ros args) ->
      find_function ros rs = Some f ->
      funsig f = sig ->
      step (State s c (Vptr stk Int.zero) pc rs m)
        E0 (Callstate s f rs##args (Mem.free m stk))
  | exec_Ialloc:
      forall s c sp pc rs m pc' arg res sz m' b,
      c!pc = Some(Ialloc arg res pc') ->
      rs#arg = Vint sz ->
      Mem.alloc m 0 (Int.signed sz) = (m', b) ->
      step (State s c sp pc rs m)
        E0 (State s c sp pc' (rs#res <- (Vptr b Int.zero)) m')
  | exec_Icond_true:
      forall s c sp pc rs m cond args ifso ifnot,
      c!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition cond rs##args m = Some true ->
      step (State s c sp pc rs m)
        E0 (State s c sp ifso rs m)
  | exec_Icond_false:
      forall s c sp pc rs m cond args ifso ifnot,
      c!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition cond rs##args m = Some false ->
      step (State s c sp pc rs m)
        E0 (State s c sp ifnot rs m)
  | exec_Ireturn:
      forall s c stk pc rs m or,
      c!pc = Some(Ireturn or) ->
      step (State s c (Vptr stk Int.zero) pc rs m)
        E0 (Returnstate s (regmap_optget or Vundef rs) (Mem.free m stk))
  | exec_function_internal:
      forall s f args m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      step (Callstate s (Internal f) args m)
        E0 (State s
                  f.(fn_code)
                  (Vptr stk Int.zero)
                  f.(fn_entrypoint)
                  (init_regs args f.(fn_params))
                  m')
  | exec_function_external:
      forall s ef args res t m,
      event_match ef args t res ->
      step (Callstate s (External ef) args m)
         t (Returnstate s res m)
  | exec_return:
      forall res c sp pc rs s vres m,
      step (Returnstate (Stackframe res c sp pc rs :: s) vres m)
        E0 (State s c sp pc (rs#res <- vres) m).

Lemma exec_Iop':
  forall s c sp pc rs m op args res pc' rs' v,
  c!pc = Some(Iop op args res pc') ->
  eval_operation ge sp op rs##args m = Some v ->
  rs' = (rs#res <- v) ->
  step (State s c sp pc rs m)
    E0 (State s c sp pc' rs' m).
Proof.
  intros. subst rs'. eapply exec_Iop; eauto.
Qed.

Lemma exec_Iload':
  forall s c sp pc rs m chunk addr args dst pc' rs' a v,
  c!pc = Some(Iload chunk addr args dst pc') ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.loadv chunk m a = Some v ->
  rs' = (rs#dst <- v) ->
  step (State s c sp pc rs m)
    E0 (State s c sp pc' rs' m).
Proof.
  intros. subst rs'. eapply exec_Iload; eauto.
Qed.

End RELSEM.

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty call stack. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f,
      let ge := Genv.globalenv p in
      let m0 := Genv.init_mem p in
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      initial_state p (Callstate nil f nil m0).

(** A final state is a [Returnstate] with an empty call stack. *)

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate nil (Vint r) m) r.

Definition exec_program (p: program) (beh: program_behavior) : Prop :=
  program_behaves step (initial_state p) final_state (Genv.globalenv p) beh.

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
      | Itailcall sig ros args => nil
      | Ialloc arg res s => s :: nil
      | Icond cond args ifso ifnot => ifso :: ifnot :: nil
      | Ireturn optarg => nil
      end
  end.

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
