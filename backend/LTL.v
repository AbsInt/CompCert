(** The LTL intermediate language: abstract syntax and semantics.

  LTL (``Location Transfer Language'') is the target language
  for register allocation and the source language for linearization. *)

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
Require Import Locations.
Require Import Conventions.

(** * Abstract syntax *)

(** LTL is close to RTL, but uses locations instead of pseudo-registers. *)

Definition node := positive.

Inductive instruction: Set :=
  | Lnop: node -> instruction
  | Lop: operation -> list loc -> loc -> node -> instruction
  | Lload: memory_chunk -> addressing -> list loc -> loc -> node -> instruction
  | Lstore: memory_chunk -> addressing -> list loc -> loc -> node -> instruction
  | Lcall: signature -> loc + ident -> list loc -> loc -> node -> instruction
  | Ltailcall: signature -> loc + ident -> list loc -> instruction
  | Lalloc: loc -> loc -> node -> instruction
  | Lcond: condition -> list loc -> node -> node -> instruction
  | Lreturn: option loc -> instruction.

Definition code: Set := PTree.t instruction.

Record function: Set := mkfunction {
  fn_sig: signature;
  fn_params: list loc;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node;
  fn_nextpc: node;
  fn_code_wf: forall (pc: node), Plt pc fn_nextpc \/ fn_code!pc = None
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
- Caller-save machine registers have the same values
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

(** [parmov srcs dsts ls] performs the parallel assignment
  of locations [dsts] to the values of the corresponding locations
  [srcs].  *)

Fixpoint parmov (srcs dsts: list loc) (ls: locset) {struct srcs} : locset :=
  match srcs, dsts with
  | s1 :: sl, d1 :: dl => Locmap.set d1 (ls s1) (parmov sl dl ls)
  | _, _ => ls
  end.

Definition set_result_reg (s: signature) (or: option loc) (ls: locset) :=
  match or with 
  | Some r => Locmap.set (R (loc_result s)) (ls r) ls
  | None => ls
  end.

(** The components of an LTL execution state are:

- [State cs f sp pc ls m]: [f] is the function currently executing.
  [sp] is the stack pointer (as in RTL).  [pc] is the current
  program point (CFG node) within the code of [f].
  [ls] maps locations to their current values. [m] is the current
  memory state.
- [Callstate cs f ls m]:
  [f] is the function definition that we are calling.
  [ls] is the values of locations just before the call.
  [m] is the current memory state.
- [Returnstate cs sig ls m]:
  [sig] is the signature of the function that just returned.
  [ls] is the values of locations just before the return.
  [m] is the current memory state.

[cs] is a list of stack frames [Stackframe res f sp ls pc],
where [res] is the location that will receive the result of the call,
[f] is the calling function, [sp] its stack pointer,
[ls] the values of locations just before the call,
and [pc] the program point within [f] of the successor of the
[Lcall] instruction. *)

Inductive stackframe : Set :=
  | Stackframe:
      forall (res: loc) (f: function) (sp: val) (ls: locset) (pc: node), 
      stackframe.

Inductive state : Set :=
  | State:
      forall (stack: list stackframe) (f: function) (sp: val)
             (pc: node) (ls: locset) (m: mem), state
  | Callstate:
      forall (stack: list stackframe) (f: fundef) (ls: locset) (m: mem),
      state
  | Returnstate:
      forall (stack: list stackframe) (sig: signature) (ls: locset) (m: mem),
      state.

Definition parent_locset (stack: list stackframe) : locset :=
  match stack with
  | nil => Locmap.init Vundef
  | Stackframe res f sp ls pc :: stack' => ls
  end.

Variable ge: genv.

Definition find_function (los: loc + ident) (rs: locset) : option fundef :=
  match los with
  | inl l => Genv.find_funct ge (rs l)
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

(** The main difference between the LTL transition relation
  and the RTL transition relation is the handling of function calls.
  In RTL, arguments and results to calls are transmitted via
  [vargs] and [vres] components of [Callstate] and [Returnstate],
  respectively.  The semantics takes care of transferring these values
  between the pseudo-registers of the caller and of the callee.
  
  In lower-level intermediate languages (e.g [Linear], [Mach], [PPC]),
  arguments and results are transmitted implicitly: the generated
  code for the caller arranges for arguments to be left in conventional
  registers and stack locations, as determined by the calling conventions,
  where the function being called will find them.  Similarly,
  conventional registers will be used to pass the result value back
  to the caller.

  In LTL, we take an hybrid view of argument and result passing.
  The LTL code does not contain (yet) instructions for moving
  arguments and results to the conventional registers.  However,
  the dynamic semantics "goes through the motions" of such code:
- The [exec_Lcall] transition from [State] to [Callstate]
  leaves the values of arguments in the conventional locations
  given by [loc_arguments].
- The [exec_function_internal] transition from [Callstate] to [State]
  changes the view of stack slots ([Outgoing] slots slide to
  [Incoming] slots as per [call_regs]), then recovers the
  values of parameters from the conventional locations given by
  [loc_parameters].
- The [exec_Lreturn] transition from [State] to [Returnstate]
  moves the result value to the conventional location [loc_result],
  then restores the values of callee-save locations from
  the location state of the caller, using [return_regs].
- The [exec_return] transition from [Returnstate] to [State]
  reads the result value from the conventional location [loc_result],
  then stores it in the result location for the [Lcall] instruction.

This complicated protocol will make it much easier to prove
the correctness of the [Stacking] pass later, which inserts actual
code that performs all the shuffling of arguments and results
described above.
*)

Inductive step: state -> trace -> state -> Prop :=
  | exec_Lnop:
      forall s f sp pc rs m pc',
      (fn_code f)!pc = Some(Lnop pc') ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Lop:
      forall s f sp pc rs m op args res pc' v,
      (fn_code f)!pc = Some(Lop op args res pc') ->
      eval_operation ge sp op (map rs args) m = Some v ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (Locmap.set res v rs) m)
  | exec_Lload:
      forall s f sp pc rs m chunk addr args dst pc' a v,
      (fn_code f)!pc = Some(Lload chunk addr args dst pc') ->
      eval_addressing ge sp addr (map rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (Locmap.set dst v rs) m)
  | exec_Lstore:
      forall s f sp pc rs m chunk addr args src pc' a m',
      (fn_code f)!pc = Some(Lstore chunk addr args src pc') ->
      eval_addressing ge sp addr (map rs args) = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m')
  | exec_Lcall:
      forall s f sp pc rs m sig ros args res pc' f',
      (fn_code f)!pc = Some(Lcall sig ros args res pc') ->
      find_function ros rs = Some f' ->
      funsig f' = sig ->
      let rs1 := parmov args (loc_arguments sig) rs in
      step (State s f sp pc rs m)
        E0 (Callstate (Stackframe res f sp rs1 pc' :: s) f' rs1 m)
  | exec_Ltailcall:
      forall s f stk pc rs m sig ros args f',
      (fn_code f)!pc = Some(Ltailcall sig ros args) ->
      find_function ros rs = Some f' ->
      funsig f' = sig ->
      let rs1 := parmov args (loc_arguments sig) rs in
      let rs2 := return_regs (parent_locset s) rs1 in
      step (State s f (Vptr stk Int.zero) pc rs m)
        E0 (Callstate s f' rs2 (Mem.free m stk))
  | exec_Lalloc:
      forall s f sp pc rs m pc' arg res sz m' b,
      (fn_code f)!pc = Some(Lalloc arg res pc') ->
      rs arg = Vint sz ->
      Mem.alloc m 0 (Int.signed sz) = (m', b) ->
      let rs1 := Locmap.set (R loc_alloc_argument) (rs arg) rs in
      let rs2 := Locmap.set (R loc_alloc_result) (Vptr b Int.zero) rs1 in
      let rs3 := Locmap.set res (rs2 (R loc_alloc_result)) rs2 in
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs3 m')
  | exec_Lcond_true:
      forall s f sp pc rs m cond args ifso ifnot,
      (fn_code f)!pc = Some(Lcond cond args ifso ifnot) ->
      eval_condition cond (map rs args) m = Some true ->
      step (State s f sp pc rs m)
        E0 (State s f sp ifso rs m)
  | exec_Lcond_false:
      forall s f sp pc rs m cond args ifso ifnot,
      (fn_code f)!pc = Some(Lcond cond args ifso ifnot) ->
      eval_condition cond (map rs args) m = Some false ->
      step (State s f sp pc rs m)
        E0 (State s f sp ifnot rs m)
  | exec_Lreturn:
      forall s f stk pc rs m or,
      (fn_code f)!pc = Some(Lreturn or) ->
      let rs1 := set_result_reg f.(fn_sig) or rs in
      let rs2 := return_regs (parent_locset s) rs1 in
      step (State s f (Vptr stk Int.zero) pc rs m)
        E0 (Returnstate s f.(fn_sig) rs2 (Mem.free m stk))
  | exec_function_internal:
      forall s f rs m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      let rs1 := call_regs rs in
      let rs2 := parmov (loc_parameters f.(fn_sig)) f.(fn_params) rs1 in
      step (Callstate s (Internal f) rs m)
        E0 (State s f (Vptr stk Int.zero) f.(fn_entrypoint) rs2 m')
  | exec_function_external:
      forall s ef t res rs m,
      let args := map rs (Conventions.loc_arguments ef.(ef_sig)) in
      event_match ef args t res ->
      let rs1 :=
        Locmap.set (R (Conventions.loc_result ef.(ef_sig))) res rs in
      step (Callstate s (External ef) rs m)
         t (Returnstate s ef.(ef_sig) rs1 m)
  | exec_return:
      forall res f sp rs0 pc s sig rs m,
      let rs1 := Locmap.set res (rs (R (loc_result sig))) rs in
      step (Returnstate (Stackframe res f sp rs0 pc :: s) 
                        sig rs m)
        E0 (State s f sp pc rs1 m).

End RELSEM.

(** Execution of a whole program boils down to invoking its main
  function.  The result of the program is the return value of the
  main function, to be found in the machine register dictated
  by the calling conventions. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f,
      let ge := Genv.globalenv p in
      let m0 := Genv.init_mem p in
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      initial_state p (Callstate nil f (Locmap.init Vundef) m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall sig rs m r,
      rs (R (loc_result sig)) = Vint r ->
      final_state (Returnstate nil sig rs m) r.

Definition exec_program (p: program) (beh: program_behavior) : Prop :=
  program_behaves step (initial_state p) final_state (Genv.globalenv p) beh.

(** * Operations over LTL *)

(** Computation of the possible successors of an instruction.
  This is used in particular for dataflow analyses. *)

Definition successors (f: function) (pc: node) : list node :=
  match f.(fn_code)!pc with
  | None => nil
  | Some i =>
      match i with
      | Lnop s => s :: nil
      | Lop op args res s => s :: nil
      | Lload chunk addr args dst s => s :: nil
      | Lstore chunk addr args src s => s :: nil
      | Lcall sig ros args res s => s :: nil
      | Ltailcall sig ros args => nil
      | Lalloc arg res s => s :: nil
      | Lcond cond args ifso ifnot => ifso :: ifnot :: nil
      | Lreturn optarg => nil
      end
  end.
