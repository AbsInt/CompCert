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

(** The Linear intermediate language: abstract syntax and semantcs *)

(** The Linear language is a variant of LTLin where arithmetic
    instructions operate on machine registers (type [mreg]) instead
    of arbitrary locations.  Special instructions [Lgetstack] and
    [Lsetstack] are provided to access stack slots. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import Conventions.

(** * Abstract syntax *)

Definition label := positive.

Inductive instruction: Type :=
  | Lgetstack: slot -> mreg -> instruction
  | Lsetstack: mreg -> slot -> instruction
  | Lop: operation -> list mreg -> mreg -> instruction
  | Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Lcall: signature -> mreg + ident -> instruction
  | Ltailcall: signature -> mreg + ident -> instruction
  | Lbuiltin: external_function -> list mreg -> mreg -> instruction
  | Lannot: external_function -> list loc -> instruction
  | Llabel: label -> instruction
  | Lgoto: label -> instruction
  | Lcond: condition -> list mreg -> label -> instruction
  | Ljumptable: mreg -> list label -> instruction
  | Lreturn: instruction.

Definition code: Type := list instruction.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Definition genv := Genv.t fundef unit.
Definition locset := Locmap.t.

(** * Operational semantics *)

(** Looking up labels in the instruction list.  *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Llabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Llabel lbl else instr <> Llabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

(** [find_label lbl c] returns a list of instruction, suffix of the
  code [c], that immediately follows the [Llabel lbl] pseudo-instruction.
  If the label [lbl] is multiply-defined, the first occurrence is
  retained.  If the label [lbl] is not defined, [None] is returned. *)

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
  end.

Section RELSEM.

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

Definition reglist (rs: locset) (rl: list mreg) : list val :=
  List.map (fun r => rs (R r)) rl.

(** Calling conventions are reflected at the level of location sets
  (environments mapping locations to values) by the following two 
  functions.  

  [call_regs caller] returns the location set at function entry,
  as a function of the location set [caller] of the calling function.
- Temporary registers are undefined.
- Other machine registers have the same values as in the caller.
- Incoming stack slots (used for parameter passing) have the same
  values as the corresponding outgoing stack slots (used for argument
  passing) in the caller.
- Local and outgoing stack slots are initialized to undefined values.
*) 

Definition call_regs (caller: locset) : locset :=
  fun (l: loc) =>
    match l with
    | R r => if In_dec Loc.eq (R r) temporaries then Vundef else caller (R r)
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
        if In_dec Loc.eq (R r) temporaries then
          callee (R r)
        else if In_dec Loc.eq (R r) destroyed_at_call then
          callee (R r)
        else
          caller (R r)
    | S s => caller (S s)
    end.

(** Temporaries destroyed across operations *)

Definition undef_op (op: operation) (rs: locset) :=
  match op with
  | Omove => Locmap.undef destroyed_at_move rs
  | _ => Locmap.undef temporaries rs
  end.

Definition undef_getstack (s: slot) (rs: locset) :=
  match s with
  | Incoming _ _ => Locmap.set (R IT1) Vundef rs
  | _ => rs
  end.

Definition undef_setstack (rs: locset) :=
  Locmap.undef destroyed_at_move rs.

(** Linear execution states. *)

Inductive stackframe: Type :=
  | Stackframe:
      forall (f: function)         (**r calling function *)
             (sp: val)             (**r stack pointer in calling function *)
             (rs: locset)          (**r location state in calling function *)
             (c: code),            (**r program point in calling function *)
      stackframe.

Inductive state: Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r function currently executing *)
             (sp: val)                (**r stack pointer *)
             (c: code)                (**r current program point *)
             (rs: locset)             (**r location state *)
             (m: mem),                (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (rs: locset)             (**r location state at point of call *)
             (m: mem),                (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (rs: locset)             (**r location state at point of return *)
             (m: mem),                (**r memory state *)
      state.

(** [parent_locset cs] returns the mapping of values for locations
  of the caller function. *)

Definition parent_locset (stack: list stackframe) : locset :=
  match stack with
  | nil => Locmap.init Vundef
  | Stackframe f sp ls c :: stack' => ls
  end.

(** The main difference between the Linear transition relation
  and the LTL transition relation is the handling of function calls.
  In LTL, arguments and results to calls are transmitted via
  [vargs] and [vres] components of [Callstate] and [Returnstate],
  respectively.  The semantics takes care of transferring these values
  between the locations of the caller and of the callee.
  
  In Linear and lower-level languages (Mach, PPC), arguments and
  results are transmitted implicitly: the generated code for the
  caller arranges for arguments to be left in conventional registers
  and stack locations, as determined by the calling conventions, where
  the function being called will find them.  Similarly, conventional
  registers will be used to pass the result value back to the caller.
  This is reflected in the definition of [Callstate] and [Returnstate] 
  above, where a whole location state [rs] is passed instead of just
  the values of arguments or returns as in LTL.

  These location states passed across calls are treated in a way that
  reflects the callee-save/caller-save convention:
- The [exec_Lcall] transition from [State] to [Callstate]
  saves the current location state [ls] in the call stack,
  and passes it to the callee.
- The [exec_function_internal] transition from [Callstate] to [State]
  changes the view of stack slots ([Outgoing] slots slide to
  [Incoming] slots as per [call_regs]).
- The [exec_Lreturn] transition from [State] to [Returnstate]
  restores the values of callee-save locations from
  the location state of the caller, using [return_regs].

This protocol makes it much easier to later prove the correctness of
the [Stacking] pass, which inserts actual code that performs the
saving and restoring of callee-save registers described above.
*)

Inductive step: state -> trace -> state -> Prop :=
  | exec_Lgetstack:
      forall s f sp sl r b rs m,
      step (State s f sp (Lgetstack sl r :: b) rs m)
        E0 (State s f sp b (Locmap.set (R r) (rs (S sl)) (undef_getstack sl rs)) m)
  | exec_Lsetstack:
      forall s f sp r sl b rs m,
      step (State s f sp (Lsetstack r sl :: b) rs m)
        E0 (State s f sp b (Locmap.set (S sl) (rs (R r)) (undef_setstack rs)) m)
  | exec_Lop:
      forall s f sp op args res b rs m v,
      eval_operation ge sp op (reglist rs args) m = Some v ->
      step (State s f sp (Lop op args res :: b) rs m)
        E0 (State s f sp b (Locmap.set (R res) v (undef_op op rs)) m)
  | exec_Lload:
      forall s f sp chunk addr args dst b rs m a v,
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      step (State s f sp (Lload chunk addr args dst :: b) rs m)
        E0 (State s f sp b (Locmap.set (R dst) v (undef_temps rs)) m)
  | exec_Lstore:
      forall s f sp chunk addr args src b rs m m' a,
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.storev chunk m a (rs (R src)) = Some m' ->
      step (State s f sp (Lstore chunk addr args src :: b) rs m)
        E0 (State s f sp b (undef_temps rs) m')
  | exec_Lcall:
      forall s f sp sig ros b rs m f',
      find_function ros rs = Some f' ->
      sig = funsig f' ->
      step (State s f sp (Lcall sig ros :: b) rs m)
        E0 (Callstate (Stackframe f sp rs b:: s) f' rs m)
  | exec_Ltailcall:
      forall s f stk sig ros b rs m f' m',
      find_function ros rs = Some f' ->
      sig = funsig f' ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Int.zero) (Ltailcall sig ros :: b) rs m)
        E0 (Callstate s f' (return_regs (parent_locset s) rs) m')
  | exec_Lbuiltin:
      forall s f sp rs m ef args res b t v m',
      external_call ef ge (reglist rs args) m t v m' ->
      step (State s f sp (Lbuiltin ef args res :: b) rs m)
         t (State s f sp b (Locmap.set (R res) v (undef_temps rs)) m')
  | exec_Lannot:
      forall s f sp rs m ef args b t v m',
      external_call ef ge (map rs args) m t v m' ->
      step (State s f sp (Lannot ef args :: b) rs m)
         t (State s f sp b rs m')
  | exec_Llabel:
      forall s f sp lbl b rs m,
      step (State s f sp (Llabel lbl :: b) rs m)
        E0 (State s f sp b rs m)
  | exec_Lgoto:
      forall s f sp lbl b rs m b',
      find_label lbl f.(fn_code) = Some b' ->
      step (State s f sp (Lgoto lbl :: b) rs m)
        E0 (State s f sp b' rs m)
  | exec_Lcond_true:
      forall s f sp cond args lbl b rs m b',
      eval_condition cond (reglist rs args) m = Some true ->
      find_label lbl f.(fn_code) = Some b' ->
      step (State s f sp (Lcond cond args lbl :: b) rs m)
        E0 (State s f sp b' (undef_temps rs) m)
  | exec_Lcond_false:
      forall s f sp cond args lbl b rs m,
      eval_condition cond (reglist rs args) m = Some false ->
      step (State s f sp (Lcond cond args lbl :: b) rs m)
        E0 (State s f sp b (undef_temps rs) m)
  | exec_Ljumptable:
      forall s f sp arg tbl b rs m n lbl b',
      rs (R arg) = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      find_label lbl f.(fn_code) = Some b' ->
      step (State s f sp (Ljumptable arg tbl :: b) rs m)
        E0 (State s f sp b' (undef_temps rs) m)
  | exec_Lreturn:
      forall s f stk b rs m m',
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Int.zero) (Lreturn :: b) rs m)
        E0 (Returnstate s (return_regs (parent_locset s) rs) m')
  | exec_function_internal:
      forall s f rs m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      step (Callstate s (Internal f) rs m)
        E0 (State s f (Vptr stk Int.zero) f.(fn_code) (call_regs rs) m')
  | exec_function_external:
      forall s ef args res rs1 rs2 m t m',
      external_call ef ge args m t res m' ->
      args = List.map rs1 (loc_arguments (ef_sig ef)) ->
      rs2 = Locmap.set (R (loc_result (ef_sig ef))) res rs1 ->
      step (Callstate s (External ef) rs1 m)
         t (Returnstate s rs2 m')
  | exec_return:
      forall s f sp rs0 c rs m,
      step (Returnstate (Stackframe f sp rs0 c :: s) rs m)
        E0 (State s f sp c rs m).

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      initial_state p (Callstate nil f (Locmap.init Vundef) m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs (R (loc_result (mksignature nil (Some Tint)))) = Vint r ->
      final_state (Returnstate nil rs m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).
