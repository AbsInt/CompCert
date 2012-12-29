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

(** Abstract syntax and semantics for the Csharpminor language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Cminor.
Require Import Smallstep.

(** Abstract syntax *)

(** Csharpminor is a low-level imperative language structured in expressions,
  statements, functions and programs.  Expressions include
  reading temporary variables, taking the address of a variable,
  constants, arithmetic operations, and dereferencing addresses. *)

Inductive constant : Type :=
  | Ointconst: int -> constant          (**r integer constant *)
  | Ofloatconst: float -> constant.     (**r floating-point constant *)

Definition unary_operation : Type := Cminor.unary_operation.
Definition binary_operation : Type := Cminor.binary_operation.

Inductive expr : Type :=
  | Evar : ident -> expr                (**r reading a temporary variable  *)
  | Eaddrof : ident -> expr             (**r taking the address of a variable *)
  | Econst : constant -> expr           (**r constants *)
  | Eunop : unary_operation -> expr -> expr  (**r unary operation *)
  | Ebinop : binary_operation -> expr -> expr -> expr (**r binary operation *)
  | Eload : memory_chunk -> expr -> expr. (**r memory read *)

(** Statements include expression evaluation, temporary variable assignment,
  memory stores, function calls, an if/then/else conditional,
  infinite loops, blocks and early block exits, and early function returns.
  [Sexit n] terminates prematurely the execution of the [n+1] enclosing
  [Sblock] statements. *)

Definition label := ident.

Inductive stmt : Type :=
  | Sskip: stmt
  | Sset : ident -> expr -> stmt
  | Sstore : memory_chunk -> expr -> expr -> stmt
  | Scall : option ident -> signature -> expr -> list expr -> stmt
  | Sbuiltin : option ident -> external_function -> list expr -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: expr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: expr -> lbl_stmt -> stmt
  | Sreturn: option expr -> stmt
  | Slabel: label -> stmt -> stmt
  | Sgoto: label -> stmt

with lbl_stmt : Type :=
  | LSdefault: stmt -> lbl_stmt
  | LScase: int -> stmt -> lbl_stmt -> lbl_stmt.

(** Functions are composed of a return type, a list of parameter names,
  a list of local variables with their sizes, a list of temporary variables,
  and a statement representing the function body.  *)

Record function : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list (ident * Z);
  fn_temps: list ident;
  fn_body: stmt
}.

Definition fundef := AST.fundef function.

Definition program : Type := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

(** * Operational semantics *)

(** Three evaluation environments are involved:
- [genv]: global environments, map symbols and functions to memory blocks,
    and maps symbols to variable informations (type [var_kind])
- [env]: local environments, map local variables 
    to pairs (memory block, size)
- [temp_env]: local environments, map temporary variables to
    their current values.
*)

Definition genv := Genv.t fundef unit.
Definition env := PTree.t (block * Z).
Definition temp_env := PTree.t val.

Definition empty_env : env := PTree.empty (block * Z).
Definition empty_temp_env : temp_env := PTree.empty val.

(** Initialization of temporary variables *)

Fixpoint create_undef_temps (temps: list ident) : temp_env :=
  match temps with
  | nil => PTree.empty val
  | id :: temps' => PTree.set id Vundef (create_undef_temps temps')
 end.

(** Initialization of temporaries that are parameters. *)

Fixpoint bind_parameters (formals: list ident) (args: list val)
                         (le: temp_env) : option temp_env :=
 match formals, args with
 | nil, nil => Some le
 | id :: xl, v :: vl => bind_parameters xl vl (PTree.set id v le)
 | _, _ => None
 end. 

(** Continuations *)

Inductive cont: Type :=
  | Kstop: cont                         (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kblock: cont -> cont                (**r exit a block, then do cont *)
  | Kcall: option ident -> function -> env -> temp_env -> cont -> cont.
                                        (**r return to caller *)

(** States *)

Inductive state: Type :=
  | State:                      (**r Execution within a function *)
      forall (f: function)              (**r currently executing function  *)
             (s: stmt)                  (**r statement under consideration *)
             (k: cont)                  (**r its continuation -- what to do next *)
             (e: env)                   (**r current local environment *)
             (le: temp_env)             (**r current temporary environment *)
             (m: mem),                  (**r current memory state *)
      state
  | Callstate:                  (**r Invocation of a function *)
      forall (f: fundef)                (**r function to invoke *)
             (args: list val)           (**r arguments provided by caller *)
             (k: cont)                  (**r what to do next  *)
             (m: mem),                  (**r memory state *)
      state
  | Returnstate:                (**r Return from a function *)
      forall (v: val)                   (**r Return value *)
             (k: cont)                  (**r what to do next *)
             (m: mem),                  (**r memory state *)
      state.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kblock k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

(** Resolve [switch] statements. *)

Fixpoint select_switch (n: int) (sl: lbl_stmt) {struct sl} : lbl_stmt :=
  match sl with
  | LSdefault _ => sl
  | LScase c s sl' => if Int.eq c n then sl else select_switch n sl'
  end.

Fixpoint seq_of_lbl_stmt (sl: lbl_stmt) : stmt :=
  match sl with
  | LSdefault s => s
  | LScase c s sl' => Sseq s (seq_of_lbl_stmt sl')
  end.

(** Find the statement and manufacture the continuation 
  corresponding to a label *)

Fixpoint find_label (lbl: label) (s: stmt) (k: cont) 
                    {struct s}: option (stmt * cont) :=
  match s with
  | Sseq s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sloop s1 =>
      find_label lbl s1 (Kseq (Sloop s1) k)
  | Sblock s1 =>
      find_label lbl s1 (Kblock k)
  | Sswitch a sl =>
      find_label_ls lbl sl k
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end

with find_label_ls (lbl: label) (sl: lbl_stmt) (k: cont) 
                   {struct sl}: option (stmt * cont) :=
  match sl with
  | LSdefault s => find_label lbl s k
  | LScase _ s sl' =>
      match find_label lbl s (Kseq (seq_of_lbl_stmt sl') k) with
      | Some sk => Some sk
      | None => find_label_ls lbl sl' k
      end
  end.

(** Evaluation of operator applications. *)

Definition eval_constant (cst: constant) : option val :=
  match cst with
  | Ointconst n => Some (Vint n)
  | Ofloatconst n => Some (Vfloat n)
  end.

Definition eval_unop := Cminor.eval_unop.

Definition eval_binop := Cminor.eval_binop.

(** Allocation of local variables at function entry.  Each variable is
  bound to the reference to a fresh block of the appropriate size. *)

Inductive alloc_variables: env -> mem ->
                           list (ident * Z) ->
                           env -> mem -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables e m nil e m
  | alloc_variables_cons:
      forall e m id sz vars m1 b1 m2 e2,
      Mem.alloc m 0 sz = (m1, b1) ->
      alloc_variables (PTree.set id (b1, sz) e) m1 vars e2 m2 ->
      alloc_variables e m ((id, sz) :: vars) e2 m2.

(** List of blocks mentioned in an environment, with low and high bounds *)

Definition block_of_binding (id_b_sz: ident * (block * Z)) :=
  match id_b_sz with (id, (b, sz)) => (b, 0, sz) end.

Definition blocks_of_env (e: env) : list (block * Z * Z) :=
  List.map block_of_binding (PTree.elements e).

Section RELSEM.

Variable ge: genv.

(* Evaluation of the address of a variable: 
   [eval_var_addr prg ge e id b] states that variable [id] 
   in environment [e] evaluates to block [b]. *)

Inductive eval_var_addr: env -> ident -> block -> Prop :=
  | eval_var_addr_local:
      forall e id b sz,
      PTree.get id e = Some (b, sz) ->
      eval_var_addr e id b
  | eval_var_addr_global:
      forall e id b,
      PTree.get id e = None ->
      Genv.find_symbol ge id = Some b ->
      eval_var_addr e id b.

(** Evaluation of an expression: [eval_expr prg e m a v] states
  that expression [a], in initial memory state [m] and local
  environment [e], evaluates to value [v]. *)

Section EVAL_EXPR.

Variable e: env.
Variable le: temp_env.
Variable m: mem.

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Evar: forall id v,
      le!id = Some v ->
      eval_expr (Evar id) v
  | eval_Eaddrof: forall id b,
      eval_var_addr e id b ->
      eval_expr (Eaddrof id) (Vptr b Int.zero)
  | eval_Econst: forall cst v,
      eval_constant cst = Some v ->
      eval_expr (Econst cst) v
  | eval_Eunop: forall op a1 v1 v,
      eval_expr a1 v1 ->
      eval_unop op v1 = Some v ->
      eval_expr (Eunop op a1) v
  | eval_Ebinop: forall op a1 a2 v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      eval_binop op v1 v2 m = Some v ->
      eval_expr (Ebinop op a1 a2) v
  | eval_Eload: forall chunk a v1 v,
      eval_expr a v1 ->
      Mem.loadv chunk m v1 = Some v ->
      eval_expr (Eload chunk a) v.

(** Evaluation of a list of expressions:
  [eval_exprlist prg e m al vl] states that the list [al] of
  expressions evaluate to the list [vl] of values.  The other
  parameters are as in [eval_expr]. *)

Inductive eval_exprlist: list expr -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist nil nil
  | eval_Econs: forall a1 al v1 vl,
      eval_expr a1 v1 -> eval_exprlist al vl ->
      eval_exprlist (a1 :: al) (v1 :: vl).

End EVAL_EXPR.


(** One step of execution *)

Inductive step: state -> trace -> state -> Prop :=

  | step_skip_seq: forall f s k e le m,
      step (State f Sskip (Kseq s k) e le m)
        E0 (State f s k e le m)
  | step_skip_block: forall f k e le m,
      step (State f Sskip (Kblock k) e le m)
        E0 (State f Sskip k e le m)
  | step_skip_call: forall f k e le m m',
      is_call_cont k ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f Sskip k e le m)
        E0 (Returnstate Vundef k m')

  | step_set: forall f id a k e le m v,
      eval_expr e le m a v ->
      step (State f (Sset id a) k e le m)
        E0 (State f Sskip k e (PTree.set id v le) m)

  | step_store: forall f chunk addr a k e le m vaddr v m',
      eval_expr e le m addr vaddr ->
      eval_expr e le m a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      step (State f (Sstore chunk addr a) k e le m)
        E0 (State f Sskip k e le m')

  | step_call: forall f optid sig a bl k e le m vf vargs fd,
      eval_expr e le m a vf ->
      eval_exprlist e le m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      step (State f (Scall optid sig a bl) k e le m)
        E0 (Callstate fd vargs (Kcall optid f e le k) m)

  | step_builtin: forall f optid ef bl k e le m vargs t vres m',
      eval_exprlist e le m bl vargs ->
      external_call ef ge vargs m t vres m' ->
      step (State f (Sbuiltin optid ef bl) k e le m)
         t (State f Sskip k e (Cminor.set_optvar optid vres le) m')

  | step_seq: forall f s1 s2 k e le m,
      step (State f (Sseq s1 s2) k e le m)
        E0 (State f s1 (Kseq s2 k) e le m)

  | step_ifthenelse: forall f a s1 s2 k e le m v b,
      eval_expr e le m a v ->
      Val.bool_of_val v b ->
      step (State f (Sifthenelse a s1 s2) k e le m)
        E0 (State f (if b then s1 else s2) k e le m)

  | step_loop: forall f s k e le m,
      step (State f (Sloop s) k e le m)
        E0 (State f s (Kseq (Sloop s) k) e le m)

  | step_block: forall f s k e le m,
      step (State f (Sblock s) k e le m)
        E0 (State f s (Kblock k) e le m)

  | step_exit_seq: forall f n s k e le m,
      step (State f (Sexit n) (Kseq s k) e le m)
        E0 (State f (Sexit n) k e le m)
  | step_exit_block_0: forall f k e le m,
      step (State f (Sexit O) (Kblock k) e le m)
        E0 (State f Sskip k e le m)
  | step_exit_block_S: forall f n k e le m,
      step (State f (Sexit (S n)) (Kblock k) e le m)
        E0 (State f (Sexit n) k e le m)

  | step_switch: forall f a cases k e le m n,
      eval_expr e le m a (Vint n) ->
      step (State f (Sswitch a cases) k e le m)
        E0 (State f (seq_of_lbl_stmt (select_switch n cases)) k e le m)

  | step_return_0: forall f k e le m m',
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f (Sreturn None) k e le m)
        E0 (Returnstate Vundef (call_cont k) m')
  | step_return_1: forall f a k e le m v m',
      eval_expr e le m a v ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f (Sreturn (Some a)) k e le m)
        E0 (Returnstate v (call_cont k) m')
  | step_label: forall f lbl s k e le m,
      step (State f (Slabel lbl s) k e le m)
        E0 (State f s k e le m)

  | step_goto: forall f lbl k e le m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
      step (State f (Sgoto lbl) k e le m)
        E0 (State f s' k' e le m)

  | step_internal_function: forall f vargs k m m1 e le,
      list_norepet (map fst f.(fn_vars)) ->
      list_norepet f.(fn_params) ->
      list_disjoint f.(fn_params) f.(fn_temps) ->
      alloc_variables empty_env m (fn_vars f) e m1 ->
      bind_parameters f.(fn_params) vargs (create_undef_temps f.(fn_temps)) = Some le ->
      step (Callstate (Internal f) vargs k m)
        E0 (State f f.(fn_body) k e le m1)

  | step_external_function: forall ef vargs k m t vres m',
      external_call ef ge vargs m t vres m' ->
      step (Callstate (External ef) vargs k m)
         t (Returnstate vres k m')        

  | step_return: forall v optid f e le k m,
      step (Returnstate v (Kcall optid f e le k) m)
        E0 (State f Sskip k e (Cminor.set_optvar optid v le) m).

End RELSEM.

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty continuation. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      initial_state p (Callstate f nil Kstop m0).

(** A final state is a [Returnstate] with an empty continuation. *)

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate (Vint r) Kstop m) r.

(** Wrapping up these definitions in a small-step semantics. *)

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).
