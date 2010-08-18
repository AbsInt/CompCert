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
  reading global or local variables, reading store locations,
  arithmetic operations, function calls, and conditional expressions
  (similar to [e1 ? e2 : e3] in C). 

  Unlike in Cminor (the next intermediate language of the back-end),
  Csharpminor local variables reside in memory, and their addresses can
  be taken using [Eaddrof] expressions.
*)

Inductive constant : Type :=
  | Ointconst: int -> constant          (**r integer constant *)
  | Ofloatconst: float -> constant.     (**r floating-point constant *)

Definition unary_operation : Type := Cminor.unary_operation.
Definition binary_operation : Type := Cminor.binary_operation.

Inductive expr : Type :=
  | Evar : ident -> expr                (**r reading a scalar variable  *)
  | Etempvar : ident -> expr            (**r reading a temporary variable *)
  | Eaddrof : ident -> expr             (**r taking the address of a variable *)
  | Econst : constant -> expr           (**r constants *)
  | Eunop : unary_operation -> expr -> expr  (**r unary operation *)
  | Ebinop : binary_operation -> expr -> expr -> expr (**r binary operation *)
  | Eload : memory_chunk -> expr -> expr (**r memory read *)
  | Econdition : expr -> expr -> expr -> expr. (**r conditional expression *)

(** Statements include expression evaluation, variable assignment,
  memory stores, function calls, an if/then/else conditional,
  infinite loops, blocks and early block exits, and early function returns.
  [Sexit n] terminates prematurely the execution of the [n+1] enclosing
  [Sblock] statements. *)

Definition label := ident.

Inductive stmt : Type :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sset : ident -> expr -> stmt
  | Sstore : memory_chunk -> expr -> expr -> stmt
  | Scall : option ident -> signature -> expr -> list expr -> stmt
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

(** The variables can be either scalar variables
  (whose type, size and signedness are given by a [memory_chunk]
  or array variables (of the indicated sizes).  The only operation
  permitted on an array variable is taking its address. *)

Inductive var_kind : Type :=
  | Vscalar: memory_chunk -> var_kind
  | Varray: Z -> var_kind.

Definition sizeof (lv: var_kind) : Z :=
  match lv with
  | Vscalar chunk => size_chunk chunk
  | Varray sz => Zmax 0 sz
  end.

(** Functions are composed of a return type, a list of parameter names
  with associated memory chunks (parameters must be scalar), a list of
  local variables with associated [var_kind] description, and a
  statement representing the function body.  *)

Definition param_name (p: ident * memory_chunk) := fst p.
Definition param_chunk (p: ident * memory_chunk) := snd p.
Definition variable_name (v: ident * var_kind) := fst v.
Definition variable_kind (v: ident * var_kind) := snd v.

Record function : Type := mkfunction {
  fn_return: option typ;
  fn_params: list (ident * memory_chunk);
  fn_vars: list (ident * var_kind);
  fn_temps: list ident;
  fn_body: stmt
}.

Definition fundef := AST.fundef function.

Definition program : Type := AST.program fundef var_kind.

Definition fn_sig (f: function) :=
  mksignature (List.map type_of_chunk (List.map param_chunk f.(fn_params)))
              f.(fn_return).

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Definition var_of_param (p: ident * memory_chunk) : ident * var_kind :=
  (fst p, Vscalar (snd p)).

Definition fn_variables (f: function) :=
  List.map var_of_param f.(fn_params) ++ f.(fn_vars).

Definition fn_params_names (f: function) := List.map param_name f.(fn_params).
Definition fn_vars_names (f: function) := List.map variable_name f.(fn_vars).

(** * Operational semantics *)

(** Three evaluation environments are involved:
- [genv]: global environments, map symbols and functions to memory blocks,
    and maps symbols to variable informations (type [var_kind])
- [env]: local environments, map local variables 
    to pairs (memory block, variable information)
- [temp_env]: local environments, map temporary variables to
    their current values.
*)

Definition genv := Genv.t fundef var_kind.
Definition env := PTree.t (block * var_kind).
Definition temp_env := PTree.t val.

Definition empty_env : env := PTree.empty (block * var_kind).
Definition empty_temp_env : temp_env := PTree.empty val.

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

Definition eval_binop (op: binary_operation)
                      (arg1 arg2: val) (m: mem): option val :=
  match op, arg1, arg2 with
  | Cminor.Ocmp c, Vptr b1 n1, Vptr b2 n2 =>
      if Mem.valid_pointer m b1 (Int.signed n1)
      && Mem.valid_pointer m b2 (Int.signed n2)
      then Cminor.eval_binop op arg1 arg2
      else None
  | _, _, _ =>
      Cminor.eval_binop op arg1 arg2
  end.

(** Allocation of local variables at function entry.  Each variable is
  bound to the reference to a fresh block of the appropriate size. *)

Inductive alloc_variables: env -> mem ->
                           list (ident * var_kind) ->
                           env -> mem -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables e m nil e m
  | alloc_variables_cons:
      forall e m id lv vars m1 b1 m2 e2,
      Mem.alloc m 0 (sizeof lv) = (m1, b1) ->
      alloc_variables (PTree.set id (b1, lv) e) m1 vars e2 m2 ->
      alloc_variables e m ((id, lv) :: vars) e2 m2.

(** List of blocks mentioned in an environment, with low and high bounds *)

Definition block_of_binding (id_b_lv: ident * (block * var_kind)) :=
  match id_b_lv with (id, (b, lv)) => (b, 0, sizeof lv) end.

Definition blocks_of_env (e: env) : list (block * Z * Z) :=
  List.map block_of_binding (PTree.elements e).

(** Initialization of local variables that are parameters.  The value
  of the corresponding argument is stored into the memory block
  bound to the parameter. *)

Definition val_normalized (v: val) (chunk: memory_chunk) : Prop :=
  Val.load_result chunk v = v.

Inductive bind_parameters: env ->
                           mem -> list (ident * memory_chunk) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall e m,
      bind_parameters e m nil nil m
  | bind_parameters_cons:
      forall e m id chunk params v1 vl b m1 m2,
      PTree.get id e = Some (b, Vscalar chunk) ->
      val_normalized v1 chunk ->
      Mem.store chunk m b 0 v1 = Some m1 ->
      bind_parameters e m1 params vl m2 ->
      bind_parameters e m ((id, chunk) :: params) (v1 :: vl) m2.

Section RELSEM.

Variable ge: genv.

(* Evaluation of the address of a variable: 
   [eval_var_addr prg ge e id b] states that variable [id] 
   in environment [e] evaluates to block [b]. *)

Inductive eval_var_addr: env -> ident -> block -> Prop :=
  | eval_var_addr_local:
      forall e id b vi,
      PTree.get id e = Some (b, vi) ->
      eval_var_addr e id b
  | eval_var_addr_global:
      forall e id b,
      PTree.get id e = None ->
      Genv.find_symbol ge id = Some b ->
      eval_var_addr e id b.

(* Evaluation of a reference to a scalar variable:
   [eval_var_ref prg ge e id b chunk] states
   that variable [id] in environment [e] evaluates to block [b]
   and is associated with the memory chunk [chunk]. *)

Inductive eval_var_ref: env -> ident -> block -> memory_chunk -> Prop :=
  | eval_var_ref_local:
      forall e id b chunk,
      PTree.get id e = Some (b, Vscalar chunk) ->
      eval_var_ref e id b chunk
  | eval_var_ref_global:
      forall e id b gv chunk,
      PTree.get id e = None ->
      Genv.find_symbol ge id = Some b ->
      Genv.find_var_info ge b = Some gv ->
      gvar_info gv = Vscalar chunk ->
      eval_var_ref e id b chunk.

(** Evaluation of an expression: [eval_expr prg e m a v] states
  that expression [a], in initial memory state [m] and local
  environment [e], evaluates to value [v]. *)

Section EVAL_EXPR.

Variable e: env.
Variable le: temp_env.
Variable m: mem.

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Evar: forall id b chunk v,
      eval_var_ref e id b chunk ->
      Mem.load chunk m b 0 = Some v ->
      eval_expr (Evar id) v
  | eval_Etempvar: forall id v,
      le!id = Some v ->
      eval_expr (Etempvar id) v
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
      eval_expr (Eload chunk a) v
  | eval_Econdition: forall a b c v1 vb1 v2,
      eval_expr a v1 ->
      Val.bool_of_val v1 vb1 ->
      eval_expr (if vb1 then b else c) v2 ->
      eval_expr (Econdition a b c) v2.

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

(** Execution of an assignment to a variable. *)

Inductive exec_assign: env -> mem -> ident -> val -> mem -> Prop :=
  exec_assign_intro: forall e m id v b chunk m',
    eval_var_ref e id b chunk ->
    val_normalized v chunk ->
    Mem.store chunk m b 0 v = Some m' ->
    exec_assign e m id v m'.

(*
Inductive exec_opt_assign: env -> mem -> option ident -> val -> mem -> Prop :=
  | exec_assign_none: forall e m v,
      exec_opt_assign e m None v m
  | exec_assign_some: forall e m id v m',
      exec_assign e m id v m' ->
      exec_opt_assign e m (Some id) v m'.
*)

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
      f.(fn_return) = None ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f Sskip k e le m)
        E0 (Returnstate Vundef k m')

  | step_assign: forall f id a k e le m m' v,
      eval_expr e le m a v ->
      exec_assign e m id v m' ->
      step (State f (Sassign id a) k e le m)
        E0 (State f Sskip k e le m')

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

  | step_internal_function: forall f vargs k m m1 m2 e,
      list_norepet (fn_params_names f ++ fn_vars_names f) ->
      alloc_variables empty_env m (fn_variables f) e m1 ->
      bind_parameters e m1 f.(fn_params) vargs m2 ->
      step (Callstate (Internal f) vargs k m)
        E0 (State f f.(fn_body) k e empty_temp_env m2)

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

(** Execution of a whole program: [exec_program p beh]
  holds if the application of [p]'s main function to no arguments
  in the initial memory state for [p] has [beh] as observable
  behavior. *)

Definition exec_program (p: program) (beh: program_behavior) : Prop :=
  program_behaves step (initial_state p) final_state 
                  (Genv.globalenv p) beh.


