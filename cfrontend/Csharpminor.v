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
Require Import Mem.
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

Inductive constant : Set :=
  | Ointconst: int -> constant          (**r integer constant *)
  | Ofloatconst: float -> constant.     (**r floating-point constant *)

Definition unary_operation : Set := Cminor.unary_operation.
Definition binary_operation : Set := Cminor.binary_operation.

Inductive expr : Set :=
  | Evar : ident -> expr                (**r reading a scalar variable  *)
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

Inductive stmt : Set :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sstore : memory_chunk -> expr -> expr -> stmt
  | Scall : option ident -> signature -> expr -> list expr -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: expr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: expr -> list (int * nat) -> nat -> stmt
  | Sreturn: option expr -> stmt.

(** The variables can be either scalar variables
  (whose type, size and signedness are given by a [memory_chunk]
  or array variables (of the indicated sizes).  The only operation
  permitted on an array variable is taking its address. *)

Inductive var_kind : Set :=
  | Vscalar: memory_chunk -> var_kind
  | Varray: Z -> var_kind.

(** Functions are composed of a signature, a list of parameter names
  with associated memory chunks (parameters must be scalar), a list of
  local variables with associated [var_kind] description, and a
  statement representing the function body.  *)

Record function : Set := mkfunction {
  fn_sig: signature;
  fn_params: list (ident * memory_chunk);
  fn_vars: list (ident * var_kind);
  fn_body: stmt
}.

Definition fundef := AST.fundef function.

Definition program : Set := AST.program fundef var_kind.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.

(** * Operational semantics *)

(** The operational semantics for Csharpminor is given in big-step operational
  style.  Expressions evaluate to values, and statements evaluate to
  ``outcomes'' indicating how execution should proceed afterwards. *)

Inductive outcome: Set :=
  | Out_normal: outcome                (**r continue in sequence *)
  | Out_exit: nat -> outcome           (**r terminate [n+1] enclosing blocks *)
  | Out_return: option val -> outcome. (**r return immediately to caller *)

Definition outcome_result_value
                 (out: outcome) (ot: option typ) (v: val) : Prop :=
  match out, ot with
  | Out_normal, None => v = Vundef
  | Out_return None, None => v = Vundef
  | Out_return (Some v'), Some ty => v = v'
  | _, _ => False
  end.

Definition outcome_block (out: outcome) : outcome :=
  match out with
  | Out_normal => Out_normal
  | Out_exit O => Out_normal
  | Out_exit (S n) => Out_exit n
  | Out_return optv => Out_return optv
  end.

Fixpoint switch_target (n: int) (dfl: nat) (cases: list (int * nat))
                       {struct cases} : nat :=
  match cases with
  | nil => dfl
  | (n1, lbl1) :: rem => if Int.eq n n1 then lbl1 else switch_target n dfl rem
  end.

(** Three kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [gvarenv]: map global variables to variable informations (type [var_kind]);
- [env]: local environments, map local variables 
    to memory blocks and variable informations.
*)

Definition genv := Genv.t fundef.
Definition gvarenv := PTree.t var_kind.
Definition env := PTree.t (block * var_kind).
Definition empty_env : env := PTree.empty (block * var_kind).

Definition sizeof (lv: var_kind) : Z :=
  match lv with
  | Vscalar chunk => size_chunk chunk
  | Varray sz => Zmax 0 sz
  end.

Definition fn_variables (f: function) :=
  List.map
    (fun id_chunk => (fst id_chunk, Vscalar (snd id_chunk))) f.(fn_params)
  ++ f.(fn_vars).

Definition fn_params_names (f: function) :=
  List.map (@fst ident memory_chunk) f.(fn_params).

Definition fn_vars_names (f: function) :=
  List.map (@fst ident var_kind) f.(fn_vars).

Definition global_var_env (p: program): gvarenv :=
  List.fold_left
    (fun gve x => match x with (id, init, k) => PTree.set id k gve end)
    p.(prog_vars) (PTree.empty var_kind).

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
      if valid_pointer m b1 (Int.signed n1)
      && valid_pointer m b2 (Int.signed n2)
      then Cminor.eval_binop op arg1 arg2
      else None
  | _, _, _ =>
      Cminor.eval_binop op arg1 arg2
  end.

(** Allocation of local variables at function entry.  Each variable is
  bound to the reference to a fresh block of the appropriate size. *)

Inductive alloc_variables: env -> mem ->
                           list (ident * var_kind) ->
                           env -> mem -> list block -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables e m nil e m nil
  | alloc_variables_cons:
      forall e m id lv vars m1 b1 m2 e2 lb,
      Mem.alloc m 0 (sizeof lv) = (m1, b1) ->
      alloc_variables (PTree.set id (b1, lv) e) m1 vars e2 m2 lb ->
      alloc_variables e m ((id, lv) :: vars) e2 m2 (b1 :: lb).

(** Initialization of local variables that are parameters.  The value
  of the corresponding argument is stored into the memory block
  bound to the parameter. *)

Inductive bind_parameters: env ->
                           mem -> list (ident * memory_chunk) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall e m,
      bind_parameters e m nil nil m
  | bind_parameters_cons:
      forall e m id chunk params v1 vl b m1 m2,
      PTree.get id e = Some (b, Vscalar chunk) ->
      Mem.store chunk m b 0 v1 = Some m1 ->
      bind_parameters e m1 params vl m2 ->
      bind_parameters e m ((id, chunk) :: params) (v1 :: vl) m2.

Section RELSEM.

Variable prg: program.
Let ge := Genv.globalenv prg.

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
      forall e id b chunk,
      PTree.get id e = None ->
      Genv.find_symbol ge id = Some b ->
      PTree.get id (global_var_env prg) = Some (Vscalar chunk) ->
      eval_var_ref e id b chunk.

(** Evaluation of an expression: [eval_expr prg e m a v] states
  that expression [a], in initial memory state [m] and local
  environment [e], evaluates to value [v]. *)

Section EVAL_EXPR.

Variable e: env.
Variable m: mem.

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Evar: forall id b chunk v,
      eval_var_ref e id b chunk ->
      Mem.load chunk m b 0 = Some v ->
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
    Mem.store chunk m b 0 v = Some m' ->
    exec_assign e m id v m'.

Inductive exec_opt_assign: env -> mem -> option ident -> val -> mem -> Prop :=
  | exec_assign_none: forall e m v,
      exec_opt_assign e m None v m
  | exec_assign_some: forall e m id v m',
      exec_assign e m id v m' ->
      exec_opt_assign e m (Some id) v m'.

(** Evaluation of a function invocation: [eval_funcall prg m f args t m' res]
  means that the function [f], applied to the arguments [args] in
  memory state [m], returns the value [res] in modified memory state [m'].
  [t] is the trace of observable events performed during the call. *)

Inductive eval_funcall:
        mem -> fundef -> list val -> trace ->
        mem -> val -> Prop :=
  | eval_funcall_internal:
      forall m f vargs e m1 lb m2 t m3 out vres,
      list_norepet (fn_params_names f ++ fn_vars_names f) ->
      alloc_variables empty_env m (fn_variables f) e m1 lb ->
      bind_parameters e m1 f.(fn_params) vargs m2 ->
      exec_stmt e m2 f.(fn_body) t m3 out ->
      outcome_result_value out f.(fn_sig).(sig_res) vres ->
      eval_funcall m (Internal f) vargs t (Mem.free_list m3 lb) vres
  | eval_funcall_external:
      forall m ef vargs t vres,
      event_match ef vargs t vres ->
      eval_funcall m (External ef) vargs t m vres

(** Execution of a statement: [exec_stmt prg e m s t m' out]
  means that statement [s] executes with outcome [out].
  [m] is the initial memory state, [m'] the final memory state,
  and [t] the trace of events performed.
  The other parameters are as in [eval_expr]. *)

with exec_stmt:
         env ->
         mem -> stmt -> trace ->
         mem -> outcome -> Prop :=
  | exec_Sskip:
      forall e m,
      exec_stmt e m Sskip E0 m Out_normal
  | exec_Sassign:
      forall e m id a v m',
      eval_expr e m a v ->
      exec_assign e m id v m' ->
      exec_stmt e m (Sassign id a) E0 m' Out_normal
  | exec_Sstore:
      forall e m chunk a b v1 v2 m',
      eval_expr e m a v1 ->
      eval_expr e m b v2 ->
      Mem.storev chunk m v1 v2 = Some m' ->
      exec_stmt e m (Sstore chunk a b) E0 m' Out_normal
  | exec_Scall:
      forall e m optid sig a bl vf vargs f t m1 vres m2,
      eval_expr e m a vf ->
      eval_exprlist e m bl vargs ->
      Genv.find_funct ge vf = Some f ->
      funsig f = sig ->
      eval_funcall m f vargs t m1 vres ->
      exec_opt_assign e m1 optid vres m2 ->
      exec_stmt e m (Scall optid sig a bl) t m2 Out_normal
  | exec_Sseq_continue:
      forall e m s1 s2 t1 t2 m1 m2 t out,
      exec_stmt e m s1 t1 m1 Out_normal ->
      exec_stmt e m1 s2 t2 m2 out ->
      t = t1 ** t2 ->
      exec_stmt e m (Sseq s1 s2) t m2 out
  | exec_Sseq_stop:
      forall e m s1 s2 t1 m1 out,
      exec_stmt e m s1 t1 m1 out ->
      out <> Out_normal ->
      exec_stmt e m (Sseq s1 s2) t1 m1 out
  | exec_Sifthenelse:
      forall e m a sl1 sl2 v vb t m' out,
      eval_expr e m a v ->
      Val.bool_of_val v vb ->
      exec_stmt e m (if vb then sl1 else sl2) t m' out ->
      exec_stmt e m (Sifthenelse a sl1 sl2) t m' out
  | exec_Sloop_loop:
      forall e m sl t1 m1 t2 m2 out t,
      exec_stmt e m sl t1 m1 Out_normal ->
      exec_stmt e m1 (Sloop sl) t2 m2 out ->
      t = t1 ** t2 ->
      exec_stmt e m (Sloop sl) t m2 out
  | exec_Sloop_stop:
      forall e m sl t1 m1 out,
      exec_stmt e m sl t1 m1 out ->
      out <> Out_normal ->
      exec_stmt e m (Sloop sl) t1 m1 out
  | exec_Sblock:
      forall e m sl t1 m1 out,
      exec_stmt e m sl t1 m1 out ->
      exec_stmt e m (Sblock sl) t1 m1 (outcome_block out)
  | exec_Sexit:
      forall e m n,
      exec_stmt e m (Sexit n) E0 m (Out_exit n)
  | exec_Sswitch:
      forall e m a cases default n,
      eval_expr e m a (Vint n) ->
      exec_stmt e m (Sswitch a cases default)
               E0 m (Out_exit (switch_target n default cases))
  | exec_Sreturn_none:
      forall e m,
      exec_stmt e m (Sreturn None) E0 m (Out_return None)
  | exec_Sreturn_some:
      forall e m a v,
      eval_expr e m a v ->
      exec_stmt e m (Sreturn (Some a)) E0 m (Out_return (Some v)).

Scheme eval_funcall_ind2 := Minimality for eval_funcall Sort Prop
  with exec_stmt_ind2 := Minimality for exec_stmt Sort Prop.

(** Coinductive semantics for divergence. *)

Inductive block_seq_context: (stmt -> stmt) -> Prop :=
  | block_seq_context_base_1:
      block_seq_context (fun x => Sblock x)
  | block_seq_context_base_2: forall s,
      block_seq_context (fun x => Sseq x s)
  | block_seq_context_ctx_1: forall ctx,
      block_seq_context ctx ->
      block_seq_context (fun x => Sblock (ctx x))
  | block_seq_context_ctx_2: forall s ctx,
      block_seq_context ctx ->
      block_seq_context (fun x => Sseq (ctx x) s).

CoInductive evalinf_funcall:
        mem -> fundef -> list val -> traceinf -> Prop :=
  | evalinf_funcall_internal:
      forall m f vargs e m1 lb m2 t,
      list_norepet (fn_params_names f ++ fn_vars_names f) ->
      alloc_variables empty_env m (fn_variables f) e m1 lb ->
      bind_parameters e m1 f.(fn_params) vargs m2 ->
      execinf_stmt e m2 f.(fn_body) t ->
      evalinf_funcall m (Internal f) vargs t

with execinf_stmt:
         env -> mem -> stmt -> traceinf -> Prop :=
  | execinf_Scall:
      forall e m optid sig a bl vf vargs f t,
      eval_expr e m a vf ->
      eval_exprlist e m bl vargs ->
      Genv.find_funct ge vf = Some f ->
      funsig f = sig ->
      evalinf_funcall m f vargs t ->
      execinf_stmt e m (Scall optid sig a bl) t
  | execinf_Sseq_1:
      forall e m s1 s2 t,
      execinf_stmt e m s1 t ->
      execinf_stmt e m (Sseq s1 s2) t
  | execinf_Sseq_2:
      forall e m s1 s2 t1 t2 m1 t,
      exec_stmt e m s1 t1 m1 Out_normal ->
      execinf_stmt e m1 s2 t2 ->
      t = t1 *** t2 ->
      execinf_stmt e m (Sseq s1 s2) t
  | execinf_Sifthenelse:
      forall e m a sl1 sl2 v vb t,
      eval_expr e m a v ->
      Val.bool_of_val v vb ->
      execinf_stmt e m (if vb then sl1 else sl2) t ->
      execinf_stmt e m (Sifthenelse a sl1 sl2) t
  | execinf_Sloop_body:
      forall e m sl t,
      execinf_stmt e m sl t ->
      execinf_stmt e m (Sloop sl) t
  | execinf_Sloop_loop:
      forall e m sl t1 m1 t2 t,
      exec_stmt e m sl t1 m1 Out_normal ->
      execinf_stmt e m1 (Sloop sl) t2 ->
      t = t1 *** t2 ->
      execinf_stmt e m (Sloop sl) t
  | execinf_Sblock:
      forall e m sl t,
      execinf_stmt e m sl t ->
      execinf_stmt e m (Sblock sl) t
  | execinf_stutter:
      forall n e m s t,
      execinf_stmt_N n e m s t ->
      execinf_stmt e m s t
  | execinf_Sloop_block:
      forall e m sl t1 m1 t2 t,
      exec_stmt e m sl t1 m1 Out_normal ->
      execinf_stmt e m1 (Sblock (Sloop sl)) t2 ->
      t = t1 *** t2 ->
      execinf_stmt e m (Sloop sl) t

with execinf_stmt_N:
         nat -> env -> mem -> stmt -> traceinf -> Prop :=
  | execinf_context: forall n e m s t ctx,
      execinf_stmt e m s t -> block_seq_context ctx ->
      execinf_stmt_N n e m (ctx s) t
  | execinf_sleep: forall n e m s t,
      execinf_stmt_N n e m s t ->
      execinf_stmt_N (S n) e m s t.

Lemma execinf_stmt_N_inv:
  forall n e m s t,
  execinf_stmt_N n e m s t ->
  match s with
  | Sblock s1 => execinf_stmt e m s1 t
  | Sseq s1 s2 => execinf_stmt e m s1 t
  | _ => False
  end.
Proof.
  assert (BASECASE: forall e m s t ctx,
          execinf_stmt e m s t -> block_seq_context ctx ->
          match ctx s with
          | Sblock s1 => execinf_stmt e m s1 t
          | Sseq s1 s2 => execinf_stmt e m s1 t
          | _ => False
          end).
  intros. inv H0.
  auto.
  auto.
  apply execinf_stutter with O. apply execinf_context; eauto. 
  apply execinf_stutter with O. apply execinf_context; eauto.

  induction n; intros; inv H.
  apply BASECASE; auto.
  apply BASECASE; auto.
  eapply IHn; eauto.
Qed.

Lemma execinf_Sblock_inv:
  forall e m s t,
  execinf_stmt e m (Sblock s) t ->
  execinf_stmt e m s t.
Proof.
  intros. inv H.
  auto.
  exact (execinf_stmt_N_inv _ _ _ _ _ H0). 
Qed.

End RELSEM.

(** Execution of a whole program: [exec_program p beh]
  holds if the application of [p]'s main function to no arguments
  in the initial memory state for [p] has [beh] as observable
  behavior. *)

Inductive exec_program (p: program): program_behavior -> Prop :=
  | program_terminates:
      forall b f t m r,
      let ge := Genv.globalenv p in
      let m0 := Genv.init_mem p in
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      eval_funcall p m0 f nil t m (Vint r) ->
      exec_program p (Terminates t r)
  | program_diverges:
      forall b f t,
      let ge := Genv.globalenv p in
      let m0 := Genv.init_mem p in
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      evalinf_funcall p m0 f nil t ->
      exec_program p (Diverges t).
