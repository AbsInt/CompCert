(** Abstract syntax and semantics for the Cminor language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Op.
Require Import Globalenvs.

(** * Abstract syntax *)

(** Cminor is a low-level imperative language structured in expressions,
  statements, functions and programs.  Expressions include
  reading and writing local variables, reading and writing store locations,
  arithmetic operations, function calls, and conditional expressions
  (similar to [e1 ? e2 : e3] in C).  The [Elet] and [Eletvar] constructs
  enable sharing the computations of subexpressions.  De Bruijn notation
  is used: [Eletvar n] refers to the value bound by then [n+1]-th enclosing
  [Elet] construct.

  A variant [condexpr] of [expr] is used to represent expressions
  which are evaluated for their boolean value only and not their exact value.
*)

Inductive expr : Set :=
  | Evar : ident -> expr
  | Eassign : ident -> expr -> expr
  | Eop : operation -> exprlist -> expr
  | Eload : memory_chunk -> addressing -> exprlist -> expr
  | Estore : memory_chunk -> addressing -> exprlist -> expr -> expr
  | Ecall : signature -> expr -> exprlist -> expr
  | Econdition : condexpr -> expr -> expr -> expr
  | Elet : expr -> expr -> expr
  | Eletvar : nat -> expr

with condexpr : Set :=
  | CEtrue: condexpr
  | CEfalse: condexpr
  | CEcond: condition -> exprlist -> condexpr
  | CEcondition : condexpr -> condexpr -> condexpr -> condexpr

with exprlist : Set :=
  | Enil: exprlist
  | Econs: expr -> exprlist -> exprlist.

(** Statements include expression evaluation, an if/then/else conditional,
  infinite loops, blocks and early block exits, and early function returns.
  [Sexit n] terminates prematurely the execution of the [n+1] enclosing
  [Sblock] statements. *)

Inductive stmt : Set :=
  | Sexpr: expr -> stmt
  | Sifthenelse: condexpr -> stmtlist -> stmtlist -> stmt
  | Sloop: stmtlist -> stmt
  | Sblock: stmtlist -> stmt
  | Sexit: nat -> stmt
  | Sreturn: option expr -> stmt

with stmtlist : Set :=
  | Snil: stmtlist
  | Scons: stmt -> stmtlist -> stmtlist.

(** Functions are composed of a signature, a list of parameter names,
  a list of local variables, and a list of statements representing
  the function body.  Each function can allocate a memory block of
  size [fn_stackspace] on entrance.  This block will be deallocated
  automatically before the function returns.  Pointers into this block
  can be taken with the [Oaddrstack] operator. *)

Record function : Set := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list ident;
  fn_stackspace: Z;
  fn_body: stmtlist
}.

Definition program := AST.program function.

(** * Operational semantics *)

(** The operational semantics for Cminor is given in big-step operational
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

(** Three kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [env]: local environments, map local variables to values;
- [lenv]: let environments, map de Bruijn indices to values.
*)

Definition genv := Genv.t function.
Definition env := PTree.t val.
Definition letenv := list val.

(** The following functions build the initial local environment at
  function entry, binding parameters to the provided arguments and
  initializing local variables to [Vundef]. *)

Fixpoint set_params (vl: list val) (il: list ident) {struct il} : env :=
  match il, vl with
  | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
  | i1 :: is, nil => PTree.set i1 Vundef (set_params nil is)
  | _, _ => PTree.empty val
  end.

Fixpoint set_locals (il: list ident) (e: env) {struct il} : env :=
  match il with
  | nil => e
  | i1 :: is => PTree.set i1 Vundef (set_locals is e)
  end.

Section RELSEM.

Variable ge: genv.

(** Evaluation of an expression: [eval_expr ge sp le e m a e' m' v]
  states that expression [a], in initial local environment [e] and
  memory state [m], evaluates to value [v].  [e'] and [m'] are the final
  local environment and memory state, respectively, reflecting variable
  assignments and memory stores possibly performed by [a].  [ge] and
  [le] are the global environment and let environment respectively, and
  are unchanged during evaluation.  [sp] is the pointer to the memory
  block allocated for this function (stack frame).
*)

Inductive eval_expr:
         val -> letenv ->
         env -> mem -> expr ->
         env -> mem -> val -> Prop :=
  | eval_Evar:
      forall sp le e m id v,
      PTree.get id e = Some v ->
      eval_expr sp le e m (Evar id) e m v
  | eval_Eassign:
      forall sp le e m id a e1 m1 v,
      eval_expr sp le e m a e1 m1 v ->
      eval_expr sp le e m (Eassign id a) (PTree.set id v e1) m1 v
  | eval_Eop:
      forall sp le e m op al e1 m1 vl v,
      eval_exprlist sp le e m al e1 m1 vl ->
      eval_operation ge sp op vl = Some v ->
      eval_expr sp le e m (Eop op al) e1 m1 v
  | eval_Eload:
      forall sp le e m chunk addr al e1 m1 v vl a,
      eval_exprlist sp le e m al e1 m1 vl ->
      eval_addressing ge sp addr vl = Some a ->
      Mem.loadv chunk m1 a = Some v ->
      eval_expr sp le e m (Eload chunk addr al) e1 m1 v
  | eval_Estore:
      forall sp le e m chunk addr al b e1 m1 vl e2 m2 m3 v a,
      eval_exprlist sp le e m al e1 m1 vl ->
      eval_expr sp le e1 m1 b e2 m2 v ->
      eval_addressing ge sp addr vl = Some a ->
      Mem.storev chunk m2 a v = Some m3 ->
      eval_expr sp le e m (Estore chunk addr al b) e2 m3 v
  | eval_Ecall:
      forall sp le e m sig a bl e1 e2 m1 m2 m3 vf vargs vres f,
      eval_expr sp le e m a e1 m1 vf ->
      eval_exprlist sp le e1 m1 bl e2 m2 vargs ->
      Genv.find_funct ge vf = Some f ->
      f.(fn_sig) = sig ->
      eval_funcall m2 f vargs m3 vres ->
      eval_expr sp le e m (Ecall sig a bl) e2 m3 vres
  | eval_Econdition:
      forall sp le e m a b c e1 m1 v1 e2 m2 v2,
      eval_condexpr sp le e m a e1 m1 v1 ->
      eval_expr sp le e1 m1 (if v1 then b else c) e2 m2 v2 ->
      eval_expr sp le e m (Econdition a b c) e2 m2 v2
  | eval_Elet:
      forall sp le e m a b e1 m1 v1 e2 m2 v2,
      eval_expr sp le e m a e1 m1 v1 ->
      eval_expr sp (v1::le) e1 m1 b e2 m2 v2 ->
      eval_expr sp le e m (Elet a b) e2 m2 v2
  | eval_Eletvar:
      forall sp le e m n v,
      nth_error le n = Some v ->
      eval_expr sp le e m (Eletvar n) e m v

(** Evaluation of a condition expression:
  [eval_condexpr ge sp le e m a e' m' b]
  states that condition expression [a] evaluates to the boolean value [b].
  The other parameters are as in [eval_expr].
*)

with eval_condexpr:
         val -> letenv ->
         env -> mem -> condexpr ->
         env -> mem -> bool -> Prop :=
  | eval_CEtrue:
      forall sp le e m,
      eval_condexpr sp le e m CEtrue e m true
  | eval_CEfalse:
      forall sp le e m,
      eval_condexpr sp le e m CEfalse e m false
  | eval_CEcond:
      forall sp le e m cond al e1 m1 vl b,
      eval_exprlist sp le e m al e1 m1 vl ->
      eval_condition cond vl = Some b ->
      eval_condexpr sp le e m (CEcond cond al) e1 m1 b
  | eval_CEcondition:
      forall sp le e m a b c e1 m1 vb1 e2 m2 vb2,
      eval_condexpr sp le e m a e1 m1 vb1 ->
      eval_condexpr sp le e1 m1 (if vb1 then b else c) e2 m2 vb2 ->
      eval_condexpr sp le e m (CEcondition a b c) e2 m2 vb2

(** Evaluation of a list of expressions:
  [eval_exprlist ge sp le al m a e' m' vl]
  states that the list [al] of expressions evaluate 
  to the list [vl] of values.
  The other parameters are as in [eval_expr].
*)

with eval_exprlist:
         val -> letenv ->
         env -> mem -> exprlist ->
         env -> mem -> list val -> Prop :=
  | eval_Enil:
      forall sp le e m,
      eval_exprlist sp le e m Enil e m nil
  | eval_Econs:
      forall sp le e m a bl e1 m1 v e2 m2 vl,
      eval_expr sp le e m a e1 m1 v ->
      eval_exprlist sp le e1 m1 bl e2 m2 vl ->
      eval_exprlist sp le e m (Econs a bl) e2 m2 (v :: vl)

(** Evaluation of a function invocation: [eval_funcall ge m f args m' res]
  means that the function [f], applied to the arguments [args] in
  memory state [m], returns the value [res] in modified memory state [m'].
*)

with eval_funcall:
        mem -> function -> list val ->
        mem -> val -> Prop :=
  | eval_funcall_intro:
      forall m f vargs m1 sp e e2 m2 out vres,
      Mem.alloc m 0 f.(fn_stackspace) = (m1, sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      exec_stmtlist (Vptr sp Int.zero) e m1 f.(fn_body) e2 m2 out ->
      outcome_result_value out f.(fn_sig).(sig_res) vres ->
      eval_funcall m f vargs (Mem.free m2 sp) vres

(** Execution of a statement: [exec_stmt ge sp e m s e' m' out]
  means that statement [s] executes with outcome [out].
  The other parameters are as in [eval_expr]. *)

with exec_stmt:
         val ->
         env -> mem -> stmt ->
         env -> mem -> outcome -> Prop :=
  | exec_Sexpr:
      forall sp e m a e1 m1 v,
      eval_expr sp nil e m a e1 m1 v ->
      exec_stmt sp e m (Sexpr a) e1 m1 Out_normal
  | exec_Sifthenelse:
      forall sp e m a sl1 sl2 e1 m1 v1 e2 m2 out,
      eval_condexpr sp nil e m a e1 m1 v1 ->
      exec_stmtlist sp e1 m1 (if v1 then sl1 else sl2) e2 m2 out ->
      exec_stmt sp e m (Sifthenelse a sl1 sl2) e2 m2 out
  | exec_Sloop_loop:
      forall sp e m sl e1 m1 e2 m2 out,
      exec_stmtlist sp e m sl e1 m1 Out_normal ->
      exec_stmt sp e1 m1 (Sloop sl) e2 m2 out ->
      exec_stmt sp e m (Sloop sl) e2 m2 out
  | exec_Sloop_stop:
      forall sp e m sl e1 m1 out,
      exec_stmtlist sp e m sl e1 m1 out ->
      out <> Out_normal ->
      exec_stmt sp e m (Sloop sl) e1 m1 out
  | exec_Sblock:
      forall sp e m sl e1 m1 out,
      exec_stmtlist sp e m sl e1 m1 out ->
      exec_stmt sp e m (Sblock sl) e1 m1 (outcome_block out)
  | exec_Sexit:
      forall sp e m n,
      exec_stmt sp e m (Sexit n) e m (Out_exit n)
  | exec_Sreturn_none:
      forall sp e m,
      exec_stmt sp e m (Sreturn None) e m (Out_return None)
  | exec_Sreturn_some:
      forall sp e m a e1 m1 v,
      eval_expr sp nil e m a e1 m1 v ->
      exec_stmt sp e m (Sreturn (Some a)) e1 m1 (Out_return (Some v))

(** Execution of a list of statements: [exec_stmtlist ge sp e m sl e' m' out]
  means that the list [sl] of statements executes sequentially
  with outcome [out].  Execution stops at the first statement that
  leads an outcome different from [Out_normal].
  The other parameters are as in [eval_expr]. *)

with exec_stmtlist:
         val ->
         env -> mem -> stmtlist ->
         env -> mem -> outcome -> Prop :=
  | exec_Snil:
      forall sp e m,
      exec_stmtlist sp e m Snil e m Out_normal
  | exec_Scons_continue:
      forall sp e m s sl e1 m1 e2 m2 out,
      exec_stmt sp e m s e1 m1 Out_normal ->
      exec_stmtlist sp e1 m1 sl e2 m2 out ->
      exec_stmtlist sp e m (Scons s sl) e2 m2 out
  | exec_Scons_stop:
      forall sp e m s sl e1 m1 out,
      exec_stmt sp e m s e1 m1 out ->
      out <> Out_normal ->
      exec_stmtlist sp e m (Scons s sl) e1 m1 out.

End RELSEM.

(** Execution of a whole program: [exec_program p r]
  holds if the application of [p]'s main function to no arguments
  in the initial memory state for [p] eventually returns value [r]. *)

Definition exec_program (p: program) (r: val) : Prop :=
  let ge := Genv.globalenv p in
  let m0 := Genv.init_mem p in
  exists b, exists f, exists m,
  Genv.find_symbol ge p.(prog_main) = Some b /\
  Genv.find_funct_ptr ge b = Some f /\
  f.(fn_sig) = mksignature nil (Some Tint) /\
  eval_funcall ge m0 f nil m r.

