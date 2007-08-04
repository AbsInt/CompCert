(** Abstract syntax and semantics for the Cminor language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Events.
Require Import Values.
Require Import Mem.
Require Import Globalenvs.
Require Import Switch.

(** * Abstract syntax *)

(** Cminor is a low-level imperative language structured in expressions,
  statements, functions and programs.  We first define the constants
  and operators that occur within expressions. *)

Inductive constant : Set :=
  | Ointconst: int -> constant     (**r integer constant *)
  | Ofloatconst: float -> constant (**r floating-point constant *)
  | Oaddrsymbol: ident -> int -> constant (**r address of the symbol plus the offset *)
  | Oaddrstack: int -> constant.   (**r stack pointer plus the given offset *)

Inductive unary_operation : Set :=
  | Ocast8unsigned: unary_operation        (**r 8-bit zero extension  *)
  | Ocast8signed: unary_operation          (**r 8-bit sign extension  *)
  | Ocast16unsigned: unary_operation       (**r 16-bit zero extension  *)
  | Ocast16signed: unary_operation         (**r 16-bit sign extension *)
  | Onegint: unary_operation               (**r integer opposite *)
  | Onotbool: unary_operation              (**r boolean negation  *)
  | Onotint: unary_operation               (**r bitwise complement  *)
  | Onegf: unary_operation                 (**r float opposite *)
  | Oabsf: unary_operation                 (**r float absolute value *)
  | Osingleoffloat: unary_operation        (**r float truncation *)
  | Ointoffloat: unary_operation           (**r integer to float *)
  | Ofloatofint: unary_operation           (**r float to signed integer *)
  | Ofloatofintu: unary_operation.         (**r float to unsigned integer *)

Inductive binary_operation : Set :=
  | Oadd: binary_operation                 (**r integer addition *)
  | Osub: binary_operation                 (**r integer subtraction *)
  | Omul: binary_operation                 (**r integer multiplication *)
  | Odiv: binary_operation                 (**r integer signed division *)
  | Odivu: binary_operation                (**r integer unsigned division *)
  | Omod: binary_operation                 (**r integer signed modulus *)
  | Omodu: binary_operation                (**r integer unsigned modulus *)
  | Oand: binary_operation                 (**r bitwise ``and'' *)
  | Oor: binary_operation                  (**r bitwise ``or'' *)
  | Oxor: binary_operation                 (**r bitwise ``xor'' *)
  | Oshl: binary_operation                 (**r left shift *)
  | Oshr: binary_operation                 (**r right signed shift *)
  | Oshru: binary_operation                (**r right unsigned shift *)
  | Oaddf: binary_operation                (**r float addition *)
  | Osubf: binary_operation                (**r float subtraction *)
  | Omulf: binary_operation                (**r float multiplication *)
  | Odivf: binary_operation                (**r float division *)
  | Ocmp: comparison -> binary_operation   (**r integer signed comparison *)
  | Ocmpu: comparison -> binary_operation  (**r integer unsigned comparison *)
  | Ocmpf: comparison -> binary_operation. (**r float comparison *)

(** Expressions include reading local variables, constants and
  arithmetic operations, reading and writing store locations,
  function calls, and conditional expressions
  (similar to [e1 ? e2 : e3] in C).
  The [Elet] and [Eletvar] constructs enable sharing the computations
  of subexpressions.  De Bruijn notation is used: [Eletvar n] refers
  to the value bound by then [n+1]-th enclosing [Elet] construct. *)

Inductive expr : Set :=
  | Evar : ident -> expr
  | Econst : constant -> expr
  | Eunop : unary_operation -> expr -> expr
  | Ebinop : binary_operation -> expr -> expr -> expr
  | Eload : memory_chunk -> expr -> expr
  | Estore : memory_chunk -> expr -> expr -> expr
  | Ecall : signature -> expr -> exprlist -> expr
  | Econdition : expr -> expr -> expr -> expr
  | Elet : expr -> expr -> expr
  | Eletvar : nat -> expr
  | Ealloc : expr -> expr

with exprlist : Set :=
  | Enil: exprlist
  | Econs: expr -> exprlist -> exprlist.

(** Statements include expression evaluation, assignment to local variables,
  an if/then/else conditional, infinite loops, blocks and early block
  exits, and early function returns.  [Sexit n] terminates prematurely
  the execution of the [n+1] enclosing [Sblock] statements. *)

Inductive stmt : Set :=
  | Sskip: stmt
  | Sexpr: expr -> stmt
  | Sassign : ident -> expr -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: expr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: expr -> list (int * nat) -> nat -> stmt
  | Sreturn: option expr -> stmt
  | Stailcall: signature -> expr -> exprlist -> stmt.

(** Functions are composed of a signature, a list of parameter names,
  a list of local variables, and a  statement representing
  the function body.  Each function can allocate a memory block of
  size [fn_stackspace] on entrance.  This block will be deallocated
  automatically before the function returns.  Pointers into this block
  can be taken with the [Oaddrstack] operator. *)

Record function : Set := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list ident;
  fn_stackspace: Z;
  fn_body: stmt
}.

Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.

(** * Operational semantics *)

(** The operational semantics for Cminor is given in big-step operational
  style.  Expressions evaluate to values, and statements evaluate to
  ``outcomes'' indicating how execution should proceed afterwards. *)

Inductive outcome: Set :=
  | Out_normal: outcome                (**r continue in sequence *)
  | Out_exit: nat -> outcome           (**r terminate [n+1] enclosing blocks *)
  | Out_return: option val -> outcome  (**r return immediately to caller *)
  | Out_tailcall_return: val -> outcome. (**r already returned to caller via a tailcall *)

Definition outcome_block (out: outcome) : outcome :=
  match out with
  | Out_exit O => Out_normal
  | Out_exit (S n) => Out_exit n
  | out => out
  end.

Definition outcome_result_value
    (out: outcome) (retsig: option typ) (vres: val) : Prop :=
  match out, retsig with
  | Out_normal, None => vres = Vundef
  | Out_return None, None => vres = Vundef
  | Out_return (Some v), Some ty => vres = v
  | Out_tailcall_return v, _ => vres = v
  | _, _ => False
  end.

Definition outcome_free_mem
    (out: outcome) (m: mem) (sp: block) : mem :=
  match out with
  | Out_tailcall_return _ => m
  | _ => Mem.free m sp
  end.

(** Three kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [env]: local environments, map local variables to values;
- [lenv]: let environments, map de Bruijn indices to values.
*)

Definition genv := Genv.t fundef.
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

(** Evaluation of constants and operator applications.
    [None] is returned when the computation is undefined, e.g.
    if arguments are of the wrong types, or in case of an integer division
    by zero. *)

Definition eval_constant (sp: val) (cst: constant) : option val :=
  match cst with
  | Ointconst n => Some (Vint n)
  | Ofloatconst n => Some (Vfloat n)
  | Oaddrsymbol s ofs =>
      match Genv.find_symbol ge s with
      | None => None
      | Some b => Some (Vptr b ofs)
      end
  | Oaddrstack ofs =>
      match sp with
      | Vptr b n => Some (Vptr b (Int.add n ofs))
      | _ => None
      end
  end.

Definition eval_unop (op: unary_operation) (arg: val) : option val :=
  match op, arg with
  | Ocast8unsigned, _ => Some (Val.cast8unsigned arg)
  | Ocast8signed, _ => Some (Val.cast8signed arg)
  | Ocast16unsigned, _ => Some (Val.cast16unsigned arg)
  | Ocast16signed, _ => Some (Val.cast16signed arg)
  | Onegint, Vint n1 => Some (Vint (Int.neg n1))
  | Onotbool, Vint n1 => Some (Val.of_bool (Int.eq n1 Int.zero))
  | Onotbool, Vptr b1 n1 => Some Vfalse
  | Onotint, Vint n1 => Some (Vint (Int.not n1))
  | Onegf, Vfloat f1 => Some (Vfloat (Float.neg f1))
  | Oabsf, Vfloat f1 => Some (Vfloat (Float.abs f1))
  | Osingleoffloat, _ => Some (Val.singleoffloat arg)
  | Ointoffloat, Vfloat f1 => Some (Vint (Float.intoffloat f1))
  | Ofloatofint, Vint n1 => Some (Vfloat (Float.floatofint n1))
  | Ofloatofintu, Vint n1 => Some (Vfloat (Float.floatofintu n1))
  | _, _ => None
  end.

Definition eval_compare_null (c: comparison) (n: int) : option val :=
  if Int.eq n Int.zero 
  then match c with Ceq => Some Vfalse | Cne => Some Vtrue | _ => None end
  else None.

Definition eval_binop
            (op: binary_operation) (arg1 arg2: val) (m: mem): option val :=
  match op, arg1, arg2 with
  | Oadd, Vint n1, Vint n2 => Some (Vint (Int.add n1 n2))
  | Oadd, Vint n1, Vptr b2 n2 => Some (Vptr b2 (Int.add n2 n1))
  | Oadd, Vptr b1 n1, Vint n2 => Some (Vptr b1 (Int.add n1 n2))
  | Osub, Vint n1, Vint n2 => Some (Vint (Int.sub n1 n2))
  | Osub, Vptr b1 n1, Vint n2 => Some (Vptr b1 (Int.sub n1 n2))
  | Osub, Vptr b1 n1, Vptr b2 n2 =>
      if eq_block b1 b2 then Some (Vint (Int.sub n1 n2)) else None
  | Omul, Vint n1, Vint n2 => Some (Vint (Int.mul n1 n2))
  | Odiv, Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.divs n1 n2))
  | Odivu, Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.divu n1 n2))
  | Omod, Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.mods n1 n2))
  | Omodu, Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.modu n1 n2))
  | Oand, Vint n1, Vint n2 => Some (Vint (Int.and n1 n2))
  | Oor, Vint n1, Vint n2 => Some (Vint (Int.or n1 n2))
  | Oxor, Vint n1, Vint n2 => Some (Vint (Int.xor n1 n2))
  | Oshl, Vint n1, Vint n2 =>
      if Int.ltu n2 (Int.repr 32) then Some (Vint (Int.shl n1 n2)) else None
  | Oshr, Vint n1, Vint n2 =>
      if Int.ltu n2 (Int.repr 32) then Some (Vint (Int.shr n1 n2)) else None
  | Oshru, Vint n1, Vint n2 =>
      if Int.ltu n2 (Int.repr 32) then Some (Vint (Int.shru n1 n2)) else None
   | Oaddf, Vfloat f1, Vfloat f2 => Some (Vfloat (Float.add f1 f2))
  | Osubf, Vfloat f1, Vfloat f2 => Some (Vfloat (Float.sub f1 f2))
  | Omulf, Vfloat f1, Vfloat f2 => Some (Vfloat (Float.mul f1 f2))
  | Odivf, Vfloat f1, Vfloat f2 => Some (Vfloat (Float.div f1 f2))
  | Ocmp c, Vint n1, Vint n2 =>
      Some (Val.of_bool(Int.cmp c n1 n2))
  | Ocmp c, Vptr b1 n1, Vptr b2 n2 =>
      if valid_pointer m b1 (Int.signed n1)
      && valid_pointer m b2 (Int.signed n2) then
        if eq_block b1 b2 then Some(Val.of_bool(Int.cmp c n1 n2)) else None
      else
        None
  | Ocmp c, Vptr b1 n1, Vint n2 => eval_compare_null c n2
  | Ocmp c, Vint n1, Vptr b2 n2 => eval_compare_null c n1
  | Ocmpu c, Vint n1, Vint n2 =>
      Some (Val.of_bool(Int.cmpu c n1 n2))
  | Ocmpf c, Vfloat f1, Vfloat f2 =>
      Some (Val.of_bool (Float.cmp c f1 f2))
  | _, _, _ => None
  end.

(** Evaluation of an expression: [eval_expr ge sp le e m a t m' v]
  states that expression [a], in initial local environment [e] and
  memory state [m], evaluates to value [v].  [m'] is the final
  memory state, reflecting memory stores possibly performed by [a].
  [t] is the trace of I/O events generated during the evaluation.
  Expressions do not assign variables, therefore the local environment
  [e] is unchanged.  [ge] and [le] are the global environment and let
  environment respectively, and are unchanged during evaluation.  [sp]
  is the pointer to the memory block allocated for this function
  (stack frame).
*)

Inductive eval_expr:
         val -> letenv -> env ->
         mem -> expr -> trace -> mem -> val -> Prop :=
  | eval_Evar:
      forall sp le e m id v,
      PTree.get id e = Some v ->
      eval_expr sp le e m (Evar id) E0 m v
  | eval_Econst:
      forall sp le e m cst v,
      eval_constant sp cst = Some v ->
      eval_expr sp le e m (Econst cst) E0 m v
  | eval_Eunop:
      forall sp le e m op a t m1 v1 v,
      eval_expr sp le e m a t m1 v1 ->
      eval_unop op v1 = Some v ->
      eval_expr sp le e m (Eunop op a) t m1 v
  | eval_Ebinop:
      forall sp le e m op a1 a2 t1 m1 v1 t2 m2 v2 t v,
      eval_expr sp le e m a1 t1 m1 v1 ->
      eval_expr sp le e m1 a2 t2 m2 v2 ->
      eval_binop op v1 v2 m2 = Some v ->
      t = t1 ** t2 ->
      eval_expr sp le e m (Ebinop op a1 a2) t m2 v
  | eval_Eload:
      forall sp le e m chunk a t m1 v1 v,
      eval_expr sp le e m a t m1 v1 ->
      Mem.loadv chunk m1 v1 = Some v ->
      eval_expr sp le e m (Eload chunk a) t m1 v
  | eval_Estore:
      forall sp le e m chunk a1 a2 t t1 m1 v1 t2 m2 v2 m3,
      eval_expr sp le e m a1 t1 m1 v1 ->
      eval_expr sp le e m1 a2 t2 m2 v2 ->
      Mem.storev chunk m2 v1 v2 = Some m3 ->
      t = t1 ** t2 ->
      eval_expr sp le e m (Estore chunk a1 a2) t m3 v2
  | eval_Ecall:
      forall sp le e m sig a bl t t1 m1 t2 m2 t3 m3 vf vargs vres f,
      eval_expr sp le e m a t1 m1 vf ->
      eval_exprlist sp le e m1 bl t2 m2 vargs ->
      Genv.find_funct ge vf = Some f ->
      funsig f = sig ->
      eval_funcall m2 f vargs t3 m3 vres ->
      t = t1 ** t2 ** t3 ->
      eval_expr sp le e m (Ecall sig a bl) t m3 vres
  | eval_Econdition:
      forall sp le e m a1 a2 a3 t t1 m1 v1 b1 t2 m2 v2,
      eval_expr sp le e m a1 t1 m1 v1 ->
      Val.bool_of_val v1 b1 ->
      eval_expr sp le e m1 (if b1 then a2 else a3) t2 m2 v2 ->
      t = t1 ** t2 ->
      eval_expr sp le e m (Econdition a1 a2 a3) t m2 v2
  | eval_Elet:
      forall sp le e m a b t t1 m1 v1 t2 m2 v2,
      eval_expr sp le e m a t1 m1 v1 ->
      eval_expr sp (v1::le) e m1 b t2 m2 v2 ->
      t = t1 ** t2 ->
      eval_expr sp le e m (Elet a b) t m2 v2
  | eval_Eletvar:
      forall sp le e m n v,
      nth_error le n = Some v ->
      eval_expr sp le e m (Eletvar n) E0 m v
  | eval_Ealloc:
      forall sp le e m a t m1 n m2 b,
      eval_expr sp le e m a t m1 (Vint n) ->
      Mem.alloc m1 0 (Int.signed n) = (m2, b) ->
      eval_expr sp le e m (Ealloc a) t m2 (Vptr b Int.zero)

(** Evaluation of a list of expressions:
  [eval_exprlist ge sp le al m a m' vl]
  states that the list [al] of expressions evaluate 
  to the list [vl] of values.
  The other parameters are as in [eval_expr].
*)

with eval_exprlist:
         val -> letenv -> env ->
         mem -> exprlist -> trace -> mem -> list val -> Prop :=
  | eval_Enil:
      forall sp le e m,
      eval_exprlist sp le e m Enil E0 m nil
  | eval_Econs:
      forall sp le e m a bl t t1 m1 v t2 m2 vl,
      eval_expr sp le e m a t1 m1 v ->
      eval_exprlist sp le e m1 bl t2 m2 vl ->
      t = t1 ** t2 ->
      eval_exprlist sp le e m (Econs a bl) t m2 (v :: vl)

(** Evaluation of a function invocation: [eval_funcall ge m f args m' res]
  means that the function [f], applied to the arguments [args] in
  memory state [m], returns the value [res] in modified memory state [m'].
  [t] is the trace of observable events generated during the invocation.
*)

with eval_funcall:
        mem -> fundef -> list val -> trace ->
        mem -> val -> Prop :=
  | eval_funcall_internal:
      forall m f vargs m1 sp e t e2 m2 out vres,
      Mem.alloc m 0 f.(fn_stackspace) = (m1, sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      exec_stmt (Vptr sp Int.zero) e m1 f.(fn_body) t e2 m2 out ->
      outcome_result_value out f.(fn_sig).(sig_res) vres ->
      eval_funcall m (Internal f) vargs t (outcome_free_mem out m2 sp) vres
  | eval_funcall_external:
      forall ef m args t res,
      event_match ef args t res ->
      eval_funcall m (External ef) args t m res

(** Execution of a statement: [exec_stmt ge sp e m s e' m' out]
  means that statement [s] executes with outcome [out].
  [e] is the initial environment and [m] is the initial memory state.
  [e'] is the final environment, reflecting variable assignments performed
  by [s].  [m'] is the final memory state, reflecting memory stores
  performed by [s].  The other parameters are as in [eval_expr]. *)

with exec_stmt:
         val ->
         env -> mem -> stmt -> trace ->
         env -> mem -> outcome -> Prop :=
  | exec_Sskip:
      forall sp e m,
      exec_stmt sp e m Sskip E0 e m Out_normal
  | exec_Sexpr:
      forall sp e m a t m1 v,
      eval_expr sp nil e m a t m1 v ->
      exec_stmt sp e m (Sexpr a) t e m1 Out_normal
  | exec_Sassign:
      forall sp e m id a t m1 v,
      eval_expr sp nil e m a t m1 v ->
      exec_stmt sp e m (Sassign id a) t (PTree.set id v e) m1 Out_normal
  | exec_Sifthenelse:
      forall sp e m a s1 s2 t t1 m1 v1 b1 t2 e2 m2 out,
      eval_expr sp nil e m a t1 m1 v1 ->
      Val.bool_of_val v1 b1 ->
      exec_stmt sp e m1 (if b1 then s1 else s2) t2 e2 m2 out ->
      t = t1 ** t2 ->
      exec_stmt sp e m (Sifthenelse a s1 s2) t e2 m2 out
  | exec_Sseq_continue:
      forall sp e m t s1 t1 e1 m1 s2 t2 e2 m2 out,
      exec_stmt sp e m s1 t1 e1 m1 Out_normal ->
      exec_stmt sp e1 m1 s2 t2 e2 m2 out ->
      t = t1 ** t2 ->
      exec_stmt sp e m (Sseq s1 s2) t e2 m2 out
  | exec_Sseq_stop:
      forall sp e m t s1 s2 e1 m1 out,
      exec_stmt sp e m s1 t e1 m1 out ->
      out <> Out_normal ->
      exec_stmt sp e m (Sseq s1 s2) t e1 m1 out
  | exec_Sloop_loop:
      forall sp e m s t t1 e1 m1 t2 e2 m2 out,
      exec_stmt sp e m s t1 e1 m1 Out_normal ->
      exec_stmt sp e1 m1 (Sloop s) t2 e2 m2 out ->
      t = t1 ** t2 ->
      exec_stmt sp e m (Sloop s) t e2 m2 out
  | exec_Sloop_stop:
      forall sp e m t s e1 m1 out,
      exec_stmt sp e m s t e1 m1 out ->
      out <> Out_normal ->
      exec_stmt sp e m (Sloop s) t e1 m1 out
  | exec_Sblock:
      forall sp e m s t e1 m1 out,
      exec_stmt sp e m s t e1 m1 out ->
      exec_stmt sp e m (Sblock s) t e1 m1 (outcome_block out)
  | exec_Sexit:
      forall sp e m n,
      exec_stmt sp e m (Sexit n) E0 e m (Out_exit n)
  | exec_Sswitch:
      forall sp e m a cases default t1 m1 n,
      eval_expr sp nil e m a t1 m1 (Vint n) ->
      exec_stmt sp e m (Sswitch a cases default)
                t1 e m1 (Out_exit (switch_target n default cases))
  | exec_Sreturn_none:
      forall sp e m,
      exec_stmt sp e m (Sreturn None) E0 e m (Out_return None)
  | exec_Sreturn_some:
      forall sp e m a t m1 v,
      eval_expr sp nil e m a t m1 v ->
      exec_stmt sp e m (Sreturn (Some a)) t e m1 (Out_return (Some v))
  | exec_Stailcall:
      forall sp e m sig a bl t t1 m1 t2 m2 t3 m3 vf vargs vres f,
      eval_expr (Vptr sp Int.zero) nil e m a t1 m1 vf ->
      eval_exprlist (Vptr sp Int.zero) nil e m1 bl t2 m2 vargs ->
      Genv.find_funct ge vf = Some f ->
      funsig f = sig ->
      eval_funcall (Mem.free m2 sp) f vargs t3 m3 vres ->
      t = t1 ** t2 ** t3 ->
      exec_stmt (Vptr sp Int.zero) e m (Stailcall sig a bl) t e m3 (Out_tailcall_return vres).

Scheme eval_expr_ind4 := Minimality for eval_expr Sort Prop
  with eval_exprlist_ind4 := Minimality for eval_exprlist Sort Prop
  with eval_funcall_ind4 := Minimality for eval_funcall Sort Prop
  with exec_stmt_ind4 := Minimality for exec_stmt Sort Prop.

End RELSEM.

(** Execution of a whole program: [exec_program p t r]
  holds if the application of [p]'s main function to no arguments
  in the initial memory state for [p] performs the input/output
  operations described in the trace [t], and eventually returns value [r].
*)

Definition exec_program (p: program) (t: trace) (r: val) : Prop :=
  let ge := Genv.globalenv p in
  let m0 := Genv.init_mem p in
  exists b, exists f, exists m,
  Genv.find_symbol ge p.(prog_main) = Some b /\
  Genv.find_funct_ptr ge b = Some f /\
  funsig f = mksignature nil (Some Tint) /\
  eval_funcall ge m0 f nil t m r.

