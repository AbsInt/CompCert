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

(** Abstract syntax *)

(** Csharpminor is a low-level imperative language structured in expressions,
  statements, functions and programs.  Expressions include
  reading global or local variables, reading store locations,
  arithmetic operations, function calls, and conditional expressions
  (similar to [e1 ? e2 : e3] in C).  The [Elet] and [Eletvar] constructs
  enable sharing the computations of subexpressions.  De Bruijn notation
  is used: [Eletvar n] refers to the value bound by then [n+1]-th enclosing
  [Elet] construct.

  Unlike in Cminor (the next intermediate language of the back-end),
  Csharpminor local variables reside in memory, and their address can
  be taken using [Eaddrof] expressions.

  Another difference with Cminor is that Csharpminor is entirely 
  processor-neutral. In particular, Csharpminor uses a standard set of
  operations: it does not reflect processor-specific operations nor
  addressing modes. *)

Inductive operation : Set :=
  | Ointconst: int -> operation         (**r integer constant *)
  | Ofloatconst: float -> operation     (**r floating-point constant *)
  | Ocast8unsigned: operation           (**r 8-bit zero extension  *)
  | Ocast8signed: operation             (**r 8-bit sign extension  *)
  | Ocast16unsigned: operation          (**r 16-bit zero extension  *)
  | Ocast16signed: operation            (**r 16-bit sign extension *)
  | Onotint: operation                  (**r bitwise complement  *)
  | Oadd: operation                     (**r integer addition *)
  | Osub: operation                     (**r integer subtraction *)
  | Omul: operation                     (**r integer multiplication *)
  | Odiv: operation                     (**r integer signed division *)
  | Odivu: operation                    (**r integer unsigned division *)
  | Omod: operation                     (**r integer signed modulus *)
  | Omodu: operation                    (**r integer unsigned modulus *)
  | Oand: operation                     (**r bitwise ``and'' *)
  | Oor: operation                      (**r bitwise ``or'' *)
  | Oxor: operation                     (**r bitwise ``xor'' *)
  | Oshl: operation                     (**r left shift *)
  | Oshr: operation                     (**r right signed shift *)
  | Oshru: operation                    (**r right unsigned shift *)
  | Onegf: operation                    (**r float opposite *)
  | Oabsf: operation                    (**r float absolute value *)
  | Oaddf: operation                    (**r float addition *)
  | Osubf: operation                    (**r float subtraction *)
  | Omulf: operation                    (**r float multiplication *)
  | Odivf: operation                    (**r float division *)
  | Osingleoffloat: operation           (**r float truncation *)
  | Ointoffloat: operation              (**r integer to float *)
  | Ofloatofint: operation              (**r float to signed integer *)
  | Ofloatofintu: operation             (**r float to unsigned integer *)
  | Ocmp: comparison -> operation       (**r integer signed comparison *)
  | Ocmpu: comparison -> operation      (**r integer unsigned comparison *)
  | Ocmpf: comparison -> operation.     (**r float comparison *)

Inductive expr : Set :=
  | Evar : ident -> expr                (**r reading a scalar variable  *)
  | Eaddrof : ident -> expr             (**r taking the address of a variable *)
  | Eop : operation -> exprlist -> expr (**r arithmetic operation *)
  | Eload : memory_chunk -> expr -> expr (**r memory read *)
  | Ecall : signature -> expr -> exprlist -> expr (**r function call *)
  | Econdition : expr -> expr -> expr -> expr (**r conditional expression *)
  | Elet : expr -> expr -> expr         (**r let binding  *)
  | Eletvar : nat -> expr               (**r reference to a let-bound variable *)
  | Ealloc : expr -> expr               (**r memory allocation *)

with exprlist : Set :=
  | Enil: exprlist
  | Econs: expr -> exprlist -> exprlist.

(** Statements include expression evaluation, variable assignment,
  memory stores, an if/then/else conditional,
  infinite loops, blocks and early block exits, and early function returns.
  [Sexit n] terminates prematurely the execution of the [n+1] enclosing
  [Sblock] statements. *)

Inductive stmt : Set :=
  | Sskip: stmt
  | Sexpr: expr -> stmt
  | Sassign : ident -> expr -> stmt
  | Sstore : memory_chunk -> expr -> expr -> stmt
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

(** Four kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [gvarenv]: map global variables to var info;
- [env]: local environments, map local variables to memory blocks + var info;
- [lenv]: let environments, map de Bruijn indices to values.
*)
Definition genv := Genv.t fundef.
Definition gvarenv := PTree.t var_kind.
Definition env := PTree.t (block * var_kind).
Definition empty_env : env := PTree.empty (block * var_kind).
Definition letenv := list val.

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

Definition eval_compare_null (c: comparison) (n: int) : option val :=
  if Int.eq n Int.zero 
  then match c with Ceq => Some Vfalse | Cne => Some Vtrue | _ => None end
  else None.

Definition eval_operation (op: operation) (vl: list val) (m: mem): option val :=
  match op, vl with
  | Ointconst n, nil => Some (Vint n)
  | Ofloatconst n, nil => Some (Vfloat n)
  | Ocast8unsigned, Vint n1 :: nil => Some (Vint (Int.cast8unsigned n1))
  | Ocast8signed, Vint n1 :: nil => Some (Vint (Int.cast8signed n1))
  | Ocast16unsigned, Vint n1 :: nil => Some (Vint (Int.cast16unsigned n1))
  | Ocast16signed, Vint n1 :: nil => Some (Vint (Int.cast16signed n1))
  | Onotint, Vint n1 :: nil => Some (Vint (Int.not n1))
  | Oadd, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.add n1 n2))
  | Oadd, Vint n1 :: Vptr b2 n2 :: nil => Some (Vptr b2 (Int.add n2 n1))
  | Oadd, Vptr b1 n1 :: Vint n2 :: nil => Some (Vptr b1 (Int.add n1 n2))
  | Osub, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.sub n1 n2))
  | Osub, Vptr b1 n1 :: Vint n2 :: nil => Some (Vptr b1 (Int.sub n1 n2))
  | Osub, Vptr b1 n1 :: Vptr b2 n2 :: nil =>
      if eq_block b1 b2 then Some (Vint (Int.sub n1 n2)) else None
  | Omul, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.mul n1 n2))
  | Odiv, Vint n1 :: Vint n2 :: nil =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.divs n1 n2))
  | Odivu, Vint n1 :: Vint n2 :: nil =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.divu n1 n2))
  | Omod, Vint n1 :: Vint n2 :: nil =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.mods n1 n2))
  | Omodu, Vint n1 :: Vint n2 :: nil =>
      if Int.eq n2 Int.zero then None else Some (Vint (Int.modu n1 n2))
  | Oand, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.and n1 n2))
  | Oor, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.or n1 n2))
  | Oxor, Vint n1 :: Vint n2 :: nil => Some (Vint (Int.xor n1 n2))
  | Oshl, Vint n1 :: Vint n2 :: nil =>
      if Int.ltu n2 (Int.repr 32) then Some (Vint (Int.shl n1 n2)) else None
  | Oshr, Vint n1 :: Vint n2 :: nil =>
      if Int.ltu n2 (Int.repr 32) then Some (Vint (Int.shr n1 n2)) else None
  | Oshru, Vint n1 :: Vint n2 :: nil =>
      if Int.ltu n2 (Int.repr 32) then Some (Vint (Int.shru n1 n2)) else None
  | Onegf, Vfloat f1 :: nil => Some (Vfloat (Float.neg f1))
  | Oabsf, Vfloat f1 :: nil => Some (Vfloat (Float.abs f1))
  | Oaddf, Vfloat f1 :: Vfloat f2 :: nil => Some (Vfloat (Float.add f1 f2))
  | Osubf, Vfloat f1 :: Vfloat f2 :: nil => Some (Vfloat (Float.sub f1 f2))
  | Omulf, Vfloat f1 :: Vfloat f2 :: nil => Some (Vfloat (Float.mul f1 f2))
  | Odivf, Vfloat f1 :: Vfloat f2 :: nil => Some (Vfloat (Float.div f1 f2))
  | Osingleoffloat, Vfloat f1 :: nil =>
      Some (Vfloat (Float.singleoffloat f1))
  | Ointoffloat, Vfloat f1 :: nil => 
      Some (Vint (Float.intoffloat f1))
  | Ofloatofint, Vint n1 :: nil => 
      Some (Vfloat (Float.floatofint n1))
  | Ofloatofintu, Vint n1 :: nil => 
      Some (Vfloat (Float.floatofintu n1))
  | Ocmp c, Vint n1 :: Vint n2 :: nil =>
      Some (Val.of_bool(Int.cmp c n1 n2))
  | Ocmp c, Vptr b1 n1 :: Vptr b2 n2 :: nil =>
      if valid_pointer m b1 (Int.signed n1)
      && valid_pointer m b2 (Int.signed n2) then
        if eq_block b1 b2 then Some(Val.of_bool(Int.cmp c n1 n2)) else None
      else
        None
  | Ocmp c, Vptr b1 n1 :: Vint n2 :: nil => eval_compare_null c n2
  | Ocmp c, Vint n1 :: Vptr b2 n2 :: nil => eval_compare_null c n1
  | Ocmpu c, Vint n1 :: Vint n2 :: nil =>
      Some (Val.of_bool(Int.cmpu c n1 n2))
  | Ocmpf c, Vfloat f1 :: Vfloat f2 :: nil =>
      Some (Val.of_bool (Float.cmp c f1 f2))
  | _, _ => None
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

(** Evaluation of an expression: [eval_expr prg le e m a m' v] states
  that expression [a], in initial memory state [m], evaluates to value
  [v].  [m'] is the final memory state, respectively, reflecting
  memory stores possibly performed by [a].  [e] and [le] are the
  local environment and let environment respectively. *)

Inductive eval_expr:
         letenv -> env ->
         mem -> expr -> trace -> mem -> val -> Prop :=
  | eval_Evar:
      forall le e m id b chunk v,
      eval_var_ref e id b chunk ->
      Mem.load chunk m b 0 = Some v ->
      eval_expr le e m (Evar id) E0 m v
  | eval_Eaddrof:
      forall le e m id b,
      eval_var_addr e id b ->
      eval_expr le e m (Eaddrof id) E0 m (Vptr b Int.zero)
  | eval_Eop:
      forall le e m op al t m1 vl v,
      eval_exprlist le e m al t m1 vl ->
      eval_operation op vl m1 = Some v ->
      eval_expr le e m (Eop op al) t m1 v
  | eval_Eload:
      forall le e m chunk a t m1 v1 v,
      eval_expr le e m a t m1 v1 ->
      Mem.loadv chunk m1 v1 = Some v ->
      eval_expr le e m (Eload chunk a) t m1 v
  | eval_Ecall:
      forall le e m sig a bl t1 m1 t2 m2 t3 m3 vf vargs vres f t,
      eval_expr le e m a t1 m1 vf ->
      eval_exprlist le e m1 bl t2 m2 vargs ->
      Genv.find_funct ge vf = Some f ->
      funsig f = sig ->
      eval_funcall m2 f vargs t3 m3 vres ->
      t = t1 ** t2 ** t3 ->
      eval_expr le e m (Ecall sig a bl) t m3 vres
  | eval_Econdition_true:
      forall le e m a b c t1 m1 v1 t2 m2 v2 t,
      eval_expr le e m a t1 m1 v1 ->
      Val.is_true v1 ->
      eval_expr le e m1 b t2 m2 v2 ->
      t = t1 ** t2 ->
      eval_expr le e m (Econdition a b c) t m2 v2
  | eval_Econdition_false:
      forall le e m a b c t1 m1 v1 t2 m2 v2 t,
      eval_expr le e m a t1 m1 v1 ->
      Val.is_false v1 ->
      eval_expr le e m1 c t2 m2 v2 ->
      t = t1 ** t2 ->
      eval_expr le e m (Econdition a b c) t m2 v2
  | eval_Elet:
      forall le e m a b t1 m1 v1 t2 m2 v2 t,
      eval_expr le e m a t1 m1 v1 ->
      eval_expr (v1::le) e m1 b t2 m2 v2 ->
      t = t1 ** t2 ->
      eval_expr le e m (Elet a b) t m2 v2
  | eval_Eletvar:
      forall le e m n v,
      nth_error le n = Some v ->
      eval_expr le e m (Eletvar n) E0 m v
  | eval_Ealloc:
      forall le e m a t m1 n m2 b,
      eval_expr le e m a t m1 (Vint n) ->
      Mem.alloc m1 0 (Int.signed n) = (m2, b) ->
      eval_expr le e m (Ealloc a) t m2 (Vptr b Int.zero)

(** Evaluation of a list of expressions:
  [eval_exprlist prg le al m a m' vl]
  states that the list [al] of expressions evaluate 
  to the list [vl] of values.
  The other parameters are as in [eval_expr].
*)

with eval_exprlist:
         letenv -> env ->
         mem -> exprlist -> trace ->
         mem -> list val -> Prop :=
  | eval_Enil:
      forall le e m,
      eval_exprlist le e m Enil E0 m nil
  | eval_Econs:
      forall le e m a bl t1 m1 v t2 m2 vl t,
      eval_expr le e m a t1 m1 v ->
      eval_exprlist le e m1 bl t2 m2 vl ->
      t = t1 ** t2 ->
      eval_exprlist le e m (Econs a bl) t m2 (v :: vl)

(** Evaluation of a function invocation: [eval_funcall prg m f args m' res]
  means that the function [f], applied to the arguments [args] in
  memory state [m], returns the value [res] in modified memory state [m'].
*)
with eval_funcall:
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

(** Execution of a statement: [exec_stmt prg e m s m' out]
  means that statement [s] executes with outcome [out].
  The other parameters are as in [eval_expr]. *)

with exec_stmt:
         env ->
         mem -> stmt -> trace ->
         mem -> outcome -> Prop :=
  | exec_Sskip:
      forall e m,
      exec_stmt e m Sskip E0 m Out_normal
  | exec_Sexpr:
      forall e m a t m1 v,
      eval_expr nil e m a t m1 v ->
      exec_stmt e m (Sexpr a) t m1 Out_normal
  | eval_Sassign:
      forall e m id a t m1 b chunk v m2,
      eval_expr nil e m a t m1 v ->
      eval_var_ref e id b chunk ->
      Mem.store chunk m1 b 0 v = Some m2 ->
      exec_stmt e m (Sassign id a) t m2 Out_normal
  | eval_Sstore:
      forall e m chunk a b t1 m1 v1 t2 m2 v2 t3 m3,
      eval_expr nil e m a t1 m1 v1 ->
      eval_expr nil e m1 b t2 m2 v2 ->
      Mem.storev chunk m2 v1 v2 = Some m3 ->
      t3 = t1 ** t2 ->
      exec_stmt e m (Sstore chunk a b) t3 m3 Out_normal
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
  | exec_Sifthenelse_true:
      forall e m a sl1 sl2 t1 m1 v1 t2 m2 out t,
      eval_expr nil e m a t1 m1 v1 ->
      Val.is_true v1 ->
      exec_stmt e m1 sl1 t2 m2 out ->
      t = t1 ** t2 ->
      exec_stmt e m (Sifthenelse a sl1 sl2) t m2 out
  | exec_Sifthenelse_false:
      forall e m a sl1 sl2 t1 m1 v1 t2 m2 out t,
      eval_expr nil e m a t1 m1 v1 ->
      Val.is_false v1 ->
      exec_stmt e m1 sl2 t2 m2 out ->
      t = t1 ** t2 ->
      exec_stmt e m (Sifthenelse a sl1 sl2) t m2 out
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
      forall e m a cases default t1 m1 n,
      eval_expr nil e m a t1 m1 (Vint n) ->
      exec_stmt e m (Sswitch a cases default)
               t1 m1 (Out_exit (switch_target n default cases))
  | exec_Sreturn_none:
      forall e m,
      exec_stmt e m (Sreturn None) E0 m (Out_return None)
  | exec_Sreturn_some:
      forall e m a t1 m1 v,
      eval_expr nil e m a t1 m1 v ->
      exec_stmt e m (Sreturn (Some a)) t1 m1 (Out_return (Some v)).

Scheme eval_expr_ind4 := Minimality for eval_expr Sort Prop
  with eval_exprlist_ind4 := Minimality for eval_exprlist Sort Prop
  with eval_funcall_ind4 := Minimality for eval_funcall Sort Prop
  with exec_stmt_ind4 := Minimality for exec_stmt Sort Prop.

End RELSEM.

(** Execution of a whole program: [exec_program p r]
  holds if the application of [p]'s main function to no arguments
  in the initial memory state for [p] eventually returns value [r]. *)

Definition exec_program (p: program) (t: trace) (r: val) : Prop :=
  let ge := Genv.globalenv p in
  let m0 := Genv.init_mem p in
  exists b, exists f, exists m,
  Genv.find_symbol ge p.(prog_main) = Some b /\
  Genv.find_funct_ptr ge b = Some f /\
  funsig f = mksignature nil (Some Tint) /\
  eval_funcall p m0 f nil t m r.
