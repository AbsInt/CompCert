(** The Cminor language after instruction selection. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Events.
Require Import Values.
Require Import Mem.
Require Import Cminor.
Require Import Op.
Require Import Globalenvs.
Require Import Switch.

(** * Abstract syntax *)

(** CminorSel programs share the general structure of Cminor programs:
  functions, statements and expressions.  However, CminorSel uses
  machine-dependent operations, addressing modes and conditions,
  as defined in module [Op] and used in lower-level intermediate
  languages ([RTL] and below).  Moreover, a variant [condexpr] of [expr]
  is used to represent expressions which are evaluated for their
  boolean value only and not their exact value.
*)

Inductive expr : Set :=
  | Evar : ident -> expr
  | Eop : operation -> exprlist -> expr
  | Eload : memory_chunk -> addressing -> exprlist -> expr
  | Estore : memory_chunk -> addressing -> exprlist -> expr -> expr
  | Ecall : signature -> expr -> exprlist -> expr
  | Econdition : condexpr -> expr -> expr -> expr
  | Elet : expr -> expr -> expr
  | Eletvar : nat -> expr
  | Ealloc : expr -> expr

with condexpr : Set :=
  | CEtrue: condexpr
  | CEfalse: condexpr
  | CEcond: condition -> exprlist -> condexpr
  | CEcondition : condexpr -> condexpr -> condexpr -> condexpr

with exprlist : Set :=
  | Enil: exprlist
  | Econs: expr -> exprlist -> exprlist.

(** Statements are as in Cminor, except that the condition of an
  if/then/else conditional is a [condexpr]. *)

Inductive stmt : Set :=
  | Sskip: stmt
  | Sexpr: expr -> stmt
  | Sassign : ident -> expr -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: condexpr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: expr -> list (int * nat) -> nat -> stmt
  | Sreturn: option expr -> stmt
  | Stailcall: signature -> expr -> exprlist -> stmt.

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

(** Three kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [env]: local environments, map local variables to values;
- [lenv]: let environments, map de Bruijn indices to values.
*)

Definition genv := Genv.t fundef.

Section RELSEM.

Variable ge: genv.

(** The evaluation predicates have the same general shape as those
    of Cminor.  Refer to the description of Cminor semantics for
    the meaning of the parameters of the predicates.
    One additional predicate is introduced:
    [eval_condexpr ge sp le e m a t m' b], meaning that the conditional
    expression [a] evaluates to the boolean [b]. *)

Inductive eval_expr:
         val -> letenv -> env ->
         mem -> expr -> trace -> mem -> val -> Prop :=
  | eval_Evar:
      forall sp le e m id v,
      PTree.get id e = Some v ->
      eval_expr sp le e m (Evar id) E0 m v
  | eval_Eop:
      forall sp le e m op al t m1 vl v,
      eval_exprlist sp le e m al t m1 vl ->
      eval_operation ge sp op vl m1 = Some v ->
      eval_expr sp le e m (Eop op al) t m1 v
  | eval_Eload:
      forall sp le e m chunk addr al t m1 v vl a,
      eval_exprlist sp le e m al t m1 vl ->
      eval_addressing ge sp addr vl = Some a ->
      Mem.loadv chunk m1 a = Some v ->
      eval_expr sp le e m (Eload chunk addr al) t m1 v
  | eval_Estore:
      forall sp le e m chunk addr al b t t1 m1 vl t2 m2 m3 v a,
      eval_exprlist sp le e m al t1 m1 vl ->
      eval_expr sp le e m1 b t2 m2 v ->
      eval_addressing ge sp addr vl = Some a ->
      Mem.storev chunk m2 a v = Some m3 ->
      t = t1 ** t2 ->
      eval_expr sp le e m (Estore chunk addr al b) t m3 v
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
      forall sp le e m a b c t t1 m1 v1 t2 m2 v2,
      eval_condexpr sp le e m a t1 m1 v1 ->
      eval_expr sp le e m1 (if v1 then b else c) t2 m2 v2 ->
      t = t1 ** t2 ->
      eval_expr sp le e m (Econdition a b c) t m2 v2
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

with eval_condexpr:
         val -> letenv -> env ->
         mem -> condexpr -> trace -> mem -> bool -> Prop :=
  | eval_CEtrue:
      forall sp le e m,
      eval_condexpr sp le e m CEtrue E0 m true
  | eval_CEfalse:
      forall sp le e m,
      eval_condexpr sp le e m CEfalse E0 m false
  | eval_CEcond:
      forall sp le e m cond al t1 m1 vl b,
      eval_exprlist sp le e m al t1 m1 vl ->
      eval_condition cond vl m1 = Some b ->
      eval_condexpr sp le e m (CEcond cond al) t1 m1 b
  | eval_CEcondition:
      forall sp le e m a b c t t1 m1 vb1 t2 m2 vb2,
      eval_condexpr sp le e m a t1 m1 vb1 ->
      eval_condexpr sp le e m1 (if vb1 then b else c) t2 m2 vb2 ->
      t = t1 ** t2 ->
      eval_condexpr sp le e m (CEcondition a b c) t m2 vb2

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
      forall sp e m a s1 s2 t t1 m1 v1 t2 e2 m2 out,
      eval_condexpr sp nil e m a t1 m1 v1 ->
      exec_stmt sp e m1 (if v1 then s1 else s2) t2 e2 m2 out ->
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

Scheme eval_expr_ind5 := Minimality for eval_expr Sort Prop
  with eval_condexpr_ind5 := Minimality for eval_condexpr Sort Prop
  with eval_exprlist_ind5 := Minimality for eval_exprlist Sort Prop
  with eval_funcall_ind5 := Minimality for eval_funcall Sort Prop
  with exec_stmt_ind5 := Minimality for exec_stmt Sort Prop.

End RELSEM.

Definition exec_program (p: program) (t: trace) (r: val) : Prop :=
  let ge := Genv.globalenv p in
  let m0 := Genv.init_mem p in
  exists b, exists f, exists m,
  Genv.find_symbol ge p.(prog_main) = Some b /\
  Genv.find_funct_ptr ge b = Some f /\
  funsig f = mksignature nil (Some Tint) /\
  eval_funcall ge m0 f nil t m r.

