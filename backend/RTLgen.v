(** Translation from Cminor to RTL. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Op.
Require Import Registers.
Require Import Cminor.
Require Import RTL.

(** * Translation environments and state *)

(** The translation functions are parameterized by the following 
  compile-time environment, which maps Cminor local variables and
  let-bound variables to RTL registers.   The mapping for local variables
  is computed from the Cminor variable declarations at the beginning of
  the translation of a function, and does not change afterwards.
  The mapping for let-bound variables is initially empty and updated
  during translation of expressions, when crossing a [Elet] binding. *)

Record mapping: Set := mkmapping {
  map_vars: PTree.t reg;
  map_letvars: list reg
}.

(** The translation functions modify a global state, comprising the
  current state of the control-flow graph for the function being translated,
  as well as sources of fresh RTL registers and fresh CFG nodes. *)

Record state: Set := mkstate {
  st_nextreg: positive;
  st_nextnode: positive;
  st_code: code;
  st_wf: forall (pc: positive), Plt pc st_nextnode \/ st_code!pc = None
}.

(** ** The state and error monad *)

(** The translation functions can fail to produce RTL code, for instance
  if a non-declared variable is referenced.  They must also modify
  the global state, adding new nodes to the control-flow graph and
  generating fresh temporary registers.  In a language like ML or Java,
  we would use exceptions to report errors and mutable data structures
  to modify the global state.  These luxuries are not available in Coq,
  however.  Instead, we use a monadic encoding of the translation:
  translation functions take the current global state as argument,
  and return either [Error] to denote an error, or [OK r s] to denote
  success.  [s] is the modified state, and [r] the result value of the
  translation function. 

  We now define this monadic encoding -- the ``state and error'' monad --
  as well as convenient syntax to express monadic computations. *)

Set Implicit Arguments.

Inductive res (A: Set) : Set :=
  | Error: res A
  | OK: A -> state -> res A.

Definition mon (A: Set) : Set := state -> res A.

Definition ret (A: Set) (x: A) : mon A := fun (s: state) => OK x s.

Definition error (A: Set) : mon A := fun (s: state) => Error A.

Definition bind (A B: Set) (f: mon A) (g: A -> mon B) : mon B :=
  fun (s: state) =>
    match f s with
    | Error => Error B
    | OK a s' => g a s'
    end.

Definition bind2 (A B C: Set) (f: mon (A * B)) (g: A -> B -> mon C) : mon C :=
  bind f (fun xy => g (fst xy) (snd xy)).

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200).

(** ** Operations on state *)

(** The initial state (empty CFG). *)

Lemma init_state_wf:
  forall pc, Plt pc 1%positive \/ (PTree.empty instruction)!pc = None.
Proof. intros; right; apply PTree.gempty. Qed.

Definition init_state : state :=
  mkstate 1%positive 1%positive (PTree.empty instruction) init_state_wf.

(** Adding a node with the given instruction to the CFG.  Return the
    label of the new node. *)

Lemma add_instr_wf:
  forall s i pc,
  let n := s.(st_nextnode) in
  Plt pc (Psucc n) \/ (PTree.set n i s.(st_code))!pc = None.
Proof.
  intros. case (peq pc n); intro.
  subst pc; left; apply Plt_succ.
  rewrite PTree.gso; auto.
  elim (st_wf s pc); intro.
  left. apply Plt_trans_succ. exact H.
  right; assumption.
Qed.

Definition add_instr (i: instruction) : mon node :=
  fun s =>
    let n := s.(st_nextnode) in
    OK n
       (mkstate s.(st_nextreg)
                (Psucc n)
                (PTree.set n i s.(st_code))
                (add_instr_wf s i)).

(** [add_instr] can be decomposed in two steps: reserving a fresh
  CFG node, and filling it later with an instruction.  This is needed
  to compile loops. *)

Lemma reserve_instr_wf:
  forall s pc,
  Plt pc (Psucc s.(st_nextnode)) \/ s.(st_code)!pc = None.
Proof.
  intros. elim (st_wf s pc); intro.
  left; apply Plt_trans_succ; auto.
  right; auto.
Qed.

Definition reserve_instr : mon node :=
  fun s =>
    let n := s.(st_nextnode) in
    OK n (mkstate s.(st_nextreg) (Psucc n) s.(st_code)
                  (reserve_instr_wf s)).

Lemma update_instr_wf:
  forall s n i,
  Plt n s.(st_nextnode) ->
  forall pc,
  Plt pc s.(st_nextnode) \/ (PTree.set n i s.(st_code))!pc = None.
Proof.
  intros.
  case (peq pc n); intro.
  subst pc; left; assumption.
  rewrite PTree.gso; auto. exact (st_wf s pc).
Qed.

Definition update_instr (n: node) (i: instruction) : mon unit :=
  fun s =>
    match plt n s.(st_nextnode) with
    | left PEQ =>
        OK tt (mkstate s.(st_nextreg) s.(st_nextnode)
                       (PTree.set n i s.(st_code))
                       (@update_instr_wf s n i PEQ))
    | right _ =>
        Error unit
    end.

(** Generate a fresh RTL register. *)

Definition new_reg : mon reg :=
  fun s =>
    OK s.(st_nextreg)
       (mkstate (Psucc s.(st_nextreg))
                s.(st_nextnode) s.(st_code) s.(st_wf)).

(** ** Operations on mappings *)

Definition init_mapping : mapping :=
  mkmapping (PTree.empty reg) nil.

Definition add_var (map: mapping) (name: ident) : mon (reg * mapping) :=
  do r <- new_reg;
     ret (r, mkmapping (PTree.set name r map.(map_vars))
                       map.(map_letvars)).

Fixpoint add_vars (map: mapping) (names: list ident) 
                  {struct names} : mon (list reg * mapping) :=
  match names with
  | nil => ret (nil, map)
  | n1 :: nl =>
      do (rl, map1) <- add_vars map nl;
      do (r1, map2) <- add_var map1 n1;
      ret (r1 :: rl, map2)
  end.

Definition find_var (map: mapping) (name: ident) : mon reg :=
  match PTree.get name map.(map_vars) with
  | None => error reg
  | Some r => ret r
  end.

Definition add_letvar (map: mapping) (r: reg) : mapping :=
  mkmapping map.(map_vars) (r :: map.(map_letvars)).

Definition find_letvar (map: mapping) (idx: nat) : mon reg :=
  match List.nth_error map.(map_letvars) idx with
  | None => error reg
  | Some r => ret r
  end.

(** ** Optimized temporary generation *)

(** [alloc_reg map a] returns the RTL register where the evaluation
  of expression [a] should leave its result -- the ``target register''
  for evaluating [a].  In general, this is a
  fresh temporary register.  Exception: if [a] is a let-bound variable
  or a local variable, we return the RTL register associated
  with that variable instead.  Returning a fresh temporary in all cases
  would be semantically correct, but would generate less efficient 
  RTL code. *)

Definition alloc_reg (map: mapping) (a: expr) : mon reg :=
  match a with
  | Evar id   => find_var map id
  | Eletvar n => find_letvar map n
  | _         => new_reg
  end.

(** [alloc_regs] is similar, but for a list of expressions. *)

Fixpoint alloc_regs (map: mapping) (al: exprlist)
                    {struct al}: mon (list reg) :=
  match al with
  | Enil =>
      ret nil
  | Econs a bl =>
      do rl <- alloc_regs map bl;
      do r  <- alloc_reg map a;
      ret (r :: rl)
  end.

(** * RTL generation **)

(** Insertion of a register-to-register move instruction. *)

Definition add_move (rs rd: reg) (nd: node) : mon node :=
  if Reg.eq rs rd
  then ret nd
  else add_instr (Iop Omove (rs::nil) rd nd).

(** Translation of an expression.  [transl_expr map mut a rd nd]
  enriches the current CFG with the RTL instructions necessary
  to compute the value of Cminor expression [a], leave its result
  in register [rd], and branch to node [nd].  It returns the node
  of the first instruction in this sequence.  [map] is the compile-time
  translation environment. *)

Fixpoint transl_expr (map: mapping) (a: expr) (rd: reg) (nd: node)
                     {struct a}: mon node :=
  match a with
  | Evar v =>
      do r <- find_var map v; add_move r rd nd
  | Eop op al =>
      do rl <- alloc_regs map al;
      do no <- add_instr (Iop op rl rd nd);
         transl_exprlist map al rl no
  | Eload chunk addr al =>
      do rl <- alloc_regs map al;
      do no <- add_instr (Iload chunk addr rl rd nd);
         transl_exprlist map al rl no
  | Estore chunk addr al b =>
      do rl <- alloc_regs map al;
      do no <- add_instr (Istore chunk addr rl rd nd);
      do ns <- transl_expr map b rd no;
         transl_exprlist map al rl ns
  | Ecall sig b cl =>
      do rf <- alloc_reg map b;
      do rargs <- alloc_regs map cl;
      do n1 <- add_instr (Icall sig (inl _ rf) rargs rd nd);
      do n2 <- transl_exprlist map cl rargs n1;
         transl_expr map b rf n2
  | Econdition b c d =>
      do nfalse <- transl_expr map d rd nd;
      do ntrue  <- transl_expr map c rd nd;
         transl_condition map b ntrue nfalse
  | Elet b c =>
      do r  <- new_reg;
      do nc <- transl_expr (add_letvar map r) c rd nd;
         transl_expr map b r nc
  | Eletvar n =>
      do r <- find_letvar map n; add_move r rd nd
  | Ealloc a =>
      do r <- alloc_reg map a;
      do no <- add_instr (Ialloc r rd nd);
         transl_expr map a r no
  end

(** Translation of a conditional expression.  Similar to [transl_expr],
  but the expression is evaluated for its truth value, and the generated
  code branches to one of two possible continuation nodes [ntrue] or 
  [nfalse] depending on the truth value of [a]. *)

with transl_condition (map: mapping) (a: condexpr) (ntrue nfalse: node)
                      {struct a}: mon node :=
  match a with
  | CEtrue =>
      ret ntrue
  | CEfalse =>
      ret nfalse
  | CEcond cond bl =>
      do rl <- alloc_regs map bl;
      do nt <- add_instr (Icond cond rl ntrue nfalse);
         transl_exprlist map bl rl nt
  | CEcondition b c d =>
      do nd <- transl_condition map d ntrue nfalse;
      do nc <- transl_condition map c ntrue nfalse;
         transl_condition map b nc nd
  end

(** Translation of a list of expressions.  The expressions are evaluated
  left-to-right, and their values left in the given list of registers. *)

with transl_exprlist (map: mapping) (al: exprlist) (rl: list reg) (nd: node)
                     {struct al} : mon node :=
  match al, rl with
  | Enil, nil =>
      ret nd
  | Econs b bs, r :: rs =>
      do no <- transl_exprlist map bs rs nd; transl_expr map b r no
  | _, _ =>
      error node
  end.

(** Auxiliary for branch prediction.  When compiling an if/then/else
  statement, we have a choice between translating the ``then'' branch
  first or the ``else'' branch first.  Linearization of RTL control-flow
  graph, performed later, will exploit this choice as a hint about
  which branch is most frequently executed.  However, this choice has
  no impact on program correctness.  We delegate the choice to an
  external heuristic (written in OCaml), declared below.  *)

Parameter more_likely: condexpr -> stmt -> stmt -> bool.

(** Auxiliary for translating [Sswitch] statements. *)

Definition transl_exit (nexits: list node) (n: nat) : mon node :=
  match nth_error nexits n with
  | None => error node
  | Some ne => ret ne
  end.

Fixpoint transl_switch (r: reg) (nexits: list node)
                       (cases: list (int * nat)) (default: nat)
                       {struct cases} : mon node :=
  match cases with
  | nil =>
      transl_exit nexits default
  | (key1, exit1) :: cases' =>
      do ncont <- transl_switch r nexits cases' default;
      do nfound <- transl_exit nexits exit1;
      add_instr (Icond (Ccompimm Ceq key1) (r :: nil) nfound ncont)
  end.

(** Translation of statements.  [transl_stmt map s nd nexits nret rret]
  enriches the current CFG with the RTL instructions necessary to
  execute the Cminor statement [s], and returns the node of the first
  instruction in this sequence.  The generated instructions continue
  at node [nd] if the statement terminates normally, at node [nret]
  if it terminates by early return, and at the [n]-th node in the list
  [nlist] if it terminates by an [exit n] construct.  [rret] is the
  register where the return value of the function must be stored, if any. *)

Fixpoint transl_stmt (map: mapping) (s: stmt) (nd: node)
                     (nexits: list node) (nret: node) (rret: option reg)
                     {struct s} : mon node :=
  match s with
  | Sskip =>
      ret nd
  | Sexpr a =>
      do r <- alloc_reg map a; transl_expr map a r nd
  | Sassign v b =>
      do rv <- find_var map v;
      do rt <- alloc_reg map b;
      do no <- add_move rt rv nd;
      transl_expr map b rt no
  | Sseq s1 s2 =>
      do ns <- transl_stmt map s2 nd nexits nret rret;
      transl_stmt map s1 ns nexits nret rret
  | Sifthenelse a strue sfalse =>
      if more_likely a strue sfalse then
        do nfalse <- transl_stmt map sfalse nd nexits nret rret;
        do ntrue  <- transl_stmt map strue  nd nexits nret rret;
        transl_condition map a ntrue nfalse
      else
        do ntrue  <- transl_stmt map strue  nd nexits nret rret;
        do nfalse <- transl_stmt map sfalse nd nexits nret rret;
        transl_condition map a ntrue nfalse
  | Sloop sbody =>
      do nloop <- reserve_instr;
      do nbody <- transl_stmt map sbody nloop nexits nret rret;
      do x <- update_instr nloop (Inop nbody);
      ret nbody
  | Sblock sbody =>
      transl_stmt map sbody nd (nd :: nexits) nret rret
  | Sexit n =>
      transl_exit nexits n
  | Sswitch a cases default =>
      do r <- alloc_reg map a;
      do ns <- transl_switch r nexits cases default;
      transl_expr map a r ns
  | Sreturn opt_a =>
      match opt_a, rret with
      | None, None => ret nret
      | Some a, Some r => transl_expr map a r nret
      | _, _ => error node
      end
  end.

(** Translation of a Cminor function. *)

Definition ret_reg (sig: signature) (rd: reg) : option reg :=
  match sig.(sig_res) with
  | None => None
  | Some ty => Some rd
  end.

Definition transl_fun (f: Cminor.function) : mon (node * list reg) :=
  do (rparams, map1) <- add_vars init_mapping f.(Cminor.fn_params);
  do (rvars, map2) <- add_vars map1 f.(Cminor.fn_vars);
  do rret <- new_reg;
  let orret := ret_reg f.(Cminor.fn_sig) rret in
  do nret <- add_instr (Ireturn orret);
  do nentry <- transl_stmt map2 f.(Cminor.fn_body) nret nil nret orret;
  ret (nentry, rparams).

Definition transl_function (f: Cminor.function) : option RTL.function :=
  match transl_fun f init_state with
  | Error => None
  | OK (nentry, rparams) s =>
      Some (RTL.mkfunction
             f.(Cminor.fn_sig)
             rparams
             f.(Cminor.fn_stackspace)
             s.(st_code)
             nentry
             s.(st_nextnode)
             s.(st_wf))
  end.

Definition transl_fundef := transf_partial_fundef transl_function.

(** Translation of a whole program. *)

Definition transl_program (p: Cminor.program) : option RTL.program :=
  transform_partial_program transl_fundef p.
