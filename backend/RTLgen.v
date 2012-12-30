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

(** Translation from CminorSel to RTL. *)

Require Import Coqlib.
Require Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Switch.
Require Import Op.
Require Import Registers.
Require Import CminorSel.
Require Import RTL.

Open Local Scope string_scope.

(** * Translation environments and state *)

(** The translation functions are parameterized by the following 
  compile-time environment, which maps CminorSel local variables and
  let-bound variables to RTL registers.   The mapping for local variables
  is computed from the CminorSel variable declarations at the beginning of
  the translation of a function, and does not change afterwards.
  The mapping for let-bound variables is initially empty and updated
  during translation of expressions, when crossing a [Elet] binding. *)

Record mapping: Type := mkmapping {
  map_vars: PTree.t reg;
  map_letvars: list reg
}.

(** The translation functions modify a global state, comprising the
  current state of the control-flow graph for the function being translated,
  as well as sources of fresh RTL registers and fresh CFG nodes. *)

Record state: Type := mkstate {
  st_nextreg: positive;
  st_nextnode: positive;
  st_code: code;
  st_wf: forall (pc: positive), Plt pc st_nextnode \/ st_code!pc = None
}.

(** Operations over the global state satisfy a crucial monotonicity property:
  nodes are only added to the CFG, but are never removed nor their
  instructions are changed; similarly, fresh nodes and fresh registers
  are only consumed, but never reused.  This property is captured by
  the following predicate over states, which we show is a partial
  order. *)

Inductive state_incr: state -> state -> Prop :=
  state_incr_intro:
    forall (s1 s2: state),
    Ple s1.(st_nextnode) s2.(st_nextnode) ->
    Ple s1.(st_nextreg) s2.(st_nextreg) ->
    (forall pc,
      s1.(st_code)!pc = None \/ s2.(st_code)!pc = s1.(st_code)!pc) ->
    state_incr s1 s2.

Lemma state_incr_refl:
  forall s, state_incr s s.
Proof.
  intros. apply state_incr_intro.
  apply Ple_refl. apply Ple_refl. intros; auto.
Qed.

Lemma state_incr_trans:
  forall s1 s2 s3, state_incr s1 s2 -> state_incr s2 s3 -> state_incr s1 s3.
Proof.
  intros. inv H; inv H0. apply state_incr_intro.
  apply Ple_trans with (st_nextnode s2); assumption. 
  apply Ple_trans with (st_nextreg s2); assumption.
  intros. generalize (H3 pc) (H5 pc). intuition congruence.
Qed.

(** ** The state and error monad *)

(** The translation functions can fail to produce RTL code, for instance
  if a non-declared variable is referenced.  They must also modify
  the global state, adding new nodes to the control-flow graph and
  generating fresh temporary registers.  In a language like ML or Java,
  we would use exceptions to report errors and mutable data structures
  to modify the global state.  These luxuries are not available in Coq,
  however.  Instead, we use a monadic encoding of the translation:
  translation functions take the current global state as argument,
  and return either [Error msg] to denote an error, 
  or [OK r s incr] to denote success.  [s] is the modified state, [r]
  the result value of the translation function.  and [incr] a proof
  that the final state is in the [state_incr] relation with the
  initial state.  In the error case, [msg] is an error message (see
  modules [Errors]) describing the problem.

  We now define this monadic encoding -- the ``state and error'' monad --
  as well as convenient syntax to express monadic computations. *)

Inductive res (A: Type) (s: state): Type :=
  | Error: Errors.errmsg -> res A s
  | OK: A -> forall (s': state), state_incr s s' -> res A s.

Implicit Arguments OK [A s].
Implicit Arguments Error [A s].

Definition mon (A: Type) : Type := forall (s: state), res A s.

Definition ret (A: Type) (x: A) : mon A :=
  fun (s: state) => OK x s (state_incr_refl s).

Implicit Arguments ret [A].

Definition error (A: Type) (msg: Errors.errmsg) : mon A := fun (s: state) => Error msg.

Implicit Arguments error [A].

Definition bind (A B: Type) (f: mon A) (g: A -> mon B) : mon B :=
  fun (s: state) =>
    match f s with
    | Error msg => Error msg
    | OK a s' i =>
        match g a s' with
        | Error msg => Error msg
        | OK b s'' i' => OK b s'' (state_incr_trans s s' s'' i i')
        end
    end.

Implicit Arguments bind [A B].

Definition bind2 (A B C: Type) (f: mon (A * B)) (g: A -> B -> mon C) : mon C :=
  bind f (fun xy => g (fst xy) (snd xy)).

Implicit Arguments bind2 [A B C].

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200).

Definition handle_error (A: Type) (f g: mon A) : mon A :=
  fun (s: state) =>
    match f s with
    | OK a s' i => OK a s' i
    | Error _ => g s
    end.

Implicit Arguments handle_error [A].

(** ** Operations on state *)

(** The initial state (empty CFG). *)

Remark init_state_wf:
  forall pc, Plt pc 1%positive \/ (PTree.empty instruction)!pc = None.
Proof. intros; right; apply PTree.gempty. Qed.

Definition init_state : state :=
  mkstate 1%positive 1%positive (PTree.empty instruction) init_state_wf.

(** Adding a node with the given instruction to the CFG.  Return the
    label of the new node. *)

Remark add_instr_wf:
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

Remark add_instr_incr:
  forall s i,
  let n := s.(st_nextnode) in
  state_incr s (mkstate s.(st_nextreg)
                (Psucc n)
                (PTree.set n i s.(st_code))
                (add_instr_wf s i)).
Proof.
  constructor; simpl.
  apply Ple_succ.
  apply Ple_refl.
  intros. destruct (st_wf s pc). right. apply PTree.gso. apply Plt_ne; auto. auto.
Qed.

Definition add_instr (i: instruction) : mon node :=
  fun s =>
    let n := s.(st_nextnode) in
    OK n
       (mkstate s.(st_nextreg) (Psucc n) (PTree.set n i s.(st_code)) 
                (add_instr_wf s i))
       (add_instr_incr s i).

(** [add_instr] can be decomposed in two steps: reserving a fresh
  CFG node, and filling it later with an instruction.  This is needed
  to compile loops. *)

Remark reserve_instr_wf:
  forall s pc,
  Plt pc (Psucc s.(st_nextnode)) \/ s.(st_code)!pc = None.
Proof.
  intros. elim (st_wf s pc); intro.
  left; apply Plt_trans_succ; auto.
  right; auto.
Qed.

Remark reserve_instr_incr:
  forall s,
  let n := s.(st_nextnode) in
  state_incr s (mkstate s.(st_nextreg)
                (Psucc n)
                s.(st_code)
                (reserve_instr_wf s)).
Proof.
  intros; constructor; simpl.
  apply Ple_succ.
  apply Ple_refl.
  auto.
Qed.

Definition reserve_instr: mon node :=
  fun (s: state) =>
  let n := s.(st_nextnode) in
  OK n
     (mkstate s.(st_nextreg) (Psucc n) s.(st_code) (reserve_instr_wf s))
     (reserve_instr_incr s).

Remark update_instr_wf:
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

Remark update_instr_incr:
  forall s n i (LT: Plt n s.(st_nextnode)),
  s.(st_code)!n = None ->
  state_incr s
             (mkstate s.(st_nextreg) s.(st_nextnode) (PTree.set n i s.(st_code))
                     (update_instr_wf s n i LT)).
Proof.
  intros.
  constructor; simpl; intros.
  apply Ple_refl.
  apply Ple_refl.
  rewrite PTree.gsspec. destruct (peq pc n). left; congruence. right; auto.
Qed.

Definition check_empty_node:
  forall (s: state) (n: node), { s.(st_code)!n = None } + { True }.
Proof.
  intros. case (s.(st_code)!n); intros. right; auto. left; auto.
Defined.

Definition update_instr (n: node) (i: instruction) : mon unit :=
  fun s =>
    match plt n s.(st_nextnode), check_empty_node s n with
    | left LT, left EMPTY =>
        OK tt
           (mkstate s.(st_nextreg) s.(st_nextnode) (PTree.set n i s.(st_code))
                    (update_instr_wf s n i LT))
           (update_instr_incr s n i LT EMPTY)
    | _, _ =>
        Error (Errors.msg "RTLgen.update_instr")
    end.

(** Generate a fresh RTL register. *)

Remark new_reg_incr:
  forall s,
  state_incr s (mkstate (Psucc s.(st_nextreg))
                        s.(st_nextnode) s.(st_code) s.(st_wf)).
Proof.
  constructor; simpl. apply Ple_refl. apply Ple_succ. auto.
Qed.

Definition new_reg : mon reg :=
  fun s =>
    OK s.(st_nextreg)
       (mkstate (Psucc s.(st_nextreg)) s.(st_nextnode) s.(st_code) s.(st_wf))
       (new_reg_incr s).

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
  | None => error (Errors.MSG "RTLgen: unbound variable " :: Errors.CTX name :: nil)
  | Some r => ret r
  end.

Definition add_letvar (map: mapping) (r: reg) : mapping :=
  mkmapping map.(map_vars) (r :: map.(map_letvars)).

Definition find_letvar (map: mapping) (idx: nat) : mon reg :=
  match List.nth_error map.(map_letvars) idx with
  | None => error (Errors.msg "RTLgen: unbound let variable")
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
      do r  <- alloc_reg map a;
      do rl <- alloc_regs map bl;
      ret (r :: rl)
  end.

(** A variant of [alloc_regs] for two-address instructions:
  reuse the result register as destination for the first argument. *)

Definition alloc_regs_2addr (map: mapping) (al: exprlist) (rd: reg)
                            : mon (list reg) :=
  match al with
  | Enil =>
      ret nil
  | Econs a bl =>
      do rl <- alloc_regs map bl; ret (rd :: rl)
  end.

(** [alloc_optreg] is used for function calls.  If a destination is
  specified for the call, it is returned.  Otherwise, a fresh
  register is returned. *)

Definition alloc_optreg (map: mapping) (dest: option ident) : mon reg :=
  match dest with
  | Some id => find_var map id
  | None => new_reg
  end.

(** * RTL generation **)

(** Insertion of a register-to-register move instruction. *)

Definition add_move (rs rd: reg) (nd: node) : mon node :=
  if Reg.eq rs rd
  then ret nd
  else add_instr (Iop Omove (rs::nil) rd nd).

(** Translation of an expression.  [transl_expr map a rd nd]
  enriches the current CFG with the RTL instructions necessary
  to compute the value of CminorSel expression [a], leave its result
  in register [rd], and branch to node [nd].  It returns the node
  of the first instruction in this sequence.  [map] is the compile-time
  translation environment. *)

Fixpoint transl_expr (map: mapping) (a: expr) (rd: reg) (nd: node)
                     {struct a}: mon node :=
  match a with
  | Evar v =>
      do r <- find_var map v; add_move r rd nd
  | Eop op al =>
      do rl <- if two_address_op op
               then alloc_regs_2addr map al rd
               else alloc_regs map al;
      do no <- add_instr (Iop op rl rd nd);
      transl_exprlist map al rl no
  | Eload chunk addr al =>
      do rl <- alloc_regs map al;
      do no <- add_instr (Iload chunk addr rl rd nd);
         transl_exprlist map al rl no
  | Econdition cond al b c =>
      do rl <- alloc_regs map al;
      do nfalse <- transl_expr map c rd nd;
      do ntrue  <- transl_expr map b rd nd;
      do nt <- add_instr (Icond cond rl ntrue nfalse);
         transl_exprlist map al rl nt
  | Elet b c =>
      do r  <- new_reg;
      do nc <- transl_expr (add_letvar map r) c rd nd;
         transl_expr map b r nc
  | Eletvar n =>
      do r <- find_letvar map n; add_move r rd nd
  end

(** Translation of a list of expressions.  The expressions are evaluated
  left-to-right, and their values stored in the given list of registers. *)

with transl_exprlist (map: mapping) (al: exprlist) (rl: list reg) (nd: node)
                     {struct al} : mon node :=
  match al, rl with
  | Enil, nil =>
      ret nd
  | Econs b bs, r :: rs =>
      do no <- transl_exprlist map bs rs nd; transl_expr map b r no
  | _, _ =>
      error (Errors.msg "RTLgen.transl_exprlist")
  end.

(** Auxiliary for branch prediction.  When compiling an if/then/else
  statement, we have a choice between translating the ``then'' branch
  first or the ``else'' branch first.  Linearization of RTL control-flow
  graph, performed later, will exploit this choice as a hint about
  which branch is most frequently executed.  However, this choice has
  no impact on program correctness.  We delegate the choice to an
  external heuristic (written in OCaml), declared below.  *)

Parameter more_likely: condition -> stmt -> stmt -> bool.

(** Auxiliary for translating [Sswitch] statements. *)

Parameter compile_switch: nat -> table -> comptree.

Definition transl_exit (nexits: list node) (n: nat) : mon node :=
  match nth_error nexits n with
  | None => error (Errors.msg "RTLgen: wrong exit")
  | Some ne => ret ne
  end.

Fixpoint transl_jumptable (nexits: list node) (tbl: list nat) : mon (list node) :=
  match tbl with
  | nil => ret nil
  | t1 :: tl =>
      do n1 <- transl_exit nexits t1;
      do nl <- transl_jumptable nexits tl;
      ret (n1 :: nl)
  end.

Fixpoint transl_switch (r: reg) (nexits: list node) (t: comptree)
                       {struct t} : mon node :=
  match t with
  | CTaction act =>
      transl_exit nexits act
  | CTifeq key act t' =>
      do ncont <- transl_switch r nexits t';
      do nfound <- transl_exit nexits act;
      add_instr (Icond (Ccompimm Ceq key) (r :: nil) nfound ncont)
  | CTiflt key t1 t2 =>
      do n2 <- transl_switch r nexits t2;
      do n1 <- transl_switch r nexits t1;
      add_instr (Icond (Ccompuimm Clt key) (r :: nil) n1 n2)
  | CTjumptable ofs sz tbl t' =>
      do rt <- new_reg;
      do ttbl <- transl_jumptable nexits tbl;
      do n1 <- add_instr (Ijumptable rt ttbl);
      do n2 <- transl_switch r nexits t';
      do n3 <- add_instr (Icond (Ccompuimm Clt sz) (rt :: nil) n1 n2);
      let op := if Int.eq ofs Int.zero then Omove else Oaddimm (Int.neg ofs) in
      add_instr (Iop op (r :: nil) rt n3)
  end.

(** Detect a two-address operator at the top of an expression. *)

Fixpoint expr_is_2addr_op (e: expr) : bool :=
  match e with
  | Eop op _ => two_address_op op
  | Econdition cond el e2 e3 => expr_is_2addr_op e2 || expr_is_2addr_op e3
  | Elet e1 e2 => expr_is_2addr_op e2
  | _ => false
  end.

(** Translation of statements.  [transl_stmt map s nd nexits nret rret]
  enriches the current CFG with the RTL instructions necessary to
  execute the CminorSel statement [s], and returns the node of the first
  instruction in this sequence.  The generated instructions continue
  at node [nd] if the statement terminates normally, at node [nret]
  if it terminates by early return, and at the [n]-th node in the list
  [nlist] if it terminates by an [exit n] construct.  [rret] is the
  register where the return value of the function must be stored, if any. *)

Definition labelmap : Type := PTree.t node.

Fixpoint transl_stmt (map: mapping) (s: stmt) (nd: node)
                     (nexits: list node) (ngoto: labelmap) (nret: node) (rret: option reg)
                     {struct s} : mon node :=
  match s with
  | Sskip =>
      ret nd
  | Sassign v b =>
      do r <- find_var map v;
      if expr_is_2addr_op b then
        do rd <- new_reg;
        do n1 <- add_move rd r nd;
        transl_expr map b rd n1
      else
        transl_expr map b r nd
  | Sstore chunk addr al b =>
      do rl <- alloc_regs map al;
      do r <- alloc_reg map b;
      do no <- add_instr (Istore chunk addr rl r nd);
      do ns <- transl_expr map b r no;
         transl_exprlist map al rl ns
  | Scall optid sig (inl b) cl =>
      do rf <- alloc_reg map b;
      do rargs <- alloc_regs map cl;
      do r <- alloc_optreg map optid;
      do n1 <- add_instr (Icall sig (inl _ rf) rargs r nd);
      do n2 <- transl_exprlist map cl rargs n1;
         transl_expr map b rf n2
  | Scall optid sig (inr id) cl =>
      do rargs <- alloc_regs map cl;
      do r <- alloc_optreg map optid;
      do n1 <- add_instr (Icall sig (inr _ id) rargs r nd);
      transl_exprlist map cl rargs n1
  | Stailcall sig (inl b) cl =>
      do rf <- alloc_reg map b;
      do rargs <- alloc_regs map cl;
      do n1 <- add_instr (Itailcall sig (inl _ rf) rargs);
      do n2 <- transl_exprlist map cl rargs n1;
         transl_expr map b rf n2
  | Stailcall sig (inr id) cl =>
      do rargs <- alloc_regs map cl;
      do n1 <- add_instr (Itailcall sig (inr _ id) rargs);
      transl_exprlist map cl rargs n1
  | Sbuiltin optid ef al =>
      do rargs <- alloc_regs map al;
      do r <- alloc_optreg map optid;
      do n1 <- add_instr (Ibuiltin ef rargs r nd);
         transl_exprlist map al rargs n1
  | Sseq s1 s2 =>
      do ns <- transl_stmt map s2 nd nexits ngoto nret rret;
      transl_stmt map s1 ns nexits ngoto nret rret
  | Sifthenelse cond al strue sfalse =>
      do rl <- alloc_regs map al;
      if more_likely cond strue sfalse then
        do nfalse <- transl_stmt map sfalse nd nexits ngoto nret rret;
        do ntrue  <- transl_stmt map strue  nd nexits ngoto nret rret;
        do nt <- add_instr (Icond cond rl ntrue nfalse);
           transl_exprlist map al rl nt
      else
        do ntrue  <- transl_stmt map strue  nd nexits ngoto nret rret;
        do nfalse <- transl_stmt map sfalse nd nexits ngoto nret rret;
        do nt <- add_instr (Icond cond rl ntrue nfalse);
           transl_exprlist map al rl nt
  | Sloop sbody =>
      do n1 <- reserve_instr;
      do n2 <- transl_stmt map sbody n1 nexits ngoto nret rret;
      do xx <- update_instr n1 (Inop n2);
      add_instr (Inop n2)
  | Sblock sbody =>
      transl_stmt map sbody nd (nd :: nexits) ngoto nret rret
  | Sexit n =>
      transl_exit nexits n
  | Sswitch a cases default =>
      let t := compile_switch default cases in
      if validate_switch default cases t then
        (do r <- alloc_reg map a;
         do ns <- transl_switch r nexits t;
         transl_expr map a r ns)
      else
        error (Errors.msg "RTLgen: wrong switch")
  | Sreturn opt_a =>
      match opt_a, rret with
      | None, _ => ret nret
      | Some a, Some r => transl_expr map a r nret
      | _, _ => error (Errors.msg "RTLgen: type mismatch on return")
      end
  | Slabel lbl s' =>
      do ns <- transl_stmt map s' nd nexits ngoto nret rret;
      match ngoto!lbl with
      | None => error (Errors.msg "RTLgen: unbound label")
      | Some n =>
          do xx <-
            (handle_error (update_instr n (Inop ns))
                          (error (Errors.MSG "Multiply-defined label " ::
                                  Errors.CTX lbl :: nil)));
          ret ns
      end
  | Sgoto lbl =>
      match ngoto!lbl with
      | None => error (Errors.MSG "Undefined defined label " ::
                       Errors.CTX lbl :: nil)
      | Some n => ret n
      end
  end.

(** Preallocate CFG nodes for each label defined in the function body. *)

Definition alloc_label (lbl: Cminor.label) (maps: labelmap * state) : labelmap * state :=
  let (map, s) := maps in
  let n := s.(st_nextnode) in
  (PTree.set lbl n map,
   mkstate s.(st_nextreg) (Psucc s.(st_nextnode)) s.(st_code) (reserve_instr_wf s)).

Fixpoint reserve_labels (s: stmt) (ms: labelmap * state)
                        {struct s} : labelmap * state :=
  match s with
  | Sseq s1 s2 => reserve_labels s1 (reserve_labels s2 ms)
  | Sifthenelse cond al s1 s2 => reserve_labels s1 (reserve_labels s2 ms)
  | Sloop s1 => reserve_labels s1 ms
  | Sblock s1 => reserve_labels s1 ms
  | Slabel lbl s1 => alloc_label lbl (reserve_labels s1 ms)
  | _ => ms
  end.

(** Translation of a CminorSel function. *)

Definition ret_reg (sig: signature) (rd: reg) : option reg :=
  match sig.(sig_res) with
  | None => None
  | Some ty => Some rd
  end.

Definition transl_fun (f: CminorSel.function) (ngoto: labelmap): mon (node * list reg) :=
  do (rparams, map1) <- add_vars init_mapping f.(CminorSel.fn_params);
  do (rvars, map2) <- add_vars map1 f.(CminorSel.fn_vars);
  do rret <- new_reg;
  let orret := ret_reg f.(CminorSel.fn_sig) rret in
  do nret <- add_instr (Ireturn orret);
  do nentry <- transl_stmt map2 f.(CminorSel.fn_body) nret nil ngoto nret orret;
  ret (nentry, rparams).

Definition transl_function (f: CminorSel.function) : Errors.res RTL.function :=
  let (ngoto, s0) := reserve_labels f.(fn_body) (PTree.empty node, init_state) in
  match transl_fun f ngoto s0 with
  | Error msg => Errors.Error msg
  | OK (nentry, rparams) s i =>
      Errors.OK (RTL.mkfunction
                   f.(CminorSel.fn_sig)
                   rparams
                   f.(CminorSel.fn_stackspace)
                   s.(st_code)
                   nentry)
  end.

Definition transl_fundef := transf_partial_fundef transl_function.

(** Translation of a whole program. *)

Definition transl_program (p: CminorSel.program) : Errors.res RTL.program :=
  transform_partial_program transl_fundef p.
