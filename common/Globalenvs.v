(** Global environments are a component of the dynamic semantics of 
  all languages involved in the compiler.  A global environment
  maps symbol names (names of functions and of global variables)
  to the corresponding memory addresses.  It also maps memory addresses
  of functions to the corresponding function descriptions.  

  Global environments, along with the initial memory state at the beginning
  of program execution, are built from the program of interest, as follows:
- A distinct memory address is assigned to each function of the program.
  These function addresses use negative numbers to distinguish them from
  addresses of memory blocks.  The associations of function name to function
  address and function address to function description are recorded in
  the global environment.
- For each global variable, a memory block is allocated and associated to
  the name of the variable.

  These operations reflect (at a high level of abstraction) what takes
  place during program linking and program loading in a real operating
  system. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Mem.

Set Implicit Arguments.

Module Type GENV.

(** ** Types and operations *)

  Variable t: Set -> Set.
   (** The type of global environments.  The parameter [F] is the type
       of function descriptions. *)

  Variable globalenv: forall (F V: Set), program F V -> t F.
   (** Return the global environment for the given program. *)

  Variable init_mem: forall (F V: Set), program F V -> mem.
   (** Return the initial memory state for the given program. *)

  Variable find_funct_ptr: forall (F: Set), t F -> block -> option F.
   (** Return the function description associated with the given address,
       if any. *)

  Variable find_funct: forall (F: Set), t F -> val -> option F.
   (** Same as [find_funct_ptr] but the function address is given as
       a value, which must be a pointer with offset 0. *)

  Variable find_symbol: forall (F: Set), t F -> ident -> option block.
   (** Return the address of the given global symbol, if any. *)

(** ** Properties of the operations. *)

  Hypothesis find_funct_inv:
    forall (F: Set) (ge: t F) (v: val) (f: F),
    find_funct ge v = Some f -> exists b, v = Vptr b Int.zero.
  Hypothesis find_funct_find_funct_ptr:
    forall (F: Set) (ge: t F) (b: block),
    find_funct ge (Vptr b Int.zero) = find_funct_ptr ge b.    
  Hypothesis find_funct_ptr_prop:
    forall (F V: Set) (P: F -> Prop) (p: program F V) (b: block) (f: F),
    (forall id f, In (id, f) (prog_funct p) -> P f) ->
    find_funct_ptr (globalenv p) b = Some f ->
    P f.
  Hypothesis find_funct_prop:
    forall (F V: Set) (P: F -> Prop) (p: program F V) (v: val) (f: F),
    (forall id f, In (id, f) (prog_funct p) -> P f) ->
    find_funct (globalenv p) v = Some f ->
    P f.
  Hypothesis find_funct_ptr_symbol_inversion:
    forall (F V: Set) (p: program F V) (id: ident) (b: block) (f: F),
    find_symbol (globalenv p) id = Some b ->
    find_funct_ptr (globalenv p) b = Some f ->
    In (id, f) p.(prog_funct).

  Hypothesis initmem_nullptr:
    forall (F V: Set) (p: program F V),
    let m := init_mem p in
    valid_block m nullptr /\
    m.(blocks) nullptr = empty_block 0 0.
  Hypothesis initmem_block_init:
    forall (F V: Set) (p: program F V) (b: block),
    exists id, (init_mem p).(blocks) b = block_init_data id.
  Hypothesis find_funct_ptr_inv:
    forall (F V: Set) (p: program F V) (b: block) (f: F),
    find_funct_ptr (globalenv p) b = Some f -> b < 0.
  Hypothesis find_symbol_inv:
    forall (F V: Set) (p: program F V) (id: ident) (b: block),
    find_symbol (globalenv p) id = Some b -> b < nextblock (init_mem p).

(** Commutation properties between program transformations
  and operations over global environments. *)

  Hypothesis find_funct_ptr_transf:
    forall (A B V: Set) (transf: A -> B) (p: program A V) (b: block) (f: A),
    find_funct_ptr (globalenv p) b = Some f ->
    find_funct_ptr (globalenv (transform_program transf p)) b = Some (transf f).
  Hypothesis find_funct_transf:
    forall (A B V: Set) (transf: A -> B) (p: program A V) (v: val) (f: A),
    find_funct (globalenv p) v = Some f ->
    find_funct (globalenv (transform_program transf p)) v = Some (transf f).
  Hypothesis find_symbol_transf:
    forall (A B V: Set) (transf: A -> B) (p: program A V) (s: ident),
    find_symbol (globalenv (transform_program transf p)) s =
    find_symbol (globalenv p) s.
  Hypothesis init_mem_transf:
    forall (A B V: Set) (transf: A -> B) (p: program A V),
    init_mem (transform_program transf p) = init_mem p.

(** Commutation properties between partial program transformations
  and operations over global environments. *)

  Hypothesis find_funct_ptr_transf_partial:
    forall (A B V: Set) (transf: A -> option B)
           (p: program A V) (p': program B V),
    transform_partial_program transf p = Some p' ->
    forall (b: block) (f: A),
    find_funct_ptr (globalenv p) b = Some f ->
    find_funct_ptr (globalenv p') b = transf f /\ transf f <> None.
  Hypothesis find_funct_transf_partial:
    forall (A B V: Set) (transf: A -> option B)
           (p: program A V) (p': program B V),
    transform_partial_program transf p = Some p' ->
    forall (v: val) (f: A),
    find_funct (globalenv p) v = Some f ->
    find_funct (globalenv p') v = transf f /\ transf f <> None.
  Hypothesis find_symbol_transf_partial:
    forall (A B V: Set) (transf: A -> option B)
           (p: program A V) (p': program B V),
    transform_partial_program transf p = Some p' ->
    forall (s: ident),
    find_symbol (globalenv p') s = find_symbol (globalenv p) s.
  Hypothesis init_mem_transf_partial:
    forall (A B V: Set) (transf: A -> option B)
           (p: program A V) (p': program B V),
    transform_partial_program transf p = Some p' ->
    init_mem p' = init_mem p.

  Hypothesis find_funct_ptr_transf_partial2:
    forall (A B V W: Set) (transf_fun: A -> option B) (transf_var: V -> option W)
           (p: program A V) (p': program B W),
    transform_partial_program2 transf_fun transf_var p = Some p' ->
    forall (b: block) (f: A),
    find_funct_ptr (globalenv p) b = Some f ->
    find_funct_ptr (globalenv p') b = transf_fun f /\ transf_fun f <> None.
  Hypothesis find_funct_transf_partial2:
    forall (A B V W: Set) (transf_fun: A -> option B) (transf_var: V -> option W)
           (p: program A V) (p': program B W),
    transform_partial_program2 transf_fun transf_var p = Some p' ->
    forall (v: val) (f: A),
    find_funct (globalenv p) v = Some f ->
    find_funct (globalenv p') v = transf_fun f /\ transf_fun f <> None.
  Hypothesis find_symbol_transf_partial2:
    forall (A B V W: Set) (transf_fun: A -> option B) (transf_var: V -> option W)
           (p: program A V) (p': program B W),
    transform_partial_program2 transf_fun transf_var p = Some p' ->
    forall (s: ident),
    find_symbol (globalenv p') s = find_symbol (globalenv p) s.
  Hypothesis init_mem_transf_partial2:
    forall (A B V W: Set) (transf_fun: A -> option B) (transf_var: V -> option W)
           (p: program A V) (p': program B W),
    transform_partial_program2 transf_fun transf_var p = Some p' ->
    init_mem p' = init_mem p.

End GENV.

(** The rest of this library is a straightforward implementation of
  the module signature above. *)

Module Genv: GENV.

Section GENV.

Variable F: Set.                    (* The type of functions *)
Variable V: Set.                    (* The type of information over variables *)

Record genv : Set := mkgenv {
  functions: ZMap.t (option F);     (* mapping function ptr -> function *)
  nextfunction: Z;
  symbols: PTree.t block                (* mapping symbol -> block *)
}.

Definition t := genv.

Definition add_funct (name_fun: (ident * F)) (g: genv) : genv :=
  let b := g.(nextfunction) in
  mkgenv (ZMap.set b (Some (snd name_fun)) g.(functions))
         (Zpred b)
         (PTree.set (fst name_fun) b g.(symbols)).

Definition add_symbol (name: ident) (b: block) (g: genv) : genv :=
  mkgenv g.(functions)
         g.(nextfunction)
         (PTree.set name b g.(symbols)).

Definition find_funct_ptr (g: genv) (b: block) : option F :=
  ZMap.get b g.(functions).

Definition find_funct (g: genv) (v: val) : option F :=
  match v with
  | Vptr b ofs =>
      if Int.eq ofs Int.zero then find_funct_ptr g b else None
  | _ =>
      None
  end.

Definition find_symbol (g: genv) (symb: ident) : option block :=
  PTree.get symb g.(symbols).

Lemma find_funct_inv:
  forall (ge: t) (v: val) (f: F),
  find_funct ge v = Some f -> exists b, v = Vptr b Int.zero.
Proof.
  intros until f. unfold find_funct. destruct v; try (intros; discriminate).
  generalize (Int.eq_spec i Int.zero). case (Int.eq i Int.zero); intros.
  exists b. congruence.
  discriminate.
Qed.

Lemma find_funct_find_funct_ptr:
  forall (ge: t) (b: block),
  find_funct ge (Vptr b Int.zero) = find_funct_ptr ge b. 
Proof.
  intros. simpl. 
  generalize (Int.eq_spec Int.zero Int.zero).
  case (Int.eq Int.zero Int.zero); intros.
  auto. tauto.
Qed.

(* Construct environment and initial memory store *)

Definition empty : genv :=
  mkgenv (ZMap.init None) (-1) (PTree.empty block).

Definition add_functs (init: genv) (fns: list (ident * F)) : genv :=
  List.fold_right add_funct init fns.

Definition add_globals 
       (init: genv * mem) (vars: list (ident * list init_data * V))
       : genv * mem :=
  List.fold_right
    (fun (id_init: ident * list init_data * V) (g_st: genv * mem) =>
       match id_init, g_st with
       | ((id, init), info), (g, st) =>
           let (st', b) := Mem.alloc_init_data st init in
           (add_symbol id b g, st')
       end)
    init vars.

Definition globalenv_initmem (p: program F V) : (genv * mem) :=
  add_globals
    (add_functs empty p.(prog_funct), Mem.empty)
    p.(prog_vars).

Definition globalenv (p: program F V) : genv :=
  fst (globalenv_initmem p).
Definition init_mem  (p: program F V) : mem :=
  snd (globalenv_initmem p).

Lemma functions_globalenv:
  forall (p: program F V),
  functions (globalenv p) = functions (add_functs empty p.(prog_funct)).
Proof.
  assert (forall init vars,
     functions (fst (add_globals init vars)) = functions (fst init)).
  induction vars; simpl.
  reflexivity.
  destruct a as [[id1 init1] info1]. destruct (add_globals init vars).
  simpl. exact IHvars. 

  unfold add_globals; simpl. 
  intros. unfold globalenv; unfold globalenv_initmem.
  rewrite H. reflexivity.
Qed.

Lemma initmem_nullptr:
  forall (p: program F V),
  let m := init_mem p in
  valid_block m nullptr /\
  m.(blocks) nullptr = mkblock 0 0 (fun y => Undef) (undef_undef_outside 0 0).
Proof.
  pose (P := fun m => valid_block m nullptr /\
        m.(blocks) nullptr = mkblock 0 0 (fun y => Undef) (undef_undef_outside 0 0)).
  assert (forall init, P (snd init) -> forall vars, P (snd (add_globals init vars))).
  induction vars; simpl; intros.
  auto.
  destruct a as [[id1 in1] inf1]. 
  destruct (add_globals init vars) as [g st]. 
  simpl in *. destruct IHvars. split.
  red; simpl. red in H0. omega.
  simpl. rewrite update_o. auto. unfold block. red in H0. omega. 

  intro. unfold init_mem, globalenv_initmem. apply H. 
  red; simpl. split. compute. auto. reflexivity.
Qed. 

Lemma initmem_block_init:
  forall (p: program F V) (b: block),
  exists id, (init_mem p).(blocks) b = block_init_data id.
Proof.
  assert (forall g0 vars g1 m b,
      add_globals (g0, Mem.empty) vars = (g1, m) ->
      exists id, m.(blocks) b = block_init_data id).
  induction vars; simpl.
  intros. inversion H. unfold Mem.empty; simpl. 
  exists (@nil init_data). symmetry. apply Mem.block_init_data_empty.
  destruct a as [[id1 init1] info1]. 
  caseEq (add_globals (g0, Mem.empty) vars). intros g1 m1 EQ. 
  intros g m b EQ1. injection EQ1; intros EQ2 EQ3; clear EQ1.
  rewrite <- EQ2; simpl. unfold update.
  case (zeq b (nextblock m1)); intro.
  exists init1; auto.
  eauto.
  intros. caseEq (globalenv_initmem p). 
  intros g m EQ. unfold init_mem; rewrite EQ; simpl. 
  unfold globalenv_initmem in EQ. eauto.
Qed.      

Remark nextfunction_add_functs_neg:
  forall fns, nextfunction (add_functs empty fns) < 0.
Proof.
  induction fns; simpl; intros. omega. unfold Zpred. omega.
Qed.

Theorem find_funct_ptr_inv:
  forall (p: program F V) (b: block) (f: F),
  find_funct_ptr (globalenv p) b = Some f -> b < 0.
Proof.
  intros until f.
  assert (forall fns, ZMap.get b (functions (add_functs empty fns)) = Some f -> b < 0).
    induction fns; simpl.
    rewrite ZMap.gi. congruence.
    rewrite ZMap.gsspec. case (ZIndexed.eq b (nextfunction (add_functs empty fns))); intro.
    intro. rewrite e. apply nextfunction_add_functs_neg.
    auto. 
  unfold find_funct_ptr. rewrite functions_globalenv. 
  intros. eauto.
Qed.

Theorem find_symbol_inv:
  forall (p: program F V) (id: ident) (b: block),
  find_symbol (globalenv p) id = Some b -> b < nextblock (init_mem p).
Proof.
  assert (forall fns s b,
    (symbols (add_functs empty fns)) ! s = Some b -> b < 0).
  induction fns; simpl; intros until b.
  rewrite PTree.gempty. congruence.
  rewrite PTree.gsspec. destruct a; simpl. case (peq s i); intro.
  intro EQ; inversion EQ. apply nextfunction_add_functs_neg.
  eauto.
  assert (forall fns vars g m s b,
    add_globals (add_functs empty fns, Mem.empty) vars = (g, m) ->
    (symbols g)!s = Some b ->
    b < nextblock m).
  induction vars; simpl; intros until b.
  intros. inversion H0. subst g m. simpl. 
  generalize (H fns s b H1). omega.
  destruct a as [[id1 init1] info1]. 
  caseEq (add_globals (add_functs empty fns, Mem.empty) vars).
  intros g1 m1 ADG EQ. inversion EQ; subst g m; clear EQ.
  unfold add_symbol; simpl. rewrite PTree.gsspec. case (peq s id1); intro.
  intro EQ; inversion EQ. omega.
  intro. generalize (IHvars _ _ _ _ ADG H0). omega.
  intros until b. unfold find_symbol, globalenv, init_mem, globalenv_initmem; simpl.
  caseEq (add_globals (add_functs empty (prog_funct p), Mem.empty)
                      (prog_vars p)); intros g m EQ.
  simpl; intros. eauto. 
Qed.

End GENV.

(* Invariants on functions *)
Lemma find_funct_ptr_prop:
  forall (F V: Set) (P: F -> Prop) (p: program F V) (b: block) (f: F),
  (forall id f, In (id, f) (prog_funct p) -> P f) ->
  find_funct_ptr (globalenv p) b = Some f ->
  P f.
Proof.
  intros until f.
  unfold find_funct_ptr. rewrite functions_globalenv.
  generalize (prog_funct p). induction l; simpl.
  rewrite ZMap.gi. intros; discriminate.
  rewrite ZMap.gsspec.
  case (ZIndexed.eq b (nextfunction (add_functs (empty F) l))); intros.
  apply H with (fst a). left. destruct a. simpl in *. congruence.
  apply IHl. intros. apply H with id. right. auto. auto.
Qed.

Lemma find_funct_prop:
  forall (F V: Set) (P: F -> Prop) (p: program F V) (v: val) (f: F),
  (forall id f, In (id, f) (prog_funct p) -> P f) ->
  find_funct (globalenv p) v = Some f ->
  P f.
Proof.
  intros until f. unfold find_funct. 
  destruct v; try (intros; discriminate).
  case (Int.eq i Int.zero); [idtac | intros; discriminate].
  intros. eapply find_funct_ptr_prop; eauto.
Qed.

Lemma find_funct_ptr_symbol_inversion:
  forall (F V: Set) (p: program F V) (id: ident) (b: block) (f: F),
  find_symbol (globalenv p) id = Some b ->
  find_funct_ptr (globalenv p) b = Some f ->
  In (id, f) p.(prog_funct).
Proof.
  intros until f.
  assert (forall fns,
           let g := add_functs (empty F) fns in
           PTree.get id g.(symbols) = Some b ->
           b > g.(nextfunction)).
    induction fns; simpl.
    rewrite PTree.gempty. congruence.
    rewrite PTree.gsspec. case (peq id (fst a)); intro.
    intro EQ. inversion EQ. unfold Zpred. omega.
    intros. generalize (IHfns H). unfold Zpred; omega.
  assert (forall fns,
           let g := add_functs (empty F) fns in
           PTree.get id g.(symbols) = Some b ->
           ZMap.get b g.(functions) = Some f ->
           In (id, f) fns).
    induction fns; simpl.
    rewrite ZMap.gi. congruence.
    set (g := add_functs (empty F) fns). 
    rewrite PTree.gsspec. rewrite ZMap.gsspec. 
    case (peq id (fst a)); intro.
    intro EQ. inversion EQ. unfold ZIndexed.eq. rewrite zeq_true. 
    intro EQ2. left. destruct a. simpl in *. congruence. 
    intro. unfold ZIndexed.eq. rewrite zeq_false. intro. eauto.
    generalize (H _ H0). fold g. unfold block. omega.
  assert (forall g0 m0, b < 0 ->
          forall vars g m,
          @add_globals F V (g0, m0) vars = (g, m) ->
          PTree.get id g.(symbols) = Some b ->
          PTree.get id g0.(symbols) = Some b).
    induction vars; simpl.
    intros. inversion H2. auto.
    destruct a as [[id1 init1] info1]. caseEq (add_globals (g0, m0) vars). 
    intros g1 m1 EQ g m EQ1. injection EQ1; simpl; clear EQ1.
    unfold add_symbol; intros A B. rewrite <- B. simpl. 
    rewrite PTree.gsspec. case (peq id id1); intros.
    assert (b > 0). injection H2; intros. rewrite <- H3. apply nextblock_pos. 
    omegaContradiction.
    eauto. 
  intros. 
  generalize (find_funct_ptr_inv _ _ H3). intro.
  pose (g := add_functs (empty F) (prog_funct p)). 
  apply H0.  
  apply H1 with Mem.empty (prog_vars p) (globalenv p) (init_mem p).
  auto. unfold globalenv, init_mem. rewrite <- surjective_pairing.
  reflexivity. assumption. rewrite <- functions_globalenv. assumption.
Qed.

(* Global environments and program transformations. *)

Section TRANSF_PROGRAM_PARTIAL2.

Variable A B V W: Set.
Variable transf_fun: A -> option B.
Variable transf_var: V -> option W.
Variable p: program A V.
Variable p': program B W.
Hypothesis transf_OK:
  transform_partial_program2 transf_fun transf_var p = Some p'.

Lemma add_functs_transf:
  forall (fns: list (ident * A)) (tfns: list (ident * B)),
  map_partial transf_fun fns = Some tfns ->
  let r := add_functs (empty A) fns in
  let tr := add_functs (empty B) tfns in
  nextfunction tr = nextfunction r /\
  symbols tr = symbols r /\
  forall (b: block) (f: A),
  ZMap.get b (functions r) = Some f ->
  ZMap.get b (functions tr) = transf_fun f /\ transf_fun f <> None.
Proof.
  induction fns; simpl.

  intros; injection H; intro; subst tfns.
  simpl. split. reflexivity. split. reflexivity.
  intros b f; repeat (rewrite ZMap.gi). intros; discriminate.

  intro tfns. destruct a. caseEq (transf_fun a). intros a' TA. 
  caseEq (map_partial transf_fun fns). intros l TPP EQ.
  injection EQ; intro; subst tfns.
  clear EQ. simpl. 
  generalize (IHfns l TPP).
  intros [HR1 [HR2 HR3]].
  rewrite HR1. rewrite HR2.
  split. reflexivity.
  split. reflexivity.
  intros b f.
  case (zeq b (nextfunction (add_functs (empty A) fns))); intro.
  subst b. repeat (rewrite ZMap.gss). 
  intro EQ; injection EQ; intro; subst f; clear EQ.
  rewrite TA. split. auto. discriminate.
  repeat (rewrite ZMap.gso; auto). 

  intros; discriminate.
  intros; discriminate.
Qed.

Lemma mem_add_globals_transf:
  forall (g1: genv A) (g2: genv B) (m: mem) 
         (vars: list (ident * list init_data * V))
         (tvars: list (ident * list init_data * W)),
  map_partial transf_var vars = Some tvars ->
  snd (add_globals (g1, m) vars) = snd (add_globals (g2, m) tvars).
Proof.
  induction vars; simpl.
  intros. inversion H. reflexivity.
  intro. destruct a as [[id1 init1] info1]. 
  caseEq (transf_var info1); try congruence.
  intros tinfo1 EQ1.
  caseEq (map_partial transf_var vars); try congruence.
  intros tvars' EQ2 EQ3. 
  inversion EQ3. simpl. 
  generalize (IHvars _ EQ2). 
  destruct (add_globals (g1, m) vars).
  destruct (add_globals (g2, m) tvars').
  simpl. intro. subst m1. auto.
Qed.

Lemma symbols_add_globals_transf:
  forall (g1: genv A) (g2: genv B) (m: mem),
  symbols g1 = symbols g2 ->
  forall (vars: list (ident * list init_data * V))
         (tvars: list (ident * list init_data * W)),
  map_partial transf_var vars = Some tvars ->
  symbols (fst (add_globals (g1, m) vars)) =
  symbols (fst (add_globals (g2, m) tvars)).
Proof.
  induction vars; simpl.
  intros. inversion H0. assumption.
  intro. destruct a as [[id1 init1] info1]. 
  caseEq (transf_var info1); try congruence. intros tinfo1 EQ1.
  caseEq (map_partial transf_var vars); try congruence.
  intros tvars' EQ2 EQ3. inversion EQ3; simpl. 
  generalize (IHvars _ EQ2). 
  generalize (mem_add_globals_transf g1 g2 m vars EQ2).
  destruct (add_globals (g1, m) vars).
  destruct (add_globals (g2, m) tvars').
  simpl. intros. congruence.
Qed.

(*
Lemma prog_funct_transf_OK:
  transf_partial_program transf p.(prog_funct) = Some p'.(prog_funct).
Proof.
  generalize transf_OK; unfold transform_partial_program.
  case (transf_partial_program transf (prog_funct p)); simpl; intros.
  injection transf_OK0; intros; subst p'. reflexivity.
  discriminate.
Qed.
*)

Theorem find_funct_ptr_transf_partial2:
  forall (b: block) (f: A),
  find_funct_ptr (globalenv p) b = Some f ->
  find_funct_ptr (globalenv p') b = transf_fun f /\ transf_fun f <> None.
Proof.
  intros until f. functional inversion transf_OK. 
  destruct (add_functs_transf _ H0) as [P [Q R]]. 
  unfold find_funct_ptr. repeat rewrite functions_globalenv. simpl. 
  auto.
Qed.

Theorem find_funct_transf_partial2:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  find_funct (globalenv p') v = transf_fun f /\ transf_fun f <> None.
Proof.
  intros until f. unfold find_funct. 
  case v; try (intros; discriminate).
  intros b ofs.
  case (Int.eq ofs Int.zero); try (intros; discriminate).
  apply find_funct_ptr_transf_partial2. 
Qed.

Lemma symbols_init_transf2:
  symbols (globalenv p') = symbols (globalenv p).
Proof.
  unfold globalenv. unfold globalenv_initmem.
  functional inversion transf_OK.
  destruct (add_functs_transf _ H0) as [P [Q R]]. 
  simpl. symmetry. apply symbols_add_globals_transf. auto. auto.
Qed.

Theorem find_symbol_transf_partial2:
  forall (s: ident),
  find_symbol (globalenv p') s = find_symbol (globalenv p) s.
Proof.
  intros. unfold find_symbol. 
  rewrite symbols_init_transf2. auto.
Qed.

Theorem init_mem_transf_partial2:
  init_mem p' = init_mem p.
Proof.
  unfold init_mem. unfold globalenv_initmem. 
  functional inversion transf_OK.
  simpl. symmetry. apply mem_add_globals_transf. auto.
Qed.

End TRANSF_PROGRAM_PARTIAL2.


Section TRANSF_PROGRAM_PARTIAL.

Variable A B V: Set.
Variable transf: A -> option B.
Variable p: program A V.
Variable p': program B V.
Hypothesis transf_OK: transform_partial_program transf p = Some p'.

Remark transf2_OK:
  transform_partial_program2 transf (fun x => Some x) p = Some p'.
Proof.
  rewrite <- transf_OK. unfold transform_partial_program2, transform_partial_program.
  destruct (map_partial transf (prog_funct p)); auto.
  rewrite map_partial_identity; auto. 
Qed.

Theorem find_funct_ptr_transf_partial:
  forall (b: block) (f: A),
  find_funct_ptr (globalenv p) b = Some f ->
  find_funct_ptr (globalenv p') b = transf f /\ transf f <> None.
Proof.
  exact (@find_funct_ptr_transf_partial2 _ _ _ _ _ _ _ _ transf2_OK).
Qed.

Theorem find_funct_transf_partial:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  find_funct (globalenv p') v = transf f /\ transf f <> None.
Proof.
  exact (@find_funct_transf_partial2 _ _ _ _ _ _ _ _ transf2_OK).
Qed.

Theorem find_symbol_transf_partial:
  forall (s: ident),
  find_symbol (globalenv p') s = find_symbol (globalenv p) s.
Proof.
  exact (@find_symbol_transf_partial2 _ _ _ _ _ _ _ _ transf2_OK).
Qed.

Theorem init_mem_transf_partial:
  init_mem p' = init_mem p.
Proof.
  exact (@init_mem_transf_partial2 _ _ _ _ _ _ _ _ transf2_OK).
Qed.

End TRANSF_PROGRAM_PARTIAL.

Section TRANSF_PROGRAM.

Variable A B V: Set.
Variable transf: A -> B.
Variable p: program A V.
Let tp := transform_program transf p.

Remark transf_OK:
  transform_partial_program (fun x => Some (transf x)) p = Some tp.
Proof.
  unfold tp, transform_program, transform_partial_program.
  rewrite map_partial_total. reflexivity.
Qed.

Theorem find_funct_ptr_transf:
  forall (b: block) (f: A),
  find_funct_ptr (globalenv p) b = Some f ->
  find_funct_ptr (globalenv tp) b = Some (transf f).
Proof.
  intros. 
  destruct (@find_funct_ptr_transf_partial _ _ _ _ _ _ transf_OK _ _ H)
  as [X Y]. auto.
Qed.

Theorem find_funct_transf:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  find_funct (globalenv tp) v = Some (transf f).
Proof.
  intros. 
  destruct (@find_funct_transf_partial _ _ _ _ _ _ transf_OK _ _ H)
  as [X Y]. auto.
Qed.

Theorem find_symbol_transf:
  forall (s: ident),
  find_symbol (globalenv tp) s = find_symbol (globalenv p) s.
Proof.
  exact (@find_symbol_transf_partial _ _ _ _ _ _ transf_OK).
Qed.

Theorem init_mem_transf:
  init_mem tp = init_mem p.
Proof.
  exact (@init_mem_transf_partial _ _ _ _ _ _ transf_OK).
Qed.

End TRANSF_PROGRAM.

End Genv.
