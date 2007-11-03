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
Require Import Errors.
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

  Hypothesis find_symbol_exists:
    forall (F V: Set) (p: program F V)
           (id: ident) (init: list init_data) (v: V),
    In (id, init, v) (prog_vars p) ->
    exists b, find_symbol (globalenv p) id = Some b.
  Hypothesis find_funct_ptr_exists:
    forall (F V: Set) (p: program F V) (id: ident) (f: F),
    list_norepet (prog_funct_names p) ->
    list_disjoint (prog_funct_names p) (prog_var_names p) ->
    In (id, f) (prog_funct p) ->
    exists b, find_symbol (globalenv p) id = Some b
           /\ find_funct_ptr (globalenv p) b = Some f.

  Hypothesis find_funct_ptr_inversion:
    forall (F V: Set) (P: F -> Prop) (p: program F V) (b: block) (f: F),
    find_funct_ptr (globalenv p) b = Some f ->
    exists id, In (id, f) (prog_funct p).
  Hypothesis find_funct_inversion:
    forall (F V: Set) (P: F -> Prop) (p: program F V) (v: val) (f: F),
    find_funct (globalenv p) v = Some f ->
    exists id, In (id, f) (prog_funct p).
  Hypothesis find_funct_ptr_symbol_inversion:
    forall (F V: Set) (p: program F V) (id: ident) (b: block) (f: F),
    find_symbol (globalenv p) id = Some b ->
    find_funct_ptr (globalenv p) b = Some f ->
    In (id, f) p.(prog_funct).

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

  Hypothesis initmem_nullptr:
    forall (F V: Set) (p: program F V),
    let m := init_mem p in
    valid_block m nullptr /\
    m.(blocks) nullptr = empty_block 0 0.
  Hypothesis initmem_inject_neutral:
    forall (F V: Set) (p: program F V),
    mem_inject_neutral (init_mem p).
  Hypothesis find_funct_ptr_negative:
    forall (F V: Set) (p: program F V) (b: block) (f: F),
    find_funct_ptr (globalenv p) b = Some f -> b < 0.
  Hypothesis find_symbol_not_fresh:
    forall (F V: Set) (p: program F V) (id: ident) (b: block),
    find_symbol (globalenv p) id = Some b -> b < nextblock (init_mem p).
  Hypothesis global_addresses_distinct:
    forall (F V: Set) (p: program F V) id1 id2 b1 b2,
    id1<>id2 ->
    find_symbol (globalenv p) id1 = Some b1 ->
    find_symbol (globalenv p) id2 = Some b2 ->
    b1<>b2.

(** Commutation properties between program transformations
  and operations over global environments. *)

  Hypothesis find_funct_ptr_transf:
    forall (A B V: Set) (transf: A -> B) (p: program A V),
    forall (b: block) (f: A),
    find_funct_ptr (globalenv p) b = Some f ->
    find_funct_ptr (globalenv (transform_program transf p)) b = Some (transf f).
  Hypothesis find_funct_transf:
    forall (A B V: Set) (transf: A -> B) (p: program A V),
    forall (v: val) (f: A),
    find_funct (globalenv p) v = Some f ->
    find_funct (globalenv (transform_program transf p)) v = Some (transf f).
  Hypothesis find_symbol_transf:
    forall (A B V: Set) (transf: A -> B) (p: program A V),
    forall (s: ident),
    find_symbol (globalenv (transform_program transf p)) s =
    find_symbol (globalenv p) s.
  Hypothesis init_mem_transf:
    forall (A B V: Set) (transf: A -> B) (p: program A V),
    init_mem (transform_program transf p) = init_mem p.
  Hypothesis find_funct_ptr_rev_transf:
    forall (A B V: Set) (transf: A -> B) (p: program A V),
    forall (b : block) (tf : B),
    find_funct_ptr (globalenv (transform_program transf p)) b = Some tf ->
    exists f : A, find_funct_ptr (globalenv p) b = Some f /\ transf f = tf.
  Hypothesis find_funct_rev_transf:
    forall (A B V: Set) (transf: A -> B) (p: program A V),
    forall (v : val) (tf : B),
    find_funct (globalenv (transform_program transf p)) v = Some tf ->
    exists f : A, find_funct (globalenv p) v = Some f /\ transf f = tf.

(** Commutation properties between partial program transformations
  and operations over global environments. *)

  Hypothesis find_funct_ptr_transf_partial:
    forall (A B V: Set) (transf: A -> res B) (p: program A V) (p': program B V),
    transform_partial_program transf p = OK p' ->
    forall (b: block) (f: A),
    find_funct_ptr (globalenv p) b = Some f ->
    exists f',
    find_funct_ptr (globalenv p') b = Some f' /\ transf f = OK f'.
  Hypothesis find_funct_transf_partial:
    forall (A B V: Set) (transf: A -> res B) (p: program A V) (p': program B V),
    transform_partial_program transf p = OK p' ->
    forall (v: val) (f: A),
    find_funct (globalenv p) v = Some f ->
    exists f',
    find_funct (globalenv p') v = Some f' /\ transf f = OK f'.
  Hypothesis find_symbol_transf_partial:
    forall (A B V: Set) (transf: A -> res B) (p: program A V) (p': program B V),
    transform_partial_program transf p = OK p' ->
    forall (s: ident),
    find_symbol (globalenv p') s = find_symbol (globalenv p) s.
  Hypothesis init_mem_transf_partial:
    forall (A B V: Set) (transf: A -> res B) (p: program A V) (p': program B V),
    transform_partial_program transf p = OK p' ->
    init_mem p' = init_mem p.
  Hypothesis find_funct_ptr_rev_transf_partial:
    forall (A B V: Set) (transf: A -> res B) (p: program A V) (p': program B V),
    transform_partial_program transf p = OK p' ->
    forall (b : block) (tf : B),
    find_funct_ptr (globalenv p') b = Some tf ->
    exists f : A,
      find_funct_ptr (globalenv p) b = Some f /\ transf f = OK tf.
  Hypothesis find_funct_rev_transf_partial:
    forall (A B V: Set) (transf: A -> res B) (p: program A V) (p': program B V),
    transform_partial_program transf p = OK p' ->
    forall (v : val) (tf : B),
    find_funct (globalenv p') v = Some tf ->
    exists f : A,
      find_funct (globalenv p) v = Some f /\ transf f = OK tf.

  Hypothesis find_funct_ptr_transf_partial2:
    forall (A B V W: Set) (transf_fun: A -> res B) (transf_var: V -> res W)
           (p: program A V) (p': program B W),
    transform_partial_program2 transf_fun transf_var p = OK p' ->
    forall (b: block) (f: A),
    find_funct_ptr (globalenv p) b = Some f ->
    exists f',
    find_funct_ptr (globalenv p') b = Some f' /\ transf_fun f = OK f'.
  Hypothesis find_funct_transf_partial2:
    forall (A B V W: Set) (transf_fun: A -> res B) (transf_var: V -> res W)
           (p: program A V) (p': program B W),
    transform_partial_program2 transf_fun transf_var p = OK p' ->
    forall (v: val) (f: A),
    find_funct (globalenv p) v = Some f ->
    exists f',
    find_funct (globalenv p') v = Some f' /\ transf_fun f = OK f'.
  Hypothesis find_symbol_transf_partial2:
    forall (A B V W: Set) (transf_fun: A -> res B) (transf_var: V -> res W)
           (p: program A V) (p': program B W),
    transform_partial_program2 transf_fun transf_var p = OK p' ->
    forall (s: ident),
    find_symbol (globalenv p') s = find_symbol (globalenv p) s.
  Hypothesis init_mem_transf_partial2:
    forall (A B V W: Set) (transf_fun: A -> res B) (transf_var: V -> res W)
           (p: program A V) (p': program B W),
    transform_partial_program2 transf_fun transf_var p = OK p' ->
    init_mem p' = init_mem p.
  Hypothesis find_funct_ptr_rev_transf_partial2:
    forall (A B V W: Set) (transf_fun: A -> res B) (transf_var: V -> res W)
           (p: program A V) (p': program B W),
    transform_partial_program2 transf_fun transf_var p = OK p' ->
    forall (b : block) (tf : B),
    find_funct_ptr (globalenv p') b = Some tf ->
    exists f : A,
      find_funct_ptr (globalenv p) b = Some f /\ transf_fun f = OK tf.
  Hypothesis find_funct_rev_transf_partial2:
    forall (A B V W: Set) (transf_fun: A -> res B) (transf_var: V -> res W)
           (p: program A V) (p': program B W),
    transform_partial_program2 transf_fun transf_var p = OK p' ->
    forall (v : val) (tf : B),
    find_funct (globalenv p') v = Some tf ->
    exists f : A,
      find_funct (globalenv p) v = Some f /\ transf_fun f = OK tf.

(** Commutation properties between matching between programs
  and operations over global environments. *)

  Hypothesis find_funct_ptr_match:
    forall (A B V W: Set) (match_fun: A -> B -> Prop)
           (match_var: V -> W -> Prop) (p: program A V) (p': program B W),
    match_program match_fun match_var p p' ->
    forall (b : block) (f : A),
    find_funct_ptr (globalenv p) b = Some f ->
    exists tf : B,
    find_funct_ptr (globalenv p') b = Some tf /\ match_fun f tf.
  Hypothesis find_funct_ptr_rev_match:
    forall (A B V W: Set) (match_fun: A -> B -> Prop)
           (match_var: V -> W -> Prop) (p: program A V) (p': program B W),
    match_program match_fun match_var p p' ->
    forall (b : block) (tf : B),
    find_funct_ptr (globalenv p') b = Some tf ->
    exists f : A,
    find_funct_ptr (globalenv p) b = Some f /\ match_fun f tf.
  Hypothesis find_funct_match:
    forall (A B V W: Set) (match_fun: A -> B -> Prop)
           (match_var: V -> W -> Prop) (p: program A V) (p': program B W),
    match_program match_fun match_var p p' ->
    forall (v : val) (f : A),
    find_funct (globalenv p) v = Some f ->
    exists tf : B, find_funct (globalenv p') v = Some tf /\ match_fun f tf.
  Hypothesis find_funct_rev_match:
    forall (A B V W: Set) (match_fun: A -> B -> Prop)
           (match_var: V -> W -> Prop) (p: program A V) (p': program B W),
    match_program match_fun match_var p p' ->
    forall (v : val) (tf : B),
    find_funct (globalenv p') v = Some tf ->
    exists f : A, find_funct (globalenv p) v = Some f /\ match_fun f tf.
  Hypothesis find_symbol_match:
    forall (A B V W: Set) (match_fun: A -> B -> Prop)
           (match_var: V -> W -> Prop) (p: program A V) (p': program B W),
    match_program match_fun match_var p p' ->
    forall (s : ident),
    find_symbol (globalenv p') s = find_symbol (globalenv p) s.
  Hypothesis init_mem_match:
    forall (A B V W: Set) (match_fun: A -> B -> Prop)
           (match_var: V -> W -> Prop) (p: program A V) (p': program B W),
    match_program match_fun match_var p p' ->
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
  m.(blocks) nullptr = mkblock 0 0 (fun y => Undef).
Proof.
  pose (P := fun m => valid_block m nullptr /\
        m.(blocks) nullptr = mkblock 0 0 (fun y => Undef)).
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

Lemma initmem_inject_neutral:
  forall (p: program F V),
  mem_inject_neutral (init_mem p).
Proof.
  assert (forall g0 vars g1 m,
      add_globals (g0, Mem.empty) vars = (g1, m) ->
      mem_inject_neutral m).
  Opaque alloc_init_data.
  induction vars; simpl. 
  intros. inv H. red; intros. destruct (load_inv _ _ _ _ _ H).
  simpl in H1. rewrite Mem.getN_init in H1. 
  replace v with Vundef. auto. destruct chunk; simpl in H1; auto.
  destruct a as [[id1 init1] info1]. 
  caseEq (add_globals (g0, Mem.empty) vars). intros g1 m1 EQ.
  caseEq (alloc_init_data m1 init1). intros m2 b ALLOC.
  intros. inv H. 
  eapply Mem.alloc_init_data_neutral; eauto.
  intros. caseEq (globalenv_initmem p). intros g m EQ.
  unfold init_mem; rewrite EQ; simpl. 
  unfold globalenv_initmem in EQ. eauto.
Qed.      

Remark nextfunction_add_functs_neg:
  forall fns, nextfunction (add_functs empty fns) < 0.
Proof.
  induction fns; simpl; intros. omega. unfold Zpred. omega.
Qed.

Theorem find_funct_ptr_negative:
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

Remark find_symbol_add_functs_neg:
  forall (fns: list (ident * F)) s b,
  find_symbol (add_functs empty fns) s = Some b ->
  b < 0.
Proof.
  unfold find_symbol. induction fns; simpl; intros until b.
  rewrite PTree.gempty. congruence.
  rewrite PTree.gsspec. destruct a; simpl. case (peq s i); intro.
  intro EQ; inversion EQ. apply nextfunction_add_functs_neg.
  eauto.
Qed.

Remark find_symbol_add_globals_not_fresh:
  forall (fns: list (ident * F)) (vars: list (ident * list init_data * V)) g m s b,
  add_globals (add_functs empty fns, Mem.empty) vars = (g, m) ->
  (symbols g)!s = Some b ->
  b < nextblock m.
Proof.
  induction vars; simpl; intros until b.
  intros. inv H. simpl. generalize (find_symbol_add_functs_neg _ _ H0). omega.
  destruct a as [[id1 init1] info1]. 
  caseEq (add_globals (add_functs empty fns, Mem.empty) vars).
  Transparent alloc_init_data. unfold alloc_init_data. 
  intros g1 m1 ADG EQ. inv EQ.
  unfold add_symbol; simpl. rewrite PTree.gsspec. case (peq s id1); intro.
  intro EQ; inversion EQ. omega.
  intro. generalize (IHvars _ _ _ _ ADG H). omega.
Qed.

Theorem find_symbol_not_fresh:
  forall (p: program F V) (id: ident) (b: block),
  find_symbol (globalenv p) id = Some b -> b < nextblock (init_mem p).
Proof.
  intros until b. unfold find_symbol, globalenv, init_mem, globalenv_initmem; simpl.
  caseEq (add_globals (add_functs empty (prog_funct p), Mem.empty)
                      (prog_vars p)); intros g m EQ.
  simpl; intros. eapply find_symbol_add_globals_not_fresh; eauto. 
Qed.

End GENV.

(* Invariants on functions *)

Lemma find_symbol_exists:
  forall (F V: Set) (p: program F V)
         (id: ident) (init: list init_data) (v: V),
  In (id, init, v) (prog_vars p) ->
  exists b, find_symbol (globalenv p) id = Some b.
Proof.
  intros until v.
  assert (forall initm vl, In (id, init, v) vl ->
           exists b, PTree.get id (@symbols F (fst (add_globals initm vl))) = Some b).
  induction vl; simpl; intros.
  elim H.
  destruct a as [[id0 init0] v0]. 
  caseEq (add_globals initm vl). intros g1 m1 EQ. simpl. 
  rewrite PTree.gsspec. destruct (peq id id0). econstructor; eauto.
  elim H; intro. congruence. generalize (IHvl H0). rewrite EQ. auto. 
  intros. unfold globalenv, find_symbol, globalenv_initmem. auto.
Qed.

Remark find_symbol_above_nextfunction:
  forall (F: Set) (id: ident) (b: block) (fns: list (ident * F)),
  let g := add_functs (empty F) fns in
  PTree.get id g.(symbols) = Some b ->
  b > g.(nextfunction).
Proof.
  induction fns; simpl.
  rewrite PTree.gempty. congruence.
  rewrite PTree.gsspec. case (peq id (fst a)); intro.
  intro EQ. inversion EQ. unfold Zpred. omega.
  intros. generalize (IHfns H). unfold Zpred; omega.
Qed.

Remark find_symbol_add_globals:
  forall (F V: Set) (id: ident) (ge_m: t F * mem) (vars: list (ident * list init_data * V)),
  ~In id (map (fun x: ident * list init_data * V => fst(fst x)) vars) ->
  find_symbol (fst (add_globals ge_m vars)) id =
  find_symbol (fst ge_m) id.
Proof.
  unfold find_symbol; induction vars; simpl; intros.
  auto.
  destruct a as [[id0 init0] var0]. simpl in *.
  caseEq (add_globals ge_m vars); intros ge' m' EQ.
  simpl. rewrite PTree.gso. rewrite EQ in IHvars. simpl in IHvars. 
  apply IHvars. tauto. intuition congruence.
Qed.

Lemma find_funct_ptr_exists:
  forall (F V: Set) (p: program F V) (id: ident) (f: F),
  list_norepet (prog_funct_names p) ->
  list_disjoint (prog_funct_names p) (prog_var_names p) ->
  In (id, f) (prog_funct p) ->
  exists b, find_symbol (globalenv p) id = Some b
         /\ find_funct_ptr (globalenv p) b = Some f.
Proof.
  intros until f.
  assert (forall (fns: list (ident * F)),
           list_norepet (map (@fst ident F) fns) ->
           In (id, f) fns ->
           exists b, find_symbol (add_functs (empty F) fns) id = Some b
                   /\ find_funct_ptr (add_functs (empty F) fns) b = Some f).
  unfold find_symbol, find_funct_ptr. induction fns; intros.
  elim H0.
  destruct a as [id0 f0]; simpl in *. inv H. 
  unfold add_funct; simpl.
  rewrite PTree.gsspec. destruct (peq id id0). 
  subst id0. econstructor; split. eauto.
  replace f0 with f. apply ZMap.gss. 
  elim H0; intro. congruence. elim H3. 
  change id with (@fst ident F (id, f)). apply List.in_map. auto.
  exploit IHfns; eauto. elim H0; intro. congruence. auto.
  intros [b [X Y]]. exists b; split. auto. rewrite ZMap.gso. auto.
  generalize (find_symbol_above_nextfunction _ _ X).
  unfold block; unfold ZIndexed.t; intro; omega.

  intros. exploit H; eauto. assumption. intros [b [X Y]].
  exists b; split.
  unfold globalenv, globalenv_initmem. rewrite find_symbol_add_globals. 
  assumption. apply list_disjoint_notin with (prog_funct_names p). assumption. 
  unfold prog_funct_names. change id with (fst (id, f)). 
  apply List.in_map; auto.
  unfold find_funct_ptr. rewrite functions_globalenv. 
  assumption. 
Qed.

Lemma find_funct_ptr_inversion:
  forall (F V: Set) (P: F -> Prop) (p: program F V) (b: block) (f: F),
  find_funct_ptr (globalenv p) b = Some f ->
  exists id, In (id, f) (prog_funct p).
Proof.
  intros until f.
  assert (forall fns: list (ident * F),
    find_funct_ptr (add_functs (empty F) fns) b = Some f ->
    exists id, In (id, f) fns).
  unfold find_funct_ptr. induction fns; simpl.
  rewrite ZMap.gi. congruence.
  destruct a as [id0 f0]; simpl. 
  rewrite ZMap.gsspec. destruct (ZIndexed.eq b (nextfunction (add_functs (empty F) fns))).
  intro. inv H. exists id0; auto.
  intro. exploit IHfns; eauto. intros [id A]. exists id; auto.
  unfold find_funct_ptr; rewrite functions_globalenv. intros; apply H; auto.
Qed.

Lemma find_funct_ptr_prop:
  forall (F V: Set) (P: F -> Prop) (p: program F V) (b: block) (f: F),
  (forall id f, In (id, f) (prog_funct p) -> P f) ->
  find_funct_ptr (globalenv p) b = Some f ->
  P f.
Proof.
  intros. exploit find_funct_ptr_inversion; eauto. intros [id A]. eauto.
Qed.

Lemma find_funct_inversion:
  forall (F V: Set) (P: F -> Prop) (p: program F V) (v: val) (f: F),
  find_funct (globalenv p) v = Some f ->
  exists id, In (id, f) (prog_funct p).
Proof.
  intros. exploit find_funct_inv; eauto. intros [b EQ]. rewrite EQ in H.
  rewrite find_funct_find_funct_ptr in H. 
  eapply find_funct_ptr_inversion; eauto.
Qed.

Lemma find_funct_prop:
  forall (F V: Set) (P: F -> Prop) (p: program F V) (v: val) (f: F),
  (forall id f, In (id, f) (prog_funct p) -> P f) ->
  find_funct (globalenv p) v = Some f ->
  P f.
Proof.
  intros. exploit find_funct_inversion; eauto. intros [id A]. eauto.
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
    generalize (find_symbol_above_nextfunction _ _ H). fold g. unfold block. omega.
  assert (forall g0 m0, b < 0 ->
          forall vars g m,
          @add_globals F V (g0, m0) vars = (g, m) ->
          PTree.get id g.(symbols) = Some b ->
          PTree.get id g0.(symbols) = Some b).
    induction vars; simpl.
    intros. inv H1. auto.
    destruct a as [[id1 init1] info1]. caseEq (add_globals (g0, m0) vars). 
    intros g1 m1 EQ g m EQ1. injection EQ1; simpl; clear EQ1.
    unfold add_symbol; intros A B. rewrite <- B. simpl. 
    rewrite PTree.gsspec. case (peq id id1); intros.
    assert (b > 0). inv H1. apply nextblock_pos. 
    omegaContradiction.
    eauto. 
  intros. 
  generalize (find_funct_ptr_negative _ _ H2). intro.
  pose (g := add_functs (empty F) (prog_funct p)). 
  apply H.  
  apply H0 with Mem.empty (prog_vars p) (globalenv p) (init_mem p).
  auto. unfold globalenv, init_mem. rewrite <- surjective_pairing.
  reflexivity. assumption. rewrite <- functions_globalenv. assumption.
Qed.

Theorem global_addresses_distinct:
  forall (F V: Set) (p: program F V) id1 id2 b1 b2,
  id1<>id2 ->
  find_symbol (globalenv p) id1 = Some b1 ->
  find_symbol (globalenv p) id2 = Some b2 ->
  b1<>b2.
Proof.
  intros.
  assert (forall fns,
    find_symbol (add_functs (empty F) fns) id1 = Some b1 ->
    find_symbol (add_functs (empty F) fns) id2 = Some b2 ->
    b1 <> b2).
  unfold find_symbol. induction fns; simpl; intros.
  rewrite PTree.gempty in H2. discriminate.
  destruct a as [id f]; simpl in *. 
  rewrite PTree.gsspec in H2.
  destruct (peq id1 id). subst id. inv H2.
  rewrite PTree.gso in H3; auto. 
  generalize (find_symbol_above_nextfunction _ _ H3). unfold block. omega.
  rewrite PTree.gsspec in H3. 
  destruct (peq id2 id). subst id. inv H3.
  generalize (find_symbol_above_nextfunction _ _ H2). unfold block. omega.
  eauto.
  set (ge0 := add_functs (empty F) p.(prog_funct)).
  assert (forall (vars: list (ident * list init_data * V)) ge m,
    add_globals (ge0, Mem.empty) vars = (ge, m) ->
    find_symbol ge id1 = Some b1 ->
    find_symbol ge id2 = Some b2 ->
    b1 <> b2).
  unfold find_symbol. induction vars; simpl. 
  intros. inv H3. subst ge. apply H2 with (p.(prog_funct)); auto. 
  intros ge m. destruct a as [[id init] info]. 
  caseEq (add_globals (ge0, Mem.empty) vars). intros ge1 m1 A B. inv B.
  unfold add_symbol. simpl. intros.
  rewrite PTree.gsspec in H3; destruct (peq id1 id). subst id. inv H3.
  rewrite PTree.gso in H4; auto. 
  generalize (find_symbol_add_globals_not_fresh _ _ _ A H4). unfold block; omega.
  rewrite PTree.gsspec in H4; destruct (peq id2 id). subst id. inv H4.
  generalize (find_symbol_add_globals_not_fresh _ _ _ A H3). unfold block; omega.
  eauto.
  set (ge_m := add_globals (ge0, Mem.empty) p.(prog_vars)).
  apply H3 with (p.(prog_vars)) (fst ge_m) (snd ge_m).
  fold ge_m. apply surjective_pairing. auto. auto.
Qed.

(* Global environments and program transformations. *)

Section MATCH_PROGRAM.

Variable A B V W: Set.
Variable match_fun: A -> B -> Prop.
Variable match_var: V -> W -> Prop.
Variable p: program A V.
Variable p': program B W.
Hypothesis match_prog:
  match_program match_fun match_var p p'.

Lemma add_functs_match:
  forall (fns: list (ident * A)) (tfns: list (ident * B)),
  list_forall2 (match_funct_entry match_fun) fns tfns ->
  let r := add_functs (empty A) fns in
  let tr := add_functs (empty B) tfns in
  nextfunction tr = nextfunction r /\
  symbols tr = symbols r /\
  forall (b: block) (f: A),
  ZMap.get b (functions r) = Some f ->
  exists tf, ZMap.get b (functions tr) = Some tf /\ match_fun f tf.
Proof.
  induction 1; simpl.

  split. reflexivity. split. reflexivity.
  intros b f; repeat (rewrite ZMap.gi). intros; discriminate.

  destruct a1 as [id1 fn1]. destruct b1 as [id2 fn2]. 
  simpl. red in H. destruct H. 
  destruct IHlist_forall2 as [X [Y Z]].
  rewrite X. rewrite Y.  
  split. auto.
  split. congruence.
  intros b f.
  repeat (rewrite ZMap.gsspec). 
  destruct (ZIndexed.eq b (nextfunction (add_functs (empty A) al))).
  intro EQ; inv EQ. exists fn2; auto.
  auto.
Qed.

Lemma add_functs_rev_match:
  forall (fns: list (ident * A)) (tfns: list (ident * B)),
  list_forall2 (match_funct_entry match_fun) fns tfns ->
  let r := add_functs (empty A) fns in
  let tr := add_functs (empty B) tfns in
  nextfunction tr = nextfunction r /\
  symbols tr = symbols r /\
  forall (b: block) (tf: B),
  ZMap.get b (functions tr) = Some tf ->
  exists f, ZMap.get b (functions r) = Some f /\ match_fun f tf.
Proof.
  induction 1; simpl.

  split. reflexivity. split. reflexivity.
  intros b f; repeat (rewrite ZMap.gi). intros; discriminate.

  destruct a1 as [id1 fn1]. destruct b1 as [id2 fn2]. 
  simpl. red in H. destruct H. 
  destruct IHlist_forall2 as [X [Y Z]].
  rewrite X. rewrite Y.  
  split. auto.
  split. congruence.
  intros b f.
  repeat (rewrite ZMap.gsspec). 
  destruct (ZIndexed.eq b (nextfunction (add_functs (empty A) al))).
  intro EQ; inv EQ. exists fn1; auto.
  auto.
Qed.

Lemma mem_add_globals_match:
  forall (g1: genv A) (g2: genv B) (m: mem) 
         (vars: list (ident * list init_data * V))
         (tvars: list (ident * list init_data * W)),
  list_forall2 (match_var_entry match_var) vars tvars ->
  snd (add_globals (g1, m) vars) = snd (add_globals (g2, m) tvars).
Proof.
  induction 1; simpl.
  auto.
  destruct a1 as [[id1 init1] info1].
  destruct b1 as [[id2 init2] info2].
  red in H. destruct H as [X [Y Z]]. subst id2 init2. 
  generalize IHlist_forall2. 
  destruct (add_globals (g1, m) al).
  destruct (add_globals (g2, m) bl).
  simpl. intro. subst m1. auto.
Qed.

Lemma symbols_add_globals_match:
  forall (g1: genv A) (g2: genv B) (m: mem),
  symbols g1 = symbols g2 ->
  forall (vars: list (ident * list init_data * V))
         (tvars: list (ident * list init_data * W)),
  list_forall2 (match_var_entry match_var) vars tvars ->
  symbols (fst (add_globals (g1, m) vars)) =
  symbols (fst (add_globals (g2, m) tvars)).
Proof.
  induction 2; simpl.
  auto.
  destruct a1 as [[id1 init1] info1].
  destruct b1 as [[id2 init2] info2].
  red in H0. destruct H0 as [X [Y Z]]. subst id2 init2. 
  generalize IHlist_forall2.
  generalize (mem_add_globals_match g1 g2 m H1).
  destruct (add_globals (g1, m) al).
  destruct (add_globals (g2, m) bl).
  simpl. intros. congruence.
Qed.

Theorem find_funct_ptr_match:
  forall (b: block) (f: A),
  find_funct_ptr (globalenv p) b = Some f ->
  exists tf, find_funct_ptr (globalenv p') b = Some tf /\ match_fun f tf.
Proof.
  intros until f. destruct match_prog as [X [Y Z]]. 
  destruct (add_functs_match X) as [P [Q R]]. 
  unfold find_funct_ptr. repeat rewrite functions_globalenv.
  auto.
Qed.

Theorem find_funct_ptr_rev_match:
  forall (b: block) (tf: B),
  find_funct_ptr (globalenv p') b = Some tf ->
  exists f, find_funct_ptr (globalenv p) b = Some f /\ match_fun f tf.
Proof.
  intros until tf. destruct match_prog as [X [Y Z]]. 
  destruct (add_functs_rev_match X) as [P [Q R]]. 
  unfold find_funct_ptr. repeat rewrite functions_globalenv.
  auto.
Qed.

Theorem find_funct_match:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  exists tf, find_funct (globalenv p') v = Some tf /\ match_fun f tf.
Proof.
  intros until f. unfold find_funct. 
  case v; try (intros; discriminate).
  intros b ofs.
  case (Int.eq ofs Int.zero); try (intros; discriminate).
  apply find_funct_ptr_match.
Qed.

Theorem find_funct_rev_match:
  forall (v: val) (tf: B),
  find_funct (globalenv p') v = Some tf ->
  exists f, find_funct (globalenv p) v = Some f /\ match_fun f tf.
Proof.
  intros until tf. unfold find_funct. 
  case v; try (intros; discriminate).
  intros b ofs.
  case (Int.eq ofs Int.zero); try (intros; discriminate).
  apply find_funct_ptr_rev_match.
Qed.

Lemma symbols_init_match:
  symbols (globalenv p') = symbols (globalenv p).
Proof.
  unfold globalenv. unfold globalenv_initmem.
  destruct match_prog as [X [Y Z]].
  destruct (add_functs_match X) as [P [Q R]]. 
  simpl. symmetry. apply symbols_add_globals_match. auto. auto.
Qed.

Theorem find_symbol_match:
  forall (s: ident),
  find_symbol (globalenv p') s = find_symbol (globalenv p) s.
Proof.
  intros. unfold find_symbol. 
  rewrite symbols_init_match. auto.
Qed.

Theorem init_mem_match:
  init_mem p' = init_mem p.
Proof.
  unfold init_mem. unfold globalenv_initmem.
  destruct match_prog as [X [Y Z]]. 
  symmetry. apply mem_add_globals_match. auto.
Qed.

End MATCH_PROGRAM.

Section TRANSF_PROGRAM_PARTIAL2.

Variable A B V W: Set.
Variable transf_fun: A -> res B.
Variable transf_var: V -> res W.
Variable p: program A V.
Variable p': program B W.
Hypothesis transf_OK:
  transform_partial_program2 transf_fun transf_var p = OK p'.

Remark prog_match:
  match_program
    (fun fd tfd => transf_fun fd = OK tfd)
    (fun info tinfo => transf_var info = OK tinfo)
    p p'.
Proof.
  apply transform_partial_program2_match; auto.
Qed.

Theorem find_funct_ptr_transf_partial2:
  forall (b: block) (f: A),
  find_funct_ptr (globalenv p) b = Some f ->
  exists f',
  find_funct_ptr (globalenv p') b = Some f' /\ transf_fun f = OK f'.
Proof.
  intros. 
  exploit find_funct_ptr_match. eexact prog_match. eauto. 
  intros [tf [X Y]]. exists tf; auto.
Qed.

Theorem find_funct_ptr_rev_transf_partial2:
  forall (b: block) (tf: B),
  find_funct_ptr (globalenv p') b = Some tf ->
  exists f, find_funct_ptr (globalenv p) b = Some f /\ transf_fun f = OK tf.
Proof.
  intros. 
  exploit find_funct_ptr_rev_match. eexact prog_match. eauto. auto. 
Qed.

Theorem find_funct_transf_partial2:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  exists f',
  find_funct (globalenv p') v = Some f' /\ transf_fun f = OK f'.
Proof.
  intros. 
  exploit find_funct_match. eexact prog_match. eauto. 
  intros [tf [X Y]]. exists tf; auto.
Qed.

Theorem find_funct_rev_transf_partial2:
  forall (v: val) (tf: B),
  find_funct (globalenv p') v = Some tf ->
  exists f, find_funct (globalenv p) v = Some f /\ transf_fun f = OK tf.
Proof.
  intros. 
  exploit find_funct_rev_match. eexact prog_match. eauto. auto. 
Qed.

Theorem find_symbol_transf_partial2:
  forall (s: ident),
  find_symbol (globalenv p') s = find_symbol (globalenv p) s.
Proof.
  intros. eapply find_symbol_match. eexact prog_match.
Qed.

Theorem init_mem_transf_partial2:
  init_mem p' = init_mem p.
Proof.
  intros. eapply init_mem_match. eexact prog_match.
Qed.

End TRANSF_PROGRAM_PARTIAL2.

Section TRANSF_PROGRAM_PARTIAL.

Variable A B V: Set.
Variable transf: A -> res B.
Variable p: program A V.
Variable p': program B V.
Hypothesis transf_OK: transform_partial_program transf p = OK p'.

Remark transf2_OK:
  transform_partial_program2 transf (fun x => OK x) p = OK p'.
Proof.
  rewrite <- transf_OK. unfold transform_partial_program2, transform_partial_program.
  destruct (map_partial prefix_funct_name transf (prog_funct p)); auto.
  rewrite map_partial_identity; auto. 
Qed.

Theorem find_funct_ptr_transf_partial:
  forall (b: block) (f: A),
  find_funct_ptr (globalenv p) b = Some f ->
  exists f',
  find_funct_ptr (globalenv p') b = Some f' /\ transf f = OK f'.
Proof.
  exact (@find_funct_ptr_transf_partial2 _ _ _ _ _ _ _ _ transf2_OK).
Qed.

Theorem find_funct_ptr_rev_transf_partial:
  forall (b: block) (tf: B),
  find_funct_ptr (globalenv p') b = Some tf ->
  exists f, find_funct_ptr (globalenv p) b = Some f /\ transf f = OK tf.
Proof.
  exact (@find_funct_ptr_rev_transf_partial2 _ _ _ _ _ _ _ _ transf2_OK).
Qed.

Theorem find_funct_transf_partial:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  exists f',
  find_funct (globalenv p') v = Some f' /\ transf f = OK f'.
Proof.
  exact (@find_funct_transf_partial2 _ _ _ _ _ _ _ _ transf2_OK).
Qed.

Theorem find_funct_rev_transf_partial:
  forall (v: val) (tf: B),
  find_funct (globalenv p') v = Some tf ->
  exists f, find_funct (globalenv p) v = Some f /\ transf f = OK tf.
Proof.
  exact (@find_funct_rev_transf_partial2 _ _ _ _ _ _ _ _ transf2_OK).
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
  transform_partial_program (fun x => OK (transf x)) p = OK tp.
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
  as [f' [X Y]]. congruence.
Qed.

Theorem find_funct_ptr_rev_transf:
  forall (b: block) (tf: B),
  find_funct_ptr (globalenv tp) b = Some tf ->
  exists f, find_funct_ptr (globalenv p) b = Some f /\ transf f = tf.
Proof.
  intros. exploit find_funct_ptr_rev_transf_partial. eexact transf_OK. eauto.
  intros [f [X Y]]. exists f; split. auto. congruence.
Qed.

Theorem find_funct_transf:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  find_funct (globalenv tp) v = Some (transf f).
Proof.
  intros. 
  destruct (@find_funct_transf_partial _ _ _ _ _ _ transf_OK _ _ H)
  as [f' [X Y]]. congruence.
Qed.

Theorem find_funct_rev_transf:
  forall (v: val) (tf: B),
  find_funct (globalenv tp) v = Some tf ->
  exists f, find_funct (globalenv p) v = Some f /\ transf f = tf.
Proof.
  intros. exploit find_funct_rev_transf_partial. eexact transf_OK. eauto.
  intros [f [X Y]]. exists f; split. auto. congruence.
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
