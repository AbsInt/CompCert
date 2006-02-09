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

  Variable globalenv: forall (F: Set), program F -> t F.
   (** Return the global environment for the given program. *)

  Variable init_mem: forall (F: Set), program F -> mem.
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
    forall (F: Set) (P: F -> Prop) (p: program F) (b: block) (f: F),
    (forall id f, In (id, f) (prog_funct p) -> P f) ->
    find_funct_ptr (globalenv p) b = Some f ->
    P f.
  Hypothesis find_funct_prop:
    forall (F: Set) (P: F -> Prop) (p: program F) (v: val) (f: F),
    (forall id f, In (id, f) (prog_funct p) -> P f) ->
    find_funct (globalenv p) v = Some f ->
    P f.
  Hypothesis initmem_nullptr:
    forall (F: Set) (p: program F),
    let m := init_mem p in
    valid_block m nullptr /\
    m.(blocks) nullptr = empty_block 0 0.
  Hypothesis initmem_undef:
    forall (F: Set) (p: program F) (b: block),
    exists lo, exists hi, 
    (init_mem p).(blocks) b = empty_block lo hi.
  Hypothesis find_funct_ptr_inv:
    forall (F: Set) (p: program F) (b: block) (f: F),
    find_funct_ptr (globalenv p) b = Some f -> b < 0.
  Hypothesis find_symbol_inv:
    forall (F: Set) (p: program F) (id: ident) (b: block),
    find_symbol (globalenv p) id = Some b -> b < nextblock (init_mem p).

(** Commutation properties between program transformations
  and operations over global environments. *)

  Hypothesis find_funct_ptr_transf:
    forall (A B: Set) (transf: A -> B) (p: program A) (b: block) (f: A),
    find_funct_ptr (globalenv p) b = Some f ->
    find_funct_ptr (globalenv (transform_program transf p)) b = Some (transf f).
  Hypothesis find_funct_transf:
    forall (A B: Set) (transf: A -> B) (p: program A) (v: val) (f: A),
    find_funct (globalenv p) v = Some f ->
    find_funct (globalenv (transform_program transf p)) v = Some (transf f).
  Hypothesis find_symbol_transf:
    forall (A B: Set) (transf: A -> B) (p: program A) (s: ident),
    find_symbol (globalenv (transform_program transf p)) s =
    find_symbol (globalenv p) s.
  Hypothesis init_mem_transf:
    forall (A B: Set) (transf: A -> B) (p: program A),
    init_mem (transform_program transf p) = init_mem p.

(** Commutation properties between partial program transformations
  and operations over global environments. *)

  Hypothesis find_funct_ptr_transf_partial:
    forall (A B: Set) (transf: A -> option B)
           (p: program A) (p': program B),
    transform_partial_program transf p = Some p' ->
    forall (b: block) (f: A),
    find_funct_ptr (globalenv p) b = Some f ->
    find_funct_ptr (globalenv p') b = transf f /\ transf f <> None.
  Hypothesis find_funct_transf_partial:
    forall (A B: Set) (transf: A -> option B)
           (p: program A) (p': program B),
    transform_partial_program transf p = Some p' ->
    forall (v: val) (f: A),
    find_funct (globalenv p) v = Some f ->
    find_funct (globalenv p') v = transf f /\ transf f <> None.
  Hypothesis find_symbol_transf_partial:
    forall (A B: Set) (transf: A -> option B)
           (p: program A) (p': program B),
    transform_partial_program transf p = Some p' ->
    forall (s: ident),
    find_symbol (globalenv p') s = find_symbol (globalenv p) s.
  Hypothesis init_mem_transf_partial:
    forall (A B: Set) (transf: A -> option B)
           (p: program A) (p': program B),
    transform_partial_program transf p = Some p' ->
    init_mem p' = init_mem p.
End GENV.

(** The rest of this library is a straightforward implementation of
  the module signature above. *)

Module Genv: GENV.

Section GENV.

Variable funct: Set.                    (* The type of functions *)

Record genv : Set := mkgenv {
  functions: ZMap.t (option funct);     (* mapping function ptr -> function *)
  nextfunction: Z;
  symbols: PTree.t block                (* mapping symbol -> block *)
}.

Definition t := genv.

Definition add_funct (name_fun: (ident * funct)) (g: genv) : genv :=
  let b := g.(nextfunction) in
  mkgenv (ZMap.set b (Some (snd name_fun)) g.(functions))
         (Zpred b)
         (PTree.set (fst name_fun) b g.(symbols)).

Definition add_symbol (name: ident) (b: block) (g: genv) : genv :=
  mkgenv g.(functions)
         g.(nextfunction)
         (PTree.set name b g.(symbols)).

Definition find_funct_ptr (g: genv) (b: block) : option funct :=
  ZMap.get b g.(functions).

Definition find_funct (g: genv) (v: val) : option funct :=
  match v with
  | Vptr b ofs =>
      if Int.eq ofs Int.zero then find_funct_ptr g b else None
  | _ =>
      None
  end.

Definition find_symbol (g: genv) (symb: ident) : option block :=
  PTree.get symb g.(symbols).

Lemma find_funct_inv:
  forall (ge: t) (v: val) (f: funct),
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

Definition add_functs (init: genv) (fns: list (ident * funct)) : genv :=
  List.fold_right add_funct init fns.

Definition add_globals 
        (init: genv * mem) (vars: list (ident * Z)) : genv * mem :=
  List.fold_right
    (fun (id_sz: ident * Z) (g_st: genv * mem) =>
       let (id, sz) := id_sz in
       let (g, st) := g_st in
       let (st', b) := Mem.alloc st 0 sz in
       (add_symbol id b g, st'))
    init vars.

Definition globalenv_initmem (p: program funct) : (genv * mem) :=
  add_globals
    (add_functs empty p.(prog_funct), Mem.empty)
    p.(prog_vars).

Definition globalenv (p: program funct) : genv :=
  fst (globalenv_initmem p).
Definition init_mem  (p: program funct) : mem :=
  snd (globalenv_initmem p).

Lemma functions_globalenv:
  forall (p: program funct),
  functions (globalenv p) = functions (add_functs empty p.(prog_funct)).
Proof.
  assert (forall (init: genv * mem) (vars: list (ident * Z)),
     functions (fst (add_globals init vars)) = functions (fst init)).
  induction vars; simpl.
  reflexivity.
  destruct a. destruct (add_globals init vars).
  simpl. exact IHvars. 

  unfold add_globals; simpl. 
  intros. unfold globalenv; unfold globalenv_initmem.
  rewrite H. reflexivity.
Qed.

Lemma initmem_nullptr:
  forall (p: program funct),
  let m := init_mem p in
  valid_block m nullptr /\
  m.(blocks) nullptr = mkblock 0 0 (fun y => Undef) (undef_undef_outside 0 0).
Proof.
  assert
   (forall (init: genv * mem),
    let m1 := snd init in
    0 < m1.(nextblock) ->
    m1.(blocks) nullptr = mkblock 0 0 (fun y => Undef) (undef_undef_outside 0 0) ->
    forall (vars: list (ident * Z)),
    let m2 := snd (add_globals init vars) in
    0 < m2.(nextblock) /\
    m2.(blocks) nullptr = mkblock 0 0 (fun y => Undef) (undef_undef_outside 0 0)).
  induction vars; simpl; intros.
  tauto.
  destruct a. 
  caseEq (add_globals init vars). intros g m2 EQ. 
  rewrite EQ in IHvars. simpl in IHvars. elim IHvars; intros.
  simpl. split. omega. 
  rewrite update_o. auto. apply sym_not_equal. apply Zlt_not_eq. exact H1.

  intro. unfold init_mem. unfold globalenv_initmem. 
  unfold valid_block. apply H. simpl. omega. reflexivity.
Qed. 

Lemma initmem_undef:
  forall (p: program funct) (b: block),
  exists lo, exists hi, 
  (init_mem p).(blocks) b = empty_block lo hi.
Proof.
  assert (forall g0 vars g1 m b,
      add_globals (g0, Mem.empty) vars = (g1, m) ->
      exists lo, exists hi, 
      m.(blocks) b = empty_block lo hi).
  induction vars; simpl.
  intros. inversion H. unfold Mem.empty; simpl. 
  exists 0; exists 0. auto.
  destruct a. caseEq (add_globals (g0, Mem.empty) vars). intros g1 m1 EQ. 
  intros g m b EQ1. injection EQ1; intros EQ2 EQ3; clear EQ1.
  rewrite <- EQ2; simpl. unfold update.
  case (zeq b (nextblock m1)); intro.
  exists 0; exists z; auto.
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
  forall (p: program funct) (b: block) (f: funct),
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
  forall (p: program funct) (id: ident) (b: block),
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
  destruct a. caseEq (add_globals (add_functs empty fns, Mem.empty) vars).
  intros g1 m1 ADG EQ. inversion EQ; subst g m; clear EQ.
  unfold add_symbol; simpl. rewrite PTree.gsspec. case (peq s i); intro.
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
  forall (F: Set) (P: F -> Prop) (p: program F) (b: block) (f: F),
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
  forall (F: Set) (P: F -> Prop) (p: program F) (v: val) (f: F),
  (forall id f, In (id, f) (prog_funct p) -> P f) ->
  find_funct (globalenv p) v = Some f ->
  P f.
Proof.
  intros until f. unfold find_funct. 
  destruct v; try (intros; discriminate).
  case (Int.eq i Int.zero); [idtac | intros; discriminate].
  intros. eapply find_funct_ptr_prop; eauto.
Qed.

(* Global environments and program transformations. *)

Section TRANSF_PROGRAM_PARTIAL.

Variable A B: Set.
Variable transf: A -> option B.
Variable p: program A.
Variable p': program B.
Hypothesis transf_OK: transform_partial_program transf p = Some p'.

Lemma add_functs_transf:
  forall (fns: list (ident * A)) (tfns: list (ident * B)),
  transf_partial_program transf fns = Some tfns ->
  let r := add_functs (empty A) fns in
  let tr := add_functs (empty B) tfns in
  nextfunction tr = nextfunction r /\
  symbols tr = symbols r /\
  forall (b: block) (f: A),
  ZMap.get b (functions r) = Some f ->
  ZMap.get b (functions tr) = transf f /\ transf f <> None.
Proof.
  induction fns; simpl.

  intros; injection H; intro; subst tfns.
  simpl. split. reflexivity. split. reflexivity.
  intros b f; repeat (rewrite ZMap.gi). intros; discriminate.

  intro tfns. destruct a. caseEq (transf a). intros a' TA. 
  caseEq (transf_partial_program transf fns). intros l TPP EQ.
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
  forall (g1: genv A) (g2: genv B) (m: mem) (vars: list (ident * Z)),
  snd (add_globals (g1, m) vars) = snd (add_globals (g2, m) vars).
Proof.
  induction vars; simpl.
  reflexivity.
  destruct a. destruct (add_globals (g1, m) vars).
  destruct (add_globals (g2, m) vars).
  simpl in IHvars. subst m1. reflexivity. 
Qed. 

Lemma symbols_add_globals_transf:
  forall (g1: genv A) (g2: genv B) (m: mem),
  symbols g1 = symbols g2 ->
  forall (vars: list (ident * Z)),
  symbols (fst (add_globals (g1, m) vars)) =
  symbols (fst (add_globals (g2, m) vars)).
Proof.
  induction vars; simpl.
  assumption.
  generalize (mem_add_globals_transf g1 g2 m vars); intro.
  destruct a. destruct (add_globals (g1, m) vars).
  destruct (add_globals (g2, m) vars).
  simpl. simpl in IHvars. simpl in H0. 
  rewrite H0; rewrite IHvars. reflexivity.
Qed.

Lemma prog_funct_transf_OK:
  transf_partial_program transf p.(prog_funct) = Some p'.(prog_funct).
Proof.
  generalize transf_OK; unfold transform_partial_program.
  case (transf_partial_program transf (prog_funct p)); simpl; intros.
  injection transf_OK0; intros; subst p'. reflexivity.
  discriminate.
Qed.

Theorem find_funct_ptr_transf_partial:
  forall (b: block) (f: A),
  find_funct_ptr (globalenv p) b = Some f ->
  find_funct_ptr (globalenv p') b = transf f /\ transf f <> None.
Proof.
  intros until f. 
  generalize (add_functs_transf p.(prog_funct) prog_funct_transf_OK).
  intros [X [Y Z]].
  unfold find_funct_ptr. 
  repeat (rewrite functions_globalenv). 
  apply Z. 
Qed.

Theorem find_funct_transf_partial:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  find_funct (globalenv p') v = transf f /\ transf f <> None.
Proof.
  intros until f. unfold find_funct. 
  case v; try (intros; discriminate).
  intros b ofs.
  case (Int.eq ofs Int.zero); try (intros; discriminate).
  apply find_funct_ptr_transf_partial. 
Qed.

Lemma symbols_init_transf:
  symbols (globalenv p') = symbols (globalenv p).
Proof.
  unfold globalenv. unfold globalenv_initmem.
  generalize (add_functs_transf p.(prog_funct) prog_funct_transf_OK).
  intros [X [Y Z]].
  generalize transf_OK.
  unfold transform_partial_program.
  case (transf_partial_program transf (prog_funct p)).
  intros. injection transf_OK0; intro; subst p'; simpl.
  symmetry. apply symbols_add_globals_transf.
  symmetry. exact Y. 
  intros; discriminate.
Qed.

Theorem find_symbol_transf_partial:
  forall (s: ident),
  find_symbol (globalenv p') s = find_symbol (globalenv p) s.
Proof.
  intros. unfold find_symbol. 
  rewrite symbols_init_transf. auto.
Qed.

Theorem init_mem_transf_partial:
  init_mem p' = init_mem p.
Proof.
  unfold init_mem. unfold globalenv_initmem. 
  generalize transf_OK.
  unfold transform_partial_program.
  case (transf_partial_program transf (prog_funct p)).
  intros. injection transf_OK0; intro; subst p'; simpl.
  symmetry. apply mem_add_globals_transf. 
  intros; discriminate.
Qed.

End TRANSF_PROGRAM_PARTIAL.

Section TRANSF_PROGRAM.

Variable A B: Set.
Variable transf: A -> B.
Variable p: program A.
Let tp := transform_program transf p.

Definition transf_partial (x: A) : option B := Some (transf x).

Lemma transf_program_transf_partial_program:
  forall (fns: list (ident * A)),
  transf_partial_program transf_partial fns =
  Some (transf_program transf fns).
Proof.
  induction fns; simpl.
   reflexivity.
   destruct a. rewrite IHfns. reflexivity.
Qed.

Lemma transform_program_transform_partial_program:
  transform_partial_program transf_partial p = Some tp.
Proof.
  unfold tp. unfold transform_partial_program, transform_program.
  rewrite transf_program_transf_partial_program.
  reflexivity.
Qed.

Theorem find_funct_ptr_transf:
  forall (b: block) (f: A),
  find_funct_ptr (globalenv p) b = Some f ->
  find_funct_ptr (globalenv tp) b = Some (transf f).
Proof.
  intros.
  generalize (find_funct_ptr_transf_partial transf_partial p
                  transform_program_transform_partial_program).
  intros. elim (H0 b f H). intros. exact H1.
Qed.

Theorem find_funct_transf:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  find_funct (globalenv tp) v = Some (transf f).
Proof.
  intros.
  generalize (find_funct_transf_partial transf_partial p
                  transform_program_transform_partial_program).
  intros. elim (H0 v f H). intros. exact H1.
Qed.

Theorem find_symbol_transf:
  forall (s: ident),
  find_symbol (globalenv tp) s = find_symbol (globalenv p) s.
Proof.
  intros.
  apply find_symbol_transf_partial with transf_partial.
  apply transform_program_transform_partial_program.
Qed.

Theorem init_mem_transf:
  init_mem tp = init_mem p.
Proof.
  apply init_mem_transf_partial with transf_partial.
  apply transform_program_transform_partial_program.
Qed.

End TRANSF_PROGRAM.

End Genv.
