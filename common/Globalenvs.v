(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*  with contributions from Andrew Tolmach (Portland State University) *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

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

Require Recdef.
Require Import Zwf.
Require Import Axioms.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.

Local Open Scope pair_scope.
Local Open Scope error_monad_scope.

Set Implicit Arguments.

Module Genv.

(** * Global environments *)

Section GENV.

Variable F: Type.  (**r The type of function descriptions *)
Variable V: Type.  (**r The type of information attached to variables *)

(** The type of global environments. *)

Record t: Type := mkgenv {
  genv_symb: PTree.t block;             (**r mapping symbol -> block *)
  genv_funs: ZMap.t (option F);         (**r mapping function pointer -> definition *)
  genv_vars: ZMap.t (option (globvar V)); (**r mapping variable pointer -> info *)
  genv_nextfun: block;                  (**r next function pointer *)
  genv_nextvar: block;                  (**r next variable pointer *)
  genv_nextfun_neg: genv_nextfun < 0;
  genv_nextvar_pos: genv_nextvar > 0;
  genv_symb_range: forall id b, PTree.get id genv_symb = Some b -> b <> 0 /\ genv_nextfun < b /\ b < genv_nextvar;
  genv_funs_range: forall b f, ZMap.get b genv_funs = Some f -> genv_nextfun < b < 0;
  genv_vars_range: forall b v, ZMap.get b genv_vars = Some v -> 0 < b < genv_nextvar;
  genv_vars_inj: forall id1 id2 b, 
    PTree.get id1 genv_symb = Some b -> PTree.get id2 genv_symb = Some b -> id1 = id2
}.

(** ** Lookup functions *)

(** [find_symbol ge id] returns the block associated with the given name, if any *)

Definition find_symbol (ge: t) (id: ident) : option block :=
  PTree.get id ge.(genv_symb).

(** [find_funct_ptr ge b] returns the function description associated with
    the given address. *)

Definition find_funct_ptr (ge: t) (b: block) : option F :=
  ZMap.get b ge.(genv_funs).

(** [find_funct] is similar to [find_funct_ptr], but the function address
    is given as a value, which must be a pointer with offset 0. *)

Definition find_funct (ge: t) (v: val) : option F :=
  match v with
  | Vptr b ofs => if Int.eq_dec ofs Int.zero then find_funct_ptr ge b else None
  | _ => None
  end.

(** [invert_symbol ge b] returns the name associated with the given block, if any *)

Definition invert_symbol (ge: t) (b: block) : option ident :=
  PTree.fold
    (fun res id b' => if eq_block b b' then Some id else res)
    ge.(genv_symb) None.

(** [find_var_info ge b] returns the information attached to the variable
   at address [b]. *)

Definition find_var_info (ge: t) (b: block) : option (globvar V) :=
  ZMap.get b ge.(genv_vars).

(** ** Constructing the global environment *)

Program Definition add_function (ge: t) (idf: ident * F) : t :=
  @mkgenv
    (PTree.set idf#1 ge.(genv_nextfun) ge.(genv_symb))
    (ZMap.set ge.(genv_nextfun) (Some idf#2) ge.(genv_funs))
    ge.(genv_vars)
    (ge.(genv_nextfun) - 1)
    ge.(genv_nextvar)
    _ _ _ _ _ _.
Next Obligation.
  destruct ge; simpl; omega.
Qed.
Next Obligation.
  destruct ge; auto.
Qed.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H. destruct (peq id i). inv H. unfold block; omega.
  exploit genv_symb_range0; eauto. unfold block; omega.
Qed.
Next Obligation.
  destruct ge; simpl in *. rewrite ZMap.gsspec in H. 
  destruct (ZIndexed.eq b genv_nextfun0). subst; omega. 
  exploit genv_funs_range0; eauto. omega.
Qed.
Next Obligation.
  destruct ge; eauto. 
Qed.
Next Obligation.
  destruct ge; simpl in *. 
  rewrite PTree.gsspec in H. rewrite PTree.gsspec in H0. 
  destruct (peq id1 i); destruct (peq id2 i).
  congruence.
  exploit genv_symb_range0; eauto. intros [A B]. inv H. omegaContradiction.
  exploit genv_symb_range0; eauto. intros [A B]. inv H0. omegaContradiction.
  eauto.
Qed.

Program Definition add_variable (ge: t) (idv: ident * globvar V) : t :=
  @mkgenv
    (PTree.set idv#1 ge.(genv_nextvar) ge.(genv_symb))
    ge.(genv_funs)
    (ZMap.set ge.(genv_nextvar) (Some idv#2) ge.(genv_vars))
    ge.(genv_nextfun)
    (ge.(genv_nextvar) + 1)
    _ _ _ _ _ _.
Next Obligation.
  destruct ge; auto.
Qed.
Next Obligation.
  destruct ge; simpl; omega.
Qed.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H. destruct (peq id i). inv H. unfold block; omega.
  exploit genv_symb_range0; eauto. unfold block; omega.
Qed.
Next Obligation.
  destruct ge; eauto. 
Qed.
Next Obligation.
  destruct ge; simpl in *. rewrite ZMap.gsspec in H. 
  destruct (ZIndexed.eq b genv_nextvar0). subst; omega. 
  exploit genv_vars_range0; eauto. omega.
Qed.
Next Obligation.
  destruct ge; simpl in *. 
  rewrite PTree.gsspec in H. rewrite PTree.gsspec in H0. 
  destruct (peq id1 i); destruct (peq id2 i).
  congruence.
  exploit genv_symb_range0; eauto. intros [A B]. inv H. omegaContradiction.
  exploit genv_symb_range0; eauto. intros [A B]. inv H0. omegaContradiction.
  eauto.
Qed.

Program Definition empty_genv : t :=
  @mkgenv (PTree.empty block) (ZMap.init None) (ZMap.init None) (-1) 1 _ _ _ _ _ _.
Next Obligation.
  omega.
Qed.
Next Obligation.
  omega.
Qed.
Next Obligation.
  rewrite PTree.gempty in H. discriminate.
Qed.
Next Obligation.
  rewrite ZMap.gi in H. discriminate.
Qed.
Next Obligation.
  rewrite ZMap.gi in H. discriminate.
Qed.
Next Obligation.
  rewrite PTree.gempty in H. discriminate.
Qed.

Definition add_functions (ge: t) (fl: list (ident * F)) : t :=
  List.fold_left add_function fl ge.

Lemma add_functions_app : forall ge fl1 fl2,
  add_functions ge (fl1 ++ fl2) = add_functions (add_functions ge fl1) fl2.
Proof. 
  intros. unfold add_functions. rewrite fold_left_app. auto.
Qed.


Definition add_variables (ge: t) (vl: list (ident * globvar V)) : t :=
  List.fold_left add_variable vl ge.

Lemma add_variables_app : forall ge vl1 vl2 ,
  add_variables ge (vl1 ++ vl2) = add_variables (add_variables ge vl1) vl2.
Proof. 
  intros. unfold add_variables. rewrite fold_left_app. auto.
Qed.

Definition globalenv (p: program F V) :=
  add_variables (add_functions empty_genv p.(prog_funct)) p.(prog_vars).

(** ** Properties of the operations over global environments *)

Theorem find_funct_inv:
  forall ge v f,
  find_funct ge v = Some f -> exists b, v = Vptr b Int.zero.
Proof.
  intros until f; unfold find_funct. 
  destruct v; try congruence. 
  destruct (Int.eq_dec i Int.zero); try congruence.
  intros. exists b; congruence.
Qed.

Theorem find_funct_find_funct_ptr:
  forall ge b,
  find_funct ge (Vptr b Int.zero) = find_funct_ptr ge b.
Proof.
  intros; simpl. apply dec_eq_true.
Qed.

Theorem find_symbol_exists:
  forall p id gv,
  In (id, gv) (prog_vars p) ->
  exists b, find_symbol (globalenv p) id = Some b.
Proof.
  intros until gv.
  assert (forall vl ge,
          (exists b, find_symbol ge id = Some b) ->
          exists b, find_symbol (add_variables ge vl) id = Some b).
  unfold find_symbol; induction vl; simpl; intros. auto. apply IHvl.
  simpl. rewrite PTree.gsspec. fold ident. destruct (peq id a#1).
  exists (genv_nextvar ge); auto. auto.

  assert (forall vl ge, In (id, gv) vl ->
          exists b, find_symbol (add_variables ge vl) id = Some b).
  unfold find_symbol; induction vl; simpl; intros. contradiction.
  destruct H0. apply H. subst; unfold find_symbol; simpl.
  rewrite PTree.gss. exists (genv_nextvar ge); auto.
  eauto.

  intros. unfold globalenv; eauto. 
Qed.

Theorem find_var_exists:
  forall p id gv,
  list_norepet (prog_var_names p) ->
  In (id, gv) (prog_vars p) ->
  exists b,
     find_symbol (globalenv p) id = Some b
  /\ find_var_info (globalenv p) b = Some gv.
Proof.
  intros until gv.
  assert (forall vl ge,
    ~In id (var_names vl) ->
    (exists b, find_symbol ge id = Some b /\ find_var_info ge b = Some gv) ->
    (exists b, find_symbol (add_variables ge vl) id = Some b
           /\  find_var_info (add_variables ge vl) b = Some gv)).
  induction vl; simpl; intros.
  auto.
  apply IHvl. tauto. destruct a as [id1 gv1]. destruct H0 as [b [P Q]].
  unfold add_variable, find_symbol, find_var_info; simpl. 
  exists b; split. rewrite PTree.gso. auto. intuition. 
  rewrite ZMap.gso. auto. exploit genv_vars_range; eauto.
  unfold ZIndexed.t; omega.

  unfold globalenv, prog_var_names.
  generalize (prog_vars p) (add_functions empty_genv (prog_funct p)).
  induction l; simpl; intros.
  contradiction.
  destruct a as [id1 gv1]; simpl in *. inv H0.
  destruct H1. inv H0.
  apply H; auto.
  exists (genv_nextvar t0); split.
  unfold find_symbol, add_variable; simpl. apply PTree.gss.
  unfold find_var_info, add_variable; simpl. apply ZMap.gss.
  apply IHl; auto. 
Qed.  

Remark add_variables_inversion : forall vs e x b,
  find_symbol (add_variables e vs) x = Some b ->
  In x (var_names vs) \/ find_symbol e x = Some b. 
Proof.
  induction vs; intros. 
    simpl in H.  intuition.
    simpl in H. destruct (IHvs _ _ _ H).
       left. simpl. intuition.
       destruct a as [y ?]. 
       unfold add_variable, find_symbol in H0. simpl in H0. 
       rewrite PTree.gsspec in H0. destruct (peq x y); subst; simpl; intuition.
Qed.

Remark add_functions_inversion : forall fs e x b,
  find_symbol (add_functions e fs) x = Some b -> 
  In x (funct_names fs) \/ find_symbol e x = Some b. 
Proof.
  induction fs; intros. 
    simpl in H.  intuition.
    simpl in H. destruct (IHfs _ _ _ H).
       left. simpl. intuition.
       destruct a as [y ?]. 
       unfold add_variable, find_symbol in H0. simpl in H0. 
       rewrite PTree.gsspec in H0. destruct (peq x y); subst; simpl; intuition.
Qed.

Lemma find_symbol_inversion : forall p x b,
  find_symbol (globalenv p) x = Some b ->
  In x (prog_var_names p ++ prog_funct_names p). 
Proof.
 unfold prog_var_names, prog_funct_names, globalenv. 
 intros.
 apply in_app.
 apply add_variables_inversion in H. intuition.
 apply add_functions_inversion in H0. inversion H0. intuition. 
 unfold find_symbol in H. 
 rewrite PTree.gempty in H. inversion H.
Qed.
 

Remark add_functions_same_symb:
  forall id fl ge, 
  ~In id (funct_names fl) ->
  find_symbol (add_functions ge fl) id = find_symbol ge id.
Proof.
  induction fl; simpl; intros. auto. 
  rewrite IHfl. unfold find_symbol; simpl. apply PTree.gso. intuition. intuition.
Qed.

Remark add_functions_same_address:
  forall b fl ge,
  b > ge.(genv_nextfun) ->
  find_funct_ptr (add_functions ge fl) b = find_funct_ptr ge b.
Proof.
  induction fl; simpl; intros. auto. 
  rewrite IHfl. unfold find_funct_ptr; simpl. apply ZMap.gso. 
  red; intros; subst b; omegaContradiction.
  simpl. omega. 
Qed.

Remark add_variables_same_symb:
  forall id vl ge, 
  ~In id (var_names vl) -> 
  find_symbol (add_variables ge vl) id = find_symbol ge id.
Proof.
  induction vl; simpl; intros. auto. 
  rewrite IHvl. unfold find_symbol; simpl. apply PTree.gso. intuition. intuition.
Qed.

Remark add_variables_same_address:
  forall b vl ge,
  b < ge.(genv_nextvar) ->
  find_var_info (add_variables ge vl) b = find_var_info ge b.
Proof.
  induction vl; simpl; intros. auto. 
  rewrite IHvl. unfold find_var_info; simpl. apply ZMap.gso. 
  red; intros; subst b; omegaContradiction.
  simpl. omega. 
Qed.

Remark add_variables_same_funs:
  forall b vl ge, find_funct_ptr (add_variables ge vl) b = find_funct_ptr ge b.
Proof.
  induction vl; simpl; intros. auto. rewrite IHvl. auto.
Qed.

Remark add_functions_nextvar:
  forall fl ge, genv_nextvar (add_functions ge fl) = genv_nextvar ge.
Proof.
  induction fl; simpl; intros. auto. rewrite IHfl. auto. 
Qed.

Remark add_variables_nextvar:
  forall vl ge, genv_nextvar (add_variables ge vl) = genv_nextvar ge + Z_of_nat(List.length vl).
Proof.
  induction vl; intros.
  simpl. unfold block; omega.
  simpl length; rewrite inj_S; simpl. rewrite IHvl. simpl. unfold block; omega.
Qed.

Theorem find_funct_ptr_exists:
  forall p id f,
  list_norepet (prog_funct_names p) ->
  list_disjoint (prog_funct_names p) (prog_var_names p) ->
  In (id, f) (prog_funct p) ->
  exists b, find_symbol (globalenv p) id = Some b
         /\ find_funct_ptr (globalenv p) b = Some f.
Proof.
  intros until f.

  assert (forall fl ge, In (id, f) fl -> list_norepet (funct_names fl) ->
          exists b, find_symbol (add_functions ge fl) id = Some b
                 /\ find_funct_ptr (add_functions ge fl) b = Some f).
  induction fl; simpl; intros. contradiction. inv H0. 
  destruct H. subst a. exists (genv_nextfun ge); split.
  rewrite add_functions_same_symb; auto. unfold find_symbol; simpl. apply PTree.gss.
  rewrite add_functions_same_address. unfold find_funct_ptr; simpl. apply ZMap.gss. 
  simpl; omega.
  apply IHfl; auto. 

  intros. exploit (H p.(prog_funct) empty_genv); eauto. intros [b [A B]].
  unfold globalenv; exists b; split.
  rewrite add_variables_same_symb. auto. eapply list_disjoint_notin; eauto. 
  unfold prog_funct_names. change id with (fst (id, f)). apply in_map; auto. 
  rewrite add_variables_same_funs. auto.
Qed.

Theorem find_funct_ptr_prop:
  forall (P: F -> Prop) p b f,
  (forall id f, In (id, f) (prog_funct p) -> P f) ->
  find_funct_ptr (globalenv p) b = Some f ->
  P f.
Proof.
  intros until f. intros PROP.
  assert (forall fl ge,
          List.incl fl (prog_funct p) ->
          match find_funct_ptr ge b with None => True | Some f => P f end ->
          match find_funct_ptr (add_functions ge fl) b with None => True | Some f => P f end).
  induction fl; simpl; intros. auto.
  apply IHfl. eauto with coqlib. unfold find_funct_ptr; simpl.
  destruct a as [id' f']; simpl. 
  rewrite ZMap.gsspec. destruct (ZIndexed.eq b (genv_nextfun ge)). 
  apply PROP with id'. apply H. auto with coqlib. 
  assumption.

  unfold globalenv. rewrite add_variables_same_funs. intro. 
  exploit (H p.(prog_funct) empty_genv). auto with coqlib. 
  unfold find_funct_ptr; simpl. rewrite ZMap.gi. auto.
  rewrite H0. auto.
Qed.

Theorem find_funct_prop:
  forall (P: F -> Prop) p v f,
  (forall id f, In (id, f) (prog_funct p) -> P f) ->
  find_funct (globalenv p) v = Some f ->
  P f.
Proof.
  intros. exploit find_funct_inv; eauto. intros [b EQ]. subst v. 
  rewrite find_funct_find_funct_ptr in H0. 
  eapply find_funct_ptr_prop; eauto.
Qed.

Theorem find_funct_ptr_inversion:
  forall p b f,
  find_funct_ptr (globalenv p) b = Some f ->
  exists id, In (id, f) (prog_funct p).
Proof.
  intros. pattern f. apply find_funct_ptr_prop with p b; auto.
  intros. exists id; auto.
Qed.

Theorem find_funct_inversion:
  forall p v f,
  find_funct (globalenv p) v = Some f ->
  exists id, In (id, f) (prog_funct p).
Proof.
  intros. pattern f. apply find_funct_prop with p v; auto.
  intros. exists id; auto.
Qed.

Theorem find_funct_ptr_negative:
  forall p b f,
  find_funct_ptr (globalenv p) b = Some f -> b < 0.
Proof.
  unfold find_funct_ptr. intros. destruct (globalenv p). simpl in H. 
  exploit genv_funs_range0; eauto. omega. 
Qed.

Theorem find_var_info_positive:
  forall p b v,
  find_var_info (globalenv p) b = Some v -> b > 0.
Proof.
  unfold find_var_info. intros. destruct (globalenv p). simpl in H. 
  exploit genv_vars_range0; eauto. omega. 
Qed.

Remark add_variables_symb_neg:
  forall id b vl ge,
  find_symbol (add_variables ge vl) id = Some b -> b < 0 ->
  find_symbol ge id = Some b.
Proof.
  induction vl; simpl; intros. auto.
  exploit IHvl; eauto. unfold find_symbol; simpl. rewrite PTree.gsspec. 
  fold ident. destruct (peq id (a#1)); auto. intros. inv H1. 
  generalize (genv_nextvar_pos ge). intros. omegaContradiction.
Qed.

Theorem find_funct_ptr_symbol_inversion:
  forall p id b f,
  find_symbol (globalenv p) id = Some b ->
  find_funct_ptr (globalenv p) b = Some f ->
  In (id, f) p.(prog_funct).
Proof.
  intros until f.

  assert (forall fl ge,
          find_symbol (add_functions ge fl) id = Some b ->
          find_funct_ptr (add_functions ge fl) b = Some f ->
          In (id, f) fl \/ (find_symbol ge id = Some b /\ find_funct_ptr ge b = Some f)).
  induction fl; simpl; intros.
  auto.
  exploit IHfl; eauto. intros [A | [A B]]. auto.
  destruct a as [id' f'].
  unfold find_symbol in A; simpl in A.
  unfold find_funct_ptr in B; simpl in B.
  rewrite PTree.gsspec in A. destruct (peq id id'). inv A. 
  rewrite ZMap.gss in B. inv B. auto.
  rewrite ZMap.gso in B. right; auto. 
  exploit genv_symb_range; eauto. unfold block, ZIndexed.t; omega.

  intros. assert (b < 0) by (eapply find_funct_ptr_negative; eauto). 
  unfold globalenv in *. rewrite add_variables_same_funs in H1.
  exploit (H (prog_funct p) empty_genv). 
  eapply add_variables_symb_neg; eauto. auto. 
  intuition. unfold find_symbol in H3; simpl in H3. rewrite PTree.gempty in H3. discriminate.
Qed.

Theorem find_symbol_not_nullptr:
  forall p id b,
  find_symbol (globalenv p) id = Some b -> b <> Mem.nullptr.
Proof.
  intros until b. unfold find_symbol. destruct (globalenv p); simpl. 
  intros. exploit genv_symb_range0; eauto. intuition.
Qed.

Theorem global_addresses_distinct:
  forall ge id1 id2 b1 b2,
  id1 <> id2 ->
  find_symbol ge id1 = Some b1 ->
  find_symbol ge id2 = Some b2 ->
  b1 <> b2.
Proof.
  intros. red; intros; subst. elim H. destruct ge. eauto. 
Qed.

Theorem invert_find_symbol:
  forall ge id b,
  invert_symbol ge b = Some id -> find_symbol ge id = Some b.
Proof.
  intros until b; unfold find_symbol, invert_symbol.
  apply PTree_Properties.fold_rec.
  intros. rewrite H in H0; auto. 
  congruence.
  intros. destruct (eq_block b v). inv H2. apply PTree.gss. 
  rewrite PTree.gsspec. destruct (peq id k).
  subst. assert (m!k = Some b) by auto. congruence.
  auto.
Qed.

Theorem find_invert_symbol:
  forall ge id b,
  find_symbol ge id = Some b -> invert_symbol ge b = Some id.
Proof.
  intros until b.
  assert (find_symbol ge id = Some b -> exists id', invert_symbol ge b = Some id').
  unfold find_symbol, invert_symbol.
  apply PTree_Properties.fold_rec.
  intros. rewrite H in H0; auto.
  rewrite PTree.gempty; congruence.
  intros. destruct (eq_block b v). exists k; auto.
  rewrite PTree.gsspec in H2. destruct (peq id k).
  inv H2. congruence. auto. 

  intros; exploit H; eauto. intros [id' A]. 
  assert (id = id'). eapply genv_vars_inj; eauto. apply invert_find_symbol; auto.
  congruence.
Qed.

(** * Construction of the initial memory state *)

Section INITMEM.

Variable ge: t.

Definition init_data_size (i: init_data) : Z :=
  match i with
  | Init_int8 _ => 1
  | Init_int16 _ => 2
  | Init_int32 _ => 4
  | Init_float32 _ => 4
  | Init_float64 _ => 8
  | Init_addrof _ _ => 4
  | Init_space n => Zmax n 0
  end.

Lemma init_data_size_pos:
  forall i, init_data_size i >= 0.
Proof.
  destruct i; simpl; try omega. generalize (Zle_max_r z 0). omega.
Qed.

Definition store_init_data (m: mem) (b: block) (p: Z) (id: init_data) : option mem :=
  match id with
  | Init_int8 n => Mem.store Mint8unsigned m b p (Vint n)
  | Init_int16 n => Mem.store Mint16unsigned m b p (Vint n)
  | Init_int32 n => Mem.store Mint32 m b p (Vint n)
  | Init_float32 n => Mem.store Mfloat32 m b p (Vfloat n)
  | Init_float64 n => Mem.store Mfloat64 m b p (Vfloat n)
  | Init_addrof symb ofs =>
      match find_symbol ge symb with
      | None => None
      | Some b' => Mem.store Mint32 m b p (Vptr b' ofs)
      end
  | Init_space n => Some m
  end.

Fixpoint store_init_data_list (m: mem) (b: block) (p: Z) (idl: list init_data)
                              {struct idl}: option mem :=
  match idl with
  | nil => Some m
  | id :: idl' =>
      match store_init_data m b p id with
      | None => None
      | Some m' => store_init_data_list m' b (p + init_data_size id) idl'
      end
  end.

Function store_zeros (m: mem) (b: block) (n: Z) {wf (Zwf 0) n}: option mem :=
  if zle n 0 then Some m else
    let n' := n - 1 in
    match Mem.store Mint8unsigned m b n' Vzero with
    | Some m' => store_zeros m' b n'
    | None => None
    end.
Proof.
  intros. red. omega.
  apply Zwf_well_founded.
Qed.

Fixpoint init_data_list_size (il: list init_data) {struct il} : Z :=
  match il with
  | nil => 0
  | i :: il' => init_data_size i + init_data_list_size il'
  end.

Definition perm_globvar (gv: globvar V) : permission :=
  if gv.(gvar_volatile) then Nonempty
  else if gv.(gvar_readonly) then Readable
  else Writable.

Definition alloc_variable (m: mem) (idv: ident * globvar V) : option mem :=
  let init := idv#2.(gvar_init) in
  let sz := init_data_list_size init in
  let (m1, b) := Mem.alloc m 0 sz in
  match store_zeros m1 b sz with
  | None => None
  | Some m2 =>
      match store_init_data_list m2 b 0 init with
      | None => None
      | Some m3 => Mem.drop_perm m3 b 0 sz (perm_globvar idv#2)
      end
  end.

Fixpoint alloc_variables (m: mem) (vl: list (ident * globvar V))
                         {struct vl} : option mem :=
  match vl with
  | nil => Some m
  | v :: vl' =>
      match alloc_variable m v with
      | None => None
      | Some m' => alloc_variables m' vl'
      end
  end.

Lemma alloc_variables_app : forall vl1 vl2 m m1,
  alloc_variables m vl1 = Some m1 ->
  alloc_variables m1 vl2 = alloc_variables m (vl1 ++ vl2).
Proof.
  induction vl1.
    simpl. intros.  inversion H; subst. auto.
    simpl. intros. destruct (alloc_variable m a); eauto. inversion H.
Qed.

Remark store_init_data_list_nextblock:
  forall idl b m p m',
  store_init_data_list m b p idl = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction idl; simpl; intros until m'.
  intros. congruence.
  caseEq (store_init_data m b p a); try congruence. intros. 
  transitivity (Mem.nextblock m0). eauto. 
  destruct a; simpl in H; try (eapply Mem.nextblock_store; eauto; fail).
  congruence. 
  destruct (find_symbol ge i); try congruence. eapply Mem.nextblock_store; eauto. 
Qed.

Remark store_zeros_nextblock:
  forall m b n m', store_zeros m b n = Some m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  intros until n. functional induction (store_zeros m b n); intros.
  inv H; auto.
  rewrite IHo; eauto with mem.
  congruence.
Qed.

Remark alloc_variable_nextblock:
  forall v m m',
  alloc_variable m v = Some m' ->
  Mem.nextblock m' = Zsucc(Mem.nextblock m).
Proof.
  unfold alloc_variable.
  intros until m'.   
  set (init := gvar_init v#2).
  set (sz := init_data_list_size init).
  caseEq (Mem.alloc m 0 sz). intros m1 b ALLOC.
  caseEq (store_zeros m1 b sz); try congruence. intros m2 STZ.
  caseEq (store_init_data_list m2 b 0 init); try congruence. intros m3 STORE.
  caseEq (Mem.drop_perm m3 b 0 sz (perm_globvar v#2)); try congruence. intros m4 DROP REC. 
  inv REC; subst.
  rewrite (Mem.nextblock_drop _ _ _ _ _ _ DROP). 
  rewrite (store_init_data_list_nextblock _ _ _ _ STORE).
  rewrite (store_zeros_nextblock _ _ _ STZ). 
  rewrite (Mem.nextblock_alloc _ _ _ _ _ ALLOC). 
  auto.
Qed.


Remark alloc_variables_nextblock:
  forall vl m m',
  alloc_variables m vl = Some m' ->
  Mem.nextblock m' = Mem.nextblock m + Z_of_nat(List.length vl).
Proof.
  induction vl.
  simpl; intros. inv H; unfold block; omega.
  simpl length; rewrite inj_S; simpl. intros m m'. 
  unfold alloc_variable. 
  set (init := gvar_init a#2).
  set (sz := init_data_list_size init).
  caseEq (Mem.alloc m 0 sz). intros m1 b ALLOC.
  caseEq (store_zeros m1 b sz); try congruence. intros m2 STZ.
  caseEq (store_init_data_list m2 b 0 init); try congruence. intros m3 STORE.
  caseEq (Mem.drop_perm m3 b 0 sz (perm_globvar a#2)); try congruence. intros m4 DROP REC.
  rewrite (IHvl _ _ REC).
  rewrite (Mem.nextblock_drop _ _ _ _ _ _ DROP). 
  rewrite (store_init_data_list_nextblock _ _ _ _ STORE).
  rewrite (store_zeros_nextblock _ _ _ STZ).
  rewrite (Mem.nextblock_alloc _ _ _ _ _ ALLOC).
  unfold block in *; omega.
Qed.


Remark store_zeros_perm:
  forall k prm b' q m b n m',
  store_zeros m b n = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  intros until n. functional induction (store_zeros m b n); intros.
  inv H; tauto.
  destruct (IHo _ H); intros. split; eauto with mem.
  congruence.
Qed.

Remark store_init_data_list_perm:
  forall k prm b' q idl b m p m',
  store_init_data_list m b p idl = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  induction idl; simpl; intros until m'.
  intros. inv H. tauto. 
  caseEq (store_init_data m b p a); try congruence. intros.
  rewrite <- (IHidl _ _ _ _ H0).
  destruct a; simpl in H; split; eauto with mem.
  inv H; auto. inv H; auto. 
  destruct (find_symbol ge i); try congruence. eauto with mem.
  destruct (find_symbol ge i); try congruence. eauto with mem.
Qed.

Remark alloc_variables_perm:
  forall k prm b' q vl m m',
  alloc_variables m vl = Some m' ->
  Mem.valid_block m b' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  induction vl.
  simpl; intros. inv H. tauto. 
  intros until m'. simpl. unfold alloc_variable. 
  set (init := gvar_init a#2).
  set (sz := init_data_list_size init).
  caseEq (Mem.alloc m 0 sz). intros m1 b ALLOC.
  caseEq (store_zeros m1 b sz); try congruence. intros m2 STZ.
  caseEq (store_init_data_list m2 b 0 init); try congruence. intros m3 STORE.
  caseEq (Mem.drop_perm m3 b 0 sz (perm_globvar a#2)); try congruence. intros m4 DROP REC VALID.
  assert (b' <> b). apply Mem.valid_not_valid_diff with m; eauto with mem.
  assert (VALID': Mem.valid_block m4 b').
    unfold Mem.valid_block. rewrite (Mem.nextblock_drop _ _ _ _ _ _ DROP).
    rewrite (store_init_data_list_nextblock _ _ _ _ STORE).  
    rewrite (store_zeros_nextblock _ _ _ STZ).  
    change (Mem.valid_block m1 b'). eauto with mem.
  rewrite <- (IHvl _ _ REC VALID').
  split; intros.
  eapply Mem.perm_drop_3; eauto.
  rewrite <- store_init_data_list_perm; [idtac|eauto].
  rewrite <- store_zeros_perm; [idtac|eauto].
  eauto with mem.
  assert (Mem.perm m1 b' q k prm).
    rewrite store_zeros_perm; [idtac|eauto].
    rewrite store_init_data_list_perm; [idtac|eauto].
    eapply Mem.perm_drop_4; eauto.
  exploit Mem.perm_alloc_inv; eauto. rewrite zeq_false; auto.
Qed.

Remark store_zeros_outside:
  forall m b n m',
  store_zeros m b n = Some m' ->
  forall chunk b' p,
  b' <> b -> Mem.load chunk m' b' p = Mem.load chunk m b' p.
Proof.
  intros until n. functional induction (store_zeros m b n); intros.
  inv H; auto.
  rewrite IHo; auto. eapply Mem.load_store_other; eauto. 
  inv H.
Qed.

Remark store_init_data_list_outside:
  forall b il m p m',
  store_init_data_list m b p il = Some m' ->
  forall chunk b' q,
  b' <> b \/ q + size_chunk chunk <= p ->
  Mem.load chunk m' b' q = Mem.load chunk m b' q.
Proof.
  induction il; simpl.
  intros; congruence.
  intros until m'. caseEq (store_init_data m b p a); try congruence. 
  intros m1 A B chunk b' q C. transitivity (Mem.load chunk m1 b' q).
  eapply IHil; eauto. generalize (init_data_size_pos a). intuition omega.
  destruct a; simpl in A;
  try (eapply Mem.load_store_other; eauto; intuition; fail).
  congruence.
  destruct (find_symbol ge i); try congruence. 
  eapply Mem.load_store_other; eauto; intuition.
Qed.

Fixpoint load_store_init_data (m: mem) (b: block) (p: Z) (il: list init_data) {struct il} : Prop :=
  match il with
  | nil => True
  | Init_int8 n :: il' =>
      Mem.load Mint8unsigned m b p = Some(Vint(Int.zero_ext 8 n))
      /\ load_store_init_data m b (p + 1) il'
  | Init_int16 n :: il' =>
      Mem.load Mint16unsigned m b p = Some(Vint(Int.zero_ext 16 n))
      /\ load_store_init_data m b (p + 2) il'
  | Init_int32 n :: il' =>
      Mem.load Mint32 m b p = Some(Vint n)
      /\ load_store_init_data m b (p + 4) il'
  | Init_float32 n :: il' =>
      Mem.load Mfloat32 m b p = Some(Vfloat(Float.singleoffloat n))
      /\ load_store_init_data m b (p + 4) il'
  | Init_float64 n :: il' =>
      Mem.load Mfloat64 m b p = Some(Vfloat n)
      /\ load_store_init_data m b (p + 8) il'
  | Init_addrof symb ofs :: il' =>
      (exists b', find_symbol ge symb = Some b' /\ Mem.load Mint32 m b p = Some(Vptr b' ofs))
      /\ load_store_init_data m b (p + 4) il'
  | Init_space n :: il' =>
      load_store_init_data m b (p + Zmax n 0) il'
  end.

Lemma store_init_data_list_charact:
  forall b il m p m',
  store_init_data_list m b p il = Some m' ->
  load_store_init_data m' b p il.
Proof.
  assert (A: forall chunk v m b p m1 il m',
    Mem.store chunk m b p v = Some m1 ->
    store_init_data_list m1 b (p + size_chunk chunk) il = Some m' ->
    Val.has_type v (type_of_chunk chunk) ->
    Mem.load chunk m' b p = Some(Val.load_result chunk v)).
  intros. transitivity (Mem.load chunk m1 b p).
  eapply store_init_data_list_outside; eauto. right. omega. 
  eapply Mem.load_store_same; eauto. 

  induction il; simpl.
  auto.
  intros until m'. caseEq (store_init_data m b p a); try congruence. 
  intros m1 B C.
  exploit IHil; eauto. intro D. 
  destruct a; simpl in B; intuition.
  eapply (A Mint8unsigned (Vint i)); eauto. simpl; auto.
  eapply (A Mint16unsigned (Vint i)); eauto. simpl; auto.
  eapply (A Mint32 (Vint i)); eauto. simpl; auto.
  eapply (A Mfloat32 (Vfloat f)); eauto. simpl; auto.
  eapply (A Mfloat64 (Vfloat f)); eauto. simpl; auto.
  destruct (find_symbol ge i); try congruence. exists b0; split; auto. 
  eapply (A Mint32 (Vptr b0 i0)); eauto. simpl; auto. 
Qed.

Remark load_alloc_variables:
  forall chunk b p vl m m',
  alloc_variables m vl = Some m' ->
  Mem.valid_block m b ->
  Mem.load chunk m' b p = Mem.load chunk m b p.
Proof.
  induction vl; simpl; intros until m'.
  congruence.
  unfold alloc_variable. 
  set (init := gvar_init a#2).
  set (sz := init_data_list_size init).
  caseEq (Mem.alloc m 0 sz). intros m1 b1 ALLOC.
  caseEq (store_zeros m1 b1 sz); try congruence. intros m2 STZ.
  caseEq (store_init_data_list m2 b1 0 init); try congruence. intros m3 STORE.
  caseEq (Mem.drop_perm m3 b1 0 sz (perm_globvar a#2)); try congruence. intros m4 DROP REC VALID.
  assert (b <> b1). apply Mem.valid_not_valid_diff with m; eauto with mem.
  transitivity (Mem.load chunk m4 b p).
  apply IHvl; auto. red.
  rewrite (Mem.nextblock_drop _ _ _ _ _ _ DROP). 
  rewrite (store_init_data_list_nextblock _ _ _ _ STORE).
  rewrite (store_zeros_nextblock _ _ _ STZ).
  change (Mem.valid_block m1 b). eauto with mem.
  transitivity (Mem.load chunk m3 b p). 
  eapply Mem.load_drop; eauto. 
  transitivity (Mem.load chunk m2 b p).
  eapply store_init_data_list_outside; eauto.
  transitivity (Mem.load chunk m1 b p).
  eapply store_zeros_outside; eauto.
  eapply Mem.load_alloc_unchanged; eauto.
Qed. 

Remark load_store_init_data_invariant:
  forall m m' b,
  (forall chunk ofs, Mem.load chunk m' b ofs = Mem.load chunk m b ofs) ->
  forall il p,
  load_store_init_data m b p il -> load_store_init_data m' b p il.
Proof.
  induction il; intro p; simpl.
  auto.
  repeat rewrite H. destruct a; intuition. 
Qed.

Definition variables_initialized (g: t) (m: mem) :=
  forall b gv,
  find_var_info g b = Some gv ->
  Mem.range_perm m b 0 (init_data_list_size gv.(gvar_init)) Cur (perm_globvar gv)
  /\ (forall ofs k p, Mem.perm m b ofs k p ->
        0 <= ofs < init_data_list_size gv.(gvar_init) /\ perm_order (perm_globvar gv) p)
  /\ (gv.(gvar_volatile) = false -> load_store_init_data m b 0 gv.(gvar_init)).

Lemma alloc_variable_initialized:
  forall g m id v m',
  genv_nextvar g = Mem.nextblock m ->
  alloc_variable m (id, v) = Some m' ->
  variables_initialized g m ->
  variables_initialized (add_variable g (id, v)) m'
  /\ genv_nextvar (add_variable g (id,v)) = Mem.nextblock m'.
Proof.
  intros. revert H0. unfold alloc_variable. simpl. 
  set (il := gvar_init v).
  set (sz := init_data_list_size il).
  caseEq (Mem.alloc m 0 sz).   intros m1 b1 ALLOC.
  caseEq (store_zeros m1 b1 sz); try congruence. intros m2 ZEROS.
  caseEq (store_init_data_list m2 b1 0 il); try congruence. intros m3 INIT DROP.
  exploit Mem.nextblock_alloc; eauto.  intros NB1.
  assert (Mem.nextblock m' = Mem.nextblock m1).
    rewrite (Mem.nextblock_drop _ _ _ _ _ _ DROP).
    rewrite (store_init_data_list_nextblock _ _ _ _ INIT).
    eapply store_zeros_nextblock; eauto.
  exploit Mem.alloc_result; eauto. intro RES.
  split.
  (* var-init *)
  red; intros. revert H2.
  unfold add_variable, find_var_info; simpl.
  rewrite H; rewrite <- RES.
  rewrite ZMap.gsspec. destruct (ZIndexed.eq b b1); intros VI.
  (* new var *)
  injection VI; intro EQ. subst b gv. clear VI.
  fold il. fold sz.
  split. red; intros. eapply Mem.perm_drop_1; eauto.
  split. intros. 
    assert (0 <= ofs < sz).
      eapply Mem.perm_alloc_3; eauto. 
      rewrite store_zeros_perm; [idtac|eauto].
      rewrite store_init_data_list_perm; [idtac|eauto].
      eapply Mem.perm_drop_4; eauto.
  split; auto. eapply Mem.perm_drop_2; eauto.
  intros. 
  apply load_store_init_data_invariant with m3.
  intros. eapply Mem.load_drop; eauto. right; right; right.
  unfold perm_globvar. destruct (gvar_volatile v); try discriminate.
  destruct (gvar_readonly v); auto with mem.
  eapply store_init_data_list_charact; eauto.
  (* older vars *)
  exploit H1; eauto. intros [A [B C]].
  split. red; intros. eapply Mem.perm_drop_3; eauto. 
  rewrite <- store_init_data_list_perm; [idtac|eauto].
  rewrite <- store_zeros_perm; [idtac|eauto].
  eapply Mem.perm_alloc_1; eauto.
  split. intros. eapply B. 
  eapply Mem.perm_alloc_4; eauto.   
  rewrite store_zeros_perm; [idtac|eauto].
  rewrite store_init_data_list_perm; [idtac|eauto].
  eapply Mem.perm_drop_4; eauto.
  intros. apply load_store_init_data_invariant with m; auto.
  intros. transitivity (Mem.load chunk m3 b ofs). 
  eapply Mem.load_drop; eauto. 
  transitivity (Mem.load chunk m2 b ofs). 
  eapply store_init_data_list_outside; eauto.
  transitivity (Mem.load chunk m1 b ofs). 
  eapply store_zeros_outside; eauto.
  eapply Mem.load_alloc_unchanged; eauto.
  red. exploit genv_vars_range; eauto. rewrite <- H. omega.
  rewrite H0; rewrite NB1; rewrite H; auto.
Qed.

Lemma alloc_variables_initialized:
  forall vl g m m',
  genv_nextvar g = Mem.nextblock m ->
  alloc_variables m vl = Some m' ->
  variables_initialized g m ->
  variables_initialized (add_variables g vl) m'.
Proof.
  induction vl; simpl; intros.
  inv H0; auto.
  destruct (alloc_variable m a) as [m1|]_eqn; try discriminate.
  destruct a as [id gv].
  exploit alloc_variable_initialized; eauto. intros [P Q].
  eapply IHvl; eauto. 
Qed.

End INITMEM.

Definition init_mem (p: program F V) :=
  alloc_variables (globalenv p) Mem.empty p.(prog_vars).

Theorem find_symbol_not_fresh:
  forall p id b m,
  init_mem p = Some m ->
  find_symbol (globalenv p) id = Some b -> Mem.valid_block m b.
Proof.
  unfold init_mem; intros.
  exploit alloc_variables_nextblock; eauto. rewrite Mem.nextblock_empty. intro.
  exploit genv_symb_range; eauto. intros.
  generalize (add_variables_nextvar (prog_vars p) (add_functions empty_genv (prog_funct p))).
  rewrite add_functions_nextvar. simpl genv_nextvar. intro.
  red. rewrite H1. rewrite <- H3. intuition.
Qed.

Lemma init_mem_genv_vars : forall p m,
    init_mem p = Some m -> 
    genv_nextvar (globalenv p) = Mem.nextblock m.
Proof.
    clear. unfold globalenv, init_mem.  intros.
    exploit alloc_variables_nextblock; eauto.
    simpl (Mem.nextblock Mem.empty). 
    rewrite add_variables_nextvar.  rewrite add_functions_nextvar.
    simpl (genv_nextvar empty_genv).  auto.
Qed.

Theorem find_var_info_not_fresh:
  forall p b gv m,
  init_mem p = Some m ->
  find_var_info (globalenv p) b = Some gv -> Mem.valid_block m b.
Proof.
  unfold init_mem; intros.
  exploit alloc_variables_nextblock; eauto. rewrite Mem.nextblock_empty. intro.
  exploit genv_vars_range; eauto. intros.
  generalize (add_variables_nextvar (prog_vars p) (add_functions empty_genv (prog_funct p))).
  rewrite add_functions_nextvar. simpl genv_nextvar. intro.
  red. rewrite H1. rewrite <- H3. intuition.
Qed.

Theorem init_mem_characterization:
  forall p b gv m,
  find_var_info (globalenv p) b = Some gv ->
  init_mem p = Some m ->
  Mem.range_perm m b 0 (init_data_list_size gv.(gvar_init)) Cur (perm_globvar gv)
  /\ (forall ofs k p, Mem.perm m b ofs k p ->
        0 <= ofs < init_data_list_size gv.(gvar_init) /\ perm_order (perm_globvar gv) p)
  /\ (gv.(gvar_volatile) = false -> load_store_init_data (globalenv p) m b 0 gv.(gvar_init)).
Proof.
  intros. eapply alloc_variables_initialized; eauto. 
  rewrite add_functions_nextvar; auto. 
  red; intros. exploit genv_vars_range; eauto. rewrite add_functions_nextvar. 
  simpl. intros. omegaContradiction.
Qed.

(** ** Compatibility with memory injections *)

Section INITMEM_INJ.

Variable ge: t.
Variable thr: block.
Hypothesis symb_inject: forall id b, find_symbol ge id = Some b -> b < thr.

Lemma store_init_data_neutral:
  forall m b p id m',
  Mem.inject_neutral thr m ->
  b < thr ->
  store_init_data ge m b p id = Some m' ->
  Mem.inject_neutral thr m'.
Proof.
  intros.
  destruct id; simpl in H1; try (eapply Mem.store_inject_neutral; eauto; fail).
  inv H1; auto.
  revert H1. caseEq (find_symbol ge i); try congruence. intros b' FS ST. 
  eapply Mem.store_inject_neutral; eauto. 
  econstructor. unfold Mem.flat_inj. apply zlt_true; eauto. 
  rewrite Int.add_zero. auto. 
Qed.

Lemma store_init_data_list_neutral:
  forall b idl m p m',
  Mem.inject_neutral thr m ->
  b < thr ->
  store_init_data_list ge m b p idl = Some m' ->
  Mem.inject_neutral thr m'.
Proof.
  induction idl; simpl.
  intros; congruence.
  intros until m'; intros INJ FB.
  caseEq (store_init_data ge m b p a); try congruence. intros. 
  eapply IHidl. eapply store_init_data_neutral; eauto. auto. eauto. 
Qed.

Lemma store_zeros_neutral:
  forall m b n m',
  Mem.inject_neutral thr m ->
  b < thr ->
  store_zeros m b n = Some m' ->
  Mem.inject_neutral thr m'.
Proof.
  intros until n. functional induction (store_zeros m b n); intros.
  inv H1; auto.
  apply IHo; auto. eapply Mem.store_inject_neutral; eauto. constructor.  
  inv H1.
Qed.

Lemma alloc_variable_neutral:
  forall id m m',
  alloc_variable ge m id = Some m' ->
  Mem.inject_neutral thr m ->
  Mem.nextblock m < thr ->
  Mem.inject_neutral thr m'.
Proof.
  intros until m'. unfold alloc_variable.
  set (init := gvar_init id#2).
  set (sz := init_data_list_size init).
  caseEq (Mem.alloc m 0 sz); try congruence. intros m1 b ALLOC.
  caseEq (store_zeros m1 b sz); try congruence. intros m2 STZ.
  caseEq (store_init_data_list ge m2 b 0 init); try congruence.
  intros m3 STORE DROP NEUTRAL NEXT.
  assert (b < thr). rewrite (Mem.alloc_result _ _ _ _ _ ALLOC). auto.
  eapply Mem.drop_inject_neutral; eauto. 
  eapply store_init_data_list_neutral with (m := m2) (b := b); eauto.
  eapply store_zeros_neutral with (m := m1); eauto. 
  eapply Mem.alloc_inject_neutral; eauto.
Qed.

Lemma alloc_variables_neutral:
  forall idl m m',
  alloc_variables ge m idl = Some m' ->
  Mem.inject_neutral thr m ->
  Mem.nextblock m' <= thr ->
  Mem.inject_neutral thr m'.
Proof.
  induction idl; simpl.
  intros. congruence.
  intros until m'. caseEq (alloc_variable ge m a); try congruence. intros.
  assert (Mem.nextblock m' = Mem.nextblock m + Z_of_nat(length (a :: idl))).
  eapply alloc_variables_nextblock with ge. simpl. rewrite H. auto. 
  simpl length in H3. rewrite inj_S in H3. 
  exploit alloc_variable_neutral; eauto. unfold block in *; omega.
Qed.

End INITMEM_INJ.

Theorem initmem_inject:
  forall p m,
  init_mem p = Some m ->
  Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m.
Proof.
  unfold init_mem; intros.
  apply Mem.neutral_inject. 
  eapply alloc_variables_neutral; eauto. 
  intros. exploit find_symbol_not_fresh; eauto.
  apply Mem.empty_inject_neutral.
  omega.
Qed.

Section INITMEM_AUGMENT_INJ. 

Variable ge: t.
Variable thr: block.

Lemma store_init_data_augment: 
  forall m1 m2 b p id m2', 
  Mem.inject (Mem.flat_inj thr) m1 m2 -> 
  b >= thr -> 
  store_init_data ge m2 b p id = Some m2' ->
  Mem.inject (Mem.flat_inj thr) m1 m2'.
Proof. 
  intros until m2'. intros INJ BND ST. 
  assert (P: forall chunk ofs v m2', 
             Mem.store chunk m2 b ofs v = Some m2' -> 
             Mem.inject (Mem.flat_inj thr) m1 m2'). 
    intros. eapply Mem.store_outside_inject; eauto. 
    intros. unfold Mem.flat_inj in H0.
    destruct (zlt b' thr); inversion H0; subst. omega. 
  destruct id; simpl in ST; try (eapply P; eauto; fail).
  inv ST; auto. 
  revert ST.  caseEq (find_symbol ge i); try congruence. intros; eapply P; eauto. 
Qed.

Lemma store_init_data_list_augment:
  forall b idl m1 m2 p m2', 
  Mem.inject (Mem.flat_inj thr) m1 m2 -> 
  b >= thr -> 
  store_init_data_list ge m2 b p idl = Some m2' ->
  Mem.inject (Mem.flat_inj thr) m1 m2'.
Proof. 
  induction idl; simpl.
  intros; congruence.
  intros until m2'; intros INJ FB.
  caseEq (store_init_data ge m2 b p a); try congruence. intros. 
  eapply IHidl. eapply store_init_data_augment; eauto. auto. eauto. 
Qed.

Lemma store_zeros_augment:
  forall m1 m2 b n m2',
  Mem.inject (Mem.flat_inj thr) m1 m2 ->
  b >= thr ->
  store_zeros m2 b n = Some m2' ->
  Mem.inject (Mem.flat_inj thr) m1 m2'.
Proof.
  intros until n. functional induction (store_zeros m2 b n); intros.
  inv H1; auto.
  apply IHo; auto. exploit Mem.store_outside_inject; eauto. simpl. 
  intros. exfalso. unfold Mem.flat_inj in H2. destruct (zlt b' thr). 
    inversion H2; subst; omega.  
    discriminate.
  inv H1.
Qed.

Lemma alloc_variable_augment:
  forall id m1 m2 m2',
  alloc_variable ge m2 id = Some m2' ->
  Mem.inject (Mem.flat_inj thr) m1 m2 -> 
  Mem.nextblock m2 >= thr -> 
  Mem.inject (Mem.flat_inj thr) m1 m2'.
Proof.
  intros until m2'. unfold alloc_variable. 
  set (sz := init_data_list_size (gvar_init id#2)).
  caseEq (Mem.alloc m2 0 sz); try congruence. intros m3 b ALLOC.
  caseEq (store_zeros m3 b sz); try congruence. intros m4 STZ.
  caseEq (store_init_data_list ge m4 b 0 (gvar_init id#2)); try congruence.
  intros m5 STORE DROP INJ NEXT.
  assert (b >= thr). 
     pose proof (Mem.fresh_block_alloc _ _ _ _ _ ALLOC).  
     unfold Mem.valid_block in H.  unfold block in *; omega. 
  eapply Mem.drop_outside_inject. 2: eauto.  
  eapply store_init_data_list_augment. 2: eauto. 2: eauto. 
  eapply store_zeros_augment. 2: eauto. 2: eauto.
  eapply Mem.alloc_right_inject; eauto. 
  intros. unfold Mem.flat_inj in H0. destruct (zlt b' thr); inversion H0. 
     subst; exfalso; omega.
Qed.

Lemma alloc_variables_augment:
  forall idl m1 m2 m2',
  alloc_variables ge m2 idl = Some m2' ->
  Mem.inject (Mem.flat_inj thr) m1 m2 ->
  Mem.nextblock m2 >= thr ->
  Mem.inject (Mem.flat_inj thr) m1 m2'.
Proof.
  induction idl; simpl.
  intros. congruence.
  intros until m2'. caseEq (alloc_variable ge m2 a); try congruence. intros.
  eapply IHidl with (m2 := m); eauto.  
    eapply alloc_variable_augment; eauto. 
    rewrite (alloc_variable_nextblock _ _ _ H). 
    unfold block in *; omega. 
Qed.

End INITMEM_AUGMENT_INJ. 

End GENV.

(** * Commutation with program transformations *)

(** ** Commutation with matching between programs. *)

Section MATCH_PROGRAMS.

Variables A B V W: Type.
Variable match_fun: A -> B -> Prop.
Variable match_varinfo: V -> W -> Prop.

Inductive match_globvar: globvar V -> globvar W -> Prop :=
  | match_globvar_intro: forall info1 info2 init ro vo,
      match_varinfo info1 info2 ->
      match_globvar (mkglobvar info1 init ro vo) (mkglobvar info2 init ro vo).

Record match_genvs (new_functs : list (ident * B)) (new_vars : list (ident * globvar W)) 
                   (ge1: t A V) (ge2: t B W): Prop := {
  mge_nextfun: genv_nextfun ge2 = genv_nextfun ge1 - Z_of_nat(length new_functs);
  mge_nextvar: genv_nextvar ge2 = genv_nextvar ge1 + Z_of_nat(length new_vars);
  mge_symb:    forall id,  ~ In id ((funct_names new_functs) ++ (var_names new_vars)) -> 
                   PTree.get id (genv_symb ge2) = PTree.get id (genv_symb ge1);
  mge_funs:
    forall b f, ZMap.get b (genv_funs ge1) = Some f ->
    exists tf, ZMap.get b (genv_funs ge2) = Some tf /\ match_fun f tf;
  mge_rev_funs:
    forall b tf, ZMap.get b (genv_funs ge2) = Some tf ->
    if zlt (genv_nextfun ge1) b then 
      exists f, ZMap.get b (genv_funs ge1) = Some f /\ match_fun f tf
    else 
      In tf (map (@snd ident B) new_functs);
  mge_vars:
    forall b v, ZMap.get b (genv_vars ge1) = Some v ->
    exists tv, ZMap.get b (genv_vars ge2) = Some tv /\ match_globvar v tv;
  mge_rev_vars:
    forall b tv, ZMap.get b (genv_vars ge2) = Some tv ->
    if zlt b (genv_nextvar ge1) then
      exists v, ZMap.get b (genv_vars ge1) = Some v /\ match_globvar v tv
    else
      In tv (map (@snd ident (globvar W)) new_vars)
}.

Lemma add_function_match:
  forall ge1 ge2 id f1 f2,
  match_genvs nil nil ge1 ge2 ->
  match_fun f1 f2 ->
  match_genvs nil nil (add_function ge1 (id, f1)) (add_function ge2 (id, f2)).
Proof.
  intros. destruct H. 
     simpl in mge_nextfun0. rewrite Zminus_0_r in mge_nextfun0. 
     simpl in mge_nextvar0. rewrite Zplus_0_r in mge_nextvar0. 
  constructor; simpl. 
  rewrite Zminus_0_r. congruence.
  rewrite Zplus_0_r. congruence.
  intros. rewrite mge_nextfun0. 
    repeat rewrite PTree.gsspec. destruct (peq id0 id); auto. 
    rewrite mge_nextfun0. intros. rewrite ZMap.gsspec in H. rewrite ZMap.gsspec. 
    destruct (ZIndexed.eq b (genv_nextfun ge1)). 
     exists f2; split; congruence.
     eauto.
  rewrite mge_nextfun0. intros. rewrite ZMap.gsspec in H. rewrite ZMap.gsspec. 
   destruct (ZIndexed.eq b (genv_nextfun ge1)). 
    subst b. destruct (zlt (genv_nextfun ge1 - 1) (genv_nextfun ge1)). 
      exists f1; split; congruence. omega. 
    pose proof (mge_rev_funs0 b tf H). 
    destruct (zlt (genv_nextfun ge1) b); 
      destruct (zlt (genv_nextfun ge1 - 1) b).  auto. omega. exfalso; omega. intuition.
  auto.
  auto.
Qed.

Lemma add_functions_match:
  forall fl1 fl2, list_forall2 (match_funct_entry match_fun) fl1 fl2 ->
  forall ge1 ge2, match_genvs nil nil ge1 ge2 ->
  match_genvs nil nil (add_functions ge1 fl1) (add_functions ge2 fl2).
Proof.
  induction 1; intros; simpl. 
  auto.
  destruct a1 as [id1 f1]; destruct b1 as [id2 f2].
  destruct H. subst. apply IHlist_forall2. apply add_function_match; auto.
Qed.

Lemma add_function_augment_match: 
  forall new_functs new_vars ge1 ge2 id f2,
  match_genvs new_functs new_vars ge1 ge2 ->
  match_genvs (new_functs++((id,f2)::nil)) new_vars ge1 (add_function ge2 (id, f2)).
Proof.
  intros. destruct H. constructor; simpl. 
  rewrite mge_nextfun0. rewrite app_length. 
       simpl. rewrite inj_plus. rewrite inj_S. rewrite inj_0. unfold block; omega. (* painful! *)
  auto.
  intros. unfold funct_names in H. rewrite map_app in H. rewrite in_app in H.  rewrite in_app in H. simpl in H. 
     destruct (peq id id0). subst. intuition. rewrite PTree.gso. 
     apply mge_symb0. intro.  apply H. rewrite in_app in H0. inversion H0; intuition. intuition. 
  intros. rewrite ZMap.gso. auto. 
     rewrite mge_nextfun0. pose proof (genv_funs_range ge1 b H). intro; subst; omega.
  intros. rewrite ZMap.gsspec in H. 
     destruct (ZIndexed.eq b (genv_nextfun ge2)). 
       destruct (zlt (genv_nextfun ge1) b). 
          exfalso.  rewrite mge_nextfun0 in e.  unfold block; omega. 
          rewrite map_app. rewrite in_app.  simpl.  inversion H; intuition.
       pose proof (mge_rev_funs0 b tf H). 
          destruct (zlt (genv_nextfun ge1) b). 
            auto.
            rewrite map_app. rewrite in_app. intuition. 
  auto.
  auto.
Qed.


Lemma add_functions_augment_match:
  forall fl new_functs new_vars ge1 ge2, 
    match_genvs new_functs new_vars ge1 ge2 ->
    match_genvs (new_functs++fl) new_vars ge1 (add_functions ge2 fl).
Proof.
  induction fl; simpl. 
    intros. rewrite app_nil_r. auto. 
    intros. replace (new_functs ++ a :: fl) with ((new_functs ++ (a::nil)) ++ fl) 
       by (rewrite app_ass; auto). 
     apply IHfl. destruct a. apply add_function_augment_match. auto.
Qed.


Lemma add_variable_match:
  forall new_functs ge1 ge2 id v1 v2,
  match_genvs new_functs nil ge1 ge2 ->
  match_globvar v1 v2 ->
  match_genvs new_functs nil (add_variable ge1 (id, v1)) (add_variable ge2 (id, v2)).
Proof.
  intros. destruct H. 
     simpl in mge_nextvar0. rewrite Zplus_0_r in mge_nextvar0. 
  constructor; simpl. 
  auto. 
    rewrite Zplus_0_r. rewrite mge_nextvar0. auto. 
  intros. rewrite mge_nextvar0. 
    repeat rewrite PTree.gsspec. destruct (peq id0 id); auto. 
  auto.
  auto.
  rewrite mge_nextvar0. intros. rewrite ZMap.gsspec in H. rewrite ZMap.gsspec. 
    destruct (ZIndexed.eq b (genv_nextvar ge1)). 
     exists v2; split; congruence.
     eauto.
  rewrite mge_nextvar0. intros. rewrite ZMap.gsspec in H. rewrite ZMap.gsspec. 
   destruct (ZIndexed.eq b (genv_nextvar ge1)). 
    subst b. inversion H; subst. 
      destruct (zlt (genv_nextvar ge1) (genv_nextvar ge1 + 1)). 
        exists v1; split; congruence. omega. 
      pose proof (mge_rev_vars0 _ _ H).
        destruct (zlt b (genv_nextvar ge1));
          destruct (zlt b (genv_nextvar ge1 + 1)).  auto. omega. exfalso; omega. intuition.
Qed.

Lemma add_variables_match:
  forall vl1 vl2, list_forall2 (match_var_entry match_varinfo) vl1 vl2 ->
  forall new_functs ge1 ge2, match_genvs new_functs nil ge1 ge2 ->
  match_genvs new_functs nil (add_variables ge1 vl1) (add_variables ge2 vl2).
Proof.
  induction 1; intros; simpl. 
  auto.
  inv H. apply IHlist_forall2. apply add_variable_match; auto. constructor; auto.
Qed.


Lemma add_variable_augment_match:
  forall ge1 new_functs new_vars ge2 id v2,
  match_genvs new_functs new_vars ge1 ge2 ->
  match_genvs new_functs (new_vars++((id,v2)::nil)) ge1 (add_variable ge2 (id, v2)).
Proof.
  intros. destruct H. constructor; simpl. 
  auto.
  rewrite mge_nextvar0. rewrite app_length. 
       simpl. rewrite inj_plus. rewrite inj_S. rewrite inj_0. unfold block; omega. (* painful! *)
  intros. unfold funct_names, var_names in H. rewrite map_app in H. rewrite in_app in H.  rewrite in_app in H. simpl in H. 
     destruct (peq id id0). subst. intuition. rewrite PTree.gso. 
     apply mge_symb0. intro.  apply H. rewrite in_app in H0. inversion H0; intuition. intuition. 
  auto.
  auto.
  intros. rewrite ZMap.gso. auto. 
     rewrite mge_nextvar0. pose proof (genv_vars_range ge1 b H). intro; subst; omega.
  intros. rewrite ZMap.gsspec in H. 
     destruct (ZIndexed.eq b (genv_nextvar ge2)). 
       destruct (zlt b (genv_nextvar ge1)). 
          exfalso.  rewrite mge_nextvar0 in e.  unfold block; omega. 
          rewrite map_app. rewrite in_app.  simpl.  inversion H; intuition.
       pose proof (mge_rev_vars0 b tv H). 
          destruct (zlt b (genv_nextvar ge1)). 
            auto.
            rewrite map_app. rewrite in_app. intuition. 

Qed.

Lemma add_variables_augment_match:
  forall vl ge1 new_functs new_vars ge2, 
    match_genvs new_functs new_vars ge1 ge2 ->
    match_genvs new_functs (new_vars++vl) ge1  (add_variables ge2 vl).
Proof.
  induction vl; simpl. 
    intros. rewrite app_nil_r. auto. 
    intros. replace (new_vars ++ a :: vl) with ((new_vars ++ (a::nil)) ++ vl) 
       by (rewrite app_ass; auto). 
     apply IHvl. destruct a. apply add_variable_augment_match. auto.
Qed.

Variable new_functs : list (ident * B).
Variable new_vars : list (ident * globvar W).
Variable new_main : ident.

Variable p: program A V.
Variable p': program B W.
Hypothesis progmatch: 
  match_program match_fun match_varinfo new_functs new_vars new_main p p'.

Lemma globalenvs_match:
  match_genvs new_functs new_vars (globalenv p) (globalenv p').
Proof.
  unfold globalenv. destruct progmatch. clear progmatch.
  destruct H as [tfuncts [P1 P2]]. destruct H0.  clear H0. destruct H as [tvars [Q1 Q2]]. 
  rewrite P2.  rewrite Q2. clear P2 Q2.
  rewrite add_variables_app. 
  rewrite add_functions_app. 
  pattern new_vars at 1. replace new_vars with (nil++new_vars) by auto.
  apply add_variables_augment_match.
  apply add_variables_match; auto. 
  pattern new_functs at 1. replace new_functs with (nil++new_functs) by auto. 
  apply add_functions_augment_match.
  apply add_functions_match; auto. 
  constructor; simpl; auto; intros; rewrite ZMap.gi in H; congruence.
Qed.

Theorem find_funct_ptr_match:
  forall (b : block) (f : A),
  find_funct_ptr (globalenv p) b = Some f ->
  exists tf : B,
  find_funct_ptr (globalenv p') b = Some tf /\ match_fun f tf.
Proof (mge_funs globalenvs_match).

Theorem find_funct_ptr_rev_match:
  forall (b : block) (tf : B),
  find_funct_ptr (globalenv p') b = Some tf ->
  if zlt (genv_nextfun (globalenv p)) b then 
      exists f, find_funct_ptr (globalenv p) b = Some f /\ match_fun f tf
  else 
      In tf (map (@snd ident B) new_functs).
Proof (mge_rev_funs globalenvs_match).

Theorem find_funct_match:
  forall (v : val) (f : A),
  find_funct (globalenv p) v = Some f ->
  exists tf : B, find_funct (globalenv p') v = Some tf /\ match_fun f tf.
Proof.
  intros. exploit find_funct_inv; eauto. intros [b EQ]. subst v. 
  rewrite find_funct_find_funct_ptr in H. 
  rewrite find_funct_find_funct_ptr.
  apply find_funct_ptr_match. auto.
Qed.

Theorem find_funct_rev_match:
  forall (v : val) (tf : B),
  find_funct (globalenv p') v = Some tf ->
  (exists f, find_funct (globalenv p) v = Some f /\ match_fun f tf) 
  \/ (In tf (map (@snd ident B) new_functs)).
Proof.
  intros. exploit find_funct_inv; eauto. intros [b EQ]. subst v. 
  rewrite find_funct_find_funct_ptr in H. 
  rewrite find_funct_find_funct_ptr.
  apply find_funct_ptr_rev_match in H. 
   destruct (zlt (genv_nextfun (globalenv p)) b); intuition. 
Qed.

Theorem find_var_info_match:
  forall (b : block) (v : globvar V),
  find_var_info (globalenv p) b = Some v ->
  exists tv,
  find_var_info (globalenv p') b = Some tv /\ match_globvar v tv.
Proof (mge_vars globalenvs_match).

Theorem find_var_info_rev_match:
  forall (b : block) (tv : globvar W),
  find_var_info (globalenv p') b = Some tv ->
  if zlt b (genv_nextvar (globalenv p)) then 
    exists v, find_var_info (globalenv p) b = Some v /\ match_globvar v tv
  else
    In tv (map (@snd ident (globvar W)) new_vars).  
Proof (mge_rev_vars globalenvs_match).

Theorem find_symbol_match:
  forall (s : ident),
  ~In s (funct_names new_functs ++ var_names new_vars) -> 
  find_symbol (globalenv p') s = find_symbol (globalenv p) s.
Proof.
  intros. destruct globalenvs_match. unfold find_symbol.  auto. 
Qed.

Hypothesis new_ids_fresh : 
  (forall s', find_symbol (globalenv p) s' <> None  -> 
             ~In s' (funct_names new_functs ++ var_names new_vars)).

Lemma store_init_data_list_match:
  forall idl m b ofs m',
  store_init_data_list (globalenv p) m b ofs idl = Some m' ->
  store_init_data_list (globalenv p') m b ofs idl = Some m'.
Proof.
  induction idl; simpl; intros. 
  auto.
  assert (forall m', store_init_data (globalenv p) m b ofs a = Some m' ->
          store_init_data (globalenv p') m b ofs a = Some m').
   destruct a; simpl; auto. rewrite find_symbol_match. auto. 
     inversion H.  case_eq (find_symbol (globalenv p) i). 
       intros. apply new_ids_fresh. intro. rewrite H0 in H2; inversion H2. 
       intro. rewrite H0 in H1. inversion H1. 
  case_eq (store_init_data (globalenv p) m b ofs a); intros. 
    rewrite H1 in H. 
    pose proof (H0 _ H1). rewrite H2. auto. 
    rewrite H1 in H. inversion H. 
Qed.

Lemma alloc_variables_match:
  forall vl1 vl2, list_forall2 (match_var_entry match_varinfo) vl1 vl2 ->
  forall m m',
  alloc_variables (globalenv p) m vl1 = Some m' -> 
  alloc_variables (globalenv p') m vl2 = Some m'.
Proof.
  induction 1; intros until m'; simpl.
  auto.
  inv H. 
  unfold alloc_variable; simpl. 
  destruct (Mem.alloc m 0 (init_data_list_size init)). 
  destruct (store_zeros m0 b (init_data_list_size init)); auto. 
  case_eq (store_init_data_list (globalenv p) m1 b 0 init); intros m2 P. 
  rewrite (store_init_data_list_match _ _ _ _ P). 
  change (perm_globvar (mkglobvar info2 init ro vo))
    with (perm_globvar (mkglobvar info1 init ro vo)).
  destruct (Mem.drop_perm m2 b 0 (init_data_list_size init)
    (perm_globvar (mkglobvar info1 init ro vo))); auto. 
  inversion P. 
Qed.

Theorem init_mem_match:
  forall m, init_mem p = Some m -> 
  init_mem p' = alloc_variables (globalenv p') m new_vars.
Proof.
  unfold init_mem. destruct progmatch. destruct H0.  destruct H0 as [tvars [P1 P2]].
  rewrite P2. 
  intros. 
  erewrite <- alloc_variables_app; eauto. 
  eapply alloc_variables_match; eauto. 
Qed.

End MATCH_PROGRAMS.

Section TRANSF_PROGRAM_AUGMENT.

Variable A B V W: Type.
Variable transf_fun: A -> res B.
Variable transf_var: V -> res W.

Variable new_functs : list (ident * B).
Variable new_vars : list (ident * globvar W).
Variable new_main : ident.

Variable p: program A V.
Variable p': program B W.

Hypothesis transf_OK:
  transform_partial_augment_program transf_fun transf_var new_functs new_vars new_main p = OK p'.

Remark prog_match:
  match_program
    (fun fd tfd => transf_fun fd = OK tfd)
    (fun info tinfo => transf_var info = OK tinfo)
    new_functs new_vars new_main
    p p'.
Proof.
  apply transform_partial_augment_program_match; auto.
Qed.

Theorem find_funct_ptr_transf_augment:
  forall (b: block) (f: A),
  find_funct_ptr (globalenv p) b = Some f ->
  exists f',
  find_funct_ptr (globalenv p') b = Some f' /\ transf_fun f = OK f'.
Proof.
  intros. 
  exploit find_funct_ptr_match. eexact prog_match. eauto. 
  intros [tf [X Y]]. exists tf; auto.
Qed.



(* This may not yet be in the ideal form for easy use .*)
Theorem find_new_funct_ptr_exists: 
  list_norepet (prog_funct_names p ++ funct_names new_functs) ->
  list_disjoint (prog_funct_names p ++ funct_names new_functs)  (prog_var_names p ++ var_names new_vars) ->
  forall id f, In (id, f) new_functs -> 
  exists b, find_symbol (globalenv p') id = Some b
         /\ find_funct_ptr (globalenv p') b = Some f.
Proof.
  intros. 
  destruct p. 
  unfold transform_partial_augment_program in transf_OK. 
  monadInv transf_OK. rename x into prog_funct'.  rename x0 into prog_vars'. simpl in *.
  assert (funct_names prog_funct = funct_names prog_funct').
   clear - EQ.  generalize dependent prog_funct'. induction prog_funct; intros.
      simpl in EQ. inversion EQ; subst; auto.
      simpl in EQ. destruct a. destruct (transf_fun a); try discriminate. monadInv EQ.
      simpl; f_equal; auto.
  assert (var_names prog_vars = var_names prog_vars').
   clear - EQ1.  generalize dependent prog_vars'. induction prog_vars; intros.
      simpl in EQ1. inversion EQ1; subst; auto.
      simpl in EQ1. destruct a. destruct (transf_globvar transf_var g); try discriminate. monadInv EQ1.
      simpl; f_equal; auto.
  apply find_funct_ptr_exists. 
  unfold prog_funct_names in *; simpl in *. 
  rewrite funct_names_app. rewrite <- H2. auto.
  unfold prog_funct_names, prog_var_names in *; simpl in *.  
  rewrite funct_names_app. rewrite var_names_app. rewrite <- H2. rewrite <- H3.  auto.
  simpl. intuition.
Qed.

Theorem find_funct_ptr_rev_transf_augment:
  forall (b: block) (tf: B),
  find_funct_ptr (globalenv p') b = Some tf ->
  if (zlt (genv_nextfun (globalenv p)) b) then
   (exists f, find_funct_ptr (globalenv p) b = Some f /\ transf_fun f = OK tf)
  else 
   In tf (map (@snd ident B) new_functs).
Proof.
  intros. 
  exploit find_funct_ptr_rev_match;eauto. eexact prog_match; eauto. auto. 
Qed.


Theorem find_funct_transf_augment:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  exists f',
  find_funct (globalenv p') v = Some f' /\ transf_fun f = OK f'.
Proof.
  intros. 
  exploit find_funct_match. eexact prog_match. eauto. 
  intros [tf [X Y]]. exists tf; auto.
Qed.

Theorem find_funct_rev_transf_augment: 
  forall (v: val) (tf: B),
  find_funct (globalenv p') v = Some tf ->
  (exists f, find_funct (globalenv p) v = Some f /\ transf_fun f = OK tf) \/
  In tf (map (@snd ident B) new_functs). 
Proof.
  intros. 
  exploit find_funct_rev_match. eexact prog_match. eauto. auto. 
Qed.

Theorem find_var_info_transf_augment:
  forall (b: block) (v: globvar V),
  find_var_info (globalenv p) b = Some v ->
  exists v',
  find_var_info (globalenv p') b = Some v' /\ transf_globvar transf_var v = OK v'.
Proof.
  intros. 
  exploit find_var_info_match. eexact prog_match. eauto. 
  intros [tv [X Y]]. exists tv; split; auto. inv Y. unfold transf_globvar; simpl.
  rewrite H0; simpl. auto.
Qed.

Theorem find_new_var_exists:
  forall id gv,
  list_norepet (var_names new_vars) ->
  In (id, gv) new_vars ->
  exists b, find_symbol (globalenv p') id = Some b /\ find_var_info (globalenv p') b = Some gv.
Proof.
  intros. 
  assert (P: forall b vars (ge: t B W),
          ~In id (var_names vars) ->
          find_symbol ge id = Some b
          /\ find_var_info ge b = Some gv ->
          find_symbol (add_variables ge vars) id = Some b
          /\ find_var_info (add_variables ge vars) b = Some gv).
  induction vars; simpl; intros. auto. apply IHvars. tauto.
  destruct a as [id1 gv1]; unfold add_variable, find_symbol, find_var_info; simpl in *.
  destruct H2; split. rewrite PTree.gso. auto. intuition. 
  rewrite ZMap.gso. auto. exploit genv_vars_range; eauto. unfold ZIndexed.t; omega.

  assert (Q: forall vars (ge: t B W),
          list_norepet (var_names vars) ->
          In (id, gv) vars ->
          exists b, find_symbol (add_variables ge vars) id = Some b
                 /\ find_var_info (add_variables ge vars) b = Some gv).
    induction vars; simpl; intros.
    contradiction.
    destruct a as [id1 gv1]; simpl in *. inv H1. destruct H2. inv H1. 
    exists (genv_nextvar ge). apply P; auto. 
    unfold add_variable, find_symbol, find_var_info; simpl in *.
    split. apply PTree.gss. apply ZMap.gss. 
    apply IHvars; auto. 

  unfold transform_partial_augment_program in transf_OK. 
  monadInv transf_OK. rename x into prog_funct'.  rename x0 into prog_vars'. simpl in *.
  unfold globalenv; simpl. repeat rewrite add_variables_app. apply Q; auto.
Qed.

Theorem find_var_info_rev_transf_augment:
  forall (b: block) (v': globvar W),
  find_var_info (globalenv p') b = Some v' ->
  if zlt b (genv_nextvar (globalenv p)) then
    (exists v, find_var_info (globalenv p) b = Some v /\ transf_globvar transf_var v = OK v')
  else
    (In v' (map (@snd ident (globvar W)) new_vars)).
Proof.
  intros. 
  exploit find_var_info_rev_match. eexact prog_match. eauto.
  destruct (zlt b (genv_nextvar (globalenv p))); auto.
  intros [v [X Y]]. exists v; split; auto. inv Y. unfold transf_globvar; simpl. 
  rewrite H0; simpl. auto.
Qed.

Theorem find_symbol_transf_augment:  
  forall (s: ident), 
  ~ In s (funct_names new_functs ++ var_names new_vars) -> 
  find_symbol (globalenv p') s = find_symbol (globalenv p) s.
Proof.
  intros. eapply find_symbol_match. eexact prog_match. auto.
Qed.

Theorem init_mem_transf_augment: 
   (forall s', find_symbol (globalenv p) s' <> None -> 
     ~ In s' (funct_names new_functs ++ var_names new_vars)) -> 
   forall m, init_mem p = Some m -> 
   init_mem p' = alloc_variables (globalenv p') m new_vars.
Proof.
  intros. eapply init_mem_match. eexact prog_match. auto. auto.
Qed.
 
Theorem init_mem_inject_transf_augment:
   (forall s', find_symbol (globalenv p) s' <> None -> 
     ~ In s' (funct_names new_functs ++ var_names new_vars)) -> 
  forall m, init_mem p = Some m ->
  forall m', init_mem p' = Some m' -> 
  Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m'.
Proof.
  intros. 
  pose proof (initmem_inject p H0). 
  erewrite init_mem_transf_augment in H1; eauto. 
  eapply alloc_variables_augment; eauto. omega.
Qed.


End TRANSF_PROGRAM_AUGMENT.

Section TRANSF_PROGRAM_PARTIAL2.

Variable A B V W: Type.
Variable transf_fun: A -> res B.
Variable transf_var: V -> res W.
Variable p: program A V.
Variable p': program B W.
Hypothesis transf_OK:
  transform_partial_program2 transf_fun transf_var p = OK p'.

Remark transf_augment_OK:
  transform_partial_augment_program transf_fun transf_var nil nil p.(prog_main) p = OK p'.
Proof.
  rewrite <- transf_OK. 
  unfold transform_partial_augment_program, transform_partial_program2. 
  destruct (map_partial prefix_name transf_fun (prog_funct p)); auto. simpl. 
  destruct (map_partial prefix_name (transf_globvar transf_var) (prog_vars p)); simpl. 
  repeat rewrite app_nil_r. auto. auto.
Qed.

Theorem find_funct_ptr_transf_partial2:
  forall (b: block) (f: A),
  find_funct_ptr (globalenv p) b = Some f ->
  exists f',
  find_funct_ptr (globalenv p') b = Some f' /\ transf_fun f = OK f'.
Proof.
  exact (@find_funct_ptr_transf_augment _ _ _ _ _ _ _ _ _ _ _ transf_augment_OK).
Qed.

Theorem find_funct_ptr_rev_transf_partial2:
  forall (b: block) (tf: B),
  find_funct_ptr (globalenv p') b = Some tf ->
  exists f, find_funct_ptr (globalenv p) b = Some f /\ transf_fun f = OK tf.
Proof.
  pose proof (@find_funct_ptr_rev_transf_augment _ _ _ _ _ _ _ _ _ _ _ transf_augment_OK).
  intros.  pose proof (H b tf H0). 
  destruct (zlt (genv_nextfun (globalenv p)) b).  auto. inversion H1. 
Qed.

Theorem find_funct_transf_partial2:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  exists f',
  find_funct (globalenv p') v = Some f' /\ transf_fun f = OK f'.
Proof.
  exact (@find_funct_transf_augment _ _ _ _ _ _ _ _ _ _ _ transf_augment_OK).
Qed.

Theorem find_funct_rev_transf_partial2:
  forall (v: val) (tf: B),
  find_funct (globalenv p') v = Some tf ->
  exists f, find_funct (globalenv p) v = Some f /\ transf_fun f = OK tf.
Proof.
  pose proof (@find_funct_rev_transf_augment _ _ _ _ _ _ _ _ _ _ _ transf_augment_OK).
  intros. pose proof (H v tf H0). 
  destruct H1. auto. inversion H1. 
Qed.

Theorem find_var_info_transf_partial2:
  forall (b: block) (v: globvar V),
  find_var_info (globalenv p) b = Some v ->
  exists v',
  find_var_info (globalenv p') b = Some v' /\ transf_globvar transf_var v = OK v'.
Proof.
  exact (@find_var_info_transf_augment _ _ _ _ _ _ _ _ _ _ _ transf_augment_OK).
Qed.

Theorem find_var_info_rev_transf_partial2:
  forall (b: block) (v': globvar W),
  find_var_info (globalenv p') b = Some v' ->
  exists v,
  find_var_info (globalenv p) b = Some v /\ transf_globvar transf_var v = OK v'.
Proof.
  pose proof (@find_var_info_rev_transf_augment _ _ _ _ _ _ _ _ _ _ _ transf_augment_OK).
  intros.  pose proof (H b v' H0). 
  destruct (zlt b (genv_nextvar (globalenv p))).  auto. inversion H1. 
Qed.

Theorem find_symbol_transf_partial2:
  forall (s: ident),
  find_symbol (globalenv p') s = find_symbol (globalenv p) s.
Proof.
  pose proof (@find_symbol_transf_augment _ _ _ _ _ _ _ _ _ _ _ transf_augment_OK).
  auto.
Qed.

Theorem init_mem_transf_partial2:
  forall m, init_mem p = Some m -> init_mem p' = Some m.
Proof.
  pose proof (@init_mem_transf_augment _ _ _ _ _ _ _ _ _ _ _ transf_augment_OK).
  intros. simpl in H. apply H; auto.  
Qed.

End TRANSF_PROGRAM_PARTIAL2.

Section TRANSF_PROGRAM_PARTIAL.

Variable A B V: Type.
Variable transf: A -> res B.
Variable p: program A V.
Variable p': program B V.
Hypothesis transf_OK: transform_partial_program transf p = OK p'.

Remark transf2_OK:
  transform_partial_program2 transf (fun x => OK x) p = OK p'.
Proof.
  rewrite <- transf_OK. 
  unfold transform_partial_program2, transform_partial_program.
  destruct (map_partial prefix_name transf (prog_funct p)); auto.
  simpl. replace (transf_globvar (fun (x : V) => OK x)) with (fun (v: globvar V) => OK v).
  rewrite map_partial_identity; auto.
  apply extensionality; intros. destruct x; auto.
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

Theorem find_var_info_transf_partial:
  forall (b: block),
  find_var_info (globalenv p') b = find_var_info (globalenv p) b.
Proof.
  intros. case_eq (find_var_info (globalenv p) b); intros.
  exploit find_var_info_transf_partial2. eexact transf2_OK. eauto. 
  intros [v' [P Q]]. monadInv Q. rewrite P. inv EQ. destruct g; auto. 
  case_eq (find_var_info (globalenv p') b); intros.
  exploit find_var_info_rev_transf_partial2. eexact transf2_OK. eauto.
  intros [v' [P Q]]. monadInv Q. inv EQ. congruence. 
  auto.
Qed.

Theorem init_mem_transf_partial:
  forall m, init_mem p = Some m -> init_mem p' = Some m.
Proof.
  exact (@init_mem_transf_partial2 _ _ _ _ _ _ _ _ transf2_OK).
Qed.

End TRANSF_PROGRAM_PARTIAL.

Section TRANSF_PROGRAM.

Variable A B V: Type.
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

Theorem find_var_info_transf:
  forall (b: block),
  find_var_info (globalenv tp) b = find_var_info (globalenv p) b.
Proof.
  exact (@find_var_info_transf_partial _ _ _ _ _ _ transf_OK).
Qed.

Theorem init_mem_transf:
  forall m, init_mem p = Some m -> init_mem tp = Some m.
Proof.
  exact (@init_mem_transf_partial _ _ _ _ _ _ transf_OK).
Qed.

End TRANSF_PROGRAM.

End Genv.
