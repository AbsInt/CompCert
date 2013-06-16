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

(** Auxiliary function for initialization of global variables. *)

Function store_zeros (m: mem) (b: block) (p: Z) (n: Z) {wf (Zwf 0) n}: option mem :=
  if zle n 0 then Some m else
    match Mem.store Mint8unsigned m b p Vzero with
    | Some m' => store_zeros m' b (p + 1) (n - 1)
    | None => None
    end.
Proof.
  intros. red. omega.
  apply Zwf_well_founded.
Qed.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Module Genv.

(** * Global environments *)

Section GENV.

Variable F: Type.  (**r The type of function descriptions *)
Variable V: Type.  (**r The type of information attached to variables *)

(** The type of global environments. *)

Record t: Type := mkgenv {
  genv_symb: PTree.t block;             (**r mapping symbol -> block *)
  genv_funs: PTree.t F;                 (**r mapping function pointer -> definition *)
  genv_vars: PTree.t (globvar V);       (**r mapping variable pointer -> info *)
  genv_next: block;                     (**r next symbol pointer *)
  genv_symb_range: forall id b, PTree.get id genv_symb = Some b -> Plt b genv_next;
  genv_funs_range: forall b f, PTree.get b genv_funs = Some f -> Plt b genv_next;
  genv_vars_range: forall b v, PTree.get b genv_vars = Some v -> Plt b genv_next;
  genv_funs_vars: forall b1 b2 f v,
    PTree.get b1 genv_funs = Some f -> PTree.get b2 genv_vars = Some v -> b1 <> b2;
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
  PTree.get b ge.(genv_funs).

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
  PTree.get b ge.(genv_vars).

(** ** Constructing the global environment *)

Program Definition add_global (ge: t) (idg: ident * globdef F V) : t :=
  @mkgenv
    (PTree.set idg#1 ge.(genv_next) ge.(genv_symb))
    (match idg#2 with
     | Gfun f => PTree.set ge.(genv_next) f ge.(genv_funs)
     | Gvar v => ge.(genv_funs)
     end)
    (match idg#2 with
     | Gfun f => ge.(genv_vars)
     | Gvar v => PTree.set ge.(genv_next) v ge.(genv_vars)
     end)
    (Psucc ge.(genv_next))
    _ _ _ _ _.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H. destruct (peq id i). inv H. apply Plt_succ.
  apply Plt_trans_succ; eauto.
Qed.
Next Obligation.
  destruct ge; simpl in *. 
  destruct g. 
  rewrite PTree.gsspec in H. 
  destruct (peq b genv_next0). inv H. apply Plt_succ.
  apply Plt_trans_succ; eauto.
  apply Plt_trans_succ; eauto.
Qed.
Next Obligation.
  destruct ge; simpl in *. 
  destruct g.
  apply Plt_trans_succ; eauto.
  rewrite PTree.gsspec in H. 
  destruct (peq b genv_next0). inv H. apply Plt_succ.
  apply Plt_trans_succ; eauto.
Qed.
Next Obligation.
  destruct ge; simpl in *.
  destruct g.
  rewrite PTree.gsspec in H.
  destruct (peq b1 genv_next0). inv H.
  apply sym_not_equal; apply Plt_ne; eauto.
  eauto.
  rewrite PTree.gsspec in H0.
  destruct (peq b2 genv_next0). inv H0.
  apply Plt_ne; eauto.
  eauto.
Qed.
Next Obligation.
  destruct ge; simpl in *. 
  rewrite PTree.gsspec in H. rewrite PTree.gsspec in H0. 
  destruct (peq id1 i); destruct (peq id2 i).
  congruence.
  inv H. eelim Plt_strict. eapply genv_symb_range0; eauto.
  inv H0. eelim Plt_strict. eapply genv_symb_range0; eauto.
  eauto.
Qed.

Definition add_globals (ge: t) (gl: list (ident * globdef F V)) : t :=
  List.fold_left add_global gl ge.

Lemma add_globals_app:
  forall gl2 gl1 ge,
  add_globals ge (gl1 ++ gl2) = add_globals (add_globals ge gl1) gl2.
Proof.
  induction gl1; simpl; intros. auto. rewrite IHgl1; auto.
Qed.

Program Definition empty_genv : t :=
  @mkgenv (PTree.empty _) (PTree.empty _) (PTree.empty _) 1%positive _ _ _ _ _.
Next Obligation.
  rewrite PTree.gempty in H. discriminate.
Qed.
Next Obligation.
  rewrite PTree.gempty in H. discriminate.
Qed.
Next Obligation.
  rewrite PTree.gempty in H. discriminate.
Qed.
Next Obligation.
  rewrite PTree.gempty in H. discriminate.
Qed.
Next Obligation.
  rewrite PTree.gempty in H. discriminate.
Qed.

Definition globalenv (p: program F V) :=
  add_globals empty_genv p.(prog_defs).

(** Proof principles *)

Section GLOBALENV_PRINCIPLES.

Variable P: t -> Prop.

Lemma add_globals_preserves:
  forall gl ge,
  (forall ge id g, P ge -> In (id, g) gl -> P (add_global ge (id, g))) ->
  P ge -> P (add_globals ge gl).
Proof.
  induction gl; simpl; intros. 
  auto.
  destruct a. apply IHgl; auto. 
Qed.

Lemma add_globals_ensures:
  forall id g gl ge,
  (forall ge id g, P ge -> In (id, g) gl -> P (add_global ge (id, g))) ->
  (forall ge, P (add_global ge (id, g))) ->
  In (id, g) gl -> P (add_globals ge gl).
Proof.
  induction gl; simpl; intros.
  contradiction.
  destruct H1. subst a. apply add_globals_preserves; auto. 
  apply IHgl; auto. 
Qed.

Lemma add_globals_norepet_ensures:
  forall id g gl ge,
  (forall ge id1 g1, P ge -> In (id1, g1) gl -> id1 <> id -> P (add_global ge (id1, g1))) ->
  (forall ge, P (add_global ge (id, g))) ->
  In (id, g) gl -> list_norepet (map fst gl) -> P (add_globals ge gl).
Proof.
  induction gl; simpl; intros.
  contradiction.
  inv H2. 
  destruct H1. subst a. simpl in H5. 
  apply add_globals_preserves; auto.
  intros. apply H. auto. auto. red; intros; subst id0. elim H5. 
  change id with (fst (id, g0)). apply List.in_map; auto. 
  apply IHgl; auto. 
Qed.

End GLOBALENV_PRINCIPLES.

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
  forall p id g,
  In (id, g) (prog_defs p) ->
  exists b, find_symbol (globalenv p) id = Some b.
Proof.
  intros. unfold globalenv. eapply add_globals_ensures; eauto.
(* preserves *)
  intros. unfold find_symbol; simpl. rewrite PTree.gsspec. destruct (peq id id0).
  econstructor; eauto.
  auto.
(* ensures *)
  intros. unfold find_symbol; simpl. rewrite PTree.gss. econstructor; eauto.
Qed.

Theorem find_funct_ptr_exists:
  forall p id f,
  list_norepet (prog_defs_names p) ->
  In (id, Gfun f) (prog_defs p) ->
  exists b,
     find_symbol (globalenv p) id = Some b
  /\ find_funct_ptr (globalenv p) b = Some f.
Proof.
  intros; unfold globalenv. eapply add_globals_norepet_ensures; eauto.
(* preserves *)
  intros. unfold find_symbol, find_funct_ptr in *; simpl.
  destruct H1 as [b [A B]]. exists b; split.
  rewrite PTree.gso; auto.
  destruct g1 as [f1 | v1]. rewrite PTree.gso. auto.
  apply Plt_ne. eapply genv_funs_range; eauto.
  auto. 
(* ensures *)
  intros. unfold find_symbol, find_funct_ptr in *; simpl.
  exists (genv_next ge); split. apply PTree.gss. apply PTree.gss.
Qed.

Theorem find_var_exists:
  forall p id v,
  list_norepet (prog_defs_names p) ->
  In (id, Gvar v) (prog_defs p) ->
  exists b,
     find_symbol (globalenv p) id = Some b
  /\ find_var_info (globalenv p) b = Some v.
Proof.
  intros; unfold globalenv. eapply add_globals_norepet_ensures; eauto.
(* preserves *)
  intros. unfold find_symbol, find_var_info in *; simpl.
  destruct H1 as [b [A B]]. exists b; split.
  rewrite PTree.gso; auto.
  destruct g1 as [f1 | v1]. auto. rewrite PTree.gso. auto.
  apply Plt_ne. eapply genv_vars_range; eauto.
(* ensures *)
  intros. unfold find_symbol, find_var_info in *; simpl.
  exists (genv_next ge); split. apply PTree.gss. apply PTree.gss. 
Qed.

Lemma find_symbol_inversion : forall p x b,
  find_symbol (globalenv p) x = Some b ->
  In x (prog_defs_names p).
Proof.
  intros until b; unfold globalenv. eapply add_globals_preserves.
(* preserves *)
  unfold find_symbol; simpl; intros. rewrite PTree.gsspec in H1. 
  destruct (peq x id). subst x. change id with (fst (id, g)). apply List.in_map; auto.
  auto.
(* base *)
  unfold find_symbol; simpl; intros. rewrite PTree.gempty in H. discriminate.
Qed.

Theorem find_funct_ptr_inversion:
  forall p b f,
  find_funct_ptr (globalenv p) b = Some f ->
  exists id, In (id, Gfun f) (prog_defs p).
Proof.
  intros until f. unfold globalenv. apply add_globals_preserves. 
(* preserves *)
  unfold find_funct_ptr; simpl; intros. destruct g; auto. 
  rewrite PTree.gsspec in H1. destruct (peq b (genv_next ge)).
  inv H1. exists id; auto.
  auto.
(* base *)
  unfold find_funct_ptr; simpl; intros. rewrite PTree.gempty in H. discriminate.
Qed.

Theorem find_funct_inversion:
  forall p v f,
  find_funct (globalenv p) v = Some f ->
  exists id, In (id, Gfun f) (prog_defs p).
Proof.
  intros. exploit find_funct_inv; eauto. intros [b EQ]. subst v. 
  rewrite find_funct_find_funct_ptr in H.
  eapply find_funct_ptr_inversion; eauto.
Qed.

Theorem find_funct_ptr_prop:
  forall (P: F -> Prop) p b f,
  (forall id f, In (id, Gfun f) (prog_defs p) -> P f) ->
  find_funct_ptr (globalenv p) b = Some f ->
  P f.
Proof.
  intros. exploit find_funct_ptr_inversion; eauto. intros [id IN]. eauto.
Qed.

Theorem find_funct_prop:
  forall (P: F -> Prop) p v f,
  (forall id f, In (id, Gfun f) (prog_defs p) -> P f) ->
  find_funct (globalenv p) v = Some f ->
  P f.
Proof.
  intros. exploit find_funct_inversion; eauto. intros [id IN]. eauto.
Qed.

Theorem find_funct_ptr_symbol_inversion:
  forall p id b f,
  find_symbol (globalenv p) id = Some b ->
  find_funct_ptr (globalenv p) b = Some f ->
  In (id, Gfun f) p.(prog_defs).
Proof.
  intros until f. unfold globalenv, find_symbol, find_funct_ptr. apply add_globals_preserves. 
(* preserves *)
  intros. simpl in *. rewrite PTree.gsspec in H1. destruct (peq id id0). 
  inv H1. destruct g as [f1|v1]. rewrite PTree.gss in H2. inv H2. auto.
  eelim Plt_strict. eapply genv_funs_range; eauto.
  destruct g as [f1|v1]. rewrite PTree.gso in H2. auto.
  apply Plt_ne. eapply genv_symb_range; eauto.
  auto.
(* initial *)
  intros. simpl in *. rewrite PTree.gempty in H. discriminate.
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

Definition advance_next (gl: list (ident * globdef F V)) (x: positive) :=
  List.fold_left (fun n g => Psucc n) gl x.

Remark genv_next_add_globals:
  forall gl ge,
  genv_next (add_globals ge gl) = advance_next gl (genv_next ge).
Proof.
  induction gl; simpl; intros.
  auto.
  rewrite IHgl. auto. 
Qed.

(** * Construction of the initial memory state *)

Section INITMEM.

Variable ge: t.

Definition init_data_size (i: init_data) : Z :=
  match i with
  | Init_int8 _ => 1
  | Init_int16 _ => 2
  | Init_int32 _ => 4
  | Init_int64 _ => 8
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
  | Init_int64 n => Mem.store Mint64 m b p (Vlong n)
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

Fixpoint init_data_list_size (il: list init_data) {struct il} : Z :=
  match il with
  | nil => 0
  | i :: il' => init_data_size i + init_data_list_size il'
  end.

Definition perm_globvar (gv: globvar V) : permission :=
  if gv.(gvar_volatile) then Nonempty
  else if gv.(gvar_readonly) then Readable
  else Writable.

Definition alloc_global (m: mem) (idg: ident * globdef F V): option mem :=
  match idg with
  | (id, Gfun f) =>
      let (m1, b) := Mem.alloc m 0 1 in
      Mem.drop_perm m1 b 0 1 Nonempty
  | (id, Gvar v) =>
      let init := v.(gvar_init) in
      let sz := init_data_list_size init in
      let (m1, b) := Mem.alloc m 0 sz in
      match store_zeros m1 b 0 sz with
      | None => None
      | Some m2 =>
          match store_init_data_list m2 b 0 init with
          | None => None
          | Some m3 => Mem.drop_perm m3 b 0 sz (perm_globvar v)
          end
      end
  end.

Fixpoint alloc_globals (m: mem) (gl: list (ident * globdef F V))
                       {struct gl} : option mem :=
  match gl with
  | nil => Some m
  | g :: gl' =>
      match alloc_global m g with
      | None => None
      | Some m' => alloc_globals m' gl'
      end
  end.

Lemma alloc_globals_app : forall gl1 gl2 m m1,
  alloc_globals m gl1 = Some m1 ->
  alloc_globals m1 gl2 = alloc_globals m (gl1 ++ gl2).
Proof.
  induction gl1.
  simpl. intros.  inversion H; subst. auto.
  simpl. intros. destruct (alloc_global m a); eauto. inversion H.
Qed.

(** Next-block properties *)

Remark store_zeros_nextblock:
  forall m b p n m', store_zeros m b p n = Some m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  intros until n. functional induction (store_zeros m b p n); intros.
  inv H; auto.
  rewrite IHo; eauto with mem.
  congruence.
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

Remark alloc_global_nextblock:
  forall g m m',
  alloc_global m g = Some m' ->
  Mem.nextblock m' = Psucc(Mem.nextblock m).
Proof.
  unfold alloc_global. intros.
  destruct g as [id [f|v]]. 
  (* function *)
  destruct (Mem.alloc m 0 1) as [m1 b] eqn:?.
  erewrite Mem.nextblock_drop; eauto. erewrite Mem.nextblock_alloc; eauto. 
  (* variable *)
  set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:?.
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate.
  erewrite Mem.nextblock_drop; eauto.
  erewrite store_init_data_list_nextblock; eauto.
  erewrite store_zeros_nextblock; eauto.
  erewrite Mem.nextblock_alloc; eauto.
Qed.

Remark alloc_globals_nextblock:
  forall gl m m',
  alloc_globals m gl = Some m' ->
  Mem.nextblock m' = advance_next gl (Mem.nextblock m).
Proof.
  induction gl; simpl; intros.
  congruence.
  destruct (alloc_global m a) as [m1|] eqn:?; try discriminate.
  erewrite IHgl; eauto. erewrite alloc_global_nextblock; eauto.
Qed.

(** Permissions *)

Remark store_zeros_perm:
  forall k prm b' q m b p n m',
  store_zeros m b p n = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  intros until n. functional induction (store_zeros m b p n); intros.
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
  assert (forall chunk v,
          Mem.store chunk m b p v = Some m0 ->
          (Mem.perm m b' q k prm <-> Mem.perm m0 b' q k prm)).
    intros; split; eauto with mem. 
  destruct a; simpl in H; eauto.
  inv H; tauto.
  destruct (find_symbol ge i). eauto. discriminate.
Qed.

Remark alloc_global_perm:
  forall k prm b' q idg m m',
  alloc_global m idg = Some m' ->
  Mem.valid_block m b' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  intros. destruct idg as [id [f|v]]; simpl in H. 
  (* function *)
  destruct (Mem.alloc m 0 1) as [m1 b] eqn:?. 
  assert (b' <> b). apply Mem.valid_not_valid_diff with m; eauto with mem.
  split; intros.
  eapply Mem.perm_drop_3; eauto. eapply Mem.perm_alloc_1; eauto. 
  eapply Mem.perm_alloc_4; eauto. eapply Mem.perm_drop_4; eauto. 
  (* variable *)
  set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:?.
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate.
  assert (b' <> b). apply Mem.valid_not_valid_diff with m; eauto with mem.
  split; intros.
  eapply Mem.perm_drop_3; eauto.
  erewrite <- store_init_data_list_perm; [idtac|eauto].
  erewrite <- store_zeros_perm; [idtac|eauto].
  eapply Mem.perm_alloc_1; eauto. 
  eapply Mem.perm_alloc_4; eauto.
  erewrite store_zeros_perm; [idtac|eauto].
  erewrite store_init_data_list_perm; [idtac|eauto]. 
  eapply Mem.perm_drop_4; eauto. 
Qed.

Remark alloc_globals_perm:
  forall k prm b' q gl m m',
  alloc_globals m gl = Some m' ->
  Mem.valid_block m b' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  induction gl.
  simpl; intros. inv H. tauto.
  simpl; intros. destruct (alloc_global m a) as [m1|] eqn:?; try discriminate.
  erewrite alloc_global_perm; eauto. eapply IHgl; eauto. 
  unfold Mem.valid_block in *. erewrite alloc_global_nextblock; eauto.
  apply Plt_trans_succ; auto.
Qed.

(** Data preservation properties *)

Remark store_zeros_outside:
  forall m b p n m',
  store_zeros m b p n = Some m' ->
  forall chunk b' p',
  b' <> b \/ p' + size_chunk chunk <= p \/ p + n <= p' ->
  Mem.load chunk m' b' p' = Mem.load chunk m b' p'.
Proof.
  intros until n. functional induction (store_zeros m b p n); intros.
  inv H; auto.
  transitivity (Mem.load chunk m' b' p'). 
  apply IHo. auto. intuition omega. 
  eapply Mem.load_store_other; eauto. simpl. intuition omega. 
  discriminate.
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
  intros. destruct (store_init_data m b p a) as [m1|] eqn:?; try congruence.
  transitivity (Mem.load chunk m1 b' q).
  eapply IHil; eauto. generalize (init_data_size_pos a). intuition omega.
  destruct a; simpl in Heqo;
  try (eapply Mem.load_store_other; eauto; intuition; fail).
  inv Heqo. auto.
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
  | Init_int64 n :: il' =>
      Mem.load Mint64 m b p = Some(Vlong n)
      /\ load_store_init_data m b (p + 8) il'
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
    Mem.load chunk m' b p = Some(Val.load_result chunk v)).
  intros. transitivity (Mem.load chunk m1 b p).
  eapply store_init_data_list_outside; eauto. right. omega. 
  eapply Mem.load_store_same; eauto. 

  induction il; simpl.
  auto.
  intros. destruct (store_init_data m b p a) as [m1|] eqn:?; try congruence.
  exploit IHil; eauto. intro D. 
  destruct a; simpl in Heqo; intuition.
  eapply (A Mint8unsigned (Vint i)); eauto.
  eapply (A Mint16unsigned (Vint i)); eauto.
  eapply (A Mint32 (Vint i)); eauto.
  eapply (A Mint64 (Vlong i)); eauto.
  eapply (A Mfloat32 (Vfloat f)); eauto.
  eapply (A Mfloat64 (Vfloat f)); eauto.
  destruct (find_symbol ge i); try congruence. exists b0; split; auto. 
  eapply (A Mint32 (Vptr b0 i0)); eauto. 
Qed.

Remark load_alloc_global:
  forall chunk b p id g m m',
  alloc_global m (id, g) = Some m' ->
  Mem.valid_block m b ->
  Mem.load chunk m' b p = Mem.load chunk m b p.
Proof.
  intros. destruct g as [f|v]; simpl in H.
  (* function *)
  destruct (Mem.alloc m 0 1) as [m1 b'] eqn:?. 
  assert (b <> b'). apply Mem.valid_not_valid_diff with m; eauto with mem.
  transitivity (Mem.load chunk m1 b p). 
  eapply Mem.load_drop; eauto. 
  eapply Mem.load_alloc_unchanged; eauto.
  (* variable *)
  set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b'] eqn:?.
  destruct (store_zeros m1 b' 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list m2 b' 0 init) as [m3|] eqn:?; try discriminate.
  assert (b <> b'). apply Mem.valid_not_valid_diff with m; eauto with mem.
  transitivity (Mem.load chunk m3 b p). 
  eapply Mem.load_drop; eauto.
  transitivity (Mem.load chunk m2 b p).
  eapply store_init_data_list_outside; eauto. 
  transitivity (Mem.load chunk m1 b p).
  eapply store_zeros_outside; eauto.
  eapply Mem.load_alloc_unchanged; eauto.
Qed.

Remark load_alloc_globals:
  forall chunk b p gl m m',
  alloc_globals m gl = Some m' ->
  Mem.valid_block m b ->
  Mem.load chunk m' b p = Mem.load chunk m b p.
Proof.
  induction gl; simpl; intros.
  congruence.
  destruct (alloc_global m a) as [m''|] eqn:?; try discriminate.
  transitivity (Mem.load chunk m'' b p). 
  apply IHgl; auto. unfold Mem.valid_block in *. 
  erewrite alloc_global_nextblock; eauto. 
  apply Plt_trans with (Mem.nextblock m); auto. apply Plt_succ.
  destruct a as [id g]. eapply load_alloc_global; eauto. 
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

Definition functions_initialized (g: t) (m: mem) :=
  forall b fd,
  find_funct_ptr g b = Some fd ->
  Mem.perm m b 0 Cur Nonempty
  /\ (forall ofs k p, Mem.perm m b ofs k p -> ofs = 0 /\ perm_order Nonempty p).

Lemma alloc_global_initialized:
  forall ge m id g m',
  genv_next ge = Mem.nextblock m ->
  alloc_global m (id, g) = Some m' ->
  variables_initialized ge m ->
  functions_initialized ge m ->
  variables_initialized (add_global ge (id, g)) m'
  /\ functions_initialized (add_global ge (id, g)) m'
  /\ genv_next (add_global ge (id, g)) = Mem.nextblock m'.
Proof.
  intros. 
  exploit alloc_global_nextblock; eauto. intros NB. split.
(* variables-initialized *)
  destruct g as [f|v].
(* function *)
  red; intros. unfold find_var_info in H3. simpl in H3. 
  exploit H1; eauto. intros [A [B C]].
  assert (D: Mem.valid_block m b). 
    red. exploit genv_vars_range; eauto. rewrite H; auto.
  split. red; intros. erewrite <- alloc_global_perm; eauto. 
  split. intros. eapply B. erewrite alloc_global_perm; eauto. 
  intros. apply load_store_init_data_invariant with m; auto. 
  intros. eapply load_alloc_global; eauto. 
(* variable *)
  red; intros. unfold find_var_info in H3. simpl in H3. rewrite PTree.gsspec in H3.
  destruct (peq b (genv_next ge0)).
  (* same *)
  inv H3. simpl in H0.
  set (init := gvar_init gv) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b'] eqn:?.
  destruct (store_zeros m1 b' 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list m2 b' 0 init) as [m3|] eqn:?; try discriminate.
  exploit Mem.alloc_result; eauto. intro RES. 
  replace (genv_next ge0) with b' by congruence.
  split. red; intros. eapply Mem.perm_drop_1; eauto.
  split. intros.
  assert (0 <= ofs < sz).
    eapply Mem.perm_alloc_3; eauto.
    erewrite store_zeros_perm; [idtac|eauto].
    erewrite store_init_data_list_perm; [idtac|eauto]. 
    eapply Mem.perm_drop_4; eauto.
  split. auto. eapply Mem.perm_drop_2; eauto.
  intros. apply load_store_init_data_invariant with m3. 
  intros. eapply Mem.load_drop; eauto. 
  right; right; right. unfold perm_globvar. rewrite H3. 
  destruct (gvar_readonly gv); auto with mem.
  eapply store_init_data_list_charact; eauto.
  (* older var *)
  exploit H1; eauto. intros [A [B C]].
  assert (D: Mem.valid_block m b). 
    red. exploit genv_vars_range; eauto. rewrite H; auto. 
  split. red; intros. erewrite <- alloc_global_perm; eauto. 
  split. intros. eapply B. erewrite alloc_global_perm; eauto. 
  intros. apply load_store_init_data_invariant with m; auto. 
  intros. eapply load_alloc_global; eauto.
(* functions-initialized *)
  split. destruct g as [f|v].
(* function *)
  red; intros. unfold find_funct_ptr in H3. simpl in H3. rewrite PTree.gsspec in H3.
  destruct (peq b (genv_next ge0)).
  (* same *)
  inv H3. simpl in H0. 
  destruct (Mem.alloc m 0 1) as [m1 b'] eqn:?. 
  exploit Mem.alloc_result; eauto. intro RES. 
  replace (genv_next ge0) with b' by congruence.
  split. eapply Mem.perm_drop_1; eauto. omega. 
  intros.
  assert (0 <= ofs < 1).
    eapply Mem.perm_alloc_3; eauto.
    eapply Mem.perm_drop_4; eauto.
  split. omega. eapply Mem.perm_drop_2; eauto.
  (* older function *)
  exploit H2; eauto. intros [A B].
  assert (D: Mem.valid_block m b). 
    red. exploit genv_funs_range; eauto. rewrite H; auto.
  split. erewrite <- alloc_global_perm; eauto. 
  intros. eapply B. erewrite alloc_global_perm; eauto.
(* variables *)
  red; intros. unfold find_funct_ptr in H3. simpl in H3. 
  exploit H2; eauto. intros [A B].
  assert (D: Mem.valid_block m b). 
    red. exploit genv_funs_range; eauto. rewrite H; auto.
  split. erewrite <- alloc_global_perm; eauto. 
  intros. eapply B. erewrite alloc_global_perm; eauto.
(* nextblock *)
  rewrite NB. simpl. rewrite H. auto.
Qed.

Lemma alloc_globals_initialized:
  forall gl ge m m',
  genv_next ge = Mem.nextblock m ->
  alloc_globals m gl = Some m' ->
  variables_initialized ge m ->
  functions_initialized ge m ->
  variables_initialized (add_globals ge gl) m' /\ functions_initialized (add_globals ge gl) m'.
Proof.
  induction gl; simpl; intros.
  inv H0; auto.
  destruct a as [id g]. destruct (alloc_global m (id, g)) as [m1|] eqn:?; try discriminate.
  exploit alloc_global_initialized; eauto. intros [P [Q R]].
  eapply IHgl; eauto. 
Qed.

End INITMEM.

Definition init_mem (p: program F V) :=
  alloc_globals (globalenv p) Mem.empty p.(prog_defs).

Lemma init_mem_genv_next: forall p m,
  init_mem p = Some m -> 
  genv_next (globalenv p) = Mem.nextblock m.
Proof.
  unfold init_mem; intros.
  exploit alloc_globals_nextblock; eauto. rewrite Mem.nextblock_empty. intro.
  generalize (genv_next_add_globals (prog_defs p) empty_genv). 
  fold (globalenv p). simpl genv_next. intros. congruence.
Qed.

Theorem find_symbol_not_fresh:
  forall p id b m,
  init_mem p = Some m ->
  find_symbol (globalenv p) id = Some b -> Mem.valid_block m b.
Proof.
  intros. red. erewrite <- init_mem_genv_next; eauto. 
  eapply genv_symb_range; eauto.
Qed.

Theorem find_funct_ptr_not_fresh:
  forall p b f m,
  init_mem p = Some m ->
  find_funct_ptr (globalenv p) b = Some f -> Mem.valid_block m b.
Proof.
  intros. red. erewrite <- init_mem_genv_next; eauto. 
  eapply genv_funs_range; eauto.
Qed.

Theorem find_var_info_not_fresh:
  forall p b gv m,
  init_mem p = Some m ->
  find_var_info (globalenv p) b = Some gv -> Mem.valid_block m b.
Proof.
  intros. red. erewrite <- init_mem_genv_next; eauto. 
  eapply genv_vars_range; eauto.
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
  intros. eapply alloc_globals_initialized; eauto.
  rewrite Mem.nextblock_empty. auto. 
  red; intros. unfold find_var_info in H1. simpl in H1. rewrite PTree.gempty in H1. congruence.
  red; intros. unfold find_funct_ptr in H1. simpl in H1. rewrite PTree.gempty in H1. congruence.
Qed.

Theorem init_mem_characterization_2:
  forall p b fd m,
  find_funct_ptr (globalenv p) b = Some fd ->
  init_mem p = Some m ->
  Mem.perm m b 0 Cur Nonempty
  /\ (forall ofs k p, Mem.perm m b ofs k p -> ofs = 0 /\ perm_order Nonempty p).
Proof.
  intros. unfold init_mem in H0. eapply alloc_globals_initialized; eauto.
  rewrite Mem.nextblock_empty. auto.
  red; intros. unfold find_var_info in H1. simpl in H1. rewrite PTree.gempty in H1. congruence.
  red; intros. unfold find_funct_ptr in H1. simpl in H1. rewrite PTree.gempty in H1. congruence.
Qed.

(** ** Compatibility with memory injections *)

Section INITMEM_INJ.

Variable ge: t.
Variable thr: block.
Hypothesis symb_inject: forall id b, find_symbol ge id = Some b -> Plt b thr.

Lemma store_zeros_neutral:
  forall m b p n m',
  Mem.inject_neutral thr m ->
  Plt b thr ->
  store_zeros m b p n = Some m' ->
  Mem.inject_neutral thr m'.
Proof.
  intros until n. functional induction (store_zeros m b p n); intros.
  inv H1; auto.
  apply IHo; auto. eapply Mem.store_inject_neutral; eauto. constructor.  
  inv H1.
Qed.

Lemma store_init_data_neutral:
  forall m b p id m',
  Mem.inject_neutral thr m ->
  Plt b thr ->
  store_init_data ge m b p id = Some m' ->
  Mem.inject_neutral thr m'.
Proof.
  intros.
  destruct id; simpl in H1; try (eapply Mem.store_inject_neutral; eauto; fail).
  congruence.
  destruct (find_symbol ge i) as [b'|] eqn:E; try discriminate.
  eapply Mem.store_inject_neutral; eauto. 
  econstructor. unfold Mem.flat_inj. apply pred_dec_true; auto. eauto.  
  rewrite Int.add_zero. auto. 
Qed.

Lemma store_init_data_list_neutral:
  forall b idl m p m',
  Mem.inject_neutral thr m ->
  Plt b thr ->
  store_init_data_list ge m b p idl = Some m' ->
  Mem.inject_neutral thr m'.
Proof.
  induction idl; simpl; intros.
  congruence.
  destruct (store_init_data ge m b p a) as [m1|] eqn:E; try discriminate.
  eapply IHidl. eapply store_init_data_neutral; eauto. auto. eauto. 
Qed.

Lemma alloc_global_neutral:
  forall idg m m',
  alloc_global ge m idg = Some m' ->
  Mem.inject_neutral thr m ->
  Plt (Mem.nextblock m) thr ->
  Mem.inject_neutral thr m'.
Proof.
  intros. destruct idg as [id [f|v]]; simpl in H.
  (* function *)
  destruct (Mem.alloc m 0 1) as [m1 b] eqn:?.
  assert (Plt b thr). rewrite (Mem.alloc_result _ _ _ _ _ Heqp). auto.
  eapply Mem.drop_inject_neutral; eauto. 
  eapply Mem.alloc_inject_neutral; eauto.
  (* variable *)
  set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:?.
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list ge m2 b 0 init) as [m3|] eqn:?; try discriminate.
  assert (Plt b thr). rewrite (Mem.alloc_result _ _ _ _ _ Heqp). auto.
  eapply Mem.drop_inject_neutral; eauto. 
  eapply store_init_data_list_neutral with (m := m2) (b := b); eauto.
  eapply store_zeros_neutral with (m := m1); eauto. 
  eapply Mem.alloc_inject_neutral; eauto.
Qed.

Remark advance_next_le: forall gl x, Ple x (advance_next gl x).
Proof.
  induction gl; simpl; intros.
  apply Ple_refl.
  apply Ple_trans with (Psucc x). apply Ple_succ. eauto.
Qed.

Lemma alloc_globals_neutral:
  forall gl m m',
  alloc_globals ge m gl = Some m' ->
  Mem.inject_neutral thr m ->
  Ple (Mem.nextblock m') thr ->
  Mem.inject_neutral thr m'.
Proof.
  induction gl; intros.
  simpl in *. congruence.
  exploit alloc_globals_nextblock; eauto. intros EQ. 
  simpl in *. destruct (alloc_global ge m a) as [m1|] eqn:E; try discriminate.
  exploit alloc_global_neutral; eauto.
  assert (Ple (Psucc (Mem.nextblock m)) (Mem.nextblock m')).
  { rewrite EQ. apply advance_next_le. }
  unfold Plt, Ple in *; zify; omega.
Qed.

End INITMEM_INJ.

Theorem initmem_inject:
  forall p m,
  init_mem p = Some m ->
  Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m.
Proof.
  unfold init_mem; intros.
  apply Mem.neutral_inject. 
  eapply alloc_globals_neutral; eauto. 
  intros. exploit find_symbol_not_fresh; eauto.
  apply Mem.empty_inject_neutral.
  apply Ple_refl.
Qed.

Section INITMEM_AUGMENT_INJ. 

Variable ge: t.
Variable thr: block.

Lemma store_zeros_augment:
  forall m1 m2 b p n m2',
  Mem.inject (Mem.flat_inj thr) m1 m2 ->
  Ple thr b ->
  store_zeros m2 b p n = Some m2' ->
  Mem.inject (Mem.flat_inj thr) m1 m2'.
Proof.
  intros until n. functional induction (store_zeros m2 b p n); intros.
  inv H1; auto.
  apply IHo; auto. exploit Mem.store_outside_inject; eauto. simpl. 
  intros. exfalso. unfold Mem.flat_inj in H2. destruct (plt b' thr). 
  inv H2. unfold Plt, Ple in *. zify; omega.
  discriminate.
  discriminate.
Qed.

Lemma store_init_data_augment: 
  forall m1 m2 b p id m2', 
  Mem.inject (Mem.flat_inj thr) m1 m2 -> 
  Ple thr b -> 
  store_init_data ge m2 b p id = Some m2' ->
  Mem.inject (Mem.flat_inj thr) m1 m2'.
Proof. 
  intros until m2'. intros INJ BND ST. 
  assert (P: forall chunk ofs v m2', 
             Mem.store chunk m2 b ofs v = Some m2' -> 
             Mem.inject (Mem.flat_inj thr) m1 m2'). 
    intros. eapply Mem.store_outside_inject; eauto. 
    intros. unfold Mem.flat_inj in H0.
    destruct (plt b' thr); inv H0. unfold Plt, Ple in *. zify; omega.
  destruct id; simpl in ST; try (eapply P; eauto; fail).
  congruence.
  revert ST.  caseEq (find_symbol ge i); try congruence. intros; eapply P; eauto. 
Qed.

Lemma store_init_data_list_augment:
  forall b idl m1 m2 p m2', 
  Mem.inject (Mem.flat_inj thr) m1 m2 -> 
  Ple thr b -> 
  store_init_data_list ge m2 b p idl = Some m2' ->
  Mem.inject (Mem.flat_inj thr) m1 m2'.
Proof. 
  induction idl; simpl.
  intros; congruence.
  intros until m2'; intros INJ FB.
  caseEq (store_init_data ge m2 b p a); try congruence. intros. 
  eapply IHidl. eapply store_init_data_augment; eauto. auto. eauto. 
Qed.

Lemma alloc_global_augment:
  forall idg m1 m2 m2',
  alloc_global ge m2 idg = Some m2' ->
  Mem.inject (Mem.flat_inj thr) m1 m2 -> 
  Ple thr (Mem.nextblock m2) -> 
  Mem.inject (Mem.flat_inj thr) m1 m2'.
Proof.
  intros. destruct idg as [id [f|v]]; simpl in H.
  (* function *)
  destruct (Mem.alloc m2 0 1) as [m3 b] eqn:?.
  assert (Ple thr b). rewrite (Mem.alloc_result _ _ _ _ _ Heqp). auto.
  eapply Mem.drop_outside_inject. 2: eauto. 
  eapply Mem.alloc_right_inject; eauto.
  intros. unfold Mem.flat_inj in H3. destruct (plt b' thr); inv H3.
  unfold Plt, Ple in *. zify; omega.
  (* variable *)
  set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m2 0 sz) as [m3 b] eqn:?.
  destruct (store_zeros m3 b 0 sz) as [m4|] eqn:?; try discriminate.
  destruct (store_init_data_list ge m4 b 0 init) as [m5|] eqn:?; try discriminate.
  assert (Ple thr b). rewrite (Mem.alloc_result _ _ _ _ _ Heqp). auto.
  eapply Mem.drop_outside_inject. 2: eauto. 
  eapply store_init_data_list_augment. 3: eauto. 2: eauto.
  eapply store_zeros_augment. 3: eauto. 2: eauto.
  eapply Mem.alloc_right_inject; eauto.
  intros. unfold Mem.flat_inj in H3. destruct (plt b' thr); inv H3.
  unfold Plt, Ple in *. zify; omega.
Qed.

Lemma alloc_globals_augment:
  forall gl m1 m2 m2',
  alloc_globals ge m2 gl = Some m2' ->
  Mem.inject (Mem.flat_inj thr) m1 m2 ->
  Ple thr (Mem.nextblock m2) ->
  Mem.inject (Mem.flat_inj thr) m1 m2'.
Proof.
  induction gl; simpl.
  intros. congruence.
  intros until m2'. caseEq (alloc_global ge m2 a); try congruence. intros.
  eapply IHgl with (m2 := m); eauto.  
    eapply alloc_global_augment; eauto. 
    rewrite (alloc_global_nextblock _ _ _ H). 
    apply Ple_trans with (Mem.nextblock m2); auto. apply Ple_succ.
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

Record match_genvs (new_globs : list (ident * globdef B W)) 
                   (ge1: t A V) (ge2: t B W): Prop := {
  mge_next:
    genv_next ge2 = advance_next new_globs (genv_next ge1);
  mge_symb:
    forall id, ~ In id (map fst new_globs) ->
                   PTree.get id (genv_symb ge2) = PTree.get id (genv_symb ge1);
  mge_funs:
    forall b f, PTree.get b (genv_funs ge1) = Some f ->
    exists tf, PTree.get b (genv_funs ge2) = Some tf /\ match_fun f tf;
  mge_rev_funs:
    forall b tf, PTree.get b (genv_funs ge2) = Some tf ->
    if plt b (genv_next ge1) then 
      exists f, PTree.get b (genv_funs ge1) = Some f /\ match_fun f tf
    else 
      In (Gfun tf) (map snd new_globs);
  mge_vars:
    forall b v, PTree.get b (genv_vars ge1) = Some v ->
    exists tv, PTree.get b (genv_vars ge2) = Some tv /\ match_globvar v tv;
  mge_rev_vars:
    forall b tv, PTree.get b (genv_vars ge2) = Some tv ->
    if plt b (genv_next ge1) then
      exists v, PTree.get b (genv_vars ge1) = Some v /\ match_globvar v tv
    else
      In (Gvar tv) (map snd new_globs)
}.

Lemma add_global_match:
  forall ge1 ge2 idg1 idg2,
  match_genvs nil ge1 ge2 ->
  match_globdef match_fun match_varinfo idg1 idg2 ->
  match_genvs nil (add_global ge1 idg1) (add_global ge2 idg2).
Proof.
  intros. destruct H. simpl in mge_next0.
  inv H0.
(* two functions *)
  constructor; simpl.
  congruence.
  intros. rewrite mge_next0. 
    repeat rewrite PTree.gsspec. destruct (peq id0 id); auto.
  rewrite mge_next0. intros. rewrite PTree.gsspec in H0. rewrite PTree.gsspec. 
    destruct (peq b (genv_next ge1)). 
     exists f2; split; congruence.
     eauto.
  rewrite mge_next0. intros. rewrite PTree.gsspec in H0. rewrite PTree.gsspec. 
   destruct (peq b (genv_next ge1)). 
    subst b. rewrite pred_dec_true. exists f1; split; congruence. apply Plt_succ.
    pose proof (mge_rev_funs0 b tf H0). 
    destruct (plt b (genv_next ge1)). rewrite pred_dec_true. auto. apply Plt_trans_succ; auto.
    contradiction.
  eauto.
  intros.
    pose proof (mge_rev_vars0 b tv H0). 
    destruct (plt b (genv_next ge1)). rewrite pred_dec_true. auto.
    apply Plt_trans with (genv_next ge1); auto. apply Plt_succ.
    contradiction.
(* two variables *)
  constructor; simpl.
  congruence.
  intros. rewrite mge_next0. 
    repeat rewrite PTree.gsspec. destruct (peq id0 id); auto.
  eauto.
  intros.
    pose proof (mge_rev_funs0 b tf H0). 
    destruct (plt b (genv_next ge1)). rewrite pred_dec_true. auto. apply Plt_trans_succ; auto.
    contradiction.
  rewrite mge_next0. intros. rewrite PTree.gsspec in H0. rewrite PTree.gsspec. 
    destruct (peq b (genv_next ge1)).
    econstructor; split. eauto. inv H0. constructor; auto. 
    eauto.
  rewrite mge_next0. intros. rewrite PTree.gsspec in H0. rewrite PTree.gsspec. 
   destruct (peq b (genv_next ge1)). 
    subst b. rewrite pred_dec_true.
    econstructor; split. eauto. inv H0. constructor; auto. apply Plt_succ.
    pose proof (mge_rev_vars0 b tv H0). 
    destruct (plt b (genv_next ge1)). rewrite pred_dec_true. auto. apply Plt_trans_succ; auto.
    contradiction.
Qed.

Lemma add_globals_match:
  forall gl1 gl2, list_forall2 (match_globdef match_fun match_varinfo) gl1 gl2 ->
  forall ge1 ge2, match_genvs nil ge1 ge2 ->
  match_genvs nil (add_globals ge1 gl1) (add_globals ge2 gl2).
Proof.
  induction 1; intros; simpl. 
  auto.
  apply IHlist_forall2. apply add_global_match; auto.
Qed.

Lemma add_global_augment_match: 
  forall new_globs ge1 ge2 idg,
  match_genvs new_globs ge1 ge2 ->
  match_genvs (new_globs ++ (idg :: nil)) ge1 (add_global ge2 idg).
Proof.
  intros. destruct H. 
  assert (LE: Ple (genv_next ge1) (genv_next ge2)).
  { rewrite mge_next0; apply advance_next_le. }
  constructor; simpl.
  rewrite mge_next0. unfold advance_next. rewrite fold_left_app. simpl. auto.
  intros. rewrite map_app in H. rewrite in_app in H. simpl in H. 
    destruct (peq id idg#1). subst. intuition. rewrite PTree.gso. 
    apply mge_symb0. intuition. auto. 
  intros. destruct idg as [id1 [f1|v1]]; simpl; eauto.
    rewrite PTree.gso. eauto.
    exploit genv_funs_range; eauto. intros.
    unfold Plt, Ple in *; zify; omega.
  intros. rewrite map_app. destruct idg as [id1 [f1|v1]]; simpl in H.
    rewrite PTree.gsspec in H. destruct (peq b (genv_next ge2)). 
    rewrite pred_dec_false. rewrite in_app. simpl; right; left. congruence.
    subst b. unfold Plt, Ple in *; zify; omega.
    exploit mge_rev_funs0; eauto. destruct (plt b (genv_next ge1)); auto. 
    rewrite in_app. tauto.
    exploit mge_rev_funs0; eauto. destruct (plt b (genv_next ge1)); auto. 
    rewrite in_app. tauto.
  intros. destruct idg as [id1 [f1|v1]]; simpl; eauto.
    rewrite PTree.gso. eauto. exploit genv_vars_range; eauto. 
    unfold Plt, Ple in *; zify; omega.
  intros. rewrite map_app. destruct idg as [id1 [f1|v1]]; simpl in H.
    exploit mge_rev_vars0; eauto. destruct (plt b (genv_next ge1)); auto. 
    rewrite in_app. tauto.
    rewrite PTree.gsspec in H. destruct (peq b (genv_next ge2)). 
    rewrite pred_dec_false. rewrite in_app. simpl; right; left. congruence.
    subst b. unfold Plt, Ple in *; zify; omega.
    exploit mge_rev_vars0; eauto. destruct (plt b (genv_next ge1)); auto. 
    rewrite in_app. tauto.
Qed.

Lemma add_globals_augment_match: 
  forall gl new_globs ge1 ge2,
  match_genvs new_globs ge1 ge2 ->
  match_genvs (new_globs ++ gl) ge1 (add_globals ge2 gl).
Proof.
  induction gl; simpl. 
    intros. rewrite app_nil_r. auto. 
    intros. change (a :: gl) with ((a :: nil) ++ gl). rewrite <- app_ass.
      apply IHgl. apply add_global_augment_match. auto.
Qed.

Variable new_globs : list (ident * globdef B W).
Variable new_main : ident.

Variable p: program A V.
Variable p': program B W.
Hypothesis progmatch: 
  match_program match_fun match_varinfo new_globs new_main p p'.

Lemma globalenvs_match:
  match_genvs new_globs (globalenv p) (globalenv p').
Proof.
  unfold globalenv. destruct progmatch as [[tglob [P Q]] R].
  rewrite Q. rewrite add_globals_app. 
  change new_globs with (nil ++ new_globs) at 1. 
  apply add_globals_augment_match.
  apply add_globals_match; auto.
  constructor; simpl; auto; intros; rewrite PTree.gempty in H; congruence.
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
  if plt b (genv_next (globalenv p)) then 
      exists f, find_funct_ptr (globalenv p) b = Some f /\ match_fun f tf
  else 
      In (Gfun tf) (map snd new_globs).
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
  \/ (In (Gfun tf) (map snd new_globs)).
Proof.
  intros. exploit find_funct_inv; eauto. intros [b EQ]. subst v. 
  rewrite find_funct_find_funct_ptr in H. 
  rewrite find_funct_find_funct_ptr.
  apply find_funct_ptr_rev_match in H. 
   destruct (plt b (genv_next (globalenv p))); auto.
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
  if plt b (genv_next (globalenv p)) then 
    exists v, find_var_info (globalenv p) b = Some v /\ match_globvar v tv
  else
    In (Gvar tv) (map snd new_globs).
Proof (mge_rev_vars globalenvs_match).

Theorem find_symbol_match:
  forall (s : ident),
  ~In s (map fst new_globs) ->
  find_symbol (globalenv p') s = find_symbol (globalenv p) s.
Proof.
  intros. destruct globalenvs_match. unfold find_symbol.  auto. 
Qed.

Hypothesis new_ids_fresh : 
  forall s', find_symbol (globalenv p) s' <> None  -> 
             ~In s' (map fst new_globs).

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
   simpl in H. destruct (find_symbol (globalenv p) i) as [b'|] eqn:?; try discriminate.
   apply new_ids_fresh. congruence.
  case_eq (store_init_data (globalenv p) m b ofs a); intros. 
    rewrite H1 in H. 
    pose proof (H0 _ H1). rewrite H2. auto. 
    rewrite H1 in H. inversion H. 
Qed.

Lemma alloc_globals_match:
  forall gl1 gl2, list_forall2 (match_globdef match_fun match_varinfo) gl1 gl2 ->
  forall m m',
  alloc_globals (globalenv p) m gl1 = Some m' -> 
  alloc_globals (globalenv p') m gl2 = Some m'.
Proof.
  induction 1; simpl; intros.
  auto.
  destruct (alloc_global (globalenv p) m a1) as [m1|] eqn:?; try discriminate.
  assert (alloc_global (globalenv p') m b1 = Some m1).
    inv H; simpl in *. 
    auto.
    set (sz := init_data_list_size init) in *.
    destruct (Mem.alloc m 0 sz) as [m2 b] eqn:?.
    destruct (store_zeros m2 b 0 sz) as [m3|] eqn:?; try discriminate.
    destruct (store_init_data_list (globalenv p) m3 b 0 init) as [m4|] eqn:?; try discriminate.
    erewrite store_init_data_list_match; eauto. 
  rewrite H2. eauto.
Qed.

Theorem init_mem_match:
  forall m, init_mem p = Some m -> 
  init_mem p' = alloc_globals (globalenv p') m new_globs.
Proof.
  unfold init_mem; intros.
  destruct progmatch as [[tglob [P Q]] R].
  rewrite Q. erewrite <- alloc_globals_app; eauto. 
  eapply alloc_globals_match; eauto. 
Qed.

End MATCH_PROGRAMS.

Section TRANSF_PROGRAM_AUGMENT.

Variable A B V W: Type.
Variable transf_fun: A -> res B.
Variable transf_var: V -> res W.

Variable new_globs : list (ident * globdef B W).
Variable new_main : ident.

Variable p: program A V.
Variable p': program B W.

Hypothesis transf_OK:
  transform_partial_augment_program transf_fun transf_var new_globs new_main p = OK p'.

Remark prog_match:
  match_program
    (fun fd tfd => transf_fun fd = OK tfd)
    (fun info tinfo => transf_var info = OK tinfo)
    new_globs new_main
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

Theorem find_new_funct_ptr_exists: 
  list_norepet (List.map fst new_globs) ->
  forall id f, In (id, Gfun f) new_globs -> 
  exists b, find_symbol (globalenv p') id = Some b
         /\ find_funct_ptr (globalenv p') b = Some f.
Proof.
  intros. destruct prog_match as [[tglob [P Q]] R]. 
  unfold globalenv. rewrite Q. rewrite add_globals_app. 
  eapply add_globals_norepet_ensures; eauto.
(* preserves *)
  intros. unfold find_symbol, find_funct_ptr in *; simpl.
  destruct H1 as [b [X Y]]. exists b; split.
  rewrite PTree.gso; auto.
  destruct g1 as [f1 | v1]. rewrite PTree.gso. auto.
  apply Plt_ne. eapply genv_funs_range; eauto.
  auto. 
(* ensures *)
  intros. unfold find_symbol, find_funct_ptr in *; simpl.
  exists (genv_next ge); split. apply PTree.gss. apply PTree.gss. 
Qed.

Theorem find_funct_ptr_rev_transf_augment:
  forall (b: block) (tf: B),
  find_funct_ptr (globalenv p') b = Some tf ->
  if plt b (genv_next (globalenv p)) then
   (exists f, find_funct_ptr (globalenv p) b = Some f /\ transf_fun f = OK tf)
  else 
   In (Gfun tf) (map snd new_globs).
Proof.
  intros. 
  exploit find_funct_ptr_rev_match; eauto. eexact prog_match; eauto. auto. 
Qed.

Theorem find_funct_transf_augment:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  exists f',
  find_funct (globalenv p') v = Some f' /\ transf_fun f = OK f'.
Proof.
  intros. 
  exploit find_funct_match. eexact prog_match. eauto. auto. 
Qed.

Theorem find_funct_rev_transf_augment: 
  forall (v: val) (tf: B),
  find_funct (globalenv p') v = Some tf ->
  (exists f, find_funct (globalenv p) v = Some f /\ transf_fun f = OK tf) \/
  In (Gfun tf) (map snd new_globs).
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
  exploit find_var_info_match. eexact prog_match. eauto. intros [tv [X Y]]. 
  exists tv; split; auto. inv Y. unfold transf_globvar; simpl.
  rewrite H0; simpl. auto.
Qed.

Theorem find_new_var_exists:
  list_norepet (List.map fst new_globs) ->
  forall id gv, In (id, Gvar gv) new_globs -> 
  exists b, find_symbol (globalenv p') id = Some b
         /\ find_var_info (globalenv p') b = Some gv.
Proof.
  intros. destruct prog_match as [[tglob [P Q]] R]. 
  unfold globalenv. rewrite Q. rewrite add_globals_app. 
  eapply add_globals_norepet_ensures; eauto.
(* preserves *)
  intros. unfold find_symbol, find_var_info in *; simpl.
  destruct H1 as [b [X Y]]. exists b; split.
  rewrite PTree.gso; auto.
  destruct g1 as [f1 | v1]. auto. rewrite PTree.gso. auto.
  red; intros; subst b. eelim Plt_strict. eapply genv_vars_range; eauto.
(* ensures *)
  intros. unfold find_symbol, find_var_info in *; simpl.
  exists (genv_next ge); split. apply PTree.gss. apply PTree.gss. 
Qed.

Theorem find_var_info_rev_transf_augment:
  forall (b: block) (v': globvar W),
  find_var_info (globalenv p') b = Some v' ->
  if plt b (genv_next (globalenv p)) then
    (exists v, find_var_info (globalenv p) b = Some v /\ transf_globvar transf_var v = OK v')
  else
    (In (Gvar v') (map snd new_globs)).
Proof.
  intros. 
  exploit find_var_info_rev_match. eexact prog_match. eauto.
  destruct (plt b (genv_next (globalenv p))); auto.
  intros [v [X Y]]. exists v; split; auto. inv Y. unfold transf_globvar; simpl. 
  rewrite H0; simpl. auto.
Qed.

Theorem find_symbol_transf_augment:  
  forall (s: ident), 
  ~ In s (map fst new_globs) ->
  find_symbol (globalenv p') s = find_symbol (globalenv p) s.
Proof.
  intros. eapply find_symbol_match. eexact prog_match. auto.
Qed.

Theorem init_mem_transf_augment: 
   (forall s', find_symbol (globalenv p) s' <> None -> 
     ~ In s' (map fst new_globs)) ->
   forall m, init_mem p = Some m -> 
   init_mem p' = alloc_globals (globalenv p') m new_globs.
Proof.
  intros. eapply init_mem_match. eexact prog_match. auto. auto.
Qed.
 
Theorem init_mem_inject_transf_augment:
   (forall s', find_symbol (globalenv p) s' <> None -> 
     ~ In s' (map fst new_globs)) ->
  forall m, init_mem p = Some m ->
  forall m', init_mem p' = Some m' -> 
  Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m'.
Proof.
  intros. 
  pose proof (initmem_inject p H0). 
  erewrite init_mem_transf_augment in H1; eauto. 
  eapply alloc_globals_augment; eauto. apply Ple_refl. 
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
  transform_partial_augment_program transf_fun transf_var nil p.(prog_main) p = OK p'.
Proof.
  rewrite <- transf_OK. symmetry. apply transform_partial_program2_augment.
Qed.

Theorem find_funct_ptr_transf_partial2:
  forall (b: block) (f: A),
  find_funct_ptr (globalenv p) b = Some f ->
  exists f',
  find_funct_ptr (globalenv p') b = Some f' /\ transf_fun f = OK f'.
Proof.
  exact (@find_funct_ptr_transf_augment _ _ _ _ _ _ _ _ _ _ transf_augment_OK).
Qed.

Theorem find_funct_ptr_rev_transf_partial2:
  forall (b: block) (tf: B),
  find_funct_ptr (globalenv p') b = Some tf ->
  exists f, find_funct_ptr (globalenv p) b = Some f /\ transf_fun f = OK tf.
Proof.
  pose proof (@find_funct_ptr_rev_transf_augment _ _ _ _ _ _ _ _ _ _ transf_augment_OK).
  intros.  pose proof (H b tf H0). 
  destruct (plt b (genv_next (globalenv p))).  auto. contradiction.
Qed.

Theorem find_funct_transf_partial2:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  exists f',
  find_funct (globalenv p') v = Some f' /\ transf_fun f = OK f'.
Proof.
  exact (@find_funct_transf_augment _ _ _ _ _ _ _ _ _ _ transf_augment_OK).
Qed.

Theorem find_funct_rev_transf_partial2:
  forall (v: val) (tf: B),
  find_funct (globalenv p') v = Some tf ->
  exists f, find_funct (globalenv p) v = Some f /\ transf_fun f = OK tf.
Proof.
  pose proof (@find_funct_rev_transf_augment _ _ _ _ _ _ _ _ _ _ transf_augment_OK).
  intros. pose proof (H v tf H0). 
  destruct H1. auto. contradiction.
Qed.

Theorem find_var_info_transf_partial2:
  forall (b: block) (v: globvar V),
  find_var_info (globalenv p) b = Some v ->
  exists v',
  find_var_info (globalenv p') b = Some v' /\ transf_globvar transf_var v = OK v'.
Proof.
  exact (@find_var_info_transf_augment _ _ _ _ _ _ _ _ _ _ transf_augment_OK).
Qed.

Theorem find_var_info_rev_transf_partial2:
  forall (b: block) (v': globvar W),
  find_var_info (globalenv p') b = Some v' ->
  exists v,
  find_var_info (globalenv p) b = Some v /\ transf_globvar transf_var v = OK v'.
Proof.
  pose proof (@find_var_info_rev_transf_augment _ _ _ _ _ _ _ _ _ _ transf_augment_OK).
  intros.  pose proof (H b v' H0). 
  destruct (plt b (genv_next (globalenv p))).  auto. contradiction.
Qed.

Theorem find_symbol_transf_partial2:
  forall (s: ident),
  find_symbol (globalenv p') s = find_symbol (globalenv p) s.
Proof.
  pose proof (@find_symbol_transf_augment _ _ _ _ _ _ _ _ _ _ transf_augment_OK).
  auto.
Qed.

Theorem init_mem_transf_partial2:
  forall m, init_mem p = Some m -> init_mem p' = Some m.
Proof.
  pose proof (@init_mem_transf_augment _ _ _ _ _ _ _ _ _ _ transf_augment_OK).
  intros. simpl in H. apply H; auto.  
Qed.

End TRANSF_PROGRAM_PARTIAL2.

Section TRANSF_PROGRAM_PARTIAL.

Variable A B V: Type.
Variable transf: A -> res B.
Variable p: program A V.
Variable p': program B V.
Hypothesis transf_OK: transform_partial_program transf p = OK p'.

Theorem find_funct_ptr_transf_partial:
  forall (b: block) (f: A),
  find_funct_ptr (globalenv p) b = Some f ->
  exists f',
  find_funct_ptr (globalenv p') b = Some f' /\ transf f = OK f'.
Proof.
  exact (@find_funct_ptr_transf_partial2 _ _ _ _ _ _ _ _ transf_OK).
Qed.

Theorem find_funct_ptr_rev_transf_partial:
  forall (b: block) (tf: B),
  find_funct_ptr (globalenv p') b = Some tf ->
  exists f, find_funct_ptr (globalenv p) b = Some f /\ transf f = OK tf.
Proof.
  exact (@find_funct_ptr_rev_transf_partial2 _ _ _ _ _ _ _ _ transf_OK).
Qed.

Theorem find_funct_transf_partial:
  forall (v: val) (f: A),
  find_funct (globalenv p) v = Some f ->
  exists f',
  find_funct (globalenv p') v = Some f' /\ transf f = OK f'.
Proof.
  exact (@find_funct_transf_partial2 _ _ _ _ _ _ _ _ transf_OK).
Qed.

Theorem find_funct_rev_transf_partial:
  forall (v: val) (tf: B),
  find_funct (globalenv p') v = Some tf ->
  exists f, find_funct (globalenv p) v = Some f /\ transf f = OK tf.
Proof.
  exact (@find_funct_rev_transf_partial2 _ _ _ _ _ _ _ _ transf_OK).
Qed.

Theorem find_symbol_transf_partial:
  forall (s: ident),
  find_symbol (globalenv p') s = find_symbol (globalenv p) s.
Proof.
  exact (@find_symbol_transf_partial2 _ _ _ _ _ _ _ _ transf_OK).
Qed.

Theorem find_var_info_transf_partial:
  forall (b: block),
  find_var_info (globalenv p') b = find_var_info (globalenv p) b.
Proof.
  intros. case_eq (find_var_info (globalenv p) b); intros.
  exploit find_var_info_transf_partial2. eexact transf_OK. eauto. 
  intros [v' [P Q]]. monadInv Q. rewrite P. inv EQ. destruct g; auto. 
  case_eq (find_var_info (globalenv p') b); intros.
  exploit find_var_info_rev_transf_partial2. eexact transf_OK. eauto.
  intros [v' [P Q]]. monadInv Q. inv EQ. congruence. 
  auto.
Qed.

Theorem init_mem_transf_partial:
  forall m, init_mem p = Some m -> init_mem p' = Some m.
Proof.
  exact (@init_mem_transf_partial2 _ _ _ _ _ _ _ _ transf_OK).
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
  unfold tp. apply transform_program_partial_program. 
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
