(** Typing rules and a type inference algorithm for RTL. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import union_find.

(** * The type system *)

(** Like Cminor and all intermediate languages, RTL can be equipped with
  a simple type system that statically guarantees that operations
  and addressing modes are applied to the right number of arguments
  and that the arguments are of the correct types.  The type algebra
  is trivial, consisting of the two types [Tint] (for integers and pointers)
  and [Tfloat] (for floats).  

  Additionally, we impose that each pseudo-register has the same type
  throughout the function.  This requirement helps with register allocation,
  enabling each pseudo-register to be mapped to a single hardware register
  or stack location of the correct type.


  The typing judgement for instructions is of the form [wt_instr f env instr],
  where [f] is the current function (used to type-check [Ireturn] 
  instructions) and [env] is a typing environment associating types to
  pseudo-registers.  Since pseudo-registers have unique types throughout
  the function, the typing environment does not change during type-checking
  of individual instructions.  One point to note is that we have two
  polymorphic operators, [Omove] and [Oundef], which can work both
  over integers and floats.
*)

Definition regenv := reg -> typ.

Section WT_INSTR.

Variable env: regenv.
Variable funct: function.

Inductive wt_instr : instruction -> Prop :=
  | wt_Inop:
      forall s,
      wt_instr (Inop s)
  | wt_Iopmove:
      forall r1 r s,
      env r1 = env r ->
      wt_instr (Iop Omove (r1 :: nil) r s)
  | wt_Iopundef:
      forall r s,
      wt_instr (Iop Oundef nil r s)
  | wt_Iop:
      forall op args res s,
      op <> Omove -> op <> Oundef ->
      (List.map env args, env res) = type_of_operation op ->
      wt_instr (Iop op args res s)
  | wt_Iload:
      forall chunk addr args dst s,
      List.map env args = type_of_addressing addr ->
      env dst = type_of_chunk chunk ->
      wt_instr (Iload chunk addr args dst s)
  | wt_Istore:
      forall chunk addr args src s,
      List.map env args = type_of_addressing addr ->
      env src = type_of_chunk chunk ->
      wt_instr (Istore chunk addr args src s)
  | wt_Icall:
      forall sig ros args res s,
      match ros with inl r => env r = Tint | inr s => True end ->
      List.map env args = sig.(sig_args) ->
      env res = match sig.(sig_res) with None => Tint | Some ty => ty end ->
      wt_instr (Icall sig ros args res s)
  | wt_Icond:
      forall cond args s1 s2,
      List.map env args = type_of_condition cond ->
      wt_instr (Icond cond args s1 s2)
  | wt_Ireturn: 
      forall optres,
      option_map env optres = funct.(fn_sig).(sig_res) ->
      wt_instr (Ireturn optres).

End WT_INSTR.

(** A function [f] is well-typed w.r.t. a typing environment [env],
   written [wt_function env f], if all instructions are well-typed,
   parameters agree in types with the function signature, and
   names of parameters are pairwise distinct. *)

Record wt_function (env: regenv) (f: function) : Prop :=
  mk_wt_function {
    wt_params:
      List.map env f.(fn_params) = f.(fn_sig).(sig_args);
    wt_norepet:
      list_norepet f.(fn_params);
    wt_instrs:
      forall pc instr, f.(fn_code)!pc = Some instr -> wt_instr env f instr
  }.

(** * Type inference *)

(** There are several ways to ensure that RTL code is well-typed and
  to obtain the typing environment (type assignment for pseudo-registers)
  needed for register allocation.  One is to start with well-typed Cminor
  code and show type preservation for RTL generation and RTL optimizations.
  Another is to start with untyped RTL and run a type inference algorithm
  that reconstructs the typing environment, determining the type of
  each pseudo-register from its uses in the code.  We follow the second
  approach.

  The algorithm and its correctness proof in this section were
  contributed by Damien Doligez. *)

(** ** Type inference algorithm *)

Set Implicit Arguments.

(** Type inference for RTL is similar to that for simply-typed 
  lambda-calculus: we use type variables to represent the types
  of registers that have not yet been determined to be [Tint] or [Tfloat]
  based on their uses.  We need exactly one type variable per pseudo-register,
  therefore type variables can be conveniently equated with registers.
  The type of a register during inference is therefore either
  [tTy t] (with [t = Tint] or [t = Tfloat]) for a known type,
  or [tReg r] to mean ``the same type as that of register [r]''. *)

Inductive myT : Set :=
  | tTy : typ -> myT
  | tReg : reg -> myT.

(** The algorithm proceeds by unification of the currently inferred
  type for a pseudo-register with the type dictated by its uses.
  Unification builds on a ``union-find'' data structure representing
  equivalence classes of types (see module [Union_find]).
*)

Module myreg.
  Definition T := myT.
  Definition eq : forall (x y : T), {x=y}+{x<>y}.
  Proof.
    destruct x; destruct y; auto;
    try (apply right; discriminate); try (apply left; discriminate).
    destruct t; destruct t0;
    try (apply right; congruence); try (apply left; congruence).
    elim (peq r r0); intros.
    rewrite a; apply left; apply refl_equal.
    apply right; congruence.
  Defined.
End myreg.

Module mymap.
  Definition elt := myreg.T.
  Definition encode (t : myreg.T) : positive :=
    match t with
    | tTy Tint => xH
    | tTy Tfloat => xI xH
    | tReg r => xO r
    end.
  Definition decode (p : positive) : elt :=
    match p with
    | xH => tTy Tint
    | xI _ => tTy Tfloat
    | xO r => tReg r
    end.

  Lemma encode_decode : forall x : myreg.T, decode (encode x) = x.
  Proof.
    destruct x; try destruct t; simpl; auto.
  Qed.

  Lemma encode_injective :
    forall (x y : myreg.T), encode x = encode y -> x = y.
  Proof.
    intros.
    unfold encode in H. destruct x; destruct y; try congruence;
    try destruct t; try destruct t0; congruence.
  Qed.

  Definition T := PTree.t positive.
  Definition empty := PTree.empty positive.
  Definition get (adr : elt) (t : T) :=
    option_map decode (PTree.get (encode adr) t).
  Definition add (adr dat : elt) (t : T) :=
    PTree.set (encode adr) (encode dat) t.

  Theorem get_empty : forall (x : elt), get x empty = None.
  Proof.
    intro.
    unfold get. unfold empty.
    rewrite PTree.gempty.
    simpl; auto.
  Qed.
  Theorem get_add_1 :
    forall (x y : elt) (m : T), get x (add x y m) = Some y.
  Proof.
    intros.
    unfold add. unfold get.
    rewrite PTree.gss.
    simpl; rewrite encode_decode; auto.
  Qed.
  Theorem get_add_2 :
    forall (x y z : elt) (m : T), z <> x -> get z (add x y m) = get z m.
  Proof.
    intros.
    unfold get. unfold add.
    rewrite PTree.gso; auto.
    intro. apply H. apply encode_injective. auto.
  Qed.
End mymap.

Module Uf := Unionfind (myreg) (mymap).

Definition error := Uf.identify Uf.empty (tTy Tint) (tTy Tfloat).

Fixpoint fold2 (A B : Set) (f : Uf.T -> A -> B -> Uf.T)
               (init : Uf.T) (la : list A) (lb : list B) {struct la}
               : Uf.T :=
  match la, lb with
  | ha::ta, hb::tb => fold2 f (f init ha hb) ta tb
  | nil, nil => init
  | _, _ => error
  end.

Definition option_fold2 (A B : Set) (f : Uf.T -> A -> B -> Uf.T)
                        (init : Uf.T) (oa : option A) (ob : option B)
                        : Uf.T :=
  match oa, ob with
  | Some a, Some b => f init a b
  | None, None => init
  | _, _ => error
  end.

Definition teq (ty1 ty2 : typ) : bool :=
  match ty1, ty2 with
  | Tint, Tint => true
  | Tfloat, Tfloat => true
  | _, _ => false
  end.

Definition type_rtl_arg (u : Uf.T) (r : reg) (t : typ) :=
  Uf.identify u (tReg r) (tTy t).

Definition type_rtl_ros (u : Uf.T) (ros : reg+ident) :=
  match ros with
  | inl r => Uf.identify u (tReg r) (tTy Tint)
  | inr s => u
  end.

Definition type_of_sig_res (sig : signature) :=
  match sig.(sig_res) with None => Tint | Some ty => ty end.

(** This is the core type inference function.  The [u] argument is
  the current substitution / equivalence classes between types.
  An updated set of equivalence classes, reflecting unifications
  possibly performed during the type-checking of [i], is returned.
  Note that [type_rtl_instr] never fails explicitly.  However,
  in case of type error (e.g. applying the [Oadd] integer operation
  to float registers), the equivalence relation returned will
  put [tTy Tint] and [tTy Tfloat] in the same equivalence class.
  This fact will propagate through type inference for other instructions,
  and be detected at the end of type inference, indicating a typing failure.
*)

Definition type_rtl_instr (rtyp : option typ)
    (u : Uf.T) (_ : positive) (i : instruction) :=
  match i with
  | Inop _ => u
  | Iop Omove (r1 :: nil) r0 _ => Uf.identify u (tReg r0) (tReg r1)
  | Iop Omove _ _ _ => error
  | Iop Oundef nil _ _ => u
  | Iop Oundef _ _ _ => error
  | Iop op args r0 _ =>
      let (argtyp, restyp) := type_of_operation op in
      let u1 := type_rtl_arg u r0 restyp in
      fold2 type_rtl_arg u1 args argtyp
  | Iload chunk addr args r0 _ =>  
      let u1 := type_rtl_arg u r0 (type_of_chunk chunk) in
      fold2 type_rtl_arg u1 args (type_of_addressing addr)
  | Istore chunk addr args r0 _ =>
      let u1 := type_rtl_arg u r0 (type_of_chunk chunk) in
      fold2 type_rtl_arg u1 args (type_of_addressing addr)
  | Icall sign ros args r0 _ =>
      let u1 := type_rtl_ros u ros in
      let u2 := type_rtl_arg u1 r0 (type_of_sig_res sign) in
      fold2 type_rtl_arg u2 args sign.(sig_args)
  | Icond cond args _ _ =>
      fold2 type_rtl_arg u args (type_of_condition cond)
  | Ireturn o => option_fold2 type_rtl_arg u o rtyp
  end.

Definition mk_env (u : Uf.T) (r : reg) :=
  if myreg.eq (Uf.repr u (tReg r)) (Uf.repr u (tTy Tfloat))
  then Tfloat
  else Tint.

Fixpoint member (x : reg) (l : list reg) {struct l} : bool :=
  match l with
  | nil => false
  | y :: rest => if peq x y then true else member x rest
  end.

Fixpoint repet (l : list reg) : bool :=
  match l with
  | nil => false
  | x :: rest => member x rest || repet rest
  end.

Definition type_rtl_function (f : function) :=
  let u1 := PTree.fold (type_rtl_instr f.(fn_sig).(sig_res))
                       f.(fn_code) Uf.empty in
  let u2 := fold2 type_rtl_arg u1 f.(fn_params) f.(fn_sig).(sig_args) in
  if repet f.(fn_params) then
    None
  else
    if myreg.eq (Uf.repr u2 (tTy Tint)) (Uf.repr u2 (tTy Tfloat))
    then None
    else Some (mk_env u2).

Unset Implicit Arguments.

(** ** Correctness proof for type inference *)

(** General properties of the type equivalence relation. *)

Definition consistent (u : Uf.T) :=
  Uf.repr u (tTy Tint) <> Uf.repr u (tTy Tfloat).

Lemma consistent_not_eq : forall (u : Uf.T) (A : Type) (x y : A),
  consistent u ->
  (if myreg.eq (Uf.repr u (tTy Tint)) (Uf.repr u (tTy Tfloat)) then x else y)
  = y.
  Proof.
    intros.
    unfold consistent in H.
    destruct (myreg.eq (Uf.repr u (tTy Tint)) (Uf.repr u (tTy Tfloat)));
    congruence.
  Qed.

Lemma equal_eq : forall (t : myT) (A : Type) (x y : A),
  (if myreg.eq t t then x else y) = x.
  Proof.
    intros.
    destruct (myreg.eq t t); congruence.
  Qed.

Lemma error_inconsistent : forall (A : Prop), consistent error -> A.
  Proof.
    intros.
    absurd (consistent error); auto.
    intro.
    unfold error in H.  unfold consistent in H.
    rewrite Uf.sameclass_identify_1 in H.
    congruence.
  Qed.

Lemma teq_correct : forall (t1 t2 : typ), teq t1 t2 = true -> t1 = t2.
  Proof.
    intros; destruct t1; destruct t2; try simpl in H; congruence.
  Qed.

Definition included (u1 u2 : Uf.T) : Prop :=
  forall (e1 e2: myT),
    Uf.repr u1 e1 = Uf.repr u1 e2 -> Uf.repr u2 e1 = Uf.repr u2 e2.

Lemma included_refl :
  forall (e : Uf.T), included e e.
  Proof.
    unfold included. auto.
  Qed.

Lemma included_trans :
  forall (e1 e2 e3 : Uf.T),
  included e3 e2 -> included e2 e1 -> included e3 e1.
  Proof.
    unfold included. auto.
  Qed.

Lemma included_consistent :
  forall (u1 u2 : Uf.T),
  included u1 u2 -> consistent u2 -> consistent u1.
  Proof.
    unfold consistent. unfold included.
    intros.
    intro. apply H0. apply H.
    auto.
  Qed.

Lemma included_identify :
  forall (u : Uf.T) (t1 t2 : myT), included u (Uf.identify u t1 t2).
  Proof.
  unfold included.
  intros.
  apply Uf.sameclass_identify_2; auto.
  Qed.

Lemma type_arg_correct_1 :
  forall (u : Uf.T) (r : reg) (t : typ),
  consistent (type_rtl_arg u r t)
  -> Uf.repr (type_rtl_arg u r t) (tReg r)
     = Uf.repr (type_rtl_arg u r t) (tTy t).
  Proof.
    intros.
    unfold type_rtl_arg.
    rewrite Uf.sameclass_identify_1.
    auto.
  Qed.

Lemma type_arg_correct :
  forall (u : Uf.T) (r : reg) (t : typ),
  consistent (type_rtl_arg u r t) -> mk_env (type_rtl_arg u r t) r = t.
  Proof.
    intros.
    unfold mk_env. 
    rewrite type_arg_correct_1.
    destruct t.
    apply consistent_not_eq; auto.
    destruct (myreg.eq (Uf.repr (type_rtl_arg u r Tfloat) (tTy Tfloat)));
    congruence.
    auto.
  Qed.

Lemma type_arg_included :
  forall (u : Uf.T) (r : reg) (t : typ), included u (type_rtl_arg u r t).
  Proof.
    intros.
    unfold type_rtl_arg.
    apply included_identify.
  Qed.

Lemma type_arg_extends :
  forall (u : Uf.T) (r : reg) (t : typ),
  consistent (type_rtl_arg u r t) -> consistent u.
  Proof.
    intros.
    apply included_consistent with (u2 := type_rtl_arg u r t).
    apply type_arg_included.
    auto.
  Qed.

Lemma type_args_included :
  forall (l1 : list reg) (l2 : list typ) (u : Uf.T),
  consistent (fold2 type_rtl_arg u l1 l2)
  -> included u (fold2 type_rtl_arg u l1 l2).
  Proof.
    induction l1; intros; destruct l2.
    simpl in H; simpl; apply included_refl.
    simpl in H. apply error_inconsistent. auto.
    simpl in H. apply error_inconsistent. auto.
    simpl.
    simpl in H.
    apply included_trans with (e2 := type_rtl_arg u a t).
    apply type_arg_included.
    apply IHl1.
    auto.
  Qed.

Lemma type_args_extends :
  forall (l1 : list reg) (l2 : list typ) (u : Uf.T),
  consistent (fold2 type_rtl_arg u l1 l2) -> consistent u.
  Proof.
    intros.
    apply (included_consistent _ _ (type_args_included l1 l2 u H)).
    auto.
  Qed.

Lemma type_args_correct :
  forall (l1 : list reg) (l2 : list typ) (u : Uf.T),
  consistent (fold2 type_rtl_arg u l1 l2)
  -> map (mk_env (fold2 type_rtl_arg u l1 l2)) l1 = l2.
  Proof.
    induction l1.
    intros.
    destruct l2.
    unfold map; simpl; auto.
    simpl in H; apply error_inconsistent; auto.
    intros.
    destruct l2.
    simpl in H; apply error_inconsistent; auto.
    simpl.
    simpl in H.
    rewrite (IHl1 l2 (type_rtl_arg u a t) H).
    unfold mk_env.
    destruct t.
    rewrite (type_args_included _ _ _ H (tReg a) (tTy Tint)).
    rewrite consistent_not_eq; auto.
    apply type_arg_correct_1.
    apply type_args_extends with (l1 := l1) (l2 := l2); auto.
    rewrite (type_args_included _ _ _ H (tReg a) (tTy Tfloat)).
    rewrite equal_eq; auto.
    apply type_arg_correct_1.
    apply type_args_extends with (l1 := l1) (l2 := l2); auto.
  Qed.

(** Correctness of [wt_params]. *)

Lemma type_rtl_function_params :
  forall (f: function) (env: regenv),
  type_rtl_function f = Some env
  -> List.map env f.(fn_params) = f.(fn_sig).(sig_args).
  Proof.
    destruct f; unfold type_rtl_function; simpl.
    destruct (repet fn_params); simpl; intros; try congruence.
    pose (u := PTree.fold (type_rtl_instr (sig_res fn_sig)) fn_code Uf.empty).
    fold u in H.
    cut (consistent (fold2 type_rtl_arg u fn_params (sig_args fn_sig))).
    intro.
    pose (R := Uf.repr (fold2 type_rtl_arg u fn_params (sig_args fn_sig))).
    fold R in H.
    destruct (myreg.eq (R (tTy Tint)) (R (tTy Tfloat))).
    congruence.
    injection H.
    intro.
    rewrite <- H1.
    apply type_args_correct.
    auto.
    intro.
    rewrite H0 in H.
    rewrite equal_eq in H.
    congruence.
  Qed.

(** Correctness of [wt_norepet]. *)

Lemma member_correct :
  forall (l : list reg) (a : reg), member a l = false -> ~In a l.
  Proof.
    induction l; simpl; intros; try tauto.
    destruct (peq a0 a); simpl; try congruence.
    intro. destruct H0; try congruence.
    generalize H0; apply IHl; auto.
  Qed.

Lemma repet_correct :
  forall (l : list reg), repet l = false -> list_norepet l.
  Proof.
    induction l; simpl; intros.
     exact (list_norepet_nil reg).
     elim (orb_false_elim (member a l) (repet l) H); intros.
     apply list_norepet_cons.
      apply member_correct; auto.
      apply IHl; auto.
  Qed.

Lemma type_rtl_function_norepet :
  forall (f: function) (env: regenv),
  type_rtl_function f = Some env
  -> list_norepet f.(fn_params).
  Proof.
    destruct f; unfold type_rtl_function; simpl.
    intros. cut (repet fn_params = false).
     intro. apply repet_correct. auto.
     destruct (repet fn_params); congruence.
  Qed.

(** Correctness of [wt_instrs]. *)

Lemma step1 :
  forall (f : function) (env : regenv),
  type_rtl_function f = Some env
  -> exists u2 : Uf.T,
       included (PTree.fold (type_rtl_instr f.(fn_sig).(sig_res))
                            f.(fn_code) Uf.empty)
                u2
       /\ env = mk_env u2
       /\ consistent u2.
  Proof.
    intros f env.
    pose (u1 := (PTree.fold (type_rtl_instr f.(fn_sig).(sig_res))
                            f.(fn_code) Uf.empty)).
    fold u1.
    unfold type_rtl_function.
    intros.
    destruct (repet f.(fn_params)).
    congruence.
    fold u1 in H.
    pose (u2 := (fold2 type_rtl_arg u1 f.(fn_params) f.(fn_sig).(sig_args))).
    fold u2 in H.
    exists u2.
    caseEq (myreg.eq (Uf.repr u2 (tTy Tint)) (Uf.repr u2 (tTy Tfloat))).
    intros.
    rewrite e in H.
    rewrite equal_eq in H.
    congruence.
    intros.
    rewrite consistent_not_eq in H.
    apply conj.
    unfold u2.
    apply type_args_included.
    auto.
    apply conj; auto.
    congruence.
    auto.
  Qed.

Lemma let_fold_args_res :
  forall (u : Uf.T) (l : list reg) (r : reg) (e : list typ * typ),
  (let (argtyp, restyp) := e in
   fold2 type_rtl_arg (type_rtl_arg u r restyp) l argtyp)
  = fold2 type_rtl_arg (type_rtl_arg u r (snd e)) l (fst e).
  Proof.
    intros. rewrite (surjective_pairing e). simpl. auto.
  Qed.

Lemma type_args_res_included :
  forall (l1 : list reg) (l2 : list typ) (u : Uf.T) (r : reg) (t : typ),
  consistent (fold2 type_rtl_arg (type_rtl_arg u r t) l1 l2)
  -> included u (fold2 type_rtl_arg (type_rtl_arg u r t) l1 l2).
  Proof.
  intros.
  apply included_trans with (e2 := type_rtl_arg u r t).
  apply type_arg_included.
  apply type_args_included; auto.
  Qed.

Lemma type_args_res_ros_included :
  forall (l1 : list reg) (l2 : list typ) (u : Uf.T) (r : reg) (t : typ)
         (ros : reg+ident),
  consistent (fold2 type_rtl_arg (type_rtl_arg (type_rtl_ros u ros) r t) l1 l2)
  -> included u (fold2 type_rtl_arg (type_rtl_arg (type_rtl_ros u ros) r t) l1 l2).
Proof.
  intros.
  apply included_trans with (e2 := type_rtl_ros u ros).
  unfold type_rtl_ros; destruct ros.
  apply included_identify.
  apply included_refl.
  apply type_args_res_included; auto.
Qed.

Lemma type_instr_included :
  forall (p : positive) (i : instruction) (u : Uf.T) (res_ty : option typ),
  consistent (type_rtl_instr res_ty u p i)
  -> included u (type_rtl_instr res_ty u p i).
  Proof.
    intros.
    destruct i; simpl; simpl in H; try apply type_args_res_included; auto.
    apply included_refl; auto.
    destruct o; simpl; simpl in H; try apply type_args_res_included; auto.
    destruct l; simpl; simpl in H; auto.
    apply error_inconsistent; auto.
    destruct l; simpl; simpl in H; auto.
    apply included_identify.
    apply error_inconsistent; auto.
    destruct l; simpl; simpl in H; auto.
    apply included_refl.
    apply error_inconsistent; auto.
    apply type_args_res_ros_included; auto.
    apply type_args_included; auto.
    destruct res_ty; destruct o; simpl; simpl in H;
      try (apply error_inconsistent; auto; fail).
    apply type_arg_included.
    apply included_refl.
   Qed.

Lemma type_instrs_extends :
  forall (l : list (positive * instruction)) (u : Uf.T) (res_ty : option typ),
  consistent
      (fold_left (fun v p => type_rtl_instr res_ty v (fst p) (snd p)) l u)
  -> consistent u.
Proof.
  induction l; simpl; intros.
  auto.
  apply included_consistent
     with (u2 := (type_rtl_instr res_ty u (fst a) (snd a))).
  apply type_instr_included.
  apply IHl with (res_ty := res_ty); auto.
  apply IHl with (res_ty := res_ty); auto.
Qed.

Lemma type_instrs_included :
  forall (l : list (positive * instruction)) (u : Uf.T) (res_ty : option typ),
  consistent
      (fold_left (fun v p => type_rtl_instr res_ty v (fst p) (snd p)) l u)
  -> included u
         (fold_left (fun v p => type_rtl_instr res_ty v (fst p) (snd p)) l u).
  Proof.
    induction l; simpl; intros.
    apply included_refl; auto.
    apply included_trans with (e2 := (type_rtl_instr res_ty u (fst a) (snd a))).
    apply type_instr_included.
    apply type_instrs_extends with (res_ty := res_ty) (l := l); auto.
    apply IHl; auto.
  Qed.

Lemma step2 :
  forall (res_ty : option typ) (c : code) (u0 : Uf.T),
  consistent (PTree.fold (type_rtl_instr res_ty) c u0) ->
  forall (pc : positive) (i : instruction),
  c!pc = Some i
  -> exists u : Uf.T,
        consistent (type_rtl_instr res_ty u pc i)
     /\ included (type_rtl_instr res_ty u pc i)
                    (PTree.fold (type_rtl_instr res_ty) c u0).
  Proof.
    intros.
    rewrite PTree.fold_spec.
    rewrite PTree.fold_spec in H.
    pose (H1 := PTree.elements_correct _ _ H0).
    generalize H. clear H.
    generalize u0. clear u0.
    generalize H1. clear H1.
    induction (PTree.elements c).
    intros.
    absurd (In (pc, i) nil).
    apply in_nil.
    auto.
    intros.
    simpl in H.
    elim H1.
    intro.
    rewrite H2 in H.
    simpl in H.
    rewrite H2. simpl.
    exists u0.
    apply conj.
    apply type_instrs_extends with (res_ty := res_ty) (l := l).
    auto.
    apply type_instrs_included.
    auto.
    intro.
    simpl.
    apply IHl.
    auto.
    auto.
  Qed.

Definition mapped (u : Uf.T) (r : reg) :=
  Uf.repr u (tReg r) = Uf.repr u (tTy Tfloat)
  \/ Uf.repr u (tReg r) = Uf.repr u (tTy Tint).

Definition definite (u : Uf.T) (i : instruction) :=
  match i with
  | Inop _ => True
  | Iop Omove (r1 :: nil) r0 _ => Uf.repr u (tReg r1) = Uf.repr u (tReg r0)
  | Iop Oundef _ _ _ => True
  | Iop _ args r0 _ =>
         mapped u r0 /\ forall r : reg, In r args -> mapped u r
  | Iload _ _ args r0 _ =>
         mapped u r0 /\ forall r : reg, In r args -> mapped u r
  | Istore _ _ args r0 _ =>
         mapped u r0 /\ forall r : reg, In r args -> mapped u r
  | Icall _ ros args r0 _ =>
      match ros with inl r => mapped u r | _ => True end
      /\ mapped u r0 /\ forall r : reg, In r args -> mapped u r
  | Icond _ args _ _ =>
      forall r : reg, In r args -> mapped u r
  | Ireturn None => True
  | Ireturn (Some r) => mapped u r
  end.

Lemma type_arg_complete :
  forall (u : Uf.T) (r : reg) (t : typ),
  mapped (type_rtl_arg u r t) r.
Proof.
  intros.
  unfold type_rtl_arg.
  unfold mapped.
  destruct t.
  right; apply Uf.sameclass_identify_1.
  left; apply Uf.sameclass_identify_1.
Qed.

Lemma type_arg_mapped :
  forall (u : Uf.T) (r r0 : reg) (t : typ),
  mapped u r0 -> mapped (type_rtl_arg u r t) r0.
Proof.
  unfold mapped.
  unfold type_rtl_arg.
  intros.
  elim H; intros.
  left; apply Uf.sameclass_identify_2; auto.
  right; apply Uf.sameclass_identify_2; auto.
Qed.

Lemma type_args_mapped :
  forall (lr : list reg) (lt : list typ) (u : Uf.T) (r : reg),
  consistent (fold2 type_rtl_arg u lr lt) ->
  mapped u r ->
    mapped (fold2 type_rtl_arg u lr lt) r.
Proof.
  induction lr; simpl; intros.
  destruct lt; simpl; auto; try (apply error_inconsistent; auto; fail).
  destruct lt; simpl; auto; try (apply error_inconsistent; auto; fail).
  apply IHlr.
  auto.
  apply type_arg_mapped; auto.
Qed.

Lemma type_args_complete :
  forall (lr : list reg) (lt : list typ) (u : Uf.T),
  consistent (fold2 type_rtl_arg u lr lt)
  -> forall r, (In r lr -> mapped (fold2 type_rtl_arg u lr lt) r).
Proof.
  induction lr; simpl; intros.
  destruct lt; simpl; try tauto.
  destruct lt; simpl.
  apply error_inconsistent; auto.
  elim H0; intros.
  rewrite H1.
  rewrite H1 in H.
  apply type_args_mapped; auto.
  apply type_arg_complete.
  apply IHlr; auto.
Qed.

Lemma type_res_complete :
  forall (u : Uf.T) (lr : list reg) (lt : list typ) (r : reg) (t : typ),
  consistent (fold2 type_rtl_arg (type_rtl_arg u r t) lr lt)
  -> mapped (fold2 type_rtl_arg (type_rtl_arg u r t) lr lt) r.
Proof.
  intros.
  apply type_args_mapped; auto.
  apply type_arg_complete.
Qed.

Lemma type_args_res_complete :
  forall (u : Uf.T) (lr : list reg) (lt : list typ) (r : reg) (t : typ),
  consistent (fold2 type_rtl_arg (type_rtl_arg u r t) lr lt)
  -> mapped (fold2 type_rtl_arg (type_rtl_arg u r t) lr lt) r
      /\ forall rr, (In rr lr -> mapped (fold2 type_rtl_arg (type_rtl_arg u r t)
                                                            lr lt)
                                        rr).
Proof.
  intros.
  apply conj.
  apply type_res_complete; auto.
  apply type_args_complete; auto.
Qed.

Lemma type_ros_complete :
  forall (u : Uf.T) (lr : list reg) (lt : list typ) (r r1 : reg) (t : typ),
  consistent (fold2 type_rtl_arg (type_rtl_arg
                                    (type_rtl_ros u (inl ident r1)) r t) lr lt)
  ->
  mapped (fold2 type_rtl_arg (type_rtl_arg
                                (type_rtl_ros u (inl ident r1)) r t) lr lt) r1.
Proof.
  intros.
  apply type_args_mapped; auto.
  apply type_arg_mapped.
  unfold type_rtl_ros.
  unfold mapped.
  right.
  apply Uf.sameclass_identify_1; auto.
Qed.

Lemma type_res_correct :
  forall (u : Uf.T) (lr : list reg) (lt : list typ) (r : reg) (t : typ),
  consistent (fold2 type_rtl_arg (type_rtl_arg u r t) lr lt)
  -> mk_env (fold2 type_rtl_arg (type_rtl_arg u r t) lr lt) r = t.
Proof.
  intros.
  unfold mk_env.
  rewrite (type_args_included _ _ _ H (tReg r) (tTy t)).
  destruct t.
  apply consistent_not_eq; auto.
  apply equal_eq; auto.
  unfold type_rtl_arg; apply Uf.sameclass_identify_1; auto.
Qed.

Lemma type_ros_correct :
  forall (u : Uf.T) (lr : list reg) (lt : list typ) (r r1 : reg) (t : typ),
  consistent (fold2 type_rtl_arg (type_rtl_arg
                                    (type_rtl_ros u (inl ident r1)) r t) lr lt)
  ->
  mk_env (fold2 type_rtl_arg (type_rtl_arg
                                (type_rtl_ros u (inl ident r1)) r t) lr lt) r1
  = Tint.
Proof.
  intros.
  unfold mk_env.
  rewrite (type_args_included _ _ _ H (tReg r1) (tTy Tint)).
  apply consistent_not_eq; auto.
  rewrite (type_arg_included (type_rtl_ros u (inl ident r1)) r t (tReg r1) (tTy Tint)).
  auto.
  simpl.
  apply Uf.sameclass_identify_1; auto.
Qed.

Lemma step3 :
  forall (u : Uf.T) (f : function) (c : code) (i : instruction) (pc : positive),
  c!pc = Some i ->
  consistent (type_rtl_instr f.(fn_sig).(sig_res) u pc i)
  ->    wt_instr (mk_env (type_rtl_instr f.(fn_sig).(sig_res) u pc i)) f i
     /\ definite (type_rtl_instr f.(fn_sig).(sig_res) u pc i) i.
  Proof.
    Opaque type_rtl_arg.
    intros.
    destruct i; simpl in H0; simpl.
     (* Inop *)
     apply conj; auto. apply wt_Inop.
     (* Iop *)
     destruct o;
       try (apply conj; [
             apply wt_Iop; try congruence; simpl;
               rewrite (type_args_correct _ _ _ H0);
               rewrite (type_res_correct _ _ _ _ _ H0);
               auto
            |apply (type_args_res_complete _ _ _ _ _ H0)]).
      (* Omove *)
      destruct l; [apply error_inconsistent; auto | idtac].
      destruct l; [idtac | apply error_inconsistent; auto].
      apply conj.
      apply wt_Iopmove.
      simpl.
      unfold mk_env.
      rewrite Uf.sameclass_identify_1.
      congruence.
      simpl.
      rewrite Uf.sameclass_identify_1; congruence.
      (* Oundef *)
      destruct l; [idtac | apply error_inconsistent; auto].
      apply conj. apply wt_Iopundef.
      unfold definite. auto.
     (* Iload *)
     apply conj.
      apply wt_Iload.
       rewrite (type_args_correct _ _ _ H0); auto.
       rewrite (type_res_correct _ _ _ _ _ H0); auto.
      simpl; apply (type_args_res_complete _ _ _ _ _ H0).
     (* IStore *)
     apply conj.
      apply wt_Istore.
       rewrite (type_args_correct _ _ _ H0); auto.
       rewrite (type_res_correct _ _ _ _ _ H0); auto.
      simpl; apply (type_args_res_complete _ _ _ _ _ H0).
     (* Icall *)
     apply conj.
      apply wt_Icall.
       destruct s0; auto. apply type_ros_correct. auto.
       apply type_args_correct. auto.
       fold (type_of_sig_res s). apply type_res_correct. auto.
      destruct s0.
       apply conj.
        apply type_ros_complete. auto.
        apply type_args_res_complete. auto.
       apply conj; auto.
         apply type_args_res_complete. auto.
     (* Icond *) 
     apply conj.
      apply wt_Icond.
       apply (type_args_correct _ _ _ H0).
       simpl; apply (type_args_complete _ _ _ H0).
     (* Ireturn *)
     destruct o; simpl.
      apply conj.
       apply wt_Ireturn.
         destruct f.(fn_sig).(sig_res); simpl; simpl in H0.
          rewrite type_arg_correct; auto.
          apply error_inconsistent; auto.
       destruct f.(fn_sig).(sig_res); simpl; simpl in H0.
          apply type_arg_complete.
          apply error_inconsistent; auto.
      apply conj; auto. apply wt_Ireturn.
        destruct f.(fn_sig).(sig_res); simpl; simpl in H0.
         apply error_inconsistent; auto.
         congruence.
    Transparent type_rtl_arg.
  Qed.

Lemma mapped_included_consistent :
  forall (u1 u2 : Uf.T) (r : reg),
  mapped u1 r ->
  included u1 u2 ->
  consistent u2 ->
  mk_env u2 r = mk_env u1 r.
Proof.
  intros.
  unfold mk_env.
  unfold mapped in H.
  elim H; intros; rewrite H2; rewrite (H0 _ _ H2).
  rewrite equal_eq; rewrite equal_eq; auto.
  rewrite (consistent_not_eq u2).
  rewrite (consistent_not_eq u1).
  auto.
  apply included_consistent with (u2 := u2).
  auto.
  auto.
  auto.
Qed.

Lemma mapped_list_included :
  forall (u1 u2 : Uf.T) (lr : list reg),
  (forall r, In r lr -> mapped u1 r) ->
  included u1 u2 ->
  consistent u2 ->
    map (mk_env u2) lr = map (mk_env u1) lr.
Proof.
  induction lr; simpl; intros.
  auto.
  rewrite (mapped_included_consistent u1 u2 a).
  rewrite IHlr; auto.
  apply (H a); intros.
  left; auto.
  auto.
  auto.
Qed.

Lemma included_mapped :
  forall (u1 u2 : Uf.T) (r : reg),
  included u1 u2 ->
  mapped u1 r ->
    mapped u2 r.
Proof.
  unfold mapped.
  intros.
  elim H0; intros.
  left; rewrite (H _ _ H1); auto.
  right; rewrite (H _ _ H1); auto.
Qed.

Lemma included_mapped_forall :
  forall (u1 u2 : Uf.T) (r : reg) (l : list reg),
  included u1 u2 ->
  mapped u1 r /\ (forall r, In r l -> mapped u1 r) ->
    mapped u2 r /\ (forall r, In r l -> mapped u2 r).
Proof.
  intros.
  elim H0; intros.
  apply conj.
  apply (included_mapped _ _ r H); auto.
  intros.
  apply (included_mapped _ _ r0 H).
  apply H2; auto.
Qed.

Lemma definite_included :
  forall (u1 u2 : Uf.T) (i : instruction),
  included u1 u2 -> definite u1 i -> definite u2 i.
Proof.
  unfold definite.
  intros.
  destruct i; try apply (included_mapped_forall _ _ _ _ H H0); auto.
  destruct o; try apply (included_mapped_forall _ _ _ _ H H0); auto.
  destruct l; auto.
  apply (included_mapped_forall _ _ _ _ H H0).
  destruct l; auto.
  apply (included_mapped_forall _ _ _ _ H H0).
  destruct s0; auto.
  elim H0; intros.
  apply conj.
  apply (included_mapped _ _ _ H H1).
  apply (included_mapped_forall _ _ _ _ H H2).
  elim H0; intros.
  apply conj; auto.
  apply (included_mapped_forall _ _ _ _ H H2).
  intros.
  apply (included_mapped _ _ _ H (H0 r H1)).
  destruct o; auto.
  apply (included_mapped _ _ _ H H0).
Qed.

Lemma step4 :
  forall (f : function) (u1 u3 : Uf.T) (i : instruction),
  included u3 u1 ->
  wt_instr (mk_env u3) f i ->
  definite u3 i ->
  consistent u1 ->
    wt_instr (mk_env u1) f i.
  Proof.
    intros f u1 u3 i H1 H H0 X.
    destruct H; try simpl in H0; try (elim H0; intros).
     apply wt_Inop.
     apply wt_Iopmove. unfold mk_env. rewrite (H1 _ _ H0). auto.
     apply wt_Iopundef.
     apply wt_Iop; auto.
       destruct op; try congruence; simpl; simpl in H3;
       simpl in H0; elim H0; intros; rewrite (mapped_included_consistent _ _ _ H4 H1 X);
       rewrite (mapped_list_included _ _ _ H5 H1); auto.
     apply wt_Iload.
      rewrite (mapped_list_included _ _ _ H4 H1); auto.
      rewrite (mapped_included_consistent _ _ _ H3 H1 X). auto.
     apply wt_Istore.
      rewrite (mapped_list_included _ _ _ H4 H1); auto.
      rewrite (mapped_included_consistent _ _ _ H3 H1 X). auto.
     elim H5; intros; destruct ros; apply wt_Icall.
      rewrite (mapped_included_consistent _ _ _ H4 H1 X); auto.
      rewrite (mapped_list_included _ _ _ H7 H1); auto.
      rewrite (mapped_included_consistent _ _ _ H6 H1 X); auto.
      auto.
      rewrite (mapped_list_included _ _ _ H7 H1); auto.
      rewrite (mapped_included_consistent _ _ _ H6 H1 X); auto.
     apply wt_Icond. rewrite (mapped_list_included _ _ _ H0 H1); auto.
     apply wt_Ireturn.
      destruct optres; destruct f.(fn_sig).(sig_res);
        simpl in H; simpl; try congruence.
        rewrite (mapped_included_consistent _ _ _ H0 H1 X); auto.
  Qed.

Lemma type_rtl_function_instrs :
  forall (f: function) (env: regenv),
  type_rtl_function f = Some env
  -> forall pc i, f.(fn_code)!pc = Some i -> wt_instr env f i.
  Proof.
    intros.
    elim (step1 _ _ H).
    intros.
    elim H1.
    intros.
    elim H3.
    intros.
    rewrite H4.
    elim (step2 _ _ _ (included_consistent _ _ H2 H5) _ _ H0).
    intros.
    elim H6. intros.
    elim (step3 x0 f _ _ _ H0); auto. intros.
    apply (step4 f _ _ i H2); auto.
    apply (step4 _ _ _ _ H8 H9 H10).
    apply (included_consistent _ _ H2); auto.
    apply (definite_included _ _ _ H8 H10); auto.
  Qed.

(** Combining the sub-proofs. *)

Theorem type_rtl_function_correct:
  forall (f: function) (env: regenv),
  type_rtl_function f = Some env -> wt_function env f.
  Proof.
    intros.
    exact (mk_wt_function env f (type_rtl_function_params f _ H)
                                (type_rtl_function_norepet f _ H)
                                (type_rtl_function_instrs f _ H)).
  Qed.

Definition wt_program (p: program) : Prop :=
  forall i f, In (i, f) (prog_funct p) -> type_rtl_function f <> None.

(** * Type preservation during evaluation *)

(** The type system for RTL is not sound in that it does not guarantee
  progress: well-typed instructions such as [Icall] can fail because
  of run-time type tests (such as the equality between calle and caller's
  signatures).  However, the type system guarantees a type preservation
  property: if the execution does not fail because of a failed run-time
  test, the result values and register states match the static
  typing assumptions.  This preservation property will be useful
  later for the proof of semantic equivalence between [Machabstr] and [Mach].
  Even though we do not need it for [RTL], we show preservation for [RTL]
  here, as a warm-up exercise and because some of the lemmas will be
  useful later. *)

Require Import Globalenvs.
Require Import Values.
Require Import Mem.
Require Import Integers.

Definition wt_regset (env: regenv) (rs: regset) : Prop :=
  forall r, Val.has_type (rs#r) (env r).

Lemma wt_regset_assign:
  forall env rs v r,
  wt_regset env rs ->
  Val.has_type v (env r) ->
  wt_regset env (rs#r <- v).
Proof.
  intros; red; intros. 
  rewrite Regmap.gsspec.
  case (peq r0 r); intro.
  subst r0. assumption.
  apply H.
Qed.

Lemma wt_regset_list:
  forall env rs,
  wt_regset env rs ->
  forall rl, Val.has_type_list (rs##rl) (List.map env rl).
Proof.
  induction rl; simpl.
  auto.
  split. apply H. apply IHrl.
Qed.  

Lemma wt_init_regs:
  forall env rl args,
  Val.has_type_list args (List.map env rl) ->
  wt_regset env (init_regs args rl).
Proof.
  induction rl; destruct args; simpl; intuition.
  red; intros. rewrite Regmap.gi. simpl; auto. 
  apply wt_regset_assign; auto.
Qed.

Section SUBJECT_REDUCTION.

Variable p: program.

Hypothesis wt_p: wt_program p.

Let ge := Genv.globalenv p.

Definition exec_instr_subject_reduction
    (c: code) (sp: val)
    (pc: node) (rs: regset) (m: mem)
    (pc': node) (rs': regset) (m': mem) : Prop :=
  forall env f
         (CODE: c = fn_code f)
         (WT_FN: wt_function env f)
         (WT_RS: wt_regset env rs),
  wt_regset env rs'.

Definition exec_function_subject_reduction
    (f: function) (args: list val) (m: mem) (res: val) (m': mem) : Prop :=
  forall env,
  wt_function env f ->  
  Val.has_type_list args f.(fn_sig).(sig_args) ->
  Val.has_type res
    (match f.(fn_sig).(sig_res) with None => Tint | Some ty => ty end).

Lemma subject_reduction:
  forall f args m res m',
  exec_function ge f args m res m' ->
  exec_function_subject_reduction f args m res m'.
Proof.
  apply (exec_function_ind_3 ge
           exec_instr_subject_reduction
           exec_instr_subject_reduction
           exec_function_subject_reduction);
  intros; red; intros;
  try (rewrite CODE in H;
       generalize (wt_instrs env _ WT_FN pc _ H);
       intro WT_INSTR;
       inversion WT_INSTR).
 
  assumption.

  apply wt_regset_assign. auto. 
  subst op. subst args. simpl in H0. injection H0; intro. 
  subst v. rewrite <- H2. apply WT_RS.

  apply wt_regset_assign. auto.
  subst op; subst args; simpl in H0. injection H0; intro; subst v.
  simpl; auto.

  apply wt_regset_assign. auto.
  replace (env res) with (snd (type_of_operation op)).
  apply type_of_operation_sound with function ge rs##args sp; auto.
  rewrite <- H7. reflexivity.

  apply wt_regset_assign. auto. rewrite H8. 
  eapply type_of_chunk_correct; eauto.

  assumption.

  apply wt_regset_assign. auto. rewrite H11. rewrite H1.
  assert (type_rtl_function f <> None).
    destruct ros; simpl in H0.
    pattern f. apply Genv.find_funct_prop with function p (rs#r).
    exact wt_p. exact H0. 
    caseEq (Genv.find_symbol ge i); intros; rewrite H12 in H0.
    pattern f. apply Genv.find_funct_ptr_prop with function p b.
    exact wt_p. exact H0.
    discriminate.
  assert (exists env1, wt_function env1 f).
    caseEq (type_rtl_function f); intros; try congruence.
    exists t. apply type_rtl_function_correct; auto.
  elim H13; intros env1 WT_FN1. 
  eapply H3. eexact WT_FN1. rewrite <- H1. rewrite <- H10.
  apply wt_regset_list; auto. 

  assumption.
  assumption.
  assumption.
  eauto.
  eauto.

  assert (WT_INIT: wt_regset env (init_regs args (fn_params f))).
    apply wt_init_regs. rewrite (wt_params env f H4). assumption.
  generalize (H1 env f (refl_equal (fn_code f)) H4 WT_INIT). 
  intro WT_RS.
  generalize (wt_instrs env _ H4 pc _ H2).
  intro WT_INSTR; inversion WT_INSTR.
  destruct or; simpl in H3; simpl in H7; rewrite <- H7.
  rewrite H3. apply WT_RS. 
  rewrite H3. simpl; auto.
Qed. 

End SUBJECT_REDUCTION.
