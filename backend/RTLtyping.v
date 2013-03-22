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

(** Typing rules and a type inference algorithm for RTL. *)

Require Import Recdef.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import Globalenvs.
Require Import Values.
Require Import Integers.
Require Import Events.
Require Import RTL.
Require Import Conventions.

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

  Finally, we also check that the successors of instructions
  are valid, i.e. refer to non-empty nodes in the CFG.

  The typing judgement for instructions is of the form [wt_instr f env
  instr], where [f] is the current function (used to type-check
  [Ireturn] instructions) and [env] is a typing environment
  associating types to pseudo-registers.  Since pseudo-registers have
  unique types throughout the function, the typing environment does
  not change during type-checking of individual instructions.  One
  point to note is that we have one polymorphic operator, [Omove],
  which can work over both integers and floats.
*)

Definition regenv := reg -> typ.

Section WT_INSTR.

Variable env: regenv.
Variable funct: function.

Definition valid_successor (s: node) : Prop :=
  exists i, funct.(fn_code)!s = Some i.

Inductive wt_instr : instruction -> Prop :=
  | wt_Inop:
      forall s,
      valid_successor s ->
      wt_instr (Inop s)
  | wt_Iopmove:
      forall r1 r s,
      env r1 = env r ->
      valid_successor s ->
      wt_instr (Iop Omove (r1 :: nil) r s)
  | wt_Iop:
      forall op args res s,
      op <> Omove ->
      (List.map env args, env res) = type_of_operation op ->
      valid_successor s ->
      wt_instr (Iop op args res s)
  | wt_Iload:
      forall chunk addr args dst s,
      List.map env args = type_of_addressing addr ->
      env dst = type_of_chunk chunk ->
      valid_successor s ->
      wt_instr (Iload chunk addr args dst s)
  | wt_Istore:
      forall chunk addr args src s,
      List.map env args = type_of_addressing addr ->
      env src = type_of_chunk chunk ->
      valid_successor s ->
      wt_instr (Istore chunk addr args src s)
  | wt_Icall:
      forall sig ros args res s,
      match ros with inl r => env r = Tint | inr s => True end ->
      List.map env args = sig.(sig_args) ->
      env res = proj_sig_res sig ->
      valid_successor s ->
      wt_instr (Icall sig ros args res s)
  | wt_Itailcall:
      forall sig ros args,
      match ros with inl r => env r = Tint | inr s => True end ->
      sig.(sig_res) = funct.(fn_sig).(sig_res) ->
      List.map env args = sig.(sig_args) ->
      tailcall_possible sig ->
      wt_instr (Itailcall sig ros args)
  | wt_Ibuiltin:
      forall ef args res s,
      List.map env args = (ef_sig ef).(sig_args) ->
      env res = proj_sig_res (ef_sig ef) ->
      arity_ok (ef_sig ef).(sig_args) = true \/ ef_reloads ef = false ->
      valid_successor s ->
      wt_instr (Ibuiltin ef args res s)
  | wt_Icond:
      forall cond args s1 s2,
      List.map env args = type_of_condition cond ->
      valid_successor s1 ->
      valid_successor s2 ->
      wt_instr (Icond cond args s1 s2)
  | wt_Ijumptable:
      forall arg tbl,
      env arg = Tint ->
      (forall s, In s tbl -> valid_successor s) ->
      list_length_z tbl * 4 <= Int.max_unsigned ->
      wt_instr (Ijumptable arg tbl)
  | wt_Ireturn: 
      forall optres,
      option_map env optres = funct.(fn_sig).(sig_res) ->
      wt_instr (Ireturn optres).

End WT_INSTR.

(** A function [f] is well-typed w.r.t. a typing environment [env],
   written [wt_function env f], if all instructions are well-typed,
   parameters agree in types with the function signature, and
   parameters are pairwise distinct. *)

Record wt_function (f: function) (env: regenv): Prop :=
  mk_wt_function {
    wt_params:
      List.map env f.(fn_params) = f.(fn_sig).(sig_args);
    wt_norepet:
      list_norepet f.(fn_params);
    wt_instrs:
      forall pc instr, 
      f.(fn_code)!pc = Some instr -> wt_instr env f instr;
    wt_entrypoint:
      valid_successor f f.(fn_entrypoint)
}.

Inductive wt_fundef: fundef -> Prop :=
  | wt_fundef_external: forall ef,
      wt_fundef (External ef)
  | wt_function_internal: forall f env,
      wt_function f env ->
      wt_fundef (Internal f).

Definition wt_program (p: program): Prop :=
  forall i f, In (i, Gfun f) (prog_defs p) -> wt_fundef f.

(** * Type inference *)

Section INFERENCE.

Local Open Scope error_monad_scope.

Variable f: function.

(** The type inference engine operates over a state that has two components:
- [te_typ]: a partial map from pseudoregisters to types, for
  pseudoregs whose types are already determined from their uses;
- [te_eqs]: a list of pairs [(r1,r2)] of pseudoregisters, indicating that
  [r1] and [r2] must have the same type because they are involved in a move
  [r1 := r2] or [r2 := r1], but this type is not yet determined.
*)

Record typenv : Type := Typenv {
  te_typ: PTree.t typ;            (**r mapping reg -> known type *)
  te_eqs: list (reg * reg)        (**r pairs of regs that must have same type *)
}.

(** Determine that [r] must have type [ty]. *)

Definition type_reg (e: typenv) (r: reg) (ty: typ) : res typenv :=
  match e.(te_typ)!r with
  | None => OK {| te_typ := PTree.set r ty e.(te_typ); te_eqs := e.(te_eqs) |}
  | Some ty' => if typ_eq ty ty' then OK e else Error (MSG "bad type for variable " :: POS r :: nil)
  end.

Fixpoint type_regs (e: typenv) (rl: list reg) (tyl: list typ) {struct rl}: res typenv :=
  match rl, tyl with
  | nil, nil => OK e
  | r1::rs, ty1::tys => do e1 <- type_reg e r1 ty1; type_regs e1 rs tys
  | _, _ => Error (msg "arity mismatch")
  end.

Definition type_ros (e: typenv) (ros: reg + ident) : res typenv :=
  match ros with
  | inl r => type_reg e r Tint
  | inr s => OK e
  end.

(** Determine that [r1] and [r2] must have the same type.  If none of
  [r1] and [r2] has known type, just record an equality constraint.
  The boolean result is [true] if one of the types of [r1] and [r2]
  was previously unknown and could be determined because the other type is
  known.  Otherwise, [te_typ] does not change and [false] is returned. *)

Function type_move (e: typenv) (r1 r2: reg) : res (bool * typenv) :=
  match e.(te_typ)!r1, e.(te_typ)!r2 with
  | None, None =>
      OK (false, {| te_typ := e.(te_typ); te_eqs := (r1, r2) :: e.(te_eqs) |})
  | Some ty1, None =>
      OK (true, {| te_typ := PTree.set r2 ty1 e.(te_typ); te_eqs := e.(te_eqs) |})
  | None, Some ty2 =>
      OK (true, {| te_typ := PTree.set r1 ty2 e.(te_typ); te_eqs := e.(te_eqs) |})
  | Some ty1, Some ty2 =>
      if typ_eq ty1 ty2
      then OK (false, e)
      else Error(MSG "ill-typed move between " :: POS r1 :: MSG " and " :: POS r2 :: nil)
  end.

(** Checking the validity of successor nodes. *)

Definition check_successor (s: node): res unit :=
  match f.(fn_code)!s with
  | None => Error (MSG "bad successor " :: POS s :: nil)
  | Some i => OK tt
  end.

Fixpoint check_successors (sl: list node): res unit :=
  match sl with
  | nil => OK tt
  | s1 :: sl' => do x <- check_successor s1; check_successors sl'
  end.

Definition is_move (op: operation) : bool :=
  match op with Omove => true | _ => false end.

(** First pass: check structural constraints and process all type constraints
  of the form [typeof(r) = ty] arising from the RTL instructions.
  Simultaneously, record equations [typeof(r1) = typeof(r2)] arising
  from move instructions that cannot be immediately resolved. *)

Definition type_instr (e: typenv) (i: instruction) : res typenv :=
  match i with
  | Inop s =>
      do x <- check_successor s; OK e
  | Iop op args res s =>
      do x <- check_successor s;
      if is_move op then
        match args with
        | arg :: nil => do (changed, e') <- type_move e arg res; OK e'
        | _ => Error (msg "ill-formed move")
        end
      else
       (let (targs, tres) := type_of_operation op in
        do e1 <- type_regs e args targs; type_reg e1 res tres)
  | Iload chunk addr args dst s =>
      do x <- check_successor s;
      do e1 <- type_regs e args (type_of_addressing addr);
      type_reg e1 dst (type_of_chunk chunk)
  | Istore chunk addr args src s =>
      do x <- check_successor s;
      do e1 <- type_regs e args (type_of_addressing addr);
      type_reg e1 src (type_of_chunk chunk)
  | Icall sig ros args res s =>
      do x <- check_successor s;
      do e1 <- type_ros e ros;
      do e2 <- type_regs e1 args sig.(sig_args);
      type_reg e2 res (proj_sig_res sig)
  | Itailcall sig ros args =>
      do e1 <- type_ros e ros;
      do e2 <- type_regs e1 args sig.(sig_args);
      if opt_typ_eq sig.(sig_res) f.(fn_sig).(sig_res) then
        if tailcall_is_possible sig
        then OK e2
        else Error(msg "tailcall not possible")
      else Error(msg "bad return type in tailcall")
  | Ibuiltin ef args res s =>
      let sig := ef_sig ef in
      do x <- check_successor s;
      do e1 <- type_regs e args sig.(sig_args);
      do e2 <- type_reg e1 res (proj_sig_res sig);
      if (negb (ef_reloads ef)) || arity_ok sig.(sig_args)
      then OK e2
      else Error(msg "cannot reload builtin")
  | Icond cond args s1 s2 =>
      do x1 <- check_successor s1;
      do x2 <- check_successor s2;
      type_regs e args (type_of_condition cond)
  | Ijumptable arg tbl =>
      do x <- check_successors tbl;
      do e1 <- type_reg e arg Tint;
      if zle (list_length_z tbl * 4) Int.max_unsigned then OK e1 else Error(msg "jumptable too big")
  | Ireturn optres =>
      match optres, f.(fn_sig).(sig_res) with
      | None, None => OK e
      | Some r, Some t => type_reg e r t
      | _, _ => Error(msg "bad return")
      end
  end.

Definition type_code (e: typenv): res typenv :=
  PTree.fold
    (fun re pc i =>
       match re with
       | Error _ => re
       | OK e =>
           match type_instr e i with
           | Error msg => Error(MSG "At PC " :: POS pc :: MSG ": " :: msg)
           | OK e' => OK e'
           end
       end)
    f.(fn_code) (OK e).

(** Second pass: iteratively process the remaining equality constraints
    arising out of "move" instructions *)

Definition equations := list (reg * reg).

Fixpoint solve_rec (e: typenv) (changed: bool) (q: equations) : res (typenv * bool) :=
  match q with 
  | nil =>
      OK (e, changed)
  | (r1, r2) :: q' =>
      do (changed1, e1) <- type_move e r1 r2; solve_rec e1 (changed || changed1) q'
  end.

Lemma type_move_length:
  forall e r1 r2 changed e',
  type_move e r1 r2 = OK (changed, e') ->
  if changed 
  then List.length e'.(te_eqs) = List.length e.(te_eqs)
  else (List.length e'.(te_eqs) <= S (List.length e.(te_eqs)))%nat.
Proof.
  intros. functional inversion H; subst; simpl; omega.
Qed.

Lemma solve_rec_length:
  forall q e changed e' changed',
  solve_rec e changed q = OK (e', changed') ->
  (List.length e'.(te_eqs) <= List.length e.(te_eqs) + List.length q)%nat.
Proof.
  induction q; simpl; intros. 
- inv H. omega.
- destruct a as [r1 r2]. monadInv H. 
  assert (length (te_eqs x0) <= S (length (te_eqs e)))%nat.
  {
    exploit type_move_length; eauto. destruct x; omega. 
  }
  exploit IHq; eauto. 
  omega.
Qed.

Lemma solve_rec_shorter:
  forall q e e',
  solve_rec e false q = OK (e', true) ->
  (List.length e'.(te_eqs) < List.length e.(te_eqs) + List.length q)%nat.
Proof.
  induction q; simpl; intros.
- discriminate.
- destruct a as [r1 r2]; monadInv H.
  exploit type_move_length; eauto. destruct x; intros. 
  exploit solve_rec_length; eauto. omega.
  exploit IHq; eauto. omega.
Qed.

Definition length_typenv (e: typenv) := length e.(te_eqs).

Function solve_equations (e: typenv) {measure length_typenv e} : res typenv :=
  match solve_rec {| te_typ := e.(te_typ); te_eqs := nil |} false e.(te_eqs) with
  | OK (e', false) => OK e                    (**r no progress made: terminate *)
  | OK (e', true) => solve_equations e'       (**r at least one type changed: iterate *)
  | Error msg => Error msg
  end.
Proof.
  intros. exploit solve_rec_shorter; eauto. 
Qed.

(** The final type assignment aribtrarily gives type [Tint] to the 
  pseudoregs that are still unconstrained at the end of type inference. *)

Definition make_regenv (e: typenv) : regenv :=
  fun r => match e.(te_typ)!r with Some ty => ty | None => Tint end.

Definition check_params_norepet (params: list reg): res unit :=
  if list_norepet_dec Reg.eq params then OK tt else Error(msg "duplicate parameters").

Definition type_function : res regenv :=
  do e1 <- type_code {| te_typ := PTree.empty typ; te_eqs := nil |};
  do e2 <- type_regs e1 f.(fn_params) f.(fn_sig).(sig_args);
  do e3 <- solve_equations e2;
  do x1 <- check_params_norepet f.(fn_params);
  do x2 <- check_successor f.(fn_entrypoint);
  OK (make_regenv e3).

(** ** Soundness proof *)

(** What it means for a final type assignment [te] to satisfy the constraints
  collected so far in the [e] state. *)

Definition satisf (te: regenv) (e: typenv) : Prop :=
     (forall r ty, e.(te_typ)!r = Some ty -> te r = ty)
  /\ (forall r1 r2, In (r1, r2) e.(te_eqs) -> te r1 = te r2).

Remark type_reg_incr:
  forall e r ty e' te, type_reg e r ty = OK e' -> satisf te e' -> satisf te e.
Proof.
  unfold type_reg; intros; destruct (e.(te_typ)!r) eqn:E.
  destruct (typ_eq ty t); inv H. auto.
  inv H. destruct H0 as [A B]. split; intros.
  apply A. simpl. rewrite PTree.gso; auto. congruence. 
  apply B. simpl; auto. 
Qed.

Hint Resolve type_reg_incr: ty.

Remark type_regs_incr:
  forall rl tyl e e' te, type_regs e rl tyl = OK e' -> satisf te e' -> satisf te e.
Proof.
  induction rl; simpl; intros; destruct tyl; try discriminate.
  inv H; eauto with ty.
  monadInv H. eauto with ty.
Qed.

Hint Resolve type_regs_incr: ty.

Remark type_ros_incr:
  forall e ros e' te, type_ros e ros = OK e' -> satisf te e' -> satisf te e.
Proof.
  unfold type_ros; intros. destruct ros. eauto with ty. inv H; auto with ty.
Qed.

Hint Resolve type_ros_incr: ty.

Remark type_move_incr:
  forall e r1 r2 changed e' te,
  type_move e r1 r2 = OK (changed, e') ->
  satisf te e' -> satisf te e.
Proof.
  intros. destruct H0 as [A B]. functional inversion H; subst; simpl in *.
- split; auto. 
- split; intros. apply A. rewrite PTree.gso; auto. congruence. auto. 
- split; intros. apply A. rewrite PTree.gso; auto. congruence. auto.
- split; auto.
Qed.

Hint Resolve type_move_incr: ty.

Lemma type_reg_sound:
  forall e r ty e' te, type_reg e r ty = OK e' -> satisf te e' -> te r = ty.
Proof.
  unfold type_reg; intros. destruct H0 as [A B]. 
  destruct (e.(te_typ)!r) as [t|] eqn:E.
  destruct (typ_eq ty t); inv H. apply A; auto.
  inv H. apply A. simpl. apply PTree.gss.
Qed.

Lemma type_regs_sound:
  forall rl tyl e e' te, type_regs e rl tyl = OK e' -> satisf te e' -> map te rl = tyl.
Proof.
  induction rl; simpl; intros; destruct tyl; try discriminate.
- auto.
- monadInv H. f_equal; eauto. eapply type_reg_sound. eauto. eauto with ty. 
Qed.

Lemma type_ros_sound:
  forall e ros e' te, type_ros e ros = OK e' -> satisf te e' ->
  match ros with inl r => te r = Tint | inr s => True end.
Proof.
  unfold type_ros; intros. destruct ros. 
  eapply type_reg_sound; eauto.
  auto.
Qed.

Lemma type_move_sound:
  forall e r1 r2 changed e' te,
  type_move e r1 r2 = OK (changed, e') -> satisf te e' -> te r1 = te r2.
Proof.
  intros. destruct H0 as [A B]. functional inversion H; subst; simpl in *.
- apply B; auto.
- rewrite (A r1 ty1). rewrite (A r2 ty1). auto. 
  apply PTree.gss. rewrite PTree.gso; auto. congruence.
- rewrite (A r1 ty2). rewrite (A r2 ty2). auto. 
  rewrite PTree.gso; auto. congruence. apply PTree.gss.
- erewrite ! A; eauto. 
Qed.

Lemma check_successor_sound:
  forall s x, check_successor s = OK x -> valid_successor f s.
Proof.
  unfold check_successor, valid_successor; intros. 
  destruct (fn_code f)!s; inv H. exists i; auto.
Qed.

Hint Resolve check_successor_sound: ty.

Lemma check_successors_sound:
  forall sl x, check_successors sl = OK x -> forall s, In s sl -> valid_successor f s.
Proof.
  induction sl; simpl; intros. 
  contradiction.
  monadInv H. destruct H0. subst a; eauto with ty. eauto. 
Qed.

Lemma type_instr_incr:
  forall e i e' te,
  type_instr e i = OK e' -> satisf te e' -> satisf te e.
Proof.
  intros; destruct i; try (monadInv H); eauto with ty.
- (* op *)
  destruct (is_move o) eqn:ISMOVE.
  destruct l; try discriminate. destruct l; monadInv EQ0. eauto with ty.
  destruct (type_of_operation o) as [targs tres] eqn:TYOP. monadInv EQ0. eauto with ty.
- (* tailcall *)
  destruct (opt_typ_eq (sig_res s) (sig_res (fn_sig f))); try discriminate.
  destruct (tailcall_is_possible s) eqn:TCIP; inv EQ2.
  eauto with ty.
- (* builtin *)
  destruct (negb (ef_reloads e0) || arity_ok (sig_args (ef_sig e0))) eqn:E; inv EQ3.
  eauto with ty.
- (* jumptable *)
  destruct (zle (list_length_z l * 4) Int.max_unsigned); inv EQ2.
  eauto with ty.
- (* return *)
  simpl in H. destruct o as [r|] eqn: RET; destruct (sig_res (fn_sig f)) as [t|] eqn: RES; try discriminate.
  eauto with ty.
  inv H; auto with ty.
Qed.

Lemma type_instr_sound:
  forall e i e' te,
  type_instr e i = OK e' -> satisf te e' -> wt_instr te f i.
Proof.
  intros; destruct i; try (monadInv H); simpl.
- (* nop *)
  constructor; eauto with ty.
- (* op *)
  destruct (is_move o) eqn:ISMOVE.
  (* move *)
  + assert (o = Omove) by (unfold is_move in ISMOVE; destruct o; congruence).
    subst o.
    destruct l; try discriminate. destruct l; monadInv EQ0.
    constructor. eapply type_move_sound; eauto. eauto with ty.
  + destruct (type_of_operation o) as [targs tres] eqn:TYOP. monadInv EQ0.
    apply wt_Iop. 
    unfold is_move in ISMOVE; destruct o; congruence.
    rewrite TYOP. f_equal. eapply type_regs_sound; eauto with ty. eapply type_reg_sound; eauto.
    eauto with ty.
- (* load *)
  constructor.
  eapply type_regs_sound; eauto with ty. eapply type_reg_sound; eauto.
  eauto with ty.
- (* store *)
  constructor.
  eapply type_regs_sound; eauto with ty. eapply type_reg_sound; eauto.
  eauto with ty.
- (* call *)
  constructor. 
  eapply type_ros_sound; eauto with ty. 
  eapply type_regs_sound; eauto with ty.
  eapply type_reg_sound; eauto.
  eauto with ty.
- (* tailcall *)
  destruct (opt_typ_eq (sig_res s) (sig_res (fn_sig f))); try discriminate.
  destruct (tailcall_is_possible s) eqn:TCIP; inv EQ2.
  constructor.
  eapply type_ros_sound; eauto with ty. 
  auto.
  eapply type_regs_sound; eauto with ty.
  apply tailcall_is_possible_correct; auto.
- (* builtin *)
  destruct (negb (ef_reloads e0) || arity_ok (sig_args (ef_sig e0))) eqn:E; inv EQ3.
  constructor.
  eapply type_regs_sound; eauto with ty.
  eapply type_reg_sound; eauto.
  destruct (ef_reloads e0); auto.
  eauto with ty.
- (* cond *)
  constructor.
  eapply type_regs_sound; eauto with ty.
  eauto with ty.
  eauto with ty.
- (* jumptable *)
  destruct (zle (list_length_z l * 4) Int.max_unsigned); inv EQ2.
  constructor.
  eapply type_reg_sound; eauto.
  eapply check_successors_sound; eauto. 
  auto.
- (* return *)
  simpl in H. destruct o as [r|] eqn: RET; destruct (sig_res (fn_sig f)) as [t|] eqn: RES; try discriminate.
  constructor. simpl. rewrite RES. f_equal. eapply type_reg_sound; eauto.
  inv H. constructor. rewrite RES; auto. 
Qed.

Lemma type_code_sound:
  forall e e' te,
  type_code e = OK e' ->
  forall pc i, f.(fn_code)!pc = Some i -> satisf te e' -> wt_instr te f i.
Proof.
  intros e0 e1 te TCODE.
  set (P := fun c opte =>
         match opte with
         | Error _ => True
         | OK e' => forall pc i, c!pc = Some i -> satisf te e' -> wt_instr te f i
         end).
  assert (P f.(fn_code) (OK e1)).
  {
    rewrite <- TCODE. unfold type_code. apply PTree_Properties.fold_rec; unfold P; intros. 
    - (* extensionality *)
      destruct a; auto. intros. rewrite <- H in H1. eapply H0; eauto. 
    - (* base case *)
      rewrite PTree.gempty in H; discriminate.
    - (* inductive case *)
      destruct a as [e|?]; auto. 
      destruct (type_instr e v) as [e'|?] eqn:TYINSTR; auto.
      intros. rewrite PTree.gsspec in H2. destruct (peq pc k). 
      inv H2. eapply type_instr_sound; eauto. 
      eapply H1; eauto. eapply type_instr_incr; eauto. 
  }
  intros; eapply H; eauto. 
Qed.

Lemma solve_rec_incr:
  forall te q e changed e' changed',
  solve_rec e changed q = OK (e', changed') -> satisf te e' -> satisf te e.
Proof.
  induction q; simpl; intros.
- inv H; auto.
- destruct a as [r1 r2]; monadInv H. eauto with ty. 
Qed.

Lemma solve_rec_sound:
  forall r1 r2 te q e changed e' changed',
  solve_rec e changed q = OK (e', changed') -> satisf te e' -> In (r1, r2) q -> te r1 = te r2.
Proof.
  induction q; simpl; intros.
- contradiction. 
- destruct a as [r3 r4]; monadInv H. destruct H1 as [A|A].
  inv A. eapply type_move_sound; eauto. eapply solve_rec_incr; eauto. 
  eapply IHq; eauto.
Qed.

Lemma solve_rec_false:
  forall q e changed e',
  solve_rec e changed q = OK (e', false) -> changed = false.
Proof.
  induction q; simpl; intros. 
- inv H; auto.
- destruct a as [r1 r2]; monadInv H. exploit IHq; eauto. rewrite orb_false_iff. tauto. 
Qed.

Lemma solve_rec_solved:
  forall r1 r2 q e changed e',
  solve_rec e changed q = OK (e', false) ->
  In (r1, r2) q -> make_regenv e r1 = make_regenv e r2.
Proof.
  induction q; simpl; intros.
- contradiction.
- destruct a as [r3 r4]; monadInv H.
  assert (x = false). 
  { exploit solve_rec_false; eauto. rewrite orb_false_iff. tauto. }
  subst x. functional inversion EQ.
  + destruct H0 as [A|A]. 
    inv A. unfold make_regenv. rewrite H1; rewrite H2; auto.
    subst x0. exploit IHq; eauto.
  + destruct H0 as [A|A]. 
    inv A. unfold make_regenv. rewrite H1; rewrite H2; auto.
    subst x0. exploit IHq; eauto.
Qed.

Lemma solve_equations_incr:
  forall te e e', solve_equations e = OK e' -> satisf te e' -> satisf te e.
Proof.
  intros te e0; functional induction (solve_equations e0); intros.
- inv H. auto.
- exploit solve_rec_incr; eauto. intros [A B]. split; intros.
  apply A; auto.
  eapply solve_rec_sound; eauto. 
- discriminate.
Qed.

Lemma solve_equations_sound:
  forall e e', solve_equations e = OK e' -> satisf (make_regenv e') e'.
Proof.
  intros e0; functional induction (solve_equations e0); intros.
- inv H. split; intros. 
  unfold make_regenv; rewrite H; auto. 
  exploit solve_rec_solved; eauto.
- eauto.
- discriminate.
Qed.

Theorem type_function_correct:
  forall env, type_function = OK env -> wt_function f env.
Proof.
  unfold type_function; intros. monadInv H. 
  exploit solve_equations_sound; eauto. intros SAT1.
  exploit solve_equations_incr; eauto. intros SAT0.
  exploit type_regs_incr; eauto. intros SAT.
  constructor.
- (* type of parameters *)
  eapply type_regs_sound; eauto.
- (* parameters are unique *)
  unfold check_params_norepet in EQ2. 
  destruct (list_norepet_dec Reg.eq (fn_params f)); inv EQ2; auto. 
- (* instructions are well typed *)
  intros; eapply type_code_sound; eauto.
- (* entry point is valid *)
  eauto with ty. 
Qed.

(** ** Completeness proof *)

Lemma type_reg_complete:
  forall te e r ty,
  satisf te e -> te r = ty -> exists e', type_reg e r ty = OK e' /\ satisf te e'.
Proof.
  intros. unfold type_reg. 
  destruct ((te_typ e)!r) as [ty'|] eqn: E.
  exists e; split; auto. replace ty' with ty. apply dec_eq_true.
  exploit (proj1 H); eauto. congruence. 
  econstructor; split. reflexivity. 
  destruct H as [A B]; split; simpl; intros; auto. 
  rewrite PTree.gsspec in H. destruct (peq r0 r); auto. congruence. 
Qed.

Lemma type_regs_complete:
  forall te rl tyl e,
  satisf te e -> map te rl = tyl -> exists e', type_regs e rl tyl = OK e' /\ satisf te e'.
Proof.
  induction rl; simpl; intros; subst tyl.
  exists e; auto.
  destruct (type_reg_complete te e a (te a)) as [e1 [A B]]; auto.
  exploit IHrl; eauto. intros [e' [C D]]. 
  exists e'; split; auto. rewrite A; simpl; rewrite C; auto.
Qed.

Lemma type_ros_complete:
  forall te ros e,
  satisf te e ->
  match ros with inl r => te r = Tint | inr s => True end ->
  exists e', type_ros e ros = OK e' /\ satisf te e'.
Proof.
  intros; destruct ros; simpl. 
  eapply type_reg_complete; eauto.
  exists e; auto.
Qed.

Lemma type_move_complete:
  forall te r1 r2 e,
  satisf te e ->
  te r1 = te r2 ->
  exists changed e', type_move e r1 r2 = OK (changed, e') /\ satisf te e'.
Proof.
  intros. functional induction (type_move e r1 r2). 
- econstructor; econstructor; split; eauto. 
  destruct H as [A B]; split; simpl; intros; auto. 
  destruct H; auto. congruence.
- econstructor; econstructor; split; eauto. 
  destruct H as [A B]; split; simpl; intros; auto. 
  rewrite PTree.gsspec in H. destruct (peq r r2); auto. 
  subst. exploit A; eauto. congruence. 
- econstructor; econstructor; split; eauto. 
  destruct H as [A B]; split; simpl; intros; auto. 
  rewrite PTree.gsspec in H. destruct (peq r r1); auto. 
  subst. exploit A; eauto. congruence.
- econstructor; econstructor; split; eauto.
- destruct H as [A B]. apply A in e0. apply A in e1. congruence. 
Qed.

Lemma check_successor_complete:
  forall s, valid_successor f s -> check_successor s = OK tt.
Proof.
  unfold valid_successor, check_successor; intros. 
  destruct H as [i EQ]; rewrite EQ; auto.
Qed.

Lemma type_instr_complete:
  forall te e i,
  satisf te e ->
  wt_instr te f i ->
  exists e', type_instr e i = OK e' /\ satisf te e'.
Proof.
  induction 2; simpl.
- (* nop *)
  econstructor; split. rewrite check_successor_complete; simpl; eauto. auto.
- (* move *)
  exploit type_move_complete; eauto. intros (changed & e' & A & B).
  exists e'; split. rewrite check_successor_complete by auto; simpl. rewrite A; auto. auto.
- (* other op *)
  destruct (type_of_operation op) as [targ tres]. injection H1; clear H1; intros. 
  exploit type_regs_complete. eauto. eauto. intros [e1 [A B]].
  exploit type_reg_complete. eexact B. eauto. intros [e2 [C D]].
  exists e2; split; auto.
  rewrite check_successor_complete by auto; simpl. 
  replace (is_move op) with false. rewrite A; simpl; rewrite C; auto.
  destruct op; reflexivity || congruence.
- (* load *)
  exploit type_regs_complete. eauto. eauto. intros [e1 [A B]].
  exploit type_reg_complete. eexact B. eauto. intros [e2 [C D]].
  exists e2; split; auto.
  rewrite check_successor_complete by auto; simpl. 
  rewrite A; simpl; rewrite C; auto.
- (* store *)
  exploit type_regs_complete. eauto. eauto. intros [e1 [A B]].
  exploit type_reg_complete. eexact B. eauto. intros [e2 [C D]].
  exists e2; split; auto.
  rewrite check_successor_complete by auto; simpl. 
  rewrite A; simpl; rewrite C; auto.
- (* call *)
  exploit type_ros_complete. eauto. eauto. intros [e1 [A B]].
  exploit type_regs_complete. eauto. eauto. intros [e2 [C D]].
  exploit type_reg_complete. eexact D. eauto. intros [e3 [E F]].
  exists e3; split; auto. 
  rewrite check_successor_complete by auto; simpl. 
  rewrite A; simpl; rewrite C; simpl; rewrite E; auto.
- (* tailcall *)
  exploit type_ros_complete. eauto. eauto. intros [e1 [A B]].
  exploit type_regs_complete. eauto. eauto. intros [e2 [C D]].
  exists e2; split; auto. 
  rewrite A; simpl; rewrite C; simpl. 
  rewrite H1; rewrite dec_eq_true. 
  replace (tailcall_is_possible sig) with true; auto. 
  revert H3. unfold tailcall_possible, tailcall_is_possible. generalize (loc_arguments sig). 
  induction l; simpl; intros. auto.
  exploit (H3 a); auto. intros. destruct a; try contradiction. apply IHl.
  intros; apply H3; auto. 
- (* builtin *)
  exploit type_regs_complete. eauto. eauto. intros [e1 [A B]].
  exploit type_reg_complete. eexact B. eauto. intros [e2 [C D]].
  exists e2; split; auto.
  rewrite check_successor_complete by auto; simpl. 
  rewrite A; simpl; rewrite C; simpl.
  destruct H2; rewrite H2. 
  rewrite orb_true_r. auto. 
  auto. 
- (* cond *)
  exploit type_regs_complete. eauto. eauto. intros [e1 [A B]].
  exists e1; split; auto.
  rewrite check_successor_complete by auto; simpl. 
  rewrite check_successor_complete by auto; simpl.
  auto.
- (* jumptbl *)
  exploit type_reg_complete. eauto. eauto. intros [e1 [A B]].
  exists e1; split; auto.
  replace (check_successors tbl) with (OK tt). simpl. 
  rewrite A; simpl. apply zle_true; auto. 
  revert H1. generalize tbl. induction tbl0; simpl; intros. auto. 
  rewrite check_successor_complete by auto; simpl.
  apply IHtbl0; intros; auto.
- (* return *)
  rewrite <- H0. destruct optres; simpl.
  apply type_reg_complete; auto.
  exists e; auto.
Qed.

Lemma type_code_complete:
  forall te e,
  (forall pc instr, f.(fn_code)!pc = Some instr -> wt_instr te f instr) ->
  satisf te e ->
  exists e', type_code e = OK e' /\ satisf te e'.
Proof.
  intros te e0 WTC SAT0.
  set (P := fun c res =>
        (forall pc i, c!pc = Some i -> wt_instr te f i) ->
        exists e', res = OK e' /\ satisf te e').
  assert (P f.(fn_code) (type_code e0)).
  {
    unfold type_code. apply PTree_Properties.fold_rec; unfold P; intros.
    - apply H0. intros. apply H1 with pc. rewrite <- H; auto. 
    - exists e0; auto. 
    - destruct H1 as [e [A B]]. 
      intros. apply H2 with pc. rewrite PTree.gso; auto. congruence.
      subst a. 
      destruct (type_instr_complete te e v) as [e' [C D]].
      auto. apply H2 with k. apply PTree.gss. 
      exists e'; split; auto. rewrite C; auto. 
  }
  apply H; auto.
Qed.

Lemma solve_rec_complete:
  forall te q e changed,
  satisf te e ->
  (forall r1 r2, In (r1, r2) q -> te r1 = te r2) ->
  exists e' changed', solve_rec e changed q = OK(e', changed') /\ satisf te e'.
Proof.
  induction q; simpl; intros. 
- exists e; exists changed; auto.
- destruct a as [r3 r4]. 
  exploit type_move_complete. eauto. apply H0. left; eauto. 
  intros (changed1 & e1 & A & B).
  destruct (IHq e1 (changed || changed1)) as (e2 & changed2 & C & D); auto.
  exists e2; exists changed2; split; auto. rewrite A; simpl; rewrite C; auto.
Qed.

Lemma solve_equations_complete:
  forall te e,
  satisf te e ->
  exists e', solve_equations e = OK e' /\ satisf te e'.
Proof.
  intros te e0. functional induction (solve_equations e0); intros.
- exists e; auto. 
- destruct (solve_rec_complete te (te_eqs e) {| te_typ := te_typ e; te_eqs := nil |} false)
  as (e1 & changed1 & A & B). 
  destruct H; split; intros. apply H; auto. contradiction.
  exact (proj2 H). 
  rewrite e0 in A. inv A. auto. 
- destruct (solve_rec_complete te (te_eqs e) {| te_typ := te_typ e; te_eqs := nil |} false)
  as (e1 & changed1 & A & B). 
  destruct H; split; intros. apply H; auto. contradiction.
  exact (proj2 H).
  congruence.
Qed.

Theorem type_function_complete:
  forall te, wt_function f te -> exists te, type_function = OK te.
Proof.
  intros. destruct H. 
  destruct (type_code_complete te {| te_typ := PTree.empty typ; te_eqs := nil |}) as (e1 & A & B).
  auto. split; simpl; intros. rewrite PTree.gempty in H; congruence. contradiction.
  destruct (type_regs_complete te f.(fn_params) f.(fn_sig).(sig_args) e1) as (e2 & C & D); auto.
  destruct (solve_equations_complete te e2) as (e3 & E & F); auto.
  exists (make_regenv e3); unfold type_function. 
  rewrite A; simpl. rewrite C; simpl. rewrite E; simpl. 
  unfold check_params_norepet. rewrite pred_dec_true; auto. simpl. 
  rewrite check_successor_complete by auto. auto. 
Qed.

End INFERENCE.

(** * Type preservation during evaluation *)

(** The type system for RTL is not sound in that it does not guarantee
  progress: well-typed instructions such as [Icall] can fail because
  of run-time type tests (such as the equality between callee and caller's
  signatures).  However, the type system guarantees a type preservation
  property: if the execution does not fail because of a failed run-time
  test, the result values and register states match the static
  typing assumptions.  This preservation property will be useful
  later for the proof of semantic equivalence between [Linear] and [Mach].
  Even though we do not need it for [RTL], we show preservation for [RTL]
  here, as a warm-up exercise and because some of the lemmas will be
  useful later. *)

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

Inductive wt_stackframes: list stackframe -> option typ -> Prop :=
  | wt_stackframes_nil:
      wt_stackframes nil (Some Tint)
  | wt_stackframes_cons:
      forall s res f sp pc rs env tyres,
      wt_function f env ->
      wt_regset env rs ->
      env res = match tyres with None => Tint | Some t => t end ->
      wt_stackframes s (sig_res (fn_sig f)) ->
      wt_stackframes (Stackframe res f sp pc rs :: s) tyres.

Inductive wt_state: state -> Prop :=
  | wt_state_intro:
      forall s f sp pc rs m env
        (WT_STK: wt_stackframes s (sig_res (fn_sig f)))
        (WT_FN: wt_function f env)
        (WT_RS: wt_regset env rs),
      wt_state (State s f sp pc rs m)
  | wt_state_call:
      forall s f args m,
      wt_stackframes s (sig_res (funsig f)) ->
      wt_fundef f ->
      Val.has_type_list args (sig_args (funsig f)) ->
      wt_state (Callstate s f args m)
  | wt_state_return:
      forall s v m tyres,
      wt_stackframes s tyres ->
      Val.has_type v (match tyres with None => Tint | Some t => t end) ->
      wt_state (Returnstate s v m).

Section SUBJECT_REDUCTION.

Variable p: program.

Hypothesis wt_p: wt_program p.

Let ge := Genv.globalenv p.

Lemma subject_reduction:
  forall st1 t st2, step ge st1 t st2 ->
  forall (WT: wt_state st1), wt_state st2.
Proof.
  induction 1; intros; inv WT;
  try (generalize (wt_instrs _ _ WT_FN pc _ H);
       intro WT_INSTR;
       inv WT_INSTR).
  (* Inop *)
  econstructor; eauto.
  (* Iop *)
  econstructor; eauto.
  apply wt_regset_assign. auto. 
  simpl in H0. inv H0. rewrite <- H3. apply WT_RS.
  econstructor; eauto.
  apply wt_regset_assign. auto.
  replace (env res) with (snd (type_of_operation op)).
  eapply type_of_operation_sound; eauto.
  rewrite <- H6. reflexivity.
  (* Iload *)
  econstructor; eauto.
  apply wt_regset_assign. auto. rewrite H8. 
  eapply type_of_chunk_correct; eauto.
  (* Istore *)
  econstructor; eauto.
  (* Icall *)
  assert (wt_fundef fd).
    destruct ros; simpl in H0.
    pattern fd. apply Genv.find_funct_prop with fundef unit p (rs#r).
    exact wt_p. exact H0. 
    caseEq (Genv.find_symbol ge i); intros; rewrite H1 in H0.
    pattern fd. apply Genv.find_funct_ptr_prop with fundef unit p b.
    exact wt_p. exact H0.
    discriminate.
  econstructor; eauto.
  econstructor; eauto.
  rewrite <- H7. apply wt_regset_list. auto.
  (* Itailcall *)
  assert (wt_fundef fd).
    destruct ros; simpl in H0.
    pattern fd. apply Genv.find_funct_prop with fundef unit p (rs#r).
    exact wt_p. exact H0. 
    caseEq (Genv.find_symbol ge i); intros; rewrite H1 in H0.
    pattern fd. apply Genv.find_funct_ptr_prop with fundef unit p b.
    exact wt_p. exact H0.
    discriminate.
  econstructor; eauto.
  rewrite H6; auto.
  rewrite <- H7. apply wt_regset_list. auto.
  (* Ibuiltin *)
  econstructor; eauto.
  apply wt_regset_assign. auto. 
  rewrite H6. eapply external_call_well_typed; eauto. 
  (* Icond *)
  econstructor; eauto.
  (* Ijumptable *)
  econstructor; eauto.
  (* Ireturn *)
  econstructor; eauto. 
  destruct or; simpl in *.
  rewrite <- H2. apply WT_RS. exact I.
  (* internal function *)
  simpl in *. inv H5. inversion H1; subst.  
  econstructor; eauto.
  apply wt_init_regs; auto. rewrite wt_params0; auto.
  (* external function *)
  simpl in *. inv H5. 
  econstructor; eauto. 
  change (Val.has_type res (proj_sig_res (ef_sig ef))).
  eapply external_call_well_typed; eauto.
  (* return *)
  inv H1. econstructor; eauto. 
  apply wt_regset_assign; auto. congruence. 
Qed.

End SUBJECT_REDUCTION.
