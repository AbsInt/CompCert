(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines a number of data types and operations used in
  the abstract syntax trees of many of the intermediate languages. *)

Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Floats.

Set Implicit Arguments.

(** * Syntactic elements *)

(** Identifiers (names of local variables, of global symbols and functions,
  etc) are represented by the type [positive] of positive integers. *)

Definition ident := positive.

Definition ident_eq := peq.

(** The intermediate languages are weakly typed, using only two types:
  [Tint] for integers and pointers, and [Tfloat] for floating-point
  numbers. *)

Inductive typ : Type :=
  | Tint : typ
  | Tfloat : typ.

Definition typesize (ty: typ) : Z :=
  match ty with Tint => 4 | Tfloat => 8 end.

Lemma typesize_pos: forall ty, typesize ty > 0.
Proof. destruct ty; simpl; omega. Qed.

Lemma typ_eq: forall (t1 t2: typ), {t1=t2} + {t1<>t2}.
Proof. decide equality. Qed.

Lemma opt_typ_eq: forall (t1 t2: option typ), {t1=t2} + {t1<>t2}.
Proof. decide equality. apply typ_eq. Qed.

(** Additionally, function definitions and function calls are annotated
  by function signatures indicating the number and types of arguments,
  as well as the type of the returned value if any.  These signatures
  are used in particular to determine appropriate calling conventions
  for the function. *)

Record signature : Type := mksignature {
  sig_args: list typ;
  sig_res: option typ
}.

Definition proj_sig_res (s: signature) : typ :=
  match s.(sig_res) with
  | None => Tint
  | Some t => t
  end.

(** Memory accesses (load and store instructions) are annotated by
  a ``memory chunk'' indicating the type, size and signedness of the
  chunk of memory being accessed. *)

Inductive memory_chunk : Type :=
  | Mint8signed : memory_chunk     (**r 8-bit signed integer *)
  | Mint8unsigned : memory_chunk   (**r 8-bit unsigned integer *)
  | Mint16signed : memory_chunk    (**r 16-bit signed integer *)
  | Mint16unsigned : memory_chunk  (**r 16-bit unsigned integer *)
  | Mint32 : memory_chunk          (**r 32-bit integer, or pointer *)
  | Mfloat32 : memory_chunk        (**r 32-bit single-precision float *)
  | Mfloat64 : memory_chunk.       (**r 64-bit double-precision float *)

(** Initialization data for global variables. *)

Inductive init_data: Type :=
  | Init_int8: int -> init_data
  | Init_int16: int -> init_data
  | Init_int32: int -> init_data
  | Init_float32: float -> init_data
  | Init_float64: float -> init_data
  | Init_space: Z -> init_data
  | Init_addrof: ident -> int -> init_data   (**r address of symbol + offset *)
  | Init_pointer: list init_data -> init_data.

(** Whole programs consist of:
- a collection of function definitions (name and description);
- the name of the ``main'' function that serves as entry point in the program;
- a collection of global variable declarations, consisting of
  a name, initialization data, and additional information.

The type of function descriptions and that of additional information
for variables vary among the various intermediate languages and are
taken as parameters to the [program] type.  The other parts of whole
programs are common to all languages. *)

Record program (F V: Type) : Type := mkprogram {
  prog_funct: list (ident * F);
  prog_main: ident;
  prog_vars: list (ident * list init_data * V)
}.

Definition prog_funct_names (F V: Type) (p: program F V) : list ident :=
  map (@fst ident F) p.(prog_funct).

Definition prog_var_names (F V: Type) (p: program F V) : list ident :=
  map (fun x: ident * list init_data * V => fst(fst x)) p.(prog_vars).

(** * Generic transformations over programs *)

(** We now define a general iterator over programs that applies a given
  code transformation function to all function descriptions and leaves
  the other parts of the program unchanged. *)

Section TRANSF_PROGRAM.

Variable A B V: Type.
Variable transf: A -> B.

Definition transf_program (l: list (ident * A)) : list (ident * B) :=
  List.map (fun id_fn => (fst id_fn, transf (snd id_fn))) l.

Definition transform_program (p: program A V) : program B V :=
  mkprogram
    (transf_program p.(prog_funct))
    p.(prog_main)
    p.(prog_vars).

Lemma transform_program_function:
  forall p i tf,
  In (i, tf) (transform_program p).(prog_funct) ->
  exists f, In (i, f) p.(prog_funct) /\ transf f = tf.
Proof.
  simpl. unfold transf_program. intros.
  exploit list_in_map_inv; eauto. 
  intros [[i' f] [EQ IN]]. simpl in EQ. inversion EQ; subst. 
  exists f; split; auto.
Qed.

End TRANSF_PROGRAM.

(** The following is a variant of [transform_program] where the
  code transformation function can fail and therefore returns an
  option type. *)

Open Local Scope error_monad_scope.
Open Local Scope string_scope.

Section MAP_PARTIAL.

Variable A B C: Type.
Variable prefix_errmsg: A -> errmsg.
Variable f: B -> res C.

Fixpoint map_partial (l: list (A * B)) : res (list (A * C)) :=
  match l with
  | nil => OK nil
  | (a, b) :: rem =>
      match f b with
      | Error msg => Error (prefix_errmsg a ++ msg)%list
      | OK c =>
          do rem' <- map_partial rem; 
          OK ((a, c) :: rem')
      end
  end.

Remark In_map_partial:
  forall l l' a c,
  map_partial l = OK l' ->
  In (a, c) l' ->
  exists b, In (a, b) l /\ f b = OK c.
Proof.
  induction l; simpl.
  intros. inv H. elim H0.
  intros until c. destruct a as [a1 b1].
  caseEq (f b1); try congruence.
  intro c1; intros. monadInv H0. 
  elim H1; intro. inv H0. exists b1; auto. 
  exploit IHl; eauto. intros [b [P Q]]. exists b; auto.
Qed.

Remark map_partial_forall2:
  forall l l',
  map_partial l = OK l' ->
  list_forall2
    (fun (a_b: A * B) (a_c: A * C) =>
       fst a_b = fst a_c /\ f (snd a_b) = OK (snd a_c))
    l l'.
Proof.
  induction l; simpl.
  intros. inv H. constructor.
  intro l'. destruct a as [a b].
  caseEq (f b). 2: congruence. intro c; intros. monadInv H0.  
  constructor. simpl. auto. auto. 
Qed.

End MAP_PARTIAL.

Remark map_partial_total:
  forall (A B C: Type) (prefix: A -> errmsg) (f: B -> C) (l: list (A * B)),
  map_partial prefix (fun b => OK (f b)) l =
  OK (List.map (fun a_b => (fst a_b, f (snd a_b))) l).
Proof.
  induction l; simpl.
  auto.
  destruct a as [a1 b1]. rewrite IHl. reflexivity.
Qed.

Remark map_partial_identity:
  forall (A B: Type) (prefix: A -> errmsg) (l: list (A * B)),
  map_partial prefix (fun b => OK b) l = OK l.
Proof.
  induction l; simpl.
  auto.
  destruct a as [a1 b1]. rewrite IHl. reflexivity.
Qed.

Section TRANSF_PARTIAL_PROGRAM.

Variable A B V: Type.
Variable transf_partial: A -> res B.

Definition prefix_funct_name (id: ident) : errmsg :=
  MSG "In function " :: CTX id :: MSG ": " :: nil.

Definition transform_partial_program (p: program A V) : res (program B V) :=
  do fl <- map_partial prefix_funct_name transf_partial p.(prog_funct);
  OK (mkprogram fl p.(prog_main) p.(prog_vars)).

Lemma transform_partial_program_function:
  forall p tp i tf,
  transform_partial_program p = OK tp ->
  In (i, tf) tp.(prog_funct) ->
  exists f, In (i, f) p.(prog_funct) /\ transf_partial f = OK tf.
Proof.
  intros. monadInv H. simpl in H0.  
  eapply In_map_partial; eauto.
Qed.

Lemma transform_partial_program_main:
  forall p tp,
  transform_partial_program p = OK tp ->
  tp.(prog_main) = p.(prog_main).
Proof.
  intros. monadInv H. reflexivity.
Qed.

Lemma transform_partial_program_vars:
  forall p tp,
  transform_partial_program p = OK tp ->
  tp.(prog_vars) = p.(prog_vars).
Proof.
  intros. monadInv H. reflexivity.
Qed.

End TRANSF_PARTIAL_PROGRAM.

(** The following is a variant of [transform_program_partial] where
  both the program functions and the additional variable information
  are transformed by functions that can fail. *)

Section TRANSF_PARTIAL_PROGRAM2.

Variable A B V W: Type.
Variable transf_partial_function: A -> res B.
Variable transf_partial_variable: V -> res W.

Definition prefix_var_name (id_init: ident * list init_data) : errmsg :=
  MSG "In global variable " :: CTX (fst id_init) :: MSG ": " :: nil.

Definition transform_partial_program2 (p: program A V) : res (program B W) :=
  do fl <- map_partial prefix_funct_name transf_partial_function p.(prog_funct);
  do vl <- map_partial prefix_var_name transf_partial_variable p.(prog_vars);
  OK (mkprogram fl p.(prog_main) vl).

Lemma transform_partial_program2_function:
  forall p tp i tf,
  transform_partial_program2 p = OK tp ->
  In (i, tf) tp.(prog_funct) ->
  exists f, In (i, f) p.(prog_funct) /\ transf_partial_function f = OK tf.
Proof.
  intros. monadInv H.  
  eapply In_map_partial; eauto. 
Qed.

Lemma transform_partial_program2_variable:
  forall p tp i tv,
  transform_partial_program2 p = OK tp ->
  In (i, tv) tp.(prog_vars) ->
  exists v, In (i, v) p.(prog_vars) /\ transf_partial_variable v = OK tv.
Proof.
  intros. monadInv H. 
  eapply In_map_partial; eauto. 
Qed.

Lemma transform_partial_program2_main:
  forall p tp,
  transform_partial_program2 p = OK tp ->
  tp.(prog_main) = p.(prog_main).
Proof.
  intros. monadInv H. reflexivity.
Qed.

End TRANSF_PARTIAL_PROGRAM2.

(** The following is a relational presentation of 
  [transform_program_partial2].  Given relations between function
  definitions and between variable information, it defines a relation
  between programs stating that the two programs have the same shape
  (same global names, etc) and that identically-named function definitions 
  are variable information are related. *)

Section MATCH_PROGRAM.

Variable A B V W: Type.
Variable match_fundef: A -> B -> Prop.
Variable match_varinfo: V -> W -> Prop.

Definition match_funct_entry (x1: ident * A) (x2: ident * B) :=
  match x1, x2 with
  | (id1, fn1), (id2, fn2) => id1 = id2 /\ match_fundef fn1 fn2
  end.

Definition match_var_entry (x1: ident * list init_data * V) (x2: ident * list init_data * W) :=
  match x1, x2 with
  | (id1, init1, info1), (id2, init2, info2) => id1 = id2 /\ init1 = init2 /\ match_varinfo info1 info2
  end.

Definition match_program (p1: program A V) (p2: program B W) : Prop :=
  list_forall2 match_funct_entry p1.(prog_funct) p2.(prog_funct)
  /\ p1.(prog_main) = p2.(prog_main)
  /\ list_forall2 match_var_entry p1.(prog_vars) p2.(prog_vars).

End MATCH_PROGRAM.

Remark transform_partial_program2_match:
  forall (A B V W: Type)
         (transf_partial_function: A -> res B)
         (transf_partial_variable: V -> res W)
         (p: program A V) (tp: program B W),
  transform_partial_program2 transf_partial_function transf_partial_variable p = OK tp ->
  match_program 
    (fun fd tfd => transf_partial_function fd = OK tfd)
    (fun info tinfo => transf_partial_variable info = OK tinfo)
    p tp.
Proof.
  intros. monadInv H. split.
  apply list_forall2_imply with
    (fun (ab: ident * A) (ac: ident * B) =>
       fst ab = fst ac /\ transf_partial_function (snd ab) = OK (snd ac)).
  eapply map_partial_forall2. eauto. 
  intros. destruct v1; destruct v2; simpl in *. auto.
  split. auto.
  apply list_forall2_imply with
    (fun (ab: ident * list init_data * V) (ac: ident * list init_data * W) =>
       fst ab = fst ac /\ transf_partial_variable (snd ab) = OK (snd ac)).
  eapply map_partial_forall2. eauto. 
  intros. destruct v1; destruct v2; simpl in *. destruct p0; destruct p1. intuition congruence.
Qed.

(** * External functions *)

(** For most languages, the functions composing the program are either
  internal functions, defined within the language, or external functions
  (a.k.a. system calls) that emit an event when applied.  We define
  a type for such functions and some generic transformation functions. *)

Record external_function : Type := mkextfun {
  ef_id: ident;
  ef_sig: signature
}.

Inductive fundef (F: Type): Type :=
  | Internal: F -> fundef F
  | External: external_function -> fundef F.

Implicit Arguments External [F].

Section TRANSF_FUNDEF.

Variable A B: Type.
Variable transf: A -> B.

Definition transf_fundef (fd: fundef A): fundef B :=
  match fd with
  | Internal f => Internal (transf f)
  | External ef => External ef
  end.

End TRANSF_FUNDEF.

Section TRANSF_PARTIAL_FUNDEF.

Variable A B: Type.
Variable transf_partial: A -> res B.

Definition transf_partial_fundef (fd: fundef A): res (fundef B) :=
  match fd with
  | Internal f => do f' <- transf_partial f; OK (Internal f')
  | External ef => OK (External ef)
  end.

End TRANSF_PARTIAL_FUNDEF.

