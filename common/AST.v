(** This file defines a number of data types and operations used in
  the abstract syntax trees of many of the intermediate languages. *)

Require Import Coqlib.
Require Import Integers.
Require Import Floats.

Set Implicit Arguments.

(** Identifiers (names of local variables, of global symbols and functions,
  etc) are represented by the type [positive] of positive integers. *)

Definition ident := positive.

Definition ident_eq := peq.

(** The languages are weakly typed, using only two types: [Tint] for
  integers and pointers, and [Tfloat] for floating-point numbers. *)

Inductive typ : Set :=
  | Tint : typ
  | Tfloat : typ.

Definition typesize (ty: typ) : Z :=
  match ty with Tint => 4 | Tfloat => 8 end.

(** Additionally, function definitions and function calls are annotated
  by function signatures indicating the number and types of arguments,
  as well as the type of the returned value if any.  These signatures
  are used in particular to determine appropriate calling conventions
  for the function. *)

Record signature : Set := mksignature {
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

Inductive memory_chunk : Set :=
  | Mint8signed : memory_chunk     (**r 8-bit signed integer *)
  | Mint8unsigned : memory_chunk   (**r 8-bit unsigned integer *)
  | Mint16signed : memory_chunk    (**r 16-bit signed integer *)
  | Mint16unsigned : memory_chunk  (**r 16-bit unsigned integer *)
  | Mint32 : memory_chunk          (**r 32-bit integer, or pointer *)
  | Mfloat32 : memory_chunk        (**r 32-bit single-precision float *)
  | Mfloat64 : memory_chunk.       (**r 64-bit double-precision float *)

(** Initialization data for global variables. *)

Inductive init_data: Set :=
  | Init_int8: int -> init_data
  | Init_int16: int -> init_data
  | Init_int32: int -> init_data
  | Init_float32: float -> init_data
  | Init_float64: float -> init_data
  | Init_space: Z -> init_data
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

Record program (F V: Set) : Set := mkprogram {
  prog_funct: list (ident * F);
  prog_main: ident;
  prog_vars: list (ident * list init_data * V)
}.

(** We now define a general iterator over programs that applies a given
  code transformation function to all function descriptions and leaves
  the other parts of the program unchanged. *)

Section TRANSF_PROGRAM.

Variable A B V: Set.
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

Section MAP_PARTIAL.

Variable A B C: Set.
Variable f: B -> option C.

Fixpoint map_partial (l: list (A * B)) : option (list (A * C)) :=
  match l with
  | nil => Some nil
  | (a, b) :: rem =>
      match f b with
      | None => None
      | Some c =>
          match map_partial rem with
          | None => None
          | Some res => Some ((a, c) :: res)
          end
      end
  end.

Remark In_map_partial:
  forall l l' a c,
  map_partial l = Some l' ->
  In (a, c) l' ->
  exists b, In (a, b) l /\ f b = Some c.
Proof.
  induction l; simpl.
  intros. inversion H; subst. elim H0.
  destruct a as [a1 b1]. intros until c.
  caseEq (f b1); try congruence.
  intros c1 EQ1. caseEq (map_partial l); try congruence.
  intros res EQ2 EQ3 IN. inversion EQ3; clear EQ3; subst l'.
  elim IN; intro. inversion H; subst. 
  exists b1; auto.
  exploit IHl; eauto. intros [b [P Q]]. exists b; auto.
Qed.

End MAP_PARTIAL.

Remark map_partial_total:
  forall (A B C: Set) (f: B -> C) (l: list (A * B)),
  map_partial (fun b => Some (f b)) l =
  Some (List.map (fun a_b => (fst a_b, f (snd a_b))) l).
Proof.
  induction l; simpl.
  auto.
  destruct a as [a1 b1]. rewrite IHl. reflexivity.
Qed.

Remark map_partial_identity:
  forall (A B: Set) (l: list (A * B)),
  map_partial (fun b => Some b) l = Some l.
Proof.
  induction l; simpl.
  auto.
  destruct a as [a1 b1]. rewrite IHl. reflexivity.
Qed.

Section TRANSF_PARTIAL_PROGRAM.

Variable A B V: Set.
Variable transf_partial: A -> option B.

Function transform_partial_program (p: program A V) : option (program B V) :=
  match map_partial transf_partial p.(prog_funct) with
  | None => None
  | Some fl => Some (mkprogram fl p.(prog_main) p.(prog_vars))
  end.

Lemma transform_partial_program_function:
  forall p tp i tf,
  transform_partial_program p = Some tp ->
  In (i, tf) tp.(prog_funct) ->
  exists f, In (i, f) p.(prog_funct) /\ transf_partial f = Some tf.
Proof.
  intros. functional inversion H. 
  apply In_map_partial with fl; auto. 
  inversion H; subst tp; assumption.
Qed.

Lemma transform_partial_program_main:
  forall p tp,
  transform_partial_program p = Some tp ->
  tp.(prog_main) = p.(prog_main).
Proof.
  intros. functional inversion H. reflexivity.
Qed.

Lemma transform_partial_program_vars:
  forall p tp,
  transform_partial_program p = Some tp ->
  tp.(prog_vars) = p.(prog_vars).
Proof.
  intros. functional inversion H. reflexivity.
Qed.

End TRANSF_PARTIAL_PROGRAM.

(** The following is a variant of [transform_program_partial] where
  both the program functions and the additional variable information
  are transformed by functions that can fail. *)

Section TRANSF_PARTIAL_PROGRAM2.

Variable A B V W: Set.
Variable transf_partial_function: A -> option B.
Variable transf_partial_variable: V -> option W.

Function transform_partial_program2 (p: program A V) : option (program B W) :=
  match map_partial transf_partial_function p.(prog_funct) with
  | None => None
  | Some fl =>
      match map_partial transf_partial_variable p.(prog_vars) with
      | None => None
      | Some vl => Some (mkprogram fl p.(prog_main) vl)
      end
  end.

Lemma transform_partial_program2_function:
  forall p tp i tf,
  transform_partial_program2 p = Some tp ->
  In (i, tf) tp.(prog_funct) ->
  exists f, In (i, f) p.(prog_funct) /\ transf_partial_function f = Some tf.
Proof.
  intros. functional inversion H. 
  apply In_map_partial with fl. auto. subst tp; assumption.
Qed.

Lemma transform_partial_program2_variable:
  forall p tp i tv,
  transform_partial_program2 p = Some tp ->
  In (i, tv) tp.(prog_vars) ->
  exists v, In (i, v) p.(prog_vars) /\ transf_partial_variable v = Some tv.
Proof.
  intros. functional inversion H. 
  apply In_map_partial with vl. auto. subst tp; assumption.
Qed.

Lemma transform_partial_program2_main:
  forall p tp,
  transform_partial_program2 p = Some tp ->
  tp.(prog_main) = p.(prog_main).
Proof.
  intros. functional inversion H. reflexivity.
Qed.

End TRANSF_PARTIAL_PROGRAM2.

(** For most languages, the functions composing the program are either
  internal functions, defined within the language, or external functions
  (a.k.a. system calls) that emit an event when applied.  We define
  a type for such functions and some generic transformation functions. *)

Record external_function : Set := mkextfun {
  ef_id: ident;
  ef_sig: signature
}.

Inductive fundef (F: Set): Set :=
  | Internal: F -> fundef F
  | External: external_function -> fundef F.

Implicit Arguments External [F].

Section TRANSF_FUNDEF.

Variable A B: Set.
Variable transf: A -> B.

Definition transf_fundef (fd: fundef A): fundef B :=
  match fd with
  | Internal f => Internal (transf f)
  | External ef => External ef
  end.

End TRANSF_FUNDEF.

Section TRANSF_PARTIAL_FUNDEF.

Variable A B: Set.
Variable transf_partial: A -> option B.

Definition transf_partial_fundef (fd: fundef A): option (fundef B) :=
  match fd with
  | Internal f =>
      match transf_partial f with
      | None => None
      | Some f' => Some (Internal f')
      end
  | External ef => Some (External ef)
  end.

End TRANSF_PARTIAL_FUNDEF.

