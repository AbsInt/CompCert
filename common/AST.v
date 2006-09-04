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
  | Init_space: Z -> init_data.

(** Whole programs consist of:
- a collection of function definitions (name and description);
- the name of the ``main'' function that serves as entry point in the program;
- a collection of global variable declarations (name and initializer).

The type of function descriptions varies among the various intermediate
languages and is taken as parameter to the [program] type.  The other parts
of whole programs are common to all languages. *)

Record program (funct: Set) : Set := mkprogram {
  prog_funct: list (ident * funct);
  prog_main: ident;
  prog_vars: list (ident * list init_data)
}.

(** We now define a general iterator over programs that applies a given
  code transformation function to all function descriptions and leaves
  the other parts of the program unchanged. *)

Section TRANSF_PROGRAM.

Variable A B: Set.
Variable transf: A -> B.

Fixpoint transf_program (l: list (ident * A)) : list (ident * B) :=
  match l with
  | nil => nil
  | (id, fn) :: rem => (id, transf fn) :: transf_program rem
  end.

Definition transform_program (p: program A) : program B :=
  mkprogram
    (transf_program p.(prog_funct))
    p.(prog_main)
    p.(prog_vars).

Remark transf_program_functions:
  forall fl i tf,
  In (i, tf) (transf_program fl) ->
  exists f, In (i, f) fl /\ transf f = tf.
Proof.
  induction fl; simpl.
  tauto.
  destruct a. simpl. intros.
  elim H; intro. exists a. split. left. congruence. congruence.
  generalize (IHfl _ _ H0). intros [f [IN TR]].
  exists f. split. right. auto. auto.
Qed.

Lemma transform_program_function:
  forall p i tf,
  In (i, tf) (transform_program p).(prog_funct) ->
  exists f, In (i, f) p.(prog_funct) /\ transf f = tf.
Proof.
  simpl. intros. eapply transf_program_functions; eauto.
Qed.

End TRANSF_PROGRAM.

(** The following is a variant of [transform_program] where the
  code transformation function can fail and therefore returns an
  option type. *)

Section TRANSF_PARTIAL_PROGRAM.

Variable A B: Set.
Variable transf_partial: A -> option B.

Fixpoint transf_partial_program
            (l: list (ident * A)) : option (list (ident * B)) :=
  match l with
  | nil => Some nil
  | (id, fn) :: rem =>
      match transf_partial fn with
      | None => None
      | Some fn' =>
          match transf_partial_program rem with
          | None => None
          | Some res => Some ((id, fn') :: res)
          end
      end
  end.

Definition transform_partial_program (p: program A) : option (program B) :=
  match transf_partial_program p.(prog_funct) with
  | None => None
  | Some fl => Some (mkprogram fl p.(prog_main) p.(prog_vars))
  end.

Remark transf_partial_program_functions:
  forall fl tfl i tf,
  transf_partial_program fl = Some tfl ->
  In (i, tf) tfl ->
  exists f, In (i, f) fl /\ transf_partial f = Some tf.
Proof.
  induction fl; simpl.
  intros; injection H; intro; subst tfl; contradiction.
  case a; intros id fn. intros until tf.
  caseEq (transf_partial fn).
  intros tfn TFN.
  caseEq (transf_partial_program fl).
  intros tfl1 TFL1 EQ. injection EQ; intro; clear EQ; subst tfl.
  simpl.  intros [EQ1|IN1].
  exists fn. intuition congruence.
  generalize (IHfl _ _ _ TFL1 IN1).
  intros [f [X Y]].
  exists f. intuition congruence.
  intros; discriminate.
  intros; discriminate.
Qed.

Lemma transform_partial_program_function:
  forall p tp i tf,
  transform_partial_program p = Some tp ->
  In (i, tf) tp.(prog_funct) ->
  exists f, In (i, f) p.(prog_funct) /\ transf_partial f = Some tf.
Proof.
  intros until tf.
  unfold transform_partial_program.
  caseEq (transf_partial_program (prog_funct p)).
  intros. apply transf_partial_program_functions with l; auto.
  injection H0; intros; subst tp. exact H1.
  intros; discriminate.
Qed.

Lemma transform_partial_program_main:
  forall p tp,
  transform_partial_program p = Some tp ->
  tp.(prog_main) = p.(prog_main).
Proof.
  intros p tp. unfold transform_partial_program.
  destruct (transf_partial_program (prog_funct p)).
  intro EQ; injection EQ; intro EQ1; rewrite <- EQ1; reflexivity.
  intro; discriminate.
Qed.

End TRANSF_PARTIAL_PROGRAM.

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

