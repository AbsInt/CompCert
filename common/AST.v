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

(** The type (integer/pointer or float) of a chunk. *)

Definition type_of_chunk (c: memory_chunk) : typ :=
  match c with
  | Mint8signed => Tint
  | Mint8unsigned => Tint
  | Mint16signed => Tint
  | Mint16unsigned => Tint
  | Mint32 => Tint
  | Mfloat32 => Tfloat
  | Mfloat64 => Tfloat
  end.

(** Initialization data for global variables. *)

Inductive init_data: Type :=
  | Init_int8: int -> init_data
  | Init_int16: int -> init_data
  | Init_int32: int -> init_data
  | Init_float32: float -> init_data
  | Init_float64: float -> init_data
  | Init_space: Z -> init_data
  | Init_addrof: ident -> int -> init_data.  (**r address of symbol + offset *)

(** Information attached to global variables. *)

Record globvar (V: Type) : Type := mkglobvar {
  gvar_info: V;                    (**r language-dependent info, e.g. a type *)
  gvar_init: list init_data;       (**r initialization data *)
  gvar_readonly: bool;             (**r read-only variable? (const) *)
  gvar_volatile: bool              (**r volatile variable? *)
}.

(** Whole programs consist of:
- a collection of function definitions (name and description);
- the name of the ``main'' function that serves as entry point in the program;
- a collection of global variable declarations (name and information).

The type of function descriptions and that of additional information
for variables vary among the various intermediate languages and are
taken as parameters to the [program] type.  The other parts of whole
programs are common to all languages. *)

Record program (F V: Type) : Type := mkprogram {
  prog_funct: list (ident * F);
  prog_main: ident;
  prog_vars: list (ident * globvar V)
}.

Definition prog_funct_names (F V: Type) (p: program F V) : list ident :=
  map (@fst ident F) p.(prog_funct).

Definition prog_var_names (F V: Type) (p: program F V) : list ident :=
  map (@fst ident (globvar V)) p.(prog_vars).

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

Definition prefix_name (id: ident) : errmsg :=
  MSG "In function " :: CTX id :: MSG ": " :: nil.

Definition transform_partial_program (p: program A V) : res (program B V) :=
  do fl <- map_partial prefix_name transf_partial p.(prog_funct);
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

Definition transf_globvar (g: globvar V) : res (globvar W) :=
  do info' <- transf_partial_variable g.(gvar_info);
  OK (mkglobvar info' g.(gvar_init) g.(gvar_readonly) g.(gvar_volatile)).

Definition transform_partial_program2 (p: program A V) : res (program B W) :=
  do fl <- map_partial prefix_name transf_partial_function p.(prog_funct);
  do vl <- map_partial prefix_name transf_globvar p.(prog_vars);
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
  forall p tp i tg,
  transform_partial_program2 p = OK tp ->
  In (i, tg) tp.(prog_vars) ->
  exists v,
     In (i, mkglobvar v tg.(gvar_init) tg.(gvar_readonly) tg.(gvar_volatile)) p.(prog_vars)
  /\ transf_partial_variable v = OK tg.(gvar_info).
Proof.
  intros. monadInv H. exploit In_map_partial; eauto. intros [g [P Q]].
  monadInv Q. simpl in *. exists (gvar_info g); split. destruct g; auto. auto.
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

Inductive match_funct_entry: ident * A -> ident * B -> Prop :=
  | match_funct_entry_intro: forall id fn1 fn2,
      match_fundef fn1 fn2 ->
      match_funct_entry (id, fn1) (id, fn2).

Inductive match_var_entry: ident * globvar V -> ident * globvar W -> Prop :=
  | match_var_entry_intro: forall id info1 info2 init ro vo,
      match_varinfo info1 info2 ->
      match_var_entry (id, mkglobvar info1 init ro vo)
                      (id, mkglobvar info2 init ro vo).

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
  intros. destruct v1; destruct v2; simpl in *. destruct H1; subst. constructor. auto.
  split. auto.
  apply list_forall2_imply with
    (fun (ab: ident * globvar V) (ac: ident * globvar W) =>
       fst ab = fst ac /\ transf_globvar transf_partial_variable (snd ab) = OK (snd ac)).
  eapply map_partial_forall2. eauto. 
  intros. destruct v1; destruct v2; simpl in *. destruct H1; subst. 
  monadInv H2. destruct g; simpl in *. constructor. auto.
Qed.

(** * External functions *)

(** For most languages, the functions composing the program are either
  internal functions, defined within the language, or external functions
  (a.k.a. system calls) that emit an event when applied.  We define
  a type for such functions and some generic transformation functions. *)

Record external_function : Type := mkextfun {
  ef_id: ident;
  ef_sig: signature;
  ef_inline: bool
}.

(** Function definitions are the union of internal and external functions. *)

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

