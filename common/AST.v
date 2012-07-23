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
  | Mfloat64 : memory_chunk        (**r 64-bit double-precision float *)
  | Mfloat64al32 : memory_chunk.   (**r 64-bit double-precision float, 4-aligned *)

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
  | Mfloat64al32 => Tfloat
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

Definition funct_names (F: Type) (fl: list (ident * F)) : list ident :=
  map (@fst ident F) fl. 

Lemma funct_names_app : forall (F: Type) (fl1 fl2 : list (ident * F)),
  funct_names (fl1 ++ fl2) = funct_names fl1 ++ funct_names fl2. 
Proof.
  intros; unfold funct_names; apply list_append_map.
Qed.
  
Definition var_names (V: Type) (vl: list (ident * globvar V)) : list ident :=
  map (@fst ident (globvar V)) vl. 

Lemma var_names_app : forall (V: Type) (vl1 vl2 : list (ident * globvar V)),
  var_names (vl1 ++ vl2) = var_names vl1 ++ funct_names vl2. 
Proof.
  intros; unfold var_names; apply list_append_map.
Qed.
  
Definition prog_funct_names (F V: Type) (p: program F V) : list ident :=
  funct_names p.(prog_funct).

Definition prog_var_names (F V: Type) (p: program F V) : list ident :=
  var_names p.(prog_vars).

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

(** The following is a variant of [transform_partial_program2] where the
     where the set of functions and global data is augmented, and
     the main function is potentially changed. *)

Section TRANSF_PARTIAL_AUGMENT_PROGRAM.

Variable A B V W: Type.
Variable transf_partial_function: A -> res B.
Variable transf_partial_variable: V -> res W.

Variable new_functs : list (ident * B).
Variable new_vars : list (ident * globvar W).
Variable new_main : ident.

Definition transform_partial_augment_program (p: program A V) : res (program B W)  :=
  do fl <- map_partial prefix_name transf_partial_function p.(prog_funct);
  do vl <- map_partial prefix_name (transf_globvar transf_partial_variable) p.(prog_vars);
  OK (mkprogram (fl ++ new_functs) new_main (vl ++ new_vars)).

Lemma transform_partial_augment_program_function:
  forall p tp i tf,
  transform_partial_augment_program p = OK tp ->
  In (i, tf) tp.(prog_funct) ->
  (exists f, In (i, f) p.(prog_funct) /\ transf_partial_function f = OK tf)
  \/ In (i,tf) new_functs.
Proof.
  intros. monadInv H. simpl in H0.  
  rewrite in_app in H0.  destruct H0. 
  left. eapply In_map_partial; eauto.
  right. auto. 
Qed.

Lemma transform_partial_augment_program_main:
  forall p tp,
  transform_partial_augment_program p = OK tp ->
  tp.(prog_main) = new_main.
Proof.
  intros. monadInv H. reflexivity.
Qed.


Lemma transform_partial_augment_program_variable:
  forall p tp i tg,
  transform_partial_augment_program p = OK tp ->
  In (i, tg) tp.(prog_vars) ->
  (exists v, In (i, mkglobvar v tg.(gvar_init) tg.(gvar_readonly) tg.(gvar_volatile)) p.(prog_vars) /\ transf_partial_variable v = OK tg.(gvar_info))
  \/ In (i,tg) new_vars.
Proof.
  intros. monadInv H. 
  simpl in H0.  rewrite in_app in H0.  inversion H0. 
  left. exploit In_map_partial; eauto.  intros [g [P Q]]. 
  monadInv Q. simpl in *. exists (gvar_info g); split. destruct g; auto. auto. 
  right. auto.
Qed.

End TRANSF_PARTIAL_AUGMENT_PROGRAM.


(** The following is a relational presentation of 
  [transform_partial_augment_preogram].  Given relations between function
  definitions and between variable information, it defines a relation
  between programs stating that the two programs have appropriately related
  shapes (global names are preserved and possibly augmented, etc) 
  and that identically-named function definitions
  and variable information are related. *)

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

Definition match_program (new_functs : list (ident * B))
                         (new_vars : list (ident * globvar W))
                         (new_main : ident)
                         (p1: program A V)  (p2: program B W) : Prop :=
  (exists tfuncts, list_forall2 match_funct_entry p1.(prog_funct) tfuncts /\
                                (p2.(prog_funct) = tfuncts ++ new_functs)) /\
  (exists tvars, list_forall2 match_var_entry p1.(prog_vars) tvars /\
                                (p2.(prog_vars) = tvars ++ new_vars)) /\
  p2.(prog_main) = new_main.

End MATCH_PROGRAM.

Remark transform_partial_augment_program_match:
  forall (A B V W: Type)
         (transf_partial_function: A -> res B)
         (transf_partial_variable : V -> res W)
         (p: program A V) 
         (new_functs : list (ident * B))
         (new_vars : list (ident * globvar W))
         (new_main : ident)
         (tp: program B W),
  transform_partial_augment_program transf_partial_function transf_partial_variable new_functs new_vars new_main p = OK tp ->
  match_program 
    (fun fd tfd => transf_partial_function fd = OK tfd)
    (fun info tinfo => transf_partial_variable info = OK tinfo)
    new_functs new_vars new_main
    p tp.
Proof.
  intros. unfold transform_partial_augment_program in H. monadInv H. split.
  exists x. split. 
  apply list_forall2_imply with
    (fun (ab: ident * A) (ac: ident * B) =>
       fst ab = fst ac /\ transf_partial_function (snd ab) = OK (snd ac)).
  eapply map_partial_forall2. eauto. 
  intros. destruct v1; destruct v2; simpl in *.
  destruct H1; subst. constructor. auto. 
  auto. 
  split. exists x0.  split.
  apply list_forall2_imply with
    (fun (ab: ident * globvar V) (ac: ident * globvar W) =>
       fst ab = fst ac /\ transf_globvar transf_partial_variable (snd ab) = OK (snd ac)).
  eapply map_partial_forall2. eauto.
  intros. destruct v1; destruct v2; simpl in *. destruct H1; subst. 
  monadInv H2. destruct g; simpl in *.  constructor. auto.  auto.  auto. 
Qed.

(** * External functions *)

(** For most languages, the functions composing the program are either
  internal functions, defined within the language, or external functions,
  defined outside.  External functions include system calls but also
  compiler built-in functions.  We define a type for external functions
  and associated operations. *)

Inductive external_function : Type :=
  | EF_external (name: ident) (sg: signature)
     (** A system call or library function.  Produces an event
         in the trace. *)
  | EF_builtin (name: ident) (sg: signature)
     (** A compiler built-in function.  Behaves like an external, but
         can be inlined by the compiler. *)
  | EF_vload (chunk: memory_chunk)
     (** A volatile read operation.  If the adress given as first argument
         points within a volatile global variable, generate an
         event and return the value found in this event.  Otherwise,
         produce no event and behave like a regular memory load. *)
  | EF_vstore (chunk: memory_chunk)
     (** A volatile store operation.   If the adress given as first argument
         points within a volatile global variable, generate an event.
         Otherwise, produce no event and behave like a regular memory store. *)
  | EF_vload_global (chunk: memory_chunk) (id: ident) (ofs: int)
     (** A volatile load operation from a global variable. 
         Specialized version of [EF_vload]. *)
  | EF_vstore_global (chunk: memory_chunk) (id: ident) (ofs: int)
     (** A volatile store operation in a global variable. 
         Specialized version of [EF_vstore]. *)
  | EF_malloc
     (** Dynamic memory allocation.  Takes the requested size in bytes
         as argument; returns a pointer to a fresh block of the given size.
         Produces no observable event. *)
  | EF_free
     (** Dynamic memory deallocation.  Takes a pointer to a block
         allocated by an [EF_malloc] external call and frees the
         corresponding block.
         Produces no observable event. *)
  | EF_memcpy (sz: Z) (al: Z)
     (** Block copy, of [sz] bytes, between addresses that are [al]-aligned. *)
  | EF_annot (text: ident) (targs: list typ)
     (** A programmer-supplied annotation.  Takes zero, one or several arguments,
         produces an event carrying the text and the values of these arguments,
         and returns no value. *)
  | EF_annot_val (text:ident) (targ: typ).
     (** Another form of annotation that takes one argument, produces
         an event carrying the text and the value of this argument,
         and returns the value of the argument. *)

(** The type signature of an external function. *)

Definition ef_sig (ef: external_function): signature :=
  match ef with
  | EF_external name sg => sg
  | EF_builtin name sg => sg
  | EF_vload chunk => mksignature (Tint :: nil) (Some (type_of_chunk chunk))
  | EF_vstore chunk => mksignature (Tint :: type_of_chunk chunk :: nil) None
  | EF_vload_global chunk _ _ => mksignature nil (Some (type_of_chunk chunk))
  | EF_vstore_global chunk _ _ => mksignature (type_of_chunk chunk :: nil) None
  | EF_malloc => mksignature (Tint :: nil) (Some Tint)
  | EF_free => mksignature (Tint :: nil) None
  | EF_memcpy sz al => mksignature (Tint :: Tint :: nil) None
  | EF_annot text targs => mksignature targs None
  | EF_annot_val text targ => mksignature (targ :: nil) (Some targ)
  end.

(** Whether an external function should be inlined by the compiler. *)

Definition ef_inline (ef: external_function) : bool :=
  match ef with
  | EF_external name sg => false
  | EF_builtin name sg => true
  | EF_vload chunk => true
  | EF_vstore chunk => true
  | EF_vload_global chunk id ofs => true
  | EF_vstore_global chunk id ofs => true
  | EF_malloc => false
  | EF_free => false
  | EF_memcpy sz al => true
  | EF_annot text targs => true
  | EF_annot_val text targ => true
  end.

(** Whether an external function must reload its arguments. *)

Definition ef_reloads (ef: external_function) : bool :=
  match ef with
  | EF_annot text targs => false
  | _ => true
  end.

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

