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

(** Computation of live ranges for local variables that carry
    debugging information. *)

Require Import Axioms Coqlib Maps Iteration Errors.
Require Import Integers Floats AST.
Require Import Machregs Locations Conventions Linear.

(** A debug info is a [builtin_arg loc] expression that safely evaluates
   in any context. *)

Fixpoint safe_builtin_arg {A: Type} (a: builtin_arg A) : Prop :=
  match a with
  | BA _ | BA_int _ | BA_long _ | BA_float _ | BA_single _ => True
  | BA_splitlong hi lo => safe_builtin_arg hi /\ safe_builtin_arg lo
  | _ => False
  end.

Definition debuginfo := { a : builtin_arg loc | safe_builtin_arg a }.

(** Normalization of debug info.  Prefer an actual location to a constant.
    Make sure that the debug info is safe to evaluate in any context. *)

Definition normalize_debug_1 (a: builtin_arg loc) : option debuginfo :=
  match a with
  | BA x => Some (exist _ (BA x) I)
  | BA_int n => Some (exist _ (BA_int n) I)
  | BA_long n => Some (exist _ (BA_long n) I)
  | BA_float n => Some (exist _ (BA_float n) I)
  | BA_single n => Some (exist _ (BA_single n) I)
  | BA_splitlong (BA hi) (BA lo) => Some (exist _ (BA_splitlong (BA hi) (BA lo)) (conj I I))
  | _ => None
  end.

Fixpoint normalize_debug (l: list (builtin_arg loc)) : option debuginfo :=
  match l with
  | nil => None
  | a :: l' =>
      match a with
      | BA_int _ | BA_long _ | BA_float _ | BA_single _ =>
          match normalize_debug l' with
          | Some i => Some i
          | None => normalize_debug_1 a
          end
      | _ => normalize_debug_1 a
      end
  end.

(** * Availability analysis *)

(** This static analysis tracks which locations (registers and stack slots)
    contain the values of which C local variables.

    The abstraction of the program state at a program point is a list of
    pairs (variable name, location).  It is kept sorted by increasing name.
    The location is represented by a safe [builtin_arg loc] expression. *)

Definition avail : Type := list (ident * debuginfo).

(** Operations on [avail] abstract states. *)

Fixpoint set_state (v: ident) (i: debuginfo) (s: avail) : avail :=
  match s with
  | nil => (v, i) :: nil
  | (v', i') as vi' :: s' =>
      match Pos.compare v v' with
      | Eq => (v, i) :: s'
      | Lt => (v, i) :: s
      | Gt => vi' :: set_state v i s'
      end
  end.

Fixpoint remove_state (v: ident) (s: avail) : avail :=
  match s with
  | nil => nil
  | (v', i') as vi' :: s' =>
      match Pos.compare v v' with
      | Eq => s'
      | Lt => s
      | Gt => vi' :: remove_state v s'
      end
  end.

Fixpoint set_debug_info (v: ident) (info: list (builtin_arg loc)) (s: avail) :=
  match normalize_debug info with
  | Some a => set_state v a s
  | None   => remove_state v s
  end.

(** When the program writes to a register or stack location, some
  availability information is invalidated. *)

Fixpoint arg_no_overlap (a: builtin_arg loc) (l: loc) : bool :=
  match a with
  | BA l' => Loc.diff_dec l' l
  | BA_splitlong hi lo => arg_no_overlap hi l && arg_no_overlap lo l
  | _ => true
  end.

Definition kill (l: loc) (s: avail) : avail :=
  List.filter (fun vi => arg_no_overlap (proj1_sig (snd vi)) l) s.

Fixpoint kill_res (r: builtin_res mreg) (s: avail) : avail :=
  match r with
  | BR r => kill (R r) s
  | BR_none => s
  | BR_splitlong hi lo => kill_res hi (kill_res lo s)
  end.

(** Likewise when a function call takes place. *)

Fixpoint arg_preserved (a: builtin_arg loc) : bool :=
  match a with
  | BA (R r) => negb (List.In_dec mreg_eq r destroyed_at_call)
  | BA (S _ _ _) => true
  | BA_splitlong hi lo => arg_preserved hi && arg_preserved lo
  | _ => true
  end.

Definition kill_at_call (s: avail) : avail :=
  List.filter (fun vi => arg_preserved (proj1_sig(snd vi))) s.

(** The join of two availability states is the intersection of the
    corresponding lists. *)

Definition eq_arg (a1 a2: builtin_arg loc) : {a1=a2} + {a1<>a2}.
Proof.
  generalize Loc.eq ident_eq Int.eq_dec Int64.eq_dec Ptrofs.eq_dec Float.eq_dec Float32.eq_dec chunk_eq;
  decide equality.
Defined.
Global Opaque eq_arg.

Definition eq_debuginfo (i1 i2: debuginfo) : {i1=i2} + {i1 <> i2}.
Proof.
  destruct (eq_arg (proj1_sig i1) (proj1_sig i2)).
  left. destruct i1, i2; simpl in *. subst x0. f_equal. apply proof_irr.
  right. congruence.
Defined.
Global Opaque eq_debuginfo.

Fixpoint join (s1: avail) (s2: avail) {struct s1} : avail :=
  match s1 with
  | nil => nil
  | (v1, i1) as vi1 :: s1' =>
      let fix join2 (s2: avail) : avail :=
        match s2 with
        | nil => nil
        | (v2, i2) as vi2 :: s2' =>
            match Pos.compare v1 v2 with
            | Eq => if eq_debuginfo i1 i2 then vi1 :: join s1' s2' else join s1' s2'
            | Lt => join s1' s2
            | Gt => join2 s2'
            end
        end
      in join2 s2
  end.

Definition eq_state (s1 s2: avail) : {s1=s2} + {s1<>s2}.
Proof.
  apply list_eq_dec. decide equality. apply eq_debuginfo. apply ident_eq.
Defined.
Global Opaque eq_state.

Definition top : avail := nil.

(** Record availability information at labels. *)

Definition labelmap := (PTree.t avail * bool)%type.

Definition get_label (lbl: label) (lm: labelmap) : option avail :=
  PTree.get lbl (fst lm).

Definition update_label (lbl: label) (s1: avail) (lm: labelmap) :
                                  labelmap * avail :=
  match get_label lbl lm with
  | None =>
      ((PTree.set lbl s1 (fst lm), true), s1)
  | Some s2 =>
      let s := join s1 s2 in
      if eq_state s s2
      then (lm, s2)
      else ((PTree.set lbl s (fst lm), true), s)
  end.

Fixpoint update_labels (lbls: list label) (s: avail) (lm: labelmap) :
                                  labelmap :=
  match lbls with
  | nil => lm
  | lbl1 :: lbls =>
      update_labels lbls s (fst (update_label lbl1 s lm))
  end.

(** Classification of builtins *)

Definition is_debug_setvar (ef: external_function) :=
  match ef with
  | EF_debug 2%positive txt targs => Some txt
  | _ => None
  end.

Definition is_builtin_debug_setvar (i: instruction) :=
  match i with
  | Lbuiltin ef args BR_none => is_debug_setvar ef
  | _ => None
  end.

(** The transfer function for the forward dataflow analysis. *)

Definition transfer (lm: labelmap) (before: option avail) (i: instruction):
                                      labelmap * option avail :=
  match before with
  | None =>
      match i with
      | Llabel lbl => (lm, get_label lbl lm)
      | _ => (lm, None)
      end
  | Some s =>
      match i with
      | Lgetstack sl ofs ty rd =>
          (lm, Some (kill (R rd) s))
      | Lsetstack rs sl ofs ty =>
          (lm, Some (kill (S sl ofs ty) s))
      | Lop op args dst =>
          (lm, Some (kill (R dst) s))
      | Lload chunk addr args dst =>
          (lm, Some (kill (R dst) s))
      | Lstore chunk addr args src =>
          (lm, before)
      | Lcall sg ros =>
          (lm, Some (kill_at_call s))
      | Ltailcall sg ros =>
          (lm, None)
      | Lbuiltin ef args res =>
          let s' :=
            match is_debug_setvar ef with
            | Some v => set_debug_info v args s
            | None   => s
            end in
          (lm, Some (kill_res res s'))
      | Llabel lbl =>
          let (lm1, s1) := update_label lbl s lm in
          (lm1, Some s1)
      | Lgoto lbl =>
          let (lm1, s1) := update_label lbl s lm in
          (lm1, None)
      | Lcond cond args lbl =>
          let (lm1, s1) := update_label lbl s lm in
          (lm1, before)
      | Ljumptable r lbls =>
          (update_labels lbls s lm, None)
      | Lreturn =>
          (lm, None)
      end
  end.

(** One pass of forward analysis over the code [c].
    Return an updated label map. *)

Fixpoint ana_code (lm: labelmap) (before: option avail) (c: code) : labelmap :=
  match c with
  | nil => lm
  | i :: c =>
      let (lm1, after) := transfer lm before i in
      ana_code lm1 after c
  end.

(** Iterate [ana_code] until the label map is stable. *)

Definition ana_iter (c: code) (lm: labelmap) : labelmap + labelmap :=
  let lm' := ana_code (fst lm, false) (Some top) c in
  if snd lm' then inr _ lm' else inl _ lm.

Definition ana_function (f: function) : option labelmap :=
  PrimIter.iterate _ _ (ana_iter f.(fn_code)) (PTree.empty _, false).

(** * Code transformation *)

(** Compute the changes between two abstract states *)

Fixpoint diff (s1 s2: avail) {struct s1} : avail :=
  match s1 with
  | nil => nil
  | (v1, i1) as vi1 :: s1' =>
      let fix diff2 (s2: avail) : avail :=
        match s2 with
        | nil => s1
        | (v2, i2) :: s2' =>
            match Pos.compare v1 v2 with
            | Eq => if eq_debuginfo i1 i2 then diff s1' s2' else vi1 :: diff s1' s2'
            | Lt => vi1 :: diff s1' s2
            | Gt => diff2 s2'
            end
        end
      in diff2 s2
  end.

Definition delta_state (before after: option avail) : avail * avail :=
  match before, after with
  | None, None => (nil, nil)
  | Some b, None => (b, nil)
  | None, Some a => (nil, a)
  | Some b, Some a => (diff b a, diff a b)
  end.

(** Insert debug annotations at the beginning and end of live ranges
    of locations that correspond to source local variables. *)

Definition add_start_range (vi: ident * debuginfo) (c: code) : code :=
  let (v, i) := vi in
  Lbuiltin (EF_debug 3%positive v nil) (proj1_sig i :: nil) BR_none :: c.

Definition add_end_range (vi: ident * debuginfo) (c: code) : code :=
  let (v, i) := vi in
  Lbuiltin (EF_debug 4%positive v nil) nil BR_none :: c.

Definition add_delta_ranges (before after: option avail) (c: code) : code :=
  let (killed, born) := delta_state before after in
  List.fold_right add_end_range (List.fold_right add_start_range c born) killed.

Fixpoint skip_debug_setvar (lm: labelmap) (before: option avail) (c: code) :=
  match c with
  | nil => before
  | i :: c' =>
      match is_builtin_debug_setvar i with
      | Some _ => skip_debug_setvar lm (snd (transfer lm before i)) c'
      | None => before
      end
  end.

Fixpoint transf_code (lm: labelmap) (before: option avail) (c: code) : code :=
  match c with
  | nil => nil
  | Lgoto lbl1 :: Llabel lbl2 :: c' =>
      (* This special case avoids some redundant start/end annotations *)
      let after := get_label lbl2 lm in
      Lgoto lbl1 :: Llabel lbl2 ::
      add_delta_ranges before after (transf_code lm after c')
  | i :: c' =>
      let after := skip_debug_setvar lm (snd (transfer lm before i)) c' in
      i :: add_delta_ranges before after (transf_code lm after c')
  end.

Local Open Scope string_scope.

Definition transf_function (f: function) : res function :=
  match ana_function f with
  | None => Error (msg "Debugvar: analysis diverges")
  | Some lm =>
      OK (mkfunction f.(fn_sig) f.(fn_stacksize)
                     (transf_code lm (Some top) f.(fn_code)))
  end.

Definition transf_fundef (fd: fundef) : res fundef :=
  AST.transf_partial_fundef transf_function fd.

Definition transf_program (p: program) : res program :=
  transform_partial_program transf_fundef p.

