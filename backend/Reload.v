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

(** Reloading, spilling, and explication of calling conventions. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Op.
Require Import Locations.
Require Import LTLin.
Require Import Conventions.
Require Import Parallelmove.
Require Import Linear.

Open Local Scope error_monad_scope.

(** * Spilling and reloading *)

(** Operations in the Linear language, like those of the target processor,
  operate only over machine registers, but not over stack slots.
  Consider the LTLin instruction
<<
        r1 <- Lop(Oadd, r1 :: r2 :: nil)
>>
  and assume that [r1] and [r2] are assigned to stack locations [S s1]
  and [S s2], respectively.  The translated LTL code must load these
  stack locations into temporary integer registers (this is called
  ``reloading''), perform the [Oadd] operation over these temporaries,
  leave the result in a temporary, then store the temporary back to
  stack location [S s1] (this is called ``spilling'').  In other term,
  the generated Linear code has the following shape:
<<
        IT1 <- Lgetstack s1;
        IT2 <- Lgetstack s2;
        IT1 <- Lop(Oadd, IT1 :: IT2 :: nil);
        Lsetstack s1 IT1;
>>
  This section provides functions that assist in choosing appropriate
  temporaries and inserting the required spilling and reloading
  operations. *)

(** ** Allocation of temporary registers for reloading and spilling. *)

(** [reg_for l] returns a machine register appropriate for working
    over the location [l]: either the machine register [m] if [l = R m],
    or a temporary register of [l]'s type if [l] is a stack slot. *)

Definition reg_for (l: loc) : mreg :=
  match l with
  | R r => r
  | S s => match slot_type s with Tint => IT1 | Tfloat => FT1 end
  end.

(** [regs_for ll] is similar, for a list of locations [ll].
    We ensure that distinct temporaries are used for
    different elements of [ll].
    The result is correct only if [enough_temporaries ll = true]
    (see below). *)

Fixpoint regs_for_rec (locs: list loc) (itmps ftmps: list mreg)
                      {struct locs} : list mreg :=
  match locs with
  | nil => nil
  | R r :: ls => r :: regs_for_rec ls itmps ftmps
  | S s :: ls =>
      match slot_type s with
      | Tint =>
          match itmps with
          | nil => nil
          | it1 :: its => it1 :: regs_for_rec ls its ftmps
          end
      | Tfloat =>
          match ftmps with
          | nil => nil
          | ft1 :: fts => ft1 :: regs_for_rec ls itmps fts
          end
      end
  end.

Definition regs_for (locs: list loc) :=
  regs_for_rec locs int_temporaries float_temporaries.

(** Detect the situations where not enough temporaries are available
    for reloading. *)

Fixpoint enough_temporaries_rec (locs: list loc) (itmps ftmps: list mreg)
                                {struct locs} : bool :=
  match locs with
  | nil => true
  | R r :: ls => enough_temporaries_rec ls itmps ftmps
  | S s :: ls =>
      match slot_type s with
      | Tint =>
          match itmps with
          | nil => false
          | it1 :: its => enough_temporaries_rec ls its ftmps
          end
      | Tfloat =>
          match ftmps with
          | nil => false
          | ft1 :: fts => enough_temporaries_rec ls itmps fts
          end
      end
  end.

Definition enough_temporaries (locs: list loc) :=
  enough_temporaries_rec locs int_temporaries float_temporaries.

(** ** Insertion of Linear reloads, stores and moves *)

(** [add_spill src dst k] prepends to [k] the instructions needed
  to assign location [dst] the value of machine register [mreg]. *)

Definition add_spill (src: mreg) (dst: loc) (k: code) :=
  match dst with
  | R rd => if mreg_eq src rd then k else Lop Omove (src :: nil) rd :: k
  | S sl => Lsetstack src sl :: k
  end.

(** [add_reload src dst k] prepends to [k] the instructions needed
  to assign machine register [mreg] the value of the location [src]. *)

Definition add_reload (src: loc) (dst: mreg) (k: code) :=
  match src with
  | R rs => if mreg_eq rs dst then k else Lop Omove (rs :: nil) dst :: k
  | S sl => Lgetstack sl dst :: k
  end.

(** [add_reloads] is similar for a list of locations (as sources)
  and a list of machine registers (as destinations).  *)

Fixpoint add_reloads (srcs: list loc) (dsts: list mreg) (k: code)
                                            {struct srcs} : code :=
  match srcs, dsts with
  | s1 :: sl, t1 :: tl => add_reload s1 t1 (add_reloads sl tl k)
  | _, _ => k
  end.

(** [add_move src dst k] prepends to [k] the instructions that copy
  the value of location [src] into location [dst]. *)

Definition add_move (src dst: loc) (k: code) :=
  if Loc.eq src dst then k else
    match src, dst with
    | R rs, _ =>
        add_spill rs dst k
    | _, R rd =>
        add_reload src rd k
    | S ss, S sd =>
        let tmp :=
          match slot_type ss with Tint => IT1 | Tfloat => FT1 end in
        add_reload src tmp (add_spill tmp dst k)
    end.

(** [parallel_move srcs dsts k] is similar, but for a list of
  source locations and a list of destination locations of the same
  length.  This is a parallel move, meaning that some of the 
  destinations can also occur as sources. *)

Definition parallel_move (srcs dsts: list loc) (k: code) : code :=
  List.fold_right
    (fun p k => add_move (fst p) (snd p) k)
     k (parmove srcs dsts).

(** * Code transformation *)

(** We insert appropriate reload, spill and parallel move operations
  around each of the instructions of the source code. *)

Definition transf_instr 
     (f: LTLin.function) (instr: LTLin.instruction) (k: code) : code :=
  match instr with
  | LTLin.Lop op args res =>
      match is_move_operation op args with
      | Some src =>
          add_move src res k
      | None =>
          let rargs := regs_for args in
          let rres := reg_for res in
          add_reloads args rargs (Lop op rargs rres :: add_spill rres res k)
      end
  | LTLin.Lload chunk addr args dst =>
      let rargs := regs_for args in
      let rdst := reg_for dst in
      add_reloads args rargs
        (Lload chunk addr rargs rdst :: add_spill rdst dst k)
  | LTLin.Lstore chunk addr args src =>
      if enough_temporaries (src :: args) then
        match regs_for (src :: args) with
        | nil => k                       (* never happens *)
        | rsrc :: rargs =>
            add_reloads (src :: args) (rsrc :: rargs)
              (Lstore chunk addr rargs rsrc :: k)
        end
      else
        let rargs := regs_for args in
        let rsrc := reg_for src in
        add_reloads args rargs
          (Lop (op_for_binary_addressing addr) rargs IT2 ::
           add_reload src rsrc
             (Lstore chunk (Aindexed Int.zero) (IT2 :: nil) rsrc :: k))
  | LTLin.Lcall sig los args res =>
      let largs := loc_arguments sig in
      let rres  := loc_result sig in
      match los with
      | inl fn =>
          parallel_move args largs
            (add_reload fn (reg_for fn)
              (Lcall sig (inl _ (reg_for fn)) :: add_spill rres res k))
      | inr id =>
          parallel_move args largs
            (Lcall sig (inr _ id) :: add_spill rres res k)
      end
  | LTLin.Ltailcall sig los args =>
      let largs := loc_arguments sig in
      match los with
      | inl fn =>
          parallel_move args largs
            (add_reload fn IT1
              (Ltailcall sig (inl _ IT1) :: k))
      | inr id =>
          parallel_move args largs
            (Ltailcall sig (inr _ id) :: k)
      end
  | LTLin.Lbuiltin ef args dst =>
      if ef_reloads ef then
       (let rargs := regs_for args in
        let rdst := reg_for dst in
        add_reloads args rargs
          (Lbuiltin ef rargs rdst :: add_spill rdst dst k))
      else
        Lannot ef args :: k
  | LTLin.Llabel lbl =>
      Llabel lbl :: k
  | LTLin.Lgoto lbl =>
      Lgoto lbl :: k
  | LTLin.Lcond cond args lbl =>
      let rargs := regs_for args in
      add_reloads args rargs (Lcond cond rargs lbl :: k)
  | LTLin.Ljumptable arg tbl =>
      let rarg := reg_for arg in
      add_reload arg rarg (Ljumptable rarg tbl :: k)
  | LTLin.Lreturn None =>
      Lreturn :: k
  | LTLin.Lreturn (Some loc) =>
      add_reload loc (loc_result (LTLin.fn_sig f)) (Lreturn :: k)
  end.

Definition transf_code (f: LTLin.function) (c: LTLin.code) : code :=
  List.fold_right (transf_instr f) nil c.

Definition transf_function (f: LTLin.function) : function :=
  mkfunction
    (LTLin.fn_sig f)
    (LTLin.fn_stacksize f)
    (parallel_move (loc_parameters (LTLin.fn_sig f)) (LTLin.fn_params f)
       (transf_code f (LTLin.fn_code f))).

Definition transf_fundef (fd: LTLin.fundef) : Linear.fundef :=
  transf_fundef transf_function fd.

Definition transf_program (p: LTLin.program) : Linear.program :=
  transform_program transf_fundef p.

