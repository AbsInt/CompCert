(** Reloading, spilling, and explication of calling conventions. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import LTLin.
Require Import Conventions.
Require Import Parallelmove.
Require Import Linear.

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

(** [regs_for ll] is similar, for a list of locations [ll] of length
    at most 3.  We ensure that distinct temporaries are used for
    different elements of [ll]. *)

Fixpoint regs_for_rec (locs: list loc) (itmps ftmps: list mreg)
                      {struct locs} : list mreg :=
  match locs, itmps, ftmps with
  | l1 :: ls, it1 :: its, ft1 :: fts =>
      match l1 with
      | R r => r
      | S s => match slot_type s with Tint => it1 | Tfloat => ft1 end
      end
      :: regs_for_rec ls its fts
  | _, _, _ => nil
  end.

Definition regs_for (locs: list loc) :=
  regs_for_rec locs (IT1 :: IT2 :: IT3 :: nil) (FT1 :: FT2 :: FT3 :: nil).

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
      match regs_for (src :: args) with
      | nil => nil                       (* never happens *)
      | rsrc :: rargs =>
          add_reloads (src :: args) (rsrc :: rargs)
            (Lstore chunk addr rargs rsrc :: k)
      end
  | LTLin.Lcall sig los args res =>
      let largs := loc_arguments sig in
      let rres  := loc_result sig in
      match los with
      | inl fn =>
          add_reload fn IT3
            (parallel_move args largs
              (Lcall sig (inl _ IT3) :: add_spill rres res k))
      | inr id =>
          parallel_move args largs
            (Lcall sig (inr _ id) :: add_spill rres res k)
      end
  | LTLin.Ltailcall sig los args =>
      let largs := loc_arguments sig in
      match los with
      | inl fn =>
          add_reload fn IT3
            (parallel_move args largs
              (Ltailcall sig (inl _ IT3) :: k))
      | inr id =>
          parallel_move args largs
            (Ltailcall sig (inr _ id) :: k)
      end
  | LTLin.Lalloc arg res =>
      add_reload arg loc_alloc_argument
        (Lalloc :: add_spill loc_alloc_result res k)
  | LTLin.Llabel lbl =>
      Llabel lbl :: k
  | LTLin.Lgoto lbl =>
      Lgoto lbl :: k
  | LTLin.Lcond cond args lbl =>
      let rargs := regs_for args in
      add_reloads args rargs (Lcond cond rargs lbl :: k)
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

