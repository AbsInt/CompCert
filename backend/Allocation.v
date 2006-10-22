(** Register allocation, spilling, reloading and explicitation of
   calling conventions. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import RTLtyping.
Require Import Kildall.
Require Import Locations.
Require Import Conventions.
Require Import Coloring.
Require Import Parallelmove.

(** * Liveness analysis over RTL *)

(** A register [r] is live at a point [p] if there exists a path
    from [p] to some instruction that uses [r] as argument,
    and [r] is not redefined along this path.
    Liveness can be computed by a backward dataflow analysis.
    The analysis operates over sets of (live) pseudo-registers. *)

Notation reg_live := Regset.add.
Notation reg_dead := Regset.remove.

Definition reg_option_live (or: option reg) (lv: Regset.t) :=
  match or with None => lv | Some r => reg_live r lv end.

Definition reg_sum_live (ros: reg + ident) (lv: Regset.t) :=
  match ros with inl r => reg_live r lv | inr s => lv end.

Fixpoint reg_list_live
             (rl: list reg) (lv: Regset.t) {struct rl} : Regset.t :=
  match rl with
  | nil => lv
  | r1 :: rs => reg_list_live rs (reg_live r1 lv)
  end.

Fixpoint reg_list_dead
             (rl: list reg) (lv: Regset.t) {struct rl} : Regset.t :=
  match rl with
  | nil => lv
  | r1 :: rs => reg_list_dead rs (reg_dead r1 lv)
  end.

(** Here is the transfer function for the dataflow analysis.
    Since this is a backward dataflow analysis, it takes as argument
    the abstract register set ``after'' the given instruction,
    i.e. the registers that are live after; and it returns as result
    the abstract register set ``before'' the given instruction,
    i.e. the registers that must be live before.
    The general relation between ``live before'' and ``live after''
    an instruction is that a register is live before if either
    it is one of the arguments of the instruction, or it is not the result
    of the instruction and it is live after.
    However, if the result of a side-effect-free instruction is not 
    live ``after'', the whole instruction will be removed later
    (since it computes a useless result), thus its arguments need not
    be live ``before''. *)

Definition transfer
            (f: RTL.function) (pc: node) (after: Regset.t) : Regset.t :=
  match f.(fn_code)!pc with
  | None =>
      after
  | Some i =>
      match i with
      | Inop s =>
          after
      | Iop op args res s =>
          if Regset.mem res after then
            reg_list_live args (reg_dead res after)
          else
            after
      | Iload chunk addr args dst s =>
          if Regset.mem dst after then
            reg_list_live args (reg_dead dst after)
          else
            after
      | Istore chunk addr args src s =>
          reg_list_live args (reg_live src after)
      | Icall sig ros args res s =>
          reg_list_live args
           (reg_sum_live ros (reg_dead res after))
      | Ialloc arg res s =>
          reg_live arg (reg_dead res after)
      | Icond cond args ifso ifnot =>
          reg_list_live args after
      | Ireturn optarg =>
          reg_option_live optarg after
      end
  end.

(** The liveness analysis is then obtained by instantiating the
    general framework for backward dataflow analysis provided by
    module [Kildall].  *)

Module DS := Backward_Dataflow_Solver(Regset)(NodeSetBackward).

Definition analyze (f: RTL.function): option (PMap.t Regset.t) :=
  DS.fixpoint (successors f) f.(fn_nextpc) (transfer f) nil.

(** * Spilling and reloading *)

(** LTL operations, like those of the target processor, operate only
  over machine registers, but not over stack slots.  Consider
  the RTL instruction
<<
        r1 <- Iop(Oadd, r1 :: r2 :: nil)
>>
  and assume that [r1] and [r2] are assigned to stack locations [S s1]
  and [S s2], respectively.  The translated LTL code must load these
  stack locations into temporary integer registers (this is called
  ``reloading''), perform the [Oadd] operation over these temporaries,
  leave the result in a temporary, then store the temporary back to
  stack location [S s1] (this is called ``spilling'').  In other term,
  the generated LTL code has the following shape:
<<
        IT1 <- Bgetstack s1;
        IT2 <- Bgetstack s2;
        IT1 <- Bop(Oadd, IT1 :: IT2 :: nil);
        Bsetstack s1 IT1;
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

(** ** Insertion of LTL reloads, stores and moves *)

Require Import LTL.

(** [add_spill src dst k] prepends to [k] the instructions needed
  to assign location [dst] the value of machine register [mreg]. *)

Definition add_spill (src: mreg) (dst: loc) (k: block) :=
  match dst with
  | R rd => if mreg_eq src rd then k else Bop Omove (src :: nil) rd k
  | S sl => Bsetstack src sl k
  end.

(** [add_reload src dst k] prepends to [k] the instructions needed
  to assign machine register [mreg] the value of the location [src]. *)

Definition add_reload (src: loc) (dst: mreg) (k: block) :=
  match src with
  | R rs => if mreg_eq rs dst then k else Bop Omove (rs :: nil) dst k
  | S sl => Bgetstack sl dst k
  end.

(** [add_reloads] is similar for a list of locations (as sources)
  and a list of machine registers (as destinations).  *)

Fixpoint add_reloads (srcs: list loc) (dsts: list mreg) (k: block)
                                            {struct srcs} : block :=
  match srcs, dsts with
  | s1 :: sl, t1 :: tl =>
      add_reload s1 t1 (add_reloads sl tl k)
  | _, _ =>
      k
  end.

(** [add_move src dst k] prepends to [k] the instructions that copy
  the value of location [src] into location [dst]. *)

Definition add_move (src dst: loc) (k: block) :=
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
  length.  This is a parallel move, meaning that arbitrary overlap
  between the sources and destinations is permitted. *)

Definition parallel_move (srcs dsts: list loc) (k: block) : block :=
  List.fold_right
    (fun p k => add_move (fst p) (snd p) k)
     k (parmove srcs dsts).

(** ** Constructors for LTL instructions *)

(** The following functions generate LTL instructions operating
  over the given locations.  Appropriate reloading and spilling operations
  are added around the core LTL instruction. *)

Definition add_op (op: operation) (args: list loc) (res: loc) (s: node) :=
  match is_move_operation op args with
  | Some src =>
      add_move src res (Bgoto s)
  | None =>
      let rargs := regs_for args in
      let rres := reg_for res in
      add_reloads args rargs (Bop op rargs rres (add_spill rres res (Bgoto s)))
  end.

Definition add_load (chunk: memory_chunk) (addr: addressing)
                    (args: list loc) (dst: loc) (s: node) :=
  let rargs := regs_for args in
  let rdst := reg_for dst in
  add_reloads args rargs
    (Bload chunk addr rargs rdst (add_spill rdst dst (Bgoto s))).

Definition add_store (chunk: memory_chunk) (addr: addressing)
                     (args: list loc) (src: loc) (s: node) :=
  match regs_for (src :: args) with
  | nil => Breturn                      (* never happens *)
  | rsrc :: rargs =>
      add_reloads (src :: args) (rsrc :: rargs)
        (Bstore chunk addr rargs rsrc (Bgoto s))
  end.

Definition add_alloc (arg: loc) (res: loc) (s: node) :=
  add_reload arg Conventions.loc_alloc_argument
    (Balloc (add_spill Conventions.loc_alloc_result res (Bgoto s))).

(** For function calls, we also add appropriate moves to and from
  the canonical locations for function arguments and function results,
  as dictated by the calling conventions. *)

Definition add_call (sig: signature) (ros: loc + ident)
                    (args: list loc) (res: loc) (s: node) :=
  let rargs := loc_arguments sig in
  let rres  := loc_result sig in
  match ros with
  | inl fn =>
      (add_reload fn IT3
        (parallel_move args rargs
          (Bcall sig (inl _ IT3) (add_spill rres res (Bgoto s)))))
  | inr id =>
      parallel_move args rargs
        (Bcall sig (inr _ id) (add_spill rres res (Bgoto s)))
  end.

Definition add_cond (cond: condition) (args: list loc) (ifso ifnot: node) :=
  let rargs := regs_for args in
  add_reloads args rargs (Bcond cond rargs ifso ifnot).

(** For function returns, we add the appropriate move of the result
  to the conventional location for the function result.  If the function
  returns with no value, we explicitly set the function result register
  to the [Vundef] value, for consistency with RTL's semantics. *)

Definition add_return (sig: signature) (optarg: option loc) :=
  match optarg with
  | Some arg => add_reload arg (loc_result sig) Breturn
  | None     => Bop Oundef nil (loc_result sig) Breturn
  end.
  
(** For function entry points, we move from the parameter locations
  dictated by the calling convention to the locations of the function
  parameters.  We also explicitly set to [Vundef] the locations
  of pseudo-registers that are live at function entry but are not
  parameters, again for consistency with RTL's semantics. *)

Fixpoint add_undefs (ll: list loc) (b: block) {struct ll} : block :=
  match ll with
  | nil => b
  | R r :: ls => Bop Oundef nil r (add_undefs ls b)
  | S s :: ls => add_undefs ls b
  end.

Definition add_entry (sig: signature) (params: list loc) (undefs: list loc)
                     (s: node) :=
  parallel_move (loc_parameters sig) params (add_undefs undefs (Bgoto s)).

(** * Translation from RTL to LTL *)

(** Each [RTL] instruction translates to an [LTL] basic block.
  The register assignment [assign] returned by register allocation
  is applied to the arguments and results of the RTL
  instruction, followed by an invocation of the appropriate [LTL]
  constructor function that will deal with spilling, reloading and
  calling conventions.  In addition, dead instructions are eliminated.
  Dead instructions are instructions without side-effects ([Iop] and
  [Iload]) whose result register is dead, i.e. whose result value
  is never used. *)

Definition transf_instr
         (f: RTL.function) (live: PMap.t Regset.t) (assign: reg -> loc)
         (pc: node) (instr: RTL.instruction) : LTL.block :=
  match instr with
  | Inop s =>
      Bgoto s
  | Iop op args res s =>
      if Regset.mem res live!!pc then
        add_op op (List.map assign args) (assign res) s
      else
        Bgoto s
  | Iload chunk addr args dst s =>
      if Regset.mem dst live!!pc then
        add_load chunk addr (List.map assign args) (assign dst) s
      else
        Bgoto s
  | Istore chunk addr args src s =>
      add_store chunk addr (List.map assign args) (assign src) s
  | Icall sig ros args res s =>
      add_call sig (sum_left_map assign ros) (List.map assign args)
                   (assign res) s
  | Ialloc arg res s =>
      add_alloc (assign arg) (assign res) s
  | Icond cond args ifso ifnot =>
      add_cond cond (List.map assign args) ifso ifnot
  | Ireturn optarg =>
      add_return f.(RTL.fn_sig) (option_map assign optarg)
  end.

Definition transf_entrypoint
     (f: RTL.function) (live: PMap.t Regset.t) (assign: reg -> loc)
     (newcode: LTL.code) : LTL.code :=
  let oldentry := RTL.fn_entrypoint f in
  let newentry := RTL.fn_nextpc f in
  let undefs :=
    Regset.elements (reg_list_dead (RTL.fn_params f)
                                   (transfer f oldentry live!!oldentry)) in
  PTree.set
    newentry
    (add_entry (RTL.fn_sig f)
               (List.map assign (RTL.fn_params f))
               (List.map assign undefs)
               oldentry)
    newcode.

Lemma transf_entrypoint_wf:
  forall (f: RTL.function) (live: PMap.t Regset.t) (assign: reg -> loc),
  let tc1 := PTree.map (transf_instr f live assign) (RTL.fn_code f) in
  let tc2 := transf_entrypoint f live assign tc1 in
  forall (pc: node), Plt pc (Psucc (RTL.fn_nextpc f)) \/ tc2!pc = None.
Proof.
  intros. case (plt pc (Psucc (RTL.fn_nextpc f))); intro.
  left. auto. 
  right. 
  assert (pc <> RTL.fn_nextpc f).
  red; intro. subst pc. elim n. apply Plt_succ.
  assert (~ (Plt pc (RTL.fn_nextpc f))).
  red; intro. elim n. apply Plt_trans_succ; auto.
  unfold tc2. unfold transf_entrypoint. 
  rewrite PTree.gso; auto. 
  unfold tc1. rewrite PTree.gmap. 
  elim (RTL.fn_code_wf f pc); intro.
  contradiction. unfold option_map. rewrite H1. auto.
Qed.

(** The translation of a function performs liveness analysis,
  construction and coloring of the inference graph, and per-instruction
  transformation as described above. *)

Definition transf_function (f: RTL.function) : option LTL.function :=
  match type_function f with
  | None => None
  | Some env =>
    match analyze f with
    | None => None
    | Some live =>
      let pc0 := f.(RTL.fn_entrypoint) in
      let live0 := transfer f pc0 live!!pc0 in
      match regalloc f live live0 env with
      | None => None
      | Some assign =>
          Some (LTL.mkfunction
            (RTL.fn_sig f)
            (RTL.fn_stacksize f)
            (transf_entrypoint f live assign
                   (PTree.map (transf_instr f live assign) (RTL.fn_code f)))
            (RTL.fn_nextpc f)
            (transf_entrypoint_wf f live assign))
      end
    end
  end.

Definition transf_fundef (fd: RTL.fundef) : option LTL.fundef :=
  transf_partial_fundef transf_function fd.

Definition transf_program (p: RTL.program) : option LTL.program :=
  transform_partial_program transf_fundef p.

