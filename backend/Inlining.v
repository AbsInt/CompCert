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

(** RTL function inlining *)

Require Import Coqlib Wfsimpl Maps Errors Integers.
Require Import AST Linking.
Require Import Op Registers RTL.

(** ** Environment of inlinable functions *)

(** We maintain a mapping from function names to their definitions.
  In this mapping, we only include internal functions that are eligible for
  inlining, as determined by the external heuristic
  [should_inline]. *)

Definition funenv : Type := PTree.t function.

Definition size_fenv (fenv: funenv) := PTree_Properties.cardinal fenv.

Parameter inlining_info: Type.  (* abstract type, implemented on the Caml side *)

Parameter inlining_analysis: program -> inlining_info.

Parameter should_inline: inlining_info -> ident -> function -> bool.

Definition add_globdef (io: inlining_info) (fenv: funenv) (idg: ident * globdef fundef unit) : funenv :=
  match idg with
  | (id, Gfun (Internal f)) =>
      if should_inline io id f
      then PTree.set id f fenv
      else PTree.remove id fenv
  | (id, _) =>
      PTree.remove id fenv
  end.

Definition funenv_program (p: program) : funenv :=
  let io := inlining_analysis p in
  List.fold_left (add_globdef io) p.(prog_defs) (PTree.empty function).

(** State monad *)

(** To construct incrementally the CFG of a function after inlining,
  we use a state monad similar to that used in module [RTLgen].
  It records the current state of the CFG, plus counters to generate
  fresh pseudo-registers and fresh CFG nodes.  It also records the
  stack size needed for the inlined function. *)

Record state : Type := mkstate {
  st_nextreg: positive;                 (**r last used pseudo-register *)
  st_nextnode: positive;                (**r last used CFG node *)
  st_code: code;                        (**r current CFG  *)
  st_stksize: Z                         (**r current stack size *)
}.

(** Monotone evolution of the state. *)

Inductive sincr (s1 s2: state) : Prop :=
  Sincr (NEXTREG: Ple s1.(st_nextreg) s2.(st_nextreg))
        (NEXTNODE: Ple s1.(st_nextnode) s2.(st_nextnode))
        (STKSIZE: s1.(st_stksize) <= s2.(st_stksize)).

Remark sincr_refl: forall s, sincr s s.
Proof.
  intros; constructor; xomega.
Qed.

Lemma sincr_trans: forall s1 s2 s3, sincr s1 s2 -> sincr s2 s3 -> sincr s1 s3.
Proof.
  intros. inv H; inv H0. constructor; xomega.
Qed.

(** Dependently-typed state monad, ensuring that the final state is
  greater or equal (in the sense of predicate [sincr] above) than
  the initial state. *)

Inductive res {A: Type} {s: state}: Type := R (x: A) (s': state) (I: sincr s s').

Definition mon (A: Type) : Type := forall (s: state), @res A s.

(** Operations on this monad. *)

Definition ret {A: Type} (x: A): mon A :=
  fun s => R x s (sincr_refl s).

Definition bind {A B: Type} (x: mon A) (f: A -> mon B): mon B :=
  fun s1 => match x s1 with R vx s2 I1 =>
              match f vx s2 with R vy s3 I2 =>
                R vy s3 (sincr_trans s1 s2 s3 I1 I2)
              end
            end.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).

Definition initstate :=
  mkstate 1%positive 1%positive (PTree.empty instruction) 0.

Program Definition set_instr (pc: node) (i: instruction): mon unit :=
  fun s =>
    R tt
      (mkstate s.(st_nextreg) s.(st_nextnode) (PTree.set pc i s.(st_code)) s.(st_stksize))
      _.
Next Obligation.
  intros; constructor; simpl; xomega.
Qed.

Program Definition add_instr (i: instruction): mon node :=
  fun s =>
    let pc := s.(st_nextnode) in
    R pc
      (mkstate s.(st_nextreg) (Pos.succ pc) (PTree.set pc i s.(st_code)) s.(st_stksize))
      _.
Next Obligation.
  intros; constructor; simpl; xomega.
Qed.

Program Definition reserve_nodes (numnodes: positive): mon positive :=
  fun s =>
    R s.(st_nextnode)
      (mkstate s.(st_nextreg) (Pos.add s.(st_nextnode) numnodes) s.(st_code) s.(st_stksize))
      _.
Next Obligation.
  intros; constructor; simpl; xomega.
Qed.

Program Definition reserve_regs (numregs: positive): mon positive :=
  fun s =>
    R s.(st_nextreg)
      (mkstate (Pos.add s.(st_nextreg) numregs) s.(st_nextnode) s.(st_code) s.(st_stksize))
      _.
Next Obligation.
  intros; constructor; simpl; xomega.
Qed.

Program Definition request_stack (sz: Z): mon unit :=
  fun s =>
    R tt
      (mkstate s.(st_nextreg) s.(st_nextnode) s.(st_code) (Z.max s.(st_stksize) sz))
      _.
Next Obligation.
  intros; constructor; simpl; xomega.
Qed.

Program Definition ptree_mfold {A: Type} (f: positive -> A -> mon unit) (t: PTree.t A): mon unit :=
  fun s =>
    R tt
      (PTree.fold (fun s1 k v => match f k v s1 return _ with R _ s2 _ => s2 end) t s)
      _.
Next Obligation.
  apply PTree_Properties.fold_rec.
  auto.
  apply sincr_refl.
  intros. destruct (f k v a). eapply sincr_trans; eauto.
Qed.

(** ** Inlining contexts *)

(** A context describes how to insert the CFG for a source function into
  the CFG for the function after inlining:
- a source instruction at PC [n] is relocated to PC [n + ctx.(dpc)];
- all pseudo-registers of this instruction are shifted by [ctx.(dreg)];
- all stack references are shifted by [ctx.(dstk)];
- "return" instructions are transformed into "return" or "move" instructions
  as governed by [ctx.(retinfo)].
*)

Record context: Type := mkcontext {
  dpc: positive;                        (**r offset for PCs *)
  dreg: positive;                       (**r offset for pseudo-regs *)
  dstk: Z;                              (**r offset for stack references *)
  mreg: positive;                       (**r max pseudo-reg number *)
  mstk: Z;                              (**r original stack block size *)
  retinfo: option(node * reg)           (**r where to branch on return *)
                                        (**r and deposit return value *)
}.

(** The following functions "shift" (relocate) PCs, registers, operations, etc. *)

Definition shiftpos (p amount: positive) := Pos.pred (Pos.add p amount).

Definition spc (ctx: context) (pc: node) := shiftpos pc ctx.(dpc).

Definition sreg (ctx: context) (r: reg) := shiftpos r ctx.(dreg).

Definition sregs (ctx: context) (rl: list reg) := List.map (sreg ctx) rl.

Definition sros (ctx: context) (ros: reg + ident) := sum_left_map (sreg ctx) ros.

Definition sop (ctx: context) (op: operation) :=
  shift_stack_operation ctx.(dstk) op.

Definition saddr (ctx: context) (addr: addressing) :=
  shift_stack_addressing ctx.(dstk) addr.

Fixpoint sbuiltinarg (ctx: context) (a: builtin_arg reg) : builtin_arg reg :=
  match a with
  | BA x => BA (sreg ctx x)
  | BA_loadstack chunk ofs => BA_loadstack chunk (Ptrofs.add ofs (Ptrofs.repr ctx.(dstk)))
  | BA_addrstack ofs => BA_addrstack (Ptrofs.add ofs (Ptrofs.repr ctx.(dstk)))
  | BA_splitlong hi lo => BA_splitlong (sbuiltinarg ctx hi) (sbuiltinarg ctx lo)
  | BA_addptr a1 a2 => BA_addptr (sbuiltinarg ctx a1) (sbuiltinarg ctx a2)
  | _ => a
  end.

Definition sbuiltinres (ctx: context) (a: builtin_res reg) : builtin_res reg :=
  match a with
  | BR x => BR (sreg ctx x)
  | _    => BR_none
  end.

(** The initial context, used to copy the CFG of a toplevel function. *)

Definition initcontext (dpc dreg nreg: positive) (sz: Z) :=
  {| dpc := dpc;
     dreg := dreg;
     dstk := 0;
     mreg := nreg;
     mstk := Z.max sz 0;
     retinfo := None |}.

(** The context used to inline a call to another function. *)

Definition min_alignment (sz: Z) :=
  if zle sz 1 then 1
  else if zle sz 2 then 2
  else if zle sz 4 then 4 else 8.

Definition callcontext (ctx: context)
                      (dpc dreg nreg: positive) (sz: Z)
                      (retpc: node) (retreg: reg) :=
  {| dpc := dpc;
     dreg := dreg;
     dstk := align (ctx.(dstk) + ctx.(mstk)) (min_alignment sz);
     mreg := nreg;
     mstk := Z.max sz 0;
     retinfo := Some (spc ctx retpc, sreg ctx retreg) |}.

(** The context used to inline a tail call to another function. *)

Definition tailcontext (ctx: context) (dpc dreg nreg: positive) (sz: Z) :=
  {| dpc := dpc;
     dreg := dreg;
     dstk := align ctx.(dstk) (min_alignment sz);
     mreg := nreg;
     mstk := Z.max sz 0;
     retinfo := ctx.(retinfo) |}.

(** ** Recursive expansion and copying of a CFG *)

(** Insert "move" instructions to copy the arguments of an inlined
    function into its parameters. *)

Fixpoint add_moves (srcs dsts: list reg) (succ: node): mon node :=
  match srcs, dsts with
  | s1 :: sl, d1 :: dl =>
      do n <- add_instr (Iop Omove (s1 :: nil) d1 succ);
      add_moves sl dl n
  | _, _ =>
      ret succ
  end.

(** To prevent infinite inlining of a recursive function, when we
  inline the body of a function [f], this function is removed from the
  environment of inlinable functions and therefore becomes ineligible
  for inlining.  This decreases the size (number of entries) of the
  environment and guarantees termination.  Inlining is, therefore,
  presented as a well-founded recursion over the size of the environment. *)

Section EXPAND_CFG.

Variable fenv: funenv.

(** The [rec] parameter is the recursor: [rec fenv' P ctx f] copies
  the body of function [f], with inline expansion within, as governed
  by context [ctx].  It can only be called for function environments
  [fenv'] strictly smaller than the current environment [fenv]. *)

Variable rec: forall fenv', (size_fenv fenv' < size_fenv fenv)%nat -> context -> function -> mon unit.

(** Given a register-or-symbol [ros], can we inline the corresponding call? *)

Inductive inline_decision (ros: reg + ident) : Type :=
  | Cannot_inline
  | Can_inline (id: ident) (f: function) (P: ros = inr reg id) (Q: fenv!id = Some f).

Program Definition can_inline (ros: reg + ident): inline_decision ros :=
  match ros with
  | inl r => Cannot_inline _
  | inr id => match fenv!id with Some f => Can_inline _ id f _ _ | None => Cannot_inline _ end
  end.

(** Inlining of a call to function [f].  An appropriate context is
  created, then the CFG of [f] is recursively copied, then moves
  are inserted to copy the arguments of the call to the parameters of [f]. *)

Definition inline_function (ctx: context) (id: ident) (f: function)
                           (P: PTree.get id fenv = Some f)
                           (args: list reg)
                           (retpc: node) (retreg: reg) : mon node :=
  let npc := max_pc_function f in
  let nreg := max_reg_function f in
  do dpc <- reserve_nodes npc;
  do dreg <- reserve_regs nreg;
  let ctx' := callcontext ctx dpc dreg nreg f.(fn_stacksize) retpc retreg in
  do x <- rec (PTree.remove id fenv) (PTree_Properties.cardinal_remove P) ctx' f;
  add_moves (sregs ctx args) (sregs ctx' f.(fn_params)) (spc ctx' f.(fn_entrypoint)).

(** Inlining of a tail call to function [f].  Similar to [inline_function],
  but the new context is different. *)

Definition inline_tail_function (ctx: context) (id: ident) (f: function)
                               (P: PTree.get id fenv = Some f)
                               (args: list reg): mon node :=
  let npc := max_pc_function f in
  let nreg := max_reg_function f in
  do dpc <- reserve_nodes npc;
  do dreg <- reserve_regs nreg;
  let ctx' := tailcontext ctx dpc dreg nreg f.(fn_stacksize) in
  do x <- rec (PTree.remove id fenv) (PTree_Properties.cardinal_remove P) ctx' f;
  add_moves (sregs ctx args) (sregs ctx' f.(fn_params)) (spc ctx' f.(fn_entrypoint)).

(** The instruction generated for a [Ireturn] instruction found in an
  inlined function body. *)

Definition inline_return (ctx: context) (or: option reg) (retinfo: node * reg) :=
  match retinfo, or with
  | (retpc, retreg), Some r => Iop Omove (sreg ctx r :: nil) retreg retpc
  | (retpc, retreg), None   => Inop retpc
  end.

(** Expansion and copying of an instruction.  For most instructions,
  its registers and successor PC are shifted as per the context [ctx],
  then the instruction is inserted in the final CFG at its final position
  [spc ctx pc].

  [Icall] instructions are either replaced by a "goto" to the expansion
  of the called function, or shifted as described above.

  [Itailcall] instructions are similar, with one additional case.  If
  the [Itailcall] occurs in the body of an inlined function, and
  cannot be inlined itself, it must be turned into an [Icall]
  instruction that branches to the return point of the inlined
  function.

  Finally, [Ireturn] instructions within an inlined function are
  turned into a "move" or "goto" that stores the result, if any,
  into the destination register, then branches back to the successor
  of the inlined call. *)

Definition expand_instr (ctx: context) (pc: node) (i: instruction): mon unit :=
  match i with
  | Inop s =>
      set_instr (spc ctx pc) (Inop (spc ctx s))
  | Iop op args res s =>
      set_instr (spc ctx pc)
                (Iop (sop ctx op) (sregs ctx args) (sreg ctx res) (spc ctx s))
  | Iload chunk addr args dst s =>
      set_instr (spc ctx pc)
                (Iload chunk (saddr ctx addr) (sregs ctx args) (sreg ctx dst) (spc ctx s))
  | Istore chunk addr args src s =>
      set_instr (spc ctx pc)
                (Istore chunk (saddr ctx addr) (sregs ctx args) (sreg ctx src) (spc ctx s))
  | Icall sg ros args res s =>
      match can_inline ros with
      | Cannot_inline =>
          set_instr (spc ctx pc)
                    (Icall sg (sros ctx ros) (sregs ctx args) (sreg ctx res) (spc ctx s))
      | Can_inline id f P Q =>
          do n <- inline_function ctx id f Q args s res;
          set_instr (spc ctx pc) (Inop n)
      end
  | Itailcall sg ros args =>
      match can_inline ros with
      | Cannot_inline =>
          match ctx.(retinfo) with
          | None =>
              set_instr (spc ctx pc)
                        (Itailcall sg (sros ctx ros) (sregs ctx args))
          | Some(rpc, rreg) =>
              set_instr (spc ctx pc)
                        (Icall sg (sros ctx ros) (sregs ctx args) rreg rpc)
          end
      | Can_inline id f P Q =>
          do n <- inline_tail_function ctx id f Q args;
          set_instr (spc ctx pc) (Inop n)
      end
  | Ibuiltin ef args res s =>
      set_instr (spc ctx pc)
                (Ibuiltin ef (map (sbuiltinarg ctx) args) (sbuiltinres ctx res) (spc ctx s))
  | Icond cond args s1 s2 =>
      set_instr (spc ctx pc)
                (Icond cond (sregs ctx args) (spc ctx s1) (spc ctx s2))
  | Ijumptable r tbl =>
      set_instr (spc ctx pc)
                (Ijumptable (sreg ctx r) (List.map (spc ctx) tbl))
  | Ireturn or =>
      match ctx.(retinfo) with
      | None =>
          set_instr (spc ctx pc) (Ireturn (option_map (sreg ctx) or))
      | Some rinfo =>
          set_instr (spc ctx pc) (inline_return ctx or rinfo)
      end
  end.

(** The expansion of a function [f] iteratively expands all its
  instructions, after recording how much stack it needs. *)

Definition expand_cfg_rec (ctx: context) (f: function): mon unit :=
  do x <- request_stack (ctx.(dstk) + ctx.(mstk));
  ptree_mfold (expand_instr ctx) f.(fn_code).

End EXPAND_CFG.

(** Here we "tie the knot" of the recursion, taking the fixpoint
  of [expand_cfg_rec]. *)

Definition expand_cfg := Fixm size_fenv expand_cfg_rec.

(** Start of the recursion: copy and inline function [f] in the
  initial context. *)

Definition expand_function (fenv: funenv) (f: function): mon context :=
  let npc := max_pc_function f in
  let nreg := max_reg_function f in
  do dpc <- reserve_nodes npc;
  do dreg <- reserve_regs nreg;
  let ctx := initcontext dpc dreg nreg f.(fn_stacksize) in
  do x <- expand_cfg fenv ctx f;
  ret ctx.

(** ** Inlining in functions and whole programs. *)

Local Open Scope string_scope.

(** Inlining can increase the size of the function's stack block.  We must
  make sure that the new size does not exceed [Ptrofs.max_unsigned], otherwise
  address computations within the stack would overflow and produce incorrect
  results. *)

Definition transf_function (fenv: funenv) (f: function) : Errors.res function :=
  let '(R ctx s _) := expand_function fenv f initstate in
  if zlt s.(st_stksize) Ptrofs.max_unsigned then
    OK (mkfunction f.(fn_sig)
                   (sregs ctx f.(fn_params))
                   s.(st_stksize)
                   s.(st_code)
                   (spc ctx f.(fn_entrypoint)))
  else
    Error(msg "Inlining: stack too big").

Definition transf_fundef (fenv: funenv) (fd: fundef) : Errors.res fundef :=
  AST.transf_partial_fundef (transf_function fenv) fd.

Definition transf_program (p: program): Errors.res program :=
  let fenv := funenv_program p in
  AST.transform_partial_program (transf_fundef fenv) p.

