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

(** Common subexpression elimination over RTL.  This optimization
  proceeds by value numbering over extended basic blocks. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Kildall.

(** * Value numbering *)

(** The idea behind value numbering algorithms is to associate
  abstract identifiers (``value numbers'') to the contents of registers
  at various program points, and record equations between these
  identifiers.  For instance, consider the instruction
  [r1 = add(r2, r3)] and assume that [r2] and [r3] are mapped
  to abstract identifiers [x] and [y] respectively at the program
  point just before this instruction.  At the program point just after,
  we can add the equation [z = add(x, y)] and associate [r1] with [z],
  where [z] is a fresh abstract identifier.  However, if we already
  knew an equation [u = add(x, y)], we can preferably add no equation
  and just associate [r1] with [u].  If there exists a register [r4]
  mapped with [u] at this point, we can then replace the instruction
  [r1 = add(r2, r3)] by a move instruction [r1 = r4], therefore eliminating
  a common subexpression and reusing the result of an earlier addition.

  Abstract identifiers / value numbers are represented by positive integers.
  Equations are of the form [valnum = rhs], where the right-hand sides
  [rhs] are either arithmetic operations or memory loads. *)

Definition valnum := positive.

Inductive rhs : Type :=
  | Op: operation -> list valnum -> rhs
  | Load: memory_chunk -> addressing -> list valnum -> rhs.

Definition eq_valnum: forall (x y: valnum), {x=y}+{x<>y} := peq.

Definition eq_list_valnum (x y: list valnum) : {x=y}+{x<>y}.
Proof.
  induction x; intros; case y; intros.
  left; auto.
  right; congruence.
  right; congruence.
  case (eq_valnum a v); intros.
  case (IHx l); intros.
  left; congruence.
  right; congruence.
  right; congruence.
Qed.

Definition eq_rhs (x y: rhs) : {x=y}+{x<>y}.
Proof.
  generalize Int.eq_dec; intro.
  generalize Float.eq_dec; intro.
  generalize eq_operation; intro.
  generalize eq_addressing; intro.
  assert (forall (x y: memory_chunk), {x=y}+{x<>y}). decide equality.
  generalize eq_valnum; intro.
  generalize eq_list_valnum; intro.
  decide equality.
Qed.

(** A value numbering is a collection of equations between value numbers
  plus a partial map from registers to value numbers.  Additionally,
  we maintain the next unused value number, so as to easily generate
  fresh value numbers. *)

Record numbering : Type := mknumbering {
  num_next: valnum;
  num_eqs: list (valnum * rhs);
  num_reg: PTree.t valnum
}.

Definition empty_numbering :=
  mknumbering 1%positive nil (PTree.empty valnum).

(** [valnum_reg n r] returns the value number for the contents of
  register [r].  If none exists, a fresh value number is returned
  and associated with register [r].  The possibly updated numbering
  is also returned.  [valnum_regs] is similar, but for a list of
  registers. *)

Definition valnum_reg (n: numbering) (r: reg) : numbering * valnum :=
  match PTree.get r n.(num_reg) with
  | Some v => (n, v)
  | None   => (mknumbering (Psucc n.(num_next))
                           n.(num_eqs)
                           (PTree.set r n.(num_next) n.(num_reg)),
               n.(num_next))
  end.

Fixpoint valnum_regs (n: numbering) (rl: list reg)
                     {struct rl} : numbering * list valnum :=
  match rl with
  | nil =>
      (n, nil)
  | r1 :: rs =>
      let (n1, v1) := valnum_reg n r1 in
      let (ns, vs) := valnum_regs n1 rs in
      (ns, v1 :: vs)
  end.

(** [find_valnum_rhs rhs eqs] searches the list of equations [eqs]
  for an equation of the form [vn = rhs] for some value number [vn].
  If found, [Some vn] is returned, otherwise [None] is returned. *)

Fixpoint find_valnum_rhs (r: rhs) (eqs: list (valnum * rhs))
                         {struct eqs} : option valnum :=
  match eqs with
  | nil => None
  | (v, r') :: eqs1 =>
      if eq_rhs r r' then Some v else find_valnum_rhs r eqs1
  end.

(** [add_rhs n rd rhs] updates the value numbering [n] to reflect
  the computation of the operation or load represented by [rhs]
  and the storing of the result in register [rd].  If an equation
  [vn = rhs] is known, register [rd] is set to [vn].  Otherwise,
  a fresh value number [vn] is generated and associated with [rd],
  and the equation [vn = rhs] is added. *)

Definition add_rhs (n: numbering) (rd: reg) (rh: rhs) : numbering :=
  match find_valnum_rhs rh n.(num_eqs) with
  | Some vres =>
      mknumbering n.(num_next) n.(num_eqs)
                  (PTree.set rd vres n.(num_reg))
  | None =>
      mknumbering (Psucc n.(num_next))
                  ((n.(num_next), rh) :: n.(num_eqs))
                  (PTree.set rd n.(num_next) n.(num_reg))
  end.

(** [add_op n rd op rs] specializes [add_rhs] for the case of an
  arithmetic operation.  The right-hand side corresponding to [op]
  and the value numbers for the argument registers [rs] is built
  and added to [n] as described in [add_rhs].   

  If [op] is a move instruction, we simply assign the value number of
  the source register to the destination register, since we know that
  the source and destination registers have exactly the same value.
  This enables more common subexpressions to be recognized. For instance:
<<
     z = add(x, y);  u = x; v = add(u, y);
>>
  Since [u] and [x] have the same value number, the second [add] 
  is recognized as computing the same result as the first [add],
  and therefore [u] and [z] have the same value number. *)

Definition add_op (n: numbering) (rd: reg) (op: operation) (rs: list reg) :=
  match is_move_operation op rs with
  | Some r =>
      let (n1, v) := valnum_reg n r in
      mknumbering n1.(num_next) n1.(num_eqs) (PTree.set rd v n1.(num_reg))  
  | None =>
      let (n1, vs) := valnum_regs n rs in
      add_rhs n1 rd (Op op vs)
  end.

(** [add_load n rd chunk addr rs] specializes [add_rhs] for the case of a
  memory load.  The right-hand side corresponding to [chunk], [addr]
  and the value numbers for the argument registers [rs] is built
  and added to [n] as described in [add_rhs]. *)

Definition add_load (n: numbering) (rd: reg) 
                    (chunk: memory_chunk) (addr: addressing)
                    (rs: list reg) :=
  let (n1, vs) := valnum_regs n rs in
  add_rhs n1 rd (Load chunk addr vs).

(** [add_unknown n rd] returns a numbering where [rd] is mapped to a
   fresh value number, and no equations are added.  This is useful
   to model instructions with unpredictable results such as [Ibuiltin]. *)

Definition add_unknown (n: numbering) (rd: reg) :=
  mknumbering (Psucc n.(num_next))
              n.(num_eqs)
              (PTree.set rd n.(num_next) n.(num_reg)).

(** [kill_load n] removes all equations involving memory loads.
  It is used to reflect the effect of a memory store, which can
  potentially invalidate all such equations. *)

Fixpoint kill_load_eqs (eqs: list (valnum * rhs)) : list (valnum * rhs) :=
  match eqs with
  | nil => nil
  | (_, Load _ _ _) :: rem => kill_load_eqs rem
  | v_rh :: rem => v_rh :: kill_load_eqs rem
  end.

Definition kill_loads (n: numbering) : numbering :=
  mknumbering n.(num_next)
              (kill_load_eqs n.(num_eqs))
              n.(num_reg).

(* [reg_valnum n vn] returns a register that is mapped to value number
   [vn], or [None] if no such register exists. *)

Definition reg_valnum (n: numbering) (vn: valnum) : option reg :=
  PTree.fold
    (fun (res: option reg) (r: reg) (v: valnum) =>
       if peq v vn then Some r else res)
    n.(num_reg) None.

(* [find_rhs] and its specializations [find_op] and [find_load]
   return a register that already holds the result of the given arithmetic
   operation or memory load, according to the given numbering.
   [None] is returned if no such register exists. *)

Definition find_rhs (n: numbering) (rh: rhs) : option reg :=
  match find_valnum_rhs rh n.(num_eqs) with
  | None => None
  | Some vres => reg_valnum n vres
  end.

Definition find_op
    (n: numbering) (op: operation) (rs: list reg) : option reg :=
  let (n1, vl) := valnum_regs n rs in
  find_rhs n1 (Op op vl).

Definition find_load
    (n: numbering) (chunk: memory_chunk) (addr: addressing) (rs: list reg) : option reg :=
  let (n1, vl) := valnum_regs n rs in
  find_rhs n1 (Load chunk addr vl).

(** * The static analysis *)

(** We now define a notion of satisfiability of a numbering.  This semantic
  notion plays a central role in the correctness proof (see [CSEproof]),
  but is defined here because we need it to define the ordering over
  numberings used in the static analysis. 

  A numbering is satisfiable in a given register environment and memory
  state if there exists a valuation, mapping value numbers to actual values,
  that validates both the equations and the association of registers
  to value numbers. *)

Definition equation_holds
     (valuation: valnum -> val)
     (ge: genv) (sp: val) (m: mem) 
     (vres: valnum) (rh: rhs) : Prop :=
  match rh with
  | Op op vl =>
      eval_operation ge sp op (List.map valuation vl) =
      Some (valuation vres)
  | Load chunk addr vl =>
      exists a,
      eval_addressing ge sp addr (List.map valuation vl) = Some a /\
      Mem.loadv chunk m a = Some (valuation vres)
  end.

Definition numbering_holds
   (valuation: valnum -> val)
   (ge: genv) (sp: val) (rs: regset) (m: mem) (n: numbering) : Prop :=
     (forall vn rh,
       In (vn, rh) n.(num_eqs) ->
       equation_holds valuation ge sp m vn rh)
  /\ (forall r vn,
       PTree.get r n.(num_reg) = Some vn -> rs#r = valuation vn).

Definition numbering_satisfiable
   (ge: genv) (sp: val) (rs: regset) (m: mem) (n: numbering) : Prop :=
  exists valuation, numbering_holds valuation ge sp rs m n.

Lemma empty_numbering_satisfiable:
  forall ge sp rs m, numbering_satisfiable ge sp rs m empty_numbering.
Proof.
  intros; red. 
  exists (fun (vn: valnum) => Vundef). split; simpl; intros.
  elim H.
  rewrite PTree.gempty in H. discriminate. 
Qed. 

(** We now equip the type [numbering] with a partial order and a greatest
  element.  The partial order is based on entailment: [n1] is greater
  than [n2] if [n1] is satisfiable whenever [n2] is.  The greatest element
  is, of course, the empty numbering (no equations). *)

Module Numbering.
  Definition t := numbering.
  Definition ge (n1 n2: numbering) : Prop :=
    forall ge sp rs m, 
    numbering_satisfiable ge sp rs m n2 ->
    numbering_satisfiable ge sp rs m n1.
  Definition top := empty_numbering.
  Lemma top_ge: forall x, ge top x.
  Proof.
    intros; red; intros. unfold top. apply empty_numbering_satisfiable.
  Qed.
  Lemma refl_ge: forall x, ge x x.
  Proof.
    intros; red; auto.
  Qed.
End Numbering.

(** We reuse the solver for forward dataflow inequations based on
  propagation over extended basic blocks defined in library [Kildall]. *)

Module Solver := BBlock_solver(Numbering).

(** The transfer function for the dataflow analysis returns the numbering
  ``after'' execution of the instruction at [pc], as a function of the
  numbering ``before''.  For [Iop] and [Iload] instructions, we add
  equations or reuse existing value numbers as described for
  [add_op] and [add_load].  For [Istore] instructions, we forget
  all equations involving memory loads.  For [Icall] instructions,
  we could simply associate a fresh, unconstrained by equations value number
  to the result register.  However, it is often undesirable to eliminate
  common subexpressions across a function call (there is a risk of 
  increasing too much the register pressure across the call), so we
  just forget all equations and start afresh with an empty numbering.
  Finally, the remaining instructions modify neither registers nor
  the memory, so we keep the numbering unchanged. *)

Definition transfer (f: function) (pc: node) (before: numbering) :=
  match f.(fn_code)!pc with
  | None => before
  | Some i =>
      match i with
      | Inop s =>
          before
      | Iop op args res s =>
          add_op before res op args
      | Iload chunk addr args dst s =>
          add_load before dst chunk addr args
      | Istore chunk addr args src s =>
          kill_loads before
      | Icall sig ros args res s =>
          empty_numbering
      | Itailcall sig ros args =>
          empty_numbering
      | Ibuiltin ef args res s =>
          add_unknown (kill_loads before) res
      | Icond cond args ifso ifnot =>
          before
      | Ijumptable arg tbl =>
          before
      | Ireturn optarg =>
          before
      end
  end.

(** The static analysis solves the dataflow inequations implied
  by the [transfer] function using the ``extended basic block'' solver,
  which produces sub-optimal solutions quickly.  The result is
  a mapping from program points to numberings.  In the unlikely
  case where the solver fails to find a solution, we simply associate
  empty numberings to all program points, which is semantically correct
  and effectively deactivates the CSE optimization. *)

Definition analyze (f: RTL.function): PMap.t numbering :=
  match Solver.fixpoint (successors f) (transfer f) f.(fn_entrypoint) with
  | None => PMap.init empty_numbering
  | Some res => res
  end.

(** * Code transformation *)

(** The code transformation is performed instruction by instruction.
  [Iload] instructions and non-trivial [Iop] instructions are turned
  into move instructions if their result is already available in a
  register, as indicated by the numbering inferred at that program point.

  Some operations are so cheap to compute that it is generally not
  worth reusing their results.  These operations are detected by the
  function [is_trivial_op] in module [Op]. *)

Definition transf_instr (n: numbering) (instr: instruction) :=
  match instr with
  | Iop op args res s =>
      if is_trivial_op op then instr else
        match find_op n op args with
        | None => instr
        | Some r => Iop Omove (r :: nil) res s
        end
  | Iload chunk addr args dst s =>
      match find_load n chunk addr args with
      | None => instr
      | Some r => Iop Omove (r :: nil) dst s
      end
  | _ =>
      instr
  end.

Definition transf_code (approxs: PMap.t numbering) (instrs: code) : code :=
  PTree.map (fun pc instr => transf_instr approxs!!pc instr) instrs.

Definition transf_function (f: function) : function :=
  let approxs := analyze f in
  mkfunction
        f.(fn_sig)
        f.(fn_params)
        f.(fn_stacksize)
        (transf_code approxs f.(fn_code))
        f.(fn_entrypoint).

Definition transf_fundef (f: fundef) : fundef :=
  AST.transf_fundef transf_function f.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.

