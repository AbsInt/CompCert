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

Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Values Memory.
Require Import Op Registers RTL.
Require Import ValueDomain ValueAnalysis CSEdomain CombineOp.

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

  The representation of value numbers and equations is described in
  module [CSEdomain]. *)

(** * Operations on value numberings *)

(** [valnum_reg n r] returns the value number for the contents of
  register [r].  If none exists, a fresh value number is returned
  and associated with register [r].  The possibly updated numbering
  is also returned.  [valnum_regs] is similar, but for a list of
  registers. *)

Definition valnum_reg (n: numbering) (r: reg) : numbering * valnum :=
  match PTree.get r n.(num_reg) with
  | Some v => (n, v)
  | None   =>
      let v := n.(num_next) in
      ( {| num_next := Pos.succ v;
           num_eqs  := n.(num_eqs);
           num_reg  := PTree.set r v n.(num_reg);
           num_val  := PMap.set v (r :: nil) n.(num_val) |},
       v)
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

Fixpoint find_valnum_rhs (r: rhs) (eqs: list equation)
                         {struct eqs} : option valnum :=
  match eqs with
  | nil => None
  | Eq v str r' :: eqs1 =>
      if str && eq_rhs r r' then Some v else find_valnum_rhs r eqs1
  end.

(** [find_valnum_rhs' rhs eqs] is similar, but also accepts equations
  of the form [vn >= rhs]. *)

Fixpoint find_valnum_rhs' (r: rhs) (eqs: list equation)
                          {struct eqs} : option valnum :=
  match eqs with
  | nil => None
  | Eq v str r' :: eqs1 =>
      if eq_rhs r r' then Some v else find_valnum_rhs' r eqs1
  end.

(** [find_valnum_num vn eqs] searches the list of equations [eqs]
  for an equation of the form [vn = rhs] for some equation [rhs].
  If found, [Some rhs] is returned, otherwise [None] is returned. *)

Fixpoint find_valnum_num (v: valnum) (eqs: list equation)
                         {struct eqs} : option rhs :=
  match eqs with
  | nil => None
  | Eq v' str r' :: eqs1 =>
      if str && peq v v' then Some r' else find_valnum_num v eqs1
  end.

(** [reg_valnum n vn] returns a register that is mapped to value number
    [vn], or [None] if no such register exists. *)

Definition reg_valnum (n: numbering) (vn: valnum) : option reg :=
  match PMap.get vn n.(num_val) with
  | nil => None
  | r :: rs => Some r
  end.

(** [regs_valnums] is similar, for a list of value numbers. *)

Fixpoint regs_valnums (n: numbering) (vl: list valnum) : option (list reg) :=
  match vl with
  | nil => Some nil
  | v1 :: vs =>
      match reg_valnum n v1, regs_valnums n vs with
      | Some r1, Some rs => Some (r1 :: rs)
      | _, _ => None
      end
  end.

(** [find_rhs] return a register that already holds the result of the
    given arithmetic operation or memory load, or a value more defined
    than this result, according to the given
    numbering.  [None] is returned if no such register exists. *)

Definition find_rhs (n: numbering) (rh: rhs) : option reg :=
  match find_valnum_rhs' rh n.(num_eqs) with
  | None => None
  | Some vres => reg_valnum n vres
  end.

(** Update the [num_val] mapping prior to a redefinition of register [r]. *)

Definition forget_reg (n: numbering) (rd: reg) : PMap.t (list reg) :=
  match PTree.get rd n.(num_reg) with
  | None => n.(num_val)
  | Some v => PMap.set v (List.remove peq rd (PMap.get v n.(num_val))) n.(num_val)
  end.

Definition update_reg (n: numbering) (rd: reg) (vn: valnum) : PMap.t (list reg) :=
  let nv := forget_reg n rd in PMap.set vn (rd :: PMap.get vn nv) nv.

(** [add_rhs n rd rhs] updates the value numbering [n] to reflect
  the computation of the operation or load represented by [rhs]
  and the storing of the result in register [rd].  If an equation
  [vn = rhs] is known, register [rd] is set to [vn].  Otherwise,
  a fresh value number [vn] is generated and associated with [rd],
  and the equation [vn = rhs] is added. *)

Definition add_rhs (n: numbering) (rd: reg) (rh: rhs) : numbering :=
  match find_valnum_rhs rh n.(num_eqs) with
  | Some vres =>
      {| num_next := n.(num_next);
         num_eqs  := n.(num_eqs);
         num_reg  := PTree.set rd vres n.(num_reg);
         num_val  := update_reg n rd vres |}
  | None =>
      {| num_next := Pos.succ n.(num_next);
         num_eqs  := Eq n.(num_next) true rh :: n.(num_eqs);
         num_reg  := PTree.set rd n.(num_next) n.(num_reg);
         num_val  := update_reg n rd n.(num_next) |}
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
      {| num_next := n1.(num_next);
         num_eqs  := n1.(num_eqs);
         num_reg  := PTree.set rd v n1.(num_reg);
         num_val  := update_reg n1 rd v |}
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

(** [set_unknown n rd] returns a numbering where [rd] is mapped to
  no value number, and no equations are added.  This is useful
  to model instructions with unpredictable results such as [Ibuiltin]. *)

Definition set_unknown (n: numbering) (rd: reg) :=
  {| num_next := n.(num_next);
     num_eqs  := n.(num_eqs);
     num_reg  := PTree.remove rd n.(num_reg);
     num_val  := forget_reg n rd |}.

Definition set_res_unknown (n: numbering) (res: builtin_res reg) :=
  match res with
  | BR r => set_unknown n r
  | _    => n
  end.

(** [kill_equations pred n] remove all equations satisfying predicate [pred]. *)

Fixpoint kill_eqs (pred: rhs -> bool) (eqs: list equation) : list equation :=
  match eqs with
  | nil => nil
  | (Eq l strict r) as eq :: rem =>
      if pred r then kill_eqs pred rem else eq :: kill_eqs pred rem
  end.

Definition kill_equations (pred: rhs -> bool) (n: numbering) : numbering :=
  {| num_next := n.(num_next);
     num_eqs  := kill_eqs pred n.(num_eqs);
     num_reg  := n.(num_reg);
     num_val  := n.(num_val) |}.

(** [kill_all_loads n] removes all equations involving memory loads,
  as well as those involving memory-dependent operators.
  It is used to reflect the effect of a builtin operation, which can
  change memory in unpredictable ways and potentially invalidate all such equations. *)

Definition filter_loads (r: rhs) : bool :=
  match r with
  | Op op _ => op_depends_on_memory op
  | Load _ _ _ => true
  end.

Definition kill_all_loads (n: numbering) : numbering :=
  kill_equations filter_loads n.

(** [kill_loads_after_store app n chunk addr args] removes all equations
  involving loads that could be invalidated by a store of quantity [chunk]
  at address determined by [addr] and [args].  Loads that are disjoint
  from this store are preserved.  Equations involving memory-dependent
  operators are also removed. *)

Definition filter_after_store (app: VA.t) (n: numbering) (p: aptr) (sz: Z) (r: rhs) :=
  match r with
  | Op op vl =>
      op_depends_on_memory op
  | Load chunk addr vl =>
      match regs_valnums n vl with
      | None => true
      | Some rl =>
          negb (pdisjoint (aaddressing app addr rl) (size_chunk chunk) p sz)
      end
  end.

Definition kill_loads_after_store
             (app: VA.t) (n: numbering)
             (chunk: memory_chunk) (addr: addressing) (args: list reg) :=
  let p := aaddressing app addr args in
  kill_equations (filter_after_store app n p (size_chunk chunk)) n.

(** [add_store_result n chunk addr rargs rsrc] updates the numbering [n]
  to reflect the knowledge gained after executing an instruction
  [Istore chunk addr rargs rsrc].  An equation [vsrc >= Load chunk addr vargs]
  is added, but only if the value of [rsrc] is known to be normalized
  with respect to [chunk]. *)

Definition store_normalized_range (chunk: memory_chunk) : aval :=
  match chunk with
  | Mint8signed => Sgn Ptop 8
  | Mint8unsigned => Uns Ptop 8
  | Mint16signed => Sgn Ptop 16
  | Mint16unsigned => Uns Ptop 16
  | _ => Vtop
  end.

Definition add_store_result (app: VA.t) (n: numbering) (chunk: memory_chunk) (addr: addressing)
                            (rargs: list reg) (rsrc: reg) :=
  if vincl (avalue app rsrc) (store_normalized_range chunk) then
    let (n1, vsrc) := valnum_reg n rsrc in
    let (n2, vargs) := valnum_regs n1 rargs in
    {| num_next := n2.(num_next);
       num_eqs  := Eq vsrc false (Load chunk addr vargs) :: n2.(num_eqs);
       num_reg  := n2.(num_reg);
       num_val  := n2.(num_val) |}
  else n.

(** [kill_loads_after_storebyte n dst sz] removes all equations
  involving loads that could be invalidated by a store of [sz] bytes
  starting at address [dst]. Loads that are disjoint from this
  store-bytes are preserved.  Equations involving memory-dependent
  operators are also removed. *)

Definition kill_loads_after_storebytes
             (app: VA.t) (n: numbering) (dst: aptr) (sz: Z) :=
  kill_equations (filter_after_store app n dst sz) n.

(** [add_memcpy app n1 n2 rsrc rdst sz] adds equations to [n2] that
  represent the effect of a [memcpy] block copy operation of [sz] bytes
  from the address denoted by [rsrc] to the address denoted by [rdst].
  [n2] is the numbering returned by [kill_loads_after_storebytes]
  and [n1] is the original numbering before the [memcpy] operation.
  Valid equations (found in [n1]) involving loads within the source
  area of the [memcpy] are translated as equations involving loads
  within the destination area, and added to numbering [n2].
  Currently, we only track [memcpy] operations between stack
  locations, as often occur when compiling assignments between local C
  variables of struct type. *)

Definition shift_memcpy_eq (src sz delta: Z) (e: equation) :=
  match e with
  | Eq l strict (Load chunk (Ainstack i) _) =>
      let i := Ptrofs.unsigned i in
      let j := i + delta in
      if zle src i
      && zle (i + size_chunk chunk) (src + sz)
      && zeq (Z.modulo delta (align_chunk chunk)) 0
      && zle 0 j
      && zle j Ptrofs.max_unsigned
      then Some(Eq l strict (Load chunk (Ainstack (Ptrofs.repr j)) nil))
      else None
  | _ => None
  end.

Fixpoint add_memcpy_eqs (src sz delta: Z) (eqs1 eqs2: list equation) :=
  match eqs1 with
  | nil => eqs2
  | e :: eqs =>
      match shift_memcpy_eq src sz delta e with
      | None => add_memcpy_eqs src sz delta eqs eqs2
      | Some e' => e' :: add_memcpy_eqs src sz delta eqs eqs2
      end
  end.

Definition add_memcpy (n1 n2: numbering) (asrc adst: aptr) (sz: Z) :=
  match asrc, adst with
  | Stk src, Stk dst =>
      {| num_next := n2.(num_next);
         num_eqs  := add_memcpy_eqs (Ptrofs.unsigned src) sz
                                    (Ptrofs.unsigned dst - Ptrofs.unsigned src)
                                    n1.(num_eqs) n2.(num_eqs);
         num_reg  := n2.(num_reg);
         num_val  := n2.(num_val) |}
  | _, _ => n2
  end.

(** Take advantage of known equations to select more efficient
  forms of operations, addressing modes, and conditions. *)

Section REDUCE.

Variable A: Type.
Variable f: (valnum -> option rhs) -> A -> list valnum -> option (A * list valnum).
Variable n: numbering.

Fixpoint reduce_rec (niter: nat) (op: A) (args: list valnum) : option(A * list reg) :=
  match niter with
  | O => None
  | Datatypes.S niter' =>
      match f (fun v => find_valnum_num v n.(num_eqs)) op args with
      | None => None
      | Some(op', args') =>
          match reduce_rec niter' op' args' with
          | None =>
              match regs_valnums n args' with Some rl => Some(op', rl) | None => None end
          | Some _ as res =>
              res
          end
      end
  end.

Definition reduce (op: A) (rl: list reg) (vl: list valnum) : A * list reg :=
  match reduce_rec 4%nat op vl with
  | None     => (op, rl)
  | Some res => res
  end.

End REDUCE.

(** * The static analysis *)

(** We now equip the type [numbering] with a partial order and a greatest
  element.  The partial order is based on entailment: [n1] is greater
  than [n2] if [n1] is satisfiable whenever [n2] is.  The greatest element
  is, of course, the empty numbering (no equations). *)

Module Numbering.
  Definition t := numbering.
  Definition ge (n1 n2: numbering) : Prop :=
    forall valu ge sp rs m,
    numbering_holds valu ge sp rs m n2 ->
    numbering_holds valu ge sp rs m n1.
  Definition top := empty_numbering.
  Lemma top_ge: forall x, ge top x.
  Proof.
    intros; red; intros. unfold top. apply empty_numbering_holds.
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
  equations involving memory loads at possibly overlapping locations,
  then add an equation for loads from the same location stored to.
  For [Icall] instructions, we could simply associate a fresh, unconstrained by equations value number
  to the result register.  However, it is often undesirable to eliminate
  common subexpressions across a function call (there is a risk of
  increasing too much the register pressure across the call), so we
  just forget all equations and start afresh with an empty numbering.
  Finally, for instructions that modify neither registers nor
  the memory, we keep the numbering unchanged.

  For builtin invocations [Ibuiltin], we have three strategies:
- Forget all equations.  This is appropriate for builtins that can be
  turned into function calls
  ([EF_external], [EF_runtime], [EF_malloc], [EF_free]).
- Forget equations involving loads but keep equations over registers.
  This is appropriate for builtins that can modify memory,
  e.g. volatile stores, or [EF_builtin]
- Keep all equations, taking advantage of the fact that neither memory
  nor registers are modified.  This is appropriate for annotations
  and for volatile loads.
*)

Definition transfer (f: function) (approx: PMap.t VA.t) (pc: node) (before: numbering) :=
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
          let app := approx!!pc in
          let n := kill_loads_after_store app before chunk addr args in
          add_store_result app n chunk addr args src
      | Icall sig ros args res s =>
          empty_numbering
      | Itailcall sig ros args =>
          empty_numbering
      | Ibuiltin ef args res s =>
          match ef with
          | EF_external _ _ | EF_runtime _ _ | EF_malloc | EF_free | EF_inline_asm _ _ _ =>
              empty_numbering
          | EF_builtin _ _ | EF_vstore _ =>
              set_res_unknown (kill_all_loads before) res
          | EF_memcpy sz al =>
              match args with
              | dst :: src :: nil =>
                  let app := approx!!pc in
                  let adst := aaddr_arg app dst in
                  let asrc := aaddr_arg app src in
                  let n := kill_loads_after_storebytes app before adst sz in
                  set_res_unknown (add_memcpy before n asrc adst sz) res
              | _ =>
                  empty_numbering
              end
          | EF_vload _ | EF_annot _ _ _ | EF_annot_val _ _ _ | EF_debug _ _ _ =>
              set_res_unknown before res
          end
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
  a mapping from program points to numberings. *)

Definition analyze (f: RTL.function) (approx: PMap.t VA.t): option (PMap.t numbering) :=
  Solver.fixpoint (fn_code f) successors_instr (transfer f approx) f.(fn_entrypoint).

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
        let (n1, vl) := valnum_regs n args in
        match find_rhs n1 (Op op vl) with
        | Some r =>
            Iop Omove (r :: nil) res s
        | None =>
            let (op', args') := reduce _ combine_op n1 op args vl in
            Iop op' args' res s
        end
  | Iload chunk addr args dst s =>
      let (n1, vl) := valnum_regs n args in
      match find_rhs n1 (Load chunk addr vl) with
      | Some r =>
          Iop Omove (r :: nil) dst s
      | None =>
          let (addr', args') := reduce _ combine_addr n1 addr args vl in
          Iload chunk addr' args' dst s
      end
  | Istore chunk addr args src s =>
      let (n1, vl) := valnum_regs n args in
      let (addr', args') := reduce _ combine_addr n1 addr args vl in
      Istore chunk addr' args' src s
  | Icond cond args s1 s2 =>
      let (n1, vl) := valnum_regs n args in
      let (cond', args') := reduce _ combine_cond n1 cond args vl in
      Icond cond' args' s1 s2
  | _ =>
      instr
  end.

Definition transf_code (approxs: PMap.t numbering) (instrs: code) : code :=
  PTree.map (fun pc instr => transf_instr approxs!!pc instr) instrs.

Definition vanalyze := ValueAnalysis.analyze.

Definition transf_function (rm: romem) (f: function) : res function :=
  let approx := vanalyze rm f in
  match analyze f approx with
  | None => Error (msg "CSE failure")
  | Some approxs =>
      OK(mkfunction
           f.(fn_sig)
           f.(fn_params)
           f.(fn_stacksize)
           (transf_code approxs f.(fn_code))
           f.(fn_entrypoint))
  end.

Definition transf_fundef (rm: romem) (f: fundef) : res fundef :=
  AST.transf_partial_fundef (transf_function rm) f.

Definition transf_program (p: program) : res program :=
  transform_partial_program (transf_fundef (romem_for p)) p.

