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

(** Construction and coloring of the interference graph. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import RTLtyping.
Require Import Locations.
Require Import Conventions.
Require Import InterfGraph.

(** * Construction of the interference graph *)

(** Two registers interfere if there exists a program point where
    they are both simultaneously live, and it is possible that they
    contain different values at this program point.  Consequently,
    two registers that do not interfere can be merged into one register
    while preserving the program behavior: there is no program point
    where this merged register would have to hold two different values
    (for the two original registers), so to speak.

    The simplified algorithm for constructing the interference graph
    from the results of the liveness analysis is as follows:
<<
     start with empty interference graph
     for each parameter p and register r live at the function entry point:
         add conflict edge p <-> r 
     for each instruction I in function:
         let L be the live registers "after" I
         if I is a "move" instruction  dst <- src, and dst is live:
            add conflict edges dst <-> r for each r in L \ {dst, src}
         else if I is an instruction with result dst, and dst is live:
            add conflict edges dst <-> r for each r in L \ {dst};
         if I is a "call" instruction dst <- f(args),
            add conflict edges between all pseudo-registers in L \ {dst}
            and all caller-save machine registers
     done
>>
    Notice that edges are added only when a register becomes live.
    A register becomes live either if it is the result of an operation
    (and is live afterwards), or if we are at the function entrance
    and the register is a function parameter.  For two registers to
    be simultaneously live at some program point, it must be the case
    that one becomes live at a point where the other is already live.
    Hence, it suffices to add interference edges between registers
    that become live at some instruction and registers that are already
    live at this instruction.  

    Notice also the special treatment of ``move'' instructions:
    since the destination register of the ``move'' is assigned the same value
    as the source register, it is semantically correct to assign
    the destination and the source registers to the same register,
    even if the source register remains live afterwards.
    (This is even desirable, since the ``move'' instruction can then
    be eliminated.)  Thus, no interference is added between the
    source and the destination of a ``move'' instruction.

    Finally, for ``call'' instructions, we must make sure that
    pseudo-registers live across the instruction are allocated to
    callee-save machine register or to stack slots, but never to
    caller-save machine registers (these lose their values across
    the call).  We therefore add the corresponding conflict edges
    between pseudo-registers live across and caller-save machine
    registers (pairwise).  

    The full algorithm is similar to the simplified algorithm above,
    but records preference edges in addition to conflict edges.
    Preference edges guide the graph coloring algorithm by telling it
    that better code will be obtained eventually if it is possible
    to allocate certain pseudo-registers to the same location or to
    a given machine register.  Preference edges are added:
-   between the destination and source pseudo-registers of a ``move''
    instruction;
-   between the arguments of a ``call'' instruction and the locations
    of the arguments as dictated by the calling conventions;
-   between the result of a ``call'' instruction and the location
    of the result as dictated by the calling conventions.
*)

Definition add_interf_live
    (filter: reg -> bool) (res: reg) (live: Regset.t) (g: graph): graph :=
  Regset.fold 
    (fun r g => if filter r then add_interf r res g else g) live g.

Definition add_interf_op
    (res: reg) (live: Regset.t) (g: graph): graph :=
  add_interf_live
    (fun r => if Reg.eq r res then false else true)
    res live g.

Definition add_interf_move
    (arg res: reg) (live: Regset.t) (g: graph): graph :=
  add_interf_live
    (fun r =>
       if Reg.eq r res then false else
       if Reg.eq r arg then false else true)
    res live g.

Definition add_interf_destroyed
    (live: Regset.t) (destroyed: list mreg) (g: graph): graph :=
  List.fold_left
    (fun g mr => Regset.fold (fun r g => add_interf_mreg r mr g) live g)
    destroyed g.

Definition add_interfs_indirect_call
    (rfun: reg) (locs: list loc) (g: graph): graph :=
  List.fold_left
    (fun g loc =>
      match loc with R mr => add_interf_mreg rfun mr g | _ => g end)
    locs g.

Definition add_interf_call
    (ros: reg + ident) (locs: list loc) (g: graph): graph :=
  match ros with
  | inl rfun => add_interfs_indirect_call rfun locs g
  | inr idfun => g
  end.

Fixpoint add_prefs_call
    (args: list reg) (locs: list loc) (g: graph) {struct args} : graph :=
  match args, locs with
  | a1 :: al, l1 :: ll =>
      add_prefs_call al ll
        (match l1 with R mr => add_pref_mreg a1 mr g | _ => g end)
  | _, _ => g
  end.

Definition add_prefs_builtin (ef: external_function)
                            (args: list reg) (res: reg) (g: graph) : graph :=
  match ef, args with
  | EF_annot_val txt targ, arg1 :: _ => add_pref arg1 res g
  | _, _ => g
  end.

Definition add_interf_entry
    (params: list reg) (live: Regset.t) (g: graph): graph :=
  List.fold_left (fun g r => add_interf_op r live g) params g.

Fixpoint add_interf_params
    (params: list reg) (g: graph) {struct params}: graph :=
  match params with
  | nil => g
  | p1 :: pl =>
      add_interf_params pl
        (List.fold_left
          (fun g r => if Reg.eq r p1 then g else add_interf r p1 g)
          pl g)
  end.

Definition add_edges_instr
    (sig: signature) (i: instruction) (live: Regset.t) (g: graph) : graph :=
  match i with
  | Iop op args res s =>
      if Regset.mem res live then
        match is_move_operation op args with
        | Some arg =>
            add_pref arg res (add_interf_move arg res live g)
        | None =>
            add_interf_op res live g
        end
      else g
  | Iload chunk addr args dst s =>
      if Regset.mem dst live
      then add_interf_op dst live g
      else g
  | Icall sig ros args res s =>
      let largs := loc_arguments sig in
      let lres := loc_result sig in
      add_prefs_call args largs
        (add_pref_mreg res lres
          (add_interf_op res live
            (add_interf_call ros largs
              (add_interf_destroyed
                (Regset.remove res live) destroyed_at_call_regs g))))
  | Itailcall sig ros args =>
      let largs := loc_arguments sig in
      add_prefs_call args largs
        (add_interf_call ros largs g)
  | Ibuiltin ef args res s =>
      add_prefs_builtin ef args res (add_interf_op res live g)
  | Ireturn (Some r) =>
      add_pref_mreg r (loc_result sig) g
  | _ => g
  end.

Definition add_edges_instrs (f: function) (live: PMap.t Regset.t) : graph :=
  PTree.fold
    (fun g pc i => add_edges_instr f.(fn_sig) i live!!pc g)
    f.(fn_code)
    empty_graph.

Definition interf_graph (f: function) (live: PMap.t Regset.t) (live0: Regset.t) :=
  add_prefs_call f.(fn_params) (loc_parameters f.(fn_sig))
    (add_interf_params f.(fn_params)
      (add_interf_entry f.(fn_params) live0
        (add_edges_instrs f live))).

(** * Graph coloring *)

(** The actual coloring of the graph is performed by a function written
  directly in Caml, and not proved correct in any way.  This function
  takes as argument the [RTL] function, the interference graph for
  this function, an assignment of types to [RTL] pseudo-registers,
  and the set of all [RTL] pseudo-registers mentioned in the
  interference graph.  It returns the coloring as a function from
  pseudo-registers to locations. *)

Parameter graph_coloring: 
  function -> graph -> regenv -> Regset.t -> (reg -> loc).

(** To ensure that the result of [graph_coloring] is a correct coloring,
  we check a posteriori its result using the following Coq functions.
  Let [coloring] be the function [reg -> loc] returned by [graph_coloring].
  The three properties checked are:
- [coloring r1 <> coloring r2] if there is a conflict edge between
  [r1] and [r2] in the interference graph.
- [coloring r1 <> R m2] if there is a conflict edge between pseudo-register
  [r1] and machine register [m2] in the interference graph.
- For all [r] mentioned in the interference graph,
  the location [coloring r] is acceptable and has the same type as [r].
*)

Definition check_coloring_1 (g: graph) (coloring: reg -> loc) :=
  SetRegReg.for_all 
    (fun r1r2 =>
      if Loc.eq (coloring (fst r1r2)) (coloring (snd r1r2)) then false else true)
    g.(interf_reg_reg).

Definition check_coloring_2 (g: graph) (coloring: reg -> loc) :=
  SetRegMreg.for_all 
    (fun r1mr2 =>
      if Loc.eq (coloring (fst r1mr2)) (R (snd r1mr2)) then false else true)
    g.(interf_reg_mreg).

Definition same_typ (t1 t2: typ) :=
  match t1, t2 with
  | Tint, Tint => true
  | Tfloat, Tfloat => true
  | _, _ => false
  end.

Definition loc_is_acceptable (l: loc) :=
  match l with
  | R r => 
     if In_dec Loc.eq l temporaries then false else true
  | S (Local ofs ty) =>
     if zlt ofs 0 then false else true
  | _ =>
     false
  end.

Definition check_coloring_3 (rs: Regset.t) (env: regenv) (coloring: reg -> loc) :=
  Regset.for_all
    (fun r =>
      let l := coloring r in
      andb (loc_is_acceptable l) (same_typ (env r) (Loc.type l)))
    rs.

Definition check_coloring
       (g: graph) (env: regenv) (rs: Regset.t) (coloring: reg -> loc) :=
  andb (check_coloring_1 g coloring)
       (andb (check_coloring_2 g coloring)
             (check_coloring_3 rs env coloring)).

(** To preserve decidability of checking, the checks
  (especially the third one) are performed for the pseudo-registers
  mentioned in the interference graph.  To facilitate the proofs,
  it is convenient to ensure that the properties hold for all
  pseudo-registers.  To this end, we ``clip'' the candidate coloring
  returned by [graph_coloring]: the final coloring behave identically
  over pseudo-registers mentioned in the interference graph,
  but returns a dummy machine register of the correct type otherwise. *)

Definition alloc_of_coloring (coloring: reg -> loc) (env: regenv) (rs: Regset.t) :=
  fun r =>
    if Regset.mem r rs
    then coloring r
    else match env r with Tint => R dummy_int_reg | Tfloat => R dummy_float_reg end.

(** * Coloring of the interference graph *)

(** The following function combines the phases described above:
  construction of the interference graph, coloring by untrusted
  Caml code, checking of the candidate coloring returned,
  and adjustment of this coloring.  If the coloring candidate is
  incorrect, [None] is returned, causing register allocation to fail. *)

Definition regalloc
    (f: function) (live: PMap.t Regset.t) (live0: Regset.t) (env: regenv) :=
  let g := interf_graph f live live0 in
  let rs := all_interf_regs g in
  let coloring := graph_coloring f g env rs in
  if check_coloring g env rs coloring
  then Some (alloc_of_coloring coloring env rs)
  else None.
