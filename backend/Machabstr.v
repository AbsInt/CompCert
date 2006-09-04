(** Alternate semantics for the Mach intermediate language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Mem.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Conventions.
Require Import Mach.

(** This file defines an alternate semantics for the Mach intermediate
  language, which differ from the standard semantics given in file [Mach]
  as follows: the stack access instructions [Mgetstack], [Msetstack]
  and [Mgetparam] are interpreted not as memory accesses, but as
  accesses in a frame environment, not resident in memory.  The evaluation
  relations take two such frame environments as parameters and results,
  one for the current function and one for its caller. 

  Not having the frame data in memory facilitates the proof of
  the [Stacking] pass, which shows that the generated code executes
  correctly with the alternate semantics.  In file [Machabstr2mach],
  we show an implication from this alternate semantics to
  the standard semantics, thus establishing that the [Stacking] pass
  generates code that behaves correctly against the standard [Mach]
  semantics as well. *)

(** * Structure of abstract stack frames *)

(** A frame has the same structure as the contents of a memory block. *)

Definition frame := block_contents.

Definition empty_frame := empty_block 0 0.

Definition mem_type (ty: typ) :=
  match ty with Tint => Size32 | Tfloat => Size64 end.

(** [get_slot fr ty ofs v] holds if the frame [fr] contains value [v]
  with type [ty] at word offset [ofs]. *)

Inductive get_slot: frame -> typ -> Z -> val -> Prop :=
  | get_slot_intro:
      forall fr ty ofs v,
      0 <= ofs ->
      fr.(low) + ofs + 4 * typesize ty <= 0 ->
      v = load_contents (mem_type ty) fr.(contents) (fr.(low) + ofs) -> 
      get_slot fr ty ofs v.

Remark size_mem_type:
  forall ty, size_mem (mem_type ty) = 4 * typesize ty.
Proof.
  destruct ty; reflexivity.
Qed.

Remark set_slot_undef_outside:
  forall fr ty ofs v,
  fr.(high) = 0 ->
  0 <= ofs ->
  fr.(low) + ofs + 4 * typesize ty <= 0 ->
  (forall x, x < fr.(low) \/ x >= fr.(high) -> fr.(contents) x = Undef) ->
  (forall x, x < fr.(low) \/ x >= fr.(high) ->
     store_contents (mem_type ty) fr.(contents) (fr.(low) + ofs) v x = Undef).
Proof.
  intros. apply store_contents_undef_outside with fr.(low) fr.(high).
  rewrite <- size_mem_type in H1. omega. assumption. assumption.
Qed.  

(** [set_slot fr ty ofs v fr'] holds if frame [fr'] is obtained from
  frame [fr] by storing value [v] with type [ty] at word offset [ofs]. *)

Inductive set_slot: frame -> typ -> Z -> val -> frame -> Prop :=
  | set_slot_intro:
      forall fr ty ofs v
      (A: fr.(high) = 0)
      (B: 0 <= ofs)
      (C: fr.(low) + ofs + 4 * typesize ty <= 0),
      set_slot fr ty ofs v
        (mkblock fr.(low) fr.(high)
          (store_contents (mem_type ty) fr.(contents) (fr.(low) + ofs) v)
          (set_slot_undef_outside fr ty ofs v A B C fr.(undef_outside))).

Definition init_frame (f: function) :=
  empty_block (- f.(fn_framesize)) 0.

Section RELSEM.

Variable ge: genv.

(** Execution of one instruction has the form
  [exec_instr ge f sp parent c rs fr m c' rs' fr' m'],
  where [parent] is the caller's frame (read-only)
  and [fr], [fr'] are the current frame, before and after execution
  of one instruction.  The other parameters are as in the Mach semantics. *)

Inductive exec_instr:
      function -> val -> frame ->
      code -> regset -> frame -> mem -> trace ->
      code -> regset -> frame -> mem -> Prop :=
  | exec_Mlabel:
      forall f sp parent lbl c rs fr m,
      exec_instr f sp parent
                 (Mlabel lbl :: c) rs fr m
              E0 c rs fr m
  | exec_Mgetstack:
      forall f sp parent ofs ty dst c rs fr m v,
      get_slot fr ty (Int.signed ofs) v ->
      exec_instr f sp parent
                 (Mgetstack ofs ty dst :: c) rs fr m
              E0 c (rs#dst <- v) fr m
  | exec_Msetstack:
     forall f sp parent src ofs ty c rs fr m fr',
      set_slot fr ty (Int.signed ofs) (rs src) fr' ->
      exec_instr f sp parent
                 (Msetstack src ofs ty :: c) rs fr m
              E0 c rs fr' m
  | exec_Mgetparam:
      forall f sp parent ofs ty dst c rs fr m v,
      get_slot parent ty (Int.signed ofs) v ->
      exec_instr f sp parent
                 (Mgetparam ofs ty dst :: c) rs fr m
              E0 c (rs#dst <- v) fr m
  | exec_Mop:
      forall f sp parent op args res c rs fr m v,
      eval_operation ge sp op rs##args = Some v ->
      exec_instr f sp parent
                 (Mop op args res :: c) rs fr m
              E0 c (rs#res <- v) fr m
  | exec_Mload:
      forall f sp parent chunk addr args dst c rs fr m a v,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      exec_instr f sp parent
                 (Mload chunk addr args dst :: c) rs fr m
              E0 c (rs#dst <- v) fr m
  | exec_Mstore:
      forall f sp parent chunk addr args src c rs fr m m' a,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      exec_instr f sp parent
                 (Mstore chunk addr args src :: c) rs fr m
              E0 c rs fr m'
  | exec_Mcall:
      forall f sp parent sig ros c rs fr m t f' rs' m',
      find_function ge ros rs = Some f' ->
      exec_function f' fr rs m t rs' m' ->
      exec_instr f sp parent
                 (Mcall sig ros :: c) rs fr m
               t c rs' fr m'
  | exec_Malloc:
      forall f sp parent c rs fr m sz m' blk,
      rs (Conventions.loc_alloc_argument) = Vint sz ->
      Mem.alloc m 0 (Int.signed sz) = (m', blk) ->
      exec_instr f sp parent
                 (Malloc :: c) rs fr m
              E0 c (rs#Conventions.loc_alloc_result <- 
                                              (Vptr blk Int.zero)) fr m'
  | exec_Mgoto:
      forall f sp parent lbl c rs fr m c',
      find_label lbl f.(fn_code) = Some c' ->
      exec_instr f sp parent
                 (Mgoto lbl :: c) rs fr m
              E0 c' rs fr m
  | exec_Mcond_true:
      forall f sp parent cond args lbl c rs fr m c',
      eval_condition cond rs##args = Some true ->
      find_label lbl f.(fn_code) = Some c' ->
      exec_instr f sp parent
                 (Mcond cond args lbl :: c) rs fr m
              E0 c' rs fr m
  | exec_Mcond_false:
      forall f sp parent cond args lbl c rs fr m,
      eval_condition cond rs##args = Some false ->
      exec_instr f sp parent
                 (Mcond cond args lbl :: c) rs fr m
              E0 c rs fr m

with exec_instrs:
      function -> val -> frame ->
      code -> regset -> frame -> mem -> trace ->
      code -> regset -> frame -> mem -> Prop :=
  | exec_refl:
      forall f sp parent c rs fr m,
      exec_instrs f sp parent  c rs fr m E0 c rs fr m
  | exec_one:
      forall f sp parent c rs fr m t c' rs' fr' m',
      exec_instr f sp parent  c rs fr m t c' rs' fr' m' ->
      exec_instrs f sp parent  c rs fr m t c' rs' fr' m'
  | exec_trans:
      forall f sp parent c1 rs1 fr1 m1 t1 c2 rs2 fr2 m2 t2 c3 rs3 fr3 m3 t3,
      exec_instrs f sp parent  c1 rs1 fr1 m1 t1 c2 rs2 fr2 m2 ->
      exec_instrs f sp parent  c2 rs2 fr2 m2 t2 c3 rs3 fr3 m3 ->
      t3 = t1 ** t2 ->
      exec_instrs f sp parent  c1 rs1 fr1 m1 t3 c3 rs3 fr3 m3

with exec_function_body:
      function -> frame -> val -> val ->
      regset -> mem -> trace -> regset -> mem -> Prop :=
  | exec_funct_body:
      forall f parent link ra rs m t rs' m1 m2 stk fr1 fr2 fr3 c,
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      set_slot (init_frame f) Tint 0 link fr1 ->
      set_slot fr1 Tint 4 ra fr2 ->
      exec_instrs f (Vptr stk (Int.repr (-f.(fn_framesize)))) parent
                  f.(fn_code) rs fr2 m1
                t (Mreturn :: c) rs' fr3 m2 ->
      exec_function_body f parent link ra rs m t rs' (Mem.free m2 stk)

with exec_function:
      fundef -> frame -> regset -> mem -> trace -> regset -> mem -> Prop :=
  | exec_funct_internal:
      forall f parent rs m t rs' m',
      (forall link ra, 
         Val.has_type link Tint ->
         Val.has_type ra Tint ->
         exec_function_body f parent link ra rs m t rs' m') ->
      exec_function (Internal f) parent rs m t rs' m'
  | exec_funct_external:
      forall ef parent args res rs1 rs2 m t,
      event_match ef args t res ->
      args = rs1##(Conventions.loc_external_arguments ef.(ef_sig)) ->
      rs2 = (rs1#(Conventions.loc_result ef.(ef_sig)) <- res) ->
      exec_function (External ef) parent rs1 m t rs2 m.

Scheme exec_instr_ind4 := Minimality for exec_instr Sort Prop
  with exec_instrs_ind4 := Minimality for exec_instrs Sort Prop
  with exec_function_body_ind4 := Minimality for exec_function_body Sort Prop
  with exec_function_ind4 := Minimality for exec_function Sort Prop.

(** Ugly mutual induction principle over evaluation derivations.
  Coq is not able to generate it directly, even though it is
  an immediate consequence of the 4 induction principles generated
  by the [Scheme] command above. *)

Lemma exec_mutual_induction:
 forall
         (P
          P0 : function ->
               val ->
               frame ->
               code ->
               regset ->
               frame ->
               mem -> trace -> code -> regset -> frame -> mem -> Prop)
         (P1 : function ->
               frame ->
               val -> val -> regset -> mem -> trace -> regset -> mem -> Prop)
         (P2 : fundef ->
               frame -> regset -> mem -> trace -> regset -> mem -> Prop),
       (forall (f : function) (sp : val) (parent : frame) (lbl : label)
          (c : list instruction) (rs : regset) (fr : frame) (m : mem),
        P f sp parent (Mlabel lbl :: c) rs fr m E0 c rs fr m) ->
       (forall (f0 : function) (sp : val) (parent : frame) (ofs : int)
          (ty : typ) (dst : mreg) (c : list instruction) (rs : regset)
          (fr : frame) (m : mem) (v : val),
        get_slot fr ty (Int.signed ofs) v ->
        P f0 sp parent (Mgetstack ofs ty dst :: c) rs fr m E0 c rs # dst <- v
          fr m) ->
       (forall (f1 : function) (sp : val) (parent : frame) (src : mreg)
          (ofs : int) (ty : typ) (c : list instruction) (rs : mreg -> val)
          (fr : frame) (m : mem) (fr' : frame),
        set_slot fr ty (Int.signed ofs) (rs src) fr' ->
        P f1 sp parent (Msetstack src ofs ty :: c) rs fr m E0 c rs fr' m) ->
       (forall (f2 : function) (sp : val) (parent : frame) (ofs : int)
          (ty : typ) (dst : mreg) (c : list instruction) (rs : regset)
          (fr : frame) (m : mem) (v : val),
        get_slot parent ty (Int.signed ofs) v ->
        P f2 sp parent (Mgetparam ofs ty dst :: c) rs fr m E0 c rs # dst <- v
          fr m) ->
       (forall (f3 : function) (sp : val) (parent : frame) (op : operation)
          (args : list mreg) (res : mreg) (c : list instruction)
          (rs : mreg -> val) (fr : frame) (m : mem) (v : val),
        eval_operation ge sp op rs ## args = Some v ->
        P f3 sp parent (Mop op args res :: c) rs fr m E0 c rs # res <- v fr m) ->
       (forall (f4 : function) (sp : val) (parent : frame)
          (chunk : memory_chunk) (addr : addressing) (args : list mreg)
          (dst : mreg) (c : list instruction) (rs : mreg -> val) (fr : frame)
          (m : mem) (a v : val),
        eval_addressing ge sp addr rs ## args = Some a ->
        loadv chunk m a = Some v ->
        P f4 sp parent (Mload chunk addr args dst :: c) rs fr m E0 c
          rs # dst <- v fr m) ->
       (forall (f5 : function) (sp : val) (parent : frame)
          (chunk : memory_chunk) (addr : addressing) (args : list mreg)
          (src : mreg) (c : list instruction) (rs : mreg -> val) (fr : frame)
          (m m' : mem) (a : val),
        eval_addressing ge sp addr rs ## args = Some a ->
        storev chunk m a (rs src) = Some m' ->
        P f5 sp parent (Mstore chunk addr args src :: c) rs fr m E0 c rs fr
          m') ->
       (forall (f6 : function) (sp : val) (parent : frame) (sig : signature)
          (ros : mreg + ident) (c : list instruction) (rs : regset)
          (fr : frame) (m : mem) (t : trace) (f' : fundef) (rs' : regset)
          (m' : mem),
        find_function ge ros rs = Some f' ->
        exec_function f' fr rs m t rs' m' ->
        P2 f' fr rs m t rs' m' ->
        P f6 sp parent (Mcall sig ros :: c) rs fr m t c rs' fr m') ->
       (forall (f7 : function) (sp : val) (parent : frame)
          (c : list instruction) (rs : mreg -> val) (fr : frame) (m : mem)
          (sz : int) (m' : mem) (blk : block),
        rs Conventions.loc_alloc_argument = Vint sz ->
        alloc m 0 (Int.signed sz) = (m', blk) ->
        P f7 sp parent (Malloc :: c) rs fr m E0 c
          rs # Conventions.loc_alloc_result <- (Vptr blk Int.zero) fr m') ->
       (forall (f7 : function) (sp : val) (parent : frame) (lbl : label)
          (c : list instruction) (rs : regset) (fr : frame) (m : mem)
          (c' : code),
        find_label lbl (fn_code f7) = Some c' ->
        P f7 sp parent (Mgoto lbl :: c) rs fr m E0 c' rs fr m) ->
       (forall (f8 : function) (sp : val) (parent : frame) (cond : condition)
          (args : list mreg) (lbl : label) (c : list instruction)
          (rs : mreg -> val) (fr : frame) (m : mem) (c' : code),
        eval_condition cond rs ## args = Some true ->
        find_label lbl (fn_code f8) = Some c' ->
        P f8 sp parent (Mcond cond args lbl :: c) rs fr m E0 c' rs fr m) ->
       (forall (f9 : function) (sp : val) (parent : frame) (cond : condition)
          (args : list mreg) (lbl : label) (c : list instruction)
          (rs : mreg -> val) (fr : frame) (m : mem),
        eval_condition cond rs ## args = Some false ->
        P f9 sp parent (Mcond cond args lbl :: c) rs fr m E0 c rs fr m) ->
       (forall (f10 : function) (sp : val) (parent : frame) (c : code)
          (rs : regset) (fr : frame) (m : mem),
        P0 f10 sp parent c rs fr m E0 c rs fr m) ->
       (forall (f11 : function) (sp : val) (parent : frame) (c : code)
          (rs : regset) (fr : frame) (m : mem) (t : trace) (c' : code)
          (rs' : regset) (fr' : frame) (m' : mem),
        exec_instr f11 sp parent c rs fr m t c' rs' fr' m' ->
        P f11 sp parent c rs fr m t c' rs' fr' m' ->
        P0 f11 sp parent c rs fr m t c' rs' fr' m') ->
       (forall (f12 : function) (sp : val) (parent : frame) (c1 : code)
          (rs1 : regset) (fr1 : frame) (m1 : mem) (t1 : trace) (c2 : code)
          (rs2 : regset) (fr2 : frame) (m2 : mem) (t2 : trace) (c3 : code)
          (rs3 : regset) (fr3 : frame) (m3 : mem) (t3 : trace),
        exec_instrs f12 sp parent c1 rs1 fr1 m1 t1 c2 rs2 fr2 m2 ->
        P0 f12 sp parent c1 rs1 fr1 m1 t1 c2 rs2 fr2 m2 ->
        exec_instrs f12 sp parent c2 rs2 fr2 m2 t2 c3 rs3 fr3 m3 ->
        P0 f12 sp parent c2 rs2 fr2 m2 t2 c3 rs3 fr3 m3 ->
        t3 = t1 ** t2 -> P0 f12 sp parent c1 rs1 fr1 m1 t3 c3 rs3 fr3 m3) ->
       (forall (f13 : function) (parent : frame) (link ra : val)
          (rs : regset) (m : mem) (t : trace) (rs' : regset) (m1 m2 : mem)
          (stk : block) (fr1 fr2 fr3 : frame) (c : list instruction),
        alloc m 0 (fn_stacksize f13) = (m1, stk) ->
        set_slot (init_frame f13) Tint 0 link fr1 ->
        set_slot fr1 Tint 4 ra fr2 ->
        exec_instrs f13 (Vptr stk (Int.repr (- fn_framesize f13))) parent
          (fn_code f13) rs fr2 m1 t (Mreturn :: c) rs' fr3 m2 ->
        P0 f13 (Vptr stk (Int.repr (- fn_framesize f13))) parent
          (fn_code f13) rs fr2 m1 t (Mreturn :: c) rs' fr3 m2 ->
        P1 f13 parent link ra rs m t rs' (free m2 stk)) ->
       (forall (f14 : function) (parent : frame) (rs : regset) (m : mem)
          (t : trace) (rs' : regset) (m' : mem),
        (forall link ra : val,
         Val.has_type link Tint ->
         Val.has_type ra Tint ->
         exec_function_body f14 parent link ra rs m t rs' m') ->
        (forall link ra : val,
         Val.has_type link Tint ->
         Val.has_type ra Tint -> P1 f14 parent link ra rs m t rs' m') ->
        P2 (Internal f14) parent rs m t rs' m') ->
       (forall (ef : external_function) (parent : frame) (args : list val)
          (res : val) (rs1 : mreg -> val) (rs2 : RegEq.t -> val) (m : mem)
          (t0 : trace),
        event_match ef args t0 res ->
        args = rs1 ## (Conventions.loc_external_arguments (ef_sig ef)) ->
        rs2 = rs1 # (Conventions.loc_result (ef_sig ef)) <- res ->
        P2 (External ef) parent rs1 m t0 rs2 m) ->
      (forall (f16 : function) (v : val) (f17 : frame) (c : code)
         (r : regset) (f18 : frame) (m : mem) (t : trace) (c0 : code)
         (r0 : regset) (f19 : frame) (m0 : mem),
       exec_instr f16 v f17 c r f18 m t c0 r0 f19 m0 ->
       P f16 v f17 c r f18 m t c0 r0 f19 m0)
   /\ (forall (f16 : function) (v : val) (f17 : frame) (c : code)
         (r : regset) (f18 : frame) (m : mem) (t : trace) (c0 : code)
         (r0 : regset) (f19 : frame) (m0 : mem),
       exec_instrs f16 v f17 c r f18 m t c0 r0 f19 m0 ->
       P0 f16 v f17 c r f18 m t c0 r0 f19 m0)
   /\ (forall (f16 : function) (f17 : frame) (v v0 : val) (r : regset)
         (m : mem) (t : trace) (r0 : regset) (m0 : mem),
       exec_function_body f16 f17 v v0 r m t r0 m0 ->
       P1 f16 f17 v v0 r m t r0 m0)
   /\ (forall (f16 : fundef) (f17 : frame) (r : regset) (m : mem) (t : trace)
         (r0 : regset) (m0 : mem),
       exec_function f16 f17 r m t r0 m0 -> P2 f16 f17 r m t r0 m0).
Proof.
  intros. split. apply (exec_instr_ind4 P P0 P1 P2); assumption.
  split. apply (exec_instrs_ind4 P P0 P1 P2); assumption.
  split. apply (exec_function_body_ind4 P P0 P1 P2); assumption.
  apply (exec_function_ind4 P P0 P1 P2); assumption.
Qed.

End RELSEM.

Definition exec_program (p: program) (t: trace) (r: val) : Prop :=
  let ge := Genv.globalenv p in
  let m0 := Genv.init_mem p in
  exists b, exists f, exists rs, exists m,
  Genv.find_symbol ge p.(prog_main) = Some b /\
  Genv.find_funct_ptr ge b = Some f /\
  exec_function ge f empty_frame (Regmap.init Vundef) m0 t rs m /\
  rs R3 = r.

