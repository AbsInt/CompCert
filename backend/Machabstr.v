(** Alternate semantics for the Mach intermediate language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Mem.
Require Import Integers.
Require Import Values.
Require Import Mem.
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
      code -> regset -> frame -> mem ->
      code -> regset -> frame -> mem -> Prop :=
  | exec_Mlabel:
      forall f sp parent lbl c rs fr m,
      exec_instr f sp parent
                 (Mlabel lbl :: c) rs fr m
                 c rs fr m
  | exec_Mgetstack:
      forall f sp parent ofs ty dst c rs fr m v,
      get_slot fr ty (Int.signed ofs) v ->
      exec_instr f sp parent
                 (Mgetstack ofs ty dst :: c) rs fr m
                 c (rs#dst <- v) fr m
  | exec_Msetstack:
     forall f sp parent src ofs ty c rs fr m fr',
      set_slot fr ty (Int.signed ofs) (rs src) fr' ->
      exec_instr f sp parent
                 (Msetstack src ofs ty :: c) rs fr m
                 c rs fr' m
  | exec_Mgetparam:
      forall f sp parent ofs ty dst c rs fr m v,
      get_slot parent ty (Int.signed ofs) v ->
      exec_instr f sp parent
                 (Mgetparam ofs ty dst :: c) rs fr m
                 c (rs#dst <- v) fr m
  | exec_Mop:
      forall f sp parent op args res c rs fr m v,
      eval_operation ge sp op rs##args = Some v ->
      exec_instr f sp parent
                 (Mop op args res :: c) rs fr m
                 c (rs#res <- v) fr m
  | exec_Mload:
      forall f sp parent chunk addr args dst c rs fr m a v,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      exec_instr f sp parent
                 (Mload chunk addr args dst :: c) rs fr m
                 c (rs#dst <- v) fr m
  | exec_Mstore:
      forall f sp parent chunk addr args src c rs fr m m' a,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      exec_instr f sp parent
                 (Mstore chunk addr args src :: c) rs fr m
                 c rs fr m'
  | exec_Mcall:
      forall f sp parent sig ros c rs fr m f' rs' m',
      find_function ge ros rs = Some f' ->
      exec_function f' fr rs m rs' m' ->
      exec_instr f sp parent
                 (Mcall sig ros :: c) rs fr m
                 c rs' fr m'
  | exec_Mgoto:
      forall f sp parent lbl c rs fr m c',
      find_label lbl f.(fn_code) = Some c' ->
      exec_instr f sp parent
                 (Mgoto lbl :: c) rs fr m
                 c' rs fr m
  | exec_Mcond_true:
      forall f sp parent cond args lbl c rs fr m c',
      eval_condition cond rs##args = Some true ->
      find_label lbl f.(fn_code) = Some c' ->
      exec_instr f sp parent
                 (Mcond cond args lbl :: c) rs fr m
                 c' rs fr m
  | exec_Mcond_false:
      forall f sp parent cond args lbl c rs fr m,
      eval_condition cond rs##args = Some false ->
      exec_instr f sp parent
                 (Mcond cond args lbl :: c) rs fr m
                 c rs fr m

with exec_instrs:
      function -> val -> frame ->
      code -> regset -> frame -> mem ->
      code -> regset -> frame -> mem -> Prop :=
  | exec_refl:
      forall f sp parent c rs fr m,
      exec_instrs f sp parent  c rs fr m  c rs fr m
  | exec_one:
      forall f sp parent c rs fr m c' rs' fr' m',
      exec_instr f sp parent  c rs fr m  c' rs' fr' m' ->
      exec_instrs f sp parent  c rs fr m  c' rs' fr' m'
  | exec_trans:
      forall f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2 c3 rs3 fr3 m3,
      exec_instrs f sp parent  c1 rs1 fr1 m1  c2 rs2 fr2 m2 ->
      exec_instrs f sp parent  c2 rs2 fr2 m2  c3 rs3 fr3 m3 ->
      exec_instrs f sp parent  c1 rs1 fr1 m1  c3 rs3 fr3 m3

with exec_function_body:
      function -> frame -> val -> val ->
      regset -> mem -> regset -> mem -> Prop :=
  | exec_funct_body:
      forall f parent link ra rs m rs' m1 m2 stk fr1 fr2 fr3 c,
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      set_slot (init_frame f) Tint 0 link fr1 ->
      set_slot fr1 Tint 4 ra fr2 ->
      exec_instrs f (Vptr stk (Int.repr (-f.(fn_framesize)))) parent
                  f.(fn_code) rs fr2 m1
                  (Mreturn :: c) rs' fr3 m2 ->
      exec_function_body f parent link ra rs m rs' (Mem.free m2 stk)

with exec_function:
      function -> frame -> regset -> mem -> regset -> mem -> Prop :=
  | exec_funct:
      forall f parent rs m rs' m',
      (forall link ra, 
         Val.has_type link Tint ->
         Val.has_type ra Tint ->
         exec_function_body f parent link ra rs m rs' m') ->
      exec_function f parent rs m rs' m'.

Scheme exec_instr_ind4 := Minimality for exec_instr Sort Prop
  with exec_instrs_ind4 := Minimality for exec_instrs Sort Prop
  with exec_function_body_ind4 := Minimality for exec_function_body Sort Prop
  with exec_function_ind4 := Minimality for exec_function Sort Prop.

(** Ugly mutual induction principle over evaluation derivations.
  Coq is not able to generate it directly, even though it is
  an immediate consequence of the 4 induction principles generated
  by the [Scheme] command above. *)

Lemma exec_mutual_induction:
  forall (P
          P0 : function ->
               val ->
               frame ->
               code ->
               regset ->
               frame -> mem -> code -> regset -> frame -> mem -> Prop)
         (P1 : function ->
               frame -> val -> val -> regset -> mem -> regset -> mem -> Prop)
         (P2 : function -> frame -> regset -> mem -> regset -> mem -> Prop),
       (forall (f : function) (sp : val) (parent : frame) (lbl : label)
          (c : list instruction) (rs : regset) (fr : frame) (m : mem),
        P f sp parent (Mlabel lbl :: c) rs fr m c rs fr m) ->
       (forall (f : function) (sp : val) (parent : frame) (ofs : int)
          (ty : typ) (dst : mreg) (c : list instruction) (rs : regset)
          (fr : frame) (m : mem) (v : val),
        get_slot fr ty (Int.signed ofs) v ->
        P f sp parent (Mgetstack ofs ty dst :: c) rs fr m c rs # dst <- v fr
          m) ->
       (forall (f : function) (sp : val) (parent : frame) (src : mreg)
          (ofs : int) (ty : typ) (c : list instruction) (rs : mreg -> val)
          (fr : frame) (m : mem) (fr' : frame),
        set_slot fr ty (Int.signed ofs) (rs src) fr' ->
        P f sp parent (Msetstack src ofs ty :: c) rs fr m c rs fr' m) ->
       (forall (f : function) (sp : val) (parent : frame) (ofs : int)
          (ty : typ) (dst : mreg) (c : list instruction) (rs : regset)
          (fr : frame) (m : mem) (v : val),
        get_slot parent ty (Int.signed ofs) v ->
        P f sp parent (Mgetparam ofs ty dst :: c) rs fr m c rs # dst <- v fr
          m) ->
       (forall (f : function) (sp : val) (parent : frame) (op : operation)
          (args : list mreg) (res : mreg) (c : list instruction)
          (rs : mreg -> val) (fr : frame) (m : mem) (v : val),
        eval_operation ge sp op rs ## args = Some v ->
        P f sp parent (Mop op args res :: c) rs fr m c rs # res <- v fr m) ->
       (forall (f : function) (sp : val) (parent : frame)
          (chunk : memory_chunk) (addr : addressing) (args : list mreg)
          (dst : mreg) (c : list instruction) (rs : mreg -> val) (fr : frame)
          (m : mem) (a v : val),
        eval_addressing ge sp addr rs ## args = Some a ->
        loadv chunk m a = Some v ->
        P f sp parent (Mload chunk addr args dst :: c) rs fr m c
          rs # dst <- v fr m) ->
       (forall (f : function) (sp : val) (parent : frame)
          (chunk : memory_chunk) (addr : addressing) (args : list mreg)
          (src : mreg) (c : list instruction) (rs : mreg -> val) (fr : frame)
          (m m' : mem) (a : val),
        eval_addressing ge sp addr rs ## args = Some a ->
        storev chunk m a (rs src) = Some m' ->
        P f sp parent (Mstore chunk addr args src :: c) rs fr m c rs fr m') ->
       (forall (f : function) (sp : val) (parent : frame) (sig : signature)
          (ros : mreg + ident) (c : list instruction) (rs : regset)
          (fr : frame) (m : mem) (f' : function) (rs' : regset) (m' : mem),
        find_function ge ros rs = Some f' ->
        exec_function f' fr rs m rs' m' ->
        P2 f' fr rs m rs' m' ->
        P f sp parent (Mcall sig ros :: c) rs fr m c rs' fr m') ->
       (forall (f : function) (sp : val) (parent : frame) (lbl : label)
          (c : list instruction) (rs : regset) (fr : frame) (m : mem)
          (c' : code),
        find_label lbl (fn_code f) = Some c' ->
        P f sp parent (Mgoto lbl :: c) rs fr m c' rs fr m) ->
       (forall (f : function) (sp : val) (parent : frame)
          (cond : condition) (args : list mreg) (lbl : label)
          (c : list instruction) (rs : mreg -> val) (fr : frame) (m : mem)
          (c' : code),
        eval_condition cond rs ## args = Some true ->
        find_label lbl (fn_code f) = Some c' ->
        P f sp parent (Mcond cond args lbl :: c) rs fr m c' rs fr m) ->
       (forall (f : function) (sp : val) (parent : frame)
          (cond : condition) (args : list mreg) (lbl : label)
          (c : list instruction) (rs : mreg -> val) (fr : frame) (m : mem),
        eval_condition cond rs ## args = Some false ->
        P f sp parent (Mcond cond args lbl :: c) rs fr m c rs fr m) ->
       (forall (f : function) (sp : val) (parent : frame) (c : code)
          (rs : regset) (fr : frame) (m : mem),
        P0 f sp parent c rs fr m c rs fr m) ->
       (forall (f : function) (sp : val) (parent : frame) (c : code)
          (rs : regset) (fr : frame) (m : mem) (c' : code) (rs' : regset)
          (fr' : frame) (m' : mem),
        exec_instr f sp parent c rs fr m c' rs' fr' m' ->
        P f sp parent c rs fr m c' rs' fr' m' ->
        P0 f sp parent c rs fr m c' rs' fr' m') ->
       (forall (f : function) (sp : val) (parent : frame) (c1 : code)
          (rs1 : regset) (fr1 : frame) (m1 : mem) (c2 : code) (rs2 : regset)
          (fr2 : frame) (m2 : mem) (c3 : code) (rs3 : regset) (fr3 : frame)
          (m3 : mem),
        exec_instrs f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2 ->
        P0 f sp parent c1 rs1 fr1 m1 c2 rs2 fr2 m2 ->
        exec_instrs f sp parent c2 rs2 fr2 m2 c3 rs3 fr3 m3 ->
        P0 f sp parent c2 rs2 fr2 m2 c3 rs3 fr3 m3 ->
        P0 f sp parent c1 rs1 fr1 m1 c3 rs3 fr3 m3) ->
       (forall (f : function) (parent : frame) (link ra : val) (rs : regset)
          (m : mem) (rs' : regset) (m1 m2 : mem) (stk : block)
          (fr1 fr2 fr3 : frame) (c : list instruction),
        alloc m 0 (fn_stacksize f) = (m1, stk) ->
        set_slot (init_frame f) Tint 0 link fr1 ->
        set_slot fr1 Tint 4 ra fr2 ->
        exec_instrs f (Vptr stk (Int.repr (-f.(fn_framesize)))) parent (fn_code f) rs fr2 m1 (Mreturn :: c) rs' fr3
          m2 ->
        P0 f (Vptr stk (Int.repr (-f.(fn_framesize)))) parent (fn_code f) rs fr2 m1 (Mreturn :: c) rs' fr3 m2 ->
        P1 f parent link ra rs m rs' (free m2 stk)) ->
       (forall (f : function) (parent : frame) (rs : regset) (m : mem)
          (rs' : regset) (m' : mem),
        (forall link ra : val,
         Val.has_type link Tint ->
         Val.has_type ra Tint ->
         exec_function_body f parent link ra rs m rs' m') ->
        (forall link ra : val,
         Val.has_type link Tint ->
         Val.has_type ra Tint -> P1 f parent link ra rs m rs' m') ->
        P2 f parent rs m rs' m') ->
       (forall (f15 : function) (sp : val) (f16 : frame) (c : code)
         (r : regset) (f17 : frame) (m : mem) (c0 : code) (r0 : regset)
         (f18 : frame) (m0 : mem),
       exec_instr f15 sp f16 c r f17 m c0 r0 f18 m0 ->
       P f15 sp f16 c r f17 m c0 r0 f18 m0)
   /\  (forall (f15 : function) (sp : val) (f16 : frame) (c : code)
         (r : regset) (f17 : frame) (m : mem) (c0 : code) (r0 : regset)
         (f18 : frame) (m0 : mem),
       exec_instrs f15 sp f16 c r f17 m c0 r0 f18 m0 ->
       P0 f15 sp f16 c r f17 m c0 r0 f18 m0)
   /\  (forall (f15 : function) (f16 : frame) (v1 v2 : val) (r : regset) (m : mem)
         (r0 : regset) (m0 : mem),
       exec_function_body f15 f16 v1 v2 r m r0 m0 -> P1 f15 f16 v1 v2 r m r0 m0)
   /\  (forall (f15 : function) (f16 : frame) (r : regset) (m : mem)
         (r0 : regset) (m0 : mem),
       exec_function f15 f16 r m r0 m0 -> P2 f15 f16 r m r0 m0).
Proof.
  intros. split. apply (exec_instr_ind4 P P0 P1 P2); assumption.
  split. apply (exec_instrs_ind4 P P0 P1 P2); assumption.
  split. apply (exec_function_body_ind4 P P0 P1 P2); assumption.
  apply (exec_function_ind4 P P0 P1 P2); assumption.
Qed.

End RELSEM.

Definition exec_program (p: program) (r: val) : Prop :=
  let ge := Genv.globalenv p in
  let m0 := Genv.init_mem p in
  exists b, exists f, exists rs, exists m,
  Genv.find_symbol ge p.(prog_main) = Some b /\
  Genv.find_funct_ptr ge b = Some f /\
  f.(fn_sig) = mksignature nil (Some Tint) /\
  exec_function ge f empty_frame (Regmap.init Vundef) m0 rs m /\
  rs (Conventions.loc_result f.(fn_sig)) = r.

