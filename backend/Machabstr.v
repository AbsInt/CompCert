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

(** The Mach intermediate language: abstract semantics. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Memory.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Import Mach.
Require Stacklayout.

(** This file defines the "abstract" semantics for the Mach
  intermediate language, as opposed to the more concrete
  semantics given in module [Machconcr].

  The only difference with the concrete semantics is the interpretation
  of the stack access instructions [Mgetstack], [Msetstack] and [Mgetparam].
  In the concrete semantics, these are interpreted as memory accesses
  relative to the stack pointer.  In the abstract semantics, these 
  instructions are interpreted as accesses in a frame environment,
  not resident in memory.  The frame environment is an additional
  component of the state.

  Not having the frame data in memory facilitates the proof of
  the [Stacking] pass, which shows that the generated code executes
  correctly with the abstract semantics.
*)

(** * Structure of abstract stack frames *)

(** An abstract stack frame is a mapping from (type, offset) pairs to
    values.  Like location sets (see module [Locations]), overlap
    can occur. *)

Definition frame : Type := typ -> Z -> val.

Definition typ_eq: forall (ty1 ty2: typ), {ty1=ty2} + {ty1<>ty2}.
Proof. decide equality. Defined.

Definition update (ty: typ) (ofs: Z) (v: val) (f: frame) : frame :=
  fun ty' ofs' => 
    if zeq ofs ofs' then
      if typ_eq ty ty' then v else Vundef
    else
      if zle (ofs' + AST.typesize ty') ofs then f ty' ofs'
      else if zle (ofs + AST.typesize ty) ofs' then f ty' ofs'
      else Vundef.

Lemma update_same:
  forall ty ofs v fr,
  update ty ofs v fr ty ofs = v.
Proof.
  unfold update; intros. 
  rewrite zeq_true. rewrite dec_eq_true. auto.
Qed. 

Lemma update_other:
  forall ty ofs v fr ty' ofs',
  ofs + AST.typesize ty <= ofs' \/ ofs' + AST.typesize ty' <= ofs ->
  update ty ofs v fr ty' ofs' = fr ty' ofs'.
Proof.
  unfold update; intros.
  generalize (AST.typesize_pos ty). 
  generalize (AST.typesize_pos ty'). intros.
  rewrite zeq_false.
  destruct H. rewrite zle_false. apply zle_true. auto. omega.
  apply zle_true. auto. 
  omega.
Qed.

Definition empty_frame : frame := fun ty ofs => Vundef.

Section FRAME_ACCESSES.

Variable f: function.

(** A slot [(ty, ofs)] within a frame is valid in function [f] if it lies
  within the bounds of [f]'s frame, it does not overlap with
  the slots reserved for the return address and the back link,
  and it is aligned on a 4-byte boundary. *)

Inductive slot_valid: typ -> Z -> Prop :=
  slot_valid_intro:
    forall ty ofs,
    0 <= ofs ->
    ofs + AST.typesize ty <= f.(fn_framesize) ->
    (ofs + AST.typesize ty <= Int.signed f.(fn_link_ofs)
       \/ Int.signed f.(fn_link_ofs) + 4 <= ofs) ->
    (ofs + AST.typesize ty <= Int.signed f.(fn_retaddr_ofs)
       \/ Int.signed f.(fn_retaddr_ofs) + 4 <= ofs) ->
    (4 | ofs) ->
    slot_valid ty ofs.

(** [get_slot f fr ty ofs v] holds if the frame [fr] contains value [v]
  with type [ty] at word offset [ofs]. *)

Inductive get_slot: frame -> typ -> Z -> val -> Prop :=
  | get_slot_intro:
      forall fr ty ofs v,
      slot_valid ty ofs ->
      v = fr ty (ofs - f.(fn_framesize)) ->
      get_slot fr ty ofs v.

(** [set_slot f fr ty ofs v fr'] holds if frame [fr'] is obtained from
  frame [fr] by storing value [v] with type [ty] at word offset [ofs]. *)

Inductive set_slot: frame -> typ -> Z -> val -> frame -> Prop :=
  | set_slot_intro:
      forall fr ty ofs v fr',
      slot_valid ty ofs ->
      fr' = update ty (ofs - f.(fn_framesize)) v fr ->
      set_slot fr ty ofs v fr'.

(** Extract the values of the arguments of an external call. *)

Inductive extcall_arg: regset -> frame -> loc -> val -> Prop :=
  | extcall_arg_reg: forall rs fr r,
      extcall_arg rs fr (R r) (rs r)
  | extcall_arg_stack: forall rs fr ofs ty v,
      get_slot fr ty (Int.signed (Int.repr (Stacklayout.fe_ofs_arg + 4 * ofs))) v ->
      extcall_arg rs fr (S (Outgoing ofs ty)) v.

Inductive extcall_args: regset -> frame -> list loc -> list val -> Prop :=
  | extcall_args_nil: forall rs fr,
      extcall_args rs fr nil nil
  | extcall_args_cons: forall rs fr l1 ll v1 vl,
      extcall_arg rs fr l1 v1 -> extcall_args rs fr ll vl ->
      extcall_args rs fr (l1 :: ll) (v1 :: vl).

Definition extcall_arguments
   (rs: regset) (fr: frame) (sg: signature) (args: list val) : Prop :=
  extcall_args rs fr (loc_arguments sg) args.
    
End FRAME_ACCESSES.

(** Mach execution states. *)

Inductive stackframe: Type :=
  | Stackframe:
      forall (f: function)      (**r calling function *)
             (sp: val)          (**r stack pointer in calling function *)
             (c: code)          (**r program point in calling function *)
             (fr: frame),       (**r frame state in calling function *)
      stackframe.

Inductive state: Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r function currently executing *)
             (sp: val)                (**r stack pointer *)
             (c: code)                (**r current program point *)
             (rs: regset)             (**r register state *)
             (fr: frame)              (**r frame state *)
             (m: mem),                (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (rs: regset)             (**r register state *)
             (m: mem),                (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (rs: regset)             (**r register state *)
             (m: mem),                (**r memory state *)
      state.

(** [parent_frame s] returns the frame of the calling function.
  It is used to access function parameters that are passed on the stack
  (the [Mgetparent] instruction).
  [parent_function s] returns the calling function itself.
  Suitable defaults are used if there are no calling function. *)

Definition parent_frame (s: list stackframe) : frame :=
  match s with
  | nil => empty_frame
  | Stackframe f sp c fr :: s => fr
  end.

Definition empty_function := 
  mkfunction (mksignature nil None) nil 0 0 Int.zero Int.zero.

Definition parent_function (s: list stackframe) : function :=
  match s with
  | nil => empty_function
  | Stackframe f sp c fr :: s => f
  end.

Section RELSEM.

Variable ge: genv.

Definition find_function (ros: mreg + ident) (rs: regset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge (rs r)
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

Inductive step: state -> trace -> state -> Prop :=
  | exec_Mlabel:
      forall s f sp lbl c rs fr m,
      step (State s f sp (Mlabel lbl :: c) rs fr m)
        E0 (State s f sp c rs fr m)
  | exec_Mgetstack:
      forall s f sp ofs ty dst c rs fr m v,
      get_slot f fr ty (Int.signed ofs) v ->
      step (State s f sp (Mgetstack ofs ty dst :: c) rs fr m)
        E0 (State s f sp c (rs#dst <- v) fr m)
  | exec_Msetstack:
     forall s f sp src ofs ty c rs fr m fr',
      set_slot f fr ty (Int.signed ofs) (rs src) fr' ->
      step (State s f sp (Msetstack src ofs ty :: c) rs fr m)
        E0 (State s f sp c rs fr' m)
  | exec_Mgetparam:
      forall s f sp ofs ty dst c rs fr m v,
      get_slot (parent_function s) (parent_frame s) ty (Int.signed ofs) v ->
      step (State s f sp (Mgetparam ofs ty dst :: c) rs fr m)
        E0 (State s f sp c (rs # IT1 <- Vundef # dst <- v) fr m)
  | exec_Mop:
      forall s f sp op args res c rs fr m v,
      eval_operation ge sp op rs##args = Some v ->
      step (State s f sp (Mop op args res :: c) rs fr m)
        E0 (State s f sp c ((undef_op op rs)#res <- v) fr m)
  | exec_Mload:
      forall s f sp chunk addr args dst c rs fr m a v,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      step (State s f sp (Mload chunk addr args dst :: c) rs fr m)
        E0 (State s f sp c ((undef_temps rs)#dst <- v) fr m)
  | exec_Mstore:
      forall s f sp chunk addr args src c rs fr m m' a,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      step (State s f sp (Mstore chunk addr args src :: c) rs fr m)
        E0 (State s f sp c (undef_temps rs) fr m')
  | exec_Mcall:
      forall s f sp sig ros c rs fr m f',
      find_function ros rs = Some f' ->
      step (State s f sp (Mcall sig ros :: c) rs fr m)
        E0 (Callstate (Stackframe f sp c fr :: s) f' rs m)
  | exec_Mtailcall:
      forall s f stk soff sig ros c rs fr m f' m',
      find_function ros rs = Some f' ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk soff) (Mtailcall sig ros :: c) rs fr m)
        E0 (Callstate s f' rs m')
  | exec_Mbuiltin:
      forall s f sp rs fr m ef args res b t v m',
      external_call ef ge rs##args m t v m' ->
      step (State s f sp (Mbuiltin ef args res :: b) rs fr m)
         t (State s f sp b ((undef_temps rs)#res <- v) fr m')
  | exec_Mgoto:
      forall s f sp lbl c rs fr m c',
      find_label lbl f.(fn_code) = Some c' ->
      step (State s f sp (Mgoto lbl :: c) rs fr m)
        E0 (State s f sp c' rs fr m)
  | exec_Mcond_true:
      forall s f sp cond args lbl c rs fr m c',
      eval_condition cond rs##args = Some true ->
      find_label lbl f.(fn_code) = Some c' ->
      step (State s f sp (Mcond cond args lbl :: c) rs fr m)
        E0 (State s f sp c' (undef_temps rs) fr m)
  | exec_Mcond_false:
      forall s f sp cond args lbl c rs fr m,
      eval_condition cond rs##args = Some false ->
      step (State s f sp (Mcond cond args lbl :: c) rs fr m)
        E0 (State s f sp c (undef_temps rs) fr m)
  | exec_Mjumptable:
      forall s f sp arg tbl c rs fr m n lbl c',
      rs arg = Vint n ->
      list_nth_z tbl (Int.signed n) = Some lbl ->
      find_label lbl f.(fn_code) = Some c' ->
      step (State s f sp (Mjumptable arg tbl :: c) rs fr m)
        E0 (State s f sp c' (undef_temps rs) fr m)
  | exec_Mreturn:
      forall s f stk soff c rs fr m m',
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk soff) (Mreturn :: c) rs fr m)
        E0 (Returnstate s rs m')
  | exec_function_internal:
      forall s f rs m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      step (Callstate s (Internal f) rs m)
        E0 (State s f (Vptr stk (Int.repr (-f.(fn_framesize))))
                  f.(fn_code) rs empty_frame m')
  | exec_function_external:
      forall s ef args res rs1 rs2 m t m',
      external_call ef ge args m t res m' ->
      extcall_arguments (parent_function s) rs1 (parent_frame s) (ef_sig ef) args ->
      rs2 = (rs1#(loc_result (ef_sig ef)) <- res) ->
      step (Callstate s (External ef) rs1 m)
         t (Returnstate s rs2 m')
  | exec_return:
      forall f sp c fr s rs m,
      step (Returnstate (Stackframe f sp c fr :: s) rs m)
        E0 (State s f sp c rs fr m).

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      initial_state p (Callstate nil f (Regmap.init Vundef) m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs (loc_result (mksignature nil (Some Tint))) = Vint r ->
      final_state (Returnstate nil rs m) r.

Definition exec_program (p: program) (beh: program_behavior) : Prop :=
  program_behaves step (initial_state p) final_state (Genv.globalenv p) beh.
