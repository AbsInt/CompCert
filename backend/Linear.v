(** The Linear intermediate language: abstract syntax and semantcs *)

(** The Linear language is a variant of LTL where control-flow is not
    expressed as a graph of basic blocks, but as a linear list of
    instructions with explicit labels and ``goto'' instructions. *)

Require Import Relations.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Mem.
Require Import Events.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Conventions.

(** * Abstract syntax *)

Definition label := positive.

(** Linear instructions are similar to their LTL counterpart:
  arguments and results are machine registers, except for the
  [Lgetstack] and [Lsetstack] instructions which are register-stack moves.
  Except the last three, these instructions continue in sequence
  with the next instruction in the linear list of instructions.
  Unconditional branches [Lgoto] and conditional branches [Lcond]
  transfer control to the given code label.  Labels are explicitly
  inserted in the instruction list as pseudo-instructions [Llabel]. *)

Inductive instruction: Set :=
  | Lgetstack: slot -> mreg -> instruction
  | Lsetstack: mreg -> slot -> instruction
  | Lop: operation -> list mreg -> mreg -> instruction
  | Lload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Lstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Lcall: signature -> mreg + ident -> instruction
  | Lalloc: instruction
  | Llabel: label -> instruction
  | Lgoto: label -> instruction
  | Lcond: condition -> list mreg -> label -> instruction
  | Lreturn: instruction.

Definition code: Set := list instruction.

Record function: Set := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.

Definition genv := Genv.t fundef.
Definition locset := Locmap.t.

(** * Operational semantics *)

(** Looking up labels in the instruction list.  *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Llabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Llabel lbl else instr <> Llabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

(** [find_label lbl c] returns a list of instruction, suffix of the
  code [c], that immediately follows the [Llabel lbl] pseudo-instruction.
  If the label [lbl] is multiply-defined, the first occurrence is
  retained.  If the label [lbl] is not defined, [None] is returned. *)

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
  end.

Section RELSEM.

Variable ge: genv.

Definition find_function (ros: mreg + ident) (rs: locset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge (rs (R r))
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

(** [exec_instr ge f sp c ls m c' ls' m'] represents the execution
  of the first instruction in the code sequence [c].  [ls] and [m]
  are the initial location set and memory state, respectively.
  [c'] is the current code sequence after execution of the instruction:
  it is the tail of [c] if the instruction falls through. 
  [ls'] and [m'] are the final location state and memory state. *)

Inductive exec_instr: function -> val ->
                      code -> locset -> mem -> trace ->
                      code -> locset -> mem -> Prop :=
  | exec_Lgetstack:
      forall f sp sl r b rs m,
      exec_instr f sp (Lgetstack sl r :: b) rs m
                   E0 b (Locmap.set (R r) (rs (S sl)) rs) m
  | exec_Lsetstack:
      forall f sp r sl b rs m,
      exec_instr f sp (Lsetstack r sl :: b) rs m
                   E0 b (Locmap.set (S sl) (rs (R r)) rs) m
  | exec_Lop:
      forall f sp op args res b rs m v,
      eval_operation ge sp op (reglist args rs) = Some v ->
      exec_instr f sp (Lop op args res :: b) rs m
                   E0 b (Locmap.set (R res) v rs) m
  | exec_Lload:
      forall f sp chunk addr args dst b rs m a v,
      eval_addressing ge sp addr (reglist args rs) = Some a ->
      loadv chunk m a = Some v ->
      exec_instr f sp (Lload chunk addr args dst :: b) rs m
                   E0 b (Locmap.set (R dst) v rs) m
  | exec_Lstore:
      forall f sp chunk addr args src b rs m m' a,
      eval_addressing ge sp addr (reglist args rs) = Some a ->
      storev chunk m a (rs (R src)) = Some m' ->
      exec_instr f sp (Lstore chunk addr args src :: b) rs m
                   E0 b rs m'
  | exec_Lcall:
      forall f sp sig ros b rs m t f' rs' m',
      find_function ros rs = Some f' ->
      sig = funsig f' ->
      exec_function f' rs m t rs' m' ->
      exec_instr f sp (Lcall sig ros :: b) rs m
                    t b (return_regs rs rs') m'
  | exec_Lalloc:
      forall f sp b rs m sz m' blk,
      rs (R Conventions.loc_alloc_argument) = Vint sz ->
      Mem.alloc m 0 (Int.signed sz) = (m', blk) ->
      exec_instr f sp (Lalloc :: b) rs m
                   E0 b (Locmap.set (R Conventions.loc_alloc_result) 
                                    (Vptr blk Int.zero) rs) m'
  | exec_Llabel:
      forall f sp lbl b rs m,
      exec_instr f sp (Llabel lbl :: b) rs m
                   E0 b rs m
  | exec_Lgoto:
      forall f sp lbl b rs m b',
      find_label lbl f.(fn_code) = Some b' ->
      exec_instr f sp (Lgoto lbl :: b) rs m
                   E0 b' rs m
  | exec_Lcond_true:
      forall f sp cond args lbl b rs m b',
      eval_condition cond (reglist args rs) = Some true ->
      find_label lbl f.(fn_code) = Some b' ->
      exec_instr f sp (Lcond cond args lbl :: b) rs m
                   E0 b' rs m
  | exec_Lcond_false:
      forall f sp cond args lbl b rs m,
      eval_condition cond (reglist args rs) = Some false ->
      exec_instr f sp (Lcond cond args lbl :: b) rs m
                   E0 b rs m

with exec_instrs: function -> val ->
                  code -> locset -> mem -> trace ->
                  code -> locset -> mem -> Prop :=
  | exec_refl:
      forall f sp b rs m,
      exec_instrs f sp b rs m E0 b rs m
  | exec_one:
      forall f sp b1 rs1 m1 t b2 rs2 m2,
      exec_instr f sp b1 rs1 m1 t b2 rs2 m2 ->
      exec_instrs f sp b1 rs1 m1 t b2 rs2 m2
  | exec_trans:
      forall f sp b1 rs1 m1 t1 b2 rs2 m2 t2 b3 rs3 m3 t,
      exec_instrs f sp b1 rs1 m1 t1 b2 rs2 m2 ->
      exec_instrs f sp b2 rs2 m2 t2 b3 rs3 m3 ->
      t = t1 ** t2 ->
      exec_instrs f sp b1 rs1 m1 t b3 rs3 m3

with exec_function: fundef -> locset -> mem -> trace -> locset -> mem -> Prop :=
  | exec_funct_internal:
      forall f rs m t m1 stk rs2 m2 b,
      alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      exec_instrs f (Vptr stk Int.zero)
                  f.(fn_code) (call_regs rs) m1
                t (Lreturn :: b) rs2 m2 ->
      exec_function (Internal f) rs m t rs2 (free m2 stk)
  | exec_funct_external:
      forall ef args res rs1 rs2 m t,
      event_match ef args t res ->
      args = List.map rs1 (Conventions.loc_arguments ef.(ef_sig)) ->
      rs2 = Locmap.set (R (Conventions.loc_result ef.(ef_sig))) res rs1 ->
      exec_function (External ef) rs1 m t rs2 m.

Scheme exec_instr_ind3 := Minimality for exec_instr Sort Prop
  with exec_instrs_ind3 := Minimality for exec_instrs Sort Prop
  with exec_function_ind3 := Minimality for exec_function Sort Prop.

End RELSEM.

Definition exec_program (p: program) (t: trace) (r: val) : Prop :=
  let ge := Genv.globalenv p in
  let m0 := Genv.init_mem p in
  exists b, exists f, exists rs, exists m,
  Genv.find_symbol ge p.(prog_main) = Some b /\
  Genv.find_funct_ptr ge b = Some f /\
  funsig f = mksignature nil (Some Tint) /\
  exec_function ge f (Locmap.init Vundef) m0 t rs m /\
  rs (R (Conventions.loc_result (funsig f))) = r.

