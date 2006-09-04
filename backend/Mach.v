(** The Mach intermediate language: abstract syntax and semantics.

  Mach is the last intermediate language before generation of assembly
  code.
*)

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
Require Conventions.

(** * Abstract syntax *)

(** Like Linear, the Mach language is organized as lists of instructions
  operating over machine registers, with default fall-through behaviour
  and explicit labels and branch instructions.  

  The main difference with Linear lies in the instructions used to
  access the activation record.  Mach has three such instructions:
  [Mgetstack] and [Msetstack] to read and write within the activation
  record for the current function, at a given word offset and with a
  given type; and [Mgetparam], to read within the activation record of
  the caller.

  These instructions implement a more concrete view of the activation
  record than the the [Bgetstack] and [Bsetstack] instructions of
  Linear: actual offsets are used instead of abstract stack slots; the
  distinction between the caller's frame and the callee's frame is
  made explicit. *)

Definition label := positive.

Inductive instruction: Set :=
  | Mgetstack: int -> typ -> mreg -> instruction
  | Msetstack: mreg -> int -> typ -> instruction
  | Mgetparam: int -> typ -> mreg -> instruction
  | Mop: operation -> list mreg -> mreg -> instruction
  | Mload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Mstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Mcall: signature -> mreg + ident -> instruction
  | Malloc: instruction
  | Mlabel: label -> instruction
  | Mgoto: label -> instruction
  | Mcond: condition -> list mreg -> label -> instruction
  | Mreturn: instruction.

Definition code := list instruction.

Record function: Set := mkfunction
  { fn_sig: signature;
    fn_code: code;
    fn_stacksize: Z;
    fn_framesize: Z }.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => f.(fn_sig)
  | External ef => ef.(ef_sig)
  end.

Definition genv := Genv.t fundef.

(** * Dynamic semantics *)

Module RegEq.
  Definition t := mreg.
  Definition eq := mreg_eq.
End RegEq.

Module Regmap := EMap(RegEq).

Definition regset := Regmap.t val.

Notation "a ## b" := (List.map a b) (at level 1).
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level).

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Mlabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Mlabel lbl else instr <> Mlabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
  end.

(** The three stack-related Mach instructions are interpreted as
  memory accesses relative to the stack pointer.  More precisely:
- [Mgetstack ofs ty r] is a memory load at offset [ofs * 4] relative
  to the stack pointer.
- [Msetstack r ofs ty] is a memory store at offset [ofs * 4] relative
  to the stack pointer.
- [Mgetparam ofs ty r] is a memory load at offset [ofs * 4]
  relative to the pointer found at offset 0 from the stack pointer.
  The semantics maintain a linked structure of activation records,
  with the current record containing a pointer to the record of the
  caller function at offset 0. *)

Definition chunk_of_type (ty: typ) :=
  match ty with Tint => Mint32 | Tfloat => Mfloat64 end.

Definition load_stack (m: mem) (sp: val) (ty: typ) (ofs: int) :=
  Mem.loadv (chunk_of_type ty) m (Val.add sp (Vint ofs)).

Definition store_stack (m: mem) (sp: val) (ty: typ) (ofs: int) (v: val) :=
  Mem.storev (chunk_of_type ty) m (Val.add sp (Vint ofs)) v.

Definition align_16_top (lo hi: Z) :=
  Zmax 0 (((hi - lo + 15) / 16) * 16 + lo).

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

(** [exec_instr ge f sp c rs m c' rs' m'] reflects the execution of
  the first instruction in the current instruction sequence [c].  
  [c'] is the current instruction sequence after this execution.
  [rs] and [rs'] map machine registers to values, respectively
  before and after instruction execution.  [m] and [m'] are the
  memory states before and after. *)

Inductive exec_instr:
      function -> val ->
      code -> regset -> mem -> trace ->
      code -> regset -> mem -> Prop :=
  | exec_Mlabel:
      forall f sp lbl c rs m,
      exec_instr f sp
                 (Mlabel lbl :: c) rs m
              E0 c rs m
  | exec_Mgetstack:
      forall f sp ofs ty dst c rs m v,
      load_stack m sp ty ofs = Some v ->
      exec_instr f sp
                 (Mgetstack ofs ty dst :: c) rs m
              E0 c (rs#dst <- v) m
  | exec_Msetstack:
      forall f sp src ofs ty c rs m m',
      store_stack m sp ty ofs (rs src) = Some m' ->
      exec_instr f sp
                 (Msetstack src ofs ty :: c) rs m
              E0 c rs m'
  | exec_Mgetparam:
      forall f sp parent ofs ty dst c rs m v,
      load_stack m sp Tint (Int.repr 0) = Some parent ->
      load_stack m parent ty ofs = Some v ->
      exec_instr f sp
                 (Mgetparam ofs ty dst :: c) rs m
              E0 c (rs#dst <- v) m
  | exec_Mop:
      forall f sp op args res c rs m v,
      eval_operation ge sp op rs##args = Some v ->
      exec_instr f sp
                 (Mop op args res :: c) rs m
              E0 c (rs#res <- v) m
  | exec_Mload:
      forall f sp chunk addr args dst c rs m a v,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      exec_instr f sp 
                 (Mload chunk addr args dst :: c) rs m
              E0 c (rs#dst <- v) m
  | exec_Mstore:
      forall f sp chunk addr args src c rs m m' a,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      exec_instr f sp
                 (Mstore chunk addr args src :: c) rs m
              E0 c rs m'
  | exec_Mcall:
      forall f sp sig ros c rs m f' t rs' m',
      find_function ros rs = Some f' ->
      exec_function f' sp rs m t rs' m' ->
      exec_instr f sp
                 (Mcall sig ros :: c) rs m
               t c rs' m'
  | exec_Malloc:
      forall f sp c rs m sz m' blk,
      rs (Conventions.loc_alloc_argument) = Vint sz ->
      Mem.alloc m 0 (Int.signed sz) = (m', blk) ->
      exec_instr f sp 
                 (Malloc :: c) rs m
              E0 c (rs#Conventions.loc_alloc_result <- 
                                              (Vptr blk Int.zero)) m'
  | exec_Mgoto:
      forall f sp lbl c rs m c',
      find_label lbl f.(fn_code) = Some c' ->
      exec_instr f sp
                 (Mgoto lbl :: c) rs m
              E0 c' rs m
  | exec_Mcond_true:
      forall f sp cond args lbl c rs m c',
      eval_condition cond rs##args = Some true ->
      find_label lbl f.(fn_code) = Some c' ->
      exec_instr f sp
                 (Mcond cond args lbl :: c) rs m
              E0 c' rs m
  | exec_Mcond_false:
      forall f sp cond args lbl c rs m,
      eval_condition cond rs##args = Some false ->
      exec_instr f sp
                 (Mcond cond args lbl :: c) rs m
              E0 c rs m

with exec_instrs:
      function -> val ->
      code -> regset -> mem -> trace ->
      code -> regset -> mem -> Prop :=
  | exec_refl:
      forall f sp c rs m,
      exec_instrs f sp  c rs m E0 c rs m
  | exec_one:
      forall f sp c rs m t c' rs' m',
      exec_instr f sp c rs m t c' rs' m' ->
      exec_instrs f sp c rs m t c' rs' m'
  | exec_trans:
      forall f sp c1 rs1 m1 t1 c2 rs2 m2 t2 c3 rs3 m3 t3,
      exec_instrs f sp  c1 rs1 m1 t1 c2 rs2 m2 ->
      exec_instrs f sp  c2 rs2 m2 t2 c3 rs3 m3 ->
      t3 = t1 ** t2 ->
      exec_instrs f sp  c1 rs1 m1 t3 c3 rs3 m3

(** In addition to reserving the word at offset 0 in the activation 
  record for maintaining the linking of activation records,
  we need to reserve the word at offset 4 to store the return address
  into the caller.  However, the return address (a pointer within
  the code of the caller) is not precisely known at this point:
  it will be determined only after the final translation to PowerPC
  assembly code.  Therefore, we simply reserve that word in the strongest
  sense of the word ``reserve'': we make sure that whatever pointer
  is stored there at function entry keeps the same value until the
  final return instruction, and that the return value and final memory
  state are the same regardless of the return address.  
  This is captured in the evaluation rule [exec_function]
  that quantifies universally over all possible values of the return
  address, and pass this value to [exec_function_body].  In other
  terms, the inference rule [exec_function] has an infinity of
  premises, one for each possible return address.  Such infinitely
  branching inference rules are uncommon in operational semantics,
  but cause no difficulties in Coq. *)

with exec_function_body:
      function -> val -> val ->
      regset -> mem -> trace -> regset -> mem -> Prop :=
  | exec_funct_body:
      forall f parent ra rs m t rs' m1 m2 m3 m4 stk c,
      Mem.alloc m (- f.(fn_framesize))
                  (align_16_top (- f.(fn_framesize)) f.(fn_stacksize))
                                                        = (m1, stk) ->
      let sp := Vptr stk (Int.repr (-f.(fn_framesize))) in
      store_stack m1 sp Tint (Int.repr 0) parent = Some m2 ->
      store_stack m2 sp Tint (Int.repr 4) ra = Some m3 ->
      exec_instrs f sp
                  f.(fn_code) rs m3
                t (Mreturn :: c) rs' m4 ->
      load_stack m4 sp Tint (Int.repr 0) = Some parent ->
      load_stack m4 sp Tint (Int.repr 4) = Some ra ->
      exec_function_body f parent ra rs m t rs' (Mem.free m4 stk)

with exec_function:
      fundef -> val -> regset -> mem -> trace -> regset -> mem -> Prop :=
  | exec_funct_internal:
      forall f parent rs m t rs' m',
      (forall ra,
         Val.has_type ra Tint ->
         exec_function_body f parent ra rs m t rs' m') ->
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

End RELSEM.

Definition exec_program (p: program) (t: trace) (r: val) : Prop :=
  let ge := Genv.globalenv p in
  let m0 := Genv.init_mem p in
  exists b, exists f, exists rs, exists m,
  Genv.find_symbol ge p.(prog_main) = Some b /\
  Genv.find_funct_ptr ge b = Some f /\
  exec_function ge f (Vptr Mem.nullptr Int.zero) (Regmap.init Vundef) m0
                     t rs m /\
  rs R3 = r.

