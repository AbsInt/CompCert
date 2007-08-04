(** Correctness proof for PPC generation: auxiliary results. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Mem.
Require Import Globalenvs.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Machconcr.
Require Import Machtyping.
Require Import PPC.
Require Import PPCgen.
Require Conventions.

(** * Properties of low half/high half decomposition *)

Lemma high_half_signed_zero:
  forall v, Val.add (high_half_signed v) Vzero = high_half_signed v.
Proof.
  intros. generalize (high_half_signed_type v).
  rewrite Val.add_commut. 
  case (high_half_signed v); simpl; intros; try contradiction.
  auto. 
  rewrite Int.add_commut; rewrite Int.add_zero; auto. 
  rewrite Int.add_zero; auto. 
Qed.

Lemma high_half_unsigned_zero:
  forall v, Val.add (high_half_unsigned v) Vzero = high_half_unsigned v.
Proof.
  intros. generalize (high_half_unsigned_type v).
  rewrite Val.add_commut. 
  case (high_half_unsigned v); simpl; intros; try contradiction.
  auto. 
  rewrite Int.add_commut; rewrite Int.add_zero; auto. 
  rewrite Int.add_zero; auto. 
Qed.

Lemma low_high_u:
  forall n, Int.or (Int.shl (high_u n) (Int.repr 16)) (low_u n) = n.
Proof.
  intros. unfold high_u, low_u.
  rewrite Int.shl_rolm. rewrite Int.shru_rolm. 
  rewrite Int.rolm_rolm. 
  change (Int.modu (Int.add (Int.sub (Int.repr (Z_of_nat wordsize)) (Int.repr 16))
                            (Int.repr 16))
                   (Int.repr (Z_of_nat wordsize)))
    with (Int.zero).
  rewrite Int.rolm_zero. rewrite <- Int.and_or_distrib.
  exact (Int.and_mone n).
  reflexivity. reflexivity.
Qed.

Lemma low_high_u_xor:
  forall n, Int.xor (Int.shl (high_u n) (Int.repr 16)) (low_u n) = n.
Proof.
  intros. unfold high_u, low_u.
  rewrite Int.shl_rolm. rewrite Int.shru_rolm. 
  rewrite Int.rolm_rolm. 
  change (Int.modu (Int.add (Int.sub (Int.repr (Z_of_nat wordsize)) (Int.repr 16))
                            (Int.repr 16))
                   (Int.repr (Z_of_nat wordsize)))
    with (Int.zero).
  rewrite Int.rolm_zero. rewrite <- Int.and_xor_distrib.
  exact (Int.and_mone n).
  reflexivity. reflexivity.
Qed.

Lemma low_high_s:
  forall n, Int.add (Int.shl (high_s n) (Int.repr 16)) (low_s n) = n.
Proof.
  intros. rewrite Int.shl_mul_two_p. 
  unfold high_s. 
  rewrite <- (Int.divu_pow2 (Int.sub n (low_s n)) (Int.repr 65536) (Int.repr 16)).
  change (two_p (Int.unsigned (Int.repr 16))) with 65536.

  assert (forall x y, y > 0 -> (x - x mod y) mod y = 0).
  intros. apply Zmod_unique with (x / y). 
  generalize (Z_div_mod_eq x y H). intro. rewrite Zmult_comm. omega.
  omega.

  assert (Int.modu (Int.sub n (low_s n)) (Int.repr 65536) = Int.zero).
  unfold Int.modu, Int.zero. decEq. 
  change (Int.unsigned (Int.repr 65536)) with 65536.
  unfold Int.sub. 
  assert (forall a b, Int.eqm a b -> b mod 65536 = 0 -> a mod 65536 = 0).
  intros a b [k EQ] H1. rewrite EQ. 
  change modulus with (65536 * 65536). 
  rewrite Zmult_assoc. rewrite Zplus_comm. rewrite Z_mod_plus. auto.
  omega.
  eapply H0. apply Int.eqm_sym. apply Int.eqm_unsigned_repr. 
  unfold low_s. unfold Int.cast16signed. 
  set (N := Int.unsigned n).
  case (zlt (N mod 65536) 32768); intro.
  apply H0 with (N - N mod 65536). auto with ints.
  apply H. omega.
  apply H0 with (N - (N mod 65536 - 65536)). auto with ints.
  replace (N - (N mod 65536 - 65536))
     with ((N - N mod 65536) + 1 * 65536).
  rewrite Z_mod_plus. apply H. omega. omega. ring. 

  assert (Int.repr 65536 <> Int.zero). compute. congruence. 
  generalize (Int.modu_divu_Euclid (Int.sub n (low_s n)) (Int.repr 65536) H1).
  rewrite H0. rewrite Int.add_zero. intro. rewrite <- H2. 
  rewrite Int.sub_add_opp. rewrite Int.add_assoc. 
  replace (Int.add (Int.neg (low_s n)) (low_s n)) with Int.zero.
  apply Int.add_zero. symmetry. rewrite Int.add_commut. 
  rewrite <- Int.sub_add_opp. apply Int.sub_idem.

  reflexivity.
Qed.

(** * Correspondence between Mach registers and PPC registers *)

Hint Extern 2 (_ <> _) => discriminate: ppcgen.

(** Mapping from Mach registers to PPC registers. *)

Definition preg_of (r: mreg) :=
  match mreg_type r with
  | Tint => IR (ireg_of r)
  | Tfloat => FR (freg_of r)
  end.

Lemma preg_of_injective:
  forall r1 r2, preg_of r1 = preg_of r2 -> r1 = r2.
Proof.
  destruct r1; destruct r2; simpl; intros; reflexivity || discriminate.
Qed.

(** Characterization of PPC registers that correspond to Mach registers. *)

Definition is_data_reg (r: preg) : Prop :=
  match r with
  | IR GPR2 => False
  | FR FPR13 => False
  | PC => False    | LR => False    | CTR => False
  | CR0_0 => False | CR0_1 => False | CR0_2 => False | CR0_3 => False
  | CARRY => False
  | _ => True
  end.

Lemma ireg_of_is_data_reg:
  forall (r: mreg), is_data_reg (ireg_of r).
Proof.
  destruct r; exact I.
Qed.

Lemma freg_of_is_data_reg:
  forall (r: mreg), is_data_reg (ireg_of r).
Proof.
  destruct r; exact I.
Qed.

Lemma preg_of_is_data_reg:
  forall (r: mreg), is_data_reg (preg_of r).
Proof.
  destruct r; exact I.
Qed.

Lemma ireg_of_not_GPR1:
  forall r, ireg_of r <> GPR1.
Proof.
  intro. case r; discriminate.
Qed.
Lemma ireg_of_not_GPR2:
  forall r, ireg_of r <> GPR2.
Proof.
  intro. case r; discriminate.
Qed.
Lemma freg_of_not_FPR13:
  forall r, freg_of r <> FPR13.
Proof.
  intro. case r; discriminate.
Qed.
Hint Resolve ireg_of_not_GPR1 ireg_of_not_GPR2 freg_of_not_FPR13: ppcgen.

Lemma preg_of_not:
  forall r1 r2, ~(is_data_reg r2) -> preg_of r1 <> r2.
Proof.
  intros; red; intro. subst r2. elim H. apply preg_of_is_data_reg.
Qed.
Hint Resolve preg_of_not: ppcgen.

Lemma preg_of_not_GPR1:
  forall r, preg_of r <> GPR1.
Proof.
  intro. case r; discriminate.
Qed.
Hint Resolve preg_of_not_GPR1: ppcgen.

(** Agreement between Mach register sets and PPC register sets. *)

Definition agree (ms: Mach.regset) (sp: val) (rs: PPC.regset) :=
  rs#GPR1 = sp /\ forall r: mreg, ms r = rs#(preg_of r).

Lemma preg_val:
  forall ms sp rs r,
  agree ms sp rs -> ms r = rs#(preg_of r).
Proof.
  intros. elim H. auto.
Qed.
  
Lemma ireg_val:
  forall ms sp rs r,
  agree ms sp rs ->
  mreg_type r = Tint ->
  ms r = rs#(ireg_of r).
Proof.
  intros. elim H; intros.
  generalize (H2 r). unfold preg_of. rewrite H0. auto.
Qed.

Lemma freg_val:
  forall ms sp rs r,
  agree ms sp rs ->
  mreg_type r = Tfloat ->
  ms r = rs#(freg_of r).
Proof.
  intros. elim H; intros.
  generalize (H2 r). unfold preg_of. rewrite H0. auto.
Qed.

Lemma sp_val:
  forall ms sp rs,
  agree ms sp rs ->
  sp = rs#GPR1.
Proof.
  intros. elim H; auto.
Qed.

Lemma agree_exten_1:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r, is_data_reg r -> rs'#r = rs#r) ->
  agree ms sp rs'.
Proof.
  unfold agree; intros. elim H; intros.
  split. rewrite H0. auto. exact I. 
  intros. rewrite H0. auto. apply preg_of_is_data_reg.
Qed.

Lemma agree_exten_2:
  forall ms sp rs rs',
  agree ms sp rs ->
  (forall r,
     r <> IR GPR2 -> r <> FR FPR13 ->
     r <> PC -> r <> LR -> r <> CTR ->
     r <> CR0_0 -> r <> CR0_1 -> r <> CR0_2 -> r <> CR0_3 ->
     r <> CARRY ->
     rs'#r = rs#r) ->
  agree ms sp rs'.
Proof.
  intros. apply agree_exten_1 with rs. auto.
  intros. apply H0; (red; intro; subst r; elim H1).
Qed.

(** Preservation of register agreement under various assignments. *)

Lemma agree_set_mreg:
  forall ms sp rs r v,
  agree ms sp rs ->
  agree (Regmap.set r v ms) sp (rs#(preg_of r) <- v).
Proof.
  unfold agree; intros. elim H; intros; clear H.
  split. rewrite Pregmap.gso. auto. apply sym_not_eq. apply preg_of_not_GPR1.
  intros. unfold Regmap.set. case (RegEq.eq r0 r); intro.
  subst r0. rewrite Pregmap.gss. auto.
  rewrite Pregmap.gso. auto. red; intro. 
  elim n. apply preg_of_injective; auto.
Qed.
Hint Resolve agree_set_mreg: ppcgen.

Lemma agree_set_mireg:
  forall ms sp rs r v,
  agree ms sp (rs#(preg_of r) <- v) ->
  mreg_type r = Tint ->
  agree ms sp (rs#(ireg_of r) <- v).
Proof.
  intros. unfold preg_of in H. rewrite H0 in H. auto.
Qed.
Hint Resolve agree_set_mireg: ppcgen.

Lemma agree_set_mfreg:
  forall ms sp rs r v,
  agree ms sp (rs#(preg_of r) <- v) ->
  mreg_type r = Tfloat ->
  agree ms sp (rs#(freg_of r) <- v).
Proof.
  intros. unfold preg_of in H. rewrite H0 in H. auto.
Qed.
Hint Resolve agree_set_mfreg: ppcgen.

Lemma agree_set_other:
  forall ms sp rs r v,
  agree ms sp rs ->
  ~(is_data_reg r) ->
  agree ms sp (rs#r <- v).
Proof.
  intros. apply agree_exten_1 with rs.
  auto. intros. apply Pregmap.gso. red; intro; subst r0; contradiction.
Qed.
Hint Resolve agree_set_other: ppcgen.

Lemma agree_nextinstr:
  forall ms sp rs,
  agree ms sp rs -> agree ms sp (nextinstr rs).
Proof.
  intros. unfold nextinstr. apply agree_set_other. auto. auto.
Qed.
Hint Resolve agree_nextinstr: ppcgen.

Lemma agree_set_mireg_twice:
  forall ms sp rs r v v',
  agree ms sp rs ->
  mreg_type r = Tint ->
  agree (Regmap.set r v ms) sp (rs #(ireg_of r) <- v' #(ireg_of r) <- v).
Proof.
  intros. replace (IR (ireg_of r)) with (preg_of r). elim H; intros.
  split. repeat (rewrite Pregmap.gso; auto with ppcgen).
  intros. case (mreg_eq r r0); intro.
  subst r0. rewrite Regmap.gss. rewrite Pregmap.gss. auto.
  assert (preg_of r <> preg_of r0). 
    red; intro. elim n. apply preg_of_injective. auto.
  rewrite Regmap.gso; auto.
  repeat (rewrite Pregmap.gso; auto).
  unfold preg_of. rewrite H0. auto.
Qed.
Hint Resolve agree_set_mireg_twice: ppcgen.

Lemma agree_set_twice_mireg:
  forall ms sp rs r v v',
  agree (Regmap.set r v' ms) sp rs ->
  mreg_type r = Tint ->
  agree (Regmap.set r v ms) sp (rs#(ireg_of r) <- v).
Proof.
  intros. elim H; intros.
  split. rewrite Pregmap.gso. auto. 
  generalize (ireg_of_not_GPR1 r); congruence.
  intros. generalize (H2 r0). 
  case (mreg_eq r0 r); intro.
  subst r0. repeat rewrite Regmap.gss. unfold preg_of; rewrite H0.
  rewrite Pregmap.gss. auto.
  repeat rewrite Regmap.gso; auto.
  rewrite Pregmap.gso. auto. 
  replace (IR (ireg_of r)) with (preg_of r).
  red; intros. elim n. apply preg_of_injective; auto.
  unfold preg_of. rewrite H0. auto.
Qed.
Hint Resolve agree_set_twice_mireg: ppcgen.

Lemma agree_set_commut:
  forall ms sp rs r1 r2 v1 v2,
  r1 <> r2 ->
  agree ms sp ((rs#r2 <- v2)#r1 <- v1) ->
  agree ms sp ((rs#r1 <- v1)#r2 <- v2).
Proof.
  intros. apply agree_exten_1 with ((rs#r2 <- v2)#r1 <- v1). auto.
  intros. 
  case (preg_eq r r1); intro.
  subst r1. rewrite Pregmap.gss. rewrite Pregmap.gso. rewrite Pregmap.gss.
  auto. auto.
  case (preg_eq r r2); intro.
  subst r2. rewrite Pregmap.gss. rewrite Pregmap.gso. rewrite Pregmap.gss.
  auto. auto.
  repeat (rewrite Pregmap.gso; auto). 
Qed. 
Hint Resolve agree_set_commut: ppcgen.

Lemma agree_nextinstr_commut:
  forall ms sp rs r v,
  agree ms sp (rs#r <- v) ->
  r <> PC ->
  agree ms sp ((nextinstr rs)#r <- v).
Proof.
  intros. unfold nextinstr. apply agree_set_commut. auto. 
  apply agree_set_other. auto. auto. 
Qed.
Hint Resolve agree_nextinstr_commut: ppcgen.

Lemma agree_set_mireg_exten:
  forall ms sp rs r v (rs': regset),
  agree ms sp rs ->
  mreg_type r = Tint ->
  rs'#(ireg_of r) = v ->
  (forall r', 
     r' <> IR GPR2 -> r' <> FR FPR13 ->
     r' <> PC -> r' <> LR -> r' <> CTR ->
     r' <> CR0_0 -> r' <> CR0_1 -> r' <> CR0_2 -> r' <> CR0_3 ->
     r' <> CARRY ->
     r' <> IR (ireg_of r) -> rs'#r' = rs#r') ->
  agree (Regmap.set r v ms) sp rs'.
Proof.
  intros. apply agree_exten_2 with (rs#(ireg_of r) <- v).
  auto with ppcgen.
  intros. unfold Pregmap.set. case (PregEq.eq r0 (ireg_of r)); intro.
  subst r0. auto. apply H2; auto.
Qed.

(** Useful properties of the PC and GPR0 registers. *)

Lemma nextinstr_inv:
  forall r rs, r <> PC -> (nextinstr rs)#r = rs#r.
Proof.
  intros. unfold nextinstr. apply Pregmap.gso. auto.
Qed.
Hint Resolve nextinstr_inv: ppcgen.

Lemma nextinstr_set_preg:
  forall rs m v,
  (nextinstr (rs#(preg_of m) <- v))#PC = Val.add rs#PC Vone.
Proof.
  intros. unfold nextinstr. rewrite Pregmap.gss. 
  rewrite Pregmap.gso. auto. apply sym_not_eq. auto with ppcgen.
Qed.
Hint Resolve nextinstr_set_preg: ppcgen.

Lemma gpr_or_zero_not_zero:
  forall rs r, r <> GPR0 -> gpr_or_zero rs r = rs#r.
Proof.
  intros. unfold gpr_or_zero. case (ireg_eq r GPR0); tauto.
Qed.
Lemma gpr_or_zero_zero:
  forall rs, gpr_or_zero rs GPR0 = Vzero.
Proof.
  intros. reflexivity.
Qed.
Hint Resolve gpr_or_zero_not_zero gpr_or_zero_zero: ppcgen.

(** Connection between Mach and PPC calling conventions for external
    functions. *)

Lemma loc_external_result_match:
  forall sg,
  PPC.loc_external_result sg = preg_of (Conventions.loc_result sg).
Proof.
  intros. destruct sg as [sargs sres]. 
  destruct sres. destruct t; reflexivity. reflexivity.
Qed.

Lemma extcall_args_match:
  forall ms m sp rs,
  agree ms sp rs ->
  forall tyl iregl fregl ofs args,
  (forall r, In r iregl -> mreg_type r = Tint) ->
  (forall r, In r fregl -> mreg_type r = Tfloat) ->
  Machconcr.extcall_args ms m sp (Conventions.loc_arguments_rec tyl iregl fregl ofs) args ->
  PPC.extcall_args rs m tyl (List.map ireg_of iregl) (List.map freg_of fregl) (4 * ofs) args.
Proof.
  induction tyl; intros.
  inversion H2; constructor.
  destruct a. 
  (* integer case *)
  destruct iregl as [ | ir1 irl]. 
  (* stack *)
  inversion H2; subst; clear H2. inversion H8; subst; clear H8.
  constructor. replace (rs GPR1) with sp. assumption. 
  eapply sp_val; eauto. 
  change (@nil ireg) with (ireg_of ## nil). 
  replace (4 * ofs + 4) with (4 * (ofs + 1)) by omega. 
  apply IHtyl; auto. 
  (* register *)
  inversion H2; subst; clear H2. inversion H8; subst; clear H8.
  simpl map. econstructor. eapply ireg_val; eauto.
  apply H0; simpl; auto. 
  replace (4 * ofs + 4) with (4 * (ofs + 1)) by omega. 
  apply IHtyl; auto. 
  intros; apply H0; simpl; auto.
  (* float case *)
  destruct fregl as [ | fr1 frl]. 
  (* stack *)
  inversion H2; subst; clear H2. inversion H8; subst; clear H8.
  constructor. replace (rs GPR1) with sp. assumption. 
  eapply sp_val; eauto. 
  change (@nil freg) with (freg_of ## nil). 
  replace (4 * ofs + 8) with (4 * (ofs + 2)) by omega. 
  apply IHtyl; auto. 
  (* register *)
  inversion H2; subst; clear H2. inversion H8; subst; clear H8.
  simpl map. econstructor. eapply freg_val; eauto.
  apply H1; simpl; auto. 
  replace (4 * ofs + 8) with (4 * (ofs + 2)) by omega. 
  rewrite list_map_drop2.
  apply IHtyl; auto. 
  intros; apply H0. apply list_drop2_incl. auto.
  intros; apply H1; simpl; auto.
Qed.

Ltac ElimOrEq :=
  match goal with
  |  |- (?x = ?y) \/ _ -> _ =>
       let H := fresh in
       (intro H; elim H; clear H;
        [intro H; rewrite <- H; clear H | ElimOrEq])
  |  |- False -> _ =>
       let H := fresh in (intro H; contradiction)
  end.

Lemma extcall_arguments_match:
  forall ms m sp rs sg args,
  agree ms sp rs ->
  Machconcr.extcall_arguments ms m sp sg args ->
  PPC.extcall_arguments rs m sg args.
Proof.
  unfold Machconcr.extcall_arguments, PPC.extcall_arguments; intros.
  change (extcall_args rs m sg.(sig_args)
    (List.map ireg_of Conventions.int_param_regs)
    (List.map freg_of Conventions.float_param_regs) (4 * 14) args).
  eapply extcall_args_match; eauto. 
  intro; simpl; ElimOrEq; reflexivity.  
  intro; simpl; ElimOrEq; reflexivity.  
Qed.

(** * Execution of straight-line code *)

Section STRAIGHTLINE.

Variable ge: genv.
Variable fn: code.

(** Straight-line code is composed of PPC instructions that execute
  in sequence (no branches, no function calls and returns).
  The following inductive predicate relates the machine states
  before and after executing a straight-line sequence of instructions.
  Instructions are taken from the first list instead of being fetched
  from memory. *)

Inductive exec_straight: code -> regset -> mem -> 
                         code -> regset -> mem -> Prop :=
  | exec_straight_one:
      forall i1 c rs1 m1 rs2 m2,
      exec_instr ge fn i1 rs1 m1 = OK rs2 m2 ->
      rs2#PC = Val.add rs1#PC Vone ->
      exec_straight (i1 :: c) rs1 m1 c rs2 m2
  | exec_straight_step:
      forall i c rs1 m1 rs2 m2 c' rs3 m3,
      exec_instr ge fn i rs1 m1 = OK rs2 m2 ->
      rs2#PC = Val.add rs1#PC Vone ->
      exec_straight c rs2 m2 c' rs3 m3 ->
      exec_straight (i :: c) rs1 m1 c' rs3 m3.

Lemma exec_straight_trans:
  forall c1 rs1 m1 c2 rs2 m2 c3 rs3 m3,
  exec_straight c1 rs1 m1 c2 rs2 m2 ->
  exec_straight c2 rs2 m2 c3 rs3 m3 ->
  exec_straight c1 rs1 m1 c3 rs3 m3.
Proof.
  induction 1; intros.
  apply exec_straight_step with rs2 m2; auto.
  apply exec_straight_step with rs2 m2; auto.
Qed.

Lemma exec_straight_two:
  forall i1 i2 c rs1 m1 rs2 m2 rs3 m3,
  exec_instr ge fn i1 rs1 m1 = OK rs2 m2 ->
  exec_instr ge fn i2 rs2 m2 = OK rs3 m3 ->
  rs2#PC = Val.add rs1#PC Vone ->
  rs3#PC = Val.add rs2#PC Vone ->
  exec_straight (i1 :: i2 :: c) rs1 m1 c rs3 m3.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  apply exec_straight_one; auto.
Qed.

Lemma exec_straight_three:
  forall i1 i2 i3 c rs1 m1 rs2 m2 rs3 m3 rs4 m4,
  exec_instr ge fn i1 rs1 m1 = OK rs2 m2 ->
  exec_instr ge fn i2 rs2 m2 = OK rs3 m3 ->
  exec_instr ge fn i3 rs3 m3 = OK rs4 m4 ->
  rs2#PC = Val.add rs1#PC Vone ->
  rs3#PC = Val.add rs2#PC Vone ->
  rs4#PC = Val.add rs3#PC Vone ->
  exec_straight (i1 :: i2 :: i3 :: c) rs1 m1 c rs4 m4.
Proof.
  intros. apply exec_straight_step with rs2 m2; auto.
  eapply exec_straight_two; eauto.
Qed.

(** * Correctness of PowerPC constructor functions *)

(** Properties of comparisons. *)

Lemma compare_float_spec:
  forall rs v1 v2,
  let rs1 := nextinstr (compare_float rs v1 v2) in
     rs1#CR0_0 = Val.cmpf Clt v1 v2
  /\ rs1#CR0_1 = Val.cmpf Cgt v1 v2
  /\ rs1#CR0_2 = Val.cmpf Ceq v1 v2
  /\ forall r', r' <> PC -> r' <> CR0_0 -> r' <> CR0_1 ->
       r' <> CR0_2 -> r' <> CR0_3 -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  intros. rewrite nextinstr_inv; auto.
  unfold compare_float. repeat (rewrite Pregmap.gso; auto).
Qed.

Lemma compare_sint_spec:
  forall rs v1 v2,
  let rs1 := nextinstr (compare_sint rs v1 v2) in
     rs1#CR0_0 = Val.cmp Clt v1 v2
  /\ rs1#CR0_1 = Val.cmp Cgt v1 v2
  /\ rs1#CR0_2 = Val.cmp Ceq v1 v2
  /\ forall r', r' <> PC -> r' <> CR0_0 -> r' <> CR0_1 ->
       r' <> CR0_2 -> r' <> CR0_3 -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  intros. rewrite nextinstr_inv; auto.
  unfold compare_sint. repeat (rewrite Pregmap.gso; auto).
Qed.

Lemma compare_uint_spec:
  forall rs v1 v2,
  let rs1 := nextinstr (compare_uint rs v1 v2) in
     rs1#CR0_0 = Val.cmpu Clt v1 v2
  /\ rs1#CR0_1 = Val.cmpu Cgt v1 v2
  /\ rs1#CR0_2 = Val.cmpu Ceq v1 v2
  /\ forall r', r' <> PC -> r' <> CR0_0 -> r' <> CR0_1 ->
       r' <> CR0_2 -> r' <> CR0_3 -> rs1#r' = rs#r'.
Proof.
  intros. unfold rs1.
  split. reflexivity.
  split. reflexivity.
  split. reflexivity.
  intros. rewrite nextinstr_inv; auto.
  unfold compare_uint. repeat (rewrite Pregmap.gso; auto).
Qed.

(** Loading a constant. *)

Lemma loadimm_correct:
  forall r n k rs m,
  exists rs',
     exec_straight (loadimm r n k) rs m  k rs' m
  /\ rs'#r = Vint n
  /\ forall r': preg, r' <> r -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold loadimm.
  case (Int.eq (high_s n) Int.zero).
  (* addi *)
  exists (nextinstr (rs#r <- (Vint n))).
  split. apply exec_straight_one. 
  simpl. rewrite Int.add_commut. rewrite Int.add_zero. reflexivity.
  reflexivity. 
  split. rewrite nextinstr_inv; auto with ppcgen.
   apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* addis *)
  generalize (Int.eq_spec (low_s n) Int.zero); case (Int.eq (low_s n) Int.zero); intro.
  exists (nextinstr (rs#r <- (Vint n))).
  split. apply exec_straight_one. 
  simpl. rewrite Int.add_commut. 
  rewrite <- H. rewrite low_high_s. reflexivity.
  reflexivity. 
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* addis + ori *)
  pose (rs1 := nextinstr (rs#r <- (Vint (Int.shl (high_u n) (Int.repr 16))))).
  exists (nextinstr (rs1#r <- (Vint n))).
  split. eapply exec_straight_two. 
  simpl. rewrite Int.add_commut. rewrite Int.add_zero. reflexivity.
  simpl. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  unfold Val.or. rewrite low_high_u. reflexivity.
  reflexivity. reflexivity.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
  unfold rs1. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
Qed.

(** Add integer immediate. *)

Lemma addimm_1_correct:
  forall r1 r2 n k rs m,
  r1 <> GPR0 ->
  r2 <> GPR0 ->
  exists rs',
     exec_straight (addimm_1 r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.add rs#r2 (Vint n)
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold addimm_1.
  (* addi *)
  case (Int.eq (high_s n) Int.zero).
  exists (nextinstr (rs#r1 <- (Val.add rs#r2 (Vint n)))).
  split. apply exec_straight_one. 
  simpl. rewrite gpr_or_zero_not_zero; auto.
  reflexivity. 
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto. 
  (* addis *)
  generalize (Int.eq_spec (low_s n) Int.zero); case (Int.eq (low_s n) Int.zero); intro.
  exists (nextinstr (rs#r1 <- (Val.add rs#r2 (Vint n)))).
  split. apply exec_straight_one.
  simpl. rewrite gpr_or_zero_not_zero; auto.
  generalize (low_high_s n). rewrite H1. rewrite Int.add_zero. intro.
  rewrite H2. auto.
  reflexivity.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* addis + addi *)
  pose (rs1 := nextinstr (rs#r1 <- (Val.add rs#r2 (Vint (Int.shl (high_s n) (Int.repr 16)))))).
  exists (nextinstr (rs1#r1 <- (Val.add rs#r2 (Vint n)))).
  split. apply exec_straight_two with rs1 m.
  simpl. rewrite gpr_or_zero_not_zero; auto. 
  simpl. rewrite gpr_or_zero_not_zero; auto.
  unfold rs1 at 1. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss.
  rewrite Val.add_assoc. simpl. rewrite low_high_s. auto.
  reflexivity. reflexivity. 
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss. 
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
  unfold rs1. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
Qed. 

Lemma addimm_2_correct:
  forall r1 r2 n k rs m,
  r2 <> GPR2 ->
  exists rs',
     exec_straight (addimm_2 r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.add rs#r2 (Vint n)
  /\ forall r': preg, r' <> r1 -> r' <> GPR2 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold addimm_2.
  generalize (loadimm_correct GPR2 n (Padd r1 r2 GPR2 :: k) rs m).
  intros [rs1 [EX [RES OTHER]]].
  exists (nextinstr (rs1#r1 <- (Val.add rs#r2 (Vint n)))).
  split. eapply exec_straight_trans. eexact EX. 
  apply exec_straight_one. simpl. rewrite RES. rewrite OTHER.
  auto. congruence. discriminate.
  reflexivity. 
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
Qed.

Lemma addimm_correct:
  forall r1 r2 n k rs m,
  r2 <> GPR2 ->
  exists rs',
     exec_straight (addimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = Val.add rs#r2 (Vint n)
  /\ forall r': preg, r' <> r1 -> r' <> GPR2 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold addimm.
  case (ireg_eq r1 GPR0); intro.
  apply addimm_2_correct; auto.
  case (ireg_eq r2 GPR0); intro.
  apply addimm_2_correct; auto.
  generalize (addimm_1_correct r1 r2 n k rs m n0 n1).  
  intros [rs' [EX [RES OTH]]]. exists rs'. intuition. 
Qed.

(** And integer immediate. *)

Lemma andimm_correct:
  forall r1 r2 n k (rs : regset) m,
  r2 <> GPR2 ->
  let v := Val.and rs#r2 (Vint n) in
  exists rs',
     exec_straight (andimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = v
  /\ rs'#CR0_2 = Val.cmp Ceq v Vzero
  /\ forall r': preg,
       r' <> r1 -> r' <> GPR2 -> r' <> PC ->
       r' <> CR0_0 -> r' <> CR0_1 -> r' <> CR0_2 -> r' <> CR0_3 ->
       rs'#r' = rs#r'.
Proof.
  intros. unfold andimm.
  case (Int.eq (high_u n) Int.zero).
  (* andi *)
  exists (nextinstr (compare_sint (rs#r1 <- v) v Vzero)).
  generalize (compare_sint_spec (rs#r1 <- v) v Vzero).
  intros [A [B [C D]]].
  split. apply exec_straight_one. reflexivity. reflexivity.
  split. rewrite D; try discriminate. apply Pregmap.gss. 
  split. auto.
  intros. rewrite D; auto. apply Pregmap.gso; auto.
  (* andis *)
  generalize (Int.eq_spec (low_u n) Int.zero);
  case (Int.eq (low_u n) Int.zero); intro.
  exists (nextinstr (compare_sint (rs#r1 <- v) v Vzero)).
  generalize (compare_sint_spec (rs#r1 <- v) v Vzero).
  intros [A [B [C D]]].
  split. apply exec_straight_one. simpl.
  generalize (low_high_u n). rewrite H0. rewrite Int.or_zero. 
  intro. rewrite H1. reflexivity. reflexivity.
  split. rewrite D; try discriminate. apply Pregmap.gss. 
  split. auto.
  intros. rewrite D; auto. apply Pregmap.gso; auto.
  (* loadimm + and *)
  generalize (loadimm_correct GPR2 n (Pand_ r1 r2 GPR2 :: k) rs m).
  intros [rs1 [EX1 [RES1 OTHER1]]].
  exists (nextinstr (compare_sint (rs1#r1 <- v) v Vzero)).
  generalize (compare_sint_spec (rs1#r1 <- v) v Vzero).
  intros [A [B [C D]]].
  split. eapply exec_straight_trans. eexact EX1. 
  apply exec_straight_one. simpl. rewrite RES1. 
  rewrite (OTHER1 r2). reflexivity. congruence. congruence.
  reflexivity. 
  split. rewrite D; try discriminate. apply Pregmap.gss. 
  split. auto.
  intros. rewrite D; auto. rewrite Pregmap.gso; auto.
Qed.

(** Or integer immediate. *)

Lemma orimm_correct:
  forall r1 (r2: ireg) n k (rs : regset) m,
  let v := Val.or rs#r2 (Vint n) in
  exists rs',
     exec_straight (orimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = v
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold orimm.
  case (Int.eq (high_u n) Int.zero).
  (* ori *)
  exists (nextinstr (rs#r1 <- v)).
  split. apply exec_straight_one. reflexivity. reflexivity.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* oris *)
  generalize (Int.eq_spec (low_u n) Int.zero);
  case (Int.eq (low_u n) Int.zero); intro.
  exists (nextinstr (rs#r1 <- v)).
  split. apply exec_straight_one. simpl.
  generalize (low_high_u n). rewrite H. rewrite Int.or_zero. 
  intro. rewrite H0. reflexivity. reflexivity.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* oris + ori *)
  pose (rs1 := nextinstr (rs#r1 <- (Val.or rs#r2 (Vint (Int.shl (high_u n) (Int.repr 16)))))).
  exists (nextinstr (rs1#r1 <- v)).
  split. apply exec_straight_two with rs1 m.
  reflexivity. simpl. unfold rs1 at 1. 
  rewrite nextinstr_inv; auto with ppcgen.
  rewrite Pregmap.gss. rewrite Val.or_assoc. simpl. 
  rewrite low_high_u. reflexivity. reflexivity. reflexivity. 
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
  unfold rs1. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
Qed.

(** Xor integer immediate. *)

Lemma xorimm_correct:
  forall r1 (r2: ireg) n k (rs : regset) m,
  let v := Val.xor rs#r2 (Vint n) in
  exists rs',
     exec_straight (xorimm r1 r2 n k) rs m  k rs' m
  /\ rs'#r1 = v
  /\ forall r': preg, r' <> r1 -> r' <> PC -> rs'#r' = rs#r'.
Proof.
  intros. unfold xorimm.
  case (Int.eq (high_u n) Int.zero).
  (* xori *)
  exists (nextinstr (rs#r1 <- v)).
  split. apply exec_straight_one. reflexivity. reflexivity.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* xoris *)
  generalize (Int.eq_spec (low_u n) Int.zero);
  case (Int.eq (low_u n) Int.zero); intro.
  exists (nextinstr (rs#r1 <- v)).
  split. apply exec_straight_one. simpl.
  generalize (low_high_u_xor n). rewrite H. rewrite Int.xor_zero. 
  intro. rewrite H0. reflexivity. reflexivity.
  split. rewrite nextinstr_inv; auto with ppcgen. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* xoris + xori *)
  pose (rs1 := nextinstr (rs#r1 <- (Val.xor rs#r2 (Vint (Int.shl (high_u n) (Int.repr 16)))))).
  exists (nextinstr (rs1#r1 <- v)).
  split. apply exec_straight_two with rs1 m.
  reflexivity. simpl. unfold rs1 at 1. 
  rewrite nextinstr_inv; try discriminate. 
  rewrite Pregmap.gss. rewrite Val.xor_assoc. simpl. 
  rewrite low_high_u_xor. reflexivity. reflexivity. reflexivity. 
  split. rewrite nextinstr_inv; auto with ppcgen.
  apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
  unfold rs1. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
Qed.

(** Indexed memory loads. *)

Lemma loadind_aux_correct:
  forall (base: ireg) ofs ty dst (rs: regset) m v,
  Mem.loadv (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) = Some v ->
  mreg_type dst = ty ->
  base <> GPR0 ->
  exec_instr ge fn (loadind_aux base ofs ty dst) rs m =
    OK (nextinstr (rs#(preg_of dst) <- v)) m.
Proof.
  intros. unfold loadind_aux. unfold preg_of. rewrite H0. destruct ty.
  simpl. unfold load1. rewrite gpr_or_zero_not_zero; auto.
  unfold const_low. simpl in H. rewrite H. auto.
  simpl. unfold load1. rewrite gpr_or_zero_not_zero; auto.
  unfold const_low. simpl in H. rewrite H. auto.
Qed.

Lemma loadind_correct:
  forall (base: ireg) ofs ty dst k (rs: regset) m v,
  Mem.loadv (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) = Some v ->
  mreg_type dst = ty ->
  base <> GPR0 ->
  exists rs',
     exec_straight (loadind base ofs ty dst k) rs m k rs' m
  /\ rs'#(preg_of dst) = v
  /\ forall r, r <> PC -> r <> GPR2 -> r <> preg_of dst -> rs'#r = rs#r.
Proof.
  intros. unfold loadind.
  assert (preg_of dst <> PC).
    unfold preg_of. case (mreg_type dst); discriminate.
  (* short offset *)
  case (Int.eq (high_s ofs) Int.zero).
  exists (nextinstr (rs#(preg_of dst) <- v)).
  split. apply exec_straight_one. apply loadind_aux_correct; auto. 
  unfold nextinstr. rewrite Pregmap.gss. rewrite Pregmap.gso. auto. auto.
  split. rewrite nextinstr_inv; auto. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. apply Pregmap.gso; auto.
  (* long offset *)
  pose (rs1 := nextinstr (rs#GPR2 <- (Val.add rs#base (Vint (Int.shl (high_s ofs) (Int.repr 16)))))).
  exists (nextinstr (rs1#(preg_of dst) <- v)).
  split. apply exec_straight_two with rs1 m.
  simpl. rewrite gpr_or_zero_not_zero; auto. 
  apply loadind_aux_correct. 
  unfold rs1. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  rewrite Val.add_assoc. simpl. rewrite low_high_s. assumption.
  auto. discriminate. reflexivity. 
  unfold nextinstr. rewrite Pregmap.gss. rewrite Pregmap.gso. auto. auto.
  split. rewrite nextinstr_inv; auto. apply Pregmap.gss.
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
  unfold rs1. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
Qed.

(** Indexed memory stores. *)

Lemma storeind_aux_correct:
  forall (base: ireg) ofs ty src (rs: regset) m m',
  Mem.storev (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) (rs#(preg_of src)) = Some m' ->
  mreg_type src = ty ->
  base <> GPR0 ->
  exec_instr ge fn (storeind_aux src base ofs ty) rs m =
    OK (nextinstr rs) m'.
Proof.
  intros. unfold storeind_aux. unfold preg_of in H. rewrite H0 in H. destruct ty.
  simpl. unfold store1. rewrite gpr_or_zero_not_zero; auto.
  unfold const_low. simpl in H. rewrite H. auto.
  simpl. unfold store1. rewrite gpr_or_zero_not_zero; auto.
  unfold const_low. simpl in H. rewrite H. auto.
Qed.

Lemma storeind_correct:
  forall (base: ireg) ofs ty src k (rs: regset) m m',
  Mem.storev (chunk_of_type ty) m (Val.add rs#base (Vint ofs)) (rs#(preg_of src)) = Some m' ->
  mreg_type src = ty ->
  base <> GPR0 ->
  exists rs',
     exec_straight (storeind src base ofs ty k) rs m k rs' m'
  /\ forall r, r <> PC -> r <> GPR2 -> rs'#r = rs#r.
Proof.
  intros. unfold storeind.
  (* short offset *)
  case (Int.eq (high_s ofs) Int.zero).
  exists (nextinstr rs).
  split. apply exec_straight_one. apply storeind_aux_correct; auto. 
  reflexivity. 
  intros. rewrite nextinstr_inv; auto. 
  (* long offset *)
  pose (rs1 := nextinstr (rs#GPR2 <- (Val.add rs#base (Vint (Int.shl (high_s ofs) (Int.repr 16)))))).
  exists (nextinstr rs1).
  split. apply exec_straight_two with rs1 m.
  simpl. rewrite gpr_or_zero_not_zero; auto. 
  apply storeind_aux_correct; auto with ppcgen.
  unfold rs1. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  rewrite nextinstr_inv; auto with ppcgen.
  rewrite Pregmap.gso; auto with ppcgen.
  rewrite Val.add_assoc. simpl. rewrite low_high_s. assumption.
  reflexivity. reflexivity.
  intros. rewrite nextinstr_inv; auto.
  unfold rs1. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
Qed.

(** Float comparisons. *)

Lemma floatcomp_correct:
  forall cmp (r1 r2: freg) k rs m,
  exists rs',
     exec_straight (floatcomp cmp r1 r2 k) rs m k rs' m
  /\ rs'#(reg_of_crbit (fst (crbit_for_fcmp cmp))) = 
       (if snd (crbit_for_fcmp cmp)
        then Val.cmpf cmp rs#r1 rs#r2
        else Val.notbool (Val.cmpf cmp rs#r1 rs#r2))
  /\ forall r', 
       r' <> PC -> r' <> CR0_0 -> r' <> CR0_1 ->
       r' <> CR0_2 -> r' <> CR0_3 -> rs'#r' = rs#r'.
Proof.
  intros. 
  generalize (compare_float_spec rs rs#r1 rs#r2).
  intros [A [B [C D]]].
  set (rs1 := nextinstr (compare_float rs rs#r1 rs#r2)) in *.
  assert ((cmp = Ceq \/ cmp = Cne \/ cmp = Clt \/ cmp = Cgt)
          \/ (cmp = Cle \/ cmp = Cge)).
    case cmp; tauto.
  unfold floatcomp.  elim H; intro; clear H.
  exists rs1.
  split. generalize H0; intros [EQ|[EQ|[EQ|EQ]]]; subst cmp;
  apply exec_straight_one; reflexivity.
  split. 
  generalize H0; intros [EQ|[EQ|[EQ|EQ]]]; subst cmp; simpl; auto. 
  rewrite Val.negate_cmpf_eq. auto.
  auto.
  (* two instrs *)
  exists (nextinstr (rs1#CR0_3 <- (Val.cmpf cmp rs#r1 rs#r2))).
  split. elim H0; intro; subst cmp.
  apply exec_straight_two with rs1 m.
  reflexivity. simpl. 
  rewrite C; rewrite A. rewrite Val.or_commut. rewrite <- Val.cmpf_le.
  reflexivity. reflexivity. reflexivity.
  apply exec_straight_two with rs1 m.
  reflexivity. simpl. 
  rewrite C; rewrite B. rewrite Val.or_commut. rewrite <- Val.cmpf_ge.
  reflexivity. reflexivity. reflexivity.
  split. elim H0; intro; subst cmp; simpl.
  reflexivity.
  reflexivity.
  intros. rewrite nextinstr_inv; auto. rewrite Pregmap.gso; auto.
Qed.

Ltac TypeInv :=
  match goal with
  | H: (List.map ?f ?x = nil) |- _ =>
      destruct x; [clear H | simpl in H; discriminate]
  | H: (List.map ?f ?x = ?hd :: ?tl) |- _ =>
      destruct x; simpl in H;
      [ discriminate |
        injection H; clear H; let T := fresh "T" in (
          intros H T; TypeInv) ]
  | _ => idtac
  end.

(** Translation of conditions. *)

Lemma transl_cond_correct_aux:
  forall cond args k ms sp rs m,
  map mreg_type args = type_of_condition cond ->
  agree ms sp rs ->
  exists rs',
     exec_straight (transl_cond cond args k) rs m k rs' m
  /\ rs'#(reg_of_crbit (fst (crbit_for_cond cond))) = 
       (if snd (crbit_for_cond cond)
        then eval_condition_total cond (map ms args)
        else Val.notbool (eval_condition_total cond (map ms args)))
  /\ agree ms sp rs'.
Proof.
  intros.  destruct cond; simpl in H; TypeInv.
  (* Ccomp *)
  simpl. 
  generalize (compare_sint_spec rs ms#m0 ms#m1).
  intros [A [B [C D]]].
  exists (nextinstr (compare_sint rs ms#m0 ms#m1)).
  split. apply exec_straight_one. simpl. 
  repeat (rewrite <- (ireg_val ms sp rs); auto).
  reflexivity.
  split. 
  case c; simpl; auto; rewrite <- Val.negate_cmp; simpl; auto.
  apply agree_exten_2 with rs; auto.
  (* Ccompu *)
  simpl. 
  generalize (compare_uint_spec rs ms#m0 ms#m1).
  intros [A [B [C D]]].
  exists (nextinstr (compare_uint rs ms#m0 ms#m1)).
  split. apply exec_straight_one. simpl. 
  repeat (rewrite <- (ireg_val ms sp rs); auto).
  reflexivity.
  split. 
  case c; simpl; auto; rewrite <- Val.negate_cmpu; simpl; auto.
  apply agree_exten_2 with rs; auto.
  (* Ccompimm *)
  simpl.
  case (Int.eq (high_s i) Int.zero).
  generalize (compare_sint_spec rs ms#m0 (Vint i)).
  intros [A [B [C D]]].
  exists (nextinstr (compare_sint rs ms#m0 (Vint i))).
  split. apply exec_straight_one. simpl. 
  repeat (rewrite <- (ireg_val ms sp rs); auto).
  reflexivity.
  split. 
  case c; simpl; auto; rewrite <- Val.negate_cmp; simpl; auto.
  apply agree_exten_2 with rs; auto.
  generalize (loadimm_correct GPR2 i (Pcmpw (ireg_of m0) GPR2 :: k) rs m).
  intros [rs1 [EX1 [RES1 OTH1]]].
  assert (agree ms sp rs1). apply agree_exten_2 with rs; auto.
  generalize (compare_sint_spec rs1 ms#m0 (Vint i)).
  intros [A [B [C D]]].
  exists (nextinstr (compare_sint rs1 ms#m0 (Vint i))).
  split. eapply exec_straight_trans. eexact EX1.
  apply exec_straight_one. simpl. 
  repeat (rewrite <- (ireg_val ms sp rs1); auto). rewrite RES1.
  reflexivity. reflexivity.
  split. 
  case c; simpl; auto; rewrite <- Val.negate_cmp; simpl; auto.
  apply agree_exten_2 with rs1; auto.
  (* Ccompuimm *)
  simpl.
  case (Int.eq (high_u i) Int.zero).
  generalize (compare_uint_spec rs ms#m0 (Vint i)).
  intros [A [B [C D]]].
  exists (nextinstr (compare_uint rs ms#m0 (Vint i))).
  split. apply exec_straight_one. simpl. 
  repeat (rewrite <- (ireg_val ms sp rs); auto).
  reflexivity.
  split. 
  case c; simpl; auto; rewrite <- Val.negate_cmpu; simpl; auto.
  apply agree_exten_2 with rs; auto.
  generalize (loadimm_correct GPR2 i (Pcmplw (ireg_of m0) GPR2 :: k) rs m).
  intros [rs1 [EX1 [RES1 OTH1]]].
  assert (agree ms sp rs1). apply agree_exten_2 with rs; auto.
  generalize (compare_uint_spec rs1 ms#m0 (Vint i)).
  intros [A [B [C D]]].
  exists (nextinstr (compare_uint rs1 ms#m0 (Vint i))).
  split. eapply exec_straight_trans. eexact EX1.
  apply exec_straight_one. simpl. 
  repeat (rewrite <- (ireg_val ms sp rs1); auto). rewrite RES1.
  reflexivity. reflexivity.
  split. 
  case c; simpl; auto; rewrite <- Val.negate_cmpu; simpl; auto.
  apply agree_exten_2 with rs1; auto.
  (* Ccompf *)
  simpl.
  generalize (floatcomp_correct c (freg_of m0) (freg_of m1) k rs m).
  intros [rs' [EX [RES OTH]]].
  exists rs'. split. auto. 
  split. rewrite RES. repeat (rewrite <- (freg_val ms sp rs); auto). 
  apply agree_exten_2 with rs; auto.
  (* Cnotcompf *)
  simpl. 
  generalize (floatcomp_correct c (freg_of m0) (freg_of m1) k rs m).
  intros [rs' [EX [RES OTH]]].
  exists rs'. split. auto. 
  split. rewrite RES. repeat (rewrite <- (freg_val ms sp rs); auto).
  assert (forall v1 v2, Val.notbool (Val.notbool (Val.cmpf c v1 v2)) = Val.cmpf c v1 v2).
    intros v1 v2; unfold Val.cmpf; destruct v1; destruct v2; auto. 
    apply Val.notbool_idem2.
  rewrite H.
  generalize RES. case (snd (crbit_for_fcmp c)); simpl; auto.
  apply agree_exten_2 with rs; auto.
  (* Cmaskzero *)
  simpl.
  generalize (andimm_correct GPR2 (ireg_of m0) i k rs m (ireg_of_not_GPR2 m0)).
  intros [rs' [A [B [C D]]]].
  exists rs'. split. assumption. 
  split. rewrite C. rewrite <- (ireg_val ms sp rs); auto.
  apply agree_exten_2 with rs; auto.
  (* Cmasknotzero *)
  simpl.
  generalize (andimm_correct GPR2 (ireg_of m0) i k rs m (ireg_of_not_GPR2 m0)).
  intros [rs' [A [B [C D]]]].
  exists rs'. split. assumption. 
  split. rewrite C. rewrite <- (ireg_val ms sp rs); auto.
  rewrite Val.notbool_idem3. reflexivity. 
  apply agree_exten_2 with rs; auto.
Qed.

Lemma transl_cond_correct:
  forall cond args k ms sp rs m b,
  map mreg_type args = type_of_condition cond ->
  agree ms sp rs ->
  eval_condition cond (map ms args) m = Some b ->
  exists rs',
     exec_straight (transl_cond cond args k) rs m k rs' m
  /\ rs'#(reg_of_crbit (fst (crbit_for_cond cond))) = 
       (if snd (crbit_for_cond cond)
        then Val.of_bool b
        else Val.notbool (Val.of_bool b))
  /\ agree ms sp rs'.
Proof.
  intros. rewrite <- (eval_condition_weaken _ _ _ H1). 
  apply transl_cond_correct_aux; auto.
Qed.

(** Translation of arithmetic operations. *)

Ltac TranslOpSimpl :=
  match goal with
  | |- exists rs' : regset,
         exec_straight ?c ?rs ?m ?k rs' ?m /\
         agree (Regmap.set ?res ?v ?ms) ?sp rs'  =>
    (exists (nextinstr (rs#(ireg_of res) <- v));
     split; 
     [ apply exec_straight_one;
       [ repeat (rewrite (ireg_val ms sp rs); auto); reflexivity
       | reflexivity ]
     | auto with ppcgen ])
  ||
    (exists (nextinstr (rs#(freg_of res) <- v));
     split; 
     [ apply exec_straight_one;
       [ repeat (rewrite (freg_val ms sp rs); auto); reflexivity
       | reflexivity ]
     | auto with ppcgen ])
  end.

Lemma transl_op_correct:
  forall op args res k ms sp rs m v,
  wt_instr (Mop op args res) ->
  agree ms sp rs ->
  eval_operation ge sp op (map ms args) m = Some v ->
  exists rs',
     exec_straight (transl_op op args res k) rs m k rs' m
  /\ agree (Regmap.set res v ms) sp rs'.
Proof.
  intros. rewrite <- (eval_operation_weaken _ _ _ _ _ H1). clear H1; clear v.
  inversion H.
  (* Omove *)
  simpl. exists (nextinstr (rs#(preg_of res) <- (ms r1))).
  split. caseEq (mreg_type r1); intro.
  apply exec_straight_one. simpl. rewrite (ireg_val ms sp rs); auto.
  simpl. unfold preg_of. rewrite <- H2. rewrite H5. reflexivity.
  auto with ppcgen.
  apply exec_straight_one. simpl. rewrite (freg_val ms sp rs); auto.
  simpl. unfold preg_of. rewrite <- H2. rewrite H5. reflexivity.
  auto with ppcgen.
  auto with ppcgen.
  (* Other instructions *)
  clear H1; clear H2; clear H4.
  destruct op; simpl in H5; injection H5; clear H5; intros;
  TypeInv; simpl; try (TranslOpSimpl).
  (* Omove again *)
  congruence.
  (* Ointconst *)
  generalize (loadimm_correct (ireg_of res) i k rs m).
  intros [rs' [A [B C]]]. 
  exists rs'. split. auto. 
  apply agree_set_mireg_exten with rs; auto. 
  (* Ofloatconst *)
  exists (nextinstr (rs#(freg_of res) <- (Vfloat f) #GPR2 <- Vundef)).
  split. apply exec_straight_one. reflexivity. reflexivity.
  auto with ppcgen.
  (* Oaddrsymbol *)
  set (v := find_symbol_offset ge i i0).
  pose (rs1 := nextinstr (rs#(ireg_of res) <- (high_half_unsigned v))).
  exists (nextinstr (rs1#(ireg_of res) <- v)).
  split. apply exec_straight_two with rs1 m.
  unfold exec_instr. rewrite gpr_or_zero_zero.
  unfold const_high. rewrite Val.add_commut. 
  rewrite high_half_unsigned_zero. reflexivity. 
  simpl. unfold rs1 at 1. rewrite nextinstr_inv; auto with ppcgen.
  rewrite Pregmap.gss.
  fold v. rewrite Val.or_commut. rewrite low_high_half_unsigned.
  reflexivity. reflexivity. reflexivity. 
  unfold rs1. auto with ppcgen.
  (* Oaddrstack *)
  assert (GPR1 <> GPR2). discriminate.
  generalize (addimm_correct (ireg_of res) GPR1 i k rs m H2). 
  intros [rs' [EX [RES OTH]]].
  exists rs'. split. auto. 
  apply agree_set_mireg_exten with rs; auto.
  rewrite (sp_val ms sp rs). auto. auto. 
  (* Ocast8unsigned *)
  exists (nextinstr (rs#(ireg_of res) <- (Val.rolm (ms m0) Int.zero (Int.repr 255)))).
  split. apply exec_straight_one. repeat (rewrite (ireg_val ms sp rs)); auto. reflexivity.
  replace (Val.cast8unsigned (ms m0))
      with (Val.rolm (ms m0) Int.zero (Int.repr 255)).
  auto with ppcgen. 
  unfold Val.rolm, Val.cast8unsigned. destruct (ms m0); auto. 
  rewrite Int.rolm_zero. rewrite Int.cast8unsigned_and. auto.
  (* Ocast16unsigned *)
  exists (nextinstr (rs#(ireg_of res) <- (Val.rolm (ms m0) Int.zero (Int.repr 65535)))).
  split. apply exec_straight_one. repeat (rewrite (ireg_val ms sp rs)); auto. reflexivity.
  replace (Val.cast16unsigned (ms m0))
      with (Val.rolm (ms m0) Int.zero (Int.repr 65535)).
  auto with ppcgen. 
  unfold Val.rolm, Val.cast16unsigned. destruct (ms m0); auto. 
  rewrite Int.rolm_zero. rewrite Int.cast16unsigned_and. auto.
  (* Oaddimm *)
  generalize (addimm_correct (ireg_of res) (ireg_of m0) i k rs m
                            (ireg_of_not_GPR2 m0)).
  intros [rs' [A [B C]]]. 
  exists rs'. split. auto.
  apply agree_set_mireg_exten with rs; auto.
  rewrite (ireg_val ms sp rs); auto. 
  (* Osub *)
  exists (nextinstr (rs#(ireg_of res) <- (Val.sub (ms m0) (ms m1)) #CARRY <- Vundef)).
  split. apply exec_straight_one. repeat (rewrite (ireg_val ms sp rs); auto).
  simpl. reflexivity. auto with ppcgen.
  (* Osubimm *)
  case (Int.eq (high_s i) Int.zero).
  exists (nextinstr (rs#(ireg_of res) <- (Val.sub (Vint i) (ms m0)) #CARRY <- Vundef)).
  split. apply exec_straight_one. rewrite (ireg_val ms sp rs); auto.
  reflexivity. simpl. auto with ppcgen.
  generalize (loadimm_correct GPR2 i (Psubfc (ireg_of res) (ireg_of m0) GPR2 :: k) rs m).
  intros [rs1 [EX [RES OTH]]].
  assert (agree ms sp rs1). apply agree_exten_2 with rs; auto.
  exists (nextinstr (rs1#(ireg_of res) <- (Val.sub (Vint i) (ms m0)) #CARRY <- Vundef)).
  split. eapply exec_straight_trans. eexact EX. 
  apply exec_straight_one. repeat (rewrite (ireg_val ms sp rs); auto).
  simpl. rewrite RES. rewrite OTH. reflexivity. 
  generalize (ireg_of_not_GPR2 m0); congruence.
  discriminate.
  reflexivity. simpl; auto with ppcgen.
  (* Omulimm *)
  case (Int.eq (high_s i) Int.zero).
  exists (nextinstr (rs#(ireg_of res) <- (Val.mul (ms m0) (Vint i)))).
  split. apply exec_straight_one. rewrite (ireg_val ms sp rs); auto.
  reflexivity. auto with ppcgen.
  generalize (loadimm_correct GPR2 i (Pmullw (ireg_of res) (ireg_of m0) GPR2 :: k) rs m).
  intros [rs1 [EX [RES OTH]]].
  assert (agree ms sp rs1). apply agree_exten_2 with rs; auto.
  exists (nextinstr (rs1#(ireg_of res) <- (Val.mul (ms m0) (Vint i)))).
  split. eapply exec_straight_trans. eexact EX. 
  apply exec_straight_one. repeat (rewrite (ireg_val ms sp rs); auto).
  simpl. rewrite RES. rewrite OTH. reflexivity. 
  generalize (ireg_of_not_GPR2 m0); congruence.
  discriminate.
  reflexivity. simpl; auto with ppcgen.
  (* Oand *)
  pose (v := Val.and (ms m0) (ms m1)).
  pose (rs1 := rs#(ireg_of res) <- v).
  generalize (compare_sint_spec rs1 v Vzero).
  intros [A [B [C D]]].
  exists (nextinstr (compare_sint rs1 v Vzero)).
  split. apply exec_straight_one. 
  unfold rs1, v. repeat (rewrite (ireg_val ms sp rs); auto). 
  reflexivity.  
  apply agree_exten_2 with rs1. unfold rs1, v; auto with ppcgen.
  auto.
  (* Oandimm *)
  generalize (andimm_correct (ireg_of res) (ireg_of m0) i k rs m
                             (ireg_of_not_GPR2 m0)).
  intros [rs' [A [B [C D]]]]. 
  exists rs'. split. auto. apply agree_set_mireg_exten with rs; auto.
  rewrite (ireg_val ms sp rs); auto.
  (* Oorimm *)
  generalize (orimm_correct (ireg_of res) (ireg_of m0) i k rs m).
  intros [rs' [A [B C]]]. 
  exists rs'. split. auto. apply agree_set_mireg_exten with rs; auto.
  rewrite (ireg_val ms sp rs); auto.
  (* Oxorimm *)
  generalize (xorimm_correct (ireg_of res) (ireg_of m0) i k rs m).
  intros [rs' [A [B C]]]. 
  exists rs'. split. auto. apply agree_set_mireg_exten with rs; auto.
  rewrite (ireg_val ms sp rs); auto.
  (* Oshr *)
  exists (nextinstr (rs#(ireg_of res) <- (Val.shr (ms m0) (ms m1)) #CARRY <- (Val.shr_carry (ms m0) (ms m1)))).
  split. apply exec_straight_one. repeat (rewrite (ireg_val ms sp rs); auto).
  reflexivity. auto with ppcgen.
  (* Oshrimm *)
  exists (nextinstr (rs#(ireg_of res) <- (Val.shr (ms m0) (Vint i)) #CARRY <- (Val.shr_carry (ms m0) (Vint i)))).
  split. apply exec_straight_one. repeat (rewrite (ireg_val ms sp rs); auto).
  reflexivity. auto with ppcgen.
  (* Oxhrximm *)
  pose (rs1 := nextinstr (rs#(ireg_of res) <- (Val.shr (ms m0) (Vint i)) #CARRY <- (Val.shr_carry (ms m0) (Vint i)))).
  exists (nextinstr (rs1#(ireg_of res) <- (Val.shrx (ms m0) (Vint i)))).
  split. apply exec_straight_two with rs1 m.
  unfold rs1; rewrite (ireg_val ms sp rs); auto.
  simpl; unfold rs1; repeat rewrite <- (ireg_val ms sp rs); auto.
  repeat (rewrite nextinstr_inv; try discriminate).
  repeat rewrite Pregmap.gss. decEq. decEq. 
  apply (f_equal3 (@Pregmap.set val)); auto.
  rewrite Pregmap.gso. rewrite Pregmap.gss. apply Val.shrx_carry.
  discriminate. reflexivity. reflexivity.
  apply agree_exten_2 with (rs#(ireg_of res) <- (Val.shrx (ms m0) (Vint i))).
  auto with ppcgen. 
  intros. rewrite nextinstr_inv; auto. 
  case (preg_eq (ireg_of res) r); intro.
  subst r. repeat rewrite Pregmap.gss. auto.
  repeat rewrite Pregmap.gso; auto.
  unfold rs1. rewrite nextinstr_inv; auto.
  repeat rewrite Pregmap.gso; auto.
  (* Ointoffloat *)
  exists (nextinstr (rs#(ireg_of res) <- (Val.intoffloat (ms m0)) #FPR13 <- Vundef)).
  split. apply exec_straight_one. 
  repeat (rewrite (freg_val ms sp rs); auto).
  reflexivity. auto with ppcgen.
  (* Ofloatofint *)
  exists (nextinstr (rs#(freg_of res) <- (Val.floatofint (ms m0)) #GPR2 <- Vundef #FPR13 <- Vundef)).
  split. apply exec_straight_one. 
  repeat (rewrite (ireg_val ms sp rs); auto).
  reflexivity. auto 10 with ppcgen.
  (* Ofloatofintu *)
  exists (nextinstr (rs#(freg_of res) <- (Val.floatofintu (ms m0)) #GPR2 <- Vundef #FPR13 <- Vundef)).
  split. apply exec_straight_one. 
  repeat (rewrite (ireg_val ms sp rs); auto).
  reflexivity. auto 10 with ppcgen.
  (* Ocmp *)
  set (bit := fst (crbit_for_cond c)).
  set (isset := snd (crbit_for_cond c)).
  set (k1 :=
        Pmfcrbit (ireg_of res) bit ::
        (if isset
         then k
         else Pxori (ireg_of res) (ireg_of res) (Cint Int.one) :: k)).
  generalize (transl_cond_correct_aux c args k1 ms sp rs m H2 H0).
  fold bit; fold isset. 
  intros [rs1 [EX1 [RES1 AG1]]].
  set (rs2 := nextinstr (rs1#(ireg_of res) <- (rs1#(reg_of_crbit bit)))).
  destruct isset.
  exists rs2.
  split. apply exec_straight_trans with k1 rs1 m. assumption.
  unfold k1. apply exec_straight_one. 
  reflexivity. reflexivity. 
  unfold rs2. rewrite RES1. auto with ppcgen. 
  exists (nextinstr (rs2#(ireg_of res) <- (eval_condition_total c ms##args))).
  split. apply exec_straight_trans with k1 rs1 m. assumption.
  unfold k1. apply exec_straight_two with rs2 m.
  reflexivity. simpl. 
  replace (Val.xor (rs2 (ireg_of res)) (Vint Int.one))
     with (eval_condition_total c ms##args).
  reflexivity.
  unfold rs2. rewrite nextinstr_inv; auto with ppcgen. rewrite Pregmap.gss. 
  rewrite RES1. apply Val.notbool_xor. apply eval_condition_total_is_bool.
  reflexivity. reflexivity. 
  unfold rs2. auto with ppcgen. 
Qed.

Lemma transl_load_store_correct:
  forall (mk1: constant -> ireg -> instruction) (mk2: ireg -> ireg -> instruction)
    addr args k ms sp rs m ms' m',
  (forall cst (r1: ireg) (rs1: regset) k,
    eval_addressing_total ge sp addr (map ms args) = Val.add rs1#r1 (const_low ge cst) ->
    agree ms sp rs1 ->
    r1 <> GPR0 ->
    exists rs',
    exec_straight (mk1 cst r1 :: k) rs1 m k rs' m' /\
    agree ms' sp rs') ->
  (forall (r1 r2: ireg) (rs1: regset) k,
    eval_addressing_total ge sp addr (map ms args) = Val.add rs1#r1 rs1#r2 ->
    agree ms sp rs1 ->
    exists rs',
    exec_straight (mk2 r1 r2 :: k) rs1 m k rs' m' /\
    agree ms' sp rs') ->
  agree ms sp rs ->
  map mreg_type args = type_of_addressing addr ->
  exists rs',
    exec_straight (transl_load_store mk1 mk2 addr args k) rs m
                        k rs' m'
  /\ agree ms' sp rs'.
Proof.
  intros. destruct addr; simpl in H2; TypeInv; simpl.
  (* Aindexed *)
  case (ireg_eq (ireg_of t) GPR0); intro.
  (* Aindexed from GPR0 *)
  set (rs1 := nextinstr (rs#GPR2 <- (ms t))).
  set (rs2 := nextinstr (rs1#GPR2 <- (Val.add (ms t) (Vint (Int.shl (high_s i) (Int.repr 16)))))).
  assert (ADDR: eval_addressing_total ge sp (Aindexed i) ms##(t :: nil) =
                Val.add rs2#GPR2 (const_low ge (Cint (low_s i)))).
    simpl. unfold rs2. rewrite nextinstr_inv. rewrite Pregmap.gss.
    rewrite Val.add_assoc. simpl. rewrite low_high_s. auto.
    discriminate.
  assert (AG: agree ms sp rs2). unfold rs2, rs1; auto 6 with ppcgen.
  assert (NOT0: GPR2 <> GPR0). discriminate.
  generalize (H _ _ _ k ADDR AG NOT0).
  intros [rs' [EX' AG']].
  exists rs'. split.
  apply exec_straight_trans with (mk1 (Cint (low_s i)) GPR2 :: k) rs2 m.
  apply exec_straight_two with rs1 m.
  unfold rs1. rewrite (ireg_val ms sp rs); auto.
  unfold rs2. replace (ms t) with (rs1#GPR2). auto.
  unfold rs1. rewrite nextinstr_inv. apply Pregmap.gss. discriminate.
  reflexivity. reflexivity.  
  assumption. assumption.
  (* Aindexed short *)
  case (Int.eq (high_s i) Int.zero).
  assert (ADDR: eval_addressing_total ge sp (Aindexed i) ms##(t :: nil) =
                Val.add rs#(ireg_of t) (const_low ge (Cint i))).
    simpl. rewrite (ireg_val ms sp rs); auto.
  generalize (H _ _ _ k ADDR H1 n). intros [rs' [EX' AG']].
  exists rs'. split. auto. auto.
  (* Aindexed long *)
  set (rs1 := nextinstr (rs#GPR2 <- (Val.add (ms t) (Vint (Int.shl (high_s i) (Int.repr 16)))))).
  assert (ADDR: eval_addressing_total ge sp (Aindexed i) ms##(t :: nil) =
                Val.add rs1#GPR2 (const_low ge (Cint (low_s i)))).
    simpl. unfold rs1. rewrite nextinstr_inv. rewrite Pregmap.gss.
    rewrite Val.add_assoc. simpl. rewrite low_high_s. auto.
    discriminate.
  assert (AG: agree ms sp rs1). unfold rs1; auto with ppcgen.
  assert (NOT0: GPR2 <> GPR0). discriminate.
  generalize (H _ _ _ k ADDR AG NOT0). intros [rs' [EX' AG']].
  exists rs'. split. apply exec_straight_step with rs1 m.
  simpl. rewrite gpr_or_zero_not_zero; auto. 
  rewrite <- (ireg_val ms sp rs); auto. reflexivity.
  assumption. assumption.
  (* Aindexed2 *)
  apply H0. 
  simpl. repeat (rewrite (ireg_val ms sp rs); auto). auto.
  (* Aglobal *)
  set (rs1 := nextinstr (rs#GPR2 <- (const_high ge (Csymbol_high_signed i i0)))).
  assert (ADDR: eval_addressing_total ge sp (Aglobal i i0) ms##nil =
                Val.add rs1#GPR2 (const_low ge (Csymbol_low_signed i i0))).
    simpl. unfold rs1. rewrite nextinstr_inv. rewrite Pregmap.gss.
    unfold const_high, const_low. 
    set (v := symbol_offset ge i i0).
    symmetry. rewrite Val.add_commut. apply low_high_half_signed. 
    discriminate.
  assert (AG: agree ms sp rs1). unfold rs1; auto with ppcgen.
  assert (NOT0: GPR2 <> GPR0). discriminate.
  generalize (H _ _ _ k ADDR AG NOT0). intros [rs' [EX' AG']].
  exists rs'. split. apply exec_straight_step with rs1 m.
  unfold exec_instr. rewrite gpr_or_zero_zero. 
  rewrite Val.add_commut. unfold const_high. 
  rewrite high_half_signed_zero.
  reflexivity. reflexivity.
  assumption. assumption.
  (* Abased *)
  assert (COMMON:
    forall (rs1: regset) r,
    r <> GPR0 ->
    ms t = rs1#r ->
    agree ms sp rs1 ->
    exists rs',
      exec_straight
        (Paddis GPR2 r (Csymbol_high_signed i i0)
         :: mk1 (Csymbol_low_signed i i0) GPR2 :: k) rs1 m k rs' m'
      /\ agree ms' sp rs').
  intros. 
  set (rs2 := nextinstr (rs1#GPR2 <- (Val.add (ms t) (const_high ge (Csymbol_high_signed i i0))))).
  assert (ADDR: eval_addressing_total ge sp (Abased i i0) ms##(t::nil) =
                Val.add rs2#GPR2 (const_low ge (Csymbol_low_signed i i0))).
    simpl. unfold rs2. rewrite nextinstr_inv. rewrite Pregmap.gss.
    unfold const_high. 
    set (v := symbol_offset ge i i0).
    rewrite Val.add_assoc. 
    rewrite (Val.add_commut (high_half_signed v)).
    rewrite low_high_half_signed. apply Val.add_commut.
    discriminate.
  assert (AG: agree ms sp rs2). unfold rs2; auto with ppcgen.
  assert (NOT0: GPR2 <> GPR0). discriminate.
  generalize (H _ _ _ k ADDR AG NOT0). intros [rs' [EX' AG']].
  exists rs'. split. apply exec_straight_step with rs2 m.
  unfold exec_instr. rewrite gpr_or_zero_not_zero; auto.
  rewrite <- H3. reflexivity. reflexivity. 
  assumption. assumption.
  case (ireg_eq (ireg_of t) GPR0); intro.
  set (rs1 := nextinstr (rs#GPR2 <- (ms t))).
  assert (R1: GPR2 <> GPR0). discriminate.
  assert (R2: ms t = rs1 GPR2). 
    unfold rs1. rewrite nextinstr_inv. rewrite Pregmap.gss; auto.
    discriminate.
  assert (R3: agree ms sp rs1). unfold rs1; auto with ppcgen.
  generalize (COMMON rs1 GPR2 R1 R2 R3). intros [rs' [EX' AG']].
  exists rs'. split.
  apply exec_straight_step with rs1 m.
  unfold rs1. rewrite (ireg_val ms sp rs); auto. reflexivity.
  assumption. assumption.
  apply COMMON; auto. eapply ireg_val; eauto.
  (* Ainstack *)
  case (Int.eq (high_s i) Int.zero).
  apply H. simpl. rewrite (sp_val ms sp rs); auto. auto.
  discriminate.
  set (rs1 := nextinstr (rs#GPR2 <- (Val.add sp (Vint (Int.shl (high_s i) (Int.repr 16)))))).
  assert (ADDR: eval_addressing_total ge sp (Ainstack i) ms##nil =
                Val.add rs1#GPR2 (const_low ge (Cint (low_s i)))).
    simpl. unfold rs1. rewrite nextinstr_inv. rewrite Pregmap.gss.
    rewrite Val.add_assoc. decEq. simpl. rewrite low_high_s. auto.
    discriminate.
  assert (AG: agree ms sp rs1). unfold rs1; auto with ppcgen.
  assert (NOT0: GPR2 <> GPR0). discriminate.
  generalize (H _ _ _ k ADDR AG NOT0). intros [rs' [EX' AG']].
  exists rs'. split. apply exec_straight_step with rs1 m.
  simpl. rewrite gpr_or_zero_not_zero. 
  unfold rs1. rewrite (sp_val ms sp rs). reflexivity.
  auto. discriminate. reflexivity. assumption. assumption.
Qed.

(** Translation of memory loads. *)

Lemma transl_load_correct:
  forall (mk1: constant -> ireg -> instruction) (mk2: ireg -> ireg -> instruction)
    chunk addr args k ms sp rs m dst a v,
  (forall cst (r1: ireg) (rs1: regset),
    exec_instr ge fn (mk1 cst r1) rs1 m =
    load1 ge chunk (preg_of dst) cst r1 rs1 m) ->
  (forall (r1 r2: ireg) (rs1: regset),
    exec_instr ge fn (mk2 r1 r2) rs1 m =
    load2 chunk (preg_of dst) r1 r2 rs1 m) ->
  agree ms sp rs ->
  map mreg_type args = type_of_addressing addr ->
  eval_addressing ge sp addr (map ms args) = Some a ->
  Mem.loadv chunk m a = Some v ->
  exists rs',
    exec_straight (transl_load_store mk1 mk2 addr args k) rs m
                        k rs' m
  /\ agree (Regmap.set dst v ms) sp rs'.
Proof.
  intros. apply transl_load_store_correct with ms.
  intros. exists (nextinstr (rs1#(preg_of dst) <- v)). 
  split. apply exec_straight_one. rewrite H. 
  unfold load1. rewrite gpr_or_zero_not_zero; auto. 
  rewrite <- (eval_addressing_weaken _ _ _ _ H3) in H4.
  rewrite H5 in H4. rewrite H4. auto.
  auto with ppcgen. auto with ppcgen. 
  intros. exists (nextinstr (rs1#(preg_of dst) <- v)). 
  split. apply exec_straight_one. rewrite H0. 
  unfold load2. 
  rewrite <- (eval_addressing_weaken _ _ _ _ H3) in H4.
  rewrite H5 in H4. rewrite H4. auto.
  auto with ppcgen. auto with ppcgen. 
  auto. auto.
Qed.

(** Translation of memory stores. *)

Lemma transl_store_correct:
  forall (mk1: constant -> ireg -> instruction) (mk2: ireg -> ireg -> instruction)
    chunk addr args k ms sp rs m src a m',
  (forall cst (r1: ireg) (rs1: regset),
    exec_instr ge fn (mk1 cst r1) rs1 m =
    store1 ge chunk (preg_of src) cst r1 rs1 m) ->
  (forall (r1 r2: ireg) (rs1: regset),
    exec_instr ge fn (mk2 r1 r2) rs1 m =
    store2 chunk (preg_of src) r1 r2 rs1 m) ->
  agree ms sp rs ->
  map mreg_type args = type_of_addressing addr ->
  eval_addressing ge sp addr (map ms args) = Some a ->
  Mem.storev chunk m a (ms src) = Some m' ->
  exists rs',
    exec_straight (transl_load_store mk1 mk2 addr args k) rs m
                        k rs' m'
  /\ agree ms sp rs'.
Proof.
  intros.   apply transl_load_store_correct with ms.
  intros. exists (nextinstr rs1). 
  split. apply exec_straight_one. rewrite H. 
  unfold store1. rewrite gpr_or_zero_not_zero; auto. 
  rewrite <- (eval_addressing_weaken _ _ _ _ H3) in H4.
  rewrite H5 in H4. elim H6; intros. rewrite H9 in H4.
  rewrite H4. auto.
  auto with ppcgen. auto with ppcgen. 
  intros. exists (nextinstr rs1).
  split. apply exec_straight_one. rewrite H0. 
  unfold store2. 
  rewrite <- (eval_addressing_weaken _ _ _ _ H3) in H4.
  rewrite H5 in H4. elim H6; intros. rewrite H8 in H4.
  rewrite H4. auto.
  auto with ppcgen. auto with ppcgen. 
  auto. auto.
Qed.

(** Translation of allocations *)

Lemma transl_alloc_correct:
  forall ms sp rs sz m m' blk k,
  agree ms sp rs ->
  ms Conventions.loc_alloc_argument = Vint sz ->
  Mem.alloc m 0 (Int.signed sz) = (m', blk) ->
  let ms' := Regmap.set Conventions.loc_alloc_result (Vptr blk Int.zero) ms in
  exists rs',
    exec_straight (Pallocblock :: k) rs m k rs' m'
  /\ agree ms' sp rs'.
Proof.
  intros. 
  pose (rs' := nextinstr (rs#GPR3 <- (Vptr blk Int.zero) #LR <- (Val.add rs#PC Vone))).
  exists rs'; split.
  apply exec_straight_one. unfold exec_instr. 
  generalize (preg_val _ _ _ Conventions.loc_alloc_argument H).
  unfold preg_of; intro. simpl in H2. rewrite <- H2. rewrite H0.
  rewrite H1. reflexivity.
  reflexivity. 
  unfold ms', rs'. apply agree_nextinstr. apply agree_set_other. 
  change (IR GPR3) with (preg_of Conventions.loc_alloc_result).
  apply agree_set_mreg. auto.
  simpl. tauto.
Qed.

End STRAIGHTLINE.

