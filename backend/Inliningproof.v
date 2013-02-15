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

(** RTL function inlining: semantic preservation *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import Inlining.
Require Import Inliningspec.
Require Import RTL.

Section INLINING.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: transf_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Let fenv := funenv_program prog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros. apply Genv.find_symbol_transf_partial with (transf_fundef fenv); auto.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. apply Genv.find_var_info_transf_partial with (transf_fundef fenv); auto.
Qed.

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists f', Genv.find_funct tge v = Some f' /\ transf_fundef fenv f = OK f'.
Proof (Genv.find_funct_transf_partial (transf_fundef fenv) _ TRANSF).

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists f', Genv.find_funct_ptr tge b = Some f' /\ transf_fundef fenv f = OK f'.
Proof (Genv.find_funct_ptr_transf_partial (transf_fundef fenv) _ TRANSF).

Lemma sig_function_translated:
  forall f f', transf_fundef fenv f = OK f' -> funsig f' = funsig f.
Proof.
  intros. destruct f; Errors.monadInv H.
  exploit transf_function_spec; eauto. intros SP; inv SP. auto. 
  auto.
Qed.

(** ** Properties of contexts and relocations *)

Remark sreg_below_diff:
  forall ctx r r', Ple r' ctx.(dreg) -> sreg ctx r <> r'.
Proof.
  intros. unfold sreg. xomega. 
Qed.

Remark context_below_diff:
  forall ctx1 ctx2 r1 r2,
  context_below ctx1 ctx2 -> Ple r1 ctx1.(mreg) -> sreg ctx1 r1 <> sreg ctx2 r2.
Proof.
  intros. red in H. unfold sreg. xomega. 
Qed.

Remark context_below_le:
  forall ctx1 ctx2 r, context_below ctx1 ctx2 -> Ple r ctx1.(mreg) -> Ple (sreg ctx1 r) ctx2.(dreg).
Proof.
  intros. red in H. unfold sreg. xomega.
Qed.

(** ** Agreement between register sets before and after inlining. *)

Definition agree_regs (F: meminj) (ctx: context) (rs rs': regset) :=
  (forall r, Ple r ctx.(mreg) -> val_inject F rs#r rs'#(sreg ctx r))
/\(forall r, Plt ctx.(mreg) r -> rs#r = Vundef).

Definition val_reg_charact (F: meminj) (ctx: context) (rs': regset) (v: val) (r: reg) :=
  (Plt ctx.(mreg) r /\ v = Vundef) \/ (Ple r ctx.(mreg) /\ val_inject F v rs'#(sreg ctx r)).

Remark Plt_Ple_dec:
  forall p q, {Plt p q} + {Ple q p}.
Proof.
  intros. destruct (plt p q). left; auto. right; xomega.
Qed.

Lemma agree_val_reg_gen:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> val_reg_charact F ctx rs' rs#r r.
Proof.
  intros. destruct H as [A B].
  destruct (Plt_Ple_dec (mreg ctx) r). 
  left. rewrite B; auto. 
  right. auto.
Qed.

Lemma agree_val_regs_gen:
  forall F ctx rs rs' rl,
  agree_regs F ctx rs rs' -> list_forall2 (val_reg_charact F ctx rs') rs##rl rl.
Proof.
  induction rl; intros; constructor; auto. apply agree_val_reg_gen; auto.
Qed.

Lemma agree_val_reg:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> val_inject F rs#r rs'#(sreg ctx r).
Proof.
  intros. exploit agree_val_reg_gen; eauto. instantiate (1 := r). intros [[A B] | [A B]].
  rewrite B; auto.
  auto.
Qed.

Lemma agree_val_regs:
  forall F ctx rs rs' rl, agree_regs F ctx rs rs' -> val_list_inject F rs##rl rs'##(sregs ctx rl).
Proof.
  induction rl; intros; simpl. constructor. constructor; auto. apply agree_val_reg; auto.
Qed.

Lemma agree_set_reg:
  forall F ctx rs rs' r v v',
  agree_regs F ctx rs rs' ->
  val_inject F v v' ->
  Ple r ctx.(mreg) ->
  agree_regs F ctx (rs#r <- v) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec. 
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. unfold sreg; xomega. 
  rewrite Regmap.gso. auto. xomega. 
Qed.

Lemma agree_set_reg_undef:
  forall F ctx rs rs' r v',
  agree_regs F ctx rs rs' ->
  agree_regs F ctx (rs#r <- Vundef) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec. 
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. unfold sreg; xomega.
  rewrite Regmap.gsspec. destruct (peq r0 r); auto. 
Qed.

Lemma agree_set_reg_undef':
  forall F ctx rs rs' r,
  agree_regs F ctx rs rs' ->
  agree_regs F ctx (rs#r <- Vundef) rs'.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite Regmap.gsspec. 
  destruct (peq r0 r). subst r0. auto. auto.
  rewrite Regmap.gsspec. destruct (peq r0 r); auto. 
Qed.

Lemma agree_regs_invariant:
  forall F ctx rs rs1 rs2,
  agree_regs F ctx rs rs1 ->
  (forall r, Plt ctx.(dreg) r -> Ple r (ctx.(dreg) + ctx.(mreg)) -> rs2#r = rs1#r) ->
  agree_regs F ctx rs rs2.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite H0. auto. unfold sreg; xomega. unfold sreg; xomega. 
  apply H1; auto.
Qed.

Lemma agree_regs_incr:
  forall F ctx rs1 rs2 F',
  agree_regs F ctx rs1 rs2 ->
  inject_incr F F' ->
  agree_regs F' ctx rs1 rs2.
Proof.
  intros. destruct H. split; intros. eauto. auto. 
Qed.

Remark agree_regs_init:
  forall F ctx rs, agree_regs F ctx (Regmap.init Vundef) rs.
Proof.
  intros; split; intros. rewrite Regmap.gi; auto. rewrite Regmap.gi; auto. 
Qed.

Lemma agree_regs_init_regs:
  forall F ctx rl vl vl',
  val_list_inject F vl vl' ->
  (forall r, In r rl -> Ple r ctx.(mreg)) ->
  agree_regs F ctx (init_regs vl rl) (init_regs vl' (sregs ctx rl)).
Proof.
  induction rl; simpl; intros.
  apply agree_regs_init.
  inv H. apply agree_regs_init.
  apply agree_set_reg; auto. 
Qed.

(** ** Executing sequences of moves *)

Lemma tr_moves_init_regs:
  forall F stk f sp m ctx1 ctx2, context_below ctx1 ctx2 ->
  forall rdsts rsrcs vl pc1 pc2 rs1,
  tr_moves f.(fn_code) pc1 (sregs ctx1 rsrcs) (sregs ctx2 rdsts) pc2 ->
  (forall r, In r rdsts -> Ple r ctx2.(mreg)) ->
  list_forall2 (val_reg_charact F ctx1 rs1) vl rsrcs ->
  exists rs2,
    star step tge (State stk f sp pc1 rs1 m)
               E0 (State stk f sp pc2 rs2 m)
  /\ agree_regs F ctx2 (init_regs vl rdsts) rs2
  /\ forall r, Ple r ctx2.(dreg) -> rs2#r = rs1#r.
Proof.
  induction rdsts; simpl; intros.
(* rdsts = nil *)
  inv H0. exists rs1; split. apply star_refl. split. apply agree_regs_init. auto.
(* rdsts = a :: rdsts *)
  inv H2. inv H0. 
  exists rs1; split. apply star_refl. split. apply agree_regs_init. auto.
  simpl in H0. inv H0.
  exploit IHrdsts; eauto. intros [rs2 [A [B C]]].
  exists (rs2#(sreg ctx2 a) <- (rs2#(sreg ctx1 b1))).
  split. eapply star_right. eauto. eapply exec_Iop; eauto. traceEq.
  split. destruct H3 as [[P Q] | [P Q]].
  subst a1. eapply agree_set_reg_undef; eauto.
  eapply agree_set_reg; eauto. rewrite C; auto. apply context_below_le; auto.
  intros. rewrite Regmap.gso. auto. apply sym_not_equal. eapply sreg_below_diff; eauto.
  destruct H2; discriminate.
Qed.

(** ** Memory invariants *)

(** A stack location is private if it is not the image of a valid
   location and we have full rights on it. *)

Definition loc_private (F: meminj) (m m': mem) (sp: block) (ofs: Z) : Prop :=
  Mem.perm m' sp ofs Cur Freeable /\
  (forall b delta, F b = Some(sp, delta) -> ~Mem.perm m b (ofs - delta) Max Nonempty).

(** Likewise, for a range of locations. *)

Definition range_private (F: meminj) (m m': mem) (sp: block) (lo hi: Z) : Prop :=
  forall ofs, lo <= ofs < hi -> loc_private F m m' sp ofs.

Lemma range_private_invariant:
  forall F m m' sp lo hi F1 m1 m1',
  range_private F m m' sp lo hi ->
  (forall b delta ofs,
      F1 b = Some(sp, delta) ->
      Mem.perm m1 b ofs Max Nonempty ->
      lo <= ofs + delta < hi ->
      F b = Some(sp, delta) /\ Mem.perm m b ofs Max Nonempty) ->
  (forall ofs, Mem.perm m' sp ofs Cur Freeable -> Mem.perm m1' sp ofs Cur Freeable) ->
  range_private F1 m1 m1' sp lo hi.
Proof.
  intros; red; intros. exploit H; eauto. intros [A B]. split; auto.
  intros; red; intros. exploit H0; eauto. omega. intros [P Q]. 
  eelim B; eauto.
Qed.

Lemma range_private_perms:
  forall F m m' sp lo hi,
  range_private F m m' sp lo hi ->
  Mem.range_perm m' sp lo hi Cur Freeable.
Proof.
  intros; red; intros. eapply H; eauto.
Qed.

Lemma range_private_alloc_left:
  forall F m m' sp' base hi sz m1 sp F1,
  range_private F m m' sp' base hi ->
  Mem.alloc m 0 sz = (m1, sp) ->
  F1 sp = Some(sp', base) ->
  (forall b, b <> sp -> F1 b = F b) ->
  range_private F1 m1 m' sp' (base + Zmax sz 0) hi.
Proof.
  intros; red; intros. 
  exploit (H ofs). generalize (Zmax2 sz 0). omega. intros [A B].
  split; auto. intros; red; intros.
  exploit Mem.perm_alloc_inv; eauto.
  destruct (zeq b sp); intros.
  subst b. rewrite H1 in H4; inv H4. 
  rewrite Zmax_spec in H3. destruct (zlt 0 sz); omega.
  rewrite H2 in H4; auto. eelim B; eauto. 
Qed.

Lemma range_private_free_left:
  forall F m m' sp base sz hi b m1,
  range_private F m m' sp (base + Zmax sz 0) hi ->
  Mem.free m b 0 sz = Some m1 ->
  F b = Some(sp, base) ->
  Mem.inject F m m' ->
  range_private F m1 m' sp base hi.
Proof.
  intros; red; intros. 
  destruct (zlt ofs (base + Zmax sz 0)) as [z|z].
  red; split. 
  replace ofs with ((ofs - base) + base) by omega.
  eapply Mem.perm_inject; eauto.
  eapply Mem.free_range_perm; eauto.
  rewrite Zmax_spec in z. destruct (zlt 0 sz); omega. 
  intros; red; intros. destruct (eq_block b b0).
  subst b0. rewrite H1 in H4; inv H4.
  eelim Mem.perm_free_2; eauto. rewrite Zmax_spec in z. destruct (zlt 0 sz); omega.
  exploit Mem.mi_no_overlap; eauto. 
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.free_range_perm. eauto. 
  instantiate (1 := ofs - base). rewrite Zmax_spec in z. destruct (zlt 0 sz); omega.
  eapply Mem.perm_free_3; eauto. 
  intros [A | A]. congruence. omega. 

  exploit (H ofs). omega. intros [A B]. split. auto.
  intros; red; intros. eelim B; eauto. eapply Mem.perm_free_3; eauto.
Qed.

Lemma range_private_extcall:
  forall F F' m1 m2 m1' m2' sp base hi,
  range_private F m1 m1' sp base hi ->
  (forall b ofs p,
     Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  mem_unchanged_on (loc_out_of_reach F m1) m1' m2' ->
  Mem.inject F m1 m1' ->
  inject_incr F F' ->
  inject_separated F F' m1 m1' ->
  Mem.valid_block m1' sp ->
  range_private F' m2 m2' sp base hi.
Proof.
  intros until hi; intros RP PERM UNCH INJ INCR SEP VB.
  red; intros. exploit RP; eauto. intros [A B].
  destruct UNCH as [U1 U2].
  split. auto. 
  intros. red in SEP. destruct (F b) as [[sp1 delta1] |] eqn:?.
  exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ. 
  red; intros; eelim B; eauto. eapply PERM; eauto. 
  red. destruct (zlt b (Mem.nextblock m1)); auto. 
  exploit Mem.mi_freeblocks; eauto. congruence.
  exploit SEP; eauto. tauto. 
Qed.

(** ** Relating global environments *)

Inductive match_globalenvs (F: meminj) (bound: Z): Prop :=
  | mk_match_globalenvs
      (POS: bound > 0)
      (DOMAIN: forall b, b < bound -> F b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, F b1 = Some(b2, delta) -> b2 < bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> b < bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> b < bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> b < bound).

Lemma find_function_agree:
  forall ros rs fd F ctx rs' bound,
  find_function ge ros rs = Some fd ->
  agree_regs F ctx rs rs' ->
  match_globalenvs F bound ->
  exists fd',
  find_function tge (sros ctx ros) rs' = Some fd' /\ transf_fundef fenv fd = OK fd'.
Proof.
  intros. destruct ros as [r | id]; simpl in *.
  (* register *)
  assert (rs'#(sreg ctx r) = rs#r).
    exploit Genv.find_funct_inv; eauto. intros [b EQ].
    assert (A: val_inject F rs#r rs'#(sreg ctx r)). eapply agree_val_reg; eauto.
    rewrite EQ in A; inv A.
    inv H1. rewrite DOMAIN in H5. inv H5. auto.
    apply FUNCTIONS with fd. 
    rewrite EQ in H; rewrite Genv.find_funct_find_funct_ptr in H. auto.
  rewrite H2. eapply functions_translated; eauto.
  (* symbol *)
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try discriminate.
  eapply function_ptr_translated; eauto.
Qed.

(** ** Relating stacks *)

Inductive match_stacks (F: meminj) (m m': mem):
             list stackframe -> list stackframe -> block -> Prop :=
  | match_stacks_nil: forall bound1 bound
        (MG: match_globalenvs F bound1)
        (BELOW: bound1 <= bound),
      match_stacks F m m' nil nil bound
  | match_stacks_cons: forall res f sp pc rs stk f' sp' rs' stk' bound ctx
        (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs')
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: F sp = Some(sp', ctx.(dstk)))
        (PRIV: range_private F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (RES: Ple res ctx.(mreg))
        (BELOW: sp' < bound),
      match_stacks F m m'
                   (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
                   (Stackframe (sreg ctx res) f' (Vptr sp' Int.zero) (spc ctx pc) rs' :: stk')
                   bound
  | match_stacks_untailcall: forall stk res f' sp' rpc rs' stk' bound ctx
        (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs')
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (RET: ctx.(retinfo) = Some (rpc, res))
        (BELOW: sp' < bound),
      match_stacks F m m'
                   stk
                   (Stackframe res f' (Vptr sp' Int.zero) rpc rs' :: stk')
                   bound

with match_stacks_inside (F: meminj) (m m': mem):
        list stackframe -> list stackframe -> function -> context -> block -> regset -> Prop :=
  | match_stacks_inside_base: forall stk stk' f' ctx sp' rs'
        (MS: match_stacks F m m' stk stk' sp')
        (RET: ctx.(retinfo) = None)
        (DSTK: ctx.(dstk) = 0),
      match_stacks_inside F m m' stk stk' f' ctx sp' rs'
  | match_stacks_inside_inlined: forall res f sp pc rs stk stk' f' ctx sp' rs' ctx'
        (MS: match_stacks_inside F m m' stk stk' f' ctx' sp' rs')
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code))
        (AG: agree_regs F ctx' rs rs')
        (SP: F sp = Some(sp', ctx'.(dstk)))
        (PAD: range_private F m m' sp' (ctx'.(dstk) + ctx'.(mstk)) ctx.(dstk))
        (RES: Ple res ctx'.(mreg))
        (RET: ctx.(retinfo) = Some (spc ctx' pc, sreg ctx' res))
        (BELOW: context_below ctx' ctx)
        (SBELOW: context_stack_call ctx' ctx),
      match_stacks_inside F m m' (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
                                 stk' f' ctx sp' rs'.

(** Properties of match_stacks *)

Section MATCH_STACKS.

Variable F: meminj.
Variables m m': mem.

Lemma match_stacks_globalenvs:
  forall stk stk' bound,
  match_stacks F m m' stk stk' bound -> exists b, match_globalenvs F b
with match_stacks_inside_globalenvs:
  forall stk stk' f ctx sp rs', 
  match_stacks_inside F m m' stk stk' f ctx sp rs' -> exists b, match_globalenvs F b.
Proof.
  induction 1; eauto.
  induction 1; eauto.
Qed.

Lemma match_globalenvs_preserves_globals:
  forall b, match_globalenvs F b -> meminj_preserves_globals ge F.
Proof.
  intros. inv H. red. split. eauto. split. eauto.
  intros. symmetry. eapply IMAGE; eauto.
Qed. 

Lemma match_stacks_inside_globals:
  forall stk stk' f ctx sp rs', 
  match_stacks_inside F m m' stk stk' f ctx sp rs' -> meminj_preserves_globals ge F.
Proof.
  intros. exploit match_stacks_inside_globalenvs; eauto. intros [b A]. 
  eapply match_globalenvs_preserves_globals; eauto.
Qed.

Lemma match_stacks_bound:
  forall stk stk' bound bound1,
  match_stacks F m m' stk stk' bound ->
  bound <= bound1 ->
  match_stacks F m m' stk stk' bound1.
Proof.
  intros. inv H.
  apply match_stacks_nil with bound0. auto. omega.
  eapply match_stacks_cons; eauto. omega.
  eapply match_stacks_untailcall; eauto. omega. 
Qed. 

Variable F1: meminj.
Variables m1 m1': mem.
Hypothesis INCR: inject_incr F F1.

Lemma match_stacks_invariant:
  forall stk stk' bound, match_stacks F m m' stk stk' bound ->
  forall (INJ: forall b1 b2 delta, 
               F1 b1 = Some(b2, delta) -> b2 < bound -> F b1 = Some(b2, delta))
         (PERM1: forall b1 b2 delta ofs,
               F1 b1 = Some(b2, delta) -> b2 < bound ->
               Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
         (PERM2: forall b ofs, b < bound ->
               Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
         (PERM3: forall b ofs k p, b < bound ->
               Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
  match_stacks F1 m1 m1' stk stk' bound

with match_stacks_inside_invariant:
  forall stk stk' f' ctx sp' rs1, 
  match_stacks_inside F m m' stk stk' f' ctx sp' rs1 ->
  forall rs2
         (RS: forall r, Ple r ctx.(dreg) -> rs2#r = rs1#r)
         (INJ: forall b1 b2 delta, 
               F1 b1 = Some(b2, delta) -> b2 <= sp' -> F b1 = Some(b2, delta))
         (PERM1: forall b1 b2 delta ofs,
               F1 b1 = Some(b2, delta) -> b2 <= sp' ->
               Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
         (PERM2: forall b ofs, b <= sp' ->
               Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
         (PERM3: forall b ofs k p, b <= sp' ->
               Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
  match_stacks_inside F1 m1 m1' stk stk' f' ctx sp' rs2.

Proof.
  induction 1; intros.
  (* nil *)
  apply match_stacks_nil with (bound1 := bound1).
  inv MG. constructor; auto. 
  intros. apply IMAGE with delta. eapply INJ; eauto. omega. auto. 
  omega.
  (* cons *)
  apply match_stacks_cons with (ctx := ctx); auto.
  eapply match_stacks_inside_invariant; eauto.
  intros; eapply INJ; eauto; omega.
  intros; eapply PERM1; eauto; omega.
  intros; eapply PERM2; eauto; omega.
  intros; eapply PERM3; eauto; omega.
  eapply agree_regs_incr; eauto.
  eapply range_private_invariant; eauto. 
  (* untailcall *)
  apply match_stacks_untailcall with (ctx := ctx); auto. 
  eapply match_stacks_inside_invariant; eauto.
  intros; eapply INJ; eauto; omega.
  intros; eapply PERM1; eauto; omega.
  intros; eapply PERM2; eauto; omega.
  intros; eapply PERM3; eauto; omega.
  eapply range_private_invariant; eauto. 

  induction 1; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto.
  eapply match_stacks_invariant; eauto. 
  intros; eapply INJ; eauto; omega.
  intros; eapply PERM1; eauto; omega.
  intros; eapply PERM2; eauto; omega.
  intros; eapply PERM3; eauto; omega.
  (* inlined *)
  apply match_stacks_inside_inlined with (ctx' := ctx'); auto. 
  apply IHmatch_stacks_inside; auto.
  intros. apply RS. red in BELOW. xomega. 
  apply agree_regs_incr with F; auto. 
  apply agree_regs_invariant with rs'; auto. 
  intros. apply RS. red in BELOW. xomega. 
  eapply range_private_invariant; eauto.
    intros. split. eapply INJ; eauto. omega. eapply PERM1; eauto. omega.
    intros. eapply PERM2; eauto. omega.
Qed.

Lemma match_stacks_empty:
  forall stk stk' bound,
  match_stacks F m m' stk stk' bound -> stk = nil -> stk' = nil
with match_stacks_inside_empty:
  forall stk stk' f ctx sp rs,
  match_stacks_inside F m m' stk stk' f ctx sp rs -> stk = nil -> stk' = nil /\ ctx.(retinfo) = None.
Proof.
  induction 1; intros.
  auto.
  discriminate.
  exploit match_stacks_inside_empty; eauto. intros [A B]. congruence.
  induction 1; intros.
  split. eapply match_stacks_empty; eauto. auto.
  discriminate.
Qed.

End MATCH_STACKS.

(** Preservation by assignment to a register *)

Lemma match_stacks_inside_set_reg:
  forall F m m' stk stk' f' ctx sp' rs' r v, 
  match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
  match_stacks_inside F m m' stk stk' f' ctx sp' (rs'#(sreg ctx r) <- v).
Proof.
  intros. eapply match_stacks_inside_invariant; eauto. 
  intros. apply Regmap.gso. unfold sreg. xomega. 
Qed.

(** Preservation by a memory store *)

Lemma match_stacks_inside_store:
  forall F m m' stk stk' f' ctx sp' rs' chunk b ofs v m1 chunk' b' ofs' v' m1', 
  match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
  Mem.store chunk m b ofs v = Some m1 ->
  Mem.store chunk' m' b' ofs' v' = Some m1' ->
  match_stacks_inside F m1 m1' stk stk' f' ctx sp' rs'.
Proof.
  intros. 
  eapply match_stacks_inside_invariant; eauto with mem.
Qed.

(** Preservation by an allocation *)

Lemma match_stacks_inside_alloc_left:
  forall F m m' stk stk' f' ctx sp' rs',
  match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
  forall sz m1 b F1 delta,
  Mem.alloc m 0 sz = (m1, b) ->
  inject_incr F F1 ->
  F1 b = Some(sp', delta) ->
  (forall b1, b1 <> b -> F1 b1 = F b1) ->
  delta >= ctx.(dstk) ->
  match_stacks_inside F1 m1 m' stk stk' f' ctx sp' rs'.
Proof.
  induction 1; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto. 
  eapply match_stacks_invariant; eauto.
  intros. destruct (eq_block b1 b).
  subst b1. rewrite H1 in H4; inv H4. omegaContradiction.
  rewrite H2 in H4; auto. 
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (zeq b1 b); intros; auto.
  subst b1. rewrite H1 in H4. inv H4. omegaContradiction.
  (* inlined *)
  eapply match_stacks_inside_inlined; eauto. 
  eapply IHmatch_stacks_inside; eauto. destruct SBELOW. omega. 
  eapply agree_regs_incr; eauto.
  eapply range_private_invariant; eauto. 
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (zeq b0 b); intros.
  subst b0. rewrite H2 in H5; inv H5. omegaContradiction. 
  rewrite H3 in H5; auto. 
Qed.

(** Preservation by freeing *)

Lemma match_stacks_free_left:
  forall F m m' stk stk' sp b lo hi m1,
  match_stacks F m m' stk stk' sp ->
  Mem.free m b lo hi = Some m1 ->
  match_stacks F m1 m' stk stk' sp.
Proof.
  intros. eapply match_stacks_invariant; eauto.
  intros. eapply Mem.perm_free_3; eauto. 
Qed.

Lemma match_stacks_free_right:
  forall F m m' stk stk' sp lo hi m1',
  match_stacks F m m' stk stk' sp ->
  Mem.free m' sp lo hi = Some m1' ->
  match_stacks F m m1' stk stk' sp.
Proof.
  intros. eapply match_stacks_invariant; eauto. 
  intros. eapply Mem.perm_free_1; eauto. left. unfold block; omega.
  intros. eapply Mem.perm_free_3; eauto.
Qed.

Lemma min_alignment_sound:
  forall sz n, (min_alignment sz | n) -> Mem.inj_offset_aligned n sz.
Proof.
  intros; red; intros. unfold min_alignment in H. 
  assert (2 <= sz -> (2 | n)). intros.
    destruct (zle sz 1). omegaContradiction.
    destruct (zle sz 2). auto. 
    destruct (zle sz 4). apply Zdivides_trans with 4; auto. exists 2; auto.
    apply Zdivides_trans with 8; auto. exists 4; auto.
  assert (4 <= sz -> (4 | n)). intros.
    destruct (zle sz 1). omegaContradiction.
    destruct (zle sz 2). omegaContradiction.
    destruct (zle sz 4). auto.
    apply Zdivides_trans with 8; auto. exists 2; auto.
  assert (8 <= sz -> (8 | n)). intros.
    destruct (zle sz 1). omegaContradiction.
    destruct (zle sz 2). omegaContradiction.
    destruct (zle sz 4). omegaContradiction.
    auto.
  destruct chunk; simpl in *; auto.
  apply Zone_divide.
  apply Zone_divide.
  apply H2; omega.
Qed.

(** Preservation by external calls *)

Section EXTCALL.

Variables F1 F2: meminj.
Variables m1 m2 m1' m2': mem.
Hypothesis MAXPERM: forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
Hypothesis MAXPERM': forall b ofs p, Mem.valid_block m1' b -> Mem.perm m2' b ofs Max p -> Mem.perm m1' b ofs Max p.
Hypothesis UNCHANGED: mem_unchanged_on (loc_out_of_reach F1 m1) m1' m2'.
Hypothesis INJ: Mem.inject F1 m1 m1'.
Hypothesis INCR: inject_incr F1 F2.
Hypothesis SEP: inject_separated F1 F2 m1 m1'.

Lemma match_stacks_extcall:
  forall stk stk' bound, 
  match_stacks F1 m1 m1' stk stk' bound ->
  bound <= Mem.nextblock m1' ->
  match_stacks F2 m2 m2' stk stk' bound
with match_stacks_inside_extcall:
  forall stk stk' f' ctx sp' rs',
  match_stacks_inside F1 m1 m1' stk stk' f' ctx sp' rs' ->
  sp' < Mem.nextblock m1' ->
  match_stacks_inside F2 m2 m2' stk stk' f' ctx sp' rs'.
Proof.
  induction 1; intros.
  apply match_stacks_nil with bound1; auto. 
    inv MG. constructor; intros; eauto. 
    destruct (F1 b1) as [[b2' delta']|] eqn:?.
    exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ. eapply IMAGE; eauto. 
    exploit SEP; eauto. intros [A B]. elim B. red. omega. 
  eapply match_stacks_cons; eauto. 
    eapply match_stacks_inside_extcall; eauto. omega. 
    eapply agree_regs_incr; eauto. 
    eapply range_private_extcall; eauto. red; omega. 
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red; omega.
  eapply match_stacks_untailcall; eauto. 
    eapply match_stacks_inside_extcall; eauto. omega. 
    eapply range_private_extcall; eauto. red; omega. 
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red; omega.
  induction 1; intros.
  eapply match_stacks_inside_base; eauto.
    eapply match_stacks_extcall; eauto. omega. 
  eapply match_stacks_inside_inlined; eauto. 
    eapply agree_regs_incr; eauto. 
    eapply range_private_extcall; eauto.
Qed.

End EXTCALL.

(** Change of context corresponding to an inlined tailcall *)

Lemma align_unchanged:
  forall n amount, amount > 0 -> (amount | n) -> align n amount = n.
Proof.
  intros. destruct H0 as [p EQ]. subst n. unfold align. decEq. 
  apply Zdiv_unique with (b := amount - 1). omega. omega.
Qed.

Lemma match_stacks_inside_inlined_tailcall:
  forall F m m' stk stk' f' ctx sp' rs' ctx' f,
  match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
  context_below ctx ctx' ->
  context_stack_tailcall ctx f ctx' ->
  ctx'.(retinfo) = ctx.(retinfo) ->
  range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize) ->
  tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code) ->
  match_stacks_inside F m m' stk stk' f' ctx' sp' rs'.
Proof.
  intros. inv H.
  (* base *)
  eapply match_stacks_inside_base; eauto. congruence. 
  rewrite H1. rewrite DSTK. apply align_unchanged. apply min_alignment_pos. apply Zdivide_0.
  (* inlined *)
  assert (dstk ctx <= dstk ctx'). rewrite H1. apply align_le. apply min_alignment_pos.
  eapply match_stacks_inside_inlined; eauto. 
  red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; omega. apply H3. inv H4. xomega. 
  congruence. 
  unfold context_below in *. xomega.
  unfold context_stack_call in *. omega. 
Qed.

(** ** Relating states *)

Inductive match_states: state -> state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk' f' sp' rs' m' F ctx
        (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs')
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: F sp = Some(sp', ctx.(dstk)))
        (MINJ: Mem.inject F m m')
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states (State stk f (Vptr sp Int.zero) pc rs m)
                   (State stk' f' (Vptr sp' Int.zero) (spc ctx pc) rs' m')
  | match_call_states: forall stk fd args m stk' fd' args' m' F
        (MS: match_stacks F m m' stk stk' (Mem.nextblock m'))
        (FD: transf_fundef fenv fd = OK fd')
        (VINJ: val_list_inject F args args')
        (MINJ: Mem.inject F m m'),
      match_states (Callstate stk fd args m)
                   (Callstate stk' fd' args' m')
  | match_call_regular_states: forall stk f vargs m stk' f' sp' rs' m' F ctx ctx' pc' pc1' rargs
        (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs')
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (BELOW: context_below ctx' ctx)
        (NOP: f'.(fn_code)!pc' = Some(Inop pc1'))
        (MOVES: tr_moves f'.(fn_code) pc1' (sregs ctx' rargs) (sregs ctx f.(fn_params)) (spc ctx f.(fn_entrypoint)))
        (VINJ: list_forall2 (val_reg_charact F ctx' rs') vargs rargs)
        (MINJ: Mem.inject F m m')
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states (Callstate stk (Internal f) vargs m)
                   (State stk' f' (Vptr sp' Int.zero) pc' rs' m')
  | match_return_states: forall stk v m stk' v' m' F
        (MS: match_stacks F m m' stk stk' (Mem.nextblock m'))
        (VINJ: val_inject F v v')
        (MINJ: Mem.inject F m m'),
      match_states (Returnstate stk v m)
                   (Returnstate stk' v' m')
  | match_return_regular_states: forall stk v m stk' f' sp' rs' m' F ctx pc' or rinfo
        (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs')
        (RET: ctx.(retinfo) = Some rinfo)
        (AT: f'.(fn_code)!pc' = Some(inline_return ctx or rinfo))
        (VINJ: match or with None => v = Vundef | Some r => val_inject F v rs'#(sreg ctx r) end)
        (MINJ: Mem.inject F m m')
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states (Returnstate stk v m)
                   (State stk' f' (Vptr sp' Int.zero) pc' rs' m').

(** ** Forward simulation *)

Definition measure (S: state) : nat :=
  match S with
  | State _ _ _ _ _ _ => 1%nat
  | Callstate _ _ _ _ => 0%nat
  | Returnstate _ _ _ => 0%nat
  end.

Lemma tr_funbody_inv:
  forall sz cts f c pc i,
  tr_funbody fenv sz cts f c -> f.(fn_code)!pc = Some i -> tr_instr fenv sz cts pc i c.
Proof.
  intros. inv H. eauto. 
Qed.

Theorem step_simulation:
  forall S1 t S2,
  step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.

(* nop *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  left; econstructor; split. 
  eapply plus_one. eapply exec_Inop; eauto.
  econstructor; eauto.

(* op *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_operation_inject. 
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eexact MINJ. eauto.
  fold (sop ctx op). intros [v' [A B]].
  left; econstructor; split.
  eapply plus_one. eapply exec_Iop; eauto. erewrite eval_operation_preserved; eauto.
  exact symbols_preserved. 
  econstructor; eauto. 
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto. 
  
(* load *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject. 
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold (saddr ctx addr). intros [a' [P Q]].
  exploit Mem.loadv_inject; eauto. intros [v' [U V]].
  assert (eval_addressing tge (Vptr sp' Int.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
  rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
  left; econstructor; split.
  eapply plus_one. eapply exec_Iload; eauto.
  econstructor; eauto. 
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto. 

(* store *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject. 
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold saddr. intros [a' [P Q]].
  exploit Mem.storev_mapped_inject; eauto. eapply agree_val_reg; eauto. 
  intros [m1' [U V]].
  assert (eval_addressing tge (Vptr sp' Int.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
    rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
  left; econstructor; split.
  eapply plus_one. eapply exec_Istore; eauto.
  destruct a; simpl in H1; try discriminate.
  destruct a'; simpl in U; try discriminate.
  econstructor; eauto.
  eapply match_stacks_inside_store; eauto.
  eapply Mem.store_valid_block_1; eauto.
  eapply range_private_invariant; eauto.
  intros; split; auto. eapply Mem.perm_store_2; eauto.
  intros; eapply Mem.perm_store_1; eauto.
  intros. eapply SSZ2. eapply Mem.perm_store_2; eauto.

(* call *)
  exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
  exploit find_function_agree; eauto. intros [fd' [A B]].
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
(* not inlined *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto.
  eapply sig_function_translated; eauto.
  econstructor; eauto.
  eapply match_stacks_cons; eauto. 
  eapply agree_val_regs; eauto. 
(* inlined *)
  assert (fd = Internal f0).
    simpl in H0. destruct (Genv.find_symbol ge id) as [b|] eqn:?; try discriminate.
    exploit (funenv_program_compat prog); eauto. intros. 
    unfold ge in H0. congruence.
  subst fd.
  right; split. simpl; omega. split. auto. 
  econstructor; eauto. 
  eapply match_stacks_inside_inlined; eauto.
  red; intros. apply PRIV. inv H13. destruct H16. xomega.
  apply agree_val_regs_gen; auto.
  red; intros; apply PRIV. destruct H16. omega. 

(* tailcall *)
  exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
  exploit find_function_agree; eauto. intros [fd' [A B]].
  assert (PRIV': range_private F m' m'0 sp' (dstk ctx) f'.(fn_stacksize)).
    eapply range_private_free_left; eauto. inv FB. rewrite <- H4. auto. 
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
(* within the original function *)
  inv MS0; try congruence.
  assert (X: { m1' | Mem.free m'0 sp' 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)). 
    replace ofs with (ofs + dstk ctx) by omega. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. omega.
    inv FB. eapply range_private_perms; eauto. xomega.
  destruct X as [m1' FREE].
  left; econstructor; split.
  eapply plus_one. eapply exec_Itailcall; eauto.
  eapply sig_function_translated; eauto.
  econstructor; eauto.
  eapply match_stacks_bound with (bound := sp'). 
  eapply match_stacks_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto. 
    intros. eapply Mem.perm_free_1; eauto. left; unfold block; omega.
    intros. eapply Mem.perm_free_3; eauto.
  erewrite Mem.nextblock_free; eauto. red in VB; omega.
  eapply agree_val_regs; eauto.
  eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
  (* show that no valid location points into the stack block being freed *)
  intros. rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [P Q]. 
  eelim Q; eauto. replace (ofs + delta - delta) with ofs by omega. 
  apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
(* turned into a call *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto.
  eapply sig_function_translated; eauto.
  econstructor; eauto.
  eapply match_stacks_untailcall; eauto.
  eapply match_stacks_inside_invariant; eauto. 
    intros. eapply Mem.perm_free_3; eauto.
  eapply agree_val_regs; eauto.
  eapply Mem.free_left_inject; eauto.
(* inlined *)
  assert (fd = Internal f0).
    simpl in H0. destruct (Genv.find_symbol ge id) as [b|] eqn:?; try discriminate.
    exploit (funenv_program_compat prog); eauto. intros. 
    unfold ge in H0. congruence.
  subst fd.
  right; split. simpl; omega. split. auto. 
  econstructor; eauto.
  eapply match_stacks_inside_inlined_tailcall; eauto.
  eapply match_stacks_inside_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto.
  apply agree_val_regs_gen; auto.
  eapply Mem.free_left_inject; eauto.
  red; intros; apply PRIV'. 
    assert (dstk ctx <= dstk ctx'). red in H14; rewrite H14. apply align_le. apply min_alignment_pos.
    omega.

(* builtin *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit external_call_mem_inject; eauto. 
    eapply match_stacks_inside_globals; eauto.
    instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto. 
  intros [F1 [v1 [m1' [A [B [C [D [E [J K]]]]]]]]].
  left; econstructor; split.
  eapply plus_one. eapply exec_Ibuiltin; eauto. 
    eapply external_call_symbols_preserved; eauto. 
    exact symbols_preserved. exact varinfo_preserved.
  econstructor.
    eapply match_stacks_inside_set_reg. 
    eapply match_stacks_inside_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto.
    intros; eapply external_call_max_perm; eauto. 
    intros; eapply external_call_max_perm; eauto. 
  auto. 
  eapply agree_set_reg. eapply agree_regs_incr; eauto. auto. auto. 
  apply J; auto.
  auto. 
  eapply external_call_valid_block; eauto. 
  eapply range_private_extcall; eauto. 
    intros; eapply external_call_max_perm; eauto. 
  auto. 
  intros. apply SSZ2. eapply external_call_max_perm; eauto. 

(* cond *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (eval_condition cond rs'##(sregs ctx args) m' = Some b).
    eapply eval_condition_inject; eauto. eapply agree_val_regs; eauto. 
  left; econstructor; split.
  eapply plus_one. eapply exec_Icond; eauto. 
  destruct b; econstructor; eauto. 

(* jumptable *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (val_inject F rs#arg rs'#(sreg ctx arg)). eapply agree_val_reg; eauto.
  rewrite H0 in H2; inv H2. 
  left; econstructor; split.
  eapply plus_one. eapply exec_Ijumptable; eauto.
  rewrite list_nth_z_map. rewrite H1. simpl; reflexivity. 
  econstructor; eauto. 

(* return *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  (* not inlined *)
  inv MS0; try congruence.
  assert (X: { m1' | Mem.free m'0 sp' 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)). 
    replace ofs with (ofs + dstk ctx) by omega. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. omega.
    inv FB. eapply range_private_perms; eauto.
    generalize (Zmax_spec (fn_stacksize f) 0). destruct (zlt 0 (fn_stacksize f)); omega.
  destruct X as [m1' FREE].
  left; econstructor; split.
  eapply plus_one. eapply exec_Ireturn; eauto. 
  econstructor; eauto.
  eapply match_stacks_bound with (bound := sp'). 
  eapply match_stacks_invariant; eauto.
    intros. eapply Mem.perm_free_3; eauto. 
    intros. eapply Mem.perm_free_1; eauto. left; unfold block; omega.
    intros. eapply Mem.perm_free_3; eauto.
  erewrite Mem.nextblock_free; eauto. red in VB; omega.
  destruct or; simpl. apply agree_val_reg; auto. auto.
  eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
  (* show that no valid location points into the stack block being freed *)
  intros. inversion FB; subst.
  assert (PRIV': range_private F m' m'0 sp' (dstk ctx) f'.(fn_stacksize)).
    rewrite H8 in PRIV. eapply range_private_free_left; eauto. 
  rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [A B]. 
  eelim B; eauto. replace (ofs + delta - delta) with ofs by omega. 
  apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.

  (* inlined *)
  right. split. simpl. omega. split. auto. 
  econstructor; eauto.
  eapply match_stacks_inside_invariant; eauto. 
    intros. eapply Mem.perm_free_3; eauto.
  destruct or; simpl. apply agree_val_reg; auto. auto.
  eapply Mem.free_left_inject; eauto.
  inv FB. rewrite H4 in PRIV. eapply range_private_free_left; eauto. 

(* internal function, not inlined *)
  assert (A: exists f', tr_function fenv f f' /\ fd' = Internal f'). 
    Errors.monadInv FD. exists x. split; auto. eapply transf_function_spec; eauto. 
  destruct A as [f' [TR EQ]]. inversion TR; subst.
  exploit Mem.alloc_parallel_inject. eauto. eauto. apply Zle_refl. 
    instantiate (1 := fn_stacksize f'). inv H0. xomega. 
  intros [F' [m1' [sp' [A [B [C [D E]]]]]]].
  left; econstructor; split.
  eapply plus_one. eapply exec_function_internal; eauto.
  rewrite H5. econstructor.
  instantiate (1 := F'). apply match_stacks_inside_base.
  assert (SP: sp' = Mem.nextblock m'0) by (eapply Mem.alloc_result; eauto).
  rewrite <- SP in MS0. 
  eapply match_stacks_invariant; eauto.
    intros. destruct (eq_block b1 stk). 
    subst b1. rewrite D in H7; inv H7. unfold block in *; omegaContradiction.
    rewrite E in H7; auto. 
    intros. exploit Mem.perm_alloc_inv. eexact H. eauto. 
    destruct (zeq b1 stk); intros; auto. 
    subst b1. rewrite D in H7; inv H7. unfold block in *; omegaContradiction.
    intros. eapply Mem.perm_alloc_1; eauto. 
    intros. exploit Mem.perm_alloc_inv. eexact A. eauto. 
    rewrite zeq_false; auto. unfold block; omega.
  auto. auto. auto. 
  rewrite H4. apply agree_regs_init_regs. eauto. auto. inv H0; auto. congruence. auto.
  eapply Mem.valid_new_block; eauto.
  red; intros. split.
  eapply Mem.perm_alloc_2; eauto. inv H0; xomega.
  intros; red; intros. exploit Mem.perm_alloc_inv. eexact H. eauto.
  destruct (zeq b stk); intros. 
  subst. rewrite D in H8; inv H8. inv H0; xomega.
  rewrite E in H8; auto. eelim Mem.fresh_block_alloc. eexact A. eapply Mem.mi_mappedblocks; eauto.
  auto.
  intros. exploit Mem.perm_alloc_inv; eauto. rewrite zeq_true. omega. 

(* internal function, inlined *)
  inversion FB; subst.
  exploit Mem.alloc_left_mapped_inject. 
    eauto.
    eauto.
    (* sp' is valid *)
    instantiate (1 := sp'). auto.
    (* offset is representable *)
    instantiate (1 := dstk ctx). generalize (Zmax2 (fn_stacksize f) 0). omega.
    (* size of target block is representable *)
    intros. right. exploit SSZ2; eauto with mem. inv FB; omega.
    (* we have full permissions on sp' at and above dstk ctx *)
    intros. apply Mem.perm_cur. apply Mem.perm_implies with Freeable; auto with mem.
    eapply range_private_perms; eauto. xomega.
    (* offset is aligned *)
    replace (fn_stacksize f - 0) with (fn_stacksize f) by omega.
    inv FB. apply min_alignment_sound; auto.
    (* nobody maps to (sp, dstk ctx...) *)
    intros. exploit (PRIV (ofs + delta')); eauto. xomega.
    intros [A B]. eelim B; eauto.
    replace (ofs + delta' - delta') with ofs by omega.
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
  intros [F' [A [B [C D]]]].
  exploit tr_moves_init_regs; eauto. intros [rs'' [P [Q R]]].
  left; econstructor; split. 
  eapply plus_left. eapply exec_Inop; eauto. eexact P. traceEq.
  econstructor.
  eapply match_stacks_inside_alloc_left; eauto.
  eapply match_stacks_inside_invariant; eauto.
  omega.
  auto.
  apply agree_regs_incr with F; auto.
  auto. auto. auto.
  rewrite H2. eapply range_private_alloc_left; eauto.
  auto. auto.

(* external function *)
  exploit match_stacks_globalenvs; eauto. intros [bound MG].
  exploit external_call_mem_inject; eauto. 
    eapply match_globalenvs_preserves_globals; eauto.
  intros [F1 [v1 [m1' [A [B [C [D [E [J K]]]]]]]]].
  simpl in FD. inv FD. 
  left; econstructor; split.
  eapply plus_one. eapply exec_function_external; eauto. 
    eapply external_call_symbols_preserved; eauto. 
    exact symbols_preserved. exact varinfo_preserved.
  econstructor.
    eapply match_stacks_bound with (Mem.nextblock m'0).
    eapply match_stacks_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto.
    intros; eapply external_call_max_perm; eauto. 
    intros; eapply external_call_max_perm; eauto.
    omega.
    eapply external_call_nextblock; eauto. 
    auto. auto.

(* return fron noninlined function *)
  inv MS0.
  (* normal case *)
  left; econstructor; split.
  eapply plus_one. eapply exec_return.
  econstructor; eauto. 
  apply match_stacks_inside_set_reg; auto. 
  apply agree_set_reg; auto.
  (* untailcall case *)
  inv MS; try congruence.
  rewrite RET in RET0; inv RET0.
(*
  assert (rpc = pc). unfold spc in H0; unfold node in *; xomega.
  assert (res0 = res). unfold sreg in H1; unfold reg in *; xomega.
  subst rpc res0.
*)
  left; econstructor; split.
  eapply plus_one. eapply exec_return.
  eapply match_regular_states. 
  eapply match_stacks_inside_set_reg; eauto.
  auto. 
  apply agree_set_reg; auto.
  auto. auto. auto.
  red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; omega. apply PRIV; omega.
  auto. auto. 
  
(* return from inlined function *)
  inv MS0; try congruence. rewrite RET0 in RET; inv RET. 
  unfold inline_return in AT. 
  assert (PRIV': range_private F m m' sp' (dstk ctx' + mstk ctx') f'.(fn_stacksize)).
    red; intros. destruct (zlt ofs (dstk ctx)). apply PAD. omega. apply PRIV. omega.
  destruct or.
  (* with a result *)
  left; econstructor; split. 
  eapply plus_one. eapply exec_Iop; eauto. simpl. reflexivity. 
  econstructor; eauto. apply match_stacks_inside_set_reg; auto. apply agree_set_reg; auto.
  (* without a result *)
  left; econstructor; split. 
  eapply plus_one. eapply exec_Inop; eauto.
  econstructor; eauto. subst vres. apply agree_set_reg_undef'; auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 -> exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  exists (Callstate nil tf nil m0); split.
  econstructor; eauto.
    unfold transf_program in TRANSF. eapply Genv.init_mem_transf_partial; eauto.
    rewrite symbols_preserved. 
    rewrite (transform_partial_program_main _ _ TRANSF).  auto.
    rewrite <- H3. apply sig_function_translated; auto. 
  econstructor; eauto. 
  instantiate (1 := Mem.flat_inj (Mem.nextblock m0)). 
  apply match_stacks_nil with (Mem.nextblock m0).
  constructor; intros. 
    apply Mem.nextblock_pos.
    unfold Mem.flat_inj. apply zlt_true; auto. 
    unfold Mem.flat_inj in H. destruct (zlt b1 (Mem.nextblock m0)); congruence.
    eapply Genv.find_symbol_not_fresh; eauto.
    eapply Genv.find_funct_ptr_not_fresh; eauto.
    eapply Genv.find_var_info_not_fresh; eauto. 
    omega.
  eapply Genv.initmem_inject; eauto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H.
  exploit match_stacks_empty; eauto. intros EQ; subst. inv VINJ. constructor.
  exploit match_stacks_inside_empty; eauto. intros [A B]. congruence. 
Qed.

Theorem transf_program_correct:
  forward_simulation (semantics prog) (semantics tprog).
Proof.
  eapply forward_simulation_star.
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact step_simulation. 
Qed.

End INLINING.
