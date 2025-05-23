(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria Paris            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Associating semantics to built-in functions *)

From Coq Require Import String.
Require Import Coqlib.
Require Import AST Integers Floats Values Memdata.
Local Open Scope asttyp_scope.

(** This module provides definitions and mechanisms to associate semantics
  with names of built-in functions.

  This module is independent of the target architecture.  Each target
  provides a [Builtins1] module that lists the built-ins semantics
  appropriate for the target.
*)

Definition val_opt_has_rettype (ov: option val) (t: xtype) : Prop :=
  match ov with Some v => Val.has_rettype v t | None => True end.

Definition val_opt_inject (j: meminj) (ov ov': option val) : Prop :=
  match ov, ov' with
  | None, _ => True
  | Some v, Some v' => Val.inject j v v'
  | _, None => False
  end.

(** The semantics of a built-in function is a partial function
  from list of values to values.  
  It must agree with the return type stated in the signature,
  and be compatible with value injections.
*)

Record builtin_sem (tret: xtype) : Type := mkbuiltin {
  bs_sem :> list val -> option val;
  bs_well_typed: forall vl, 
    val_opt_has_rettype (bs_sem vl) tret;
  bs_inject: forall j vl vl',
    Val.inject_list j vl vl' -> val_opt_inject j (bs_sem vl) (bs_sem vl')
}.

(** Builtin functions can be created from functions over values, such as those
  from the [Values.Val] module.  Proofs of well-typedness and compatibility with
  injections must be provided. The constructor functions have names
- [mkbuiltin_vNt] for a [t]otal function of [N] arguments that are [v]alues, or
- [mkbuiltin_vNp] for a [p]artial function of [N] arguments that are [v]alues.
*)

Local Unset Program Cases.

Program Definition mkbuiltin_v1t 
     (tret: xtype) (f: val -> val)
     (WT: forall v1, Val.has_rettype (f v1) tret)
     (INJ: forall j v1 v1', Val.inject j v1 v1' -> Val.inject j (f v1) (f v1')) :=
  mkbuiltin tret (fun vl => match vl with v1 :: nil => Some (f v1) | _ => None end) _ _.
Next Obligation.
  red; destruct vl; auto. destruct vl; auto.
Qed.
Next Obligation.
  red; inv H; auto. inv H1; auto. 
Qed.

Program Definition mkbuiltin_v2t 
     (tret: xtype) (f: val -> val -> val)
     (WT: forall v1 v2, Val.has_rettype (f v1 v2) tret)
     (INJ: forall j v1 v1' v2 v2',
           Val.inject j v1 v1' -> Val.inject j v2 v2' ->
           Val.inject j (f v1 v2) (f v1' v2')) :=
  mkbuiltin tret (fun vl => match vl with v1 :: v2 :: nil => Some (f v1 v2) | _ => None end) _ _.
Next Obligation.
  red; destruct vl; auto. destruct vl; auto. destruct vl; auto.
Qed.
Next Obligation.
  red; inv H; auto. inv H1; auto. inv H2; auto.
Qed.

Program Definition mkbuiltin_v3t 
     (tret: xtype) (f: val -> val -> val -> val)
     (WT: forall v1 v2 v3, Val.has_rettype (f v1 v2 v3) tret)
     (INJ: forall j v1 v1' v2 v2' v3 v3',
           Val.inject j v1 v1' -> Val.inject j v2 v2' -> Val.inject j v3 v3' ->
           Val.inject j (f v1 v2 v3) (f v1' v2' v3')) :=
  mkbuiltin tret (fun vl => match vl with v1 :: v2 :: v3 :: nil => Some (f v1 v2 v3) | _ => None end) _ _.
Next Obligation.
  red; destruct vl; auto. destruct vl; auto. destruct vl; auto. destruct vl; auto.
Qed.
Next Obligation.
  red; inv H; auto. inv H1; auto. inv H2; auto. inv H3; auto.
Qed.

Program Definition mkbuiltin_v1p
     (tret: xtype) (f: val -> option val)
     (WT: forall v1, val_opt_has_rettype (f v1) tret)
     (INJ: forall j v1 v1',
        Val.inject j v1 v1' -> val_opt_inject j (f v1) (f v1')) :=
  mkbuiltin tret (fun vl => match vl with v1 :: nil => f v1 | _ => None end) _ _.
Next Obligation.
  red; destruct vl; auto. destruct vl; auto. apply WT.
Qed.
Next Obligation.
  red; inv H; auto. inv H1; auto. apply INJ; auto. 
Qed.

Program Definition mkbuiltin_v2p
     (tret: xtype) (f: val -> val -> option val)
     (WT: forall v1 v2, val_opt_has_rettype (f v1 v2) tret)
     (INJ: forall j v1 v1' v2 v2',
        Val.inject j v1 v1' -> Val.inject j v2 v2' ->
        val_opt_inject j (f v1 v2) (f v1' v2')) :=
  mkbuiltin tret (fun vl => match vl with v1 :: v2 :: nil => f v1 v2 | _ => None end)  _ _.
Next Obligation.
  red; destruct vl; auto. destruct vl; auto. destruct vl; auto. apply WT.
Qed.
Next Obligation.
  red; inv H; auto. inv H1; auto. inv H2; auto. apply INJ; auto. 
Qed.

(** For numerical functions, involving only integers and floating-point numbers
  but no pointer values, we can automate the proofs of well-typedness and
  of compatibility with injections. *)

(** First we define a mapping from syntactic types ([Tint], [Tfloat], etc) to semantic Coq types. *)

Definition valty (t: typ) : Type :=
  match t with
  | Tint => int
  | Tlong => int64
  | Tfloat => float
  | Tsingle => float32
  | Tany32 | Tany64 => Empty_set (**r no clear semantic meaning *)
  end.

Definition valxty (t: xtype) : Type :=
  match t with
  | Xbool => { n: int | n = Int.zero \/ n = Int.one }
  | Xint8signed => { n: int | n = Int.sign_ext 8 n }
  | Xint8unsigned => { n: int | n = Int.zero_ext 8 n }
  | Xint16signed => { n: int | n = Int.sign_ext 16 n }
  | Xint16unsigned => { n: int | n = Int.zero_ext 16 n }
  | Xint => int
  | Xlong => int64
  | Xfloat => float
  | Xsingle => float32
  | Xptr => Empty_set            (**r not a number *)
  | Xany32 | Xany64 => Empty_set (**r not a number *)
  | Xvoid => unit
  end.

(** We can inject from the numerical type [valxty t] to the value type [val]. *)

Definition inj_num (t: xtype) : valxty t -> val :=
  match t with
  | Xbool | Xint8signed | Xint8unsigned | Xint16signed | Xint16unsigned => fun n => Vint (proj1_sig n)
  | Xint => Vint
  | Xlong => Vlong
  | Xfloat => Vfloat
  | Xsingle => Vsingle
  | _ => fun _ => Vundef
  end.

(** Conversely, we can project a value to the numerical type [valty t]. *)

Definition proj_num {A: Type} (t: typ) (k0: A) (v: val): (valty t -> A) -> A :=
  match t with
  | Tint => fun k1 => match v with Vint n => k1 n | _ => k0 end
  | Tlong => fun k1 => match v with Vlong n => k1 n | _ => k0 end
  | Tfloat => fun k1 => match v with Vfloat n => k1 n | _ => k0 end
  | Tsingle => fun k1 => match v with Vsingle n => k1 n | _ => k0 end
  | Tany32 | Tany64 => fun k1 => k0
  end.

Lemma inj_num_wt: forall t x, Val.has_rettype (inj_num t x) t.
Proof.
  destruct t; intros; simpl; auto; apply proj2_sig.
Qed.

Lemma inj_num_inject: forall j t x, Val.inject j (inj_num t x) (inj_num t x).
Proof.
  destruct t; intros; constructor.
Qed.

Lemma inj_num_opt_wt: forall t x, val_opt_has_rettype (option_map (inj_num t) x) t.
Proof.
  intros. destruct x; simpl. apply inj_num_wt. auto. 
Qed.

Lemma inj_num_opt_inject: forall j t x,
  val_opt_inject j (option_map (inj_num t) x) (option_map (inj_num t) x).
Proof.
  destruct x; simpl. apply inj_num_inject. auto.
Qed.

Lemma proj_num_wt:
  forall tres t k1 v,
  (forall x, Val.has_rettype (k1 x) tres) ->
  Val.has_rettype (proj_num t Vundef v k1) tres.
Proof.
  intros.
  assert (U: Val.has_rettype Vundef tres).
  { destruct tres; exact I. }
  intros. destruct t; simpl; destruct v; auto.
Qed.

Lemma proj_num_inject:
  forall j t k1 v k1' v',
  (forall x, Val.inject j (k1 x) (k1' x)) ->
  Val.inject j v v' -> 
  Val.inject j (proj_num t Vundef v k1) (proj_num t Vundef v' k1').
Proof.
  intros. destruct t; simpl; inv H0; auto.
Qed.

Lemma proj_num_opt_wt:
  forall tres t k0 k1 v,
  k0 = None \/ k0 = Some Vundef ->
  (forall x, val_opt_has_rettype (k1 x) tres) ->
  val_opt_has_rettype (proj_num t k0 v k1) tres.
Proof.
  intros.
  assert (val_opt_has_rettype k0 tres).
  { destruct H; subst k0. exact I. hnf. destruct tres; exact I. }
  destruct t; simpl; destruct v; auto.
Qed.

Lemma proj_num_opt_inject:
  forall j k0 t k1 v k1' v',
  (forall ov, val_opt_inject j k0 ov) ->
  (forall x, val_opt_inject j (k1 x) (k1' x)) ->
  Val.inject j v v' -> 
  val_opt_inject j (proj_num t k0 v k1) (proj_num t k0 v' k1').
Proof.
  intros. destruct t; simpl; inv H1; auto.
Qed.

(** Wrapping numerical functions as built-ins.  The constructor functions
  have names
- [mkbuiltin_nNt] for a [t]otal function of [N] numbers, or
- [mkbuiltin_vNp] for a [p]artial function of [N] numbers.
 *)

Program Definition mkbuiltin_n1t 
    (targ1: typ) (tres: xtype)
    (f: valty targ1 -> valxty tres) :=
  mkbuiltin_v1t tres
    (fun v1 => proj_num targ1 Vundef v1 (fun x => inj_num tres (f x)))
    _ _.
Next Obligation.
  auto using proj_num_wt, inj_num_wt.
Qed.
Next Obligation.
  auto using proj_num_inject, inj_num_inject.
Qed.

Program Definition mkbuiltin_n2t 
    (targ1 targ2: typ) (tres: xtype)
    (f: valty targ1 -> valty targ2 -> valxty tres) :=
  mkbuiltin_v2t tres
    (fun v1 v2 =>
       proj_num targ1 Vundef v1 (fun x1 =>
       proj_num targ2 Vundef v2 (fun x2 => inj_num tres (f x1 x2))))
    _ _.
Next Obligation.
  auto using proj_num_wt, inj_num_wt.
Qed.
Next Obligation.
  auto using proj_num_inject, inj_num_inject.
Qed.

Program Definition mkbuiltin_n3t 
    (targ1 targ2 targ3: typ) (tres: xtype)
    (f: valty targ1 -> valty targ2 -> valty targ3 -> valxty tres) :=
  mkbuiltin_v3t tres
    (fun v1 v2 v3 =>
       proj_num targ1 Vundef v1 (fun x1 =>
       proj_num targ2 Vundef v2 (fun x2 =>
       proj_num targ3 Vundef v3 (fun x3 => inj_num tres (f x1 x2 x3)))))
    _ _.
Next Obligation.
  auto using proj_num_wt, inj_num_wt.
Qed.
Next Obligation.
  auto using proj_num_inject, inj_num_inject.
Qed.

Program Definition mkbuiltin_n1p
    (targ1: typ) (tres: xtype)
    (f: valty targ1 -> option (valxty tres)) :=
  mkbuiltin_v1p tres
    (fun v1 => proj_num targ1 None v1 (fun x => option_map (inj_num tres) (f x)))
    _ _.
Next Obligation.
  auto using proj_num_opt_wt, inj_num_opt_wt.
Qed.
Next Obligation.
  apply proj_num_opt_inject; auto. intros; red; auto. intros; apply inj_num_opt_inject.
Qed.

Program Definition mkbuiltin_n2p
    (targ1 targ2: typ) (tres: xtype)
    (f: valty targ1 -> valty targ2 -> option (valxty tres)) :=
  mkbuiltin_v2p tres
    (fun v1 v2 =>
      proj_num targ1 None v1 (fun x1 =>
      proj_num targ2 None v2 (fun x2 => option_map (inj_num tres) (f x1 x2))))
    _ _.
Next Obligation.
  auto using proj_num_opt_wt, inj_num_opt_wt.
Qed.
Next Obligation.
  apply proj_num_opt_inject; auto. intros; red; auto. intros.
  apply proj_num_opt_inject; auto. intros; red; auto. intros.
  apply inj_num_opt_inject.
Qed.

(** Looking up builtins by name and signature *)

Section LOOKUP.

Context {A: Type} (sig_of: A -> signature).

Fixpoint lookup_builtin (name: string) (sg: signature) (l: list (string * A)) : option A :=
  match l with
  | nil => None
  | (n, b) :: l =>
      if string_dec name n && signature_eq sg (sig_of b)
      then Some b
      else lookup_builtin name sg l
  end.

Lemma lookup_builtin_sig: forall name sg b l,
  lookup_builtin name sg l = Some b -> sig_of b = sg.
Proof.
  induction l as [ | [n b'] l ]; simpl; intros.
- discriminate.
- destruct (string_dec name n && signature_eq sg (sig_of b')) eqn:E.
+ InvBooleans. congruence.
+ auto.
Qed.

End LOOKUP.

(** The standard, platform-independent built-ins *)

Inductive standard_builtin : Type :=
  | BI_select (t: typ)
  | BI_fabs
  | BI_fabsf
  | BI_fsqrt
  | BI_negl
  | BI_addl
  | BI_subl
  | BI_mull
  | BI_i16_bswap
  | BI_i32_bswap
  | BI_i64_bswap
  | BI_unreachable
  | BI_i64_umulh
  | BI_i64_smulh
  | BI_i64_sdiv
  | BI_i64_udiv
  | BI_i64_smod
  | BI_i64_umod
  | BI_i64_shl
  | BI_i64_shr
  | BI_i64_sar
  | BI_i64_dtos
  | BI_i64_dtou
  | BI_i64_stod
  | BI_i64_utod
  | BI_i64_stof
  | BI_i64_utof.

Definition eq_standard_builtin: forall (x y: standard_builtin), {x=y} + {x<>y}.
Proof.
  generalize typ_eq; decide equality.
Defined.

Local Open Scope string_scope.

Definition standard_builtin_table : list (string * standard_builtin) :=
    ("__builtin_sel", BI_select Tint)
 :: ("__builtin_sel", BI_select Tlong)
 :: ("__builtin_sel", BI_select Tfloat)
 :: ("__builtin_sel", BI_select Tsingle)
 :: ("__builtin_fabs", BI_fabs)
 :: ("__builtin_fabsf", BI_fabsf)
 :: ("__builtin_fsqrt", BI_fsqrt)
 :: ("__builtin_sqrt", BI_fsqrt)
 :: ("__builtin_negl", BI_negl)
 :: ("__builtin_addl", BI_addl)
 :: ("__builtin_subl", BI_subl)
 :: ("__builtin_mull", BI_mull)
 :: ("__builtin_bswap16", BI_i16_bswap)
 :: ("__builtin_bswap", BI_i32_bswap)
 :: ("__builtin_bswap32", BI_i32_bswap)
 :: ("__builtin_bswap64", BI_i64_bswap)
 :: ("__builtin_unreachable", BI_unreachable)
 :: ("__compcert_i64_umulh", BI_i64_umulh)
 :: ("__compcert_i64_smulh", BI_i64_smulh)
 :: ("__compcert_i64_sdiv", BI_i64_sdiv)
 :: ("__compcert_i64_udiv", BI_i64_udiv)
 :: ("__compcert_i64_smod", BI_i64_smod)
 :: ("__compcert_i64_umod", BI_i64_umod)
 :: ("__compcert_i64_shl", BI_i64_shl)
 :: ("__compcert_i64_shr", BI_i64_shr)
 :: ("__compcert_i64_sar", BI_i64_sar)
 :: ("__compcert_i64_dtos", BI_i64_dtos)
 :: ("__compcert_i64_dtou", BI_i64_dtou)
 :: ("__compcert_i64_stod", BI_i64_stod)
 :: ("__compcert_i64_utod", BI_i64_utod)
 :: ("__compcert_i64_stof", BI_i64_stof)
 :: ("__compcert_i64_utof", BI_i64_utof)
 :: nil.

Definition standard_builtin_sig (b: standard_builtin) : signature :=
  match b with
  | BI_select t =>
      let t := inj_type t in [Xint; t; t ---> t]
  | BI_fabs | BI_fsqrt =>
      [Xfloat ---> Xfloat]
  | BI_fabsf =>
      [Xsingle ---> Xsingle]
  | BI_negl =>
      [Xlong ---> Xlong]
  | BI_addl | BI_subl | BI_i64_umulh| BI_i64_smulh 
  | BI_i64_sdiv | BI_i64_udiv | BI_i64_smod | BI_i64_umod =>
      [Xlong; Xlong ---> Xlong]
  | BI_mull =>
      [Xint; Xint ---> Xlong]
  | BI_i32_bswap =>
      [Xint ---> Xint]
  | BI_i64_bswap =>
      [Xlong ---> Xlong]
  | BI_i16_bswap =>
      [Xint16unsigned ---> Xint16unsigned]
  | BI_unreachable =>
      mksignature nil Xvoid cc_default
  | BI_i64_shl  | BI_i64_shr | BI_i64_sar =>
      [Xlong; Xint ---> Xlong]
  | BI_i64_dtos | BI_i64_dtou =>
      [Xfloat ---> Xlong]
  | BI_i64_stod | BI_i64_utod =>
      [Xlong ---> Xfloat]
  | BI_i64_stof | BI_i64_utof =>
      [Xlong ---> Xsingle]
  end.

Program Definition standard_builtin_sem (b: standard_builtin) : builtin_sem (sig_res (standard_builtin_sig b)) :=
  match b with
  | BI_select t =>
      mkbuiltin (inj_type t) 
       (fun vargs => match vargs with
          | Vint n :: v1 :: v2 :: nil => Some (Val.normalize (if Int.eq n Int.zero then v2 else v1) t)
          | _ => None
        end) _ _
  | BI_fabs => mkbuiltin_n1t Tfloat Xfloat Float.abs
  | BI_fabsf => mkbuiltin_n1t Tsingle Xsingle Float32.abs
  | BI_fsqrt => mkbuiltin_n1t Tfloat Xfloat Float.sqrt
  | BI_negl => mkbuiltin_n1t Tlong Xlong Int64.neg
  | BI_addl => mkbuiltin_v2t Xlong Val.addl _ _ 
  | BI_subl => mkbuiltin_v2t Xlong Val.subl _ _
  | BI_mull => mkbuiltin_v2t Xlong Val.mull' _ _
  | BI_i16_bswap =>
    mkbuiltin_n1t Tint Xint16unsigned
                  (fun n => Int.repr (decode_int (List.rev (encode_int 2%nat (Int.unsigned n)))))
  | BI_i32_bswap =>
    mkbuiltin_n1t Tint Xint
                  (fun n => Int.repr (decode_int (List.rev (encode_int 4%nat (Int.unsigned n)))))
  | BI_i64_bswap =>
    mkbuiltin_n1t Tlong Xlong
                  (fun n => Int64.repr (decode_int (List.rev (encode_int 8%nat (Int64.unsigned n)))))
  | BI_unreachable => mkbuiltin Xvoid (fun vargs => None) _ _
  | BI_i64_umulh => mkbuiltin_n2t Tlong Tlong Xlong Int64.mulhu
  | BI_i64_smulh => mkbuiltin_n2t Tlong Tlong Xlong Int64.mulhs
  | BI_i64_sdiv => mkbuiltin_v2p Xlong Val.divls _ _
  | BI_i64_udiv => mkbuiltin_v2p Xlong Val.divlu _ _
  | BI_i64_smod => mkbuiltin_v2p Xlong Val.modls _ _
  | BI_i64_umod => mkbuiltin_v2p Xlong Val.modlu _ _
  | BI_i64_shl => mkbuiltin_v2t Xlong Val.shll _ _
  | BI_i64_shr => mkbuiltin_v2t Xlong Val.shrlu _ _
  | BI_i64_sar => mkbuiltin_v2t Xlong Val.shrl _ _
  | BI_i64_dtos => mkbuiltin_n1p Tfloat Xlong Float.to_long
  | BI_i64_dtou => mkbuiltin_n1p Tfloat Xlong Float.to_longu
  | BI_i64_stod => mkbuiltin_n1t Tlong Xfloat Float.of_long
  | BI_i64_utod => mkbuiltin_n1t Tlong Xfloat Float.of_longu
  | BI_i64_stof => mkbuiltin_n1t Tlong Xsingle Float32.of_long
  | BI_i64_utof => mkbuiltin_n1t Tlong Xsingle Float32.of_longu
  end.
Next Obligation. 
  red. destruct vl; auto. destruct v; auto. 
  destruct vl; auto. destruct vl; auto. destruct vl; auto.
  apply Val.has_inj_type. apply Val.normalize_type.
Qed.
Next Obligation.
  red. inv H; auto. inv H0; auto. inv H1; auto. inv H0; auto. inv H2; auto.
  apply Val.normalize_inject. destruct (Int.eq i Int.zero); auto.
Qed.
Next Obligation.
  unfold Val.addl, Val.has_type; destruct v1; auto; destruct v2; auto; destruct Archi.ptr64; auto.
Qed.
Next Obligation.
  apply Val.addl_inject; auto.
Qed.   
Next Obligation.
  unfold Val.subl, Val.has_type, negb; destruct v1; auto; destruct v2; auto;
  destruct Archi.ptr64; auto; destruct (eq_block b0 b1); auto.
Qed.
Next Obligation.
  apply Val.subl_inject; auto.
Qed.
Next Obligation.
  unfold Val.mull', Val.has_type; destruct v1; simpl; auto; destruct v2; auto.
Qed.
Next Obligation.
  inv H; simpl; auto. inv H0; auto.
Qed.
Next Obligation.
  set (bl := rev (encode_int 2 (Int.unsigned n))).
  set (x := decode_int bl).
  assert (length bl = 2%nat).
  { unfold bl. rewrite List.rev_length. apply encode_int_length. }
  assert (0 <= x < two_p 16).
  { generalize (int_of_bytes_range (rev_if_be bl)). rewrite rev_if_be_length, H. auto. }
  assert (two_p 16 < Int.max_unsigned) by (compute; auto).
  apply Int.eqm_samerepr. rewrite Int.unsigned_repr by lia. rewrite Zbits.Zzero_ext_mod by lia.
  apply Int.eqm_refl2. rewrite Z.mod_small; auto.
Qed.
Next Obligation.
  red. destruct v1; simpl; auto. destruct v2; auto. destruct orb; exact I.
Qed.
Next Obligation.
  red. inv H; simpl; auto. inv H0; auto. destruct orb; auto.
Qed.
Next Obligation.
  red. destruct v1; simpl; auto. destruct v2; auto. destruct Int64.eq; exact I.
Qed.
Next Obligation.
  red. inv H; simpl; auto. inv H0; auto. destruct Int64.eq; auto.
Qed.
Next Obligation.
  red. destruct v1; simpl; auto. destruct v2; auto. destruct orb; exact I.
Qed.
Next Obligation.
  red. inv H; simpl; auto. inv H0; auto. destruct orb; auto.
Qed.
Next Obligation.
  red. destruct v1; simpl; auto. destruct v2; auto. destruct Int64.eq; exact I.
Qed.
Next Obligation.
  red. inv H; simpl; auto. inv H0; auto. destruct Int64.eq; auto.
Qed.
Next Obligation.
  red. destruct v1; simpl; auto. destruct v2; auto. destruct Int.ltu; auto.
Qed.
Next Obligation.
  inv H; simpl; auto. inv H0; auto. destruct Int.ltu; auto.
Qed.
Next Obligation.
  red. destruct v1; simpl; auto. destruct v2; auto. destruct Int.ltu; auto.
Qed.
Next Obligation.
  inv H; simpl; auto. inv H0; auto. destruct Int.ltu; auto.
Qed.
Next Obligation.
  red. destruct v1; simpl; auto. destruct v2; auto. destruct Int.ltu; auto.
Qed.
Next Obligation.
  inv H; simpl; auto. inv H0; auto. destruct Int.ltu; auto.
Qed.

