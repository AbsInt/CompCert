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

(** Instruction selection *)

(** The instruction selection pass recognizes opportunities for using
  combined arithmetic and logical operations and addressing modes
  offered by the target processor.  For instance, the expression [x + 1]
  can take advantage of the "immediate add" instruction of the processor,
  and on the PowerPC, the expression [(x >> 6) & 0xFF] can be turned
  into a "rotate and mask" instruction.

  Instruction selection proceeds by bottom-up rewriting over expressions.
  The source language is Cminor and the target language is CminorSel. *)

Require String.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Globalenvs.
Require Import Switch.
Require Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.
Require Import SelectDiv.
Require Import SelectLong.
Require Machregs.

Local Open Scope cminorsel_scope.
Local Open Scope error_monad_scope.

(** Conversion of conditions *)

Function condexpr_of_expr (e: expr) : condexpr :=
  match e with
  | Eop (Ocmp c) el => CEcond c el
  | Econdition a b c => CEcondition a (condexpr_of_expr b) (condexpr_of_expr c)
  | Elet a b => CElet a (condexpr_of_expr b)
  | _ => CEcond (Ccompuimm Cne Int.zero) (e ::: Enil)
  end.

(** Conversion of loads and stores *)

Definition load (chunk: memory_chunk) (e1: expr) :=
  match addressing chunk e1 with
  | (mode, args) => Eload chunk mode args
  end.

Definition store (chunk: memory_chunk) (e1 e2: expr) :=
  match addressing chunk e1 with
  | (mode, args) => Sstore chunk mode args e2
  end.

(** Instruction selection for operator applications.  Most of the work
    is done by the processor-specific smart constructors defined
    in modules [SelectOp] and [SelectLong]. *)

Section SELECTION.

Variable hf: helper_functions.

Definition sel_constant (cst: Cminor.constant) : expr :=
  match cst with
  | Cminor.Ointconst n => Eop (Ointconst n) Enil
  | Cminor.Ofloatconst f => Eop (Ofloatconst f) Enil
  | Cminor.Osingleconst f => Eop (Osingleconst f) Enil
  | Cminor.Olongconst n => longconst n
  | Cminor.Oaddrsymbol id ofs => addrsymbol id ofs
  | Cminor.Oaddrstack ofs => addrstack ofs
  end.

Definition sel_unop (op: Cminor.unary_operation) (arg: expr) : expr :=
  match op with
  | Cminor.Ocast8unsigned => cast8unsigned arg
  | Cminor.Ocast8signed => cast8signed arg
  | Cminor.Ocast16unsigned => cast16unsigned arg
  | Cminor.Ocast16signed => cast16signed arg
  | Cminor.Onegint => negint arg
  | Cminor.Onotint => notint arg
  | Cminor.Onegf => negf arg
  | Cminor.Oabsf => absf arg
  | Cminor.Onegfs => negfs arg
  | Cminor.Oabsfs => absfs arg
  | Cminor.Osingleoffloat => singleoffloat arg
  | Cminor.Ofloatofsingle => floatofsingle arg
  | Cminor.Ointoffloat => intoffloat arg
  | Cminor.Ointuoffloat => intuoffloat arg
  | Cminor.Ofloatofint => floatofint arg
  | Cminor.Ofloatofintu => floatofintu arg
  | Cminor.Ointofsingle => intofsingle arg
  | Cminor.Ointuofsingle => intuofsingle arg
  | Cminor.Osingleofint => singleofint arg
  | Cminor.Osingleofintu => singleofintu arg
  | Cminor.Onegl => negl arg
  | Cminor.Onotl => notl arg
  | Cminor.Ointoflong => intoflong arg
  | Cminor.Olongofint => longofint arg
  | Cminor.Olongofintu => longofintu arg
  | Cminor.Olongoffloat => longoffloat hf arg
  | Cminor.Olonguoffloat => longuoffloat hf arg
  | Cminor.Ofloatoflong => floatoflong hf arg
  | Cminor.Ofloatoflongu => floatoflongu hf arg
  | Cminor.Olongofsingle => longofsingle hf arg
  | Cminor.Olonguofsingle => longuofsingle hf arg
  | Cminor.Osingleoflong => singleoflong hf arg
  | Cminor.Osingleoflongu => singleoflongu hf arg
  end.

Definition sel_binop (op: Cminor.binary_operation) (arg1 arg2: expr) : expr :=
  match op with
  | Cminor.Oadd => add arg1 arg2
  | Cminor.Osub => sub arg1 arg2
  | Cminor.Omul => mul arg1 arg2
  | Cminor.Odiv => divs arg1 arg2
  | Cminor.Odivu => divu arg1 arg2
  | Cminor.Omod => mods arg1 arg2
  | Cminor.Omodu => modu arg1 arg2
  | Cminor.Oand => and arg1 arg2
  | Cminor.Oor => or arg1 arg2
  | Cminor.Oxor => xor arg1 arg2
  | Cminor.Oshl => shl arg1 arg2
  | Cminor.Oshr => shr arg1 arg2
  | Cminor.Oshru => shru arg1 arg2
  | Cminor.Oaddf => addf arg1 arg2
  | Cminor.Osubf => subf arg1 arg2
  | Cminor.Omulf => mulf arg1 arg2
  | Cminor.Odivf => divf arg1 arg2
  | Cminor.Oaddfs => addfs arg1 arg2
  | Cminor.Osubfs => subfs arg1 arg2
  | Cminor.Omulfs => mulfs arg1 arg2
  | Cminor.Odivfs => divfs arg1 arg2
  | Cminor.Oaddl => addl arg1 arg2
  | Cminor.Osubl => subl arg1 arg2
  | Cminor.Omull => mull hf arg1 arg2
  | Cminor.Odivl => divl hf arg1 arg2
  | Cminor.Odivlu => divlu hf arg1 arg2
  | Cminor.Omodl => modl hf arg1 arg2
  | Cminor.Omodlu => modlu hf arg1 arg2
  | Cminor.Oandl => andl arg1 arg2
  | Cminor.Oorl => orl arg1 arg2
  | Cminor.Oxorl => xorl arg1 arg2
  | Cminor.Oshll => shll hf arg1 arg2
  | Cminor.Oshrl => shrl hf arg1 arg2
  | Cminor.Oshrlu => shrlu hf arg1 arg2
  | Cminor.Ocmp c => comp c arg1 arg2
  | Cminor.Ocmpu c => compu c arg1 arg2
  | Cminor.Ocmpf c => compf c arg1 arg2
  | Cminor.Ocmpfs c => compfs c arg1 arg2
  | Cminor.Ocmpl c => cmpl c arg1 arg2
  | Cminor.Ocmplu c => cmplu c arg1 arg2
  end.

(** Conversion from Cminor expression to Cminorsel expressions *)

Fixpoint sel_expr (a: Cminor.expr) : expr :=
  match a with
  | Cminor.Evar id => Evar id
  | Cminor.Econst cst => sel_constant cst
  | Cminor.Eunop op arg => sel_unop op (sel_expr arg)
  | Cminor.Ebinop op arg1 arg2 => sel_binop op (sel_expr arg1) (sel_expr arg2)
  | Cminor.Eload chunk addr => load chunk (sel_expr addr)
  end.

Fixpoint sel_exprlist (al: list Cminor.expr) : exprlist :=
  match al with
  | nil => Enil
  | a :: bl => Econs (sel_expr a) (sel_exprlist bl)
  end.

(** Recognition of immediate calls and calls to built-in functions
    that should be inlined *)

Inductive call_kind : Type :=
  | Call_default
  | Call_imm (id: ident)
  | Call_builtin (ef: external_function).

Definition expr_is_addrof_ident (e: Cminor.expr) : option ident :=
  match e with
  | Cminor.Econst (Cminor.Oaddrsymbol id ofs) =>
      if Int.eq ofs Int.zero then Some id else None
  | _ => None
  end.

Definition classify_call (ge: Cminor.genv) (e: Cminor.expr) : call_kind :=
  match expr_is_addrof_ident e with
  | None => Call_default
  | Some id =>
      match Genv.find_symbol ge id with
      | None => Call_imm id
      | Some b =>
          match Genv.find_funct_ptr ge b with
          | Some(External ef) => if ef_inline ef then Call_builtin ef else Call_imm id
          | _ => Call_imm id
          end
      end
  end.

(** Builtin arguments and results *)

Definition sel_builtin_arg
       (e: Cminor.expr) (c: builtin_arg_constraint): AST.builtin_arg expr :=
  let e' := sel_expr e in
  let ba := builtin_arg e' in
  if builtin_arg_ok ba c then ba else BA e'.

Fixpoint sel_builtin_args
       (el: list Cminor.expr)
       (cl: list builtin_arg_constraint): list (AST.builtin_arg expr) :=
  match el with
  | nil => nil
  | e :: el =>
      sel_builtin_arg e (List.hd OK_default cl) :: sel_builtin_args el (List.tl cl)
  end.

Definition sel_builtin_res (optid: option ident) : builtin_res ident :=
  match optid with
  | None => BR_none
  | Some id => BR id
  end.

(** Conversion of Cminor [switch] statements to decision trees. *)

Parameter compile_switch: Z -> nat -> table -> comptree.

Section SEL_SWITCH.

Variable make_cmp_eq: expr -> Z -> expr.
Variable make_cmp_ltu: expr -> Z -> expr.
Variable make_sub: expr -> Z -> expr.
Variable make_to_int: expr -> expr.

Fixpoint sel_switch (arg: nat) (t: comptree): exitexpr :=
  match t with
  | CTaction act =>
      XEexit act
  | CTifeq key act t' =>
      XEcondition (condexpr_of_expr (make_cmp_eq (Eletvar arg) key))
                  (XEexit act)
                  (sel_switch arg t')
  | CTiflt key t1 t2 =>
      XEcondition (condexpr_of_expr (make_cmp_ltu (Eletvar arg) key))
                  (sel_switch arg t1)
                  (sel_switch arg t2)
  | CTjumptable ofs sz tbl t' =>
      XElet (make_sub (Eletvar arg) ofs)
        (XEcondition (condexpr_of_expr (make_cmp_ltu (Eletvar O) sz))
                     (XEjumptable (make_to_int (Eletvar O)) tbl)
                     (sel_switch (S arg) t'))
  end.

End SEL_SWITCH.

Definition sel_switch_int :=
  sel_switch
    (fun arg n => comp Ceq arg (Eop (Ointconst (Int.repr n)) Enil))
    (fun arg n => compu Clt arg (Eop (Ointconst (Int.repr n)) Enil))
    (fun arg ofs => sub arg (Eop (Ointconst (Int.repr ofs)) Enil))
    (fun arg => arg).

Definition sel_switch_long :=
  sel_switch
    (fun arg n => cmpl Ceq arg (longconst (Int64.repr n)))
    (fun arg n => cmplu Clt arg (longconst (Int64.repr n)))
    (fun arg ofs => subl arg (longconst (Int64.repr ofs)))
    lowlong.

(** Conversion from Cminor statements to Cminorsel statements. *)

Fixpoint sel_stmt (ge: Cminor.genv) (s: Cminor.stmt) : res stmt :=
  match s with
  | Cminor.Sskip => OK Sskip
  | Cminor.Sassign id e => OK (Sassign id (sel_expr e))
  | Cminor.Sstore chunk addr rhs => OK (store chunk (sel_expr addr) (sel_expr rhs))
  | Cminor.Scall optid sg fn args =>
      OK (match classify_call ge fn with
      | Call_default => Scall optid sg (inl _ (sel_expr fn)) (sel_exprlist args)
      | Call_imm id  => Scall optid sg (inr _ id) (sel_exprlist args)
      | Call_builtin ef => Sbuiltin (sel_builtin_res optid) ef
                                    (sel_builtin_args args
                                       (Machregs.builtin_constraints ef))
      end)
  | Cminor.Sbuiltin optid ef args =>
      OK (Sbuiltin (sel_builtin_res optid) ef
                   (sel_builtin_args args (Machregs.builtin_constraints ef)))
  | Cminor.Stailcall sg fn args =>
      OK (match classify_call ge fn with
      | Call_imm id  => Stailcall sg (inr _ id) (sel_exprlist args)
      | _            => Stailcall sg (inl _ (sel_expr fn)) (sel_exprlist args)
      end)
  | Cminor.Sseq s1 s2 =>
      do s1' <- sel_stmt ge s1; do s2' <- sel_stmt ge s2;
      OK (Sseq s1' s2')
  | Cminor.Sifthenelse e ifso ifnot =>
      do ifso' <- sel_stmt ge ifso; do ifnot' <- sel_stmt ge ifnot;
      OK (Sifthenelse (condexpr_of_expr (sel_expr e)) ifso' ifnot')
  | Cminor.Sloop body =>
      do body' <- sel_stmt ge body; OK (Sloop body')
  | Cminor.Sblock body =>
      do body' <- sel_stmt ge body; OK (Sblock body')
  | Cminor.Sexit n => OK (Sexit n)
  | Cminor.Sswitch false e cases dfl =>
      let t := compile_switch Int.modulus dfl cases in
      if validate_switch Int.modulus dfl cases t
      then OK (Sswitch (XElet (sel_expr e) (sel_switch_int O t)))
      else Error (msg "Selection: bad switch (int)")
  | Cminor.Sswitch true e cases dfl =>
      let t := compile_switch Int64.modulus dfl cases in
      if validate_switch Int64.modulus dfl cases t
      then OK (Sswitch (XElet (sel_expr e) (sel_switch_long O t)))
      else Error (msg "Selection: bad switch (long)")
  | Cminor.Sreturn None => OK (Sreturn None)
  | Cminor.Sreturn (Some e) => OK (Sreturn (Some (sel_expr e)))
  | Cminor.Slabel lbl body =>
      do body' <- sel_stmt ge body; OK (Slabel lbl body')
  | Cminor.Sgoto lbl => OK (Sgoto lbl)
  end.

(** Conversion of functions. *)

Definition sel_function (ge: Cminor.genv) (f: Cminor.function) : res function :=
  do body' <- sel_stmt ge f.(Cminor.fn_body);
  OK (mkfunction
        f.(Cminor.fn_sig)
        f.(Cminor.fn_params)
        f.(Cminor.fn_vars)
        f.(Cminor.fn_stackspace)
        body').

Definition sel_fundef (ge: Cminor.genv) (f: Cminor.fundef) : res fundef :=
  transf_partial_fundef (sel_function ge) f.

End SELECTION.

(** Setting up the helper functions. *)

Definition globdef := AST.globdef Cminor.fundef unit.

(** We build a partial mapping from global identifiers to their definitions,
  restricting ourselves to the globals we are interested in, namely
  the external function declarations whose name starts with "__i64_".
  This ensures that the mapping remains small and that [lookup_helper]
  below is efficient. *)

Definition globdef_of_interest (gd: globdef) : bool :=
  match gd with
  | Gfun (External (EF_external name sg)) => String.prefix "__i64_" name
  | _ => false
  end.

Definition record_globdef (globs: PTree.t globdef) (id_gd: ident * globdef) :=
  let (id, gd) := id_gd in
  if globdef_of_interest gd
  then PTree.set id gd globs
  else PTree.remove id globs.

Definition record_globdefs (p: Cminor.program) : PTree.t globdef :=
  List.fold_left record_globdef p.(prog_defs) (PTree.empty _).

Definition lookup_helper_aux
     (name: String.string) (sg: signature) (res: option ident)
     (id: ident) (gd: globdef) :=
  match gd with
  | Gfun (External (EF_external name' sg')) =>
      if String.string_dec name name' && signature_eq sg sg'
      then Some id
      else res
  | _ => res
  end.

Definition lookup_helper (globs: PTree.t globdef)
                         (name: String.string) (sg: signature) : res ident :=
  match PTree.fold (lookup_helper_aux name sg) globs None with
  | Some id => OK id
  | None    => Error (MSG name :: MSG ": missing or incorrect declaration" :: nil)
  end.

Local Open Scope string_scope.

Definition get_helpers (p: Cminor.program) : res helper_functions :=
  let globs := record_globdefs p in
  do i64_dtos <- lookup_helper globs "__i64_dtos" sig_f_l ;
  do i64_dtou <- lookup_helper globs "__i64_dtou" sig_f_l ;
  do i64_stod <- lookup_helper globs "__i64_stod" sig_l_f ;
  do i64_utod <- lookup_helper globs "__i64_utod" sig_l_f ;
  do i64_stof <- lookup_helper globs "__i64_stof" sig_l_s ;
  do i64_utof <- lookup_helper globs "__i64_utof" sig_l_s ;
  do i64_sdiv <- lookup_helper globs "__i64_sdiv" sig_ll_l ;
  do i64_udiv <- lookup_helper globs "__i64_udiv" sig_ll_l ;
  do i64_smod <- lookup_helper globs "__i64_smod" sig_ll_l ;
  do i64_umod <- lookup_helper globs "__i64_umod" sig_ll_l ;
  do i64_shl <- lookup_helper globs "__i64_shl" sig_li_l ;
  do i64_shr <- lookup_helper globs "__i64_shr" sig_li_l ;
  do i64_sar <- lookup_helper globs "__i64_sar" sig_li_l ;
  OK (mk_helper_functions
     i64_dtos i64_dtou i64_stod i64_utod i64_stof i64_utof
     i64_sdiv i64_udiv i64_smod i64_umod
     i64_shl i64_shr i64_sar).

(** Conversion of programs. *)

Definition sel_program (p: Cminor.program) : res program :=
  do hf <- get_helpers p;
  transform_partial_program (sel_fundef hf (Genv.globalenv p)) p.

