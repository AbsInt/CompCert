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

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Globalenvs.
Require Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.

Open Local Scope cminorsel_scope.

(** Conversion of conditions *)

Function condition_of_expr (e: expr) : condition * exprlist :=
  match e with
  | Eop (Ocmp c) el => (c, el)
  | _ => (Ccompuimm Cne Int.zero, e ::: Enil)
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
    in module [SelectOp]. *)

Definition sel_constant (cst: Cminor.constant) : expr :=
  match cst with
  | Cminor.Ointconst n => Eop (Ointconst n) Enil
  | Cminor.Ofloatconst f => Eop (Ofloatconst f) Enil
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
  | Cminor.Osingleoffloat => singleoffloat arg
  | Cminor.Ointoffloat => intoffloat arg
  | Cminor.Ointuoffloat => intuoffloat arg
  | Cminor.Ofloatofint => floatofint arg
  | Cminor.Ofloatofintu => floatofintu arg
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
  | Cminor.Ocmp c => comp c arg1 arg2
  | Cminor.Ocmpu c => compu c arg1 arg2
  | Cminor.Ocmpf c => compf c arg1 arg2
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

(** Conversion from Cminor statements to Cminorsel statements. *)

Fixpoint sel_stmt (ge: Cminor.genv) (s: Cminor.stmt) : stmt :=
  match s with
  | Cminor.Sskip => Sskip
  | Cminor.Sassign id e => Sassign id (sel_expr e)
  | Cminor.Sstore chunk addr rhs => store chunk (sel_expr addr) (sel_expr rhs)
  | Cminor.Scall optid sg fn args =>
      match classify_call ge fn with
      | Call_default => Scall optid sg (inl _ (sel_expr fn)) (sel_exprlist args)
      | Call_imm id  => Scall optid sg (inr _ id) (sel_exprlist args)
      | Call_builtin ef => Sbuiltin optid ef (sel_exprlist args)
      end
  | Cminor.Sbuiltin optid ef args =>
      Sbuiltin optid ef (sel_exprlist args)
  | Cminor.Stailcall sg fn args => 
      match classify_call ge fn with
      | Call_imm id  => Stailcall sg (inr _ id) (sel_exprlist args)
      | _            => Stailcall sg (inl _ (sel_expr fn)) (sel_exprlist args)
      end
  | Cminor.Sseq s1 s2 => Sseq (sel_stmt ge s1) (sel_stmt ge s2)
  | Cminor.Sifthenelse e ifso ifnot =>
      let (cond, args) := condition_of_expr (sel_expr e) in
      Sifthenelse cond args (sel_stmt ge ifso) (sel_stmt ge ifnot)
  | Cminor.Sloop body => Sloop (sel_stmt ge body)
  | Cminor.Sblock body => Sblock (sel_stmt ge body)
  | Cminor.Sexit n => Sexit n
  | Cminor.Sswitch e cases dfl => Sswitch (sel_expr e) cases dfl
  | Cminor.Sreturn None => Sreturn None
  | Cminor.Sreturn (Some e) => Sreturn (Some (sel_expr e))
  | Cminor.Slabel lbl body => Slabel lbl (sel_stmt ge body)
  | Cminor.Sgoto lbl => Sgoto lbl
  end.

(** Conversion of functions and programs. *)

Definition sel_function (ge: Cminor.genv) (f: Cminor.function) : function :=
  mkfunction
    f.(Cminor.fn_sig)
    f.(Cminor.fn_params)
    f.(Cminor.fn_vars)
    f.(Cminor.fn_stackspace)
    (sel_stmt ge f.(Cminor.fn_body)).

Definition sel_fundef (ge: Cminor.genv) (f: Cminor.fundef) : fundef :=
  transf_fundef (sel_function ge) f.

Definition sel_program (p: Cminor.program) : program :=
  let ge := Genv.globalenv p in
  transform_program (sel_fundef ge) p.



