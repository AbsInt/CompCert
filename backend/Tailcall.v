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

(** Recognition of tail calls. *)

Require Import Coqlib.
Require Import Maps.
Require Import Compopts.
Require Import AST.
Require Import Registers.
Require Import Op.
Require Import RTL.
Require Import Conventions.

(** An [Icall] instruction that stores its result in register [rreg]
  can be turned into a tail call if:
- its successor is a [Ireturn None] or [Ireturn (Some rreg)] instruction;
- the stack block of the current function is empty: [stacksize = 0].

If the current function had a non-empty stack block, it could be that
the called function accesses it, for instance if a pointer into the
stack block is passed as an argument.  In this case, it would be 
semantically incorrect to deallocate the stack block before the call,
as [Itailcall] does.  Therefore, the optimization can only be performed if
the stack block of the current function is empty, in which case it makes
no semantic difference to deallocate it before or after the call.

Another complication is that the [Ireturn] instruction does not, in general,
follow immediately the [Icall] instruction: the RTL code generator
can have inserted moves and no-ops between these instructions.
The general pattern we recognize is therefore:
<<
       r1 <- call(....)
       nop
       r2 <- r1
       r3 <- r2
       return r3
>>
The [is_return] function below recognizes this pattern.
*)

Fixpoint is_return (n: nat) (f: function) (pc: node) (rret: reg) 
                   {struct n}: bool :=
  match n with
  | O => false
  | S n' =>
      match f.(fn_code)!pc with
      | Some(Ireturn None) => true
      | Some(Ireturn (Some r)) => Reg.eq r rret
      | Some(Inop s) => is_return n' f s rret
      | Some(Iop op args dst s) =>
          match is_move_operation op args with
          | None => false
          | Some src =>
              if Reg.eq rret src
              then is_return n' f s dst
              else false
          end
      | _ => false
      end
  end.

(** To ensure termination, we bound arbitrarily the number of iterations
of the [is_return] function: we look ahead for a nop/move/return of length
at most [niter] instructions. *)

Definition niter := 5%nat.

(** The code transformation is straightforward: call instructions
  followed by an appropriate nop/move/return sequence become
  tail calls; other instructions are unchanged.

  To ensure that the resulting RTL code is well typed, we
  restrict the transformation to the cases where a tail call is
  allowed by the calling conventions, and where the result signatures
  match. *)

Definition transf_instr (f: function) (pc: node) (instr: instruction) :=
  match instr with
  | Icall sig ros args res s =>
      if is_return niter f s res
      && tailcall_is_possible sig
      && opt_typ_eq sig.(sig_res) f.(fn_sig).(sig_res)
      then Itailcall sig ros args
      else instr
  | _ => instr
  end.

(** A function is transformed only if its stack block is empty,
  as explained above.  Moreover, we can turn tail calls off
  using a compilation option. *)

Definition transf_function (f: function) : function :=
  if zeq f.(fn_stacksize) 0 && eliminate_tailcalls tt
  then RTL.transf_function (transf_instr f) f
  else f.

Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.
