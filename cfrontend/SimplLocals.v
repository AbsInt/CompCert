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

(** Pulling local scalar variables whose address is not taken
  into temporary variables. *)

Require Import FSets.
Require FSetAVL.
Require Import Coqlib Ordered Errors.
Require Import AST Linking.
Require Import Ctypes Cop Clight.
Require Compopts.

Open Scope error_monad_scope.
Open Scope string_scope.
Open Scope list_scope.

Module VSet := FSetAVL.Make(OrderedPositive).

(** The set of local variables that can be lifted to temporaries,
  because they are scalar and their address is not taken. *)

Definition compilenv := VSet.t.

Definition is_liftable_var (cenv: compilenv) (a: expr) : option ident :=
  match a with
  | Evar id ty => if VSet.mem id cenv then Some id else None
  | _ => None
  end.

(** Smart constructor for casts *)

Definition make_cast (a: expr) (tto: type) : expr :=
  match classify_cast (typeof a) tto with
  | cast_case_pointer => a
  | cast_case_i2i I32 _ => a
  | cast_case_f2f => a
  | cast_case_s2s => a
  | cast_case_l2l => a
  | cast_case_struct _ _ => a
  | cast_case_union _ _ => a
  | cast_case_void => a
  | _ => Ecast a tto
  end.

(** Insertion of debug annotations *)

Definition Sdebug_temp (id: ident) (ty: type) :=
  Sbuiltin None (EF_debug 2%positive id (typ_of_type ty :: nil))
                (Tcons (typeconv ty) Tnil)
                (Etempvar id ty :: nil).

Definition Sdebug_var (id: ident) (ty: type) :=
  Sbuiltin None (EF_debug 5%positive id (AST.Tptr :: nil))
                (Tcons (Tpointer ty noattr) Tnil)
                (Eaddrof (Evar id ty) (Tpointer ty noattr) :: nil).

Definition Sset_debug (id: ident) (ty: type) (a: expr) :=
  if Compopts.debug tt
  then Ssequence (Sset id (make_cast a ty)) (Sdebug_temp id ty)
  else Sset id (make_cast a ty).

(** Rewriting of expressions and statements. *)

Fixpoint simpl_expr (cenv: compilenv) (a: expr) : expr :=
  match a with
  | Econst_int _ _ => a
  | Econst_float _ _ => a
  | Econst_single _ _ => a
  | Econst_long _ _ => a
  | Evar id ty => if VSet.mem id cenv then Etempvar id ty else Evar id ty
  | Etempvar id ty => Etempvar id ty
  | Ederef a1 ty => Ederef (simpl_expr cenv a1) ty
  | Eaddrof a1 ty => Eaddrof (simpl_expr cenv a1) ty
  | Eunop op a1 ty => Eunop op (simpl_expr cenv a1) ty
  | Ebinop op a1 a2 ty => Ebinop op (simpl_expr cenv a1) (simpl_expr cenv a2) ty
  | Ecast a1 ty => Ecast (simpl_expr cenv a1) ty
  | Efield a1 fld ty => Efield (simpl_expr cenv a1) fld ty
  | Esizeof _ _ => a
  | Ealignof _ _ => a
  end.

Definition simpl_exprlist (cenv: compilenv) (al: list expr) : list expr :=
  List.map (simpl_expr cenv) al.

Definition check_temp (cenv: compilenv) (id: ident) : res unit :=
  if VSet.mem id cenv
  then Error (MSG "bad temporary " :: CTX id :: nil)
  else OK tt.

Definition check_opttemp (cenv: compilenv) (optid: option ident) : res unit :=
  match optid with
  | Some id => check_temp cenv id
  | None => OK tt
  end.

Fixpoint simpl_stmt (cenv: compilenv) (s: statement) : res statement :=
  match s with
  | Sskip => OK Sskip
  | Sassign a1 a2 =>
      match is_liftable_var cenv a1 with
      | Some id =>
          OK (Sset_debug id (typeof a1) (simpl_expr cenv a2))
      | None =>
          OK (Sassign (simpl_expr cenv a1) (simpl_expr cenv a2))
      end
  | Sset id a =>
      do x <- check_temp cenv id;
      OK (Sset id (simpl_expr cenv a))
  | Scall optid a al =>
      do x <- check_opttemp cenv optid;
      OK (Scall optid (simpl_expr cenv a) (simpl_exprlist cenv al))
  | Sbuiltin optid ef tyargs al =>
      do x <- check_opttemp cenv optid;
      OK (Sbuiltin optid ef tyargs (simpl_exprlist cenv al))
  | Ssequence s1 s2 =>
      do s1' <- simpl_stmt cenv s1;
      do s2' <- simpl_stmt cenv s2;
      OK (Ssequence s1' s2')
  | Sifthenelse a s1 s2 =>
      do s1' <- simpl_stmt cenv s1;
      do s2' <- simpl_stmt cenv s2;
      OK (Sifthenelse (simpl_expr cenv a) s1' s2')
  | Sloop s1 s2 =>
      do s1' <- simpl_stmt cenv s1;
      do s2' <- simpl_stmt cenv s2;
      OK (Sloop s1' s2')
  | Sbreak => OK Sbreak
  | Scontinue => OK Scontinue
  | Sreturn opta => OK (Sreturn (option_map (simpl_expr cenv) opta))
  | Sswitch a ls =>
      do ls' <- simpl_lblstmt cenv ls;
      OK (Sswitch (simpl_expr cenv a) ls')
  | Slabel lbl s =>
      do s' <- simpl_stmt cenv s;
      OK (Slabel lbl s')
  | Sgoto lbl => OK (Sgoto lbl)
  end

with simpl_lblstmt (cenv: compilenv) (ls: labeled_statements) : res labeled_statements :=
  match ls with
  | LSnil =>
      OK LSnil
  | LScons c s ls1 =>
      do s' <- simpl_stmt cenv s;
      do ls1' <- simpl_lblstmt cenv ls1;
      OK (LScons c s' ls1')
  end.

(** Function parameters that are not lifted to temporaries must be
  stored in the corresponding local variable at function entry. *)

Fixpoint store_params (cenv: compilenv) (params: list (ident * type))
                      (s: statement): statement :=
  match params with
  | nil => s
  | (id, ty) :: params' =>
      if VSet.mem id cenv
      then store_params cenv params' s
      else Ssequence (Sassign (Evar id ty) (Etempvar id ty))
                     (store_params cenv params' s)
  end.

(** Compute the set of variables whose address is taken *)

Fixpoint addr_taken_expr (a: expr): VSet.t :=
  match a with
  | Econst_int _ _ => VSet.empty
  | Econst_float _ _ => VSet.empty
  | Econst_single _ _ => VSet.empty
  | Econst_long _ _ => VSet.empty
  | Evar id ty => VSet.empty
  | Etempvar id ty => VSet.empty
  | Ederef a1 ty => addr_taken_expr a1
  | Eaddrof (Evar id ty1) ty => VSet.singleton id
  | Eaddrof a1 ty => addr_taken_expr a1
  | Eunop op a1 ty => addr_taken_expr a1
  | Ebinop op a1 a2 ty => VSet.union (addr_taken_expr a1) (addr_taken_expr a2)
  | Ecast a1 ty => addr_taken_expr a1
  | Efield a1 fld ty => addr_taken_expr a1
  | Esizeof _ _ => VSet.empty
  | Ealignof _ _ => VSet.empty
  end.

Fixpoint addr_taken_exprlist (l: list expr) : VSet.t :=
  match l with
  | nil => VSet.empty
  | a :: l' => VSet.union (addr_taken_expr a) (addr_taken_exprlist l')
  end.

Fixpoint addr_taken_stmt (s: statement) : VSet.t :=
  match s with
  | Sskip => VSet.empty
  | Sassign a b => VSet.union (addr_taken_expr a) (addr_taken_expr b)
  | Sset id a => addr_taken_expr a
  | Scall optid a bl => VSet.union (addr_taken_expr a) (addr_taken_exprlist bl)
  | Sbuiltin optid ef tyargs bl => addr_taken_exprlist bl
  | Ssequence s1 s2 => VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)
  | Sifthenelse a s1 s2 =>
      VSet.union (addr_taken_expr a) (VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2))
  | Sloop s1 s2 => VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)
  | Sbreak => VSet.empty
  | Scontinue => VSet.empty
  | Sreturn None => VSet.empty
  | Sreturn (Some a) => addr_taken_expr a
  | Sswitch a ls => VSet.union (addr_taken_expr a) (addr_taken_lblstmt ls)
  | Slabel lbl s => addr_taken_stmt s
  | Sgoto lbl => VSet.empty
  end

with addr_taken_lblstmt (ls: labeled_statements) : VSet.t :=
  match ls with
  | LSnil => VSet.empty
  | LScons c s ls' => VSet.union (addr_taken_stmt s) (addr_taken_lblstmt ls')
  end.

(** The compilation environment for a function is the set of local variables
  that are scalars and whose addresses are not taken. *)

Definition add_local_variable (atk: VSet.t) (id_ty: ident * type)
                              (cenv: compilenv) : compilenv :=
  let (id, ty) := id_ty in
  match access_mode ty with
  | By_value chunk => if VSet.mem id atk then cenv else VSet.add id cenv
  | _ => cenv
  end.

Definition cenv_for (f: function) : compilenv :=
  let atk := addr_taken_stmt f.(fn_body) in
  List.fold_right (add_local_variable atk) VSet.empty (f.(fn_params) ++ f.(fn_vars)).

(** Transform a function *)

Definition add_debug_var (id_ty: ident * type) (s: statement) :=
  let (id, ty) := id_ty in Ssequence (Sdebug_var id ty) s.

Definition add_debug_vars (vars: list (ident * type)) (s: statement) :=
  if Compopts.debug tt
  then List.fold_right add_debug_var s vars
  else s.

Definition add_debug_param (id_ty: ident * type) (s: statement) :=
  let (id, ty) := id_ty in Ssequence (Sdebug_temp id ty) s.

Definition add_debug_params (params: list (ident * type)) (s: statement) :=
  if Compopts.debug tt
  then List.fold_right add_debug_param s params
  else s.

Definition remove_lifted (cenv: compilenv) (vars: list (ident * type)) :=
  List.filter (fun id_ty => negb (VSet.mem (fst id_ty) cenv)) vars.

Definition add_lifted (cenv: compilenv) (vars1 vars2: list (ident * type)) :=
  List.filter (fun id_ty => VSet.mem (fst id_ty) cenv) vars1 ++ vars2.

Definition transf_function (f: function) : res function :=
  let cenv := cenv_for f in
  assertion (list_disjoint_dec ident_eq (var_names f.(fn_params)) (var_names f.(fn_temps)));
  do body' <- simpl_stmt cenv f.(fn_body);
  let vars' := remove_lifted cenv (f.(fn_params) ++ f.(fn_vars)) in
  let temps' := add_lifted cenv f.(fn_vars) f.(fn_temps) in
  OK {| fn_return := f.(fn_return);
        fn_callconv := f.(fn_callconv);
        fn_params := f.(fn_params);
        fn_vars := vars';
        fn_temps := temps';
        fn_body := add_debug_params f.(fn_params)
                      (store_params cenv f.(fn_params)
                        (add_debug_vars vars' body')) |}.

(** Whole-program transformation *)

Definition transf_fundef (fd: fundef) : res fundef :=
  match fd with
  | Internal f => do tf <- transf_function f; OK (Internal tf)
  | External ef targs tres cconv => OK (External ef targs tres cconv)
  end.

Definition transf_program (p: program) : res program :=
  do p1 <- AST.transform_partial_program transf_fundef p;
  OK {| prog_defs := AST.prog_defs p1;
        prog_public := AST.prog_public p1;
        prog_main := AST.prog_main p1;
        prog_types := prog_types p;
        prog_comp_env := prog_comp_env p;
        prog_comp_env_eq := prog_comp_env_eq p |}.
