(** Translation from Csharpminor to Cminor. *)

Require Import Coqlib.
Require Import Maps.
Require Import Sets. 
Require Import AST.
Require Import Integers.
Require Mem.
Require Import Csharpminor.
Require Import Op.
Require Import Cminor.
Require Cmconstr.

(** The main task in translating Csharpminor to Cminor is to explicitly
  stack-allocate local variables whose address is taken: these local
  variables become sub-blocks of the Cminor stack data block for the
  current function.  Taking the address of such a variable becomes
  a [Oaddrstack] operation with the corresponding offset.  Accessing
  or assigning such a variable becomes a load or store operation at
  that address.  Only scalar local variables whose address is never
  taken in the Csharpminor code can be mapped to Cminor local
  variable, since the latter do not reside in memory.  

  Other tasks performed during the translation to Cminor:
- Transformation of Csharpminor's standard set of operators and
  trivial addressing modes to Cminor's processor-dependent operators
  and addressing modes.  This is done using the optimizing Cminor
  constructor functions provided in file [Cmconstr], therefore performing
  instruction selection on the fly.
- Insertion of truncation, zero- and sign-extension operations when
  assigning to a Csharpminor local variable of ``small'' type
  (e.g. [Mfloat32] or [Mint8signed]).  This is necessary to preserve
  the ``normalize at assignment-time'' semantics of Csharpminor.
*)

(** Translation of operators. *)

Definition make_op (op: Csharpminor.operation) (el: exprlist): option expr :=
  match el with
  | Enil =>
      match op with
      | Csharpminor.Ointconst n => Some(Eop (Ointconst n) Enil)
      | Csharpminor.Ofloatconst n => Some(Eop (Ofloatconst n) Enil)
      | _ => None
      end
  | Econs e1 Enil =>
      match op with
      | Csharpminor.Ocast8unsigned => Some(Cmconstr.cast8unsigned e1)
      | Csharpminor.Ocast8signed => Some(Cmconstr.cast8signed e1)
      | Csharpminor.Ocast16unsigned => Some(Cmconstr.cast16unsigned e1)
      | Csharpminor.Ocast16signed => Some(Cmconstr.cast16signed e1)
      | Csharpminor.Onotint => Some(Cmconstr.notint e1)
      | Csharpminor.Onegf => Some(Cmconstr.negfloat e1)
      | Csharpminor.Oabsf => Some(Cmconstr.absfloat e1)
      | Csharpminor.Osingleoffloat => Some(Cmconstr.singleoffloat e1)
      | Csharpminor.Ointoffloat => Some(Cmconstr.intoffloat e1)
      | Csharpminor.Ofloatofint => Some(Cmconstr.floatofint e1)
      | Csharpminor.Ofloatofintu => Some(Cmconstr.floatofintu e1)
      | _ => None
      end
  | Econs e1 (Econs e2 Enil) =>
      match op with
      | Csharpminor.Oadd => Some(Cmconstr.add e1 e2)
      | Csharpminor.Osub => Some(Cmconstr.sub e1 e2)
      | Csharpminor.Omul => Some(Cmconstr.mul e1 e2)
      | Csharpminor.Odiv => Some(Cmconstr.divs e1 e2)
      | Csharpminor.Odivu => Some(Cmconstr.divu e1 e2)
      | Csharpminor.Omod => Some(Cmconstr.mods e1 e2)
      | Csharpminor.Omodu => Some(Cmconstr.modu e1 e2)
      | Csharpminor.Oand => Some(Cmconstr.and e1 e2)
      | Csharpminor.Oor => Some(Cmconstr.or e1 e2)
      | Csharpminor.Oxor => Some(Cmconstr.xor e1 e2)
      | Csharpminor.Oshl => Some(Cmconstr.shl e1 e2)
      | Csharpminor.Oshr => Some(Cmconstr.shr e1 e2)
      | Csharpminor.Oshru => Some(Cmconstr.shru e1 e2)
      | Csharpminor.Oaddf => Some(Cmconstr.addf e1 e2)
      | Csharpminor.Osubf => Some(Cmconstr.subf e1 e2)
      | Csharpminor.Omulf => Some(Cmconstr.mulf e1 e2)
      | Csharpminor.Odivf => Some(Cmconstr.divf e1 e2)
      | Csharpminor.Ocmp c => Some(Cmconstr.cmp c e1 e2)
      | Csharpminor.Ocmpu c => Some(Cmconstr.cmpu c e1 e2)
      | Csharpminor.Ocmpf c => Some(Cmconstr.cmpf c e1 e2)
      | _ => None
      end
  | _ => None
  end.

(** [make_cast chunk e] returns a Cminor expression that normalizes
  the value of Cminor expression [e] as prescribed by the memory chunk
  [chunk].  For instance, 8-bit sign extension is performed if
  [chunk] is [Mint8signed]. *)

Definition make_cast (chunk: memory_chunk) (e: expr): expr :=
  match chunk with
  | Mint8signed => Cmconstr.cast8signed e
  | Mint8unsigned => Cmconstr.cast8unsigned e
  | Mint16signed => Cmconstr.cast16signed e
  | Mint16unsigned => Cmconstr.cast16unsigned e
  | Mint32 => e
  | Mfloat32 => Cmconstr.singleoffloat e
  | Mfloat64 => e
  end.

Definition make_load (chunk: memory_chunk) (e: expr): expr :=
  Cmconstr.load chunk e.

(** In Csharpminor, the value of a store expression is the stored data
  normalized to the memory chunk.  In Cminor, it is the stored data.
  For the translation, we could normalize before storing.  However,
  the memory model performs automatic normalization of the stored
  data.  It is therefore correct to store the data as is, then
  normalize the result value of the store expression.  This is more
  efficient in general because often the result value is ignored:
  the normalization code will therefore be eliminated later as dead
  code. *)

Definition make_store (chunk: memory_chunk) (e1 e2: expr): expr :=
  make_cast chunk (Cmconstr.store chunk e1 e2).

Definition make_stackaddr (ofs: Z): expr :=
  Eop (Oaddrstack (Int.repr ofs)) Enil.

Definition make_globaladdr (id: ident): expr :=
  Eop (Oaddrsymbol id Int.zero) Enil.

(** Compile-time information attached to each Csharpminor
  variable: global variables, local variables, function parameters.
  [Var_local] denotes a scalar local variable whose address is not
  taken; it will be translated to a Cminor local variable of the
  same name.  [Var_stack_scalar] and [Var_stack_array] denote
  local variables that are stored as sub-blocks of the Cminor stack
  data block.  [Var_global_scalar] and [Var_global_array] denote
  global variables, stored in the global symbols with the same names. *)

Inductive var_info: Set :=
  | Var_local: memory_chunk -> var_info
  | Var_stack_scalar: memory_chunk -> Z -> var_info
  | Var_stack_array: Z -> var_info
  | Var_global_scalar: memory_chunk -> var_info
  | Var_global_array: var_info.

Definition compilenv := PTree.t var_info.

(** Generation of Cminor code corresponding to accesses to Csharpminor 
  local variables: reads, assignments, and taking the address of. *)

Definition var_get (cenv: compilenv) (id: ident): option expr :=
  match PTree.get id cenv with
  | Some(Var_local chunk) =>
      Some(Evar id)
  | Some(Var_stack_scalar chunk ofs) =>
      Some(make_load chunk (make_stackaddr ofs))
  | Some(Var_global_scalar chunk) =>
      Some(make_load chunk (make_globaladdr id))
  | _ =>
      None
  end.

Definition var_set (cenv: compilenv) (id: ident) (rhs: expr): option expr :=
  match PTree.get id cenv with
  | Some(Var_local chunk) =>
      Some(Eassign id (make_cast chunk rhs))
  | Some(Var_stack_scalar chunk ofs) =>
      Some(make_store chunk (make_stackaddr ofs) rhs)
  | Some(Var_global_scalar chunk) =>
      Some(make_store chunk (make_globaladdr id) rhs)
  | _ =>
      None
  end.

Definition var_addr (cenv: compilenv) (id: ident): option expr :=
  match PTree.get id cenv with
  | Some(Var_stack_scalar chunk ofs) => Some (make_stackaddr ofs)
  | Some(Var_stack_array ofs) => Some (make_stackaddr ofs)
  | Some(Var_global_scalar chunk) => Some (make_globaladdr id)
  | Some(Var_global_array) => Some (make_globaladdr id)
  | _ => None
  end.

(** The translation from Csharpminor to Cminor can fail, which we
  encode by returning option types ([None] denotes error).
  Propagation of errors is done in monadic style, using the following
  [bind] monadic composition operator, and a [do] notation inspired
  by Haskell's. *)

Definition bind (A B: Set) (a: option A) (b: A -> option B): option B :=
  match a with
  | None => None
  | Some x => b x
  end.

Notation "'do' X <- A ; B" := (bind _ _ A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).

(** Translation of expressions.  All the hard work is done by the
  [make_*] and [var_*] functions defined above. *)

Fixpoint transl_expr (cenv: compilenv) (e: Csharpminor.expr)
                     {struct e}: option expr :=
  match e with
  | Csharpminor.Evar id => var_get cenv id
  | Csharpminor.Eaddrof id => var_addr cenv id
  | Csharpminor.Eassign id e =>
      do te <- transl_expr cenv e; var_set cenv id te
  | Csharpminor.Eop op el =>
      do tel <- transl_exprlist cenv el; make_op op tel
  | Csharpminor.Eload chunk e =>
      do te <- transl_expr cenv e; Some (make_load chunk te)
  | Csharpminor.Estore chunk e1 e2 =>
      do te1 <- transl_expr cenv e1;
      do te2 <- transl_expr cenv e2;
      Some (make_store chunk te1 te2)
  | Csharpminor.Ecall sig e el =>
      do te <- transl_expr cenv e;
      do tel <- transl_exprlist cenv el;
      Some (Ecall sig te tel)
  | Csharpminor.Econdition e1 e2 e3 =>
      do te1 <- transl_expr cenv e1;
      do te2 <- transl_expr cenv e2;
      do te3 <- transl_expr cenv e3;
      Some (Cmconstr.conditionalexpr te1 te2 te3)
  | Csharpminor.Elet e1 e2 =>
      do te1 <- transl_expr cenv e1;
      do te2 <- transl_expr cenv e2;
      Some (Elet te1 te2)
  | Csharpminor.Eletvar n =>
      Some (Eletvar n)
  end

with transl_exprlist (cenv: compilenv) (el: Csharpminor.exprlist)
                     {struct el}: option exprlist :=
  match el with
  | Csharpminor.Enil =>
      Some Enil
  | Csharpminor.Econs e1 e2 =>
      do te1 <- transl_expr cenv e1;
      do te2 <- transl_exprlist cenv e2;
      Some (Econs te1 te2)
  end.

(** Translation of statements.  Entirely straightforward. *)

Fixpoint transl_stmt (cenv: compilenv) (s: Csharpminor.stmt)
                     {struct s}: option stmt :=
  match s with
  | Csharpminor.Sskip =>
      Some Sskip
  | Csharpminor.Sexpr e =>
      do te <- transl_expr cenv e; Some(Sexpr te)
  | Csharpminor.Sseq s1 s2 =>
      do ts1 <- transl_stmt cenv s1;
      do ts2 <- transl_stmt cenv s2;
      Some (Sseq ts1 ts2)
  | Csharpminor.Sifthenelse e s1 s2 =>
      do te <- transl_expr cenv e;
      do ts1 <- transl_stmt cenv s1;
      do ts2 <- transl_stmt cenv s2;
      Some (Cmconstr.ifthenelse te ts1 ts2)
  | Csharpminor.Sloop s =>
      do ts <- transl_stmt cenv s;
      Some (Sloop ts)
  | Csharpminor.Sblock s =>
      do ts <- transl_stmt cenv s;
      Some (Sblock ts)
  | Csharpminor.Sexit n =>
      Some (Sexit n)
  | Csharpminor.Sswitch e cases default =>
      do te <- transl_expr cenv e; Some(Sswitch te cases default)
  | Csharpminor.Sreturn None =>
      Some (Sreturn None)
  | Csharpminor.Sreturn (Some e) =>
      do te <- transl_expr cenv e; Some (Sreturn (Some te))
  end.

(** Computation of the set of variables whose address is taken in
  a piece of Csharpminor code. *)

Module Identset := MakeSet(PTree).

Fixpoint addr_taken_expr (e: Csharpminor.expr): Identset.t :=
  match e with
  | Csharpminor.Evar id => Identset.empty
  | Csharpminor.Eaddrof id => Identset.add id Identset.empty
  | Csharpminor.Eassign id e => addr_taken_expr e
  | Csharpminor.Eop op el => addr_taken_exprlist el
  | Csharpminor.Eload chunk e => addr_taken_expr e
  | Csharpminor.Estore chunk e1 e2 =>
      Identset.union (addr_taken_expr e1) (addr_taken_expr e2)
  | Csharpminor.Ecall sig e el =>
      Identset.union (addr_taken_expr e) (addr_taken_exprlist el)
  | Csharpminor.Econdition e1 e2 e3 =>
      Identset.union (addr_taken_expr e1) 
        (Identset.union (addr_taken_expr e2) (addr_taken_expr e3))
  | Csharpminor.Elet e1 e2 =>
      Identset.union (addr_taken_expr e1) (addr_taken_expr e2)
  | Csharpminor.Eletvar n => Identset.empty
  end

with addr_taken_exprlist (e: Csharpminor.exprlist): Identset.t :=
  match e with
  | Csharpminor.Enil => Identset.empty
  | Csharpminor.Econs e1 e2 =>
      Identset.union (addr_taken_expr e1) (addr_taken_exprlist e2)
  end.

Fixpoint addr_taken_stmt (s: Csharpminor.stmt): Identset.t :=
  match s with
  | Csharpminor.Sskip => Identset.empty
  | Csharpminor.Sexpr e => addr_taken_expr e
  | Csharpminor.Sseq s1 s2 =>
      Identset.union (addr_taken_stmt s1) (addr_taken_stmt s2)
  | Csharpminor.Sifthenelse e s1 s2 =>
      Identset.union (addr_taken_expr e)
        (Identset.union (addr_taken_stmt s1) (addr_taken_stmt s2))
  | Csharpminor.Sloop s => addr_taken_stmt s
  | Csharpminor.Sblock s => addr_taken_stmt s
  | Csharpminor.Sexit n => Identset.empty
  | Csharpminor.Sswitch e cases default => addr_taken_expr e
  | Csharpminor.Sreturn None => Identset.empty
  | Csharpminor.Sreturn (Some e) => addr_taken_expr e
  end.

(** Layout of the Cminor stack data block and construction of the 
  compilation environment.  Csharpminor local variables that are
  arrays or whose address is taken are allocated a slot in the Cminor
  stack data.  While this is not important for correctness, sufficient
  padding is inserted to ensure adequate alignment of addresses. *)

Definition assign_variable
    (atk: Identset.t)
    (id_lv: ident * var_kind)
    (cenv_stacksize: compilenv * Z) : compilenv * Z :=
  let (cenv, stacksize) := cenv_stacksize in
  match id_lv with
  | (id, Varray sz) =>
      let ofs := align stacksize 8 in
      (PTree.set id (Var_stack_array ofs) cenv, ofs + Zmax 0 sz)
  | (id, Vscalar chunk) =>
      if Identset.mem id atk then
        let sz := Mem.size_chunk chunk in
        let ofs := align stacksize sz in
        (PTree.set id (Var_stack_scalar chunk ofs) cenv, ofs + sz)
      else
        (PTree.set id (Var_local chunk) cenv, stacksize)
  end.

Fixpoint assign_variables
    (atk: Identset.t)
    (id_lv_list: list (ident * var_kind))
    (cenv_stacksize: compilenv * Z)
    {struct id_lv_list}: compilenv * Z :=
  match id_lv_list with
  | nil => cenv_stacksize
  | id_lv :: rem =>
      assign_variables atk rem (assign_variable atk id_lv cenv_stacksize)
  end.

Definition build_compilenv
          (globenv: compilenv) (f: Csharpminor.function) : compilenv * Z :=
  assign_variables
    (addr_taken_stmt f.(Csharpminor.fn_body))
    (fn_variables f)
    (globenv, 0).

Definition assign_global_variable
     (ce: compilenv) (id_vi: ident * var_kind) : compilenv :=
  match id_vi with
  | (id, Vscalar chunk) => PTree.set id (Var_global_scalar chunk) ce
  | (id, Varray sz) => PTree.set id Var_global_array ce
  end.

Definition build_global_compilenv (p: Csharpminor.program) : compilenv :=
  List.fold_left assign_global_variable 
                 p.(prog_vars) (PTree.empty var_info).

(** Function parameters whose address is taken must be stored in their
  stack slots at function entry.  (Cminor passes these parameters in
  local variables.) *)

Fixpoint store_parameters
       (cenv: compilenv) (params: list (ident * memory_chunk))
       {struct params} : stmt :=
  match params with
  | nil => Sskip
  | (id, chunk) :: rem =>
      match PTree.get id cenv with
      | Some(Var_local chunk) =>
          Sseq (Sexpr (Eassign id (make_cast chunk (Evar id))))
               (store_parameters cenv rem)
      | Some(Var_stack_scalar chunk ofs) =>
          Sseq (Sexpr (make_store chunk (make_stackaddr ofs) (Evar id)))
               (store_parameters cenv rem)
      | _ =>
          Sskip (* should never happen *)
      end
  end.

(** Translation of a Csharpminor function.  We must check that the
  required Cminor stack block is no bigger than [Int.max_signed],
  otherwise address computations within the stack block could
  overflow machine arithmetic and lead to incorrect code. *)

Definition transl_function
         (gce: compilenv) (f: Csharpminor.function): option function :=
  let (cenv, stacksize) := build_compilenv gce f in
  if zle stacksize Int.max_signed then
    do tbody <- transl_stmt cenv f.(Csharpminor.fn_body);
       Some (mkfunction
              (Csharpminor.fn_sig f)
              (Csharpminor.fn_params_names f)
              (Csharpminor.fn_vars_names f)
              stacksize
              (Sseq (store_parameters cenv f.(Csharpminor.fn_params)) tbody))
  else None.

Definition transl_program (p: Csharpminor.program) : option program :=
  let gce := build_global_compilenv p in
  transform_partial_program (transl_function gce) (program_of_program p).
