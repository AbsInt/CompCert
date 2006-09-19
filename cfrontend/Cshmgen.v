Require Import Coqlib.
Require Import Integers.
Require Import Floats.
Require Import AST.
Require Import Csyntax.
Require Import Csharpminor.

(** The error monad *)

Definition bind (A B: Set) (f: option A) (g: A -> option B) :=
  match f with None => None | Some x => g x end.

Implicit Arguments bind [A B].

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).

(** ** Operations on C types *)

Definition signature_of_function (f: Csyntax.function) : signature :=
  mksignature 
   (typlist_of_typelist (type_of_params (Csyntax.fn_params f)))
   (opttyp_of_type (Csyntax.fn_return f)).

Definition chunk_of_type (ty: type): option memory_chunk :=
  match access_mode ty with
  | By_value chunk => Some chunk
  | _ => None
  end.

Definition var_kind_of_type (ty: type): option var_kind :=
  match ty with
  | Tint I8 Signed => Some(Vscalar Mint8signed)
  | Tint I8 Unsigned => Some(Vscalar Mint8unsigned)
  | Tint I16 Signed => Some(Vscalar Mint16signed)
  | Tint I16 Unsigned => Some(Vscalar Mint16unsigned)
  | Tint I32 _ => Some(Vscalar Mint32)
  | Tfloat F32 => Some(Vscalar Mfloat32)
  | Tfloat F64 => Some(Vscalar Mfloat64)
  | Tvoid => None
  | Tpointer _ => Some(Vscalar Mint32)
  | Tarray _ _ => Some(Varray (Csyntax.sizeof ty))
  | Tfunction _ _ => None
  | Tstruct _ fList => Some(Varray (Csyntax.sizeof ty))
  | Tunion _ fList => Some(Varray (Csyntax.sizeof ty))
  | Tcomp_ptr _ => Some(Vscalar Mint32)
end.
  
(** ** Csharpminor constructors *)

(* The following functions build Csharpminor expressions that compute
   the value of a C operation.  Most construction functions take
   as arguments
   - Csharpminor subexpressions that compute the values of the
     arguments of the operation;
   - The C types of the arguments of the operation.  These types
     are used to insert the necessary numeric conversions and to
     resolve operation overloading.
   Most of these functions return an [option expr], with [None] 
   denoting a case where the operation is not defined at the given types.
*)

Definition make_intconst (n: int) :=  Eop (Ointconst n) Enil.

Definition make_floatconst (f: float) :=  Eop (Ofloatconst f) Enil.

Definition make_unop (op: operation) (e: expr) :=  Eop op (Econs e Enil).

Definition make_binop (op: operation) (e1 e2: expr) :=
    Eop op (Econs e1 (Econs e2 Enil)).

Definition make_floatofint (e: expr) (sg: signedness) :=
  match sg with
  | Signed => make_unop Ofloatofint e
  | Unsigned => make_unop Ofloatofintu e
  end.

(* [make_boolean e ty] returns a Csharpminor expression that evaluates
   to the boolean value of [e].  Recall that:
     - in Csharpminor, [false] is the integer 0,
       [true] any non-zero integer or any pointer
     - in C, [false] is the integer 0, the null pointer, the float 0.0
       [true] is any non-zero integer, non-null pointer, non-null float.
*)
Definition make_boolean (e: expr) (ty: type) :=
  match ty with
  | Tfloat _ => make_binop (Ocmpf Cne) e (make_floatconst Float.zero)
  | _ => e
  end.

Definition make_neg (e: expr) (ty: type) :=
  match ty with
  | Tint _ _ => Some (make_binop Osub (make_intconst Int.zero) e)
  | Tfloat _ => Some (make_unop Onegf e)
  | _ => None
  end.

Definition make_notbool (e: expr) (ty: type) :=
  match ty with
  | Tfloat _ => make_binop (Ocmpf Ceq) e (make_floatconst Float.zero)
  | _ => make_unop Onotbool e
  end.

Definition make_notint (e: expr) (ty: type) :=
  make_unop Onotint e.

Definition make_add (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_add ty1 ty2 with
  | add_case_ii => Some (make_binop Oadd e1 e2)
  | add_case_ff => Some (make_binop Oaddf e1 e2)
  | add_case_pi ty =>
      let n := make_intconst (Int.repr (Csyntax.sizeof ty)) in
      Some (make_binop Oadd e1 (make_binop Omul n e2))
  | add_default => None
  end.

Definition make_sub (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_sub ty1 ty2 with
  | sub_case_ii => Some (make_binop Osub e1 e2)
  | sub_case_ff => Some (make_binop Osubf e1 e2)
  | sub_case_pi ty =>
      let n := make_intconst (Int.repr (Csyntax.sizeof ty)) in
      Some (make_binop Osub e1 (make_binop Omul n e2))
  | sub_case_pp ty =>
      let n := make_intconst (Int.repr (Csyntax.sizeof ty)) in
      Some (make_binop Odivu (make_binop Osub e1 e2) n)
  | sub_default => None
  end.

Definition make_mul (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_mul ty1 ty2 with
  | mul_case_ii => Some (make_binop Omul e1 e2)
  | mul_case_ff => Some (make_binop Omulf e1 e2)
  | mul_default => None
  end.

Definition make_div (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_div ty1 ty2 with
  | div_case_I32unsi => Some (make_binop Odivu e1 e2)
  | div_case_ii => Some (make_binop Odiv e1 e2)
  | div_case_ff => Some (make_binop Odivf e1 e2)
  | div_default => None
  end.

Definition make_mod (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_mod ty1 ty2 with
  | mod_case_I32unsi => Some (make_binop Omodu e1 e2)
  | mod_case_ii=> Some (make_binop Omod e1 e2)
  | mod_default => None
  end.

Definition make_and (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  Some(make_binop Oand e1 e2).

Definition make_or (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  Some(make_binop Oor e1 e2).

Definition make_xor (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  Some(make_binop Oxor e1 e2).

Definition make_shl (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  Some(make_binop Oshl e1 e2).

Definition make_shr (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_shr ty1 ty2 with
  | shr_case_I32unsi => Some (make_binop Oshru e1 e2)
  | shr_case_ii=> Some (make_binop Oshr e1 e2)
  | shr_default => None
  end.

Definition make_cmp (c: comparison) (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  match classify_cmp ty1 ty2 with
  | cmp_case_I32unsi => Some (make_binop (Ocmpu c) e1 e2)
  | cmp_case_ii => Some (make_binop (Ocmp c) e1 e2)
  | cmp_case_ff => Some (make_binop (Ocmpf c) e1 e2)
  | cmp_case_pi => Some (make_binop (Ocmp c) e1 e2)
  | cmp_case_pp => Some (make_binop (Ocmp c) e1 e2)
  | cmp_default => None
  end.

Definition make_andbool (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  Econdition
    (make_boolean e1 ty1)
    (Econdition
       (make_boolean e2 ty2)
       (make_intconst Int.one)
       (make_intconst Int.zero))
    (make_intconst Int.zero).

Definition make_orbool (e1: expr) (ty1: type) (e2: expr) (ty2: type) :=
  Econdition
    (make_boolean e1 ty1)
    (make_intconst Int.one)
    (Econdition
       (make_boolean e2 ty2)
       (make_intconst Int.one)
       (make_intconst Int.zero)).

(* [make_cast from to e] applies to [e] the numeric conversions needed
   to transform a result of type [from] to a result of type [to].
   It is decomposed in two functions:
   - [make_cast1]  converts between int/pointer and float if necessary
   - [make_cast2]  converts to a "smaller" int or float type if necessary.
*)

Definition make_cast1 (from to: type) (e: expr) :=
  match from, to with
  | Tint _ uns, Tfloat _ => make_floatofint e uns
  | Tfloat _, Tint _ _ => make_unop Ointoffloat e
  | _, _ => e
  end.

Definition make_cast2 (from to: type) (e: expr) :=
  match to with
  | Tint I8 Signed => make_unop Ocast8signed e  
  | Tint I8 Unsigned => make_unop Ocast8unsigned e  
  | Tint I16 Signed => make_unop Ocast16signed e  
  | Tint I16 Unsigned => make_unop Ocast16unsigned e  
  | Tfloat F32 => make_unop Osingleoffloat e
  | _ => e
  end.

Definition make_cast (from to: type) (e: expr) :=
  make_cast2 from to (make_cast1 from to e).

(* [make_load addr ty_res] loads a value of type [ty_res] from
   the memory location denoted by the Csharpminor expression [addr].
   If [ty_res] is an array or function type, returns [addr] instead,
   as consistent with C semantics.
*)

Definition make_load (addr: expr) (ty_res: type) :=
  match (access_mode ty_res) with
  | By_value chunk => Some (Eload chunk addr)
  | By_reference => Some addr
  | By_nothing => None
  end.

(* [make_store addr ty_res rhs ty_rhs] stores the value of the
   Csharpminor expression [rhs] into the memory location denoted by the
   Csharpminor expression [addr].  
   [ty] is the type of the memory location. *)

Definition make_store (addr: expr) (ty: type) (rhs: expr) :=
  match access_mode ty with
  | By_value chunk => Some (Sstore chunk addr rhs)
  | _ => None
  end.

(** ** Reading and writing variables *)

(* [var_get id ty] builds Csharpminor code that evaluates to the
   value of C variable [id] with type [ty].  Note that 
   C variables of array or function type evaluate to the address
   of the corresponding CabsCoq memory block, while variables of other types
   evaluate to the contents of the corresponding C memory block.
*)

Definition var_get (id: ident) (ty: type) :=
  match access_mode ty with
  | By_value chunk => Some (Evar id)
  | By_reference => Some (Eaddrof id)
  | _ => None
  end.

(* [var_set id ty rhs] stores the value of the Csharpminor
   expression [rhs] into the CabsCoq variable [id] of type [ty].
*)

Definition var_set (id: ident) (ty: type) (rhs: expr) :=
  match access_mode ty with
  | By_value chunk => Some (Sassign id rhs)
  | _ => None
  end.

(** ** Translation of operators *)

Definition transl_unop (op: unary_operation) (a: expr) (ta: type) : option expr :=
  match op with
  | Csyntax.Onotbool => Some(make_notbool a ta)
  | Csyntax.Onotint => Some(make_notint a ta)
  | Csyntax.Oneg => make_neg a ta
  end.

Definition transl_binop (op: binary_operation) (a: expr) (ta: type)
                                  (b: expr) (tb: type) : option expr :=
  match op with
  | Csyntax.Oadd => make_add a ta b tb
  | Csyntax.Osub => make_sub a ta b tb
  | Csyntax.Omul => make_mul a ta b tb
  | Csyntax.Odiv => make_div a ta b tb
  | Csyntax.Omod => make_mod a ta b tb
  | Csyntax.Oand => make_and a ta b tb
  | Csyntax.Oor  => make_or a ta b tb
  | Csyntax.Oxor => make_xor a ta b tb
  | Csyntax.Oshl => make_shl a ta b tb
  | Csyntax.Oshr => make_shr a ta b tb
  | Csyntax.Oeq => make_cmp Ceq a ta b tb
  | Csyntax.One => make_cmp Cne a ta b tb
  | Csyntax.Olt => make_cmp Clt a ta b tb
  | Csyntax.Ogt => make_cmp Cgt a ta b tb
  | Csyntax.Ole => make_cmp Cle a ta b tb
  | Csyntax.Oge => make_cmp Cge a ta b tb
  end.

(** ** Translation of expressions *)

(* [transl_expr a] returns the Csharpminor code that computes the value
   of expression [a]. The result is an option type to enable error reporting.

   Most cases are self-explanatory.  We outline the non-obvious cases:

   a && b    --->    a ? (b ? 1 : 0) : 0

   a || b    --->    a ? 1 : (b ? 1 : 0)
*)

Fixpoint transl_expr (a: Csyntax.expr) {struct a} : option expr :=
  match a with
  | Expr (Csyntax.Econst_int n) _ =>
      Some(make_intconst n)
  | Expr (Csyntax.Econst_float n) _ =>
      Some(make_floatconst n)
  | Expr (Csyntax.Evar id) ty =>
      var_get id ty
  | Expr (Csyntax.Ederef b) _ =>
      do tb <- transl_expr b;
      make_load tb (typeof a)
  | Expr (Csyntax.Eaddrof b) _ =>
      transl_lvalue b
  | Expr (Csyntax.Eunop op b) _ =>
      do tb <- transl_expr b;
      transl_unop op tb (typeof b)
  | Expr (Csyntax.Ebinop op b c) _ =>
      do tb <- transl_expr b;
      do tc <- transl_expr c;
      transl_binop op tb (typeof b) tc (typeof c)
  | Expr (Csyntax.Ecast ty b) _ =>
      do tb <- transl_expr b;
      Some (make_cast (typeof b) ty tb)
  | Expr (Csyntax.Eindex b c) ty =>
      do tb <- transl_expr b;
      do tc <- transl_expr c;
      do ts <- make_add tb (typeof b) tc (typeof c);
      make_load ts ty
  | Expr (Csyntax.Ecall b cl) _ =>
      match (classify_fun (typeof b)) with
      | fun_case_f args res =>
          do tb <- transl_expr b;
          do tcl <- transl_exprlist cl;
          Some(Ecall (signature_of_type args res) tb tcl)
      | _ => None
      end 
  | Expr (Csyntax.Eandbool b c) _ =>
      do tb <- transl_expr b;
      do tc <- transl_expr c;
      Some(make_andbool tb (typeof b) tc (typeof c))
  | Expr (Csyntax.Eorbool b c) _ =>
      do tb <- transl_expr b;
      do tc <- transl_expr c;
      Some(make_orbool tb (typeof b) tc (typeof c))
  | Expr (Csyntax.Esizeof ty) _ =>
      Some(make_intconst (Int.repr (Csyntax.sizeof ty)))
  | Expr (Csyntax.Efield b i) ty => 
      match typeof b with
      | Tstruct _ fld =>
          do tb <- transl_lvalue b;
          do ofs <- field_offset i fld;
          make_load
            (make_binop Oadd tb (make_intconst (Int.repr ofs)))
            ty
      | Tunion _ fld =>
          do tb <- transl_lvalue b;
          make_load tb ty
      | _ => None
      end
  end

(* [transl_lvalue a] returns the Csharpminor code that evaluates
   [a] as a lvalue, that is, code that returns the memory address
   where the value of [a] is stored.
*)

with transl_lvalue (a: Csyntax.expr) {struct a} : option expr :=
  match a with
  | Expr (Csyntax.Evar id) _ =>
      Some (Eaddrof id)
  | Expr (Csyntax.Ederef b) _ =>
      transl_expr b
  | Expr (Csyntax.Eindex b c) _ =>
      do tb <- transl_expr b;
      do tc <- transl_expr c;
      make_add tb (typeof b) tc (typeof c)
  | Expr (Csyntax.Efield b i) ty => 
      match typeof b with
      | Tstruct _ fld =>
          do tb <- transl_lvalue b;
          do ofs <- field_offset i fld;
          Some (make_binop Oadd tb (make_intconst (Int.repr ofs)))
      | Tunion _ fld =>
          transl_lvalue b
      | _ => None
      end
  | _ => None
  end

(* [transl_exprlist al] returns a list of Csharpminor expressions
   that compute the values of the list [al] of Csyntax expressions.
   Used for function applications. *)

with transl_exprlist (al: Csyntax.exprlist): option exprlist :=
  match al with
  | Csyntax.Enil => Some Enil
  | Csyntax.Econs a1 a2 =>
      do ta1 <- transl_expr a1;
      do ta2 <- transl_exprlist a2;
      Some (Econs ta1 ta2)
  end.

(** ** Translation of statements *)

(** Determine if a C expression is a variable *)

Definition is_variable (e: Csyntax.expr) : option ident :=
  match e with
  | Expr (Csyntax.Evar id) _ => Some id
  | _ => None
  end.

(* [exit_if_false e] return the statement that tests the boolean
   value of the CabsCoq expression [e] and performs an [exit 0] if [e]
   evaluates to false.
*)
Definition exit_if_false (e: Csyntax.expr) : option stmt :=
  do te <- transl_expr e;
  Some(Sifthenelse
        (make_boolean te (typeof e))
        Sskip
        (Sexit 0%nat)).

(* [transl_statement nbrk ncnt s] returns a Csharpminor statement
   that performs the same computations as the CabsCoq statement [s].

   If the statement [s] terminates prematurely on a [break] construct,
   the generated Csharpminor statement terminates prematurely on an
   [exit nbrk] construct.

   If the statement [s] terminates prematurely on a [continue]
   construct, the generated Csharpminor statement terminates
   prematurely on an [exit ncnt] construct.

   Immediately within a loop, [nbrk = 1] and [ncnt = 0], but this 
   changes when we're inside a [switch] construct.

   The general translation for loops is as follows:

while (e1) s;       --->     block {
                               loop {
                                 if (!e1) exit 0;
                                 block { s }
                                 // continue in s branches here
                               }
                             }
                             // break in s branches here

do s; while (e1);   --->     block {
                               loop {
                                 block { s }
                                 // continue in s branches here
                                 if (!e1) exit 0;
                               }
                             }
                             // break in s branches here

for (e1;e2;e3) s;   --->     e1;
                             block {
                               loop {
                                 if (!e2) exit 0;
                                 block { s }
                                 // continue in s branches here
                                 e3;
                               }
                             }
                             // break in s branches here

switch (e) {        --->    block { block { block { block {
  case N1: s1;                switch (e) { N1: exit 0; N2: exit 1; default: exit 2; }
  case N2: s2;                } ; s1  // with break -> exit 2  and continue -> exit 3
  default: s;                 } ; s2  // with break -> exit 1  and continue -> exit 2
}                             } ; s   // with break -> exit 0  and continue -> exit 1
                              }
*)

Fixpoint switch_table (sl: labeled_statements) (k: nat) {struct sl} : list (int * nat) :=
  match sl with
  | LSdefault _ => nil
  | LScase ni _ rem => (ni, k) :: switch_table rem (k+1)
  end.

Fixpoint transl_statement (nbrk ncnt: nat) (s: Csyntax.statement) {struct s} : option stmt :=
  match s with
  | Csyntax.Sskip =>
      Some Sskip
  | Csyntax.Sexpr e =>
      do te <- transl_expr e;
      Some (Sexpr te)
  | Csyntax.Sassign b c =>
      match (is_variable b) with
      | Some id =>
          do tc <- transl_expr c;
          var_set id (typeof b) tc
      | None =>
          do tb <- transl_lvalue b;
          do tc <- transl_expr c;
          make_store tb (typeof b) tc
      end 
  | Csyntax.Ssequence s1 s2 =>
      do ts1 <- transl_statement nbrk ncnt s1;
      do ts2 <- transl_statement nbrk ncnt s2;
      Some (Sseq ts1 ts2)
  | Csyntax.Sifthenelse e s1 s2 =>
      do te <- transl_expr e;
      do ts1 <- transl_statement nbrk ncnt s1;
      do ts2 <- transl_statement nbrk ncnt s2;
      Some (Sifthenelse (make_boolean te (typeof e)) ts1 ts2)
  | Csyntax.Swhile e s1 =>
      do te <- exit_if_false e;
      do ts1 <- transl_statement 1%nat 0%nat s1;
      Some (Sblock (Sloop (Sseq te (Sblock ts1))))
  | Csyntax.Sdowhile e s1 =>
      do te <- exit_if_false e;
      do ts1 <- transl_statement 1%nat 0%nat s1;
      Some (Sblock (Sloop (Sseq (Sblock ts1) te)))
  | Csyntax.Sfor e1 e2 e3 s1 =>
      do te1 <- transl_statement nbrk ncnt e1;
      do te2 <- exit_if_false e2;
      do te3 <- transl_statement nbrk ncnt e3;
      do ts1 <- transl_statement 1%nat 0%nat s1;
      Some (Sseq te1 (Sblock (Sloop (Sseq te2 (Sseq (Sblock ts1) te3)))))
  | Csyntax.Sbreak =>
      Some (Sexit nbrk)
  | Csyntax.Scontinue =>
      Some (Sexit ncnt)
  | Csyntax.Sreturn (Some e) =>
      do te <- transl_expr e;
      Some (Sreturn (Some te))
  | Csyntax.Sreturn None =>
      Some (Sreturn None)
  | Csyntax.Sswitch e sl =>
      let cases := switch_table sl 0 in
      let ncases := List.length cases in
      do te <- transl_expr e;
      transl_lblstmts ncases (ncnt + ncases + 1)%nat sl (Sblock (Sswitch te cases ncases))
  end

with transl_lblstmts (nbrk ncnt: nat) (sl: labeled_statements) (body: stmt)
                     {struct sl}: option stmt :=
  match sl with
  | LSdefault s =>
      do ts <- transl_statement nbrk ncnt s;
      Some (Sblock (Sseq body ts))
  | LScase _ s rem =>
      do ts <- transl_statement nbrk ncnt s;
      transl_lblstmts (pred nbrk) (pred ncnt) rem (Sblock (Sseq body ts))
  end.

(*** Translation of functions *)

Definition transl_params (l: list (ident * type)) :=
   AST.map_partial chunk_of_type l.
Definition transl_vars (l: list (ident * type)) :=
   AST.map_partial var_kind_of_type l.

Definition transl_function (f: Csyntax.function) : option function :=
  do tparams <- transl_params (Csyntax.fn_params f);
  do tvars <- transl_vars (Csyntax.fn_vars f);
  do tbody <- transl_statement 1%nat 0%nat (Csyntax.fn_body f);
  Some (mkfunction (signature_of_function f) tparams tvars tbody).

Definition transl_fundef (f: Csyntax.fundef) : option fundef :=
  match f with
  | Csyntax.Internal g => 
      do tg <- transl_function g; Some(AST.Internal tg)
  | Csyntax.External id args res =>
      Some(AST.External (external_function id args res))
  end.

(** ** Translation of programs *)

Definition transl_globvar (ty: type) := var_kind_of_type ty.

Definition transl_program (p: Csyntax.program) : option program :=
  transform_partial_program2 transl_fundef transl_globvar p.
