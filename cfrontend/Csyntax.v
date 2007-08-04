(** * Abstract syntax for the Clight language *)

Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import AST.

(** ** Abstract syntax *)

(** Types *)

Inductive signedness : Set :=
  | Signed: signedness
  | Unsigned: signedness.

Inductive intsize : Set :=
  | I8: intsize
  | I16: intsize
  | I32: intsize.

Inductive floatsize : Set :=
  | F32: floatsize
  | F64: floatsize.

Inductive type : Set :=
  | Tvoid: type
  | Tint: intsize -> signedness -> type
  | Tfloat: floatsize -> type
  | Tpointer: type -> type
  | Tarray: type -> Z -> type
  | Tfunction: typelist -> type -> type
  | Tstruct: ident -> fieldlist -> type
  | Tunion: ident ->fieldlist -> type
  | Tcomp_ptr: ident -> type

with typelist : Set :=
  | Tnil: typelist
  | Tcons: type -> typelist -> typelist

with fieldlist : Set :=
  | Fnil: fieldlist
  | Fcons: ident -> type -> fieldlist -> fieldlist.

(** Arithmetic and logical operators *)

Inductive unary_operation : Set :=
  | Onotbool : unary_operation
  | Onotint : unary_operation
  | Oneg : unary_operation.

Inductive binary_operation : Set :=
  | Oadd : binary_operation
  | Osub : binary_operation
  | Omul : binary_operation
  | Odiv : binary_operation
  | Omod : binary_operation
  | Oand : binary_operation
  | Oor : binary_operation
  | Oxor : binary_operation
  | Oshl : binary_operation
  | Oshr : binary_operation
  | Oeq: binary_operation
  | One: binary_operation
  | Olt: binary_operation
  | Ogt: binary_operation
  | Ole: binary_operation
  | Oge: binary_operation.

(** Expressions *)

Inductive expr : Set :=
  | Expr: expr_descr -> type -> expr

with expr_descr : Set :=
  | Econst_int: int -> expr_descr
  | Econst_float: float -> expr_descr
  | Evar: ident -> expr_descr
  | Ederef: expr -> expr_descr
  | Eaddrof: expr -> expr_descr
  | Eunop: unary_operation -> expr -> expr_descr
  | Ebinop: binary_operation -> expr -> expr -> expr_descr
  | Ecast: type -> expr -> expr_descr
  | Eindex: expr -> expr -> expr_descr 
  | Ecall: expr -> exprlist -> expr_descr 
  | Eandbool: expr -> expr -> expr_descr
  | Eorbool: expr -> expr -> expr_descr
  | Esizeof: type -> expr_descr
  | Efield: expr -> ident -> expr_descr

with exprlist : Set :=
  | Enil: exprlist
  | Econs: expr -> exprlist -> exprlist.

(** Extract the type part of a type-annotated Clight expression. *)

Definition typeof (e: expr) : type :=
  match e with Expr de te => te end.

(** Statements *)

Inductive statement : Set :=
  | Sskip : statement
  | Sexpr : expr -> statement
  | Sassign : expr -> expr -> statement
  | Ssequence : statement -> statement -> statement
  | Sifthenelse : expr  -> statement -> statement -> statement
  | Swhile : expr -> statement -> statement
  | Sdowhile : expr -> statement -> statement
  | Sfor: statement -> expr -> statement -> statement -> statement
  | Sbreak : statement
  | Scontinue : statement
  | Sreturn : option expr -> statement
  | Sswitch : expr -> labeled_statements -> statement

with labeled_statements : Set :=
  | LSdefault: statement -> labeled_statements
  | LScase: int -> statement -> labeled_statements -> labeled_statements.

(** Function definition *)

Record function : Set := mkfunction {
  fn_return: type;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_body: statement
}.

Inductive fundef : Set :=
  | Internal: function -> fundef
  | External: ident -> typelist -> type -> fundef.

(** Program *)

Definition program : Set := AST.program fundef type.

(** ** Operations over types *)

(** The type of a function definition *)

Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
  end.

Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External id args res => Tfunction args res
  end.

(** Natural alignment of a type *)

Fixpoint alignof (t: type) : Z :=
  match t with
  | Tvoid => 1
  | Tint I8 _ => 1
  | Tint I16 _ => 2
  | Tint I32 _ => 4
  | Tfloat F32 => 4
  | Tfloat F64 => 8
  | Tpointer _ => 4
  | Tarray t' n => alignof t'
  | Tfunction _ _ => 1
  | Tstruct _ fld => alignof_fields fld
  | Tunion _ fld => alignof_fields fld
  | Tcomp_ptr _ => 4
  end

with alignof_fields (f: fieldlist) : Z :=
  match f with
  | Fnil => 1
  | Fcons id t f' => Zmax (alignof t) (alignof_fields f')
  end.

Scheme type_ind2 := Induction for type Sort Prop
  with fieldlist_ind2 := Induction for fieldlist Sort Prop.

Lemma alignof_fields_pos:
  forall f, alignof_fields f > 0.
Proof.
  induction f; simpl.
  omega.
  generalize (Zmax2 (alignof t) (alignof_fields f)). omega.
Qed.

Lemma alignof_pos:
  forall t, alignof t > 0.
Proof.
  induction t; simpl; auto; try omega.
  destruct i; omega.
  destruct f; omega.
  apply alignof_fields_pos.
  apply alignof_fields_pos.
Qed.

(** Size of a type (in bytes) *)

Fixpoint sizeof (t: type) : Z :=
  match t with
  | Tvoid => 1
  | Tint I8 _ => 1
  | Tint I16 _ => 2
  | Tint I32 _ => 4
  | Tfloat F32 => 4
  | Tfloat F64 => 8
  | Tpointer _ => 4
  | Tarray t' n => sizeof t' * Zmax 1 n
  | Tfunction _ _ => 1
  | Tstruct _ fld => align (Zmax 1 (sizeof_struct fld 0)) (alignof t)
  | Tunion _ fld => align (Zmax 1 (sizeof_union fld)) (alignof t)
  | Tcomp_ptr _ => 4
  end

with sizeof_struct (fld: fieldlist) (pos: Z) {struct fld} : Z :=
  match fld with
  | Fnil => pos
  | Fcons id t fld' => sizeof_struct fld' (align pos (alignof t) + sizeof t)
  end

with sizeof_union (fld: fieldlist) : Z :=
  match fld with
  | Fnil => 0
  | Fcons id t fld' => Zmax (sizeof t) (sizeof_union fld')
  end.

Lemma sizeof_pos:
  forall t, sizeof t > 0.
Proof.
  intro t0.
  apply (type_ind2 (fun t => sizeof t > 0)
                   (fun f => sizeof_union f >= 0 /\ forall pos, pos >= 0 -> sizeof_struct f pos >= 0));
  intros; simpl; auto; try omega.
  destruct i; omega.
  destruct f; omega.
  apply Zmult_gt_0_compat. auto. generalize (Zmax1 1 z); omega.
  destruct H. 
  generalize (align_le (Zmax 1 (sizeof_struct f 0)) (alignof_fields f) (alignof_fields_pos f)). 
  generalize (Zmax1 1 (sizeof_struct f 0)). omega. 
  generalize (align_le (Zmax 1 (sizeof_union f)) (alignof_fields f) (alignof_fields_pos f)). 
  generalize (Zmax1 1 (sizeof_union f)). omega. 
  split. omega. auto.
  destruct H0. split; intros.
  generalize (Zmax2 (sizeof t) (sizeof_union f)). omega.
  apply H1. 
  generalize (align_le pos (alignof t) (alignof_pos t)). omega.
Qed.

(** Byte offset for a field in a struct. *)

Open Local Scope string_scope.

Fixpoint field_offset_rec (id: ident) (fld: fieldlist) (pos: Z)
                              {struct fld} : res Z :=
  match fld with
  | Fnil => Error (MSG "Unknown field " :: CTX id :: nil)
  | Fcons id' t fld' =>
      if ident_eq id id'
      then OK (align pos (alignof t))
      else field_offset_rec id fld' (align pos (alignof t) + sizeof t)
  end.

Definition field_offset (id: ident) (fld: fieldlist) : res Z :=
  field_offset_rec id fld 0.

(* Describe how a variable of the given type must be accessed:
     - by value, i.e. by loading from the address of the variable
       with the given chunk
     - by reference, i.e. by just returning the address of the variable
     - not at all, e.g. the [void] type. *)

Inductive mode: Set :=
  | By_value: memory_chunk -> mode
  | By_reference: mode
  | By_nothing: mode.

Definition access_mode (ty: type) : mode :=
  match ty with
  | Tint I8 Signed => By_value Mint8signed
  | Tint I8 Unsigned => By_value Mint8unsigned
  | Tint I16 Signed => By_value Mint16signed
  | Tint I16 Unsigned => By_value Mint16unsigned
  | Tint I32 _ => By_value Mint32
  | Tfloat F32 => By_value Mfloat32
  | Tfloat F64 => By_value Mfloat64
  | Tvoid => By_nothing
  | Tpointer _ => By_value Mint32
  | Tarray _ _ => By_reference
  | Tfunction _ _ => By_reference
  | Tstruct _ fList => By_nothing
  | Tunion _ fList => By_nothing
  | Tcomp_ptr _ => By_value Mint32
end.

(** Classification of arithmetic operations and comparisons *)

Inductive classify_add_cases : Set :=
  | add_case_ii: classify_add_cases         (* int , int *)
  | add_case_ff: classify_add_cases         (* float , float *)
  | add_case_pi: type -> classify_add_cases (* ptr | array, int *)
  | add_default: classify_add_cases.        (* other *)

Definition classify_add (ty1: type) (ty2: type) :=
  match ty1, ty2 with
  | Tint _ _, Tint _ _ => add_case_ii
  | Tfloat _, Tfloat _ => add_case_ff
  | Tpointer ty, Tint _ _ => add_case_pi ty
  | Tarray ty _, Tint _ _ => add_case_pi ty 
  | _, _ => add_default
  end.

Inductive classify_sub_cases : Set :=
  | sub_case_ii: classify_sub_cases          (* int , int *)
  | sub_case_ff: classify_sub_cases          (* float , float *)
  | sub_case_pi: type -> classify_sub_cases  (* ptr | array , int *)
  | sub_case_pp: type -> classify_sub_cases  (* ptr | array , ptr | array *)
  | sub_default: classify_sub_cases .        (* other *)

Definition classify_sub (ty1: type) (ty2: type) :=
  match ty1, ty2 with
  | Tint _ _ , Tint _ _ => sub_case_ii
  | Tfloat _ , Tfloat _ => sub_case_ff
  | Tpointer ty , Tint _ _ => sub_case_pi ty
  | Tarray ty _ , Tint _ _ => sub_case_pi ty
  | Tpointer ty , Tpointer _ => sub_case_pp ty
  | Tpointer ty , Tarray _ _=> sub_case_pp ty
  | Tarray ty _ , Tpointer _ => sub_case_pp ty
  | Tarray ty _ , Tarray _ _ => sub_case_pp ty 
  | _ ,_ => sub_default
  end.

Inductive classify_mul_cases : Set:=
  | mul_case_ii: classify_mul_cases (* int , int *)
  | mul_case_ff: classify_mul_cases (* float , float *)
  | mul_default: classify_mul_cases . (* other *)

Definition classify_mul (ty1: type) (ty2: type) :=
  match ty1,ty2 with
  | Tint _ _, Tint _ _ => mul_case_ii
  | Tfloat _ , Tfloat _ => mul_case_ff
  | _,_  => mul_default
end.

Inductive classify_div_cases : Set:=
  | div_case_I32unsi: classify_div_cases (* uns int32 , int *)
  | div_case_ii: classify_div_cases    (* int , int *) 
  | div_case_ff: classify_div_cases    (* float , float *)
  | div_default: classify_div_cases. (* other *)

Definition classify_div (ty1: type) (ty2: type) :=
  match ty1,ty2 with 
  | Tint I32 Unsigned, Tint _ _ => div_case_I32unsi 
  | Tint _ _ , Tint I32 Unsigned => div_case_I32unsi 
  | Tint _ _ , Tint _ _ => div_case_ii 
  | Tfloat _ , Tfloat _ => div_case_ff 
  | _ ,_ => div_default 
end.

Inductive classify_mod_cases : Set:=
  | mod_case_I32unsi: classify_mod_cases  (* uns I32 , int *)
  | mod_case_ii: classify_mod_cases  (* int , int *)
  | mod_default: classify_mod_cases . (* other *)

Definition classify_mod (ty1: type) (ty2: type) :=
  match ty1,ty2 with
  | Tint I32 Unsigned , Tint _ _ => mod_case_I32unsi 
  | Tint _ _ , Tint I32 Unsigned => mod_case_I32unsi 
  | Tint _ _ , Tint _ _ => mod_case_ii 
  | _ , _ => mod_default 
end .

Inductive classify_shr_cases :Set:=
  | shr_case_I32unsi:  classify_shr_cases (* uns I32 , int *)
  | shr_case_ii :classify_shr_cases (* int , int *)
  | shr_default : classify_shr_cases . (* other *)

Definition classify_shr (ty1: type) (ty2: type) :=
  match ty1,ty2 with
  | Tint I32 Unsigned , Tint _ _ => shr_case_I32unsi
  | Tint _ _ , Tint _ _ => shr_case_ii
  | _ , _ => shr_default 
  end.

Inductive classify_cmp_cases : Set:=
  | cmp_case_I32unsi: classify_cmp_cases (* uns I32 , int *)
  | cmp_case_ii: classify_cmp_cases  (* int , int*)
  | cmp_case_ff: classify_cmp_cases  (* float , float *)
  | cmp_case_pi: classify_cmp_cases  (* ptr | array , int *)
  | cmp_case_pp:classify_cmp_cases   (* ptr | array , ptr | array *)
  | cmp_default: classify_cmp_cases . (* other *)

Definition classify_cmp (ty1: type) (ty2: type) :=
  match ty1,ty2 with 
  | Tint I32 Unsigned , Tint _ _ => cmp_case_I32unsi 
  | Tint _ _ , Tint I32 Unsigned => cmp_case_I32unsi 
  | Tint _ _ , Tint _ _ => cmp_case_ii 
  | Tfloat _ , Tfloat _ => cmp_case_ff
  | Tpointer _ , Tint _ _ => cmp_case_pi 
  | Tarray _ _ , Tint _ _ => cmp_case_pi 
  | Tpointer _ , Tpointer _ => cmp_case_pp
  | Tpointer _ , Tarray _ _ => cmp_case_pp
  | Tarray _ _ ,Tpointer _ => cmp_case_pp
  | Tarray _ _ ,Tarray _ _ => cmp_case_pp
  | _ , _ => cmp_default
  end.

Inductive classify_fun_cases : Set:=
  | fun_case_f: typelist -> type -> classify_fun_cases   (* type fun | ptr fun*)
  | fun_default: classify_fun_cases . (* other *)

Definition classify_fun (ty: type) :=
  match ty with 
  | Tfunction args res => fun_case_f args res
  | Tpointer (Tfunction args res) => fun_case_f args res
  | _ => fun_default
  end.

(** Mapping between Clight types and Cminor types and external functions *)

Definition typ_of_type (t: type) : AST.typ :=
  match t with
  | Tfloat _ => AST.Tfloat
  | _ => AST.Tint
  end.

Definition opttyp_of_type (t: type) : option AST.typ :=
  match t with
  | Tvoid => None
  | Tfloat _ => Some AST.Tfloat
  | _ => Some AST.Tint
  end.

Fixpoint typlist_of_typelist (tl: typelist) : list AST.typ :=
  match tl with
  | Tnil => nil
  | Tcons hd tl => typ_of_type hd :: typlist_of_typelist tl
  end.

Definition signature_of_type (args: typelist) (res: type) : signature :=
  mksignature (typlist_of_typelist args) (opttyp_of_type res).

Definition external_function
    (id: ident) (targs: typelist) (tres: type) : AST.external_function :=
  mkextfun id (signature_of_type targs tres).
