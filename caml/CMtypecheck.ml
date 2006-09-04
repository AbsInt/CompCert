(* A type-checker for Cminor *)

open Printf
open Datatypes
open CList
open Camlcoq
open AST
open Integers
open Op
open Cminor

exception Error of string

let name_of_typ = function Tint -> "int" | Tfloat -> "float"

type ty = Base of typ | Var of ty option ref

let newvar () = Var (ref None)
let tint = Base Tint
let tfloat = Base Tfloat

let ty_of_typ = function Tint -> tint | Tfloat -> tfloat

let rec ty_of_sig_args = function
  | Coq_nil -> []
  | Coq_cons(t, l) -> ty_of_typ t :: ty_of_sig_args l

let rec repr t =
  match t with
  | Base _ -> t
  | Var r -> match !r with None -> t | Some t' -> repr t'

let unify t1 t2 =
  match (repr t1, repr t2) with
  | Base b1, Base b2 ->
      if b1 <> b2 then
        raise (Error (sprintf "Expected type %s, actual type %s\n"
                              (name_of_typ b1) (name_of_typ b2)))
  | Base b, Var r -> r := Some (Base b)
  | Var r, Base b -> r := Some (Base b)
  | Var r1, Var r2 -> r1 := Some (Var r2)

let unify_list l1 l2 =
  let ll1 = List.length l1 and ll2 = List.length l2 in
  if ll1 <> ll2 then
    raise (Error (sprintf "Arity mismatch: expected %d, actual %d\n" ll1 ll2));
  List.iter2 unify l1 l2

let type_var env id =
  try
    List.assoc id env
  with Not_found ->
    raise (Error (sprintf "Unbound variable %s\n" (extern_atom id)))

let type_letvar env n =
  let n = camlint_of_nat n in
  try
    List.nth env n
  with Not_found ->
    raise (Error (sprintf "Unbound let variable #%d\n" n))

let name_of_comparison = function
  | Ceq -> "eq"
  | Cne -> "ne"
  | Clt -> "lt"
  | Cle -> "le"
  | Cgt -> "gt"
  | Cge -> "ge"

let type_condition = function
  | Ccomp _ -> [tint;tint]
  | Ccompu _ -> [tint;tint]
  | Ccompimm _ -> [tint]
  | Ccompuimm _ -> [tint]
  | Ccompf _ -> [tfloat;tfloat]
  | Cnotcompf _ -> [tfloat;tfloat]
  | Cmaskzero _ -> [tint]
  | Cmasknotzero _ -> [tint]

let name_of_condition = function
  | Ccomp c -> sprintf "comp %s" (name_of_comparison c)
  | Ccompu c ->  sprintf "compu %s" (name_of_comparison c)
  | Ccompimm(c, n) -> sprintf "compimm %s %ld" (name_of_comparison c) (camlint_of_coqint n)
  | Ccompuimm(c, n) -> sprintf "compuimm %s %ld" (name_of_comparison c) (camlint_of_coqint n)
  | Ccompf c -> sprintf "compf %s" (name_of_comparison c)
  | Cnotcompf c -> sprintf "notcompf %s" (name_of_comparison c)
  | Cmaskzero n -> sprintf "maskzero %ld" (camlint_of_coqint n)
  | Cmasknotzero n ->  sprintf "masknotzero %ld" (camlint_of_coqint n)

let type_operation = function
  | Omove -> let v = newvar() in [v], v
  | Ointconst _ -> [], tint
  | Ofloatconst _ -> [], tfloat
  | Oaddrsymbol _ -> [], tint
  | Oaddrstack _ -> [], tint
  | Oundef -> [], newvar()
  | Ocast8signed -> [tint], tint
  | Ocast16signed -> [tint], tint
  | Ocast8unsigned -> [tint], tint
  | Ocast16unsigned -> [tint], tint
  | Oadd -> [tint;tint], tint
  | Oaddimm _ -> [tint], tint
  | Osub -> [tint;tint], tint
  | Osubimm _ -> [tint], tint
  | Omul -> [tint;tint], tint
  | Omulimm _ -> [tint], tint
  | Odiv -> [tint;tint], tint
  | Odivu -> [tint;tint], tint
  | Oand -> [tint;tint], tint
  | Oandimm _ -> [tint], tint
  | Oor -> [tint;tint], tint
  | Oorimm _ -> [tint], tint
  | Oxor -> [tint;tint], tint
  | Oxorimm _ -> [tint], tint
  | Onand -> [tint;tint], tint
  | Onor -> [tint;tint], tint
  | Onxor -> [tint;tint], tint
  | Oshl -> [tint;tint], tint
  | Oshr -> [tint;tint], tint
  | Oshrimm _ -> [tint], tint
  | Oshrximm _ -> [tint], tint
  | Oshru -> [tint;tint], tint
  | Orolm _ -> [tint], tint
  | Onegf -> [tfloat], tfloat
  | Oabsf -> [tfloat], tfloat
  | Oaddf -> [tfloat;tfloat], tfloat
  | Osubf -> [tfloat;tfloat], tfloat
  | Omulf -> [tfloat;tfloat], tfloat
  | Odivf -> [tfloat;tfloat], tfloat
  | Omuladdf -> [tfloat;tfloat;tfloat], tfloat
  | Omulsubf -> [tfloat;tfloat;tfloat], tfloat
  | Osingleoffloat -> [tfloat], tfloat
  | Ointoffloat -> [tfloat], tint
  | Ofloatofint -> [tint], tfloat
  | Ofloatofintu -> [tint], tfloat
  | Ocmp c -> type_condition c, tint

let name_of_operation = function
  | Omove -> "move"
  | Ointconst n -> sprintf "intconst %ld" (camlint_of_coqint n)
  | Ofloatconst n -> sprintf "floatconst %g" n
  | Oaddrsymbol (s, ofs) -> sprintf "addrsymbol %s %ld" (extern_atom s) (camlint_of_coqint ofs)
  | Oaddrstack n -> sprintf "addrstack %ld" (camlint_of_coqint n)
  | Oundef -> "undef"
  | Ocast8signed -> "cast8signed"
  | Ocast16signed -> "cast16signed"
  | Ocast8unsigned -> "cast8unsigned"
  | Ocast16unsigned -> "cast16unsigned"
  | Oadd -> "add"
  | Oaddimm n -> sprintf "addimm %ld" (camlint_of_coqint n)
  | Osub -> "sub"
  | Osubimm n -> sprintf "subimm %ld" (camlint_of_coqint n)
  | Omul -> "mul"
  | Omulimm n -> sprintf "mulimm %ld" (camlint_of_coqint n)
  | Odiv -> "div"
  | Odivu -> "divu"
  | Oand -> "and"
  | Oandimm n -> sprintf "andimm %ld" (camlint_of_coqint n)
  | Oor -> "or"
  | Oorimm n -> sprintf "orimm %ld" (camlint_of_coqint n)
  | Oxor -> "xor"
  | Oxorimm n -> sprintf "xorimm %ld" (camlint_of_coqint n)
  | Onand -> "nand"
  | Onor -> "nor"
  | Onxor -> "nxor"
  | Oshl -> "shl"
  | Oshr -> "shr"
  | Oshrimm n -> sprintf "shrimm %ld" (camlint_of_coqint n)
  | Oshrximm n -> sprintf "shrximm %ld" (camlint_of_coqint n)
  | Oshru -> "shru"
  | Orolm(n, m) -> sprintf "rolm %ld %ld" (camlint_of_coqint n) (camlint_of_coqint m)
  | Onegf -> "negf"
  | Oabsf -> "absf"
  | Oaddf -> "addf"
  | Osubf -> "subf"
  | Omulf -> "mulf"
  | Odivf -> "divf"
  | Omuladdf -> "muladdf"
  | Omulsubf -> "mulsubf"
  | Osingleoffloat -> "singleoffloat"
  | Ointoffloat -> "intoffloat"
  | Ofloatofint -> "floatofint"
  | Ofloatofintu -> "floatofintu"
  | Ocmp c -> name_of_condition c

let type_addressing = function
  | Aindexed _ -> [tint]
  | Aindexed2 -> [tint;tint]
  | Aglobal _ -> []
  | Abased _ -> [tint]
  | Ainstack _ -> []

let name_of_addressing = function
  | Aindexed n -> sprintf "indexed %ld" (camlint_of_coqint n)
  | Aindexed2 -> sprintf "indexed2"
  | Aglobal(s, ofs) -> sprintf "global %s %ld" (extern_atom s) (camlint_of_coqint ofs)
  | Abased(s, ofs) -> sprintf "based %s %ld" (extern_atom s) (camlint_of_coqint ofs)
  | Ainstack n -> sprintf "instack %ld" (camlint_of_coqint n)

let type_chunk = function
  | Mint8signed -> tint
  | Mint8unsigned -> tint
  | Mint16signed -> tint
  | Mint16unsigned -> tint
  | Mint32 -> tint
  | Mfloat32 -> tfloat
  | Mfloat64 -> tfloat

let name_of_chunk = function
  | Mint8signed -> "int8signed"
  | Mint8unsigned -> "int8unsigned"
  | Mint16signed -> "int16signed"
  | Mint16unsigned -> "int16unsigned"
  | Mint32 -> "int32"
  | Mfloat32 -> "float32"
  | Mfloat64 -> "float64"

let rec type_expr env lenv e =
  match e with
  | Evar id ->
      type_var env id
  | Eassign(id, e1) ->
      let tid = type_var env id in
      let te1 = type_expr env lenv e1 in
      begin try
        unify tid te1
      with Error s ->
        raise (Error (sprintf "In assignment to %s:\n%s" (extern_atom id) s))
      end;
      tid
  | Eop(op, el) ->
      let tel = type_exprlist env lenv el in
      let (targs, tres) = type_operation op in
      begin try
        unify_list targs tel
      with Error s ->
        raise (Error (sprintf "In application of operator %s:\n%s"
                              (name_of_operation op) s))
      end;
      tres
  | Eload(chunk, addr, el) ->
      let tel = type_exprlist env lenv el in
      begin try
        unify_list (type_addressing addr) tel
      with Error s ->
        raise (Error (sprintf "In load %s %s:\n%s"
                              (name_of_chunk chunk) (name_of_addressing addr) s))
      end;
      type_chunk chunk
  | Estore(chunk, addr, el, e1) ->
      let tel = type_exprlist env lenv el in
      let te1 = type_expr env lenv e1 in
      begin try
        unify_list (type_addressing addr) tel;
        unify (type_chunk chunk) te1
      with Error s ->
        raise (Error (sprintf "In store %s %s:\n%s"
                              (name_of_chunk chunk) (name_of_addressing addr) s))
      end;
      te1
  | Ecall(sg, e1, el) ->
      let te1 = type_expr env lenv e1 in
      let tel = type_exprlist env lenv el in
      begin try
        unify tint te1;
        unify_list (ty_of_sig_args sg.sig_args) tel
      with Error s ->
        raise (Error (sprintf "In call:\n%s" s))
      end;
      begin match sg.sig_res with
      | None -> tint (*???*)
      | Some t -> ty_of_typ t
      end
  | Econdition(e1, e2, e3) ->
      type_condexpr env lenv e1;
      let te2 = type_expr env lenv e2 in
      let te3 = type_expr env lenv e3 in
      begin try
        unify te2 te3
      with Error s ->
        raise (Error (sprintf "In conditional expression:\n%s" s))
      end;
      te2
  | Elet(e1, e2) ->
      let te1 = type_expr env lenv e1 in
      let te2 = type_expr env (te1 :: lenv) e2 in
      te2
  | Eletvar n ->
      type_letvar lenv n
  | Ealloc e ->
      let te = type_expr env lenv e in
      begin try
        unify tint te
      with Error s ->
        raise (Error (sprintf "In alloc:\n%s" s))
      end;
      tint

and type_exprlist env lenv el =
  match el with
  | Enil -> []
  | Econs (e1, et) ->
      let te1 = type_expr env lenv e1 in
      let tet = type_exprlist env lenv et in
      (te1 :: tet)

and type_condexpr env lenv ce =
  match ce with
  | CEtrue -> ()
  | CEfalse -> ()
  | CEcond(c, el) ->
      let tel = type_exprlist env lenv el in
      begin try
        unify_list (type_condition c) tel
      with Error s ->
        raise (Error (sprintf "In condition %s:\n%s" (name_of_condition c) s))
      end
  | CEcondition(ce1, ce2, ce3) ->
      type_condexpr env lenv ce1;
      type_condexpr env lenv ce2;
      type_condexpr env lenv ce3

let rec type_stmt env blk ret s =
  match s with
  | Sskip -> ()
  | Sexpr e -> 
      ignore (type_expr env [] e)
  | Sseq(s1, s2) ->
      type_stmt env blk ret s1;
      type_stmt env blk ret s2
  | Sifthenelse(ce, s1, s2) ->
      type_condexpr env [] ce;
      type_stmt env blk ret s1;
      type_stmt env blk ret s2
  | Sloop s1 ->
      type_stmt env blk ret s1
  | Sblock s1 ->
      type_stmt env (blk + 1) ret s1
  | Sexit n ->
      if camlint_of_nat n >= blk then
        raise (Error (sprintf "Bad exit(%d)\n" (camlint_of_nat n)))
  | Sswitch(e, cases, deflt) ->
      unify (type_expr env [] e) tint
  | Sreturn None ->
      begin match ret with
      | None -> ()
      | Some tret -> raise (Error ("return without argument"))
      end
  | Sreturn (Some e) ->
      begin match ret with
      | None -> raise (Error "return with argument")
      | Some tret -> 
          begin try
            unify (type_expr env [] e) (ty_of_typ tret)
          with Error s ->
            raise (Error (sprintf "In return:\n%s" s))
          end
      end

let rec env_of_vars idl =
  match idl with
  | Coq_nil -> []
  | Coq_cons(id1, idt) -> (id1, newvar()) :: env_of_vars idt

let type_function id f =
  try
    type_stmt
       (env_of_vars f.fn_vars @ env_of_vars f.fn_params)
       0 f.fn_sig.sig_res f.fn_body
  with Error s ->
    raise (Error (sprintf "In function %s:\n%s" (extern_atom id) s))

let type_fundef (Coq_pair (id, fd)) =
  match fd with
  | Internal f -> type_function id f
  | External ef -> ()

let type_program p =
  coqlist_iter type_fundef p.prog_funct; p
