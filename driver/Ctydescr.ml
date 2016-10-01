open Printf
open Camlcoq
open Tydesc

let check ty x = TyIO.check x ty; true
  
(* From stdlib *)

let list t = List t
let pair t1 t2 = Tuple [t1;t2]

let rec repr_nat = Sum("nat", [
  "O", [];
  "S", [repr_nat]
])

let nat = Base {
  base_name = "nat";
  base_check = check repr_nat;
  base_parse = (fun synt s -> assert false);
  base_print = (fun synt x ->
    let s = string_of_int (Nat.to_int x) in
    match synt with
    | `Coq -> s ^ "%nat"
    |  _   -> s)
}

let rec repr_positive = Sum("positive", [
  "xI", [repr_positive];
  "xO", [repr_positive];
  "xH", []
])

let positive = Base {
  base_name = "positive";
  base_check = check repr_positive;
  base_parse = (fun synt s -> assert false);
  base_print = (fun synt x -> Z.to_string (Z.Zpos x))
}

let repr_N = Sum("N", [
  "N0", [];
  "Npos", [repr_positive]
])

let _N = Base {
  base_name = "N";
  base_check = check repr_N;
  base_parse = (fun synt s -> assert false);
  base_print = (fun synt x ->
    let y = match x with N.N0 -> Z.Z0 | N.Npos p -> Z.Zpos p in
    let s = Z.to_string y in
    match synt with
    | `Coq -> s ^ "%N"
    |  _   -> s)
}

let repr_Z = Sum("Z", [
  "Z0", [];
  "Zpos", [repr_positive];
  "Zneg", [repr_positive]
])

let _Z = Base {
  base_name = "Z";
  base_check = check repr_Z;
  base_parse = (fun synt s -> assert false);
  base_print = (fun synt x ->
    let s = Z.to_string x in
    match synt with
    | `Coq -> s ^ "%Z"
    |  _   -> s)
}

(* From Integers *)

let int = Base {
  base_name = "int";
  base_check = check repr_Z;
  base_parse = (fun synt s ->
    let (n, s') = get_number s in
    try (coqint_of_camlint (Int32.of_string n), s')
    with Failure _ ->
      raise (Parsing_failure(get_position s, sprintf "bad 'int' literal %S" n)));
  base_print = (fun synt x ->
    let s = Z.to_string x in
    match synt with
    | `Coq -> "(mkint " ^ s ^ "%Z)"
    |  _   -> s)
}

let int64 = Base {
  base_name = "int64";
  base_check = check repr_Z;
  base_parse = (fun synt s ->
    let (n, s') = get_number s in
    try (coqint_of_camlint64 (Int64.of_string n), s')
    with Failure _ ->
      raise (Parsing_failure(get_position s, sprintf "bad 'int64' literal %S" n)));
  base_print = (fun synt x ->
    let s = Z.to_string x in
    match synt with
    | `Coq -> "(mkint64 " ^ s ^ "%Z)"
    |  _   -> s)
}

(* From Floats *)

let nan_pl = positive

let binary_float = Sum("binary_float", [
  "B754_zero", [bool];
  "B754_infinity", [bool];
  "B754_nan", [bool; nan_pl];
  "B754_finite", [bool; positive; _Z]
])

let float = Base {
  base_name = "float";
  base_check = check binary_float;
  base_parse = (fun synt s ->
    let (n, s') = get_number s in
    try (Floats.Float.of_bits (coqint_of_camlint64 (Int64.of_string n)), s')
    with Failure _ ->
      raise (Parsing_failure(get_position s, sprintf "bad 'float' literal %S" n)));
  base_print = (fun synt x ->
    let s = Z.to_string (Floats.Float.to_bits x) in
    match synt with
    | `Coq -> "(mkfloat " ^ s ^ "%Z)"
    |  _   -> s)
}

let float32 = Base {
  base_name = "float32";
  base_check = check binary_float;
  base_parse = (fun synt s ->
    let (n, s') = get_number s in
    try (Floats.Float32.of_bits (coqint_of_camlint (Int32.of_string n)), s')
    with Failure _ ->
      raise (Parsing_failure(get_position s, sprintf "bad 'float32' literal %S" n)));
  base_print = (fun synt x ->
    let s = Z.to_string (Floats.Float.to_bits x) in
    match synt with
    | `Coq -> "(mkfloat32 " ^ s ^ "%Z)"
    |  _   -> s)
}

(* From Maps *)

let ptree a =
  let rec t = Sum(sprintf "PTree.t[%s]" (describe_ty a), [
    "Leaf", [];
    "Node", [t; option a; t]
  ]) in t

(* From AST *)

let ident = positive

let typ = Sum("typ", [
  "AST.Tint", [];
  "AST.Tfloat", [];
  "AST.Tlong", [];
  "AST.Tsingle", [];
  "AST.Tany32", [];
  "AST.Tany64", [];
])

let calling_convention = Record("calling_convention", [
  "cc_vararg", bool;
  "cc_structret", bool;
])

let default_calling_convention = {
  dfl_val = AST.cc_default;
  dfl_print = (function `Coq -> Some "cc_default" | _ -> None)
}

let calling_convention_d =
  Default(calling_convention, default_calling_convention)

let signature = Record("signature", [
  "sig_args", list typ;
  "sig_res", option typ;
  "sig_cc", calling_convention_d;
])

let memory_chunk = Sum("memory_chunk", [
  "Mint8signed", [];
  "Mint8unsigned", [];
  "Mint16signed", [];
  "Mint16unsigned", [];
  "Mint32", [];
  "Mint64", [];
  "Mfloat32", [];
  "Mfloat64", [];
  "Many32", [];
  "Many64", [];
])

let init_data = Sum("init_data", [
  "Init_int8", [int];
  "Init_int16", [int];
  "Init_int32", [int];
  "Init_int64", [int64];
  "Init_float32", [float32];
  "Init_float64", [float];
  "Init_space", [_Z];
  "Init_addrof", [ident; int];
])

let globvar v = Record(sprintf "globvar[%s]" (describe_ty v), [
  "gvar_info", v;
  "gvar_init", list init_data;
  "gvar_readonly", bool;
  "gvar_volatile", bool;
])

let globdef f v = Sum(sprintf "globdef[%s][%s]" (describe_ty f) (describe_ty v), [
  "Gfun", [f];
  "Gvar", [globvar v];
])

let external_function = Sum("external_function", [
  "EF_external", [ident; signature];
  "EF_builtin", [ident; signature];
  "EF_vload", [memory_chunk];
  "EF_vstore", [memory_chunk];
  "EF_vload_global", [memory_chunk; ident; int];
  "EF_vstore_global", [memory_chunk; ident; int];
  "EF_malloc", [];
  "EF_free", [];
  "EF_memcpy", [_Z; _Z];
  "EF_annot", [ident; list typ];
  "EF_annot_val", [ident; typ];
  "EF_inline_asm", [ident; signature; list string];
])

(* From Values *)

let block = positive

let val_ = Sum("val", [
  "Vundef", [];
  "Vint", [int];
  "Vlong", [int64];
  "Vfloat", [float];
  "Vsingle", [float32];
  "Vptr", [block; int];
])

(* From Ctypes *)

let signedness = Sum("signedness", [
  "Signed", [];
  "Unsigned", [];
])

let intsize = Sum("intsize", [
  "I8", [];
  "I16", [];
  "I32", [];
  "IBool", [];
])

let floatsize = Sum("floatsize", [
  "F32", [];
  "F64", [];
])

let attr = Record("attr", [
  "attr_volatile", bool;
  "attr_alignas", option _N;
])

let attr_default = {
  dfl_val = Ctypes.noattr;
  dfl_print = (function `Coq -> Some "noattr" | _ -> None)
}

let attr_d = Default(attr, attr_default)

let rec type_ = Sum("type", [
  "Tvoid", [];
  "Tint", [intsize; signedness; attr_d];
  "Tlong", [signedness; attr_d];
  "Tfloat", [floatsize; attr_d];
  "Tpointer", [type_; attr_d];
  "Tarray", [type_; _Z; attr_d];
  "Tfunction", [typelist; type_; calling_convention_d];
  "Tstruct", [ident; attr_d];
  "Tunion", [ident; attr_d];
])
and typelist = Sum("typelist", [
  "Tnil", [];
  "Tcons", [type_; typelist];
])

let  struct_or_union = Sum("struct_or_union", [
  "Struct", [];
  "Union", [];
])

let members = list (pair ident type_)

let composite_definition = Sum("composite_definition", [
  "Composite", [ident; struct_or_union; members; attr_d];
])

let composite = Record("composite",[
  "co_su", struct_or_union;
  "co_members", members;
  "co_attr", attr;
  "co_sizeof", _Z;
  "co_alignof", _Z;
  "co_rank", nat
])

let composite_env = ptree composite

(* From Cop *)

let unary_operation = Sum("unary_operation", [
  "Onotbool", [];
  "Onotint", [];
  "Oneg", [];
  "Oabsfloat", [];
])

let binary_operation = Sum("binary_operation", [
  "Oadd", [];
  "Osub", [];
  "Omul", [];
  "Odiv", [];
  "Omod", [];
  "Oand", [];
  "Oor", [];
  "Oxor", [];
  "Oshl", [];
  "Oshr", [];
  "Oeq", [];
  "One", [];
  "Olt", [];
  "Ogt", [];
  "Ole", [];
  "Oge", [];
])

let incr_or_decr = Sum("incr_or_decr", [
  "Incr", [];
  "Decr", [];
])

(* From Csyntax *)

let rec expr = Sum("expr", [
  "Eval", [val_; type_];
  "Evar", [ident; type_];
  "Efield", [expr; ident; type_];
  "Evalof", [expr; type_];
  "Ederef", [expr; type_];
  "Eaddrof", [expr; type_];
  "Eunop", [unary_operation; expr; type_];
  "Ebinop", [binary_operation; expr; expr; type_];
  "Ecast", [expr; type_];
  "Eseqand", [expr; expr; type_];
  "Eseqor", [expr; expr; type_];
  "Econdition", [expr; expr; expr; type_];
  "Esizeof", [type_; type_];
  "Ealignof", [type_; type_];
  "Eassign", [expr; expr; type_];
  "Eassignop", [binary_operation; expr; expr; type_; type_];
  "Epostincr", [incr_or_decr; expr; type_];
  "Ecomma", [expr; expr; type_];
  "Ecall", [expr; exprlist; type_];
  "Ebuiltin", [external_function; typelist; exprlist; type_];
  "Eloc", [block; int; type_];
  "Eparen", [expr; type_; type_];
])
and exprlist = Sum("exprlist", [
  "Enil", [];
  "Econs", [expr; exprlist];
])

let label = ident

let rec statement = Sum("statement", [
  "Sskip", [];
  "Sdo", [expr];
  "Ssequence", [statement; statement];
  "Sifthenelse", [expr; statement; statement];
  "Swhile", [expr; statement];
  "Sdowhile", [expr; statement];
  "Sfor", [statement; expr; statement; statement];
  "Sbreak", [];
  "Scontinue", [];
  "Sreturn", [option expr];
  "Sswitch", [expr; labeled_statements];
  "Slabel", [label; statement];
  "Sgoto", [label];
])
and labeled_statements = Sum("labeled_statements", [
  "LSnil", [];
  "LScons", [option _Z; statement; labeled_statements];
])

let function_ = Record("function", [
  "fn_return", type_;
  "fn_callconv", calling_convention_d;
  "fn_params", list (pair ident type_);
  "fn_vars", list (pair ident type_);
  "fn_body", statement;
])

let fundef = Sum("fundef", [
  "Internal", [function_];
  "External", [external_function; typelist; type_; calling_convention_d];
])

let repr_program = Record("program", [
  "prog_defs", list (pair ident (globdef fundef type_));
  "prog_public", list ident;
  "prog_main", ident;
  "prog_types", list composite_definition;
  "prog_comp_env", composite_env
])

type program2 = Program of
   (AST.ident * (Csyntax.fundef, Ctypes.coq_type) AST.globdef) list
 * AST.ident list
 * AST.ident
 * Ctypes.composite_definition list

let program2 = Sum("program2", [
  "mkprogram", [list (pair ident (globdef fundef type_));
                list ident;
                ident;
                list composite_definition]
])

let program2_of_program p =
  Csyntax.(Program(p.prog_defs, p.prog_public, p.prog_main, p.prog_types))
let program_of_program2 (Program(d,p,m,t)) =
  Csyntax.(
    match Ctypes.build_composite_env t with
    | Errors.Error _ -> assert false
    | Errors.OK e -> {prog_defs = d; prog_public = p; prog_main = m;
                      prog_types = t; prog_comp_env = e})

let program = As(program2, {
  conv_name = "program";
  conv_check = check repr_program;
  conv_out = program2_of_program;
  conv_in = program_of_program2
})

