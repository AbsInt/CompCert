open Printf

type ty =
  | Int8u  | Int8s
  | Int16u | Int16s
  | Int32
  | Int64
  | Float32
  | Float64
  | String
  | Struct of int * (string * ty) list

type funsig = {
    args: ty list;
    varargs: ty list;    (* empty list if fixed-argument function *)
    res: ty option
  }

type value =
  | VInt of int
  | VInt32 of int32
  | VInt64 of int64
  | VFloat of float
  | VString of string
  | VStruct of value list

(* Print a value.  If [norm] is true, re-normalize values of
   small numerical types. *)

let zero_ext n k =
  n land ((1 lsl k) - 1)

let sign_ext n k =
  (n lsl (Sys.int_size - k)) asr (Sys.int_size - k)

let normalize_float32 n =
  Int32.float_of_bits (Int32.bits_of_float n)

let rec print_value ~norm oc (ty, v) =
  match (ty, v) with
  | (Int8u, VInt n) ->
      fprintf oc "%d" (if norm then zero_ext n 8 else n)
  | (Int8s, VInt n) ->
      fprintf oc "%d" (if norm then sign_ext n 8 else n)
  | (Int16u, VInt n) ->
      fprintf oc "%d" (if norm then zero_ext n 16 else n)
  | (Int16s, VInt n) ->
      fprintf oc "%d" (if norm then sign_ext n 16 else n)
  | (Int32, VInt32 n) ->
      fprintf oc "%ld" n
  | (Int64, VInt64 n) ->
      fprintf oc "%Ld" n
  | (Float32, VFloat f) ->
      if norm
      then fprintf oc "%hF" (normalize_float32 f)
      else fprintf oc "%h" f
  | (Float64, VFloat f) ->
      fprintf oc "%h" f
  | (String, VString s) ->
      fprintf oc "%S" s
  | (Struct(id, (fld1, ty1) :: members), VStruct (v1 :: vl)) ->
      fprintf oc "(struct s%d){" id;
      print_value ~norm oc (ty1, v1);
      List.iter2
        (fun (fld, ty) v -> fprintf oc ", %a" (print_value ~norm) (ty, v))
        members vl;
      fprintf oc "}"
  | _, _ ->
      assert false

(* Generate random values of the given type *)

let random_char () = Char.chr (Char.code 'a' + Random.int 26)

let random_string () =
  let len = Random.int 3 in
  String.init len (fun _ -> random_char ())

let random_int () =
  Random.bits() - (1 lsl 29)

let random_int32 () =
  Int32.(logxor (of_int (Random.bits()))
                (shift_left (of_int (Random.bits())) 30))

let random_int64 () =
  Int64.(logxor (of_int (Random.bits()))
                (logxor (shift_left (of_int (Random.bits())) 30)
                        (shift_left (of_int (Random.bits())) 60)))

let random_float64 () =
  Random.float 100.0 -. 50.0

(* Returns a random value.  Small numerical types are not normalized. *)

let rec random_value = function
  | Int8u | Int8s | Int16u | Int16s ->
      VInt (random_int())
  | Int32 ->
      VInt32 (random_int32())
  | Int64 ->
      VInt64 (random_int64())
  | Float32 | Float64 ->
      VFloat (random_float64())
  | String ->
      VString (random_string())
  | Struct(id, members) ->
      VStruct (List.map (fun (fld, ty) -> random_value ty) members)

let random_retvalue = function
  | None -> VInt 0 (* meaningless *)
  | Some ty -> random_value ty

(* Generate function declaration, definition, and call *)

let string_of_ty = function
  | Int8u -> "unsigned char"
  | Int8s -> "signed char"
  | Int16u -> "unsigned short"
  | Int16s -> "short"
  | Int32 -> "int"
  | Int64 -> "long long"
  | Float32 -> "float"
  | Float64 -> "double"
  | String -> "char *"
  | Struct(id, _) -> sprintf "struct s%d" id

let string_of_optty = function
  | None -> "void"
  | Some t -> string_of_ty t

let declare_struct oc id members =
  fprintf oc "struct s%d {\n" id;
  List.iter
    (fun (fld, ty) -> fprintf oc "  %s %s;\n" (string_of_ty ty) fld)
    members;
  fprintf oc "};\n"

let declare_function oc name sg =
  fprintf oc "%s %s(" (string_of_optty sg.res) name;
  begin match sg.args with
  | [] -> fprintf oc "void"
  | t0 :: tl ->
      fprintf oc "%s x0" (string_of_ty t0);
      List.iteri (fun n t -> fprintf oc ", %s x%d" (string_of_ty t) (n + 1)) tl;
      if sg.varargs <> [] then fprintf oc ", ..."
  end;
  fprintf oc ")"

let rec compare_value oc variable value ty =
  match ty with
  | Struct(id, members) ->
      begin match value with
      | VStruct vl ->
          List.iter2
            (fun (fld, ty) v ->
              compare_value oc (sprintf "%s.%s" variable fld) v ty)
            members vl
      | _ ->
          assert false
      end
  | String ->
      fprintf oc "  check (strcmp(%s, %a) == 0);\n"
                 variable (print_value ~norm:true) (ty, value)
  | _ ->
      fprintf oc "  check (%s == %a);\n"
                 variable (print_value ~norm:true) (ty, value)

let define_function oc name sg vargs vres =
  declare_function oc name sg;
  fprintf oc "\n{\n";
  if sg.varargs <> [] then begin
    fprintf oc "  va_list l;\n";
    fprintf oc "  va_start(l, x%d);\n" (List.length sg.args - 1);
    List.iteri
      (fun n t ->
        fprintf oc "  %s x%d = va_arg(l, %s);\n"
                   (string_of_ty t) (n + List.length sg.args) (string_of_ty t))
      sg.varargs;
    fprintf oc "  va_end(l);\n";
  end;
  List.iteri
    (fun n (t, v) -> compare_value oc (sprintf "x%d" n) v t)
    (List.combine (sg.args @ sg.varargs) vargs);
  begin match sg.res with
    | None -> ()
    | Some tres ->
        fprintf oc "  return %a;\n" (print_value ~norm:false) (tres, vres)
  end;
  fprintf oc "}\n\n"

let call_function oc name sg vargs vres =
  fprintf oc "void call_%s(void)\n" name;
  fprintf oc "{\n";
  begin match sg.res with
  | None -> fprintf oc "  %s(" name
  | Some t -> fprintf oc "  %s r = %s(" (string_of_ty t) name
  end;
  begin match (sg.args @ sg.varargs), vargs with
  | [], [] -> ()
  | ty1 :: tyl, v1 :: vl ->
      print_value ~norm:false oc (ty1, v1);
      List.iter2
        (fun ty v -> fprintf oc ", %a" (print_value ~norm:false) (ty, v))
        tyl vl
  | _, _ ->
      assert false
  end;
  fprintf oc ");\n";
  begin match sg.res with
  | None -> ()
  | Some tyres -> compare_value oc "r" vres tyres
  end;
  fprintf oc "}\n\n"

let function_counter = ref 0

let generate_one_test oc0 oc1 oc2 sg =
  incr function_counter;
  let num = !function_counter in
  let vargs = List.map random_value (sg.args @ sg.varargs) in
  let vres = random_retvalue sg.res in
  let name = "f" ^ string_of_int num in
  fprintf oc0 "extern ";
  declare_function oc0 name sg;
  fprintf oc0 ";\n";
  define_function oc1 name sg vargs vres;
  call_function oc2 name sg vargs vres

let call_all_test oc =
  fprintf oc "int main(void)\n";
  fprintf oc "{\n";
  fprintf oc "  alarm(60);\n";
  for i = 1 to !function_counter do
    fprintf oc "  call_f%d();\n" i
  done;
  fprintf oc "  return failed;\n";
  fprintf oc "}\n"

(* Generate interesting function signatures *)

let all_ty =
  [| Int8u; Int8s; Int16u; Int16s; Int32; Int64; Float32; Float64; String |]

let base_ty =
  [| Int32; Int64; Float32; Float64 |]

let makerun pat len =
  let rec make i l =
    if l <= 0
    then []
    else pat.(i) :: make ((i + 1) mod (Array.length pat)) (l - 1)
  in make 0 len

let gen_fixed_sigs f =
  (* All possible return types *)
  Array.iter
    (fun ty -> f { args = []; varargs = []; res = Some ty })
    all_ty;
  (* All possible argument types *)
  Array.iter
    (fun ty -> f { args = [ty]; varargs = []; res = None })
    all_ty;
  (* 2 arguments of base types *)
  Array.iter
    (fun ty1 ->
      Array.iter
        (fun ty2 -> f { args = [ty1; ty2]; varargs = []; res = None })
        base_ty)
    base_ty;
  (* 3 arguments of base types *)
  Array.iter
    (fun ty1 ->
      Array.iter
        (fun ty2 ->
          Array.iter
            (fun ty3 -> f { args = [ty1; ty2; ty3]; varargs = []; res = None })
            base_ty)
        base_ty)
    base_ty;
  (* 4 arguments of base types *)
  Array.iter
    (fun ty1 ->
      Array.iter
        (fun ty2 ->
          Array.iter
            (fun ty3 ->
              Array.iter
                (fun ty4 ->
                   f { args = [ty1; ty2; ty3; ty4]; varargs = []; res = None })
                base_ty)
            base_ty)
        base_ty)
    base_ty;
  (* Runs of 6, 8, 10, 12, 16, 32 arguments of various patterns *)
  Array.iter
    (fun pat ->
      Array.iter
        (fun len ->
          f { args = makerun pat len; varargs = []; res = None })
        [| 6;8;10;12;16;32 |])
    [| [|Int32|]; [|Int64|]; [|Float32|]; [|Float64|];
       [|Int32;Int64|]; [|Int32;Float32|]; [|Int32;Float64|]; 
       [|Int64;Float32|]; [|Int64;Float64|]; [|Float32;Float64|];
       [|Int32;Int64;Float32;Float64|]
    |]

let split_list l n =
  let rec split l n accu =
    if n <= 0 then (List.rev accu, l) else
      match l with
      | [] -> assert false
      | h :: t -> split t (n - 1) (h :: accu)
  in split l n []

let is_vararg_type = function
  | Int32 | Int64 | Float64 | String -> true
  | _ -> false

let gen_vararg_sigs f =
  let make_vararg sg n =
    if List.length sg.args > n then begin
      let (fixed, varia) = split_list sg.args n in
      if List.for_all is_vararg_type varia
      && is_vararg_type (List.nth fixed (n - 1)) then
        f { args = fixed; varargs = varia; res = sg.res }
    end
  in
    gen_fixed_sigs
     (fun sg -> make_vararg sg 2; make_vararg sg 6; make_vararg sg 14)

(* Generate interesting struct types *)

let struct_counter = ref 0

let mkstruct oc members =
  incr struct_counter;
  let id = !struct_counter in
  declare_struct oc id members;
  Struct(id, members)

let member_ty =
  [| Int8u; Int16u; Int32; Int64; Float32; Float64 |]

let gen_structs oc f =
  (* One field of any type *)
  Array.iter
    (fun ty -> f (mkstruct oc [("a", ty)]))
    all_ty;
  (* Two fields of interesting types *)
  Array.iter
    (fun ty1 ->
      Array.iter
        (fun ty2 -> f (mkstruct oc [("a", ty1); ("b", ty2)]))
        member_ty)
    member_ty;
  (* 3, 4, 6, 8 fields of identical interesting type *)
  Array.iter
    (fun ty ->
       f (mkstruct oc [("a", ty); ("b", ty); ("c", ty)]);
       f (mkstruct oc [("a", ty); ("b", ty); ("c", ty); ("d", ty)]);
       f (mkstruct oc [("a", ty); ("b", ty); ("c", ty); ("d", ty);
                       ("e", ty); ("f", ty)]);
       f (mkstruct oc [("a", ty); ("b", ty); ("c", ty); ("d", ty);
                       ("e", ty); ("f", ty); ("g", ty); ("h", ty)]))
    member_ty

let gen_struct_sigs oc f =
  let make ty =
    (* Struct return *)
    f { args = []; varargs = []; res = Some ty };
    (* Struct passing (once, twice) *)
    f { args = [ty]; varargs = []; res = None };
    f { args = [ty;ty]; varargs = []; res = None };
    (* Struct passing mixed with scalar arguments *)
    f { args = [Int32;ty]; varargs = []; res = None };
    f { args = [Float64;ty]; varargs = []; res = None }
  in
    gen_structs oc make

(* Random generation *)

let pick arr =
  arr.(Random.int (Array.length arr))

let big_ty = [| Int32; Int64; Float32; Float64; String |]

let vararg_ty =  [| Int32; Int64; Float64; String |]

let random_funsig vararg =
  let res = if Random.bool() then Some (pick all_ty) else None in
  let numargs = Random.int 12 in
  let args = List.init numargs (fun _ -> pick big_ty) in
  let numvarargs = 
    if vararg && numargs > 0 && is_vararg_type (List.nth args (numargs - 1))
    then 1 + Random.int 12
    else 0 in
  let varargs = List.init numvarargs (fun _ -> pick vararg_ty) in
  { args; varargs; res }

let header =
{|#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
|}

let checking_code = {|
extern int failed;

static void failure(const char * assertion, const char * file,
                    int line, const char * fn)
{
  fprintf(stderr, "%s:%d:%s: assertion %s failed\n", file, line, fn, assertion);
  failed = 1;
}

#define check(expr) ((expr) ? (void)0 : failure(#expr,__FILE__,__LINE__,__func__))
|}

let output_prefix = ref "abifuzz"
let gen_vararg = ref false
let gen_struct = ref false
let num_random = ref 0

let _ =
  Arg.parse [
     "-plain", Arg.Unit (fun () -> gen_vararg := false; gen_struct := false),
       " generate fixed-argument functions without structs";
     "-vararg", Arg.Set gen_vararg,
       " generate variable-argument functions";
     "-structs", Arg.Set gen_struct,
       " generate functions that exchange structs";
     "-o", Arg.String (fun s -> output_prefix := s),
       " <prefix> produce <prefix>.h, <prefix>def.c and <prefix>use.c files";
     "-rnd", Arg.Int (fun n -> num_random := n),
       " <num> produce <num> extra functions with random signatures";
     "-seed", Arg.Int Random.init,
       " <seed> use the given seed for randomization"
  ]
  (fun s -> raise (Arg.Bad ("don't know what to do with " ^ s)))
  "Usage: generator [options]\n\nOptions are:";
  let oc0 = open_out (!output_prefix ^ "_decl.h")
  and oc1 = open_out (!output_prefix ^ "_def.c")
  and oc2 = open_out (!output_prefix ^ "_use.c") in
  fprintf oc0 "%s\n%s\n" header checking_code;
  fprintf oc1 "%s#include \"%s_decl.h\"\n\n" header !output_prefix;
  fprintf oc2 "%s#include \"%s_decl.h\"\n\nint failed = 0;\n\n"
              header !output_prefix;
  let cont = generate_one_test oc0 oc1 oc2 in
  if !gen_vararg then gen_vararg_sigs cont
  else if !gen_struct then gen_struct_sigs oc0 cont
  else gen_fixed_sigs cont;
  for i = 1 to !num_random do
    cont (random_funsig !gen_vararg)
  done;
  call_all_test oc2;
  close_out oc0; close_out oc1; close_out oc2
