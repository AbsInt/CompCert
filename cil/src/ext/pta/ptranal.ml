(* MODIF: Loop constructor replaced by 3 constructors: While, DoWhile, For. *)

(*
 *
 * Copyright (c) 2001-2002,
 *  John Kodumal        <jkodumal@eecs.berkeley.edu>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)

exception Bad_return
exception Bad_function


open Cil

module H = Hashtbl

module A = Olf
exception UnknownLocation = A.UnknownLocation

type access = A.lvalue * bool

type access_map = (lval, access) H.t

(** a mapping from varinfo's back to fundecs *)
module VarInfoKey =
struct
  type t = varinfo
  let compare v1 v2 = v1.vid - v2.vid
end

module F = Map.Make (VarInfoKey)


(***********************************************************************)
(*                                                                     *)
(* Global Variables                                                    *)
(*                                                                     *)
(***********************************************************************)

let model_strings = ref false
let print_constraints = A.print_constraints
let debug_constraints = A.debug_constraints
let debug_aliases = A.debug_aliases
let smart_aliases = A.smart_aliases
let debug = A.debug
let analyze_mono = A.analyze_mono
let no_flow = A.no_flow
let no_sub = A.no_sub
let fun_ptrs_as_funs = ref false
let show_progress = ref false
let debug_may_aliases = ref false

let found_undefined = ref false

let conservative_undefineds = ref false

let current_fundec : fundec option ref = ref None

let fun_access_map : (fundec, access_map) H.t = H.create 64

(* A mapping from varinfos to fundecs *)
let fun_varinfo_map = ref F.empty

let current_ret : A.tau option ref = ref None

let lvalue_hash : (varinfo,A.lvalue) H.t = H.create 64

let expressions : (exp,A.tau) H.t = H.create 64

let lvalues : (lval,A.lvalue) H.t = H.create 64

let fresh_index : (unit -> int) =
  let count = ref 0 in
    fun () ->
      incr count;
      !count

let alloc_names = [
  "malloc";
  "calloc";
  "realloc";
  "xmalloc";
  "__builtin_alloca";
  "alloca";
  "kmalloc"
]

let all_globals : varinfo list ref = ref []
let all_functions : fundec list ref = ref []


(***********************************************************************)
(*                                                                     *)
(* Utility Functions                                                   *)
(*                                                                     *)
(***********************************************************************)

let is_undefined_fun = function
    Lval (lh, o) ->
      if isFunctionType (typeOfLval (lh, o))  then
        match lh with
            Var v -> v.vstorage = Extern
          | _ -> false
      else false
  | _ -> false

let is_alloc_fun = function
    Lval (lh, o) ->
      if isFunctionType (typeOfLval (lh, o)) then
        match lh with
            Var v -> List.mem v.vname alloc_names
          | _ -> false
      else false
  | _ -> false

let next_alloc = function
    Lval (Var v, o) ->
      let name = Printf.sprintf "%s@%d" v.vname (fresh_index ())
      in
        A.address (A.make_lvalue false name (Some v)) (* check *)
  | _ -> raise Bad_return

let is_effect_free_fun = function
    Lval (lh, o) when isFunctionType (typeOfLval (lh, o)) ->
      begin
        match lh with
            Var v ->
              begin
                try ("CHECK_" = String.sub v.vname 0 6)
                with Invalid_argument _ -> false
              end
          | _ -> false
      end
  | _ -> false


(***********************************************************************)
(*                                                                     *)
(* AST Traversal Functions                                             *)
(*                                                                     *)
(***********************************************************************)

(* should do nothing, might need to worry about Index case *)
(* let analyzeOffset (o : offset ) : A.tau = A.bottom () *)

let analyze_var_decl (v : varinfo ) : A.lvalue =
  try H.find lvalue_hash v
  with Not_found ->
    let lv = A.make_lvalue false v.vname (Some v)
    in
      H.add lvalue_hash v lv;
      lv

let isFunPtrType (t : typ) : bool =
  match t with
      TPtr (t, _) -> isFunctionType t
    | _ -> false

let rec analyze_lval (lv : lval ) : A.lvalue =
  let find_access (l : A.lvalue) (is_var : bool) : A.lvalue =
    match !current_fundec with
        None -> l
      | Some f ->
          let accesses = H.find fun_access_map f in
            if H.mem accesses lv then l
            else
              begin
                H.add accesses lv (l, is_var);
                l
              end in
  let result =
    match lv with
        Var v, _ -> (* instantiate every syntactic occurrence of a function *)
          let alv =
            if isFunctionType (typeOfLval lv) then
              A.instantiate (analyze_var_decl v) (fresh_index ())
            else analyze_var_decl v
          in
            find_access alv true
      | Mem e, _ ->
          (* assert (not (isFunctionType(typeOf(e))) ); *)
          let alv =
            if !fun_ptrs_as_funs && isFunPtrType (typeOf e) then
              analyze_expr_as_lval e
            else A.deref (analyze_expr e)
          in
            find_access alv false
  in
    H.replace lvalues lv result;
    result
and analyze_expr_as_lval (e : exp) : A.lvalue =
  match e with
      Lval l ->  analyze_lval l
    | _ -> assert false (* todo -- other kinds of expressions? *)
and analyze_expr (e : exp ) : A.tau =
  let result =
    match e with
        Const (CStr s) ->
          if !model_strings then
            A.address (A.make_lvalue
                         false
                         s
                         (Some (makeVarinfo false s charConstPtrType)))
          else A.bottom ()
      | Const c -> A.bottom ()
      | Lval l -> A.rvalue (analyze_lval l)
      | SizeOf _ -> A.bottom ()
      | SizeOfStr _ -> A.bottom ()
      | AlignOf _ -> A.bottom ()
      | UnOp (op, e, t) -> analyze_expr e
      | BinOp (op, e, e', t) -> A.join (analyze_expr e) (analyze_expr e')
      | CastE (t, e) -> analyze_expr e
      | AddrOf l ->
          if !fun_ptrs_as_funs && isFunctionType (typeOfLval l) then
            A.rvalue (analyze_lval l)
          else A.address (analyze_lval l)
      | StartOf l -> A.address (analyze_lval l)
      | AlignOfE _ -> A.bottom ()
      | SizeOfE _ -> A.bottom ()
 in
  H.add expressions e result;
  result


(* check *)
let rec analyze_init (i : init ) : A.tau =
  match i with
      SingleInit e -> analyze_expr e
    | CompoundInit (t, oi) ->
        A.join_inits (List.map (function (_, i) -> analyze_init i) oi)

let analyze_instr (i : instr ) : unit =
  match i with
      Set (lval, rhs, l) ->
        A.assign (analyze_lval lval) (analyze_expr rhs)
    | Call (res, fexpr, actuals, l) ->
        if not (isFunctionType (typeOf fexpr)) then
          () (* todo : is this a varargs? *)
        else if is_alloc_fun fexpr then
          begin
            if !debug then print_string "Found allocation function...\n";
            match res with
                Some r -> A.assign (analyze_lval r) (next_alloc fexpr)
              | None -> ()
          end
        else if is_effect_free_fun fexpr then
          List.iter (fun e -> ignore (analyze_expr e)) actuals
        else (* todo : check to see if the thing is an undefined function *)
          let fnres, site =
            if is_undefined_fun fexpr & !conservative_undefineds then
              A.apply_undefined (List.map analyze_expr actuals)
            else
              A.apply (analyze_expr fexpr) (List.map analyze_expr actuals)
          in
            begin
              match res with
                  Some r ->
                    begin
                      A.assign_ret site (analyze_lval r) fnres;
                      found_undefined := true;
                    end
                | None -> ()
            end
    | Asm _ -> ()

let rec analyze_stmt (s : stmt ) : unit =
  match s.skind with
      Instr il -> List.iter analyze_instr il
    | Return (eo, l) ->
        begin
          match eo with
              Some e ->
                begin
                  match !current_ret with
                      Some ret -> A.return ret (analyze_expr e)
                    | None -> raise Bad_return
                end
            | None -> ()
        end
    | Goto (s', l) -> () (* analyze_stmt(!s') *)
    | If (e, b, b', l) ->
        (* ignore the expression e; expressions can't be side-effecting *)
        analyze_block b;
        analyze_block b'
    | Switch (e, b, sl, l) ->
        analyze_block b;
        List.iter analyze_stmt sl
(*
    | Loop (b, l, _, _) -> analyze_block b
*)
    | While (_, b, _) -> analyze_block b
    | DoWhile (_, b, _) -> analyze_block b
    | For (bInit, _, bIter, b, _) ->
	analyze_block bInit;
	analyze_block bIter;
	analyze_block b
    | Block b -> analyze_block b
    | TryFinally (b, h, _) ->
        analyze_block b;
        analyze_block h
    | TryExcept (b, (il, _), h, _) ->
        analyze_block b;
        List.iter analyze_instr il;
        analyze_block h
    | Break l -> ()
    | Continue l -> ()


and analyze_block (b : block ) : unit =
  List.iter analyze_stmt b.bstmts

let analyze_function (f : fundec ) : unit =
  let oldlv = analyze_var_decl f.svar in
  let ret = A.make_fresh (f.svar.vname ^ "_ret") in
  let formals = List.map analyze_var_decl f.sformals in
  let newf = A.make_function f.svar.vname formals ret in
    if !show_progress then
      Printf.printf "Analyzing function %s\n" f.svar.vname;
    fun_varinfo_map := F.add f.svar f (!fun_varinfo_map);
    current_fundec := Some f;
    H.add fun_access_map f (H.create 8);
    A.assign oldlv newf;
    current_ret := Some ret;
    analyze_block f.sbody

let analyze_global (g : global ) : unit =
  match g with
      GVarDecl (v, l) -> () (* ignore (analyze_var_decl(v)) -- no need *)
    | GVar (v, init, l) ->
        all_globals := v :: !all_globals;
        begin
          match init.init with
              Some i -> A.assign (analyze_var_decl v) (analyze_init i)
            | None -> ignore (analyze_var_decl v)
        end
    | GFun (f, l) ->
        all_functions := f :: !all_functions;
        analyze_function f
    | _ -> ()

let analyze_file (f : file) : unit =
  iterGlobals f analyze_global


(***********************************************************************)
(*                                                                     *)
(* High-level Query Interface                                          *)
(*                                                                     *)
(***********************************************************************)

(* Same as analyze_expr, but no constraints. *)
let rec traverse_expr (e : exp) : A.tau =
  H.find expressions e

and traverse_expr_as_lval (e : exp) : A.lvalue =
  match e with
    | Lval l -> traverse_lval l
    | _ -> assert false (* todo -- other kinds of expressions? *)

and traverse_lval (lv : lval ) : A.lvalue =
  H.find lvalues lv

let may_alias (e1 : exp) (e2 : exp) : bool =
  let tau1,tau2 = traverse_expr e1, traverse_expr e2 in
  let result = A.may_alias tau1 tau2 in
    if !debug_may_aliases then
      begin
        let doc1 = d_exp () e1 in
        let doc2 = d_exp () e2 in
        let s1 = Pretty.sprint ~width:30 doc1 in
        let s2 = Pretty.sprint ~width:30 doc2 in
          Printf.printf
            "%s and %s may alias? %s\n"
            s1
            s2
            (if result then "yes" else "no")
      end;
    result

let resolve_lval (lv : lval) : varinfo list =
  A.points_to (traverse_lval lv)

let resolve_exp (e : exp) : varinfo list =
  A.epoints_to (traverse_expr e)

let resolve_funptr (e : exp) : fundec list =
  let varinfos = A.epoints_to (traverse_expr e) in
    List.fold_left
      (fun fdecs -> fun vinf ->
         try F.find vinf !fun_varinfo_map :: fdecs
         with Not_found -> fdecs)
      []
      varinfos

let count_hash_elts h =
  let result = ref 0 in
    H.iter (fun _ -> fun _ -> incr result) lvalue_hash;
    !result

let compute_may_aliases (b : bool) : unit =
  let rec compute_may_aliases_aux (exps : exp list) =
    match exps with
        [] -> ()
      | h :: t ->
          ignore (List.map (may_alias h) t);
          compute_may_aliases_aux t
  and exprs : exp list ref = ref [] in
    H.iter (fun e -> fun _ -> exprs := e :: !exprs) expressions;
    compute_may_aliases_aux !exprs


let compute_results (show_sets : bool) : unit =
  let total_pointed_to = ref 0
  and total_lvalues = H.length lvalue_hash
  and counted_lvalues = ref 0
  and lval_elts : (string * (string list)) list ref = ref [] in
  let print_result (name, set) =
    let rec print_set s =
      match s with
          [] -> ()
        | h :: [] -> print_string h
        | h :: t ->
            print_string (h ^ ", ");
            print_set t
    and ptsize = List.length set in
      total_pointed_to := !total_pointed_to + ptsize;
      if ptsize > 0 then
        begin
          print_string (name ^ "(" ^ (string_of_int ptsize) ^ ") -> ");
          print_set set;
          print_newline ()
        end
  in
  (* Make the most pessimistic assumptions about globals if an
     undefined function is present. Such a function can write to every
     global variable *)
  let hose_globals () : unit =
    List.iter
      (fun vd -> A.assign_undefined (analyze_var_decl vd))
      !all_globals
  in
  let show_progress_fn (counted : int ref) (total : int) : unit =
    incr counted;
    if !show_progress then
      Printf.printf "Computed flow for %d of %d sets\n" !counted total
  in
    if !conservative_undefineds && !found_undefined then hose_globals ();
    A.finished_constraints ();
    if show_sets then
      begin
        print_endline "Computing points-to sets...";
        Hashtbl.iter
          (fun vinf -> fun lv ->
             show_progress_fn counted_lvalues total_lvalues;
             try lval_elts := (vinf.vname, A.points_to_names lv) :: !lval_elts
             with A.UnknownLocation -> ())
          lvalue_hash;
        List.iter print_result !lval_elts;
        Printf.printf
          "Total number of things pointed to: %d\n"
          !total_pointed_to
      end;
    if !debug_may_aliases then
      begin
        Printf.printf "Printing may alias relationships\n";
        compute_may_aliases true
      end

let print_types () : unit =
  print_string "Printing inferred types of lvalues...\n";
  Hashtbl.iter
    (fun vi -> fun lv ->
       Printf.printf "%s : %s\n" vi.vname (A.string_of_lvalue lv))
    lvalue_hash



(** Alias queries. For each function, gather sets of locals, formals, and
    globals. Do n^2 work for each of these functions, reporting whether or not
    each pair of values is aliased. Aliasing is determined by taking points-to
    set intersections.
*)
let compute_aliases = compute_may_aliases


(***********************************************************************)
(*                                                                     *)
(* Abstract Location Interface                                         *)
(*                                                                     *)
(***********************************************************************)

type absloc = A.absloc

let rec lvalue_of_varinfo (vi : varinfo) : A.lvalue =
  H.find lvalue_hash vi

let lvalue_of_lval = traverse_lval
let tau_of_expr = traverse_expr

(** return an abstract location for a varinfo, resp. lval *)
let absloc_of_varinfo vi =
  A.absloc_of_lvalue (lvalue_of_varinfo vi)

let absloc_of_lval lv =
  A.absloc_of_lvalue (lvalue_of_lval lv)

let absloc_e_points_to e =
  A.absloc_epoints_to (tau_of_expr e)

let absloc_lval_aliases lv =
  A.absloc_points_to (lvalue_of_lval lv)

(* all abslocs that e transitively points to *)
let absloc_e_transitive_points_to (e : Cil.exp) : absloc list =
  let rec lv_trans_ptsto (worklist : varinfo list) (acc : varinfo list) : absloc list =
    match worklist with
        [] -> List.map absloc_of_varinfo acc
      | vi :: wklst'' ->
          if List.mem vi acc then lv_trans_ptsto wklst'' acc
          else
            lv_trans_ptsto
              (List.rev_append
                 (A.points_to (lvalue_of_varinfo vi))
                 wklst'')
              (vi :: acc)
  in
    lv_trans_ptsto (A.epoints_to (tau_of_expr e)) []

let absloc_eq a b = A.absloc_eq (a, b)

let d_absloc: unit -> absloc -> Pretty.doc = A.d_absloc


let ptrAnalysis = ref false
let ptrResults = ref false
let ptrTypes = ref false



(** Turn this into a CIL feature *)
let feature : featureDescr = {
  fd_name = "ptranal";
  fd_enabled = ptrAnalysis;
  fd_description = "alias analysis";
  fd_extraopt = [
    ("--ptr_may_aliases",
     Arg.Unit (fun _ -> debug_may_aliases := true),
     "Print out results of may alias queries");
    ("--ptr_unify", Arg.Unit (fun _ -> no_sub := true),
     "Make the alias analysis unification-based");
    ("--ptr_model_strings", Arg.Unit (fun _ -> model_strings := true),
     "Make the alias analysis model string constants");
    ("--ptr_conservative",
     Arg.Unit (fun _ -> conservative_undefineds := true),
     "Treat undefineds conservatively in alias analysis");
    ("--ptr_results", Arg.Unit (fun _ -> ptrResults := true),
     "print the results of the alias analysis");
    ("--ptr_mono", Arg.Unit (fun _ -> analyze_mono := true),
     "run alias analysis monomorphically");
    ("--ptr_types",Arg.Unit (fun _ -> ptrTypes := true),
     "print inferred points-to analysis types")
  ];
  fd_doit = (function (f: file) ->
               analyze_file f;
               compute_results !ptrResults;
               if !ptrTypes then print_types ());
  fd_post_check = false (* No changes *)
}
