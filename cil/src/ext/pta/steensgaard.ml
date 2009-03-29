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

(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(* This file is currently unused by CIL.  It is included in the        *)
(*   distribution for reference only.                                  *)
(*                                                                     *)
(*                                                                     *)
(***********************************************************************)


(***********************************************************************)
(*                                                                     *)
(* Type Declarations                                                   *)
(*                                                                     *)
(***********************************************************************)

exception Inconsistent of string
exception Bad_cache
exception No_contents
exception Bad_proj
exception Bad_type_copy
exception Instantiation_cycle

module U = Uref
module S = Setp
module H = Hashtbl
module Q = Queue

(** Polarity kinds-- positive, negative, or nonpolar. *)
type polarity = Pos 
		| Neg 
		| Non

(** Label bounds. The polymorphic type is a hack for recursive modules *)  
type 'a bound = {index : int; info : 'a} 

(** The 'a type may in general contain urefs, which makes Pervasives.compare
  incorrect. However, the bounds will always be correct because if two tau's
  get unified, their cached instantiations will be re-entered into the 
  worklist, ensuring that any labels find the new bounds *)
module Bound =
struct 
  type 'a t = 'a bound
  let compare (x : 'a t) (y : 'a t) = 
    Pervasives.compare x y
end

module B = S.Make(Bound)

type 'a boundset = 'a B.t

(** Constants, which identify elements in points-to sets *)
type constant = int * string

module Constant =
struct
  type t = constant

  let compare ((xid,_) : t) ((yid,_) : t) =
    Pervasives.compare xid yid
end

module C = Set.Make(Constant)

(** Sets of constants. Set union is used when two labels containing 
  constant sets are unified *)
type constantset = C.t

type lblinfo = {
  mutable l_name: string;
  (** Name of this label *)
  mutable aliases: constantset;
  (** Set of constants (tags) for checking aliases *)
  p_bounds: label boundset U.uref; 
  (** Set of umatched (p) lower bounds *)
  n_bounds: label boundset U.uref; 
  (** Set of unmatched (n) lower bounds *)
  mutable p_cached: bool;
  (** Flag indicating whether all reachable p edges have been locally cached *)
  mutable n_cached: bool;
  (** Flag indicating whether all reachable n edges have been locally cached *)
  mutable on_path: bool;
  (** For cycle detection during reachability queries *)
}

(** Constructor labels *)
and label = lblinfo U.uref 

(** The type of lvalues. *)
type lvalue = {
  l: label; 
  contents: tau
}

(** Data for variables. *)
and vinfo = {
  v_name: string; 
  mutable v_global: bool; 
  v_cache: cache
} 

(** Data for ref constructors.  *)
and rinfo = {
  rl: label; 
  mutable r_global: bool; 
  points_to: tau; 
  r_cache: cache
}

(** Data for fun constructors. *)
and finfo = {
  fl: label; 
  mutable f_global: bool; 
  args: tau list ref; 
  ret: tau; 
  f_cache: cache
}

(* Data for pairs. Note there is no label. *)
and pinfo = {
  mutable p_global: bool; 
  ptr: tau; 
  lam: tau; 
  p_cache: cache
}

(** Type constructors discovered by type inference *)
and tinfo = Wild
            | Var of vinfo
	    | Ref of rinfo
	    | Fun of finfo
	    | Pair of pinfo 
 
(** The top-level points-to type. *)
and tau = tinfo U.uref

(** The instantiation constraint cache. The index is used as a key. *)
and cache = (int,polarity * tau) H.t

(* Type of semi-unification constraints *)
type su_constraint = Instantiation of tau * (int * polarity) * tau
		     | Unification of tau * tau

(** Association lists, used for printing recursive types. The first element 
  is a type that has been visited. The second element is the string
  representation of that type (so far). If the string option is set, then 
  this type occurs within itself, and is associated with the recursive var
  name stored in the option. When walking a type, add it to an association 
  list. 

  Example : suppose we have the constraint 'a = ref('a). The type is unified
  via cyclic unification, and would loop infinitely if we attempted to print
  it. What we want to do is print the type u rv. ref(rv). This is accomplished
  in the following manner:
  
  -- ref('a) is visited. It is not in the association list, so it is added
  and the string "ref(" is stored in the second element. We recurse to print
  the first argument of the constructor.

  -- In the recursive call, we see that 'a (or ref('a)) is already in the
  association list, so the type is recursive. We check the string option,
  which is None, meaning that this is the first recurrence of the type. We
  create a new recursive variable, rv and set the string option to 'rv. Next,
  we prepend u rv. to the string representation we have seen before, "ref(",
  and return "rv" as the string representation of this type.

  -- The string so far is "u rv.ref(". The recursive call returns, and we
  complete the type by printing the result of the call, "rv", and ")"

  In a type where the recursive variable appears twice, e.g. 'a = pair('a,'a),
  the second time we hit 'a, the string option will be set, so we know to 
  reuse the same recursive variable name.
*)
type association = tau * string ref * string option ref
  
(***********************************************************************)
(*                                                                     *)
(* Global Variables                                                    *)
(*                                                                     *)
(***********************************************************************)

(** Print the instantiations constraints (loops with cyclic structures). *)
let print_constraints : bool ref = ref false

(** Solve constraints as they are introduced. If this is false, constraints
  are solved in batch fashion at calls to solveConstraints. *)
let solve_online : bool ref = ref true

(** If true, print all constraints (including induced) and show additional 
 debug output. *)
let debug = ref false			       
let debug_constraints = debug

(** If true, print out extra verbose debug information (including contents
  of label sets *)
let verbose_debug = ref false


(** If true, make the flow step a no-op *)
let no_flow = ref false

let no_sub = ref false

(** If true, do not add instantiation constraints *)
let analyze_mono = ref false

(** A counter for generating unique integers. *)
let counter : int ref = ref 0

(** A list of equality constraints. *)
let eq_worklist : su_constraint Q.t = Q.create()

(** A list of instantiation constraints. *)
let inst_worklist : su_constraint Q.t = Q.create()

(***********************************************************************)
(*                                                                     *)
(* Utility Functions                                                   *)
(*                                                                     *)
(***********************************************************************)

(** Consistency check for inferred types *)
let  pair_or_var (t : tau) = 
  match (U.deref t) with
    | Pair _ -> true
    | Var _ -> true
    | _ -> false

let ref_or_var (t : tau) =
   match (U.deref t) with
     | Ref _ -> true
     | Var _ -> true
     | _ -> false

let fun_or_var (t : tau) =
  match (U.deref t) with
    | Fun _ -> true
    | Var _ -> true
    |  _ -> false

(** Generate a unique integer. *)
let fresh_index () : int = 
  incr counter; 
  !counter

(** Negate a polarity. *)
let negate (p : polarity) : polarity =
  match p with
    | Pos -> Neg
    | Neg -> Pos
    | Non -> Non

(** Compute the least-upper-bounds of two polarities. *)
let lub (p,p' : polarity * polarity) : polarity = 
  match p with
    | Pos -> 
	begin
	  match p' with 
	    | Pos -> Pos
	    | _ -> Non
	end
    | Neg -> 
	begin
	  match p' with
	    | Neg -> Neg 
	    | _ -> Non
	end
    | Non -> Non

(** Extract the cache from a type *)
let get_cache (t : tau) : cache =
  match U.deref t with 
    | Wild -> raise Bad_cache
    | Var v -> v.v_cache
    | Ref r -> r.r_cache
    | Pair p -> p.p_cache
    | Fun f -> f.f_cache

(** Determine whether or not a type is global *)
let get_global (t : tau) : bool = 
  match U.deref t with
    |  Wild -> false
    | Var v -> v.v_global
    | Ref r -> r.r_global
    | Pair p -> p.p_global
    | Fun f -> f.f_global

(** Return true if a type is monomorphic (global). *)
let global_tau = get_global

let global_lvalue lv = get_global lv.contents

(** Return true if e is a member of l (according to uref equality) *)
let rec ulist_mem e l =
  match l with
    | [] -> false
    | h :: t -> if (U.equal(h,e)) then true else ulist_mem e t 

(** Convert a polarity to a string *)
let string_of_polarity p = 
    match p with 
      | Pos -> "+"
      | Neg -> "-"
      | Non -> "T"

(** Convert a label to a string, short representation *)
let string_of_label2 (l : label) : string = 
  "\"" ^ (U.deref l).l_name ^ "\""

(** Convert a label to a string, long representation *)
let string_of_label (l : label ) : string =
  let rec constset_to_string = function
    | (_,s) :: [] -> s
    | (_,s) :: t -> s ^ "," ^ (constset_to_string t)
    | [] -> ""
  in
  let aliases = constset_to_string (C.elements ((U.deref l).aliases))
  in
    if ( (aliases = "") || (not !verbose_debug))
    then string_of_label2 l 
    else aliases

(** Return true if the element [e] is present in the association list *)
let rec assoc_list_mem (e : tau) (l : association list) =
  match l with
    | [] -> None
    | (h,s,so) :: t -> 
	if (U.equal(h,e)) then (Some (s,so)) else assoc_list_mem e t
	
(** Given a tau, create a unique recursive variable name. This should always
  return the same name for a given tau *)
let fresh_recvar_name (t : tau) : string =	    
  match U.deref t with
    | Pair p -> "rvp" ^ string_of_int((Hashtbl.hash p)) 
    | Ref r -> "rvr" ^ string_of_int((Hashtbl.hash r)) 
    | Fun f -> "rvf" ^ string_of_int((Hashtbl.hash f))
    | _ -> raise (Inconsistent ("recvar_name"))

(** Return a string representation of a tau, using association lists. *)
let string_of_tau (t : tau ) : string = 
  let tau_map : association list ref = ref [] in
  let rec string_of_tau' t = 
    match (assoc_list_mem t (!tau_map)) with
      | Some (s,so) -> (* recursive type. see if a var name has been set *)
	  begin
	    match (!so) with
	      | None ->
		  begin
		    let rv = fresh_recvar_name(t) in
		      s := "u " ^ rv ^ "." ^ (!s);
		      so := Some (rv);
		      rv
		  end
	      | Some rv -> rv
	  end
      | None -> (* type's not recursive. Add it to the assoc list and cont. *)
	  let s = ref "" in
	  let so : string option ref = ref None in
	    begin
	      tau_map := (t,s,so) :: (!tau_map);

	      (match (U.deref t) with
		| Wild -> s := "_"; 
		| Var v -> s := v.v_name;
		| Pair p -> 
		    begin
		      assert (ref_or_var(p.ptr));
		      assert (fun_or_var(p.lam));
		      s := "{";
		      s := (!s) ^ (string_of_tau' p.ptr);
		      s := (!s) ^ ",";
		      s := (!s) ^ (string_of_tau' p.lam);
		      s := (!s) ^"}"
		
		    end
		| Ref r ->
		    begin
		      assert(pair_or_var(r.points_to));
		      s := "ref(|";
		      s := (!s) ^ (string_of_label r.rl);
		      s := (!s) ^ "|,";
		      s := (!s) ^ (string_of_tau' r.points_to);
		      s := (!s) ^ ")"
		    
		    end
		| Fun f ->
		    begin
		      assert(pair_or_var(f.ret));
		      let rec string_of_args = function
			| h :: [] ->
			    begin
			      assert(pair_or_var(h));
			      s := (!s) ^ (string_of_tau' h)
			    end
			| h :: t -> 
			    begin
			      assert(pair_or_var(h));
			      s := (!s) ^ (string_of_tau' h) ^ ",";
			      string_of_args t
			    end
			| [] -> ()
		      in
			s := "fun(|";
			s := (!s) ^ (string_of_label f.fl);
			s := (!s) ^ "|,";
			s := (!s) ^ "<";
			if (List.length !(f.args) > 0) 
			then
			  string_of_args !(f.args)
			else
			  s := (!s) ^ "void";
			s := (!s) ^">,";
			s := (!s) ^ (string_of_tau' f.ret);
			s := (!s) ^ ")"
		    end);
	      tau_map := List.tl (!tau_map);
	      !s
	    end
  in
    string_of_tau' t

(** Convert an lvalue to a string *)	
let rec string_of_lvalue (lv : lvalue) : string =
  let contents = (string_of_tau(lv.contents)) in
  let l = (string_of_label lv.l) in
    assert(pair_or_var(lv.contents));
    Printf.sprintf "[%s]^(%s)" contents l
	      
(** Print a list of tau elements, comma separated *)
let rec print_tau_list (l : tau list) : unit = 
  let t_strings = List.map string_of_tau l in
  let rec print_t_strings = function
    | h :: [] -> print_string h; print_newline();
    | h :: t -> print_string h; print_string ", "; print_t_strings t
    | [] -> ()
  in
    print_t_strings t_strings

(** Print a constraint. *)
let print_constraint (c : su_constraint) = 
  match c with 
    | Unification (t,t') -> 
	let lhs = string_of_tau t in
	let rhs = string_of_tau t' in 
	  Printf.printf "%s == %s\n" lhs rhs
    | Instantiation (t,(i,p),t') ->
	let lhs = string_of_tau t in
	let rhs = string_of_tau t' in
	let index = string_of_int i in
	let pol = string_of_polarity p in
	  Printf.printf "%s <={%s,%s} %s\n" lhs index pol rhs

(* If [positive] is true, return the p-edge bounds, otherwise, return
   the n-edge bounds. *)    
let get_bounds (positive : bool) (l : label) : label boundset U.uref =
  if (positive) then
    (U.deref l).p_bounds
  else
    (U.deref l).n_bounds

(** Used for cycle detection during the flow step. Returns true if the
 label [l] is found on the current path. *)
let on_path (l : label) : bool =
  (U.deref l).on_path

(** Used for cycle detection during the flow step. Identifies [l] as being
  on/off the current path. *) 
let set_on_path (l : label) (b : bool) : unit =
  (U.deref l).on_path <- b

(** Make the type a global type *)
let set_global (t : tau) (b : bool) : bool =
  if (!debug && b) 
  then 
    Printf.printf "Setting a new global : %s\n" (string_of_tau t);
  begin
    assert ( (not (get_global(t)) ) || b );
    (match U.deref t with
       | Wild -> ()
       | Var v -> v.v_global <- b
       | Ref r -> r.r_global <- b
       | Pair p -> p.p_global <- b
       | Fun f -> f.f_global <- b);
    b
  end

(** Return a label's bounds as a string *)
let string_of_bounds (is_pos : bool) (l : label) : string =
  let bounds = 
    if (is_pos) then
      U.deref ((U.deref l).p_bounds)
    else
      U.deref ((U.deref l).n_bounds)
  in
    B.fold (fun b -> fun res -> res ^ (string_of_label2 b.info) ^ " "
	   ) bounds ""
    
(***********************************************************************)
(*                                                                     *)
(* Type Operations -- these do not create any constraints              *)
(*                                                                     *)
(***********************************************************************)

let wild_val = U.uref Wild

(** The wild (don't care) value. *)
let wild () : tau =
  wild_val

(** Create an lvalue with label [lbl] and tau contents [t]. *)
let make_lval (lbl,t : label * tau) : lvalue = 
  {l = lbl; contents = t}

(** Create a new label with name [name]. Also adds a fresh constant
 with name [name] to this label's aliases set. *)  
let make_label (name : string) : label =
  U.uref {
    l_name = name;
    aliases = (C.add (fresh_index(),name) C.empty); 
    p_bounds = U.uref (B.empty); 
    n_bounds = U.uref (B.empty);
    p_cached = false;
    n_cached = false;
    on_path = false
 }

(** Create a new label with an unspecified name and an empty alias set. *) 
let fresh_label () : label =
  U.uref {
    l_name = "l_" ^ (string_of_int (fresh_index()));
    aliases = (C.empty); 
    p_bounds = U.uref (B.empty); 
    n_bounds = U.uref (B.empty);
    p_cached = false;
    n_cached = false;
    on_path = false
 }

(** Create a fresh bound. *)
let make_bound (i,a : int * 'a) : 'a bound = 
  {index = i; info = a }

(** Create a fresh named variable with name '[name]. *)
let make_var (b: bool) (name : string) : tau =
   U.uref (Var {v_name = ("'" ^name); 
		v_global = b; 
		v_cache = H.create 4})

(** Create a fresh unnamed variable (name will be 'fv). *)
let fresh_var () : tau =
  make_var false ("fv" ^ (string_of_int (fresh_index())) )

(** Create a fresh unnamed variable (name will be 'fi). *)
let fresh_var_i () : tau = 
 make_var false ("fi" ^ (string_of_int (fresh_index())) )

(** Create a Fun constructor. *)
let make_fun (lbl,a,r : label * (tau list) * tau) : tau =
  U.uref (Fun {fl = lbl ; 
	       f_global = false; 
	       args = ref a; 
	       ret = r;
	       f_cache = H.create 4})

(** Create a Ref constructor. *)
let make_ref (lbl,pt : label * tau) : tau =
  U.uref (Ref {rl = lbl ; 
	       r_global = false; 
	       points_to = pt; 
	       r_cache = H.create 4})

(** Create a Pair constructor. *)
let make_pair (p,f : tau * tau) : tau =
  U.uref (Pair {ptr = p; 
		p_global = false;
		lam = f; 
		p_cache = H.create 4})

(** Copy the toplevel constructor of [t], putting fresh variables in each
  argement of the constructor. *)
let copy_toplevel (t : tau) : tau = 
  match U.deref t with
    | Pair _ -> 
	make_pair (fresh_var_i(), fresh_var_i())
    | Ref  _ -> 
	make_ref (fresh_label(),fresh_var_i())
    | Fun  f -> 
	let fresh_fn = fun _ -> fresh_var_i()
	in
	  make_fun (fresh_label(), List.map fresh_fn !(f.args) , fresh_var_i())
    | _ -> raise Bad_type_copy

let pad_args (l,l' : (tau list ref) * (tau list ref)) : unit =
  let padding = ref ((List.length (!l)) - (List.length (!l')))
  in
    if (!padding == 0) then ()
    else 
      let to_pad = 
	if (!padding > 0) then l' else (padding := -(!padding);l)
      in
	for i = 1 to (!padding)  do
	  to_pad := (!to_pad) @ [fresh_var()]
	done

(***********************************************************************)
(*                                                                     *)
(* Constraint Generation/ Resolution                                   *)
(*                                                                     *)
(***********************************************************************)

(** Returns true if the constraint has no effect, i.e. either the left-hand
  side or the right-hand side is wild. *)
let wild_constraint (t,t' : tau * tau) : bool = 
  let ti,ti' = U.deref t, U.deref t' in
    match ti,ti' with
      | Wild, _ -> true
      | _, Wild -> true
      | _ -> false

exception Cycle_found

(** Cycle detection between instantiations. Returns true if there is a cycle
  from t to t' *)
let exists_cycle (t,t' : tau * tau) : bool =
  let visited : tau list ref = ref [] in
  let rec exists_cycle' t =
    if (ulist_mem t (!visited))
    then
      begin (*
	print_string "Instantiation cycle found :";
	print_tau_list (!visited);
	print_newline();
	print_string (string_of_tau t);
	print_newline(); *)
	(* raise Instantiation_cycle *) 
	(* visited := List.tl (!visited) *) (* check *)
      end
    else
      begin
	visited := t :: (!visited);
	if (U.equal(t,t')) 
	then raise Cycle_found
	else
	  H.iter (fun _ -> fun (_,t'') -> 
		    if (U.equal (t,t'')) then () 
		    else
		      ignore (exists_cycle' t'')
		 ) (get_cache t) ;
	visited := List.tl (!visited)
      end
  in
    try
      exists_cycle' t;
      false
    with
      | Cycle_found -> true
	
exception Subterm
  
(** Returns true if [t'] is a proper subterm of [t] *)
let proper_subterm (t,t') = 
  let visited : tau list ref = ref [] in
  let rec proper_subterm' t = 
    if (ulist_mem t (!visited)) 
    then () (* recursive type *)
    else
      if (U.equal (t,t'))
      then raise Subterm
      else
	begin
	  visited := t :: (!visited);
	  (
	    match (U.deref t) with
	      | Wild -> ()
	      | Var _ -> ()
	      | Ref r ->
		  proper_subterm' r.points_to
	      | Pair p ->
		  proper_subterm' p.ptr;
		  proper_subterm' p.lam
	      | Fun f ->
		  proper_subterm' f.ret;
		  List.iter (proper_subterm') !(f.args)
	  );
	  visited := List.tl (!visited)
	  end
  in
    try
      if (U.equal(t,t')) then false 
      else
	begin
	  proper_subterm' t;
	  false
	end
    with
      | Subterm -> true

(** The extended occurs check. Search for a cycle of instantiations from [t]
  to [t']. If such a cycle exists, check to see that [t'] is a proper subterm
  of [t]. If it is, then return true *)
let eoc (t,t') : bool =
  if (exists_cycle(t,t') && proper_subterm(t,t'))
  then
    begin
      if (!debug)
      then
	Printf.printf "Occurs check : %s occurs within %s\n" (string_of_tau t')
	  (string_of_tau t)
      else 
	();
      true 
    end
  else
   false
  
(** Resolve an instantiation constraint *)
let rec instantiate_int (t,(i,p),t' : tau * (int * polarity) * tau) =
  if  ( wild_constraint(t,t') || (not (store(t,(i,p),t'))) || 
	U.equal(t,t') )
  then ()
  else 
    let ti,ti' = U.deref t, U.deref t' in
      match ti,ti' with 
	| Ref r, Ref r' -> 
	    instantiate_ref(r,(i,p),r')
	| Fun f, Fun f' -> 
	    instantiate_fun(f,(i,p),f')
	| Pair pr, Pair pr' ->
	    begin
	      add_constraint_int (Instantiation (pr.ptr,(i,p),pr'.ptr));
	      add_constraint_int (Instantiation (pr.lam,(i,p),pr'.lam))
	    end
	| Var v, _ -> ()
	| _,Var v' -> 
	    if eoc(t,t')
	    then 
	      add_constraint_int (Unification (t,t'))
	    else
	      begin
		unstore(t,i);
		add_constraint_int (Unification ((copy_toplevel t),t'));
		add_constraint_int (Instantiation (t,(i,p),t')) 
	      end
	| _ -> raise (Inconsistent("instantiate"))

(** Apply instantiations to the ref's label, and structurally down the type.
  Contents of ref constructors are instantiated with polarity Non. *)
and instantiate_ref (ri,(i,p),ri') : unit =
  add_constraint_int (Instantiation(ri.points_to,(i,Non),ri'.points_to));
  instantiate_label (ri.rl,(i,p),ri'.rl)

(** Apply instantiations to the fun's label, and structurally down the type. 
   Flip the polarity for the function's args. If the lengths of the argument
   lists don't match, extend the shorter list as necessary.  *)
and instantiate_fun (fi,(i,p),fi') : unit =
    pad_args (fi.args, fi'.args);
    assert(List.length !(fi.args) == List.length !(fi'.args));
    add_constraint_int (Instantiation (fi.ret,(i,p),fi'.ret));
    List.iter2 (fun t ->fun t' -> 
		  add_constraint_int (Instantiation(t,(i,negate p),t'))) 
      !(fi.args) !(fi'.args);
    instantiate_label (fi.fl,(i,p),fi'.fl)

(** Instantiate a label. Update the label's bounds with new flow edges. 
 *)
and instantiate_label (l,(i,p),l' : label * (int * polarity) * label) : unit =
  if (!debug) then
    Printf.printf "%s <= {%d,%s} %s\n" (string_of_label l) i 
      (string_of_polarity p) (string_of_label l');
  let li,li' = U.deref l, U.deref l' in
    match p with
      | Pos ->
	  U.update (li'.p_bounds, 
		    B.add(make_bound (i,l)) (U.deref li'.p_bounds)
		   )
      | Neg -> 
	  U.update (li.n_bounds, 
		    B.add(make_bound (i,l')) (U.deref li.n_bounds)
		   )
      | Non ->
	  begin
	    U.update (li'.p_bounds, 
		      B.add(make_bound (i,l)) (U.deref li'.p_bounds)
		     );
	    U.update (li.n_bounds, 
		      B.add(make_bound (i,l')) (U.deref li.n_bounds)
		     )
	  end
	     
(** Resolve a unification constraint. Does the uref unification after grabbing
  a copy of the information before the two infos are unified. The other 
  interesting feature of this function is the way 'globalness' is propagated.
  If a non-global is unified with a global, the non-global becomes global. 
  If the ecr became global, there is a problem because none of its cached 
  instantiations know that the type became monomorphic. In this case, they
  must be re-inserted via merge-cache. Merge-cache always reinserts cached
  instantiations from the non-ecr type, i.e. the type that was 'killed' by the
  unification. *)
and unify_int (t,t' : tau * tau) : unit = 
  if (wild_constraint(t,t') || U.equal(t,t')) 
  then ()
  else 
    let ti, ti' = U.deref t, U.deref t' in
      begin
	U.unify combine (t,t');
	match ti,ti' with
	  | Var v, _ -> 
	      begin 
		if (set_global t' (v.v_global || (get_global t')))
		then (H.iter (merge_cache t') (get_cache t'))
		else ();
		H.iter (merge_cache t') v.v_cache
	      end
	  | _, Var v ->
	      begin 
		if (set_global t (v.v_global || (get_global t)))
		then (H.iter (merge_cache t) (get_cache t))
		else ();
		H.iter (merge_cache t) v.v_cache
	      end
	  | Ref r, Ref r' -> 
	      begin
		if (set_global t (r.r_global || r'.r_global))
		then (H.iter (merge_cache t) (get_cache t))
		else ();
		H.iter (merge_cache t) r'.r_cache;
		unify_ref(r,r')
	      end
	  | Fun f, Fun f' -> 
	      begin
		if (set_global t (f.f_global || f'.f_global))
		then (H.iter (merge_cache t) (get_cache t))
		else (); 
		H.iter (merge_cache t) f'.f_cache;
		unify_fun (f,f');
	      end
	  | Pair p, Pair p' ->
	      begin
		if (set_global t (p.p_global || p'.p_global))
		then (H.iter (merge_cache t) (get_cache t))
		else (); 
		H.iter (merge_cache t) p'.p_cache;
		add_constraint_int (Unification (p.ptr,p'.ptr));
		add_constraint_int (Unification (p.lam,p'.lam))
	      end
	  | _ -> raise (Inconsistent("unify"))
      end

(** Unify the ref's label, and apply unification structurally down the type. *)
and unify_ref (ri,ri' : rinfo * rinfo) : unit =
  add_constraint_int (Unification (ri.points_to,ri'.points_to));
  unify_label(ri.rl,ri'.rl) 

(** Unify the fun's label, and apply unification structurally down the type, 
  at arguments and return value. When combining two lists of different lengths,
  always choose the longer list for the representative. *)
and unify_fun (li,li' : finfo * finfo) : unit = 
  let rec union_args  = function
    | _, [] -> false
    | [], _ -> true
    | h :: t, h' :: t' -> 
	add_constraint_int (Unification (h,h')); union_args(t,t') 
  in
    begin
      unify_label(li.fl,li'.fl);
      add_constraint_int (Unification (li.ret,li'.ret));
      if (union_args(!(li.args),!(li'.args))) 
      then li.args := !(li'.args);
    end

(** Unify two labels, combining the set of constants denoting aliases. *)
and unify_label (l,l' : label * label) : unit =
  let pick_name (li,li' : lblinfo * lblinfo) = 
    if ( (String.length li.l_name) > 1 && (String.sub (li.l_name) 0 2) = "l_") 
    then 
      li.l_name <- li'.l_name
    else ()
  in
  let combine_label (li,li' : lblinfo *lblinfo) : lblinfo =
    let p_bounds = U.deref (li.p_bounds) in
    let p_bounds' = U.deref (li'.p_bounds) in
    let n_bounds = U.deref (li.n_bounds) in
    let n_bounds' = U.deref (li'.n_bounds) in 
      begin
	pick_name(li,li');
	li.aliases <- C.union (li.aliases) (li'.aliases);
	U.update (li.p_bounds, (B.union p_bounds p_bounds'));
	U.update (li.n_bounds, (B.union n_bounds n_bounds'));
	li
    end
  in(*
    if (!debug) then
      begin
	Printf.printf "Unifying %s with %s...\n" 
	  (string_of_label l) (string_of_label l');
	Printf.printf "pbounds : %s\n" (string_of_bounds true l);
	Printf.printf "nbounds : %s\n" (string_of_bounds false l);
	Printf.printf "pbounds : %s\n" (string_of_bounds true l');
	Printf.printf "nbounds : %s\n\n" (string_of_bounds false l')
      end; *)
    U.unify combine_label (l,l')
    (* if (!debug) then
      begin
	Printf.printf "pbounds : %s\n" (string_of_bounds true l);
	Printf.printf "nbounds : %s\n" (string_of_bounds false l)
      end *)

(** Re-assert a cached instantiation constraint, since the old type was 
  killed by a unification *)
and merge_cache (rep : tau) (i : int) (p,t' : polarity * tau) : unit =
  add_constraint_int (Instantiation (rep,(i,p),t'))
      
(** Pick the representative info for two tinfo's. This function prefers the
  first argument when both arguments are the same structure, but when
  one type is a structure and the other is a var, it picks the structure. *)
and combine (ti,ti' : tinfo * tinfo) : tinfo = 
  match ti,ti' with
    | Var _, _ -> ti'
    | _,_ -> ti 

(** Add a new constraint induced by other constraints. *)
and add_constraint_int (c : su_constraint) =
  if (!print_constraints && !debug) then print_constraint c else (); 
  begin
    match c with
      | Instantiation _ ->
	  Q.add c inst_worklist
      | Unification _ ->
	  Q.add c eq_worklist
  end;
  if (!debug) then solve_constraints() else ()
  
(** Add a new constraint introduced through this module's interface (a 
  top-level constraint). *)
and add_constraint (c : su_constraint) =
  begin
    add_constraint_int (c);
    if (!print_constraints && not (!debug)) then print_constraint c else (); 
    if (!solve_online) then solve_constraints() else ()
  end


(* Fetch constraints, preferring equalities. *)
and fetch_constraint () : su_constraint option =
  if (Q.length eq_worklist > 0)
  then 
    Some (Q.take eq_worklist)
  else if (Q.length inst_worklist > 0)
  then
    Some (Q.take inst_worklist)
  else
    None 

(** Returns the target of a cached instantiation, if it exists. *)
and target (t,i,p : tau * int * polarity) : (polarity * tau) option =
  let cache = get_cache t in
    if (global_tau t) then Some (Non,t) 
    else
      try
	Some (H.find cache i)
      with 
	| Not_found -> None
	  
(** Caches a new instantiation, or applies well-formedness. *)
and store ( t,(i,p),t' : tau * (int * polarity) * tau) : bool =
  let cache = get_cache t in
    match target(t,i,p) with
      | Some (p'',t'') ->
	  if (U.equal (t',t'') && (lub(p,p'') = p''))
	  then
	      false
	  else
	    begin
	      add_constraint_int (Unification (t',t''));
	      H.replace cache i (lub(p,p''),t'');
	      (* add a new forced instantiation as well *)
	      if (lub(p,p'') = p'') 
	      then ()
	      else
		begin
		  unstore(t,i);
		  add_constraint_int (Instantiation (t,(i,lub(p,p'')),t''))
		end;
	      false 
	    end
      | None ->
	  begin
	    H.add cache i (p,t');
	    true
	  end

(** Remove a cached instantiation. Used when type structure changes *)
and unstore (t,i : tau * int) =
let cache = get_cache t in
  H.remove cache i

(** The main solver loop. *)
and solve_constraints () : unit = 
  match fetch_constraint () with
    | Some c ->
	begin
	  (match c with
	     | Instantiation (t,(i,p),t') -> instantiate_int (t,(i,p),t')
	     | Unification (t,t') -> unify_int (t,t')
	  );
	  solve_constraints()
	end
    | None -> ()


(***********************************************************************)
(*                                                                     *)
(* Interface Functions                                                 *)
(*                                                                     *)
(***********************************************************************)
    
(** Return the contents of the lvalue. *)
let rvalue (lv : lvalue) : tau = 
  lv.contents

(** Dereference the rvalue. If it does not have enough structure to support
  the operation, then the correct structure is added via new unification
  constraints. *)
let rec deref (t : tau) : lvalue =
  match U.deref t with 
    | Pair p ->
	(
	  match U.deref (p.ptr) with
	    | Var _ ->
		begin 
		 (* let points_to = make_pair(fresh_var(),fresh_var()) in *)
		  let points_to = fresh_var() in 
		  let l = fresh_label() in
		  let r = make_ref(l,points_to)
		  in
		    add_constraint (Unification (p.ptr,r));
		    make_lval(l, points_to)
		end
	    | Ref r -> make_lval(r.rl, r.points_to)
	    | _ -> raise (Inconsistent("deref"))
	)
    | Var v -> 
	begin
	  add_constraint (Unification (t,make_pair(fresh_var(),fresh_var())));
	  deref t
	end
    | _ -> raise (Inconsistent("deref -- no top level pair"))

(** Form the union of [t] and [t']. *)
let join (t : tau) (t' : tau) : tau = 
  let t''  = fresh_var() in
    add_constraint (Unification (t,t''));
    add_constraint (Unification (t',t''));
    t''

(** Form the union of a list [tl], expected to be the initializers of some
  structure or array type. *)
let join_inits (tl : tau list) : tau = 
  let t' = fresh_var() in
    begin
      List.iter (function t'' -> add_constraint (Unification(t',t''))) tl;
      t'
    end

(** Take the address of an lvalue. Does not add constraints. *)
let address (lv  : lvalue) : tau = 
  make_pair (make_ref (lv.l, lv.contents), fresh_var() )
    
(** Instantiate a type with index i. By default, uses positive polarity. 
 Adds an instantiation constraint. *)
let instantiate (lv : lvalue) (i : int) : lvalue = 
  if (!analyze_mono) then lv
  else
    begin
      let l' = fresh_label () in
      let t' = fresh_var_i () in
	instantiate_label(lv.l,(i,Pos),l');
	add_constraint (Instantiation (lv.contents,(i,Pos),t'));
	make_lval(l',t') (* check -- fresh label ?? *)
    end 
    
(** Constraint generated from assigning [t] to [lv]. *)
let assign (lv : lvalue) (t : tau) : unit = 
  add_constraint (Unification (lv.contents,t))
    

(** Project out the first (ref) component or a pair. If the argument [t] has
  no discovered structure, raise No_contents. *)
let proj_ref (t : tau) : tau = 
  match U.deref t with
    | Pair p -> p.ptr
    | Var v -> raise No_contents
    | _ -> raise Bad_proj

(* Project out the second (fun) component of a pair. If the argument [t] has
 no discovered structure, create it on the fly by adding constraints. *)
let proj_fun (t : tau) : tau = 
  match U.deref t with
    | Pair p -> p.lam
    | Var v -> 
	let p,f = fresh_var(), fresh_var() in
	  add_constraint (Unification (t,make_pair(p,f)));
	  f
    | _ -> raise Bad_proj

let get_args (t : tau) : tau list ref =
  match U.deref t with 
    | Fun f -> f.args
    | _ -> raise (Inconsistent("get_args"))

(** Function type [t] is applied to the arguments [actuals]. Unifies the 
  actuals with the formals of [t]. If no functions have been discovered for 
  [t] yet, create a fresh one and unify it with t. The result is the return
  value of the function. *)
let apply (t : tau) (al : tau list) : tau = 
  let f = proj_fun(t) in
  let actuals = ref al in 
  let formals,ret =
    match U.deref f with
      | Fun fi -> (fi.args),fi.ret
      | Var v ->
	  let new_l,new_ret,new_args = 
	    fresh_label(), fresh_var (), 
	    List.map (function _ -> fresh_var()) (!actuals) 
	  in
	  let new_fun = make_fun(new_l,new_args,new_ret) in
	    add_constraint (Unification(new_fun,f));
	    (get_args new_fun,new_ret)
      | Ref _ -> raise (Inconsistent ("apply_ref"))
      | Pair _ -> raise (Inconsistent ("apply_pair"))
      | Wild -> raise (Inconsistent("apply_wild"))
  in
    pad_args(formals,actuals);
    List.iter2 (fun actual -> fun formal -> 
		  add_constraint (Unification (actual,formal))
	       ) !actuals !formals;
    ret 
    
(** Create a new function type with name [name], list of formal arguments 
  [formals], and return value [ret]. Adds no constraints. *)
let make_function (name : string) (formals : lvalue list) (ret : tau) : tau = 
  let 
    f = make_fun(make_label(name),List.map (fun x -> rvalue x) formals, ret) 
  in
    make_pair(fresh_var(),f)

(** Create an lvalue. If [is_global] is true, the lvalue will be treated 
    monomorphically. *)
let make_lvalue (is_global : bool) (name : string) : lvalue = 
  if (!debug && is_global) 
  then 
    Printf.printf "Making global lvalue : %s\n" name
  else ();
  make_lval(make_label(name), make_var is_global name)
 

(** Create a fresh non-global named variable. *)
let make_fresh (name : string) : tau =
  make_var false (name)

(** The default type for constants. *)
let bottom () : tau = 
  make_var false ("bottom")

(** Unify the result of a function with its return value. *)
let return (t : tau) (t' : tau) =
  add_constraint (Unification (t,t'))


(***********************************************************************)
(*                                                                     *)
(* Query/Extract Solutions                                             *)
(*                                                                     *)
(***********************************************************************)

(** Unify the data stored in two label bounds. *)
let combine_lbounds (s,s' : label boundset * label boundset) =
  B.union s s'

(** Truncates a list of urefs [l] to those elements up to and including the 
  first occurence of the specified element [elt].  *)
let truncate l elt = 
  let keep = ref true in
    List.filter 
      (fun x -> 
	 if (not (!keep)) 
	 then 
	     false
	 else
	   begin
	     if  (U.equal(x,elt)) 
	     then 
	       keep := false
	     else ();
	     true
	   end
      ) l

let debug_cycle_bounds is_pos c =
  let rec debug_cycle_bounds' = function
    | h :: [] -> 
	Printf.printf "%s --> %s\n" (string_of_bounds is_pos h) 
	(string_of_label2 h)
    | h :: t ->
	begin
	  Printf.printf "%s --> %s\n" (string_of_bounds is_pos h)
	    (string_of_label2 h);
	  debug_cycle_bounds' t
	end
    | [] -> ()
  in
    debug_cycle_bounds' c

(** For debugging, print a cycle of instantiations *)
let debug_cycle (is_pos,c,l,p) =
  let kind = if is_pos then "P" else "N" in
  let rec string_of_cycle = function 
    | h :: [] -> string_of_label2 h
    | [] -> ""
    | h :: t -> Printf.sprintf "%s,%s" (string_of_label2 h) (string_of_cycle t)
  in
    Printf.printf "Collapsing %s cycle around %s:\n" kind (string_of_label2 l);
    Printf.printf "Elements are: %s\n" (string_of_cycle c);
    Printf.printf "Per-element bounds:\n";
    debug_cycle_bounds is_pos c;
    Printf.printf "Full path is: %s" (string_of_cycle p);
    print_newline()

(** Compute pos or neg flow, depending on [is_pos]. Searches for cycles in the
  instantiations (can these even occur?) and unifies either the positive or
  negative edge sets for the labels on the cycle. Note that this does not 
  ever unify the labels themselves. The return is the new bounds of the 
  argument label *)
let rec flow (is_pos : bool) (path : label list) (l : label) : label boundset =
  let collapse_cycle () = 
    let cycle = truncate path l in
      debug_cycle (is_pos,cycle,l,path);
      List.iter (fun x -> U.unify combine_lbounds 
		   ((get_bounds is_pos x),get_bounds is_pos l)
		) cycle
  in
    if (on_path l) 
    then
      begin
	collapse_cycle (); 
	(* set_on_path l false; *)
	B.empty
      end
    else
      if ( (is_pos && (U.deref l).p_cached) || 
	   ( (not is_pos) && (U.deref l).n_cached) ) then
	begin
	  U.deref (get_bounds is_pos l)
	end
      else
	begin
	  let newbounds = ref B.empty in
	  let base = get_bounds is_pos l in
	    set_on_path l true;
	    if (is_pos) then 
	      (U.deref l).p_cached <- true 
	    else 
	      (U.deref l).n_cached <- true;
	    B.iter 
	      (fun x -> 
		 if (U.equal(x.info,l)) then () 
		 else
		   (newbounds := 
		    (B.union (!newbounds) (flow is_pos (l :: path) x.info)))
	      ) (U.deref base); 
	    set_on_path l false;
	    U.update (base,(B.union (U.deref base) !newbounds));
	    U.deref base
	end
	
(** Compute and cache any positive flow. *)
let pos_flow l : constantset  = 
  let result = ref C.empty in 
    begin
      ignore (flow true [] l);
      B.iter (fun x -> result := C.union (!result) (U.deref(x.info)).aliases )
	(U.deref (get_bounds true l)); 
      !result
    end
    
(** Compute and cache any negative flow. *)
let neg_flow l : constantset =
  let result = ref C.empty in
    begin
      ignore (flow false [] l); 
      B.iter (fun x -> result := C.union (!result) (U.deref(x.info)).aliases )
	(U.deref (get_bounds false l));
      !result
    end
    
(** Compute and cache any pos-neg flow. Assumes that both pos_flow and
  neg_flow have been computed for the label [l]. *)
let pos_neg_flow(l : label) : constantset  =
  let result = ref C.empty in
    begin
      B.iter (fun x -> result := C.union (!result) (pos_flow x.info))
	(U.deref (get_bounds false l));
      !result
    end

(** Compute a points-to set by computing positive, then negative, then
  positive-negative flow for a label. *)
let points_to_int (lv : lvalue) : constantset =
  let visited_caches : cache list ref  = ref [] in
  let rec points_to_tau (t : tau) : constantset =
    try 
      begin
	match U.deref (proj_ref t) with
	  | Var v -> C.empty
	  | Ref r ->
	      begin
		let pos = pos_flow r.rl in
		let neg = neg_flow r.rl in
		let interproc = C.union (pos_neg_flow r.rl) (C.union pos neg)
		in
		  C.union ((U.deref(r.rl)).aliases) interproc
	      end
	  | _ -> raise (Inconsistent ("points_to"))
      end
    with
      | No_contents ->
	  begin
	    match (U.deref t) with
	      | Var v -> rebuild_flow v.v_cache
	      | _ -> raise (Inconsistent ("points_to"))
	  end
  and rebuild_flow (c : cache) : constantset = 
    if (List.mem c (!visited_caches) ) (* cyclic instantiations *)
    then
      begin
	(* visited_caches := List.tl (!visited_caches); *) (* check *)
	C.empty
      end
    else
      begin
	visited_caches :=  c :: (!visited_caches);
	let result = ref (C.empty) in
	  H.iter (fun _ -> fun(p,t) -> 
		    match p with 
		      | Pos -> () 
		      | _ -> result := C.union (!result) (points_to_tau t)
		 ) c;
	  visited_caches := List.tl (!visited_caches);
	  !result
      end
  in
    if (!no_flow) then 
      (U.deref lv.l).aliases
    else 
      points_to_tau (lv.contents)

let points_to (lv : lvalue) : string list =
  List.map snd (C.elements (points_to_int lv))

let alias_query (a_progress : bool) (lv : lvalue list) : int * int = 
  (0,0) (* todo *)
(*
  let a_count = ref 0 in
  let ptsets = List.map points_to_int lv in
  let total_sets = List.length ptsets in
  let counted_sets = ref 0 in 
  let record_alias s s' = 
    if (C.is_empty (C.inter s s')) 
    then ()
    else (incr a_count)
  in
  let rec check_alias = function
    | h :: t ->
	begin
	  List.iter (record_alias h) ptsets; 
	  check_alias t 
	end
    | [] -> ()
  in
    check_alias ptsets;
    !a_count
*)
