(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
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

(* 
 * Heapify: a program transform that looks over functions, finds those
 * that have local (stack) variables that contain arrays, puts all such
 * local variables into a single heap allocated structure, changes all
 * accesses to such variables into accesses to fields of that structure
 * and frees the structure on return. 
 *)
open Cil

(* utilities that should be in Cil.ml *)
(* sfg: this function appears to never be called *)
let mkSimpleField ci fn ft fl =
  { fcomp = ci ; fname = fn ; ftype = ft ; fbitfield = None ; fattr = [];
    floc = fl }


(* actual Heapify begins *)

let heapifyNonArrays = ref false

(* Does this local var contain an array? *)
let rec containsArray (t:typ) : bool =  (* does this type contain an array? *)
  match unrollType t with
    TArray _ -> true
  | TComp(ci, _) -> (* look at the types of the fields *)
      List.exists (fun fi -> containsArray fi.ftype) ci.cfields
  | _ -> 
    (* Ignore other types, including TInt and TPtr.  We don't care whether
       there are arrays in the base types of pointers; only about whether
       this local variable itself needs to be moved to the heap. *)
   false


class heapifyModifyVisitor big_struct big_struct_fields varlist free 
    (currentFunction: fundec) = object(self)
  inherit nopCilVisitor  (* visit lvalues and statements *)
  method vlval l = match l with (* should we change this one? *)
    Var(vi),vi_offset when List.mem_assoc vi varlist -> (* check list *)
      let i = List.assoc vi varlist in (* find field offset *)
      let big_struct_field = List.nth big_struct_fields i in
      let new_lval = Mem(Lval(big_struct, NoOffset)),
	Field(big_struct_field,vi_offset) in (* rewrite the lvalue *)
      ChangeDoChildrenPost(new_lval, (fun l -> l))
  | _ -> DoChildren (* ignore other lvalues *)
  method vstmt s = match s.skind with (* also rewrite the return *)
    Return(None,loc) -> 
      let free_instr = Call(None,free,[Lval(big_struct,NoOffset)],loc) in
      self#queueInstr [free_instr]; (* insert free_instr before the return *)
      DoChildren
  | Return(Some exp ,loc) ->
      (* exp may depend on big_struct, so evaluate it before calling free. 
       * This becomes:  tmp = exp; free(big_struct); return tmp; *)
      let exp_new = visitCilExpr (self :> cilVisitor) exp in
      let ret_tmp = makeTempVar currentFunction (typeOf exp_new) in
      let eval_ret_instr = Set(var ret_tmp, exp_new, loc) in
      let free_instr = Call(None,free,[Lval(big_struct,NoOffset)],loc) in
      (* insert the instructions before the return *)
      self#queueInstr [eval_ret_instr; free_instr];
      s.skind <- (Return(Some(Lval(var ret_tmp)), loc));
      DoChildren
  | _ -> DoChildren (* ignore other statements *)
end
    
class heapifyAnalyzeVisitor f alloc free = object 
  inherit nopCilVisitor (* only look at function bodies *)
  method vglob gl = match gl with
    GFun(fundec,funloc) -> 
      let counter = ref 0 in (* the number of local vars containing arrays *)
      let varlist = ref [] in  (* a list of (var,id) pairs, in reverse order *)
      List.iter (fun vi ->  
         (* find all local vars with arrays.  If the user requests it,
            we also look for non-array vars whose address is taken. *)
        if (containsArray vi.vtype) || (vi.vaddrof && !heapifyNonArrays)
        then begin
          varlist := (vi,!counter) :: !varlist ; (* add it to the list *)
          incr counter (* put the next such var in the next slot *)
        end
        ) fundec.slocals ; 
      if (!varlist <> []) then begin (* some local vars contain arrays *)
        let name = (fundec.svar.vname ^ "_heapify") in
        let ci = mkCompInfo true name (* make a big structure *)
	    (fun _ -> List.rev_map (* reverse the list to fix the order *)
                (* each local var becomes a field *)
		(fun (vi,i) -> vi.vname,vi.vtype,None,[],vi.vdecl) !varlist) [] in
        let vi = makeLocalVar fundec name (TPtr(TComp(ci,[]),[])) in
        let modify = new heapifyModifyVisitor (Var(vi)) ci.cfields
	    !varlist free fundec in (* rewrite accesses to local vars *)
        fundec.sbody <- visitCilBlock modify fundec.sbody ;
        let alloc_stmt = mkStmt (* allocate the big struct on the heap *)
            (Instr [Call(Some(Var(vi),NoOffset), alloc, 
			 [SizeOf(TComp(ci,[]))],funloc)]) in
        fundec.sbody.bstmts <- alloc_stmt :: fundec.sbody.bstmts ; 
	fundec.slocals <- List.filter (fun vi -> (* remove local vars *)
	  not (List.mem_assoc vi !varlist)) fundec.slocals ; 
	let typedec = (GCompTag(ci,funloc)) in (* declare the big struct *)
        ChangeTo([typedec ; GFun(fundec,funloc)])  (* done! *)
      end else
	DoChildren	(* ignore everything else *)
  | _ -> DoChildren
end
    
let heapify (f : file) (alloc : exp) (free : exp)  =
  visitCilFile (new heapifyAnalyzeVisitor f alloc free) f;
  f

(* heapify code ends here *)

let default_heapify (f : file) =
  let alloc_fun = emptyFunction "malloc" in
  let free_fun = emptyFunction "free" in
  let alloc_exp = (Lval((Var(alloc_fun.svar)),NoOffset)) in
  let free_exp = (Lval((Var(free_fun.svar)),NoOffset)) in
  ignore (heapify f alloc_exp free_exp)
    
(* StackGuard clone *)

class sgModifyVisitor restore_ra_stmt = object
	inherit nopCilVisitor
  method vstmt s = match s.skind with (* also rewrite the return *)
    Return(_,loc) -> let new_block = mkBlock [restore_ra_stmt ; s] in 
			ChangeTo(mkStmt (Block(new_block)))  
	| _ -> DoChildren (* ignore other statements *)
end

class sgAnalyzeVisitor f push pop get_ra set_ra = object
  inherit nopCilVisitor
  method vfunc fundec = 
    let needs_guarding = List.fold_left 
	(fun acc vi -> acc || containsArray vi.vtype) 
	false fundec.slocals in
    if needs_guarding then begin
      let ra_tmp = makeLocalVar fundec "return_address" voidPtrType in
      let ra_exp = Lval(Var(ra_tmp),NoOffset) in 
      let save_ra_stmt = mkStmt (* save the current return address *)
	  (Instr [Call(Some(Var(ra_tmp),NoOffset), get_ra, [], locUnknown) ;
		   Call(None, push, [ra_exp], locUnknown)]) in
      let restore_ra_stmt = mkStmt (* restore the old return address *)
	  (Instr [Call(Some(Var(ra_tmp),NoOffset), pop, [], locUnknown) ;
		   Call(None, set_ra, [ra_exp], locUnknown)]) in
      let modify = new sgModifyVisitor restore_ra_stmt in
      fundec.sbody <- visitCilBlock modify fundec.sbody ;
      fundec.sbody.bstmts <- save_ra_stmt :: fundec.sbody.bstmts ;
      ChangeTo(fundec)  (* done! *)
    end else DoChildren
end
          
let stackguard (f : file) (push : exp) (pop : exp) 
    (get_ra : exp) (set_ra : exp) = 
  visitCilFileSameGlobals (new sgAnalyzeVisitor f push pop get_ra set_ra) f;
  f
    (* stackguard code ends *)
    
let default_stackguard (f : file) =
  let expify fundec = Lval(Var(fundec.svar),NoOffset) in
  let push = expify (emptyFunction "stackguard_push") in
  let pop = expify (emptyFunction "stackguard_pop") in
  let get_ra = expify (emptyFunction "stackguard_get_ra") in
  let set_ra = expify (emptyFunction "stackguard_set_ra") in
  let global_decl = 
"extern void * stackguard_get_ra();
extern void stackguard_set_ra(void *new_ra);
/* You must provide an implementation for functions that get and set the
 * return address. Such code is unfortunately architecture specific.
 */
struct stackguard_stack {
  void * data;
  struct stackguard_stack * next;
} * stackguard_stack;

void stackguard_push(void *ra) {
  void * old = stackguard_stack;
  stackguard_stack = (struct stackguard_stack *)
    malloc(sizeof(stackguard_stack));
  stackguard_stack->data = ra;
  stackguard_stack->next = old;
}

void * stackguard_pop() {
  void * ret = stackguard_stack->data;
  void * next = stackguard_stack->next;
  free(stackguard_stack);
  stackguard_stack->next = next;
  return ret;
}" in
    f.globals <- GText(global_decl) :: f.globals ;
    ignore (stackguard f push pop get_ra set_ra )
      
      
let feature1 : featureDescr = 
  { fd_name = "stackGuard";
    fd_enabled = Cilutil.doStackGuard;
    fd_description = "instrument function calls and returns to maintain a separate stack for return addresses" ;
    fd_extraopt = [];
    fd_doit = (function (f: file) -> default_stackguard f);
    fd_post_check = true;
  } 
let feature2 : featureDescr = 
  { fd_name = "heapify";
    fd_enabled = Cilutil.doHeapify;
    fd_description = "move stack-allocated arrays to the heap" ;
    fd_extraopt = [
      "--heapifyAll", Arg.Set heapifyNonArrays,
      "When using heapify, move all local vars whose address is taken, not just arrays.";
    ];
    fd_doit = (function (f: file) -> default_heapify f);
    fd_post_check = true;
  } 
      





