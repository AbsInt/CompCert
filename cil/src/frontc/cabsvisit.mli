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

(* cabsvisit.mli *)
(* interface for cabsvisit.ml *)

(* Different visiting actions. 'a will be instantiated with exp, instr, etc. *)
type 'a visitAction = 
    SkipChildren                        (* Do not visit the children. Return 
                                         * the node as it is *)
  | ChangeTo of 'a                      (* Replace the expression with the 
                                         * given one *)
  | DoChildren                          (* Continue with the children of this 
                                         * node. Rebuild the node on return 
                                         * if any of the children changes 
                                         * (use == test) *)
  | ChangeDoChildrenPost of 'a * ('a -> 'a) (* First consider that the entire 
                                          * exp is replaced by the first 
                                          * paramenter. Then continue with 
                                          * the children. On return rebuild 
                                          * the node if any of the children 
                                          * has changed and then apply the 
                                          * function on the node *)

type nameKind = 
    NVar                                (** Variable or function prototype 
                                           name *)
  | NFun                                (** Function definition name *)
  | NField                              (** The name of a field *)
  | NType                               (** The name of a type *)


(* All visit methods are called in preorder! (but you can use 
 * ChangeDoChildrenPost to change the order) *)
class type cabsVisitor = object
  method vexpr: Cabs.expression -> Cabs.expression visitAction   (* expressions *)
  method vinitexpr: Cabs.init_expression -> Cabs.init_expression visitAction   
  method vstmt: Cabs.statement -> Cabs.statement list visitAction
  method vblock: Cabs.block -> Cabs.block visitAction
  method vvar: string -> string                  (* use of a variable 
                                                        * names *)
  method vdef: Cabs.definition -> Cabs.definition list visitAction
  method vtypespec: Cabs.typeSpecifier -> Cabs.typeSpecifier visitAction
  method vdecltype: Cabs.decl_type -> Cabs.decl_type visitAction

      (* For each declaration we call vname *)
  method vname: nameKind -> Cabs.specifier -> Cabs.name -> Cabs.name visitAction
  method vspec: Cabs.specifier -> Cabs.specifier visitAction     (* specifier *)
  method vattr: Cabs.attribute -> Cabs.attribute list visitAction


  method vEnterScope: unit -> unit
  method vExitScope: unit -> unit
end


class nopCabsVisitor: cabsVisitor


val visitCabsTypeSpecifier: cabsVisitor -> 
                            Cabs.typeSpecifier -> Cabs.typeSpecifier
val visitCabsSpecifier: cabsVisitor -> Cabs.specifier -> Cabs.specifier

(** Visits a decl_type. The bool argument is saying whether we are ina 
  * function definition and thus the scope in a PROTO should extend until the 
  * end of the function *)
val visitCabsDeclType: cabsVisitor -> bool -> Cabs.decl_type -> Cabs.decl_type
val visitCabsDefinition: cabsVisitor -> Cabs.definition -> Cabs.definition list
val visitCabsBlock: cabsVisitor -> Cabs.block -> Cabs.block
val visitCabsStatement: cabsVisitor -> Cabs.statement -> Cabs.statement list
val visitCabsExpression: cabsVisitor -> Cabs.expression -> Cabs.expression
val visitCabsAttributes: cabsVisitor -> Cabs.attribute list 
                                     -> Cabs.attribute list
val visitCabsName: cabsVisitor -> nameKind 
                   -> Cabs.specifier -> Cabs.name -> Cabs.name
val visitCabsFile: cabsVisitor -> Cabs.file -> Cabs.file



(** Set by the visitor to the current location *)
val visitorLocation: Cabs.cabsloc ref
