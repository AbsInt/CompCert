(** A framework for data flow analysis for CIL code.  Before using 
    this framework, you must initialize the Control-flow Graph for your
    program, e.g using {!Cfg.computeFileCFG} *)

type 't action = 
    Default (** The default action *)
  | Done of 't (** Do not do the default action. Use this result *)
  | Post of ('t -> 't) (** The default action, followed by the given 
                        * transformer *)

type 't stmtaction = 
    SDefault   (** The default action *)
  | SDone      (** Do not visit this statement or its successors *)
  | SUse of 't (** Visit the instructions and successors of this statement
                  as usual, but use the specified state instead of the 
                  one that was passed to doStmt *)

(* For if statements *)
type 't guardaction = 
    GDefault      (** The default state *) 
  | GUse of 't    (** Use this data for the branch *)
  | GUnreachable  (** The branch will never be taken. *)


(******************************************************************
 **********
 **********         FORWARDS 
 **********
 ********************************************************************)

module type ForwardsTransfer = sig
  val name: string (** For debugging purposes, the name of the analysis *)

  val debug: bool ref (** Whether to turn on debugging *)

  type t  (** The type of the data we compute for each block start. May be 
           * imperative.  *)

  val copy: t -> t
  (** Make a deep copy of the data *)


  val stmtStartData: t Inthash.t
  (** For each statement id, the data at the start. Not found in the hash 
   * table means nothing is known about the state at this point. At the end 
   * of the analysis this means that the block is not reachable. *)

  val pretty: unit -> t -> Pretty.doc 
  (** Pretty-print the state *)

  val computeFirstPredecessor: Cil.stmt -> t -> t
  (** Give the first value for a predecessors, compute the value to be set 
   * for the block *)

  val combinePredecessors: Cil.stmt -> old:t -> t -> t option
  (** Take some old data for the start of a statement, and some new data for 
   * the same point. Return None if the combination is identical to the old 
   * data. Otherwise, compute the combination, and return it. *)

  val doInstr: Cil.instr -> t -> t action
  (** The (forwards) transfer function for an instruction. The 
   * {!Cil.currentLoc} is set before calling this. The default action is to 
   * continue with the state unchanged. *)

  val doStmt: Cil.stmt -> t -> t stmtaction
  (** The (forwards) transfer function for a statement. The {!Cil.currentLoc} 
   * is set before calling this. The default action is to do the instructions
   * in this statement, if applicable, and continue with the successors. *)

  val doGuard: Cil.exp -> t -> t guardaction
  (** Generate the successor to an If statement assuming the given expression
    * is nonzero.  Analyses that don't need guard information can return 
    * GDefault; this is equivalent to returning GUse of the input.
    * A return value of GUnreachable indicates that this half of the branch
    * will not be taken and should not be explored.  This will be called
    * twice per If, once for "then" and once for "else".  
    *)

  val filterStmt: Cil.stmt -> bool
  (** Whether to put this statement in the worklist. This is called when a 
   * block would normally be put in the worklist. *)
  
end

module ForwardsDataFlow (T : ForwardsTransfer) : sig
  val compute: Cil.stmt list -> unit
  (** Fill in the T.stmtStartData, given a number of initial statements to 
   * start from. All of the initial statements must have some entry in 
   * T.stmtStartData (i.e., the initial data should not be bottom) *)
end

(******************************************************************
 **********
 **********         BACKWARDS 
 **********
 ********************************************************************)
module type BackwardsTransfer = sig
  val name: string (** For debugging purposes, the name of the analysis *)

  val debug: bool ref (** Whether to turn on debugging *)

  type t  (** The type of the data we compute for each block start. In many 
           * presentations of backwards data flow analysis we maintain the 
           * data at the block end. This is not easy to do with JVML because 
           * a block has many exceptional ends. So we maintain the data for 
           * the statement start. *)

  val pretty: unit -> t -> Pretty.doc (** Pretty-print the state *)

  val stmtStartData: t Inthash.t
  (** For each block id, the data at the start. This data structure must be 
   * initialized with the initial data for each block *)

  val combineStmtStartData: Cil.stmt -> old:t -> t -> t option
  (** When the analysis reaches the start of a block, combine the old data 
   * with the one we have just computed. Return None if the combination is 
   * the same as the old data, otherwise return the combination. In the 
   * latter case, the predecessors of the statement are put on the working 
   * list. *)


  val combineSuccessors: t -> t -> t
  (** Take the data from two successors and combine it *)


  val doStmt: Cil.stmt -> t action
  (** The (backwards) transfer function for a branch. The {!Cil.currentLoc} is 
   * set before calling this. If it returns None, then we have some default 
   * handling. Otherwise, the returned data is the data before the branch 
   * (not considering the exception handlers) *)

  val doInstr: Cil.instr -> t -> t action
  (** The (backwards) transfer function for an instruction. The 
   * {!Cil.currentLoc} is set before calling this. If it returns None, then we 
   * have some default handling. Otherwise, the returned data is the data 
   * before the branch (not considering the exception handlers) *)

  val filterStmt: Cil.stmt -> Cil.stmt -> bool
  (** Whether to put this predecessor block in the worklist. We give the 
   * predecessor and the block whose predecessor we are (and whose data has 
   * changed)  *)
  
end

module BackwardsDataFlow (T : BackwardsTransfer) : sig
  val compute: Cil.stmt list -> unit
  (** Fill in the T.stmtStartData, given a number of initial statements to 
   * start from (the sinks for the backwards data flow). All of the statements
   * (not just the initial ones!) must have some entry in T.stmtStartData 
   * (i.e., the initial data should not be bottom) *)
end
