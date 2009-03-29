(* MODIF: Loop constructor replaced by 3 constructors: While, DoWhile, For. *)

module IH = Inthash
module E = Errormsg

open Cil
open Pretty

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


module ForwardsDataFlow = 
  functor (T : ForwardsTransfer) ->
  struct

    (** Keep a worklist of statements to process. It is best to keep a queue, 
     * because this way it is more likely that we are going to process all 
     * predecessors of a statement before the statement itself. *)
    let worklist: Cil.stmt Queue.t = Queue.create ()

    (** We call this function when we have encountered a statement, with some 
     * state. *)
    let reachedStatement (s: stmt) (d: T.t) : unit = 
      (** see if we know about it already *)
      E.pushContext (fun _ -> dprintf "Reached statement %d with %a" 
          s.sid T.pretty d);
      let newdata: T.t option = 
        try
          let old = IH.find T.stmtStartData s.sid in 
          match T.combinePredecessors s ~old:old d with 
            None -> (* We are done here *)
              if !T.debug then 
                ignore (E.log "FF(%s): reached stmt %d with %a\n  implies the old state %a\n"
                          T.name s.sid T.pretty d T.pretty old);
              None
          | Some d' -> begin
              (* We have changed the data *) 
              if !T.debug then 
                ignore (E.log "FF(%s): weaken data for block %d: %a\n" 
                          T.name s.sid T.pretty d');
              Some d'
          end
        with Not_found -> (* was bottom before *)
          let d' = T.computeFirstPredecessor s d in 
          if !T.debug then 
            ignore (E.log "FF(%s): set data for block %d: %a\n" 
                      T.name s.sid T.pretty d');
          Some d'
      in
      E.popContext ();
      match newdata with 
        None -> ()
      | Some d' -> 
          IH.replace T.stmtStartData s.sid d';
          if T.filterStmt s && 
            not (Queue.fold (fun exists s' -> exists || s'.sid = s.sid)
                            false
                            worklist) then 
            Queue.add s worklist


    (** Get the two successors of an If statement *)
    let ifSuccs (s:stmt) : stmt * stmt = 
      let fstStmt blk = match blk.bstmts with
          [] -> Cil.dummyStmt
        | fst::_ -> fst
      in
      match s.skind with
        If(e, b1, b2, _) ->
          let thenSucc = fstStmt b1 in
          let elseSucc = fstStmt b2 in
          let oneFallthrough () = 
            let fallthrough = 
              List.filter 
                (fun s' -> thenSucc != s' && elseSucc != s')
                s.succs
            in
            match fallthrough with
              [] -> E.s (bug "Bad CFG: missing fallthrough for If.")
            | [s'] -> s'
            | _ ->  E.s (bug "Bad CFG: multiple fallthrough for If.")
          in
          (* If thenSucc or elseSucc is Cil.dummyStmt, it's an empty block.
             So the successor is the statement after the if *)
          let stmtOrFallthrough s' =
            if s' == Cil.dummyStmt then
              oneFallthrough ()
            else 
              s'
          in
          (stmtOrFallthrough thenSucc,
           stmtOrFallthrough elseSucc)
            
      | _-> E.s (bug "ifSuccs on a non-If Statement.")

    (** Process a statement *)
    let processStmt (s: stmt) : unit = 
      currentLoc := get_stmtLoc s.skind;
      if !T.debug then 
        ignore (E.log "FF(%s).stmt %d at %t\n" T.name s.sid d_thisloc);

      (* It must be the case that the block has some data *)
      let init: T.t = 
         try T.copy (IH.find T.stmtStartData s.sid) 
         with Not_found -> 
            E.s (E.bug "FF(%s): processing block without data" T.name)
      in

      (** See what the custom says *)
      match T.doStmt s init with 
        SDone  -> ()
      | (SDefault | SUse _) as act -> begin
          let curr = match act with
              SDefault -> init
            | SUse d -> d
            | SDone -> E.s (bug "SDone")
          in
          (* Do the instructions in order *)
          let handleInstruction (s: T.t) (i: instr) : T.t = 
            currentLoc := get_instrLoc i;
            
            (* Now handle the instruction itself *)
            let s' = 
              let action = T.doInstr i s in 
              match action with 
               | Done s' -> s'
               | Default -> s (* do nothing *)
               | Post f -> f s
            in
            s'
          in

          let after: T.t = 
            match s.skind with 
              Instr il -> 
                (* Handle instructions starting with the first one *)
                List.fold_left handleInstruction curr il

            | Goto _ | Break _ | Continue _ | If _ 
            | TryExcept _ | TryFinally _ 
            | Switch _ | (*Loop _*) While _ | DoWhile _ | For _
	    | Return _ | Block _ -> curr
          in
          currentLoc := get_stmtLoc s.skind;
                
          (* Handle If guards *)
          let succsToReach = match s.skind with
              If (e, _, _, _) -> begin
                let not_e = UnOp(LNot, e, intType) in
                let thenGuard = T.doGuard e after in
                let elseGuard = T.doGuard not_e after in
                if thenGuard = GDefault && elseGuard = GDefault then
                  (* this is the common case *)
                  s.succs
                else begin
                  let doBranch succ guard =
                    match guard with
                      GDefault -> reachedStatement succ after
                    | GUse d ->  reachedStatement succ d
                    | GUnreachable -> 
                        if !T.debug then 
                          ignore (E.log "FF(%s): Not exploring branch to %d\n" 
                                    T.name succ.sid);

                        ()
                  in
                  let thenSucc, elseSucc = ifSuccs s  in
                  doBranch thenSucc thenGuard;
                  doBranch elseSucc elseGuard;
                  []
                end
              end
            | _ -> s.succs
          in
          (* Reach the successors *)
          List.iter (fun s' -> reachedStatement s' after) succsToReach;

      end




          (** Compute the data flow. Must have the CFG initialized *)
    let compute (sources: stmt list) = 
      Queue.clear worklist;
      List.iter (fun s -> Queue.add s worklist) sources;

      (** All initial stmts must have non-bottom data *)
      List.iter (fun s -> 
         if not (IH.mem T.stmtStartData s.sid) then 
           E.s (E.error "FF(%s): initial stmt %d does not have data"
                  T.name s.sid))
         sources;
      if !T.debug then
        ignore (E.log "\nFF(%s): processing\n"
                  T.name); 
      let rec fixedpoint () = 
        if !T.debug && not (Queue.is_empty worklist) then 
          ignore (E.log "FF(%s): worklist= %a\n" 
                    T.name
                    (docList (fun s -> num s.sid)) 
                    (List.rev
                       (Queue.fold (fun acc s -> s :: acc) [] worklist)));
        try 
          let s = Queue.take worklist in 
          processStmt s;
          fixedpoint ();
        with Queue.Empty -> 
          if !T.debug then 
            ignore (E.log "FF(%s): done\n\n" T.name)
      in
      fixedpoint ()
          
  end



(******************************************************************
 **********
 **********         BACKWARDS 
 **********
 ********************************************************************)
module type BackwardsTransfer = sig
  val name: string (* For debugging purposes, the name of the analysis *)

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

module BackwardsDataFlow = 
  functor (T : BackwardsTransfer) -> 
  struct

    let getStmtStartData (s: stmt) : T.t = 
      try IH.find T.stmtStartData s.sid
      with Not_found -> 
        E.s (E.bug "BF(%s): stmtStartData is not initialized for %d"
               T.name s.sid)

    (** Process a statement and return true if the set of live return 
     * addresses on its entry has changed. *)
    let processStmt (s: stmt) : bool = 
      if !T.debug then 
        ignore (E.log "FF(%s).stmt %d\n" T.name s.sid);


      (* Find the state before the branch *)
      currentLoc := get_stmtLoc s.skind;
      let d: T.t = 
        match T.doStmt s with 
           Done d -> d
         | (Default | Post _) as action -> begin
             (* Do the default one. Combine the successors *)
             let res = 
               match s.succs with 
                 [] -> E.s (E.bug "You must doStmt for the statements with no successors")
               | fst :: rest -> 
                   List.fold_left (fun acc succ -> 
                     T.combineSuccessors acc (getStmtStartData succ))
                     (getStmtStartData fst)
                     rest
             in
             (* Now do the instructions *)
             let res' = 
               match s.skind with 
                 Instr il -> 
                   (* Now scan the instructions in reverse order. This may 
                    * Stack_overflow on very long blocks ! *)
                   let handleInstruction (i: instr) (s: T.t) : T.t = 
                     currentLoc := get_instrLoc i;
                     (* First handle the instruction itself *)
                     let action = T.doInstr i s in 
                     match action with 
                     | Done s' -> s'
                     | Default -> s (* do nothing *)
                     | Post f -> f s
                   in
                   (* Handle instructions starting with the last one *)
                   List.fold_right handleInstruction il res

               | _ -> res
             in
             match action with 
               Post f -> f res'
             | _ -> res'
         end
      in

      (* See if the state has changed. The only changes are that it may grow.*)
      let s0 = getStmtStartData s in 

      match T.combineStmtStartData s ~old:s0 d with 
        None -> (* The old data is good enough *)
          false

      | Some d' -> 
          (* We have changed the data *) 
          if !T.debug then 
            ignore (E.log "BF(%s): set data for block %d: %a\n" 
                      T.name s.sid T.pretty d');
          IH.replace T.stmtStartData s.sid d';
          true


          (** Compute the data flow. Must have the CFG initialized *)
    let compute (sinks: stmt list) = 
      let worklist: Cil.stmt Queue.t = Queue.create () in
      List.iter (fun s -> Queue.add s worklist) sinks;
      if !T.debug && not (Queue.is_empty worklist) then
        ignore (E.log "\nBF(%s): processing\n" 
                  T.name); 
      let rec fixedpoint () = 
        if !T.debug &&  not (Queue.is_empty worklist) then 
          ignore (E.log "BF(%s): worklist= %a\n" 
                    T.name
                    (docList (fun s -> num s.sid)) 
                    (List.rev
                       (Queue.fold (fun acc s -> s :: acc) [] worklist)));
        try 
          let s = Queue.take worklist in 
          let changes = processStmt s in 
          if changes then begin
            (* We must add all predecessors of block b, only if not already 
             * in and if the filter accepts them. *)
            List.iter 
              (fun p ->
                if not (Queue.fold (fun exists s' -> exists || p.sid = s'.sid) 
                          false worklist) &&
                  T.filterStmt p s then 
                  Queue.add p worklist)
              s.preds;
          end;
          fixedpoint ();

        with Queue.Empty -> 
          if !T.debug then 
            ignore (E.log "BF(%s): done\n\n" T.name)
      in
      fixedpoint ();
          
  end


