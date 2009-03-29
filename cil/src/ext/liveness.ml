
(* Calculate which variables are live at
 * each statememnt.
 *
 *
 *
 *)

open Cil
open Pretty

module DF = Dataflow
module UD = Usedef
module IH = Inthash
module E = Errormsg

let debug = ref false

let live_label = ref ""
let live_func = ref ""

module VS = UD.VS

let debug_print () vs = (VS.fold
    (fun vi d -> 
      d ++ text "name: " ++ text vi.vname
	++ text " id: " ++ num vi.vid ++ text " ")
    vs nil) ++ line

let min_print () vs = (VS.fold
    (fun vi d ->
      d ++ text vi.vname
	++ text "(" ++ d_type () vi.vtype ++ text ")"
	++ text ",")
    vs nil) ++ line

let printer = ref debug_print

module LiveFlow = struct
  let name = "Liveness"
  let debug = debug
  type t = VS.t

  let pretty () vs =
    let fn = !printer in
    fn () vs
    
  let stmtStartData = IH.create 32

  let combineStmtStartData (stm:stmt) ~(old:t) (now:t) =
    if not(VS.compare old now = 0)
    then Some(VS.union old now)
    else None

  let combineSuccessors = VS.union

  let doStmt stmt =
    if !debug then ignore(E.log "looking at: %a\n" d_stmt stmt);
    match stmt.succs with
      [] -> let u,d = UD.computeUseDefStmtKind stmt.skind in
      if !debug then ignore(E.log "doStmt: no succs %d\n" stmt.sid);
      DF.Done u
    | _ ->
	let handle_stm vs = match stmt.skind with
	  Instr _ -> vs
	| s -> let u, d = UD.computeUseDefStmtKind s in
	  VS.union u (VS.diff vs d)
	in
	DF.Post handle_stm

  let doInstr i vs =
    let transform vs' =
      let u,d = UD.computeUseDefInstr i in
      VS.union u (VS.diff vs' d)
    in
    DF.Post transform

  let filterStmt stm1 stm2 = true

end

module L = DF.BackwardsDataFlow(LiveFlow)

let sink_stmts = ref []
class sinkFinderClass = object(self)
  inherit nopCilVisitor

  method vstmt s = match s.succs with
    [] -> (sink_stmts := s :: (!sink_stmts);
	   DoChildren)
  | _ -> DoChildren

end

(* gives list of return statements from a function *)
(* fundec -> stm list *)
let find_sinks fdec =
  sink_stmts := [];
  ignore(visitCilFunction (new sinkFinderClass) fdec);
  !sink_stmts

(* XXX: This does not compute the best ordering to
 * give to the work-list algorithm.
 *)
let all_stmts = ref []
class nullAdderClass = object(self)
  inherit nopCilVisitor

  method vstmt s =
    all_stmts := s :: (!all_stmts);
    IH.add LiveFlow.stmtStartData s.sid VS.empty;
    DoChildren

end

let null_adder fdec =
  ignore(visitCilFunction (new nullAdderClass) fdec);
  !all_stmts

let computeLiveness fdec =
  IH.clear LiveFlow.stmtStartData;
  UD.onlyNoOffsetsAreDefs := false;
  all_stmts := [];
  let a = null_adder fdec in
  L.compute a

let print_everything () =
  let d = IH.fold (fun i vs d -> 
    d ++ num i ++ text ": " ++ LiveFlow.pretty () vs) 
      LiveFlow.stmtStartData nil in
  ignore(printf "%t" (fun () -> d))

let match_label lbl = match lbl with
  Label(str,_,b) ->
    if !debug then ignore(E.log "Liveness: label seen: %s\n" str);
    (*b && *)(String.compare str (!live_label) = 0)
| _ -> false

class doFeatureClass = object(self)
  inherit nopCilVisitor

  method vfunc fd =
    if String.compare fd.svar.vname (!live_func) = 0 then 
      (Cfg.clearCFGinfo fd;
       ignore(Cfg.cfgFun fd);
       computeLiveness fd;
       if String.compare (!live_label) "" = 0 then
	 (printer := min_print;
	  print_everything();
	  SkipChildren)
       else DoChildren)
    else SkipChildren

  method vstmt s =
    if List.exists match_label s.labels then try
      let vs = IH.find LiveFlow.stmtStartData s.sid in
      (printer := min_print;
       ignore(printf "%a" LiveFlow.pretty vs);
       SkipChildren)
    with Not_found -> 
      if !debug then ignore(E.log "Liveness: stmt: %d not found\n" s.sid);
      DoChildren
    else 
      (if List.length s.labels = 0 then
	if !debug then ignore(E.log "Liveness: no label at sid=%d\n" s.sid);
      DoChildren)

end

let do_live_feature (f:file) =
  visitCilFile (new doFeatureClass) f

let feature =
  {
   fd_name = "Liveness";
   fd_enabled = ref false;
   fd_description = "Spit out live variables at a label";
   fd_extraopt = [
   "--live_label",
   Arg.String (fun s -> live_label := s),
   "Output the variables live at this label";
   "--live_func",
   Arg.String (fun s -> live_func := s),
   "Output the variables live at each statement in this function.";
   "--live_debug",
   Arg.Unit (fun n -> debug := true),
   "Print lots of debugging info";];
   fd_doit = do_live_feature;
   fd_post_check = false
 }
