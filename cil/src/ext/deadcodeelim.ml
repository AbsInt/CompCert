(* Eliminate assignment instructions whose results are not
   used *)

open Cil
open Pretty

module E = Errormsg
module RD = Reachingdefs
module UD = Usedef
module IH = Inthash
module S = Stats

module IS = Set.Make(
  struct
    type t = int
    let compare = compare
  end)

let debug = RD.debug


let usedDefsSet = ref IS.empty
(* put used def ids into usedDefsSet *)
(* assumes reaching definitions have already been computed *)
class usedDefsCollectorClass = object(self)
    inherit RD.rdVisitorClass

  method add_defids iosh e u =
    UD.VS.iter (fun vi ->
      if IH.mem iosh vi.vid then 
	let ios = IH.find iosh vi.vid in
	if !debug then ignore(E.log "DCE: IOS size for vname=%s at stmt=%d: %d\n" 
				vi.vname sid (RD.IOS.cardinal ios));
	RD.IOS.iter (function
	    Some(i) -> 
	      if !debug then ignore(E.log "DCE: def %d used: %a\n" i d_plainexp e);
	      usedDefsSet := IS.add i (!usedDefsSet)
	  | None -> ()) ios
      else if !debug then ignore(E.log "DCE: vid %d:%s not in stm:%d iosh at %a\n"
				   vi.vid vi.vname sid d_plainexp e)) u

  method vexpr e =
    let u = UD.computeUseExp e in
    match self#get_cur_iosh() with
      Some(iosh) -> self#add_defids iosh e u; DoChildren
    | None ->
	if !debug then ignore(E.log "DCE: use but no rd data: %a\n" d_plainexp e);
	DoChildren

  method vinst i =
    let handle_inst iosh i = match i with
    | Asm(_,_,slvl,_,_,_) -> List.iter (fun (s,lv) ->
	match lv with (Var v, off) ->
	  if s.[0] = '+' then
	    self#add_defids iosh (Lval(Var v, off)) (UD.VS.singleton v)
	| _ -> ()) slvl
    | _ -> ()
    in
    begin try
      cur_rd_dat <- Some(List.hd rd_dat_lst);
      rd_dat_lst <- List.tl rd_dat_lst
    with Failure "hd" -> ()
    end;
    match self#get_cur_iosh() with
      Some iosh -> handle_inst iosh i; DoChildren
    | None -> DoChildren

end

(***************************************************
 * Also need to find reads from volatiles 
 * uses two functions I've put in ciltools which 
 * are basically what Zach wrote, except one is for 
 * types and one is for vars. Another difference is
 * they filter out pointers to volatiles. This 
 * handles DMA 
 ***************************************************)
class hasVolatile flag = object (self)
  inherit nopCilVisitor   
  method vlval l = 
    let tp = typeOfLval l in
    if (Ciltools.is_volatile_tp tp) then flag := true;
    DoChildren
  method vexpr e =
    DoChildren
end

let exp_has_volatile e = 
  let flag = ref false in
  ignore (visitCilExpr (new hasVolatile flag) e);
  !flag
 (***************************************************)

let removedCount = ref 0
(* Filter out instructions whose definition ids are not
   in usedDefsSet *)
class uselessInstrElim : cilVisitor = object(self)
  inherit nopCilVisitor

  method vstmt stm =

    let test (i,(_,s,iosh)) =
      match i with 
	Call _ -> true 
      | Set((Var vi,NoOffset),e,_) ->
	  if vi.vglob || (Ciltools.is_volatile_vi vi) || (exp_has_volatile e) then true else
	  let _, defd = UD.computeUseDefInstr i in
	  let rec loop n =
	    if n < 0 then false else
	    if IS.mem (n+s) (!usedDefsSet)
	    then true
	    else loop (n-1)
	  in
	  if loop (UD.VS.cardinal defd - 1)
	  then true
	  else (incr removedCount; false)
      | _ -> true
    in

    let filter il stmdat =
      let rd_dat_lst = RD.instrRDs il stm.sid stmdat false in
      let ildatlst = List.combine il rd_dat_lst in
      let ildatlst' = List.filter test ildatlst in
      let (newil,_) = List.split ildatlst' in
      newil
    in

    match RD.getRDs stm.sid with
      None -> DoChildren
    | Some(_,s,iosh) ->
	match stm.skind with
	  Instr il ->
	    stm.skind <- Instr(filter il ((),s,iosh));
	    SkipChildren
	| _ -> DoChildren
	    
end

(* until fixed point is reached *)
let elim_dead_code_fp (fd : fundec) :  fundec =
  (* fundec -> fundec *)
  let rec loop fd =
    usedDefsSet := IS.empty;
    removedCount := 0;
    S.time "reaching definitions" RD.computeRDs fd;
    ignore(visitCilFunction (new usedDefsCollectorClass :> cilVisitor) fd);
    let fd' = visitCilFunction (new uselessInstrElim) fd in
    if !removedCount = 0 then fd' else loop fd'
  in
  loop fd

(* just once *)
let elim_dead_code (fd : fundec) :  fundec =
  (* fundec -> fundec *)
  usedDefsSet := IS.empty;
  removedCount := 0;
  S.time "reaching definitions" RD.computeRDs fd;
  ignore(visitCilFunction (new usedDefsCollectorClass :> cilVisitor) fd);
  let fd' = visitCilFunction (new uselessInstrElim) fd in
  fd'

class deadCodeElimClass : cilVisitor = object(self)
    inherit nopCilVisitor

  method vfunc fd =
    let fd' = elim_dead_code fd in
    ChangeTo(fd')

end

let dce f =
  if !debug then ignore(E.log "DCE: starting dead code elimination\n");
  visitCilFile (new deadCodeElimClass) f
