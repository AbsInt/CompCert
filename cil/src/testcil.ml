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

(* A test for CIL *)
open Pretty
open Cil
module E = Errormsg

let lu = locUnknown

(* If you have trouble try to reproduce the problem on a smaller type. Try 
 * limiting the maxNesting and integerKinds *)
let integerKinds = [ IChar; ISChar; IUChar; IInt; IUInt; IShort; IUShort;
                     ILong; IULong; ILongLong; IULongLong ] 
let floatKinds = [ FFloat; FDouble ] 
    
let baseTypes = 
       (List.map (fun ik -> (1, fun _ -> TInt(ik, []))) integerKinds)
     @ (List.map (fun fk -> (1, fun _ -> TFloat(fk, []))) floatKinds)


(* Make a random struct *)
let maxNesting  = ref 3  (* Maximum number of levels for struct nesting *)
let maxFields   = ref 8  (* The maximum number of fields in a struct *)
let useBitfields = ref false
let useZeroBitfields = ref true



(* Collect here the globals *)
let globals: global list ref = ref []
let addGlobal (g:global) = globals := g :: !globals
let getGlobals () = List.rev !globals
 
(* Collect here the statements for main *)
let statements: stmt list ref = ref []
let addStatement (s: stmt) = statements := s :: !statements
let getStatements () = List.rev !statements

(* Keep here the main function *)
let main: fundec ref = ref dummyFunDec
let mainRetVal: varinfo ref = ref dummyFunDec.svar

let assertId = ref 0 
let addAssert (b: exp) (extra: stmt list) : unit = 
  incr assertId;
  addStatement (mkStmt (If(UnOp(LNot, b, intType),
                           mkBlock (extra @ 
                                    [mkStmt (Return (Some (integer !assertId),
                                                     lu))]),
                           mkBlock [], lu)))

let addSetRetVal (b: exp) (extra: stmt list) : unit = 
  addStatement 
    (mkStmt (If(UnOp(LNot, b, intType),
                mkBlock (extra @ 
                         [mkStmtOneInstr (Set(var !mainRetVal, one, lu))]),
                mkBlock [], lu)))


let printfFun: fundec = 
  let fdec = emptyFunction "printf" in
  fdec.svar.vtype <- 
     TFun(intType, Some [ ("format", charPtrType, [])], true, []);
  fdec


let memsetFun: fundec = 
  let fdec = emptyFunction "memset" in
  fdec.svar.vtype <- 
     TFun(voidPtrType, Some [ ("start", voidPtrType, []);
                              ("v", intType, []);
                              ("len", uintType, [])], false, []);
  fdec

let checkOffsetFun: fundec = 
  let fdec = emptyFunction "checkOffset" in
  fdec.svar.vtype <- 
     TFun(voidType, Some [ ("start", voidPtrType, []);
                           ("len", uintType, []);
                           ("expected_start", intType, []);
                           ("expected_width", intType, []);
                           ("name", charPtrType, []) ], false, []);
  fdec

let checkSizeOfFun: fundec = 
  let fdec = emptyFunction "checkSizeOf" in
  fdec.svar.vtype <- 
     TFun(voidType, Some [ ("len", uintType, []);
                           ("expected", intType, []);
                           ("name", charPtrType, []) ], false, []);
  fdec


let doPrintf format args = 
  mkStmtOneInstr (Call(None, Lval(var printfFun.svar),
                       (Const(CStr format)) :: args, lu))


(* Select among the choices, each with a given weight *)
type 'a selection = int * (unit -> 'a)
let select (choices: 'a selection list) : 'a = 
  (* Find the total weight *)
  let total = List.fold_left (fun sum (w, _) -> sum + w) 0 choices in
  if total = 0 then E.s (E.bug "Total for choices = 0\n");
  (* Pick a random number *)
  let thechoice = Random.int total in
  (* Now get the choice *)
  let rec loop thechoice = function
      [] -> E.s (E.bug "Ran out of choices\n")
    | (w, c) :: rest -> 
        if thechoice < w then c () else loop (thechoice - w) rest
  in
  loop thechoice choices


(* Generate a new name *)
let nameId = ref 0
let newName (base: string) = 
  incr nameId;
  base ^ (string_of_int !nameId)


(********** Testing of SIZEOF ***********)

(* The current selection of types *)
let typeChoices : typ selection list ref = ref [] 

let baseTypeChoices : typ selection list ref = ref []


let currentNesting = ref 0
let mkCompType (iss: bool) =  
  if !currentNesting >= !maxNesting then (* Replace it with an int *)
    select !baseTypeChoices
  else begin
    incr currentNesting;
    let ci = 
      mkCompInfo iss (newName "comp") 
        (fun _ -> 
          let nrFields = 1 + (Random.int !maxFields) in
          let rec mkFields (i: int) =
            if i = nrFields then [] else begin
              let ft = select !typeChoices in
              let fname = "f" ^ string_of_int i in
              let fname', width = 
                if not !useBitfields || not (isIntegralType ft) 
                                     || (Random.int 8 >= 6) then 
                  fname, None 
                else begin
                  let tw = bitsSizeOf ft in (* Assume this works for TInt *)
                  let w = (if !useZeroBitfields then 0 else 1) + 
                          Random.int (3 * tw / 4) in
                  (if w = 0 then "___missing_field_name" else fname), Some w
                end
              in
              (fname', ft, width, [], lu) :: mkFields (i + 1) 
            end
          in
          mkFields 0)
        []
    in
    decr currentNesting;
    (* Register it with the file *)
    addGlobal (GCompTag(ci, lu));
    TComp(ci, [])
  end

(* Make a pointer type. They are all equal so make one to void *)
let mkPtrType () = TPtr(TVoid([]), [])

(* Make an array type. *)
let mkArrayType () = 
  if !currentNesting >= !maxNesting then 
    select !baseTypeChoices
  else begin
    incr currentNesting;
    let at = TArray(select !typeChoices, Some (integer (1 + (Random.int 32))),
                    []) in
    decr currentNesting;
    at
  end
  

let testSizeOf () = 
  let doOne (i: int) = 
(*    ignore (E.log "doOne %d\n" i); *)
    (* Make a random type *)
    let t = select !typeChoices in
    (* Create a global with that type *)
    let g = makeGlobalVar (newName "g") t in
    addGlobal (GVar(g, {init=None}, lu));
    addStatement (mkStmtOneInstr(Call(None, Lval(var memsetFun.svar),
                                      [ mkAddrOrStartOf (var g); zero;
                                        SizeOfE(Lval(var g))], lu)));
    try
(*      if i = 0 then ignore (E.log "0: %a\n" d_plaintype t); *)
      let bsz = 
        try bitsSizeOf t  (* This is what we are testing *)
        with e -> begin
          ignore (E.log "Exception %s caught while computing bitsSizeOf(%a)\n"
                    (Printexc.to_string e) d_type t);
          raise (Failure "")
        end
      in
(*      ignore (E.log "1 "); *)
      if bsz mod 8 <> 0 then begin
        ignore (E.log "bitsSizeOf did not return a multiple of 8\n");
        raise (Failure "");
      end;
(*      ignore (E.log "2 "); *)
      (* Check the offset of all fields in there *)
      let rec checkOffsets (lv: lval) (lvt: typ) = 
        match lvt with
          TComp(c, _) -> 
            List.iter 
              (fun f -> 
                if f.fname <> "___missing_field_name" then 
                  checkOffsets (addOffsetLval (Field(f, NoOffset)) lv) f.ftype)
              c.cfields
        | TArray (bt, Some len, _) -> 
            let leni = 
              match isInteger len with
                Some i64 -> Int64.to_int i64
              | None -> E.s (E.bug "Array length is not a constant")
            in
            let i = Random.int leni in
            checkOffsets (addOffsetLval (Index(integer i, NoOffset)) lv) bt

        | _ -> (* Now a base type *)
            let _, off = lv in 
            let start, width = bitsOffset t off in
            let setLv (v: exp) = 
              match lvt with
                TFloat (FFloat, _) -> 
                  Set((Mem (mkCast (AddrOf lv) intPtrType), NoOffset),
                      v, lu)
              | TFloat (FDouble, _) -> 
                  Set((Mem (mkCast (AddrOf lv) 
                              (TPtr(TInt(IULongLong, []), []))), NoOffset),
                      mkCast v (TInt(IULongLong, [])), lu)

              | (TPtr _ | TInt((IULongLong|ILongLong), _)) -> 
                  Set(lv, mkCast v lvt, lu)
              | _ -> Set(lv, v, lu)
            in
            let ucharPtrType = TPtr(TInt(IUChar, []), []) in
            let s = 
              mkStmt (Instr ([ setLv mone;
                               Call(None, Lval(var checkOffsetFun.svar),
                                    [ mkCast (mkAddrOrStartOf (var g))
                                             ucharPtrType;
                                      SizeOfE (Lval(var g));
                                      integer start; 
                                      integer width;
                                      (Const(CStr(sprint 80 
                                                    (d_lval () lv))))],lu);
                               setLv zero])) in
            addStatement s
      in
      checkOffsets (var g) t;
(*      ignore (E.log "3 ");*)
      (* Now check the size of *)
      let s = mkStmtOneInstr (Call(None, Lval(var checkSizeOfFun.svar),
                                   [ SizeOfE (Lval (var g));
                                     integer (bitsSizeOf t);
                                     mkString g.vname ], lu)) in
      addStatement s;
(*      ignore (E.log "10\n"); *)
    with _ -> ()
  in

  (* Make the composite choices more likely *)
  typeChoices := 
     [ (1, mkPtrType); 
       (5, mkArrayType);
       (5, fun _ -> mkCompType true);
       (5, fun _ -> mkCompType false); ]
     @ baseTypes;
  baseTypeChoices := baseTypes;
  useBitfields := false;
  maxFields := 4;
  for i = 0 to 100 do 
    doOne i
  done;
                   
  (* Now test the bitfields. *)
  typeChoices :=  [ (1, fun _ -> mkCompType true) ];
  baseTypeChoices := [(1, fun _ -> TInt(IInt, []))];
  useBitfields := true;

  for i = 0 to 100 do
    doOne i
  done;

  (* Now make it a bit more complicated *)
  baseTypeChoices := 
     List.map (fun ik -> (1, fun _ -> TInt(ik, []))) 
       [IInt; ILong; IUInt; IULong ];
  useBitfields := true;
  for i = 0 to 100 do
    doOne i
  done;

  (* An really complicated now *)
  baseTypeChoices := baseTypes;
  useBitfields := true;
  for i = 0 to 100 do 
    doOne i
  done;

  ()


(* Now the main tester. Pass to it the name of a command "cmd" that when 
 * invoked will compile "testingcil.c" and run the result *)
let createFile () = 

  assertId := 0;
  nameId := 0;

  (* Start a new file *)
  globals := [];
  statements := [];

  (* Now make a main function *)
  main := emptyFunction "main";
  !main.svar.vtype <- TFun(intType, None, false, []);
  mainRetVal := makeGlobalVar "retval" intType;

  addGlobal (GVar(!mainRetVal, {init=None}, lu));
  addGlobal (GText("#include \"testcil.h\"\n"));
  addStatement (mkStmtOneInstr(Set(var !mainRetVal, zero, lu)));

  (* Add prototype for printf *)
  addGlobal (GVar(printfFun.svar, {init=None}, lu));
  addGlobal (GVar(memsetFun.svar, {init=None}, lu));

  (* now fill in the composites and the code of main. For simplicity we add 
   * the statements of main in reverse order *)

  testSizeOf ();


  (* Now add a return 0 at the end *)
  addStatement (mkStmt (Return(Some (Lval(var !mainRetVal)), lu)));
  
  
  (* Add main at the end *)
  addGlobal (GFun(!main, lu));
  !main.sbody.bstmts <- getStatements ();

  (* Now build the CIL.file *)
  let file = 
    { fileName = "testingcil.c";
      globals  = getGlobals ();
      globinit = None;
      globinitcalled = false;
    } 
  in
  (* Print the file *)
  let oc = open_out "testingcil.c" in
  dumpFile defaultCilPrinter oc "testingcil.c" file;
  close_out oc

  



(* initialization code for the tester *)
let randomStateFile = "testcil.random"  (* The name of a file where we store 
                                         * the state of the random number 
                                         * generator last time *)
let doit (command: string) = 
  while true do
    (* Initialize the random no generator *)
    begin
      try
        let randomFile = open_in randomStateFile in
        (* The file exists so restore the Random state *)
        Random.set_state (Marshal.from_channel randomFile);
        ignore (E.log "!! Restoring Random state from %s\n" randomStateFile);
        close_in randomFile;
        (* Leave the file there until we succeed *)
      with _ -> begin
        (* The file does not exist *)
        Random.self_init ();
        (* Save the state of the generator *)
        let randomFile = open_out randomStateFile in
        Marshal.to_channel randomFile (Random.get_state()) [] ;
        close_out randomFile;
      end
    end;
    createFile ();
    (* Now compile and run the file *)
    ignore (E.log "Running %s\n" command);
    let err = Sys.command command in
    if err <> 0 then
      E.s (E.bug "Failed to run the command: %s (errcode=%d)" command err)
    else begin
      ignore (E.log "Successfully ran one more round. Press CTRL-C to stop\n");
      (* Delete the file *)
      Sys.remove randomStateFile
    end
  done

