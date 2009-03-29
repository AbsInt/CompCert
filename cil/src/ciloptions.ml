(*
 *
 * Copyright (c) 2001-2003,
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 *  Ben Liblit          <liblit@cs.berkeley.edu>
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


module E = Errormsg

let setDebugFlag v name = 
  E.debugFlag := v;
  if v then Pretty.flushOften := true

type outfile = 
    { fname: string;
      fchan: out_channel } 

let setTraceDepth n =
  Pretty.printDepth := n


      (* Processign of output file arguments *)
let openFile (what: string) (takeit: outfile -> unit) (fl: string) = 
  if !E.verboseFlag then
    ignore (Printf.printf "Setting %s to %s\n" what fl);
  (try takeit { fname = fl;
                fchan = open_out fl }
  with _ ->
    raise (Arg.Bad ("Cannot open " ^ what ^ " file " ^ fl)))


let fileNames : string list ref = ref []
let recordFile fname = 
  fileNames := fname :: (!fileNames) 

                         (* Parsing of files with additional names *)
let parseExtraFile (s: string) = 
  try
    let sfile = open_in s in
    while true do
      let line = try input_line sfile with e -> (close_in sfile; raise e) in
      let linelen = String.length line in
      let rec scan (pos: int) (* next char to look at *)
          (start: int) : unit (* start of the word, 
                                 or -1 if none *) =
        if pos >= linelen then 
          if start >= 0 then 
            recordFile (String.sub line start (pos - start))
          else 
            () (* Just move on to the next line *)
        else
          let c = String.get line pos in
          match c with 
            ' ' | '\n' | '\r' | '\t' -> 
              (* whitespace *)
              if start >= 0 then begin
                recordFile (String.sub line start (pos - start));
              end;
              scan (pos + 1) (-1)
                
          | _ -> (* non-whitespace *)
              if start >= 0 then 
                scan (pos + 1) start 
              else
                scan (pos + 1) pos
      in
        scan 0 (-1)
    done
  with Sys_error _ -> E.s (E.error "Cannot find extra file: %s\n" s)
  |  End_of_file -> () 


let options : (string * Arg.spec * string) list = 
  [ 
    (* General Options *) 
    "", Arg.Unit (fun () -> ()), "\n\t\tGeneral Options\n" ; 

    "--version", Arg.Unit 
              (fun _ -> print_endline ("CIL version " ^ Cil.cilVersion ^
                       "\nMore information at http://cil.sourceforge.net/\n");
                 exit 0),
           "output version information and exit";
    "--verbose", Arg.Unit (fun _ -> E.verboseFlag := true),
                "Print lots of random stuff. This is passed on from cilly.";
    "--warnall", Arg.Unit (fun _ -> E.warnFlag := true), "Show all warnings";
    "--debug", Arg.String (setDebugFlag true),
                     "<xxx> turns on debugging flag xxx";
    "--nodebug", Arg.String (setDebugFlag false), 
                     "<xxx> turns off debugging flag xxx";

    "--flush", Arg.Unit (fun _ -> Pretty.flushOften := true),
                     "Flush the output streams often (aids debugging)" ;
    "--check", Arg.Unit (fun _ -> Cilutil.doCheck := true),
                     "Run a consistency check over the CIL after every operation.";
    "--nocheck", Arg.Unit (fun _ -> Cilutil.doCheck := false),
                     "turns off consistency checking of CIL";
    "--noPrintLn", Arg.Unit (fun _ -> Cil.lineDirectiveStyle := None;
                                     Cprint.printLn := false),
               "Don't output #line directives in the output.";
    "--commPrintLn", Arg.Unit (fun _ -> Cil.lineDirectiveStyle := Some Cil.LineComment;
                                       Cprint.printLnComment := true),
               "Print #line directives in the output, but put them in comments.";
    "--stats", Arg.Unit (fun _ -> Cilutil.printStats := true),
               "Print statistics about running times and memory usage.";


    "--log", Arg.String (openFile "log" (fun oc -> E.logChannel := oc.fchan)),
             "Set the name of the log file.  By default stderr is used";

    "--MSVC", Arg.Unit (fun _ ->   Cil.msvcMode := true;
                                   Frontc.setMSVCMode ();
                                   if not Machdep.hasMSVC then
                                     ignore (E.warn "Will work in MSVC mode but will be using machine-dependent parameters for GCC since you do not have the MSVC compiler installed\n")
                       ), "Enable MSVC compatibility. Default is GNU.";

    "--testcil", Arg.String (fun s -> Cilutil.testcil := s),
          "test CIL using the given compiler";

    "--ignore-merge-conflicts", 
                 Arg.Unit (fun _ -> Mergecil.ignore_merge_conflicts := true),
                  "ignore merging conflicts";
    "--sliceGlobal", Arg.Unit (fun _ -> Cilutil.sliceGlobal := true),
               "output is the slice of #pragma cilnoremove(sym) symbols";

    (* sm: some more debugging options *)
    "--tr",         Arg.String Trace.traceAddMulti,
                     "<sys>: subsystem to show debug printfs for";
    "--pdepth",     Arg.Int setTraceDepth,
                      "<n>: set max print depth (default: 5)";

    "--extrafiles", Arg.String parseExtraFile,
    "<filename>: the name of a file that contains a list of additional files to process, separated by whitespace of newlines";

    (* Lowering Options *) 
    "", Arg.Unit (fun () -> ()), "\n\t\tLowering Options\n" ; 

    "--noLowerConstants", Arg.Unit (fun _ -> Cil.lowerConstants := false), 
     "do not lower constant expressions";

    "--noInsertImplicitCasts", Arg.Unit (fun _ -> Cil.insertImplicitCasts := false),
    "do not insert implicit casts";

    "--forceRLArgEval", 
          Arg.Unit (fun n -> Cabs2cil.forceRLArgEval := true),
          "Forces right to left evaluation of function arguments";
    "--nocil", Arg.Int (fun n -> Cabs2cil.nocil := n),
                      "Do not compile to CIL the global with the given index";
    "--disallowDuplication", Arg.Unit (fun n -> Cabs2cil.allowDuplication := false),
                      "Prevent small chunks of code from being duplicated";
    "--keepunused", Arg.Set Rmtmps.keepUnused,
                "Do not remove the unused variables and types";
    "--rmUnusedInlines", Arg.Set Rmtmps.rmUnusedInlines,
                "Delete any unused inline functions.  This is the default in MSVC mode";



    "", Arg.Unit (fun () -> ()), "\n\t\tOutput Options\n" ; 
    "--printCilAsIs", Arg.Unit (fun _ -> Cil.printCilAsIs := true),
               "do not try to simplify the CIL when printing.  Without this flag, CIL will attempt to produce prettier output by e.g. changing while(1) into more meaningful loops.";
    "--noWrap", Arg.Unit (fun _ -> Cil.lineLength := 100000),
               "do not wrap long lines when printing";

  ]
    
