module H = Hashtbl
module E = Errormsg
open Pretty

let debugAlpha (prefix: string) = false
(*** Alpha conversion ***)
let alphaSeparator = "___"
let alphaSeparatorLen = String.length alphaSeparator

(** For each prefix we remember the next integer suffix to use and the list 
 * of suffixes, each with some data assciated with the newAlphaName that 
 * created the suffix. *)
type 'a alphaTableData = int * (string * 'a) list

type 'a undoAlphaElement = 
    AlphaChangedSuffix of 'a alphaTableData ref * 'a alphaTableData (* The 
                                             * reference that was changed and 
                                             * the old suffix *)
  | AlphaAddedSuffix of string          (* We added this new entry to the 
                                         * table *)

(* Create a new name based on a given name. The new name is formed from a 
 * prefix (obtained from the given name by stripping a suffix consisting of 
 * the alphaSeparator followed by only digits), followed by alphaSeparator 
 * and then by a positive integer suffix. The first argument is a table 
 * mapping name prefixes to the largest suffix used so far for that 
 * prefix. The largest suffix is one when only the version without suffix has 
 * been used. *)
let rec newAlphaName ~(alphaTable: (string, 'a alphaTableData ref) H.t)
                     ~(undolist: 'a undoAlphaElement list ref option)
                     ~(lookupname: string) 
                     ~(data: 'a) : string * 'a = 
  alphaWorker ~alphaTable:alphaTable ~undolist:undolist 
              ~lookupname:lookupname ~data:data true
  

(** Just register the name so that we will not use in the future *)
and registerAlphaName ~(alphaTable: (string, 'a alphaTableData ref) H.t)
                      ~(undolist: 'a undoAlphaElement list ref option)
                      ~(lookupname: string) 
                      ~(data: 'a) : unit = 
  ignore (alphaWorker ~alphaTable:alphaTable ~undolist:undolist 
                      ~lookupname:lookupname ~data:data false)


and alphaWorker      ~(alphaTable: (string, 'a alphaTableData ref) H.t)
                     ~(undolist: 'a undoAlphaElement list ref option)
                     ~(lookupname: string) ~(data:'a)
                     (make_new: bool) : string * 'a = 
  let prefix, suffix, (numsuffix: int) = splitNameForAlpha ~lookupname in
  if debugAlpha prefix then
    ignore (E.log "Alpha worker: prefix=%s suffix=%s (%d) create=%b. " 
              prefix suffix numsuffix make_new);
  let newname, (olddata: 'a) = 
    try
      let rc = H.find alphaTable prefix in
      let max, suffixes = !rc in 
      (* We have seen this prefix *)
      if debugAlpha prefix then
        ignore (E.log " Old max %d. Old suffixes: @[%a@]" max
                  (docList 
                     (fun (s, l) -> dprintf "%s" (* d_loc l *) s)) suffixes);
      (* Save the undo info *)
      (match undolist with 
        Some l -> l := AlphaChangedSuffix (rc, !rc) :: !l
      | _ -> ());

      let newmax, newsuffix, (olddata: 'a), newsuffixes = 
        if numsuffix > max then begin 
          (* Clearly we have not seen it *)
          numsuffix, suffix, data,
          (suffix, data) :: suffixes 
        end else begin 
          match List.filter (fun (n, _) -> n = suffix) suffixes with 
            [] -> (* Not found *)
              max, suffix, data, (suffix, data) :: suffixes
          | [(_, l) ] -> 
              (* We have seen this exact suffix before *)
              if make_new then 
                let newsuffix = alphaSeparator ^ (string_of_int (max + 1)) in
                max + 1, newsuffix, l, (newsuffix, data) :: suffixes
              else
                max, suffix, data, suffixes
          |  _ -> E.s (E.bug "Cil.alphaWorker")
        end
      in
      rc := (newmax, newsuffixes);
      prefix ^ newsuffix, olddata
    with Not_found -> begin (* First variable with this prefix *)
      (match undolist with 
        Some l -> l := AlphaAddedSuffix prefix :: !l
      | _ -> ());
      H.add alphaTable prefix (ref (numsuffix, [ (suffix, data) ]));
      if debugAlpha prefix then ignore (E.log " First seen. ");
      lookupname, data  (* Return the original name *)
    end
  in
  if debugAlpha prefix then
    ignore (E.log " Res=: %s \n" newname (* d_loc oldloc *));
  newname, olddata

(* Strip the suffix. Return the prefix, the suffix (including the separator 
 * and the numeric value, possibly empty), and the 
 * numeric value of the suffix (possibly -1 if missing) *) 
and splitNameForAlpha ~(lookupname: string) : (string * string * int) = 
  let len = String.length lookupname in
  (* Search backward for the numeric suffix. Return the first digit of the 
   * suffix. Returns len if no numeric suffix *)
  let rec skipSuffix (i: int) = 
    if i = -1 then -1 else 
    let c = Char.code (String.get lookupname i) - Char.code '0' in
    if c >= 0 && c <= 9 then 
      skipSuffix (i - 1)
    else (i + 1)
  in
  let startSuffix = skipSuffix (len - 1) in

  if startSuffix >= len (* No digits at all at the end *) ||
     startSuffix <= alphaSeparatorLen     (* Not enough room for a prefix and 
                                           * the separator before suffix *) ||
     (* Suffix starts with a 0 and has more characters after that *) 
     (startSuffix < len - 1 && String.get lookupname startSuffix = '0')  ||
     alphaSeparator <> String.sub lookupname 
                                 (startSuffix - alphaSeparatorLen)  
                                 alphaSeparatorLen 
  then
    (lookupname, "", -1)  (* No valid suffix in the name *)
  else
    (String.sub lookupname 0 (startSuffix - alphaSeparatorLen), 
     String.sub lookupname (startSuffix - alphaSeparatorLen) 
                           (len - startSuffix + alphaSeparatorLen),
     int_of_string (String.sub lookupname startSuffix (len - startSuffix)))
    

let getAlphaPrefix ~(lookupname:string) : string = 
  let p, _, _ = splitNameForAlpha ~lookupname:lookupname in
  p
      
(* Undoes the changes as specified by the undolist *)
let undoAlphaChanges ~(alphaTable: (string, 'a alphaTableData ref) H.t) 
                     ~(undolist: 'a undoAlphaElement list) = 
  List.iter
    (function 
        AlphaChangedSuffix (where, old) -> 
          where := old
      | AlphaAddedSuffix name -> 
          if debugAlpha name then 
            ignore (E.log "Removing %s from alpha table\n" name);
          H.remove alphaTable name)
    undolist

let docAlphaTable () (alphaTable: (string, 'a alphaTableData ref) H.t) = 
  let acc : (string * (int * (string * 'a) list)) list ref = ref [] in
  H.iter (fun k d -> acc := (k, !d) :: !acc) alphaTable;
  docList ~sep:line (fun (k, (d, _)) -> dprintf "  %s -> %d" k d) () !acc

