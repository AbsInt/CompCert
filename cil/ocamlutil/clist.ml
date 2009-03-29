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

open Pretty


(* We often need to concatenate sequences and using lists for this purpose is 
 * expensive. So we define a kind of "concatenable lists" that are easier to 
 * concatenate *)
type 'a clist = 
  | CList of 'a list             (* This is the only representation for empty 
                                  * *)
  | CConsL of 'a * 'a clist
  | CConsR of 'a clist * 'a 
  | CSeq  of 'a clist * 'a clist (* We concatenate only two of them at this 
                                  * time. Neither is CEmpty. To be sure 
                                  * always use append to make these  *)

let rec listifyOnto (tail: 'a list) = function
    CList l -> l @ tail
  | CConsL (x, l) -> x :: listifyOnto tail l
  | CConsR (l, x) -> listifyOnto (x :: tail) l
  | CSeq (l1, l2) -> listifyOnto (listifyOnto tail l2) l1
        
let toList l = listifyOnto [] l
let fromList l = CList l
    
    
let single x = CList [x]
let empty = CList []
    
let checkBeforeAppend  (l1: 'a clist) (l2: 'a clist) : bool =
  l1 != l2 || l1 = (CList [])

let append l1 l2 =
  if l1 = CList [] then l2 else
  if l2 = CList [] then l1 else
  begin
    if l1 == l2 then 
      raise (Failure "You should not use Clist.append to double a list");
    CSeq (l1, l2)
  end

let rec length (acc: int) = function
    CList l -> acc + (List.length l)
  | CConsL (x, l) -> length (acc + 1) l
  | CConsR (l, _) -> length (acc + 1) l
  | CSeq (l1, l2) -> length (length acc l1) l2
let length l = length 0 l  (* The external version *)
    
let map (f: 'a -> 'b) (l: 'a clist) : 'b clist = 
  let rec loop = function
      CList l -> CList (List.map f l)
    | CConsL (x, l) -> let x' = f x in CConsL (x', loop l)
    | CConsR (l, x) -> let l' = loop l in CConsR (l', f x)
    | CSeq (l1, l2) -> let l1' = loop l1 in CSeq (l1', loop l2)
  in
  loop l
    
  
let fold_left (f: 'acc -> 'a -> 'acc) (start: 'acc) (l: 'a clist) = 
  let rec loop (start: 'acc) = function
      CList l -> List.fold_left f start l
    | CConsL (x, l) -> loop (f start x) l
    | CConsR (l, x) -> let res = loop start l in f res x
    | CSeq (l1, l2) -> 
        let res1 = loop start l1 in
        loop res1 l2
  in
  loop start l
    
let iter (f: 'a -> unit) (l: 'a clist) : unit = 
  let rec loop = function
      CList l -> List.iter f l
    | CConsL (x, l) -> f x; loop l
    | CConsR (l, x) -> loop l; f x
    | CSeq (l1, l2) -> loop l1; loop l2
  in
  loop l
    
        
let rec rev (revelem: 'a -> 'a) = function
    CList l -> 
      let rec revonto (tail: 'a list) = function
          [] -> tail
        | x :: rest -> revonto (revelem x :: tail) rest
      in
      CList (revonto [] l)

  | CConsL (x, l) -> CConsR (rev revelem l, x)
  | CConsR (l, x) -> CConsL (x, rev revelem l)
  | CSeq (l1, l2) -> CSeq (rev revelem l2, rev revelem l1)


let docCList (sep: doc) (doone: 'a -> doc) () (dl: 'a clist) = 
  fold_left 
    (fun (acc: doc) (elem: 'a) -> 
      let elemd = doone elem in
      if acc == nil then elemd else acc ++ sep ++ elemd)
    nil
    dl

    
(* let debugCheck (lst: 'a clist) : unit =*)
(*   (* use a hashtable to store values encountered *)*)
(*   let tbl : 'a bool H.t = (H.create 13) in*)

(*   letrec recurse (node: 'a clist) =*)
(*     (* have we seen*)*)

(*     match node with*)
(*     | CList*)


(* --------------- testing ----------------- *)
type boxedInt =
  | BI of int
  | SomethingElse

let d_boxedInt () b =
  match b with
  | BI(i) -> (dprintf "%d" i)
  | SomethingElse -> (text "somethingElse")


(* sm: some simple tests of CLists 
let testCList () : unit =
begin
  (trace "sm" (dprintf "in testCList\n"));

  let clist1 = (fromList [BI(1); BI(2); BI(3)]) in
  (trace "sm" (dprintf "length of clist1 is %d\n"
                       (length clist1) ));

  let flattened = (toList clist1) in
  (trace "sm" (dprintf "flattened: %a\n"
                       (docList ~sep:(chr ',' ++ break) (d_boxedInt ()))
                       flattened));


end
1) in
  (trace "sm" (dprintf "flattened: %a\n"
                       (docList ~sep:(chr ',' ++ break) (d_boxedInt ()))
                       flattened));


end
*)
