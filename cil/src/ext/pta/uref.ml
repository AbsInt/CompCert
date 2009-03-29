(*
 *
 * Copyright (c) 2001-2002, 
 *  John Kodumal        <jkodumal@eecs.berkeley.edu>
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
exception Bad_find

type 'a urefC =
    Ecr of 'a * int
  | Link of 'a uref
and 'a uref = 'a urefC ref

let rec find p = 
  match !p with
    | Ecr _ -> p
    | Link p' ->
	let p'' = find p' 
	in p := Link p''; p''

let uref x = ref (Ecr(x,0))

let equal (p,p') = (find p == find p')

let deref p = 
  match ! (find p) with 
    | Ecr (x,_) -> x
    | _ -> raise Bad_find

let update (p,x) = 
  let p' = find p 
  in
    match !p' with
      | Ecr (_,rank) -> p' := Ecr(x,rank)
      | _ -> raise Bad_find
	  
let unify f (p,q) = 
  let p',q' = find p, find q in
    match (!p',!q') with 
      | (Ecr(px,pr),Ecr(qx,qr)) ->
	let x = f(px,qx) in
	  if (p' == q') then
	    p' := Ecr(x,pr)
	  else if pr == qr then
	    (q' := Ecr(x,qr+1); p' := Link q')
	  else if pr < qr then
	    (q' := Ecr(x,qr); p' := Link q')
	  else (* pr > qr *)
	    (p' := Ecr(x,pr); q' := Link p')
      | _ -> raise Bad_find
	  
let union (p,q) = 
  let p',q' = find p, find q in
    match (!p',!q') with 
      | (Ecr(px,pr),Ecr(qx,qr)) ->
	  if (p' == q') then 
	    ()
	  else if pr == qr then
	    (q' := Ecr(qx, qr+1); p' := Link q')
	  else if pr < qr then
	    p' := Link q'
	  else (* pr > qr *)
	    q' := Link p'
      | _ -> raise Bad_find
	  

