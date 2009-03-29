(* See copyright notice at the end of the file *)

(* The type of a heap (priority queue): keys are integers, data values
 * are whatever you like *)
type ('a) t = {
          elements  : (int * ('a option)) array ;
  mutable size      : int ; (* current number of elements *)
          capacity  : int ; (* max number of elements *)
} 

let create size = {
  elements = Array.create (size+1) (max_int,None) ;
  size = 0 ;
  capacity = size ; 
} 

let clear heap = heap.size <- 0  

let is_full heap = (heap.size = heap.capacity) 

let is_empty heap = (heap.size = 0) 

let insert heap prio elt = begin
  if is_full heap then begin
    raise (Invalid_argument "Heap.insert")
  end ; 
  heap.size <- heap.size + 1 ;
  let i = ref heap.size in
  while ( fst heap.elements.(!i / 2) < prio ) do
    heap.elements.(!i) <- heap.elements.(!i / 2) ;
    i := (!i / 2)
  done ;
  heap.elements.(!i) <- (prio,Some(elt))
  end

let examine_max heap = 
  if is_empty heap then begin
    raise (Invalid_argument "Heap.examine_max")
  end ; 
  match heap.elements.(1) with
    p,Some(elt) -> p,elt
  | p,None -> failwith "Heap.examine_max" 

let extract_max heap = begin
  if is_empty heap then begin
    raise (Invalid_argument "Heap.extract_max")
  end ; 
  let max = heap.elements.(1) in
  let last = heap.elements.(heap.size) in
  heap.size <- heap.size - 1 ; 
  let i = ref 1 in
  let break = ref false in 
  while (!i * 2 <= heap.size) && not !break do
    let child = ref (!i * 2) in

    (* find smaller child *)
    if (!child <> heap.size && 
        fst heap.elements.(!child+1) > fst heap.elements.(!child)) then begin
        incr child 
    end ; 

    (* percolate one level *) 
    if (fst last < fst heap.elements.(!child)) then begin
      heap.elements.(!i) <- heap.elements.(!child) ; 
      i := !child 
    end else begin
      break := true 
    end
  done ; 
  heap.elements.(!i) <- last ;
  match max with 
    p,Some(elt) -> p,elt
  | p,None -> failwith "Heap.examine_min" 
  end


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
