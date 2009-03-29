(*
 *
 * Copyright (c) 2001 by
 *  George C. Necula	necula@cs.berkeley.edu
 *  Scott McPeak        smcpeak@cs.berkeley.edu
 *  Wes Weimer          weimer@cs.berkeley.edu
 *   
 * All rights reserved.  Permission to use, copy, modify and distribute
 * this software for research purposes only is hereby granted, 
 * provided that the following conditions are met: 
 * 1. Redistributions of source code must retain the above copyright notice, 
 * this list of conditions and the following disclaimer. 
 * 2. Redistributions in binary form must reproduce the above copyright notice, 
 * this list of conditions and the following disclaimer in the documentation 
 * and/or other materials provided with the distribution. 
 * 3. The name of the authors may not be used to endorse or promote products 
 * derived from  this software without specific prior written permission. 
 *
 * DISCLAIMER:
 * THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS OR 
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES 
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. 
 * IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY DIRECT, INDIRECT, 
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, 
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS 
 * OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON 
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT 
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF 
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)

(** Utilities for maintaining timing statistics *)

(** Resets all the timings. Invoke with "true" if you want to switch to using 
 * the hardware performance counters from now on. You get an exception if 
 * there are not performance counters available *)
val reset: bool -> unit
exception NoPerfCount

(** Check if we have performance counters *)
val has_performance_counters: unit -> bool
                           
(** Sample the current cycle count, in megacycles. *)
val sample_pentium_perfcount_20: unit -> int

(** Sample the current cycle count, in kilocycles. *)
val sample_pentium_perfcount_10: unit -> int

(** Time a function and associate the time with the given string. If some
    timing information is already associated with that string, then accumulate
    the times. If this function is invoked within another timed function then
    you can have a hierarchy of timings *)
val time : string -> ('a -> 'b) -> 'a -> 'b 

(** repeattime is like time but runs the function several times until the total
    running time is greater or equal to the first argument. The total time is
    then divided by the number of times the function was run. *)
val repeattime : float -> string -> ('a -> 'b) -> 'a -> 'b

(** Print the current stats preceeded by a message *)
val print : out_channel -> string -> unit



(** Time a function and set lastTime to the time it took *)
val lastTime: float ref
val timethis: ('a -> 'b) -> 'a -> 'b




