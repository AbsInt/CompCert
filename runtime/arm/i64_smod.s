@ *****************************************************************
@
@               The Compcert verified compiler
@
@           Xavier Leroy, INRIA Paris-Rocquencourt
@
@ Copyright (c) 2013 Institut National de Recherche en Informatique et
@  en Automatique.
@
@ Redistribution and use in source and binary forms, with or without
@ modification, are permitted provided that the following conditions are met:
@     * Redistributions of source code must retain the above copyright
@       notice, this list of conditions and the following disclaimer.
@     * Redistributions in binary form must reproduce the above copyright
@       notice, this list of conditions and the following disclaimer in the
@       documentation and/or other materials provided with the distribution.
@     * Neither the name of the <organization> nor the
@       names of its contributors may be used to endorse or promote products
@       derived from this software without specific prior written permission.
@ 
@ THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
@ "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
@ LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
@ A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT
@ HOLDER> BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
@ EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
@ PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
@ PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
@ LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
@ NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
@ SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
@
@ *********************************************************************

@ Helper functions for 64-bit integer arithmetic.  ARM version.

        .text

@@@ Signed modulus	

	.global __i64_smod
__i64_smod:
        push {r4, r5, r6, r7, r8, r10, lr}
	mov r10, r1              @ r10 = sign of result
        mov r4, r1, asr#31       @ take absolute value of N
        eor r0, r0, r4           @ N = (N ^ (N >>s 31)) - (N >>s 31)
        eor r1, r1, r4
        subs r0, r0, r4
        sbc r1, r1, r4
        mov r4, r3, asr #31      @ take absolute value of D
        eor r2, r2, r4
        eor r3, r3, r4
        subs r2, r2, r4
        sbc r3, r3, r4
        bl __i64_udivmod         @ do unsigned division
        eor r0, r0, r10, asr#31  @ apply expected sign
        eor r1, r1, r10, asr#31
        subs r0, r0, r10, asr#31
        sbc r1, r1, r10, asr#31
        pop {r4, r5, r6, r7, r8, r10, lr}
        bx lr
	.type __i64_smod, %function
	.size __i64_smod, . - __i64_smod
	
