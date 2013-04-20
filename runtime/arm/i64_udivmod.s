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

@@@ Auxiliary function for division and modulus. Don't call from C

@ On entry:  N = (r0, r1) numerator    D = (r2, r3) divisor	
@ On exit:   Q = (r4, r5) quotient     R = (r0, r1) remainder	
@ Locals:    M = (r6, r7) mask         TMP = r8 temporary	
	
	.global __i64_udivmod
__i64_udivmod:
        orrs r8, r2, r3         @ is D == 0?
        bxeq lr                 @ if so, return with unspecified results
        mov r4, #0              @ Q = 0
        mov r5, #0
        mov r6, #1              @ M = 1
        mov r7, #0
1:      cmp r3, #0              @ while ((signed) D >= 0) ...
        blt 2f
        subs r8, r0, r2         @ ... and N >= D ...
        sbcs r8, r1, r3
        blo 2f
        adds r2, r2, r2         @ D = D << 1
        adc r3, r3, r3
        adds r6, r6, r6         @ M = M << 1
        adc r7, r7, r7
        b 1b
2:      subs r0, r0, r2         @ N = N - D
        sbcs r1, r1, r3
        orr r4, r4, r6          @ Q = Q | M
        orr r5, r5, r7
        bhs 3f                  @ if N was >= D, continue
        adds r0, r0, r2         @ otherwise, undo what we just did
        adc r1, r1, r3          @ N = N + D
        bic r4, r4, r6          @ Q = Q & ~M
        bic r5, r5, r7
3:      movs r7, r7, lsr #1     @ M = M >> 1
        mov r6, r6, rrx
        movs r3, r3, lsr #1     @ D = D >> 1
        mov r2, r2, rrx
        orrs r8, r6, r7         @ repeat while (M != 0) ...
        bne 2b
        bx lr
	.type __i64_udivmod, %function
	.size __i64_udivmod, . - __i64_udivmod
