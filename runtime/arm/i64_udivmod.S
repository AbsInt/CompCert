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

#include "sysdeps.h"

@@@ Auxiliary function for division and modulus. Don't call from C

@ On entry:  N = (r0, r1) numerator    D = (r2, r3) divisor
@ On exit:   Q = (r4, r5) quotient     R = (r0, r1) remainder
@ Locals:    COUNT = r6   round counter
@            TMP = r7, r8 temporary

FUNCTION(__compcert_i64_udivmod)
        orrs r7, Reg1LO, Reg1HI         @ is D == 0?
        it eq
        bxeq lr                         @ if so, return with unspecified results
        MOV Reg2LO, #0                  @ Q = 0
        MOV Reg2HI, #0
        MOV r6, #1                      @ round = 1
1:      cmp Reg1HI, #0                  @ while ((signed) D >= 0)
        blt 3f
        adds Reg1LO, Reg1LO, Reg1LO     @ D = D << 1
        adc Reg1HI, Reg1HI, Reg1HI
        subs r7, Reg0LO, Reg1LO         @ if N < D
        sbcs r8, Reg0HI, Reg1HI
        blo 2f                          @ break and restore D to previous value
        ADD r6, r6, #1                  @ increment count
        b 1b
2:      lsrs Reg1HI, Reg1HI, #1         @ D = D >> 1
        rrx Reg1LO, Reg1LO
3:      adds Reg2LO, Reg2LO, Reg2LO     @ Q = Q << 1
        adc Reg2HI, Reg2HI, Reg2HI
        subs r7, Reg0LO, Reg1LO         @ TMP = N - D
        sbcs r8, Reg0HI, Reg1HI
        blo 4f                          @ if N < D, leave N and Q unchanged
	MOV Reg0LO, r7                  @ N = N - D
        MOV Reg0HI, r8
        orr Reg2LO, Reg2LO, #1          @ Q = Q | 1
4:      subs r6, r6, #1                 @ decrement count
        bne 2b                          @ repeat until count = 0
        bx lr
ENDFUNCTION(__compcert_i64_udivmod)
