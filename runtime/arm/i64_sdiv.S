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

@@@ Signed division

FUNCTION(__compcert_i64_sdiv)
        push {r4, r5, r6, r7, r8, r10, lr}
        ASR r4, Reg0HI, #31      @ r4 = sign of N
        ASR r5, Reg1HI, #31      @ r5 = sign of D
        EOR r10, r4, r5          @ r10 = sign of result
        EOR Reg0LO, Reg0LO, r4   @ take absolute value of N
        EOR Reg0HI, Reg0HI, r4   @ N = (N ^ (N >>s 31)) - (N >>s 31)
        subs Reg0LO, Reg0LO, r4
        sbc Reg0HI, Reg0HI, r4
        EOR Reg1LO, Reg1LO, r5   @ take absolute value of D
        EOR Reg1HI, Reg1HI, r5
        subs Reg1LO, Reg1LO, r5
        sbc Reg1HI, Reg1HI, r5
        bl __compcert_i64_udivmod         @ do unsigned division
        EOR Reg0LO, Reg2LO, r10  @ apply expected sign
        EOR Reg0HI, Reg2HI, r10
        subs Reg0LO, Reg0LO, r10
        sbc Reg0HI, Reg0HI, r10
        pop {r4, r5, r6, r7, r8, r10, lr}
        bx lr
ENDFUNCTION(__compcert_i64_sdiv)
