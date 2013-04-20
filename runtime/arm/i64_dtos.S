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

@@@ Conversion from double float to signed 64-bit integer
	
	.global __i64_dtos
__i64_dtos:
        push {r4, lr}
        mov r4, r1, asr #31     @ save sign in r4
  @ extract unbiased exponent ((HI & 0x7FF00000) >> 20) - (1023 + 52) in r2
  @ note: 1023 + 52 = 1075 = 1024 + 51
  @ note: (HI & 0x7FF00000) >> 20 = (HI << 1) >> 21
        mov r2, r1, lsl #1
        mov r2, r2, lsr #21
        sub r2, r2, #51
        sub r2, r2, #1024
  @ check range of exponent
        cmn r2, #52             @ if EXP < -52, |double| is < 1.0
        blt 1f
        cmp r2, #11             @ if EXP >= 63 - 52, |double| is >= 2^63
        bge 2f
  @ extract true mantissa
        bic r1, r1, #0xFF000000
        bic r1, r1, #0x00F00000 @ HI &= ~0xFFF00000
        orr r1, r1, #0x00100000 @ HI |= 0x00100000
  @ shift it appropriately
        cmp r2, #0
        blt 3f
        bl __i64_shl            @ if EXP >= 0, shift left by EXP
        b 4f
3:      rsb r2, r2, #0
        bl __i64_shr            @ otherwise, shift right by -EXP
  @ apply sign to result
4:      eor r0, r0, r4
        eor r1, r1, r4
        subs r0, r0, r4
        sbc r1, r1, r4
        pop {r4, lr}
        bx lr
  @ special cases
1:      mov r0, #0 @ result is 0
        mov r1, #0
        pop {r4, lr}
        bx lr
2:      cmp r4, #0
        blt 6f
        mvn r0, #0              @ result is 0x7F....FF (MAX_SINT)
        mov r1, r0, lsr #1
        pop {r4, lr}
        bx lr
6:      mov r0, #0              @ result is 0x80....00 (MIN_SINT)
        mov r1, #0x80000000
        pop {r4, lr}
        bx lr
	.type __i64_dtos, %function
        .size __i64_dtos, . - __i64_dtos
