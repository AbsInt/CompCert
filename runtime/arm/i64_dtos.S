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

@@@ Conversion from double float to signed 64-bit integer
	
FUNCTION(__i64_dtos)
#ifndef VARIANT_eabi
	vmov r0, r1, d0
#endif	
        ASR r12, r1, #31       @ save sign of result in r12
  @ extract unbiased exponent ((HI & 0x7FF00000) >> 20) - (1023 + 52) in r2
  @ note: 1023 + 52 = 1075 = 1024 + 51
  @ note: (HI & 0x7FF00000) >> 20 = (HI << 1) >> 21
        LSL r2, r1, #1
        LSR r2, r2, #21
        SUB r2, r2, #51
        SUB r2, r2, #1024
  @ check range of exponent
        cmn r2, #52             @ if EXP < -52, |double| is < 1.0
        blt 1f
        cmp r2, #11             @ if EXP >= 63 - 52, |double| is >= 2^63
        bge 2f
  @ extract true mantissa
        BIC r1, r1, #0xFF000000
        BIC r1, r1, #0x00F00000 @ HI &= ~0xFFF00000
        ORR r1, r1, #0x00100000 @ HI |= 0x00100000
  @ shift it appropriately
        cmp r2, #0
        blt 3f
  @ EXP >= 0: shift left by EXP.  Note that EXP < 12        
        rsb r3, r2, #32         @ r3 = 32 - amount
        LSL r1, r1, r2
        LSR r3, r0, r3
        ORR r1, r1, r3
        LSL r0, r0, r2
	b 4f
  @ EXP < 0: shift right by -EXP.  Note that -EXP <= 52 but can be >= 32        
3:      RSB r2, r2, #0          @ r2 = -EXP = shift amount
        RSB r3, r2, #32         @ r3 = 32 - amount
        LSR r0, r0, r2
        LSL r3, r1, r3
        ORR r0, r0, r3
	SUB r3, r2, #32         @ r3 = amount - 32  (see i64_shr.s)
	LSR r3, r1, r3
	ORR r0, r0, r3
        LSR r1, r1, r2
  @ apply sign to result
4:      EOR r0, r0, r12
        EOR r1, r1, r12
        subs r0, r0, r12
        sbc r1, r1, r12
        bx lr
  @ special cases
1:      MOV r0, #0              @ result is 0
        MOV r1, #0
        bx lr
2:      cmp r12, #0
        blt 6f
        mvn r0, #0              @ result is 0x7F....FF (MAX_SINT)
        LSR r1, r0, #1
        bx lr
6:      MOV r0, #0              @ result is 0x80....00 (MIN_SINT)
        MOV r1, #0x80000000
        bx lr
ENDFUNCTION(__i64_dtos)
