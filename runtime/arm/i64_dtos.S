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

FUNCTION(__compcert_i64_dtos)
#ifndef ABI_eabi
        vmov Reg0LO, Reg0HI, d0
#endif
        ASR r12, Reg0HI, #31     @ save sign of result in r12
  @ extract unbiased exponent ((HI & 0x7FF00000) >> 20) - (1023 + 52) in r2
  @ note: 1023 + 52 = 1075 = 1024 + 51
  @ note: (HI & 0x7FF00000) >> 20 = (HI << 1) >> 21
        LSL r2, Reg0HI, #1
        LSR r2, r2, #21
        SUB r2, r2, #51
        SUB r2, r2, #1024
  @ check range of exponent
        cmn r2, #52             @ if EXP < -52, |double| is < 1.0
        blt 1f
        cmp r2, #11             @ if EXP >= 63 - 52, |double| is >= 2^63
        bge 2f
  @ extract true mantissa
        BIC Reg0HI, Reg0HI, #0xFF000000
        BIC Reg0HI, Reg0HI, #0x00F00000 @ HI &= ~0xFFF00000
        ORR Reg0HI, Reg0HI, #0x00100000 @ HI |= 0x00100000
  @ shift it appropriately
        cmp r2, #0
        blt 3f
  @ EXP >= 0: shift left by EXP.  Note that EXP < 12
        rsb r3, r2, #32         @ r3 = 32 - amount
        LSL Reg0HI, Reg0HI, r2
        LSR r3, Reg0LO, r3
        ORR Reg0HI, Reg0HI, r3
        LSL Reg0LO, Reg0LO, r2
	b 4f
  @ EXP < 0: shift right by -EXP.  Note that -EXP <= 52 but can be >= 32
3:      RSB r2, r2, #0          @ r2 = -EXP = shift amount
        RSB r3, r2, #32         @ r3 = 32 - amount
        LSR Reg0LO, Reg0LO, r2
        LSL r3, Reg0HI, r3
        ORR Reg0LO, Reg0LO, r3
        SUB r3, r2, #32         @ r3 = amount - 32  (see i64_shr.s)
        LSR r3, Reg0HI, r3
        ORR Reg0LO, Reg0LO, r3
        LSR Reg0HI, Reg0HI, r2
  @ apply sign to result
4:      EOR Reg0LO, Reg0LO, r12
        EOR Reg0HI, Reg0HI, r12
        subs Reg0LO, Reg0LO, r12
        sbc Reg0HI, Reg0HI, r12
        bx lr
  @ special cases
1:      MOV Reg0LO, #0           @ result is 0
        MOV Reg0HI, #0
        bx lr
2:      cmp r12, #0
        blt 6f
        mvn Reg0LO, #0           @ result is 0x7F....FF (MAX_SINT)
        LSR Reg0HI, Reg0LO, #1
        bx lr
6:      MOV Reg0LO, #0           @ result is 0x80....00 (MIN_SINT)
        MOV Reg0HI, #0x80000000
        bx lr
ENDFUNCTION(__compcert_i64_dtos)
