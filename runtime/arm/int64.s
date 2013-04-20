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

@ Calling conventions for R = F(X) or R = F(X,Y):
@   one or two long arguments:   XL in r0, XH in r1, YL in r2, YH in r3
@   one long argument, one int:  XL in r0, XH in r1, Y in r2
@   one float argument:          X in r0, r1
@   one long result:             RL in r0, RH in r1
@   one float result:            R in r0, r1
@ This is a little-endian convention: the low word is in the
@ low-numbered register.
@ Can use r0...r3 and f0...f7 as temporary registers (caller-save)	
	
	.text
        
@@@ Unsigned comparison	
	
	.global __i64_ucmp
__i64_ucmp:
        cmp r1, r3      @ compare high words
        cmpeq r0, r2    @ if equal, compare low words instead
        moveq r0, #0    @ res = 0 if eq
        movhi r0, #1    @ res = 1 if unsigned higher
        mvnlo r0, #0    @ res = -1 if unsigned lower
        bx lr
	.type __i64_ucmp, %function
	.size __i64_ucmp, . - __i64_ucmp
	
@@@ Signed comparison	
	
	.global __i64_scmp
__i64_scmp:
        cmp r0, r2              @ compare low words (unsigned)
        moveq r0, #0            @ res = 0 if eq
        movhi r0, #1            @ res = 1 if unsigned higher
        mvnlo r0, #0            @ res = -1 if unsigned lower
        cmp r1, r3              @ compare high words (signed)
	addgt r0, r0, #2        @ res += 2 if signed greater
	sublt r0, r0, #2        @ res -= 2 if signed less
   @ here, r0 = 0 if X == Y
   @       r0 = -3, -2, -1 if X < Y
   @       r0 = 1, 2, 3 if X > Y
        bx      lr
	.type __i64_scmp, %function
	.size __i64_scmp, . - __i64_scmp
	
@ Note on ARM shifts: the shift amount is taken modulo 256.
@ Therefore, unsigned shifts by 32 bits or more produce 0.        
	
@@@ Shift left	

	.global __i64_shl
__i64_shl:
        and r2, r2, #63         @ normalize amount to 0...63
        rsbs r3, r2, #32        @ r3 = 32 - amount
        ble 1f                  @ branch if <= 0, namely if amount >= 32
        mov r1, r1, lsl r2
        orr r1, r0, lsr r3
        mov r0, r0, lsl r2
        bx lr
1:
        sub r2, r2, #32
        mov r1, r0, lsl r2
        mov r0, #0
        bx lr
	.type __i64_shl, %function
	.size __i64_shl, . - __i64_shl

@@@ Shift right unsigned	

	.global __i64_shr
__i64_shr:
        and r2, r2, #63         @ normalize amount to 0...63
        rsbs r3, r2, #32        @ r3 = 32 - amount
        ble 1f                  @ branch if <= 0, namely if amount >= 32
        mov r0, r0, lsr r2
        orr r0, r1, lsl r3
        mov r1, r1, lsr r2
        bx lr
1:
        sub r2, r2, #32
        mov r0, r1, lsr r2
        mov r1, #0
        bx lr
	.type __i64_shr, %function
	.size __i64_shr, . - __i64_shr
	
@@@ Shift right signed

	.global __i64_sar
__i64_sar:
        and r2, r2, #63         @ normalize amount to 0...63
        rsbs r3, r2, #32        @ r3 = 32 - amount
        ble 1f                  @ branch if <= 0, namely if amount >= 32
        mov r0, r0, lsr r2
        orr r0, r1, lsl r3
        mov r1, r1, asr r2
        bx lr
1:
        sub r2, r2, #32
        mov r0, r1, asr r2
        mov r1, r1, asr #31
        bx lr
	.type __i64_sar, %function
	.size __i64_sar, . - __i64_sar
	
@@@ Auxiliary function for division and modulus. Not exported.

@ On entry:  N = (r0, r1) numerator    D = (r2, r3) divisor	
@ On exit:   Q = (r4, r5) quotient     R = (r0, r1) remainder	
@ Locals:    M = (r6, r7) mask         TMP = r8 temporary	
	
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
	
@@@ Unsigned division	
	
	.global __i64_udiv
__i64_udiv:
        push {r4, r5, r6, r7, r8, lr}
        bl __i64_udivmod
        mov r0, r4
        mov r1, r5
        pop {r4, r5, r6, r7, r8, lr}
        bx lr
	.type __i64_udiv, %function
	.size __i64_udiv, . - __i64_udiv
	
@@@ Unsigned modulus	
	
	.global __i64_umod
__i64_umod:
        push {r4, r5, r6, r7, r8, lr}
        bl __i64_udivmod         @ remainder is already in r0,r1
        pop {r4, r5, r6, r7, r8, lr}
        bx lr
	.type __i64_umod, %function
	.size __i64_umod, . - __i64_umod
	
@@@ Signed division	
	
	.global __i64_sdiv
__i64_sdiv:
        push {r4, r5, r6, r7, r8, r10, lr}
        eor r10, r1, r3          @ r10 = sign of result
        mov r4, r1, asr #31      @ take absolute value of N
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
        mov r0, r4
        mov r1, r5
        eor r0, r0, r10, asr#31  @ apply expected sign
        eor r1, r1, r10, asr#31
        subs r0, r0, r10, asr#31
        sbc r1, r1, r10, asr#31
        pop {r4, r5, r6, r7, r8, r10, lr}
        bx lr
	.type __i64_sdiv, %function
	.size __i64_sdiv, . - __i64_sdiv
	
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
	
@@@ Conversion from unsigned 64-bit integer to double float
	
	.global __i64_utod
__i64_utod:
        fmsr s0, r0
        fuitod d0, s0           @ convert low half to double (unsigned)
        fmsr s2, r1
        fuitod d1, s2           @ convert high half to double (unsigned)
        fldd d2, .LC1           @ d2 = 2^32
        fmacd d0, d1, d2        @ d0 = d0 + d1 * d2 = double value of int64
	fmrrd r0, r1, d0        @ return result in r0, r1
        bx lr
	.type __i64_utod, %function
	.size __i64_utod, . - __i64_utod
	
        .balign 8
.LC1:   .quad 0x41f0000000000000 @ 2^32 in double precision
	
@@@ Conversion from signed 64-bit integer to double float
	
	.global __i64_stod
__i64_stod:
        fmsr s0, r0
        fuitod d0, s0           @ convert low half to double (unsigned)
        fmsr s2, r1
        fsitod d1, s2           @ convert high half to double (signed)
        fldd d2, .LC1           @ d2 = 2^32
        fmacd d0, d1, d2        @ d0 = d0 + d1 * d2 = double value of int64
	fmrrd r0, r1, d0        @ return result in r0, r1
        bx lr
	.type __i64_stod, %function
	.size __i64_stod, . - __i64_stod

@@@ Conversion from double float to unsigned 64-bit integer	

	.global __i64_dtou
__i64_dtou:
        cmp r1, #0              @ is double < 0 ?
        blt 1f                  @ then it converts to 0
  @ extract unbiased exponent ((HI & 0x7FF00000) >> 20) - (1023 + 52) in r2
  @ note: 1023 + 52 = 1075 = 1024 + 51
  @ note: (HI & 0x7FF00000) >> 20 = (HI << 1) >> 21
        mov r2, r1, lsl #1
        mov r2, r2, lsr #21
        sub r2, r2, #51
        sub r2, r2, #1024
  @ check range of exponent
        cmn r2, #52             @ if EXP < -52, double is < 1.0
        blt 1f
        cmp r2, #12             @ if EXP >= 64 - 52, double is >= 2^64
        bge 2f
  @ extract true mantissa
        bic r1, r1, #0xFF000000
        bic r1, r1, #0x00F00000 @ HI &= ~0xFFF00000
        orr r1, r1, #0x00100000 @ HI |= 0x00100000
  @ shift it appropriately
        cmp r2, #0
        bge __i64_shl           @ if EXP >= 0, shift left by EXP
        rsb r2, r2, #0
        b __i64_shr             @ otherwise, shift right by -EXP
  @ special cases
1:      mov r0, #0              @ result is 0
        mov r1, #0
        bx lr
2:      mvn r0, #0              @ result is 0xFF....FF (MAX_UINT)
        mvn r1, #0
        bx lr
	.type __i64_dtou, %function
        .size __i64_dtou, . - __i64_dtou
	
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

