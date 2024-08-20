# *****************************************************************
#
#               The Compcert verified compiler
#
#           Xavier Leroy, INRIA Paris-Rocquencourt
#
# Copyright (c) 2013 Institut National de Recherche en Informatique et
#  en Automatique.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#     * Redistributions of source code must retain the above copyright
#       notice, this list of conditions and the following disclaimer.
#     * Redistributions in binary form must reproduce the above copyright
#       notice, this list of conditions and the following disclaimer in the
#       documentation and/or other materials provided with the distribution.
#     * Neither the name of the <organization> nor the
#       names of its contributors may be used to endorse or promote products
#       derived from this software without specific prior written permission.
# 
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT
# HOLDER> BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
# EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
# PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
# PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
# LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
# NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
# *********************************************************************

# Helper functions for 64-bit integer arithmetic.  PowerPC version.

	.text
	
# Unsigned division and modulus

# This function computes both the quotient and the remainder of two
# unsigned 64-bit integers.

# Input:  numerator N in (r3,r4), divisor D in (r5,r6)
# Output: quotient Q in (r5,r6),  remainder R in (r3,r4)
# Destroys: all integer caller-save registers
	
	.globl  __compcert_i64_udivmod
	.balign 16
__compcert_i64_udivmod:
        cmplwi  r5, 0           # DH == 0 ?
	stwu    r1, -32(r1)
        mflr    r0
        stw     r0, 8(r1)
        stw     r31, 12(r1)
        beq     1f
# The general case	
        stw     r30, 16(r1)
        stw     r29, 20(r1)
        stw     r28, 24(r1)
        mr      r28, r3         # Save N in (r28, r29)
        mr      r29, r4
        mr      r30, r5         # Save D in (r30, r31)
        mr      r31, r6 
  # Scale N and D down, giving N' and D', such that 2^31 <= D' < 2^32
        cntlzw  r7, r5          # r7 = leading zeros in DH = 32 - shift amount
        subfic  r8, r7, 32      # r8 = shift amount
	slw     r0, r3, r7      # N' = N >> shift amount
        srw     r3, r3, r8
        srw     r4, r4, r8
        or      r4, r4, r0
	slw     r0, r5, r7      # D' = D >> shift amount
        srw     r6, r6, r8
        or      r5, r6, r0
  # Divide N' by D' to get an approximate quotient Q
        bl      __compcert_i64_udiv6432  # r3 = quotient, r4 = remainder
        mr      r6, r3          # low half of quotient Q
        li      r5, 0           # high half of quotient is 0
  # Tentative quotient is either correct or one too high
  # Compute Q * D in (r7, r8)
4:      mullw   r7, r6, r30     # r7 = Q * DH
        mullw   r8, r6, r31     # r8 = low 32 bits of Q * DL
        mulhwu  r0, r6, r31     # r0 = high 32 bits of Q * DL
        addc    r7, r7, r0
        subfe.  r0, r0, r0      # test carry: EQ iff carry
        beq     2f              # handle overflow case
   # Compute R = N - Q * D, with borrow
        subfc   r4, r8, r29
        subfe   r3, r7, r28
        subfe.  r0, r0, r0      # test borrow: EQ iff no borrow
        beq     3f              # no borrow: N >= Q * D, we are good
        addi    r6, r6, -1      # borrow: adjust Q down by 1
        addc    r4, r4, r31     # and R up by D
        adde    r3, r3, r30
   # Finished	
3:      lwz     r0, 8(r1)
        mtlr    r0
        lwz     r31, 12(r1)
        lwz     r30, 16(r1)
        lwz     r29, 20(r1)
        lwz     r28, 24(r1)
        addi    r1, r1, 32
        blr
   # Special case when Q * D overflows
2:      addi    r6, r6, -1      # adjust Q down by 1
        b       4b              # and redo computation and check of remainder
	.balign 16
# Special case 64 bits divided by 32 bits
1:      cmplwi  r3, 0           # NH == 0?
        beq     4f
        divwu   r31, r3, r6     # Divide NH by DL, quotient QH in r31
        mullw   r0, r31, r6
        subf    r3, r0, r3      # NH is remainder of this division
        mr      r5, r6
        bl      __compcert_i64_udiv6432  # divide NH : NL by DL
        mr      r5, r31         # high word of quotient
        mr      r6, r3          # low word of quotient
                                # r4 contains low word of remainder
        li      r3, 0           # high word of remainder = 0
	lwz     r0, 8(r1)
        mtlr    r0
        lwz     r31, 12(r1)
        addi    r1, r1, 32
        blr
	.balign 16
# Special case 32 bits divided by 32 bits
4:      mr      r0, r6
	divwu   r6, r4, r6      # low word of quotient
	li      r5, 0           # high word of quotient is 0
        mullw   r0, r6, r0
        subf    r4, r0, r4      # low word of remainder
        li      r3, 0           # high word of remainder is 0
        addi    r1, r1, 32
        blr
        
        .type __compcert_i64_udivmod, @function
        .size __compcert_i64_udivmod, .-__compcert_i64_udivmod

# Auxiliary division function: 64 bit integer divided by 32 bit integer	
# Not exported
# Input:  numerator N in (r3,r4), divisor D in r5
# Output: quotient Q in r3, remainder R in r4
# Destroys: all integer caller-save registers
# Assumes: high word of N is less than D	
        
	.balign 16
__compcert_i64_udiv6432: 
# Algorithm 9.3 from Hacker's Delight, section 9.4	
# Initially: u1 in r3, u0 in r4, v in r5
#   s = __builtin_clz(v);
	cntlzw  r6, r5          # s in r6
#   v = v << s;
        slw     r5, r5, r6
#   vn1 = v >> 16;              # vn1 in r7
        srwi    r7, r5, 16
#   vn0 = v & 0xFFFF;           # vn0 in r8
        rlwinm  r8, r5, 0, 16, 31
#   un32 = (u1 << s) | (u0 >> 32 - s);
	subfic  r0, r6, 32
        srw     r0, r4, r0
        slw     r3, r3, r6     # u1 dies, un32 in r3
        or      r3, r3, r0
#   un10 = u0 << s;
        slw     r4, r4, r6     # u0 dies, un10 in r4
#   un1 = un10 >> 16;
        srwi    r9, r4, 16     # un1 in r9
#   un0 = un10 & 0xFFFF;
        rlwinm  r4, r4, 0, 16, 31 # un10 dies, un0 in r4
#   q1 = un32/vn1;
        divwu   r10, r3, r7    # q in r10
#   rhat = un32 - q1*vn1;
        mullw   r0, r10, r7
        subf    r11, r0, r3    # rhat in r11
#  again1:
1:      
#   if (q1 >= b || q1*vn0 > b*rhat + un1) {
        cmplwi  r10, 0xFFFF
        bgt     2f
        mullw   r0, r10, r8
        slwi    r12, r11, 16
        add     r12, r12, r9
        cmplw   r0, r12
        ble     3f
2:      
#     q1 = q1 - 1;
        addi    r10, r10, -1
#     rhat = rhat + vn1;
        add     r11, r11, r7
#     if (rhat < b) goto again1;}
        cmplwi  r11, 0xFFFF
        ble     1b
3:      
#   un21 = un32*b + un1 - q1*v;
        slwi    r0, r3, 16     # un32 dies
        add     r9, r0, r9     # un1 dies
        mullw   r0, r10, r5
        subf    r9, r0, r9     # un21 in r9
#   q0 = un21/vn1;
	divwu   r3, r9, r7     # q0 in r3
#   rhat = un21 - q0*vn1;
        mullw   r0, r3, r7
        subf    r11, r0, r9    # rhat in r11
# again2:
4:      
#   if (q0 >= b || q0*vn0 > b*rhat + un0) {
        cmplwi  r3, 0xFFFF
        bgt     5f
        mullw   r0, r3, r8
        slwi    r12, r11, 16
        add     r12, r12, r4
        cmplw   r0, r12
        ble     6f
5:      
#     q0 = q0 - 1;
	addi    r3, r3, -1
#     rhat = rhat + vn1;
        add     r11, r11, r7
#     if (rhat < b) goto again2;}
	cmplwi  r11, 0xFFFF
        ble     4b
6:      
#   remainder = (un21*b + un0 - q0*v) >> s;
        slwi    r0, r9, 16
        add     r4, r0, r4  # un0 dies, remainder in r4
        mullw   r0, r3, r5
        subf    r4, r0, r4
        srw     r4, r4, r6
#   quotient = q1*b + q0;
        slwi    r0, r10, 16
        add     r3, r0, r3
        blr

	.type	__compcert_i64_udiv6432, @function
	.size	__compcert_i64_udiv6432,.-__compcert_i64_udiv6432
