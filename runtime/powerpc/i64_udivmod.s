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
# Output: quotient Q in (r7,r8),  remainder R in (r3,r4)
# Locals: mask M in (r9,r10)	
	
	.globl  __i64_udivmod
	.balign 16
__i64_udivmod:
   # Set up quotient and mask
        li r8, 0                # Q = 0
        li r7, 0
        li r10, 1               # M = 1
        li r9, 0
   # Check for zero divisor
        or. r0, r6, r5
        beqlr                   # return with unspecified quotient & remainder
   # Scale divisor and mask
1:      cmpwi r5, 0             # while top bit of D is zero...
        blt 2f
        subfc r0, r6, r4        # compute borrow out of N - D
        subfe r0, r5, r3
        subfe. r0, r0, r0       # EQ iff no borrow iff N >= D
        bne 2f                  # ... and while N >= D ...
        addc r6, r6, r6         # scale divisor: D = D << 1
        adde r5, r5, r5
        addc r10, r10, r10      # scale mask: M = M << 1
        adde r9, r9, r9
        b 1b                    # end while
   # Long division
2:      subfc r4, r6, r4        # Q = Q | M, N = N - D, and compute borrow
 	or r8, r8, r10
        subfe r3, r5, r3
        or r7, r7, r9
        subfe. r0, r0, r0       # test borrow
        beq 3f                  # no borrow: N >= D, continue
        addc r4, r4, r6         # borrow: undo what we just did to N and Q
        andc r8, r8, r10
        adde r3, r3, r5
        andc r7, r7, r9
3:      slwi r0, r9, 31         # unscale mask: M = M >> 1
        srwi r10, r10, 1
        or r10, r10, r0
        srwi r9, r9, 1
        slwi r0, r5, 31         # unscale divisor: D = D >> 1
        srwi r6, r6, 1
        or r6, r6, r0
        srwi r5, r5, 1
        or. r0, r10, r9         # iterate while M != 0
        bne 2b
        blr

        .type __i64_udivmod, @function
        .size __i64_udivmod, .-__i64_udivmod
