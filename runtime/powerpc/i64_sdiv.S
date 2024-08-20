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

### Signed division	
	
        .balign 16
        .globl __compcert_i64_sdiv
__compcert_i64_sdiv:
	mflr r0
        stw r0, 4(r1)           # save return address in caller's frame
        xor r0, r3, r5          # compute sign of result (top bit)
	mtctr r0                # save it in CTR (why not?)
        srawi r0, r3, 31        # take absolute value of N
        xor r4, r4, r0          # (i.e.  N = N ^ r0 - r0,
        xor r3, r3, r0          #  where r0 = 0 if N >= 0 and r0 = -1 if N < 0)
        subfc r4, r0, r4
        subfe r3, r0, r3
        srawi r0, r5, 31        # take absolute value of D
        xor r6, r6, r0          # (same trick)
        xor r5, r5, r0
        subfc r6, r0, r6
        subfe r5, r0, r5
        bl __compcert_i64_udivmod        # do unsigned division
        lwz r0, 4(r1)
        mtlr r0                 # restore return address
        mfctr r0
        srawi r0, r0, 31        # apply expected sign to quotient
        xor r6, r6, r0          # RES = Q if CTR >= 0, -Q if CTR < 0
        xor r5, r5, r0
        subfc r4, r0, r6
        subfe r3, r0, r5
        blr
        .type __compcert_i64_sdiv, @function
        .size __compcert_i64_sdiv, .-__compcert_i64_sdiv
	
        