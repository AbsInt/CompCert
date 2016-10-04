# *****************************************************************
#
#               The Compcert verified compiler
#
#           Xavier Leroy, INRIA Paris
#
# Copyright (c) 2016 Institut National de Recherche en Informatique et
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

# Unsigned multiply high
	
# Reference C implementation in ../c/i64_umul.c

        .balign 16
        .globl __i64_umulh
__i64_umulh:
     # u1 in r3; u0 in r4; v1 in r5; v0 in r6
        mulhwu   r0, r4, r6     # k (in r0) = high((u64) u0 * (u64) v0)
        mullw    r8, r3, r6
        mulhwu   r7, r3, r6     # t (in r8:r7) = (u64) u1 * (u64) v0
        addc     r0, r8, r0     # w1 (in r0) = low (t + k)
        addze    r9, r7         # w2 (in r9) = high (t + k)
        mullw    r8, r4, r5
        mulhwu   r7, r4, r5     # t (in r8:r7) = (u64) u0 * (u64) v1
        addc     r0, r8, r0     # tmp (in r0) = low (t + w1)
        addze    r0, r7         # k (in r0) = high(t + w1)
        mullw    r8, r3, r5
        mulhwu   r7, r3, r5     # t (in r8:r7) = (u64) u1 * (u64) v1
        addc     r4, r8, r9     # add w2
        addze    r3, r7
        addc     r4, r4, r0     # add k
        addze    r3, r3
        blr
        .type __i64_umulh, @function
        .size __i64_umulh, .-__i64_umulh
