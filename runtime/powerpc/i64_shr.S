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

# Shift right unsigned
	
        .balign 16
        .globl __compcert_i64_shr
__compcert_i64_shr:
# On PowerPC, shift instructions with amount mod 64 >= 32 return 0
# lo = (lo >> amount) | (hi << (32 - amount)) | (hi >> (amount - 32))
# hi = hi >> amount
# if 0 <= amount < 32:
#    (amount - 32) mod 64 >= 32, hence hi >> (amount - 32) == 0
# if 32 <= amount < 64:
#    hi >> amount == 0
#    (32 - amount) mod 64 >= 32, hence hi << (32 - amount) == 0
        andi. r5, r5, 63        # take amount modulo 64
        subfic r6, r5, 32       # r6 = 32 - amount
        addi r7, r5, -32        # r7 = amount - 32
        srw r4, r4, r5
        slw r0, r3, r6
        or r4, r4, r0
        srw r0, r3, r7
        or r4, r4, r0
        srw r3, r3, r5
        blr
        .type __compcert_i64_shr, @function
        .size __compcert_i64_shr, .-__compcert_i64_shr
	
        