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

# Shift left
	
        .balign 16
        .globl __compcert_i64_shl
__compcert_i64_shl:
# On PowerPC, shift instructions with amount mod 64 >= 32 return 0
# hi = (hi << amount) | (lo >> (32 - amount)) | (lo << (amount - 32))
# lo = lo << amount
# if 0 <= amount < 32:
#    (amount - 32) mod 64 >= 32, hence lo << (amount - 32) == 0
# if 32 <= amount < 64:
#    lo << amount == 0
#    (32 - amount) mod 64 >= 32, hence lo >> (32 - amount) == 0
        andi. r5, r5, 63        # take amount modulo 64
        subfic r6, r5, 32       # r6 = 32 - amount
        addi r7, r5, -32        # r7 = amount - 32
        slw r3, r3, r5
        srw r0, r4, r6
        or r3, r3, r0
        slw r0, r4, r7
        or r3, r3, r0
        slw r4, r4, r5
        blr
        .type __compcert_i64_shl, @function
        .size __compcert_i64_shl, .-__compcert_i64_shl
        