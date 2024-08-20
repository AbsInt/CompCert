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

### Conversion from signed long to double float	

        .balign 16
        .globl __compcert_i64_stod
__compcert_i64_stod:
        addi r1, r1, -16
        lis r5, 0x4330
        li r6, 0
        stw r5, 0(r1)
        stw r4, 4(r1)           # 0(r1) = 2^52 + (double) XL
        stw r5, 8(r1)
        stw r6, 12(r1)          # 8(r1) = 2^52
        lfd f1, 0(r1)
        lfd f2, 8(r1)
        fsub f1, f1, f2         # f1 is XL (unsigned) as a double
        lis r5, 0x4530
        lis r6, 0x8000
        stw r5, 0(r1)           # 0(r1) = 2^84 + ((double)XH - 2^31) * 2^32
        add r3, r3, r6
        stw r3, 4(r1)
        stw r5, 8(r1)           # 8(r1) = 2^84 + 2^31 * 2^32
        stw r6, 12(r1)
        lfd f2, 0(r1)
        lfd f3, 8(r1)
        fsub f2, f2, f3         # f2 is XH (signed) * 2^32 as a double
        fadd f1, f1, f2         # add both to get result
        addi r1, r1, 16
        blr
        .type __compcert_i64_stod, @function
        .size __compcert_i64_stod, .-__compcert_i64_stod

