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

### Unsigned multiply-high

# X * Y = 2^64 XH.YH + 2^32 (XH.YL + XL.YH) + XL.YL

        .balign 16
        .globl __compcert_i64_umulh
__compcert_i64_umulh:
# r7:r8:r9 accumulate bits 127:32 of the full product
        mulhwu  r9, r4, r6        # r9 = high half of XL.YL
        mullw   r0, r4, r5        # r0 = low half of XL.YH
        addc    r9, r9, r0
        mulhwu  r0, r4, r5        # r0 = high half of XL.YH
        addze   r8, r0
        mullw   r0, r3, r6        # r0 = low half of XH.YL
        addc    r9, r9, r0
        mulhwu  r0, r3, r6        # r0 = high half of XH.YL
        adde    r8, r8, r0
        li      r7, 0
        addze   r7, r7
        mullw   r0, r3, r5        # r0 = low half of XH.YH
        addc    r4, r8, r0
        mulhwu  r0, r3, r5        # r0 = high half of XH.YH
        adde    r3, r7, r0
        blr
        .type __compcert_i64_umulh, @function
        .size __compcert_i64_umulh, .-__compcert_i64_umulh

