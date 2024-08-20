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

# Helper functions for 64-bit integer arithmetic.  PowerPC 64 version.

        .text

### Conversion from double float to unsigned long	

        .balign 16
        .globl __compcert_i64_dtou
__compcert_i64_dtou:
        lis r0, 0x5f00          # 0x5f00_0000 = 2^63 in binary32 format
        stwu r0, -16(r1)
        lfs f2, 0(r1)           # f2 = 2^63
        fcmpu cr0, f1, f2       # crbit 0 is f1 < f2
        bf 0, 1f                # branch if f1 >= 2^63 (or f1 is NaN)
	fctidz f1, f1           # convert as signed
        stfd f1, 0(r1)
        lwz r3, 0(r1)
        lwz r4, 4(r1)
        addi r1, r1, 16
        blr
1:      fsub f1, f1, f2         # shift argument down by 2^63
	fctidz f1, f1           # convert as signed
        stfd f1, 0(r1)
        lwz r3, 0(r1)
        lwz r4, 4(r1)
        addis r3, r3, 0x8000    # shift result up by 2^63
        addi r1, r1, 16
        blr
        .type __compcert_i64_dtou, @function
        .size __compcert_i64_dtou, .-__compcert_i64_dtou

        
