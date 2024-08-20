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

### Conversion from unsigned long to double float	

        .balign 16
        .globl __compcert_i64_utod
__compcert_i64_utod:
	rldicl r3, r3, 0, 32    # clear top 32 bits
	rldicl r4, r4, 0, 32    # clear top 32 bits
	lis r5, 0x4f80          # 0x4f80_0000 = 2^32 in binary32 format
        stdu r3, -32(r1)
        std r4, 8(r1)
        stw r5, 16(r1)
        lfd f1, 0(r1)           # high 32 bits of argument
        lfd f2, 8(r1)           # low 32 bits of argument
	lfs f3, 16(r1)          # 2^32
        fcfid f1, f1            # convert both 32-bit halves to FP (exactly)
	fcfid f2, f2
        fmadd f1, f1, f3, f2    # compute hi * 2^32 + lo
        addi r1, r1, 32
        blr
        .type __compcert_i64_utod, @function
        .size __compcert_i64_utod, .-__compcert_i64_utod
	
# Alternate implementation using round-to-odd:
#       rldimi r4, r3, 32, 0   # reassemble (r3,r4) as a 64-bit integer in r4
#       cmpdi r4, 0            # is r4 >= 2^63 ?
#       blt 1f
#	stdu r4, -16(r1)       # r4 < 2^63: convert as signed
#       lfd f1, 0(r1)
#       fcfid f1, f1
#       addi r1, r1, 16
#       blr
#1:     rldicl r0, r4, 0, 63   # extract low bit of r4
#       srdi r4, r4, 1
#       or r4, r4, r0          # round r4 to 63 bits, using round-to-odd
#	stdu r4, -16(r1)       # convert to binary64
#       lfd f1, 0(r1)
#       fcfid f1, f1
#       fadd f1, f1, f1        # multiply result by 2
#       addi r1, r1, 16
#       blr
        