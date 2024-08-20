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

### Conversion from signed long to single float	

        .balign 16
        .globl __compcert_i64_stof
__compcert_i64_stof:
        rldimi r4, r3, 32, 0   # reassemble (r3,r4) as a 64-bit integer in r4
   # Check whether -2^53 <= X < 2^53	
        sradi r5, r4, 53
        addi r5, r5, 1
        cmpldi r5, 2
	blt 1f
   # X is large enough that double rounding can occur.
   # Avoid it by nudging X away from the points where double rounding
   # occurs (the "round to odd" technique)
        rldicl r5, r4, 0, 53     # extract bits 0 to 11 of X
        addi r5, r5, 0x7FF       # r5 = (X & 0x7FF) + 0x7FF
   # bit 12 of r5 is 0 if all low 12 bits of X are 0, 1 otherwise
   # bits 13-63 of r5 are 0
        or r4, r4, r5            # correct bit number 12 of X
        rldicr r4, r4, 0, 52     # set to 0 bits 0 to 11 of X
   # Convert to double, then round to single
1:      stdu r4, -16(r1)
        lfd f1, 0(r1)
        fcfid f1, f1
	frsp f1, f1
        addi r1, r1, 16
        blr
        .type __compcert_i64_stof, @function
        .size __compcert_i64_stof, .-__compcert_i64_stof
	
