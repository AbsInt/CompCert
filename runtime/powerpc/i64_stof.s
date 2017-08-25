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

### Conversion from signed long to single float	

        .balign 16
        .globl __compcert_i64_stof
__compcert_i64_stof:
	mflr r9
   # Check whether -2^53 <= X < 2^53	
        srawi r5, r3, 31
        srawi r6, r3, 21        # (r5,r6) = X >> 53
        addic r6, r6, 1
        addze r5, r5            # (r5,r6) = (X >> 53) + 1
        cmplwi r5, 2
        blt 1f
   # X is large enough that double rounding can occur.
   # Avoid it by nudging X away from the points where double rounding
   # occurs (the "round to odd" technique)
        rlwinm r0, r4, 0, 21, 31 # extract bits 0 to 11 of X
        addi r0, r0, 0x7FF      # r0 = (X & 0x7FF) + 0x7FF
   # bit 12 of r0 is 0 if all low 12 bits of X are 0, 1 otherwise
   # bits 13-31 of r0 are 0
        or r4, r4, r0           # correct bit number 12 of X
        rlwinm r4, r4, 0, 0, 20 # set to 0 bits 0 to 11 of X
   # Convert to double, then round to single	
1:      bl __compcert_i64_stod
        mtlr r9
        frsp f1, f1
        blr
        .type __compcert_i64_stof, @function
        .size __compcert_i64_stof, .-__compcert_i64_stof
	
