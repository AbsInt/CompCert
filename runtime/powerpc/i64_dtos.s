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

### Conversion from double float to signed long	

        .balign 16
        .globl __compcert_i64_dtos
__compcert_i64_dtos:
        stfdu f1, -16(r1)       # extract LO (r4) and HI (r3) halves of double
        lwz r3, 0(r1)
        lwz r4, 4(r1)
        addi r1, r1, 16
        srawi r10, r3, 31       # save sign of double in r10
 # extract unbiased exponent  ((HI & 0x7FF00000) >> 20) - (1023 + 52)
        rlwinm r5, r3, 12, 21, 31
        addi r5, r5, -1075
 # check range of exponent
        cmpwi r5, -52           # if EXP < -52, abs(double) is < 1.0
        blt 1f
        cmpwi r5, 11            # if EXP >= 63 - 52, abs(double) is >= 2^63
        bge 2f
  # extract true mantissa
        rlwinm r3, r3, 0, 12, 31  # HI &= ~0xFFF00000
        oris r3, r3, 0x10         # HI |=  0x00100000
  # shift it appropriately
        cmpwi r5, 0
        blt 3f
  # if EXP >= 0, shift left by EXP.  Note that EXP < 11.
        subfic r6, r5, 32       # r6 = 32 - EXP
        slw r3, r3, r5
        srw r0, r4, r6
        or r3, r3, r0
        slw r4, r4, r5
        b 4f
  # if EXP < 0, shift right by -EXP.  Note that -EXP <= 52 but can be >= 32.
3:      subfic r5, r5, 0        # r5 = -EXP = shift amount
        subfic r6, r5, 32       # r6 = 32 - amount
        addi r7, r5, -32        # r7 = amount - 32  (see i64_shr.s)
        srw r4, r4, r5
        slw r0, r3, r6
        or r4, r4, r0
        srw r0, r3, r7
        or r4, r4, r0
        srw r3, r3, r5
  # apply sign to result	
4:      xor r4, r4, r10
        xor r3, r3, r10
        subfc r4, r10, r4
        subfe r3, r10, r3
        blr
  # Special cases
1:      li r3, 0                # result is 0
        li r4, 0
        blr
2:      li r4, -1               # result is MAX_SINT or MIN_SINT
        bge 5f                  # depending on sign
        li r4, -1               # result is MAX_SINT =  0x7FFF_FFFF
        srwi r3, r4, 1
        blr
5:      lis r3, 0x8000          # result is MIN_SINT = 0x8000_0000
        li r4, 0
        blr
        .type __compcert_i64_dtos, @function
        .size __compcert_i64_dtos, .-__compcert_i64_dtos
        