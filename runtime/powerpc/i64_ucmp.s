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

### Unsigned comparison        

        .balign 16
        .globl __i64_ucmp
__i64_ucmp:
        cmplw cr0, r3, r5       # compare high words (unsigned)
	cmplw cr1, r4, r6       # compare low words (unsigned)
        mfcr r0
# At this point, the bits of r0 are as follow:	
#   bit 31: XH < YH
#   bit 30: XH > YH        
#   bit 27: XL > YL	
#   bit 26: XL < YL	
        rlwinm r3, r0, 0, 0, 1  # r3 = r0 & 0xC000_0000
        srawi r3, r3, 24        # r4 = r4 >>s 28
# r3 = -0x80 if XH < YH
#    = 0x40  if XH > YH
#    = 0     if XH = YH        
        rlwinm r4, r0, 4, 0, 1  # r4 = (r0 << 4) & 0xC000_0000
        srawi r4, r4, 28        # r4 = r4 >>s 28
# r4 = -8  if XL < YL
#    =  4  if XL > YL
#    =  0  if XL = YL        
	add     r3, r3, r4
# r3 = -0x80 or -0x80 - 8 or -0x80 + 4 or -8 if X < Y 
#         (in all cases, r3 < 0 if X < Y)	
#    = 0x40 or 0x40 - 8 or 0x40 + 4 or 4 if X > Y 
#         (in all cases, r3 > 0 if X > Y)	
#    = 0 if X = Y
        blr
        .type __i64_ucmp, @function
        .size __i64_ucmp, .-__i64_ucmp
	
        