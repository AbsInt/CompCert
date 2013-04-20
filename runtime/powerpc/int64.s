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

# Calling conventions for R = F(X) or R = F(X,Y):
#   one or two long arguments:   XH in r3, XL in r4, YH in r5, YL in r6
#   one long argument, one int:  XH in r3, XL in r4, Y in r5
#   one float argument:          X in f1	
#   one long result:             RH in r3, RL in r4
#   one float result:            R in f1        
# This is a big-endian convention: the high word is in the low-numbered register
# Can use r3...r12 and f0...r13 as temporary registers (caller-save)	
	
	.text
        
### Opposite

        .balign 16
        .globl __i64_neg
__i64_neg:
        subfic r4, r4, 0        # RL = -XL and set borrow iff XL != 0
        subfze r3, r3           # RH = -XH - borrow
        blr
        .type __i64_neg, @function
        .size __i64_neg, .-__i64_neg

### Addition	

        .balign 16
        .globl __i64_add
__i64_add:
        addc r4, r4, r6         # RL = XL + YL and set carry if overflow
        adde r3, r3, r5         # RH = XH + YH + carry
        blr
        .type __i64_add, @function
        .size __i64_add, .-__i64_add

### Subtraction	

        .balign 16
        .globl __i64_sub
__i64_sub:
        subfc r4, r6, r4        # RL = XL - YL and set borrow if underflow
        subfe r3, r5, r3        # RH = XH - YH - borrow
        blr
        .type __i64_sub, @function
        .size __i64_sub, .-__i64_sub

### Multiplication	

        .balign 16
        .globl __i64_mul
__i64_mul:
   # Form intermediate products
        mulhwu r7, r4, r6       # r7 = high half of XL * YL
        mullw r8, r3, r6        # r8 = low half of XH * YL
        mullw r9, r4, r5        # r9 = low half of XL * YH
        mullw r4, r4, r6        # r4 = low half of XL * YL = low half of result
   # Reconstruct high half of result
        add r3, r7, r8
        add r3, r3, r9
        blr
        .type __i64_mul, @function
        .size __i64_mul, .-__i64_mul

### Helper function for division and modulus.  Not exported.	
# Input:  numerator N in (r3,r4), divisor D in (r5,r6)
# Output: quotient Q in (r7,r8),  remainder R in (r3,r4)
	.balign 16
__i64_udivmod:
   # Set up quotient and mask
        li r8, 0                # Q = 0
        li r7, 0
        li r10, 1               # M = 1
        li r9, 0
   # Check for zero divisor
        or. r0, r6, r5
        beqlr                   # return with unspecified quotient & remainder
   # Scale divisor and mask
1:      cmpwi r5, 0             # while top bit of D is zero...
        blt 2f
        subfc r0, r6, r4        # compute borrow out of N - D
        subfe r0, r5, r3
        subfe. r0, r0, r0       # EQ iff no borrow iff N >= D
        bne 2f                  # ... and while N >= D ...
        addc r6, r6, r6         # scale divisor: D = D << 1
        adde r5, r5, r5
        addc r10, r10, r10      # scale mask: M = M << 1
        adde r9, r9, r9
        b 1b                    # end while
   # Long division
2:      subfc r4, r6, r4        # Q = Q | M, N = N - D, and compute borrow
 	or r8, r8, r10
        subfe r3, r5, r3
        or r7, r7, r9
        subfe. r0, r0, r0       # test borrow
        beq 3f                  # no borrow: N >= D, continue
        addc r4, r4, r6         # borrow: undo what we just did to N and Q
        andc r8, r8, r10
        adde r3, r3, r5
        andc r7, r7, r9
3:      slwi r0, r9, 31         # unscale mask: M = M >> 1
        srwi r10, r10, 1
        or r10, r10, r0
        srwi r9, r9, 1
        slwi r0, r5, 31         # unscale divisor: D = D >> 1
        srwi r6, r6, 1
        or r6, r6, r0
        srwi r5, r5, 1
        or. r0, r10, r9         # iterate while M != 0
        bne 2b
        blr

### Unsigned division	

        .balign 16
        .globl __i64_udiv
__i64_udiv:
        mflr r11                # save return address in r11
        bl __i64_udivmod        # unsigned divide
        mtlr r11                # restore return address
        mr r3, r7               # R = quotient
        mr r4, r8
        blr
        .type __i64_udiv, @function
        .size __i64_udiv, .-__i64_udiv

### Unsigned remainder        

        .balign 16
        .globl __i64_umod
__i64_umod:
        mflr r11
        bl __i64_udivmod
        mtlr r11
        blr                     # remainder is already in R
        .type __i64_umod, @function
        .size __i64_umod, .-__i64_umod

### Signed division	
	
        .balign 16
        .globl __i64_sdiv
__i64_sdiv:
        mflr r11                # save return address
        xor r12, r3, r5         # save sign of result in r12 (top bit)
        srawi r0, r3, 31        # take absolute value of N
        xor r4, r4, r0          # (i.e.  N = N ^ r0 - r0,
        xor r3, r3, r0          #  where r0 = 0 if N >= 0 and r0 = -1 if N < 0)
        subfc r4, r0, r4
        subfe r3, r0, r3
        srawi r0, r5, 31        # take absolute value of D
        xor r6, r6, r0          # (same trick)
        xor r5, r5, r0
        subfc r6, r0, r6
        subfe r5, r0, r5
        bl __i64_udivmod        # do unsigned division
        mtlr r11                # restore return address
        srawi r0, r12, 31       # apply expected sign to quotient
        xor r8, r8, r0          # RES = Q if r12 >= 0, -Q if r12 < 0
        xor r7, r7, r0
        subfc r4, r0, r8
        subfe r3, r0, r7
        blr
        .type __i64_sdiv, @function
        .size __i64_sdiv, .-__i64_sdiv
	
## Signed remainder	
	
        .balign 16
        .globl __i64_smod
__i64_smod:
        mflr r11                # save return address
        srawi r12, r3, 31       # save sign of result in r12 (sign of N)
        xor r4, r4, r12         # and take absolute value of N
        xor r3, r3, r12
        subfc r4, r12, r4
        subfe r3, r12, r3
        srawi r0, r5, 31        # take absolute value of D
        xor r6, r6, r0
        xor r5, r5, r0
        subfc r6, r0, r6
        subfe r5, r0, r5
        bl __i64_udivmod        # do unsigned division
        mtlr r11                # restore return address
        xor r4, r4, r12         # apply expected sign to remainder
        xor r3, r3, r12         # RES = R if r12 == 0, -R if r12 == -1
        subfc r4, r12, r4
        subfe r3, r12, r3
        blr
        .type __i64_smod, @function
        .size __i64_smod, .-__i64_smod

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
	
### Signed comparison        

        .balign 16
        .globl __i64_scmp
__i64_scmp:
        cmpw cr0, r3, r5        # compare high words (signed)
	cmplw cr1, r4, r6       # compare low words (unsigned)
        mfcr r0
# Same trick as in __i64_ucmp	
        rlwinm r3, r0, 0, 0, 1
        srawi r3, r3, 24
        rlwinm r4, r0, 4, 0, 1
        srawi r4, r4, 28
	add     r3, r3, r4
        blr
        .type __i64_scmp, @function
        .size __i64_scmp, .-__i64_scmp

### Shifts	
	
# On PowerPC, shift instructions with amount mod 64 >= 32 return 0

        .balign 16
        .globl __i64_shl
__i64_shl:
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
        .type __i64_shl, @function
        .size __i64_shl, .-__i64_shl
        
        .balign 16
        .globl __i64_shr
__i64_shr:
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
        .type __i64_shr, @function
        .size __i64_shr, .-__i64_shr
	
        .balign 16
        .globl __i64_sar
__i64_sar:
        andi. r5, r5, 63        # take amount modulo 64
        cmpwi r5, 32
        bge 1f                  # amount < 32?
        subfic r6, r5, 32       # r6 = 32 - amount
        srw r4, r4, r5          # RH = XH >>s amount
        slw r0, r3, r6          # RL = XL >>u amount | XH << (32 - amount)
        or r4, r4, r0
        sraw r3, r3, r5
        blr
1:      addi r6, r5, -32        # amount >= 32
        sraw r4, r3, r6         # RL = XH >>s (amount - 32)
        srawi r3, r3, 31        # RL = sign extension of XH
        blr
        .type __i64_sar, @function
        .size __i64_sar, .-__i64_sar

### Conversion from unsigned long to double float	

        .balign 16
        .globl __i64_utod
__i64_utod:
        addi r1, r1, -16
        lis r5, 0x4330
        li r6, 0
        stw r5, 0(r1)
        stw r4, 4(r1)
        stw r5, 8(r1)
        stw r6, 12(r1)
        lfd f1, 0(r1)
        lfd f2, 8(r1)
        fsub f1, f1, f2         # f1 is XL as a double
        lis r5, 0x4530
        stw r5, 0(r1)
        stw r3, 4(r1)
        stw r5, 8(r1)
        lfd f2, 0(r1)
        lfd f3, 8(r1)
        fsub f2, f2, f3         # f2 is XH * 2^32 as a double
        fadd f1, f1, f2         # add both to get result
        addi r1, r1, 16
        blr
        .type __i64_utod, @function
        .size __i64_utod, .-__i64_utod
	
### Conversion from signed long to double float	

        .balign 16
        .globl __i64_stod
__i64_stod:
        addi r1, r1, -16
        lis r5, 0x4330
        li r6, 0
        stw r5, 0(r1)
        stw r4, 4(r1)
        stw r5, 8(r1)
        stw r6, 12(r1)
        lfd f1, 0(r1)
        lfd f2, 8(r1)
        fsub f1, f1, f2         # f1 is XL (unsigned) as a double
        lis r5, 0x4530
        lis r6, 0x8000
        stw r5, 0(r1)
        add r3, r3, r6
        stw r3, 4(r1)
        stw r5, 8(r1)
        stw r6, 12(r1)
        lfd f2, 0(r1)
        lfd f3, 8(r1)
        fsub f2, f2, f3         # f2 is XH (signed) * 2^32 as a double
        fadd f1, f1, f2         # add both to get result
        addi r1, r1, 16
        blr
        .type __i64_stod, @function
        .size __i64_stod, .-__i64_stod

### Conversion from double float to unsigned long	

        .balign 16
        .globl __i64_dtou
__i64_dtou:
        stfdu f1, -16(r1)       # extract LO (r4) and HI (r3) halves of double
        lwz r3, 0(r1)
        lwz r4, 4(r1)
        addi r1, r1, 16
        cmpwi r3, 0             # is double < 0?
        blt 1f                  # then it converts to 0
  # extract unbiased exponent  ((HI & 0x7FF00000) >> 20) - (1023 + 52)
        rlwinm r5, r3, 12, 21, 31
        addi r5, r5, -1075
  # check range of exponent
        cmpwi r5, -52           # if EXP < -52, double is < 1.0
        blt 1f
        cmpwi r5, 12            # if EXP >= 64 - 52, double is >= 2^64
        bge 2f
  # extract true mantissa
        rlwinm r3, r3, 0, 12, 31  # HI &= ~0xFFF00000
        oris r3, r3, 0x10         # HI |=  0x00100000
  # shift it appropriately
        cmpwi r5, 0
        blt 3f
        b __i64_shl             # if EXP >= 0, shift left by EXP
3:      subfic r5, r5, 0
        b __i64_shr             # if EXP < 0, shift right by -EXP
  # Special cases
1:      li r3, 0                # result is 0
        li r4, 0
        blr
2:      li r3, -1               # result is MAX_UINT
        li r4, -1
        blr
        .type __i64_dtou, @function
        .size __i64_dtou, .-__i64_dtou

### Conversion from double float to signed long	

        .balign 16
        .globl __i64_dtos
__i64_dtos:
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
        mflr r9                 # save retaddr in r9
        cmpwi r5, 0
        blt 3f
        bl __i64_shl            # if EXP >= 0, shift left by EXP
        b 4f
3:      subfic r5, r5, 0
        bl __i64_shr            # if EXP < 0, shift right by -EXP
  # apply sign to result	
4:      mtlr r9
        xor r4, r4, r10
        xor r3, r3, r10
        subfc r4, r10, r4
        subfe r3, r10, r3
        blr
  # Special cases
1:      li r3, 0                # result is 0
        li r4, 0
        blr
2:      cmpwi r10, 0            # result is MAX_SINT or MIN_SINT
        bge 5f                  # depending on sign
        li r4, -1               # result is MAX_SINT =  0x7FFF_FFFF
        srwi r3, r4, 1
        blr
5:      lis r3, 0x8000          # result is MIN_SINT = 0x8000_0000
        li r4, 0
        blr
        .type __i64_dtos, @function
        .size __i64_dtos, .-__i64_dtos
