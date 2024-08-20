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

# Helper functions for variadic functions <stdarg.h>.  IA32 version

# typedef struct {
#   unsigned char ireg;    // index of next integer register
#   unsigned char freg;    // index of next FP register
#   char * stk;            // pointer to next argument in stack
#   struct {
#     int iregs[8];
#     double fregs[8];
#   } * regs;              // pointer to saved register area
# } va_list[1];
#
# unsigned int __compcert_va_int32(va_list ap);
# unsigned long long __compcert_va_int64(va_list ap);
# double __compcert_va_float64(va_list ap);

        .text

        .balign 16
        .globl __compcert_va_int32
__compcert_va_int32:
	                        # r3 = ap = address of va_list structure
        lbz     r4, 0(r3)       # r4 = ap->ireg = next integer register
        cmplwi  r4, 8
        bge     1f
  # Next argument was passed in an integer register
        lwz     r5, 8(r3)       # r5 = ap->regs = base of saved register area
        rlwinm  r6, r4, 2, 0, 29 # r6 = r4 * 4
	addi    r4, r4, 1       # increment ap->ireg
        stb     r4, 0(r3)
        lwzx    r3, r5, r6      # load argument in r3
        blr
  # Next argument was passed on stack
1:      lwz     r5, 4(r3)       # r5 = ap->stk = next argument passed on stack
        addi    r5, r5, 4       # advance ap->stk by 4
        stw     r5, 4(r3)
	lwz     r3, -4(r5)      # load argument in r3
        blr
        .type   __compcert_va_int32, @function
        .size   __compcert_va_int32, .-__compcert_va_int32

        .balign 16
        .globl __compcert_va_int64
__compcert_va_int64:
	                        # r3 = ap = address of va_list structure
        lbz     r4, 0(r3)       # r4 = ap->ireg = next integer register
        cmplwi  r4, 7
        bge     1f
  # Next argument was passed in two consecutive integer register
        lwz     r5, 8(r3)       # r5 = ap->regs = base of saved register area
	addi    r4, r4, 3       # round r4 up to an even number and add 2
        rlwinm  r4, r4, 0, 0, 30 
        rlwinm  r6, r4, 2, 0, 29 # r6 = r4 * 4
	add     r5, r5, r6      # r5 = address of argument + 8
        stb     r4, 0(r3)       # update ap->ireg
        lwz     r3, -8(r5)      # load argument in r3:r4
        lwz     r4, -4(r5)
        blr
  # Next argument was passed on stack
1:      lwz     r5, 4(r3)       # r5 = ap->stk = next argument passed on stack
	li      r4, 8
        stb     r4, 0(r3)       # set ap->ireg = 8 so that no ireg is left
	addi    r5, r5, 15      # round r5 to a multiple of 8 and add 8
        rlwinm  r5, r5, 0, 0, 28
	stw     r5, 4(r3)       # update ap->stk
        lwz     r3, -8(r5)      # load argument in r3:r4
        lwz     r4, -4(r5)
        blr
        .type   __compcert_va_int64, @function
        .size   __compcert_va_int64, .-__compcert_va_int64

        .balign 16
        .globl __compcert_va_float64
__compcert_va_float64:
	                        # r3 = ap = address of va_list structure
        lbz     r4, 1(r3)       # r4 = ap->freg = next float register
        cmplwi  r4, 8
        bge     1f
  # Next argument was passed in a FP register
        lwz     r5, 8(r3)       # r5 = ap->regs = base of saved register area
        rlwinm  r6, r4, 3, 0, 28 # r6 = r4 * 8
	add     r5, r5, r6
        lfd     f1, 32(r5)      # load argument in f1
	addi    r4, r4, 1       # increment ap->freg
        stb     r4, 1(r3)
        blr
  # Next argument was passed on stack
1:      lwz     r5, 4(r3)       # r5 = ap->stk = next argument passed on stack
	addi    r5, r5, 15      # round r5 to a multiple of 8 and add 8
        rlwinm  r5, r5, 0, 0, 28
        lfd     f1, -8(r5)      # load argument in f1
	stw     r5, 4(r3)       # update ap->stk
        blr
        .type   __compcert_va_float64, @function
        .size   __compcert_va_float64, .-__compcert_va_int64

        .balign 16
        .globl __compcert_va_composite
__compcert_va_composite:
	b       __compcert_va_int32
        .type   __compcert_va_composite, @function
        .size   __compcert_va_composite, .-__compcert_va_composite

# Save integer and FP registers at beginning of vararg function        

        .balign 16
        .globl  __compcert_va_saveregs
__compcert_va_saveregs:
        lwz     r11, 0(r1)      # r11 point to top of our frame
        stwu    r3, -96(r11)    # register save area is 96 bytes below
        stw     r4, 4(r11)
        stw     r5, 8(r11)
        stw     r6, 12(r11)
        stw     r7, 16(r11)
        stw     r8, 20(r11)
        stw     r9, 24(r11)
        stw     r10, 28(r11)
	bf      6, 1f           # don't save FP regs if CR6 bit is clear
        stfd    f1, 32(r11)
        stfd    f2, 40(r11)
        stfd    f3, 48(r11)
        stfd    f4, 56(r11)
        stfd    f5, 64(r11)
        stfd    f6, 72(r11)
        stfd    f7, 80(r11)
        stfd    f8, 88(r11)
1:      blr
        .type   __compcert_va_saveregs, @function
        .size   __compcert_va_saveregs, .-__compcert_va_saveregs
