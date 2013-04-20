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

# Helper functions for 64-bit integer arithmetic.  IA32 version.
	
        .text

# Division and remainder

# Auxiliary function, not exported.
# Input:   20(esp), 24(esp)  is dividend N
#          28(esp), 32(esp)  is divisor  D
# Output:  esi:edi is quotient Q
#          eax:edx is remainder R
# ebp is preserved

        .balign 16
__i64_udivmod:
        cmpl $0, 32(%esp)        # single-word divisor? (DH = 0)
        jne 1f
  # Special case 64 bits divided by 32 bits
        movl 28(%esp), %ecx      # divide NH by DL
        movl 24(%esp), %eax      # (will trap if D = 0)
        xorl %edx, %edx
        divl %ecx                # eax = quotient, edx = remainder
        movl %eax, %edi          # high word of quotient in edi
        movl 20(%esp), %eax      # divide rem : NL by DL
        divl %ecx                # eax = quotient, edx = remainder
        movl %eax, %esi          # low word of quotient in esi */
        movl %edx, %eax          # low word of remainder in eax
        xorl %edx, %edx          # high word of remainder is 0, in edx
        ret
  # The general case
1:      movl 28(%esp), %ecx      # esi:ecx = D
        movl 32(%esp), %esi
        movl 20(%esp), %eax      # edx:eax = N
        movl 24(%esp), %edx
  # Scale D and N down, giving D' and N', until D' fits in 32 bits
2:      shrl $1, %esi            # shift D' right by one
        rcrl $1, %ecx
        shrl $1, %edx            # shift N' right by one
        rcrl $1, %eax
        testl %esi, %esi         # repeat until D'H = 0
        jnz 2b
  # Divide N' by D' to get an approximate quotient
        divl %ecx                # eax = quotient, edx = remainder
        movl %eax, %esi          # save tentative quotient Q in esi
  # Check for off by one quotient
  # Compute Q * D
3:      movl 32(%esp), %ecx
        imull %esi, %ecx         # ecx = Q * DH
        movl 28(%esp), %eax
        mull %esi                # edx:eax = Q * DL
        add %ecx, %edx           # edx:eax = Q * D
        jc 5f                    # overflow in addition means Q is too high
  # Compare Q * D with N, computing the remainder in the process
        movl %eax, %ecx
        movl 20(%esp), %eax
        subl %ecx, %eax
        movl %edx, %ecx
        movl 24(%esp), %edx
        sbbl %ecx, %edx          # edx:eax = N - Q * D
        jnc 4f                   # no carry: N >= Q * D, we are fine
        decl %esi                # carry: N < Q * D, adjust Q down by 1
        addl 28(%esp), %eax      # and remainder up by D
        adcl 32(%esp), %edx
  # Finished
4:      xorl %edi, %edi          # high half of quotient is 0
        ret
  # Special case when Q * D overflows
5:      decl %esi                # adjust Q down by 1
        jmp 3b                   # and redo check & computation of remainder

# Unsigned division

        .globl __i64_udiv
        .balign 16
__i64_udiv:
        pushl %ebp
        pushl %esi
        pushl %edi
        call __i64_udivmod
        movl %esi, %eax
        movl %edi, %edx
        popl %edi
        popl %esi
        popl %ebp
        ret
        .type __i64_udiv, @function
        .size __i64_udiv, . - __i64_udiv

# Unsigned remainder

        .globl __i64_umod
        .balign 16
__i64_umod:
        pushl %ebp
        pushl %esi
        pushl %edi
        call __i64_udivmod
        popl %edi
        popl %esi
        popl %ebp
        ret
        .type __i64_umod, @function
        .size __i64_umod, . - __i64_umod

# Signed division

        .globl __i64_sdiv
        .balign 16
__i64_sdiv:
        pushl %ebp
        pushl %esi
        pushl %edi
        movl 20(%esp), %esi          # esi = NH
        movl %esi, %ebp              # save sign of N in ebp
        testl %esi, %esi
        jge 1f                       # if N < 0,
        negl 16(%esp)                # N = -N
        adcl $0, %esi
        negl %esi
        movl %esi, 20(%esp)
1:      movl 28(%esp), %esi          # esi = DH
        xorl %esi, %ebp              # sign of result in ebp
        testl %esi, %esi
        jge 2f                       # if D < 0,
        negl 24(%esp)                # D = -D
        adcl $0, %esi
        negl %esi
        movl %esi, 28(%esp)
2:      call __i64_udivmod
        testl %ebp, %ebp             # apply sign to result
        jge 3f
        negl %esi
        adcl $0, %edi
        negl %edi
3:      movl %esi, %eax
        movl %edi, %edx
        popl %edi
        popl %esi
        popl %ebp
        ret
        .type __i64_sdiv, @function
        .size __i64_sdiv, . - __i64_sdiv

# Signed remainder

        .globl __i64_smod
        .balign 16
__i64_smod:
        pushl %ebp
        pushl %esi
        pushl %edi
        movl 20(%esp), %esi            # esi = NH
        movl %esi, %ebp                # save sign of result in ebp
        testl %esi, %esi
        jge 1f                         # if N < 0,
        negl 16(%esp)                  # N = -N
        adcl $0, %esi
        negl %esi
        movl %esi, 20(%esp)
1:      movl 28(%esp), %esi            # esi = DH
        testl %esi, %esi
        jge 2f                         # if D < 0,
        negl 24(%esp)                  # D = -D
        adcl $0, %esi
        negl %esi
        movl %esi, 28(%esp)
2:      call __i64_udivmod
        testl %ebp, %ebp               # apply sign to result
        jge 3f
        negl %eax
        adcl $0, %edx
        negl %edx
3:      popl %edi
        popl %esi
        popl %ebp
        ret
        .type __i64_sdiv, @function
        .size __i64_sdiv, . - __i64_sdiv

# Note on shifts:
# IA32 shift instructions treat their amount (in %cl) modulo 32

# Shift left

        .globl __i64_shl
        .balign 16
__i64_shl:
        movl 12(%esp), %ecx             # ecx = shift amount, treated mod 64
        testb $32, %cl
        jne 1f
  # shift amount < 32  
        movl 4(%esp), %eax
        movl 8(%esp), %edx
        shldl %cl, %eax, %edx           # edx = high(XH:XL << amount)
        shll %cl, %eax                  # eax = XL << amount
        ret
  # shift amount >= 32
1:      movl 4(%esp), %edx
        shll %cl, %edx                  # edx = XL << (amount - 32)
        xorl %eax, %eax                 # eax = 0
        ret
        .type __i64_shl, @function
        .size __i64_shl, . - __i64_shl

# Shift right unsigned

        .globl __i64_shr
        .balign 16
__i64_shr:
        movl 12(%esp), %ecx             # ecx = shift amount, treated mod 64
        testb $32, %cl
        jne 1f
  # shift amount < 32
        movl 4(%esp), %eax
        movl 8(%esp), %edx
        shrdl %cl, %edx, %eax           # eax = low(XH:XL >> amount)
        shrl %cl, %edx                  # edx = XH >> amount
        ret
  # shift amount >= 32
1:      movl 8(%esp), %eax
        shrl %cl, %eax                  # eax = XH >> (amount - 32)
        xorl %edx, %edx                 # edx = 0
        ret
        .type __i64_shr, @function
        .size __i64_shr, . - __i64_shr

# Shift right signed

        .globl __i64_sar
        .balign 16
__i64_sar:
        movl 12(%esp), %ecx             # ecx = shift amount, treated mod 64
        testb $32, %cl
        jne 1f
  # shift amount < 32
        movl 4(%esp), %eax
        movl 8(%esp), %edx
        shrdl %cl, %edx, %eax           # eax = low(XH:XL >> amount)
        sarl %cl, %edx                  # edx = XH >> amount (signed)
        ret
  # shift amount >= 32
1:      movl 8(%esp), %eax
        movl %eax, %edx
        sarl %cl, %eax                  # eax = XH >> (amount - 32)
        sarl $31, %edx                  # edx = sign of X
        ret
        .type __i64_sar, @function
        .size __i64_sar, . - __i64_sar

# Unsigned comparison

        .globl __i64_ucmp
        .balign 16
__i64_ucmp:
        movl 8(%esp), %eax              # compare high words
        cmpl 16(%esp), %eax
        jne 1f                          # if high words equal,
        movl 4(%esp), %eax              # compare low words
        cmpl 12(%esp), %eax
1:      seta %al                        # AL = 1 if >, 0 if <=
        setb %dl                        # DL = 1 if <, 0 if >=
        subb %dl, %al                   # AL = 0 if same, 1 if >, -1 if <
        movsbl %al, %eax
        ret
        .type __i64_ucmp, @function
        .size __i64_ucmp, . - __i64_ucmp

# Signed comparison

        .globl __i64_scmp
        .balign 16
__i64_scmp:
        movl 8(%esp), %eax              # compare high words (signed)
        cmpl 16(%esp), %eax
        je 1f                           # if different,
        setg %al                        # extract result 
        setl %dl
        subb %dl, %al
        movsbl %al, %eax
        ret
1:      movl 4(%esp), %eax              # if high words equal,
        cmpl 12(%esp), %eax             # compare low words (unsigned)
        seta %al                        # and extract result
        setb %dl
        subb %dl, %al
        movsbl %al, %eax
        ret
        .type __i64_scmp, @function
        .size __i64_scmp, . - __i64_scmp

# Conversion signed long -> float

        .globl __i64_stod
        .balign 16
__i64_stod:
        fildll 4(%esp)
        ret
        .type __i64_stod, @function
        .size __i64_stod, . - __i64_stod

# Conversion unsigned long -> float

        .globl __i64_utod
        .balign 16
__i64_utod:
        fildll 4(%esp)                  # convert as if signed
        cmpl $0, 8(%esp)                # is argument >= 2^63?
        jns 1f
        fadds LC1                       # adjust by 2^64
1:      ret
        .type __i64_stod, @function
        .size __i64_stod, . - __i64_stod

        .balign 4
LC1:    .long 0x5f800000                # 2^64 in single precision

# Conversion float -> signed long

        .globl __i64_dtos
        .balign 16
__i64_dtos:
        subl $4, %esp
  # Change rounding mode to "round towards zero"
        fnstcw 0(%esp)
        movw 0(%esp), %ax
        movb $12, %ah
        movw %ax, 2(%esp)
        fldcw 2(%esp)
  # Convert
        fldl 8(%esp)
        fistpll 8(%esp)
  # Restore rounding mode
        fldcw 0(%esp)
  # Load result in edx:eax
        movl 8(%esp), %eax
        movl 12(%esp), %edx
        addl $4, %esp
        ret
        .type __i64_dtos, @function
        .size __i64_dtos, . - __i64_dtos

# Conversion float -> unsigned long

        .globl __i64_dtou
        .balign 16
__i64_dtou:
        subl $4, %esp
  # Change rounding mode to "round towards zero"
        fnstcw 0(%esp)
        movw 0(%esp), %ax
        movb $12, %ah
        movw %ax, 2(%esp)
        fldcw 2(%esp)
  # Compare argument with 2^63
        fldl (4+4)(%esp)
        flds LC2
        fucomp
        fnstsw %ax
        sahf
        jbe 1f                  # branch if not (ARG < 2^63)
  # Argument < 2^63: convert as is
        fistpll 8(%esp)
        movl 8(%esp), %eax
        movl 12(%esp), %edx
        jmp 2f
  # Argument > 2^63: offset ARG by -2^63, then convert, then offset RES by 2^63
1:      fsubs LC2
        fistpll 8(%esp)
        movl 8(%esp), %eax
        movl 12(%esp), %edx
        addl $0x80000000, %edx
  # Restore rounding mode
2:      fldcw 0(%esp)
        addl $4, %esp
        ret
        .type __i64_dtou, @function
        .size __i64_dtou, . - __i64_dtou

        .balign 4
LC2:    .long 0x5f000000        # 2^63 in single precision
