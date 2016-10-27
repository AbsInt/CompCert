// *****************************************************************
//
//               The Compcert verified compiler
//
//           Xavier Leroy, INRIA Paris
//
// Copyright (c) 2016 Institut National de Recherche en Informatique et
//  en Automatique.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of the <organization> nor the
//       names of its contributors may be used to endorse or promote products
//       derived from this software without specific prior written permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT
// HOLDER> BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
// EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
// PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
// PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
// LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
// NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
// *********************************************************************

// Helper functions for variadic functions <stdarg.h>.  x86_64 version.
	
// typedef struct {
//    unsigned int gp_offset;
//    unsigned int fp_offset;
//    void *overflow_arg_area;
//    void *reg_save_area;
// } va_list[1];

// The va_start macro initializes the structure as follows:
// - reg_save_area: The element points to the start of the register save area.
// - overflow_arg_area: This pointer is used to fetch arguments passed on
//   the stack. It is initialized with the address of the ﬁrst argument
//   passed on the stack, if any, and then always updated to point to the
//   start of the next argument on the stack.
// - gp_offset: The element holds the offset in bytes from reg_save_area
//   to the place where the next available general purpose argument
//   register is saved. In case all argument registers have been
//   exhausted, it is set to the value 48 (6 * 8).
// - fp_offset: The element holds the offset in bytes from reg_save_area
//   to the place where the next available floating point argument
//   register is saved. In case all argument registers have been
//   exhausted, it is set to the value 176 (6 * 8 + 8 * 16).

// unsigned int __compcert_va_int32(va_list ap);
// unsigned long long __compcert_va_int64(va_list ap);
// double __compcert_va_float64(va_list ap);

#include "sysdeps.h"

FUNCTION(__compcert_va_int32)
        movl    0(%rdi), %edx           // edx = gp_offset
        cmpl    $48, %edx
        jae     1f
  // next argument is in gp reg area
        movq    16(%rdi), %rsi          // rsi = reg_save_area
        movl    0(%rsi, %rdx, 1), %eax  // next integer argument
        addl    $8, %edx
        movl    %edx, 0(%rdi)           // increment gp_offset by 8
        ret
  // next argument is in overflow arg area
1:      movq    8(%rdi), %rsi           // rsi = overflow_arg_area
        movq    0(%rsi), %rax           // next integer argument
        addq    $8, %rsi
        movq    %rsi, 8(%rdi)           // increment overflow_arg_area by 8
        ret
ENDFUNCTION(__compcert_va_int32)

FUNCTION(__compcert_va_int64)
        movl    0(%rdi), %edx           // edx = gp_offset
        cmpl    $48, %edx
        jae     1f
  // next argument is in gp reg area
        movq    16(%rdi), %rsi          // rsi = reg_save_area
        movq    0(%rsi, %rdx, 1), %rax  // next integer argument
        addl    $8, %edx
        movl    %edx, 0(%rdi)            // increment gp_offset by 8
        ret
  // next argument is in overflow arg area
1:      movq    8(%rdi), %rsi           // rsi = overflow_arg_area
        movq    0(%rsi), %rax           // next integer argument
        addq    $8, %rsi
        movq    %rsi, 8(%rdi)           // increment overflow_arg_area by 8
        ret
ENDFUNCTION(__compcert_va_int64)

FUNCTION(__compcert_va_float64)
        movl    4(%rdi), %edx           // edx = fp_offset
        cmpl    $176, %edx
        jae     1f
  // next argument is in fp reg area
        movq    16(%rdi), %rsi          // rsi = reg_save_area
        movsd   0(%rsi, %rdx, 1), %xmm0 // next floating-point argument
        addl    $16, %edx
        movl    %edx, 4(%rdi)           // increment fp_offset by 16
        ret
  // next argument is in overflow arg area
1:      movq    8(%rdi), %rsi           // rsi = overflow_arg_area
        movsd   0(%rsi), %xmm0          // next floating-point argument
        addq    $8, %rsi
        movq    %rsi, 8(%rdi)           // increment overflow_arg_area by 8
        ret
ENDFUNCTION(__compcert_va_float64)

FUNCTION(__compcert_va_composite)
        jmp     GLOB(__compcert_va_int64)     // by-ref convention, FIXME
ENDFUNCTION(__compcert_va_composite)	
	
// Save integer and FP registers at beginning of vararg function
// r10 points to register save area
// al contains number of FP arguments passed in registers
// The register save area has the following shape:
//   0, 8, ..., 40   -> 6 x 8-byte slots for saving rdi, rsi, rdx, rcx, r8, r9
//   48, 64, ... 160 -> 8 x 16-byte slots for saving xmm0...xmm7

FUNCTION(__compcert_va_saveregs)
        movq %rdi, 0(%r10)
        movq %rsi, 8(%r10)
        movq %rdx, 16(%r10)
        movq %rcx, 24(%r10)
        movq %r8, 32(%r10)
        movq %r9, 40(%r10)
        testb %al, %al
        je 1f
        movaps %xmm0, 48(%r10)
        movaps %xmm1, 64(%r10)
        movaps %xmm2, 80(%r10)
        movaps %xmm3, 96(%r10)
        movaps %xmm4, 112(%r10)
        movaps %xmm5, 128(%r10)
        movaps %xmm6, 144(%r10)
        movaps %xmm7, 160(%r10)
1:      ret
ENDFUNCTION(__compcert_va_saveregs)
