// *****************************************************************
//
//               The Compcert verified compiler
//
//           Xavier Leroy, Collège de France and INRIA Paris
//
// Copyright (c) Institut National de Recherche en Informatique et
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

// Helper functions for variadic functions <stdarg.h>.  AArch64 version.

#include "sysdeps.h"	

// typedef struct __va_list {
//   void *__stack;             // next stack parameter
//   void *__gr_top;            // top of the save area for int regs
//   void *__vr_top;            // top of the save area for float regs
//   int__gr_offs;              // offset from gr_top to next int reg
//   int__vr_offs;              // offset from gr_top to next FP reg
// }
// typedef struct __va_list va_list;   // struct passed by reference
// unsigned int __compcert_va_int32(va_list * ap);
// unsigned long long __compcert_va_int64(va_list * ap);
// double __compcert_va_float64(va_list * ap);

FUNCTION(__compcert_va_int32)
        ldr     w1, [x0, #24]   // w1 = gr_offs
        cbz     w1, 1f
  // gr_offs is not zero: load from int save area and update gr_offs
        ldr     x2, [x0, #8]    // x2 = gr_top
        ldr     w2, [x2, w1, sxtw] // w2 = the next integer
        add     w1, w1, #8
        str     w1, [x0, #24]   // update gr_offs
        mov     w0, w2
	ret
  // gr_offs is zero: load from stack save area and update stack pointer
1:      ldr     x1, [x0, #0]    // x1 = stack
        ldr     w2, [x1, #0]    // w2 = the next integer
        add     x1, x1, #8
        str     x1, [x0, #0]    // update stack
        mov     w0, w2
	ret
ENDFUNCTION(__compcert_va_int32)

FUNCTION(__compcert_va_int64)
        ldr     w1, [x0, #24]   // w1 = gr_offs
        cbz     w1, 1f
  // gr_offs is not zero: load from int save area and update gr_offs
        ldr     x2, [x0, #8]    // x2 = gr_top
        ldr     x2, [x2, w1, sxtw] // w2 = the next long integer
        add     w1, w1, #8
        str     w1, [x0, #24]   // update gr_offs
        mov     x0, x2
	ret
  // gr_offs is zero: load from stack save area and update stack pointer
1:      ldr     x1, [x0, #0]    // x1 = stack
        ldr     x2, [x1, #0]    // w2 = the next long integer
        add     x1, x1, #8
        str     x1, [x0, #0]    // update stack
        mov     x0, x2
	ret
ENDFUNCTION(__compcert_va_int64)

FUNCTION(__compcert_va_float64)
        ldr     w1, [x0, #28]   // w1 = vr_offs
        cbz     w1, 1f
  // vr_offs is not zero: load from float save area and update vr_offs
        ldr     x2, [x0, #16]   // x2 = vr_top
        ldr     d0, [x2, w1, sxtw] // d0 = the next float
        add     w1, w1, #16
        str     w1, [x0, #28]   // update vr_offs
	ret
  // gr_offs is zero: load from stack save area and update stack pointer
1:      ldr     x1, [x0, #0]    // x1 = stack
        ldr     d0, [x1, #0]    // d0 = the next float
        add     x1, x1, #8
        str     x1, [x0, #0]    // update stack
	ret
ENDFUNCTION(__compcert_va_float64)

// Right now we pass structs by reference.  This is not ABI conformant.
FUNCTION(__compcert_va_composite)
	b	__compcert_va_int64
ENDFUNCTION(__compcert_va_composite)
