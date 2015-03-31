// *****************************************************************
//
//               The Compcert verified compiler
//
//           Xavier Leroy, INRIA Paris-Rocquencourt
//
// Copyright (c) 2013 Institut National de Recherche en Informatique et
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

// Helper functions for variadic functions <stdarg.h>.  IA32 version

#include "sysdeps.h"

// typedef void * va_list;
// unsigned int __compcert_va_int32(va_list * ap);
// unsigned long long __compcert_va_int64(va_list * ap);
// double __compcert_va_float64(va_list * ap);

FUNCTION(__compcert_va_int32)
        movl 4(%esp), %ecx         // %ecx = ap parameter
        movl 0(%ecx), %edx         // %edx = current argument pointer
        movl 0(%edx), %eax         // load the int32 value there
        addl $4, %edx              // increment argument pointer by 4
        movl %edx, 0(%ecx)
        ret
ENDFUNCTION(__compcert_va_int32)
        
FUNCTION(__compcert_va_int64)
        movl 4(%esp), %ecx         // %ecx = ap parameter
        movl 0(%ecx), %edx         // %edx = current argument pointer
        movl 0(%edx), %eax         // load the int64 value there
	movl 4(%edx), %edx
        addl $8, 0(%ecx)           // increment argument pointer by 8
        ret
ENDFUNCTION(__compcert_va_int64)
	
FUNCTION(__compcert_va_float64)
        movl 4(%esp), %ecx         // %ecx = ap parameter
        movl 0(%ecx), %edx         // %edx = current argument pointer
        fldl 0(%edx)               // load the float64 value there
        addl $8, %edx              // increment argument pointer by 8
        movl %edx, 0(%ecx)
        ret
ENDFUNCTION(__compcert_va_float64)

FUNCTION(__compcert_va_composite)
        movl 4(%esp), %ecx         // %ecx = ap parameter
	movl 8(%esp), %edx         // %edx = size of composite in bytes
        movl 0(%ecx), %eax         // %eax = current argument pointer
	leal 3(%eax, %edx), %edx   // advance by size
        andl $0xfffffffc, %edx     // and round up to multiple of 4
        movl %edx, 0(%ecx)         // update argument pointer
        ret
ENDFUNCTION(__compcert_va_composite)
        
        
