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

// Helper functions for 64-bit integer arithmetic.  IA32 version.
	
#include "sysdeps.h"

// Multiply-high unsigned

#define XL 12(%esp)
#define XH 16(%esp)
#define YL 20(%esp)
#define YH 24(%esp)

// X * Y = 2^64 XH.YH + 2^32 (XH.YL + XL.YH) + XL.YL

FUNCTION(__compcert_i64_umulh)
        pushl %esi
        pushl %edi
	movl XL, %eax
        mull YL                 // EDX:EAX = 64-bit product XL.YL
        movl %edx, %ecx
        xorl %esi, %esi
        xorl %edi, %edi         // EDI:ESI:ECX accumulate bits 127:32 of result
        movl XH, %eax
        mull YL                 // EDX:EAX = 64-bit product XH.YL
        addl %eax, %ecx
        adcl %edx, %esi
	adcl $0, %edi
        movl YH, %eax
        mull XL                 // EDX:EAX = 64-bit product YH.XL
        addl %eax, %ecx
        adcl %edx, %esi
	adcl $0, %edi
        movl XH, %eax
        mull YH                 // EDX:EAX = 64-bit product XH.YH
	addl %esi, %eax
        adcl %edi, %edx
	popl %edi
	popl %esi
        ret
ENDFUNCTION(__compcert_i64_umulh)

