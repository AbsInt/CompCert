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

// Multiply-high signed

#define XL 12(%esp)
#define XH 16(%esp)
#define YL 20(%esp)
#define YH 24(%esp)

// Hacker's Delight section 8.3:
// - compute high 64 bits of the unsigned product X * Y  (see i64_umulh.S)
// - subtract X if Y < 0
// - subtract Y if X < 0

FUNCTION(__compcert_i64_smulh)
        pushl %esi
        pushl %edi
	movl XL, %eax
        mull YL                 // EDX:EAX = 64-bit product XL.YL
        movl %edx, %ecx
        xorl %esi, %esi
        xorl %edi, %edi         // EDI:ESI:ECX accumulatesbits 127:32 of result
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
	addl %eax, %esi
        adcl %edx, %edi
// Here, EDI:ESI is the high 64 bits of the unsigned product X.Y
        xorl %eax, %eax
        xorl %edx, %edx
        cmpl $0, XH
        cmovl YL, %eax
        cmovl YH, %edx          // EDX:EAX = Y if X < 0, = 0 if X >= 0
        subl %eax, %esi
        sbbl %edx, %edi         // EDI:ESI -= Y  if X < 0
        xorl %eax, %eax
        xorl %edx, %edx
        cmpl $0, YH
        cmovl XL, %eax
        cmovl XH, %edx          // EDX:EAX = X if Y < 0, = 0 if Y >= 0
        subl %eax, %esi
        sbbl %edx, %edi         // EDI:ESI -= X  if Y < 0
// Now EDI:ESI contains the high 64 bits of the signed product X.Y
        movl %esi, %eax
        movl %edi, %edx
        popl %edi
        popl %esi
        ret
ENDFUNCTION(__compcert_i64_smulh)
