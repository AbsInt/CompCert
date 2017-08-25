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

// Helper functions for 64-bit integer arithmetic.  IA32 version.
	
#include "sysdeps.h"

// Shift left

// Note: IA32 shift instructions treat their amount (in %cl) modulo 32

FUNCTION(__compcert_i64_shl)
        movl 12(%esp), %ecx             // ecx = shift amount, treated mod 64
        testb $32, %cl
        jne 1f
  // shift amount < 32  
        movl 4(%esp), %eax
        movl 8(%esp), %edx
        shldl %cl, %eax, %edx           // edx = high(XH:XL << amount)
        shll %cl, %eax                  // eax = XL << amount
        ret
  // shift amount >= 32
1:      movl 4(%esp), %edx
        shll %cl, %edx                  // edx = XL << (amount - 32)
        xorl %eax, %eax                 // eax = 0
        ret
ENDFUNCTION(__compcert_i64_shl)

