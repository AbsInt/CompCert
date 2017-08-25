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

// Conversion float -> unsigned long

FUNCTION(__compcert_i64_dtou)
        subl $4, %esp
  // Compare argument with 2^63
        fldl 8(%esp)
        flds LC1
        fucomp
        fnstsw %ax
        sahf
        jbe 1f                  // branch if not (ARG < 2^63)
  // Argument < 2^63: convert as is
  // Change rounding mode to "round towards zero"
        fnstcw 0(%esp)
        movw 0(%esp), %ax
        movb $12, %ah
        movw %ax, 2(%esp)
        fldcw 2(%esp)
  // Convert
        fistpll 8(%esp)
        movl 8(%esp), %eax
        movl 12(%esp), %edx
  // Restore rounding mode
        fldcw 0(%esp)
        addl $4, %esp
        ret
  // Argument > 2^63: offset ARG by -2^63, then convert, then offset RES by 2^63
1:      fsubs LC1
  // Change rounding mode to "round towards zero"
        fnstcw 0(%esp)
        movw 0(%esp), %ax
        movb $12, %ah
        movw %ax, 2(%esp)
        fldcw 2(%esp)
  // Convert
        fistpll 8(%esp)
        movl 8(%esp), %eax
        movl 12(%esp), %edx
  // Offset result by 2^63
        addl $0x80000000, %edx
  // Restore rounding mode
        fldcw 0(%esp)
        addl $4, %esp
        ret

        .p2align 2
LC1:    .long 0x5f000000        // 2^63 in single precision

ENDFUNCTION(__compcert_i64_dtou)
        