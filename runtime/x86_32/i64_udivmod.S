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

// Division and remainder

// Auxiliary function, never called directly from C code
// Input:   20(esp), 24(esp)  is dividend N
//          28(esp), 32(esp)  is divisor  D
// Output:  esi:edi is quotient Q
//          eax:edx is remainder R
// ebp is preserved

FUNCTION(__compcert_i64_udivmod)
        cmpl $0, 32(%esp)        // single-word divisor? (DH = 0)
        jne 1f
  // Special case 64 bits divided by 32 bits
        movl 28(%esp), %ecx      // divide NH by DL
        movl 24(%esp), %eax      // (will trap if D = 0)
        xorl %edx, %edx
        divl %ecx                // eax = quotient, edx = remainder
        movl %eax, %edi          // high word of quotient in edi
        movl 20(%esp), %eax      // divide rem : NL by DL
        divl %ecx                // eax = quotient, edx = remainder
        movl %eax, %esi          // low word of quotient in esi */
        movl %edx, %eax          // low word of remainder in eax
        xorl %edx, %edx          // high word of remainder is 0, in edx
        ret
  // The general case
1:      movl 28(%esp), %ecx      // esi:ecx = D
        movl 32(%esp), %esi
        movl 20(%esp), %eax      // edx:eax = N
        movl 24(%esp), %edx
  // Scale D and N down, giving D' and N', until D' fits in 32 bits
2:      shrl $1, %esi            // shift D' right by one
        rcrl $1, %ecx
        shrl $1, %edx            // shift N' right by one
        rcrl $1, %eax
        testl %esi, %esi         // repeat until D'H = 0
        jnz 2b
  // Divide N' by D' to get an approximate quotient
        divl %ecx                // eax = quotient, edx = remainder
        movl %eax, %esi          // save tentative quotient Q in esi
  // Check for off by one quotient
  // Compute Q * D
3:      movl 32(%esp), %ecx
        imull %esi, %ecx         // ecx = Q * DH
        movl 28(%esp), %eax
        mull %esi                // edx:eax = Q * DL
        add %ecx, %edx           // edx:eax = Q * D
        jc 5f                    // overflow in addition means Q is too high
  // Compare Q * D with N, computing the remainder in the process
        movl %eax, %ecx
        movl 20(%esp), %eax
        subl %ecx, %eax
        movl %edx, %ecx
        movl 24(%esp), %edx
        sbbl %ecx, %edx          // edx:eax = N - Q * D
        jnc 4f                   // no carry: N >= Q * D, we are fine
        decl %esi                // carry: N < Q * D, adjust Q down by 1
        addl 28(%esp), %eax      // and remainder up by D
        adcl 32(%esp), %edx
  // Finished
4:      xorl %edi, %edi          // high half of quotient is 0
        ret
  // Special case when Q * D overflows
5:      decl %esi                // adjust Q down by 1
        jmp 3b                   // and redo check & computation of remainder

ENDFUNCTION(__compcert_i64_udivmod)
