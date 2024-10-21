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

// System dependencies

#if defined(MODEL_armv7m)
// Thumb-2 only
#define THUMB
#elif defined(MODEL_armv6) || defined(MODEL_armv6t2)
// ARM-A32 only
#undef THUMB
#endif

#ifdef THUMB
#define FUNCTION(f) \
	.text; \
	.thumb; \
	.thumb_func; \
	.global f; \
f:
#else
#define FUNCTION(f) \
	.text; \
	.arm; \
	.global f; \
f:
#endif

#define ENDFUNCTION(f) \
	.type f, %function; .size f, . - f

// In Thumb2 mode, some instructions have shorter encodings in their "S" form
// (update condition flags).  For cases where the condition flags do not
// matter, we use the following macros for these instructions.
// In classic ARM mode, we prefer not to use the "S" form unless necessary.

#ifdef THUMB
#define THUMB_S(x) x##s
#else
#define THUMB_S(x) x
#endif

#define ADC THUMB_S(adc)
#define ADD THUMB_S(add)
#define AND THUMB_S(and)
#define ASR THUMB_S(asr)
#define BIC THUMB_S(bic)
#define EOR THUMB_S(eor)
#define LSL THUMB_S(lsl)
#define LSR THUMB_S(lsr)
#define MOV THUMB_S(mov)
#define ORR THUMB_S(orr)
#define RSB THUMB_S(rsb)
#define SUB THUMB_S(sub)

	.syntax unified
#if defined(MODEL_armv6)
        .arch   armv6
#elif defined(MODEL_armv6t2)
        .arch   armv6t2
#elif defined(MODEL_armv7a)
        .arch   armv7-a
#elif defined(MODEL_armv7r)
        .arch   armv7-r
#elif defined(MODEL_armv7m)
        .arch   armv7-m
#else
        .arch   armv7
#endif
	.fpu	vfpv2



// Endianness dependencies

// Location of high and low word of first register pair (r0:r1)
#ifdef ENDIANNESS_big
#define Reg0HI r0
#define Reg0LO r1
#else
#define Reg0HI r1
#define Reg0LO r0
#endif

// Location of high and low word of second register pair (r2:r3)
#ifdef ENDIANNESS_big
#define Reg1HI r2
#define Reg1LO r3
#else
#define Reg1HI r3
#define Reg1LO r2
#endif

// Location of high and low word of third register pair (r4:r5)
#ifdef ENDIANNESS_big
#define Reg2HI r4
#define Reg2LO r5
#else
#define Reg2HI r5
#define Reg2LO r4
#endif

// Location of high and low word of fourth register pair (r6:r7)
#ifdef ENDIANNESS_big
#define Reg3HI r6
#define Reg3LO r7
#else
#define Reg3HI r7
#define Reg3LO r6
#endif

#define HI(r) r##HI
#define LO(r) r##LO

// Useful operations over register pairs

// Move
#define LMOV(r,x) \
  MOV LO(r), LO(x); MOV HI(r), HI(x)

// Left shift by 1
#define LSHL1(r,x) \
  adds LO(r), LO(x), LO(x); adc HI(r), HI(x), HI(x)

// Right shift (logical) by 1
#define LSHR1(r,x) \
  lsrs HI(r), HI(x), #1; rrx LO(r), LO(x)

// Subtract and set carry flag
#define LSUBS(r,x,y) \
  subs LO(r), LO(x), LO(y); sbcs HI(r), HI(x), HI(y)

// Conditional change sign
// Set r = x if sgn = 0 and r = -x if sgn = -1
#define LCONDOPP(r,x,sgn) \
  EOR LO(r), LO(x), sgn;  EOR HI(r), HI(x), sgn; \
  subs LO(r), LO(r), sgn; sbc HI(r), HI(r), sgn

// Note on ARM shifts: the shift amount is taken modulo 256.
// If shift amount mod 256 >= 32, the shift produces 0.

// General left shift by N bits
// Branchless algorithm:
//    rh = (xh << n) | (xl >> (32-n)) | (xl << (n-32))
//    rl = xl << n
// What happens:
//    n                 0   1  ...  31      32   33  ... 63
//    (32-n) mod 255    32  31      1       0    255     224
//    (n-32) mod 255    224 225     255     0    1       31
//    xl << n           xl  xl<<1   xl<<31  0    0       0
//    xh << n           xh  xh<<1   xh<<31  0    0       0
//    xl >> (32-n)      0   xl>>31  xl>>1   xl   0       0
//    xl << (n-32)      0   0       0       xl   xl<<1   xl<<31

#define LSHL(r,x,n,t) \
  RSB t, n, #32; \
  LSL HI(r), HI(x), n; \
  LSR t, LO(x), t; \
  ORR HI(r), HI(r), t; \
  SUB t, n, #32; \
  LSL t, LO(x), t; \
  ORR HI(r), HI(r), t; \
  LSL LO(r), LO(x), n

// Special case of LSHL when the shift amount n is between 0 and 32
// No need to compute the (xl << (n-32)) term.

#define LSHL_small(r,x,n,t) \
  RSB t, n, #32; \
  LSL HI(r), HI(x), n; \
  LSR t, LO(x), t; \
  ORR HI(r), HI(r), t; \
  LSL LO(r), LO(x), n

// General right shift by N bits
// Branchless algorithm:
//    rl = (xl >> n) | (xh << (32-n)) | (xh >> (n-32))
//    rh = xh >> n
// What happens:
//    n                 0   1  ...  31      32   33  ... 63
//    (32-n) mod 255    32  31      1       0    255     224
//    (n-32) mod 255    224 225     255     0    1       31
//    xh >> n           xh  xh>>1   xh>>31  0    0       0
//    xl >> n           xl  xl>>1   xl>>31  0    0       0
//    xh << (32-n)      0   xh<<31  xh<<1   xh   0       0
//    xh >> (n-32)      0   0       0       xh   xh>>1   xh>>31

#define LSHR(r,x,n,t) \
  RSB t, n, #32; \
  LSR LO(r), LO(x), n; \
  LSL t, HI(x), t; \
  ORR LO(r), LO(r), t; \
  SUB t, n, #32; \
  LSR t, HI(x), t; \
  ORR LO(r), LO(r), t; \
  LSR HI(r), HI(x), n

// Stack is not executable

#if defined(SYS_linux) || defined(SYS_bsd)
	.section .note.GNU-stack,"",%progbits
#endif
