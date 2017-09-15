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
// Thumb2-only
#define THUMB
#else
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
