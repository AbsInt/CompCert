/*****************************************************************
 *
 *               The Compcert verified compiler
 *
 *           Xavier Leroy, INRIA Paris-Rocquencourt
 *
 * Copyright (c) 2013 Institut National de Recherche en Informatique et
 *  en Automatique.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the <organization> nor the
 *       names of its contributors may be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT
 * HOLDER> BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 **********************************************************************/

/* Helper functions for 64-bit integer arithmetic. Reference C implementation */

#include "i64.h"

/* Conversion float64 -> unsigned int64 */

unsigned long long i64_dtou(double d)
{
  /* Extract bits of d's representation */
  union { double d; unsigned long long i; } buf;
  buf.d = d;
  unsigned int h = buf.i >> 32;
  /* Negative FP numbers convert to 0 */
  if ((int) h < 0) return 0ULL;
  /* Extract unbiased exponent */
  int e = ((h & 0x7FF00000) >> 20) - (1023 + 52);
  /* Check range of exponent */
  if (e < -52) {
    /* d is less than 1.0 */
    return 0ULL;
  }
  if (e >= 64 - 52) {
    /* d is greater or equal to 2^64 */
    return 0xFFFFFFFFFFFFFFFFULL; /* max unsigned long long */
  }
  /* Extract true mantissa */
  unsigned long long m =
    (buf.i & ~0xFFF0000000000000LL) | 0x0010000000000000LL;
  /* Shift it appropriately */
  if (e >= 0)
    return i64_shl(m, e);
  else
    return i64_shr(m, -e);

}
