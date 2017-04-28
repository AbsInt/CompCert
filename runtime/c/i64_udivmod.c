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

#include <stddef.h>
#include "i64.h"

static unsigned i64_udiv6432(unsigned u1, unsigned u0,
                               unsigned v, unsigned *r);
static int i64_nlz(unsigned x);

/* Unsigned division and remainder */

unsigned long long i64_udivmod(unsigned long long n,
                                 unsigned long long d,
                                 unsigned long long * rp)
{
  unsigned dh = d >> 32;
  if (dh == 0) {
    unsigned nh = n >> 32;
    if (nh == 0) {
      /* Special case 32 / 32 */
      unsigned nl = n;
      unsigned dl = d; 
      *rp = (unsigned long long) (nl % dl);
      return (unsigned long long) (nl / dl);
    } else {
      /* Special case 64 / 32 */
      unsigned nl = n;
      unsigned dl = d; 
      unsigned qh = nh / dl;
      unsigned rl;
      unsigned ql = i64_udiv6432(nh % dl, nl, dl, &rl);
      *rp = (unsigned long long) rl; /* high word of remainder is 0 */
      return ((unsigned long long) qh) << 32 | ql;
    }
  } else {
    /* General case 64 / 64 */
    unsigned dl = d;
    /* Scale N and D down, giving N' and D' such that 2^31 <= D' < 2^32 */
    int s = 32 - i64_nlz(dh);  /* shift amount, between 1 and 32 */
    unsigned long long np = i64_shr(n, s);
    unsigned dp = (unsigned) i64_shr(d, s);
    /* Divide N' by D' to get an approximate quotient Q */
    unsigned q = i64_udiv6432(np >> 32, np, dp, NULL);
  again: ;
    /* Tentative quotient Q is either correct or one too high */
    /* Compute Q * D, checking for overflow */
    unsigned long long p1 = (unsigned long long) dl * q;
    unsigned long long p2 = (unsigned long long) (dh * q) << 32;
    unsigned long long p = p1 + p2;
    if (p < p1) {
      /* Overflow occurred: adjust Q down by 1 and redo check */
      q = q - 1; goto again;
    }
    /* Compute remainder R */
    unsigned long long r = n - p;
    if (n < p) {
      /* Q is one too high, adjust Q down by 1 and R up by D */
      q = q - 1; r = r + d;
    }
    *rp = r;
    return (unsigned long long) q;
  }
}

/* Unsigned division and remainder for 64 bits divided by 32 bits. */
/* This is algorithm "divlu" from _Hacker's Delight_, fig 9.3 */

static unsigned i64_udiv6432(unsigned u1, unsigned u0,
                               unsigned v, unsigned *r)
{
  const unsigned b = 65536; // Number base (16 bits).
  unsigned un1, un0,        // Norm. dividend LSD's.
           vn1, vn0,        // Norm. divisor digits.
           q1, q0,          // Quotient digits.
           un32, un21, un10,// Divided digit pairs.
           rhat;            // A remainder.
  int s;                    // Shift amount for norm.

  if (u1 >= v) {            // If overflow,
    if (r != NULL) *r = 0xFFFFFFFFU; // set rem to an impossible value,
    return 0xFFFFFFFFU;              // and return largest possible quotient.
  }
  s = i64_nlz(v);          // 0 <= s <= 31.
  v = v << s;                // Normalize divisor.
  vn1 = v >> 16;             // Break divisor up into
  vn0 = v & 0xFFFF;          // two 16-bit digits.
  un32 = (u1 << s) | ((u0 >> (32 - s)) & (-s >> 31));
  un10 = u0 << s;            // Shift dividend left.
  un1 = un10 >> 16;          // Break right half of
  un0 = un10 & 0xFFFF;       // dividend into two digits.
  q1 = un32/vn1;             // Compute the first quotient digit, q1.
  rhat = un32 - q1*vn1;
 again1:
  if (q1 >= b || q1*vn0 > b*rhat + un1) {
    q1 = q1 - 1;
    rhat = rhat + vn1;
    if (rhat < b) goto again1;
  }
  un21 = un32*b + un1 - q1*v; // Multiply and subtract.
  q0 = un21/vn1;              // Compute the second quotient digit, q0
  rhat = un21 - q0*vn1;
again2:
  if (q0 >= b || q0*vn0 > b*rhat + un0) {
    q0 = q0 - 1;
    rhat = rhat + vn1;
    if (rhat < b) goto again2;
  }
  if (r != NULL) *r = (un21*b + un0 - q0*v) >> s;
  return q1*b + q0;
}

/* Number of leading zeroes */

static int i64_nlz(unsigned x)
{
  if (x == 0) return 32;
  int n = 0;
  if (x <= 0x0000FFFF) { n += 16; x <<= 16; }
  if (x <= 0x00FFFFFF) { n += 8; x <<= 8; }
  if (x <= 0x0FFFFFFF) { n += 4; x <<= 4; }
  if (x <= 0x3FFFFFFF) { n += 2; x <<= 2; }
  if (x <= 0x7FFFFFFF) { n += 1; x <<= 1; }
  return n;
}
