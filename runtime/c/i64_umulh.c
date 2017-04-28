/*****************************************************************
 *
 *               The Compcert verified compiler
 *
 *           Xavier Leroy, INRIA Paris
 *
 * Copyright (c) 2016 Institut National de Recherche en Informatique et
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

typedef unsigned long long u64;
typedef unsigned int u32;

/* Unsigned multiply high */

/* Hacker's Delight, algorithm 8.1, specialized to two 32-bit words */

u64 i64_umulh(u64 u, u64 v)
{
  u32 u0 = u, u1 = u >> 32;
  u32 v0 = v, v1 = v >> 32;
  u32 w1, w2, w3, k;
  u64 t;

  t = (u64) u0 * (u64) v0;
  k = t >> 32;

  t = (u64) u1 * (u64) v0 + k;
  w1 = t;
  w2 = t >> 32;

  t = (u64) u0 * (u64) v1 + w1;
  k = t >> 32;

  t = (u64) u1 * (u64) v1 + w2 + k;

  return t;
}
