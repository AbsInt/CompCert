/* ************************************************************************** */
/*                                                                            */
/*               The Compcert verified compiler                               */
/*                                                                            */
/*           Xavier Leroy, INRIA Paris-Rocquencourt                           */
/*                                                                            */
/* Copyright (c) 2013 Institut National de Recherche en Informatique et       */
/*  en Automatique.                                                           */
/*                                                                            */
/* Redistribution and use in source and binary forms, with or without         */
/* modification, are permitted provided that the following conditions are met:*/
/*     * Redistributions of source code must retain the above copyright       */
/*       notice, this list of conditions and the following disclaimer.        */
/*     * Redistributions in binary form must reproduce the above copyright    */
/*       notice, this list of conditions and the following disclaimer in the  */
/*       documentation and/or other materials provided with the distribution. */
/*     * Neither the name of the <organization> nor the                       */
/*       names of its contributors may be used to endorse or promote products */
/*       derived from this software without specific prior written permission.*/
/*                                                                            */
/* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        */
/* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT          */
/* LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR      */
/* A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT          */
/* HOLDER> BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,           */
/* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        */
/* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         */
/* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     */
/* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       */
/* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         */
/* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               */
/*                                                                            */
/* ************************************************************************** */

/* Differential testing of 64-bit integer operations */
/* This file is to be compiled by a C compiler other than CompCert C */

#include <stdio.h>
#include <stdlib.h>

typedef unsigned long long u64;
typedef signed long long s64;

extern u64 __compcert_i64_udiv(u64 x, u64 y);
extern u64 __compcert_i64_umod(u64 x, u64 y);
extern s64 __compcert_i64_sdiv(s64 x, s64 y);
extern s64 __compcert_i64_smod(s64 x, s64 y);

extern u64 __compcert_i64_shl(u64 x, unsigned amount);
extern u64 __compcert_i64_shr(u64 x, unsigned amount);
extern s64 __compcert_i64_sar(s64 x, unsigned amount);

extern double __compcert_i64_utod(u64 x);
extern double __compcert_i64_stod(s64 x);
extern float __compcert_i64_utof(u64 x);
extern float __compcert_i64_stof(s64 x);
extern u64 __compcert_i64_dtou(double d);
extern s64 __compcert_i64_dtos(double d);

static u64 rnd64(void)
{
  static u64 seed = 0;
  seed = seed * 6364136223846793005ULL + 1442695040888963407ULL;
  return seed;
}

static int error = 0;

static void test1(u64 x, u64 y)
{
  u64 z, uy;
  s64 t, sy;
  int i;
  double f, g;
  float u, v;

  if (y != 0) {

  z = __compcert_i64_udiv(x, y);
  if (z != x / y) 
    error++, printf("%llu /u %llu = %llu, expected %llu\n", x, y, z, x / y);

  z = __compcert_i64_umod(x, y);
  if (z != x % y) 
    error++, printf("%llu %%u %llu = %llu, expected %llu\n", x, y, z, x % y);

  }

  if (y != 0 && !(x == 0x800000000000LLU && y == -1)) {

  t = __compcert_i64_sdiv(x, y);
  if (t != (s64) x / (s64) y) 
    error++, printf("%lld /s %lld = %lld, expected %lld\n", x, y, t, (s64) x / (s64) y);

  t = __compcert_i64_smod(x, y);
  if (t != (s64) x % (s64) y) 
    error++, printf("%lld %%s %lld = %lld, expected %lld\n", x, y, t, (s64) x % (s64) y);

  }

  /* Test division with small (32-bit) divisors */
  uy = y >> 32;
  sy = (s64)y >> 32;

  if (uy != 0) {

  z = __compcert_i64_udiv(x, uy);
  if (z != x / uy) 
    error++, printf("%llu /u %llu = %llu, expected %llu\n", x, uy, z, x / uy);

  z = __compcert_i64_umod(x, uy);
  if (z != x % uy) 
    error++, printf("%llu %%u %llu = %llu, expected %llu\n", x, uy, z, x % uy);

  }

  if (sy != 0 && !(x == 0x800000000000LLU && sy == -1)) {

  t = __compcert_i64_sdiv(x, sy);
  if (t != (s64) x / sy) 
    error++, printf("%lld /s %lld = %lld, expected %lld\n", x, sy, t, (s64) x / sy);

  t = __compcert_i64_smod(x, sy);
  if (t != (s64) x % sy) 
    error++, printf("%lld %%s %lld = %lld, expected %lld\n", x, sy, t, (s64) x % sy);

  }

  i = y & 63;

  z = __compcert_i64_shl(x, i);
  if (z != x << i) 
    error++, printf("%016llx << %d = %016llx, expected %016llx\n", x, i, z, x << i);

  z = __compcert_i64_shr(x, i);
  if (z != x >> i) 
    error++, printf("%016llx >>u %d = %016llx, expected %016llx\n", x, i, z, x >> i);

  t = __compcert_i64_sar(x, i);
  if (t != (s64) x >> i) 
    error++, printf("%016llx >>s %d = %016llx, expected %016llx\n", x, i, t, (s64) x >> i);

  f = __compcert_i64_utod(x);
  g = (double) x;
  if (f != g)
    error++, printf("(double) %llu (u) = %a, expected %a\n", x, f, g);

  f = __compcert_i64_stod(x);
  g = (double) (s64) x;
  if (f != g)
    error++, printf("(double) %lld (s) = %a, expected %a\n", x, f, g);

  u = __compcert_i64_utof(x);
  v = (float) x;
  if (u != v)
    error++, printf("(float) %llu (u) = %a, expected %a\n", x, u, v);

  u = __compcert_i64_stof(x);
  v = (float) (s64) x;
  if (u != v)
    error++, printf("(float) %lld (s) = %a, expected %a\n", x, u, v);

  f = (double) x;
  if (f >= 0 && f < 0x1p+64) {
    z = __compcert_i64_dtou(f);
    if (z != (u64) f)
      error++, printf("(u64) %a = %llu, expected %llu\n", f, z, (u64) f);
  }

  f = (double) (s64) x;
  if (f >= -0x1p+63 && f < 0x1p+63) {
    t = __compcert_i64_dtos(f);
    if (t != (s64) f)
      error++, printf("(s64) %a = %lld, expected %lld\n", f, z, (s64) f);
  }

  f = ((double) x) * 0.0001;
  z = __compcert_i64_dtou(f);
  if (z != (u64) f)
    error++, printf("(u64) %a = %llu, expected %llu\n", f, z, (u64) f);

  f = ((double) (s64) x) * 0.0001;
  t = __compcert_i64_dtos(f);
  if (t != (s64) f)
    error++, printf("(s64) %a = %lld, expected %lld\n", f, z, (s64) f);
}

#define NSPECIFIC 9

unsigned long long specific[NSPECIFIC] = {
  0, 1, -1, 0x7FFFFFFFULL, 0x80000000ULL, 0xFFFFFFFFULL,
  0x7FFFFFFFFFFFULL, 0x8000000000000000ULL, 0x100000003ULL
};

int main()
{
  int i, j;

  /* Some specific values */
  for (i = 0; i < NSPECIFIC; i++)
    for (j = 0; j < NSPECIFIC; j++)
      test1(specific[i], specific[j]);

  /* Random testing */
  for (i = 0; i < 50; i++) {
    for (j = 0; j < 1000000; j++)
      test1(rnd64(), rnd64());
    printf("."); fflush(stdout);
  }
  printf("\n");
  if (error == 0)
    printf ("Test passed\n");
  else
    printf ("TEST FAILED, %d error(s) detected\n", error);
  return 0;
}

