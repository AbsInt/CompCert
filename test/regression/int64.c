/* Semi-random testing of 64-bit integer operations */

#include <stdio.h>

typedef unsigned long long u64;
typedef signed long long s64;

static u64 rnd64(void)
{
  static u64 seed = 0;
  seed = seed * 6364136223846793005ULL + 1442695040888963407ULL;
  return seed;
}

static inline u64 safe_udiv64(u64 x, u64 y)
{
  if (y == 0) return 0; else return x / y;
}

static inline u64 safe_umod64(u64 x, u64 y)
{
  if (y == 0) return 0; else return x % y;
}

static inline s64 safe_sdiv64(s64 x, s64 y)
{
  if (y == 0 || (y == -1 && x == (-1LL << 63))) return 0; else return x / y;
}

static inline s64 safe_smod64(s64 x, s64 y)
{
  if (y == 0 || (y == -1 && x == (-1LL << 63))) return 0; else return x % y;
}

static void test1(u64 x, u64 y)
{
  u64 y2;
  s64 y3;
  int i;
  double f;
  float s;

  printf("x = %llx\n", x);
  printf("y = %llx\n", y);
  printf("-x = %llx\n", -x);
  printf("x + y = %llx\n", x + y);
  printf("x - y = %llx\n", x - y);
  printf("x * y = %llx\n", x * y);
  printf("x /u y = %llx\n", safe_udiv64(x, y));
  printf("x %%u y = %llx\n", safe_umod64(x, y));
  printf("x /s y = %llx\n", safe_sdiv64(x, y));
  printf("x %%s y = %llx\n", safe_smod64(x, y));
  y2 = y >> 32;
  printf("x /u y2 = %llx\n", safe_udiv64(x, y2));
  printf("x %%u y2 = %llx\n", safe_umod64(x, y2));
  y3 = ((s64)y) >> 32;
  printf("x /s y3 = %llx\n", safe_sdiv64(x, y3));
  printf("x %%s y3 = %llx\n", safe_smod64(x, y3));
  printf("x /u 3 = %llx\n", x / 3);
  printf("x %%u 3 = %llx\n", x % 3);
  printf("x /s 3 = %llx\n", (s64)x / 3);
  printf("x %%s 3 = %llx\n", (s64)x % 3);
  printf("x /u 5 = %llx\n", x / 5);
  printf("x %%u 5 = %llx\n", x % 5);
  printf("x /s 5 = %llx\n", (s64)x / 5);
  printf("x %%s 5 = %llx\n", (s64)x % 5);
  printf("x /u 11 = %llx\n", x / 11);
  printf("x %%u 11 = %llx\n", x % 11);
  printf("x /s 11 = %llx\n", (s64)x / 11);
  printf("x %%s 11 = %llx\n", (s64)x % 11);
  printf("~x = %llx\n", ~x);
  printf("x & y = %llx\n", x & y);
  printf("x | y = %llx\n", x | y);
  printf("x ^ y = %llx\n", x ^ y);
  i = y & 63;
  printf("x << i = %llx\n", x << i);
  printf("x >>u i = %llx\n", x >> i);
  printf("x >>s i = %llx\n", (s64) x >> i);
  printf("x cmpu y = %s\n",
         x == y ? "eq" : x < y ? "lt" : "gt");
  printf("x cmps y = %s\n",
         x == y ? "eq" : (s64)x < (s64)y ? "lt" : "gt");
  f = (double) x;
  printf("utod x = %llx\n", *((u64*) &f));
  f = f * 0.0001;
  printf("dtou f = %llx\n", (u64) f);
  f = (double) ((s64) x);
  printf("stod x = %llx\n", *((u64*) &f));
  f = f * 0.0001;
  printf("dtos f = %llx\n", (s64) f);
  s = (float) x;
  printf("utof x = %x\n", *((unsigned*) &s));
  s = (float) ((s64) x);
  printf("stof x = %x\n", *((unsigned*) &s));
  printf("\n");
}

u64 special_values[] = {
  0,
  1,
  -1,
  0x7FFFFFFFLLU,
  0x80000000LLU,
  0x7FFFFFFFFFFFFFFFLLU,
  0x8000000000000000LLU,
  0x100000003LLU
};

#define NUM_SPECIAL_VALUES (sizeof(special_values) / sizeof(u64))

int main()
{
  int i, j;
  u64 x, y;

  for (i = 0; i < NUM_SPECIAL_VALUES; i++) {
    for (j = 0; j < NUM_SPECIAL_VALUES; j++) {
      test1(special_values[i], special_values[j]);
    }
    test1(special_values[i], rnd64());
    test1(rnd64(), special_values[i]);
  }
  for (i = 0; i < 100; i++) {
    x = rnd64(); y = rnd64();
    test1(x, y);
  }
  return 0;
}







