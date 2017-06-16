/* Semi-random testing of 32-bit integer operations */

#include <stdio.h>

typedef unsigned int u32;
typedef signed int s32;
typedef unsigned long long u64;

static u32 rnd32(void)
{
  static u32 seed = 0;
  seed = seed * 69069 + 25173;
  return seed;
}

static inline u32 safe_udiv32(u32 x, u32 y)
{
  if (y == 0) return 0; else return x / y;
}

static inline u32 safe_umod32(u32 x, u32 y)
{
  if (y == 0) return 0; else return x % y;
}

static inline s32 safe_sdiv32(s32 x, s32 y)
{
  if (y == 0 || (y == -1 && x == (-1 << 31))) return 0; else return x / y;
}

static inline s32 safe_smod32(s32 x, s32 y)
{
  if (y == 0 || (y == -1 && x == (-1 << 31))) return 0; else return x % y;
}

static void test1(u32 x, u32 y)
{
  int i;
  double f;

  printf("x = %x\n", x);
  printf("y = %x\n", y);
  printf("-x = %x\n", -x);
  printf("x + y = %x\n", x + y);
  printf("x - y = %x\n", x - y);
  printf("x * y = %x\n", x * y);
  printf("x /u y = %x\n", safe_udiv32(x, y));
  printf("x %%u y = %x\n", safe_umod32(x, y));
  printf("x /s y = %x\n", safe_sdiv32(x, y));
  printf("x %%s y = %x\n", safe_smod32(x, y));
  printf("x /u 3 = %x\n", x / 3);
  printf("x %%u 3 = %x\n", x % 3);
  printf("x /s 3 = %x\n", (s32)x / 3);
  printf("x %%s 3 = %x\n", (s32)x % 3);
  printf("x /u 5 = %x\n", x / 5);
  printf("x %%u 5 = %x\n", x % 5);
  printf("x /s 5 = %x\n", (s32)x / 5);
  printf("x %%s 5 = %x\n", (s32)x % 5);
  printf("x /u 11 = %x\n", x / 11);
  printf("x %%u 11 = %x\n", x % 11);
  printf("x /s 11 = %x\n", (s32)x / 11);
  printf("x %%s 11 = %x\n", (s32)x % 11);
  printf("~x = %x\n", ~x);
  printf("x & y = %x\n", x & y);
  printf("x | y = %x\n", x | y);
  printf("x ^ y = %x\n", x ^ y);
  i = y & 31;
  printf("x << i = %x\n", x << i);
  printf("x >>u i = %x\n", x >> i);
  printf("x >>s i = %x\n", (s32) x >> i);
  printf("x cmpu y = %s\n",
         x == y ? "eq" : x < y ? "lt" : "gt");
  printf("x cmps y = %s\n",
         x == y ? "eq" : (s32)x < (s32)y ? "lt" : "gt");
  f = (double) x;
  printf("utod x = %llx\n", *((u64*) &f));
  f = f * 0.0001;
  printf("dtou f = %x\n", (u32) f);
  f = (double) ((s32) x);
  printf("stod x = %llx\n", *((u64*) &f));
  f = f * 0.0001;
  printf("dtos f = %x\n", (s32) f);
  printf("\n");
}

u32 special_values[] = {
  0,
  1,
  -1,
  0x7FFFFFFFU,
  0x80000000U,
};

#define NUM_SPECIAL_VALUES (sizeof(special_values) / sizeof(u32))

int main()
{
  int i, j;
  u32 x, y;

  for (i = 0; i < NUM_SPECIAL_VALUES; i++) {
    for (j = 0; j < NUM_SPECIAL_VALUES; j++) {
      test1(special_values[i], special_values[j]);
    }
    test1(special_values[i], rnd32());
    test1(rnd32(), special_values[i]);
  }
  for (i = 0; i < 100; i++) {
    x = rnd32(); y = rnd32();
    test1(x, y);
  }
  return 0;
}







