/* Validating the semantics of NaNs. 
   This tests produces output that depend on the processor.
   However, the same output must be obtained from compiled code
   and from the reference interpreter. */

#include<stdio.h>

typedef unsigned long long u64;
typedef unsigned int u32;

inline u64 bits_of_double(double d)
{
  union { double d; u64 i; } u;
  u.d = d; return u.i;
}

inline double double_of_bits(u64 i)
{
  union { double d; u64 i; } u;
  u.i = i; return u.d; 
}

inline u32 bits_of_single(float f)
{
  union { float f; u32 i; } u;
  u.f = f; return u.i;
}

inline float single_of_bits(u32 i)
{
  union { float f; u32 i; } u;
  u.i = i; return u.f;
}

char * valname[8] = {
  "+0", "-0", "+inf", "-inf",
  "snan(5)", "qnan(6)", "snan(-9)", "qnan(-1)"
};

void test64(void)
{
  volatile double val[8];
  int i, j;

  printf("--- Double precision\n");
  val[0] = 0.0;
  val[1] = - val[0];
  val[2] = double_of_bits(0x7FF0000000000000);
  val[3] = - val[2];

  val[4] = double_of_bits(0x7FF0000000000005);
  val[5] = double_of_bits(0x7FF8000000000006);
  val[6] = double_of_bits(0xFFF0000000000009);
  val[7] = double_of_bits(0xFFF8000000000001);

  for (i = 0; i < 8; i++) {
    printf("opp(%s) = 0x%016llx\n", valname[i], bits_of_double(- val[i]));
    printf("single(%s) = 0x%08x\n", valname[i], bits_of_single((float)(val[i])));
    printf("abs(%s) = 0x%016llx\n", valname[i], bits_of_double(__builtin_fabs(val[i])));
    for (j = 0; j < 8; j++) {
      printf("%s + %s = 0x%016llx\n",
             valname[i], valname[j], bits_of_double(val[i] + val[j]));
      printf("%s - %s = 0x%016llx\n",
             valname[i], valname[j], bits_of_double(val[i] - val[j]));
      printf("%s * %s = 0x%016llx\n",
             valname[i], valname[j], bits_of_double(val[i] * val[j]));
      printf("%s / %s = 0x%016llx\n",
             valname[i], valname[j], bits_of_double(val[i] / val[j]));
    }
  }
}

void test32(void)
{
  volatile float val[8];
  int i, j;

  printf("--- Single precision\n");
  val[0] = 0.0f;
  val[1] = - val[0];
  val[2] = single_of_bits(0x7F800000);
  val[3] = - val[2];

  val[4] = single_of_bits(0x7F800005);
  val[5] = single_of_bits(0x7FC00006);
  val[6] = single_of_bits(0xFF800009);
  val[7] = single_of_bits(0xFFC00001);

  for (i = 0; i < 8; i++) {
    printf("opp(%s) = 0x%08x\n", valname[i], bits_of_single(- val[i]));
    printf("double(%s) = 0x%016llx\n", valname[i], bits_of_double((double)(val[i])));
    printf("abs(%s) = 0x%08x\n", valname[i], bits_of_single(__builtin_fabs(val[i])));
    for (j = 0; j < 8; j++) {
      printf("%s + %s = 0x%08x\n",
             valname[i], valname[j], bits_of_single(val[i] + val[j]));
      printf("%s - %s = 0x%08x\n",
             valname[i], valname[j], bits_of_single(val[i] - val[j]));
      printf("%s * %s = 0x%08x\n",
             valname[i], valname[j], bits_of_single(val[i] * val[j]));
      printf("%s / %s = 0x%08x\n",
             valname[i], valname[j], bits_of_single(val[i] / val[j]));
    }
  }
}

int main(void)
{
  test64();
  test32();
  return 0;
}
