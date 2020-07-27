/* Builtin functions that are implemented on all target processors */

#include <stdio.h>

unsigned int x = 0x12345678;
unsigned int y = 0xDEADBEEF;
unsigned long long xx = 0x123456789ABCDEF0ULL;
double a = 3.14159;
double b = 2.718;
double c = 1.414;
float f = 7.25;
unsigned short s = 0x1234;

int main(int argc, char ** argv)
{
  printf("bswap(%x) = %x\n", x, __builtin_bswap(x));
  printf("bswap16(%x) = %x\n", s, __builtin_bswap16(s));
  printf("bswap64(%llx) = %llx\n", xx, __builtin_bswap64(xx));
  for (int i = 0; i < 32; i++) {
    unsigned z = 0xFFFFFFFFU >> i;
    printf("clz(%08x) = %d\n", z, __builtin_clz(z));
    z = 0x80000000U >> i;
    printf("clz(%08x) = %d\n", z, __builtin_clz(z));
  }
  for (int i = 0; i < 64; i++) {
    unsigned long long z = 0xFFFFFFFFFFFFFFFFULL >> i;
    printf("clzll(%016llx) = %d\n", z, __builtin_clzll(z));
    z = 0x8000000000000000ULL >> i;
    printf("clzll(%016llx) = %d\n", z, __builtin_clzll(z));
  }
  for (int i = 0; i < 32; i++) {
    unsigned z = 1U << i;
    printf("ctz(%08x) = %d\n", z, __builtin_ctz(z));
    z = 0xFFFFFFFFU << i;
    printf("ctz(%08x) = %d\n", z, __builtin_ctz(z));
  }
  for (int i = 0; i < 64; i++) {
    unsigned long long z = 1ULL << i;
    printf("ctzll(%016llx) = %d\n", z, __builtin_ctzll(z));
    z = 0xFFFFFFFFFFFFFFFFULL << i;
    printf("ctzll(%016llx) = %d\n", z, __builtin_ctzll(z));
  }
  printf("fabs(%f) = %f\n", a, __builtin_fabs(a));
  printf("fabs(%f) = %f\n", -a, __builtin_fabs(-a));
  printf("fabsf(%f) = %f\n", f, __builtin_fabsf(f));
  printf("fabsf(%f) = %f\n", -f, __builtin_fabsf(-f));
  printf("fsqrt(%f) = %f\n", a, __builtin_fsqrt(a));
  printf("sqrt(%f) = %f\n", a, __builtin_sqrt(a));

  /* Make sure that ignoring the result of a builtin
     doesn't cause an internal error */
  (void) __builtin_bswap(x);
  (void) __builtin_fsqrt(a);
  (void) __builtin_sel(a > 0.0, x, y);
  return 0;
}
