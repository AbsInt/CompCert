/* Fun with builtins */

#include <stdio.h>

int main(int argc, char ** argv)
{
  unsigned int x = 0x12345678;
  unsigned short s = 0x1234;
  unsigned long long zz = 0x123456789ABCDEF0ULL;
  double a = 3.14159;
  double b = 2.718;
  double c = 1.414;

  printf("bswap16(%x) = %x\n", s, __builtin_bswap16(s));
  printf("bswap32(%x) = %x\n", x, __builtin_bswap32(x));
  printf("bswap64(%llx) = %llx\n", zz, __builtin_bswap64(zz));
  printf("fmadd(%f, %f, %f) = %f\n", a, b, c, __builtin_fmadd(a, b, c));
  printf("fmsub(%f, %f, %f) = %f\n", a, b, c, __builtin_fmsub(a, b, c));
  printf("fnmadd(%f, %f, %f) = %f\n", a, b, c, __builtin_fnmadd(a, b, c));
  printf("fnmsub(%f, %f, %f) = %f\n", a, b, c, __builtin_fnmsub(a, b, c));
  printf("fabs(%f) = %f\n", a, __builtin_fabs(a));
  printf("fabs(%f) = %f\n", -a, __builtin_fabs(-a));
  printf("fsqrt(%f) = %f\n", a, __builtin_fsqrt(a));
  printf("fmax(%f, %f) = %f\n", a, b, __builtin_fmax(a, b));
  printf("fmin(%f, %f) = %f\n", a, b, __builtin_fmin(a, b));
  /* Make sure that ignoring the result of a builtin
     doesn't cause an internal error */
  (void) __builtin_fsqrt(a);
  return 0;
}
