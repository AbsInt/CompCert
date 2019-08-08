/* Fun with builtin functions */

#include <stdio.h>

int main(int argc, char ** argv)
{
  unsigned int x = 0x12345678;
  unsigned int y = 0xDEADBEEF;
  unsigned long long xx = 0x1234567812345678ULL;
  unsigned long long yy = 0x1234567800000000ULL;
  unsigned long long zz = 0x123456789ABCDEF0ULL;
  unsigned z;
  double a = 3.14159;
  double b = 2.718;
  double c = 1.414;
  unsigned short s = 0x1234;
  signed int u = 1234567;
  signed int v = -9999;

  printf("bswap(%x) = %x\n", x, __builtin_bswap(x));
  printf("bswap16(%x) = %x\n", s, __builtin_bswap16(s));
  printf("bswap64(%llx) = %llx\n", zz, __builtin_bswap64(zz));
  printf("clz(%x) = %d\n", x, __builtin_clz(x));
  printf("clzll(%llx) = %d\n", (unsigned long long) x, __builtin_clzll(x));
  printf("clzll(%llx) = %d\n", xx, __builtin_clzll(xx));
  printf("cls(%d) = %d\n", u, __builtin_cls(u));
  printf("cls(%d) = %d\n", v, __builtin_cls(v));
  printf("clsll(%lld) = %d\n", (signed long long) u, __builtin_clsll(u));
  printf("clsll(%lld) = %d\n", (signed long long) v, __builtin_clsll(v));

  printf("fsqrt(%f) = %f\n", a, __builtin_fsqrt(a));
  printf("fmadd(%f, %f, %f) = %f\n", a, b, c, __builtin_fmadd(a, b, c));
  printf("fmsub(%f, %f, %f) = %f\n", a, b, c, __builtin_fmsub(a, b, c));
  printf("fnmadd(%f, %f, %f) = %f\n", a, b, c, __builtin_fnmadd(a, b, c));
  printf("fnmsub(%f, %f, %f) = %f\n", a, b, c, __builtin_fnmsub(a, b, c));

  /* Make sure that ignoring the result of a builtin
     doesn't cause an internal error */
  (void) __builtin_bswap(x);
  (void) __builtin_fsqrt(a);
  return 0;
}


  


