/* Fun with builtin functions */

#include <stdio.h>

int main(int argc, char ** argv)
{
  unsigned int x = 0x12345678;
  unsigned int y = 0xDEADBEEF;
  double a = 3.14159;
  double b = 2.718;
  double c = 1.414;
  unsigned short s = 0x1234;

  printf("bswap(%x) = %x\n", x, __builtin_bswap(x));
  printf("bswap16(%x) = %x\n", s, __builtin_bswap16(s));
  printf("clz(%x) = %d\n", x, __builtin_clz(x));
  printf("ctz(%x) = %d\n", s, __builtin_ctz(s));

  printf("fsqrt(%f) = %f\n", a, __builtin_fsqrt(a));
  printf("fmin(%f, %f) = %f\n", a, b, __builtin_fmin(a, b));
  printf("fmax(%f, %f) = %f\n", a, b, __builtin_fmax(a, b));

#ifdef FMA3
  printf("fmadd(%f, %f, %f) = %f\n", a, b, c, __builtin_fmadd(a, b, c));
  printf("fmsub(%f, %f, %f) = %f\n", a, b, c, __builtin_fmsub(a, b, c));
  printf("fnmadd(%f, %f, %f) = %f\n", a, b, c, __builtin_fnmadd(a, b, c));
  printf("fnmsub(%f, %f, %f) = %f\n", a, b, c, __builtin_fnmsub(a, b, c));
#endif

  printf ("read_16_rev = %x\n", __builtin_read16_reversed(&s));
  printf ("read_32_rev = %x\n", __builtin_read32_reversed(&y));
  __builtin_write16_reversed(&s, 0x789A);
  printf ("after write_16_rev: %x\n", s);
  __builtin_write32_reversed(&y, 0x12345678);
  printf ("after write_32_rev: %x\n", y);
  y = 0;
  __builtin_write32_reversed(&y, 0x12345678);
  printf ("CSE write_32_rev: %s\n", y == 0x78563412 ? "ok" : "ERROR");

  return 0;
}


  


