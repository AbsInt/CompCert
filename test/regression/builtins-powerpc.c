/* Fun with builtins */

#include <stdio.h>

int main(int argc, char ** argv)
{
  unsigned int x = 0x12345678;
  unsigned int y = 0xDEADBEEF;
  double a = 3.14159;
  double b = 2.718;
  double c = 1.414;
  unsigned short s = 0x1234;

  printf("mulhw(%x, %x) = %x\n", x, y, __builtin_mulhw(x, y));
  printf("mulhwu(%x, %x) = %x\n", x, y, __builtin_mulhwu(x, y));
  printf("cntlz(%x) = %d\n", x, __builtin_cntlz(x));
  printf("bswap(%x) = %x\n", x, __builtin_bswap(x));
  printf("bswap16(%x) = %x\n", s, __builtin_bswap16(s));

  printf("fmadd(%f, %f, %f) = %f\n", a, b, c, __builtin_fmadd(a, b, c));
  printf("fmsub(%f, %f, %f) = %f\n", a, b, c, __builtin_fmsub(a, b, c));
  printf("fabs(%f) = %f\n", a, __builtin_fabs(a));
  printf("fabs(%f) = %f\n", -a, __builtin_fabs(-a));
  printf("fsqrt(%f) = %f\n", a, __builtin_fsqrt(a));
  printf("frsqrte(%f) = %f\n", a, __builtin_frsqrte(a));
  printf("fres(%f) = %f\n", a, __builtin_fres(a));
  printf("fsel(%f, %f, %f) = %f\n", a, b, c, __builtin_fsel(a, b, c));
  printf("fsel(%f, %f, %f) = %f\n", -a, b, c, __builtin_fsel(-a, b, c));
  printf("fcti(%f) = %d\n", a, __builtin_fcti(a));
  printf("fcti(%f) = %d\n", b, __builtin_fcti(b));
  printf("fcti(%f) = %d\n", c, __builtin_fcti(c));
  __builtin_eieio();
  __builtin_sync();
  __builtin_isync();
  printf ("read_16_rev = %x\n", __builtin_read16_reversed(&s));
  printf ("read_32_rev = %x\n", __builtin_read32_reversed(&y));
  __builtin_write16_reversed(&s, 0x789A);
  printf ("after write_16_rev: %x\n", s);
  __builtin_write32_reversed(&y, 0x12345678);
  printf ("after write_32_rev: %x\n", y);

  return 0;
}


  


