/* Fun with PowerPC builtins */

#include <stdio.h>

#ifdef __ppc__

int main(int argc, char ** argv)
{
  int x = 0x12345678;
  unsigned int y = 0xDEADBEEF;

  printf("mulhw(%x, %x) = %x\n", x, y, __builtin_mulhw(x, y));
  printf("mulhwu(%x, %x) = %x\n", x, y, __builtin_mulhwu(x, y));
  printf("cntlzw(%x) = %d\n", x, __builtin_cntlzw(x));

  double a = 3.14159;
  double b = 2.718;
  double c = 1.414;

  printf("fmadd(%f, %f, %f) = %f\n", a, b, c, __builtin_fmadd(a, b, c));
  printf("fmsub(%f, %f, %f) = %f\n", a, b, c, __builtin_fmsub(a, b, c));
  printf("fabs(%f) = %f\n", a, __builtin_fabs(a));
  printf("fabs(%f) = %f\n", -a, __builtin_fabs(-a));
  printf("fsqrt(%f) = %f\n", a, __builtin_fsqrt(a));
  printf("frsqrte(%f) = %f\n", a, __builtin_frsqrte(a));
  printf("fres(%f) = %f\n", a, __builtin_fres(a));
  printf("fsel(%f, %f, %f) = %f\n", a, b, c, __builtin_fsel(a, b, c));
  printf("fsel(%f, %f, %f) = %f\n", -a, b, c, __builtin_fsel(-a, b, c));

  unsigned short s = 0x1234;
  printf ("read_16_rev = %x\n", __builtin_read_int16_reversed(&s));
  printf ("read_32_rev = %x\n", __builtin_read_int32_reversed(&y));
  __builtin_write_int16_reversed(&s, 0x789A);
  printf ("after write_16_rev: %x\n", s);
  __builtin_write_int32_reversed(&y, 0x12345678);
  printf ("after write_32_rev: %x\n", y);

  __builtin_eieio();
  __builtin_sync();
  __builtin_isync();

  return 0;
}

#endif


  


