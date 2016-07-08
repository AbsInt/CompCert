/* Fun with builtins */

#include <stdio.h>
#include <math.h>

char * check_relative_error(double exact, double actual, double precision)
{
  double relative_error = (actual - exact) / exact;
  return fabs(relative_error) <= precision ? "OK" : "ERROR";
}

int main(int argc, char ** argv)
{
  unsigned int x = 0x12345678;
  unsigned int y = 0xDEADBEEF;
  unsigned long long xx = 0x1234567812345678ULL;
  unsigned z;
  double a = 3.14159;
  double b = 2.718;
  double c = 1.414;
  unsigned short s = 0x1234;

  printf("mulhw(%x, %x) = %x\n", x, y, __builtin_mulhw(x, y));
  printf("mulhwu(%x, %x) = %x\n", x, y, __builtin_mulhwu(x, y));
  printf("clz(%x) = %d\n", x, __builtin_clz(x));
  printf("clzll(%llx) = %d\n", (unsigned long long) x, __builtin_clzll(x));
  printf("clzll(%llx) = %d\n", xx, __builtin_clzll(xx));
  z = __builtin_bswap(x);
  printf("clzll(%lx) = %d\n", z, __builtin_clzll(z));
  printf("bswap(%x) = %x\n", x, __builtin_bswap(x));
  printf("bswap16(%x) = %x\n", s, __builtin_bswap16(s));

  printf("fmadd(%f, %f, %f) = %f\n", a, b, c, __builtin_fmadd(a, b, c));
  printf("fmsub(%f, %f, %f) = %f\n", a, b, c, __builtin_fmsub(a, b, c));
  printf("fabs(%f) = %f\n", a, __builtin_fabs(a));
  printf("fabs(%f) = %f\n", -a, __builtin_fabs(-a));
  printf("fsqrt(%f) = %f\n", a, __builtin_fsqrt(a));
  printf("frsqrte(%f) = %s\n",
         a, check_relative_error(1.0 / sqrt(a), __builtin_frsqrte(a), 1./32.));
  printf("fres(%f) = %s\n",
         a, check_relative_error(1.0 / a, __builtin_fres(a), 1./256.));
  printf("fsel(%f, %f, %f) = %f\n", a, b, c, __builtin_fsel(a, b, c));
  printf("fsel(%f, %f, %f) = %f\n", -a, b, c, __builtin_fsel(-a, b, c));
  printf("fcti(%f) = %d\n", a, __builtin_fcti(a));
  printf("fcti(%f) = %d\n", b, __builtin_fcti(b));
  printf("fcti(%f) = %d\n", c, __builtin_fcti(c));
  __builtin_eieio();
  __builtin_sync();
  __builtin_isync();
  printf("isel(%d, %d, %d) = %d\n", 0, x, y, __builtin_isel(0, x, y));
  printf("isel(%d, %d, %d) = %d\n", 42, x, y, __builtin_isel(42, x, y));
  printf ("read_16_rev = %x\n", __builtin_read16_reversed(&s));
  printf ("read_32_rev = %x\n", __builtin_read32_reversed(&y));
  __builtin_write16_reversed(&s, 0x789A);
  printf ("after write_16_rev: %x\n", s);
  __builtin_write32_reversed(&y, 0x12345678);
  printf ("after write_32_rev: %x\n", y);
  y = 0;
  __builtin_write32_reversed(&y, 0x12345678);
  printf ("CSE write_32_rev: %s\n", y == 0x78563412 ? "ok" : "ERROR");
  /* Make sure that ignoring the result of a builtin
     doesn't cause an internal error */
  (void) __builtin_bswap(x);
  (void) __builtin_fsqrt(a);
  return 0;
}


  


