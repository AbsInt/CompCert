/* Fun with builtins */

#include <stdio.h>

int main(int argc, char ** argv)
{
  unsigned int x = 0x12345678;
  unsigned int y = 0xDEADBEEF;
  unsigned long long xx = 0x1234567812345678ULL;
  unsigned z;
  double a = 3.14159;
  unsigned short s = 0x1234;

  printf("bswap(%x) = %x\n", x, __builtin_bswap(x));
  printf("bswap16(%x) = %x\n", s, __builtin_bswap16(s));
  printf("clz(%x) = %d\n", x, __builtin_clz(x));
  printf("clzll(%llx) = %d\n", (unsigned long long) x, __builtin_clzll(x));
  printf("clzll(%llx) = %d\n", xx, __builtin_clzll(xx));
  z = __builtin_bswap(x);
  printf("clzll(%lx) = %d\n", z, __builtin_clzll(z));
  printf("fsqrt(%f) = %f\n", a, __builtin_fsqrt(a));
  
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


  


