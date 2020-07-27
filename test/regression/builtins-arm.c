/* ARM-specific builtins */

#include <stdio.h>

unsigned int x = 0x12345678;
unsigned int y = 0xDEADBEEF;
double a = 3.14159;
unsigned short s = 0x1234;

int main(int argc, char ** argv)
{
  unsigned z;

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


  


