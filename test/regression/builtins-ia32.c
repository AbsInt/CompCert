/* Fun with builtin functions */

#include <stdio.h>

int main(int argc, char ** argv)
{
  unsigned int x = 0x12345678;
  double a = 3.14159;
  double b = 2.718;
  unsigned short s = 0x1234;

  printf("bswap(%x) = %x\n", x, __builtin_bswap(x));
  printf("bswap16(%x) = %x\n", s, __builtin_bswap16(s));

  printf("fsqrt(%f) = %f\n", a, __builtin_fsqrt(a));
  printf("fmin(%f, %f) = %f\n", a, b, __builtin_fmin(a, b));
  printf("fmax(%f, %f) = %f\n", a, b, __builtin_fmax(a, b));

  return 0;
}


  


