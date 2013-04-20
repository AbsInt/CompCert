/* Fun with builtins */

#include <stdio.h>

int main(int argc, char ** argv)
{
  unsigned int x = 0x12345678;
  unsigned int y = 0xDEADBEEF;
  double a = 3.14159;
  unsigned short s = 0x1234;

  printf("bswap(%x) = %x\n", x, __builtin_bswap(x));
  printf("bswap16(%x) = %x\n", s, __builtin_bswap16(s));
  printf("cntlz(%x) = %d\n", x, __builtin_cntlz(x));
  printf("fsqrt(%f) = %f\n", a, __builtin_fsqrt(a));
  
  return 0;
}


  


