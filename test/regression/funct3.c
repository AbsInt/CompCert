#include <stdio.h>

unsigned char foo (unsigned short n)
{
  printf("%d\n", n);
  return -30;
}

int main (void)
{
  int x = foo(-123456);
  printf("%d\n", x);
  return 0;
}
