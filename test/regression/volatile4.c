/* Addressing modes in volatiles */

#include <stdio.h>

volatile int g = 1;
volatile int b[10];

void test1(volatile int * p)
{
  volatile int l;
  volatile int a[10];

  l = 42;
  printf ("l = %d\n", l);
  a[5] = 0xff;
  printf ("a[5] = %d\n", a[5]);
  g = 3;
  printf ("g = %d\n", g);
  b[2] = -1;
  printf ("b[2] = %d\n", b[2]);
  p[1] = 80;
  printf ("p[1] = %d\n", p[1]);
}

int main()
{
  test1(&b[0]);
  return 0;
}
