/* Expansion of read-modify-write operations on volatiles */

#include <stdio.h>

volatile int x;
volatile unsigned char c;

int main()
{
  x = 0;
  printf("x = %d\n", x);

  x++;
  printf("x = %d\n", x);
  printf ("x++ = %d\n", x++);
  printf("x = %d\n", x);

  x += 42;
  printf("x = %d\n", x);
  printf ("x += 12 = %d\n", x += 12);
  printf("x = %d\n", x);

  x--;
  printf("x = %d\n", x);
  printf ("x-- = %d\n", x--);
  printf("x = %d\n", x);

  x -= 7;
  printf("x = %d\n", x);
  printf ("x -= 3 = %d\n", x -= 3);
  printf("x = %d\n", x);

  ++x;
  printf("x = %d\n", x);
  printf ("++x = %d\n", ++x);
  printf("x = %d\n", x);

  --x;
  printf("x = %d\n", x);
  printf ("--x = %d\n", --x);
  printf("x = %d\n", x);

  c = 0;
  printf("c = %d\n", c);

  c++;
  printf("c = %d\n", c);
  printf ("c++ = %d\n", c++);
  printf("c = %d\n", c);

  c += 250;
  printf("c = %d\n", c);
  printf ("c += 42 = %d\n", c += 42);
  printf("c = %d\n", c);

  c--;
  printf("c = %d\n", c);
  printf ("c-- = %d\n", c--);
  printf("c = %d\n", c);

  c -= 7;
  printf("c = %d\n", c);
  printf ("c -= 3 = %d\n", c -= 3);
  printf("c = %d\n", c);

  ++c;
  printf("c = %d\n", c);
  printf ("++c = %d\n", ++c);
  printf("c = %d\n", c);

  --c;
  printf("c = %d\n", c);
  printf ("--c = %d\n", --c);
  printf("c = %d\n", c);

  return 0;
}
