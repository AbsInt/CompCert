/* Testing _Bool type support */

#include <stdio.h>

int x = 42;
_Bool y = 777;

int main()
{
  _Bool a, b, c, d, e, f, g, h, i;
  a = x;
  b = x >= 100;
  c = (_Bool) &x;
  d = a && b;
  e = a || b;
  f = a & b;
  g = a | b;
  h = 3.14;
  i = 0.0;
  printf("a = %d\n", a);
  printf("b = %d\n", b);
  printf("c = %d\n", c);
  printf("d = %d\n", d);
  printf("e = %d\n", e);
  printf("f = %d\n", f);
  printf("g = %d\n", g);
  printf("h = %d\n", h);
  printf("i = %d\n", i);
  printf("y = %d\n", y);
  return 0;
}
