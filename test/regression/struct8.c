/* Passing structs by value */

#include <stdio.h>

struct S { int x; double d; char c; };

struct S f(struct S s, int scale)
{
  struct S r;
  r.x = s.x + scale;
  r.d = s.d * scale;
  r.c = 'f';
  return r;
}

int main()
{
  struct S a = { 123, 2.718, 'a' };
  struct S b, c, d, e;
  b = f(a, 2);
  c = f(f(a, 2), 3);
  e = f((d = f(a, 2)), 3);
  printf("a = { %d, %f, '%c' }\n", a.x, a.d, a.c);
  printf("b = { %d, %f, '%c' }\n", b.x, b.d, b.c);
  printf("c = { %d, %f, '%c' }\n", c.x, c.d, c.c);
  printf("d = { %d, %f, '%c' }\n", d.x, d.d, d.c);
  printf("e = { %d, %f, '%c' }\n", e.x, e.d, e.c);
  return 0;
}
