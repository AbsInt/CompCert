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
  struct S b = f(a, 2);
  printf("a = { %d, %f, '%c' }\n", a.x, a.d, a.c);
  printf("b = { %d, %f, '%c' }\n", b.x, b.d, b.c);
  return 0;
}
