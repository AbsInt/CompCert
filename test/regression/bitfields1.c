#include <stdio.h>

struct s {
  signed char a: 6;
  unsigned int b: 2;
};

struct t {
  unsigned int c: 16;
  _Bool d: 1;
  short e: 8;
};

int f(struct s * x, struct t * y, int z)
{
  x->a += x->b;
  y->d = z;
  return y->c + y->e;
}

int main()
{
  struct s x;
  struct t y;
  int res;

  x.a = 56;
  x.b = 2;
  y.c = 12345;
  y.d = 0;
  y.e = 89;
  res = f(&x, &y, 2);

  printf("x = {a = %d, b = %d }\n", x.a, x.b);
  printf("y = {c = %d, d = %d, e = %d }\n", y.c, y.d, y.e);
  printf("f returns %d\n", res);

  return 0;
}
