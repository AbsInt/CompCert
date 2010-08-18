#include <stdio.h>

struct s {
  signed char a: 6;
  unsigned int b: 4;
};

int f(struct s * x)
{
  return (x->a)-- - ++(x->b);
}

struct s * ding(struct s * x)
{
  printf ("Ding!\n");
  return x;
}

int main()
{
  struct s x;

  x.a = 28;
  x.b = 2;

  printf("x = {a = %d, b = %d }\n", x.a, x.b);
  printf("(x.a += 10) = %d\n", (x.a += 10));
  printf("(x.b = 17) = %d\n", (x.b = 17));
  printf("x = {a = %d, b = %d }\n", x.a, x.b);
  printf("f(&x) = %d\n", f(&x));
  printf("f(&x) = %d\n", f(&x));
  printf("f(&x) = %d\n", f(&x));
  printf("x = {a = %d, b = %d }\n", x.a, x.b);
  ding(&x)->a = 10;
  printf("x = {a = %d, b = %d }\n", x.a, x.b);
  ding(&x)->a += 2;
  printf("x = {a = %d, b = %d }\n", x.a, x.b);
  return 0;
}
