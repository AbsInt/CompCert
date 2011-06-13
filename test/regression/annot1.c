#include <stdio.h>

/* Annotations */

int f(int x)
{
  return __builtin_annot_intval("f(%1)", x + 1);
}

double g(double x, double y)
{
  __builtin_annot("g(%1, %2)", x, y);
  return x + y;
}

int main()
{
  __builtin_annot("calling f");
  printf("f returns %d\n", f(12));
  __builtin_annot("calling g");
  printf("g returns %.2f\n", g(3.14, 2.718));
  return 0;
}

