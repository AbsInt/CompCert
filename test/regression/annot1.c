#include <stdio.h>

/* Annotations */

int f(int x, int y)
{
  return __builtin_annotation("f(%1,%2)", x, y);
}

double g(double x)
{
  return __builtin_annotation("g(%1 + 1.0)", x + 1.0);
}

int main()
{
  __builtin_annotation("calling f");
  printf("f returns %d\n", f(12, 34));
  __builtin_annotation("calling g");
  printf("f returns %.2f\n", g(3.14));
  return 0;
}

