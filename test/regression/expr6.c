/* Conditional expressions */

#include <stdio.h>

int f(int x)
{
  return x >= 0 ? x : -x;
}

double g(int x, int y, double z)
{
  return x ? y : z;
}

void h(int x, int y)
{
  while (1) {
    if (x && y) break;
    printf("false\n");
    return;
  }
  printf("true\n");
}

void k(int x, int y, double z)
{
  while (1) {
    if (x ? y : z) break;
    printf("false\n");
    return;
  }
  printf("true\n");
}

int main()
{
  printf("f(42) = %d\n", f(42));
  printf("f(-1) = %d\n", f(-1));
  printf("g(1,2,3.14) = %.2f\n", g(1,2,3.14));
  printf("g(0,2,3.14) = %.2f\n", g(0,2,3.14));
  printf("h(1,2) = "); h(1,2);
  printf("h(0,2) = "); h(0,2);
  printf("h(1,0) = "); h(1,0);
  printf("k(1,2,3.14) = "); k(1,2,3.14);
  printf("k(0,2,3.14) = "); k(0,2,3.14);
  printf("k(1,0,3.14) = "); k(1,0,3.14);
  printf("k(0,2,0.00) = "); k(0,2,0.00);
  return 0;
}

