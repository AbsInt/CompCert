#include <stdio.h>

volatile int v;

int f1(void) { return v; }

void f2(void) { v = 42; }

int f3(void) { return v / v + 1 + v; }

void f4(void) { v; }

volatile int t[2];

int f5(int x) { t[0] = x; return t[0]; }

int main()
{
  v = 123;
  printf("f1() = %d\n", f1());
  f2();
  printf("v = %d\n", v);
  printf("f3() = %d\n", f3());
  f4();
  printf("f5(2) = %d\n", f5(2));
  return 0;
}
