#include <stdio.h>

/* Several equivalent forms that should be turned into cmov */

int test1(int x, int y, int a, int b)
{
  return x < y ? a : b;
}

int test2(int x, int y, int a, int b)
{
  int r;
  if (x < y) { r = a; } else { r = b; }
  return r;
}

int test3(int x, int y, int a, int b)
{
  int r = b;
  if (x < y) { r = a; }
  return r;
}

int test4(int x, int y, int a, int b)
{
  int r = a;
  if (x < y) { /*skip*/; } else { r = b; }
  return r;
}

/* A more advanced example */

int test5(int x, int y, int a)
{
  return x < y ? a + 1 : a - 1;
}

/* Unsafe operations should not be turned into cmov */

int test6(int * p)
{
  return p == NULL ? 0 : *p + 10;
}

int test7(int a, int b)
{
  return b == 0 ? -1 : a / b;
}

/* Very large operations should not be turned into cmov */

int test8(int a)
{
  return a == 0 ? 0 : a*a*a*a - 2*a*a*a + 10*a*a + 42*a - 123;
}

/* Some examples with 64-bit integers */

long long ltest1(int x, int y, long long a, long long b)
{
  return x < y ? a + 1 : b >> 2;
}

/* Some examples with floating-point */

double dmax(double x, double y)
{
  return x >= y ? x : y;
}

double dabs(double x)
{
  return x < 0.0 ? -x : x;
}

float smin(float x, float y)
{
  return x <= y ? x : y;
}

float sdoz(float x, float y)
{
  return x >= y ? x - y : 0.0f;
}

/* Examples where constant propagation should take place */

int constprop1(int x)
{
  int n = 0;
  return n ? x : 42;
}

int constprop2(int x)
{
  int n = 1;
  return n ? x : 42;
}

int constprop3(int x, int y)
{
  int n = 0;
  return x < n ? y - 1 : y + 1;
}

/* Test harness */

#define TESTI(call) printf(#call " = %d\n", call)
#define TESTL(call) printf(#call " = %lld\n", call)
#define TESTF(call) printf(#call " = %f\n", call)


int main()
{
  int i = 1234;
  TESTI(test1(0,1,12,34));
  TESTI(test1(1,0,45,67));
  TESTI(test2(0,1,12,34));
  TESTI(test2(1,0,45,67));
  TESTI(test3(0,1,12,34));
  TESTI(test3(1,0,45,67));
  TESTI(test4(0,1,12,34));
  TESTI(test4(1,0,45,67));
  TESTI(test5(0,1,12));
  TESTI(test5(1,0,45));
  TESTI(test6(NULL));
  TESTI(test6(&i));
  TESTI(test7(1,0));
  TESTI(test7(-100,4));
  TESTI(test8(0));
  TESTI(test8(1));

  TESTL(ltest1(-1, 0, 123LL, 456LL));
  TESTL(ltest1(1, 0, 123LL, 456LL));

  TESTF(dmax(0.0, 3.14));
  TESTF(dmax(1.0, -2.718));

  TESTF(dabs(1.0));
  TESTF(dabs(-2.718));

  TESTF(smin(0.0, 3.14));
  TESTF(smin(1.0, -2.718));

  TESTF(sdoz(1.0, 0.5));
  TESTF(sdoz(0.0, 3.14));

  return 0;
}
