#include <stdlib.h>
#include <stdio.h>

static double square(double x)
{
  return x * x;
}

static double integr(double (*f)(double), double low, double high, int n)
{
  double h, x, s;
  int i;

  h = (high - low) / n;
  s = 0;
  for (i = n, x = low; i > 0; i--, x += h) s += f(x);
  return s * h;
}

double test(int n)
{
  return integr(square, 0.0, 1.0, n);
}

int main(int argc, char ** argv)
{
  int n; double r;
  if (argc >= 2) n = atoi(argv[1]); else n = 10000000;
  r = test(n);
  printf("integr(square, 0.0, 1.0, %d) = %g\n", n, r);
  return 0;
}
