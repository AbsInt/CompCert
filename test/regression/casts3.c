/* Testing int <-> float conversions */

#include <stdio.h>

unsigned int urand(void)
{
  static unsigned int seed = 0;
  seed = seed * 25173 + 8453;
  return seed;
}

signed int srand(void)
{
  return (signed int) urand();
}

double fuzzing[] = { 0.0, 0.01, 0.25, 0.4, 0.5, 0.6, 0.75, 0.99 };

double fuzz(void)
{
  static unsigned int n = 0;
  n = n + 1;
  if (n >= sizeof(fuzzing) / sizeof(double)) n = 0;
  return fuzzing[n];
}

void test_signed_conv(void)
{
  int n = srand();
  double f = fuzz();
  double d = (double) n;
  double e = n < 0 ? d - f : d + f;
  int m = (int) e;
  if (m != n)
    printf("\nError: signed: %d, %g, %g, %d\n", n, f, e, m);
}

void test_unsigned_conv(void)
{
  unsigned int n = srand();
  double f = fuzz();
  double d = (double) n;
  double e = f + d;
  unsigned int m = (unsigned int) e;
  if (m != n)
    printf("\nError: unsigned: %u, %g, %g, %u\n", n, f, e, m);
}

int main()
{
  int i;
  for (i = 0; i < 1000000; i++) {
    if ((i % 1000) == 0) { printf("."); fflush(stdout); }
    test_signed_conv();
    test_unsigned_conv();
  }
  printf("\n");
  return 0;
}

