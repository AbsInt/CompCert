#include <stdlib.h>
#include <stdio.h>

extern double test(int);

int main(int argc, char ** argv)
{
  int n; double r;
  if (argc >= 2) n = atoi(argv[1]); else n = 10000;
  r = test(n);
  printf("integr(square, 0.0, 1.0, %d) = %g\n", n, r);
  return 0;
}
