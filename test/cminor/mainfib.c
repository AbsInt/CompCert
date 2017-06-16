#include <stdlib.h>
#include <stdio.h>

extern int fib(int);

int main(int argc, char ** argv)
{
  int n, r;
  if (argc >= 2) n = atoi(argv[1]); else n = 30;
  r = fib(n);
  printf("fib(%d) = %d\n", n, r);
  return 0;
}
