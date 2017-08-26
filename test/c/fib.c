#include <stdlib.h>
#include <stdio.h>

int fib(int n)
{
  if (n < 2) 
    return 1;
  else
    return fib(n-1) + fib(n-2);
}

int main(int argc, char ** argv)
{
  int n, r;
  if (argc >= 2) n = atoi(argv[1]); else n = 35;
  r = fib(n);
  printf("fib(%d) = %d\n", n, r);
  return 0;
}
