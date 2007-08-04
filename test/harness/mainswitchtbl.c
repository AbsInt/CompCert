#include <stdlib.h>
#include <stdio.h>

extern int f(int);

int main(int argc, char ** argv)
{
  int i;
  for (i = 0; i < 10; i++) printf("%2d -> %2d\n", i, f(i));
  return 0;
}
