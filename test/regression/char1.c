#include <stdio.h>
#include <limits.h>

int foo (char x) {
  char y = x;
  return ++x > y;
}

int main (void) {
  int i;
  for (i=CHAR_MIN; i<=CHAR_MAX; i++) {
    printf ("%d ", foo(i));
    if ((i&31)==31) printf ("\n");
  }
  return 0;
}
