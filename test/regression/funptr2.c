/* Comparisons of pointers to functions */

#include <stdio.h>

int f(void) { return 0; }
int g(void) { return 1; }

int main(void) {
  printf ("f == f is %d\n", &f == &f);
  printf ("f == g is %d\n", &f == &g);
  /* The following is undefined behavior */
  printf ("f + 2 == f is %d\n", ((char *) &f) + 2 == (char *) &f);
  return 0;
}
