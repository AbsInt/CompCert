#include <stdlib.h>
#include <stdio.h>
#include <string.h>

extern void quicksort(int lo, int hi, long * data);

int cmplong(const void * i, const void * j)
{
  long vi = *((long *) i);
  long vj = *((long *) j);
  if (vi == vj) return 0;
  if (vi < vj) return -1;
  return 1;
}

int main(int argc, char ** argv)
{
  int n, i;
  long * a, * b;
  int bench = 0;

  if (argc >= 2) n = atoi(argv[1]); else n = 1000;
  if (argc >= 3) bench = 1;
  a = malloc(n * sizeof(long));
  b = malloc(n * sizeof(long));
  for (i = 0; i < n; i++) b[i] = a[i] = rand() & 0xFFFF;
  quicksort(0, n - 1, a);
  if (!bench) {
    qsort(b, n, sizeof(long), cmplong);
    for (i = 0; i < n; i++) {
      if (a[i] != b[i]) { printf("Bug!\n"); return 2; }
    }
    printf("OK\n");
  }
  return 0;
}
