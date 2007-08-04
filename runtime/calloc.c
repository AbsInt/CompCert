#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>

void * compcert_alloc(int sz)
{
  void * res = malloc(sz);
  if (res == NULL) {
    fprintf(stderr, "Out of memory in compcert_alloc().\n");
    abort();
  }
  return res;
}
