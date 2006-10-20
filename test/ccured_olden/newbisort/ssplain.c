#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <limits.h>
#include <stddef.h>
#include "ssplain.h"

void chatting(char *s, ...)
{
  va_list ap;
  va_start(ap,s);
  vfprintf(stderr, s, ap);
  va_end(ap);
}

void __Olden_panic(char *s, ...)
{
  va_list ap;
  va_start(ap,s);
  vfprintf(stderr, s, ap);
  va_end(ap);
  exit(-1);
}

#ifdef SS_RAND
double drand48()
{
  double d;
  d = (double) random() / LONG_MAX;
  return d;
}


long lrand48()
{
  long l = random();
  return l;
}

void srand48(long seed)
{
  srand(seed);
}
#endif SS_RAND


static unsigned long bytes_allocated = 0;
static unsigned long allocations = 0;

void*
ssplain_malloc(int size)
{
  allocations++;
  bytes_allocated+=size;
  return malloc(size);
}

void*
ssplain_calloc(int nelems, int size)
{
  void *p;
  allocations++;
  bytes_allocated+= nelems * size;
  p =  calloc(nelems, size);
  assert (p);
  return p;
}

void
ssplain_alloc_stats()
{
  chatting("Allocation stats: %d bytes allocated in %d allocations\n",
	   bytes_allocated, allocations);
}
