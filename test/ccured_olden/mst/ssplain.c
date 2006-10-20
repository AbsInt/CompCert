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

