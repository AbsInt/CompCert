/*  This is was originally a regression test for bug 43784 of gcc.
    See ISO/IEC 9899:TC3 §6.8.6.4p4 and footnote 139. */

#include <stdio.h>

struct s {
  unsigned char a[256];
};
union u {
  struct { struct s b; int c; } d;
  struct { int c; struct s b; } e;
};

static union u v;
static struct s *p = &v.d.b;
static struct s *q = &v.e.b;

static struct s __attribute__((noinline)) rp(void)
{
  return *p;
}

static void qp(void)
{
  *q = rp();
}

int main()
{
  int i;
  for (i = 0; i < 256; i++)
    p->a[i] = i;
  qp();
  for (i = 0; i < 256; i++)
    if (q->a[i] != i)
      printf("ERROR at %d: %d\n", i, q->a[i]);
  return 0;
}

