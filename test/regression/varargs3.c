#include <stdarg.h>
#include <stdio.h>

void initialize(int first, ...)
{
  va_list ap;
  va_start(ap, first);
  while (1) {
    int * p = va_arg(ap, int *);
    if (p == NULL) break;
    *p = first;
    first++;
  }
}

void test(void)
{
  int a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q;
  initialize(42, &a, &b, &c, &d, &e, &f, &g, &h, &i, &j,
             &k, &l, &m, &n, &o, &p, &q, NULL);
  printf("a = %d\n", a);
  printf("b = %d\n", b);
  printf("c = %d\n", c);
  printf("d = %d\n", d);
  printf("e = %d\n", e);
  printf("f = %d\n", f);
  printf("g = %d\n", g);
  printf("h = %d\n", h);
  printf("i = %d\n", i);
  printf("j = %d\n", j);
  printf("k = %d\n", k);
  printf("l = %d\n", l);
  printf("m = %d\n", m);
  printf("n = %d\n", n);
  printf("o = %d\n", o);
  printf("p = %d\n", p);
  printf("q = %d\n", q);
}

void wipestack(void)
{
  unsigned int b[100];
  int i;
  for (i = 0; i < 100; i++) ((volatile unsigned int *)b)[i] = 0xDEADBEEFU;
}

int main()
{
  wipestack();
  test();
  return 0;
}
