#include <stdio.h>

struct list { int hd; struct list * tl; };

struct list * f(struct list ** p)
{
  return ((*p)->tl = 0);
}

int main()
{
  struct list l;
  l.tl = &l;
  f(&(l.tl));
  printf("Result: %d\n", (int) l.tl);
  return 0;
}
