#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>

struct cons { int hd; struct cons * tl; };
typedef struct cons * list;

extern list buildlist(int n);
extern list reverselist(list l);

int checklist(int n, list l)
{
  int i;
  for (i = 0; i <= n; i++) {
    if (l == NULL) return 0;
    if (l->hd != i) return 0;
    l = l->tl;
  }
  return (l == NULL);
}

int main(int argc, char ** argv)
{
  int n;

  if (argc >= 2) n = atoi(argv[1]); else n = 10;
  if (checklist(n, reverselist(buildlist(n)))) {
    printf("OK\n");
    return 0;
  } else {
    printf("Bug!\n");
    return 2;
  }
}

