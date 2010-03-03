#include <stdio.h>

struct value {
  int tag;
  union {
    int i;
    double r;
    char * sl;
  } u;
};

void print_value(struct value * s)
{
  printf ("%d\n", s->u.i);
}

    
