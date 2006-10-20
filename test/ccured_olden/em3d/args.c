#include <stdio.h>
#include <stdlib.h>
#include "em3d.h"

void dealwithargs(int argc, char *argv[])
{
  if (argc > 1)
    n_nodes = atoi(argv[1]);
  else
    n_nodes = 10;

  if (argc > 2)
    d_nodes = atoi(argv[2]);
  else
    d_nodes = 3;

  if (argc > 3)
    iters = atoi(argv[3]);
  else
    iters = 100;
}
