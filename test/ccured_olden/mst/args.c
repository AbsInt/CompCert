/* For copyright information, see olden_v1.0/COPYRIGHT */

#ifdef SS_PLAIN
#include "ssplain.h"
#include "mst.h"
#endif SS_PLAIN


int dealwithargs(int argc, char *argv[])
{
  int level;

  if (argc > 1)
    level = atoi(argv[1]);
  else
    level = 1024;

  return level;
}

