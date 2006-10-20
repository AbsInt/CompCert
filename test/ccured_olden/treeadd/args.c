/* For copyright information, see olden_v1.0/COPYRIGHT */

#ifdef SS_PLAIN
#include "ssplain.h"
#else SS_PLAIN
#include <cm/cmmd.h>
#include <fcntl.h>

extern int __NumNodes;
#endif SS_PLAIN

#include "tree.h"

void filestuff()
{
#ifndef SS_PLAIN
  CMMD_fset_io_mode(stdout, CMMD_independent);
  fcntl(fileno(stdout), F_SETFL, O_APPEND);
  if (CMMD_self_address()) exit(0);
  __InitRegs(0);
#endif SS_PLAIN
}

int level; 
int iters;

int dealwithargs(int argc, char *argv[])
{
#ifndef SS_PLAIN
  if (argc > 3) 
    __NumNodes = atoi(argv[2]);
  else 
    __NumNodes = 4;
#endif SS_PLAIN

  if (argc > 2)
    iters = atoi(argv[2]);
  else
    iters = 1;

  if (argc > 1)
    level = atoi(argv[1]);
  else
    level = 5;

  return level;
}
