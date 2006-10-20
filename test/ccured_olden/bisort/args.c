/* For copyright information, see olden_v1.0/COPYRIGHT */

#ifdef SS_PLAIN
#include "ssplain.h"
#endif SS_PLAIN

int mylog(int num)
{
  int j=0,k=1;
  
  while(k<num) { k*=2; j++; }
  return j;
} 

extern int flag;
int dealwithargs(int argc, char *argv[])
{
  int size;

  if (argc > 2)
    flag = atoi(argv[2]);
  else
    flag = 0;

  if (argc > 1)
    size = atoi(argv[1]);
  else
    size = 16;

  return size;  
}

