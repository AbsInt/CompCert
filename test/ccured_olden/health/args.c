/* For copyright information, see olden_v1.0/COPYRIGHT */

/*****************************************************************
 * args.c:  Handles arguments to command line.                   *
 *          To be used with health.c.                            *
 *****************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include "health.h"

#ifdef SS_PLAIN
#include "ssplain.h"
#endif SS_PLAIN

void dealwithargs(int argc, char *argv[]) { 

  if (argc < 4) 
    {
      fprintf(stderr, "usage:  health <# levels> <time> <seed>\n");
      exit(1); 
    }
  
  max_level = atoi(argv[1]);
  fprintf(stderr, "This is max_level : %d\n", max_level);
  max_time = atol(argv[2]);
  fprintf(stderr, "This is max_time : %ld\n", max_time);    // sm: "%d" -> "%ld"
  seed = atol(argv[3]);
}





