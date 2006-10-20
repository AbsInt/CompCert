/* For copyright information, see olden_v1.0/COPYRIGHT */

/**********************************************************
 * poisson.c: handles math routines for health.c          *
 **********************************************************/

#include <stdio.h>
#include <math.h>
#include "health.h"


float my_rand(long idum) 
{
  long                   k;
  float                  answer;
  
  idum ^= MASK;
  k = idum / IQ;
  idum = IA * (idum - k * IQ) - IR * k;
  idum ^= MASK;
  if (idum < 0) 
    idum  += IM;
  answer = AM * idum;
#ifdef GET_OUT
  fprintf(stderr, "my_rand: idum = %d, AM = %e, answer = %4.3f\n", 
	  idum, AM, answer);
#endif GET_OUT
  return answer; 
}






