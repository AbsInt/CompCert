#define CONST_seed 45
#include <stdlib.h>

/* initialize the random number generator for a particular processor */
void init_random(int myid)
{
  srand48(myid*CONST_seed);
}

/* return a random number from 0 to range-1 */
int gen_number(int range)
{
  return lrand48() % range;
}

/* return a random number in [-range+1,range-1] */
int gen_signed_number(int range)
{
  int temp;
 
  temp = lrand48() % (2*range-1);  /* 0..2*range-2 */
  return temp-(range-1);
}

/* Generate a double from 0.0 to 1.0 */
double gen_uniform_double()
{
  return drand48();
}

int check_percent(int percent)
{
  return (drand48() < (double) (percent/100.0));
}
