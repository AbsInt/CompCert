/* util.h
 *
 * headers for randomizing utilities 
 *
 * By: Martin C. Carlisle
 * Date: Feb 23, 1994
 *
 */

/* initialize the random number generator for a particular processor */
void init_random(int myid);

/* return a random number from 0 to range-1 */
int gen_number(int range);

/* return a random number in [-range+1,range-1] */
int gen_signed_number(int range);

/* Generate a double from 0.0 to 1.0 */
double gen_uniform_double();

/* Return 1, percent percent of the time and 0 otherwise */
int check_percent(int percent);
