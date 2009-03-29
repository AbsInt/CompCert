
/* VA.C: The program below illustrates passing a variable
 * number of arguments using the following macros:
 *      va_start            va_arg              va_end
 *      va_list             va_dcl (UNIX only)
 */

#include <stdio.h>
#include <stdarg.h>
int average( int first, ... );
union vararg_average {
  int ints;                   /* We only pass ints to this one */
};

#include "testharness.h"

int main( void )
{
   /* Call with 3 integers (-1 is used as terminator). */
  if(average( 2, 3, 4, -1 ) != 3) E(1);
  if(average( 5, 7, 9, 11, 13, -1 ) != 9) E(2);
  if(average( -1 ) != 0) E(3);

   SUCCESS;
}



/* Returns the average of a variable list of integers. */
int average( int first, ... )
{
   int count = 0, sum = 0, i = first;
   va_list marker;

   va_start( marker, first );     /* Initialize variable arguments. */
   while( i != -1 )
   {
      sum += i;
      count++;
      i = va_arg( marker, int);
   }
   va_end( marker );              /* Reset variable arguments.      */
   return( sum ? (sum / count) : 0 );
}

// Put this intentionally at the end
#pragma ccuredvararg("average", sizeof(union vararg_average))
