/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                     CLOCK                              * */
/* *                                                        * */
/* *  $Module:   CLOCK                                      * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1999, 2000, 2001                  * */
/* *  MPI fuer Informatik                                   * */
/* *                                                        * */
/* *  This program is free software; you can redistribute   * */
/* *  it and/or modify it under the terms of the GNU        * */
/* *  General Public License as published by the Free       * */
/* *  Software Foundation; either version 2 of the License, * */
/* *  or (at your option) any later version.                * */
/* *                                                        * */
/* *  This program is distributed in the hope that it will  * */
/* *  be useful, but WITHOUT ANY WARRANTY; without even     * */
/* *  the implied warranty of MERCHANTABILITY or FITNESS    * */
/* *  FOR A PARTICULAR PURPOSE.  See the GNU General Public * */
/* *  License for more details.                             * */
/* *                                                        * */
/* *  You should have received a copy of the GNU General    * */
/* *  Public License along with this program; if not, write * */
/* *  to the Free Software Foundation, Inc., 59 Temple      * */
/* *  Place, Suite 330, Boston, MA  02111-1307  USA         * */
/* *                                                        * */
/* *                                                        * */
/* $Revision: 21527 $                                        * */
/* $State$                                            * */
/* $Date: 2005-04-24 21:10:28 -0700 (Sun, 24 Apr 2005) $                             * */
/* $Author: duraid $                                       * */
/* *                                                        * */
/* *             Contact:                                   * */
/* *             Christoph Weidenbach                       * */
/* *             MPI fuer Informatik                        * */
/* *             Stuhlsatzenhausweg 85                      * */
/* *             66123 Saarbruecken                         * */
/* *             Email: weidenb@mpi-sb.mpg.de               * */
/* *             Germany                                    * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/


/* $RCSfile$ */

#include "clock.h"


/**************************************************************/
/* Global Variables                                           */
/**************************************************************/

float      clock_Akku[clock_TYPESIZE];
CLOCK_TMS  clock_Counters[clock_TYPESIZE];

#ifdef WIN
float      clock_Ping;
#endif

/**************************************************************/
/* Functions                                                  */
/**************************************************************/

void clock_Init(void)
/*********************************************************
  INPUT:   None.
  EFFECT:  Initializes the clock Module.
  RETURNS: None.
  MEMORY:  None.
**********************************************************/
{
  int i;

  for (i=0;i<clock_TYPESIZE;i++) {
    clock_InitCounter(i);
  }
#ifdef WIN
  clock_Ping = 0;
#endif
}



void clock_InitCounter(CLOCK_CLOCKS ClockCounter)
/*********************************************************
  INPUT:   A clock counter.
  EFFECT:  The clock counter <ClockCounter> is initialized.
  RETURNS: None.
  MEMORY:  None.
**********************************************************/
{
  clock_Akku[ClockCounter] = 0;
}


void clock_StartCounter(CLOCK_CLOCKS ClockCounter)
/*********************************************************
  INPUT:   A clock counter.
  EFFECT:  The clock counter <ClockCounter> is started.
  RETURNS: None.
  MEMORY:  None.
**********************************************************/
{
#ifndef CLOCK_NO_TIMING
  gettimeofday(&(clock_Counters[ClockCounter]), NULL);
#endif
}


void clock_StopPassedTime(CLOCK_CLOCKS ClockCounter) 
/*********************************************************
  INPUT:   A clock counter.
  EFFECT:  Stores the number of seconds passed since given
           counter was started in the according
	   accumulator.
  RETURNS: None.
  MEMORY:  None.
**********************************************************/
{
#ifndef CLOCK_NO_TIMING
  CLOCK_TMS    newtime;
  gettimeofday(&newtime, NULL);
  clock_Akku[ClockCounter] = clock_GetSeconds(ClockCounter);
#endif
}


void clock_StopAddPassedTime(CLOCK_CLOCKS ClockCounter) 
/*********************************************************
  INPUT:   A clock counter.
  EFFECT:  Adds the number of seconds passed since given
           counter was started to the according
	   accumulator.
  RETURNS: None.
  MEMORY:  None.
**********************************************************/
{
#ifndef CLOCK_NO_TIMING
  CLOCK_TMS    newtime;
  gettimeofday(&newtime, NULL);
  clock_Akku[ClockCounter] += clock_GetSeconds(ClockCounter);
#endif
}


float clock_GetSeconds(CLOCK_CLOCKS ClockCounter)
/*********************************************************
  INPUT:   A clock counter.
  EFFECT:  Computes the number of seconds spent by the
           counter.
  RETURNS: The number of seconds spent by the counter as
           a float.
  MEMORY:  None.
**********************************************************/
{
#ifndef CLOCK_NO_TIMING
  CLOCK_TMS    newtime;
  time_t       seconds_passed;
  long         microseconds_passed;

  gettimeofday(&newtime, NULL);

  seconds_passed = newtime.tv_sec - clock_Counters[ClockCounter].tv_sec;
  microseconds_passed = newtime.tv_usec - clock_Counters[ClockCounter].tv_usec;

  return ((float) seconds_passed
          + (microseconds_passed /(float)1000000));

#else /* CLOCK_NO_TIMING */
  return 0;
#endif /* ! CLOCK_NO_TIMING */

}

#ifdef WIN
void clock_PingOneSecond(void)
/*********************************************************
  INPUT:   None but assumes the clock_OVERALL to be properly
           initialized.
  EFFECT:  If between the previous call to this function or
           to clock_Init more one second is passed, the
	   function prints a "PING" to stdout.
	   Needed only for the windows implementation.
  CAUTION: Only needed to get around Windows95/98 scheduling
           problems.
**********************************************************/
{
  if (clock_GetSeconds(clock_OVERALL) > clock_Ping + 1) {
    clock_Ping++;
    puts("\n PING ");
  }
}
#endif



void clock_PrintTime(CLOCK_CLOCKS ClockCounter)
/*********************************************************
  INPUT:   A clock counter.
  EFFECT:  The time is printed in format hh:mm:ss.dd to stdout
  RETURNS: None.
  MEMORY:  None.
**********************************************************/
{
#ifndef CLOCK_NO_TIMING
  NAT   hours, minutes;
  float seconds;

  seconds   = clock_Akku[ClockCounter];
  hours     = (NAT)seconds/3600;
  seconds  -= hours*3600;
  minutes   = (NAT)seconds/60;
  seconds  -= (minutes*60);
  if (seconds >= 10.0)
    printf("%u:%02u:%2.2f",hours,minutes,seconds);
  else
    printf("%u:%02u:0%2.2f",hours,minutes,seconds);
#else
  fputs(" No Timing on this machine. ",stdout);
#endif
}
