/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                MISCELLANEOUS                           * */
/* *                                                        * */
/* *  $Module:   MISC                                       * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1998, 1999, 2000, 2001      * */
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

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "misc.h"

/**************************************************************/
/* Functions                                                  */
/**************************************************************/

#if 0
void misc_ErrorReport(const char * Format, ...)
{
  va_list args;
  va_start(args,Format);
  vfprintf(misc_ERROROUT,Format,args);
  va_end(args);
}

void misc_UserErrorReport(const char * Format, ...)
{
  va_list args;
  va_start(args,Format);
  vfprintf(misc_USERERROROUT,Format,args);
  va_end(args);
}
#endif

void misc_DumpCoreOut(const char* String)
/**************************************************************
  INPUT:   A  string.
  RETURNS: Nothing.
  EFFECT:  Prints <String> and then dumps a core.
***************************************************************/
{
  fprintf(stderr, "\n %s \n", String);
  misc_DumpCore();
}



int misc_ReturnValue(void)
{
  return 0;
}


int misc_Max(int a, int b)
{
  if (a > b)
    return a;
  else
    return b;
}

FILE* misc_OpenFile(const char* Name, const char* Mode)
/**************************************************************
  INPUT:   The name of a file and a string containing the mode
           for opening the file (see fopen(3)).
           Examples for Mode are "r" for reading and "w" for writing.
  RETURNS: The FILE pointer, if the file was successfully opened.
  EFFECT:  If it wasn't possible to open the file with the
           requested mode, an error message is printed and the
           program exits.
***************************************************************/
{
  FILE* File;

  File = fopen(Name,Mode);

  if (File == (FILE*)NULL) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n\tError in opening file %s for %s !\n\n", Name, 
			 (Mode[0] == 'r' ? "reading" :
			  (Mode[0] == 'w' ? "writing" : "i/o operations")));
    misc_FinishUserErrorReport();
  }  

  return File;
}

void misc_CloseFile(FILE* File, const char* Name)
/**************************************************************
  INPUT:   A FILE and its name.
  RETURNS: Nothing.
  EFFECT:  Closes the file. If an error occurs, a message is
           printed and the program exits.
***************************************************************/
{
  int Result;

  Result = fclose(File);

  if (Result != 0) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n\tError in closing file %s !\n\n", Name);
    misc_FinishUserErrorReport();
  }  
}

