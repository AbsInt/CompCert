/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                STRING HANDLING                         * */
/* *                                                        * */
/* *  $Module:   STRINGS                                    * */ 
/* *                                                        * */
/* *  Copyright (C) 1999, 2000, 2001 MPI fuer Informatik    * */
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
/* $Revision: 35442 $                                        * */
/* $State$                                            * */
/* $Date: 2007-03-28 17:24:40 -0700 (Wed, 28 Mar 2007) $                             * */
/* $Author: jeffc $                                       * */
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

#ifndef _STRINGS_
#define _STRINGS_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include <math.h>
#include "memory.h"


/**************************************************************/
/* Functions                                                  */
/**************************************************************/

#ifdef __cplusplus
extern "C" {
#endif

static __inline__ BOOL string_Equal(const char* S1, const char* S2)
{
  return strcmp(S1, S2) == 0;
}


BOOL   string_StringIsNumber(const char*);
char*  string_StringCopy(const char*);
void   string_StringFree(char*);
char*  string_IntToString(int);
BOOL   string_StringToInt(const char*, BOOL, int*);
char*  string_Conc(const char*, const char*);
char*  string_Nconc(char*, char*);
char*  string_EmptyString(void);
char*  string_Prefix(const char*, int);
char*  string_Suffix(const char*, int);
char** string_Tokens(char*, int*);

#ifdef __cplusplus
}
#endif

#endif
