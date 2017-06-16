/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *              SPASS OPTIONS HANDLING                    * */
/* *                                                        * */
/* *  $Module:    OPTIONS                                   * */ 
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


#ifndef _OPTIONS_
#define _OPTIONS_

#include <string.h>
#include <stdlib.h>
#include <stdio.h>

#include "flags.h"
#include "list.h"


/**************************************************************/
/* Data Structures and Constants                              */
/**************************************************************/

/* option type */
typedef int OPTTYPE;

#define	opts_NOARGTYPE		0 /* no argument       */
#define opts_REQARGTYPE	        1 /* required argument */
#define opts_OPTARGTYPE         2 /* optional argument */

/* option id   */
typedef int OPTID;
#define opts_IDFIRST            0 /* option id to start with      */

/* struct for declaration of options */
typedef struct {
  char*   clname;      /* option name in the command line        */
  OPTTYPE type;        /* argument type: required, optional, non */
} OPTDECL;

#define opts_ENDMARKER "--"     /* double hyphen: marks end of all options */
#define opts_DEFAULTOPTARG  "1" /* default value of options with optional arguments */

/**************************************************************
 from the getopt.h file 
 **************************************************************/
struct OPTION
{
  char *name;

  /* has_arg can't be an enum because some compilers complain about
     type mismatches in all the code that assumes it is an int.  */
  int has_arg;
  int *flag;
  int val;
};


/**************************************************************/
/* Functions                                                  */
/**************************************************************/

void        opts_Init(void);
void        opts_Free(void);
OPTID       opts_DeclareVector(OPTDECL []);
OPTID       opts_Declare(const char*, OPTTYPE);
BOOL        opts_Read(int, const char* []);
BOOL        opts_ReadOptionsFromString(const char*);
int         opts_Indicator(void);

BOOL        opts_IsSet(OPTID);
BOOL        opts_GetIntValueByName(const char*, int*);
BOOL        opts_GetValueByName(const char*, const char**);
BOOL        opts_GetValue(OPTID, const char**);
BOOL        opts_GetIntValue(OPTID, int*) ;

const char* opts_ClName(OPTID);
OPTID       opts_IdFirst(void);
OPTID       opts_Id(const char*);
BOOL        opts_IdIsNull(OPTID);

/* specials for SPASS */
void        opts_Transfer(FLAGSTORE);
void        opts_SetFlags(FLAGSTORE);
void        opts_DeclareSPASSFlagsAsOptions(void);
void        opts_PrintSPASSNames(void);

#endif
