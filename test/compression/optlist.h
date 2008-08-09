/***************************************************************************
*                       Command Line Option Parser
*
*   File    : optlist.h
*   Purpose : Header for getopt style command line option parsing
*   Author  : Michael Dipperstein
*   Date    : August 1, 2007
*
****************************************************************************
*   HISTORY
*
*   $Id: optlist.h,v 1.1.1.2 2007/09/04 04:45:42 michael Exp $
*   $Log: optlist.h,v $
*   Revision 1.1.1.2  2007/09/04 04:45:42  michael
*   Added FreeOptList.
*
*   Revision 1.1.1.1  2007/08/07 05:01:48  michael
*   Initial Release
*
****************************************************************************
*
* OptList: A command line option parsing library
* Copyright (C) 2007 by Michael Dipperstein (mdipper@alumni.engr.ucsb.edu)
*
* This file is part of the OptList library.
*
* OptList is free software; you can redistribute it and/or modify it
* under the terms of the GNU Lesser General Public License as published by
* the Free Software Foundation; either version 3 of the License, or (at
* your option) any later version.
*
* OptList is distributed in the hope that it will be useful, but
* WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser
* General Public License for more details.
*
* You should have received a copy of the GNU Lesser General Public License
* along with this program.  If not, see <http://www.gnu.org/licenses/>.
*
***************************************************************************/
#ifndef OPTLIST_H
#define OPTLIST_H

/***************************************************************************
*                             INCLUDED FILES
***************************************************************************/

/***************************************************************************
*                                 MACROS
***************************************************************************/

/***************************************************************************
*                                CONSTANTS
***************************************************************************/
#define    OL_NOINDEX    -1        /* this option has no arguement */

/***************************************************************************
*                            TYPE DEFINITIONS
***************************************************************************/
typedef struct option_t
{
    char option;
    char *argument;
    int argIndex;
    struct option_t *next;
} option_t;

/***************************************************************************
*                               PROTOTYPES
***************************************************************************/
option_t *GetOptList(int argc, char *const argv[], char *const options);
void FreeOptList(option_t *list);

#endif  /* ndef OPTLIST_H */
