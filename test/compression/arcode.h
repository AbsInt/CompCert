/***************************************************************************
*            Header for Arithmetic Encoding and Decoding Library
*
*   File    : arcode.h
*   Purpose : Provides prototypes for functions that use arithmetic coding
*             to encode/decode files.
*   Author  : Michael Dipperstein
*   Date    : April 2, 2004
*
****************************************************************************
*   UPDATES
*
*   $Id: arcode.h,v 1.3 2007/09/08 15:47:02 michael Exp $
*   $Log: arcode.h,v $
*   Revision 1.3  2007/09/08 15:47:02  michael
*   Changes required for LGPL v3.
*
*   Revision 1.2  2004/08/13 13:09:46  michael
*   Add support for adaptive encoding
*
*   Revision 1.1.1.1  2004/04/04 14:54:13  michael
*   Initial version
*
****************************************************************************
*
* Arcode: An ANSI C Arithmetic Encoding/Decoding Routines
* Copyright (C) 2004, 2006-2007 by Michael Dipperstein (mdipper@cs.ucsb.edu)
*
* This file is part of the arcode library.
*
* The arcode library is free software; you can redistribute it and/or
* modify it under the terms of the GNU Lesser General Public License as
* published by the Free Software Foundation; either version 3 of the
* License, or (at your option) any later version.
*
* The arcode library is distributed in the hope that it will be useful,
* but WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser
* General Public License for more details.
*
* You should have received a copy of the GNU Lesser General Public License
* along with this program.  If not, see <http://www.gnu.org/licenses/>.
*
***************************************************************************/

#ifndef _ARCODE_H_
#define _ARCODE_H_

/***************************************************************************
*                                CONSTANTS
***************************************************************************/
#ifndef FALSE
#define FALSE       0
#endif

#ifndef TRUE
#define TRUE        1
#endif

/***************************************************************************
*                               PROTOTYPES
***************************************************************************/
 /* encode inFile */
int ArEncodeFile(char *inFile, char *outFile, char staticModel);

/* decode inFile*/
int ArDecodeFile(char *inFile, char *outFile, char staticModel);

#endif  /* ndef _ARCODE_H_ */
