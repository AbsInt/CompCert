/***************************************************************************
*          Lempel, Ziv, Storer, and Szymanski Encoding and Decoding
*
*   File    : lzss.h
*   Purpose : Header for LZSS encode and decode routines.  Contains the
*             prototypes to be used by programs linking to the LZSS
*             library.
*   Author  : Michael Dipperstein
*   Date    : February 21, 2004
*
****************************************************************************
*   UPDATES
*
*   $Id: lzss.h,v 1.5 2007/09/20 04:34:25 michael Exp $
*   $Log: lzss.h,v $
*   Revision 1.5  2007/09/20 04:34:25  michael
*   Changes required for LGPL v3.
*
*   Revision 1.4  2006/12/26 04:09:09  michael
*   Updated e-mail address and minor text clean-up.
*
*   Revision 1.3  2004/11/13 22:51:00  michael
*   Provide distinct names for by file and by name functions and add some
*   comments to make their usage clearer.
*
*   Revision 1.2  2004/11/08 05:54:18  michael
*   1. Split encode and decode routines for smarter linking
*   2. Renamed lzsample.c sample.c to match my other samples
*   3. Makefile now builds code as libraries for better LGPL compliance.
*
*   Revision 1.1  2004/02/22 17:37:50  michael
*   Initial revision of headers for encode and decode routines.
*
*
****************************************************************************
*
* LZSS: An ANSI C LZSS Encoding/Decoding Routine
* Copyright (C) 2004, 2006, 2007 by
* Michael Dipperstein (mdipper@alumni.engr.ucsb.edu)
*
* This file is part of the lzss library.
*
* The lzss library is free software; you can redistribute it and/or
* modify it under the terms of the GNU Lesser General Public License as
* published by the Free Software Foundation; either version 3 of the
* License, or (at your option) any later version.
*
* The lzss library is distributed in the hope that it will be useful, but
* WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser
* General Public License for more details.
*
* You should have received a copy of the GNU Lesser General Public License
* along with this program.  If not, see <http://www.gnu.org/licenses/>.
*
***************************************************************************/
#ifndef _LZSS_H
#define _LZSS_H

/***************************************************************************
*                             INCLUDED FILES
***************************************************************************/
#include <stdio.h>

/***************************************************************************
*                                 MACROS
***************************************************************************/
/* macros for compatibility with older library */
#define EncodeLZSS(in, out)     EncodeLZSSByName((in), (out))
#define DecodeLZSS(in, out)     DecodeLZSSByName((in), (out))

/***************************************************************************
*                               PROTOTYPES
***************************************************************************/
/***************************************************************************
* LZSS encoding and decoding prototypes for functions with file name
* parameters.  Provide these functions with name of the file to be
* encoded/decoded (inFile) and the name of the target file (outFile).
* These functions return EXIT_SUCCESS or EXIT_FAILURE.
***************************************************************************/
int EncodeLZSSByName(char *inFile, char *outFile);
int DecodeLZSSByName(char *inFile, char *outFile);

/***************************************************************************
* LZSS encoding and decoding prototypes for functions with file pointer
* parameters.  Provide these functions with a pointer to the open binary
* file to be encoded/decoded (fpIn) and pointer to the open binary target
* file (fpOut).  It is the job of the function caller to open the files
* prior to callings these functions and to close the file after these
* functions have been called.
* These functions return EXIT_SUCCESS or EXIT_FAILURE.
***************************************************************************/
int EncodeLZSSByFile(FILE *fpIn, FILE *fpOut);
int DecodeLZSSByFile(FILE *fpIn, FILE *fpOut);

#endif      /* ndef _LZSS_H */
