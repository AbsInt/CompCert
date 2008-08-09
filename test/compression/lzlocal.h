/***************************************************************************
*          Lempel, Ziv, Storer, and Szymanski Encoding and Decoding
*
*   File    : lzlocal.h
*   Purpose : Internal headers for LZSS encode and decode routines.
*             Contains the prototypes to be used by the different match
*             finding algorithms.
*   Author  : Michael Dipperstein
*   Date    : February 18, 2004
*
****************************************************************************
*   UPDATES
*
*   $Id: lzlocal.h,v 1.5 2007/09/20 04:34:25 michael Exp $
*   $Log: lzlocal.h,v $
*   Revision 1.5  2007/09/20 04:34:25  michael
*   Changes required for LGPL v3.
*
*   Revision 1.4  2006/12/26 04:09:09  michael
*   Updated e-mail address and minor text clean-up.
*
*   Revision 1.3  2005/12/28 05:58:52  michael
*   Add Wrap macro to replace mod when value is less than twice the limit.
*
*   Revision 1.2  2004/11/08 05:54:18  michael
*   1. Split encode and decode routines for smarter linking
*   2. Renamed lzsample.c sample.c to match my other samples
*   3. Makefile now builds code as libraries for better LGPL compliance.
*
*   Revision 1.1  2004/02/22 17:32:40  michael
*   Initial revision of header files for sliding window search implementations.
*
*
****************************************************************************
*
* LZSS: An ANSI C LZSS Encoding/Decoding Routine
* Copyright (C) 2004-2007 by
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
#ifndef _LZSS_LOCAL_H
#define _LZSS_LOCAL_H

/***************************************************************************
*                             INCLUDED FILES
***************************************************************************/
#include <limits.h>

/***************************************************************************
*                                CONSTANTS
***************************************************************************/
#define FALSE   0
#define TRUE    1

#define OFFSET_BITS     12
#define LENGTH_BITS     4

#if (((1 << (OFFSET_BITS + LENGTH_BITS)) - 1) > UINT_MAX)
#error "Size of encoded data must not exceed the size of an unsigned int"
#endif

/* We want a sliding window*/
#define WINDOW_SIZE     (1 << OFFSET_BITS)

/* maximum match length not encoded and maximum length encoded (4 bits) */
#define MAX_UNCODED     2
#define MAX_CODED       ((1 << LENGTH_BITS) + MAX_UNCODED)

#define ENCODED     0       /* encoded string */
#define UNCODED     1       /* unencoded character */

/***************************************************************************
*                            TYPE DEFINITIONS
***************************************************************************/

/***************************************************************************
* This data structure stores an encoded string in (offset, length) format.
* The actual encoded string is stored using OFFSET_BITS for the offset and
* LENGTH_BITS for the length.
***************************************************************************/
typedef struct encoded_string_t
{
    unsigned int offset;    /* offset to start of longest match */
    unsigned int length;    /* length of longest match */
} encoded_string_t;

/***************************************************************************
*                                 MACROS
***************************************************************************/
/* wraps array index within array bounds (assumes value < 2 * limit) */
#if 0
#define Wrap(value, limit)      (((value) < (limit)) ? (value) : ((value) - (limit)))
#else
#define Wrap(value, limit)   ((unsigned int)(value) % (unsigned int)(limit))
#endif

/***************************************************************************
*                               PROTOTYPES
***************************************************************************/
void InitializeSearchStructures(void);

/* XL: no struct return */
void FindMatch(encoded_string_t * /*out*/,
               unsigned int windowHead, unsigned int uncodedHead);

void ReplaceChar(unsigned int charIndex, unsigned char replacement);

#endif      /* ndef _LZSS_LOCAL_H */
