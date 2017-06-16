/***************************************************************************
*                 Lempel, Ziv, Storer, and Szymanski Encoding
*
*   File    : lzdecode.c
*   Purpose : Use lzss coding (Storer and Szymanski's modified LZ77) to
*             compress lzss data files.
*   Author  : Michael Dipperstein
*   Date    : November 07, 2004
*
****************************************************************************
*   UPDATES
*
*   Date        Change
*   12/10/03    Changed handling of sliding window to better match standard
*               algorithm description.
*   12/11/03    Remebered to copy encoded characters to the sliding window
*               even when there are no more characters in the input stream.
*
*
*   Revision 1.2  2004/02/22 17:14:26  michael
*   - Separated encode/decode, match finding, and main.
*   - Use bitfiles for reading/writing files
*   - Use traditional LZSS encoding where the coded/uncoded bits
*     precede the symbol they are associated with, rather than
*     aggregating the bits.
*
*   Revision 1.1.1.1  2004/01/21 06:25:49  michael
*   Initial version
*
*   11/07/04    Separated encode and decode functions for improved
*               modularity.
*
*   $Id: lzencode.c,v 1.6 2007/09/20 04:34:25 michael Exp $
*   $Log: lzencode.c,v $
*   Revision 1.6  2007/09/20 04:34:25  michael
*   Changes required for LGPL v3.
*
*   Revision 1.5  2007/03/25 05:11:32  michael
*   Corrected file closure error reported by "Carl@Yahoo" .  Now  both input
*   and output files are closed.
*
*   Revision 1.4  2006/12/26 04:09:09  michael
*   Updated e-mail address and minor text clean-up.
*
*   Revision 1.3  2005/12/28 06:03:30  michael
*   Use slower but clearer Get/PutBitsInt for reading/writing bits.
*   Replace mod with conditional Wrap macro.
*
*   Revision 1.2  2004/11/13 22:51:00  michael
*   Provide distinct names for by file and by name functions and add some
*   comments to make their usage clearer.
*
*   Revision 1.1  2004/11/08 05:54:18  michael
*   1. Split encode and decode routines for smarter linking
*   2. Renamed lzsample.c sample.c to match my other samples
*   3. Makefile now builds code as libraries for better LGPL compliance.
*
*
*
****************************************************************************
*
* LZEncode: An ANSI C LZSS Encoding Routines
* Copyright (C) 2003-2007 by
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

/***************************************************************************
*                             INCLUDED FILES
***************************************************************************/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "lzlocal.h"
#include "bitfile.h"

/***************************************************************************
*                            TYPE DEFINITIONS
***************************************************************************/

/***************************************************************************
*                                CONSTANTS
***************************************************************************/

/***************************************************************************
*                            GLOBAL VARIABLES
***************************************************************************/
/* cyclic buffer sliding window of already read characters */
extern unsigned char slidingWindow[];
extern unsigned char uncodedLookahead[];

/***************************************************************************
*                               PROTOTYPES
***************************************************************************/

/***************************************************************************
*                                FUNCTIONS
***************************************************************************/

/****************************************************************************
*   Function   : EncodeLZSSByFile
*   Description: This function will read an input file and write an output
*                file encoded according to the traditional LZSS algorithm.
*                This algorithm encodes strings as 16 bits (a 12 bit offset
*                + a 4 bit length).
*   Parameters : fpIn - pointer to the open binary file to encode
*                fpOut - pointer to the open binary file to write encoded
*                       output
*   Effects    : fpIn is encoded and written to fpOut.  Neither file is
*                closed after exit.
*   Returned   : EXIT_SUCCESS or EXIT_FAILURE
****************************************************************************/
int EncodeLZSSByFile(FILE *fpIn, FILE *fpOut)
{
    bit_file_t *bfpOut;

    encoded_string_t matchData;
    unsigned int i, c;
    unsigned int len;                       /* length of string */

    /* head of sliding window and lookahead */
    unsigned int windowHead, uncodedHead;

    /* use stdin if no input file */
    if (fpIn == NULL)
    {
        fpIn = stdin;
    }

    if (fpOut == NULL)
    {
        /* use stdout if no output file */
        bfpOut = MakeBitFile(stdout, BF_WRITE);
    }
    else
    {
        /* convert output file to bitfile */
        bfpOut = MakeBitFile(fpOut, BF_WRITE);
    }

    windowHead = 0;
    uncodedHead = 0;

    /************************************************************************
    * Fill the sliding window buffer with some known vales.  DecodeLZSS must
    * use the same values.  If common characters are used, there's an
    * increased chance of matching to the earlier strings.
    ************************************************************************/
    memset(slidingWindow, ' ', WINDOW_SIZE * sizeof(unsigned char));

    /************************************************************************
    * Copy MAX_CODED bytes from the input file into the uncoded lookahead
    * buffer.
    ************************************************************************/
    for (len = 0; len < MAX_CODED; len++) {
        c = getc(fpIn);
        if (c == EOF) break;
        uncodedLookahead[len] = c;
    }

    if (len == 0)
    {
        return (EXIT_SUCCESS);   /* inFile was empty */
    }

    /* Look for matching string in sliding window */
    InitializeSearchStructures();
    FindMatch(&matchData, windowHead, uncodedHead);

    /* now encoded the rest of the file until an EOF is read */
    while (len > 0)
    {
        if (matchData.length > len)
        {
            /* garbage beyond last data happened to extend match length */
            matchData.length = len;
        }

        if (matchData.length <= MAX_UNCODED)
        {
            /* not long enough match.  write uncoded flag and character */
            BitFilePutBit(UNCODED, bfpOut);
            BitFilePutChar(uncodedLookahead[uncodedHead], bfpOut);

            matchData.length = 1;   /* set to 1 for 1 byte uncoded */
        }
        else
        {
            unsigned int adjustedLen;

            /* adjust the length of the match so minimun encoded len is 0*/
            adjustedLen = matchData.length - (MAX_UNCODED + 1);

            /* match length > MAX_UNCODED.  Encode as offset and length. */
            BitFilePutBit(ENCODED, bfpOut);
            BitFilePutBitsInt(bfpOut, &matchData.offset, OFFSET_BITS,
                sizeof(unsigned int));
            BitFilePutBitsInt(bfpOut, &adjustedLen, LENGTH_BITS,
                sizeof(unsigned int));
        }

        /********************************************************************
        * Replace the matchData.length worth of bytes we've matched in the
        * sliding window with new bytes from the input file.
        ********************************************************************/
        i = 0;
        while ((i < matchData.length) && ((c = getc(fpIn)) != EOF))
        {
            /* add old byte into sliding window and new into lookahead */
            ReplaceChar(windowHead, uncodedLookahead[uncodedHead]);
            uncodedLookahead[uncodedHead] = c;
            windowHead = Wrap((windowHead + 1), WINDOW_SIZE);
            uncodedHead = Wrap((uncodedHead + 1), MAX_CODED);
            i++;
        }

        /* handle case where we hit EOF before filling lookahead */
        while (i < matchData.length)
        {
            ReplaceChar(windowHead, uncodedLookahead[uncodedHead]);
            /* nothing to add to lookahead here */
            windowHead = Wrap((windowHead + 1), WINDOW_SIZE);
            uncodedHead = Wrap((uncodedHead + 1), MAX_CODED);
            len--;
            i++;
        }

        /* find match for the remaining characters */
        FindMatch(&matchData, windowHead, uncodedHead);
    }

    /* we've decoded everything, free bitfile structure */
    BitFileToFILE(bfpOut);

   return (EXIT_SUCCESS);
}

/****************************************************************************
*   Function   : EncodeLZSSByName
*   Description: This function is provided to maintain compatibility with
*                older versions of my LZSS implementation which used file
*                names instead of file pointers.
*   Parameters : inFile - name of file to encode
*                outFile - name of file to write encoded output
*   Effects    : inFile is encoded and written to outFile
*   Returned   : EXIT_SUCCESS or EXIT_FAILURE
****************************************************************************/
int EncodeLZSSByName(char *inFile, char *outFile)
{
    FILE *fpIn, *fpOut;
    int returnValue;

    /* open binary input and output files */
    if (inFile == NULL)
    {
        fpIn = stdin;
    }
    if ((fpIn = fopen(inFile, "rb")) == NULL)
    {
        perror(inFile);
        return (EXIT_FAILURE);
    }

    if (outFile == NULL)
    {
        fpOut = stdout;
    }
    else
    {
        if ((fpOut = fopen(outFile, "wb")) == NULL)
        {
            fclose(fpIn);
            perror(outFile);
            return (EXIT_FAILURE);
        }
    }

    returnValue = EncodeLZSSByFile(fpIn, fpOut);

    /* close files */
    fclose(fpIn);
    fclose(fpOut);

    return (returnValue);
}
