/***************************************************************************
*                 Lempel, Ziv, Storer, and Szymanski Decoding
*
*   File    : lzdecode.c
*   Purpose : Use lzss coding (Storer and Szymanski's modified LZ77) to
*             decompress lzss  encoded files.
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
*   $Id: lzdecode.c,v 1.7 2007/09/20 04:34:25 michael Exp $
*   $Log: lzdecode.c,v $
*   Revision 1.7  2007/09/20 04:34:25  michael
*   Changes required for LGPL v3.
*
*   Revision 1.6  2007/03/25 05:11:32  michael
*   Corrected file closure error reported by "Carl@Yahoo" .  Now  both input
*   and output files are closed.
*
*   Revision 1.5  2006/12/26 04:09:09  michael
*   Updated e-mail address and minor text clean-up.
*
*   Revision 1.4  2006/12/26 02:05:00  michael
*   Corrected bug identified by Andrej Sinicyn which resulted in stdin being
*   used as the default output for decoded data.
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
* LZDecode: An ANSI C LZSS Decoding Routines
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
*   Function   : DecodeLZSSByFile
*   Description: This function will read an LZSS encoded input file and
*                write an output file.  This algorithm encodes strings as 16
*                bits (a 12 bit offset + a 4 bit length).
*   Parameters : fpIn - pointer to the open binary file to decode
*                fpOut - pointer to the open binary file to write decoded
*                       output
*   Effects    : fpIn is decoded and written to fpOut.  Neither file is
*                closed after exit.
*   Returned   : EXIT_SUCCESS or EXIT_FAILURE
****************************************************************************/
int DecodeLZSSByFile(FILE *fpIn, FILE *fpOut)
{
    bit_file_t *bfpIn;

    int c;
    unsigned int i, nextChar;
    encoded_string_t code;              /* offset/length code for string */

    if (fpIn == NULL)
    {
        /* use stdin if no input file */
        bfpIn = MakeBitFile(stdin, BF_READ);
    }
    else
    {
        /* convert output file to bitfile */
        bfpIn = MakeBitFile(fpIn, BF_READ);
    }

    /* use stdout if no output file */
    if (fpOut == NULL)
    {
        fpOut = stdout;
    }

    /************************************************************************
    * Fill the sliding window buffer with some known vales.  EncodeLZSS must
    * use the same values.  If common characters are used, there's an
    * increased chance of matching to the earlier strings.
    ************************************************************************/
    memset(slidingWindow, ' ', WINDOW_SIZE * sizeof(unsigned char));

    nextChar = 0;

    while (TRUE)
    {
        if ((c = BitFileGetBit(bfpIn)) == EOF)
        {
            /* we hit the EOF */
            break;
        }

        if (c == UNCODED)
        {
            /* uncoded character */
            if ((c = BitFileGetChar(bfpIn)) == EOF)
            {
                break;
            }

            /* write out byte and put it in sliding window */
            putc(c, fpOut);
            slidingWindow[nextChar] = c;
            nextChar = Wrap((nextChar + 1), WINDOW_SIZE);
        }
        else
        {
            /* offset and length */
            code.offset = 0;
            code.length = 0;

            if ((BitFileGetBitsInt(bfpIn, &code.offset, OFFSET_BITS,
                sizeof(unsigned int))) == EOF)
            {
                break;
            }

            if ((BitFileGetBitsInt(bfpIn, &code.length, LENGTH_BITS,
                sizeof(unsigned int))) == EOF)
            {
                break;
            }

            code.length += MAX_UNCODED + 1;

            /****************************************************************
            * Write out decoded string to file and lookahead.  It would be
            * nice to write to the sliding window instead of the lookahead,
            * but we could end up overwriting the matching string with the
            * new string if abs(offset - next char) < match length.
            ****************************************************************/
            for (i = 0; i < code.length; i++)
            {
                c = slidingWindow[Wrap((code.offset + i), WINDOW_SIZE)];
                putc(c, fpOut);
                uncodedLookahead[i] = c;
            }

            /* write out decoded string to sliding window */
            for (i = 0; i < code.length; i++)
            {
                slidingWindow[(nextChar + i) % WINDOW_SIZE] =
                    uncodedLookahead[i];
            }

            nextChar = Wrap((nextChar + code.length), WINDOW_SIZE);
        }
    }

    /* we've decoded everything, free bitfile structure */
    BitFileToFILE(bfpIn);

    return (EXIT_SUCCESS);
}

/****************************************************************************
*   Function   : DecodeLZSSByName
*   Description: This function is provided to maintain compatibility with
*                older versions of my LZSS implementation which used file
*                names instead of file pointers.
*   Parameters : inFile - name of file to decode
*                outFile - name of file to write decoded output
*   Effects    : inFile is decoded and written to outFile
*   Returned   : EXIT_SUCCESS or EXIT_FAILURE
****************************************************************************/
int DecodeLZSSByName(char *inFile, char *outFile)
{
    FILE *fpIn, *fpOut;
    int returnValue;

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

    returnValue = DecodeLZSSByFile(fpIn, fpOut);

    /* close files */
    fclose(fpIn);
    fclose(fpOut);

    return (returnValue);
}
