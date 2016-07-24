/***************************************************************************
*                 Arithmetic Encoding and Decoding Library
*
*   File    : arcode.c
*   Purpose : Use arithmetic coding to compress/decompress file streams
*   Author  : Michael Dipperstein
*   Date    : April 2, 2004
*
****************************************************************************
*   UPDATES
*
*   $Id: arcode.c,v 1.5 2007/09/08 15:47:02 michael Exp $
*   $Log: arcode.c,v $
*   Revision 1.5  2007/09/08 15:47:02  michael
*   Changes required for LGPL v3.
*
*   Revision 1.4  2006/03/02 06:43:37  michael
*   Expanded tabs
*
*   Revision 1.3  2006/01/12 07:39:24  michael
*   Use BitFileGetBitsIntBit and FilePutBitsInt for reading and writing the
*   header.  This makes the code a little cleaner, but the new header is not
*   compatible with the old header.
*
*   Revision 1.2  2004/08/13 13:10:27  michael
*   Add support for adaptive encoding
*
*   Use binary search when trying to find decoded symbol
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

/***************************************************************************
*                             INCLUDED FILES
***************************************************************************/
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include "arcode.h"
#include "bitfile.h"

/* compile-time options */
#undef BUILD_DEBUG_OUTPUT                   /* debugging output */

#if !(USHRT_MAX < ULONG_MAX)
#error "Implementation requires USHRT_MAX < ULONG_MAX"
#endif

/***************************************************************************
*                            TYPE DEFINITIONS
***************************************************************************/
typedef unsigned short probability_t;       /* probability count type */

/***************************************************************************
*                                CONSTANTS
***************************************************************************/
#define EOF_CHAR    (UCHAR_MAX + 1)

/* number of bits used to compute running code values */
#define PRECISION           (8 * sizeof(probability_t))

/* 2 bits less than precision. keeps lower and upper bounds from crossing. */
#define MAX_PROBABILITY     (1 << (PRECISION - 2))

/***************************************************************************
*                                  MACROS
***************************************************************************/
/* set bit x to 1 in probability_t.  Bit 0 is MSB */
#define MASK_BIT(x) (probability_t)(1 << (PRECISION - (1 + (x))))

/* indices for a symbol's lower and upper cumulative probability ranges */
#define LOWER(c)        (c)
#define UPPER(c)    ((c) + 1)

/***************************************************************************
*                            GLOBAL VARIABLES
***************************************************************************/
probability_t lower;          /* lower bound of current code range */
probability_t upper;          /* upper bound of current code range */

probability_t code;           /* current MSBs of encode input stream */

unsigned char underflowBits;      /* current underflow bit count */

/* probability ranges for each symbol: [ranges[LOWER(c)], ranges[UPPER(c)]) */
probability_t ranges[UPPER(EOF_CHAR) + 1];
probability_t cumulativeProb;   /* cumulative probability  of all ranges */

/***************************************************************************
*                               PROTOTYPES
***************************************************************************/
/* read write file headers */
void WriteHeader(bit_file_t *bfpOut);
int ReadHeader(bit_file_t *bfpIn);

/* applies symbol's ranges to current upper and lower range bounds */
void ApplySymbolRange(int symbol, char staticModel);

/* routines for encoding*/
void WriteEncodedBits(bit_file_t *bfpOut);
void WriteRemaining(bit_file_t *bfpOut);
int BuildProbabilityRangeList(FILE *fpIn);
void InitializeAdaptiveProbabilityRangeList(void);

/* routines for decoding */
void InitializeDecoder(bit_file_t *bfpOut, char staticModel);
probability_t GetUnscaledCode(void);
int GetSymbolFromProbability(probability_t probability);
void ReadEncodedBits(bit_file_t *bfpIn);

/***************************************************************************
*                                FUNCTIONS
***************************************************************************/

/***************************************************************************
*   Function   : ArEncodeFile
*   Description: This routine generates a list of arithmetic code ranges for
*                a file and then uses them to write out an encoded version
*                of that file.
*   Parameters : inFile - Name of file to encode
*                outFile - Name of file to write encoded output to
*                staticModel - TRUE if encoding with a static model
*   Effects    : File is arithmetically encoded
*   Returned   : TRUE for success, otherwise FALSE.
***************************************************************************/
int ArEncodeFile(char *inFile, char *outFile, char staticModel)
{
    int c;
    FILE *fpIn;                         /* uncoded input */
    bit_file_t *bfpOut;                 /* encoded output */

    /* open input and output files */
    if ((fpIn = fopen(inFile, "rb")) == NULL)
    {
        perror(inFile);
        return FALSE;
    }

    if (outFile == NULL)
    {
        bfpOut = MakeBitFile(stdout, BF_WRITE);
    }
    else
    {
        if ((bfpOut = BitFileOpen(outFile, BF_WRITE)) == NULL)
        {
            fclose(fpIn);
            perror(outFile);
            return FALSE;
        }
    }

    if (staticModel)
    {
        /* count symbols in file and come up with a list of probability ranges */
        if (!BuildProbabilityRangeList(fpIn))
        {
            fclose(fpIn);
            BitFileClose(bfpOut);
            fprintf(stderr, "Error determining frequency ranges.\n");
            return FALSE;
        }

        rewind(fpIn);

        /* write information required to decode file to encoded file */
        WriteHeader(bfpOut);
    }
    else
    {
        /* initialize probability ranges asumming uniform distribution */
        InitializeAdaptiveProbabilityRangeList();
    }

    /* initialize coder start with full probability range [0%, 100%) */
    lower = 0;
    upper = ~0;                     /* all ones */
    underflowBits = 0;

    /* encode symbols one at a time */
    while ((c = fgetc(fpIn)) != EOF)
    {
        ApplySymbolRange(c, staticModel);
        WriteEncodedBits(bfpOut);
    }

    fclose(fpIn);

    ApplySymbolRange(EOF_CHAR, staticModel);    /* encode an EOF */
    WriteEncodedBits(bfpOut);

    WriteRemaining(bfpOut);         /* write out least significant bits */
    BitFileClose(bfpOut);

    return TRUE;
}

/***************************************************************************
*   Function   : SymbolCountToProbabilityRanges
*   Description: This routine converts the ranges array containing only
*                symbol counts to an array containing the upper and lower
*                probability ranges for each symbol.
*   Parameters : None
*   Effects    : ranges array containing symbol counts in the upper field
*                for each symbol is converted to a list of upper and lower
*                probability bounds for each symbol.
*   Returned   : None
***************************************************************************/
void SymbolCountToProbabilityRanges(void)
{
    int c;

    ranges[0] = 0;                              /* absolute lower bound is 0 */
    ranges[UPPER(EOF_CHAR)] = 1;        /* add 1 EOF character */
    cumulativeProb++;

    /* assign upper and lower probability ranges */
    for (c = 1; c <= UPPER(EOF_CHAR); c++)
    {
        ranges[c] += ranges[c - 1];
    }

#ifdef BUILD_DEBUG_OUTPUT
    /* dump list of ranges */
    for (c = 0; c < UPPER(EOF_CHAR); c++)
    {
        printf("%02X\t%d\t%d\n", c, ranges[LOWER(c)], ranges[UPPER(c)]);
    }
#endif

    return;
}

/***************************************************************************
*   Function   : BuildProbabilityRangeList
*   Description: This routine reads the input file and builds the global
*                list of upper and lower probability ranges for each
*                symbol.
*   Parameters : fpIn - file to build range list for
*   Effects    : ranges array is made to contain probability ranges for
*                each symbol.
*   Returned   : TRUE for success, otherwise FALSE.
***************************************************************************/
int BuildProbabilityRangeList(FILE *fpIn)
{
    int c;

    /***********************************************************************
    * unsigned long is used to hold the largest counts we can have without
    * any rescaling.  Rescaling may take place before probability ranges
    * are computed.
    ***********************************************************************/
    unsigned long countArray[EOF_CHAR];
    unsigned long totalCount = 0;
    unsigned long rescaleValue;

    if (fpIn == NULL)
    {
        return FALSE;
    }

        /* start with no symbols counted */
    for (c = 0; c < EOF_CHAR; c++)
    {
        countArray[c] = 0;
    }

    while ((c = fgetc(fpIn)) != EOF)
    {
        if (totalCount == ULONG_MAX)
        {
            fprintf(stderr, "Error: file too large\n");
            return FALSE;
        }

        countArray[c]++;
        totalCount++;
    }

    /* rescale counts to be < MAX_PROBABILITY */
    if (totalCount >= MAX_PROBABILITY)
    {
        rescaleValue = (totalCount / MAX_PROBABILITY) + 1;

        for (c = 0; c < EOF_CHAR; c++)
        {
            if (countArray[c] > rescaleValue)
            {
                countArray[c] /= rescaleValue;
            }
            else if (countArray[c] != 0)
            {
                countArray[c] = 1;
            }
        }
    }

    /* copy scaled symbol counts to range list */
    ranges[0] = 0;
    cumulativeProb = 0;
    for (c = 0; c < EOF_CHAR; c++)
    {
        ranges[UPPER(c)] = countArray[c];
        cumulativeProb += countArray[c];
    }

    /* convert counts to a range of probabilities */
    SymbolCountToProbabilityRanges();
    return TRUE;
}

/***************************************************************************
*   Function   : WriteHeader
*   Description: This function writes each symbol contained in the encoded
*                file as well as its rescaled number of occurrences.  A
*                decoding algorithm may use these numbers to reconstruct
*                the probability range list used to encode the file.
*   Parameters : bfpOut - pointer to open binary file to write to.
*   Effects    : Symbol values and symbol counts are written to a file.
*   Returned   : None
***************************************************************************/
void WriteHeader(bit_file_t *bfpOut)
{
    int c;
    probability_t previous = 0;         /* symbol count so far */

#if BUILD_DEBUG_OUTPUT
    printf("HEADER:\n");
#endif

    for(c = 0; c <= (EOF_CHAR - 1); c++)
    {
        if (ranges[UPPER(c)] > previous)
        {
            /* some of these symbols will be encoded */
            BitFilePutChar((char)c, bfpOut);
            previous = (ranges[UPPER(c)] - previous);   /* symbol count */

#if BUILD_DEBUG_OUTPUT
            printf("%02X\t%d\n", c, previous);
#endif

            /* write out PRECISION - 2 bit count */
            BitFilePutBitsInt(bfpOut, &previous, (PRECISION - 2),
                sizeof(probability_t));

            /* current upper range is previous for the next character */
            previous = ranges[UPPER(c)];
        }
    }

    /* now write end of table (zero count) */
    BitFilePutChar(0x00, bfpOut);
    previous = 0;
    BitFilePutBits(bfpOut, (void *)&previous, PRECISION - 2);
}

/***************************************************************************
*   Function   : InitializeAdaptiveProbabilityRangeList
*   Description: This routine builds the initial global list of upper and
*                lower probability ranges for each symbol.  This routine
*                is used by both adaptive encoding and decoding.
*                Currently it provides a uniform symbol distribution.
*                Other distributions might be better suited for known data
*                types (such as English text).
*   Parameters : NONE
*   Effects    : ranges array is made to contain initial probability ranges
*                for each symbol.
*   Returned   : NONE
***************************************************************************/
void InitializeAdaptiveProbabilityRangeList(void)
{
    int c;

    cumulativeProb = 0;
    ranges[0] = 0;          /* absolute lower range */

    /* assign upper and lower probability ranges assuming */
    for (c = 1; c <= UPPER(EOF_CHAR); c++)
    {
        ranges[c] = ranges[c - 1] + 1;
        cumulativeProb++;
    }

#ifdef BUILD_DEBUG_OUTPUT
    /* dump list of ranges */
    for (c = 0; c < UPPER(EOF_CHAR); c++)
    {
        printf("%02X\t%d\t%d\n", c, ranges[LOWER(c)], ranges[UPPER(c)]);
    }
#endif

    return;
}

/***************************************************************************
*   Function   : ApplySymbolRange
*   Description: This function is used for both encoding and decoding.  It
*                applies the range restrictions of a new symbol to the
*                current upper and lower range bounds of an encoded stream.
*                If an adaptive model is being used, the probability range
*                list will be updated after the effect of the symbol is
*                applied.
*   Parameters : symbol - The symbol to be added to the current code range
*                staticModel - TRUE if encoding/decoding with a static
*                              model.
*   Effects    : The current upper and lower range bounds are adjusted to
*                include the range effects of adding another symbol to the
*                encoded stream.  If an adaptive model is being used, the
*                probability range list will be updated.
*   Returned   : None
***************************************************************************/
void ApplySymbolRange(int symbol, char staticModel)
{
    unsigned long range;        /* must be able to hold max upper + 1 */
    unsigned long rescaled;     /* range rescaled for range of new symbol */
                                /* must hold range * max upper */

    /* for updating dynamic models */
    int i;
    probability_t original;     /* range value prior to rescale */
    probability_t delta;        /* range for individual symbol */

    /***********************************************************************
    * Calculate new upper and lower ranges.  Since the new upper range is
    * dependant of the old lower range, compute the upper range first.
    ***********************************************************************/
    range = (unsigned long)(upper - lower) + 1;         /* current range */

    /* scale upper range of the symbol being coded */
    rescaled = (unsigned long)ranges[UPPER(symbol)] * range;
    rescaled /= (unsigned long)cumulativeProb;

    /* new upper = old lower + rescaled new upper - 1*/
    upper = lower + (probability_t)rescaled - 1;

    /* scale lower range of the symbol being coded */
    rescaled = (unsigned long)ranges[LOWER(symbol)] * range;
    rescaled /= (unsigned long)cumulativeProb;

    /* new lower = old lower + rescaled new upper */
    lower = lower + (probability_t)rescaled;

    if (!staticModel)
    {
        /* add new symbol to model */
        cumulativeProb++;
        for (i = UPPER(symbol); i <= UPPER(EOF_CHAR); i++)
        {
            ranges[i] += 1;
        }

        /* half current values if cumulativeProb is too large */
        if (cumulativeProb >= MAX_PROBABILITY)
        {
            cumulativeProb = 0;
            original = 0;

            for (i = 1; i <= UPPER(EOF_CHAR); i++)
            {
                delta = ranges[i] - original;
                if (delta <= 2)
                {
                    /* prevent probability from being 0 */
                    original = ranges[i];
                    ranges[i] = ranges[i - 1] + 1;
                }
                else
                {
                    original = ranges[i];
                    ranges[i] = ranges[i - 1] + (delta / 2);
                }

                cumulativeProb += (ranges[i] - ranges[i - 1]);
            }
        }
    }

#ifdef BUILD_DEBUG_OUTPUT
    if (lower > upper)
    {
        /* compile this in when testing new models. */
        fprintf(stderr, "Panic: lower (%X)> upper (%X)\n", lower, upper);
    }
#endif
}

/***************************************************************************
*   Function   : WriteEncodedBits
*   Description: This function attempts to shift out as many code bits as
*                possible, writing the shifted bits to the encoded output
*                file.  Only bits that will be unchanged when additional
*                symbols are encoded may be written out.
*
*                If the n most significant bits of the lower and upper range
*                bounds match, they will not be changed when additional
*                symbols are encoded, so they may be shifted out.
*
*                Adjustments are also made to prevent possible underflows
*                that occur when the upper and lower ranges are so close
*                that encoding another symbol won't change their values.
*   Parameters : bfpOut - pointer to open binary file to write to.
*   Effects    : The upper and lower code bounds are adjusted so that they
*                only contain only bits that may be affected by the
*                addition of a new symbol to the encoded stream.
*   Returned   : None
***************************************************************************/
void WriteEncodedBits(bit_file_t *bfpOut)
{
    for (;;)
    {
        if ((upper & MASK_BIT(0)) == (lower & MASK_BIT(0)))
        {
            /* MSBs match, write them to output file */
            BitFilePutBit((upper & MASK_BIT(0)) != 0, bfpOut);

            /* we can write out underflow bits too */
            while (underflowBits > 0)
            {
                BitFilePutBit((upper & MASK_BIT(0)) == 0, bfpOut);
                underflowBits--;
            }
        }
        else if ((lower & MASK_BIT(1)) && !(upper & MASK_BIT(1)))
        {
            /***************************************************************
            * Possible underflow condition: neither MSBs nor second MSBs
            * match.  It must be the case that lower and upper have MSBs of
            * 01 and 10.  Remove 2nd MSB from lower and upper.
            ***************************************************************/
            underflowBits += 1;
            lower &= ~(MASK_BIT(0) | MASK_BIT(1));
            upper |= MASK_BIT(1);

            /***************************************************************
            * The shifts below make the rest of the bit removal work.  If
            * you don't believe me try it yourself.
            ***************************************************************/
        }
        else
        {
            /* nothing left to do */
            return ;
        }

        /*******************************************************************
        * Shift out old MSB and shift in new LSB.  Remember that lower has
        * all 0s beyond it's end and upper has all 1s beyond it's end.
        *******************************************************************/
        lower <<= 1;
        upper <<= 1;
        upper |= 1;
    }
}

/***************************************************************************
*   Function   : WriteRemaining
*   Description: This function writes out all remaining significant bits
*                in the upper and lower ranges and the underflow bits once
*                the last symbol has been encoded.
*   Parameters : bfpOut - pointer to open binary file to write to.
*   Effects    : Remaining significant range bits are written to the output
*                file.
*   Returned   : None
***************************************************************************/
void WriteRemaining(bit_file_t *bfpOut)
{
    BitFilePutBit((lower & MASK_BIT(1)) != 0, bfpOut);

    /* write out any unwritten underflow bits */
    for (underflowBits++; underflowBits > 0; underflowBits--)
    {
        BitFilePutBit((lower & MASK_BIT(1)) == 0, bfpOut);
    }
}

/***************************************************************************
*   Function   : ArDecodeFile
*   Description: This routine opens an arithmetically encoded file, reads
*                it's header, and builds a list of probability ranges which
*                it then uses to decode the rest of the file.
*   Parameters : inFile - Name of file to decode
*                outFile - Name of file to write decoded output to
*                staticModel - TRUE if decoding with a static model
*   Effects    : Encoded file is decoded
*   Returned   : TRUE for success, otherwise FALSE.
***************************************************************************/
int ArDecodeFile(char *inFile, char *outFile, char staticModel)
{
    int c;
    probability_t unscaled;
    bit_file_t *bfpIn;
    FILE *fpOut;

    /* open input and output files */
    if ((bfpIn = BitFileOpen(inFile, BF_READ)) == NULL)
    {
        perror(inFile);
        return FALSE;
    }

    if (outFile == NULL)
    {
        fpOut = stdout;
    }
    else
    {
        if ((fpOut = fopen(outFile, "wb")) == NULL)
        {
            BitFileClose(bfpIn);
            perror(outFile);
            return FALSE;
        }
    }

    if (staticModel)
    {
        /* build probability ranges from header in file */
        if (ReadHeader(bfpIn) == FALSE)
        {
            BitFileClose(bfpIn);
            fclose(fpOut);
            return FALSE;
        }
    }

    /* read start of code and initialize bounds, and adaptive ranges */
    InitializeDecoder(bfpIn, staticModel);

    /* decode one symbol at a time */
    for (;;)
    {
        /* get the unscaled probability of the current symbol */
        unscaled = GetUnscaledCode();

        /* figure out which symbol has the above probability */
        if((c = GetSymbolFromProbability(unscaled)) == -1)
        {
            /* error: unknown symbol */
            break;
        }

        if (c == EOF_CHAR)
        {
            /* no more symbols */
            break;
        }

        fputc((char)c, fpOut);

        /* factor out symbol */
        ApplySymbolRange(c, staticModel);
        ReadEncodedBits(bfpIn);
    }

    fclose(fpOut);
    BitFileClose(bfpIn);

    return TRUE;
}

/****************************************************************************
*   Function   : ReadHeader
*   Description: This function reads the header information stored by
*                WriteHeader.  The header can then be used to build a
*                probability range list matching the list that was used to
*                encode the file.
*   Parameters : bfpIn - file to read from
*   Effects    : Probability range list is built.
*   Returned   : TRUE for success, otherwise FALSE
****************************************************************************/
int ReadHeader(bit_file_t *bfpIn)
{
    int c;
    probability_t count;

#if BUILD_DEBUG_OUTPUT
    printf("HEADER:\n");
#endif

    cumulativeProb = 0;

    for (c = 0; c < UPPER(EOF_CHAR); c++)
    {
        ranges[UPPER(c)] = 0;
    }

    /* read [character, probability] sets */
    for (;;)
    {
        c = BitFileGetChar(bfpIn);
        count = 0;

        /* read (PRECISION - 2) bit count */
       if (BitFileGetBitsInt(bfpIn, &count, (PRECISION - 2),
            sizeof(probability_t)) == EOF)
        {
            /* premature EOF */
            fprintf(stderr, "Error: unexpected EOF\n");
            return FALSE;
        }

#if BUILD_DEBUG_OUTPUT
        printf("%02X\t%d\n", c, count);
#endif

        if (count == 0)
        {
            /* 0 count means end of header */
            break;
        }

        ranges[UPPER(c)] = count;
        cumulativeProb += count;
    }

    /* convert counts to range list */
    SymbolCountToProbabilityRanges();
    return TRUE;
}

/****************************************************************************
*   Function   : InitializeDecoder
*   Description: This function starts the upper and lower ranges at their
*                max/min values and reads in the most significant encoded
*                bits.
*   Parameters : bfpIn - file to read from
*                staticModel - TRUE if decoding using a staticModel
*   Effects    : upper, lower, and code are initialized.  The probability
*                range list will also be initialized if an adaptive model
*                will be used.
*   Returned   : TRUE for success, otherwise FALSE
****************************************************************************/
void InitializeDecoder(bit_file_t *bfpIn, char staticModel)
{
    int i;

    if (!staticModel)
    {
        /* initialize ranges for adaptive model */
        InitializeAdaptiveProbabilityRangeList();
    }

    code = 0;

    /* read PERCISION MSBs of code one bit at a time */
    for (i = 0; i < PRECISION; i++)
    {
        code <<= 1;

        /* treat EOF like 0 */
        if(BitFileGetBit(bfpIn) == 1)
        {
            code |= 1;
        }
    }

    /* start with full probability range [0%, 100%) */
    lower = 0;
    upper = ~0;         /* all ones */
}

/****************************************************************************
*   Function   : GetUnscaledCode
*   Description: This function undoes the scaling that ApplySymbolRange
*                performed before bits were shifted out.  The value returned
*                is the probability of the encoded symbol.
*   Parameters : None
*   Effects    : None
*   Returned   : The probability of the current symbol
****************************************************************************/
probability_t GetUnscaledCode(void)
{
    unsigned long range;        /* must be able to hold max upper + 1 */
    unsigned long unscaled;

    range = (unsigned long)(upper - lower) + 1;

    /* reverse the scaling operations from ApplySymbolRange */
    unscaled = (unsigned long)(code - lower) + 1;
    unscaled = unscaled * (unsigned long)cumulativeProb - 1;
    unscaled /= range;

    return ((probability_t)unscaled);
}

/****************************************************************************
*   Function   : GetSymbolFromProbability
*   Description: Given a probability, this function will return the symbol
*                whose range includes that probability.  Symbol is found
*                binary search on probability ranges.
*   Parameters : probability - probability of symbol.
*   Effects    : None
*   Returned   : -1 for failure, otherwise encoded symbol
****************************************************************************/
int GetSymbolFromProbability(probability_t probability)
{
    int first, last, middle;    /* indicies for binary search */

    first = 0;
    last = UPPER(EOF_CHAR);
    middle = last / 2;

    /* binary search */
    while (last >= first)
    {
        if (probability < ranges[LOWER(middle)])
        {
            /* lower bound is higher than probability */
            last = middle - 1;
            middle = first + ((last - first) / 2);
            continue;
        }

        if (probability >= ranges[UPPER(middle)])
        {
            /* upper bound is lower than probability */
            first = middle + 1;
            middle = first + ((last - first) / 2);
            continue;
        }

        /* we must have found the right value */
        return middle;
    }

    /* error: none of the ranges include the probability */
    fprintf(stderr, "Unknown Symbol: %d (max: %d)\n", probability,
        ranges[UPPER(EOF_CHAR)]);
    return -1;
}

/***************************************************************************
*   Function   : ReadEncodedBits
*   Description: This function attempts to shift out as many code bits as
*                possible, as bits are shifted out the coded input is
*                populated with bits from the encoded file.  Only bits
*                that will be unchanged when additional symbols are decoded
*                may be shifted out.
*
*                If the n most significant bits of the lower and upper range
*                bounds match, they will not be changed when additional
*                symbols are decoded, so they may be shifted out.
*
*                Adjustments are also made to prevent possible underflows
*                that occur when the upper and lower ranges are so close
*                that decoding another symbol won't change their values.
*   Parameters : bfpOut - pointer to open binary file to read from.
*   Effects    : The upper and lower code bounds are adjusted so that they
*                only contain only bits that will be affected by the
*                addition of a new symbol.  Replacements are read from the
*                encoded stream.
*   Returned   : None
***************************************************************************/
void ReadEncodedBits(bit_file_t *bfpIn)
{
    int nextBit;        /* next bit from encoded input */

    for (;;)
    {
        if (( upper & MASK_BIT(0)) == (lower & MASK_BIT(0)))
        {
                        /* MSBs match, allow them to be shifted out*/
        }
        else if ((lower & MASK_BIT(1)) && !(upper & MASK_BIT(1)))
        {
            /***************************************************************
            * Possible underflow condition: neither MSBs nor second MSBs
            * match.  It must be the case that lower and upper have MSBs of
            * 01 and 10.  Remove 2nd MSB from lower and upper.
            ***************************************************************/
                        lower   &= ~(MASK_BIT(0) | MASK_BIT(1));
            upper  |= MASK_BIT(1);
            code ^= MASK_BIT(1);

            /* the shifts below make the rest of the bit removal work */
        }
        else
        {
            /* nothing to shift out */
            return;
        }

        /*******************************************************************
        * Shift out old MSB and shift in new LSB.  Remember that lower has
        * all 0s beyond it's end and upper has all 1s beyond it's end.
        *******************************************************************/
                lower <<= 1;
        upper <<= 1;
        upper |= 1;
        code <<= 1;

        if ((nextBit = BitFileGetBit(bfpIn)) == EOF)
        {
            /* either all bits are shifted out or error occurred */
        }
        else
        {
            code |= nextBit;                /* add next encoded bit to code */
        }
    }

    return;
}
