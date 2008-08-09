/***************************************************************************
*                    Lempel-Ziv-Welch Decoding Functions
*
*   File    : lzwdecode.c
*   Purpose : Provides a function for decoding Lempel-Ziv-Welch encoded
*             file streams
*   Author  : Michael Dipperstein
*   Date    : January 30, 2005
*
****************************************************************************
*   UPDATES
*
*   $Id: lzwdecode.c,v 1.2 2007/09/29 01:28:09 michael Exp $
*   $Log: lzwdecode.c,v $
*   Revision 1.2  2007/09/29 01:28:09  michael
*   Changes required for LGPL v3.
*
*   Revision 1.1  2005/04/09 03:11:22  michael
*   Separated encode and decode routines into two different files in order to
*   make future enhancements easier.
*
*   Revision 1.4  2005/03/27 15:56:47  michael
*   Use variable length code words.
*   Include new e-mail addres.
*
*   Revision 1.3  2005/03/10 14:26:58  michael
*   User variable names that match discription in web page.
*
*   Revision 1.2  2005/03/10 05:44:02  michael
*   Minimize the size of the dictionary.
*
*   Revision 1.1.1.1  2005/02/21 03:35:34  michael
*   Initial Release
*
****************************************************************************
*
* LZW: An ANSI C Lempel-Ziv-Welch Encoding/Decoding Routines
* Copyright (C) 2005, 2007 by
* Michael Dipperstein (mdipper@alumni.engr.ucsb.edu)
*
* This file is part of the lzw library.
*
* The lzw library is free software; you can redistribute it and/or
* modify it under the terms of the GNU Lesser General Public License as
* published by the Free Software Foundation; either version 3 of the
* License, or (at your option) any later version.
*
* The lzw library is distributed in the hope that it will be useful, but
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
#include <limits.h>
#include <string.h>
#include "lzw.h"
#include "bitfile.h"

/***************************************************************************
*                            TYPE DEFINITIONS
***************************************************************************/
typedef struct
{
    unsigned char suffixChar;   /* last char in encoded string */
    unsigned int prefixCode;    /* code for remaining chars in string */
} decode_dictionary_t;

/***************************************************************************
*                                CONSTANTS
***************************************************************************/

#define EMPTY           -1

#define MIN_CODE_LEN    9                   /* min # bits in a code word */
#define MAX_CODE_LEN    15                  /* max # bits in a code word */

#define FIRST_CODE      (1 << CHAR_BIT)     /* value of 1st string code */

#define MAX_CODES       (1 << MAX_CODE_LEN)

#define DICT_SIZE       (MAX_CODES - FIRST_CODE)

#if (MIN_CODE_LEN <= CHAR_BIT)
#error Code words must be larger than 1 character
#endif

#if (MAX_CODE_LEN > (2 * CHAR_BIT))
#error Code words larger than 2 characters require a re-write of GetCodeWord\
 and PutCodeWord
#endif

#if ((MAX_CODES - 1) > INT_MAX)
#error There cannot be more codes than can fit in an integer
#endif

/***************************************************************************
*                                  MACROS
***************************************************************************/
#define CODE_MS_BITS(BITS)      ((BITS) - CHAR_BIT)
#define MS_BITS_MASK(BITS)      (UCHAR_MAX << (CHAR_BIT - CODE_MS_BITS(BITS)))
#define CURRENT_MAX_CODES(BITS)     (1 << (BITS))

/***************************************************************************
*                            GLOBAL VARIABLES
***************************************************************************/

/* dictionary of string the code word is the dictionary index */
decode_dictionary_t dictionary[DICT_SIZE];
char currentCodeLen;

/***************************************************************************
*                               PROTOTYPES
***************************************************************************/
unsigned char DecodeRecursive(unsigned int code, FILE *fpOut);

/* read encoded data */
int GetCodeWord(bit_file_t *bfpIn);

/***************************************************************************
*                                FUNCTIONS
***************************************************************************/

/***************************************************************************
*   Function   : LZWDecodeFile
*   Description: This routine reads an input file 1 encoded string at a
*                time and decodes it using the LZW algorithm.
*   Parameters : inFile - Name of file to decode
*                outFile - Name of file to write decoded output to
*   Effects    : File is decoded using the LZW algorithm with CODE_LEN
*                codes.
*   Returned   : TRUE for success, otherwise FALSE.
***************************************************************************/
int LZWDecodeFile(char *inFile, char *outFile)
{
    bit_file_t *bfpIn;                  /* encoded input */
    FILE *fpOut;                        /* decoded output */

    unsigned int nextCode;              /* value of next code */
    unsigned int lastCode;              /* last decoded code word */
    unsigned int code;                  /* code word to decode */
    unsigned char c;                    /* last decoded character */

    /* open input and output files */
    if (NULL == (bfpIn = BitFileOpen(inFile, BF_READ)))
    {
        perror(inFile);
        return FALSE;
    }

    if (NULL == outFile)
    {
        fpOut = stdout;
    }
    else
    {
        if (NULL == (fpOut = fopen(outFile, "wb")))
        {
            BitFileClose(bfpIn);
            perror(outFile);
            return FALSE;
        }
    }

    /* start with 9 bit code words */
    currentCodeLen = 9;

    /* initialize for decoding */
    nextCode = FIRST_CODE;  /* code for next (first) string */

    /* first code from file must be a character.  use it for initial values */
    lastCode = GetCodeWord(bfpIn);
    c = lastCode;
    fputc(lastCode, fpOut);

    /* decode rest of file */
    while ((code = GetCodeWord(bfpIn)) != EOF)
    {

        /* look for code length increase marker */
        if (((CURRENT_MAX_CODES(currentCodeLen) - 1) == code) &&
            (currentCodeLen < MAX_CODE_LEN))
        {
            currentCodeLen++;
            code = GetCodeWord(bfpIn);
        }

        if (code < nextCode)
        {
            /* we have a known code.  decode it */
            c = DecodeRecursive(code, fpOut);
        }
        else
        {
            /***************************************************************
            * We got a code that's not in our dictionary.  This must be due
            * to the string + char + string + char + string exception.
            * Build the decoded string using the last character + the
            * string from the last code.
            ***************************************************************/
            unsigned char tmp;

            tmp = c;
            c = DecodeRecursive(lastCode, fpOut);
            fputc(tmp, fpOut);
        }

        /* if room, add new code to the dictionary */
        if (nextCode < MAX_CODES)
        {
            dictionary[nextCode - FIRST_CODE].prefixCode = lastCode;
            dictionary[nextCode - FIRST_CODE].suffixChar = c;
            nextCode++;
        }

        /* save character and code for use in unknown code word case */
        lastCode = code;
    }

    fclose(fpOut);
    BitFileClose(bfpIn);
    return TRUE;
}

/***************************************************************************
*   Function   : DecodeRecursive
*   Description: This function uses the dictionary to decode a code word
*                into the string it represents and write it to the output
*                file.  The string is actually built in reverse order and
*                recursion is used to write it out in the correct order.
*   Parameters : code - the code word to decode
*                fpOut - the file that the decoded code word is written to
*   Effects    : Decoded code word is written to a file
*   Returned   : The first character in the decoded string
***************************************************************************/
unsigned char DecodeRecursive(unsigned int code, FILE *fpOut)
{
    unsigned char c;
    unsigned char firstChar;

    if (code >= FIRST_CODE)
    {
        /* code word is string + c */
        c = dictionary[code - FIRST_CODE].suffixChar;
        code = dictionary[code - FIRST_CODE].prefixCode;

        /* evaluate new code word for remaining string */
        firstChar = DecodeRecursive(code, fpOut);
    }
    else
    {
        /* code word is just c */
        c = code;
        firstChar = code;
    }

    fputc(c, fpOut);
    
    return firstChar;
}

/***************************************************************************
*   Function   : GetCodeWord
*   Description: This function reads and returns a code word from an
*                encoded file.  In order to deal with endian issue the
*                code word is read least significant byte followed by the
*                remaining bits.
*   Parameters : bfpIn - bit file containing the encoded data
*   Effects    : code word is read from encoded input
*   Returned   : The next code word in the encoded file.  EOF if the end
*                of file has been reached.
*
*   NOTE: If the code word contains more than 16 bits, this routine should
*         be modified to read in all the bytes from least significant to
*         most significant followed by any left over bits.
***************************************************************************/
int GetCodeWord(bit_file_t *bfpIn)
{
    unsigned char byte;
    int code;

    /* get LS character */
    if ((code = BitFileGetChar(bfpIn)) == EOF)
    {
        return EOF;
    }


    /* get remaining bits */
    if (BitFileGetBits(bfpIn, &byte, CODE_MS_BITS(currentCodeLen)) == EOF)
    {
        return EOF;
    }

    code |= ((int)byte) << CODE_MS_BITS(currentCodeLen);

    return code;
}
