/***************************************************************************
*                        Bit Stream File Implementation
*
*   File    : bitfile.c
*   Purpose : This file implements a simple library of I/O functions for
*             files that contain data in sizes that aren't integral bytes.
*             An attempt was made to make the functions in this library
*             analogous to functions provided to manipulate byte streams.
*             The functions contained in this library were created with
*             compression algorithms in mind, but may be suited to other
*             applications.
*   Author  : Michael Dipperstein
*   Date    : January 9, 2004
*
****************************************************************************
*   UPDATES
*
*   $Id: bitfile.c,v 1.10 2007/08/26 21:53:48 michael Exp $
*   $Log: bitfile.c,v $
*   Revision 1.10  2007/08/26 21:53:48  michael
*   Changes required for LGPL v3.
*
*   Revision 1.9  2007/07/10 05:34:07  michael
*   Remove ',' after last element in the enum endian_t.
*
*   Revision 1.8  2007/02/06 06:22:07  michael
*   Used trim program to remove trailing spaces.
*
*   Revision 1.7  2006/06/03 19:32:38  michael
*   Corrected error reporetd anonymous.  The allocation of constants used to
*   open underlying read/write/append files did not account for a terminating
*   null.
*
*   Used spell checker to correct spelling.
*
*   Revision 1.6  2005/12/08 06:56:55  michael
*   Minor text corrections.
*
*   Revision 1.5  2005/12/06 15:06:37  michael
*   Added BitFileGetBitsInt and BitFilePutBitsInt for integer types.
*
*   Revision 1.4  2005/06/23 04:34:18  michael
*   Prevent BitfileGetBits/PutBits from accessing an extra byte when given
*   an integral number of bytes.
*
*   Revision 1.3  2004/11/09 14:16:58  michael
*   Added functions to convert open bit_file_t to FILE and to
*   align open bit_file_t to the next byte.
*
*   Revision 1.2  2004/06/15 13:15:58  michael
*   Use incomplete type to hide definition of bitfile structure
*
*   Revision 1.1.1.1  2004/02/09 05:31:42  michael
*   Initial release
*
*
****************************************************************************
*
* Bitfile: Bit stream File I/O Routines
* Copyright (C) 2004-2007 by Michael Dipperstein (mdipper@cs.ucsb.edu)
*
* This file is part of the bit file library.
*
* The bit file library is free software; you can redistribute it and/or
* modify it under the terms of the GNU Lesser General Public License as
* published by the Free Software Foundation; either version 3 of the
* License, or (at your option) any later version.
*
* The bit file library is distributed in the hope that it will be useful,
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
#include <stdlib.h>
#include <errno.h>
#include "bitfile.h"

/***************************************************************************
*                            TYPE DEFINITIONS
***************************************************************************/

typedef enum
{
    BF_UNKNOWN_ENDIAN,
    BF_LITTLE_ENDIAN,
    BF_BIG_ENDIAN
} endian_t;

struct bit_file_t
{
    FILE *fp;                   /* file pointer used by stdio functions */
    endian_t endian;            /* endianess of architecture */
    unsigned char bitBuffer;    /* bits waiting to be read/written */
    unsigned char bitCount;     /* number of bits in bitBuffer */
    BF_MODES mode;              /* open for read, write, or append */
};

/* union used to test for endianess */
typedef union
{
    unsigned long word;
    unsigned char bytes[sizeof(unsigned long)];
} endian_test_t;

/***************************************************************************
*                               PROTOTYPES
***************************************************************************/
endian_t DetermineEndianess(void);

int BitFilePutBitsLE(bit_file_t *stream, void *bits, const unsigned int count);
int BitFilePutBitsBE(bit_file_t *stream, void *bits, const unsigned int count,
    const size_t size);

int BitFileGetBitsLE(bit_file_t *stream, void *bits, const unsigned int count);
int BitFileGetBitsBE(bit_file_t *stream, void *bits, const unsigned int count,
    const size_t size);

/***************************************************************************
*                                FUNCTIONS
***************************************************************************/

/***************************************************************************
*   Function   : BitFileOpen
*   Description: This function opens a bit file for reading, writing,
*                or appending.  If successful, a bit_file_t data
*                structure will be allocated and a pointer to the
*                structure will be returned.
*   Parameters : fileName - NULL terminated string containing the name of
*                           the file to be opened.
*                mode - The mode of the file to be opened
*   Effects    : The specified file will be opened and file structure will
*                be allocated.
*   Returned   : Pointer to the bit_file_t structure for the bit file
*                opened, or NULL on failure.  errno will be set for all
*                failure cases.
***************************************************************************/
bit_file_t *BitFileOpen(const char *fileName, const BF_MODES mode)
{
    char modes[3][3] = {"rb", "wb", "ab"};  /* binary modes for fopen */
    bit_file_t *bf;

    bf = (bit_file_t *)malloc(sizeof(bit_file_t));

    if (bf == NULL)
    {
        /* malloc failed */
        errno = ENOMEM;
    }
    else
    {
        bf->fp = fopen(fileName, modes[mode]);

        if (bf->fp == NULL)
        {
            /* fopen failed */
            free(bf);
            return NULL;
        }
        else
        {
            /* fopen succeeded fill in remaining bf data */
            bf->bitBuffer = 0;
            bf->bitCount = 0;
            bf->mode = mode;

            /***************************************************************
            *  TO DO: Consider using the last byte in a file to indicate
            * the number of bits in the previous byte that actually have
            * data.  If I do that, I'll need special handling of files
            * opened with a mode of BF_APPEND.
            ***************************************************************/
        }
    }

    bf->endian = DetermineEndianess();
    return (bf);
}

/***************************************************************************
*   Function   : MakeBitFile
*   Description: This function naively wraps a standard file in a
*                bit_file_t structure.  ANSI-C doesn't support file status
*                functions commonly found in other C variants, so the
*                caller must be passed as a parameter.
*   Parameters : stream - pointer to the standard file being wrapped.
*                mode - The mode of the file being wrapped.
*   Effects    : A bit_file_t structure will be created for the stream
*                passed as a parameter.
*   Returned   : Pointer to the bit_file_t structure for the bit file
*                or NULL on failure.  errno will be set for all failure
*                cases.
***************************************************************************/
bit_file_t *MakeBitFile(FILE *stream, const BF_MODES mode)
{
    bit_file_t *bf;

    if (stream == NULL)
    {
        /* can't wrapper empty steam */
        errno = EBADF;
        bf = NULL;
    }
    else
    {
        bf = (bit_file_t *)malloc(sizeof(bit_file_t));

        if (bf == NULL)
        {
            /* malloc failed */
            errno = ENOMEM;
        }
        else
        {
            /* set structure data */
            bf->fp = stream;
            bf->bitBuffer = 0;
            bf->bitCount = 0;
            bf->mode = mode;
        }
    }

    bf->endian = DetermineEndianess();

    return (bf);
}

/***************************************************************************
*   Function   : DetermineEndianess
*   Description: This function determines the endianess of the current
*                hardware architecture.  An unsigned long is set to 1.  If
*                the 1st byte of the unsigned long gets the 1, this is a
*                little endian machine.  If the last byte gets the 1, this
*                is a big endian machine.
*   Parameters : None
*   Effects    : None
*   Returned   : endian_t for current machine architecture
***************************************************************************/
endian_t DetermineEndianess(void)
{
    endian_t endian;
    endian_test_t endianTest;

    endianTest.word = 1;

    if (endianTest.bytes[0] == 1)
    {
        /* LSB is 1st byte (little endian)*/
        endian = BF_LITTLE_ENDIAN;
    }
    else if (endianTest.bytes[sizeof(unsigned long) - 1] == 1)
    {
        /* LSB is last byte (big endian)*/
        endian = BF_BIG_ENDIAN;
    }
    else
    {
        endian = BF_UNKNOWN_ENDIAN;
    }

    return endian;
}

/***************************************************************************
*   Function   : BitFileClose
*   Description: This function closes a bit file and frees all associated
*                data.
*   Parameters : stream - pointer to bit file stream being closed
*   Effects    : The specified file will be closed and the file structure
*                will be freed.
*   Returned   : 0 for success or EOF for failure.
***************************************************************************/
int BitFileClose(bit_file_t *stream)
{
    int returnValue = 0;

    if (stream == NULL)
    {
        return(EOF);
    }

    if ((stream->mode == BF_WRITE) || (stream->mode == BF_APPEND))
    {
        /* write out any unwritten bits */
        if (stream->bitCount != 0)
        {
            (stream->bitBuffer) <<= 8 - (stream->bitCount);
            fputc(stream->bitBuffer, stream->fp);   /* handle error? */
        }
    }

    /***********************************************************************
    *  TO DO: Consider writing an additional byte indicating the number of
    *  valid bits (bitCount) in the previous byte.
    ***********************************************************************/

    /* close file */
    returnValue = fclose(stream->fp);

    /* free memory allocated for bit file */
    free(stream);

    return(returnValue);
}

/***************************************************************************
*   Function   : BitFileToFILE
*   Description: This function flushes and frees the bitfile structure,
*                returning a pointer to a stdio file.
*   Parameters : stream - pointer to bit file stream being closed
*   Effects    : The specified bitfile will be made usable as a stdio
*                FILE.
*   Returned   : Pointer to FILE.  NULL for failure.
***************************************************************************/
FILE *BitFileToFILE(bit_file_t *stream)
{
    FILE *fp = NULL;

    if (stream == NULL)
    {
        return(NULL);
    }

    if ((stream->mode == BF_WRITE) || (stream->mode == BF_APPEND))
    {
        /* write out any unwritten bits */
        if (stream->bitCount != 0)
        {
            (stream->bitBuffer) <<= 8 - (stream->bitCount);
            fputc(stream->bitBuffer, stream->fp);   /* handle error? */
        }
    }

    /***********************************************************************
    *  TO DO: Consider writing an additional byte indicating the number of
    *  valid bits (bitCount) in the previous byte.
    ***********************************************************************/

    /* close file */
    fp = stream->fp;

    /* free memory allocated for bit file */
    free(stream);

    return(fp);
}

/***************************************************************************
*   Function   : BitFileByteAlign
*   Description: This function aligns the bitfile to the nearest byte.  For
*                output files, this means writing out the bit buffer with
*                extra bits set to 0.  For input files, this means flushing
*                the bit buffer.
*   Parameters : stream - pointer to bit file stream to align
*   Effects    : Flushes out the bit buffer.
*   Returned   : EOF if stream is NULL.  Otherwise, the contents of the
*                bit buffer.
***************************************************************************/
int BitFileByteAlign(bit_file_t *stream)
{
    int returnValue;

    if (stream == NULL)
    {
        return(EOF);
    }

    returnValue = stream->bitBuffer;

    if ((stream->mode == BF_WRITE) || (stream->mode == BF_APPEND))
    {
        /* write out any unwritten bits */
        if (stream->bitCount != 0)
        {
            (stream->bitBuffer) <<= 8 - (stream->bitCount);
            fputc(stream->bitBuffer, stream->fp);   /* handle error? */
        }
    }

    stream->bitBuffer = 0;
    stream->bitCount = 0;

    return (returnValue);
}

/***************************************************************************
*   Function   : BitFileGetChar
*   Description: This function returns the next byte from the file passed as
*                a parameter.
*   Parameters : stream - pointer to bit file stream to read from
*   Effects    : Reads next byte from file and updates buffer accordingly.
*   Returned   : EOF if a whole byte cannot be obtained.  Otherwise,
*                the character read.
***************************************************************************/
int BitFileGetChar(bit_file_t *stream)
{
    int returnValue;
    unsigned char tmp;

    if (stream == NULL)
    {
        return(EOF);
    }

    returnValue = fgetc(stream->fp);

    if (stream->bitCount == 0)
    {
        /* we can just get byte from file */
        return returnValue;
    }

    /* we have some buffered bits to return too */
    if (returnValue != EOF)
    {
        /* figure out what to return */
        tmp = ((unsigned char)returnValue) >> (stream->bitCount);
        tmp |= ((stream->bitBuffer) << (8 - (stream->bitCount)));

        /* put remaining in buffer. count shouldn't change. */
        stream->bitBuffer = returnValue;

        returnValue = tmp;
    }

    return returnValue;
}

/***************************************************************************
*   Function   : BitFilePutChar
*   Description: This function writes the byte passed as a parameter to the
*                file passed a parameter.
*   Parameters : c - the character to be written
*                stream - pointer to bit file stream to write to
*   Effects    : Writes a byte to the file and updates buffer accordingly.
*   Returned   : On success, the character written, otherwise EOF.
***************************************************************************/
int BitFilePutChar(const int c, bit_file_t *stream)
{
    unsigned char tmp;

    if (stream == NULL)
    {
        return(EOF);
    }

    if (stream->bitCount == 0)
    {
        /* we can just put byte from file */
        return fputc(c, stream->fp);
    }

    /* figure out what to write */
    tmp = ((unsigned char)c) >> (stream->bitCount);
    tmp = tmp | ((stream->bitBuffer) << (8 - stream->bitCount));

    if (fputc(tmp, stream->fp) != EOF)
    {
        /* put remaining in buffer. count shouldn't change. */
        stream->bitBuffer = c;
    }
    else
    {
        return EOF;
    }

    return tmp;
}

/***************************************************************************
*   Function   : BitFileGetBit
*   Description: This function returns the next bit from the file passed as
*                a parameter.  The bit value returned is the msb in the
*                bit buffer.
*   Parameters : stream - pointer to bit file stream to read from
*   Effects    : Reads next bit from bit buffer.  If the buffer is empty,
*                a new byte will be read from the file.
*   Returned   : 0 if bit == 0, 1 if bit == 1, and EOF if operation fails.
***************************************************************************/
int BitFileGetBit(bit_file_t *stream)
{
    int returnValue;

    if (stream == NULL)
    {
        return(EOF);
    }

    if (stream->bitCount == 0)
    {
        /* buffer is empty, read another character */
        if ((returnValue = fgetc(stream->fp)) == EOF)
        {
            return EOF;
        }
        else
        {
            stream->bitCount = 8;
            stream->bitBuffer = returnValue;
        }
    }

    /* bit to return is msb in buffer */
    stream->bitCount--;
    returnValue = (stream->bitBuffer) >> (stream->bitCount);

    return (returnValue & 0x01);
}

/***************************************************************************
*   Function   : BitFilePutBit
*   Description: This function writes the bit passed as a parameter to the
*                file passed a parameter.
*   Parameters : c - the bit value to be written
*                stream - pointer to bit file stream to write to
*   Effects    : Writes a bit to the bit buffer.  If the buffer has a byte,
*                the buffer is written to the file and cleared.
*   Returned   : On success, the bit value written, otherwise EOF.
***************************************************************************/
int BitFilePutBit(const int c, bit_file_t *stream)
{
    int returnValue = c;

    if (stream == NULL)
    {
        return(EOF);
    }

    stream->bitCount++;
    stream->bitBuffer <<= 1;

    if (c != 0)
    {
        stream->bitBuffer |= 1;
    }

    /* write bit buffer if we have 8 bits */
    if (stream->bitCount == 8)
    {
        if (fputc(stream->bitBuffer, stream->fp) == EOF)
        {
            returnValue = EOF;
        }

        /* reset buffer */
        stream->bitCount = 0;
        stream->bitBuffer = 0;
    }

    return returnValue;
}

/***************************************************************************
*   Function   : BitFileGetBits
*   Description: This function reads the specified number of bits from the
*                file passed as a parameter and writes them to the
*                requested memory location (msb to lsb).
*   Parameters : stream - pointer to bit file stream to read from
*                bits - address to store bits read
*                count - number of bits to read
*   Effects    : Reads bits from the bit buffer and file stream.  The bit
*                buffer will be modified as necessary.
*   Returned   : EOF for failure, otherwise the number of bits read.  If
*                an EOF is reached before all the bits are read, bits
*                will contain every bit through the last complete byte.
***************************************************************************/
int BitFileGetBits(bit_file_t *stream, void *bits, const unsigned int count)
{
    unsigned char *bytes, shifts;
    int offset, remaining, returnValue;

    bytes = (unsigned char *)bits;

    if ((stream == NULL) || (bits == NULL))
    {
        return(EOF);
    }

    offset = 0;
    remaining = count;

    /* read whole bytes */
    while (remaining >= 8)
    {
        returnValue = BitFileGetChar(stream);

        if (returnValue == EOF)
        {
            return EOF;
        }

        bytes[offset] = (unsigned char)returnValue;
        remaining -= 8;
        offset++;
    }

    if (remaining != 0)
    {
        /* read remaining bits */
        shifts = 8 - remaining;

        while (remaining > 0)
        {
            returnValue = BitFileGetBit(stream);

            if (returnValue == EOF)
            {
                return EOF;
            }

            bytes[offset] <<= 1;
            bytes[offset] |= (returnValue & 0x01);
            remaining--;
        }

        /* shift last bits into position */
        bytes[offset] <<= shifts;
    }

    return count;
}

/***************************************************************************
*   Function   : BitFilePutBits
*   Description: This function writes the specified number of bits from the
*                memory location passed as a parameter to the file passed
*                as a parameter.   Bits are written msb to lsb.
*   Parameters : stream - pointer to bit file stream to write to
*                bits - pointer to bits to write
*                count - number of bits to write
*   Effects    : Writes bits to the bit buffer and file stream.  The bit
*                buffer will be modified as necessary.
*   Returned   : EOF for failure, otherwise the number of bits written.  If
*                an error occurs after a partial write, the partially
*                written bits will not be unwritten.
***************************************************************************/
int BitFilePutBits(bit_file_t *stream, void *bits, const unsigned int count)
{
    unsigned char *bytes, tmp;
    int offset, remaining, returnValue;

    bytes = (unsigned char *)bits;

    if ((stream == NULL) || (bits == NULL))
    {
        return(EOF);
    }

    offset = 0;
    remaining = count;

    /* write whole bytes */
    while (remaining >= 8)
    {
        returnValue = BitFilePutChar(bytes[offset], stream);

        if (returnValue == EOF)
        {
            return EOF;
        }

        remaining -= 8;
        offset++;
    }

    if (remaining != 0)
    {
        /* write remaining bits */
        tmp = bytes[offset];

        while (remaining > 0)
        {
            returnValue = BitFilePutBit((tmp & 0x80), stream);

            if (returnValue == EOF)
            {
                return EOF;
            }

            tmp <<= 1;
            remaining--;
        }
    }

    return count;
}

/***************************************************************************
*   Function   : BitFileGetBitsInt
*   Description: This function provides a machine independent layer that
*                allows a single function call to stuff an arbitrary number
*                of bits into an integer type variable.
*   Parameters : stream - pointer to bit file stream to read from
*                bits - address to store bits read
*                count - number of bits to read
*                size - sizeof type containing "bits"
*   Effects    : Calls a function that reads bits from the bit buffer and
*                file stream.  The bit buffer will be modified as necessary.
*                the bits will be written to "bits" from least significant
*                byte to most significant byte.
*   Returned   : EOF for failure, otherwise the number of bits read by the
*                called function.
***************************************************************************/
int BitFileGetBitsInt(bit_file_t *stream, void *bits, const unsigned int count,
    const size_t size)
{
    int returnValue;

    if ((stream == NULL) || (bits == NULL))
    {
        return(EOF);
    }

    if (stream->endian == BF_LITTLE_ENDIAN)
    {
        returnValue = BitFileGetBitsLE(stream, bits, count);
    }
    else if (stream->endian == BF_BIG_ENDIAN)
    {
        returnValue = BitFileGetBitsBE(stream, bits, count, size);
    }
    else
    {
        returnValue = EOF;
    }

    return returnValue;
}

/***************************************************************************
*   Function   : BitFileGetBitsLE   (Little Endian)
*   Description: This function reads the specified number of bits from the
*                file passed as a parameter and writes them to the
*                requested memory location (LSB to MSB).
*   Parameters : stream - pointer to bit file stream to read from
*                bits - address to store bits read
*                count - number of bits to read
*   Effects    : Reads bits from the bit buffer and file stream.  The bit
*                buffer will be modified as necessary.  bits is treated as
*                a little endian integer of length >= (count/8) + 1.
*   Returned   : EOF for failure, otherwise the number of bits read.  If
*                an EOF is reached before all the bits are read, bits
*                will contain every bit through the last successful read.
***************************************************************************/
int BitFileGetBitsLE(bit_file_t *stream, void *bits, const unsigned int count)
{
    unsigned char *bytes, shifts;
    int offset, remaining, returnValue;

    bytes = (unsigned char *)bits;

    offset = 0;
    remaining = count;

    /* read whole bytes */
    while (remaining >= 8)
    {
        returnValue = BitFileGetChar(stream);

        if (returnValue == EOF)
        {
            return EOF;
        }

        bytes[offset] = (unsigned char)returnValue;
        remaining -= 8;
        offset++;
    }

    if (remaining != 0)
    {
        /* read remaining bits */
        shifts = 8 - remaining;

        while (remaining > 0)
        {
            returnValue = BitFileGetBit(stream);

            if (returnValue == EOF)
            {
                return EOF;
            }

            bytes[offset] <<= 1;
            bytes[offset] |= (returnValue & 0x01);
            remaining--;
        }

    }

    return count;
}

/***************************************************************************
*   Function   : BitFileGetBitsBE   (Big Endian)
*   Description: This function reads the specified number of bits from the
*                file passed as a parameter and writes them to the
*                requested memory location (LSB to MSB).
*   Parameters : stream - pointer to bit file stream to read from
*                bits - address to store bits read
*                count - number of bits to read
*                size - sizeof type containing "bits"
*   Effects    : Reads bits from the bit buffer and file stream.  The bit
*                buffer will be modified as necessary.  bits is treated as
*                a big endian integer of length size.
*   Returned   : EOF for failure, otherwise the number of bits read.  If
*                an EOF is reached before all the bits are read, bits
*                will contain every bit through the last successful read.
***************************************************************************/
int BitFileGetBitsBE(bit_file_t *stream, void *bits, const unsigned int count,
    const size_t size)
{
    unsigned char *bytes, shifts;
    int offset, remaining, returnValue;

    if (count > (size * 8))
    {
        /* too many bits to read */
        return EOF;
    }

    bytes = (unsigned char *)bits;

    offset = size - 1;
    remaining = count;

    /* read whole bytes */
    while (remaining >= 8)
    {
        returnValue = BitFileGetChar(stream);

        if (returnValue == EOF)
        {
            return EOF;
        }

        bytes[offset] = (unsigned char)returnValue;
        remaining -= 8;
        offset--;
    }

    if (remaining != 0)
    {
        /* read remaining bits */
        shifts = 8 - remaining;

        while (remaining > 0)
        {
            returnValue = BitFileGetBit(stream);

            if (returnValue == EOF)
            {
                return EOF;
            }

            bytes[offset] <<= 1;
            bytes[offset] |= (returnValue & 0x01);
            remaining--;
        }

    }

    return count;
}

/***************************************************************************
*   Function   : BitFilePutBitsInt
*   Description: This function provides a machine independent layer that
*                allows a single function call to write an arbitrary number
*                of bits from an integer type variable into a file.
*   Parameters : stream - pointer to bit file stream to write to
*                bits - pointer to bits to write
*                count - number of bits to write
*                size - sizeof type containing "bits"
*   Effects    : Calls a function that writes bits to the bit buffer and
*                file stream.  The bit buffer will be modified as necessary.
*                the bits will be written to the file stream from least
*                significant byte to most significant byte.
*   Returned   : EOF for failure, otherwise the number of bits written.  If
*                an error occurs after a partial write, the partially
*                written bits will not be unwritten.
***************************************************************************/
int BitFilePutBitsInt(bit_file_t *stream, void *bits, const unsigned int count,
    const size_t size)
{
    int returnValue;

    if ((stream == NULL) || (bits == NULL))
    {
        return(EOF);
    }

    if (stream->endian == BF_LITTLE_ENDIAN)
    {
        returnValue = BitFilePutBitsLE(stream, bits, count);
    }
    else if (stream->endian == BF_BIG_ENDIAN)
    {
        returnValue = BitFilePutBitsBE(stream, bits, count, size);
    }
    else
    {
        returnValue = EOF;
    }

    return returnValue;
}

/***************************************************************************
*   Function   : BitFilePutBitsLE   (Little Endian)
*   Description: This function writes the specified number of bits from the
*                memory location passed as a parameter to the file passed
*                as a parameter.   Bits are written LSB to MSB.
*   Parameters : stream - pointer to bit file stream to write to
*                bits - pointer to bits to write
*                count - number of bits to write
*   Effects    : Writes bits to the bit buffer and file stream.  The bit
*                buffer will be modified as necessary.  bits is treated as
*                a little endian integer of length >= (count/8) + 1.
*   Returned   : EOF for failure, otherwise the number of bits written.  If
*                an error occurs after a partial write, the partially
*                written bits will not be unwritten.
***************************************************************************/
int BitFilePutBitsLE(bit_file_t *stream, void *bits, const unsigned int count)
{
    unsigned char *bytes, tmp;
    int offset, remaining, returnValue;

    bytes = (unsigned char *)bits;
    offset = 0;
    remaining = count;

    /* write whole bytes */
    while (remaining >= 8)
    {
        returnValue = BitFilePutChar(bytes[offset], stream);

        if (returnValue == EOF)
        {
            return EOF;
        }

        remaining -= 8;
        offset++;
    }

    if (remaining != 0)
    {
        /* write remaining bits */
        tmp = bytes[offset];
        tmp <<= (8 - remaining);

        while (remaining > 0)
        {
            returnValue = BitFilePutBit((tmp & 0x80), stream);

            if (returnValue == EOF)
            {
                return EOF;
            }

            tmp <<= 1;
            remaining--;
        }
    }

    return count;
}

/***************************************************************************
*   Function   : BitFilePutBitsBE   (Big Endian)
*   Description: This function writes the specified number of bits from the
*                memory location passed as a parameter to the file passed
*                as a parameter.   Bits are written LSB to MSB.
*   Parameters : stream - pointer to bit file stream to write to
*                bits - pointer to bits to write
*                count - number of bits to write
*   Effects    : Writes bits to the bit buffer and file stream.  The bit
*                buffer will be modified as necessary.  bits is treated as
*                a big endian integer of length size.
*   Returned   : EOF for failure, otherwise the number of bits written.  If
*                an error occurs after a partial write, the partially
*                written bits will not be unwritten.
***************************************************************************/
int BitFilePutBitsBE(bit_file_t *stream, void *bits, const unsigned int count,
    const size_t size)
{
    unsigned char *bytes, tmp;
    int offset, remaining, returnValue;

    if (count > (size * 8))
    {
        /* too many bits to write */
        return EOF;
    }

    bytes = (unsigned char *)bits;
    offset = size - 1;
    remaining = count;

    /* write whole bytes */
    while (remaining >= 8)
    {
        returnValue = BitFilePutChar(bytes[offset], stream);

        if (returnValue == EOF)
        {
            return EOF;
        }

        remaining -= 8;
        offset--;
    }

    if (remaining != 0)
    {
        /* write remaining bits */
        tmp = bytes[offset];
        tmp <<= (8 - remaining);

        while (remaining > 0)
        {
            returnValue = BitFilePutBit((tmp & 0x80), stream);

            if (returnValue == EOF)
            {
                return EOF;
            }

            tmp <<= 1;
            remaining--;
        }
    }

    return count;
}
