/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *        DYNAMIC MEMORY MANAGEMENT MODULE                * */
/* *                                                        * */
/* *  $Module:   MEMORY                                     * */ 
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


#ifndef _MEMORY_
#define _MEMORY_

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include "misc.h"

/**************************************************************/
/* Data structures and constants                              */
/**************************************************************/

#ifndef memory__DYNMAXSIZE
#define memory__DYNMAXSIZE   1024 /* At most blocks of size memory__DYNMAXSIZE
				     bytes are administrated by the
				     module, larger requests are
				     directly mapped to system calls */
#endif

#ifndef memory__SHAREDPAGES
#define memory__SHAREDPAGES    1  /* Number of block sizes sharing an allocated 
				     page. By setting memory__SHAREDPAGES to 4, 
				     the module would administrate requests 
				     for 1, 2, 3 and 4 bytes on the same set of 
				     pages, requests for 5, 6, 7 and 8 on another 
				     one, etc. By default every block size has 
				     its own set of pages */
#endif

#ifndef memory__FREESHREDDER
#define memory__FREESHREDDER  'S' /*  The decimal number 83, which can also be 
				      read as 53 hexadecimal, or the character 
				      'S' in ASCII code */
#endif

#define memory__KILOBYTE        1024

#ifndef memory__DEFAULTPAGESIZE
#define memory__DEFAULTPAGESIZE (8 * memory__KILOBYTE)
                                  /* Used to set the default size of a page. 
				     If the default page size is too small to 
				     contain two objects of size memory__DYNMAXSIZE
				     the default page size is automatically 
				     increased by the function memory_Init */
#endif

#ifndef memory__UNLIMITED
#define memory__UNLIMITED       (-1)
                                  /* Used to set the maximal amount of memory
				     available for the memory module to
				     "unlimited" when calling memory_Init. */
#endif

typedef struct MEMORY_RESOURCEHELP {
  POINTER free;                    /* pointer to the next free block in list  */
  POINTER next;                    /* pointer to the next fresh block         */
  POINTER page;                    /* pointer to head of page list            */
  POINTER end_of_page;             /* pointer to the end of current page      */
  int     total_size;              /* total block size inc. debug marks       */
  int     aligned_size;            /* block size without debug marks          */
  int     offset;                  /* offset of last usable block on page     */
} MEMORY_RESOURCE;

extern MEMORY_RESOURCE * memory_ARRAY[];

#if defined(CHECK)
typedef struct MEMORY_INFOHELP {
  const char * mallocInFile;       /* origin of allocation request:   file    */
  const char * freeInFile;         /* origin of deallocation request: file    */
  unsigned short int mallocAtLine; /* origin of allocation request:   line    */
  unsigned short int freeAtLine;   /* origin of deallocation request: line    */
} MEMORY_INFONODE, * MEMORY_INFO;

#endif

typedef struct MEMORY_BIGBLOCKHEADERHELP {
  struct MEMORY_BIGBLOCKHEADERHELP * previous, * next;
} MEMORY_BIGBLOCKHEADERNODE, * MEMORY_BIGBLOCKHEADER;

extern long                  memory_MAXMEM;

extern unsigned long         memory_NEWBYTES;
extern unsigned long         memory_FREEDBYTES;

extern const unsigned int    memory_MAGICMALLOC;
extern const unsigned int    memory_MAGICFREE;

extern const unsigned int    memory_ALIGN;

extern MEMORY_BIGBLOCKHEADER memory_BIGBLOCKS;

/**************************************************************/
/* Debug Information                                          */
/**************************************************************/

extern unsigned int memory_MARKSIZE;
extern unsigned int memory_OFFSET;

/**************************************************************/
/* Check Functions                                            */
/**************************************************************/

#ifdef __cplusplus
extern "C" {
#endif


#ifdef CHECK
void    memory_CheckFree(POINTER Freepointer, unsigned int Size, unsigned int RealBlockSize, const char * File, unsigned short int Line);
#endif /* CHECK */

#ifdef __cplusplus
}
#endif

/**************************************************************/
/* Inline Functions                                           */
/**************************************************************/


static __inline__ unsigned int memory_CalculateRealBlockSize(unsigned int 
							     BlockSize)
/**********************************************************
  INPUT  : Size of a block of memory.
  RETURNS: its real size.
  SUMMARY: Calculates the size of a memory block, 
           including padding due to memory alignment and
           page sharing
**********************************************************/
{  
  unsigned int RealSize;

  RealSize = BlockSize;

  if (RealSize % memory__SHAREDPAGES) {
    RealSize += memory__SHAREDPAGES - (RealSize % memory__SHAREDPAGES);
  }

  if (RealSize % memory_ALIGN) {
    RealSize += memory_ALIGN - (RealSize % memory_ALIGN);
  }

  return RealSize;

}

static __inline__ unsigned int memory_LookupRealBlockSize(unsigned int 
							  BlockSize)
/**********************************************************
  INPUT  : Size of a block of memory.
  RETURNS: its real size.
  SUMMARY: Returns the size of a memory block, 
           including padding due to memory alignment and
           page sharing.
**********************************************************/
{  

  unsigned int RealSize;

  if (BlockSize < memory__DYNMAXSIZE) {
    RealSize = memory_ARRAY[BlockSize]->aligned_size;
  }
  else {
    RealSize = memory_CalculateRealBlockSize(BlockSize);
  }

  return RealSize;

}

#ifdef CHECK
static __inline__ void memory_SetBlockStatusAndSize(POINTER Mem, 
						    unsigned int Status,
						    unsigned int Size)
/**********************************************************
  INPUT  : a pointer to a block of memory, its status
           (memory_MAGICMALLOC or memory_MAGICFREE), and
           size.
  RETURNS: None.
  SUMMARY: Sets a status flag (memory_MAGICMALLOC or
           memory_MAGICFREE) and block size.
**********************************************************/
{
  *((int *)Mem - 1) = Size; 
  *((int *)((char *)Mem + memory_LookupRealBlockSize(Size))) = Status;
}

static __inline__ unsigned int memory_GetBlockSize(POINTER Mem)
/**********************************************************
  INPUT  : A pointer to a block of memory.
  RETURNS: its size.
  SUMMARY: Returns the size of a memory block.
**********************************************************/
{
  return *((int *)Mem - 1);
}

static __inline__ unsigned int memory_GetRealBlockSize(POINTER Mem)
/**********************************************************
  INPUT  : A pointer to a block of memory.
  RETURNS: its real size.
  SUMMARY: Returns the real size of a memory block,
           including padding bytes.
**********************************************************/
{
  return memory_LookupRealBlockSize(memory_GetBlockSize(Mem));
}

static __inline__ unsigned int memory_GetBlockStatus(POINTER Mem) 
/**********************************************************
  INPUT  : A pointer to a block of memory.
  RETURNS: its status.
  SUMMARY: Returns the status of a memory block.
**********************************************************/
{
  unsigned int Size;

  Size = memory_GetBlockSize(Mem); 

  return  *((int *)((char *)Mem + memory_LookupRealBlockSize(Size)));
}

static __inline__ void memory_SetInfo(MEMORY_INFO Info,
				      const char * MallocInFile,
				      unsigned short int MallocAtLine,
				      const char * FreeInFile,
				      unsigned short int FreeAtLine)
/**********************************************************
  INPUT  : a memory info structure, strings for files where
           the block was allocated and freed, and short 
	   integers for the corresponding lines.
  RETURNS: None.
  SUMMARY: Sets the debugging information for a memory block
**********************************************************/
{
  if (!Info) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In memory_SetInfo:");
    misc_ErrorReport("\n Memory Error. Info is a NULL pointer.\n");
    misc_FinishErrorReport();
  }
 
  Info->mallocAtLine   = MallocAtLine;
  Info->mallocInFile   = MallocInFile;
  Info->freeAtLine     = FreeAtLine;
  Info->freeInFile     = FreeInFile;
}
#endif

static __inline__ unsigned long memory_DemandedBytes(void)
/**********************************************************
  INPUT  : Nothing.
  RETURNS: Maximum number of bytes allocated at the same 
           time by the module.
  SUMMARY: Returns maximum number of allocated bytes at the
           same time.
**********************************************************/
{
  return memory_NEWBYTES;
}


static __inline__ unsigned long memory_UsedBytes(void)
/**********************************************************
  INPUT  : Nothing.
  RETURNS: Number of bytes currently in use by your program.
  SUMMARY: Returns number of bytes currently allocated.
**********************************************************/
{
  return memory_NEWBYTES-memory_FREEDBYTES;
}

#ifdef NO_MEMORY_MANAGEMENT

static __inline__ void memory_Free(POINTER Freepointer, unsigned int Size)
{
  free((char*)Freepointer);
}

#else

#ifdef CHECK
static __inline__ void memory_FreeIntern(POINTER  Freepointer, 
					 unsigned int Size, 
					 const char * File, 
					 unsigned short int Line)
#else
static __inline__ void memory_Free(POINTER Freepointer, unsigned int Size)
#endif
/**********************************************************
  INPUT  : Pointer to the block of memory to be freed, 
           and the block's size
  RETURNS: Nothing.
  SUMMARY: Frees a block of memory for reallocation.
           This function performs correctness checks
	   in debugging mode.
**********************************************************/
{ 
  unsigned int RealBlockSize; /* block큦 alignment correct size */

  RealBlockSize = memory_LookupRealBlockSize(Size);

#ifdef CHECK
  memory_CheckFree(Freepointer, Size, RealBlockSize, File, Line);
#endif


  /* Check if current block is a big block */ 
  if (Size >= memory__DYNMAXSIZE) {
    /* if that큦 true, remove it from the double linked big block list */
    MEMORY_BIGBLOCKHEADER BigBlockHeader;

    BigBlockHeader = 
      (MEMORY_BIGBLOCKHEADER) ((char *) Freepointer - memory_OFFSET
			       - sizeof(MEMORY_BIGBLOCKHEADERNODE));

    /* Check if current big block is the first block in the list */
    if (BigBlockHeader->previous != NULL) {
      /* if that큦 not true, set previous block큦 successor
	 to current block큦 successor
      */
      BigBlockHeader->previous->next = BigBlockHeader->next;
    }
    else {
      /* otherwise set the first block in the big blocks list
	 to current block큦 successor
      */
      memory_BIGBLOCKS = BigBlockHeader->next;
    }

    /* Check if current block is the last block in the list */
    if (BigBlockHeader->next != NULL) {
      /* if that큦 not true, set next block� predecessor to
	 current block큦 predecessor 
      */
      BigBlockHeader->next->previous = BigBlockHeader->previous;
    }

    /* Adapt total number of freed bytes 
       and number of bytes available for allocation
       accordingly
    */
    memory_FREEDBYTES       += RealBlockSize + memory_MARKSIZE + 
      sizeof(MEMORY_BIGBLOCKHEADERNODE);

    if (memory_MAXMEM >= 0) {
      memory_MAXMEM           += RealBlockSize + memory_MARKSIZE + 
	sizeof(MEMORY_BIGBLOCKHEADERNODE);
    }

    /* pass the call though to free() with correct pointer value */
#ifdef CHECK
    free((char *)Freepointer - memory_OFFSET 
	 - sizeof(MEMORY_BIGBLOCKHEADERNODE));
#else
    free((char*) Freepointer - sizeof(MEMORY_BIGBLOCKHEADERNODE));
#endif
  }
  else {
    /* current block is not a big block */
    /* Adapt number of allocated bytes 
       and the freed blocks list accordingly 
    */
    memory_FREEDBYTES       += memory_ARRAY[Size]->total_size;
    *(POINTER *)Freepointer  = memory_ARRAY[Size]->free;
    memory_ARRAY[Size]->free = Freepointer;
  }

}

#endif

/**************************************************************/
/* Functions                                                  */
/**************************************************************/

#ifdef __cplusplus
extern "C" {
#endif


void    memory_Init(long);
void    memory_Restrict(long);

void    memory_Print(void);
void    memory_FPrint(FILE*);
  
void    memory_PrintLeaks(void);
void    memory_PrintDetailed(void);
void    memory_PrintAllocatedBlocks(unsigned int Size);
void    memory_PrintFreedBlocks(unsigned int Size);
void    memory_PrintAllocatedBigBlocks(void);
  
void    memory_FreeAllMem(void);

#ifdef __cplusplus
}
#endif

#if defined(CHECK) && !defined(NO_MEMORY_MANAGEMENT)
/* declare drop-in debug versions memory functions */
#ifdef __cplusplus
extern "C" {
#endif
POINTER memory_MallocIntern(unsigned int, const char *, unsigned short int);
POINTER memory_CallocIntern(unsigned int,
			    unsigned int, 
			    const char *, 
			    unsigned short int);
#ifdef __cplusplus
}
#endif
#define memory_Malloc(Size) memory_MallocIntern((Size), __FILE__, __LINE__)
#define memory_Calloc(Elements, Size) \
memory_CallocIntern((Elements), (Size), __FILE__, __LINE__)
#define memory_Free(Pointer, Size) \
memory_FreeIntern((Pointer), (Size), __FILE__, __LINE__)
#else
#ifdef __cplusplus
extern "C" {
#endif
POINTER memory_Malloc(unsigned int);
POINTER memory_Calloc(unsigned int, unsigned int);
#ifdef __cplusplus
}
#endif
#endif

#endif
