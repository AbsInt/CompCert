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

#include "memory.h"

unsigned int  memory_PAGESIZE;   /* size of a page                            */
long          memory_MAXMEM;     /* amount of memory available for allocation */
static int    memory__EOF = EOF; /* internal "End Of Memory" marker           */
unsigned long memory_NEWBYTES;   /* number of allocated bytes                 */
unsigned long memory_FREEDBYTES; /* number of freed bytes                     */

const unsigned int memory_ALIGN = sizeof(POINTER); 
/* Crucial: hardware must support access to words 
   of size POINTER.
*/

#ifdef CHECK
unsigned int memory_LEFTTAG;     /* size of left debug mark                   */
unsigned int memory_OFFSET;      /* alignment-correct size of left debug mark */
unsigned int memory_MARKSIZE;    /* total size of debug marks                 */

BOOL         memory_MANAGEMENT_INITIALIZED = FALSE;

#else  /* CHECK not defined */
unsigned int memory_MARKSIZE = 0;
unsigned int memory_OFFSET   = 0;
#endif /* CHECK */

const unsigned int memory_MAGICMALLOC = 1; /* "block allocated" marker */
const unsigned int memory_MAGICFREE   = 2; /* "block freed" marker     */

/* Internal array of resources for different block sizes */
/* ... + 1 to support odd values for memory__SHAREDPAGES like 7 */
static MEMORY_RESOURCE memory_PAGES[memory__DYNMAXSIZE/memory__SHAREDPAGES + 1];


/* Resources for all administrated block sizes */
MEMORY_RESOURCE * memory_ARRAY[memory__DYNMAXSIZE];

/* double linked list for administering blocks of memory
   whose size is greater or equal to memory__DYNMAXSIZE.
*/ 
MEMORY_BIGBLOCKHEADER memory_BIGBLOCKS = NULL;

/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  INITIALIZATION                                        * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

#ifdef CHECK
static BOOL memory_ManagementInitialized(void)
/**********************************************************
   INPUT  : None.
   RETURNS: TRUE if memory management is already initialized,
            else FALSE.
   SUMMARY: Checks if memory_Init was called.
**********************************************************/
{
  return memory_MANAGEMENT_INITIALIZED;
}
#endif /* CHECK */

void memory_Init(long Maxmem)
/*************************************************************
  INPUT  : The maximal amount of memory available in bytes 
           for the memory module; if Maxmem < 0 the module 
           allocates as much memory as available from the 
           system.
  RETURNS: None.
  SUMMARY: Initializes the memory management. It has to be 
           called before you can perform any module operation. 
           This function automatically increases the default 
           page size if it is too small for two objects of 
           size memory__DYNMAXSIZE.
*************************************************************/
{
  int i;
  int extra;             /* size of internally used space on each page  */

  memory_FREEDBYTES = 0; /* set total number of freed bytes to zero     */
  memory_NEWBYTES   = 0; /* set total number of allocated bytes to zero */

  /* set the size of a page we allocate from the operating system */
  memory_PAGESIZE   = memory__DEFAULTPAGESIZE;

#ifdef CHECK

  /* Test if memory management has already been initialized */
 
  if (!memory_ManagementInitialized()) {
    /* if that is not the case, set check variable to TRUE */
    memory_MANAGEMENT_INITIALIZED = TRUE;
  }
  else {
    /* otherwise the user is trying initialize it for a 
       second time, so print an error and exit.
    */
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In memory_Init:");
    misc_UserErrorReport("\n Memory Error.");
    misc_UserErrorReport(" Trying to initialize memory management");
    misc_UserErrorReport(" for a second time.\n");
    misc_FinishUserErrorReport();
  }

  /* Calculate the size of debug marks */
  memory_LEFTTAG  = sizeof(MEMORY_INFONODE) + sizeof(unsigned int);

  if ((sizeof(MEMORY_INFONODE) + sizeof(unsigned int)) % memory_ALIGN == 0) {
    memory_OFFSET   = memory_LEFTTAG;
  }
  else {
    memory_OFFSET   = memory_LEFTTAG + memory_ALIGN 
      - (memory_LEFTTAG % memory_ALIGN);
  }

  if ((sizeof(unsigned int) % memory_ALIGN) == 0) {
    memory_MARKSIZE =  memory_OFFSET + sizeof(unsigned int);
  }
  else {
    memory_MARKSIZE =  memory_OFFSET + sizeof(unsigned int) + memory_ALIGN 
      - (sizeof(unsigned int) % memory_ALIGN);
  }
#endif

  /* Calculate the size of internally used space on each page */
  /* extra: One pointer for chaining pages, one for EOF (+ marksize) */
  extra = 2*sizeof(POINTER) + memory_MARKSIZE; 


  /* Test whether page size is reasonable with respect 
     to dynamic allocation threshold
  */
  while (memory_PAGESIZE < (2*(memory__DYNMAXSIZE + memory_MARKSIZE) + extra)) {
    /* Minimum two objects per allocated page */
    memory_PAGESIZE += memory__DEFAULTPAGESIZE/2;    
  }

  /* Set amount of memory available to the module for allocation */
  if (Maxmem <= 0) {
    /* unlimited (limited only by the operating system) */
    memory_MAXMEM = memory__UNLIMITED;
  }
  else {
    /* Maxmem bytes */
    memory_MAXMEM = Maxmem;
  }

  /* Initialize memory_ARRAY and memory_RESOURCEs */
  for (i=1; i<memory__DYNMAXSIZE; i++) {
    MEMORY_RESOURCE *CurrentResource;
    int             TotalSize;

    /* Map memory_ARRAY[i] to appropriate Resource */
    memory_ARRAY[i]               = &memory_PAGES[(i-1)/memory__SHAREDPAGES];

    CurrentResource = memory_ARRAY[i];

    CurrentResource->free            = &memory__EOF; /* no blocks freed     */
    CurrentResource->next            = &memory__EOF; /* no blocks allocated */
    CurrentResource->end_of_page     = &memory__EOF; /* no (end of) page    */
    CurrentResource->page            = &memory__EOF; /* no page allocated   */

    /* Size of a properly aligned block of requested size i */
    CurrentResource->aligned_size    = memory_CalculateRealBlockSize(i);

    /* Total block size including debug marks */
    CurrentResource->total_size      = memory_MARKSIZE 
      + CurrentResource->aligned_size;

    TotalSize                        = CurrentResource->total_size;

    /* last block큦 offset */
    CurrentResource->offset          =
      ((memory_PAGESIZE-extra)/TotalSize)*TotalSize 
      + sizeof(POINTER) + memory_OFFSET;
  }
}


void memory_Restrict(long Maxmem)
/*************************************************************
  INPUT  : The maximal amount of memory available for further 
           allocation (in bytes); if Maxmem < 0 future 
           allocations are unrestricted.
  RETURNS: None.
  SUMMARY: Sets the maximal amount of memory available for 
           future allocations. If the user tries to allocate 
           more memory, the module displays an error message 
           and terminates the program by calling the exit() 
           function.
*************************************************************/
{
  /* Reset the maximum amount of memory available */ 
  if (Maxmem <= 0) {
    /* unlimited */
    memory_MAXMEM = memory__UNLIMITED;
  }
  else {
    /* Maxmem bytes */
    memory_MAXMEM = Maxmem;
  }
}

/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  CHECK CODE                                            * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

#ifdef CHECK
static void memory_CheckIfModuleIsInitialized(const char * Function,
				       const char * File,
				       unsigned short int Line)
/********************************************************
  INPUT  : The name of the function that requests the
           check, the name of the file and the line, 
	   where the requesting function was called, and
	   the line.
  RETURNS: None.
  SUMMARY: Checks if the memory management module has
           been properly initialized. You need to
	   initialize the module by calling memory_Init
	   before you use any functions from the module.
	   If the check fails, this function prints an
	   error message and exits the application.
*********************************************************/
{
  if (!memory_ManagementInitialized()) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In %s:", Function);
    misc_UserErrorReport("\n Memory Error.");
    misc_UserErrorReport(" Memory management is not initialized.");
    misc_UserErrorReport("\n You have to call memory_Init()");
    misc_UserErrorReport(" before you can use memory management functions.\n");
    misc_UserErrorReport("\n Error occurred in %s", Function);
    misc_UserErrorReport(" called from file %s at line %d.\n",
			 File, Line);
    misc_FinishUserErrorReport();
  }
}

static void memory_CheckIfPointerIsAlreadyFreed(POINTER Pointer,
					 const char * Function,
					 const char * File,
					 unsigned short int Line)
/********************************************************
  INPUT  : The pointer to be checked, the name of the
           function that requests the check, the name of
	   the file and the line, where the requesting
	   function was called, and the line.
  RETURNS: None.
  SUMMARY: Checks if the pointer has already been freed.
	   If the check fails, this function prints an
	   error message and exits the application.
*********************************************************/
{
  if ( memory_GetBlockStatus(Pointer) == memory_MAGICFREE) {
    MEMORY_INFO  Info;          /* block큦 debug information      */

    Info = (MEMORY_INFO) ((char *) Pointer - memory_OFFSET);

    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In %s:", Function);
    misc_UserErrorReport("\n Memory Error.");
    misc_UserErrorReport(" Pointer %p was allocated in file %s at line %d.",
			 Pointer, Info->mallocInFile, Info->mallocAtLine);
    misc_UserErrorReport("\n It has already been freed in file %s at line %d.",
			 Info->freeInFile, Info->freeAtLine);
    misc_UserErrorReport("\n Size of memory block is %d bytes.",
			 memory_GetBlockSize(Pointer));
    misc_UserErrorReport("\n Error occurred in %s", Function);
    misc_UserErrorReport(" called from file %s at line %d.\n",
			 File, Line);
    misc_FinishUserErrorReport();
  }
}

static void memory_CheckPointer(POINTER Pointer, unsigned int Size) 
/*********************************************************
  INPUT  : A pointer to a block of memory, and its size.
  RETURNS: Nothing.
  SUMMARY: Checks whether a pointer points to a valid
           block of memory.
	    
           This function performs the following tests:

           Is Pointer a NULL pointer?

           Is Size equal to zero?

           Is the Pointer alignment correct?
	
           Did someone write over the memory block 
           boundaries?

           Is Size still correct?

           If Size is greater than memory__DYNMAXSIZE: 
           Is it properly administrated by the module?

           If the memory block was freed: Did someone 
           write to it after deallocation?
*********************************************************/
{

  MEMORY_INFO Info;
  unsigned int BlockSize, RealBlockSize, BlockStatus;

  Info = (MEMORY_INFO) ((char *) Pointer - memory_OFFSET);

  RealBlockSize = memory_LookupRealBlockSize(Size);

  if (Pointer == NULL) {
    /* NULL pointers must not be dereferenced */
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In memory_CheckPointer:");
    misc_UserErrorReport("\n Memory Error. Pointer is a NULL pointer.\n");
    misc_FinishUserErrorReport();
  }


  if (Size == 0) {
    /* We don큧 allocate 0 byte sized blocks */
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In memory_CheckPointer:");
    misc_UserErrorReport("\n Memory Error.");
    misc_UserErrorReport(" Pointer %p points to a block of memory", Pointer);
    misc_UserErrorReport(" with size 0.\n"); 
    misc_FinishUserErrorReport();
  }

  if ((unsigned long)Pointer % (unsigned long)memory_ALIGN){
    /* we expect all pointers to be correctly aligned */
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In memory_CheckPointer:");
    misc_UserErrorReport("\n Memory Error.");
    misc_UserErrorReport(" Pointer %p is not a legal pointer.\n", Pointer);
    misc_FinishUserErrorReport();
  }

  /* BlockStatus and BlockSize are initialized after
     we can be sure Pointer is properly aligned.
  */

  BlockStatus   = memory_GetBlockStatus(Pointer);
  BlockSize     = memory_GetBlockSize(Pointer);

  if (BlockStatus != memory_MAGICMALLOC 
      && BlockStatus != memory_MAGICFREE) {

    /* we expect block status to be either 
       memory_MAGICMALLOC or memory_MAGICFREE.
       Other values might result from overwriting,
       trying to return an unallocated block,
       or trying to return a block allocated with
       another allocator.
    */

    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In memory_CheckPointer:");
    misc_UserErrorReport("\n Memory Error.");
    misc_UserErrorReport(" Pointer %p was not (de)allocated by the module,",
			 Pointer);
    misc_UserErrorReport("\n or the memory block was corrupted.\n");
    misc_FinishUserErrorReport();
  }

  if (BlockStatus == memory_MAGICMALLOC) {
    if (BlockSize != Size) {
      
      /* we expect block size in a block큦 debug
	 information and given block size to match.
      */

      misc_StartUserErrorReport();
      misc_UserErrorReport("\n In memory_CheckPointer:");
      misc_UserErrorReport("\n Memory Error.");
      misc_UserErrorReport(" Pointer %p was apparently allocated for",
			   Pointer);
      misc_UserErrorReport(" a block of size %d,",
			   BlockSize);
      misc_UserErrorReport("\n but it is expected to be a block of size %d.",
			   Size);
      misc_UserErrorReport("\n Probably the memory block was corrupted.\n");
      misc_FinishUserErrorReport();

      /* since the left dog tag seems to be corrupted we can not safely assume 
	 that our memory info structure is still valid so we can't print it*/
    }

    if ((Size % memory_ALIGN) || (Size % memory__SHAREDPAGES)) {
      /* check the fillbytes between used storage 
	 and dog tag for overwriting */
      char * ptr, * limit;
      
      limit    = (char *)Pointer + RealBlockSize;
      
      for (ptr = (char *)Pointer + Size; ptr < limit; ptr++) {
	if (*ptr != memory__FREESHREDDER) {
	  misc_StartUserErrorReport();
	  misc_UserErrorReport("\n In memory_CheckPointer:");
	  misc_UserErrorReport("\n Memory Error.");
	  misc_UserErrorReport(" Pointer %p was allocated in file %s at line %d,",
			       Pointer, Info->mallocInFile, Info->mallocAtLine);
	  misc_UserErrorReport("\n for a block of size %d.",
			       BlockSize);
	  misc_UserErrorReport("\n The memory block was corrupted.\n");
	  misc_FinishUserErrorReport();
	}
      }
    }
  }

  if (Size >= memory__DYNMAXSIZE) {
    /* we expect big blocks to be correctly linked */
    MEMORY_BIGBLOCKHEADER BigBlockHeader;

    BigBlockHeader = (MEMORY_BIGBLOCKHEADER) ((char *) Pointer - memory_OFFSET 
					      - sizeof(MEMORY_BIGBLOCKHEADERNODE));

    /* this test might crash the program
       if something is wrong with the pointers,
       so you may not get a message every time.
    */
    if (((BigBlockHeader->previous != NULL) 
	 && (BigBlockHeader->previous->next != BigBlockHeader))
	|| ((BigBlockHeader->previous == NULL) 
	    && (memory_BIGBLOCKS != BigBlockHeader))
	|| ((BigBlockHeader->next != NULL) 
	    && (BigBlockHeader->next->previous != BigBlockHeader))) {
      
      misc_StartUserErrorReport();
      misc_UserErrorReport("\n In memory_CheckPointer:");
      misc_UserErrorReport("\n Memory Error.");
      misc_UserErrorReport(" Pointer %p was not allocated by the module,",
			   Pointer);
      misc_UserErrorReport("\n or the memory block was corrupted.\n");
      misc_FinishUserErrorReport();
    }
  }
  
  if (BlockStatus == memory_MAGICFREE) {
    /* test if someone wrote over freed memory */
    char * ptr, * limit;
    
    limit = (char *)Pointer + RealBlockSize;

    for (ptr = (char *)Pointer + sizeof(POINTER); ptr < limit ; ptr++){
      /* first sizeof(POINTER) bytes are reserved for the
	 pointer to the next freed block in the list. All
	 other bytes in the block should still have the value
	 of memory__FREESHREDDER
      */
      if (*ptr != memory__FREESHREDDER) {
	misc_StartUserErrorReport();
	misc_UserErrorReport("\n In memory_CheckPointer:");
	misc_UserErrorReport("\n Memory Error.");
	misc_UserErrorReport(" Pointer %p was allocated in file %s at line %d",
			     Pointer, Info->mallocInFile, Info->mallocAtLine);
	misc_UserErrorReport("\n for a block of size %d",BlockSize);
	misc_UserErrorReport("\n and freed in file %s at line %d.",
			     Info->freeInFile, Info->freeAtLine);
	misc_UserErrorReport("\n The memory block was used after deallocation.\n");
	misc_FinishUserErrorReport();
      }
    }
  }
}

void memory_CheckFree(POINTER Freepointer, unsigned int Size,
		      unsigned int RealBlockSize, const char * File,
		      unsigned short int Line)
/**********************************************************
   INPUT  : The pointer to be freed, the size of the block
            it is supposed to point to, the real size of
	    that block, the file and line where memory_Free
	    was called.
   RETURNS: None.
   SUMMARY: Checks if memory management was initialized,
            the given pointer is legal, and not freed
	    already. It also zeroes the freed memory, and
	    sets the block's debug and administration
	    information.
**********************************************************/
{
  MEMORY_INFO  Info;          /* block큦 debug information      */

  /* Check if memory management was initialized */
  memory_CheckIfModuleIsInitialized("memory_Free", File, Line);

  /* Check if given pointer is legal */
  memory_CheckPointer(Freepointer, Size);

  /* Check if current pointer is being freed for a second time */
  memory_CheckIfPointerIsAlreadyFreed(Freepointer, "memory_Free", File, Line);

  /* Set all bytes to zero, so we can detect overwriting of freed memory */
  memset (Freepointer, memory__FREESHREDDER, RealBlockSize);

  /* Get current block큦 debug information */
  Info = (MEMORY_INFO) ((char *) Freepointer - memory_OFFSET);

  /* Set block큦 debug and administration information */
  memory_SetInfo(Info,Info->mallocInFile, Info->mallocAtLine, File, Line);
  memory_SetBlockStatusAndSize(Freepointer, memory_MAGICFREE, Size);
}
#endif /* CHECK */

/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  MALLOC                                                * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

#ifdef NO_MEMORY_MANAGEMENT

POINTER memory_Malloc(unsigned int Bytes)
{
  char *mem; /* pointer to memory block obtained from malloc */

  /* Pass the call through to compiler큦 malloc */
  mem = (char *)malloc(Bytes);

  /* If malloc fails print an error message and exit */
  if (mem == NULL) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In memory_Malloc:");
    misc_UserErrorReport("\n Memory Error. Out of memory.\n");
    misc_FinishUserErrorReport();
  }

  return mem;
}

#else

#ifdef CHECK
POINTER memory_MallocIntern(unsigned int Bytes, 
			    const char * File, 
			    unsigned short int Line)
#else
POINTER memory_Malloc(unsigned int Bytes)
#endif
/********************************************************
  INPUT  : The size of the requested memory block.      
  RETURNS: A pointer to a block of <Bytes> bytes.       
  SUMMARY: Allocates a memory block of requested length.
  EXCEPT : Trying to allocate 0 bytes, violating a memory 
           restriction, or running out of system memory 
    	   cause the function to print an error message and 
	   call exit().
*********************************************************/
{
  char                *NewMemory;       /* pointer to allocated memory */

  MEMORY_RESOURCE     *Resource;        /* current page resource,
					   required if we do not allocate 
					   a big block */

#ifdef CHECK
  MEMORY_INFO         NewInfo;          /* Storage for file and line 
					   of allocation */
#endif


#ifdef CHECK
  /* Is the module initialized? */
  memory_CheckIfModuleIsInitialized("memory_Malloc", File, Line);

  /* Is it a request for a block of zero bytes? */
  if (Bytes == 0) {
    /* The latest draft for the ANSI C 9X standard says in section 7.20.3:

       "If the size of the space requested is zero, the behavior is
        implementation-defined: either a null pointer is returned, or
	the behavior is as if the size were some nonzero value,
	except that the pointer shall not be used to access an object."

	We have decided to print an error and exit upon such requests 
	since they are often originated by a bug. 

	Nonstandard but hopefully helpful.
    */

    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In memory_Malloc:");
    misc_UserErrorReport("\n Memory Error. Tried to allocate 0 Bytes!");
    misc_UserErrorReport("\n Error occurred in memory_Malloc");
    misc_UserErrorReport(" called from file %s at line %d.\n",
			 File, Line);
    misc_FinishUserErrorReport();
  }
#endif
  
  /* If it is a big block, then it has to be 
     administrated in a special way 
  */
  if (Bytes >= memory__DYNMAXSIZE) {
    unsigned int        RealBigBlockSize; /* real block size including 
					     padding,header 
					     and debug marks */

    /* This is what a big block looks like:

       --------------------------------------------------------------------
       | MEMORY_BIGBLOCKHEADERNODE   | debug marks | char * | debug marks |
       | previous and next big block |in debug mode| block  |in debug mode|
       --------------------------------------------------------------------
    */


    /* Calculate the real size of the big block, 
       from the size of administration information,
       the size of debug marks and the requested block size
    */

    RealBigBlockSize = sizeof(MEMORY_BIGBLOCKHEADERNODE) + 
      memory_MARKSIZE + memory_CalculateRealBlockSize(Bytes);

    /* Check for violation of maximum allocation limit */
    if (memory_MAXMEM >= 0) {
      /* there is a maximum allocation limit, 
	 let큦 see if there is enough left 
      */
      if ((unsigned int)memory_MAXMEM < RealBigBlockSize) {
	/* if it is not print an error message and exit */
	misc_StartUserErrorReport();
	misc_UserErrorReport("\n In memory_Malloc:");
	misc_UserErrorReport("\n Memory Error.");
	misc_UserErrorReport(" Terminated by user given memory restriction,\n");
	misc_UserErrorReport("\n while trying to allocate %lu bytes.\n", 
			     RealBigBlockSize);
	misc_UserErrorReport("\n Maximum amount of memory");
	misc_UserErrorReport(" left for allocation is %l bytes.\n", 
			     memory_MAXMEM);
#ifdef CHECK
	misc_UserErrorReport("\n Error occurred in memory_Malloc");
	misc_UserErrorReport(" called from file %s at line %d.\n",
			     File, Line);
#endif
	misc_FinishUserErrorReport();
      } 
      else
	/* otherwise subtract the real block size 
	   from the amount of memory available for 
	   allocation
	*/
	memory_MAXMEM -= RealBigBlockSize;
    }

    /* allocate a fresh block of memory via a call to malloc */
    NewMemory = (char *)malloc(RealBigBlockSize);

    /* Check if allocation was successful */
    if (NewMemory != NULL) {

      /* if it was, then administrate the fresh block:
	 insert it into the big block list. The list 
	 is double linked for fast deletion 
      */

      MEMORY_BIGBLOCKHEADER NewBigBlock; /* new block큦 administration 
					    information */

      /* insert the fresh block as the first list element */
      NewBigBlock = (MEMORY_BIGBLOCKHEADER) NewMemory;
      NewBigBlock->next = memory_BIGBLOCKS;
      NewBigBlock->previous = NULL;

      /* if there are already elements in the big block list,
	 change the first element큦 pointer to the previous block
	 to point to the fresh block큦 administration information
      */
      if (memory_BIGBLOCKS != NULL) {
	memory_BIGBLOCKS->previous = NewBigBlock;
      }

      /* reset the big block list pointer to point to the fresh block */ 
      memory_BIGBLOCKS = NewBigBlock;

      /* skip the administration information */
      NewMemory += sizeof(MEMORY_BIGBLOCKHEADERNODE);

#ifdef CHECK
      /* set the debug information address */
      NewInfo = (MEMORY_INFO) NewMemory;

      /* skip left debug mark */
      NewMemory += memory_OFFSET;
#endif

      /* add block큦 real size to the total sum of allocated bytes */
      memory_NEWBYTES    += RealBigBlockSize;
    }
    else {
      /* NewMemory == NULL. 
	 malloc could not allocate a memory block of required size,
	 so we print an error message and exit 
      */
      misc_StartUserErrorReport();
      misc_UserErrorReport("\n In memory_MallocIntern:");
      misc_UserErrorReport("\n Memory Error. Out of memory.");
      misc_UserErrorReport("\n Failed to allocate %d bytes.\n", 
			   RealBigBlockSize);
#ifdef CHECK
      misc_UserErrorReport("\n Error occurred in memory_Malloc");
      misc_UserErrorReport(" called from file %s at line %d.\n",
			   File, Line);
#endif
      misc_FinishUserErrorReport();
    }
  }
  else {
    /* Bytes < memory__DYNMAXSIZE.
       A memory request for a manageable size 
    */

    /* Initialize the memory resource for the given size */
    Resource = memory_ARRAY[Bytes];


    /* Check if there are freed blocks of that size */
    if (*((int *)Resource->free) != EOF) {

      /* if that is the case, then use an already freed block */

      NewMemory                 = (char *) Resource->free;

      /* update the free blocks list for that size */
      Resource->free            = *((POINTER *)(NewMemory));

      /* subtract block큦 total size from the sum of freed bytes */
      memory_FREEDBYTES        -= Resource->total_size;

#ifdef CHECK
      /* calculate the address of the block큦 debug information */ 
      NewInfo = (MEMORY_INFO) ((char*) NewMemory - memory_OFFSET);

      /* Check if the block has been used after deallocation */
      memory_CheckPointer(NewMemory, Bytes);  
#endif
    } 
    else { 
      /* there are no already freed blocks of that size */
 
      /* Check if there is enough space left on current page */
      if (Resource->next != Resource->end_of_page) {

	/* if that is the case, then use a fresh block from current page */
	NewMemory                = (char *)Resource->next;

	/* update the pointer to the next usable block */
	Resource->next           = NewMemory + Resource->total_size;

	/* add block큦 total size to the sum of allocated bytes */
	memory_NEWBYTES         += Resource->total_size;

#ifdef CHECK
	/* Check if the fresh block큦 address is sane */
	if ((char *)NewMemory > (char *) Resource->end_of_page) {
	  /* if it is not, then we have detected an internal error
	     in the module itself. Oops! So we print an error message
	     and abort, hoping that the core dump will enable us to 
	     trace the error back to its origin
	  */
	  misc_StartErrorReport();
	  misc_ErrorReport("\n In memory_Malloc:");
	  misc_ErrorReport("\n Memory Error. Address overflow %d.",Bytes);
	  misc_ErrorReport("\n Error occurred in memory_Malloc");
	  misc_ErrorReport(" called from file %s at line %d.\n", File, Line);
	  misc_FinishErrorReport();
	}

	/* if all is well, we initialize the pointer to fresh block큦
	   debug information 
	*/
	NewInfo = (MEMORY_INFO)((char*) NewMemory - memory_OFFSET);
#endif

      } 
      else { 
	/* Check for violation of maximum allocation limit */
	if (memory_MAXMEM >=0) {
	  /* there is a maximum allocation limit, 
	     let큦 see if there is enough left
	  */
	  if ((unsigned int)memory_MAXMEM < memory_PAGESIZE) {
	    /* if it is not, then print an error message and exit */
	    misc_StartUserErrorReport();
	    misc_UserErrorReport("\n In memory_Malloc:");
	    misc_UserErrorReport("\n Memory Error.");
	    misc_UserErrorReport(" Terminated by user given memory restriction.\n");
#ifdef CHECK
	    misc_UserErrorReport("\n Error occurred in memory_Malloc");
	    misc_UserErrorReport(" called from file %s at line %d.\n",
				 File, Line);
#endif
	    misc_FinishUserErrorReport();
	  } 
	  else {
	    /* otherwise subtract the page size from the limit */
	    memory_MAXMEM -= memory_PAGESIZE;
	  }
	}

	/* try to allocate a new page via malloc */
	NewMemory=(char *)malloc(memory_PAGESIZE);

	/* check if allocation was successful */
	if (NewMemory == NULL) {
	  /* if it wasn큧 print an error message and exit */
	  misc_StartUserErrorReport();
	  misc_UserErrorReport("\n In memory_Malloc:");
	  misc_UserErrorReport("\n Memory Error.");
	  misc_UserErrorReport(" Terminated, ran out of system memory.\n");
#ifdef CHECK
	  misc_UserErrorReport("\n Error occurred in memory_Malloc");
	  misc_UserErrorReport(" called from file %s at line %d.\n",
			       File, Line);
#endif
	  misc_FinishUserErrorReport();
	}

	/* otherwise administrate the fresh page,
	   i.e insert it as the first element of the 
	   page list for the given size 
	*/
	*((POINTER *)NewMemory)     = Resource->page;
	Resource->page              = NewMemory;

	/* add block큦 total size to the sum of allocated bytes */
	memory_NEWBYTES            += Resource->total_size;

	/* set the end of page pointer for the fresh page */
	Resource->end_of_page       = (char *) NewMemory + Resource->offset;

	/* skip the page list */
	NewMemory += sizeof(POINTER);

#ifdef CHECK
	/* set the debug information address */
	NewInfo    = (MEMORY_INFO) NewMemory;

	/* skip the left debug mark */
	NewMemory += memory_OFFSET;
#endif

	/* update the pointer to the next usable block */	
	Resource->next              = NewMemory + Resource->total_size;
      }
    }
  }

#ifdef CHECK
  /* Set block큦 debug information */
  memory_SetInfo(NewInfo, File, Line, NULL, 0);
  memory_SetBlockStatusAndSize(NewMemory,  
			       memory_MAGICMALLOC, Bytes);

  /* delete all block큦 usable bytes with a shredder value */
  memset(NewMemory, memory__FREESHREDDER,
	 memory_LookupRealBlockSize(Bytes));
#endif

  return NewMemory;
}

#endif



#ifdef NO_MEMORY_MANAGEMENT

POINTER memory_Calloc(unsigned int Elements, unsigned int Bytes)
{
  char *mem; /* pointer to memory block obtained from calloc */

  /* Pass call through to compiler큦 calloc */
  mem = (char *)calloc(Elements, Bytes);
  
  /* If calloc fails print an error message and exit */
  if (mem == NULL) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In memory_Calloc:");
    misc_UserErrorReport("\n Memory Error. Out of memory.\n");
    misc_FinishUserErrorReport();
  }

  return mem;
}

#else

#ifdef CHECK
POINTER memory_CallocIntern(unsigned int Elements, unsigned int Bytes, 
			    const char * File, unsigned short int Line)
#else
POINTER memory_Calloc(unsigned int Elements, unsigned int Bytes)
#endif
/********************************************************
  INPUT  : The number of requested equally huge blocks, 
           and each block's size.
  RETURNS: A pointer to a block of (Bytes * Elements) bytes.
  SUMMARY: Allocates a memory block of requested length
           filled with char value '\0'.
*********************************************************/
{
  char       * mem; /* pointer to memory block obtained from the module */

  /* Allocate memory via our memory management */
#ifdef CHECK
  mem = (char *)memory_MallocIntern(Elements * Bytes, File, Line);
#else
  mem = (char *)memory_Malloc(Elements * Bytes);
#endif

  /* If allocation was successful set all bytes to zero */ 
  if (mem != NULL) {
    memset(mem,0, Elements * Bytes);
  }
  /* otherwise print an error message and exit */
  else {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In memory_Calloc:");
    misc_UserErrorReport("\n Memory Error. Out of memory.\n");
#ifdef CHECK
    misc_UserErrorReport("\n Error occurred in memory_Calloc");
    misc_UserErrorReport(" called from file %s at line %d.\n",
			 File, Line);
#endif
    misc_FinishUserErrorReport();
  }

  return mem;
}
#endif

void memory_FreeAllMem(void) 
/**************************************************************
  INPUT  : None.
  RETURNS: None.
  SUMMARY: Frees all memory allocated by calls to the module.
***************************************************************/
{
  int i;

  /* delete all pages first by going through the memory_ARRAY.
     This is slower than traversing the array memory_PAGES
     directly, but is easier to implement correctly. Since
     the only reasonable way to call memory_FreeAllMem is
     before the program exits, a minimal performance penalty
     should be acceptable
  */

  for (i = 1; i < memory__DYNMAXSIZE; i++) {
    POINTER thispage, nextpage;
    MEMORY_RESOURCE * Resource;

    Resource = memory_ARRAY[i];

    thispage = Resource->page;

    if (*((int *)thispage) != EOF) {
      do {
	nextpage = *((POINTER *)thispage);
	free(thispage);
	thispage = nextpage;
      } while  (*((int *)thispage) != EOF);

      /* and reset the resource structure */
      Resource->page        = &memory__EOF;
      Resource->free        = &memory__EOF;
      Resource->next        = &memory__EOF;
      Resource->end_of_page = &memory__EOF;
    }
  }

  /* now delete all big blocks left */

  if (memory_BIGBLOCKS != NULL) {
    MEMORY_BIGBLOCKHEADER thisblock, nextblock;
    
    for (thisblock = memory_BIGBLOCKS; 
	 thisblock != NULL; 
	 thisblock = nextblock) {
      nextblock = thisblock->next;
      free(thisblock);
    }

    /* and reset the list pointer */
    memory_BIGBLOCKS = NULL;
  }
}

/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  DEBUGGING INFORMATION                                 * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

void memory_Print(void)
/**************************************************************
  INPUT  : None.
  RETURNS: None.
  SUMMARY: Prints module status information to stdout:
           the fixed size of an internal memory page, the size 
	   of debug marks for a block of memory, the size of 
	   demanded and freed memory in kilobytes, remaining 
	   memory in bytes and the number of allocated pages of 
	   memory.
***************************************************************/
{
#ifndef NO_MEMORY_MANAGEMENT
  /* Call memory_FPrint to print status information to stdout */
  memory_FPrint(stdout);
#endif
}

void memory_FPrint(FILE* File)
/**************************************************************
  INPUT  : A file pointer.
  RETURNS: None.
  SUMMARY: Prints module status information to given File:
           the fixed size of an internal memory page, the size 
	   of debug marks for a block of memory, the size of 
	   demanded and freed memory in kilobytes, remaining 
	   memory in bytes and the number of allocated pages of 
	   memory.
***************************************************************/
{
#ifndef NO_MEMORY_MANAGEMENT
  int     Pages;    /* number of allocated pages                  */
  int     i;
  POINTER ActPage;  /* current page in page list for a block size */

  /* Calculate the total number of pages */
  Pages = 0;
  for (i = 1; i < memory__DYNMAXSIZE; i+=memory__SHAREDPAGES) {
    /* increase i by memory_SHAREDPAGES due to page sharing */
    ActPage = memory_ARRAY[i]->page;

    /* Traverse the page list */
    while (*((int *)ActPage) != EOF) {
      Pages++;
      ActPage = *((POINTER *)ActPage);
    }
  }

  /* Print status information */
  fputs("\n###\n", File);
  fprintf(File,"### Pagesize: %d\n",
	  memory_PAGESIZE);
  fprintf(File,"### Marksize: %d\n",
	  (int)memory_MARKSIZE);
  fprintf(File,"### Memory demanded:  %lu KBytes\n", 
	  memory_NEWBYTES/memory__KILOBYTE);
  fprintf(File,"### Memory freed:     %lu KBytes\n", 
	  memory_FREEDBYTES/memory__KILOBYTE);
  fprintf(File,"### Memory remaining: %lu Bytes\n", 
	  memory_NEWBYTES-memory_FREEDBYTES);
  fprintf(File,"### Pages allocated:  %d Pages\n", 
	  Pages);
  fputs("###\n", File);
#endif
}

void memory_PrintAllocatedBlocks(unsigned int Size)
/**************************************************************
  INPUT  : Block size.
  RETURNS: None.
  SUMMARY: Prints addresses of allocated memory blocks with
           given Size to stdout, if Size is less than 
	   memory_DYNMAXSIZE.
***************************************************************/
{
#ifndef NO_MEMORY_MANAGEMENT
  MEMORY_RESOURCE *Resource;     /* current resource                   */

  POINTER          ActPage;      /* current page                       */
  POINTER          ActNext;      /* next usable block on current page */
  POINTER          ActEndOfPage; /* end of current page                */

  unsigned int     BlockSize;    /* current block size                 */

#ifdef CHECK
  MEMORY_INFO      Info;         /* current block큦 debug information  */
#endif

  /* Allocated blocks are administered 
     in two ways depending on their 
     size. If the size is less than
     memory__DYNMAXSIZE the block is
     allocated from the appropriate
     page. Otherwise the block is 
     allocated directly via a call
     to malloc or calloc.

     Thus we have two functions to
     print the allocated blocks:
     memory_PrintAllocatedBlocks and
     memory_PrintAlocatedBigBlocks.
  */


  /* Check if memory_PrintAllocatedBlocks has been called for
     a legal block size
  */

  if (Size >= memory__DYNMAXSIZE) {
    /* if that큦 not the case print an error message and exit */
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In memory_PrintAllocatedBlocks:");
    misc_UserErrorReport("\n Parameter size is too big: %d.",
			 Size);
    misc_UserErrorReport("\n Maximal allowed value is: %d.\n", 
			 memory__DYNMAXSIZE);
    misc_FinishUserErrorReport();
  }
  else {
    /* otherwise size is legal */

    /* initialize the variables */
    Resource     = memory_ARRAY[Size];
    ActPage      = Resource->page;
    ActNext      = Resource->next;
    ActEndOfPage = Resource->end_of_page;
    BlockSize    = Resource->total_size;

    /* Test if there were any requests made for blocks of that size */
    if (*((int *)ActPage) == EOF) {
      /* Check if pointers are consistent */
      if (*((int *)ActNext) == EOF) {
	/* If that is true, print that information to stdout */
	puts("   No request so far");
      }
      else {
	/* Otherwise print an error message and abort */
	 misc_StartErrorReport();
	 misc_ErrorReport("\n In memory_PrintAllocatedBlocks:");
	 misc_ErrorReport("\n Memory Error. No Page entry but Next entry.\n");
	 misc_FinishErrorReport();
      }
    }
    else {
      /* We have received some requests for blocks of that size */ 
#ifdef CHECK

      POINTER ActData; /* current block */


      /* Traverse through the page list for given block size */
      while (*((int *)ActPage) != EOF) {

	/* Initialize the variables */
	ActData      = (char *)ActPage + sizeof(POINTER) + memory_OFFSET;
	ActEndOfPage = (char *)ActPage + Resource->offset;

	/* Visit blocks on current page until the end of
	   page is reached, or an allocated block is found
	*/
	while (ActData != ActNext 
	       && ActData != ActEndOfPage
	       && memory_GetBlockStatus(ActData) != memory_MAGICMALLOC) {
	  ActData = (char *)ActData + BlockSize;
	}

	/* Check if there were any allocated blocks from current page */
	if (ActData == ActNext || ActData == ActEndOfPage) {
	  /* if that큦 not the case print the information to stdout */
	  printf("\n\n   No memory allocated from page at address %p\n", ActPage);
	}
	else {
	  /* otherwise print address and origin of (de)allocation of
	     all allocated blocks on current page, starting
	     with the block just found
	  */
	  fputs("\n\n   Allocated but not freed: ", stdout);
	  do  {
	    Info = (MEMORY_INFO) ((char *) ActData - memory_OFFSET);
	    if (memory_GetBlockStatus(ActData) == memory_MAGICMALLOC 
		&& memory_GetBlockSize(ActData) == Size) {
	      printf("\n\t%p allocated in file %s at line %d ", 
		     ActData, Info->mallocInFile, Info->mallocAtLine);
	    }
	    ActData = (char *)ActData + BlockSize;
	  } while (ActData != ActNext && ActData != ActEndOfPage);
	}

	/* go to the next page in the page list for given block size */
	ActPage = *((POINTER *)ActPage);
      }
#endif
    }
  }
#endif
}

void memory_PrintFreedBlocks(unsigned int Size)
/**************************************************************
  INPUT  : Block size.
  RETURNS: None.
  SUMMARY: Prints addresses of freed memory blocks with given 
           Size to stdout, if Size is less than 
	   memory_DYNMAXSIZE.
***************************************************************/
{
#ifndef NO_MEMORY_MANAGEMENT
  POINTER     ActFree; /* current block */

#ifdef CHECK
  MEMORY_INFO Info;    /* current block큦 debug information */
#endif

  /* since we don큧 recycle blocks whose size is
     greater or equal to memory__DYNMAXSIZE, 
     memory_PrintFreedBlocks is meaningless
     for such block sizes.
  */

  /* test if given block size is legal */
  if (Size >= memory__DYNMAXSIZE) {
    /* if that큦 not the case print an error message and exit */
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In memory_PrintFreedBlocks.");
    misc_UserErrorReport("\n Parameter Size is too big: %d.", 
			 Size);
    misc_UserErrorReport("\n Maximal allowed value is: %d.\n", 
			 memory__DYNMAXSIZE);
    misc_FinishUserErrorReport();
  }
  else {
    /* otherwise size is legal */

    /* start at the first element of the free block list
       for the given block size
    */
    ActFree = memory_ARRAY[Size]->free;

    /* test if the free block list is empty */
    if (*((int *)ActFree) == EOF) {
      /* if that큦 true, print that information to stdout */
      puts("\n\n   No freed memory");
    }
    else {
      /* otherwise traverse the list of freed blocks */

      fputs("\n\n   Free: ", stdout);
      while (*((int *)ActFree) != EOF) {
#ifdef CHECK
	/* in debug mode print current block큦 address
	   and origin of (de)allocation
	*/

	/* check if block큦 size is correct */ 
	if ( memory_GetBlockSize(ActFree) == Size) {
	  /* if that큦 true than print block큦 information */
	  Info = (MEMORY_INFO) ((char *) ActFree - memory_OFFSET);
	  printf("\n\t%p\tallocated in file %s at line %d",
		 ActFree,  Info->mallocInFile, Info->mallocAtLine);
	  printf("\n\t\tfreed in file %s at line %d",
		 Info->freeInFile, Info->freeAtLine);
	}
	else {
	  /* otherwise if we are sharing pages among different
	     block sizes, the block is uncorrupted, despite not 
	     matching assumed and real size. But if we are
	     not sharing pages then the block is probably corrupted, 
	     so print an error message and exit 
	  */

	  /* test if we are not in page sharing mode */
	  if (memory__SHAREDPAGES == 1) {
	    /* if that큦 true print an error message and exit */
	    misc_StartUserErrorReport();
	    misc_UserErrorReport("\n In memory_PrintFreedBlocks:");
	    misc_UserErrorReport("\n Memory Error. Memory block size mismatch.");
	    misc_UserErrorReport("\n Expected %d found %d for memory block at %p.\n",
				 Size, memory_GetBlockSize(ActFree), ActFree);
	    misc_UserErrorReport("\n Probably the memory block was corrupted.\n");	    
	    misc_FinishUserErrorReport();
	  }
	}

#endif

	/* go to the next free block in list */
	ActFree = *((POINTER *)ActFree);
      }
    }
  }
#endif
}


void memory_PrintAllocatedBigBlocks(void)
/**************************************************************
  INPUT  : None.
  RETURNS: None.
  SUMMARY: Prints addresses of all allocated memory blocks,
           that are greater than memory_DYNMAXSIZE to stdout.
***************************************************************/
{
#ifndef NO_MEMORY_MANAGEMENT
#ifdef CHECK
  MEMORY_BIGBLOCKHEADER Ptr;         /* current big block in list */
  MEMORY_INFO           Info;        /* block큦 debug information */
  char                * BlockStart;  /* block큦 start address     */
  
  /* start with the first block in the big block list */
  Ptr = memory_BIGBLOCKS;

  /* check whether big block list isn큧 empty */
  if (Ptr != NULL) {
    /* if that큦 the case traverse through the list
       and print each block큦 address, size and
       origin of (de)allocation information
    */
    do {
      BlockStart = (char *)Ptr + memory_OFFSET 
	+ sizeof(MEMORY_BIGBLOCKHEADERNODE);
      
      Info = (MEMORY_INFO) (BlockStart - memory_OFFSET);
      printf("\n\t%p %d bytes allocated in file %s at line %d ", 
	     (void*)BlockStart, memory_GetBlockSize(BlockStart),
	     Info->mallocInFile, Info->mallocAtLine);
      Ptr = Ptr->next;
    } while (Ptr != NULL);
    puts("");
  }
  else {
    /* otherwise there are no big blocks allocated */
    puts("   No request so far");
  }
#endif
#endif
}

void memory_PrintDetailed(void)
/**************************************************************
  INPUT  : None.
  RETURNS: None.
  SUMMARY: Prints addresses of all pages, and allocated and freed 
           blocks on them.
***************************************************************/
{
#ifndef NO_MEMORY_MANAGEMENT
  MEMORY_RESOURCE  *Resource;     /* current resource                      */

  POINTER           ActPage;      /* current page                          */
  POINTER           ActData;      /* current block                         */
  POINTER           ActEndOfPage; /* end of current page                   */
  unsigned int      BlockSize;    /* total size of a block of current size */
  unsigned int      PageOffset;   /* current page큦 offset                 */

  unsigned int      i;


  /* print end-of-memory pointer큦 address */
  printf("\n\nEOF Pointer: %p\n", (void*)&memory__EOF);

  /* for all administrated block sizes print detailed information */
  for (i=1; i<memory__DYNMAXSIZE; i++) {
    /* initialize variables for requested block size i */
    Resource     = memory_ARRAY[i];
    ActPage      = Resource->page;
    ActData      = Resource->next;
    ActEndOfPage = Resource->end_of_page;
    PageOffset   = Resource->offset;
    BlockSize    = Resource->total_size;

    /* print requested block size, aligned block size 
       and block size including debug marks
    */
    printf("\n\n Entry: %d aligned size: %d total size: %d\n", 
	   i , Resource->aligned_size, BlockSize);

    /* Check if there were any requests for blocks of size i */
    if (*((int *)ActPage) == EOF) {
      /* if that큦 not the case check if memory management is consistent */
      if (*((int *)ActData) == EOF) {
	/* if that큦 true, print that no requests occurred to stdout */
	puts("   No request so far");
      }
      else {
	/* our memory management is no longer consistent, 
	   so print an error message and abort. We hope that
	   the core dump will help us to find the bug
	*/
	misc_StartErrorReport();
	misc_ErrorReport("\n In memory_PrintDetailed:");
	misc_ErrorReport("\n Memory Error. No Page entry but Next entry.\n");
	misc_FinishErrorReport();
      }
    }
    else {
      /* we have received requests for blocks of size i */

      /* traverse the list of pages for size i */
      while (*((int *)ActPage) != EOF) {
	/* print information about current page */
	printf("\n\n   Page: %p Next Page: %p\n",
	       ActPage, *((POINTER *)ActPage));

	/* initialize variables for current page */
	ActData = ((char *)ActPage + sizeof(POINTER) + memory_OFFSET);
	ActEndOfPage = (char *)ActPage + PageOffset;

	/* print addresses of all blocks on current page */
	fputs("   Data: ", stdout);
	while (ActData != ActEndOfPage) {
	  int column;

	  fputs("\n\t\t", stdout);
	  for (column = 0; column < 6; column++) {
	    printf("%p ", ActData);
	    ActData = (char *)ActData + BlockSize;
	    if (ActData == ActEndOfPage) {
	      break;
	    }
	  }
	}

	/* go to next page in list */
	ActPage = *((POINTER *)ActPage);
      }

      /* print allocated and freed blocks of size i */
      memory_PrintAllocatedBlocks(i);
      memory_PrintFreedBlocks(i);
    }
  }

#ifdef CHECK
  /* print allocated blocks of size >= memory_DYNMAXSIZE */
  printf("\n\n Allocated blocks of size >= %d\n", 
	 memory__DYNMAXSIZE);
  memory_PrintAllocatedBigBlocks();
#endif
#endif
}


void memory_PrintLeaks(void)
/**************************************************************
  INPUT  : None.
  RETURNS: None.
  SUMMARY: Prints addresses of all allocated blocks. Should be
           used at the end of a program before the call to
	   memory_FreeAllMem.
***************************************************************/
{
#ifndef NO_MEMORY_MANAGEMENT
  POINTER           ActPage;       /* current page                     */
  POINTER           ActNext;       /* next fresh block on current page */
  POINTER           ActEndOfPage;  /* end of current page              */
  MEMORY_RESOURCE  *Resource;      /* current resource                 */
  unsigned int      Size;          /* current size                     */
  unsigned int      BlockSize;     /* total block size                 */

  /* Check if some memory is still allocated */ 
  if (memory_UsedBytes() != 0L) { 

    /* If that큦 true, print all allocated blocks  */

    /* Start with blocks administered by our memory management */
    for (Size = 1; Size < memory__DYNMAXSIZE; Size++) {
      /* Initialize variables for current block size */
      Resource     = memory_ARRAY[Size];
      ActPage      = Resource->page;
      ActNext      = Resource->next;
      ActEndOfPage = Resource->end_of_page;
      BlockSize    = Resource->total_size;

      /* Check if there were any requests for 
	 memory blocks of that size */
      if (*((int *)ActPage) != EOF) {
      
	/* if that큦 true, browse through all blocks on all pages
	   to find a block that is still allocated
	*/
#ifdef CHECK
	
	POINTER ActData;
	BOOL    LeakFound;
	
	LeakFound = FALSE;
	
	while (*((int *)ActPage) != EOF) {
	  
	  /* search through all pages for a block that is still allocated */
	  
	  ActData      = (char *)ActPage + sizeof(POINTER) + memory_OFFSET;
	  ActEndOfPage = (char *)ActPage + Resource->offset;
	  
	  while (ActData != ActNext && ActData != ActEndOfPage) {
	    if (memory_GetBlockStatus(ActData) == memory_MAGICMALLOC) {
	      LeakFound = TRUE;
	      break;
	    }
	    ActData = (char *)ActData + BlockSize;
	  }
	  
	  if (LeakFound) {
	    
	    /* if we have found one, than call memory_PrintAllocatedBlocks
	       to print its address */
	    
	    printf("\n\n  Leaked blocks of size %d:", Size);
	    
	    memory_PrintAllocatedBlocks(Size);
	    putchar('\n');
	    /* since memory_PrintAllocatedblocks prints 
	     *all* allocated blocks of specific size, we can
	     break out of the while loop
	    */
	    break;
	  }
	  else {
	    /* go to next page */
	    ActPage = *((POINTER *)ActPage);
	  }
	}

#endif

      }      
    }

#ifdef CHECK
    /* Print allocated blocks of size >= memory__DYNMAXSIZE */
    if (memory_BIGBLOCKS != NULL) {
      printf("\n\n  Leaked blocks of size >= %d\n", 
	     memory__DYNMAXSIZE);
      memory_PrintAllocatedBigBlocks();
      putchar('\n');
    }
#endif

  }
#endif
}
