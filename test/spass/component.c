/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *               COMPONENTS OF CLAUSES                    * */
/* *                                                        * */
/* *  $Module:   COMPONENT                                  * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1998, 2000, 2001                  * */
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

#include "term.h"
#include "component.h"


CLITERAL literal_Create(BOOL used, int index, LIST varlist) 
/**********************************************************
  INPUT:   A boolean used, an integer index and a list varlist.
  RETURNS: A LITERAL is created.
  MEMORY:  The boolean, integer and varlist are  no copies.
*** ********************************************************/
{ 
  CLITERAL literal;

  literal = (CLITERAL)memory_Malloc(sizeof(CLITERAL_NODE));
  literal_PutUsed(literal,used);
  literal_PutLitIndex(literal,index);
  literal_PutLitVarList(literal,varlist);
   
  return literal;
}


void literal_Delete(CLITERAL literal) 
/**********************************************************
  INPUT:   A literal.
  RETURNS: None.
  MEMORY:   Deletes the LITERAL and frees the storage.
***********************************************************/
{ 
  list_Delete(literal_GetLitVarList(literal)); 
  literal_Free(literal);
}


LITPTR litptr_Create(LIST Indexlist, LIST Termsymblist) 
/**********************************************************
  INPUT:   A list indexes and a list of terms, i.e. a list of integers.
  RETURNS: A LITPTR structure is created.
  MEMORY:  The integers in the created structure are the integers
           in indexList, no copies.
***********************************************************/
{
  LITPTR lit_ptr;
  LIST       Scan,varlist;
  CLITERAL    literal;
  int        index,n,k;

  n                 = list_Length(Indexlist);

  lit_ptr           = (LITPTR)memory_Malloc(sizeof(LITPTR_NODE));
  litptr_SetLength(lit_ptr, n);
  
  if (n > 0) {
    lit_ptr->litptr = (CLITERAL *)memory_Malloc(n * sizeof(CLITERAL));

    k = 0;
    for (Scan = Indexlist; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      index         = (int)list_Car(Scan);
      varlist       = (LIST)list_Car(Termsymblist);
      Termsymblist  = list_Cdr(Termsymblist);
      literal       = literal_Create(FALSE,index,varlist);

      litptr_SetLiteral(lit_ptr, k, literal);
            
      k++;
    }
  } else 
    lit_ptr->litptr = NULL;
            
  return lit_ptr;
}


void litptr_Delete(LITPTR lit_ptr) 
/**********************************************************
  INPUT:   A pointer to LITPTR.
  MEMORY:  Deletes the LITPTR and frees the storage.
***********************************************************/
{
  int        n,i;

  n  = litptr_Length(lit_ptr);
  
  if (n > 0) {
    for (i = 0; i < n; i++)
      literal_Delete(litptr_Literal(lit_ptr,i));

    memory_Free(lit_ptr->litptr, sizeof(CLITERAL) * n);
    memory_Free(lit_ptr, sizeof(LITPTR_NODE));
  } else
    memory_Free(lit_ptr, sizeof(LITPTR_NODE));
}


void litptr_Print(LITPTR lit_ptr)
/**************************************************************
  INPUT:   A term.
  RETURNS: void.
  SUMMARY: Prints any term to stdout. 
  CAUTION: Uses the other term_Output functions.
***************************************************************/
{ 
  int i,n;

  n = litptr_Length(lit_ptr);
  /*n = lit_ptr->length;*/
  
  if (n > 0) {
    printf("\nlength of LITPTR: %d\n",n);
    for (i = 0; i < n; i++) {
      printf("Entries of literal %d : \n",i);
      puts("----------------------");
      fputs("used:\t\t", stdout);

      if (literal_GetUsed(litptr_Literal(lit_ptr,i)))
      /*if (lit_ptr->litptr[i]->used)*/
	puts("TRUE");
      else 
	puts("FALSE");
      printf("litindex:\t%d\n",
	     literal_GetLitIndex(litptr_Literal(lit_ptr,i)));
      fputs("litvarlist:\t", stdout);
      list_Apply((void (*)(POINTER)) symbol_Print,
		 literal_GetLitVarList(litptr_Literal(lit_ptr,i)));
      puts("\n");
    }
  }else 
    puts("No entries in litptr structure");
}


BOOL litptr_AllUsed(LITPTR lit_ptr)
/**************************************************************
  INPUT:   A LITPTR.
  RETURNS: TRUE if every literal in the LITPTR is used and 
           FALSE otherwise.
***************************************************************/
{
  int n,i;

  n = litptr_Length(lit_ptr);

  for (i = 0; i < n; i++)
    if (!(literal_GetUsed(litptr_Literal(lit_ptr,i))))
      return FALSE;

  return TRUE;
}


LIST subs_CompList(LITPTR litptr)
/**********************************************************
  INPUT:   A pointer litptr.
  RETURNS: A list with indexes which represents the first component of
           with respect to the actual bindings and to litptr.
  CAUTION: The structure to which litptr points to 
           is changed destructively in the used slot.
***********************************************************/
{
  BOOL found,hasinter;
  LIST scan,complist,compindexlist;
  int  n,i,j,lit;
  
  compindexlist     = list_Nil();   /* the result will be placed into this list */
  complist          = list_Nil();   /* added afterwards */
  n                 = litptr_Length(litptr);
  
  if (n > 0) {
    for (j = 0; j < n; j++) {
      printf("\nj = %d\n",j);
      if (!literal_GetUsed(litptr_Literal(litptr,j))){
	complist      = list_Nil();
	complist      = list_Cons((POINTER)j,complist);
	compindexlist = list_Cons((POINTER)(litptr->litptr[j]->litindex),
				  compindexlist);
	literal_PutUsed(litptr_Literal(litptr,j), TRUE);
	j = n+1;
	printf("\nj == %d\n",j);
      }
    }
    
    if (j == n){ 
      list_Delete(complist);     /* There is no more component */
      return compindexlist;      /* should be empty here       */
    }
    
    found = TRUE;
    while (found) {
      found = FALSE;
      for (scan = complist; !list_Empty(scan); scan = list_Cdr(scan)) {
	lit = (int)list_Car(scan);
	for (i = 0; i < n; i++) {
	  if (!literal_GetUsed(litptr_Literal(litptr,i))) {
	    printf("lit = %d\n",lit);
	    printf("i   = %d\n",i);
	    
	    hasinter = list_HasIntersection(litptr->litptr[lit]->litvarlist,
					    litptr->litptr[i]->litvarlist); 
	    
	    if (hasinter) {
	      puts("hasinter = TRUE");
	      complist      = list_Cons((POINTER)i,complist);
	      compindexlist = list_Cons((POINTER)(litptr->litptr[i]->litindex),compindexlist); 
	      literal_PutUsed(litptr_Literal(litptr,i), TRUE);
	      found = TRUE;
	    } 
	  }      
	}          
      }
      
      if (!found) {      /* one component is finished */
	list_Delete(complist);
	found = FALSE;
      }
    }
  }
  
  return compindexlist;
}
