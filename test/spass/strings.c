/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                STRING HANDLING                         * */
/* *                                                        * */
/* *  $Module:   STRINGS                                    * */ 
/* *                                                        * */
/* *  Copyright (C) 1999, 2000, 2001 MPI fuer Informatik    * */
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
/* $Revision: 35442 $                                        * */
/* $State$                                            * */
/* $Date: 2007-03-28 17:24:40 -0700 (Wed, 28 Mar 2007) $                             * */
/* $Author: jeffc $                                       * */
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

/**************************************************************/
/* Includes                                                   */
/**************************************************************/

#include <ctype.h>
#include "stringsx.h"
#include "list.h"

/**************************************************************/
/* Functions                                                  */
/**************************************************************/



BOOL string_StringIsNumber(const char* String)
/**************************************************************
  INPUT:   A string.
  RETURNS: TRUE iff the string solely consists of number characters.
***************************************************************/
{
  int i;
  
  if (String == NULL || String[0] == '\0')
    return FALSE;
  
  i = 0;

  while (String[i] != '\0')
    if (String[i] >= '0' && String[i] <= '9')
      i++;
    else
      return FALSE;

  return TRUE;  
}


char* string_StringCopy(const char* String)
/**************************************************************
  INPUT:   A string.
  RETURNS: A copy of the string.
  EFFECT:  The memory for the copy is allocated by the memory module.
***************************************************************/
{
  char *copy;

  copy = (char *) memory_Malloc(strlen(String)+1);
  strcpy(copy, String);
  return copy;
}


void  string_StringFree(char* String)
/**************************************************************
  INPUT:   A string.
  RETURNS: Nothing.
  EFFECT:  Frees the memory used by the string.
***************************************************************/
{
  memory_Free(String, strlen(String)+1);
}


char* string_IntToString(int Number)
/**************************************************************
  INPUT:   An integer number.
  RETURNS: The number as a string.
  EFFECT:  Memory is allocated for the string.
***************************************************************/
{
  char* result;
  NAT   size = 1;

  if (Number > 9) {
    size = (NAT)log10((double) Number) + 1;
  } else if (Number < 0) {
    size = (NAT)log10((double) abs(Number)) + 2; /* including '-' */
  }
  size++; /* for '\0' */

  result = (char *) memory_Malloc(sizeof(char) * size);
  sprintf(result, "%d", Number);
  return result;
}


BOOL string_StringToInt(const char* String, BOOL PrintError, int* Result)
/**************************************************************
  INPUT:   A string that should represent a decimal number in the
           format of the library function strtol, a boolean flag
	   concerning the printing of error messages and an pointer
	   to an integer that is used as a return value.
  RETURNS: TRUE, if the string could be converted successfully, else FALSE.
  EFFECT:  This function converts the string a number of type 'int'.
	   If the string was converted successfully, the value of the
	   number is stored in <*Result> and the function returns TRUE.
           If the number is too big (> INT_MAX), too small (< INT_MIN)
	   or the string couldn't be converted completely, <*Result> is
	   set to 0.
	   If <PrintError> is TRUE, additionally an error message is written
           to stderr and the program exits.
***************************************************************/
{
  long number;
  char *end;

  end    = (char*)0x1;   /* Has to be != NULL, so we take address 1 */
  number = strtol(String, &end, 10);
  /* Now <number> is LONG_MAX or LONG_MIN if the string represents a value */
  /* out of range. The variable <end> is set to the first non-converted    */
  /* character, e.g. if the string can be converted completely, <end> points */
  /* to the terminating '\0' character. */
  if (number >= INT_MIN && number <= INT_MAX && *end == '\0') {
    /* Number was converted successfully */
    *Result = (int)number;
    return TRUE;
  } else {
    /* Number is too large or buffer can't be converted completely */
    *Result = 0;
    if (PrintError) {
      misc_StartUserErrorReport();
      misc_UserErrorReport("\nString isn't a number or number to large: %s\n",
			   String);
      misc_FinishUserErrorReport();
    }
    return FALSE;
  }
}


char* string_Conc(const char* s1, const char* s2)
/**************************************************************
  INPUT:   Two strings.
  RETURNS: A new string s1.s2
  EFFECTS: Memory is allocated for the new string.
**************************************************************/
{ 
  char* dst;

  dst = memory_Malloc(strlen(s1) + strlen(s2) + 1);
  strcpy(dst, s1);
  return strcat(dst,s2);
}


char* string_Nconc(char* s1, char* s2)
/**************************************************************
 INPUT:   Two strings.
 RETURNS: A new string s1.s2.
 EFFECTS: s1,s2 are deleted, memory for the new string is
          allocated.
 CAUTION: Both strings must have been allocated by the memory module!
**************************************************************/
{ 
  char* dst;

  dst = memory_Malloc(strlen(s1) + strlen(s2) + 1);
  strcpy(dst, s1);
  dst = strcat(dst, s2);
  
  string_StringFree(s1);
  string_StringFree(s2);

  return dst;
}


char* string_EmptyString(void)
/**************************************************************
  INPUT:   None.
  RETURNS: The empty string.
  EFFECT:  Memory is allocated for the returned string.
**************************************************************/
{
  char* s ;

  s = memory_Malloc(1);
  s[0] = '\0';
  return s;
}


char* string_Prefix(const char* s, int i)
/**************************************************************
  INPUT:   A string and a string length.
  RETURNS: The prefix of <s> of length <i>.
  EFFECT:  Memory is allocated for the returned string.
**************************************************************/
{
  char* dst;

  dst = memory_Malloc(i + 1);
  strncpy(dst, s, i);
  dst[i] = '\0';
  return dst;
}


char* string_Suffix(const char* s, int i)
/**************************************************************
  INPUT:   A string and a string length.
  RETURNS: The string that results from cutting the first
           <i> characters from string <s>.
           Returns the empty string if <i> >= length(s).
  EFFECT:  Memory is allocated for the returned string.
**************************************************************/
{
  int  l;
  char *dst;
  
  l = strlen(s);
  if (i >= l)
    return string_EmptyString();

  dst = memory_Malloc(l - i + 1);
  strcpy(dst, s+i);
  return dst;
}


char** string_Tokens(char* String, int* ArraySize)
/**************************************************************
  INPUT:   A string <String>.
  RETURNS: The function returns an array of white space separated
           substrings from <String>. <ArraySize> is set to the
	   actual size of the returned array.
	   The array size is the number of substrings + 2, since
	   the first entry is the program name and the last entry
	   is NULL.
	   This is done so to create an array similar to the
	   "argv" argument of the main() function.
  EFFECT:  This function breaks the string into several substrings
	   that don't contain any whitespace characters.
	   The argument string is modified temporarily within this
	   function, but it's restored at the end.
***************************************************************/
{
  char *LastNonSpace, *Scan, Help, **Array;
  LIST Substrings;
  NAT  i;

#ifdef CHECK
  if (String == NULL) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In string_Tokens: String is NULL pointer.");
    misc_FinishErrorReport();
  }
#endif

  Substrings = list_Nil();
  Scan = String + strlen(String) - 1;
  while (Scan >= String) {
    while (Scan >= String && isspace((int)*Scan))
      Scan--;

    if (Scan >= String) {
      LastNonSpace = Scan;
      
      do {
	Scan--;
      } while (Scan >= String && !isspace((int)*Scan));
      
      Help = *(LastNonSpace + 1);
      *(LastNonSpace + 1) = '\0';
      Substrings = list_Cons(string_StringCopy(Scan+1), Substrings);
      *(LastNonSpace + 1) = Help;
    }
  }

  *ArraySize = list_Length(Substrings) + 2;
  Array = memory_Malloc(sizeof(char*) * *ArraySize);
  Array[0] = string_StringCopy("SPASS");
  for (i = 1; !list_Empty(Substrings); Substrings = list_Pop(Substrings), i++)
    Array[i] = list_Car(Substrings);
  Array[i] = NULL;
  (*ArraySize)--;

  return Array;
}
