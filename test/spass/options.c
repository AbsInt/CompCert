/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *               SPASS OPTIONS HANDLING                   * */
/* *                                                        * */
/* *  $Module:   OPTIONS                                    * */ 
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
/* $Revision: 35442 $                                        * */
/* $State$                                            * */
/* $Date: 2007-03-28 17:24:40 -0700 (Wed, 28 Mar 2007) $                             * */
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


/***************************************************************

		 COPYRIGHT NOTICE:

                 This file contains code that               
                 has been copied with minor modifications   
                 from the 'getopt' module in the            
                 GNU gcc library 2.0. The copyright for
                 this code is claimed by
		 
		 Copyright 1991 Regents of the 
		 University of California.
		 All rights reserved.

		 The copying and modification of the
		 original code is in accordance 
		 with the copyright conditions for the      
                 GNU gcc library, which are listed below.           


    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.

    Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in the
    documentation and/or other materials provided with the distribution.

    All advertising materials mentioning features or use of this software
    must display the following acknowledgement:

    This product includes software developed by the University of
    California, Berkeley and its contributors.

    Neither the name of the University nor the names of its contributors
    may be used to endorse or promote products derived from this software
    without specific prior written permission.

    This software is provided by the regents and contributors ``as is'' and
    any express or implied warranties, including, but not limited to, the
    implied warranties of merchantability and fitness for a particular purpose
    are disclaimed.  in no event shall the regents or contributors be liable
    for any direct, indirect, incidental, special, exemplary, or consequential
    damages (including, but not limited to, procurement of substitute goods
    or services; loss of use, data, or profits; or business interruption)
    however caused and on any theory of liability, whether in contract, strict
    liability, or tort (including negligence or otherwise) arising in any way
    out of the use of this software, even if advised of the possibility of
    such damage.

************************************************************************
************************************************************************/

#include "options.h"
#include "stringsx.h"

/**************************************************************/
/* Local variables  and types                                 */
/**************************************************************/

/* all option declarations. List with *DECL entries */
static LIST opts_DECLARATIONS;

/* list of <option id/value string> tupels that holds all parameters and their values */
static LIST opts_PARAMETERS;

static OPTID opts_IdNextAvailable;


/**************************************************************/
/* Forwarding functions                                       */
/**************************************************************/

static void     opts_AddParam(OPTID, const char*);
static BOOL     opts_AddParamCheck(OPTID, const char*);

static int      opts_GetOptLongOnly(int, const char* [], const char*,
				    const struct OPTION *, int *);

static OPTDECL* opts_DeclGetById(OPTID);
static void     opts_PrintDeclarationList(LIST);
static OPTID    opts_IdNext(OPTID);
static OPTID    opts_IdEqual(OPTID, OPTID);


/*************************************************************
  Local variables and types from the former getopt module code. 
**************************************************************/

/* Describe how to deal with options that follow non-option ARGV-elements.

   If the caller did not specify anything,
   the default is REQUIRE_ORDER if the environment variable
   POSIXLY_CORRECT is defined, PERMUTE otherwise.

   REQUIRE_ORDER means don't recognize them as options;
   stop option processing when the first non-option is seen.
   This is what Unix does.
   This mode of operation is selected by either setting the environment
   variable POSIXLY_CORRECT, or using `+' as the first character
   of the list of option characters.

   PERMUTE is the default.  We permute the contents of ARGV as we scan,
   so that eventually all the non-options are at the end.  This allows options
   to be given in any order, even with programs that were not written to
   expect this.

   RETURN_IN_ORDER is an option available to programs that were written
   to expect options and other ARGV-elements in any order and that care about
   the ordering of the two.  We describe each non-option ARGV-element
   as if it were the argument of an option with character code 1.
   Using `-' as the first character of the list of option characters
   selects this mode of operation.

   The special argument `--' forces an end of option-scanning regardless
   of the value of `opts_Ordering'.  In the case of RETURN_IN_ORDER, only
   `--' can cause `getopt' to return -1 with `opts_Ind' != ARGC.  */

static enum { REQUIRE_ORDER, PERMUTE, RETURN_IN_ORDER } opts_Ordering;

/* Value of POSIXLY_CORRECT environment variable.  */
static char *opts_PosixlyCorrect;

static int opts_FirstNonOpt;
static int opts_LastNonOpt;

/* Bash 2.0 gives us an environment variable containing flags
   indicating ARGV elements that should not be considered arguments.  */

static int opts_NonOptionFlagslen;


/* For communication from `getopt' to the caller.
   When `getopt' finds an option that takes an argument,
   the argument value is returned here.
   Also, when `opts_Ordering' is RETURN_IN_ORDER,
   each non-option ARGV-element is returned here.  */

static const char *opts_Arg = NULL;

/* Index in ARGV of the next element to be scanned.
   This is used for communication to and from the caller
   and for communication between successive calls to `getopt'.

   On entry to `getopt', zero means this is the first call; initialize.

   When `getopt' returns -1, this is the index of the first of the
   non-option elements that the caller should itself scan.

   Otherwise, `optind' communicates from one call to the next
   how much of ARGV has been scanned so far.  */

/* 1003.2 says this must be 1 before any call.  */
static int opts_Ind = 1;

/* Formerly, initialization of getopt depended on opts_Ind==0, which
   causes problems with re-calling getopt as programs generally don't
   know that. */

static int opts_GetOptInitialized = 0;

/* The next char to be scanned in the option-element
   in which the last option character we returned was found.
   This allows us to pick up the scan where we left off.

   If this is zero, or a null string, it means resume the scan
   by advancing to the next ARGV-element.  */

static const char *opts_NextChar;

/* Callers store zero here to inhibit the error message
   for unrecognized options.  */

static int opts_Err = 1;

/* Set to an option character which was unrecognized.
   This must be initialized on some systems to avoid linking in the
   system's own getopt implementation.  */

static int opts_Opt = '?';


/**************************************************************/
/* Functions                                                  */
/**************************************************************/

OPTID opts_IdFirst(void)
/**************************************************************
  INPUT:   None.
  RETURNS: First option id that is used in option declarations.
***************************************************************/
{
  return opts_IDFIRST;
}

static __inline__ OPTID opts_IdNull(void)
/**************************************************************
  INPUT:   None.
  RETURNS: An NULL id that is never used for option declarations
           (used as indicator for errors etc.).
***************************************************************/
{
  return -1;
}

BOOL opts_IdIsNull(OPTID Id)
/**************************************************************
  INPUT:   An option id.
  RETURNS: TRUE iff it is the NULL id. 
***************************************************************/
{
  return opts_IdEqual(opts_IdNull(), Id);
}

static __inline__ void opts_IdIncAvailable(void)
/**************************************************************
  INPUT:   None.
  RETURNS: Nothing.
  EFFECTS: Increases the counter for next available id.
***************************************************************/
{
  opts_IdNextAvailable = opts_IdNext(opts_IdNextAvailable);
}

static __inline__ OPTID opts_IdGetNextAvailable(void)
/**************************************************************
  INPUT:   None.
  RETURNS: Nothing.
  EFFECTS: Returns the counter for the next available id.
***************************************************************/
{
  return opts_IdNextAvailable;
}

static __inline__ void opts_DeclSetClName(OPTDECL* D, char* s)
/**************************************************************
  INPUT:   An option declaration, a string.
  RETURNS: Nothing.
  EFFECTS: Sets the command line name of <D> to <s>.
***************************************************************/
{
  D->clname = s;
}

static __inline__ char* opts_DeclGetClName(OPTDECL* D)
/**************************************************************
  INPUT:   An option declaration.
  RETURNS: The command line name in <D>.
***************************************************************/
{
  return D->clname;
}


static __inline__ void opts_DeclSetType(OPTDECL* D, OPTTYPE type)
/**************************************************************
  INPUT:   An option declaration and an option type.
  RETURNS: Nothing.
  EFFECTS: Set the option type of <D> to <type>.
***************************************************************/
{
  D->type = type;
}

static __inline__ OPTTYPE opts_DeclGetType(OPTDECL* D)
/**************************************************************
  INPUT:   An option declaration.
  RETURNS: The option type of <D>.
***************************************************************/
{
  return D->type;
}

static __inline__ BOOL opts_DeclIsShortOpt(OPTDECL* D)
/**************************************************************
  INPUT:   An option declaration.
  RETURNS: TRUE iff <D> is a declaration of a short option
           (with a single character command line name).
***************************************************************/
{
  return (strlen(opts_DeclGetClName(D)) == 1);
}

static __inline__ BOOL opts_DeclHasOptArg(OPTDECL* D) 
/**************************************************************
  INPUT:   An option declaration.
  RETURNS: TRUE iff <D> is a declaration of an option
           with an optional argument.
***************************************************************/
{
  return (opts_DeclGetType(D) == opts_OPTARGTYPE);
}

static __inline__ BOOL opts_DeclHasReqArg(OPTDECL* D) 
/**************************************************************
  INPUT:   An option declaration.
  RETURNS: TRUE iff <D> is a declaration of an option
           with a required argument.
***************************************************************/
{
  return (opts_DeclGetType(D) == opts_REQARGTYPE);
}

static __inline__ BOOL opts_DeclHasNoArg(OPTDECL* D) 
/**************************************************************
  INPUT:   An option declaration.
  RETURNS: TRUE iff <D> is a declaration of an option
           with a required argument.
***************************************************************/
{
  return (opts_DeclGetType(D) == opts_NOARGTYPE );

}

OPTID opts_Declare(const char* ClName, OPTTYPE OptType)
/* declare option by name/shorthand/argtype (command line name) */
/**************************************************************
  INPUT:   An option name (its command line name) and an option type.
  RETURNS: An option id.
  EFFECTS: Appends the declaration to opts_DECLARATIONS.
***************************************************************/
{
  OPTDECL* D;
  OPTID Id;

  if (!opts_IdIsNull(opts_Id(ClName))) {
    misc_StartErrorReport();
    misc_ErrorReport("internal error: option with command line name '%s' redeclared.\n", ClName);
    misc_FinishErrorReport(); }

  D  = memory_Malloc(sizeof(OPTDECL));

  opts_DeclSetClName(D, string_StringCopy(ClName));
  opts_DeclSetType(D,OptType);
  
  opts_DECLARATIONS = list_Nconc(opts_DECLARATIONS, list_List(D));

  Id = opts_IdGetNextAvailable();
  opts_IdIncAvailable();

  return Id;
}

OPTID opts_DeclareVector(OPTDECL Decls[]) 
/**************************************************************
  INPUT:   An option declaration vector, which must have
           a NULL pointer in the clname field of the last
	   declaration.
  RETURNS: The id of the last declared option.
  EFFECTS: All option declarations are added to opts_DECLARATIONS.
***************************************************************/
{
  int i;

  i = 0;
  while (strlen(opts_DeclGetClName(&Decls[i])) != 0) {
    opts_Declare(opts_DeclGetClName(&Decls[i]), opts_DeclGetType(&Decls[i])); 
    i++;
  }
  return opts_IdGetNextAvailable();
}

static char* opts_TranslateShortOptDeclarations(void)
/**************************************************************
  INPUT:   None.
  RETURNS: A string that codes the option declarations in
           opts_DECLARATIONS in a string as required by the
	   GNU getopt module.
***************************************************************/
{
  LIST  Scan;
  char* ShortDecl;
  OPTDECL* Decl;

  ShortDecl = string_StringCopy("\0");

  Scan = opts_DECLARATIONS;
  
  while (Scan) {
    /* option is short iff:
         - it was declared with a one letter command line name or
	 - it has an abbreviation
	 */
    Decl = (OPTDECL*)list_Car(Scan);
    
    if (opts_DeclIsShortOpt(Decl)) {
      ShortDecl = string_Nconc(ShortDecl, string_StringCopy(opts_DeclGetClName(Decl)));      

      /*
	  add colon if optional or required argument 
       */
      if (opts_DeclHasReqArg(Decl)||opts_DeclHasOptArg(Decl)) 
	ShortDecl = string_Nconc(ShortDecl, string_StringCopy(":"));
    }
    Scan = list_Cdr(Scan);
  }

  /* add leading colon if any short options exist */
  if (strlen(ShortDecl) != 0) {
    ShortDecl = string_Nconc(string_StringCopy(":"),ShortDecl); }

  return ShortDecl;
}

static LIST opts_GetLongOptDeclarations(void)
/**************************************************************
  INPUT:   None.
  RETURNS: A list of all 'long option' (with command line name 
           length > 1) declarations in opts_DECLARATIONS.
  EFFECTS: Allocates list. 
***************************************************************/
{
  LIST     Scan, Long;
  OPTDECL* Decl;

  Scan = opts_DECLARATIONS;
  Long = list_Nil();

  while (!list_Empty(Scan)) {
    Decl = list_Car(Scan);

    if (!opts_DeclIsShortOpt(Decl)) {
      Long = list_Cons(Decl, Long);
    }
    Scan = list_Cdr(Scan);
  }  
  return Long;
}

static __inline__ struct OPTION *opts_GetLongOptsArray(int OptNum)
/**************************************************************
  INPUT:   An option number .
  RETURNS: An array with <OptNum> entries for OPTION structs
           as needed by GetOptLongOnly.
  EFFECTS: Allocates array.
***************************************************************/
{
  return (struct OPTION*)memory_Malloc(sizeof(struct OPTION)*(OptNum+1));
}

static void opts_FreeLongOptsArray(struct OPTION *LongOpts)
/**************************************************************
  INPUT:   An array with entries for OPTION structs
  RETURNS: Nothing
  EFFECTS: Frees array. End of array is marked by a struct OPTION
           entry with a NULL pointer in the 'name' field.
***************************************************************/
{
  int i;

  for (i=0; LongOpts[i].name != 0; i++) /* empty */;

  memory_Free(LongOpts, (i+1)*sizeof(struct OPTION));
}


static struct OPTION* opts_TranslateLongOptDeclarations(void)
/**************************************************************
  INPUT  : None
  RETURNS: Translates opts_DECLARATIONS into an array as needed
           by GetLongOptOnly
  EFFECTS: Allocates the array
***************************************************************/
{
  LIST           Scan;
  LIST           LongDeclarations;
  int            OptNum;
  int            OptCnt;
  struct OPTION* LongOpts;

  OPTDECL* Decl;

  LongDeclarations = opts_GetLongOptDeclarations();
  OptNum           = list_Length(LongDeclarations);
  LongOpts         = opts_GetLongOptsArray(OptNum);
  OptCnt = 0;
  Scan   = LongDeclarations;

  while (!list_Empty(Scan)) {
    Decl = list_Car(Scan);
    
    LongOpts[OptCnt].name = opts_DeclGetClName(Decl);

    if (opts_DeclHasOptArg(Decl))
      LongOpts[OptCnt].has_arg = 2;
    else if (opts_DeclHasReqArg(Decl)) 
      LongOpts[OptCnt].has_arg = 1; 
    else 
      LongOpts[OptCnt].has_arg = 0; 
    LongOpts[OptCnt].flag    = 0;
    LongOpts[OptCnt].val     = 0; 
    
    Scan = list_Cdr(Scan);
    OptCnt++;
  }
  /* set last field to 0 as required by getopt */
  LongOpts[OptCnt].name    = NULL;
  LongOpts[OptCnt].has_arg = 0;
  LongOpts[OptCnt].flag    = 0;
  LongOpts[OptCnt].val     = 0;

  list_Delete(LongDeclarations);

  return LongOpts;
}


static void opts_PrintLongOpts(struct OPTION *LongOpts)
/**************************************************************
  INPUT:   An array with OPTIONS structs  
  RETURNS: Nothing
  EFFECTS: Prints contents of array
***************************************************************/
{
  int i;

  if (LongOpts == NULL) {
    puts("\nPrintLongOpts gets NULL pointer.");
    return;
  }
  puts("\nLong options array:");
  
  i = 0;
  while (LongOpts[i].name != NULL) {
    printf("\nentry %d:\n",i);

    printf("Name:    %s\n", LongOpts[i].name);
    printf("has_arg: %d\n", LongOpts[i].has_arg);
    printf("flag;  : %d\n", (int)LongOpts[i].flag);
    printf("val    : %d\n", LongOpts[i].val);
    i++;
  }
}

static __inline__ OPTID opts_IdCmp(OPTID Id1, OPTID Id2)
/**************************************************************
  INPUT:   Two option ids  
  RETURNS: Analogously to strcmp: 
              '0'   if Id1 == Id2
	      '<0'  if Id1 <  Id2
	      '>0'  if Id1 >  Id2
***************************************************************/
{
  return (Id1-Id2);
}

static OPTID opts_IdEqual(OPTID Id1, OPTID Id2)
/**************************************************************
  INPUT:   Two options ids  
  RETURNS: TRUE if they are equal
***************************************************************/
{
  return (opts_IdCmp(Id1,Id2) == 0);
}

static OPTID opts_IdNext(OPTID Id)
/**************************************************************
  INPUT:   An option id  
  RETURNS: The next option id in the ordering
***************************************************************/
{
  return (Id+1);
}


const char* opts_ClName(OPTID Id)
/**************************************************************
  INPUT:   An option id
  RETURNS: Its command line name
***************************************************************/
{
  OPTDECL* Decl;

  Decl = opts_DeclGetById(Id);
  return opts_DeclGetClName(Decl);
}

OPTID opts_Id(const char* ClName) 
/**************************************************************
  INPUT:   The command line name of an option 
  RETURNS: The corresponding id of the option,
           the NULL id if no option with <ClName> exist.
***************************************************************/
{
  LIST    Scan;
  BOOL    found;
  OPTID   Id;

  Scan  = opts_DECLARATIONS;
  Id    = opts_IdFirst();
  found = FALSE;

  while (!found && !list_Empty(Scan)) {
    if (string_Equal(opts_DeclGetClName(list_Car(Scan)), ClName)) {
      found = TRUE;
    } else {
      Scan = list_Cdr(Scan);
      Id = opts_IdNext(Id);
    }
  }
  if (!found)
    Id = opts_IdNull();
  return Id;
}

static OPTID opts_ShortOptId(char c)
/**************************************************************
  INPUT:   A character
  RETURNS: The id of a short option <c>, NULL id
           if it does not exist.
***************************************************************/
{
  char Str[2];

  Str[0] = c;
  Str[1] = '\0';

  return opts_Id(Str);
}

void opts_Init(void)
/**************************************************************
  INPUT:   None
  RETURNS: Nothing 
  EFFECT:  Initialize option module 
***************************************************************/
{
  opts_DECLARATIONS = list_Nil();
  opts_PARAMETERS   = list_Nil();
  opts_Err = 1; /* let getopt generate its own error messages */
  opts_IdNextAvailable = opts_IdFirst();
}

void opts_DeclareSPASSFlagsAsOptions(void)
/**************************************************************
  INPUT:   None
  RETURNS: Nothing 
  EFFECT:  Initialize option for use with SPASS: 
           declares all SPASS flags as command line opts.
  MEMORY:  Allocates space for declarations
***************************************************************/
{
  int i;

  for (i=0; i < flag_MAXFLAG; i++) {
    opts_Declare(flag_Name(i), opts_OPTARGTYPE);
  }
}

static void opts_FreeParameterPair(LIST Pair)
/**************************************************************
  INPUT  : An (id/string) pair
  RETURNS: Nothing
  EFFECTS: Frees memory of list element and string 
***************************************************************/
{
  string_StringFree(list_PairSecond(Pair));

  list_PairFree(Pair);
}

static void opts_FreeDecl(OPTDECL* D)
/**************************************************************
  INPUT:   An options declaration
  RETURNS: Nothing
  EFFECTS: Frees memory of struct. 
***************************************************************/
{
  string_StringFree((char*)opts_DeclGetClName(D));
  memory_Free(D, sizeof(OPTDECL));
}

void opts_Free(void)
/**************************************************************
  INPUT:   None
  RETURNS: Nothing 
  EFFECT:  Free memory of module
***************************************************************/
{
  list_DeleteWithElement(opts_PARAMETERS, (void (*)(POINTER))opts_FreeParameterPair);
  list_DeleteWithElement(opts_DECLARATIONS,(void (*)(POINTER))opts_FreeDecl);
}

static void opts_PrintDeclarationList(LIST Scan)
/**************************************************************
  INPUT:   A list with option declarations
  RETURNS: Nothing
  EFFECTS: Prints the list 
***************************************************************/
{
  OPTDECL* Decl;
  OPTID    Id;

  Id = opts_IdFirst();

  while (Scan) {
    Decl = (OPTDECL*)list_Car(Scan);
    printf("Id:%-6d Name:%-18s Type:%d\n", Id, opts_DeclGetClName(Decl),
	   opts_DeclGetType(Decl));
    Scan = list_Cdr(Scan);
    Id   = opts_IdNext(Id);
  }
}

static __inline__ void opts_PrintDeclarations(void)
/**************************************************************
  INPUT:   None
  RETURNS: Nothing
  EFFECTS: Prints all currently declared options 
***************************************************************/
{
  opts_PrintDeclarationList(opts_DECLARATIONS);
}

static void opts_PrintParameters(void)
/**************************************************************
  INPUT:   None
  RETURNS: Nothing
  EFFECTS: Prints all values of options read so far 
***************************************************************/
{
  LIST Scan;
  LIST Pair;

  Scan = opts_PARAMETERS;

  while (!list_Empty(Scan)) {

    Pair = list_Car(Scan);
    printf("\nId: %d ", (OPTID)list_PairFirst(Pair));
    printf("Par: %s", (char*) list_PairSecond(Pair));

    Scan = list_Cdr(Scan);
  }
}


void opts_PrintSPASSNames(void)
/**************************************************************
  INPUT:   None 
  RETURNS: Nothing
  EFFECT:  Prints all options in three rows
***************************************************************/
{
  int i,j;
  
  for (i=0; i < flag_MAXFLAG; i=i+4) { 
    for (j =0; j <=3; j++) {
      if (i+j < flag_MAXFLAG)
	printf("%-18s ", flag_Name(i+j)); } 
    putchar('\n');
  }
}

static OPTDECL* opts_DeclGetById(OPTID Id)
/**************************************************************
  INPUT  : An option id
  RETURNS: The declaration corresponding to option <id>
***************************************************************/
{
  OPTID ScanId;
  LIST  Scan;

  ScanId = opts_IdFirst();
  Scan   = opts_DECLARATIONS;
  
  while (!list_Empty(Scan)) {
    if (opts_IdEqual(Id, ScanId))
      return list_Car(Scan);
    Scan = list_Cdr(Scan);
    ScanId = opts_IdNext(ScanId);
  }

  return (OPTDECL*)NULL;
}


/* Currently unused */
/*static*/ OPTDECL* opts_DeclGetByClName(const char* ClName)
/**************************************************************
  INPUT  : A command line name
  RETURNS: The declaration of the option with <ClName> as command
           line name, NULL if there's no such option
***************************************************************/
{
  OPTID Id;
  
  Id = opts_Id(ClName);
  if (opts_IdIsNull(Id))
    return NULL;
  return opts_DeclGetById(Id);
}


BOOL opts_Read(int argc, const char* argv[])
/**************************************************************
  INPUT:   Program parameter data 
  RETURNS: TRUE iff options are correctly specified 
  EFFECT:  Errors are commented
  MEMORY:  Builds up opts_PARAMETERS while reading
           options and their values.
***************************************************************/
{
  int        OptIndex, c;
  char       *ShortOpts;
  BOOL       Ok;
  OPTID      OptId;
  OPTDECL    *OptDecl;
  const char *OptName;
  struct OPTION *LongOpts;

  Ok = TRUE;
  
  ShortOpts = opts_TranslateShortOptDeclarations();
  LongOpts  = opts_TranslateLongOptDeclarations();

  while (Ok && (c = opts_GetOptLongOnly(argc, argv, ShortOpts, 
					LongOpts, &OptIndex)) != -1) {
    /* 
       for following eval of opts_GetOptLongOnly result see
       GNU getopt documentation. In short, opts_GetOptLongOnly
       returns a char if it has found that char as an option in
       the command line, and this option is declared in opts_DECLARATIONS. 
       It returns 0 if it has found a declared long option.
       
    */
    if (c == '?') { 
      /**** unknown option ****/ 

      /* This has already been commented by opts_GetOptLongOnly */
      return FALSE;
    } else if (c == 0) {
      /**** its a long option  ****/
      
      OptName = LongOpts[OptIndex].name;
      OptId   = opts_Id(OptName);
      OptDecl = opts_DeclGetById(OptId);
      
      if (opts_Arg == NULL) {
	/* if argument required and no arg specified, error  */
	if (opts_DeclHasReqArg(OptDecl)) {
	  misc_StartUserErrorReport();
	  misc_UserErrorReport("\nerror, option %s requires argument.\n", OptName);
	  misc_FinishUserErrorReport();
	  return FALSE;
	}
	
	/* otherwise, set default value */
	Ok = opts_AddParamCheck(OptId,opts_DEFAULTOPTARG);
      } else  
	Ok = opts_AddParamCheck(OptId,opts_Arg);
    } else {
      /**** its a short option ****/
      
      /* handle missing but required arguments. So far, this is left
	 to opts_GetOptLongOnly */
      if (c == ':') 
	return FALSE;
      
      /* 
	 
	 One further special case: if a short option has an optional
	 argument, but this argument is a '--', then take the
	 default argument value. '--' normally signifies: no further
	 options and is not interpreted nor returned by getopt as
	 an argument value of an option with argument. As we
	 permit default values for options with args, we have to declare
	 all options with args. Therefore, getopt takes 
	 
	 -o -- 
	 
	 '-o with arg --' if "o:" is the declaration. We interpret
	 this as '-o with default value'.
	 
      */
      
      else {
	OptId = opts_ShortOptId(c);
	if (opts_IdIsNull(OptId)) {
	  misc_StartErrorReport();
	  misc_ErrorReport("\ninternal error: option %c not found.\n", c);
	  misc_FinishErrorReport();
	}
	OptDecl = opts_DeclGetById(OptId);
	
	if (opts_DeclHasReqArg(OptDecl)) {
	  if (!opts_Arg) {
	    misc_StartUserErrorReport();
	    misc_UserErrorReport("\nerror: option %c requires argument.\n",c);
	    misc_FinishUserErrorReport();
	    Ok = FALSE;
	  } else if (string_Equal(opts_Arg, opts_ENDMARKER)) {
	    misc_StartUserErrorReport();
	    misc_UserErrorReport("\nerror: option %c has delimiter -- as argument.\n",c);
	    misc_FinishUserErrorReport();
	    Ok = FALSE;
	  } else 
	    Ok = opts_AddParamCheck(OptId,opts_Arg);
	}
	/* options with args */
	else if (opts_DeclHasOptArg(OptDecl)) {
	  /* if arg is present, check for endmarker */
	  if (opts_Arg) {
	    if (string_Equal(opts_Arg, opts_ENDMARKER)) 
	      Ok = opts_AddParamCheck(OptId,opts_DEFAULTOPTARG);
	    else 
	      Ok = opts_AddParamCheck(OptId,opts_Arg); }
	  else 
	    Ok = opts_AddParamCheck(OptId,opts_DEFAULTOPTARG);
	}
	/* default for options without args */
	else 
	  Ok = opts_AddParamCheck(OptId,opts_DEFAULTOPTARG);
      }
    }
  }
  
  string_StringFree(ShortOpts);
  opts_FreeLongOptsArray(LongOpts);
  
  return Ok;
}


BOOL opts_ReadOptionsFromString(const char* Options)
/**************************************************************
  INPUT:   A string containing program parameter data 
  RETURNS: TRUE iff the string contains only valid options.
           The function returns FALSE if the string contains
	   any substring that isn't a option or invalid option
	   settings.
  EFFECT:  Errors are commented (via stderr).
  MEMORY:  Builds up opts_PARAMETERS while reading options and
           their values.
  CAUTION: The function cannot !! be used in context with the
           other option evaluation functions like opts_Read.
***************************************************************/
{
  char **argv;
  char *Copy;
  int  argc, i;
  BOOL Result;

  /* Copy the options string since "string_Tokens" modifies it temporarily */
  Copy = string_StringCopy(Options);
  /* Split the string into substrings without whitespace.             */
  /* Collect the substrings in an array similar to "argv" for main(). */
  argv = string_Tokens(Copy, &argc);

  /* Check whether all options are valid. */
  Result = opts_Read(argc, (const char**)argv);
  /* Check whether the string contains only option settings. */
  if (opts_Indicator() < argc)
    Result = FALSE;

  /* Cleanup */
  for (i = argc-1; i >= 0; i--)
    string_StringFree(argv[i]);
  memory_Free(argv, sizeof(char)*(argc+1));
  string_StringFree(Copy);

  return Result;
}


BOOL opts_GetValueByName(const char* Name, const char** Value)
/**************************************************************
  INPUT:   An option command line name, a string by ref.
  RETURNS: TRUE if an option with this name exists
           in opts_PARAMETERS (as set by opts_Read()),
	   and the assigned value of this option in <Value>.
	   FALSE otherwise
  EFFECTS: <*Value> is changed 
***************************************************************/
{
  LIST Scan;
  LIST Pair;
  BOOL found;

  found = FALSE;
  Pair  = list_Nil(); /* to quiet gcc */

  for (Scan = opts_PARAMETERS;
       (!found && !list_Empty(Scan)); Scan = list_Cdr(Scan)) {
    Pair = list_Car(Scan);
    if (string_Equal(Name, opts_ClName((OPTID)list_PairFirst(Pair))))
      found = TRUE;
  }

  if (found) 
    (*Value) = list_PairSecond(Pair); 

  return found;
}

BOOL opts_GetValue(OPTID Id, const char** s) 
/**************************************************************
  INPUT:   An option id, a string by reference
  RETURNS: TRUE if an option with this id exists
           in opts_PARAMETERS (as set by opts_Read()),
	   and the assigned value of this option in <Value>.
	   FALSE otherwise
  EFFECTS: <s*> is changed 
***************************************************************/
{
  LIST Scan;
  LIST Pair;
  BOOL found;

  Pair  = list_Nil();
  found = FALSE;

  for (Scan = opts_PARAMETERS;
       (!found && !list_Empty(Scan)); Scan = list_Cdr(Scan)) {
    Pair = list_Car(Scan);
    if (opts_IdEqual(Id, (OPTID)list_PairFirst(Pair)))
      found = TRUE;
  }

  if (found) 
    (*s) = list_PairSecond(Pair);

  return found;
}


BOOL opts_GetIntValueByName(const char* Name, int* Val)
/**************************************************************
  INPUT:   An options name, an integer by reference
  RETURNS: TRUE 
           if an option with <Name> exists
           in opts_PARAMETERS (as set by opts_Read()) and 
	   if its assigned value is an integer.
	   The assigned value of this option is returned in <Val>.
	   FALSE 
	   otherwise
  EFFECTS: <Val*> is changed 
***************************************************************/
{
  const char* ValStr ;

  if (!opts_GetValueByName(Name, &ValStr)) 
    return FALSE;
  
  return string_StringToInt(ValStr, FALSE, Val);
}

BOOL opts_GetIntValue(OPTID Id, int* i) 
/**************************************************************
  INPUT:   An options name, an integer by reference
  RETURNS: TRUE 
           if an option with <Id> exists
           in opts_PARAMETERS (as set by opts_Read()) and 
	   if its assigned value is an integer.
	   T he assigned value of this option is returned in <*i>.
	   FALSE 
           otherwise
  EFFECTS: <*i> is changed 
***************************************************************/
{
  return opts_GetIntValueByName(opts_ClName(Id), i);
}



BOOL opts_IsSet(OPTID Id)
/**************************************************************
  INPUT:   An option id
  RETURNS: TRUE iff the option has been set in the command line
           (that is, is listed in opts_PARAMETERS)
***************************************************************/
{
  LIST Scan;
  LIST Pair;
  BOOL found;
  
  found = FALSE;

  for (Scan = opts_PARAMETERS;
       (!found && !list_Empty(Scan)); Scan = list_Cdr(Scan)) {
    Pair = list_Car(Scan);
    if (opts_IdEqual(Id, (OPTID)list_Car(Pair)))
      found = TRUE;
  }
  return found;
}


/* Currently unused */
/*static*/ BOOL opts_IsSetByName(const char* Name)
/**************************************************************
  INPUT:   An option name
  RETURNS: TRUE iff option with this name has been set in command line
***************************************************************/
{
  LIST Scan;
  LIST Pair;
  BOOL found;
  
  found = FALSE;

  for (Scan = opts_PARAMETERS;
       (!found && !list_Empty(Scan)); Scan = list_Cdr(Scan)) {
    Pair = list_Car(Scan);
    if (string_Equal(Name, opts_ClName((OPTID)list_PairFirst(Pair))))
      found = TRUE;
  }
  return found;
}

void opts_SetFlags(FLAGSTORE Store)
/**************************************************************
  INPUT:   A flag store.
  RETURNS: Nothing
  EFFECT : Transfer options into SPASS flags in <Store>
  CAUTION: To connect SPASS flags and options, we assume that
           all flag names and command line names of all options
	   are the same!
***************************************************************/
{
  int     IntValue;
  OPTID   Id;
  FLAG_ID i;

  for (i = 0; i < flag_MAXFLAG; i++) {
    Id = opts_Id(flag_Name(i));
    if (opts_IsSet(Id)) {
      if (opts_GetIntValue(Id, &IntValue)) {
	flag_SetFlagValue(Store, Id, IntValue);
      } else {
	misc_StartUserErrorReport();
	misc_UserErrorReport("\nerror: argument of option %s must be integer.\n",flag_Name(i));
	misc_FinishUserErrorReport();
      }
    }
  }
}

void opts_Transfer(FLAGSTORE Store)
/**************************************************************
  INPUT:   A flag store.
  RETURNS: Nothing
  EFFECT:  Transfer options from 'opts_PARAMETERS' list into SPASS
           flags in <Store> 
  CAUTION: To connect SPASS flags and options, we assume that
           all flag names and command line names of all options
	   are the same!
***************************************************************/
{
  LIST       Scan;
  LIST       Pair;
  int        IntValue;
  const char *Name, *ValStr;
  OPTID      Id;
  BOOL       ok;

  Scan = opts_PARAMETERS;

  while (!list_Empty(Scan)) {
    Pair    = list_Car(Scan);
    Id      = (int)list_PairFirst(Pair);
    ValStr  = (const char*)list_PairSecond(Pair);
    Name    = opts_ClName(Id);
    
    ok = string_StringToInt(ValStr, FALSE, &IntValue);
    if (!ok) {
      misc_StartUserErrorReport();
      misc_UserErrorReport("\nerror: argument '%s' of option '%s' must be integer.\n",
			   ValStr, Name);
      misc_FinishUserErrorReport();
    } else { 
      flag_SetFlagValue(Store, flag_Id(Name), IntValue);
    }
    Scan = list_Cdr(Scan);
  }
}


static void opts_AddParam(OPTID Id, const char* ValueString)
/**************************************************************
  INPUT:   An option id and a string with its assigned value 
  RETURNS: Nothing.
  EFFECT:  Add (Id, ValueString) tupel to 'opts_PARAMETERS' list
***************************************************************/
{ 
  LIST Pair;
  Pair = list_PairCreate((POINTER)Id, string_StringCopy(ValueString));
  opts_PARAMETERS = list_Cons(Pair, opts_PARAMETERS); 
}


static BOOL opts_AddParamCheck(OPTID Id, const char* ValueString)
/**************************************************************
  INPUT:   An option id and a string
  RETURNS: TRUE iff option with <Id> has not been defined
  EFFECTS: Adds (<Id>,<ValueString>) tupel to opts_PARAMETERS 
***************************************************************/
{
  const char* Dummy;
  if (opts_GetValue(Id, &Dummy)) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("error: option %s is multiply defined.\n", opts_ClName(Id));
    misc_FinishUserErrorReport();
    return FALSE;
  }
  opts_AddParam(Id, ValueString);
  return TRUE;
}


int opts_Indicator(void) 
/**************************************************************
  INPUT:   None
  RETURNS: Integer variable indicating position of next argument
***************************************************************/
{
  return opts_Ind;
}


static void opts_Exchange (const char *argv[])
/**************************************************************
  INPUT:   Reference to string
  RETURNS: Nothing
  EFFECT:  See below
***************************************************************/

/* Exchange two adjacent subsequences of ARGV.
   One subsequence is elements [opts_FirstNonOpt,opts_LastNonOpt)
   which contains all the non-options that have been skipped so far.
   The other is elements [opts_LastNonOpt,opts_Ind), which contains all
   the options processed since those non-options were skipped.

   `opts_FirstNonOpt' and `opts_LastNonOpt' are relocated so that they describe
   the new indices of the non-options in ARGV after they are moved.  */
{
  int bottom = opts_FirstNonOpt;
  int middle = opts_LastNonOpt;
  int top = opts_Ind;
  const char *tem;

  /* Exchange the shorter segment with the far end of the longer segment.
     That puts the shorter segment into the right place.
     It leaves the longer segment in the right place overall,
     but it consists of two parts that need to be swapped next.  */

  while (top > middle && middle > bottom) {
    if (top - middle > middle - bottom) {
      /* Bottom segment is the short one.  */
      int len = middle - bottom;
      register int i;
      
      /* Swap it with the top part of the top segment.  */
      for (i = 0; i < len; i++) {
	tem = argv[bottom + i];
	argv[bottom + i] = argv[top - (middle - bottom) + i];
	argv[top - (middle - bottom) + i] = tem;
      }
      /* Exclude the moved bottom segment from further swapping.  */
      top -= len;
    }
    else {
      /* Top segment is the short one.  */
      int len = top - middle;
      register int i;
      
      /* Swap it with the bottom part of the bottom segment.  */
      for (i = 0; i < len; i++) {
	tem = argv[bottom + i];
	argv[bottom + i] = argv[middle + i];
	argv[middle + i] = tem;
      }
      /* Exclude the moved top segment from further swapping.  */
      bottom += len;
    }
  }
  
  /* Update records for the slots the non-options now occupy.  */

  opts_FirstNonOpt += (opts_Ind - opts_LastNonOpt);
  opts_LastNonOpt = opts_Ind;
}


static const char *opts_GetOptInitialize (int argc, const char *const argv[],
					  const char *optstring)
/**************************************************************
  INPUT:   The command line arguments ('argc', 'argv') and
           a string describing options ('optstring')
  RETURNS: a possibly modified 'optstring'
  EFFECT:  Several static variables related to options
           processing are influenced (see below).
  MEMORY:  None
***************************************************************/
{
  /* Start processing options with ARGV-element 1 (since ARGV-element 0
     is the program name); the sequence of previously skipped
     non-option ARGV-elements is empty.  */

  opts_FirstNonOpt = opts_LastNonOpt = opts_Ind = 1;

  opts_NextChar = NULL;

  opts_PosixlyCorrect = getenv ("POSIXLY_CORRECT");

  /* Determine how to handle the ordering of options and nonoptions.  */

  if (optstring[0] == '-') {
    opts_Ordering = RETURN_IN_ORDER;
    ++optstring;
  }
  else if (optstring[0] == '+') {
    opts_Ordering = REQUIRE_ORDER;
    ++optstring;
  }
  else if (opts_PosixlyCorrect != NULL)
    opts_Ordering = REQUIRE_ORDER;
  else
    opts_Ordering = PERMUTE;
  
  opts_NonOptionFlagslen = 0;
  
  return optstring;
}

static int opts_GetOptInternal (int argc, const char* argv[],
				const char *optstring,
				const struct OPTION *longopts, int *longind,
				int long_only)
/**************************************************************
  INPUT:   An array of pointers to arguments (strings),
           and format information. See below for extensive
	   description
  RETURNS: -1 only if there are no more options, otherwise
           a value identifying a read option. See below.
  EFFECT:  Affects statics opts_Ind, opts_Arg, opts_Opt,
           opts_NextChar and argument array. See below.
  MEMORY:  See below. 
***************************************************************/
/* Scan elements of ARGV (whose length is ARGC) for option characters
   given in OPTSTRING.

   If an element of ARGV starts with '-', and is not exactly "-" or "--",
   then it is an option element.  The characters of this element
   (aside from the initial '-') are option characters.  If `getopt'
   is called repeatedly, it returns successively each of the option characters
   from each of the option elements.

   If `getopt' finds another option character, it returns that character,
   updating `opts_Ind' and `opts_NextChar' so that the next call to `getopt' can
   resume the scan with the following option character or ARGV-element.

   If there are no more option characters, `getopt' returns -1.
   Then `opts_Ind' is the index in ARGV of the first ARGV-element
   that is not an option.  (The ARGV-elements have been permuted
   so that those that are not options now come last.)

   OPTSTRING is a string containing the legitimate option characters.
   If an option character is seen that is not listed in OPTSTRING,
   return '?' after printing an error message.  If you set `opts_Err' to
   zero, the error message is suppressed but we still return '?'.

   If a char in OPTSTRING is followed by a colon, that means it wants an arg,
   so the following text in the same ARGV-element, or the text of the following
   ARGV-element, is returned in `opts_Arg'.  Two colons mean an option that
   wants an optional arg; if there is text in the current ARGV-element,
   it is returned in `opts_Arg', otherwise `opts_Arg' is set to zero.

   If OPTSTRING starts with `-' or `+', it requests different methods of
   handling the non-option ARGV-elements.
   See the comments about RETURN_IN_ORDER and REQUIRE_ORDER, above.

   Long-named options begin with `--' instead of `-'.
   Their names may be abbreviated as long as the abbreviation is unique
   or is an exact match for some defined option.  If they have an
   argument, it follows the option name in the same ARGV-element, separated
   from the option name by a `=', or else the in next ARGV-element.
   When `getopt' finds a long-named option, it returns 0 if that option's
   `flag' field is nonzero, the value of the option's `val' field
   if the `flag' field is zero.

   The elements of ARGV aren't really const, because we permute them.
   But we pretend they're const in the prototype to be compatible
   with other systems.

   LONGOPTS is a vector of `struct OPTION' terminated by an
   element containing a name which is zero.

   LONGIND returns the index in LONGOPT of the long-named option found.
   It is only valid when a long-named option has been found by the most
   recent call.

   If LONG_ONLY is nonzero, '-' as well as '--' can introduce
   long-named options.  */
{
  opts_Arg = NULL;

  if (!opts_GetOptInitialized || opts_Ind == 0) {
    optstring = opts_GetOptInitialize(argc, argv, optstring);
    opts_Ind = 1;		/* Don't scan ARGV[0], the program name.  */
    opts_GetOptInitialized = 1;
  }
  
  /* Test whether ARGV[opts_Ind] points to a non-option argument.
     Either it does not have option syntax, or there is an environment flag
     from the shell indicating it is not an option.  The later information
     is only used when the used in the GNU libc.  */


  if (opts_NextChar == NULL || *opts_NextChar == '\0') {
    /* Advance to the next ARGV-element.  */
    
    /* Give OPTS_FIRSTNONOPT & LAST_NONOPT rational values if OPTS_IND has been
       moved back by the user (who may also have changed the arguments).  */
    if (opts_LastNonOpt > opts_Ind)
      opts_LastNonOpt = opts_Ind;
    if (opts_FirstNonOpt > opts_Ind)
      opts_FirstNonOpt = opts_Ind;
    
    if (opts_Ordering == PERMUTE) {
      /* If we have just processed some options following some non-options,
	 exchange them so that the options come first.  */
      
      if (opts_FirstNonOpt != opts_LastNonOpt && opts_LastNonOpt != opts_Ind)
	opts_Exchange(argv);
      else if (opts_LastNonOpt != opts_Ind)
	opts_FirstNonOpt = opts_Ind;
      
      /* Skip any additional non-options
	 and extend the range of non-options previously skipped.  */
      
      while (opts_Ind < argc &&  (argv[opts_Ind][0] != '-' || argv[opts_Ind][1] == '\0'))
	opts_Ind++;
      opts_LastNonOpt = opts_Ind;
    }
    
    /* The special ARGV-element `--' means premature end of options.
       Skip it like a null option,
       then exchange with previous non-options as if it were an option,
       then skip everything else like a non-option.  */
    
    if (opts_Ind != argc && !strcmp(argv[opts_Ind], "--")) {
      opts_Ind++;
      
      if (opts_FirstNonOpt != opts_LastNonOpt && opts_LastNonOpt != opts_Ind)
	opts_Exchange(argv);
      else if (opts_FirstNonOpt == opts_LastNonOpt)
	opts_FirstNonOpt = opts_Ind;
      opts_LastNonOpt = argc;
      
      opts_Ind = argc;
    }
    
    /* If we have done all the ARGV-elements, stop the scan
       and back over any non-options that we skipped and permuted.  */
    
    if (opts_Ind == argc) {
      /* Set the next-arg-index to point at the non-options
	 that we previously skipped, so the caller will digest them.  */
      if (opts_FirstNonOpt != opts_LastNonOpt)
	opts_Ind = opts_FirstNonOpt;
      return -1;
    }
    
    /* If we have come to a non-option and did not permute it,
       either stop the scan or describe it to the caller and pass it by.  */
    
    if ( (argv[opts_Ind][0] != '-' || argv[opts_Ind][1] == '\0')) {
      if (opts_Ordering == REQUIRE_ORDER)
	return -1;
      opts_Arg = argv[opts_Ind++];
      return 1;
    }
    
    /* We have found another option-ARGV-element.
       Skip the initial punctuation.  */
    
    opts_NextChar = (argv[opts_Ind] + 1
		     + (longopts != NULL && argv[opts_Ind][1] == '-'));
  }
  
  /* Decode the current option-ARGV-element.  */
  
  /* Check whether the ARGV-element is a long option.
     
     If long_only and the ARGV-element has the form "-f", where f is
     a valid short option, don't consider it an abbreviated form of
     a long option that starts with f.  Otherwise there would be no
     way to give the -f short option.
     
     On the other hand, if there's a long option "fubar" and
     the ARGV-element is "-fu", do consider that an abbreviation of
     the long option, just like "--fu", and not "-f" with arg "u".
     
     This distinction seems to be the most useful approach.  */
  
  if (longopts != NULL
      && (argv[opts_Ind][1] == '-'
	  || (long_only && (argv[opts_Ind][2] || !strchr(optstring, argv[opts_Ind][1]))))) {
    const char *nameend;
    const struct OPTION *p;
    const struct OPTION *pfound = NULL;
    int exact = 0;
    int ambig = 0;
    int indfound = -1;
    int option_index;
    
    for (nameend = opts_NextChar; *nameend && *nameend != '='; nameend++)
      /* Do nothing.  */ ;
    
    /* Test all long options for either exact match
       or abbreviated matches.  */
    for (p = longopts, option_index = 0; p->name; p++, option_index++)
      if (!strncmp (p->name, opts_NextChar, nameend - opts_NextChar)) {
	if ((unsigned int) (nameend - opts_NextChar)
	    == (unsigned int) strlen(p->name)) {
	  /* Exact match found.  */
	  pfound = p;
	  indfound = option_index;
	  exact = 1;
	  break;
	}
	else if (pfound == NULL) {
	  /* First nonexact match found.  */
	  pfound = p;
	  indfound = option_index;
	}
	else
	  /* Second or later nonexact match found.  */
	  ambig = 1;
      }
    
    if (ambig && !exact) {
      if (opts_Err) {
	misc_StartUserErrorReport();
	misc_UserErrorReport("%s: option `%s' is ambiguous\n", argv[0], argv[opts_Ind]);
	misc_FinishUserErrorReport();
      }
      opts_NextChar += strlen(opts_NextChar);
      opts_Ind++;
      opts_Opt = 0;
      return '?';
    }
    
    if (pfound != NULL) {
      option_index = indfound;
      opts_Ind++;
      if (*nameend) {
	/* Don't test has_arg with >, because some C compilers don't
	   allow it to be used on enums.  */
	if (pfound->has_arg)
	  opts_Arg = nameend + 1;
	else {
	  if (opts_Err) {
	    if (argv[opts_Ind - 1][1] == '-') {
	      /* --option */
	      misc_StartUserErrorReport();
	      misc_UserErrorReport("%s: option `--%s' doesn't allow an argument\n",argv[0], pfound->name);
	      misc_FinishUserErrorReport();
	    }
	    else {
	      /* +option or -option */
	      misc_StartUserErrorReport();
	      misc_UserErrorReport("%s: option `%c%s' doesn't allow an argument\n",
				   argv[0], argv[opts_Ind - 1][0], pfound->name);
	      misc_FinishUserErrorReport();
	    }
	  }
	  opts_NextChar += strlen(opts_NextChar);
	  
	  opts_Opt = pfound->val;
	  return '?';
	}
      }
      else if (pfound->has_arg == 1) {
	if (opts_Ind < argc)
	  opts_Arg = argv[opts_Ind++];
	else {
	  if (opts_Err) {
	    misc_StartUserErrorReport();
	    misc_UserErrorReport("%s: option `%s' requires an argument\n",
				 argv[0], argv[opts_Ind - 1]);
	    misc_FinishUserErrorReport();
	  }
	  opts_NextChar += strlen(opts_NextChar);
	  opts_Opt = pfound->val;
	  return optstring[0] == ':' ? ':' : '?';
	}
      }
      opts_NextChar += strlen(opts_NextChar);
      if (longind != NULL)
	*longind = option_index;
      if (pfound->flag) {
	*(pfound->flag) = pfound->val;
	return 0;
      }
      return pfound->val;
    }
    
    /* Can't find it as a long option.  If this is not opts_GetOptLong_only,
       or the option starts with '--' or is not a valid short
       option, then it's an error.
       Otherwise interpret it as a short option.  */
    if (!long_only || argv[opts_Ind][1] == '-'
	|| strchr(optstring, *opts_NextChar) == NULL) {
      if (opts_Err) {
	if (argv[opts_Ind][1] == '-') {
	  /* --option */
	  misc_StartUserErrorReport();
	  misc_UserErrorReport("%s: unrecognized option `--%s'\n",argv[0], opts_NextChar);
	  misc_FinishUserErrorReport();
	}
	else {
	  /* +option or -option */
	  misc_StartUserErrorReport();
	  misc_UserErrorReport("%s: unrecognized option `%c%s'\n",
			       argv[0], argv[opts_Ind][0], opts_NextChar);
	  misc_FinishUserErrorReport();
	}
      }
      opts_NextChar = "";
      opts_Ind++;
      opts_Opt = 0;
      return '?';
    }
  }
  
  /* Look at and handle the next short option-character.  */
  
  {
    char c = *opts_NextChar++;
    char *temp = strchr(optstring, c);

    /* Increment `opts_Ind' when we start to process its last character.  */
    if (*opts_NextChar == '\0')
      ++opts_Ind;

    if (temp == NULL || c == ':') {
      if (opts_Err) {
	if (opts_PosixlyCorrect) {
	  /* 1003.2 specifies the format of this message.  */
	  misc_StartUserErrorReport();
	  misc_UserErrorReport("%s: illegal option -- %c\n", argv[0], c);
	  misc_FinishUserErrorReport();
	}
	else {
	  misc_StartUserErrorReport();
	  misc_UserErrorReport("%s: invalid option -- %c\n", argv[0], c);
	  misc_FinishUserErrorReport();
	}
      }
      opts_Opt = c;
      return '?';
    }
    /* Convenience. Treat POSIX -W foo same as long option --foo */
    if (temp[0] == 'W' && temp[1] == ';') {
      const char *nameend;
      const struct OPTION *p;
      const struct OPTION *pfound = NULL;
      int exact = 0;
      int ambig = 0;
      int indfound = 0;
      int option_index;
      
      /* This is an option that requires an argument.  */
      if (*opts_NextChar != '\0') {
	opts_Arg = opts_NextChar;
	/* If we end this ARGV-element by taking the rest as an arg,
	   we must advance to the next element now.  */
	opts_Ind++;
      }
      else if (opts_Ind == argc) {
	if (opts_Err) {
	  /* 1003.2 specifies the format of this message.  */
	  misc_StartUserErrorReport();
	  misc_UserErrorReport("%s: option requires an argument -- %c\n", argv[0], c);
	  misc_FinishUserErrorReport();
	}
	opts_Opt = c;
	if (optstring[0] == ':')
	  c = ':';
	else
	  c = '?';
	return c;
      }
      else
	/* We already incremented `opts_Ind' once;
	   increment it again when taking next ARGV-elt as argument.  */
	opts_Arg = argv[opts_Ind++];
      
      /* opts_Arg is now the argument, see if it's in the
	 table of longopts.  */
      
      for (opts_NextChar = nameend = opts_Arg; *nameend && *nameend != '='; nameend++)
	/* Do nothing.  */ ;
      
      /* Test all long options for either exact match
	 or abbreviated matches.  */
      for (p = longopts, option_index = 0; p->name; p++, option_index++)
	if (!strncmp (p->name, opts_NextChar, nameend - opts_NextChar)) {
	  if ((unsigned int) (nameend - opts_NextChar) == strlen(p->name)) {
	    /* Exact match found.  */
	    pfound = p;
	    indfound = option_index;
	    exact = 1;
	    break;
	  }
	  else if (pfound == NULL) {
	    /* First nonexact match found.  */
	    pfound = p;
	    indfound = option_index;
	  }
	  else
	    /* Second or later nonexact match found.  */
	    ambig = 1;
	}
      if (ambig && !exact) {
	if (opts_Err) {
	  misc_StartUserErrorReport();
	  misc_UserErrorReport("%s: option `-W %s' is ambiguous\n", argv[0], argv[opts_Ind]);
	  misc_FinishUserErrorReport();
	}
	opts_NextChar += strlen(opts_NextChar);
	opts_Ind++;
	return '?';
      }
      if (pfound != NULL) {
	option_index = indfound;
	if (*nameend) {
	  /* Don't test has_arg with >, because some C compilers don't
	     allow it to be used on enums.  */
	  if (pfound->has_arg)
	    opts_Arg = nameend + 1;
	  else {
	    if (opts_Err) {
	      misc_StartUserErrorReport();
	      misc_UserErrorReport("%s: option `-W %s' doesn't allow an argument\n", argv[0], pfound->name);
	      misc_FinishUserErrorReport();
	    }
	    
	    opts_NextChar += strlen(opts_NextChar);
	    return '?';
	  }
	}
	else if (pfound->has_arg == 1) {
	  if (opts_Ind < argc)
	    opts_Arg = argv[opts_Ind++];
	  else {
	    if (opts_Err) {
	      misc_StartUserErrorReport();
	      misc_UserErrorReport("%s: option `%s' requires an argument\n", argv[0], argv[opts_Ind - 1]);
	      misc_FinishUserErrorReport();
	    }
	    opts_NextChar += strlen(opts_NextChar);
	    return optstring[0] == ':' ? ':' : '?';
	  }
	}
	opts_NextChar += strlen(opts_NextChar);
	if (longind != NULL)
	  *longind = option_index;
	if (pfound->flag) {
	  *(pfound->flag) = pfound->val;
	  return 0;
	}
	return pfound->val;
      }
      opts_NextChar = NULL;
      return 'W';	/* Let the application handle it.   */
    }
    if (temp[1] == ':') {
      if (temp[2] == ':') {
	/* This is an option that accepts an argument optionally.  */
	if (*opts_NextChar != '\0') {
	  opts_Arg = opts_NextChar;
	  opts_Ind++;
	}
	else
	  opts_Arg = NULL;
	opts_NextChar = NULL;
      }
      else {
	/* This is an option that requires an argument.  */
	if (*opts_NextChar != '\0') {
	  opts_Arg = opts_NextChar;
	  /* If we end this ARGV-element by taking the rest as an arg,
	     we must advance to the next element now.  */
	  opts_Ind++;
	}
	else if (opts_Ind == argc) {
	  if (opts_Err) {
	    /* 1003.2 specifies the format of this message.  */
	    misc_StartUserErrorReport();
	    misc_UserErrorReport(("%s: option requires an argument -- %c\n"), argv[0], c);
	    misc_FinishUserErrorReport();
	  }
	  opts_Opt = c;
	  if (optstring[0] == ':')
	    c = ':';
	  else
	    c = '?';
	}
	else
	  /* We already incremented `opts_Ind' once;
	     increment it again when taking next ARGV-elt as argument.  */
	  opts_Arg = argv[opts_Ind++];
	opts_NextChar = NULL;
      }
    }
    return c;
  }
}


/* Like opts_GetOptLong, but '-' as well as '--' can indicate a long option.
   If an option that starts with '-' (not '--') doesn't match a long option,
   but does match a short option, it is parsed as a short option
   instead.  */

static int opts_GetOptLongOnly(int argc, const char* argv[], const char *options,
			       const struct OPTION *long_options, int *opt_index)
/**************************************************************
  FUNCTIONALITY: See opts_GetOptInternal
***************************************************************/
{
  return opts_GetOptInternal (argc, argv, options, long_options, opt_index, 1);
}


static void opts_Dummy(void)
/**************************************************************
  Assemble all unused functions to quiet gcc
***************************************************************/
{
  if (FALSE) {
    opts_PrintParameters();
    opts_PrintDeclarations();
    opts_DeclHasNoArg(NULL);
    opts_PrintLongOpts((struct OPTION*)NULL);
    opts_Dummy();
  }
}
