/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                     SYMBOLS                            * */
/* *                                                        * */
/* *  $Module:   SYMBOL                                     * */ 
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

#include "symbol.h"

SIGNATURE *symbol_SIGNATURE;

SYMBOL symbol_STANDARDVARCOUNTER;
SYMBOL symbol_INDEXVARCOUNTER;

const int symbol_MASK         = 3;  /* 0000011 */
const int symbol_TYPEMASK     = 3;  /* 0000011 */
const int symbol_STATMASK     = 4;  /* 0000100 */
const int symbol_TYPESTATMASK = 7;  /* 0000111 */


const int symbol_TYPEBITS      = 2;
const int symbol_STATBITS      = 1;
const int symbol_TYPESTATBITS  = 3;

const int symbol_SIGTYPES = 4;

const char symbol_SKFNAME[]="skf";
const char symbol_SKCNAME[]="skc";
const char symbol_SKPNAME[]="SkP";
const char symbol_SKANAME[]="SkC";
const int  symbol_SKLENGTH = 3;

static BOOL symbol_HASSIGNATURE;
static LIST symbol_FREEDSYMBOLS;

int  symbol_ACTINDEX;
int  symbol_ACTSKOLEMFINDEX;
int  symbol_ACTSKOLEMCINDEX;
int  symbol_ACTSKOLEMAINDEX;
int  symbol_ACTSKOLEMPINDEX;
int  symbol_ORDERING;
char *symbol_VARSTRING;

SYMBOL symbol_CONTEXT[symbol__MAXSIGNATURE];

static unsigned long symbol_COUNT[symbol__MAXSIGNATURE];

/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  SYMBOL CREATION                                       * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

int symbol_GetIncreasedOrderingCounter(void)
{
  return symbol_ORDERING++;
}

NAT symbol_MaxStringLength(void)
/**************************************************************
  INPUT:   None.
  RETURNS: The maximal number of characters needed for a string in the signature.
***************************************************************/
{
  int       Index;
  NAT       Result,Length;
  SIGNATURE Entry;

  Result = 0;
  
  for (Index=1; Index < symbol_ACTINDEX; Index++) {
    Entry = symbol_Signature(Index);
    if (Entry != NULL) {
      Length = Entry->length;
      if (Length > Result)
	Result = Length;
    }
  }
  return Result;
}

static SYMBOL symbol_SignatureCreate(char* String, int Type, int Arity,
				     int Status, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A pointer to a string, a type, the arity and the status
  RETURNS: The symbol containing the passed parameters.
  SUMMARY: Establishes a new symbol in the symbol table and returns the
	   internal representation (pointer and type).
  CAUTION: The string is not copied!
***************************************************************/
{
  SIGNATURE Entry;
  
#ifdef CHECK
  if (!symbol_SignatureExists()) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In symbol_SignatureCreate:");
    misc_ErrorReport(" Module was initialized with no signature.\n");
    misc_FinishErrorReport();
  } 
  if (Type < 0 || Type >= symbol_SIGTYPES) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In symbol_SignatureCreate: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  if ((int)symbol_ACTINDEX >= symbol__MAXSIGNATURE &&
      list_Empty(symbol_FREEDSYMBOLS)) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In symbol_SignatureCreate: No more symbols available.\n");
    misc_FinishUserErrorReport();
  }
  
  if (strlen(String)>=symbol__SYMBOLMAXLEN) {
    misc_StartUserErrorReport();
    misc_UserErrorReport("\n In symbol_SignatureCreate: String too long.\n");
    misc_FinishUserErrorReport();
  }
    
  Entry              = symbol_GetSignature();
  Entry->weight      = 1;
  Entry->props       = 0;
  Entry->name        = String;
  Entry->length      = strlen(String);
  Entry->arity       = Arity;
  Entry->generatedBy = list_Nil();
  
  if (list_Empty(symbol_FREEDSYMBOLS)) {
    Entry->info = symbol_SignatureSymbol(symbol_ACTINDEX, Type, Status);
    symbol_SetSignature(symbol_ACTINDEX++, Entry);
  }
  else {
    int Index;
    
    Index               = (int)list_Car(symbol_FREEDSYMBOLS);
    symbol_FREEDSYMBOLS = list_PointerDeleteElement(symbol_FREEDSYMBOLS,
						    (POINTER)Index);
    Entry->info = symbol_SignatureSymbol(Index, Type, Status);
    symbol_SetSignature(Index, Entry);
  }

  /* Define precedence of symbol */
  symbol_SetIncreasedOrdering(Precedence, Entry->info);

  return Entry->info;
}


SYMBOL symbol_CreateFunction(const char* String, int Arity, int Status,
			     PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A string defining a symbol name, an arity, the status the 
           created function symbol is supposed to have and a precedence
	   object.
  RETURNS: A new symbol for a new function.
  SUMMARY: Creates a new function symbol.
  EFFECTS: Inserts the new function in the symbol table.
           The precedence of the new symbol is set in <Precedence>.
***************************************************************/
{
  if (Arity == 0)
    return symbol_SignatureCreate(strcpy(memory_Malloc(symbol__SYMBOLMAXLEN),
					 String),
				  symbol_CONSTANT, Arity, Status, Precedence);
  else
    return symbol_SignatureCreate(strcpy(memory_Malloc(symbol__SYMBOLMAXLEN),
					 String),
				  symbol_FUNCTION, Arity, Status, Precedence);
}

SYMBOL symbol_CreateSkolemFunction(int Arity, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   The arity of a function to be created, and a precedence.
  RETURNS: A new skolem symbol having the required arity.
  SUMMARY: Creates a new function symbol.
  EFFECTS: Inserts the new function in the symbol table.
           The precedence of the new symbol is set in <Precedence>.
***************************************************************/
{
  char   newname[10];
  SYMBOL Result;

  Result = (SYMBOL)NULL;

  while (Result == (SYMBOL)NULL) {
    if (Arity == 0)
      sprintf(newname,"%s%d",symbol_SKCNAME,symbol_ACTSKOLEMCINDEX++);
    else
      sprintf(newname,"%s%d",symbol_SKFNAME,symbol_ACTSKOLEMFINDEX++);
    if (symbol_Lookup(newname) == 0)
      Result = symbol_CreateFunction(newname, Arity, symbol_STATLEX, Precedence);
  }

  symbol_AddProperty(Result,SKOLEM);

  return Result;
}


SYMBOL symbol_CreatePredicate(const char* String, int Arity, int Status,
			      PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A string, a symbol arity, the status the created predicate
           is supposed to have, and a precedence object.
  RETURNS: A new symbol for a new predicate.
  SUMMARY: Creates a new predicate symbol.
  EFFECTS: Inserts the new predicate symbol into the symbol table.
           The precedence of the new symbol is set in <Precedence>.
***************************************************************/
{ 
  return symbol_SignatureCreate(strcpy(memory_Malloc(symbol__SYMBOLMAXLEN),
				       String),
				symbol_PREDICATE, Arity, Status, Precedence);
}

SYMBOL symbol_CreateSkolemPredicate(int Arity, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   The arity of a new Skolem predicate symbol and a precedence object.
  RETURNS: A new symbol for a new predicate.
  SUMMARY: Creates a new predicate symbol.
  EFFECTS: Inserts the new predicate symbol into the symbol table.
           The precedence of the new symbol is set in <Precedence>.
***************************************************************/
{ 
  char   newname[10];
  SYMBOL Result;

  Result = (SYMBOL)NULL;

  while (Result == (SYMBOL)NULL) {
    if (Arity==0)
      sprintf(newname,"%s%d",symbol_SKANAME,symbol_ACTSKOLEMAINDEX++);
    else
      sprintf(newname,"%s%d",symbol_SKPNAME,symbol_ACTSKOLEMPINDEX++);
    if (symbol_Lookup(newname) == 0)
      Result = symbol_CreatePredicate(newname, Arity, symbol_STATLEX, Precedence);
  }

  return Result;
}


SYMBOL symbol_CreateJunctor(const char* String, int Arity, int Status,
			    PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A string, a symbol arity, the status the created junctor
           is supposed to have, and a precedence object.
  RETURNS: A new symbol for a new junctor.
  SUMMARY: Creates a new junctor symbol.
  EFFECTS: Inserts the new junctor symbol into the symbol table.
           The precedence of the new symbol is set in <Precedence>.
***************************************************************/
{ 
  return symbol_SignatureCreate(strcpy(memory_Malloc(symbol__SYMBOLMAXLEN),
				       String),
				symbol_JUNCTOR, Arity, Status, Precedence);
}


BOOL symbol_IsSymbol(SYMBOL Symbol)
/**************************************************************
  INPUT:    A symbol.
  RETURNS: TRUE if the symbols is  a variable or contained
           in the symbol table.
***************************************************************/
{
  return 
    (!symbol_SignatureExists() ||
     ((!symbol_Equal(Symbol, symbol__NULL)) &&
      ((symbol_IsVariable(Symbol) && Symbol<symbol_MaxVars()) || 
       (symbol_IsSignature(Symbol) && symbol_Index(Symbol)<symbol_ACTINDEX))));
}


void symbol_Delete(SYMBOL Symbol)
/**************************************************************
  INPUT:   A symbol.
  RETURNS: Nothing.
  SUMMARY: Deletes the symbol from the symbol table and frees its memory.
***************************************************************/
{
#ifdef CHECK
  if (!symbol_SignatureExists()) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In symbol_Delete: Module was initialized without signature.\n");
    misc_FinishErrorReport();
  }
  if (!symbol_IsSymbol(Symbol)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In symbol_Delete: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  if (!symbol_IsVariable(Symbol)) {
    int       Index;
    SIGNATURE Entry;
    
    Index               = symbol_Index(Symbol);
    symbol_FREEDSYMBOLS = list_Cons((POINTER)Index,symbol_FREEDSYMBOLS);
    Entry               = symbol_Signature(Index);
    symbol_SetSignature(Index, NULL);
    symbol_FreeSignature(Entry);
  }
}

LIST symbol_GetAllSymbols(void)
/**************************************************************
  INPUT:   None.
  RETURNS: A list of all generated symbols.
***************************************************************/
{
  LIST Result;

  Result = list_Nil();

  if (symbol_SignatureExists()) {
    int       Index;
    SIGNATURE S;
    
    for (Index = 1; Index < symbol_ACTINDEX; Index++) {
      S = symbol_Signature(Index);
      if (S != NULL) {
	Result = list_Cons((POINTER)symbol_GetSigSymbol(Index), Result);
      }
    }
  }
  return Result;
}


LIST symbol_GetAllPredicates(void)
/**************************************************************
  INPUT:   None.
  RETURNS: A list of all predicate symbols.
***************************************************************/
{
  LIST Result;

  Result = list_Nil();

  if (symbol_SignatureExists()) {
    int       Index;
    SIGNATURE S;
    
    for (Index = 1; Index < symbol_ACTINDEX; Index++) {
      S = symbol_Signature(Index);
      if (S != NULL && symbol_IsPredicate(symbol_GetSigSymbol(Index)))
	Result = list_Cons((POINTER)symbol_GetSigSymbol(Index), Result);
    }
  }
  return Result;
}


LIST symbol_GetAllFunctions(void)
/**************************************************************
  INPUT:   None.
  RETURNS: A list of all function symbols.
***************************************************************/
{
  LIST Result;

  Result = list_Nil();

  if (symbol_SignatureExists()) {
    int       Index;
    SIGNATURE S;
    
    for (Index = 1; Index < symbol_ACTINDEX; Index++) {
      S = symbol_Signature(Index);
      if (S != NULL && symbol_IsFunction(symbol_GetSigSymbol(Index)))
	Result = list_Cons((POINTER)symbol_GetSigSymbol(Index), Result);
    }
  }
  return Result;
}


void symbol_FreeAllSymbols(void)
/**************************************************************
  INPUT:   None.
  RETURNS: Nothing.
  EFFECTS: Frees all generated symbols
***************************************************************/
{
  if (symbol_SignatureExists()) {
    int       Index;
    SIGNATURE S;
    
    for (Index = 1; Index < symbol_ACTINDEX; Index++) {
      S = symbol_Signature(Index);
      if (S != NULL)
	symbol_FreeSignature(S);
    }
    memory_Free(symbol_SIGNATURE, sizeof(SIGNATURE[symbol__MAXSIGNATURE]));
  }
  
  memory_Free(symbol_VARSTRING, symbol__SYMBOLMAXLEN);
  list_Delete(symbol_FREEDSYMBOLS);
}


void symbol_Init(BOOL Signature)
/**************************************************************
  INPUT:   A flag indicating whether a signature is used or not.
  RETURNS: None.
  SUMMARY: Initializes the Symbol Module.
  EFFECTS: Initializes global variables.
  CAUTION: MUST BE CALLED BEFORE ANY OTHER Symbol-FUNCTION.
***************************************************************/
{
  symbol_ResetSkolemIndex();
  symbol_ContextClean();

  if (Signature)
    symbol_SIGNATURE = (SIGNATURE*)memory_Malloc(sizeof(SIGNATURE[symbol__MAXSIGNATURE]));

  symbol_STANDARDVARCOUNTER = symbol_GetInitialStandardVarCounter();
  symbol_INDEXVARCOUNTER    = symbol_GetInitialIndexVarCounter();
  
  symbol_ACTINDEX           = 1;
  symbol_ORDERING           = 1;
  symbol_VARSTRING          = memory_Malloc(symbol__SYMBOLMAXLEN);
  
  symbol_HASSIGNATURE       = Signature;
  symbol_FREEDSYMBOLS       = list_Nil();
}


BOOL symbol_SignatureExists(void)
/**************************************************************
  INPUT:   None.
  RETURNS: TRUE, if a symbol signature was created, FALSE otherwise.
***************************************************************/
{
  return symbol_HASSIGNATURE;
}

void symbol_ReinitGenericNameCounters(void)
/**************************************************************
  INPUT:   None.
  RETURNS: Nothing.
  EFFECTS: Scans the symbol signature for generic names and if
           there exists some, the corresponding counters are increased.
***************************************************************/
{
  if (symbol_SignatureExists()) {
    int          Index,Num;
    SYMBOL       Info;
    SIGNATURE    Entry;
    char         *Name,*Subname;
  
    for (Index=1; Index < symbol_ACTINDEX; Index++) {
      Entry = symbol_Signature(Index);
      if (Entry != NULL) {
	Info   = Entry->info;
	Name   = Entry->name;
	if (strlen(Name)>symbol_SKLENGTH) {
	  Subname = Name + symbol_SKLENGTH;
	
	  switch (symbol_Type(Info)) {
	  
	  case symbol_CONSTANT:
	    if (strncmp(Name,symbol_SKCNAME,symbol_SKLENGTH) == 0 && 
		string_StringIsNumber(Subname)) {
	      Num = atoi(Subname);
	      if (Num >= symbol_ACTSKOLEMCINDEX)
		symbol_ACTSKOLEMCINDEX = Num + 1;
	    }
	    break;
	  case symbol_FUNCTION:
	    if (strncmp(Name,symbol_SKFNAME,symbol_SKLENGTH) == 0  &&
		string_StringIsNumber(Subname)) {
	      Num = atoi(Subname);
	      if (Num >= symbol_ACTSKOLEMFINDEX)
		symbol_ACTSKOLEMFINDEX = Num + 1;
	    }
	    break;
	  case symbol_PREDICATE:
	    if (Entry->arity == 0) {
	      if (strncmp(Name,symbol_SKANAME,symbol_SKLENGTH) == 0  &&
		  string_StringIsNumber(Subname)) {
		Num = atoi(Subname);
		if (Num >= symbol_ACTSKOLEMAINDEX)
		  symbol_ACTSKOLEMAINDEX = Num + 1;
	      }
	    }
	    else {
	      if (strncmp(Name,symbol_SKPNAME,symbol_SKLENGTH) == 0  &&
		  string_StringIsNumber(Subname)) {
		Num = atoi(Subname);
		if (Num >= symbol_ACTSKOLEMPINDEX)
		  symbol_ACTSKOLEMPINDEX = Num + 1;
	      }
	    }    
	  }
	}
      }
    }
  }
}

  
/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  SYMBOL SEARCHING                                      * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

SYMBOL symbol_Lookup(const char* String)
/**********************************************************
  INPUT:   A pointer to a string.
  RETURNS: If a symbol with name String exists in the signature, the symbol;
           0 otherwise
********************************************************/
{
  if (symbol_SignatureExists()) {
    int       Index;
    SIGNATURE S;
    
    for (Index = 1; Index < symbol_ACTINDEX; Index++) {
      S = symbol_Signature(Index);
      if (S != NULL && string_Equal(String, S->name))
	return S->info;
    }
  }
  
  return 0;
}


/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  SPECIALS                                              * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

void symbol_LowerSignature(void)
/**************************************************************
  INPUT:   None.
  RETURNS: Nothing.
  EFFECT:  Any predicate or function symbol in the signature that
           starts with a capital letter is prefixed with "ss"
***************************************************************/
{
  int       Index;
  SIGNATURE Entry;
  SYMBOL    Info;
  char*     String;

  for (Index = 1; Index < symbol_ACTINDEX; Index++) {
    Entry = symbol_Signature(Index);
    if (Entry != NULL) {
      Info = Entry->info;
	
      if (symbol_IsPredicate(Info) || symbol_IsFunction(Info)) {
	String = Entry->name;
	if ('A' <= String[0] && String[0] <= 'Z') {
	  char* New;
	  New = (char *)memory_Malloc(symbol__SYMBOLMAXLEN);
	  strcpy(&(New[2]),String);
	  New[0] = New[1] = 's';             /* prefix "ss" */

	  Entry->name = New;
	  memory_Free(String,symbol__SYMBOLMAXLEN);
	}
      }
    }
  }
}

void symbol_Dump(PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A precedence
  RETURNS: Nothing.
  EFFECT:  Dumps all existing symbols to stdout.
***************************************************************/
{
  if (symbol_SignatureExists()) {
    int       Index;
    SIGNATURE S;
    fputs("Dump:", stdout);
    for (Index = 1; Index < symbol_ACTINDEX; Index++) {
      S = symbol_Signature(Index);
      if (S != NULL)
	printf("\n\t %4d:%4d:%4d:%4d:%4d:%s:%d", Index, S->info, S->weight,
	       Precedence[Index], S->props, S->name, S->length);
    }
  }
}


LIST symbol_SortByPrecedence(LIST Symbols, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A list of symbols, and a precedence.
  RETURNS: The same list where the elements are sorted with
           respect to decreasing precedence.
  CAUTION: Destructive.
***************************************************************/
{
  LIST Scan1,Scan2,Min;
  POINTER Exchange;

  /* We can't use list_Sort, since list_Sort expects an ordering
     function that receives two arguments. Since symbol_PrecedenceGreater
     requires three arguments, we have to define our own sorting function.
  */

  for (Scan1=Symbols; !list_Empty(Scan1); Scan1=list_Cdr(Scan1)) {
    Min = Scan1;
    for (Scan2 = list_Cdr(Scan1); !list_Empty(Scan2); Scan2 = list_Cdr(Scan2))
      if (symbol_PrecedenceGreater(Precedence, (SYMBOL) list_Car(Scan2),
				   (SYMBOL) list_Car(Min))) {
	Exchange = list_Car(Min);
	list_Rplaca(Min, list_Car(Scan2));
	list_Rplaca(Scan2, Exchange);
      }
  }

  return Symbols;
}

void symbol_RearrangePrecedence(PRECEDENCE Precedence, LIST UserPrecedence)
/**************************************************************
  INPUT:   A precedence and a list of symbols in the user 
           specified precedence, sorted in decreasing order.
  RETURNS: Nothing.
  EFFECT:  Modifies the given precedence to comply with the
           symbol precedence selected by the user.
***************************************************************/
{
  LIST Scan1, Scan2, Precedences;

  Precedences = list_Nil();

  for (Scan1 = UserPrecedence; !list_Empty(Scan1); Scan1 = list_Cdr(Scan1)) {
    Precedences = list_Cons((POINTER) symbol_Ordering(Precedence, (SYMBOL) list_Car(Scan1)), 
			    Precedences);
  }

  Precedences = list_PointerSort(Precedences);

  Scan1 = UserPrecedence;
  Scan2 = Precedences;

  while (Scan1 != list_Nil() && Scan2 != list_Nil()) {
    symbol_SetOrdering(Precedence, (SYMBOL) list_Car(Scan1), (int) list_Car(Scan2));
    Scan1 = list_Cdr(Scan1);
    Scan2 = list_Cdr(Scan2);
  }

  list_Delete(Precedences);
}
  
/* unused */
void symbol_PrintPrecedence(PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A precedence.
  RETURNS: Nothing.
  EFFECT:  Prints the precedence to stdout.
***************************************************************/
{
  if (symbol_SignatureExists()) {
    LIST      Symbols, Scan;
    int       Index;
    SIGNATURE S;
    Symbols = list_Nil();
    for (Index = 1; Index < symbol_ACTINDEX; Index++) {
      S = symbol_Signature(Index);
      if (S != NULL &&
	  (symbol_IsPredicate(S->info) || symbol_IsFunction(S->info))) 
	Symbols = list_Cons((POINTER)S->info, Symbols);
    }
    Symbols = symbol_SortByPrecedence(Symbols, Precedence);

    for (Scan = Symbols; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      S = symbol_Signature(symbol_Index((SYMBOL)list_Car(Scan)));
      fputs(S->name, stdout);
      if (!list_Empty(list_Cdr(Scan)))
	fputs(" > ", stdout);
    }
    list_Delete(Symbols);
  }
}


void symbol_FPrintPrecedence(FILE *File, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A file pointer and a precedence.
  RETURNS: void
  EFFECT:  Prints the current precedence as a setting command
           in DFG syntax to <File>.
***************************************************************/
{
  if (symbol_SignatureExists()) {
    LIST Symbols,Scan;
    int Index;
    SIGNATURE S;

    Symbols = list_Nil();
    for (Index = 1; Index < symbol_ACTINDEX; Index++) {
      S = symbol_Signature(Index);
      if (S != NULL &&
	  (symbol_IsPredicate(S->info) || symbol_IsFunction(S->info))) 
	Symbols = list_Cons((POINTER)S->info, Symbols);
    }
    Symbols = symbol_SortByPrecedence(Symbols, Precedence);
    Index   = 0;
    fputs("set_precedence(", File);
    for (Scan = Symbols; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
      S = symbol_Signature(symbol_Index((SYMBOL)list_Car(Scan)));
      fputs(S->name, File);
      if (!list_Empty(list_Cdr(Scan)))
	putc(',', File);
      if (Index > 15) {
	Index = 0;
	fputs("\n\t", File);
      }
      else
	Index++;
    }
    fputs(").", File);
    list_Delete(Symbols);
  }
}

void symbol_SetCount(SYMBOL Symbol, unsigned long Count)
/**************************************************************
  INPUT:   A symbol, and a symbol count.
  RETURNS: Nothing.
  SUMMARY: Sets the symbol count for the symbol to Count. 
***************************************************************/
{
  symbol_COUNT[symbol_Index(Symbol)] = Count;
}

unsigned long symbol_GetCount(SYMBOL Symbol)
/**************************************************************
  INPUT:   A symbol.
  RETURNS: The number of occurences of the symbol in the clause
           set.
  SUMMARY: Gets the symbol count for the symbol. 
***************************************************************/
{
  return symbol_COUNT[symbol_Index(Symbol)];
}

/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *  SYMBOL OUTPUT	                                    * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/

void symbol_Print(SYMBOL Symbol)
/**************************************************************
  INPUT:   A symbol.
  RETURNS: Nothing.
  SUMMARY: Prints a symbol to stdout. 
***************************************************************/
{
  symbol_FPrint(stdout, Symbol);
}


void symbol_FPrint(FILE* File, SYMBOL Symbol)
/**************************************************************
  INPUT:   A file and a symbol.
  RETURNS: None.
  SUMMARY: Prints a symbol to the file. 
***************************************************************/
{ 
#ifdef CHECK
  if (!symbol_IsSymbol(Symbol)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In symbol_FPrint: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  if (symbol_Equal(symbol_Null(),Symbol))
    fputs("NULL", File);
  else if (symbol_IsVariable(Symbol)) {
    SYMBOL NormSymbol;

    NormSymbol = symbol_NormVar(Symbol);

    if (symbol_IsStandardVariable(Symbol)) {
      if (Symbol <= 6)
	/* U, V, W, X, Y, Z */
	sprintf(symbol_VARSTRING,"%c", 'U' + NormSymbol - 1);
      else
	/* X1, X2, X3, ... */
	sprintf(symbol_VARSTRING,"X%d", NormSymbol - 6);
    }
    else if (symbol_IsIndexVariable(Symbol))
      /* I1, I2, I3, ... */
      sprintf(symbol_VARSTRING,"I%d", NormSymbol);

    fputs(symbol_VARSTRING, File);
  }
  else if (symbol_SignatureExists())
    fputs(symbol_Name(Symbol), File);
  else
    fprintf(File, "%d", Symbol);
}


void symbol_FPrintOtter(FILE* File, SYMBOL Symbol)
/**************************************************************
  INPUT:   A file and a symbol.
  RETURNS: None.
  SUMMARY: Prints a symbol in Otter format to stdout. 
***************************************************************/
{ 
#ifdef CHECK
  if (!symbol_IsSymbol(Symbol)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In symbol_FPrintOtter: Illegal input.\n");
    misc_FinishErrorReport();
  }
#endif

  if (symbol_IsVariable(Symbol)) {
    SYMBOL NormSymbol;

    NormSymbol = symbol_NormVar(Symbol);

    if (symbol_IsStandardVariable(Symbol)) {
      if (Symbol <= 6)
	/* u, v, w, x, y, z */
	sprintf(symbol_VARSTRING,"%c", 116 + NormSymbol);
      else
	/* x1, x2, x3, ... */
	sprintf(symbol_VARSTRING,"x%d", NormSymbol - 6);
    }
    else if (symbol_IsIndexVariable(Symbol))
      /* I1, I2, I3, ... */
      sprintf(symbol_VARSTRING,"I%d", NormSymbol);

    fputs(symbol_VARSTRING, File);
  }
  else 
    if (symbol_SignatureExists()) {
      if (symbol_IsConstant(Symbol))
	fprintf(File, "c%s", symbol_Name(Symbol));
      else
	if (symbol_IsFunction(Symbol))
	  fprintf(File, "f%s", symbol_Name(Symbol));
	else
	  if (symbol_IsPredicate(Symbol))
	    fprintf(File, "P%s", symbol_Name(Symbol));
	  else
	    fputs(symbol_Name(Symbol), File);
    }
    else
      fprintf(File, "%d", Symbol);
}


void symbol_PrintLn(SYMBOL Symbol)
/**************************************************************
  INPUT:   A symbol.
  RETURNS: None.
  SUMMARY: Prints a symbol and a newline to stdout. 
***************************************************************/
{ 
  symbol_Print(Symbol);
  putchar('\n');
  
}


void symbol_PrintAll(void)
/**************************************************************
  INPUT:   None.
  RETURNS: None.
  SUMMARY: Prints all symbols to stdout.
***************************************************************/
{
  const int symbol_TABLEBLANKS = 2;
  const int symbol_TABLETYPE   = 6;  /* breadth of the columns */
  const int symbol_TABLEARITY  = 7;
  const int symbol_TABLESTAT   = 6;
  const int symbol_TABLEPROP   = 8;  
  const int symbol_TABLESTRING = 36;

  if (symbol_SignatureExists()) {
    int          Index;
    SYMBOL       Info;
    SIGNATURE    Entry;
    unsigned int TypePos, ArityPos, StatPos, PropPos, StringPos, EndPos, ActPos;

    TypePos   = symbol_TABLEBLANKS;
    ArityPos  = TypePos   + symbol_TABLETYPE   + 1;
    StatPos   = ArityPos  + symbol_TABLEARITY  + 1;
    PropPos   = StatPos   + symbol_TABLESTAT   + 1;
    StringPos = PropPos   + symbol_TABLEPROP   + 1;
    EndPos    = StringPos + symbol_TABLESTRING + 1;

    fputs("\n\n", stdout);
    misc_PrintChar(symbol_TABLEBLANKS, ' '); putchar('+');
    misc_PrintChar(symbol_TABLETYPE,   '-'); putchar('+');
    misc_PrintChar(symbol_TABLEARITY,  '-'); putchar('+');
    misc_PrintChar(symbol_TABLESTAT,   '-'); putchar('+');
    misc_PrintChar(symbol_TABLEPROP,   '-'); putchar('+');
    misc_PrintChar(symbol_TABLESTRING, '-'); putchar('+'); putchar('\n');
    misc_PrintChar(symbol_TABLEBLANKS, ' '); putchar('|');
    ActPos = TypePos   + 1 + fputs(" Type", stdout);
    misc_PrintChar((ArityPos  - ActPos), ' '); putchar('|');
    ActPos = ArityPos  + 1 + fputs(" Arity", stdout);
    misc_PrintChar((StatPos   - ActPos), ' '); putchar('|');
    ActPos = StatPos   + 1 + fputs(" Stat", stdout);
    misc_PrintChar((PropPos   - ActPos), ' '); putchar('|');
    ActPos = PropPos   + 1 + fputs(" Prop", stdout);
    misc_PrintChar((StringPos - ActPos), ' '); putchar('|');
    ActPos = StringPos + 1 + fputs(" String", stdout);
    misc_PrintChar((EndPos    - ActPos), ' '); putchar('|'); putchar('\n');
    misc_PrintChar(symbol_TABLEBLANKS,   ' '); putchar('+');
    misc_PrintChar(symbol_TABLETYPE,     '-'); putchar('+');
    misc_PrintChar(symbol_TABLEARITY,    '-'); putchar('+');
    misc_PrintChar(symbol_TABLESTAT,     '-'); putchar('+');
    misc_PrintChar(symbol_TABLEPROP,     '-'); putchar('+');
    misc_PrintChar(symbol_TABLESTRING,   '-'); putchar('+'); putchar('\n');
  
    for (Index = 1; Index < symbol_ACTINDEX; Index++) {
      Entry  = symbol_Signature(Index);
      if (Entry != NULL) {
	Info = Entry->info;
	
	misc_PrintChar(symbol_TABLEBLANKS,   ' '); putchar('|');
	ActPos = TypePos + 1;

	switch (symbol_Type(Info)) {
	case symbol_CONSTANT:
	  ActPos += fputs(" Con", stdout); break;
	case symbol_FUNCTION:
	  ActPos += fputs(" Fun", stdout); break;
	case symbol_PREDICATE:
	  ActPos += fputs(" Pre", stdout); break;
	case symbol_JUNCTOR:
	  ActPos += fputs(" Jun", stdout); break;
	}
	misc_PrintChar((ArityPos  - ActPos), ' '); putchar('|');
	ActPos = ArityPos + 1 + printf(" %3d", Entry->arity);
	misc_PrintChar((StatPos   - ActPos), ' '); putchar('|');
	ActPos = StatPos + 1;
	if (symbol_Type(Info) == symbol_FUNCTION) {
	  switch (symbol_Stat(Info)) {
	  case symbol_STATLEX:
	    ActPos += fputs(" Lex", stdout); break;
	  case symbol_STATMUL:
	    ActPos += fputs(" Mul", stdout); break;
	  }
	}
	misc_PrintChar((PropPos   - ActPos), ' '); putchar('|');
	ActPos = PropPos + 1 + printf(" %u", Entry->props);
	misc_PrintChar((StringPos - ActPos), ' '); putchar('|');
	ActPos = StringPos + 1 +  printf(" %s", Entry->name);
	misc_PrintChar((EndPos    - ActPos), ' '); putchar('|'); putchar('\n');
      }
    }
    misc_PrintChar(symbol_TABLEBLANKS, ' '); putchar('+');
    misc_PrintChar(symbol_TABLETYPE,   '-'); putchar('+');
    misc_PrintChar(symbol_TABLEARITY,  '-'); putchar('+');
    misc_PrintChar(symbol_TABLESTAT,   '-'); putchar('+');
    misc_PrintChar(symbol_TABLEPROP,   '-'); putchar('|');
    misc_PrintChar(symbol_TABLESTRING, '-'); putchar('+'); putchar('\n');
  }
}

