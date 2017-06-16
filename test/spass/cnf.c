/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *               CNF TRANSLATOR                           * */
/* *                                                        * */
/* *  $Module:   CNF                                        * */
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
/* $Revision: 21527 $                                       * */
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

#include "cnf.h"
#include "rules-inf.h"
#include "rules-red.h"


static TERM   cnf_AntiPrenexPath(TERM, TERM);
static TERM   cnf_ApplyDefinitionInternOnce(TERM, TERM, TERM, TERM, BOOL*);

static SYMBOL cnf_GetDualSymbol(SYMBOL symbol);

static TERM   cnf_IsDefinition(TERM);

static void   cnf_OptimizedSkolemFormula(PROOFSEARCH, TERM, char*, BOOL, TERM,
					 LIST*, LIST*, BOOL, HASH, int);
static int    cnf_PredicateOccurrences(TERM, SYMBOL);

static void   cnf_RplacVar(TERM, LIST, LIST);

static LIST   cnf_SatUnit(PROOFSEARCH, LIST);
static LIST   cnf_SkolemFunctionFormula(TERM, LIST, LIST, PRECEDENCE);

/* For every variable the depth in the current term, required for */
/* strong skolemization */
static int* cnf_VARIABLEDEPTHARRAY;
/* Holds a copy of the ProofSearch--Object built by cnf_Flotter */
/* during cnf_QueryFlotter */
static PROOFSEARCH cnf_SEARCHCOPY;

/* Proofsearch--Object for the function cnf_HaveProof. We need this */
/* to reduce the number of term stamps required. */
static PROOFSEARCH cnf_HAVEPROOFPS;


void cnf_Init(FLAGSTORE Flags)
/***************************************************************
  INPUT:   A flag store.
  RETURNS: None.
  SUMMARY: Initializes the CNF Module.
  EFFECTS: Initializes global variables.
  CAUTION: MUST BE CALLED BEFORE ANY OTHER CNF-FUNCTION.
***************************************************************/
{
  /* If strong skolemization is performed, allocate array for variable depth */
  if (flag_GetFlagValue(Flags, flag_CNFSTRSKOLEM))
    cnf_VARIABLEDEPTHARRAY = (int*) memory_Malloc(sizeof(int[symbol__MAXSTANDARDVAR + 1]));
  else
    cnf_VARIABLEDEPTHARRAY = NULL;
  cnf_SEARCHCOPY  = prfs_Create();
  cnf_HAVEPROOFPS = prfs_Create();
}


void cnf_Free(FLAGSTORE Flags)
/**************************************************************
  INPUT:   A flag store.
  RETURNS: None.
  SUMMARY: Frees the CNF Module.
***************************************************************/
{
  /* If strong skolemization is performed, free array for variable depth */
  if (flag_GetFlagValue(Flags, flag_CNFSTRSKOLEM)) {
    memory_Free(cnf_VARIABLEDEPTHARRAY, sizeof(int) * (symbol__NOOFSTANDARDVAR + 1));
    cnf_VARIABLEDEPTHARRAY = NULL;
  }
  prfs_Delete(cnf_SEARCHCOPY);
  cnf_SEARCHCOPY = NULL;
  prfs_Delete(cnf_HAVEPROOFPS);
  cnf_HAVEPROOFPS = NULL;
}


static int cnf_GetFormulaPolarity(TERM term, TERM subterm)
/**********************************************************
  INPUT:   Two terms term and subterm where subterm is a
           subterm of term.
  RETURNS: The polarity of subterm in term.
********************************************************/
{  
  LIST   scan;
  TERM   term1;
  int    polterm1,bottom; 

  bottom = vec_ActMax();
  vec_Push((POINTER) 1);
  vec_Push(term);

  do {
    term1    = (TERM)vec_PopResult();
    polterm1 = (int)vec_PopResult();
    if (term1 == subterm) {
      vec_SetMax(bottom);
      return polterm1;
    }else
      if (symbol_Equal(term_TopSymbol(term1),fol_Not())) {
	vec_Push((POINTER) (- polterm1));
	vec_Push(list_Car(term_ArgumentList(term1)));
      }
    if (symbol_Equal(term_TopSymbol(term1),fol_Exist()) ||
	symbol_Equal(term_TopSymbol(term1),fol_All())) {
      vec_Push((POINTER)polterm1);
      vec_Push(list_Second(term_ArgumentList(term1)));
    }
    else
      if (symbol_Equal(term_TopSymbol(term1),fol_Implies())) {
	vec_Push((POINTER) (- polterm1));
	vec_Push(list_Car(term_ArgumentList(term1)));
	vec_Push((POINTER) polterm1);
	vec_Push(list_Second(term_ArgumentList(term1)));
      }
      else
	if (symbol_Equal(term_TopSymbol(term1),fol_Equiv())) {
	  vec_Push(0);
	  vec_Push(list_Car(term_ArgumentList(term1)));
	  vec_Push(0);
	  vec_Push(list_Second(term_ArgumentList(term1)));
	}
	else
	  if (symbol_Equal(term_TopSymbol(term1),fol_And()) ||
	      symbol_Equal(term_TopSymbol(term1),fol_Or())) {
	    for (scan = term_ArgumentList(term1);
		 !list_Empty(scan);
		 scan = list_Cdr(scan)) {
	      vec_Push((POINTER) polterm1);
	      vec_Push(list_Car(scan));
	    }
	  }
  } while (bottom != vec_ActMax());
  vec_SetMax(bottom);
  misc_StartErrorReport();
  misc_ErrorReport("\n In cnf_GetFormulaPolarity: Wrong arguments !\n");
  misc_FinishErrorReport();
  return -2;
}


static BOOL cnf_ContainsDefinitionIntern(TERM TopDef, TERM Def, int Polarity,
					 TERM* FoundPred)
/**********************************************************
  INPUT:   A term TopDef which is the top level term of the recursion.
           A term Def which is searched for a definition.
           A pointer to a term into which the predicate of the definition
	   is stored if it is found.
  RETURNS: TRUE if Def contains a definition that can be converted
           to standard form.
********************************************************/
{
  /* AND / OR */
  /* In these cases Def cannot be converted to standard form */

  if ((symbol_Equal(term_TopSymbol(Def),fol_And()) && (Polarity == 1)) ||
      (symbol_Equal(term_TopSymbol(Def),fol_Or()) && (Polarity == -1)))
    return FALSE;

  if (symbol_Equal(term_TopSymbol(Def), fol_And()) ||
     symbol_Equal(term_TopSymbol(Def),fol_Or())) {
    /* Polarity is ok */
    LIST l;
    for (l=term_ArgumentList(Def); !list_Empty(l); l=list_Cdr(l))
      if (cnf_ContainsDefinitionIntern(TopDef, list_Car(l), Polarity, FoundPred))
	return TRUE;
    return FALSE;
  }

  /* Quantifiers */
  if (fol_IsQuantifier(term_TopSymbol(Def)))
    return cnf_ContainsDefinitionIntern(TopDef, term_SecondArgument(Def), Polarity, FoundPred);
  
  /* Negation */
  if (symbol_Equal(term_TopSymbol(Def),fol_Not()))
    return cnf_ContainsDefinitionIntern(TopDef, term_FirstArgument(Def), -Polarity, FoundPred);
  
  /* Implication */
  if (symbol_Equal(term_TopSymbol(Def),fol_Implies())) {
    if (Polarity==1) {
      if (cnf_ContainsDefinitionIntern(TopDef, term_FirstArgument(Def), -Polarity, FoundPred))
	return TRUE;
      return cnf_ContainsDefinitionIntern(TopDef, term_SecondArgument(Def), Polarity, FoundPred);
    }
    return FALSE;
  }
  
  /* Equivalence */
  if (symbol_Equal(term_TopSymbol(Def),fol_Equiv()) && (Polarity==1)) {
    /* Check if equivalence itself is in correct form */
    TERM defpredicate;

    defpredicate = cnf_IsDefinition(Def);
    if (defpredicate != (TERM) NULL) {
      LIST predicate_vars, l, defpath;
      BOOL allquantifierfound;
      TERM super;
      int pol;
      /* Check if predicate occurs several times in TopDef */
      /* if (cnf_PredicateOccurrences(TopDef, term_TopSymbol(defpredicate)) > 1) {}
	 puts("\n Predicate occurs more than once.");
	 return FALSE; */


      /* Now make sure that the variables of the predicate are       */
      /* all--quantified and not in the scope of an exist quantifier */
      /*      predicate_vars = list_Copy(term_ArgumentList(defpredicate)); */
      predicate_vars = term_ListOfVariables(defpredicate);
      predicate_vars = term_DeleteDuplicatesFromList(predicate_vars);

      /* So far (going bottom--up) no all-quantifier was found for */
      /* a variable of the predicates' arguments */
      allquantifierfound = FALSE;
      
      /* Build defpath here by going bottom up */
      /* At first, list of superterms on path is top down */
      defpath = list_Nil();
      super = Def;
      while (super != (TERM) NULL) {
	defpath = list_Cons(super, defpath);
	super = term_Superterm(super);
      }
      /* No go top down and add polarities */
      pol = 1;
      for (l=defpath; !list_Empty(l); l=list_Cdr(l)) {
	list_Rplaca(l, list_PairCreate((TERM) list_Car(l), (LIST) pol));
	if (symbol_Equal(term_TopSymbol((TERM) list_Car(l)), fol_Not()))
	  pol = -pol;
	else {
	  if (symbol_Equal(term_TopSymbol((TERM) list_Car(l)), fol_Implies()) &&
	      (term_FirstArgument((TERM) list_Car(l)) == (TERM) list_Car(list_Cdr(l))))
	    pol = -pol;
	  else 
	    if (symbol_Equal(term_TopSymbol((TERM) list_Car(l)), fol_Equiv()))
	      pol = 0;
	}
      }
      /* <defpath> is now a list of pairs (term, polarity) */
      for (l=defpath; !list_Empty(l) && !list_Empty(predicate_vars); l=list_Cdr(l)) {
	LIST pair;
	TERM t;
	int p;
	/* Pair Term t / Polarity p */
	pair = (LIST) list_Car(l);
	t = (TERM) list_PairFirst(pair);
	p = (int) list_PairSecond(pair);

	if (fol_IsQuantifier(term_TopSymbol(t))) {
	  
	  /* Variables of the predicate that are universally quantified are no problem */
	  if ((symbol_Equal(term_TopSymbol(t), fol_All()) && (p==1)) ||
	      (symbol_Equal(term_TopSymbol(t), fol_Exist()) && (p==-1))) {
	    LIST scan;
	    allquantifierfound = TRUE;
	    for (scan=fol_QuantifierVariables(t); !list_Empty(scan); scan=list_Cdr(scan))
	      predicate_vars = list_DeleteElement(predicate_vars,(TERM) list_Car(scan),
						  (BOOL (*)(POINTER,POINTER))term_Equal);
	  }
	  else {
	    /* Check if allquantified variables of the predicate are in scope of an exist--quantifier */
	    /* We already found an all quantified variable */
	    if (allquantifierfound) {
	      list_Delete(predicate_vars);
	      list_DeletePairList(defpath);
	      return FALSE;
	    }
	    else {
	      LIST scan;
	      /* Check if a variable of the predicate is exist--quantified */
	      for (scan=fol_QuantifierVariables(t); !list_Empty(scan); scan=list_Cdr(scan)) {
		if (term_ListContainsTerm(predicate_vars, list_Car(scan))) {
		  list_Delete(predicate_vars);
		  list_DeletePairList(defpath);
		  return FALSE;
		}
	      }
	    }
	  }
	}
      }
      
#ifdef CHECK
      if (!list_Empty(predicate_vars)) {
	list_Delete(predicate_vars);
	misc_StartErrorReport();
	misc_ErrorReport("\n In cnf_ContainsDefinitionIntern: Definition has free variables.\n");
	misc_FinishErrorReport();
      }
#endif
      list_DeletePairList(defpath);
      *FoundPred = defpredicate;
      return TRUE;
    }
  }
  
  return FALSE;
}


BOOL cnf_ContainsDefinition(TERM Def, TERM* FoundPred)
/**********************************************************
  INPUT:   A term Def which is searched for a definition of a predicate.
           A pointer to a term into which the predicate of the definition
	   is stored if it is found.
  RETURNS: TRUE if Def contains a definition that can be converted to
           standard form.
***********************************************************/
{
  BOOL result;
#ifdef CHECK
  fol_CheckFatherLinks(Def);
#endif
  result = cnf_ContainsDefinitionIntern(Def, Def, 1, FoundPred);
#ifdef CHECK
  fol_CheckFatherLinks(Def);
#endif
  return result;
}


static TERM cnf_IsDefinition(TERM Def)
/**********************************************************
 INPUT:   A term Def.
 RETURNS: The Def term where the arguments of the equivalence are exchanged
          iff the first one is not a predicate.
**********************************************************/
{
  LIST l,freevars, predicatevars;

#ifdef CHECK
  if (Def == NULL) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cnf_IsDefinition: Empty formula.\n");
    misc_FinishErrorReport();
  }
  if (!symbol_Equal(term_TopSymbol(Def),fol_Equiv())) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cnf_IsDefinition: Formula is no equivalence.\n");
    misc_FinishErrorReport();
  }
#endif
  
  /* If the predicate is the second argument of the equivalence, exchange them */
  if (!symbol_IsPredicate(term_TopSymbol(term_FirstArgument(Def)))) {
    TERM arg1;
    arg1 = term_FirstArgument(Def);
    term_RplacFirstArgument(Def, term_SecondArgument(Def));
    term_RplacSecondArgument(Def, arg1);
  }


  /* Check if the first argument is a predicate */
  if (!symbol_IsPredicate(term_TopSymbol(term_FirstArgument(Def)))) 
    return NULL;

  /* Check if first argument is a predicate and not fol_Equality */
  /*  if (!symbol_IsPredicate(term_TopSymbol(term_FirstArgument(Def)))
      || symbol_Equal(term_TopSymbol(term_FirstArgument(Def)), fol_Equality()))) {
      return NULL;
      }*/


  /* The free variables of the non-predicate term must occur in the predicate term */
  
  freevars = fol_FreeVariables(term_SecondArgument(Def));
  freevars = term_DeleteDuplicatesFromList(freevars);
  predicatevars = term_ListOfVariables(term_FirstArgument(Def));
  predicatevars = term_DeleteDuplicatesFromList(predicatevars);

  for (l=predicatevars; !list_Empty(l); l=list_Cdr(l))
    freevars = list_DeleteElement(freevars, list_Car(l),
				  (BOOL (*)(POINTER,POINTER))term_Equal);

  if (!list_Empty(freevars)) {
    list_Delete(freevars);
    list_Delete(predicatevars);
    return NULL;
  }

  list_Delete(predicatevars);
  return term_FirstArgument(Def);
}


static BOOL cnf_ContainsPredicateIntern(TERM Target, SYMBOL Predicate, 
					int Polarity, TERM* TargetPredicate,
					TERM* ToTopLevel, LIST* TargetVars,
					LIST* VarsForTopLevel)
/**********************************************************
  INPUT:   A term (sub--) Target
           A symbol Predicate which is searched in the target term.
           The polarity of the subterm.
           A pointer to the term TargetPredicate into which the found
	   predicate term is stored.
           A pointer to the list TargetVars into which the variables found
	   in the predicates' arguments are stored.
           A pointer to a list VarsForTopLevel into which all variables are
	   stored that are all--quantified and can be moved to top level.

  RETURNS: TRUE if Formula contains the predicate for which a definition
           was found.
********************************************************/
{
  /* AND / OR */
  /* In these cases the predicate (if it exists) can not be moved to a higher level */

  if ((symbol_Equal(term_TopSymbol(Target),fol_And()) && Polarity == 1) ||
      (symbol_Equal(term_TopSymbol(Target),fol_Or()) && Polarity == -1) ||
      (symbol_Equal(term_TopSymbol(Target),fol_Implies()) && Polarity != 1) ||
      symbol_Equal(term_TopSymbol(Target), fol_Equiv())) {
    TERM s;
    LIST l;
    /* Try to find Predicate in Target */
    s = term_FindSubterm(Target, Predicate);
    if (s == NULL)
      return FALSE;
    
    /* Store variables found in the predicates arguments */
    for (l=term_ArgumentList(s); !list_Empty(l); l = list_Cdr(l))
      *TargetVars = list_Nconc(fol_FreeVariables((TERM) list_Car(l)), *TargetVars);
    *TargetVars = term_DeleteDuplicatesFromList(*TargetVars);
    /* Keep found predicate */
    *TargetPredicate = s;
    *ToTopLevel = Target;
    return TRUE;
  }
  
  /* AND / OR continued */
  if (symbol_Equal(term_TopSymbol(Target),fol_And()) || symbol_Equal(term_TopSymbol(Target),fol_Or())) {
    /* The polarity is ok here */
    LIST l;
    for (l=term_ArgumentList(Target); !list_Empty(l); l = list_Cdr(l))
      if (cnf_ContainsPredicateIntern((TERM) list_Car(l), Predicate, Polarity,
				      TargetPredicate, ToTopLevel, TargetVars,
				      VarsForTopLevel))
	return TRUE;
    return FALSE;
  }

  /* Quantifiers */
  if (fol_IsQuantifier(term_TopSymbol(Target))) {
    if (cnf_ContainsPredicateIntern(term_SecondArgument(Target), Predicate,
				    Polarity, TargetPredicate, ToTopLevel,
				    TargetVars, VarsForTopLevel)) {
      /* Quantifiers for free variables of the predicate should be moved
	 to top level to make the proof easier */
      if ((symbol_Equal(term_TopSymbol(Target), fol_All()) && Polarity == 1) ||
	  (symbol_Equal(term_TopSymbol(Target), fol_Exist()) && Polarity == -1)) {
	LIST l;
	/* Check for all variables found in the predicates arguments */
	for (l = *TargetVars; !list_Empty(l); l=list_Cdr(l)) {
	  if (term_ListContainsTerm(fol_QuantifierVariables(Target),list_Car(l)))
	    *VarsForTopLevel = list_Cons(list_Car(l), *VarsForTopLevel);
	}
      }
      return TRUE;
    }
    return FALSE;
  }

  /* Negation */
  if (symbol_Equal(term_TopSymbol(Target),fol_Not()))
    return cnf_ContainsPredicateIntern(term_FirstArgument(Target), Predicate,
				       -Polarity, TargetPredicate, ToTopLevel,
				       TargetVars, VarsForTopLevel);
  /* Implication */
  if (symbol_Equal(term_TopSymbol(Target),fol_Implies())) {
    /* In this case the predicate (if it exists) can be moved to a higher level */
    if (cnf_ContainsPredicateIntern(term_FirstArgument(Target), Predicate,
				    -Polarity, TargetPredicate, ToTopLevel,
				    TargetVars, VarsForTopLevel))
      return TRUE;
    return cnf_ContainsPredicateIntern(term_SecondArgument(Target), Predicate,
				       Polarity, TargetPredicate, ToTopLevel,
				       TargetVars, VarsForTopLevel);
  }

  /* Found the predicate */
  if (symbol_Equal(term_TopSymbol(Target), Predicate)) {
    LIST l;
    for (l = term_ArgumentList(Target); !list_Empty(l); l = list_Cdr(l))
      *TargetVars = list_Nconc(fol_FreeVariables((TERM) list_Car(l)), *TargetVars);
    *TargetVars = term_DeleteDuplicatesFromList(*TargetVars);
    
    *TargetPredicate = Target;
    *ToTopLevel      = Target;
    return TRUE;
  }
  
  /* In all other cases the predicate was not found */
  return FALSE;
}  

  
BOOL cnf_ContainsPredicate(TERM Target, SYMBOL Predicate,
			   TERM* TargetPredicate, TERM* ToTopLevel,
			   LIST* TargetVars, LIST* VarsForTopLevel)
/**********************************************************
  INPUT:   A term Target without implications.
           A symbol Predicate which is searched in the target term.
           A pointer to the predicate found in TargetTerm is recorded.
           A pointer to the term TargetPredicate into which the found
	   predicate term is stored.
           A pointer to the list TargetVars into which the variables
	   found in the predicates' arguments are stored.
           A pointer to a list VarsForTopLevel into which all variables
	   are stored that are all--quantified and can be moved to top level.
  RETURNS: TRUE if Formula contains the predicate for which a definition
           was found.
********************************************************/
{
  BOOL result;
#ifdef CHECK
  fol_CheckFatherLinks(Target);
#endif
  result = cnf_ContainsPredicateIntern(Target, Predicate, 1, TargetPredicate,
				       ToTopLevel, TargetVars, VarsForTopLevel);
#ifdef CHECK
  fol_CheckFatherLinks(Target);
#endif
  return result;
}


static int cnf_PredicateOccurrences(TERM Term, SYMBOL P)
/****************************************************
  INPUT:   A term and a predicate symbol.
  RETURNS: The number of occurrences of the predicate symbol in Term
**************************************************/			       
{
  /* Quantifiers */
  if (fol_IsQuantifier(term_TopSymbol(Term)))
    return cnf_PredicateOccurrences(term_SecondArgument(Term), P);

  /* Junctors and NOT */
  if (fol_IsJunctor(term_TopSymbol(Term)) ||
      symbol_Equal(term_TopSymbol(Term),fol_Not())) {
    LIST scan;
    int count;
    count = 0;
    for (scan=term_ArgumentList(Term); !list_Empty(scan); scan=list_Cdr(scan)) {
      count += cnf_PredicateOccurrences(list_Car(scan), P);
      /* Only the cases count==1 and count>1 are important */
      if (count > 1)
	return count;
    }
    return count;
  }
  
  if (symbol_Equal(term_TopSymbol(Term), P))
    return 1;
  return 0;
} 
  

static TERM cnf_NegationNormalFormulaPath(TERM Term, TERM PredicateTerm)
/**********************************************************
  INPUT:   A term and a predicate term which is a subterm of term
  RETURNS: The negation normal form of the term along the path.
  CAUTION: The term is destructively changed.
           This works only if the superterm member of Term and its subterms 
	   are set.
********************************************************/
{
  TERM   subterm, termL, term1;
  LIST   scan;
  SYMBOL symbol;
  BOOL   set;

  term1 = Term;
  while (term1 != NULL) {
    set = FALSE;
    if (symbol_Equal(term_TopSymbol(term1),fol_Not())) {	    
      subterm = term_FirstArgument(term1);
      if (symbol_Equal(term_TopSymbol(subterm),fol_Not())) {
	LIST l;
	term_RplacTop(term1,term_TopSymbol(term_FirstArgument(subterm)));
	list_Delete(term_ArgumentList(term1));
	term_RplacArgumentList(term1,term_ArgumentList(term_FirstArgument(subterm)));
	term_Free(term_FirstArgument(subterm));
	list_Delete(term_ArgumentList(subterm));
	term_Free(subterm);
	/* Set superterm member to new superterm */
	for (l=term_ArgumentList(term1); !list_Empty(l); l=list_Cdr(l))
	  term_RplacSuperterm(list_Car(l), term1);
	/* term1 weiter betrachten */
	set = TRUE;
      }
      else {
	if (fol_IsQuantifier(term_TopSymbol(subterm))) {
	  LIST l;
	  symbol = (SYMBOL)cnf_GetDualSymbol(term_TopSymbol(subterm));
	  termL  = term_CreateAddFather(fol_Not(),
					list_List(term_SecondArgument(subterm)));
	  list_RplacSecond(term_ArgumentList(subterm), termL);
	  term_RplacSuperterm(termL, subterm);
	  term_RplacTop(term1,symbol);
	  list_Delete(term_ArgumentList(term1));
	  term_RplacArgumentList(term1, term_ArgumentList(subterm));
	  for (l=term_ArgumentList(term1); !list_Empty(l); l = list_Cdr(l))
	    term_RplacSuperterm(list_Car(l), term1);
	  term_RplacArgumentList(subterm, list_Nil());
	  term_Delete(subterm);
	  term1 = termL;
	  /* Next term to check is not(subterm) */
	  set = TRUE;
	} 
	else {
	  if (symbol_Equal(term_TopSymbol(subterm),fol_Or()) || 
	      (symbol_Equal(term_TopSymbol(subterm),fol_And()))) {
	    LIST l;
	    symbol = (SYMBOL)cnf_GetDualSymbol(term_TopSymbol(subterm));
	    for (scan = term_ArgumentList(subterm); !list_Empty(scan);
		 scan = list_Cdr(scan)) {
	      TERM new;
	      termL = list_Car(scan);
	      new = term_CreateAddFather(fol_Not(),list_List(termL));
	      list_Rplaca(scan, new);
	      term_RplacSuperterm(new, subterm);
	    }
	    term_RplacTop(term1,symbol);
	    list_Delete(term_ArgumentList(term1));
	    term_RplacArgumentList(term1,term_ArgumentList(subterm));
	    for (l = term_ArgumentList(term1); !list_Empty(l); l=list_Cdr(l))
	      term_RplacSuperterm(list_Car(l), term1);
	    term_RplacArgumentList(subterm, list_Nil());
	    term_Delete(subterm);
	  }
	}
      }
    }
    if (!set) {
      if (!list_Empty(term_ArgumentList(term1)))
	for (scan=term_ArgumentList(term1);!list_Empty(scan);scan=list_Cdr(scan))
	  if (term_HasProperSuperterm(PredicateTerm, list_Car(scan))) {
	    term1 = list_Car(scan);
	    set = TRUE;
	    break;
	  }
      if (!set)
	term1 = NULL;
    }
  }
  return Term;
}


TERM cnf_ApplyDefinitionOnce(TERM Predicate, TERM Formula, TERM TargetTerm,
			     TERM TargetPredicate, FLAGSTORE Flags)
/*********************************************************
  INPUT:   A term Predicate which is a predicate found in a definition.
           A term Formula which is a term equivalent to the predicate.
           A term TargetTerm in which one occurrence of the predicate may be 
           replaced by the Formula.
           A term TargetPredicate which is the subterm of the TargetTerm
           to be replaced.
	   A flag store.
  RETURNS: The changed TargetTerm.
*************************************************************/
{
  SYMBOL maxvar, maxvar_temp;
  LIST bound, scan;
  BOOL success;
  
  /* Init varcounter */
  maxvar = term_MaxVar(TargetTerm);
  maxvar_temp = term_MaxVar(Formula);
  if (maxvar_temp > maxvar)
    maxvar = maxvar_temp;
  symbol_SetStandardVarCounter(maxvar);

  /* Find bound variables in formula for renaming them */
  bound = fol_BoundVariables(Formula);
  for (scan=bound; !list_Empty(scan); scan=list_Cdr(scan)) {
    /* Bound variable in definition is already used in term */
    if (term_ContainsSymbol(TargetTerm, term_TopSymbol(list_Car(scan))))
      term_ExchangeVariable(Formula, term_TopSymbol(list_Car(scan)),
			    symbol_CreateStandardVariable());
  }
  list_Delete(bound);
  TargetTerm = cnf_ApplyDefinitionInternOnce(Predicate, Formula, TargetTerm, 
					     TargetPredicate,&success);
  if (flag_GetFlagValue(Flags, flag_PAPPLYDEFS)) {
    if (success) {
      fputs("\nTarget after applying def:\n", stdout);
      fol_PrettyPrint(TargetTerm);
      puts("\n");
    }
  }
  
  return TargetTerm;
}


static TERM cnf_ApplyDefinitionInternOnce(TERM Predicate, TERM Formula, 
					  TERM TargetTerm, TERM TargetPredicate,
					  BOOL* Success)
/**********************************************************
  INPUT:   A term Predicate which is equivalence to
           Formula and Term
  RETURNS: The term in which all occurrences of P(..) are 
           replaced by Formula modulo the proper bindings
  CAUTION: Term is destructively changed!
***********************************************************/
{
  /* Quantifiers */
  if (fol_IsQuantifier(term_TopSymbol(TargetTerm))) {
    term_RplacSecondArgument(TargetTerm, 
      cnf_ApplyDefinitionInternOnce(Predicate, Formula, 
				    term_SecondArgument(TargetTerm),
				    TargetPredicate, Success));
    term_RplacSuperterm(term_SecondArgument(TargetTerm), TargetTerm);
    return TargetTerm;
  }

  /* Junctors and NOT */
  if (fol_IsJunctor(term_TopSymbol(TargetTerm)) ||
      symbol_Equal(term_TopSymbol(TargetTerm),fol_Not())) {
    LIST scan;
    for (scan=term_ArgumentList(TargetTerm); !list_Empty(scan); scan=list_Cdr(scan)) {
      list_Rplaca(scan, cnf_ApplyDefinitionInternOnce(Predicate, Formula, 
						      list_Car(scan), 
						      TargetPredicate, Success));
      term_RplacSuperterm((TERM) list_Car(scan), TargetTerm);
    }
    return TargetTerm;
  }
  
  if (symbol_Equal(term_TopSymbol(TargetTerm), term_TopSymbol(Predicate))) {
    if (TargetTerm == TargetPredicate) {
      TERM result;
      result = Formula;
      cnf_RplacVar(result, term_ArgumentList(Predicate), 
		   term_ArgumentList(TargetTerm));
      term_AddFatherLinks(result);
      term_Delete(TargetTerm);
      *Success = TRUE;
      return result;
    }
  }
  
  return TargetTerm;
} 


static TERM cnf_RemoveEquivImplFromFormula(TERM term)
/**********************************************************
  INPUT:   A term.
  RETURNS: The term  with replaced implications and equivalences.
  CAUTION: The term is destructively changed.
********************************************************/
{
  TERM term1,termL,termR,termLneg,termRneg;
  LIST scan;
  int  bottom,pol;
  
  bottom = vec_ActMax();
  vec_Push(term);

  while (bottom != vec_ActMax()) {
    term1 = (TERM)vec_PopResult();
    if (symbol_Equal(term_TopSymbol(term1),fol_Implies())) {
      term_RplacTop(term1, fol_Or());
      list_Rplaca(term_ArgumentList(term1),
		  term_Create(fol_Not(), list_List(list_Car(term_ArgumentList(term1)))));
    }else
      if (symbol_Equal(term_TopSymbol(term1),fol_Equiv())) {
	pol      = cnf_GetFormulaPolarity(term,term1);
	termL    = (TERM)list_Car(term_ArgumentList(term1));
	termR    = (TERM)list_Second(term_ArgumentList(term1));
	termLneg = term_Create(fol_Not(),list_List(term_Copy(termL)));
	termRneg = term_Create(fol_Not(),list_List(term_Copy(termR)));
	if (pol == 1 || pol == 0) {
	  term_RplacTop(term1, fol_And());
	  list_Rplaca(term_ArgumentList(term1), term_Create(fol_Or(),list_Cons(termLneg,list_List(termR))));
	  list_RplacSecond(term_ArgumentList(term1),term_Create(fol_Or(),list_Cons(termRneg,list_List(termL))));
	}else
	  if (pol == -1) {
	    term_RplacTop(term1, fol_Or());
	    list_Rplaca(term_ArgumentList(term1), term_Create(fol_And(),list_Cons(termLneg,list_List(termRneg))));
	    list_RplacSecond(term_ArgumentList(term1), term_Create(fol_And(),list_Cons(termL,list_List(termR))));
	  }
      }  
    if (!list_Empty(term_ArgumentList(term1)))
      for (scan=term_ArgumentList(term1);!list_Empty(scan);scan=list_Cdr(scan))
	vec_Push(list_Car(scan));
  }
  vec_SetMax(bottom);
  return term;
}


static TERM cnf_MovePredicateVariablesUp(TERM Term, TERM TargetPredicateTerm,
					 LIST VarsForTopLevel)
/**********************************************************
  INPUT:   A term and a predicate term which is a subterm of term
           an equivalence.
  RETURNS: The term where the free variables of the equivalence, which
           must be allquantified and not in the scope of an 
	   exist quantifier, are moved to toplevel.
  CAUTION: The term is destructively changed.
********************************************************/
{
  TERM term1;
  LIST scan;
  int  bottom;

  bottom = vec_ActMax();
  vec_Push(Term);
  
  while (bottom != vec_ActMax()) {
    term1 = (TERM)vec_PopResult();
    if (!list_Empty(term_ArgumentList(term1)))
      for (scan=term_ArgumentList(term1);!list_Empty(scan);scan=list_Cdr(scan)) {
	TERM arg;
	arg = (TERM) list_Car(scan);
	if (term_HasProperSuperterm(TargetPredicateTerm, arg)) {
	  if (symbol_Equal(term_TopSymbol(arg), fol_All())) {
	    LIST predicatevarscan, quantifiervars;
	    quantifiervars = fol_QuantifierVariables(arg);
	    for (predicatevarscan=VarsForTopLevel; !list_Empty(predicatevarscan);
		predicatevarscan = list_Cdr(predicatevarscan))
	      quantifiervars = list_DeleteElementFree(quantifiervars, 
						      (TERM) list_Car(predicatevarscan),
						      (BOOL (*)(POINTER,POINTER))term_Equal,
						      (void (*)(POINTER))term_Delete);
	    if (!list_Empty(quantifiervars))
	      term_RplacArgumentList(term_FirstArgument(arg), quantifiervars);
	    else {
	      TERM subterm;
	      subterm = term_SecondArgument(arg);
	      term_Free(term_FirstArgument(arg));
	      list_Delete(term_ArgumentList(arg));
	      term_Free(arg);
	      list_Rplaca(scan, subterm);
	      term_RplacSuperterm(subterm, term1);
	    }
	  }
	  vec_Push((TERM) list_Car(scan));
	}
      }
  }
  
  for (scan=VarsForTopLevel; !list_Empty(scan); scan = list_Cdr(scan))
    list_Rplaca(scan, term_Copy((TERM) list_Car(scan)));
  if (symbol_Equal(term_TopSymbol(Term), fol_All())) {
    LIST vars;
    vars = fol_QuantifierVariables(Term);
    vars = list_Nconc(vars, list_Copy(VarsForTopLevel));
    vars = term_DestroyDuplicatesInList(vars);
    term_RplacArgumentList(term_FirstArgument(Term), vars);
  }
  else {
    TERM newtop;
    newtop = fol_CreateQuantifier(fol_All(), list_Copy(VarsForTopLevel), list_List(Term));
    term_RplacSuperterm(Term, newtop);
    Term = newtop;
  }
  vec_SetMax(bottom);
  return Term;
}


static TERM cnf_RemoveImplFromFormulaPath(TERM Term, TERM PredicateTerm)
/**********************************************************
  INPUT:   A term and a predicate term which is a subterm of term
  RETURNS: The term where implications along the path to PredicateTerm 
           are replaced.
  CAUTION: The term is destructively changed.
           This works only if the superterm member of Term and its 
	   subterms are set.
********************************************************/
{
  TERM term1;
  LIST scan;
  int  bottom;
  
  bottom = vec_ActMax();
  vec_Push(Term);
  
  while (bottom != vec_ActMax()) {
    term1 = (TERM)vec_PopResult();
    if (term_HasProperSuperterm(PredicateTerm, term1)) {
      if (symbol_Equal(term_TopSymbol(term1),fol_Implies())) {
	TERM newterm;
	term_RplacTop(term1, fol_Or());
	newterm = term_CreateAddFather(fol_Not(), list_List(list_Car(term_ArgumentList(term1))));
	list_Rplaca(term_ArgumentList(term1), newterm);
	term_RplacSuperterm(newterm, term1);
      }
      
      if (!list_Empty(term_ArgumentList(term1)))
	for (scan=term_ArgumentList(term1);!list_Empty(scan);scan=list_Cdr(scan))
	  vec_Push(list_Car(scan));
    }
  }
  vec_SetMax(bottom);
  return Term;
}


static SYMBOL cnf_GetDualSymbol(SYMBOL symbol)
/********************************************************
  INPUT:   A predefined symbol.
  RETURNS: The dual symbol.
********************************************************/
{
  SYMBOL dual;

  dual = symbol;
  if (symbol_Equal(symbol,fol_All()))
    dual = fol_Exist();
  else
    if (symbol_Equal(symbol,fol_Exist()))
      dual = fol_All();
    else
      if (symbol_Equal(symbol,fol_Or()))
	dual = fol_And();
      else
	if (symbol_Equal(symbol,fol_And()))
	  dual =  fol_Or();
  return dual;
}


TERM cnf_NegationNormalFormula(TERM term)
/********************************************************
  INPUT:   A term.
  RETURNS: The negation normal form of the term.
  CAUTION: The term is destructively changed.
********************************************************/
{
  TERM   term1,subterm,termL;
  LIST   scan;
  SYMBOL symbol;
  int    bottom;
  
  bottom = vec_ActMax();
  vec_Push(term);

  while (bottom != vec_ActMax()) {
    term1 = (TERM)vec_PopResult();
    if (symbol_Equal(term_TopSymbol(term1),fol_Not())) {	    
      subterm = (TERM)list_Car(term_ArgumentList(term1));
      if (symbol_Equal(term_TopSymbol(subterm),fol_Not())) {
	term_RplacTop(term1,term_TopSymbol(term_FirstArgument(subterm)));
	list_Delete(term_ArgumentList(term1));
	term_RplacArgumentList(term1,term_ArgumentList(term_FirstArgument(subterm)));
	term_Free(term_FirstArgument(subterm));
	list_Delete(term_ArgumentList(subterm));
	term_Free(subterm);
	vec_Push(term1);
      }else 
	if (fol_IsQuantifier(term_TopSymbol(subterm))) {
	  symbol = (SYMBOL)cnf_GetDualSymbol(term_TopSymbol(subterm));
	  termL  = term_Create(fol_Not(),
			       list_List(term_SecondArgument(subterm)));
	  list_RplacSecond(term_ArgumentList(subterm), termL);
	  term_RplacTop(term1,symbol);
	  list_Delete(term_ArgumentList(term1));
	  term_RplacArgumentList(term1,term_CopyTermList(term_ArgumentList(subterm)));
	  term_Delete(subterm);
	} else
	  if (symbol_Equal(term_TopSymbol(subterm),fol_Or()) || 
	      symbol_Equal(term_TopSymbol(subterm),fol_And())) {
	    symbol = (SYMBOL)cnf_GetDualSymbol(term_TopSymbol(subterm));
	    for (scan = term_ArgumentList(subterm);
		 !list_Empty(scan);
		 scan = list_Cdr(scan)) {
	      termL = (TERM)list_Car(scan);
	      list_Rplaca(scan, term_Create(fol_Not(),list_List(termL)));
	    }
	    term_RplacTop(term1,symbol);
	    list_Delete(term_ArgumentList(term1));
	    term_RplacArgumentList(term1,term_CopyTermList(term_ArgumentList(subterm)));
	    term_Delete(subterm); 
	  }
    }
    if (!list_Empty(term_ArgumentList(term1)))
      for (scan=term_ArgumentList(term1);!list_Empty(scan);scan=list_Cdr(scan))
	vec_Push(list_Car(scan));
  }
  vec_SetMax(bottom);
  return term;
}


static TERM cnf_QuantMakeOneVar(TERM term)
/**************************************************************
  INPUT:   A term.
  RETURNS: The term where all quantifiers quantify over only one variable.
  CAUTION: The term is destructively changed.
***************************************************************/
{
  TERM   term1,termL;
  SYMBOL quantor;
  LIST   scan,varlist;
  int    bottom;
  
  bottom = vec_ActMax();
  vec_Push(term);       

  while (bottom != vec_ActMax()) {
    term1 = (TERM)vec_PopResult();
    if (fol_IsQuantifier(term_TopSymbol(term1))) {
      quantor = term_TopSymbol(term1);
      if (list_Length(term_ArgumentList(term_FirstArgument(term1))) > 1) {
	varlist =
	  list_Copy(list_Cdr(term_ArgumentList(term_FirstArgument(term1))));
	for (scan=varlist;!list_Empty(scan);scan=list_Cdr(scan)) {
	  termL = term_SecondArgument(term1);
	  term_RplacSecondArgument(term1, fol_CreateQuantifier(quantor,list_List(list_Car(scan)),list_List(termL)));
	}
	for (scan=varlist;!list_Empty(scan);scan=list_Cdr(scan)) {
	  term_RplacArgumentList(term_FirstArgument(term1), 
				 list_PointerDeleteElement(term_ArgumentList(term_FirstArgument(term1)),list_Car(scan)));
	}
	list_Delete(varlist);
      }
    }
    if (!list_Empty(term_ArgumentList(term1)))
      for (scan=term_ArgumentList(term1);!list_Empty(scan);scan=list_Cdr(scan))
	vec_Push(list_Car(scan));
  }
  vec_SetMax(bottom);
  return term;
}


static LIST cnf_GetSymbolList(LIST varlist)
/**************************************************************
  INPUT:   A list of variables
  RETURNS: The list of the symbols of the variables.
***************************************************************/
{
  LIST scan,result;

  result = list_Nil();
  for (scan=varlist;!list_Empty(scan);scan=list_Cdr(scan))
    result = list_Cons((POINTER)term_TopSymbol((TERM)list_Car(scan)),result);

  return result;
}


static BOOL cnf_TopIsAnd(LIST termlist)
/**************************************************************
  INPUT:   A list of terms.
  RETURNS: True if one term in termlist is a conjunction.
***************************************************************/
{
  LIST scan;

  for (scan=termlist;!list_Empty(scan);scan=list_Cdr(scan))
    if (term_TopSymbol(list_Car(scan)) == fol_And())
      return TRUE;
  return FALSE;
}


static TERM cnf_MakeOneOr(TERM term)
/**************************************************************
  INPUT:   A term.
  RETURNS: Takes all arguments of an or together.
  CAUTION: The term is destructively changed.
***************************************************************/
{

  LIST   scan;

  if (symbol_Equal(term_TopSymbol(term),fol_Or())) {
    TERM   argterm;
    scan=term_ArgumentList(term);
    while (!list_Empty(scan)) {
      argterm = (TERM)list_Car(scan);
      cnf_MakeOneOr(argterm);
      if (symbol_Equal(term_TopSymbol(argterm),fol_Or())) {
	scan = list_Cdr(scan);
	term_RplacArgumentList(term,
			       list_Nconc(term_ArgumentList(argterm),list_PointerDeleteElement(term_ArgumentList(term),argterm)));
	term_Free(argterm);
      }
      else
	scan = list_Cdr(scan);
    }
  } else if (!symbol_IsPredicate(term_TopSymbol(term)))
    for (scan=term_ArgumentList(term);!list_Empty(scan);scan=list_Cdr(scan))
      cnf_MakeOneOr(list_Car(scan));
  
  return term;
}


static TERM cnf_MakeOneOrPredicate(TERM term)
/**************************************************************
  INPUT:   A term.
  RETURNS: Takes all predicates and negated predicates as arguments 
           of an or together.
  CAUTION: The term is destructively changed.
***************************************************************/
{

  LIST   scan,scan1,predlist;

  if (cnf_TopIsAnd(term_ArgumentList(term))) {
    
    for (scan1=term_ArgumentList(term);
	 !(list_Empty(scan1) || symbol_Equal(term_TopSymbol(list_Car(scan1)),fol_And()));
	 scan1=list_Cdr(scan1));

    if (!list_Empty(scan1)) {
      predlist = list_Nil();
      for (scan=scan1; !list_Empty(scan); scan=list_Cdr(scan)) {
	if (symbol_IsPredicate(term_TopSymbol(list_Car(scan))) ||
	    fol_IsNegativeLiteral(list_Car(scan))) {
	  predlist = list_Cons(list_Car(scan),predlist);
	}
      }
      for (scan=predlist;!list_Empty(scan);scan=list_Cdr(scan))
	term_RplacArgumentList(term,
			       list_PointerDeleteElement(term_ArgumentList(term),list_Car(scan)));
      
      if (!list_Empty(predlist))
	term_RplacArgumentList(term, list_Nconc(predlist,term_ArgumentList(term)));
    }
  }
  return term;
}


static TERM cnf_MakeOneOrTerm(TERM term)
/**************************************************************
  INPUT:   A term.
  RETURNS: Takes all predicates as arguments of an or together.
  CAUTION: The term is destructively changed.
***************************************************************/
{
  return cnf_MakeOneOrPredicate(cnf_MakeOneOr(term));
}


static TERM cnf_MakeOneAnd(TERM term)
/**************************************************************
  INPUT:   A term.
  RETURNS: Takes all arguments of an and together.
  CAUTION: The term is destructively changed.
***************************************************************/
{
  LIST   scan;

  if (symbol_Equal(term_TopSymbol(term),fol_And())) {
    TERM   argterm;
    scan=term_ArgumentList(term);
    while (!list_Empty(scan)) {
      argterm = (TERM)list_Car(scan);
      cnf_MakeOneAnd(argterm);
      if (symbol_Equal(term_TopSymbol(argterm),fol_And())) {
	scan = list_Cdr(scan);
	term_RplacArgumentList(term,
			       list_Nconc(term_ArgumentList(argterm),list_PointerDeleteElement(term_ArgumentList(term),argterm)));
	term_Free(argterm);
      }
      else
	scan = list_Cdr(scan);
    }
  } else if (!symbol_IsPredicate(term_TopSymbol(term)))
    for (scan=term_ArgumentList(term);!list_Empty(scan);scan=list_Cdr(scan))
      cnf_MakeOneAnd(list_Car(scan));

  return term;
}


static TERM cnf_MakeOneAndPredicate(TERM term)
/**************************************************************
  INPUT:   A term.
  RETURNS: Takes all predicates as arguments of one or together.
  CAUTION: The term is destructively changed.
***************************************************************/
{
  LIST   scan,scan1,predlist;
  
  for (scan1=term_ArgumentList(term);
       !(list_Empty(scan1) || symbol_Equal(term_TopSymbol(list_Car(scan1)),fol_Or()));
       scan1=list_Cdr(scan1));
  
  if (!list_Empty(scan1)) {
    /* The car of scan1 points to a term with topsymbol 'or' */
    predlist = list_Nil();
    for (scan=scan1; !list_Empty(scan); scan=list_Cdr(scan)) {
      if (symbol_IsPredicate(term_TopSymbol(list_Car(scan))) &&
	  fol_IsNegativeLiteral(list_Car(scan))) {
	predlist = list_Cons(list_Car(scan),predlist);
      }
    }
    for (scan=predlist; !list_Empty(scan); scan=list_Cdr(scan))
      term_RplacArgumentList(term, list_PointerDeleteElement(term_ArgumentList(term),list_Car(scan)));
    
    if (!list_Empty(predlist))
      term_RplacArgumentList(term, list_Nconc(predlist,term_ArgumentList(term)));
  }
  return term;
}


static TERM cnf_MakeOneAndTerm(TERM term)
/**************************************************************
  INPUT:   A term.
  RETURNS: Takes all predicates as arguments of an or together.
  CAUTION: The term is destructively changed.
***************************************************************/
{
  return cnf_MakeOneAndPredicate(cnf_MakeOneAnd(term));
}


LIST cnf_ComputeLiteralLists(TERM Term)
/**********************************************************
  INPUT:   A term in negation normal form without quantifiers.
  RETURNS: The list of all literal lists corresponding to the
           CNF of Term.
***********************************************************/
{
  LIST   Scan, Scan1, Scan2, Help, Result, List1, List2, NewResult;
  SYMBOL Symbol;

  Symbol = term_TopSymbol(Term);
  Result = list_Nil();

  if (symbol_Equal(Symbol,fol_Or())) {
    Result = cnf_ComputeLiteralLists(list_Car(term_ArgumentList(Term)));
    for (Scan=list_Cdr(term_ArgumentList(Term));!list_Empty(Scan);Scan=list_Cdr(Scan)) {
      Help      = cnf_ComputeLiteralLists(list_Car(Scan));
      NewResult = list_Nil();
      for (Scan1=Help;!list_Empty(Scan1);Scan1=list_Cdr(Scan1))	    
	for (Scan2=Result;!list_Empty(Scan2);Scan2=list_Cdr(Scan2)) {
	  List1 = list_Car(Scan1);
	  List2 = list_Car(Scan2);
	  if (!list_Empty(list_Cdr(Scan2)))
	    List1 = term_CopyTermList(List1);
	  if (!list_Empty(list_Cdr(Scan1))) 
	    List2 = term_CopyTermList(List2);
	  NewResult = list_Cons(term_DestroyDuplicatesInList(list_Nconc(List1,List2)),
				NewResult);
	}
      list_Delete(Help);
      list_Delete(Result);
      Result = NewResult;
    }
    return Result;
  }

  if (symbol_Equal(Symbol,fol_And())) {
    Result = cnf_ComputeLiteralLists(list_Car(term_ArgumentList(Term)));
    for (Scan=list_Cdr(term_ArgumentList(Term));!list_Empty(Scan);Scan=list_Cdr(Scan)) {
      Result = list_Nconc(cnf_ComputeLiteralLists(list_Car(Scan)), Result);
    }
    return Result;
  }
  
  if (symbol_Equal(Symbol,fol_Not()) || symbol_IsPredicate(Symbol))
    return list_List(list_List(term_Copy(Term)));
  
    
  misc_StartErrorReport();
  misc_ErrorReport("\n In cnf_ComputeLiteralLists: Unexpected junctor in input Formula!\n");
  misc_FinishErrorReport();

  return Result;
}


static TERM cnf_DistributiveFormula(TERM Formula)
/**************************************************************
  INPUT:   A Formula in NNF which consists only of disjunctions and
           conjunctions.
  RETURNS: The Formula where the distributivity rule is exhaustively applied
           and all disjunctions and the top level conjunction are grouped.
  CAUTION: The Formula is destructively changed.
***************************************************************/
{
  TERM Result;
  LIST Scan, Lists;

  Lists = cnf_ComputeLiteralLists(Formula);
  
  for (Scan= Lists; !list_Empty(Scan); Scan=list_Cdr(Scan))
    list_Rplaca(Scan,term_Create(fol_Or(), list_Car(Scan)));

  Result = term_Create(fol_And(), Lists);
  term_Delete(Formula);

  return Result;
}



void cnf_FPrintClause(TERM term, FILE* file)
/**************************************************************
  INPUT:   A term and a file pointer.
  RETURNS: Nothing.
  EFFECT:  Print the term which contains only disjunctions to file.
           The disjunctions represent a clause.
***************************************************************/
{
    
  TERM   term1;
  LIST   scan;
  int    bottom;
  
  bottom = vec_ActMax();
  vec_Push(term);       

  while (bottom != vec_ActMax()) {
    term1 = (TERM)vec_PopResult();
    if (symbol_Equal(term_TopSymbol(term1),fol_Or())) {
      for (scan=term_ArgumentList(term1);!list_Empty(scan);scan=list_Cdr(scan))
	vec_Push(list_Car(scan));
    }else
      term_FPrint(file,term1);
  }
  fputs(".\n", file);
  vec_SetMax(bottom);
}


void cnf_FPrint(TERM term, FILE* file)
/**************************************************************
  INPUT:   A term and a file pointer.
  RETURNS: Nothing.
  EFFECT:  Print the term (in negation normal form)
           which contains only conjunctions of 
	   disjunctions to file. The conjunctions are interpreted 
	   to represent different clauses.
***************************************************************/
{
  TERM   term1;
  LIST   scan;
  int    bottom;
  
  bottom = vec_ActMax();
  vec_Push(term);       

  while (bottom != vec_ActMax()) {
    term1 = (TERM)vec_PopResult();
    if (symbol_Equal(term_TopSymbol(term1),fol_And())) {
      for (scan=term_ArgumentList(term1);!list_Empty(scan);scan=list_Cdr(scan))
	vec_Push(list_Car(scan));
    }else
      if (symbol_Equal(term_TopSymbol(term1),fol_Or()) ||
	  symbol_IsPredicate(term_TopSymbol(term1)) ||
	  symbol_Equal(term_TopSymbol(term1),fol_Not()))
	cnf_FPrintClause(term1,file);
  }
  vec_SetMax(bottom);
}


void cnf_StdoutPrint(TERM term)
/**************************************************************
  INPUT:   A term.
  RETURNS: Nothing.
  EFFECT:  Print the term (in negation normal form)
           which contains only conjunctions of 
	   disjunctions to standard out. The conjunctions are interpreted 
	   to represent different clauses.
***************************************************************/
{
  LIST termlist,scan,scan1;

  for (scan=term_ArgumentList(term); !list_Empty(scan); scan=list_Cdr(scan)) {
    termlist = list_Nil();
    if (!(symbol_IsPredicate(term_TopSymbol(list_Car(scan))) ||
	  fol_IsNegativeLiteral(list_Car(scan))))
      termlist = term_ArgumentList(list_Car(scan));
    
    if (!list_Empty(termlist)) {
      for (scan1=termlist;!list_Empty(scan1);scan1=list_Cdr(scan1))
	term_Print(list_Car(scan1));
      puts(".");
    }else{
      term_Print(list_Car(scan));
      puts(".");
    }
  }
}


void cnf_FilePrint(TERM term, FILE* file)
/**************************************************************
  INPUT:   A term and a file.
  RETURNS: Nothing.
  EFFECT:  Print the term (in negation normal form)
           which contains only conjunctions of 
	   disjunctions to file. The conjunctions are interpreted 
	   to represent different clauses.
***************************************************************/
{
  LIST termlist,scan,scan1;

  for (scan=term_ArgumentList(term); !list_Empty(scan); scan=list_Cdr(scan)) {
    termlist = list_Nil();
    if (!(symbol_IsPredicate(term_TopSymbol(list_Car(scan))) ||
	  fol_IsNegativeLiteral(list_Car(scan))))
      termlist = term_ArgumentList(list_Car(scan));
    
    if (!list_Empty(termlist)) {
      for (scan1=termlist;!list_Empty(scan1);scan1=list_Cdr(scan1))
	term_FPrint(file,list_Car(scan1));
      fputs(".\n", file);
    }else{
      term_FPrint(file,list_Car(scan));
      fputs(".\n", file);
    }
  }
  
}


void cnf_FilePrintPrefix(TERM term, FILE* file)
/**************************************************************
  INPUT:   A term and a file pointer.
  RETURNS: Nothing.
  EFFECT:  Prefix Print the term (in negation normal form)
           which contains only conjunctions of 
	   disjunctions to file. The conjunctions are interpreted 
	   to represent different clauses.
***************************************************************/
{
  LIST termlist,scan,scan1;

  for (scan=term_ArgumentList(term);!list_Empty(scan);scan=list_Cdr(scan)) {
    termlist = list_Nil();
    if (!(symbol_IsPredicate(term_TopSymbol(list_Car(scan))) ||
	  fol_IsNegativeLiteral(list_Car(scan))))
      termlist = term_ArgumentList(list_Car(scan));
    
    if (!list_Empty(termlist)) {
      for (scan1=termlist;!list_Empty(scan1);scan1=list_Cdr(scan1)) {
	term_FPrintPrefix(file,list_Car(scan1));
	if (!list_Empty(list_Cdr(scan1)))
	  fputs(" | ", file);
      }
      fputs(".\n", file);
    } else {
      term_FPrintPrefix(file,list_Car(scan));
      fputs(".\n", file);
    }
  }
}


static LIST cnf_SubsumeClauseList(LIST clauselist)
/**********************************************************
  INPUT:   A list of clauses.
  RETURNS: The list of clauses without subsumed clauses.
  CAUTION: The list is destructively changed.
***********************************************************/
{
  LIST     scan,result;
  st_INDEX stindex;
  CLAUSE   actclause;

  stindex = st_IndexCreate();
  result  = list_Nil();

  for (scan = clauselist; !list_Empty(scan); scan=list_Cdr(scan))
    res_InsertClauseIndex(list_Car(scan),stindex);

  for (scan=clauselist; !list_Empty(scan); scan=list_Cdr(scan)) {
    actclause     = list_Car(scan);
    res_DeleteClauseIndex(actclause,stindex);
    if (!res_BackSubWithLength(actclause,stindex)) {
      res_InsertClauseIndex(actclause,stindex);
      result = list_Cons(actclause,result);
    }
  }
  if (list_Length(result) != list_Length(clauselist)) {
    for (scan = result; !list_Empty(scan); scan=list_Cdr(scan))
      clauselist = list_PointerDeleteElement(clauselist,list_Car(scan));
    if (!list_Empty(result))
      clause_DeleteClauseList(clauselist);
  }else
    list_Delete(clauselist);
  st_IndexDelete(stindex);
  return result;
}


static LIST cnf_MakeClauseList(TERM term, BOOL Sorts, BOOL Conclause,
			       FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A term in cnf and two boolean values indicating
           whether sorts should be generated and whether the
	   generated clauses are Conclauses, a flag store and
	   a precedence.
  RETURNS: A list of clauses with respect to term. The terms 
           in the new clauses are the copied subterms from term.
  EFFECT:  The flag store and the precedence are not changed,
           but they're needed for creating clauses.
***************************************************************/
{
  LIST   termlist,scan,clauselist,newclauselist,delclauselist,condlist;
  CLAUSE clause;
  int    j;

  termlist   = list_Nil();
  clauselist = list_Nil();

  if (fol_IsTrue(term))
    return  clauselist;

  if (fol_IsNegativeLiteral(term) || symbol_IsPredicate(term_TopSymbol(term))) {
    termlist = list_List(term_Copy(term));
    clause = clause_CreateFromLiterals(termlist, Sorts, Conclause,TRUE,
				       Flags, Precedence);
    clauselist = list_Nconc(clauselist,list_List(clause));
    term_StartMinRenaming();
    term_Rename(clause_GetLiteralTerm(clause,0));
    list_Delete(termlist);
    return clauselist;
  }

  delclauselist = list_Nil();
  term          = cnf_MakeOneAndTerm(term);
  if (symbol_Equal(term_TopSymbol(term), fol_And())) {
    for (scan=term_ArgumentList(term); !list_Empty(scan); scan=list_Cdr(scan)) {
      list_Rplaca(scan, cnf_MakeOneOrTerm(list_Car(scan)));
      termlist = list_Nil();
      if (!(symbol_IsPredicate(term_TopSymbol(list_Car(scan))) ||
	    fol_IsNegativeLiteral(list_Car(scan)))) {
	termlist = term_CopyTermList(term_ArgumentList(list_Car(scan)));
	termlist = term_DestroyDuplicatesInList(termlist);
      } else
	termlist = list_List(term_Copy(list_Car(scan)));
  
      if (!list_Empty(termlist)) {
	clause = clause_CreateFromLiterals(termlist, Sorts, Conclause, TRUE,
					   Flags, Precedence);
	term_StartMinRenaming();
	for (j = 0; j < clause_Length(clause); j++)
	  term_Rename(clause_GetLiteralTerm(clause,j));
	clauselist = list_Cons(clause,clauselist);
	list_Delete(termlist);
      }
    }
  } else {
    /* Here the term is a disjunction, i.e. there is only one clause */
    term = cnf_MakeOneOrTerm(term);
    if (!(symbol_IsPredicate(term_TopSymbol(term)) ||
	  fol_IsNegativeLiteral(term))) {
      termlist = term_CopyTermList(term_ArgumentList(term));
      termlist = term_DestroyDuplicatesInList(termlist);
    } else
      termlist = list_List(term_Copy(term));
    
    if (!list_Empty(termlist)) {
      clause = clause_CreateFromLiterals(termlist, Sorts, Conclause, TRUE,
					 Flags, Precedence);
      term_StartMinRenaming();
      for (j = 0; j < clause_Length(clause); j++)
	term_Rename(clause_GetLiteralTerm(clause,j));
      clauselist = list_Cons(clause,clauselist);
      list_Delete(termlist);
    }
  }

  for (scan=clauselist; !list_Empty(scan); scan=list_Cdr(scan)) {
    condlist = cond_CondFast(list_Car(scan));
    if (!list_Empty(condlist))
      clause_DeleteLiterals(list_Car(scan), condlist, Flags, Precedence);
    list_Delete(condlist);
  }
  clauselist    = cnf_SubsumeClauseList(clauselist);
  newclauselist = list_Nil();
  while (!list_Empty(clauselist)) {
    clause = res_SelectLightestClause(clauselist);
    newclauselist = list_Nconc(newclauselist,list_List(clause));
    clauselist = list_PointerDeleteElement(clauselist,clause);
  }
  list_Delete(clauselist);
  for (scan=newclauselist; !list_Empty(scan); scan=list_Cdr(scan)) {
    if (res_HasTautology(list_Car(scan)))
      delclauselist = list_Cons(list_Car(scan),delclauselist);
  }
  for (scan=delclauselist; !list_Empty(scan); scan=list_Cdr(scan))
    newclauselist = list_PointerDeleteElement(newclauselist,list_Car(scan));
  clause_DeleteClauseList(delclauselist);
    
  return newclauselist;
}


TERM cnf_Flatten(TERM Term, SYMBOL Symbol)
/**************************************************************
  INPUT:   A <Term> and <Symbol> that is assumed to be associative.
  RETURNS: If the top symbol of <Term> is <Symbol> the <Term> is flattened
           as long as it contains further direct subterms starting with <Symbol>
  CAUTION: The term is destructively changed.
***************************************************************/
{
  LIST   Scan1,Scan2;

  if (symbol_Equal(term_TopSymbol(Term), Symbol)) {
    TERM   Argterm;
    Scan1 =term_ArgumentList(Term);
    while (!list_Empty(Scan1)) {
      Argterm = (TERM)list_Car(Scan1);
      Scan2   = list_Cdr(Scan1);
      if (symbol_Equal(term_TopSymbol(Argterm),Symbol)) {
	cnf_Flatten(Argterm,Symbol);
	list_NInsert(Scan1,list_Cdr(term_ArgumentList(Argterm)));   /* Be efficient ... */
	list_Rplaca(Scan1,list_Car(term_ArgumentList(Argterm)));
	list_Free(term_ArgumentList(Argterm));
	term_Free(Argterm);
      }
      Scan1  = Scan2;
    }
  }
  return Term;
}


static TERM cnf_FlattenPath(TERM Term, TERM PredicateTerm)
/**************************************************************
  INPUT:   A <Term> and <Symbol> that is assumed to be associative,
           and a predicate term which is a subterm of term
  RETURNS: If the top symbol of <Term> is <Symbol> the <Term> is flattened
           as long as it contains further direct subterms starting with <Symbol>
  CAUTION: The term is destructively changed.
***************************************************************/
{
  TERM   subterm;
  
  subterm = Term;
  while (symbol_Equal(term_TopSymbol(subterm), fol_All()))
    subterm = term_SecondArgument(subterm);

  if (symbol_Equal(term_TopSymbol(subterm), fol_Or())) {
    TERM Argterm;
    LIST scan1;
    scan1 = term_ArgumentList(subterm);
    while (!list_Empty(scan1)) {
      LIST scan2;
      Argterm = (TERM)list_Car(scan1);
      scan2   = list_Cdr(scan1);
      if (term_HasProperSuperterm(PredicateTerm, Argterm)) {
	if (symbol_Equal(term_TopSymbol(Argterm),fol_Or())) {
	  LIST l;
	  cnf_Flatten(Argterm,fol_Or());
	  for (l=term_ArgumentList(Argterm); !list_Empty(l); l=list_Cdr(l))
	    term_RplacSuperterm((TERM) list_Car(l), subterm);
	  list_NInsert(scan1,list_Cdr(term_ArgumentList(Argterm)));   /* Be efficient ... */
	  list_Rplaca(scan1,list_Car(term_ArgumentList(Argterm)));
	  list_Free(term_ArgumentList(Argterm));
	  term_Free(Argterm);
	}
      }
      scan1  = scan2;
    }
  }
  return Term;
}


static void cnf_DistrQuantorNoVarSub(TERM Term)
/**************************************************************
  INPUT:   A formula in negation normal form starting with a universal 
           (existential) quantifier and a disjunction (conjunction) as argument.
  EFFECT:  The Quantor is distributed if possible.
  CAUTION: The term is destructively changed.
***************************************************************/
{
  LIST   Variables,Subformulas,Scan1,Scan2,Rest;
  TERM   Subterm,Var,NewForm;
  SYMBOL Subtop,Top;

  Top       = term_TopSymbol(Term);
  Variables = list_Copy(fol_QuantifierVariables(Term));
  Subterm   = term_SecondArgument(Term);
  Subtop    = term_TopSymbol(Subterm);
  Subterm   = cnf_Flatten(Subterm,Subtop);

  for (Scan1=Variables;!list_Empty(Scan1);Scan1=list_Cdr(Scan1)) {
    Subformulas = list_Nil();
    Var         = (TERM)list_Car(Scan1);
    for (Scan2=term_ArgumentList(Subterm);!list_Empty(Scan2);Scan2=list_Cdr(Scan2))
      if (!fol_VarOccursFreely(Var,list_Car(Scan2)))
	Subformulas = list_Cons(list_Car(Scan2),Subformulas);
    if (!list_Empty(Subformulas)) {
      Rest     = list_NPointerDifference(term_ArgumentList(Subterm),Subformulas);
      if (list_Empty(list_Cdr(Rest))) { /* One subformula */
	if (symbol_Equal(Top,term_TopSymbol(list_Car(Rest)))) { /* Optimization: quantifier still exist */
	  NewForm = (TERM)list_Car(Rest);
	  term_RplacArgumentList(term_FirstArgument(NewForm),
				 list_Cons((POINTER)Var,fol_QuantifierVariables(NewForm)));
	  list_Delete(Rest);
	}
	else
	  NewForm = fol_CreateQuantifier(Top,list_List((POINTER)Var),Rest);
      }
      else
	NewForm = fol_CreateQuantifier(Top,list_List((POINTER)Var),list_List(term_Create(Subtop,Rest)));
      term_RplacArgumentList(Subterm,list_Cons(NewForm,Subformulas));
      term_RplacArgumentList(term_FirstArgument(Term),
			     list_PointerDeleteElement(fol_QuantifierVariables(Term),(POINTER)Var));
    } 
  }

  if (list_Empty(fol_QuantifierVariables(Term))) { /* All variables moved inside */
    term_Free(term_FirstArgument(Term));
    list_Delete(term_ArgumentList(Term));
    term_RplacTop(Term,Subtop);
    term_RplacArgumentList(Term,term_ArgumentList(Subterm));
    term_Free(Subterm);
  }
  list_Delete(Variables);
}


static TERM cnf_AntiPrenex(TERM Term)
/**************************************************************
  INPUT:   A formula in negation normal form.
  RETURNS: The term after application of anti-prenexing. Quantifiers
           are moved inside as long as possible.
  CAUTION: The term is destructively changed.
***************************************************************/
{
  LIST   Scan;
  SYMBOL Top;

  Top = term_TopSymbol(Term);

  if (fol_IsQuantifier(Top)) {
    TERM   Subterm,Actterm;
    SYMBOL DistrSymb,Subtop;          /* The junctor the respective quantifier distributes over */
    
    Subterm = term_SecondArgument(Term);
    Subtop  = term_TopSymbol(Subterm);

    if (!symbol_IsPredicate(Subtop) && 
	!symbol_Equal(Subtop,fol_Not())) { /* Formula in NNF: No Literals or Atoms */
      if (symbol_Equal(Top,fol_All()))
	DistrSymb = fol_And();
      else
	DistrSymb = fol_Or();
      if (fol_IsQuantifier(Subtop)) {
	cnf_AntiPrenex(Subterm);
	Subtop = term_TopSymbol(Subterm);
      }
      if (symbol_Equal(Subtop,DistrSymb)) {
	LIST Variables;	
	LIST NewVars;
	Variables = fol_QuantifierVariables(Term);
	Subterm   = cnf_Flatten(Subterm,DistrSymb);
	for (Scan=term_ArgumentList(Subterm);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
	  Actterm = (TERM)list_Car(Scan);
	  NewVars = list_NIntersect(fol_FreeVariables(Actterm),Variables,
				    (BOOL (*)(POINTER,POINTER))term_Equal);
	  if (!list_Empty(NewVars)) {
	    if (symbol_Equal(Top,term_TopSymbol(Actterm))) {        /* Quantor already there */
	      term_CopyTermsInList(NewVars);
	      term_RplacArgumentList(term_FirstArgument(Actterm),
				     list_Nconc(fol_QuantifierVariables(Actterm),
						NewVars));
	    }
	    else {
	      term_CopyTermsInList(NewVars);
	      list_Rplaca(Scan,fol_CreateQuantifier(Top, NewVars, list_List(Actterm)));
	    }
	  }
	}
	term_Delete(term_FirstArgument(Term));   /* Delete old variable list */
	list_Delete(term_ArgumentList(Term)); 
	term_RplacTop(Term,DistrSymb);
	term_RplacArgumentList(Term,term_ArgumentList(Subterm));
	term_Free(Subterm);
	for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan)) 
	  list_Rplaca(Scan,cnf_AntiPrenex(list_Car(Scan)));
      }
      else 
	if (!fol_IsQuantifier(Subtop)) {
	  cnf_DistrQuantorNoVarSub(Term);
	  for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
	    cnf_AntiPrenex(list_Car(Scan));
	}
    }
  }
  else
    if (!symbol_Equal(Top,fol_Not()) && !symbol_IsPredicate(Top))
      for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
	cnf_AntiPrenex(list_Car(Scan));

  return Term;
}


static void cnf_DistrQuantorNoVarSubPath(TERM Term, TERM PredicateTerm)
/**************************************************************
  INPUT:   A formula in negation normal form starting with a universal 
           (existential) quantifier and a disjunction (conjunction) as argument
	   and a predicate term which is a subterm of term.
  CAUTION: The term is destructively changed.
***************************************************************/
{
  LIST   Variables,Subformulas,Scan1,Scan2,Rest;
  TERM   Subterm,Var,NewForm;
  SYMBOL Subtop,Top;

  /*fputs("\nAN0:\t",stdout);term_Print(Term);*/

  Top       = term_TopSymbol(Term);
  Variables = list_Copy(fol_QuantifierVariables(Term));
  Subterm   = term_SecondArgument(Term);
  Subtop    = term_TopSymbol(Subterm);
  Subterm   = cnf_Flatten(Subterm,Subtop);

  /*fputs("\nAN1:\t",stdout);term_Print(Subterm);*/

  for (Scan1=Variables;!list_Empty(Scan1);Scan1=list_Cdr(Scan1)) {
    Subformulas = list_Nil();
    Var         = (TERM)list_Car(Scan1);
    /* Find subterms in which the variable does not occur freely */
    for (Scan2=term_ArgumentList(Subterm);!list_Empty(Scan2);Scan2=list_Cdr(Scan2))
      if (!fol_VarOccursFreely(Var,list_Car(Scan2)))
	Subformulas = list_Cons(list_Car(Scan2),Subformulas);
    if (!list_Empty(Subformulas)) {
      /* Rest is the list of those subterms where the variable does occur freely */
      Rest     = list_NPointerDifference(term_ArgumentList(Subterm),Subformulas);
      if (list_Empty(list_Cdr(Rest))) { /* One subformula */
	if (symbol_Equal(Top,term_TopSymbol(list_Car(Rest)))) { /* Optimization: quantifier still exist */
	  NewForm = (TERM)list_Car(Rest);
	  /* Move one variable down */
	  term_RplacArgumentList(term_FirstArgument(NewForm),
				 list_Cons((POINTER)Var,fol_QuantifierVariables(NewForm)));
	  list_Delete(Rest);
	}
	else {
	  NewForm = fol_CreateQuantifierAddFather(Top,list_List((POINTER)Var),
						  Rest);
	}
      }
      else {
	TERM t;
	t = term_CreateAddFather(Subtop,Rest);
	NewForm = fol_CreateQuantifierAddFather(Top,list_List((POINTER)Var),list_List(t));
      }
      if (term_HasProperSuperterm(PredicateTerm, NewForm))
	NewForm = cnf_AntiPrenexPath(NewForm, PredicateTerm);
      term_RplacArgumentList(Subterm,list_Cons(NewForm,Subformulas));
      term_RplacSuperterm(NewForm, Subterm);
      term_RplacArgumentList(term_FirstArgument(Term),
			     list_PointerDeleteElement(fol_QuantifierVariables(Term),(POINTER)Var));
    } 
  }

  if (list_Empty(fol_QuantifierVariables(Term))) { /* All variables moved inside */
    LIST l;
    term_Free(term_FirstArgument(Term));
    list_Delete(term_ArgumentList(Term));
    term_RplacTop(Term,Subtop);
    term_RplacArgumentList(Term,term_ArgumentList(Subterm));
    term_Free(Subterm);
    for (l=term_ArgumentList(Term); !list_Empty(l); l=list_Cdr(l))
      term_RplacSuperterm((TERM) list_Car(l), Term);
  }
  list_Delete(Variables);
}


static TERM cnf_AntiPrenexPath(TERM Term, TERM PredicateTerm)
/**************************************************************
  INPUT:   A formula in negation normal form and a predicate term
           which is a subterm of term.
  RETURNS: The term after application of anti-prenexing. Quantifiers
           are moved inside along the path as long as possible.
  CAUTION: The term is destructively changed.
***************************************************************/
{
  LIST   Scan;
  SYMBOL Top;

  Top = term_TopSymbol(Term);

  if (fol_IsQuantifier(Top)) {
    TERM   Subterm,Actterm;
    SYMBOL DistrSymb,Subtop;          /* The junctor the respective quantifier distributes over */
    
    Subterm = term_SecondArgument(Term);
    Subtop  = term_TopSymbol(Subterm);

    if (!symbol_Equal(Subtop,fol_Not()) && !symbol_IsPredicate(Subtop)) { /* No Literals or Atoms */
      if (symbol_Equal(Top,fol_All()))
	DistrSymb = fol_And();
      else
	DistrSymb = fol_Or();
      if (fol_IsQuantifier(Subtop)) {
	cnf_AntiPrenexPath(Subterm, PredicateTerm);
	Subtop = term_TopSymbol(Subterm);
      }
      if (symbol_Equal(Subtop,DistrSymb)) {
	LIST Variables;	
	LIST NewVars;
	Variables = fol_QuantifierVariables(Term);
	Subterm   = cnf_Flatten(Subterm,DistrSymb);
	term_AddFatherLinks(Subterm);
	/*
	  for (l=term_ArgumentList(Subterm); !list_Empty(l); l=list_Cdr(l))
	  term_RplacSuperterm((TERM) list_Car(l), Subterm);
	*/
	for (Scan=term_ArgumentList(Subterm);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
	  Actterm = (TERM)list_Car(Scan);
	  NewVars = list_NIntersect(fol_FreeVariables(Actterm),Variables,
				    (BOOL (*)(POINTER,POINTER))term_Equal);
	  if (!list_Empty(NewVars)) {
	    if (symbol_Equal(Top,term_TopSymbol(Actterm))) {         /* Quantor already there */
	      term_CopyTermsInList(NewVars);
	      term_RplacArgumentList(term_FirstArgument(Actterm),
				     list_Nconc(fol_QuantifierVariables(Actterm), NewVars));
	    }
	    else {
	      term_CopyTermsInList(NewVars);
	      list_Rplaca(Scan,fol_CreateQuantifierAddFather(Top, NewVars, list_List(Actterm)));
	    }
	  }
	}
	term_Delete(term_FirstArgument(Term));   /* Delete old variable list */
	list_Delete(term_ArgumentList(Term)); 
	term_RplacTop(Term,DistrSymb);
	term_RplacArgumentList(Term,term_ArgumentList(Subterm));
	term_Free(Subterm);
	term_AddFatherLinks(Term);
	for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
	  term_RplacSuperterm((TERM) list_Car(Scan), Term);
	  if (term_HasPointerSubterm((TERM) list_Car(Scan), PredicateTerm)) {
	    puts("\ncheck1");
	    list_Rplaca(Scan,cnf_AntiPrenexPath(list_Car(Scan), PredicateTerm));
	    term_RplacSuperterm((TERM) list_Car(Scan), Term);
	  }
	}
      }
      else
	if (!fol_IsQuantifier(Subtop)) {
	  cnf_DistrQuantorNoVarSubPath(Term, PredicateTerm);
	  for (Scan=term_ArgumentList(Term); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
	    if (term_HasPointerSubterm(list_Car(Scan), PredicateTerm))
	      cnf_AntiPrenexPath(list_Car(Scan), PredicateTerm);
	  }
	}
    }
  }
  else
    if (!symbol_Equal(Top,fol_Not()) && !symbol_IsPredicate(Top))
      for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
	if (term_HasProperSuperterm(PredicateTerm, (TERM) list_Car(Scan)))
	  cnf_AntiPrenexPath(list_Car(Scan), PredicateTerm);
  
  term_AddFatherLinks(Term);
  return Term;
}


static TERM cnf_RemoveTrivialOperators(TERM Term)
/**************************************************************
  INPUT:   A formula.
  RETURNS: The formula after
           removal of "or" and "and" with only one argument
  CAUTION: The term is destructively changed.
***************************************************************/
{
  SYMBOL Top;
  LIST   Scan;

  Top = term_TopSymbol(Term);

  if (symbol_IsPredicate(Top))
    return Term;

  if ((symbol_Equal(Top,fol_And()) || symbol_Equal(Top,fol_Or())) &&
      list_Empty(list_Cdr(term_ArgumentList(Term)))) {
    TERM Result;
    Result = term_FirstArgument(Term);
    term_RplacSuperterm(Result, term_Superterm(Term));
    list_Delete(term_ArgumentList(Term));
    term_Free(Term);
    return cnf_RemoveTrivialOperators(Result);
  }

  for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    list_Rplaca(Scan,cnf_RemoveTrivialOperators(list_Car(Scan)));
    term_RplacSuperterm((TERM) list_Car(Scan), Term);
  }
  
  return Term;
}


static TERM cnf_SimplifyQuantors(TERM Term)
  /**************************************************************
  INPUT:   A formula.
  RETURNS: The formula after
	   removal of bindings of variables that don't occur in the
	   respective subformula and possible mergings of quantors
  CAUTION: The term is destructively changed.
***************************************************************/
{
  SYMBOL Top;
  LIST   Scan;

  Top = term_TopSymbol(Term);

  if (symbol_IsPredicate(Top) || symbol_Equal(Top,fol_Varlist()))
    return Term;

  if (fol_IsQuantifier(Top)) {
    LIST Vars;
    TERM Var,Subterm,Aux;
    Vars    = list_Nil();
    Subterm = term_SecondArgument(Term);

    while (symbol_Equal(term_TopSymbol(Subterm),Top)) {
      term_RplacArgumentList(term_FirstArgument(Term),
			     list_Nconc(fol_QuantifierVariables(Term),fol_QuantifierVariables(Subterm)));
      term_Free(term_FirstArgument(Subterm));
      Aux = term_SecondArgument(Subterm);
      list_Delete(term_ArgumentList(Subterm));
      term_Free(Subterm);
      list_Rplaca(list_Cdr(term_ArgumentList(Term)),Aux);
      Subterm = Aux;
    }
    
    for (Scan=fol_QuantifierVariables(Term);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
      Var = (TERM)list_Car(Scan);
      if (!fol_VarOccursFreely(Var,Subterm))
	Vars = list_Cons(Var,Vars);
    }
    if (!list_Empty(Vars)) {
      Subterm = term_FirstArgument(Term);
      term_RplacArgumentList(Subterm,list_NPointerDifference(term_ArgumentList(Subterm),Vars));
      term_DeleteTermList(Vars);
      if (list_Empty(term_ArgumentList(Subterm))) {
	Subterm = term_SecondArgument(Term);
	term_Delete(term_FirstArgument(Term));
	list_Delete(term_ArgumentList(Term));
	term_Free(Term);
	return cnf_SimplifyQuantors(Subterm);
      }
    }
  }
  
  for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
    list_Rplaca(Scan,cnf_SimplifyQuantors(list_Car(Scan)));
  
  return Term; 
}


TERM cnf_RemoveTrivialAtoms(TERM Term)
/**************************************************************
  INPUT:   A formula.
  RETURNS: The formula where occurrences of the atoms "true"
           and "false" are propagated and eventually removed.
  CAUTION: The term is destructively changed.
***************************************************************/
{
  SYMBOL Top,Subtop;
  LIST   Scan;
  TERM   Result;
  BOOL   Update;


  if (!term_IsComplex(Term))
    return Term;
  
  Top    = term_TopSymbol(Term);
  Update = FALSE;

  if (symbol_Equal(Top,fol_And())) {
    Scan  = term_ArgumentList(Term);
    while (!list_Empty(Scan)) {
      Result = cnf_RemoveTrivialAtoms(list_Car(Scan));
      Subtop = term_TopSymbol(Result);
      if (symbol_Equal(Subtop,fol_True()))
	Update = TRUE;
      else
	if (symbol_Equal(Subtop,fol_False())) {
	  term_RplacTop(Term,fol_False());
	  term_DeleteTermList(term_ArgumentList(Term));
	  term_RplacArgumentList(Term,list_Nil());
	  return Term;
	}
      Scan = list_Cdr(Scan);
    }
    if (Update) {
      term_RplacArgumentList(Term,fol_DeleteTrueTermFromList(term_ArgumentList(Term)));
      if (list_Empty(term_ArgumentList(Term))) {
	term_RplacTop(Term,fol_True());
	return Term;
      }
    }
  }
  else if (symbol_Equal(Top,fol_Or())) {
    Scan  = term_ArgumentList(Term);
    while (!list_Empty(Scan)) {
      Result = cnf_RemoveTrivialAtoms(list_Car(Scan));
      Subtop = term_TopSymbol(Result);
      if (symbol_Equal(Subtop,fol_False()))
	Update = TRUE;
      else
	if (symbol_Equal(Subtop,fol_True())) {
	  term_RplacTop(Term,fol_True());
	  term_DeleteTermList(term_ArgumentList(Term));
	  term_RplacArgumentList(Term,list_Nil());
	  return Term;
	}
      Scan = list_Cdr(Scan);
    }
    if (Update) {
      term_RplacArgumentList(Term,fol_DeleteFalseTermFromList(term_ArgumentList(Term)));
      if (list_Empty(term_ArgumentList(Term))) {
	term_RplacTop(Term,fol_False());
	return Term;
      }
    }
  }
  else if (fol_IsQuantifier(Top) || symbol_Equal(Top,fol_Not())) {
    if (fol_IsQuantifier(Top))
      Result = cnf_RemoveTrivialAtoms(term_SecondArgument(Term));
    else
      Result = cnf_RemoveTrivialAtoms(term_FirstArgument(Term));
    Subtop = term_TopSymbol(Result);
    if ((symbol_Equal(Subtop,fol_False()) && symbol_Equal(Top,fol_Not())) ||
	(symbol_Equal(Subtop,fol_True()) && fol_IsQuantifier(Top))) {
      term_RplacTop(Term,fol_True());
      term_DeleteTermList(term_ArgumentList(Term));
      term_RplacArgumentList(Term,list_Nil());
      return Term;
    }
    else
      if ((symbol_Equal(Subtop,fol_True()) && symbol_Equal(Top,fol_Not())) ||
	  (symbol_Equal(Subtop,fol_False()) && fol_IsQuantifier(Top))) {
	term_RplacTop(Term,fol_False());
	term_DeleteTermList(term_ArgumentList(Term));
	term_RplacArgumentList(Term,list_Nil());
	return Term;
      }
  }
  else if (symbol_Equal(Top,fol_Implies())) {
    Result = cnf_RemoveTrivialAtoms(term_FirstArgument(Term));
    Subtop = term_TopSymbol(Result);
    if (symbol_Equal(Subtop,fol_False())) {
      term_RplacTop(Term,fol_True());
      term_DeleteTermList(term_ArgumentList(Term));
      term_RplacArgumentList(Term,list_Nil());
      return Term;
    }
    else if (symbol_Equal(Subtop,fol_True())) {
      term_Delete(Result);
      Result = term_SecondArgument(Term);
      list_Delete(term_ArgumentList(Term));
      term_RplacTop(Term,term_TopSymbol(Result));
      term_RplacArgumentList(Term,term_ArgumentList(Result));
      term_Free(Result);
      return cnf_RemoveTrivialAtoms(Term);
    }
    Result = cnf_RemoveTrivialAtoms(term_SecondArgument(Term));
    Subtop = term_TopSymbol(Result);
    if (symbol_Equal(Subtop,fol_True())) {
      term_RplacTop(Term,fol_True());
      term_DeleteTermList(term_ArgumentList(Term));
      term_RplacArgumentList(Term,list_Nil());
      return Term;
    }
    else if (symbol_Equal(Subtop,fol_False())) {
      term_RplacTop(Term,fol_Not());
      term_RplacArgumentList(Term,fol_DeleteFalseTermFromList(term_ArgumentList(Term)));
    }
  }
  else if (symbol_Equal(Top,fol_Equiv())) {
    Result = cnf_RemoveTrivialAtoms(term_FirstArgument(Term));
    Subtop = term_TopSymbol(Result);
    if (symbol_Equal(Subtop,fol_False())) {
      term_RplacTop(Term,fol_Not());
      term_RplacArgumentList(Term,fol_DeleteFalseTermFromList(term_ArgumentList(Term)));
      if (list_Empty(term_ArgumentList(Term))) {
	term_RplacTop(Term, fol_True());
	return Term;
      }
      return cnf_RemoveTrivialAtoms(Term);
    }
    else if (symbol_Equal(Subtop,fol_True())) {
      term_Delete(Result);
      Result = term_SecondArgument(Term);
      list_Delete(term_ArgumentList(Term));
      term_RplacTop(Term,term_TopSymbol(Result));
      term_RplacArgumentList(Term,term_ArgumentList(Result));
      term_Free(Result);
      return cnf_RemoveTrivialAtoms(Term);
    }
    Result = cnf_RemoveTrivialAtoms(term_SecondArgument(Term));
    Subtop = term_TopSymbol(Result);
    if (symbol_Equal(Subtop,fol_False())) {
      term_RplacTop(Term,fol_Not());
      term_RplacArgumentList(Term,fol_DeleteFalseTermFromList(term_ArgumentList(Term)));
    }
    else if (symbol_Equal(Subtop,fol_True())) {
      term_Delete(Result);
      Result = term_FirstArgument(Term);
      list_Delete(term_ArgumentList(Term));
      term_RplacTop(Term,term_TopSymbol(Result));
      term_RplacArgumentList(Term,term_ArgumentList(Result));
      term_Free(Result);
    }
  }

  return Term;
}


TERM cnf_ObviousSimplifications(TERM Term)
/**************************************************************
  INPUT:   A formula.
  RETURNS: The formula after performing the following simplifications:
             - remove "or" and "and" with only one argument
	     - remove bindings of variables that don't occur in the
	       respective subformula
	     - merge quantors
  CAUTION: The term is destructively changed.
***************************************************************/
{
  Term = cnf_RemoveTrivialAtoms(Term);
  Term = cnf_RemoveTrivialOperators(Term);
  Term = cnf_SimplifyQuantors(Term);

  return Term;
}


/* EK: warum wird Term zurueckgegeben, wenn er destruktiv geaendert wird??? */
static TERM cnf_SkolemFormula(TERM Term, PRECEDENCE Precedence, LIST* Symblist)
/**************************************************************
  INPUT:   A formula in negation normal form, a precedence and pointer
           to a list used as return value.
  RETURNS: The skolemized term and the list of introduced Skolem functions.
  CAUTION: The term is destructively changed.
           The precedence of the new Skolem functions is set in <Precedence>.
***************************************************************/
{
  SYMBOL Top,SkolemSymbol;
  TERM   Subterm,SkolemTerm;
  LIST   Varlist,Scan;
  NAT    Arity;

  Top = term_TopSymbol(Term);
    
  if (fol_IsQuantifier(term_TopSymbol(Term))) {
    if (symbol_Equal(Top,fol_All())) {
      term_Delete(term_FirstArgument(Term));
      Subterm = term_SecondArgument(Term);
      list_Delete(term_ArgumentList(Term));
      term_RplacTop(Term,term_TopSymbol(Subterm));
      term_RplacArgumentList(Term,term_ArgumentList(Subterm));
      term_Free(Subterm);
      return cnf_SkolemFormula(Term, Precedence, Symblist);
    } 
    else {  /* exist quantifier */
      Varlist = fol_FreeVariables(Term);
      Arity   = list_Length(Varlist);
      for (Scan=fol_QuantifierVariables(Term);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
	SkolemSymbol = symbol_CreateSkolemFunction(Arity, Precedence);
	*Symblist  = list_Cons((POINTER)SkolemSymbol, *Symblist);
	SkolemTerm = term_Create(SkolemSymbol,Varlist); /* Caution: Sharing of Varlist ! */
	fol_ReplaceVariable(term_SecondArgument(Term),term_TopSymbol(list_Car(Scan)),SkolemTerm);
	term_Free(SkolemTerm);
      }
      list_Delete(Varlist);
      term_Delete(term_FirstArgument(Term));
      Subterm = term_SecondArgument(Term);
      list_Delete(term_ArgumentList(Term));
      term_RplacTop(Term,term_TopSymbol(Subterm));
      term_RplacArgumentList(Term,term_ArgumentList(Subterm));
      term_Free(Subterm);
      return cnf_SkolemFormula(Term, Precedence, Symblist);
    } 
  }
  else
    if (symbol_Equal(Top,fol_And()) || symbol_Equal(Top,fol_Or()))
      for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
	cnf_SkolemFormula(list_Car(Scan), Precedence, Symblist);
  return Term;
}


static TERM cnf_Cnf(TERM Term, PRECEDENCE Precedence, LIST* Symblist)
/**************************************************************
  INPUT:   A formula, a precedence and a pointer to a list of symbols
           used as return value.
  RETURNS: The term is transformed to conjunctive normal form.
  EFFECT:  The term is destructively changed and not normalized.
           The precedence of new Skolem symbols is set in <Precedence>.
***************************************************************/
{
  /* Necessary because ren_Rename crashes if a e.g. and() has only one argument */
  Term = cnf_ObviousSimplifications(Term);
  term_AddFatherLinks(Term);
  Term = ren_Rename(Term, Precedence, Symblist, FALSE, FALSE);
  Term = cnf_RemoveEquivImplFromFormula(Term);
  Term = cnf_NegationNormalFormula(Term);
  Term = cnf_SkolemFormula(cnf_AntiPrenex(Term), Precedence, Symblist);
  Term = cnf_DistributiveFormula(Term);

  return Term;
}


static LIST cnf_GetUsedTerms(CLAUSE C, PROOFSEARCH Search,
			     HASH InputClauseToTermLabellist) 
/**************************************************************
  INPUT:   
  RETURNS: 
***************************************************************/
{
  LIST UsedTerms, Used2, Scan;
  UsedTerms = list_Copy(hsh_Get(InputClauseToTermLabellist, C));
  UsedTerms = cnf_DeleteDuplicateLabelsFromList(UsedTerms);
  if (!list_Empty(UsedTerms))
    return UsedTerms;

  for (Scan = clause_ParentClauses(C); !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    CLAUSE P;
    int ClauseNumber;
    ClauseNumber = (int) list_Car(Scan);
    P = clause_GetNumberedCl(ClauseNumber, prfs_WorkedOffClauses(Search));
    if (P == NULL) {
      P = clause_GetNumberedCl(ClauseNumber, prfs_UsableClauses(Search));
      if (P == NULL)
	P = clause_GetNumberedCl(ClauseNumber, prfs_DocProofClauses(Search));
    }
    Used2 = cnf_GetUsedTerms(P, Search, InputClauseToTermLabellist);
    UsedTerms = list_Nconc(UsedTerms, Used2);
  }
  return UsedTerms;
}


static BOOL cnf_HaveProofOptSkolem(PROOFSEARCH Search, TERM topterm,
				   char* toplabel, TERM term2,
				   LIST* UsedTerms, LIST* Symblist,
				   HASH InputClauseToTermLabellist)
/**************************************************************
  INPUT:   
  RETURNS: ??? EK
***************************************************************/
{
  LIST       ConClauses, EmptyClauses;
  LIST       scan;
  BOOL       found;
  LIST       Usables;
  FLAGSTORE  Flags;
  PRECEDENCE Precedence;

  Flags      = prfs_Store(Search);
  Precedence = prfs_Precedence(Search);
  ConClauses = list_Nil();
  found      = FALSE;
  /* List of clauses from term2 */
  term_AddFatherLinks(term2);
  term2      = cnf_Cnf(term2, Precedence, Symblist);
  Usables    = cnf_MakeClauseList(term2, FALSE, FALSE, Flags, Precedence);
  term_Delete(term2);

  for (scan=Usables; !list_Empty(scan); scan = list_Cdr(scan)) {
    clause_SetFlag(list_Car(scan), CONCLAUSE);
    if (flag_GetFlagValue(Flags, flag_DOCPROOF)) {
#ifdef CHECK
      hsh_Check(InputClauseToTermLabellist);
#endif
      hsh_Put(InputClauseToTermLabellist, list_Car(scan), toplabel);
#ifdef CHECK_CNF
      fputs("\nUsable : ", stdout);
      clause_Print(list_Car(scan));
      printf(" Label %s", toplabel);
#endif
    }
  }
  EmptyClauses = cnf_SatUnit(Search, Usables);
  if (!list_Empty(EmptyClauses)) {
    found = TRUE;
#ifdef CHECK_CNF
    fputs("\nHaveProof : Empty Clause : ", stdout);
    clause_Print((CLAUSE) list_Car(EmptyClauses));
    putchar('\n');
#endif
    if (flag_GetFlagValue(Flags, flag_DOCPROOF))
      *UsedTerms = list_Nconc(*UsedTerms, cnf_GetUsedTerms((CLAUSE) list_Car(EmptyClauses), Search, InputClauseToTermLabellist));
    EmptyClauses = list_PointerDeleteDuplicates(EmptyClauses);
    clause_DeleteClauseList(EmptyClauses);
  }
    
  /* Removing ConClauses from UsablesIndex */
  ConClauses = list_Copy(prfs_UsableClauses(Search));
  for (scan = ConClauses; !list_Empty(scan); scan = list_Cdr(scan))
    if (flag_GetFlagValue(Flags, flag_DOCPROOF))
      prfs_MoveUsableDocProof(Search, (CLAUSE) list_Car(scan));
    else
      prfs_DeleteUsable(Search, (CLAUSE) list_Car(scan));
  list_Delete(ConClauses); 
	
  return found;
}


BOOL cnf_HaveProof(LIST TermList, TERM ToProve, FLAGSTORE InputFlags,
		   PRECEDENCE InputPrecedence)
/**************************************************************
  INPUT:   A list of terms, a term to prove, a flag store and a precedence.
           The arguments are not changed.
  RETURNS: True if the termlist implies ToProve
  CAUTION: All terms are copied.
***************************************************************/
{
  PROOFSEARCH search;
  LIST        scan, usables, symblist, emptyclauses;
  BOOL        found;
  FLAGSTORE   Flags;
  PRECEDENCE  Precedence;

  /* Use global PROOFSEARCH object to avoid stamp overflow */
  search  = cnf_HAVEPROOFPS;
  usables = symblist = list_Nil();

  /* Initialize search object's flag store */
  Flags = prfs_Store(search);
  flag_CleanStore(Flags);
  flag_InitFlotterSubproofFlags(InputFlags, Flags);
  /* Initialize search object's precedence */
  Precedence = prfs_Precedence(search);
  symbol_TransferPrecedence(InputPrecedence, Precedence);

  /* Build list of clauses from the termlist */
  for (scan=TermList; !list_Empty(scan); scan=list_Cdr(scan)) {
    TERM t;
    t = term_Copy(list_Car(scan));
    t = cnf_Cnf(t, Precedence, &symblist);

    usables = list_Nconc(cnf_MakeClauseList(t,FALSE,FALSE,Flags,Precedence),
			 usables);
    term_Delete(t); 
  }

  /* Build clauses from negated term to prove */
  ToProve = term_Create(fol_Not(), list_List(term_Copy(ToProve)));
  term_AddFatherLinks(ToProve);
  ToProve = cnf_Cnf(ToProve, Precedence, &symblist);
  usables = list_Nconc(cnf_MakeClauseList(ToProve,FALSE,FALSE,Flags,Precedence),
		       usables);
  term_Delete(ToProve);

  /* SatUnit requires the CONCLAUSE flag */
  for (scan=usables;!list_Empty(scan); scan = list_Cdr(scan))
    clause_SetFlag(list_Car(scan), CONCLAUSE);

  emptyclauses = cnf_SatUnit(search, usables);
  
  if (!list_Empty(emptyclauses)) {
    found = TRUE;
    emptyclauses = list_PointerDeleteDuplicates(emptyclauses);
    clause_DeleteClauseList(emptyclauses);
  }
  else
    found = FALSE;
  prfs_Clean(search);
  symbol_DeleteSymbolList(symblist);

  return found;
}


static void cnf_RplacVarsymbFunction(TERM term, SYMBOL varsymb, TERM function)
/**********************************************************
  INPUT:   A term, a variable symbol and a function.
  EFFECT:  The variable with the symbol  varsymb in the term 
           is replaced by the function function.
  CAUTION: The term is destructively changed.
***********************************************************/
{
  int  bottom;
  TERM term1;
  LIST scan;

  bottom = vec_ActMax();
  vec_Push(term);

  while (bottom != vec_ActMax()) {
    term1 = (TERM)vec_PopResult();
    if (symbol_Equal(term_TopSymbol(term1),varsymb)) {
      term_RplacTop(term1,term_TopSymbol(function));
      term_RplacArgumentList(term1,term_CopyTermList(term_ArgumentList(function)));
    }else
      if (!list_Empty(term_ArgumentList(term1)))
	for (scan=term_ArgumentList(term1);!list_Empty(scan);scan=list_Cdr(scan))
	  vec_Push(list_Car(scan));
  }
  vec_SetMax(bottom);
}


static void cnf_RplacVar(TERM Term, LIST Varlist, LIST Termlist)
/**********************************************************
  INPUT:   A term,a variable symbol and a function.
  RETURNS: The variable with the symbol  varsymb in the term 
           is replaced by the function function.
  CAUTION: The term is destructively changed.
***********************************************************/
{
  int  bottom;
  TERM term1;
  LIST scan,scan2;

  bottom = vec_ActMax();
  vec_Push(Term);

  while (bottom != vec_ActMax()) {
    term1 = vec_PopResult();
    if (symbol_IsVariable(term_TopSymbol(term1))) {
      BOOL done;
      done = FALSE;
      for (scan=Varlist, scan2=Termlist; !list_Empty(scan) && !done; 
	   scan = list_Cdr(scan), scan2 = list_Cdr(scan2)) {
	if (symbol_Equal(term_TopSymbol(term1),term_TopSymbol(list_Car(scan)))) {
	  term_RplacTop(term1,term_TopSymbol((TERM) list_Car(scan2)));
	  term_RplacArgumentList(term1,
				 term_CopyTermList(term_ArgumentList(list_Car(scan2))));
	  done = TRUE;
	}
      }
    }
    else
      if (!list_Empty(term_ArgumentList(term1)))
	for (scan=term_ArgumentList(term1);!list_Empty(scan);scan=list_Cdr(scan))
	  vec_Push(list_Car(scan));
  }
  vec_SetMax(bottom);
}


static TERM cnf_MakeSkolemFunction(LIST varlist, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A list of variables and a precedence.
  RETURNS: The new term oskf... (oskc...) which is a function 
           with varlist as arguments.
  EFFECT:  The precedence of the new Skolem function is set in <Precedence>.
***************************************************************/
{
  TERM   term;
  SYMBOL skolem;
  
  skolem = symbol_CreateSkolemFunction(list_Length(varlist), Precedence);
  term   = term_Create(skolem, term_CopyTermList(varlist));
  return term;
}


static void cnf_PopAllQuantifier(TERM term)
/********************************************************
 INPUT:   A term whose top symbol is fol_all.
 RETURNS: Nothing.
 EFFECT:  Removes the quantifier
********************************************************/
{
  TERM SubTerm;
  LIST VarList;

#ifdef CHECK
  if (!symbol_Equal(term_TopSymbol(term), fol_All())) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cnf_PopAllQuantifier: Top symbol is not fol_All !\n");
    misc_FinishErrorReport();
  }
#endif

  VarList = term_ArgumentList(term_FirstArgument(term));
  term_DeleteTermList(VarList);
  term_Free(term_FirstArgument(term));
  SubTerm = term_SecondArgument(term);
  list_Delete(term_ArgumentList(term));
  term_RplacTop(term,term_TopSymbol(SubTerm));
  term_RplacArgumentList(term,term_ArgumentList(SubTerm));
  term_Free(SubTerm);
}


static TERM cnf_QuantifyAndNegate(TERM term, LIST VarList, LIST FreeList)
/****************************************************************
  INPUT:   A term, a list of variables to be exist-quantified,
           a list of variables to be all-quantified
  RETURNS: not(forall[FreeList](exists[VarList](term)))
  MEMORY:  The term, the lists and their arguments are copied.
***************************************************************/
{
  TERM Result;
  TERM TermCopy;
  LIST VarListCopy;
  LIST FreeListCopy;

  TermCopy = term_Copy(term);
  VarListCopy = term_CopyTermList(VarList);
  Result = fol_CreateQuantifier(fol_Exist(),VarListCopy,list_List(TermCopy));
  FreeListCopy = list_Nil();

  FreeList = fol_FreeVariables(Result);
  if (!list_Empty(FreeList)) {
    FreeListCopy = term_CopyTermList(FreeList);
    list_Delete(FreeList);
    Result = fol_CreateQuantifier(fol_All(), FreeListCopy, list_List(Result));
  }
  Result = term_Create(fol_Not(), list_List(Result));
  return Result;
}


static TERM cnf_MoveProvedTermToTopLevel(TERM Term, TERM Term1, TERM Proved,
					 LIST VarList, LIST FreeList,
					 PRECEDENCE Precedence)
/********************************************************************
  INPUT:   A top-level term, which must be a conjunction,
           a subterm <Term1> of <Term>, a subterm <Proved> of <Term1>,
	   a list of existence quantified variables <VarList>,
	   a list of free variables <FreeList> and a precedence.
           <Term1> is of the form
	   exists[...](t1 and t2 and ... and Proved and ..)
  RETURNS: A new term, where <Proved> is removed from the arguments
           of <Term1>.
  EFFECT:  The precedence of new Skolem functions is set in <Precedence>
*******************************************************************/
{
  TERM termR;
  TERM skolemfunction;
  SYMBOL varsymb;
  LIST scan;

  termR = term_SecondArgument(Term1); /* t1 and t2 and ... and Proved ... */
  term_RplacArgumentList(termR,
			 list_PointerDeleteElement(term_ArgumentList(termR),
						   Proved));
  if (list_Length(term_ArgumentList(termR)) < 2) {
    TERM termRL = term_FirstArgument(termR);     /* t1 */
    list_Delete(term_ArgumentList(termR));
    term_RplacTop(termR, term_TopSymbol(termRL));
    term_RplacArgumentList(termR,term_ArgumentList(termRL));
    term_Free(termRL);
  }

  for (scan = VarList; scan != list_Nil(); scan = list_Cdr(scan)) {
    varsymb = term_TopSymbol(list_Car(scan));
    skolemfunction = cnf_MakeSkolemFunction(FreeList, Precedence);
    cnf_RplacVarsymbFunction(termR,varsymb,skolemfunction);
    cnf_RplacVarsymbFunction(Proved,varsymb,skolemfunction); 
    term_Delete(skolemfunction); 
  }

  if (!list_Empty(FreeList)) {
    Proved = 
      fol_CreateQuantifier(fol_All(), term_CopyTermList(FreeList),
			   list_List(Proved));
    if (list_Length(FreeList) > 1)
      Proved = cnf_QuantMakeOneVar(Proved);
  }
 
  term_Delete(term_FirstArgument(Term1)); /* Variables of "exists" */
  list_Delete(term_ArgumentList(Term1));
  term_RplacTop(Term1,term_TopSymbol(termR));
  term_RplacArgumentList(Term1,term_ArgumentList(termR));
  term_Free(termR);
    
  term_RplacArgumentList(Term, list_Cons(Proved, term_ArgumentList(Term)));
  return Proved;
}


static void cnf_Skolemize(TERM Term, LIST FreeList, PRECEDENCE Precedence)
/********************************************************
  INPUT:   A existence quantified term, the list of free variables
           and a precedence.
  RETURNS: Nothing.
  EFFECT:  The term is destructively changed, i.e. the
           existence quantifier is removed by skolemization.
	   The precedence of new Skolem functions is set in <Precedence>.
*********************************************************/
{
  LIST exlist;
  TERM subterm;
  LIST symblist;

  symblist = list_Nil();
  exlist = cnf_GetSymbolList(term_ArgumentList(term_FirstArgument(Term)));
  term_Delete(term_FirstArgument(Term));
  subterm = term_SecondArgument(Term);
  list_Delete(term_ArgumentList(Term));
  term_RplacTop(Term,term_TopSymbol(subterm));
  term_RplacArgumentList(Term,term_ArgumentList(subterm));
  term_Free(subterm);
  symblist = cnf_SkolemFunctionFormula(Term, FreeList, exlist, Precedence);
  list_Delete(exlist);
  list_Delete(symblist);
}


static LIST cnf_FreeVariablesBut(TERM Term, LIST Symbols)
/********************************************************
  INPUT:   A term and a list of symbols
  RETURNS: A list of all free variable terms in Term whose symbols are 
           not in Symbols
*********************************************************/
{
  LIST follist, Scan;
  follist = fol_FreeVariables(Term);
  for (Scan = follist; !list_Empty(Scan); Scan = list_Cdr(Scan))
    if (list_Member(Symbols, (POINTER)term_TopSymbol(list_Car(Scan)),
		    (BOOL (*)(POINTER,POINTER))symbol_Equal))
      list_Rplaca(Scan,NULL);
  follist = list_PointerDeleteElement(follist,NULL);
    
  return follist;
}


static void cnf_SkolemFunctionFormulaMapped(TERM term, LIST allist, LIST map)
/**************************************************************
  INPUT:   A term  term and a  list allist of variables and a list map
           of pairs (variable symbols, function symbol)
  RETURNS: None.
  CAUTION: The term is destructively changed. All variable symbols
           in map which appear in term are replaced by the skolem functions
	   with respect to allist which contains the universally quantified
	   variables.
***************************************************************/
{
  TERM   term1;
  LIST   scan,scan1;
  SYMBOL skolem, symbol;
  int    bottom;

  bottom = vec_ActMax();
  
  for (scan1=map; !list_Empty(scan1); scan1=list_Cdr(scan1)) {
    vec_Push(term);
    symbol = (SYMBOL) list_PairFirst((LIST) list_Car(scan1));
    skolem = (SYMBOL) list_PairSecond((LIST) list_Car(scan1));

#ifdef CHECK_STRSKOLEM
    if (flag_GetFlagValue(flag_PSTRSKOLEM)) {
      fputs("\nVariable : ", stdout);
      symbol_Print(symbol);
      fputs("\nFunction : ", stdout);
      symbol_Print(skolem);
    }
#endif
    while (bottom != vec_ActMax()) {
      term1 = (TERM)vec_PopResult();

      if (symbol_Equal(term_TopSymbol(term1),symbol)) {
	term_RplacTop(term1,skolem);
	list_Delete(term_ArgumentList(term1));
	term_RplacArgumentList(term1,term_CopyTermList(allist));
      }
      if (!list_Empty(term_ArgumentList(term1)))
	for (scan=term_ArgumentList(term1);!list_Empty(scan);scan=list_Cdr(scan)) {
	  vec_Push(list_Car(scan));
	}
    }
  }
  vec_SetMax(bottom);
}


static BOOL cnf_HasDeeperVariable(LIST List1, LIST List2)
/******************************************************************
   INPUT:   Two lists of variable terms
   RETURNS: TRUE if a variable in the first list is deeper than all variables
            in the second list, FALSE otherwise.
   NOTE:    If cnf_VARIABLEDEPTHARRAY is not allocated this will crash
            If new variables are introduced by strong skolemization, their
            depth is -1.
*******************************************************************/
{
  LIST scan;
  int  maxdepth1;
  
  /* Determine maximum depth of variables in List1 */
  maxdepth1 = 0;
  for (scan=List1; !list_Empty(scan); scan=list_Cdr(scan)) {
    int i;
    i = cnf_VARIABLEDEPTHARRAY[term_TopSymbol((TERM) list_Car(scan))];
#ifdef CHECK_STRSKOLEM
    if (flag_GetFlagValue(flag_PSTRSKOLEM)) {
      fputs("\nFor variable ", stdout);
      symbol_Print(term_TopSymbol((TERM) list_Car(scan)));
      printf(" depth is %d.", i);
    }
#endif
    if (i > maxdepth1)
      maxdepth1 = i;
  }

  /* Compare with depth of variables in List2 */
  for (scan=List2; !list_Empty(scan); scan=list_Cdr(scan)) {
    int i;
    i = cnf_VARIABLEDEPTHARRAY[term_TopSymbol((TERM) list_Car(scan))];
#ifdef CHECK_STRSKOLEM
    if (flag_GetFlagValue(flag_PSTRSKOLEM)) {
      fputs("\nFor variable ", stdout);
      symbol_Print(term_TopSymbol((TERM) list_Car(scan)));
      printf(" depth is %d.", i);
    }
#endif
    if (i >= maxdepth1)
      return FALSE;
  }
  return  TRUE;
}


static void cnf_StrongSkolemization(PROOFSEARCH Search, TERM Topterm,
				    char* Toplabel, BOOL TopAnd, TERM Term, 
				    LIST* UsedTerms, LIST* Symblist,
				    BOOL Result1,
				    HASH InputClauseToTermLabellist, int Depth)
/******************************************************************
  INPUT:   An existence quantified formula. ??? EK
  RETURNS: Nothing.
  EFFECT:  The existence quantifier is removed by strong skolemization.
           The precedence of new Skolem symbols is set in the precedence
	   of the search object.
*******************************************************************/
{
  LIST       exlist;    /* Variable symbols bound by exists[]() */
  LIST       pairlist;  /* List of pairs (Subterm of AND, free variable symbols
			   not in exlist) */
  LIST       allfreevariables;
  LIST       newvariables;       /* w2..wn*/
  LIST       mapping;           /* List of pairs */
  int        numberofallfreevariables, acc_length, i;
  LIST       pair, pairscan, pairscan_pred, scan, accumulatedvariables;
  TERM       subterm, w;
  BOOL       strskolemsuccess;  /* Indicates whether strong skolemization was
				   possible */
  FLAGSTORE  Flags;
  PRECEDENCE Precedence;

  Flags      = prfs_Store(Search);
  Precedence = prfs_Precedence(Search);

  /* Necessary so that new variables really are new ! */
  if (flag_GetFlagValue(Flags, flag_CNFSTRSKOLEM))
    symbol_SetStandardVarCounter(term_MaxVar(Topterm));

  /* Get list of quantified variable symbols x_k */
  exlist = cnf_GetSymbolList(term_ArgumentList(term_FirstArgument(Term)));
  /* Pop quantifier */
  term_Delete(term_FirstArgument(Term));
  subterm = term_SecondArgument(Term);
  list_Delete(term_ArgumentList(Term));
  term_RplacTop(Term,term_TopSymbol(subterm));
  term_RplacArgumentList(Term,term_ArgumentList(subterm));
  term_Free(subterm);

  /* Now for every argument get the list of free variables whose symbols
     are not in exlist */
  pairlist = list_Nil();
  for (scan=term_ArgumentList(Term); !list_Empty(scan); scan = list_Cdr(scan)) {
    pair = list_PairCreate((TERM) list_Car(scan), 
			   cnf_FreeVariablesBut((TERM) list_Car(scan), exlist));
    if (list_Empty(pairlist)) 
      pairlist = list_List(pair);
    else {
      /* First sort subterms by number of free variables */
      int pairlength, currentlength;
      pairlength = list_Length((LIST) list_PairSecond(pair));
      pairscan = pairlist; 
      pairscan_pred = list_Nil();
      currentlength = 0;
      while (!list_Empty(pairscan)) {
	currentlength = list_Length((LIST) list_PairSecond((LIST) list_Car(pairscan)));
	if (currentlength < pairlength) {
	  pairscan_pred = pairscan;
	  pairscan = list_Cdr(pairscan);
	}
	else if (currentlength == pairlength) {
	  /* If both subterms have the same number of free variables compare depth of variables */
	  if (cnf_HasDeeperVariable((LIST) list_PairSecond((LIST) list_Car(pairscan)), /* in list */
				   (LIST) list_PairSecond(pair))) {                   /* new pair */
#ifdef CHECK_STRSKOLEM
	    if (flag_GetFlagValue(flag_PSTRSKOLEM)) {
	      fputs("\nTerm ", stdout);
	      term_Print((TERM) list_PairFirst((LIST) list_Car(pairscan)));
	      fputs("\n has deeper variable than ", stdout);
	      term_Print((TERM) list_PairFirst(pair));
	    }
#endif	    
	    pairscan_pred = pairscan;
	    pairscan = list_Cdr(pairscan);
	  }
	  else
	    break;
	}
	else
	  break;
      }
      
      /* New pair has more variables than all others in list */
      if (list_Empty(pairscan))
	list_Rplacd(pairscan_pred, list_List(pair));
      /* New pair is inserted between pairscan_pred and pairscan */
      else if (currentlength >= pairlength) { 
	/* Head of list */
	if (list_Empty(pairscan_pred))
	  pairlist = list_Cons(pair, pairlist);
	else 
	  list_InsertNext(pairscan_pred, pair);
      }
      /* The case for the same number of variables is not yet implemented */
    }
  }

#ifdef CHECK_STRSKOLEM
  if (flag_GetFlagValue(flag_PSTRSKOLEM)) {
    for (pairscan=pairlist; !list_Empty(pairscan); pairscan = list_Cdr(pairscan)) {
      LIST l;
      fputs("\nSubterm ", stdout);
      term_Print((TERM) list_PairFirst((LIST) list_Car(pairscan)));
      fputs("\n  has free variables ", stdout);
      for (l=(LIST) list_PairSecond((LIST) list_Car(pairscan)); !list_Empty(l); l = list_Cdr(l)) {
	term_Print((TERM) list_Car(l));
	fputs(" ", stdout);
      }
    }
  }
#endif

  /* Determine number of all free variablein and()--term whose symbols are not in exlist */
  /* Create map from ex_variables tp skolem symbols */
  allfreevariables = cnf_FreeVariablesBut(Term, exlist);
  numberofallfreevariables = list_Length(allfreevariables);
    
  mapping  = list_Nil();

  for (scan = exlist; !list_Empty(scan); scan = list_Cdr(scan)) {
    SYMBOL skolem;
    skolem = symbol_CreateSkolemFunction(numberofallfreevariables, Precedence);
    *Symblist = list_Cons((POINTER)skolem,*Symblist);
    mapping = list_Cons(list_PairCreate(list_Car(scan), (POINTER)skolem), 
			mapping);
  }
  list_Delete(allfreevariables);

  /* Create new variables */
  newvariables = list_Nil();

  for (i=0; i < numberofallfreevariables; i++) {
    w = term_CreateStandardVariable();
    newvariables = list_Cons(w, newvariables);
  }

#ifdef CHECK_STRSKOLEM
  if (flag_GetFlagValue(flag_PSTRSKOLEM)) {
    LIST l;
    fputs("\nNew variables : ", stdout);
    for (l=newvariables; !list_Empty(l); l = list_Cdr(l)) {
      term_Print((TERM) list_Car(l));
      fputs(" ", stdout);
    }
  }
#endif
  
  /* Now do the replacing */
  accumulatedvariables = list_Nil();
  acc_length = 0;
  strskolemsuccess = FALSE;
  for (pairscan=pairlist; !list_Empty(pairscan); pairscan=list_Cdr(pairscan)) {
    LIST allist;

    /* Add bound variables for this subterm */
    accumulatedvariables = list_Nconc(accumulatedvariables,
				      (LIST) list_PairSecond((LIST) list_Car(pairscan)));
    accumulatedvariables = term_DeleteDuplicatesFromList(accumulatedvariables);

    /* Remove new variables not (no longer) needed */
    for (i=0; i < list_Length(accumulatedvariables) - acc_length; i++) {
      term_Delete((TERM) list_Top(newvariables));
      newvariables = list_Pop(newvariables);
    }
    acc_length = list_Length(accumulatedvariables);

#ifdef CHECK_STRSKOLEM
    if (flag_GetFlagValue(flag_PSTRSKOLEM)) {
      LIST l;
      fputs("\n\nSubterm is ", stdout);
      term_Print((TERM) list_PairFirst((LIST) list_Car(pairscan)));
      fputs("\nFree variables : ", stdout);
      for (l=accumulatedvariables; !list_Empty(l); l = list_Cdr(l)) {
	term_Print((TERM) list_Car(l));
	fputs(" ", stdout);
      }
    }
#endif
    if (!list_Empty(newvariables))
      strskolemsuccess = TRUE;
    allist = list_Nconc(list_Copy(accumulatedvariables), list_Copy(newvariables));

    cnf_SkolemFunctionFormulaMapped((TERM) list_PairFirst((LIST) list_Car(pairscan)), allist,
				    mapping);
#ifdef CHECK_STRSKOLEM
    if (flag_GetFlagValue(flag_PSTRSKOLEM)) {
      fputs("\nSubterm after skolemization : ", stdout);
      term_Print(list_PairFirst((LIST) list_Car(pairscan)));
    }
#endif

    list_Delete(allist);
    cnf_OptimizedSkolemFormula(Search, Topterm, Toplabel, TopAnd,
			       (TERM) list_PairFirst((LIST) list_Car(pairscan)),
			       UsedTerms, Symblist, Result1, 
			       InputClauseToTermLabellist, Depth);
  }
  while (!list_Empty(newvariables)) {
    term_Delete((TERM) list_Top(newvariables));
    newvariables = list_Pop(newvariables);
  }
  list_Delete(accumulatedvariables); /* Only pairs and pairlist left */
  list_DeletePairList(pairlist);
  list_Delete(exlist);
  list_DeletePairList(mapping);
  if (flag_GetFlagValue(Flags, flag_PSTRSKOLEM) && strskolemsuccess) {
    fputs("\nStrong skolemization applied", stdout);
  }
}
    

static void cnf_OptimizedSkolemFormula(PROOFSEARCH Search, TERM topterm,
				       char* toplabel, BOOL TopAnd, TERM term, 
				       LIST* UsedTerms, LIST* Symblist,
				       BOOL Result1,
				       HASH InputClauseToTermLabellist,
				       int Depth)
/**************************************************************
  INPUT:   Two terms in negation normal form. ??? EK
  RETURNS: The  skolemized term with the optimized skolemization
           due to Ohlbach and Weidenbach of <term> and further improvements.
	   <rest> is used as additional, conjunctively added information.
  EFFECT:  The symbol precedence of the search  object is changed
           because new Skolem symbols are defined.
  CAUTION: The term is destructively changed.
***************************************************************/
{
  TERM       termL2, provedterm;
  LIST       freevariables, scan, varlist;
  SYMBOL     top;
  BOOL       result2;
  BOOL       optimized;
  FLAGSTORE  Flags;
  PRECEDENCE Precedence;

  result2       = FALSE;
  freevariables = list_Nil();
  Flags         = prfs_Store(Search);
  Precedence    = prfs_Precedence(Search);
  
  top = term_TopSymbol(term);
  if (fol_IsQuantifier(top)) {
    if (symbol_Equal(top,fol_All())) {
      /* For quantified variables store depth if strong skolemization is performed */
      if (flag_GetFlagValue(Flags, flag_CNFSTRSKOLEM)) {
	LIST variables;
	variables = term_ArgumentList(term_FirstArgument(term));
	for (scan=variables; !list_Empty(scan); scan=list_Cdr(scan)) {
#ifdef CHECK_STRSKOLEM
	  if (flag_GetFlagValue(Flags, flag_PSTRSKOLEM)) {
	    if (cnf_VARIABLEDEPTHARRAY[term_TopSymbol(list_Car(scan))] != -1) {
	      fputs("\nFor variable ", stderr);
	      term_Print((TERM) list_Car(scan));
	      printf(" depth is already set to %d, now setting it to %d", 
		     cnf_VARIABLEDEPTHARRAY[term_TopSymbol(list_Car(scan))],Depth);
	    }
	  }
#endif
#ifdef CHECK_STRSKOLEM
	  if (flag_GetFlagValue(Flags, flag_PSTRSKOLEM)) {
	    fputs("\nVariable ", stdout);
	    term_Print((TERM) list_Car(scan));
	    printf(" has depth %d in term\n  ", Depth);
	    term_Print(term);
	  }
#endif
	  cnf_VARIABLEDEPTHARRAY[term_TopSymbol(list_Car(scan))] = Depth;
	}
	Depth++;
      }
      cnf_PopAllQuantifier(term);
      cnf_OptimizedSkolemFormula(Search,topterm, toplabel, TopAnd, term, 
				 UsedTerms, Symblist, Result1,
				 InputClauseToTermLabellist, Depth);
      return;
    }
    freevariables = fol_FreeVariables(term);
    optimized = FALSE;
    if (symbol_Equal(term_TopSymbol(term_SecondArgument(term)), fol_And())) {
      if (flag_GetFlagValue(Flags, flag_CNFOPTSKOLEM)) {
	scan = term_ArgumentList(term_SecondArgument(term));
	varlist = term_ArgumentList(term_FirstArgument(term));
	while (!list_Empty(scan) && !optimized) {
	  if (!Result1) {
	    if (TopAnd) {
	      if (flag_GetFlagValue(Flags, flag_POPTSKOLEM)) {
		fputs("\nHaveProof not necessary", stdout);
	      }
	      result2 = TRUE;
	    }
	    else {
	      termL2 = cnf_QuantifyAndNegate((TERM) list_Car(scan), 
					     varlist, freevariables);
	      result2 = cnf_HaveProofOptSkolem(Search, topterm, toplabel, termL2,
					       UsedTerms, Symblist, 
					       InputClauseToTermLabellist);
#ifdef CHECK_OPTSKOLEM
	      if (flag_GetFlagValue(Flags, flag_POPTSKOLEM)) {
		fputs("\nHaveProof result : ", stdout);
		if (result2)
		  fputs("TRUE", stdout);
		else
		  fputs("FALSE", stdout);
	      }
#endif
	    }
	  }
	    
	  if (Result1 || result2) {
	    optimized = TRUE;
	    if (flag_GetFlagValue(Flags, flag_POPTSKOLEM)) {
	      fputs("\nIn term ", stdout);
	      term_Print(topterm);
	      fputs("\n subterm ", stdout);
	      term_Print((TERM) list_Car(scan));
	      puts(" is moved to toplevel.");
	    }
	    provedterm =
	      cnf_MoveProvedTermToTopLevel(topterm, term, list_Car(scan), 
					   varlist, freevariables, Precedence);
	    if (flag_GetFlagValue(Flags, flag_POPTSKOLEM)) {
	      fputs("Result : ", stdout);
	      term_Print(topterm);
	      putchar('\n');
	    }
	    /* provedterm is argument of top AND term */
	    cnf_OptimizedSkolemFormula(Search, topterm, toplabel, TRUE,
				       provedterm,UsedTerms, Symblist, Result1, 
				       InputClauseToTermLabellist, Depth);
	  }
	  else 
	    scan = list_Cdr(scan);
	}
      }
      if (!optimized) {
	/* Optimized skolemization not enabled or not possible */
	if (flag_GetFlagValue(Flags, flag_CNFSTRSKOLEM)) {
	  optimized = TRUE; /* Strong Skolemization is always possible after exists[..](and(..)) */
	  cnf_StrongSkolemization(Search, topterm, toplabel, TopAnd, term,
				  UsedTerms, Symblist, Result1, 
				  InputClauseToTermLabellist, Depth);
	}
      }
    }
    else
      TopAnd = FALSE;
    if (!optimized) {
      /* Optimized skolemization not enabled or not possible */
      /* Strong skolemization not enabled or not possible */
      cnf_Skolemize(term, freevariables, Precedence);
    }
    list_Delete(freevariables);
    cnf_OptimizedSkolemFormula(Search, topterm, toplabel, TopAnd, term,UsedTerms,
			       Symblist,Result1,InputClauseToTermLabellist,Depth);
    return;
  } 
  else {
    if (symbol_Equal(top,fol_And()) || symbol_Equal(top,fol_Or())) {
      if (symbol_Equal(top,fol_Or()))
	TopAnd = FALSE;
      for (scan=term_ArgumentList(term);!list_Empty(scan);
	   scan=list_Cdr(scan))
	cnf_OptimizedSkolemFormula(Search, topterm, toplabel, TopAnd,
				   (TERM) list_Car(scan),
				   UsedTerms, Symblist,
				   Result1, InputClauseToTermLabellist, Depth);
    }
  }
  return;
}


static LIST cnf_SkolemFunctionFormula(TERM term, LIST allist, LIST exlist,
				      PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A term <term>, a list <allist> of variables, a list <exlist>
           of variable symbols and a precedence.
  RETURNS: The list of new Skolem functions.
  EFFECT:  The term is destructively changed. All variable symbols
           in <exlist> which appear in <term> are replaced by skolem functions
	   with respect to <allist> which contains the universally quantified
	   variables.
	   New Skolem functions are created and their precedence is set
	   in <Precedence>.
***************************************************************/
{
  TERM   term1;
  LIST   scan, scan1, Result;
  SYMBOL skolem;
  int    bottom,n;

  Result = list_Nil();
  bottom = vec_ActMax();
  n = list_Length(allist);
  
  for (scan1=exlist; !list_Empty(scan1); scan1=list_Cdr(scan1)) {
    vec_Push(term);
    skolem = symbol_CreateSkolemFunction(n, Precedence);
    Result = list_Cons((POINTER)skolem, Result);
    
    while (bottom != vec_ActMax()) {
      term1 = (TERM)vec_PopResult();
      if (symbol_Equal(term_TopSymbol(term1),(SYMBOL)list_Car(scan1))) {
	term_RplacTop(term1,skolem);
	list_Delete(term_ArgumentList(term1));
	term_RplacArgumentList(term1,term_CopyTermList(allist));
      }
      if (!list_Empty(term_ArgumentList(term1)))
	for (scan=term_ArgumentList(term1);!list_Empty(scan);scan=list_Cdr(scan))
	  vec_Push(list_Car(scan));
    }
  }
  vec_SetMax(bottom);
  return Result;
}


static LIST cnf_OptimizedSkolemization(PROOFSEARCH Search, TERM Term,
				       char* Label, LIST* UsedTerms, 
				       LIST* Symblist, BOOL result,
				       BOOL Conjecture, 
				       HASH InputClauseToTermLabellist)
/**************************************************************
  INPUT:   A term, a shared index and a list of non-ConClauses. ??? EK
  RETURNS: The list of clauses derived from Term.
  EFFECT:  The term is skolemized using optimized skolemization wrt ShIndex.
**************************************************************/
{
  LIST       Clauses;
  TERM       FirstArg;
  int        i;
  FLAGSTORE  Flags;
  PRECEDENCE Precedence;

#ifdef CHECK
  if (Term == NULL) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cnf_OptimizedSkolemization: Input term is NULL.\n");
    misc_FinishErrorReport();
  }
#endif

  Flags      = prfs_Store(Search);
  Precedence = prfs_Precedence(Search);
  FirstArg   = Term;

  if (flag_GetFlagValue(Flags, flag_CNFSTRSKOLEM)) {
    /* Initializing array */
    for (i = 1; i <= symbol__MAXSTANDARDVAR; i++)
      cnf_VARIABLEDEPTHARRAY[i] = -1;
  }

  if (flag_GetFlagValue(Flags, flag_POPTSKOLEM) ||
      flag_GetFlagValue(Flags, flag_PSTRSKOLEM)) {
    fputs("\nTerm before skolemization : \n ", stdout);
    fol_PrettyPrintDFG(Term);
  }

  if (!fol_IsLiteral(Term)) {
    if (flag_GetFlagValue(Flags, flag_CNFOPTSKOLEM) ||
	flag_GetFlagValue(Flags, flag_CNFSTRSKOLEM))  {
      if (flag_GetFlagValue(Flags, flag_CNFOPTSKOLEM))
	Term = term_Create(fol_And(), list_List(Term)); /* CW hack: definitions are added on top level*/
      cnf_OptimizedSkolemFormula(Search, Term, Label, TRUE, FirstArg, UsedTerms, 
				 Symblist, result, InputClauseToTermLabellist, 0);
    }
    else {
      LIST Symbols;
      Symbols = list_Nil();
      Term    = cnf_SkolemFormula(Term, Precedence, &Symbols);
      list_Delete(Symbols);
    }
  }
  if (flag_GetFlagValue(Flags, flag_POPTSKOLEM) ||
      flag_GetFlagValue(Flags, flag_PSTRSKOLEM)) {
    fputs("\nTerm after skolemization : ", stdout);
    term_Print(Term);
  }
  Term    = cnf_DistributiveFormula(Term);
  Clauses = cnf_MakeClauseList(Term, FALSE, Conjecture, Flags, Precedence);
  term_Delete(Term);

  return Clauses;
}


LIST cnf_GetSkolemFunctions(TERM Term, LIST ArgList, LIST* SkolToExVar)
/**************************************************************
  INPUT:   A term, the argumentlist of a skolem function, a mapping from
           a skolem function to a variable
  RETURNS: The longest argumentlist of all skolem functions found so far.
  EFFECT:  Computes information for renaming variables and replacing 
           skolem functions during de-skolemization.
**************************************************************/ 
{
  LIST Scan;
  SYMBOL Top;
    
  Top = term_TopSymbol(Term);

  if (fol_IsQuantifier(Top)) 
    return cnf_GetSkolemFunctions(term_SecondArgument(Term), ArgList, 
				  SkolToExVar);

  if (symbol_IsFunction(Top) && symbol_HasProperty(Top, SKOLEM)) {
    BOOL found;
    SYMBOL Var = 0;
    int Arity;
    found = FALSE;
      
    /* Keep longest argument list of all skolem functions in the clause for renaming */
    /* Delete all other argument lists */
    Arity = list_Length(term_ArgumentList(Term));
    if (Arity > list_Length(ArgList)) {
      term_DeleteTermList(ArgList);
      ArgList = term_ArgumentList(Term);
    }
    else 
      term_DeleteTermList(term_ArgumentList(Term));
    term_RplacArgumentList(Term, NULL);
      
    /* Replace skolem function by variable */
    if (list_Length(*SkolToExVar) > Arity) {
      NAT i;
      LIST SkolScan = *SkolToExVar;
      for (i = 0; i < Arity; i++)
	SkolScan = list_Cdr(SkolScan);
      for (SkolScan = (LIST) list_Car(SkolScan);
	   (SkolScan != list_Nil()) && !found; SkolScan = list_Cdr(SkolScan)) {
	SYMBOL Skol;
	Skol = (SYMBOL) list_PairFirst((LIST) list_Car(SkolScan));
	if (Skol == term_TopSymbol(Term)) {
	  Var = (SYMBOL) list_PairSecond((LIST) list_Car(SkolScan));
	  found = TRUE;
	}
      }
    }
    if (!found) {
      LIST Pair;
      NAT  i;
      LIST SkolScan;

      SkolScan = *SkolToExVar;
      for (i = 0; i < Arity; i++) {
	if (list_Cdr(SkolScan) == list_Nil())
	  list_Rplacd(SkolScan, list_List(NULL));
	SkolScan = list_Cdr(SkolScan);
      }

      Var = symbol_CreateStandardVariable();
      Pair = list_PairCreate((POINTER) term_TopSymbol(Term), 
			     (POINTER) Var);
      if (list_Car(SkolScan) == list_Nil())
	list_Rplaca(SkolScan, list_List(Pair));
      else
	list_Rplaca(SkolScan, list_Nconc((LIST) list_Car(SkolScan), 
					 list_List(Pair)));
    }
    term_RplacTop(Term, Var);
  }
  else {
    for (Scan = term_ArgumentList(Term); Scan != list_Nil(); 
	Scan = list_Cdr(Scan))
      ArgList = cnf_GetSkolemFunctions((TERM) list_Car(Scan), ArgList, 
				       SkolToExVar);
  }
  return ArgList;
}


void cnf_ReplaceVariable(TERM Term, SYMBOL Old, SYMBOL New)
/**************************************************************
  INPUT:  A term, two symbols that are variables
  EFFECT: In term every occurrence of Old is replaced by New
**************************************************************/ 
{
  LIST Scan;

#ifdef CHECK
  if (!symbol_IsVariable(Old)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cnf_ReplaceVariable: Illegal input symbol.\n");
    misc_FinishErrorReport();
  }
#endif

  if (symbol_Equal(term_TopSymbol(Term), Old))
    term_RplacTop(Term, New);
  else 
    for (Scan = term_ArgumentList(Term); !list_Empty(Scan); 
	 Scan = list_Cdr(Scan))
      cnf_ReplaceVariable(list_Car(Scan), Old, New);
}


LIST cnf_RemoveSkolemFunctions(CLAUSE Clause, LIST* SkolToExVar, LIST Vars)
/**************************************************************
  INPUT:   A clause, a list which is a mapping from skolem functions to
           variables and a list of variables for forall-quantification.
  RETURNS: A list of terms derived from the clause using deskolemization
  EFFECT:  Arguments of skolem functions are renamed consistently.
           Skolemfunctions are replaced by variables.
**************************************************************/
{
  LIST Scan;
  LIST TermScan, TermList, ArgList;
  TERM Term;
  int i;

  TermList = list_Nil();

  ArgList = list_Nil();
  for (i = 0; i < clause_Length(Clause); i++) {
    Term = term_Copy(clause_GetLiteralTerm(Clause, i));
    ArgList = cnf_GetSkolemFunctions(Term, ArgList, SkolToExVar);
    TermList = list_Cons(Term, TermList);
  }
    
  if (list_Empty(ArgList))
    return TermList;
    
  /* Rename variables */
  for (Scan = ArgList; Scan != list_Nil(); Scan = list_Cdr(Scan)) {
    for (TermScan = TermList; TermScan != list_Nil(); 
	 TermScan = list_Cdr(TermScan)) {
      Term = (TERM) list_Car(TermScan);
      cnf_ReplaceVariable(Term,
			  term_TopSymbol((TERM) list_Car(Scan)),
			  (SYMBOL) list_Car(Vars));
    }
    if (list_Cdr(Vars) == list_Nil()) {
      SYMBOL New = symbol_CreateStandardVariable();
      Vars = list_Nconc(Vars, list_List((POINTER) New));
    }
    Vars = list_Cdr(Vars);
  }
  term_DeleteTermList(ArgList);
  return TermList;
}


TERM cnf_DeSkolemFormula(LIST Clauses)
/**************************************************************
  INPUT:   A list of clauses.
  RETURNS: A formula built from the clauses.
  EFFECT:  All skolem functions are removed from the clauses.
**************************************************************/
{
  LIST Scan, SkolToExVar, Vars, FreeVars, FreeVarsCopy, VarScan, TermList;
  TERM VarListTerm, TopTerm, Term;
  BOOL First;
  
  SkolToExVar = list_List(NULL);
  Vars = list_List((POINTER) symbol_CreateStandardVariable());
  
  TopTerm = term_Create(fol_And(), NULL);
  
  for (Scan = Clauses; Scan != list_Nil(); Scan = list_Cdr(Scan)) {
    TermList =  cnf_RemoveSkolemFunctions((CLAUSE) list_Car(Scan),
					  &SkolToExVar, Vars);
    Term = term_Create(fol_Or(), TermList);
    FreeVars = fol_FreeVariables(Term);
    if (!list_Empty(FreeVars)) {
      FreeVarsCopy = term_CopyTermList(FreeVars);
      list_Delete(FreeVars);
      Term = fol_CreateQuantifier(fol_All(), FreeVarsCopy, list_List(Term));
    }
    term_RplacArgumentList(TopTerm, list_Cons(Term, term_ArgumentList(TopTerm)));
  }
  
  VarScan = Vars;
  First = TRUE;
  
  for (Scan = SkolToExVar; Scan != list_Nil(); Scan = list_Cdr(Scan)) {
    if (list_Empty(list_Car(Scan))) {
      if (term_TopSymbol(TopTerm) == fol_All())
	term_RplacArgumentList(TopTerm, list_Cons(term_Create((SYMBOL) list_Car(VarScan), NULL),  
						  term_ArgumentList(TopTerm)));
      if (!First)
	TopTerm = fol_CreateQuantifier(fol_All(),
				       list_List(term_Create((SYMBOL) list_Car(VarScan), NULL)),
				       list_List(TopTerm)); 
    }
    else {
      LIST ExVarScan;
      LIST ExVars = list_Nil();
      for (ExVarScan = list_Car(Scan); ExVarScan != list_Nil();
	  ExVarScan = list_Cdr(ExVarScan)) {
	if (ExVars == list_Nil())
	  ExVars = list_List(term_Create((SYMBOL) list_PairSecond((LIST) list_Car(ExVarScan)), NULL));
	else
	  ExVars = list_Cons(term_Create((SYMBOL) list_PairSecond((LIST) list_Car(ExVarScan)), NULL), ExVars);
	list_PairFree((LIST) list_Car(ExVarScan));
      }
      list_Delete((LIST) list_Car(Scan));
      list_Rplaca(Scan, NULL);

      if (term_TopSymbol(TopTerm) == fol_Exist()) {
	VarListTerm = (TERM) list_Car(term_ArgumentList(TopTerm));
	term_RplacArgumentList(VarListTerm,
			       list_Nconc(term_ArgumentList(VarListTerm),
					  ExVars));
      }
      else
	TopTerm = fol_CreateQuantifier(fol_Exist(), ExVars, list_List(TopTerm));
      ExVars = list_Nil();

      if (!First) 
	TopTerm = fol_CreateQuantifier(fol_All(), 
				       list_List(term_Create((SYMBOL) list_Car(VarScan), NULL)),
				       list_List(TopTerm));
    }
    if (!First) 
      VarScan = list_Cdr(VarScan);
    else
      First = FALSE;
	
  }
  list_Delete(SkolToExVar);
  list_Delete(Vars);

  return TopTerm;
}


#ifdef OPTCHECK
/* Currently unused */
/*static */
LIST cnf_CheckOptimizedSkolemization(LIST* AxClauses, LIST* ConClauses,
				     TERM AxTerm, TERM ConTerm,
				     LIST NonConClauses, LIST* SkolemPredicates,
				     SHARED_INDEX ShIndex, BOOL result)
/**********************************************************
  EFFECT: Used to check the correctness of optimized skolemization
***********************************************************/
{
  TERM DeSkolemizedAxOpt, DeSkolemizedConOpt, DeSkolemizedAx, DeSkolemizedCon;
  TERM TopOpt, Top, ToProve;
  LIST SkolemFunctions2;

  if (*AxClauses != list_Nil()) {
    DeSkolemizedAxOpt = cnf_DeSkolemFormula(*AxClauses);
    if (*ConClauses != list_Nil()) {
      DeSkolemizedConOpt = cnf_DeSkolemFormula(*ConClauses);
      TopOpt = term_Create(fol_And(), 
			   list_Cons(DeSkolemizedAxOpt, 
				     list_List(DeSkolemizedConOpt)));
    }
    else 
      TopOpt = DeSkolemizedAxOpt;
  }
  else {
    DeSkolemizedConOpt = cnf_DeSkolemFormula(*ConClauses);     
    TopOpt = DeSkolemizedConOpt;
  }
  
  clause_DeleteClauseList(*AxClauses);
  clause_DeleteClauseList(*ConClauses);
  *AxClauses = list_Nil();
  *ConClauses = list_Nil();
  
  flag_SetFlagValue(flag_CNFOPTSKOLEM, flag_CNFOPTSKOLEMOFF);  
  if (AxTerm) {
    *AxClauses = cnf_OptimizedSkolemization(term_Copy(AxTerm), ShIndex, NonConClauses, result,FALSE, ClauseToTermLabellist);
  }
  if (ConTerm) {
    *ConClauses = cnf_OptimizedSkolemization(term_Copy(ConTerm), ShIndex, NonConClauses, result,TRUE, ClauseToTermLabellist);
  }
  
  if (*AxClauses != list_Nil()) {
    DeSkolemizedAx = cnf_DeSkolemFormula(*AxClauses);
    if (*ConClauses != list_Nil()) {
      DeSkolemizedCon = cnf_DeSkolemFormula(*ConClauses);
      Top = term_Create(fol_And(), 
			list_Cons(DeSkolemizedAx, 
				  list_List(DeSkolemizedCon)));
    }
    else 
      Top = DeSkolemizedAx;
  }
  else {
    DeSkolemizedCon = cnf_DeSkolemFormula(*ConClauses);    
    Top = DeSkolemizedCon;
  }
  
  clause_DeleteClauseList(*AxClauses);
  clause_DeleteClausList(*ConClauses);
  *AxClauses = list_Nil();
  *ConClauses = list_Nil();
  
  ToProve = term_Create(fol_Equiv(), list_Cons(TopOpt, list_List(Top)));
  ToProve = term_Create(fol_Not(), list_List(ToProve));
  fol_NormalizeVars(ToProve); 
  ToProve  = cnf_ObviousSimplifications(ToProve);
  term_AddFatherLinks(ToProve);
  ToProve  = ren_Rename(ToProve,SkolemPredicates,FALSE);
  ToProve  = cnf_RemoveEquivImplFromFormula(ToProve);
  ToProve  = cnf_NegationNormalFormula(ToProve);
  ToProve  = cnf_AntiPrenex(ToProve);
  
  SkolemFunctions2 = list_Nil();
  ToProve     = cnf_SkolemFormula(ToProve, &SkolemFunctions2);
  ToProve     = cnf_DistributiveFormula(ToProve);
  *ConClauses = cnf_MakeClauseList(ToProve);
  if (ToProve)
    term_Delete(ToProve);
  *AxClauses = list_Nil();
  return SkolemFunctions2;
}
#endif


PROOFSEARCH cnf_Flotter(LIST AxiomList, LIST ConjectureList, LIST* AxClauses, 
			LIST* AllLabels, HASH TermLabelToClauselist, 
			HASH ClauseToTermLabellist, FLAGSTORE InputFlags,
			PRECEDENCE InputPrecedence, LIST* Symblist)
/**************************************************************
  INPUT:   A list of axiom formulae,
           a list of conjecture formulae,
	   a pointer to a list in which clauses derived from axiom formulae 
	   are stored,
	   a pointer to a list in which clauses derived from 
	   conjecture formulae are stored, ???
	   a pointer to a list of all termlabels,
	   a hasharray in which for every term label the list of clauses 
	   derived from the term is stored (if DocProof is set),
	   a hasharray in which for every clause the list of labels 
	   of the terms used for deriving the clause is stored (if DocProof 
	   is set),
	   a flag store,
	   a precedence
	   a pointer to a list of symbols which have to be deleted later if
	   the ProofSearch object is kept.
  RETURNS: If KeepProofSearch ??? is TRUE, then the ProofSearch object is not
           freed but returned.
	   Else, NULL is returned.
  EFFECT:  ??? EK
           The precedence of new skolem symbols is set in <InputPrecedence>.
***************************************************************/
{
  LIST        Scan, Scan2, FormulaClauses,SkolemFunctions;
  LIST        SkolemPredicates, EmptyClauses, AllFormulae;
  LIST        UsedTerms;
  TERM        AxTerm,Formula;
  BOOL        Result;
  PROOFSEARCH Search;
  PRECEDENCE  Precedence;
  FLAGSTORE   Flags;
  NAT         Count;
  HASH        InputClauseToTermLabellist;

  Search = prfs_Create();

  /* Initialize the flagstore for the CNF transformation */
  Flags = prfs_Store(Search);
  flag_CleanStore(Flags);
  flag_InitFlotterFlags(InputFlags, Flags);
  /* Initialize the precedence */
  Precedence = prfs_Precedence(Search);
  symbol_TransferPrecedence(InputPrecedence, Precedence);

  if (flag_GetFlagValue(Flags, flag_DOCPROOF))
    prfs_AddDocProofSharingIndex(Search);

  AxTerm           = (TERM)NULL;
  SkolemPredicates = list_Nil();
  Result           = FALSE;
  if (flag_GetFlagValue(Flags, flag_DOCPROOF))
    InputClauseToTermLabellist = hsh_Create();
  else 
    InputClauseToTermLabellist = NULL;

  symbol_ReinitGenericNameCounters();

  for (Scan = AxiomList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    LIST Pair;
    Pair = list_Car(Scan);
    AxTerm = (TERM) list_PairSecond(Pair);
    fol_RemoveImplied(AxTerm);
    term_AddFatherLinks(AxTerm);
    fol_NormalizeVars(AxTerm);
    if (flag_GetFlagValue(Flags, flag_CNFFEQREDUCTIONS))
      cnf_PropagateSubstEquations(AxTerm);
    AxTerm = cnf_ObviousSimplifications(AxTerm);
    if (flag_GetFlagValue(Flags, flag_CNFRENAMING)) {
      term_AddFatherLinks(AxTerm);
      AxTerm = ren_Rename(AxTerm, Precedence, &SkolemPredicates,
			  flag_GetFlagValue(Flags, flag_CNFPRENAMING), TRUE);
    }
    AxTerm = cnf_RemoveEquivImplFromFormula(AxTerm);
    AxTerm = cnf_NegationNormalFormula(AxTerm);
    AxTerm = cnf_AntiPrenex(AxTerm);
    list_Rplacd(Pair, (LIST) AxTerm);
  }
  AllFormulae = AxiomList;
  
  /* At this point the list contains max. 1 element, which is a pair 
     of the label NULL and the negated
     conjunction of all conjecture formulae. */

  Count = 0;
  for (Scan = ConjectureList; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    TERM  ConTerm;
    char* Label;
    char  buf[100];
    /* Add label */  
    if (list_PairFirst(list_Car(Scan)) == NULL) {
      sprintf(buf, "conjecture%d", Count);
      Label = string_StringCopy(buf);
      list_Rplaca((LIST) list_Car(Scan), Label);
      if (flag_GetFlagValue(Flags, flag_DOCPROOF) &&
	  flag_GetFlagValue(Flags, flag_PLABELS)) {
	printf("\nAdded label %s for conjecture", Label);
	fol_PrettyPrintDFG((TERM) list_PairSecond(list_Car(Scan)));
      }
    }

    ConTerm = (TERM) list_PairSecond((LIST) list_Car(Scan));
    fol_RemoveImplied(ConTerm);
    term_AddFatherLinks(ConTerm);
    fol_NormalizeVars(ConTerm);  
    if (flag_GetFlagValue(Flags, flag_CNFFEQREDUCTIONS))
      cnf_PropagateSubstEquations(ConTerm);
    ConTerm  = cnf_ObviousSimplifications(ConTerm); 

    if (flag_GetFlagValue(Flags, flag_CNFRENAMING)) {
      term_AddFatherLinks(ConTerm);
      ConTerm = ren_Rename(ConTerm, Precedence, &SkolemPredicates,
			   flag_GetFlagValue(Flags, flag_CNFPRENAMING),TRUE);
    }
    /* fputs("\nRen:\t",stdout);term_Print(ConTerm);putchar('\n'); */
    ConTerm  = cnf_RemoveEquivImplFromFormula(ConTerm);
    ConTerm  = cnf_NegationNormalFormula(ConTerm);
    /* fputs("\nAn:\t",stdout);term_Print(ConTerm);putchar('\n'); */
    ConTerm  = cnf_AntiPrenex(ConTerm);
    /* fputs("\nPr:\t",stdout);term_Print(ConTerm);putchar('\n'); */
    /* Insert changed term into pair */
    list_Rplacd((LIST) list_Car(Scan), (LIST) ConTerm);

    Count++;
  } 

  AllFormulae = list_Append(ConjectureList, AllFormulae);
  for (Scan = ConjectureList;!list_Empty(Scan); Scan = list_Cdr(Scan))
    list_Rplaca(Scan,list_PairSecond(list_Car(Scan)));

  FormulaClauses = list_Nil();
  SkolemFunctions = list_Nil();
  Count = 0;
  for (Scan = AllFormulae; !list_Empty(Scan); Scan = list_Cdr(Scan), Count++) {
    LIST FormulaClausesTemp;
    Formula            = term_Copy((TERM) list_PairSecond(list_Car(Scan)));
#ifdef CHECK_CNF
    fputs("\nInputFormula : ",stdout); term_Print(Formula); 
    printf("\nLabel : %s", (char*) list_PairFirst(list_Car(Scan)));
#endif
    Formula            = cnf_SkolemFormula(Formula,Precedence,&SkolemFunctions);
    Formula            = cnf_DistributiveFormula(Formula);
    FormulaClausesTemp = cnf_MakeClauseList(Formula,FALSE,FALSE,Flags,Precedence);
    if (flag_GetFlagValue(Flags, flag_DOCPROOF)) {
      for (Scan2 = FormulaClausesTemp; !list_Empty(Scan2); Scan2 = list_Cdr(Scan2)) {
	hsh_Put(InputClauseToTermLabellist, list_Car(Scan2), list_PairFirst(list_Car(Scan)));
      }
    }
    FormulaClauses = list_Nconc(FormulaClauses, FormulaClausesTemp);
    term_Delete(Formula);
  }

  /* Trage nun Formula Clauses modulo Reduktion in einen Index ein */
 
  /* red_SatUnit works only on conclauses */
  for (Scan = FormulaClauses; !list_Empty(Scan); Scan = list_Cdr(Scan))
    clause_SetFlag((CLAUSE) list_Car(Scan), CONCLAUSE);
  /* For FormulaClauses a full saturation */
  /* List is deleted in red_SatUnit ! */
  EmptyClauses = red_SatUnit(Search, FormulaClauses);
  if (!list_Empty(EmptyClauses)) {
    Result = TRUE;
    /*puts("\nPROOF in FormulaClauses");*/
    clause_DeleteClauseList(EmptyClauses);
  }

  /* Move all usables to workedoff */
  FormulaClauses = list_Copy(prfs_UsableClauses(Search));
  for (Scan = FormulaClauses; !list_Empty(Scan); Scan = list_Cdr(Scan))
    prfs_MoveUsableWorkedOff(Search, (CLAUSE) list_Car(Scan));
  list_Delete(FormulaClauses);
  FormulaClauses = list_Nil();

#ifdef CHECK
  /*cnf_CheckClauseListsConsistency(ShIndex); */
#endif     


  *Symblist = list_Nil();
  for (Scan = AllFormulae; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    LIST Ax, Pair;
    UsedTerms = list_Nil();
    Pair = list_Car(Scan);
#ifdef CHECK_CNF
    fputs("\nFormula : ", stdout);
    term_Print((TERM) list_PairSecond(Pair)); 
    printf("\nLabel : %s", (char*) list_PairFirst(Pair)); 
#endif
    Ax = cnf_OptimizedSkolemization(Search, term_Copy((TERM)list_PairSecond(Pair)), 
				    (char*) list_PairFirst(Pair), &UsedTerms, 
				    Symblist,Result,FALSE,InputClauseToTermLabellist);
    /* Set CONCLAUSE flag for clauses derived from conjectures */
    if (list_PointerMember(ConjectureList,list_PairSecond(Pair))) {
      LIST l;
      for (l = Ax; !list_Empty(l); l = list_Cdr(l))
	clause_SetFlag((CLAUSE) list_Car(l), CONCLAUSE);
    }
    if (flag_GetFlagValue(Flags, flag_DOCPROOF)) {
      hsh_PutListWithCompareFunc(TermLabelToClauselist, list_PairFirst(Pair),
				 list_Copy(Ax),
				 (BOOL (*)(POINTER,POINTER))cnf_LabelEqual,
				 (unsigned long (*)(POINTER))hsh_StringHashKey);
      UsedTerms = list_Cons(list_PairFirst(Pair), UsedTerms);
      UsedTerms = cnf_DeleteDuplicateLabelsFromList(UsedTerms);
      for (Scan2 = Ax; !list_Empty(Scan2); Scan2 = list_Cdr(Scan2)) {
	hsh_PutList(ClauseToTermLabellist, list_Car(Scan2), list_Copy(UsedTerms));
	hsh_PutList(InputClauseToTermLabellist, list_Car(Scan2), list_Copy(UsedTerms));
      } 
    }
    *AxClauses = list_Nconc(*AxClauses, Ax);
    list_Delete(UsedTerms);
  }

  /* Transfer precedence of new skolem symbols into <InputPrecedence> */
  symbol_TransferPrecedence(Precedence, InputPrecedence);

  list_Delete(ConjectureList);
  if (flag_GetFlagValue(Flags, flag_DOCPROOF))
    hsh_Delete(InputClauseToTermLabellist);
  if (!flag_GetFlagValue(Flags, flag_INTERACTIVE)) { 
    list_Delete(*Symblist);
  }

  *AllLabels = list_Nil();
  for (Scan = AllFormulae; !list_Empty(Scan); Scan = list_Cdr(Scan)) {
    LIST Pair;
    Pair = list_Car(Scan);
    term_Delete((TERM) list_PairSecond(Pair));
    *AllLabels = list_Cons(list_PairFirst(Pair), *AllLabels);
    list_PairFree(Pair);
  }

  list_Delete(AllFormulae);
  list_Delete(SkolemFunctions);
  list_Delete(SkolemPredicates);

  if (!flag_GetFlagValue(Flags, flag_INTERACTIVE)) {
    symbol_ResetSkolemIndex();
    prfs_Delete(Search);
    return NULL;
  }
  else {
    /* Delete DocProof clauses */
    prfs_DeleteDocProof(Search);
    return Search;
  }
}

LIST cnf_QueryFlotter(PROOFSEARCH Search, TERM Term, LIST* Symblist)
/**************************************************************
  INPUT:   A term to derive clauses from, using optimized skolemization,
           and a ProofSearch object. 
  RETURNS: A list of derived clauses.
  EFFECT:  ??? EK
           The precedence of new skolem symbols is set in <Search>.
***************************************************************/
{
  LIST       SkolemPredicates, SkolemFunctions, IndexedClauses, Scan;
  LIST       ResultClauses, Dummy, EmptyClauses;
  TERM       TermCopy;
  int        Formulae2Clause;
  BOOL       Result;
  FLAGSTORE  Flags, SubProofFlags;
  PRECEDENCE Precedence;

  Flags      = prfs_Store(Search);
  Precedence = prfs_Precedence(Search);

  /* Initialize the flagstore of the cnf_SEARCHCOPY object with default values */
  /* and copy the value of flag_DOCPROOF from the global Proofserach object.   */
  SubProofFlags = prfs_Store(cnf_SEARCHCOPY);
  flag_InitStoreByDefaults(SubProofFlags);
  flag_TransferFlag(Flags, SubProofFlags, flag_DOCPROOF);
  /* Transfer the precedence into the local search object */
  symbol_TransferPrecedence(Precedence, prfs_Precedence(cnf_SEARCHCOPY));

  SkolemPredicates = SkolemFunctions = list_Nil();
  Result = FALSE;
  
  prfs_CopyIndices(Search, cnf_SEARCHCOPY);

  Term = term_Create(fol_Not(), list_List(Term));
  fol_NormalizeVars(Term);
  Term = cnf_ObviousSimplifications(Term);
  if (flag_GetFlagValue(Flags, flag_CNFRENAMING)) {
    term_AddFatherLinks(Term);
    Term = ren_Rename(Term, Precedence, &SkolemPredicates,
		      flag_GetFlagValue(Flags,flag_CNFPRENAMING), TRUE);
  }
  Term = cnf_RemoveEquivImplFromFormula(Term);
  Term = cnf_NegationNormalFormula(Term);
  Term = cnf_AntiPrenex(Term);
  
  TermCopy = term_Copy(Term);
  TermCopy = cnf_SkolemFormula(TermCopy, Precedence, &SkolemFunctions);
  TermCopy = cnf_DistributiveFormula(TermCopy);

  IndexedClauses = cnf_MakeClauseList(TermCopy,FALSE,FALSE,Flags,Precedence);
  term_Delete(TermCopy);

  /* red_SatUnit works only on conclauses */
  for (Scan = IndexedClauses; !list_Empty(Scan); Scan = list_Cdr(Scan))
    clause_SetFlag((CLAUSE) list_Car(Scan), CONCLAUSE);

  EmptyClauses = red_SatUnit(cnf_SEARCHCOPY, IndexedClauses);

  if (!list_Empty(EmptyClauses)) {
    Result = TRUE;
    clause_DeleteClauseList(EmptyClauses);
  }

  while (!list_Empty(prfs_UsableClauses(cnf_SEARCHCOPY))) {
    prfs_MoveUsableWorkedOff(cnf_SEARCHCOPY, (CLAUSE) list_Car(prfs_UsableClauses(cnf_SEARCHCOPY)));
  }
  /* Works only if DOCPROOF is false. Otherwise we need labels */
  Dummy = list_Nil();
  if (flag_GetFlagValue(SubProofFlags, flag_DOCPROOF))
    Formulae2Clause = TRUE;
  else
    Formulae2Clause = FALSE;
  flag_SetFlagValue(SubProofFlags, flag_DOCPROOF, flag_DOCPROOFOFF);
  ResultClauses = cnf_OptimizedSkolemization(cnf_SEARCHCOPY, term_Copy(Term),
					     NULL, &Dummy, Symblist, Result,
					     FALSE, NULL);

  if (Formulae2Clause)
    flag_SetFlagValue(SubProofFlags, flag_DOCPROOF, flag_DOCPROOFON);
  
  term_Delete(Term);
  list_Delete(SkolemPredicates);
  list_Delete(SkolemFunctions);
  prfs_Clean(cnf_SEARCHCOPY);

  /* All result clauses of queries are conjecture clauses */
  for (Scan=ResultClauses; !list_Empty(Scan); Scan=list_Cdr(Scan))
    clause_SetFlag((CLAUSE) list_Car(Scan), CONCLAUSE);

  return ResultClauses;
}


#ifdef CHECK
/* Currently unused */
/*static*/ void cnf_CheckClauseListsConsistency(SHARED_INDEX ShIndex)
/**************************************************************
  INPUT: A shared index and a list of non-ConClauses.
  EFFECT: When this function is called all clauses in the index must be
       non-ConClauses, which must also be members of the list.
**************************************************************/
{
  LIST AllClauses, scan;

  AllClauses = clause_AllIndexedClauses(ShIndex);
  for (scan = AllClauses; scan != list_Nil(); scan = list_Cdr(scan)) {
    if (clause_GetFlag((CLAUSE) list_Car(scan), CONCLAUSE)) {
      misc_StartErrorReport();
      misc_ErrorReport("\n In cnf_CheckClauseListsConsistency: Clause is a CONCLAUSE.\n");
      misc_FinishErrorReport();
    } 
    if (clause_GetFlag((CLAUSE) list_Car(scan), BLOCKED)) {
      misc_StartErrorReport();
      misc_ErrorReport("\n In cnf_CheckClauseListsConsistency: Clause is BLOCKED.\n");
      misc_FinishErrorReport();
    }
  }
  list_Delete(AllClauses);
}
#endif


static LIST cnf_SatUnit(PROOFSEARCH Search, LIST ClauseList) 
/*********************************************************
  INPUT:   A list of unshared clauses, proof search object
  RETURNS: A possibly empty list of empty clauses.
**********************************************************/
{
  CLAUSE     Given;
  LIST       Scan, Derivables, EmptyClauses, BackReduced;
  NAT        n, Derived;
  FLAGSTORE  Flags;
  PRECEDENCE Precedence;

  Flags        = prfs_Store(Search);
  Precedence   = prfs_Precedence(Search);
  Derived      = flag_GetFlagValue(Flags, flag_CNFPROOFSTEPS);
  EmptyClauses = list_Nil();
  ClauseList   = clause_ListSortWeighed(ClauseList);
  
  while (!list_Empty(ClauseList) && list_Empty(EmptyClauses)) {
    Given = (CLAUSE)list_NCar(&ClauseList);
    Given = red_CompleteReductionOnDerivedClause(Search, Given, red_ALL);
    if (Given) {
      if (clause_IsEmptyClause(Given))
        EmptyClauses = list_List(Given);
      else {
        /*fputs("\n\nGiven: ",stdout);clause_Print(Given);*/
	BackReduced = red_BackReduction(Search, Given, red_USABLE);
	
        if (Derived != 0) {
	  Derivables =
	    inf_BoundedDepthUnitResolution(Given, prfs_UsableSharingIndex(Search),
					   FALSE, Flags, Precedence);
	  Derivables =
	    list_Nconc(Derivables,
		       inf_BoundedDepthUnitResolution(Given,prfs_WorkedOffSharingIndex(Search),
						      FALSE, Flags, Precedence));
          n = list_Length(Derivables);
          if (n > Derived)
            Derived = 0;
          else
            Derived -= n;
        }
        else 
          Derivables = list_Nil();
	
        Derivables  = list_Nconc(BackReduced,Derivables);
        Derivables  = split_ExtractEmptyClauses(Derivables, &EmptyClauses);
	
	prfs_InsertUsableClause(Search, Given);
	
	for (Scan = Derivables; !list_Empty(Scan); Scan = list_Cdr(Scan))
	  ClauseList = clause_InsertWeighed(list_Car(Scan), ClauseList, Flags,
					    Precedence);
	list_Delete(Derivables);
      }
    }
  }
  clause_DeleteClauseList(ClauseList);
  return EmptyClauses;
}


TERM cnf_DefTargetConvert(TERM Target, TERM ToTopLevel, TERM ToProveDef, 
			  LIST DefPredArgs, LIST TargetPredArgs,
			  LIST TargetPredVars, LIST VarsForTopLevel,
			  FLAGSTORE Flags, PRECEDENCE Precedence,
			  BOOL* LocallyTrue)
/**********************************************************
  INPUT:   A term Target which contains a predicate that might be replaced
           by its definition.
	   A term ToTopLevel which is the highest level subterm in Target
	   that contains the predicate and can be moved to top level or().
	   A term ToProveDef which must hold if the definition is to be applied.
	   (IS DESTROYED AND FREED)
	   A list DefPredArgs of the arguments of the predicate in the
	   Definition.
	   A list TargetPredArgs of the arguments of the predicate in Target.
	   A list TargetPredVars of the variables occurring in the arguments
	   of the predicate in Target.
	   A list VarsForTopLevel containing the variables that should be
	   all-quantified at top level to make the proof easier.
	   A flag store.
	   A pointer to a boolean LocallyTrue which is set to TRUE iff
	   the definition can be applied.
  RETURNS: The Target term which is brought into standard form.
**********************************************************/

{
  TERM orterm, targettoprove;
  SYMBOL maxvar;                    /* For normalizing terms */
  LIST l1, l2;
  LIST freevars, vars;              /* Free variables in targettoprove */

  if (flag_GetFlagValue(Flags, flag_PAPPLYDEFS)) {
    puts("\nTarget :");
    fol_PrettyPrint(Target);
  }
#ifdef CHECK
  fol_CheckFatherLinks(Target);
#endif
  /* No proof found yet */
  *LocallyTrue = FALSE;

  /* Remove implications from path */
  Target = cnf_RemoveImplFromFormulaPath(Target, ToTopLevel);
    
  /* Move negations as far down as possible */
  Target = cnf_NegationNormalFormulaPath(Target, ToTopLevel);
    
  /* Move quantifiers as far down as possible */
  Target = cnf_AntiPrenexPath(Target, ToTopLevel);

  /* Move all-quantified variables from the predicates' arguments to top level */
  Target = cnf_MovePredicateVariablesUp(Target, ToTopLevel, VarsForTopLevel);

  /* Flatten top or() */
  Target = cnf_FlattenPath(Target, ToTopLevel);

  /* Now make sure that all variables in the top forall quantifier are in TargetPredVars */
  /* Not necessary, according to CW */
  if (symbol_Equal(term_TopSymbol(Target), fol_All())) {
    targettoprove = term_Copy(term_SecondArgument(Target));
    orterm        = term_SecondArgument(Target);
  }
  else {
    targettoprove = term_Copy(Target);
    orterm        = Target;
  }

  /* Find argument of targettoprove that contains the predicate and remove it */
  if (symbol_Equal(term_TopSymbol(targettoprove), fol_Or())) {
    /* Find subterm that contains the predicate */
    LIST arglist;
    arglist = term_ArgumentList(targettoprove);
    for (l1=arglist, l2=term_ArgumentList(orterm); !list_Empty(l1); 
	l1 = list_Cdr(l1), l2 = list_Cdr(l2)) {
      if (term_HasProperSuperterm(ToTopLevel, (TERM) list_Car(l2)) ||
	  (ToTopLevel == (TERM) list_Car(l2))) {
	arglist = list_PointerDeleteElementFree(arglist, list_Car(l1),
						(void (*)(POINTER))term_Delete);
	break;
      }
    }
    term_RplacArgumentList(targettoprove, arglist);
    /* Nothing left for the proof ? */
    if (list_Empty(term_ArgumentList(targettoprove))) {
      term_Delete(targettoprove);
      term_Delete(ToProveDef);
#ifdef CHECK
      fol_CheckFatherLinks(Target);
#endif
      return Target;
    }
  }
  else {
    /* Nothing left for the proof */
    term_Delete(targettoprove);
    term_Delete(ToProveDef);
#ifdef CHECK
    fol_CheckFatherLinks(Target);
#endif
    return Target;
  }

  /* Normalize variables in ToProveDef with respect to targettoprove */
  maxvar = term_MaxVar(targettoprove);
  symbol_SetStandardVarCounter(maxvar);
  vars = fol_BoundVariables(ToProveDef);
  vars = term_DeleteDuplicatesFromList(vars);
  for (l1=vars; !list_Empty(l1); l1=list_Cdr(l1))
    term_ExchangeVariable(ToProveDef, term_TopSymbol(list_Car(l1)), symbol_CreateStandardVariable());
  list_Delete(vars);
  
  /* Replace arguments of predicate in condition of definition by matching arguments
     of predicate in target term */
  for (l1=DefPredArgs, l2=TargetPredArgs; !list_Empty(l1); l1=list_Cdr(l1), l2=list_Cdr(l2)) 
    term_ReplaceVariable(ToProveDef, term_TopSymbol((TERM) list_Car(l1)), (TERM) list_Car(l2));

  targettoprove = term_Create(fol_Not(), list_List(targettoprove));
  targettoprove = cnf_NegationNormalFormula(targettoprove);
  targettoprove = term_Create(fol_Implies(), 
			      list_Cons(targettoprove, list_List(ToProveDef)));

  /* At this point ToProveDef must not be accessed again ! */
  
  /* Add all--quantifier to targettoprove */
  freevars = fol_FreeVariables(targettoprove);
  term_CopyTermsInList(freevars);
  targettoprove = fol_CreateQuantifier(fol_All(), freevars, list_List(targettoprove));
  
  if (flag_GetFlagValue(Flags, flag_PAPPLYDEFS)) {
    puts("\nConverted to :");
    fol_PrettyPrint(Target);
  }

  targettoprove = cnf_NegationNormalFormula(targettoprove);
  
  if (flag_GetFlagValue(Flags, flag_PAPPLYDEFS)) {
    puts("\nToProve for this target :");
    fol_PrettyPrint(targettoprove);
  }
 
  *LocallyTrue = cnf_HaveProof(list_Nil(), targettoprove, Flags, Precedence);
  
  term_Delete(targettoprove);

#ifdef CHECK
  fol_CheckFatherLinks(Target);
#endif

  return Target;
}


static TERM cnf_RemoveQuantFromPathAndFlatten(TERM TopTerm, TERM SubTerm)
/**********************************************************
  INPUT:  Two terms, <SubTerm> must be a subterm of <TopTerm>.
          Superterm of <SubTerm> must be an equivalence.
	  Along the path to SubTerm there are only quantifiers or disjunctions.
	  All free variables in the equivalence are free variables
	  in <SubTerm>.
	  All free variables in <SubTerm> are bound by a universal quantifier
	  (with polarity 1).
  RETURN: The destructively changed <TopTerm>.
  EFFECT: Removes all quantifiers not binding a variable in <SubTerm>
          from <subTerm>'s path.
          Moves all universal quantifiers binding free variable
	  in <SubTerm> up.
	  <TopTerm> is transformed into the form
	  forall([X1,...,Xn],or (equiv(<SubTerm>,psi),phi)).
**********************************************************/
{
  TERM Term1, Term2, Flat, Variable;
  LIST Scan1, Scan2, FreeVars;


#ifdef CHECK
  if (!fol_CheckFormula(TopTerm) || !term_HasPointerSubterm(TopTerm, SubTerm)) {
    misc_StartErrorReport();
    misc_ErrorReport("\nIn cnf_RemoveQuantFromPathAndFlatten: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  TopTerm = cnf_SimplifyQuantors(TopTerm);
  term_AddFatherLinks(TopTerm);
  Term1   = term_Superterm(SubTerm);

  while (Term1 != TopTerm) {

    while (symbol_Equal(fol_Or(), term_TopSymbol(Term1)) && (TopTerm != Term1)) {
      Term1 = term_Superterm(Term1);
    }
    if (fol_IsQuantifier(term_TopSymbol(Term1))) {
      Flat  = term_SecondArgument(Term1);
      Flat  = cnf_Flatten(Flat, fol_Or());
      Scan1 = fol_QuantifierVariables(Term1);
      while (!list_Empty(Scan1)) {
	Variable = (TERM)list_Car(Scan1);
	if (fol_VarOccursFreely(Variable, SubTerm)) {
	  Scan2 = list_Cdr(Scan1);
	  fol_DeleteQuantifierVariable(Term1, term_TopSymbol(list_Car(Scan1)));
	  Scan1 = Scan2;
	}
	else {
	  Scan1 = list_Cdr(Scan1);
	}
      }
      if (fol_IsQuantifier(term_TopSymbol(Term1))) {
	/* still variables, but not binding a variable in the equivalence term */
	LIST ArgList;

	term_RplacArgumentList(Flat, list_PointerDeleteOneElement(term_ArgumentList(Flat), SubTerm));
	ArgList = term_ArgumentList(Term1);
       	term_RplacArgumentList(Term1, list_Nil());
	Term2 = term_Create(term_TopSymbol(Term1), ArgList);
	term_RplacArgumentList(Term1, list_Cons(SubTerm, list_List(Term2)));
	term_RplacTop(Term1, fol_Or());
	Scan1 = term_ArgumentList(Term1); 
	while (!list_Empty(Scan1)) {
	  term_RplacSuperterm((TERM)list_Car(Scan1), Term1);
	  Scan1 = list_Cdr(Scan1);
	}
      }
    }
    else {

#ifdef CHECK
      if (!symbol_Equal(term_TopSymbol(Term1), fol_Or())) {
	misc_StartErrorReport();
	misc_ErrorReport("\nIn cnf_RemoveQuantFromPathAndFlatten: Illegal term Term1");
	misc_FinishErrorReport();
      }
#endif

      Term1 = cnf_Flatten(Term1, fol_Or());
    }
  }
  FreeVars = fol_FreeVariables(Term1);
  if (!list_Empty(FreeVars)) {
    term_CopyTermsInList(FreeVars);
    TopTerm = fol_CreateQuantifier(fol_All(), FreeVars, list_List(Term1));
  }
  return TopTerm;
}


TERM cnf_DefConvert(TERM Def, TERM FoundPredicate, TERM* ToProve)
/*********************************************************
  INPUT:   A term Def which is an equivalence (P(x1,..,xn) <=> Formula)
           that can be converted to standard form.
           The subterm that holds the defined predicate.
           A pointer to a term ToProve into which a term is stored
	   that has to be proved before applying the definition.
  RETURNS: The converted definition : forall([..], or(equiv(..,..), ..))
************************************************************/
{
  TERM orterm;

#ifdef CHECK
  fol_CheckFatherLinks(Def);
#endif
  
  Def = cnf_RemoveImplFromFormulaPath(Def, FoundPredicate);   /* Remove implications along the path */
  Def = cnf_NegationNormalFormulaPath(Def, FoundPredicate);   /* Move not's as far down as possible */

#ifdef CHECK
  if (!fol_CheckFormula(Def)) {
    misc_StartErrorReport();
    misc_ErrorReport("\nIn cnf_DefConvert: Illegal input Formula.\n");
    misc_FinishErrorReport();
  }
  if (!term_HasPointerSubterm(Def, FoundPredicate)) {
    misc_StartErrorReport();
    misc_ErrorReport("\nIn cnf_DefConvert: Illegal input SubTerm.\n");
    misc_FinishErrorReport();
  }
#endif

  Def = cnf_RemoveQuantFromPathAndFlatten(Def, term_Superterm(FoundPredicate));
  term_AddFatherLinks(Def);

#ifdef CHECK
  if (!fol_CheckFormula(Def)) {
    misc_StartErrorReport();
    misc_ErrorReport("\nIn cnf_DefConvert: Illegal term Def.");
    misc_FinishErrorReport();
  }
  if (!term_HasPointerSubterm(Def, FoundPredicate)) {
    misc_StartErrorReport();
    misc_ErrorReport("\nIn cnf_DefConvert: Illegal term FoundPredicate.");
    misc_FinishErrorReport();
  }
#endif

  /* Find top level or() */
  if (symbol_Equal(term_TopSymbol(Def), fol_All())) {
    /* Make sure there are several arguments */
    if (symbol_Equal(term_TopSymbol(term_SecondArgument(Def)), fol_Or()) &&
	(list_Length(term_ArgumentList(term_SecondArgument(Def))) == 1)) {
      TERM t;
      t = term_SecondArgument(Def);
      term_RplacSecondArgument(Def, term_FirstArgument(term_SecondArgument(Def)));
      term_Free(t);
      orterm = NULL;
      term_RplacSuperterm(term_SecondArgument(Def), Def);
    }
    else 
      orterm = term_SecondArgument(Def);
  }
  else {
    /* Make sure there are several arguments */
    if (symbol_Equal(term_TopSymbol(Def), fol_Or()) &&
	(list_Length(term_ArgumentList(Def)) == 1)) {
      TERM t;
      t = Def;
      Def = term_FirstArgument(Def);
      term_Free(t);
      orterm = NULL;
      term_RplacSuperterm(term_SecondArgument(Def), Def);
    }
    else 
      orterm = Def;
  }

  /* If there is something to prove */
  if (orterm != (TERM) NULL) {
    TERM equiv;
    LIST args;

    equiv = (TERM) NULL;

    /* In pell 10 there are no conditions for the equivalence */
    if (symbol_Equal(term_TopSymbol(orterm), fol_Equiv())) {
      equiv = orterm;
      *ToProve = NULL;
    }
    else {
      TERM t;
      /* First find equivalence term among arguments */
      args  = term_ArgumentList(orterm);
      equiv = term_Superterm(FoundPredicate);
      
      /* Delete equivalence from list */
      args = list_PointerDeleteElement(args, equiv);
      term_RplacArgumentList(orterm, args);
      
      /* ToProve consists of all the definitions arguments except the equivalence */
      *ToProve = term_Copy(orterm);
      
      /* Now not(*ToProve) implies the equivalence */
      /* Negate *ToProve */
      *ToProve = term_Create(fol_Not(), list_List(*ToProve));
      *ToProve = cnf_NegationNormalFormula(*ToProve);
      term_AddFatherLinks(*ToProve);

      /* Now convert definition to implication form */
      term_RplacTop(orterm, fol_Implies());
      t = term_Create(fol_Not(), 
		      list_List(term_Create(fol_Or(), 
					    term_ArgumentList(orterm))));
      term_RplacArgumentList(orterm, list_Cons(t, list_List(equiv)));

      Def = cnf_NegationNormalFormula(Def);
      term_AddFatherLinks(Def);
    }    
  }
  
#ifdef CHECK
  fol_CheckFatherLinks(Def);
#endif
  return Def;
}


LIST cnf_HandleDefinition(PROOFSEARCH Search, LIST Pair, LIST Axioms,
			  LIST Sorts, LIST Conjectures)
/*******************************************************************
  INPUT:   A PROOFSEARCH object, a pair (label, term) and 3 lists of pairs.
           If the term in pair is a definition, the defined predicate
	   is expanded in all the lists
           and added to the proofsearch object.
  RETURNS: The pair with the converted definition:
           forall([..], or(equiv(..,..), .......))
********************************************************************/
{
  TERM definition, defpredicate, equivterm;
  
  BOOL alwaysapplicable;     /* Is set to TRUE iff the definition can always be applied */
  FLAGSTORE Flags;
  PRECEDENCE Precedence;

  Flags      = prfs_Store(Search);
  Precedence = prfs_Precedence(Search);

  /* The axiomlist consists of (label, formula) pairs */
  definition = list_PairSecond(Pair);
  
  /* Test if Definition contains a definition */
  defpredicate = (TERM) NULL;
  if (cnf_ContainsDefinition(definition, &defpredicate)) { 
    TERM toprove;
    LIST allformulae, scan;

    /* Create list of all formula pairs */
    /* Check if definition may be applied to each formula */
    allformulae = list_Copy(Axioms);
    allformulae = list_Nconc(allformulae, list_Copy(Sorts));
    allformulae = list_Nconc(allformulae, list_Copy(Conjectures));
#ifdef CHECK
    for (scan=allformulae; !list_Empty(scan); scan=list_Cdr(scan)) {
      if (!list_Empty((LIST) list_Car(scan))) {
	if (!term_IsTerm((TERM) list_PairSecond((LIST) list_Car(scan))))
	  fol_CheckFatherLinks((TERM) list_PairSecond((LIST) list_Car(scan)));
      }
    }
#endif
    
    /* Convert definition to standard form */
    if (flag_GetFlagValue(Flags, flag_PAPPLYDEFS)) {
      fputs("\nPredicate : ", stdout);
      symbol_Print(term_TopSymbol(defpredicate));
    }

    definition = cnf_DefConvert(definition, defpredicate, &toprove);
    if (toprove == NULL)
      alwaysapplicable = TRUE;
    else 
      alwaysapplicable = FALSE;

    prfs_SetDefinitions(Search, list_Cons(term_Copy(definition), 
					  prfs_Definitions(Search)));
    
    if (flag_GetFlagValue(Flags, flag_PAPPLYDEFS)) {
      if (alwaysapplicable) {
	fputs("\nAlways Applicable     : ", stdout);
	fol_PrettyPrint(definition); 
      } 
    }

    /* Definition is converted to a form where the equivalence is
       the first argument of the disjunction */
    equivterm     = term_SecondArgument(term_Superterm(defpredicate));
    
    
    scan = allformulae;
    while (!list_Empty(scan)) {
      BOOL localfound;
      LIST pair, targettermvars;
      
      /* Pair label / term */
      pair = list_Car(scan);

      /* Pair may be NULL if it is a definition that could be deleted */
      if ((pair != NULL) && (definition != (TERM) list_PairSecond(pair))) {
	TERM target, targetpredicate, totoplevel;
	LIST varsfortoplevel;
	target = (TERM) list_PairSecond(pair);
	targettermvars = varsfortoplevel = list_Nil();
	
	/* If definition is not always applicable, check if it is applicable
	   for this formula */
	localfound = FALSE;
	if (!alwaysapplicable) {
	  if (cnf_ContainsPredicate(target, term_TopSymbol(defpredicate),
				    &targetpredicate, &totoplevel,
				    &targettermvars, &varsfortoplevel)) {
	    TERM toprovecopy;
	    toprovecopy = term_Copy(toprove);
	    target = cnf_DefTargetConvert(target, totoplevel, toprovecopy,
					  term_ArgumentList(defpredicate),
					  term_ArgumentList(targetpredicate),
					  targettermvars, varsfortoplevel,
					  Flags, Precedence, &localfound);
	    list_Delete(targettermvars);
	    list_Delete(varsfortoplevel);
	    targettermvars = varsfortoplevel = list_Nil();
	    
	    list_Rplacd(pair, (LIST) target);
	    if (localfound)
	      list_Rplacd(pair, 
			  (LIST) cnf_ApplyDefinitionOnce(defpredicate, 
							 equivterm,
							 list_PairSecond(pair),
							 targetpredicate,
							 Flags));
	  }
	}
	else {
	  if (cnf_ContainsPredicate(target, term_TopSymbol(defpredicate), 
				    &targetpredicate, &totoplevel,
				    &targettermvars, &varsfortoplevel))
	    list_Rplacd(pair, (LIST) cnf_ApplyDefinitionOnce(defpredicate, 
							     equivterm,
							     list_PairSecond(pair),
							     targetpredicate,
							     Flags));
	  else
	    scan = list_Cdr(scan);
	  list_Delete(targettermvars);
	  list_Delete(varsfortoplevel);
	  targettermvars = varsfortoplevel = list_Nil();
	}
      }
      else
	scan = list_Cdr(scan);
    }
    list_Delete(allformulae);
    /* toprove can be NULL if the definition can always be applied */
    if (toprove != (TERM) NULL)
      term_Delete(toprove);
    list_Rplacd(Pair, (LIST) definition);
  }
 
  return Pair;
}


LIST cnf_ApplyDefinitionToClause(CLAUSE Clause, TERM Predicate, TERM Expansion,
				 FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A clause, two terms and a flag store and a precedence.
  RETURNS: The list of clauses where each occurrence of Predicate is 
           replaced by Expansion.
***************************************************************/
{
  NAT  i;
  BOOL changed;
  LIST args, scan, symblist;
  TERM clauseterm, argument;

  changed = FALSE;
  
  /* Build term from clause */
  args = list_Nil();
  for (i = 0; i < clause_Length(Clause); i++) {
    argument = clause_GetLiteralTerm(Clause, i); /* with sign */
    args     = list_Cons(term_Copy(argument), args);
  }
  clauseterm = term_Create(fol_Or(), args);

  for (scan=term_ArgumentList(clauseterm); !list_Empty(scan); scan=list_Cdr(scan)) {
    BOOL isneg;

    argument = (TERM) list_Car(scan);
    if (symbol_Equal(term_TopSymbol(argument), fol_Not())) {
      argument = term_FirstArgument(argument);
      isneg = TRUE;
    }
    else 
      isneg = FALSE;
      
    /* Try to match with predicate */
    cont_StartBinding();
    if (unify_Match(cont_LeftContext(), Predicate, argument)) {
      SUBST subst;
      TERM  newargument;
      subst = subst_ExtractMatcher();
      newargument = subst_Apply(subst, term_Copy(Expansion));
      subst_Free(subst);
      if (isneg)
	newargument = term_Create(fol_Not(), list_List(newargument));
      term_Delete((TERM) list_Car(scan));
      list_Rplaca(scan, newargument);
      changed = TRUE;
    }      
    cont_BackTrack();
  }

  if (changed) {
    /* Build term and derive list of clauses */
    LIST result;
    if (flag_GetFlagValue(Flags, flag_PAPPLYDEFS)) {
      puts("\nClause before applying def :");
      clause_Print(Clause);
      puts("\nPredicate :");
      fol_PrettyPrint(Predicate);
      puts("\nExpansion :");
      fol_PrettyPrint(Expansion);
    }
    symblist   = list_Nil();
    clauseterm = cnf_Cnf(clauseterm, Precedence, &symblist);
    result     = cnf_MakeClauseList(clauseterm,FALSE,FALSE,Flags,Precedence);
    list_Delete(symblist);
    term_Delete(clauseterm);
    if (flag_GetFlagValue(Flags, flag_PAPPLYDEFS)) {
      LIST l;
      puts("\nClauses derived by expanding definition :");
      for (l = result; !list_Empty(l); l=list_Cdr(l)) {
	clause_Print((CLAUSE) list_Car(l));
	fputs("\n", stdout);
      }
    }
    return result;
  }
  else {
    term_Delete(clauseterm);
    return list_Nil();
  }
}


BOOL cnf_PropagateSubstEquations(TERM StartTerm)
/*************************************************************
  INPUT:   A term where we assume that father links are established and
           that no variable is bound by more than one quantifier.
  RETURNS: TRUE, if any substitutions were made, FALSE otherwise.
  EFFECT:  Function looks for equations of the form x=t where x does not
           occur in t. If x=t occurs negatively and disjunctively below
	   a universal quantifier binding x or if x=t occurs positively and
	   conjunctively below an existential quantifier binding x,
           all occurrences of  x are replaced by t in <StartTerm>.
**************************************************************/
{
  LIST   Subequ;
  TERM   QuantorTerm, Equation, EquationTerm;
  SYMBOL Variable;
  BOOL   Hit, Substituted;

#ifdef CHECK
  if (fol_VarBoundTwice(StartTerm)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In cnf_PropagateSubstEquations: Variables of");
    misc_ErrorReport("\n input term are not normalized.");
    misc_FinishErrorReport();
  }
#endif

  Substituted = FALSE;

  Subequ = fol_GetSubstEquations(StartTerm);
  for ( ; !list_Empty(Subequ); Subequ = list_Pop(Subequ)) {
    Hit          = FALSE;
    Equation     = list_Car(Subequ);
    Variable     = symbol_Null();
    QuantorTerm  = term_Null();
    EquationTerm = term_Null();

    if (term_IsVariable(term_FirstArgument(Equation)) &&
	!term_ContainsVariable(term_SecondArgument(Equation),
			       term_TopSymbol(term_FirstArgument(Equation)))) {

      Variable     = term_TopSymbol(term_FirstArgument(Equation));
      QuantorTerm  = fol_GetBindingQuantifier(Equation, Variable);
      EquationTerm = term_SecondArgument(Equation);
      Hit          = fol_PolarCheck(Equation, QuantorTerm);
    }
    if (!Hit && term_IsVariable(term_SecondArgument(Equation)) &&
	!term_ContainsVariable(term_FirstArgument(Equation),
			       term_TopSymbol(term_SecondArgument(Equation)))) {

      Variable     = term_TopSymbol(term_SecondArgument(Equation));
      QuantorTerm  = fol_GetBindingQuantifier(Equation, Variable);
      EquationTerm = term_FirstArgument(Equation);
      Hit          = fol_PolarCheck(Equation, QuantorTerm);
    }
    if (Hit) {
      fol_DeleteQuantifierVariable(QuantorTerm,Variable);
      term_ReplaceVariable(StartTerm, Variable, EquationTerm); /* We replace everythere ! */
      term_AddFatherLinks(StartTerm);
      if (symbol_Equal(term_TopSymbol(QuantorTerm),fol_Equality())) /* Trivial Formula */
	fol_SetTrue(QuantorTerm);
      else
	fol_SetTrue(Equation);
      Substituted = TRUE;
    }   
  }

  /* <Subequ> was freed in the loop. */

  return Substituted;
}
