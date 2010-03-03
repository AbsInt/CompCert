/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                       DEFINITIONS                      * */
/* *                                                        * */
/* *  $Module:   DEFS                                       * */ 
/* *                                                        * */
/* *  Copyright (C) 1998, 1999, 2000, 2001                  * */
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

#include "cnf.h"
#include "defs.h"
#include "foldfg.h"

static void def_DeleteFromClauses(DEF);
static void def_DeleteFromTerm(DEF);

DEF def_CreateFromClauses(TERM ExpTerm, TERM PredTerm, LIST Clauses, LIST Lits,
			  BOOL Con)
/**********************************************************
  INPUT:   Two terms, a list of clausenumbers, a list of literal indices and
           a boolean saying whether all clauses derived by expanding the 
	   predicate should be conclauses.
  RETURNS: A definition consisting of the 2 terms as expansion term and
           predicate term and the list of parent clause numbers and a list
	   of the indices of the defined predicate in the parent clauses.
	   ToProve and label are set to NULL.
********************************************************/
{
  DEF  result;

#ifdef CHECK
  if (!term_IsTerm(ExpTerm) || !term_IsTerm(PredTerm)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In def_CreateFromClause: Illegal input.");
    misc_FinishErrorReport();
  }
  if (list_Empty(Clauses)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In def_CreateFromClause: No parent clause given.");
    misc_FinishErrorReport();
  }
#endif

  result                   = (DEF) memory_Malloc(sizeof(DEF_NODE));
  result->expansion        = ExpTerm;
  result->predicate        = PredTerm;
  result->toprove          = (TERM) NULL;
  result->parentclauses    = list_PairCreate(Clauses, Lits);
  result->label            = (const char*) NULL;
  result->conjecture       = Con;

  return result;
}

DEF def_CreateFromTerm(TERM ExpTerm, TERM PredTerm, TERM ToProve, const char* Label)
/**********************************************************
  INPUT:   3 terms and a term label.
  RETURNS: A definition consisting of the 3 terms as expansion term,
           predicate term and term to prove before applying the 
	   definition and the label of the parent term.
	   The list of clausenumbers is set to NULL.
********************************************************/
{
  DEF  result;

#ifdef CHECK
  if (!term_IsTerm(ExpTerm) || !term_IsTerm(PredTerm)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In def_CreateFromTerm: Illegal input.");
    misc_FinishErrorReport();
  }  
  if (Label ==  NULL) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In def_CreateFromTerm: No parent clause given.");
    misc_FinishErrorReport();
  }
#endif

  result                   = (DEF) memory_Malloc(sizeof(DEF_NODE));
  result->expansion        = ExpTerm;
  result->predicate        = PredTerm;
  result->toprove          = ToProve;
  result->parentclauses    = list_PairCreate(list_Nil(), list_Nil());
  result->label            = Label;
  result->conjecture       = FALSE;

  return result;
}

static void def_DeleteFromClauses(DEF D) 
/**********************************************************
  INPUT:   A definition derived from clauses.
  EFFECT:  The definition is deleted, INCLUDING THE TERMS AND
           THE LIST OF CLAUSE NUMBERS.
********************************************************/  
{
#ifdef CHECK
  if (!term_IsTerm(def_Expansion(D)) || !term_IsTerm(def_Predicate(D))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In def_DeleteFormClauses: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  /* ToProve and Label are NULL */
  term_Delete(def_Expansion(D));
  term_Delete(def_Predicate(D));
  list_Delete(def_ClauseNumberList(D));
  list_Delete(def_ClauseLitsList(D));
  list_PairFree(D->parentclauses);

  memory_Free(D, sizeof(DEF_NODE));
}

static void def_DeleteFromTerm(DEF D) 
/**********************************************************
  INPUT:   A definition derived from a term.
  EFFECT:  The definition is deleted, INCLUDING THE TERMS.
           THE LABEL IS NOT FREED.
********************************************************/  
{
#ifdef CHECK
  if (!term_IsTerm(def_Expansion(D)) || !term_IsTerm(def_Predicate(D))) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In def_DeleteFromTerm: Illegal input.");
    misc_FinishErrorReport();
  }
#endif

  /* List of clausenumbers is NULL */
  term_Delete(def_Expansion(D));
  term_Delete(def_Predicate(D));
  if (def_ToProve(D) != (TERM) NULL)
    term_Delete(def_ToProve(D));
  list_PairFree(D->parentclauses);
  memory_Free(D, sizeof(DEF_NODE));
}

void def_Delete(DEF D)
/**********************************************************
  INPUT:   A definition derived from a term.
  EFFECT:  The definition is deleted.
  CAUTION: All elements of the definition except of the label are freed.
********************************************************/  
{
  if (!list_Empty(def_ClauseNumberList(D)))
    def_DeleteFromClauses(D);
  else
    def_DeleteFromTerm(D);
}

int def_PredicateOccurrences(TERM Term, SYMBOL P)
/****************************************************
  INPUT:   A term and a predicate symbol.
  RETURNS: The number of occurrences of the predicate symbol in Term
**************************************************/			       
{
  /* Quantifiers */
  if (fol_IsQuantifier(term_TopSymbol(Term)))
    return def_PredicateOccurrences(term_SecondArgument(Term), P);

  /* Junctors and NOT */
  if (fol_IsJunctor(term_TopSymbol(Term)) ||
      symbol_Equal(term_TopSymbol(Term),fol_Not())){
    LIST scan;
    int count;
    count = 0;
    for (scan=term_ArgumentList(Term); !list_Empty(scan); scan=list_Cdr(scan)) {
      count += def_PredicateOccurrences((TERM) list_Car(scan), P);
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

LIST def_ExtractDefsFromTerm(TERM Term, const char* Label) 
/**************************************************************
  INPUT:   A term and its label.
  RETURNS: A list of definitions found in the term.
  NOTE:    The Term is not changed, the definitions contain copies.
***************************************************************/
{
  TERM andterm;
  BOOL found;
  int  pol;
  LIST univars, termlist, defslist, scan;
  
  /* First check if there is a top level and() so that the Term may
     contain several definitions */

  andterm = Term;
  found   = FALSE;
  pol     = 1;
  univars = list_Nil();

  /* Traverse top down universal quantifiers */
  while (!found) {
    if ((symbol_Equal(term_TopSymbol(andterm), fol_All()) && (pol == 1))
	|| (symbol_Equal(term_TopSymbol(andterm), fol_Exist()) && (pol == -1))) {
      univars = list_Nconc(univars, list_Copy(fol_QuantifierVariables(andterm)));
      andterm = term_SecondArgument(andterm);
    }
    else {
      if (symbol_Equal(term_TopSymbol(andterm), fol_Not())) {
	pol = -pol;
	andterm = term_FirstArgument(andterm);
      }
      else
	found = TRUE;
    }
  }

  termlist = list_Nil();
  /* Check if conjunction was found */
  if ((symbol_Equal(term_TopSymbol(andterm), fol_And()) && (pol == 1))
      || (symbol_Equal(term_TopSymbol(andterm), fol_Or()) && (pol == -1))) {
    LIST l;
    /* Flatten nested and/or */
    /* Make copy of relevant subterm */
    andterm = cnf_Flatten(term_Copy(andterm), term_TopSymbol(andterm));
    for (l=term_ArgumentList(andterm); !list_Empty(l); l=list_Cdr(l)) {
      TERM newterm;
      newterm = fol_CreateQuantifierAddFather(fol_All(), term_CopyTermList(univars),
					      list_List(list_Car(l)));
      termlist = list_Cons(newterm, termlist);
    }
    /* Arguments are used in new terms */
    list_Delete(term_ArgumentList(andterm));
    term_Free(andterm);
  }
  else
    termlist = list_List(term_Copy(Term));
  
  list_Delete(univars);

  /* Now we have a list of terms that may contain definitions */
  defslist = list_Nil();
  for (scan=termlist; !list_Empty(scan); scan=list_Cdr(scan)) {
    TERM cand;
    TERM foundpred, toprove;

    /* Candidate from list */
    cand = (TERM) list_Car(scan);
    term_AddFatherLinks(cand);

    if (cnf_ContainsDefinition(cand, &foundpred)) {
      DEF def;
#ifdef CHECK
      if (!fol_CheckFormula(cand)) {
	misc_StartErrorReport();
	misc_ErrorReport("\n In def_ExtractDefsFromTerm: Illegal term cand");
	misc_FinishErrorReport();
      }
#endif
      cand = cnf_DefConvert(cand, foundpred, &toprove);
#ifdef CHECK
      if (!fol_CheckFormula(cand)) {
	misc_StartErrorReport();
	misc_ErrorReport("\n In def_ExtractDefsFromTerm: Illegal term cand");
	misc_FinishErrorReport();
      }
#endif
      def  = def_CreateFromTerm(term_Copy(term_SecondArgument(term_Superterm(foundpred))), 
				term_Copy(foundpred), toprove, Label);

      if (def_PredicateOccurrences(cand, term_TopSymbol(foundpred)) > 1)
	def_RemoveAttribute(def, PREDOCCURONCE);
      else 
	def_AddAttribute(def, PREDOCCURONCE);
      if (symbol_Equal(term_TopSymbol(foundpred), fol_Equality()))
	def_AddAttribute(def, ISEQUALITY);
      else
	def_RemoveAttribute(def, ISEQUALITY);

      defslist = list_Cons(def, defslist);
    }
    term_Delete(cand);
  }
  
  list_Delete(termlist);
  return defslist;
}

void def_ExtractDefsFromClauselist(PROOFSEARCH Search, LIST Clauselist)
/**************************************************************
  INPUT:   A proofsearch object and a list of clauses
  RETURNS: Nothing.
  EFFECT:  The definitions found in the clauselist object are stored in
           the proofsearch object.
  NOTE:    The clause list is not changed.
           The old list of definitions in the proofsearch object is 
	   overwritten.
***************************************************************/
{
  LIST       scan, defslist;
  FLAGSTORE  FlagStore;
  PRECEDENCE Precedence;

  defslist   = list_Nil();
  FlagStore  = prfs_Store(Search);
  Precedence = prfs_Precedence(Search);

  for (scan=Clauselist; !list_Empty(scan); scan=list_Cdr(scan)) {
    CLAUSE Clause;
    NAT index;
    LIST pair;

    Clause = (CLAUSE) list_Car(scan);
    /* Check if clause contains a predicate that may be part of a definition */
    if (clause_ContainsPotPredDef(Clause, FlagStore, Precedence, &index, &pair)) {
      LIST l, compl, compllits;
      BOOL done;

      compl = compllits = list_Nil();
      done = FALSE;
      
      /* Search for complement clauses */
      for (l=Clauselist; !list_Empty(l) && !done; l=list_Cdr(l)) {
	int predindex;
	if (clause_IsPartOfDefinition((CLAUSE) list_Car(l), 
				      clause_GetLiteralTerm(Clause, index), 
				      &predindex, pair)) {
	  compl     = list_Cons(list_Car(l), compl);
	  compllits = list_Cons((POINTER) predindex, compllits);
	  
	  if (list_Empty(list_PairFirst(pair)) &&
	      list_Empty(list_PairSecond(pair)))
	    done = TRUE;
	}
      }
      
      /* All complements found ? */ 
      if (done) {
	LIST l2, clausenumbers, args;
	DEF  def;
	NAT  i;
	TERM defterm, predterm;
	BOOL con;

	clausenumbers = list_Nil();
	con           = clause_GetFlag(Clause, CONCLAUSE);

	for (l2=compl; !list_Empty(l2); l2=list_Cdr(l2)) {
	  clausenumbers = list_Cons((POINTER) clause_Number((CLAUSE) list_Car(l2)), 
				    clausenumbers);	    
	  if (clause_GetFlag((CLAUSE) list_Car(l2), CONCLAUSE))
	    con = TRUE;
	}
	clausenumbers = list_Cons((POINTER) clause_Number(Clause), 
				  clausenumbers);
	compllits = list_Cons((POINTER) index, compllits);

	/* Build definition term */
	predterm = term_Copy(clause_GetLiteralTerm(Clause, index));
	args     = list_Nil();
	for (i = 0; i < clause_Length(Clause); i++) 
	  if (i != index)
	    args = list_Cons(term_Copy(clause_GetLiteralTerm(Clause, i)), args);
	defterm  = term_CreateAddFather(fol_Or(), args);
	/* The expansion is negative here, so it must be inverted */
	defterm  = term_Create(fol_Not(), list_List(defterm));
	defterm  = cnf_NegationNormalFormula(defterm);
	def      = def_CreateFromClauses(defterm, predterm, clausenumbers, compllits, con);
	defslist = list_Cons(def, defslist);
	if (flag_GetFlagValue(FlagStore, flag_PAPPLYDEFS)) {
	  fputs("\nNew definition found :", stdout);
	  def_Print(def);
	}
      }
      else {
	list_Delete(compllits);
	list_Delete(list_PairSecond(pair));
	list_Delete(list_PairFirst(pair));
      }
      list_Delete(compl);
      list_PairFree(pair);
    }
  }

  if (flag_GetFlagValue(FlagStore, flag_PAPPLYDEFS)) {
    if (!list_Empty(defslist)) {
      fputs("\nFound definitions :\n", stdout);
      for (scan = defslist; !list_Empty(scan); scan = list_Cdr(scan)) {
	def_Print((DEF) list_Car(scan));
	fputs("\n---\n", stdout);
      }
    }
  }

  for (scan=defslist; !list_Empty(scan); scan=list_Cdr(scan))
    symbol_AddProperty(term_TopSymbol(def_Predicate((DEF) list_Car(scan))), ISDEF);
  
  prfs_SetDefinitions(Search, list_Nconc(prfs_Definitions(Search), defslist));
}

TERM def_ApplyDefToTermOnce(DEF Def, TERM Term, FLAGSTORE FlagStore,
			    PRECEDENCE Precedence, BOOL* Complete)
/**************************************************************
  INPUT:   A DEF structure, a term and a boolean that is set
           to TRUE if no occurrences of the defined predicate
	   remain in the term. A flag store and a precedence.
  RETURNS: A term where all occurrences of the definitions
           predicate are expanded if possible.
  NOTE:    The Term is not changed.
***************************************************************/
{
  TERM newtarget, oldtarget, targetpredicate, totoplevel, toprove;
  LIST targettermvars, varsfortoplevel;
  BOOL applicable;

  oldtarget = Term;
  *Complete = TRUE;

  while (TRUE) {
    newtarget = term_Copy(oldtarget);
    term_AddFatherLinks(newtarget);
    targettermvars = varsfortoplevel = list_Nil();

    if (cnf_ContainsPredicate(newtarget, term_TopSymbol(def_Predicate(Def)),
			      &targetpredicate, &totoplevel, &targettermvars, 
			      &varsfortoplevel)) {
      *Complete  = FALSE;
      applicable = FALSE;
      /* Check if definition is not always applicable */
      if (term_Equal(def_ToProve(Def), term_Null())) { 
	applicable = TRUE;
	newtarget = cnf_ApplyDefinitionOnce(def_Predicate(Def), term_Copy(def_Expansion(Def)),
					 newtarget, targetpredicate, FlagStore);
	if (oldtarget != Term)
	  term_Delete(oldtarget);
	oldtarget = newtarget;
      	list_Delete(targettermvars);
	list_Delete(varsfortoplevel); 	
      }
      else {
	toprove = term_Copy(def_ToProve(Def));
	newtarget = cnf_DefTargetConvert(newtarget, totoplevel, toprove,
					 term_ArgumentList(def_Predicate(Def)),
					 term_ArgumentList(targetpredicate),
					 targettermvars, varsfortoplevel,
					 FlagStore, Precedence,
					 &applicable);
	list_Delete(targettermvars);
	list_Delete(varsfortoplevel); 	
	if (applicable) {
	  newtarget = cnf_ApplyDefinitionOnce(def_Predicate(Def), term_Copy(def_Expansion(Def)),
					   newtarget, targetpredicate, FlagStore);
	  if (oldtarget != Term)
	    term_Delete(oldtarget);
	  oldtarget = newtarget;
	}
	else {
	  /* Predicate still exists but cannot be expanded */
	  term_Delete(newtarget);
	  if (oldtarget == Term)
	    return NULL;
	  else {
	    oldtarget = cnf_ObviousSimplifications(oldtarget);
	    return oldtarget;
	  }
	}
      }
    }
    else {
      *Complete = TRUE;
      /* Predicate does no longer exist */
      term_Delete(newtarget);
      /* No expansion possible */
      if (oldtarget == Term)
	return NULL;
      else {
	oldtarget = cnf_ObviousSimplifications(oldtarget);
	return oldtarget;
      }
    }
  }
  return NULL; /* Unreachable */
}
    
TERM def_ApplyDefToTermExhaustive(PROOFSEARCH Search, TERM Term)
/**************************************************************
  INPUT:   A proofsearch object and a term.
  RETURNS: An expanded term.
  NOTE:    All occurences of defined predicates are expanded in the term,
           until no further changes are possible.
  CAUTION: If cyclic definitions exist, this will crash.
***************************************************************/
{
  TERM       oldterm, newterm;
  BOOL       done, complete;
  FLAGSTORE  FlagStore;
  PRECEDENCE Precedence;

  done       = FALSE;
  oldterm    = Term;
  FlagStore  = prfs_Store(Search);
  Precedence = prfs_Precedence(Search);

  while (!done) {
    LIST l;
    done = TRUE;
    /* Apply all definitions to term until no more changes occur */
    for (l=prfs_Definitions(Search); !list_Empty(l); l=list_Cdr(l)) {
      newterm = def_ApplyDefToTermOnce((DEF) list_Car(l), oldterm,
				       FlagStore, Precedence, &complete);
      if (newterm != NULL) {
	if (oldterm != Term)
	  term_Delete(oldterm);
	oldterm = newterm;
	done = FALSE;
      }
    }
  }
  if (oldterm == Term)
    return NULL;
  else
    return oldterm;
}

LIST def_ApplyDefToClauseOnce(DEF Def, CLAUSE Clause,
			      FLAGSTORE FlagStore, PRECEDENCE Precedence)
/**************************************************************
  INPUT:   A DEF structure, a clause, a flag store and a
           precedence.
  RETURNS: A list of new clauses.
  NOTE:    The clause is not changed.
           All occurences of the defined predicate are expanded
	   in the clause and in the derived clauses.
***************************************************************/
{
  LIST result, l;
  
  result = list_List(Clause);

  for (l = result; !list_Empty(l); l = list_Cdr(l)) {
    if (clause_ContainsSymbol((CLAUSE) list_Car(l), 
			      term_TopSymbol(def_Predicate(Def)))) {
      result = list_Nconc(result, 
			  cnf_ApplyDefinitionToClause((CLAUSE) list_Car(l), 
						      def_Predicate(Def),
						      def_Expansion(Def),
						      FlagStore, Precedence));
      /* Remove temporary clause */
      if ((CLAUSE) list_Car(l) != Clause)
	clause_Delete((CLAUSE) list_Car(l));
      list_Rplaca(l, NULL);
    }
  }
  result = list_PointerDeleteElement(result, NULL);

  /* Make sure the original clause is no longer in the list */
  if (!list_Empty(result))
    if (list_First(result) == Clause)
      result = list_Pop(result);
  
  for (l = result; !list_Empty(l); l=list_Cdr(l)) {
    CLAUSE c;
    c = (CLAUSE) list_Car(l);
    if (def_Conjecture(Def))
      clause_SetFlag((CLAUSE) list_Car(l), CONCLAUSE);
    clause_SetFromDefApplication(c);
    clause_SetParentClauses(c, list_Cons((POINTER) clause_Number(Clause), 
					 list_Copy(def_ClauseNumberList(Def))));
    /* Parent literal is not available, as the predicate may occur several 
       times in the target clause */
    clause_SetParentLiterals(c, list_Cons((POINTER) 0, 
					  list_Copy(def_ClauseLitsList(Def))));
  }
  return result;
}

LIST def_ApplyDefToClauseExhaustive(PROOFSEARCH Search, CLAUSE Clause)
/**************************************************************
  INPUT:   A proofsearch object and a clause.
  RETURNS: A list of derived clauses.
  NOTE:    All occurences of defined predicates are expanded in the clause.
           until no further changes are possible.
  CAUTION: If cyclic definitions exist, this will crash.
***************************************************************/
{
  LIST       newclauses, scan, result;
  CLAUSE     orig;
  FLAGSTORE  FlagStore;
  PRECEDENCE Precedence;

  orig       = clause_Copy(Clause);
  newclauses = list_List(orig);
  result     = list_Nil();
  FlagStore  = prfs_Store(Search);
  Precedence = prfs_Precedence(Search);

  while (!list_Empty(newclauses)) {
    /* Check all clauses */
    LIST l, nextlist;

    /* List of clauses derived from newclauses by expanding predicates */
    nextlist = list_Nil();

    for (l=newclauses; !list_Empty(l); l=list_Cdr(l)) {
      LIST clauses;
      CLAUSE c;
      
      c = (CLAUSE) list_Car(l);

      /* Apply all definitions to the clause */

      /* List of clauses derived from one clause in newclauses by */
      /* expanding all possible predicates */
      clauses  = list_Nil();

      for (scan=prfs_Definitions(Search); !list_Empty(scan); scan=list_Cdr(scan))
	clauses = list_Nconc(clauses, def_ApplyDefToClauseOnce((DEF) list_Car(scan), c, FlagStore, Precedence));
      
      /* If expansions were made delete old clause */
      if (!list_Empty(clauses)) {
	/* DOCPROOF ? */
	if (c != Clause) {
	  if (flag_GetFlagValue(FlagStore, flag_DOCPROOF)) {
	    prfs_InsertDocProofClause(Search, c);
	  }
	  else
	    clause_Delete(c);
	}
	nextlist = list_Nconc(nextlist, clauses);
      }
      else {
	/* No more expansions possible for this clause */
	/* If it is not the original clause, add it to the result list */
	if (c != Clause)
	  result = list_Cons(c, result);
      }
    }
    list_Delete(newclauses);
    newclauses = nextlist;
  }
      
  return result;
}
  

void def_Print(DEF D)
/**************************************************************
  INPUT:   A DEF structure.
  RETURNS: None.
  EFFECT:  Prints the definition to stdout. 
***************************************************************/
{
  LIST scan, scan2;
  fputs("\n\nAtom: ", stdout);
  fol_PrettyPrint(def_Predicate(D));
  fputs("\nExpansion: \n", stdout);
  fol_PrettyPrint(def_Expansion(D));
  if (!list_Empty(def_ClauseNumberList(D))) {
    fputs("\nParent clauses: ", stdout);
    for (scan = def_ClauseNumberList(D), scan2 = def_ClauseLitsList(D); 
	 !list_Empty(scan); scan = list_Cdr(scan), scan2 = list_Cdr(scan2)) 
      printf("%d.%d ", (NAT) list_Car(scan), (NAT) list_Car(scan2));
    if (D->conjecture)
      fputs("\nDerived from conjecture clauses.", stdout);
    else
      fputs("\nNot derived from conjecture clauses.", stdout);
  }
  else {
    fputs("\nLabel: ", stdout);
    fputs(def_Label(D), stdout);
    puts("\nGuard:");
    if (def_ToProve(D) != NULL) 
      fol_PrettyPrint(def_ToProve(D));
    else
      fputs("Nothing.", stdout);
  }

  fputs("\nAttributes: ", stdout);
  if (def_HasAttribute(D, ISEQUALITY) || def_HasAttribute(D, PREDOCCURONCE)) {
    if (def_HasAttribute(D, ISEQUALITY))
      fputs(" Equality ", stdout);
    if (def_HasAttribute(D, PREDOCCURONCE))
      fputs(" No Multiple Occurrences ", stdout);
  }
  else {
    fputs(" None ", stdout);
  }    
} 

LIST def_ApplyDefToClauselist(PROOFSEARCH Search, DEF Def, 
			      LIST Clauselist, BOOL Destructive)
/**************************************************************
  INPUT:   A proofsearch object, a DEF structure, a list of unshared clauses
           and a boolean saying whether the parent clause of an expansion
	   should be deleted.
  RETURNS: None.
  EFFECT:  For each occurrence of the defined predicate in a clause in the list,
  a new clause with expanded predicate is added to the list.
***************************************************************/
{
  LIST       l, newclauses, allnew;
  FLAGSTORE  FlagStore;
  PRECEDENCE Precedence;

  allnew     = list_Nil();
  FlagStore  = prfs_Store(Search);
  Precedence = prfs_Precedence(Search);

  for (l = Clauselist; !list_Empty(l); l = list_Cdr(l)) {
    newclauses = def_ApplyDefToClauseOnce(Def, (CLAUSE) list_Car(l),
					  FlagStore, Precedence);
    /* Expansions were possible, delete the original clause */
    if (Destructive && !list_Empty(newclauses)) {
      if (flag_GetFlagValue(FlagStore, flag_DOCPROOF))
	prfs_InsertDocProofClause(Search, (CLAUSE) list_Car(l));
      else
	clause_Delete((CLAUSE) list_Car(l));
      list_Rplaca(l, NULL);
    }
    allnew = list_Nconc(allnew, newclauses);
  }
  if (Destructive)
    Clauselist = list_PointerDeleteElement(Clauselist, NULL);


  if (flag_GetFlagValue(FlagStore, flag_PAPPLYDEFS)) {
    if (!list_Empty(allnew)) {
      fputs("\nNew clauses after applying definitions : \n", stdout);
      clause_ListPrint(allnew);
    }
  }

  Clauselist = list_Nconc(Clauselist, allnew);
  return Clauselist;
}

LIST def_ApplyDefToTermlist(DEF Def, LIST Termlist,
			    FLAGSTORE FlagStore, PRECEDENCE Precedence,
			    BOOL* Complete, BOOL Destructive)
/**************************************************************
  INPUT:   A DEF structure and a list of pairs (label, term),
           a flag store, a precedence and a pointer to a
	   boolean.
	   If Destructive is TRUE the father of an expanded
	   term is deleted.
  RETURNS: The changed list of terms.
  EFFECT:  For each occurrence of the defined predicate in a
           term in the list, a new term with expanded predicate
	   is added to the list.
	   If every occurrence of the predicate could be
	   expanded, Complete is set to TRUE.
***************************************************************/
{
  LIST l, newterms;
  
  newterms = list_Nil();

  *Complete = TRUE;
  for (l=Termlist; !list_Empty(l); l=list_Cdr(l)) {
    TERM newterm;
    TERM oldterm;
    BOOL complete;
    oldterm = list_PairSecond(list_Car(l));
    newterm = def_ApplyDefToTermOnce(Def, oldterm, FlagStore,
				     Precedence, &complete);
    if (!complete)
      *Complete = FALSE;
    /* destructive part of function */
    if (newterm != NULL) {
      newterms = list_Cons(list_PairCreate(NULL, newterm),newterms);
      if (Destructive) {
	/* Delete oldterm from Termlist */
	term_Delete(list_PairSecond(list_Car(l)));
	if (list_PairFirst(list_Car(l)) != NULL)
	  string_StringFree(list_PairFirst(list_Car(l)));
	
	list_PairFree(list_Car(l));
	list_Rplaca(l, NULL);
      }
    }
  }
  Termlist = list_PointerDeleteElement(Termlist, NULL);

  if (flag_GetFlagValue(FlagStore, flag_PAPPLYDEFS)) {
    if (!list_Empty(newterms)) {
      fputs("\n\nNew terms after applying definitions : \n", stdout);
      for (l=newterms; !list_Empty(l); l=list_Cdr(l)) {
	fputs("\n", stdout);
	fol_PrettyPrint(list_PairSecond(list_Car(l)));
      }
    }
  }
  
  Termlist = list_Nconc(Termlist, newterms);
  return Termlist;
}

void def_ExtractDefsFromTermlist(PROOFSEARCH Search, LIST Axioms, LIST Conj)
/**************************************************************
  INPUT:   A proofsearch object and 2 lists of pairs label/term.
  RETURNS: None.
  EFFECT:  Add all found definitions to the proofsearch object.
           The old list of definitions in the proofsearch object is 
	   overwritten.
***************************************************************/
{ 
  LIST      l, deflist;
  FLAGSTORE FlagStore;

  deflist   = list_Nil();
  FlagStore = prfs_Store(Search);

  for (l=Axioms; !list_Empty(l); l=list_Cdr(l)) {
    fol_NormalizeVars(list_PairSecond(list_Car(l))); /* Is needed for proper variable match ! */
    deflist = list_Nconc(deflist,
			 def_ExtractDefsFromTerm(list_PairSecond(list_Car(l)),
						 list_PairFirst(list_Car(l))));
  }
  for (l=Conj; !list_Empty(l); l=list_Cdr(l)) {
    fol_NormalizeVars(list_PairSecond(list_Car(l))); /* Is needed for proper variable match ! */
    deflist = list_Nconc(deflist,
			 def_ExtractDefsFromTerm(list_PairSecond(list_Car(l)),
						 list_PairFirst(list_Car(l))));
  }
  for (l=deflist; !list_Empty(l); l=list_Cdr(l))
    symbol_AddProperty(term_TopSymbol(def_Predicate(list_Car(l))), ISDEF);

  prfs_SetDefinitions(Search, list_Nconc(prfs_Definitions(Search), deflist));  

  if (flag_GetFlagValue(FlagStore, flag_PAPPLYDEFS)) {
    if (!list_Empty(deflist)) {
      fputs("\nFound definitions :\n", stdout);
      for (l = prfs_Definitions(Search); !list_Empty(l); l = list_Cdr(l)) {
	def_Print(list_Car(l));
	fputs("\n---\n", stdout);
      }
    }
  }
}

LIST def_FlattenWithOneDefinition(PROOFSEARCH Search, DEF Def)
/**************************************************************
  INPUT:   A proofsearch object and one definition.
  RETURNS: The list of new definitions.
  EFFECT:  For every occurrence of the defined predicate among the other
           definitions an expansion is attempted.
	   A new definition is only created if the result of the expansion is 
	   again a definition. 
	   The proofsearch object is not changed.
***************************************************************/
{
  LIST       newdefinitions;
  FLAGSTORE  FlagStore;
  PRECEDENCE Precedence;

  newdefinitions = list_Nil();
  FlagStore      = prfs_Store(Search);
  Precedence     = prfs_Precedence(Search);

  if (def_ToProve(Def) == NULL) {
    LIST definitions, l;

    definitions = prfs_Definitions(Search);

    for (l = definitions; !list_Empty(l); l=list_Cdr(l)) {
      DEF d;

      d = (DEF) list_Car(l);      
      if (d != Def) {
	/* Expansion possible */
	if (term_ContainsSymbol(def_Expansion(d), term_TopSymbol(def_Predicate(Def)))) {
	  /* Resulting term is still a definition */
	  if (!term_ContainsSymbol(def_Expansion(Def), term_TopSymbol(def_Predicate(d)))) {
	    TERM newexpansion;
	    BOOL complete;
	    DEF newdef;
	    newexpansion = def_ApplyDefToTermOnce(Def, def_Expansion(d),
						  FlagStore, Precedence,
						  &complete);
	    
	    newdef = def_CreateFromTerm(newexpansion,
					term_Copy(def_Predicate(d)), 
					term_Copy(def_ToProve(d)), def_Label(d));
	    newdefinitions = list_Cons(newdef, newdefinitions);
	  }
	}
      }
      
    }
  }
  return newdefinitions;
}


void def_FlattenWithOneDefinitionDestructive(PROOFSEARCH Search, DEF Def)
/**************************************************************
  INPUT:   A proofsearch object and one definition.
  RETURNS: None.
  EFFECT:  If the definition is always applicable, every occurrence of the 
           defined predicate among the other definitions is expanded in place.
	   If the resulting term is no longer a definition, it is deleted from
	   the proofsearch object.
	   Def is deleted.
  CAUTION: This function changes the list entries in the list of definitions 
           in the proofsearch object, so do not call it from a loop over
           all definitions.
***************************************************************/
{
  FLAGSTORE  FlagStore;
  PRECEDENCE Precedence;

  FlagStore  = prfs_Store(Search);
  Precedence = prfs_Precedence(Search);

  if (def_ToProve(Def) == NULL) {
    LIST definitions, l;

    definitions = prfs_Definitions(Search);    
    for (l = definitions; !list_Empty(l); l = list_Cdr(l)) {
      DEF d;

      d = (DEF) list_Car(l);      
      if (d != Def) {
	/* Expansion possible */
	if (term_ContainsSymbol(def_Expansion(d), term_TopSymbol(def_Predicate(Def)))) {
	  /* Resulting term is still a definition */
	  if (!term_ContainsSymbol(def_Expansion(Def), term_TopSymbol(def_Predicate(d)))) {
	    TERM newexpansion;
	    BOOL complete;

	    newexpansion = def_ApplyDefToTermOnce(Def, def_Expansion(d), FlagStore, Precedence, &complete);
	    term_Delete(def_Expansion(d));
	    def_RplacExp(d, newexpansion);
	  }
	  else {
	    symbol_RemoveProperty(term_TopSymbol(def_Predicate(d)), ISDEF);
	    def_Delete(d);
	    list_Rplaca(l, NULL);
	  }
	}
      }
      else {
	/* Remove given definition */
	list_Rplaca(l, NULL);
      }
    }
    symbol_RemoveProperty(term_TopSymbol(def_Predicate(Def)), ISDEF);
    def_Delete(Def);
    definitions = list_PointerDeleteElement(definitions, NULL);
    prfs_SetDefinitions(Search, definitions);
  }
}

void def_FlattenWithOneDefinitionSemiDestructive(PROOFSEARCH Search, DEF Def)
/**************************************************************
  INPUT:   A proofsearch object and one definition.
  RETURNS: Nothing.
  EFFECT:  If the definition can be applied to another definition
           in the search object, that definition is destructively changed.
	   If the resulting term is no longer a definition, it is deleted to
	   prevent cycles.
	   The applied definition Def is NOT deleted.
  CAUTION: After calling this function some entries of the definitions list
           in the proofsearch object may be NULL.
***************************************************************/
{
  FLAGSTORE  FlagStore;
  PRECEDENCE Precedence;

  FlagStore  = prfs_Store(Search);
  Precedence = prfs_Precedence(Search);
  
  if (def_ToProve(Def) == NULL) {
    LIST definitions, l;

    definitions = prfs_Definitions(Search);    
    for (l = definitions; !list_Empty(l); l=list_Cdr(l)) {
      DEF d;

      d = (DEF) list_Car(l);      
      if (d != Def) {
	/* Expansion possible */
	if (term_ContainsSymbol(def_Expansion(d), term_TopSymbol(def_Predicate(Def)))) {
	  /* Resulting term is still a definition */
	  if (!term_ContainsSymbol(def_Expansion(Def), term_TopSymbol(def_Predicate(d)))) {
	    TERM newexpansion;
	    BOOL complete;

	    newexpansion = def_ApplyDefToTermOnce(Def, def_Expansion(d),
						  FlagStore, Precedence,
						  &complete);
	    term_Delete(def_Expansion(d));
	    def_RplacExp(d, newexpansion);
	  }
	  else {
	    symbol_RemoveProperty(term_TopSymbol(def_Predicate(d)), ISDEF);
	    def_Delete(d);
	    list_Rplaca(l, NULL);
	  }
	}
      }
    }
  }
}

void def_FlattenDefinitionsDestructive(PROOFSEARCH Search)
/**************************************************************
  INPUT:   A proofsearch object.
  RETURNS: None.
  EFFECT:  For every definition that is always applicable try to 
           expand the predicate in other
           definitions if possible.
***************************************************************/
{
  LIST l;

  for (l = prfs_Definitions(Search); !list_Empty(l); l=list_Cdr(l)) {
    DEF d;

    d = (DEF) list_Car(l);
    fol_PrettyPrintDFG(def_Predicate(d));
    if (d != NULL)
      def_FlattenWithOneDefinitionSemiDestructive(Search, d);
  }
  prfs_SetDefinitions(Search, list_PointerDeleteElement(prfs_Definitions(Search), NULL));
}

LIST def_GetTermsForProof(TERM Term, TERM SubTerm, int Polarity)
/**************************************************************
  INPUT:   Two formulas, <Term> and <SubTerm> which must be subformula
           of <Term>,an int which is the polarity of <SubTerm> in its
	   superterm and a list of variables <Variables>.
  RETURN:  A list of formulas that are used to prove the guard of Atom.
  COMMENT: Helpfunction of def_FindProofFor Guard.
  CAUTION: Father links must be set. Free variables may exist in terms of
           return list.
	   Terms are copied.
***************************************************************/
{
  TERM   SuperTerm, AddToList;
  SYMBOL Top;
  LIST   Scan1, NewList;

  term_AddFatherLinks(Term);

#ifdef CHECK
  if (!fol_CheckFormula(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In def_GetTermsForProof: Illegal input Term.");
    misc_FinishErrorReport();
  } 
#endif

  if (Term == SubTerm)
    return list_Nil();

  SuperTerm = term_Superterm(SubTerm);
  Top       = term_TopSymbol(SuperTerm);
  NewList   = list_Nil();
  AddToList = term_Null();

  if (symbol_Equal(Top, fol_Not()))
    return def_GetTermsForProof(Term, SuperTerm, -1*Polarity);

  if (symbol_Equal(Top, fol_Or()) && Polarity == 1) {
    /* Get and store AddToList */
    for (Scan1 = term_ArgumentList(SuperTerm); !list_Empty(Scan1); Scan1 = list_Cdr(Scan1)) {
      if (!term_HasPointerSubterm(list_Car(Scan1), SubTerm))
	NewList = list_Cons(term_Create(fol_Not(),list_List(term_Copy(list_Car(Scan1)))), NewList);
      /* NewList's elements have the form not(term) */
    }
    if (list_Length(NewList) == 1) {
      AddToList = list_Car(NewList);
      list_Delete(NewList);
    }
    else {
      AddToList = term_Create(fol_And(), NewList);
    }
    return list_Cons(AddToList, def_GetTermsForProof(Term, SuperTerm, Polarity));
  }
  if (symbol_Equal(Top, fol_And()) && Polarity == -1) {
    /* Get and store AddToList */
    if (list_Length(term_ArgumentList(SuperTerm)) == 2) {
      if (!term_HasPointerSubterm(term_FirstArgument(SuperTerm), SubTerm)) {
	AddToList = term_Copy(term_FirstArgument(SuperTerm));
      }
      else {
	AddToList = term_Copy(term_SecondArgument(SuperTerm));
      }
    }
    else if (list_Length(term_ArgumentList(SuperTerm)) > 2) {
      for (Scan1 = term_ArgumentList(SuperTerm); !list_Empty(Scan1); Scan1 = list_Cdr(Scan1)) {
	if (!term_HasPointerSubterm(list_Car(Scan1), SubTerm))
	  NewList = list_Cons(term_Copy(list_Car(Scan1)), NewList);
      }
      AddToList = term_Create(fol_And(), NewList);
    }
    else { /* Only one argument */
      AddToList = term_Copy(term_FirstArgument(SuperTerm));
    }
   return list_Cons(AddToList, def_GetTermsForProof(Term, SuperTerm, Polarity));
  }
  if (symbol_Equal(Top, fol_Implies())) {
    if (term_HasPointerSubterm(term_SecondArgument(SuperTerm), SubTerm) && Polarity == 1) {
      AddToList = term_Copy(term_FirstArgument(SuperTerm));
      return list_Cons(AddToList, def_GetTermsForProof(Term, SuperTerm, Polarity));
    }
    if (term_HasPointerSubterm(term_FirstArgument(SuperTerm), SubTerm) && Polarity == -1) {
      AddToList = term_Copy(term_SecondArgument(SuperTerm));
      AddToList = term_Create(fol_Not(), list_List(AddToList));
      return list_Cons(AddToList, def_GetTermsForProof(Term, SuperTerm, -1*Polarity));
    }
  }
  if (symbol_Equal(Top, fol_Implied())) { /* symmetric to fol_Implies */
    if (term_HasPointerSubterm(term_SecondArgument(SuperTerm), SubTerm) && Polarity == -1) {
      AddToList = term_Copy(term_FirstArgument(SuperTerm));
      AddToList = term_Create(fol_Not(), list_List(AddToList));
      return list_Cons(AddToList, def_GetTermsForProof(Term, SuperTerm, -1*Polarity)); 
    }
    if (term_HasPointerSubterm(term_FirstArgument(SuperTerm), SubTerm) && Polarity == 1) {
      AddToList = term_Copy(term_SecondArgument(SuperTerm));
      return list_Cons(AddToList, def_GetTermsForProof(Term, SuperTerm, Polarity));
    }
  }
  if (fol_IsQuantifier(Top))
    return def_GetTermsForProof(Term, SuperTerm, Polarity);

  /* In all other cases, SubTerm is the top level term in which Atom occurs disjunctively */

  return list_Nil();
}

BOOL def_FindProofForGuard(TERM Term, TERM Atom, TERM Guard, FLAGSTORE FlagStore, PRECEDENCE Precedence)
/**************************************************************************
  INPUT:   A formula Term, an atom Atom, a term Guard a flag store and a 
           precedence.
  RETURNS: True iff a proof can be found for Guard in Term.
***************************************************************************/
{
  BOOL LocallyTrue;
  TERM ToProve, Conjecture;
  LIST ArgList, FreeVars;

  ArgList    = list_Nil();
  FreeVars   = list_Nil();
  ToProve    = term_Null();
  Conjecture = term_Copy(Term);

#ifdef CHECK
  if (!fol_CheckFormula(Term)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In def_FindProofForGuard: No correct formula term.");
    misc_FinishErrorReport();
  }
  if (!term_HasPointerSubterm(Term, Atom)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In def_FindProofForGuard: Illegal input.");
    misc_FinishErrorReport();
  }
#endif
  
  ArgList = def_GetTermsForProof(Term, Atom, 1);

  if (!list_Empty(ArgList)) {
    ToProve  = term_Create(fol_And(), ArgList);
    FreeVars = list_Nconc(fol_FreeVariables(ToProve), fol_FreeVariables(Guard));
    FreeVars = term_DeleteDuplicatesFromList(FreeVars);
    term_CopyTermsInList(FreeVars);

    ArgList  = list_List(term_Copy(Guard));
    ArgList  = list_Cons(ToProve, ArgList);
    ToProve  = term_Create(fol_Implies(), ArgList);
    ToProve  = fol_CreateQuantifier(fol_All(), FreeVars, list_List(ToProve));

    /* Now ToProve has the form <forall[]: A implies Guard> */
    /*    puts("\n*ToProve: "); fol_PrettyPrintDFG(ToProve); */

#ifdef CHECK
    if (!fol_CheckFormula(ToProve)) {
      misc_StartErrorReport();
      misc_ErrorReport("\n In def_FindProofForGuard: No correct formula ToProve.");
      misc_FinishErrorReport();
    }
#endif

    LocallyTrue = cnf_HaveProof(list_Nil(), ToProve, FlagStore, Precedence);
    term_Delete(ToProve);
    term_Delete(Conjecture);
    if (LocallyTrue)
      return TRUE;
  }
  else {    /* empty list */
    term_DeleteTermList(ArgList);
    term_Delete(Conjecture);
  }

  return FALSE;
}

LIST def_ApplyDefinitionToTermList(LIST Defs, LIST Terms,
				   FLAGSTORE Flags, PRECEDENCE Precedence)
/**************************************************************************
  INPUT:   A list of definitions <Defs> and a list of pairs (Label.Formula),
           the maximal number <Applics> of expansions, a flag store and a
	   precedence.
  RETURNS: The possibly destructively changed list <Terms>.
  EFFECT:  In all formulas of Terms any definition of Defs is applied exactly
           once if possible.
           The terms are changed destructively if the expanded def_predicate 
	   is not an equality.
**************************************************************************/
{
  TERM ActTerm;             /* Actual term in Terms */
  TERM DefPredicate;        /* Actual definition predicate out of Defs */
  TERM Expansion;           /* Expansion term of the definition */
  TERM Target;              /* Target predicate to be replaced */
  LIST TargetList, Scan1, Scan2, Scan3;
  BOOL Apply;
  int  Applics;

  Apply      = TRUE;
  TargetList = list_Nil();
  Applics    = flag_GetFlagValue(Flags, flag_APPLYDEFS);

  while (Apply && Applics != 0) {
    Apply = FALSE;
    
    for (Scan1=Defs; !list_Empty(Scan1) && Applics != 0; Scan1=list_Cdr(Scan1)) {
      DefPredicate = term_Copy(def_Predicate(list_Car(Scan1)));

      /*      puts("\n----\nDefPred:"); fol_PrettyPrintDFG(DefPredicate);*/

      for (Scan2=Terms; !list_Empty(Scan2) && Applics != 0; Scan2=list_Cdr(Scan2)) {
	ActTerm   = list_PairSecond(list_Car(Scan2));
	TargetList = term_FindAllAtoms(ActTerm, term_TopSymbol(DefPredicate));
	term_AddFatherLinks(ActTerm);
	
	/*	puts("\nActTerm:"); fol_PrettyPrintDFG(ActTerm);*/

	for (Scan3=TargetList; !list_Empty(Scan3) && Applics != 0; Scan3=list_Cdr(Scan3)) {
	  Target = list_Car(Scan3);
	  cont_StartBinding();

	  /*	  puts("\nTarget:"); fol_PrettyPrintDFG(Target);*/

	  if (unify_Match(cont_LeftContext(), DefPredicate, Target)) {
	    cont_BackTrack();
	    Expansion = term_Copy(def_Expansion(list_Car(Scan1)));
	    fol_NormalizeVarsStartingAt(ActTerm, term_MaxVar(Expansion));
	    unify_Match(cont_LeftContext(), DefPredicate, Target);

	    if (fol_ApplyContextToTerm(cont_LeftContext(), Expansion)) { /* Matcher applied on Expansion */
	      if (!def_HasGuard(list_Car(Scan1))) {
		Applics--;
		Apply = TRUE;
		/*		puts("\n*no Guard!");*/
		term_RplacTop(Target, term_TopSymbol(Expansion));
		term_DeleteTermList(term_ArgumentList(Target));
		term_RplacArgumentList(Target, term_ArgumentList(Expansion));
		term_RplacArgumentList(Expansion, list_Nil());
		term_AddFatherLinks(ActTerm);
#ifdef CHECK
		if (!fol_CheckFormula(ActTerm)) {
		  misc_StartErrorReport();
		  misc_ErrorReport("\n In def_ApplyDefinitionToTermList:");
		  misc_ErrorReport(" No correct formula ActTerm.");
		  misc_FinishErrorReport();
		}
#endif
		if (flag_GetFlagValue(Flags, flag_PAPPLYDEFS)) {
		  puts("\nApplied definition for");
		  fol_PrettyPrintDFG(def_Predicate(list_Car(Scan1)));
		  puts("\nNew formula:");
		  fol_PrettyPrintDFG(ActTerm);
		}
	      }
	      else {  /* check guard */
		TERM Guard;
		Guard = term_Copy(def_ToProve(list_Car(Scan1)));
		if (fol_ApplyContextToTerm(cont_LeftContext(), Guard)) {
		  cont_BackTrack(); 
		  if (def_FindProofForGuard(ActTerm, Target,Guard,
					    Flags, Precedence)) {
		    Applics--;
		    Apply = TRUE;
		    term_RplacTop(Target, term_TopSymbol(Expansion));
		    term_DeleteTermList(term_ArgumentList(Target));
		    term_RplacArgumentList(Target, term_ArgumentList(Expansion));
		    term_RplacArgumentList(Expansion, list_Nil());
		    term_AddFatherLinks(ActTerm);
#ifdef CHECK
		    if (!fol_CheckFormula(ActTerm)) {
		      misc_StartErrorReport();
		      misc_ErrorReport("\n In def_ApplyDefinitionToTermList:");
		      misc_ErrorReport(" No correct formula ActTerm");
		      misc_FinishErrorReport();
		    }
#endif
		    if (flag_GetFlagValue(Flags, flag_PAPPLYDEFS)) {
		      puts("\nApplied definition for");
		      fol_PrettyPrintDFG(def_Predicate(list_Car(Scan1)));
		      puts("\nNew formula:");
		      fol_PrettyPrintDFG(ActTerm);
		    }
		  }
		}
		term_Delete(Guard);
	      }
	    }
	    term_Delete(Expansion);	    
	  }
	  cont_BackTrack();
	}
	list_Delete(TargetList);
      }
      term_Delete(DefPredicate);
    }
  }
  return Terms;
}
