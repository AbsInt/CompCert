/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                     SUBSUMPTION                        * */
/* *                                                        * */
/* *  $Module:   SUBSUMPTION                                * */ 
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


#include "subsumption.h"

static NAT multvec_i[subs__MAXLITS];
static NAT multvec_j[subs__MAXLITS];
static NAT stamp;

static BOOL subs_InternIdc(CLAUSE, int, CLAUSE);
static BOOL subs_InternIdcEq(CLAUSE, int, CLAUSE);
static BOOL subs_InternIdcEqExcept(CLAUSE, int, CLAUSE, int);
static BOOL subs_InternIdcRes(CLAUSE, int, int, int);

/* The following functions are currently unused */
BOOL subs_IdcTestlits(CLAUSE, CLAUSE, LITPTR*);
BOOL subs_Testlits(CLAUSE, CLAUSE);


void subs_Init(void) 
{
  int i;

  stamp = 0;
  for (i = 0; i < subs__MAXLITS; i++)
    multvec_i[i] = multvec_j[i] = 0;
}


static BOOL subs_TestlitsEq(CLAUSE c1, CLAUSE c2)
/**********************************************************
  INPUT:   Two clauses c1 and c2.
  RETURNS: FALSE if c1 do not subsume c2 and TRUE otherwise.
  CAUTION: None.
***********************************************************/
{
  TERM  t1,t2;
  int   i,j,n,k;
  BOOL  found;

  n    = clause_Length(c1);
  k    = clause_Length(c2);

  for (i = 0; i < n; i++){
    j     = 0;
    found = FALSE;
    t1    = clause_GetLiteralTerm(c1,i);

    do {
      t2 = clause_GetLiteralTerm(c2,j);
      cont_StartBinding();
      if (unify_Match(cont_LeftContext(), t1, t2))
	found = TRUE;
      else{
	if (symbol_Equal(term_TopSymbol(t1),term_TopSymbol(t2)) &&
	    fol_IsEquality(fol_Atom(t1)) &&
	    fol_IsEquality(fol_Atom(t2)) &&
	    (clause_LiteralIsNotOrientedEquality(clause_GetLiteral(c1,i)) ||
	     clause_LiteralIsNotOrientedEquality(clause_GetLiteral(c2,j)))) {
	  cont_BackTrackAndStart();
	  if (unify_Match(cont_LeftContext(),
			  term_FirstArgument(fol_Atom(t1)),
			  term_SecondArgument(fol_Atom(t2))) &&
	      unify_Match(cont_LeftContext(),
			  term_SecondArgument(fol_Atom(t1)),
			  term_FirstArgument(fol_Atom(t2))))
	    found = TRUE;
	  else 
	    j++;
	}
	else
	  j++;
      }
      cont_BackTrack();
      
    } while (!found && j < k);
       
    if (!found)
      return FALSE;
  }

  return TRUE;
}


static BOOL subs_STMultiIntern(int i, CLAUSE c1, CLAUSE c2)
/**********************************************************
  INPUT:   Integers i,j and two clauses c1 and c2
           i and j stand for the i-th and the j-th literal 
	   in the clause c1 respectively c2. 
  RETURNS: FALSE if c1 does not multisubsume c2 and TRUE otherwise.
  CAUTION: None.
***********************************************************/
{  
  int  n,j;
  TERM lit1,lit2;

  j       = 0;
  n       = clause_Length(c2);
  lit1    = clause_GetLiteralTerm(c1,i);

  while (j < n) {
    if (multvec_j[j] != stamp) {
      lit2    = clause_GetLiteralTerm(c2,j);
      cont_StartBinding();
      if (unify_Match(cont_LeftContext(),lit1,lit2)) {
	if (i == (clause_Length(c1)-1)) {
	  cont_BackTrack();
	  return TRUE;
	}
	multvec_j[j] = stamp;
	if (subs_STMultiIntern(i+1, c1, c2)) {
	  cont_BackTrack();
	  return TRUE;
	}
	multvec_j[j] = 0;
      }
      cont_BackTrack();
      if (symbol_Equal(term_TopSymbol(lit1),term_TopSymbol(lit2)) &&
	  fol_IsEquality(fol_Atom(lit1)) &&
	  fol_IsEquality(fol_Atom(lit2)) &&
	  (clause_LiteralIsNotOrientedEquality(clause_GetLiteral(c1,i)) ||
	   clause_LiteralIsNotOrientedEquality(clause_GetLiteral(c2,j)))) {
	cont_StartBinding();
	if (unify_Match(cont_LeftContext(),
			term_FirstArgument(fol_Atom(lit1)),
			term_SecondArgument(fol_Atom(lit2))) &&
	    unify_Match(cont_LeftContext(),
			term_SecondArgument(fol_Atom(lit1)),
			term_FirstArgument(fol_Atom(lit2)))) {
	  if (i == (clause_Length(c1)-1)) {
	    cont_BackTrack();
	    return TRUE;
	  }
	  multvec_j[j] = stamp;
	  if (subs_STMultiIntern(i+1, c1, c2)) {
	    cont_BackTrack();
	    return TRUE;
	  }
	  multvec_j[j] = 0;
	}
	cont_BackTrack();
      }
    }
    j++;
  }
  return FALSE;
}


BOOL subs_STMulti(CLAUSE c1, CLAUSE c2)
{
  BOOL Result;
  int  n;

  n = clause_Length(c1);

  /*printf("\n St-Multi: %d -> %d",clause_Number(c1),clause_Number(c2));*/

  if (n > clause_Length(c2) ||
      (n > 1 && !subs_TestlitsEq(c1,c2))) {
    /*fputs(" Testlits failure ", stdout);*/
    return(FALSE);
  }

  if (++stamp == NAT_MAX) {
    int i;
    stamp = 1;
    for (i = 0; i < subs__MAXLITS; i++)
    multvec_i[i] = multvec_j[i] = 0;
  }
  /*unify_SaveState();*/
  Result = subs_STMultiIntern(0,c1,c2);
  /*unify_CheckState();*/
  return Result;
}


static BOOL subs_TestlitsEqExcept(CLAUSE C1, CLAUSE C2)
{
  TERM  t1,t2;
  int   i,j,n,k;
  BOOL  found;

  n    = clause_Length(C1);
  k    = clause_Length(C2);

  i = 0;
  while (multvec_i[i] == stamp && i < n)
    i++;

  while (i < n) {
    j     = 0;
    found = FALSE;
    t1    = clause_GetLiteralTerm(C1,i);

    do {
      if (multvec_j[j] == stamp)
	j++;
      else {
	t2 = clause_GetLiteralTerm(C2,j);
	cont_StartBinding();
	if (unify_MatchBindings(cont_LeftContext(), t1, t2))
	  found = TRUE;
	else {
	  if (symbol_Equal(term_TopSymbol(t1),term_TopSymbol(t2)) &&
	      fol_IsEquality(fol_Atom(t1)) &&
	      fol_IsEquality(fol_Atom(t2)) &&
	      (clause_LiteralIsNotOrientedEquality(clause_GetLiteral(C1,i)) ||
	       clause_LiteralIsNotOrientedEquality(clause_GetLiteral(C2,j)))) {
	    cont_BackTrackAndStart();
	    if (unify_MatchBindings(cont_LeftContext(),
				    term_FirstArgument(fol_Atom(t1)),
				    term_SecondArgument(fol_Atom(t2))) &&
		unify_MatchBindings(cont_LeftContext(),
				    term_SecondArgument(fol_Atom(t1)),
				    term_FirstArgument(fol_Atom(t2))))
	      found = TRUE;
	    else 
	      j++;
	  }
	  else
	    j++;
	}
	cont_BackTrack();
      }  /* else */
    } while (!found && (j < k));
       
    if (!found) 
      return FALSE;
    do
      i++;
    while (multvec_i[i] == stamp && i < n);
  } /* while i < n */


  return TRUE;
}


static BOOL subs_STMultiExceptIntern(CLAUSE C1, CLAUSE C2)
{
  int  n, i, j, k;
  NAT  occs, occsaux;
  TERM lit1,lit2;

  i    = -1;
  k    = 0;
  occs = 0;
  j    = 0;
  n    = clause_Length(C2);

  while (k < clause_Length(C1)) {
    /* Select Literal with maximal number of variable occurrences. */
    if (multvec_i[k] != stamp) {
      if (i < 0) {
	i    = k;
	occs = term_NumberOfVarOccs(clause_GetLiteralAtom(C1,i));
      } else
	if ((occsaux = term_NumberOfVarOccs(clause_GetLiteralAtom(C1,k)))
	    > occs) {
	  i    = k;
	  occs = occsaux;
	}
    }
    k++;
  }

  if (i < 0)
    return TRUE;

  lit1 = clause_GetLiteralTerm(C1, i);
  multvec_i[i] = stamp;

  while (j < n) {
    if (multvec_j[j] != stamp) {
      lit2 = clause_GetLiteralTerm(C2, j);
      cont_StartBinding();
      if (unify_MatchBindings(cont_LeftContext(), lit1, lit2)) {
	multvec_j[j] = stamp;
	if (subs_STMultiExceptIntern(C1, C2)) {
	  cont_BackTrack();
	  return TRUE;
	}
	multvec_j[j] = 0;
      }
      cont_BackTrack();
      if (symbol_Equal(term_TopSymbol(lit1),term_TopSymbol(lit2)) &&
	  fol_IsEquality(fol_Atom(lit1)) &&
	  fol_IsEquality(fol_Atom(lit2)) &&
	  (clause_LiteralIsNotOrientedEquality(clause_GetLiteral(C1,i)) ||
	   clause_LiteralIsNotOrientedEquality(clause_GetLiteral(C2,j)))) {
	cont_StartBinding();
	if (unify_MatchBindings(cont_LeftContext(),
				term_FirstArgument(fol_Atom(lit1)),
				term_SecondArgument(fol_Atom(lit2))) &&
	    unify_MatchBindings(cont_LeftContext(),
				term_SecondArgument(fol_Atom(lit1)),
				term_FirstArgument(fol_Atom(lit2)))) {
	  multvec_j[j] = stamp;
	  if (subs_STMultiExceptIntern(C1, C2)) {
	    cont_BackTrack();
	    return TRUE;
	  }
	  multvec_j[j] = 0;
	}
	cont_BackTrack();
      }
    }
    j++;
  }
  multvec_i[i] = 0;
  return FALSE;
}


BOOL subs_STMultiExcept(CLAUSE C1, CLAUSE C2, int ExceptI, int ExceptJ)
/**********************************************************
  INPUT:   Two clauses and for each clause a literal that is
           already bound to each other. If the literal value is negative,
	   a general subsumption test is performed.
  RETURNS: TRUE if the first clause subsumes the second one.
  CAUTION: The weight of the clauses must be up to date!
***********************************************************/
{
  BOOL Result;
  int  n;

  n = clause_Length(C1);

  if (n > clause_Length(C2) ||
      (clause_Weight(C1)-clause_LiteralWeight(clause_GetLiteral(C1,ExceptI))) >
      (clause_Weight(C2)-clause_LiteralWeight(clause_GetLiteral(C2,ExceptJ))))
    return FALSE;

  if (++stamp == NAT_MAX) {
    int i;
    stamp = 1;
    for (i = 0; i < subs__MAXLITS; i++)
      multvec_i[i] = multvec_j[i] = 0;
  }
  multvec_i[ExceptI] = stamp;
  multvec_j[ExceptJ] = stamp;

  if (n > 1 && !subs_TestlitsEqExcept(C1, C2))
    return FALSE;

  /*unify_SaveState();*/
  Result = subs_STMultiExceptIntern(C1, C2);
  /*unify_CheckState();*/
  return Result;
}


static BOOL subs_PartnerTest(CLAUSE C1, int c1l, int c1r, CLAUSE C2, int c2l, int c2r)
/**********************************************************
  INPUT:   Two clauses and for each clause a starting left index
           and an exclusive right index.
  RETURNS: TRUE if every literal inside the bounds of the first clause
           can be matched against a literal inside the bounds of the
	   second clause.
  CAUTION: None.
***********************************************************/
{
  TERM  t1,t2;
  int   j;
  BOOL  found;

  if (c1l == c1r)
    return TRUE;

  while (multvec_i[c1l] == stamp && c1l < c1r)
    c1l++;

  if (c1l < c1r) {
    if  (c2l == c2r)
      return FALSE;
    else
      do {
	j     = c2l;
	found = FALSE;
	t1    = clause_GetLiteralTerm(C1,c1l);

	do {
	  if (multvec_j[j] == stamp)
	    j++;
	  else {
	    t2 = clause_GetLiteralTerm(C2,j);
	    cont_StartBinding();
	    if (unify_MatchBindings(cont_LeftContext(), t1, t2))
	      found = TRUE;
	    else {
	      if (symbol_Equal(term_TopSymbol(t1),term_TopSymbol(t2)) &&
		  fol_IsEquality(fol_Atom(t1)) &&
		  fol_IsEquality(fol_Atom(t2)) &&
		  (clause_LiteralIsNotOrientedEquality(clause_GetLiteral(C1,c1l)) ||
		   clause_LiteralIsNotOrientedEquality(clause_GetLiteral(C2,j)))) {
		cont_BackTrackAndStart();
		if (unify_MatchBindings(cont_LeftContext(),
					term_FirstArgument(fol_Atom(t1)),
					term_SecondArgument(fol_Atom(t2))) &&
		    unify_MatchBindings(cont_LeftContext(),
					term_SecondArgument(fol_Atom(t1)),
					term_FirstArgument(fol_Atom(t2))))
		  found = TRUE;
		else 
		  j++;
	      }
	      else
		j++;
	    }
	    cont_BackTrack();
	  }  /* else */
	} while (!found && (j < c2r));
       
	if (!found) 
	  return FALSE;
	do
	  c1l++;
	while (multvec_i[c1l] == stamp && c1l < c1r);
      } while (c1l < c1r);
  }
  return TRUE;
}


static BOOL subs_SubsumesInternBasic(CLAUSE C1, int c1fa, int c1fs, int c1l, 
				     CLAUSE C2, int c2fa, int c2fs, int c2l)
{
  int  i, j, n, k;
  NAT  occs, occsaux;
  TERM lit1,lit2;

  i    = -1;
  k    = clause_FirstLitIndex();
  occs = 0;

  while (k < c1l) {     /* Select literal with maximal variable occurrences. */
    if (multvec_i[k] != stamp) {
      if (i < 0) {
	i    = k;
	occs = term_NumberOfVarOccs(clause_GetLiteralAtom(C1,i));
      } else
	if ((occsaux = term_NumberOfVarOccs(clause_GetLiteralAtom(C1,k)))
	    > occs) {
	  i    = k;
	  occs = occsaux;
	}
    }
    k++;
  }

  if (i < 0)
    return TRUE;

  lit1         = clause_GetLiteralTerm(C1, i);
  multvec_i[i] = stamp;

  if (i < c1fa) {                 /* Only consider relevant partner literals */
    j = clause_FirstLitIndex();
    n = c2fa;
  }
  else if (i < c1fs) {
    j = c2fa;
    n = c2fs;
  }
  else {
    j = c2fs;
    n = c2l;
  }

  while (j < n) {
    if (multvec_j[j] != stamp) {
      lit2 = clause_GetLiteralTerm(C2, j);
      cont_StartBinding();
      if (unify_MatchBindings(cont_LeftContext(), lit1, lit2)) {
	multvec_j[j] = stamp;
	if (subs_SubsumesInternBasic(C1,c1fa,c1fs,c1l,C2,c2fa,c2fs,c2l)) {
	  cont_BackTrack();
	  return TRUE;
	}
	multvec_j[j] = 0;
      }
      cont_BackTrack();
      if (symbol_Equal(term_TopSymbol(lit1),term_TopSymbol(lit2)) &&
	  fol_IsEquality(fol_Atom(lit1)) &&
	  fol_IsEquality(fol_Atom(lit2)) &&
	  (clause_LiteralIsNotOrientedEquality(clause_GetLiteral(C1,i)) ||
	   clause_LiteralIsNotOrientedEquality(clause_GetLiteral(C2,j)))) {
	cont_StartBinding();
	if (unify_MatchBindings(cont_LeftContext(),
				term_FirstArgument(fol_Atom(lit1)),
				term_SecondArgument(fol_Atom(lit2))) &&
	    unify_MatchBindings(cont_LeftContext(),
				term_SecondArgument(fol_Atom(lit1)),
				term_FirstArgument(fol_Atom(lit2)))) {
	  multvec_j[j] = stamp;
	  if (subs_SubsumesInternBasic(C1,c1fa,c1fs,c1l,C2,c2fa,c2fs,c2l)) {
	    cont_BackTrack();
	    return TRUE;
	  }
	  multvec_j[j] = 0;
	}
	cont_BackTrack();
      }
    }
    j++;
  }
  multvec_i[i] = 0;
  return FALSE;
}


BOOL subs_SubsumesBasic(CLAUSE C1, CLAUSE C2, int ExceptI, int ExceptJ)
/**********************************************************
  INPUT:   Two clauses and for each clause a literal that are
           already bound to each other. If the literal value is negative,
	   a general subsumption test is performed.
  RETURNS: TRUE if the first clause subsumes the second one with respect
           to basic restrictions on the sort literals.
  CAUTION: The weight of the clauses must be up to date!
***********************************************************/
{
  BOOL Result;
  int  c1fa,c1fs,c1l,c2fa,c2fs,c2l,lw1,lw2;

  c1fa = clause_FirstAntecedentLitIndex(C1);
  c1fs = clause_FirstSuccedentLitIndex(C1);
  c1l  = clause_Length(C1);
  c2fa = clause_FirstAntecedentLitIndex(C2);
  c2fs = clause_FirstSuccedentLitIndex(C2);
  c2l  = clause_Length(C2);

  lw1 = (ExceptI >= clause_FirstLitIndex() ?
	 clause_LiteralWeight(clause_GetLiteral(C1,ExceptI)) : 0);
  lw2 = (ExceptJ >= clause_FirstLitIndex() ?
	 clause_LiteralWeight(clause_GetLiteral(C2,ExceptJ)) : 0);

  if (c1l > c2l ||                               /* Multiset restriction */
      (clause_Weight(C1)-lw1) >  (clause_Weight(C2)-lw2)) {
    return FALSE;
  }

  if (++stamp == NAT_MAX) {
    int i;
    stamp = 1;
    for (i = 0; i < subs__MAXLITS; i++)
      multvec_i[i] = multvec_j[i] = 0;
  }

  if (ExceptI >= clause_FirstLitIndex())
    multvec_i[ExceptI] = stamp;
  if (ExceptJ >= clause_FirstLitIndex())
    multvec_j[ExceptJ] = stamp;

  if (c1l > 1 && 
      (!subs_PartnerTest(C1,clause_FirstConstraintLitIndex(C1),c1fa,
			 C2,clause_FirstConstraintLitIndex(C2),c2fa) ||
       !subs_PartnerTest(C1,c1fa,c1fs,C2,c2fa,c2fs) ||
       !subs_PartnerTest(C1,c1fs,c1l,C2,c2fs,c2l)))
    return FALSE;

#ifdef CHECK
  cont_SaveState();
#endif

  Result = subs_SubsumesInternBasic(C1,c1fa,c1fs,c1l,C2,c2fa,c2fs,c2l);

#ifdef CHECK
  cont_CheckState();
#endif

  return Result;
}


static BOOL subs_SubsumesInternWithSignature(int i, CLAUSE c1, CLAUSE c2, BOOL Variants, LIST* Bindings)
/**********************************************************
  INPUT:   
  RETURNS: 
  CAUTION: 
***********************************************************/
{  
  int  n,j;
  TERM lit1,lit2;
  LIST NewBindings,Scan;

  j           = 0;
  n           = clause_Length(c2);
  lit1        = clause_GetLiteralTerm(c1,i);
  NewBindings = list_Nil();

  while (j < n) {
    if (multvec_j[j] != stamp) {
      lit2    = clause_GetLiteralTerm(c2,j);
      cont_StartBinding();
      if (fol_SignatureMatch(lit1,lit2,&NewBindings,Variants)) {
	if (i == (clause_Length(c1)-1)) {
	  *Bindings = list_Nconc(NewBindings,*Bindings);
	  return TRUE;
	}
	multvec_j[j] = stamp;
	if (subs_SubsumesInternWithSignature(i+1, c1, c2,Variants,&NewBindings)) {
	  *Bindings = list_Nconc(NewBindings,*Bindings);
	  return TRUE;
	}
	multvec_j[j] = 0;
      }      
      for (Scan=NewBindings;!list_Empty(Scan);Scan=list_Cdr(Scan)) { /* Backtrack bindings */
	if (symbol_IsVariable((SYMBOL)list_Car(Scan)))
	  term_ClearBinding((SYMBOL)list_Car(Scan));
	else
	  symbol_ContextClearValue((SYMBOL)list_Car(Scan));
      }
      list_Delete(NewBindings);
      NewBindings = list_Nil();
      if (symbol_Equal(term_TopSymbol(fol_Atom(lit1)),term_TopSymbol(fol_Atom(lit2))) &&
	  fol_IsEquality(fol_Atom(lit1))) {
	if (fol_SignatureMatch(term_FirstArgument(fol_Atom(lit1)),
			       term_SecondArgument(fol_Atom(lit2)), &NewBindings, Variants) &&
	    fol_SignatureMatch(term_SecondArgument(fol_Atom(lit1)),
			       term_FirstArgument(fol_Atom(lit2)), &NewBindings, Variants)) {
	  if (i == (clause_Length(c1)-1)) {
	    *Bindings = list_Nconc(NewBindings,*Bindings);
	    return TRUE;
	  }
	  multvec_j[j] = stamp;
	  if (subs_SubsumesInternWithSignature(i+1, c1, c2,Variants,&NewBindings)) {
	    *Bindings = list_Nconc(NewBindings,*Bindings);
	    return TRUE;
	  }
	  multvec_j[j] = 0;
	}
	for (Scan=NewBindings;!list_Empty(Scan);Scan=list_Cdr(Scan)) { /* Backtrack bindings */
	  if (symbol_IsVariable((SYMBOL)list_Car(Scan)))
	    term_ClearBinding((SYMBOL)list_Car(Scan));
	  else
	    symbol_ContextClearValue((SYMBOL)list_Car(Scan));
	}
	list_Delete(NewBindings);
	NewBindings = list_Nil();
      }
    }
    j++;
  }
  return FALSE;
}

BOOL subs_SubsumesWithSignature(CLAUSE C1, CLAUSE C2, BOOL Variants, LIST *Bindings)
/**********************************************************
  INPUT:   Two clauses .
  RETURNS: TRUE if the first clause subsumes the second one where
           we allow signature symbols to be matched as well.
	   If <Variants> is TRUE variables must be mapped to variables.
	   Returns the signature symbols that were bound.
  EFFECT:  Symbol context bindings are established.
***********************************************************/
{
  BOOL Result;

  if (clause_Length(C1) > clause_Length(C2) ||
      clause_NumOfSuccLits(C1) > clause_NumOfSuccLits(C2) ||
      (clause_NumOfAnteLits(C1) + clause_NumOfConsLits(C1)) > 
      (clause_NumOfAnteLits(C2) + clause_NumOfConsLits(C2))) {   /* Multiset restriction */
    return FALSE;
  }

  if (++stamp == NAT_MAX) {
    int i;
    stamp = 1;
    for (i = 0; i < subs__MAXLITS; i++)
      multvec_i[i] = multvec_j[i] = 0;
  }

  term_NewMark();
  Result =  subs_SubsumesInternWithSignature(clause_FirstLitIndex(),C1,C2,Variants, Bindings);
  *Bindings = list_DeleteElementIf(*Bindings, (BOOL (*)(POINTER)) symbol_IsVariable);
  return Result;
}

static BOOL subs_SubsumesIntern(CLAUSE C1, int c1fs, int c1l, CLAUSE C2, int c2fs, int c2l)
{
  int  i, j, n, k;
  NAT  occs, occsaux;
  TERM lit1,lit2;

  i    = -1;
  k    = clause_FirstLitIndex();
  occs = 0;

  while (k < c1l) {     /* Select literal with maximal variable occurrences. */
    if (multvec_i[k] != stamp) {
      if (i < 0) {
	i    = k;
	occs = term_NumberOfVarOccs(clause_GetLiteralAtom(C1,i));
      } else
	if ((occsaux = term_NumberOfVarOccs(clause_GetLiteralAtom(C1,k)))
	    > occs) {
	  i    = k;
	  occs = occsaux;
	}
    }
    k++;
  }

  if (i < 0)
    return TRUE;

  lit1         = clause_GetLiteralTerm(C1, i);
  multvec_i[i] = stamp;

  if (i < c1fs) {                  /* Only consider relevant partner literals */
    j = clause_FirstLitIndex();
    n = c2fs;
  }
  else {
    j = c2fs;
    n = c2l;
  }

  while (j < n) {
    if (multvec_j[j] != stamp) {
      lit2 = clause_GetLiteralTerm(C2, j);
      cont_StartBinding();
      if (unify_MatchBindings(cont_LeftContext(), lit1, lit2)) {
	multvec_j[j] = stamp;
	if (subs_SubsumesIntern(C1,c1fs,c1l,C2,c2fs,c2l)) {
	  cont_BackTrack();
	  return TRUE;
	}
	multvec_j[j] = 0;
      }
      cont_BackTrack();
      if (symbol_Equal(term_TopSymbol(lit1),term_TopSymbol(lit2)) &&
	  fol_IsEquality(fol_Atom(lit1)) &&
	  fol_IsEquality(fol_Atom(lit2)) &&
	  (clause_LiteralIsNotOrientedEquality(clause_GetLiteral(C1,i)) ||
	   clause_LiteralIsNotOrientedEquality(clause_GetLiteral(C2,j)))) {
	cont_StartBinding();
	if (unify_MatchBindings(cont_LeftContext(),
				term_FirstArgument(fol_Atom(lit1)),
				term_SecondArgument(fol_Atom(lit2))) &&
	    unify_MatchBindings(cont_LeftContext(),
				term_SecondArgument(fol_Atom(lit1)),
				term_FirstArgument(fol_Atom(lit2)))) {
	  multvec_j[j] = stamp;
	  if (subs_SubsumesIntern(C1,c1fs,c1l,C2,c2fs,c2l)) {
	    cont_BackTrack();
	    return TRUE;
	  }
	  multvec_j[j] = 0;
	}
	cont_BackTrack();
      }
    }
    j++;
  }
  multvec_i[i] = 0;
  return FALSE;
}


BOOL subs_Subsumes(CLAUSE C1, CLAUSE C2, int ExceptI, int ExceptJ)
/**********************************************************
  INPUT:   Two clauses and for each clause a literal that is
           already bound to each other. If the literal value is negative,
	   a general subsumption test is performed.
  RETURNS: TRUE if the first clause subsumes the second one.
  CAUTION: The weight of the clauses must be up to date!
***********************************************************/
{
  BOOL Result;
  int  c1fs, c1l, c2fs, c2l, lw1, lw2;

  c1fs   = clause_FirstSuccedentLitIndex(C1);
  c1l    = clause_Length(C1);
  c2fs   = clause_FirstSuccedentLitIndex(C2);
  c2l    = clause_Length(C2);
  
  lw1 = (ExceptI >= clause_FirstLitIndex() ?
	 clause_LiteralWeight(clause_GetLiteral(C1,ExceptI)) : 0);
  lw2 = (ExceptJ >= clause_FirstLitIndex() ?
	 clause_LiteralWeight(clause_GetLiteral(C2,ExceptJ)) : 0);

  if (c1l > c2l ||                               /* Multiset restriction */
      (clause_Weight(C1) - lw1) > (clause_Weight(C2) - lw2))
    return FALSE;

  if (++stamp == NAT_MAX) {
    int i;
    stamp = 1;
    for (i = 0; i < subs__MAXLITS; i++)
      multvec_i[i] = multvec_j[i] = 0;
  }

  if (ExceptI >= clause_FirstLitIndex())
    multvec_i[ExceptI] = stamp;
  if (ExceptJ >= clause_FirstLitIndex())
    multvec_j[ExceptJ] = stamp;

  if (c1l > 1 && 
      (!subs_PartnerTest(C1,clause_FirstConstraintLitIndex(C1),c1fs,
			 C2,clause_FirstConstraintLitIndex(C2),c2fs) ||
       !subs_PartnerTest(C1,c1fs,c1l,C2,c2fs,c2l)))
    return FALSE;

#ifdef CHECK
  cont_SaveState();
#endif

  Result = subs_SubsumesIntern(C1,c1fs,c1l,C2,c2fs,c2l);
  
#ifdef CHECK
  cont_CheckState();
#endif

  return Result;
}




BOOL subs_ST(int i, int j, CLAUSE c1, CLAUSE c2)
/**********************************************************
  INPUT:   Integers i,j and two clauses c1 and c2.
           i and j stand for the i-th and the j-th literal 
	   in the clause c1 respectively c2.
  RETURNS: FALSE if c1 does not subsume c2 and TRUE otherwise.
  CAUTION: None.
***********************************************************/
{  
  cont_StartBinding();

  while ((j < clause_Length(c2)) &&
	 !(unify_Match(cont_LeftContext(),
		       clause_GetLiteralTerm(c1,i),
		       clause_GetLiteralTerm(c2,j)))){
    j++;
    cont_BackTrackAndStart();
  }

  if (j >= clause_Length(c2)) {
    cont_BackTrack();
    return FALSE;
  }

  if ((i == (clause_Length(c1)-1)) || subs_ST(i+1, 0, c1, c2))
    return TRUE;
  else
    cont_BackTrack();

  if (++j == clause_Length(c2))
    return FALSE;

  return subs_ST(i, j, c1, c2);
}


BOOL subs_Testlits(CLAUSE c1, CLAUSE c2)
/**********************************************************
  INPUT:   Two clauses c1 and c2.
  RETURNS: FALSE if c1 do not subsume c2 and TRUE otherwise.
  CAUTION: None.
***********************************************************/
{
  TERM   t1;
  int  i,j;
  BOOL found;

  for (i = 0; i < clause_Length(c1); i++){
    j     = 0;
    found = FALSE;
    t1    = clause_GetLiteralTerm(c1,i);

    do {
      cont_StartBinding();
      if (!(found = unify_Match(cont_LeftContext(), t1, clause_GetLiteralTerm(c2,j))))
	j++;
      cont_BackTrack();
      
    } while (!found && (j < clause_Length(c2)));
       
    if (!found)
      return FALSE;
  }

  return TRUE;
}


static LIST subs_GetVariables(TERM t)
/**********************************************************
  INPUT:   A term.
  RETURNS: The list of non bound variables of the term.
  CAUTION: None.
***********************************************************/
{
  LIST scan,insert,symbols,end;

  symbols = term_VariableSymbols(t);
  insert  = symbols;
  end     = list_Nil();

  for (scan = symbols; !list_Empty(scan); scan = list_Cdr(scan)) {
    if (!cont_VarIsBound(cont_LeftContext(), (SYMBOL)list_Car(scan))) {
      end    = insert;
      list_Rplaca(insert, list_Car(scan));
      insert = list_Cdr(insert);
    }
  }

  if (!list_Empty(insert)) {
    list_Delete(insert);
    if (list_Empty(end))
      symbols = list_Nil();
    else
      list_Rplacd(end,list_Nil());
  }

  return(symbols);
}


static BOOL subs_SubsumptionPossible(CLAUSE c1, CLAUSE c2)
/**********************************************************
  INPUT:   Two clauses c1 and c2.
  RETURNS: TRUE if every literal in c1 can independently be
           matched to a literal in c2.
  CAUTION: None.
***********************************************************/
{
  int i,j;

  for (i = 0; i < clause_Length(c1); i++) {
    for (j = 0; j < clause_Length(c2); j++) {
      cont_StartBinding();
      if (unify_Match(cont_LeftContext(),
		      clause_GetLiteralTerm(c1,i),
		      clause_GetLiteralTerm(c2,j)))
	j = clause_Length(c2) + 1;
      cont_BackTrack();
    }
    if (j == clause_Length(c2))
      return FALSE;
  }

  return TRUE;
}


BOOL subs_IdcTestlits(CLAUSE c1, CLAUSE c2, LITPTR* litptr)
/**********************************************************
  INPUT:   Two clauses c1, c2  and a pointer to a litptr structure.
  RETURNS: FALSE if c1 can not independently be matched 
           to c2 and TRUE otherwise.
  CAUTION: A structure is build and litptr points to that structure.
***********************************************************/
{
  LIST  TermIndexlist,VarSymbList,TermSymbList;
  int   i;

  if (subs_SubsumptionPossible(c1,c2)) {
 
    TermIndexlist  = list_Nil();
    VarSymbList    = list_Nil();
    TermSymbList   = list_Nil();
 
    for (i = 0; i < clause_Length(c1); i++) {
      VarSymbList = subs_GetVariables(clause_GetLiteralTerm(c1,i));
   
      if (VarSymbList != list_Nil()){
	TermIndexlist = list_Cons((POINTER)i, TermIndexlist);         
	TermSymbList  = list_Cons(VarSymbList,TermSymbList);
      } 
    }
  
    *litptr = litptr_Create(TermIndexlist,TermSymbList); 

    list_Delete(TermSymbList);
    list_Delete(TermIndexlist);

    return TRUE;
  }
  return FALSE;
}


static BOOL subs_SubsumptionVecPossible(CLAUSE c1, int vec, CLAUSE c2)
/**********************************************************
  INPUT:   Two clauses c1 and c2 and a vector pointer.
  RETURNS: TRUE if all literals in c1 which indexes stand
           in the vector with bottom pointer vec can 
	   independently be matched to a literal in c2.
  CAUTION: None.
***********************************************************/
{
  int i,j;

  for (i = vec; i < vec_ActMax(); i++) {
    for (j = 0; j < clause_Length(c2); j++) {
      cont_StartBinding();
      if (unify_Match(cont_LeftContext(),
		      clause_GetLiteralTerm(c1, (int) vec_GetNth(i)), 
		      clause_GetLiteralTerm(c2,j)))
	j = clause_Length(c2) + 1;
      cont_BackTrack();
    }
    if (j == clause_Length(c2))
      return FALSE;
  }
  
  return TRUE;
}


static BOOL subs_SubsumptionVecPossibleEq(CLAUSE c1, int vec, CLAUSE c2)
/**********************************************************
  INPUT:   Two clauses c1 and c2 and a vector pointer.
  RETURNS: TRUE if all literals in c1 which indexes stand
           in the vector with bottom pointer vec can 
	   independently be matched to a literal in c2.
  CAUTION: None.
***********************************************************/
{
  int    i,j,n;
  TERM   lit1,lit2;
  
  n = clause_Length(c2);
  for (i = vec; i < vec_ActMax(); i++) {
    lit1 = clause_GetLiteralTerm(c1, (int) vec_GetNth(i));
    for (j=0;j<n;j++) {
      lit2 = clause_GetLiteralTerm(c2,j);
      cont_StartBinding();
      if (unify_Match(cont_LeftContext(),lit1,lit2)) {
	j = n + 1;
	cont_BackTrack();
      }
      else {
	cont_BackTrack();
	if (symbol_Equal(term_TopSymbol(lit1),term_TopSymbol(lit2)) &&
	    fol_IsEquality(fol_Atom(lit1)) &&
	    fol_IsEquality(fol_Atom(lit2)) &&
	    (clause_LiteralIsNotOrientedEquality(
               clause_GetLiteral(c1, (int)vec_GetNth(i))) ||
	     clause_LiteralIsNotOrientedEquality(clause_GetLiteral(c2,j)))) {
	  cont_StartBinding();
	  if (unify_Match(cont_LeftContext(),
			  term_FirstArgument(fol_Atom(lit1)),
			  term_SecondArgument(fol_Atom(lit2))) &&
	      unify_Match(cont_LeftContext(),
			  term_SecondArgument(fol_Atom(lit1)),
			  term_FirstArgument(fol_Atom(lit2))))
	      j = n+1;
	  cont_BackTrack();
	}
      }
    }
    if (j==n)
	return FALSE;
  }
  
  return TRUE;
}


static BOOL subs_IdcVecTestlits(CLAUSE c1, int vec, CLAUSE c2, LITPTR* litptr)
/**********************************************************
  INPUT:   Two clauses c1, c2, a pointer to a literal structure and
           a vector pointer.
  RETURNS: FALSE if the literals of c1 which are designated by
           the elements of vec do not subsume c2 and TRUE otherwise.
  CAUTION: A structure is build and litptr points to that structure.
***********************************************************/
{
  LIST  TermIndexlist,VarSymbList,TermSymbList;
  int   i;
  
  if (subs_SubsumptionVecPossible(c1,vec,c2)) {
    
    TermIndexlist  = list_Nil();
    VarSymbList    = list_Nil();
    TermSymbList   = list_Nil();
    
    for (i = vec; i < vec_ActMax(); i++) {
      VarSymbList =
	subs_GetVariables(clause_GetLiteralTerm(c1, (int) vec_GetNth(i)));
   
      if (VarSymbList != list_Nil()){
	TermIndexlist = list_Cons(vec_GetNth(i), TermIndexlist);         
	TermSymbList  = list_Cons(VarSymbList,TermSymbList);
      } 
    }
	    
    *litptr = litptr_Create(TermIndexlist,TermSymbList); 

    list_Delete(TermSymbList);
    list_Delete(TermIndexlist);
	
    return TRUE;
  }
  return FALSE;
}


static BOOL subs_IdcVecTestlitsEq(CLAUSE c1, int vec, CLAUSE c2,
				  LITPTR* litptr)
/**********************************************************
  INPUT:   Two clauses c1, c2, a pointer to a literal structure and
           a vector pointer.
  RETURNS: FALSE if the literals of c1 which are designated by
           the elements of vec do not subsume c2 and TRUE otherwise.
  CAUTION: A structure is build and litptr points to that structure.
***********************************************************/
{
  LIST  TermIndexlist,VarSymbList,TermSymbList;
  int   i;
  
  if (subs_SubsumptionVecPossibleEq(c1,vec,c2)) {
    
    TermIndexlist  = list_Nil();
    VarSymbList    = list_Nil();
    TermSymbList   = list_Nil();
    
    for (i = vec; i < vec_ActMax(); i++){
      VarSymbList =
	subs_GetVariables(clause_GetLiteralTerm(c1, (int) vec_GetNth(i)));
   
      if (VarSymbList != list_Nil()){
	TermIndexlist = list_Cons(vec_GetNth(i), TermIndexlist);         
	TermSymbList  = list_Cons(VarSymbList,TermSymbList);
      } 
    }
	    
    *litptr = litptr_Create(TermIndexlist,TermSymbList); 

    list_Delete(TermSymbList);
    list_Delete(TermIndexlist);
	
    return TRUE;
  }
  return FALSE;
}


static void subs_CompVec(LITPTR litptr)
/**********************************************************
  INPUT:   A  LITPTR pointer.
  RETURNS: None.
  CAUTION: Indexes are pushed on the vector. These indexes build
           a component with respect to the structure litptr and to the 
	   actual bindings.
***********************************************************/
{
  LIST complist, end, scan;
  int  lit,n,i,j;

  n        = litptr_Length(litptr);
  complist = list_Nil();


  if (n > 0){
    for (j = 0; j < n; j++) {
      if (!literal_GetUsed(litptr_Literal(litptr,j))) {
	complist = list_Cons((POINTER)j,complist);
	vec_Push((POINTER)literal_GetLitIndex(litptr_Literal(litptr,j)));
	literal_PutUsed(litptr_Literal(litptr,j), TRUE);
	j = n + 1;
      }
    }

    if (j != n) {
      end = complist;
      for (scan = complist; !list_Empty(scan); scan = list_Cdr(scan)) {
	lit = (int)list_Car(scan);
	for (i = 0; i < n; i++) {
	  if (!literal_GetUsed(litptr_Literal(litptr,i)) &&
	     list_HasIntersection(literal_GetLitVarList(litptr_Literal(litptr,lit)),
				  literal_GetLitVarList(litptr_Literal(litptr,i)))) {
	    list_Rplacd(end,list_List((POINTER)i));
	    end = list_Cdr(end);
	    vec_Push((POINTER)literal_GetLitIndex(litptr_Literal(litptr,i)));
	    literal_PutUsed(litptr_Literal(litptr,i), TRUE);
	  }
	}
      }
      list_Delete(complist);
    }
  }
}


static BOOL subs_StVec(int i, int j, CLAUSE c1, CLAUSE c2)
/**********************************************************
  INPUT:   Integers i,j and two clauses c1 and c2.
           i is a pointer to vector and represents a 
	   literal in clause c1 and j stand for the j-th 
	   literal in the clause c2.
  RETURNS: FALSE if c1 do not subsume c2 and TRUE otherwise.
  CAUTION: None.
***********************************************************/
{  
  int a;
    
  if (j >= clause_Length(c2))
    return FALSE;
    
  a = j;
  
  cont_StartBinding();

  while ((a < clause_Length(c2)) && 
	 !(unify_Match(cont_LeftContext(),
		       clause_GetLiteralTerm(c1, (int) vec_GetNth(i)),
		       clause_GetLiteralTerm(c2,a)))){
    a++;
    cont_BackTrackAndStart();
  }
  
  if (a >= clause_Length(c2)) {
    cont_BackTrack();
    return FALSE;
  }

  if ((i == (vec_ActMax()-1)) || subs_StVec(i+1, 0, c1, c2))
    return TRUE;
  else 
    cont_BackTrack();

  return subs_StVec(i, a+1, c1, c2);
}


static int subs_SearchTop(CLAUSE c1, int vec, CLAUSE c2)
/**********************************************************
  INPUT:   Two clauses c1, c2, a vector pointer vec.
  RETURNS: The index of that literal in c1 which has the least positive
           matching tests with the literals in c2.
  CAUTION: None.
***********************************************************/
{
  int index, i, j, zaehler;

  index = (int)vec_GetNth(vec);

  for (i = vec; i < vec_ActMax(); i++) {
    zaehler = 0;
    j       = 0;
    while (j < clause_Length(c2) && zaehler < 2) {
      cont_StartBinding();
      if (unify_Match(cont_LeftContext(),
		      clause_GetLiteralTerm(c1, (int) vec_GetNth(i)),
		      clause_GetLiteralTerm(c2,j))) {
	zaehler++;
      }
      cont_BackTrack();
      j++;
    }

    if (zaehler == 0 || zaehler == 1) {
      index = (int)vec_GetNth(i);
      return index;
    }
  }
  return index;
}


static BOOL subs_TcVec(CLAUSE c1, int vec, CLAUSE c2)
/**********************************************************
  INPUT:   Two clauses c1, c2, a vector pointer vec.
  RETURNS: FALSE if the literals of c1 which are designated by
           the elements of vec do not subsume c2 and TRUE otherwise.
  CAUTION: None.
***********************************************************/
{
  int a,top_index;
  a    = 0;

  top_index = subs_SearchTop(c1,vec,c2);
    
  do {
    cont_StartBinding();
    while ((a < clause_Length(c2)) &&
	   !(unify_Match(cont_LeftContext(),
			 clause_GetLiteralTerm(c1,top_index),
			 clause_GetLiteralTerm(c2,a)))) {
      a++;
      cont_BackTrackAndStart();
    }
    
    if (a >= clause_Length(c2)){
      cont_BackTrack();
      return FALSE;
    }

    if ((vec - vec_ActMax()) == 1) 
      return TRUE;		
    
    if (subs_InternIdc(c1, vec, c2))
      return TRUE;
    else {
      cont_BackTrack();	/* Dies ist der 'Hurra' Fall.*/
      a++;			
    }

  } while (a < clause_Length(c2));
  
  return FALSE;
}

static BOOL subs_TcVecEq(CLAUSE c1, int vec, CLAUSE c2)
/**********************************************************
  INPUT:   Two clauses c1, c2, a vector pointer vec.
  RETURNS: FALSE if the literals of c1 which are designated by
           the elements of vec do not subsume c2 and TRUE otherwise.
  CAUTION: None.
***********************************************************/
{
  int a,top_index;
  BOOL search;
  TERM lit1,lit2;

  a         = 0;
  top_index = subs_SearchTop(c1,vec,c2);
  lit1      = clause_GetLiteralTerm(c1,top_index);
    
  do {
    search = TRUE;

    while (a < clause_Length(c2) && search) {
      lit2 = clause_GetLiteralTerm(c2,a);
      cont_StartBinding();
      if (unify_Match(cont_LeftContext(),lit1,lit2))
	search = FALSE;
      else {
	if (symbol_Equal(term_TopSymbol(lit1),term_TopSymbol(lit2)) &&
	    fol_IsEquality(fol_Atom(lit1)) &&
	    fol_IsEquality(fol_Atom(lit2)) &&
	    (clause_LiteralIsNotOrientedEquality(clause_GetLiteral(c1,top_index)) ||
	     clause_LiteralIsNotOrientedEquality(clause_GetLiteral(c2,a)))) {
	  cont_BackTrackAndStart();
	  if (unify_Match(cont_LeftContext(),
			  term_FirstArgument(fol_Atom(lit1)),
			  term_SecondArgument(fol_Atom(lit2))) &&
	      unify_Match(cont_LeftContext(),
			  term_SecondArgument(fol_Atom(lit1)),
			  term_FirstArgument(fol_Atom(lit2))))
	    search = FALSE;
	}
	if (search) {
	  a++;
	  cont_BackTrack();
	}
      }
    }
    
    if (a >= clause_Length(c2)) {
      cont_BackTrack();
      return FALSE;
    }

    if ((vec_ActMax() - vec) == 1) 
      return TRUE;		
    
    if (subs_InternIdcEq(c1, vec, c2))
      return TRUE;
    else {
      cont_BackTrack();
      a++;			
    }

  } while (a < clause_Length(c2));
  
  return FALSE;
}


static BOOL subs_InternIdc(CLAUSE c1, int vec, CLAUSE c2)
/**********************************************************
  INPUT:   Two clauses c1, c2, a vector pointer vec.
  RETURNS: FALSE if the literals of c1 which are designed by
           the elements of vec do not subsume c2 and TRUE otherwise.
  CAUTION: 
***********************************************************/
{
  int        locvec;
  LITPTR litptr;
  
  
  if (!subs_IdcVecTestlits(c1,vec,c2,&litptr))
    return FALSE;

  locvec = vec_ActMax();
  
  do {
    subs_CompVec(litptr);	
    if (!vec_IsMax(locvec)) {
      if (!subs_TcVec(c1,locvec,c2)) {
	vec_SetMax(locvec);
	litptr_Delete(litptr);
	return FALSE;
      } 
      else
	vec_SetMax(locvec);
    }
  } while (!litptr_AllUsed(litptr));

  litptr_Delete(litptr);
  
  return TRUE;
}


static BOOL subs_InternIdcEq(CLAUSE c1, int vec, CLAUSE c2)
/**********************************************************
  INPUT:   Two clauses c1, c2, a vector pointer vec.
  RETURNS: FALSE if the literals of c1 which are designed by
           the elements of vec do not subsume c2 and TRUE otherwise.
  CAUTION: 
***********************************************************/
{
  int        locvec;
  LITPTR litptr;
  
  
  if (!subs_IdcVecTestlitsEq(c1,vec,c2,&litptr))
    return FALSE;

  locvec = vec_ActMax();
  
  do {
    subs_CompVec(litptr);	
    if (!vec_IsMax(locvec)) {
      if (!subs_TcVecEq(c1,locvec,c2)) {
	vec_SetMax(locvec);
	litptr_Delete(litptr);
	return FALSE;
      } 
      else
	vec_SetMax(locvec);
    }

  } while (!litptr_AllUsed(litptr));

  litptr_Delete(litptr);
  
  return TRUE;
}


BOOL subs_Idc(CLAUSE c1, CLAUSE c2)
/**********************************************************
  INPUT:   Two clauses c1, c2.
  RETURNS: FALSE if c1 do not subsume c2 and TRUE otherwise.
  CAUTION: 
***********************************************************/
{
  int  i,vec;
  BOOL Result;

  vec = vec_ActMax();

  for (i = 0; i < clause_Length(c1); i++)
    vec_Push((POINTER) i);

  Result = subs_InternIdc(c1,vec,c2);
    
  vec_SetMax(vec);

  cont_Reset();
    
  return Result;
}


BOOL subs_IdcEq(CLAUSE c1, CLAUSE c2)
/**********************************************************
  INPUT:   Two clauses c1, c2.
  RETURNS: FALSE if c1 do not subsume c2 and TRUE otherwise.
  CAUTION: 
***********************************************************/
{
  int  i,vec;
  BOOL Result;

  /*fputs("\n Idc on:  ", stdout); clause_Print(c1);
    putchar('\t'); clause_Print(c2); */ 
  vec = vec_ActMax();

  for (i = 0; i < clause_Length(c1); i++)
    vec_Push((POINTER) i);

  Result = subs_InternIdcEq(c1,vec,c2);
    
  vec_SetMax(vec);

  cont_Reset();

  /*printf(" Result: %s ",(Result ? "TRUE" : "FALSE"));*/

  return Result;
}


BOOL subs_IdcEqMatch(CLAUSE c1, CLAUSE c2, SUBST subst)
/**********************************************************
  INPUT:   Two clauses c1, c2.
  RETURNS: FALSE if c1 do not subsume c2 and TRUE otherwise.
  CAUTION: 
***********************************************************/
{
  int  i,vec;
  BOOL Result;

  /* fputs("\n Idc on:  ", stdout); clause_Print(c1);
     putchar('\t'); clause_Print(c2);   DBG */
  vec = vec_ActMax();

  for (i = 0; i < clause_Length(c1); i++)
    vec_Push((POINTER) i);

  i = 0;        /* Doesn't matter, there is a general cont_Reset below */
  unify_EstablishMatcher(cont_LeftContext(), subst);

  Result = subs_InternIdcEq(c1,vec,c2);
    
  vec_SetMax(vec);

  cont_Reset();

  /*fputs("\nsubs_Idc end: ",stdout); clause_Print(c1); clause_Print(c2); DBG */

  return Result;
}


static BOOL subs_SubsumptionVecPossibleRes(CLAUSE c1, int vec,
					   int beg, int end)
/**********************************************************
  INPUT:   Two clauses c1 and c2 and three vector pointer
           vec,beg and end.
  RETURNS: TRUE if all literals in c1 which indexes stand
           in the vector with bottom pointer vec can 
	   independently be matched to a literal in c2
	   which indexes stand in the vector between the
	   pointers beg and end (exclusive).
  CAUTION: None.
***********************************************************/
{
  int  j,i;

  for (i = vec; i < vec_ActMax(); i++) {
    for (j = beg; j < end; j++){
      cont_StartBinding();
      if (unify_Match(cont_LeftContext(),
		      clause_GetLiteralTerm(c1, (int) vec_GetNth(i)), 
		      clause_GetLiteralTerm(c1, (int) vec_GetNth(j))))
	j = end+1;
      cont_BackTrack();
    }
    if (j == end)
      return FALSE;
  }
  return TRUE;
}


static BOOL subs_IdcVecTestlitsRes(CLAUSE c1, int vec,
				   int beg, int end, LITPTR* litptr)
/**********************************************************
  INPUT:   A clause c1, a pointer to a literal structure and
           three  vector pointer vec, beg and end.
  RETURNS: FALSE if the literals of c1 which are designated by
           the elements of vec can not be matched independently
	   to literal in c2 which are designated by the elements
	   of the vector between the pointers beg and end (exclusive).
  CAUTION: A structure is build and litptr points to that structure.
***********************************************************/
{
  LIST  TermIndexlist,VarSymbList,TermSymbList;
  int   i;
  
  if (subs_SubsumptionVecPossibleRes(c1,vec,beg,end)) {
    
    TermIndexlist  = list_Nil();
    VarSymbList    = list_Nil();
    TermSymbList   = list_Nil();
    
    for (i = vec; i < vec_ActMax(); i++) {
      VarSymbList =
	subs_GetVariables(clause_GetLiteralTerm(c1, (int) vec_GetNth(i)));
      
      if (VarSymbList != list_Nil()) {
	TermIndexlist = list_Cons(vec_GetNth(i), TermIndexlist);         
	TermSymbList  = list_Cons(VarSymbList,TermSymbList);
      } 
    }
    
    *litptr = litptr_Create(TermIndexlist,TermSymbList); 
    
    list_Delete(TermSymbList);
    list_Delete(TermIndexlist);
    
    return TRUE;
  }
  return FALSE;
}


static int subs_SearchTopRes(CLAUSE c1, int vec, int beg, int end)
/**********************************************************
  INPUT:   A clause c1, three vector pointers vec, beg and end.
  RETURNS: The index of that literal in c1 which has the least positive
           matching tests with the literals in c2 with respect to
	   vector and the vector pointers beg and end.
  CAUTION: None.
***********************************************************/
{
  int  index,i,j,zaehler;
    
  index = (int) vec_GetNth(vec);

  for (i = vec; i < vec_ActMax(); i++) {
    zaehler = 0;
    j       = beg;
    while ((j < end) && (zaehler < 2)) {
      cont_StartBinding();
      if (unify_Match(cont_LeftContext(),
		      clause_GetLiteralTerm(c1, (int) vec_GetNth(i)),
		      clause_GetLiteralTerm(c1, (int) vec_GetNth(j)))) {
	zaehler++;
      }
      cont_BackTrack();
      j++;
    }

    if (zaehler == 0 || zaehler == 1) {
      index = (int)vec_GetNth(i);
      return index;
    }
  }
  return index;
}


static BOOL subs_TcVecRes(CLAUSE c1, int vec, int beg, int end)
/**********************************************************
  INPUT:   A clause c1, three vector pointers vec,beg and end.
  RETURNS: FALSE if the literals of c1 which are designated by
           the elements of vec do not subsume c2 with 
	   respect to the vector and the vector pointers
	   beg and end and TRUE otherwise.
  CAUTION: None.
***********************************************************/
{
  int  a,top_index;

  a = beg;

  top_index = subs_SearchTopRes(c1,vec,beg,end);
    
  do {
    cont_StartBinding();
    while ((a < end) && 
	   !unify_Match(cont_LeftContext(),
			clause_GetLiteralTerm(c1,top_index),
			clause_GetLiteralTerm(c1,(int)vec_GetNth(a)))) {
      a++;
      cont_BackTrackAndStart();
    }
    
    if (a >= end){
      cont_BackTrack();
      return FALSE;
    }

    if ((vec - vec_ActMax()) == 1)
      return TRUE;		    
                                    
    if (subs_InternIdcRes(c1, vec, beg, end))
      return TRUE;
    else {
      cont_BackTrack();	
      a++;
    }

  } while (a < end);
  
  return FALSE;
}
       

static BOOL subs_InternIdcRes(CLAUSE c1, int vec, int beg, int end)
/**********************************************************
  INPUT:   A clause c1 and three  vector pointers vec,beg and end.
  RETURNS: FALSE if the literals of c1 which are designated by
           the elements of vec do not subsume c2 with respect
	   to vector and the vector pointers beg and end 
	   and TRUE otherwise.
  CAUTION: None.
***********************************************************/
{
  int        locvec;
  LITPTR litptr;
  
  
  if (!subs_IdcVecTestlitsRes(c1,vec,beg,end,&litptr))
    return FALSE;

  locvec = vec_ActMax();
  
  do {
    subs_CompVec(litptr);	
    if (!vec_IsMax(locvec)) {
      if (!subs_TcVecRes(c1,locvec,beg,end)) {
	vec_SetMax(locvec);
	litptr_Delete(litptr);
	return FALSE;
      } 
      else
	vec_SetMax(locvec);
    }
  } while (!litptr_AllUsed(litptr));

  litptr_Delete(litptr);
  
  return TRUE;
}


BOOL subs_IdcRes(CLAUSE c1, int beg, int end)
/**********************************************************
  INPUT:   A clause c1 and two vector pointers beg and end.
  RETURNS: FALSE if c1 do not subsume c2 with respect to
           vector and the vector pointers beg and end
	   and TRUE otherwise.
  CAUTION: 
***********************************************************/
{
  int  i,vec;
  BOOL Result;
  
  vec = vec_ActMax();
  
  for (i = 0; i < clause_Length(c1); i++)
    vec_Push((POINTER) i);
  
  Result = subs_InternIdcRes(c1, vec, beg, end);
  
  vec_SetMax(vec);
  
  cont_Reset();
  
  return Result;
}


static BOOL subs_TcVecEqExcept(CLAUSE c1, int vec, CLAUSE c2, int i2)
/**********************************************************
  INPUT:   Two clauses c1, c2, a vector pointer vec.
  RETURNS: FALSE if the literals of c1 which are designated by
           the elements of vec do not subsume c2 and TRUE otherwise.
  CAUTION: None.
***********************************************************/
{
  int a,top_index;
  BOOL search;
  TERM lit1,lit2;

  a         = 0;
  top_index = subs_SearchTop(c1,vec,c2);
  lit1      = clause_GetLiteralTerm(c1,top_index);
    
  do {
    search = TRUE;

    while (a < clause_Length(c2) && search) {
      if (a != i2) {
	lit2 = clause_GetLiteralTerm(c2,a);
	cont_StartBinding();
	if (unify_Match(cont_LeftContext(),lit1,lit2))
	    search = FALSE;
	else {
	  if (symbol_Equal(term_TopSymbol(lit1),term_TopSymbol(lit2)) &&
	      fol_IsEquality(fol_Atom(lit1)) &&
	      fol_IsEquality(fol_Atom(lit2)) &&
	      (clause_LiteralIsNotOrientedEquality(clause_GetLiteral(c1,top_index)) ||
	       clause_LiteralIsNotOrientedEquality(clause_GetLiteral(c2,a)))) {
	    cont_BackTrackAndStart();
	    if (unify_Match(cont_LeftContext(),
			    term_FirstArgument(fol_Atom(lit1)),
			    term_SecondArgument(fol_Atom(lit2))) &&
		unify_Match(cont_LeftContext(),
			    term_SecondArgument(fol_Atom(lit1)),
			    term_FirstArgument(fol_Atom(lit2))))
	      search = FALSE;
	  }
	  if (search) {
	    a++;
	    cont_BackTrack();
	  }
	}
      }
      else
	a++;
    }
    
    if (a>=clause_Length(c2)) {
      cont_BackTrack();
      return FALSE;
    }

    if ((vec_ActMax() - vec) == 1) 
      return TRUE;		
    
    if (subs_InternIdcEqExcept(c1, vec, c2, i2))
      return TRUE;
    else {
      cont_BackTrack();
      a++;			
    }

  } while (a < clause_Length(c2));
  
  return FALSE;
}


static BOOL subs_SubsumptionVecPossibleEqExcept(CLAUSE c1, int vec,
						CLAUSE c2, int i2)
/**********************************************************
  INPUT:   Two clauses c1 and c2 and a vector pointer
           and an accept literal index for c2.
  RETURNS: TRUE if all literals in c1 which indexes stand
           in the vector with bottom pointer vec can 
	   independently be matched to a literal in c2.
  CAUTION: None.
***********************************************************/
{
  int    i,j,n;
  TERM   lit1,lit2;

  n = clause_Length(c2);
  for (i = vec; i < vec_ActMax(); i++) {
    lit1 = clause_GetLiteralTerm(c1, (int) vec_GetNth(i));
    for (j = 0; j < n; j++) {
      if (j != i2) { 
	lit2 = clause_GetLiteralTerm(c2,j);
	cont_StartBinding();
	if (unify_Match(cont_LeftContext(),lit1,lit2))
	  j = n + 1;
	else {
	  if (symbol_Equal(term_TopSymbol(lit1),term_TopSymbol(lit2)) &&
	      fol_IsEquality(fol_Atom(lit1)) &&
	      fol_IsEquality(fol_Atom(lit2)) &&
	      (clause_LiteralIsNotOrientedEquality(
                 clause_GetLiteral(c1,(int)vec_GetNth(i))) ||
	       clause_LiteralIsNotOrientedEquality(clause_GetLiteral(c2,j)))) {
	    cont_BackTrackAndStart();
	    if (unify_Match(cont_LeftContext(),
			    term_FirstArgument(fol_Atom(lit1)),
			    term_SecondArgument(fol_Atom(lit2))) &&
		unify_Match(cont_LeftContext(),
			    term_SecondArgument(fol_Atom(lit1)),
			    term_FirstArgument(fol_Atom(lit2))))
	      j = n+1;
	  }
	}
	cont_BackTrack();
      }
    }
    if (j==n)
      return FALSE;
  }
  
  return TRUE;
}


static BOOL subs_IdcVecTestlitsEqExcept(CLAUSE c1, int vec,
					CLAUSE c2, int i2, LITPTR* litptr)
/**********************************************************
  INPUT:   Two clauses c1, c2, a pointer to a literal structure and
           a vector pointer and a literal index i2 in c2
  RETURNS: FALSE if the literals of c1 which are designated by
           the elements of vec do not subsume c2 and TRUE otherwise.
  CAUTION: A structure is build and litptr points to that structure.
  ***********************************************************/
{
  LIST  TermIndexlist,VarSymbList,TermSymbList;
  int   i;
  
  if (subs_SubsumptionVecPossibleEqExcept(c1,vec,c2,i2)) {
    
    TermIndexlist  = list_Nil();
    VarSymbList    = list_Nil();
    TermSymbList   = list_Nil();
    
    for (i = vec; i < vec_ActMax(); i++) {
      VarSymbList =
	subs_GetVariables(clause_GetLiteralTerm(c1, (int) vec_GetNth(i)));
   
      if (VarSymbList != list_Nil()){
	TermIndexlist = list_Cons(vec_GetNth(i), TermIndexlist);         
	TermSymbList  = list_Cons(VarSymbList,TermSymbList);
      } 
    }
	    
    *litptr = litptr_Create(TermIndexlist,TermSymbList); 

    list_Delete(TermSymbList);
    list_Delete(TermIndexlist);
	
    return TRUE;
  }
  return FALSE;
}


static BOOL subs_InternIdcEqExcept(CLAUSE c1, int vec, CLAUSE c2, int i2)
/**********************************************************
  INPUT:   Two clauses c1, c2, a vector pointer vec and a literal
           i2 in c2 which must not be considered
  RETURNS: FALSE if the literals of c1 which are designed by
           the elements of vec do not subsume c2/i2 and TRUE otherwise.
  CAUTION: 
***********************************************************/
{
  int        locvec;
  LITPTR litptr;
  
  
  if (!subs_IdcVecTestlitsEqExcept(c1,vec,c2,i2,&litptr))
    return FALSE;

  locvec = vec_ActMax();
  
  do {
    subs_CompVec(litptr);	
    if (!vec_IsMax(locvec)) {
      if (!subs_TcVecEqExcept(c1,locvec,c2,i2)) {
	vec_SetMax(locvec);
	litptr_Delete(litptr);
	return FALSE;
      } 
      else
	vec_SetMax(locvec);
    }
  } while (!litptr_AllUsed(litptr));

  litptr_Delete(litptr);
  
  return TRUE;
}


BOOL subs_IdcEqMatchExcept(CLAUSE c1, int i1, CLAUSE c2, int i2,
				  SUBST subst)
/**********************************************************
  INPUT:   Two clauses c1, c2 with the indices of two literals
           which need not to be considered and a matcher
  RETURNS: TRUE if (<c1>/<i1>)<subst> subsumes (<c2>/<i2>)<subst>
  CAUTION: 
***********************************************************/
{
  int  i,vec;
  BOOL Result;

  /*fputs("\n IdcEQExcept on:  \n\t", stdout);
    subst_Print(subst); fputs("\n\t", stdout);
    clause_Print(c1); printf(" \t\t%d \n\t",i1); 
    clause_Print(c2);  printf(" \t\t%d \n\t",i2);*/

  if (clause_Length(c1) == 1)
    Result = TRUE;
  else {
    vec = vec_ActMax();

    for (i = 0; i < clause_Length(c1); i++)
      if (i != i1)
	vec_Push((POINTER) i);

    i = 0;    /* Doesn't matter, there is a general cont_Reset below */
    unify_EstablishMatcher(cont_LeftContext(), subst);

    Result = subs_InternIdcEqExcept(c1,vec,c2,i2);

    /* printf("Result : %d",Result); */

    vec_SetMax(vec);

    cont_Reset();
  }

  return Result;
}
