/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *         INTERFACE FOR ALL ORDERING IMPLEMENTATIONS     * */
/* *                                                        * */
/* *  $Module:   ORDER                                      * */ 
/* *                                                        * */
/* *  Copyright (C) 1997, 1998, 1999, 2000, 2001            * */
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

#include "flags.h"
#include "order.h"
#include "kbo.h"
#include "rpos.h"
#include "symbol.h"

NAT        ord_VARCOUNT[symbol__MAXSTANDARDVAR][2];
PRECEDENCE ord_PRECEDENCE;


static ord_RESULT ord_CheckDomPred(TERM T1, TERM T2, PRECEDENCE P)
/**************************************************************
  INPUT:   Two terms and a precedence.
  RETURNS: An ordering result with respect to a possible domination
           of leading predicates in <T1> or <T2>.
***************************************************************/
{
  if ((term_IsAtom(T1) && symbol_HasProperty(term_TopSymbol(T1), DOMPRED)) ||
      (term_IsAtom(T2) && symbol_HasProperty(term_TopSymbol(T2), DOMPRED))) {
    if (term_IsAtom(T1)) {
      if (term_IsAtom(T2)) {
	if (symbol_HasProperty(term_TopSymbol(T1), DOMPRED) && 
	    (!symbol_HasProperty(term_TopSymbol(T2), DOMPRED) ||
	     symbol_PrecedenceGreater(P,term_TopSymbol(T1),term_TopSymbol(T2))))
	  return ord_GREATER_THAN;
	if (!symbol_HasProperty(term_TopSymbol(T1), DOMPRED) ||
	    term_TopSymbol(T1) != term_TopSymbol(T2))
	  return ord_SMALLER_THAN;
	/* If the top symbols are equal, do the normal comparison */
      } else {
	/* T1 is an atom, T2 is not, so T1 is greater */
	return ord_GREATER_THAN;
      }
    } else {
      /* T1 is not an atom, so T2 must be an atom */
      return ord_SMALLER_THAN;
    }
  }
  return ord_UNCOMPARABLE;
}


ord_RESULT ord_Compare(TERM T1, TERM T2, FLAGSTORE FlagStore, PRECEDENCE P)
/**************************************************************
  INPUT:   
  RETURNS: 
***************************************************************/
{
  ord_RESULT Aux;

#ifdef CHECK
  if (fol_IsEquality(T1) || fol_IsEquality(T2)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In ord_Compare:");
    misc_ErrorReport("\n Illegal input. One input term is an equality.");
    misc_FinishErrorReport();    
  }
#endif
  
  Aux = ord_CheckDomPred(T1, T2, P);
  if (Aux != ord_UNCOMPARABLE)
    return Aux;
  else {
    ord_PRECEDENCE = P;
    switch(flag_GetFlagValue(FlagStore, flag_ORD)) {
    case flag_ORDKBO:  return kbo_Compare(T1, T2); break;
    case flag_ORDRPOS: return rpos_Compare(T1, T2); break;
    default:
      misc_StartErrorReport(); 
      misc_ErrorReport("\n In ord_Compare:");
      misc_ErrorReport("\n Illegal ordering type.");
      misc_FinishErrorReport();
    }
  }
  return ord_UNCOMPARABLE;
}


BOOL ord_CompareEqual(TERM T1, TERM T2, FLAGSTORE Flags)
/**************************************************************
  INPUT:   Two terms and a flag store.
  RETURNS: TRUE, iff the two terms are equal with respect to the
           reduction ordering selected by the 'flag_ORD' flag.
***************************************************************/
{
  switch(flag_GetFlagValue(Flags, flag_ORD)) {
  case flag_ORDKBO:  return term_Equal(T1, T2); break;
  case flag_ORDRPOS: return rpos_Equal(T1, T2); break;
  default:
    misc_StartErrorReport(); 
    misc_ErrorReport("\n In ord_Compare: Illegal ordering type.");
    misc_FinishErrorReport();
    return FALSE;   /* unreachable code ... */
  }
}

ord_RESULT ord_ContCompare(CONTEXT C1, TERM T1, CONTEXT C2, TERM T2,
			   FLAGSTORE FlagStore, PRECEDENCE P)
{
  ord_RESULT Aux;

#ifdef CHECK
  if (fol_IsEquality(T1) || fol_IsEquality(T2)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In ord_ContCompare:");
    misc_ErrorReport("\n Illegal input. One input term is an equality.");
    misc_FinishErrorReport();
  }
#endif 
  
  Aux = ord_CheckDomPred(T1, T2, P);
  if (Aux != ord_UNCOMPARABLE)
    return Aux;
  else {
    ord_PRECEDENCE = P;
    switch(flag_GetFlagValue(FlagStore, flag_ORD)) {
    case flag_ORDKBO:  return kbo_ContCompare(C1, T1, C2, T2); break;
    case flag_ORDRPOS: return rpos_ContCompare(C1, T1, C2, T2); break;
    default:
      misc_StartErrorReport();
      misc_ErrorReport("\n In ord_ContCompare:");
      misc_ErrorReport("\n Illegal ordering type.");
      misc_FinishErrorReport();
    }
  }
  return ord_UNCOMPARABLE;
}


BOOL ord_ContGreater(CONTEXT C1, TERM T1, CONTEXT C2, TERM T2,
		     FLAGSTORE FlagStore, PRECEDENCE P)
{ 
  ord_RESULT Aux;

#ifdef CHECK
  if (fol_IsEquality(T1) || fol_IsEquality(T2)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In ord_ContGreater:");
    misc_ErrorReport("\n Illegal input. One input term is an equality.");
    misc_FinishErrorReport();
  }
#endif 
  
  Aux = ord_CheckDomPred(T1, T2, P);
  if (Aux != ord_UNCOMPARABLE)
    return (Aux == ord_GREATER_THAN);
  else {
    ord_PRECEDENCE = P;
    switch(flag_GetFlagValue(FlagStore, flag_ORD)) {
    case flag_ORDKBO:  return kbo_ContGreater(C1, T1, C2, T2); break;
    case flag_ORDRPOS: return rpos_ContGreater(C1, T1, C2, T2); break;
    default:
      misc_StartErrorReport();
      misc_ErrorReport("\n In ord_ContGreater:");
      misc_ErrorReport("\n Illegal ordering type.");
      misc_FinishErrorReport();
    }
  }
  return FALSE;   /* This line is never reached ...  */
}


ord_RESULT ord_Not(ord_RESULT Result)
/**************************************************************
  INPUT:   An ord_RESULT
  RETURNS: The negation with respect to argument switching.
***************************************************************/
{
  if (Result == ord_UNCOMPARABLE || Result == ord_EQUAL)
    return Result;

  if (Result == ord_GREATER_THAN)
    return ord_SMALLER_THAN;

  return ord_GREATER_THAN;
}


void ord_Print(ord_RESULT Result)
/**************************************************************
  INPUT:   An ord_Result.
  RETURNS: None, prints the Result as a string to stdout.
***************************************************************/
{
  switch(Result) { 
  case ord_UNCOMPARABLE:  fputs(" uncomparable ",stdout); break;
  case ord_EQUAL:         fputs(" equal ",stdout); break;
  case ord_GREATER_THAN:  fputs(" greater than ",stdout); break;
  case ord_SMALLER_THAN:  fputs(" smaller than ",stdout); break;
  default:                fputs(" Nonsense! ",stdout);
  }
}


ord_RESULT ord_LiteralCompare(TERM Lit1, BOOL Orient1, TERM Lit2, BOOL Orient2,
			      BOOL Check, FLAGSTORE FlagStore,
			      PRECEDENCE Precedence)
/*********************************************************
  INPUT:   Two term literals and two flags indicating whether these
           two literals are oriented equalities. 
	   Additionally a check flag that indicates whether
	   the orientation flags are sufficient or necessary and sufficient:
	   If Check=TRUE then if flag is FALSE it is interpreted that it is not
	   known whether the (possible) equation can be oriented oriented.
	   However, if flag is TRUE we assume that it is oriented.
	   A flag store.
	   A precedence.
  RETURNS: The result if these literals are compared with
           respect to the ordering. Dependent on their sign, the literals
	   are compared as multiset of their topsymbol terms,
	   where any literal is considered to be an equation
	   and non equational literals are considered to be
	   equations with the artificial, non-existent, minimal
	   constant tt.
  EFFECT:  The arguments of the literals are possibly, destructively flipped.
**********************************************************/
{
  ord_RESULT result,auxResult,AuxRl1r2,AuxRr1r2,AuxRr1l2,Comp1,Comp2;
  BOOL       pos1,pos2;

  pos1  = pos2  = TRUE;
  Comp1 = Comp2 = result = ord_UNCOMPARABLE;
  if (symbol_Equal(term_TopSymbol(Lit1),fol_Not())) {
    Lit1 = term_FirstArgument(Lit1);
    pos1 = FALSE;
  }
  if (symbol_Equal(term_TopSymbol(Lit2),fol_Not())) {
    Lit2 = term_FirstArgument(Lit2);
    pos2 = FALSE;
  }
      
  if (fol_IsEquality(Lit1)) {         /* Real equation */
    if (fol_IsEquality(Lit2)) {
      TERM       l1,r1,l2,r2,aux;
      l1 = term_FirstArgument(Lit1);
      r1 = term_SecondArgument(Lit1);
      l2 = term_FirstArgument(Lit2);
      r2 = term_SecondArgument(Lit2);
      if (Orient1 || 
	  (Check && 
	   ((Comp1 = ord_Compare(l1,r1,FlagStore,Precedence)) == ord_GREATER_THAN ||
	    Comp1 == ord_SMALLER_THAN))) {
	if (Comp1 == ord_SMALLER_THAN) {
	  aux = l1; l1 = r1; r1 = aux;
	}
	if (Orient2 ||
	    (Check && 
	     ((Comp2 = ord_Compare(l2,r2,FlagStore,Precedence))==ord_GREATER_THAN ||
	      Comp2 == ord_SMALLER_THAN))) {
	  /* Both equations are oriented */
	  if (Comp2 == ord_SMALLER_THAN) {
	    aux = l2; l2 = r2; r2 = aux;
	  }
	  result = ord_Compare(l1,l2, FlagStore, Precedence);
	  if (result == ord_EQUAL) {
	    if (pos1) {
	      if (pos2)
		return ord_Compare(r1,r2, FlagStore, Precedence);
	      else
		return ord_SMALLER_THAN;
	    }
	    else
	      if (pos2)
		return ord_GREATER_THAN;
	      else
		return ord_Compare(r1,r2, FlagStore, Precedence);
	  }
	  return result;
	}
	else { /* Lit2 is not oriented equation */
	  if (term_Equal(l1,l2)) {
	    result = ord_Compare(r1,r2, FlagStore, Precedence);
	    if (result == ord_EQUAL) {
	      if (pos1 && !pos2)
		return ord_SMALLER_THAN;
	      else
		if (!pos1 && pos2)
		  return ord_GREATER_THAN;
	    }
	    return result;
	  }
	  if (term_Equal(l1,r2)) {
	    result = ord_Compare(r1,l2, FlagStore, Precedence);
	    if (result == ord_EQUAL) {
	      if (pos1 && !pos2)
		return ord_SMALLER_THAN;
	      else
		if (!pos1 && pos2)
		  return ord_GREATER_THAN;
	    }
	    return result;
	  }
	  result    = ord_Compare(l1,l2, FlagStore, Precedence);
	  AuxRl1r2  = ord_Compare(l1,r2, FlagStore, Precedence);
	  if (result == AuxRl1r2)
	    return result;
	  AuxRr1r2  = ord_Compare(r1,r2, FlagStore, Precedence);
	  if (result == AuxRr1r2)
	    return result;
	  if (AuxRl1r2 == AuxRr1r2 && AuxRl1r2 == ord_SMALLER_THAN)
	    return ord_SMALLER_THAN;
	  AuxRr1l2  = ord_Compare(r1,l2, FlagStore, Precedence);
	  if (result == AuxRr1l2 && result == ord_SMALLER_THAN)
	    return  ord_SMALLER_THAN;	  
	  return ord_UNCOMPARABLE;                   
	}
      }
      else /* Lit1 is unorientable equation */
	if (Orient2 ||
	    (Check && 
	     ((Comp2 = ord_Compare(term_FirstArgument(Lit2),
				   term_SecondArgument(Lit2),
				   FlagStore, Precedence) == ord_GREATER_THAN) ||
	      Comp2 == ord_SMALLER_THAN))) {   /* Lit2 is orientable equation */
	  if (Comp2 == ord_SMALLER_THAN) {
	    aux = l2; l2 = r2; r2 = aux;
	  }
	  if (term_Equal(l1,l2)) {
	    result = ord_Compare(r1,r2, FlagStore, Precedence);
	    if (result == ord_EQUAL) {
	      if (pos1 && !pos2)
		return ord_SMALLER_THAN;
	      else
		if (!pos1 && pos2)
		  return ord_GREATER_THAN;
	    }
	    return result;
	  }
	  if (term_Equal(r1,l2)) {
	    result = ord_Compare(l1,r2, FlagStore, Precedence);
	    if (result == ord_EQUAL) {
	      if (pos1 && !pos2)
		return ord_SMALLER_THAN;
	      else
		if (!pos1 && pos2)
		  return ord_GREATER_THAN;
	    }
	    return result;
	  }
	  
	  result    = ord_Compare(l1,l2, FlagStore, Precedence);
	  AuxRr1l2  = ord_Compare(r1,l2, FlagStore, Precedence);
	  if (result == AuxRr1l2)
	    return result;
	  AuxRr1r2  = ord_Compare(r1,r2, FlagStore, Precedence);
	  if (result == AuxRr1r2)
	    return result;
	  if (AuxRr1l2 == AuxRr1r2 && AuxRr1l2 == ord_GREATER_THAN)
	    return ord_GREATER_THAN;
	  AuxRl1r2  = ord_Compare(l1,r2, FlagStore, Precedence);
	  if (result == AuxRl1r2 && result == ord_GREATER_THAN)
	    return  ord_GREATER_THAN;
	  return ord_UNCOMPARABLE;
	}
	else { /* Both literals are unorientable equations */
	  if (term_Equal(l1,l2)) {
	    result = ord_Compare(r1,r2, FlagStore, Precedence);
	    if (result == ord_EQUAL) {
	      if (pos1 && !pos2)
		return ord_SMALLER_THAN;
	      else if (!pos1 && pos2)
		return ord_GREATER_THAN;
	    }
	    return result;
	  }
	  if (term_Equal(r1,l2)) {
	    result = ord_Compare(l1,r2, FlagStore, Precedence);
	    if (result == ord_EQUAL) {
	      if (pos1 && !pos2)
		return ord_SMALLER_THAN;
	      else if (!pos1 && pos2)
		return ord_GREATER_THAN;
	    }
	    return result;
	  }
	  if (term_Equal(l1,r2)) {
	    result = ord_Compare(r1,l2, FlagStore, Precedence); 
	    if (result == ord_EQUAL) {
	      if (pos1 && !pos2)
		return ord_SMALLER_THAN;
	      else if (!pos1 && pos2)
		return ord_GREATER_THAN;
	    }
	    return result;
	  }
	  if (term_Equal(r1,r2)) {
	    result = ord_Compare(l1,l2, FlagStore, Precedence);
	    if (result == ord_EQUAL) {
	      if (pos1 && !pos2)
		return ord_SMALLER_THAN;
	      else if (!pos1 && pos2)
		return ord_GREATER_THAN;
	    }
	    return result;
	  }
	  result    = ord_Compare(l1,l2, FlagStore, Precedence);
	  if (result == ord_UNCOMPARABLE) {
	    result = ord_Compare(l1,r2, FlagStore, Precedence);
	    if (result == ord_UNCOMPARABLE) {
	     if (ord_Compare(r1,l2, FlagStore, Precedence) == ord_GREATER_THAN &&
		 ord_Compare(r1,r2, FlagStore, Precedence) == ord_GREATER_THAN)
	       return ord_GREATER_THAN;
	     return ord_UNCOMPARABLE;
	    }
	    if (result == ord_GREATER_THAN) {
	      if (ord_Compare(r1,l2, FlagStore, Precedence) == ord_GREATER_THAN)
		return ord_GREATER_THAN;
	      return ord_UNCOMPARABLE;
	    }
	    if (result == ord_SMALLER_THAN) {
	      if (ord_Compare(r1,l2, FlagStore, Precedence) == ord_SMALLER_THAN ||
		  ord_Compare(r1,r2, FlagStore, Precedence) == ord_SMALLER_THAN)
		return ord_SMALLER_THAN;
	      return ord_UNCOMPARABLE;
	    }
	  }
	  if (result == ord_GREATER_THAN) {
	    if ((result = ord_Compare(l1,r2,FlagStore,Precedence)) == ord_GREATER_THAN ||
		(auxResult = ord_Compare(r1,r2,FlagStore,Precedence)) == ord_GREATER_THAN)
	      return ord_GREATER_THAN;
	    if (result == ord_UNCOMPARABLE || auxResult == ord_UNCOMPARABLE)
		return ord_UNCOMPARABLE;
	    return ord_SMALLER_THAN;
	  }
	  if (result == ord_SMALLER_THAN) {
	    if ((result = ord_Compare(r1,l2,FlagStore,Precedence)) == ord_SMALLER_THAN ||
		(auxResult = ord_Compare(r1,r2,FlagStore,Precedence)) == ord_SMALLER_THAN)
	      return ord_SMALLER_THAN;
	    if (result == ord_UNCOMPARABLE || auxResult == ord_UNCOMPARABLE)
	      return ord_UNCOMPARABLE;
	    return ord_GREATER_THAN;
	  }
	}
    }
    else {/* Second Atom is not an equation */
      /* They can't be equal ! */
      result = ord_Compare(term_FirstArgument(Lit1),Lit2,FlagStore,Precedence);
      if (!Orient1 && result != ord_GREATER_THAN) { 
	auxResult = ord_Compare(term_SecondArgument(Lit1),Lit2,FlagStore,Precedence);
	if (auxResult == ord_GREATER_THAN)
	  result = ord_GREATER_THAN;
	else if (result != auxResult)
	  result = ord_UNCOMPARABLE;
      }
    }
  }
  else /* First Atom is not an equation */
    /* They can't be equal ! */
    if (fol_IsEquality(Lit2)) {
      result = ord_Compare(Lit1,term_FirstArgument(Lit2), FlagStore, Precedence);
      if (!Orient2 && result != ord_SMALLER_THAN) { 
	auxResult = ord_Compare(Lit1,term_SecondArgument(Lit2),FlagStore,Precedence);
	if (auxResult == ord_SMALLER_THAN)
	  result = ord_SMALLER_THAN;
	else if (result != auxResult)
	  result = ord_UNCOMPARABLE;
      }
    } else { /* None of the atoms is an equation */
      result = ord_Compare(Lit1,Lit2, FlagStore, Precedence);
      if (result == ord_EQUAL) {
	if (pos1 && !pos2)
	  result = ord_SMALLER_THAN;
	else if (!pos1 && pos2)
	  result = ord_GREATER_THAN;
      }
    }

  return result;
}
