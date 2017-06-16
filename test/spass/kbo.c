/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *         EXTENDED KNUTH BENDIX ORDERING                 * */
/* *                                                        * */
/* *  $Module:   KBO                                        * */ 
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

#include "kbo.h"
#include "order.h"

const int kbo_MINWEIGHT = 1;

/**************************************************************/
/*  Functions to implement an order on terms                  */
/**************************************************************/

static int kbo_ContCompVarCondAndWeightIntern(CONTEXT Context, TERM Term, int Index)
/**************************************************************
  INPUT:   
  EFFECT:  
***************************************************************/
{
  int Weight;

  Weight = 0;
  Term   = cont_Deref(&Context,Term);

  if (term_IsStandardVariable(Term)) {
    ord_VARCOUNT[term_TopSymbol(Term)][Index]++;
    Weight += kbo_MINWEIGHT;
  }
  else {
    LIST Scan;
    Weight += symbol_Weight(term_TopSymbol(Term));
    for (Scan=term_ArgumentList(Term); !list_Empty(Scan); Scan=list_Cdr(Scan))
      Weight += kbo_ContCompVarCondAndWeightIntern(Context, list_Car(Scan), Index);
  }

  return Weight;
}

static int kbo_ContCompVarCondAndWeight(CONTEXT Context1, TERM Term1, BOOL *VarCond1, 
					CONTEXT Context2, TERM Term2, BOOL *VarCond2)
/**************************************************************
  INPUT:   Two contexts, two terms and two pointers to booleans.
  EFFECT:  Sets the booleans with respect to the kbo variable condition.
           Computes the kbo weight difference.
	   The terms are interpreted with respect to the bindings in the respective
	   contexts.
***************************************************************/
{
  SYMBOL MaxVar1,MaxVar2;
  int    i,Weight;

  *VarCond1 = *VarCond2 = TRUE;
  MaxVar1   = cont_TermMaxVar(Context1,Term1);
  MaxVar2   = cont_TermMaxVar(Context2,Term2);

  if (MaxVar1 < MaxVar2)
    MaxVar1 = MaxVar2;

  for (i = 0; i <= MaxVar1; i++) {
    ord_VARCOUNT[i][0] = 0;
    ord_VARCOUNT[i][1] = 0;
  }

  Weight = kbo_ContCompVarCondAndWeightIntern(Context1, Term1, 0);
  Weight = Weight - kbo_ContCompVarCondAndWeightIntern(Context2, Term2, 1);

  for (i = 0; i <= MaxVar1; i++) {
    if (ord_VARCOUNT[i][0] < ord_VARCOUNT[i][1]) {
      *VarCond1 = FALSE;
      if (!*VarCond2)
	return Weight;
    }
    else if (ord_VARCOUNT[i][0] > ord_VARCOUNT[i][1]) {
      *VarCond2 = FALSE;
      if (!*VarCond1)
	return Weight;
    }
  }
  return Weight;  
}


static int kbo_CompVarCondAndWeight(TERM Term1, BOOL *VarCond1, TERM Term2, BOOL *VarCond2)
/**************************************************************
  INPUT:   Two terms and two pointers to booleans.
  EFFECT:  Sets the booleans with respect to the kbo variable condition.
           Computes the kbo weight difference.
***************************************************************/
{
  SYMBOL MaxVar1,MaxVar2;
  TERM   Term;
  LIST   Scan;
  int    i,Stack,Weight;

  *VarCond1 = *VarCond2 = TRUE;
  MaxVar1   = term_MaxVar(Term1);
  MaxVar2   = term_MaxVar(Term2);
  Stack     = stack_Bottom();
  Weight    = 0;

  if (MaxVar1 < MaxVar2)
    MaxVar1 = MaxVar2;

  for (i = 0; i <= MaxVar1; i++) {
    ord_VARCOUNT[i][0] = 0;
    ord_VARCOUNT[i][1] = 0;
  }

  Term = Term1;
  if (term_IsStandardVariable(Term)) {
    ord_VARCOUNT[term_TopSymbol(Term)][0]++;
    Weight += kbo_MINWEIGHT;
  }
  else {
    Weight += symbol_Weight(term_TopSymbol(Term));
    if (term_IsComplex(Term))
      stack_Push(term_ArgumentList(Term));
  }
  while (!stack_Empty(Stack)) {
    Scan = stack_Top();
    Term = (TERM)list_Car(Scan);
    stack_RplacTop(list_Cdr(Scan));
    if (term_IsStandardVariable(Term)) {
      Weight += kbo_MINWEIGHT;
      ord_VARCOUNT[term_TopSymbol(Term)][0]++;
    }
    else {
      Weight += symbol_Weight(term_TopSymbol(Term));
      if (term_IsComplex(Term))
	stack_Push(term_ArgumentList(Term));
    }
    while (!stack_Empty(Stack) && list_Empty(stack_Top()))
      stack_Pop();
  }

  Term = Term2;
  if (term_IsStandardVariable(Term)) {
    Weight -= kbo_MINWEIGHT;
    ord_VARCOUNT[term_TopSymbol(Term)][1]++;
  }
  else {
    Weight -= symbol_Weight(term_TopSymbol(Term));
    if (term_IsComplex(Term))
      stack_Push(term_ArgumentList(Term));
  }
  while (!stack_Empty(Stack)) {
    Scan = stack_Top();
    Term = (TERM)list_Car(Scan);
    stack_RplacTop(list_Cdr(Scan));
    if (term_IsStandardVariable(Term)) {
      Weight -= kbo_MINWEIGHT;
      ord_VARCOUNT[term_TopSymbol(Term)][1]++;
    }
    else {
      Weight -= symbol_Weight(term_TopSymbol(Term));
      if (term_IsComplex(Term))
	stack_Push(term_ArgumentList(Term));
    }
    while (!stack_Empty(Stack) && list_Empty(stack_Top()))
      stack_Pop();
  }

  for (i = 0; i <= MaxVar1; i++) {
    if (ord_VARCOUNT[i][0] < ord_VARCOUNT[i][1]) {
      *VarCond1 = FALSE;
      if (!*VarCond2)
	return Weight;
    }
   if (ord_VARCOUNT[i][0] > ord_VARCOUNT[i][1]) {
      *VarCond2 = FALSE;
      if (!*VarCond1)
	return Weight;
    }
  }
  return Weight;  
}


static ord_RESULT kbo_CompareStruc(TERM Term1, TERM Term2, int WeightDiff)
/**************************************************************
  INPUT:   Two terms where the kbo-variable condition for <Term1> and
           <Term2> is satisfied and <WeightDiff> is the kbo weight difference
	   between <Term1> and <Term2> 
  RETURNS: ord_UNCOMPARABLE, if Term1 and Term2 are uncomparable
	   ord_EQUAL,        if Term1 and Term2 are equal
	   ord_GREATER_THAN, if Term1 is greater than Term2
  CAUTION: The precedence from the order module is used to determine
           the precedence of symbols!
***************************************************************/
{
  LIST   Scan1,Scan2;
  SYMBOL Top1,Top2;

  Top1       = term_TopSymbol(Term1);
  Top2       = term_TopSymbol(Term2);

  if (WeightDiff > 0)
    return ord_GREATER_THAN;
  else 
    if (WeightDiff == 0) {
      if (symbol_IsStandardVariable(Top1)) {
	if (symbol_IsStandardVariable(Top2))
	  return ord_EQUAL;
	else
	  return ord_UNCOMPARABLE;
      }
      else
	if (symbol_IsStandardVariable(Top2) ||
	    symbol_PrecedenceGreater(ord_PRECEDENCE, Top1, Top2))
	  return ord_GREATER_THAN;
	else
	  if (Top1 == Top2) {
	    int    RecWeightDiff;
	    BOOL   T1VarCond, T2VarCond;
	    TERM   RecTerm1,RecTerm2;
	    Scan1 = term_ArgumentList(Term1);
	    Scan2 = term_ArgumentList(Term2);
	    if (symbol_HasProperty(Top1,ORDRIGHT)) {
	      int i;
	      for (i = symbol_Arity(Top1);
		   i > 0 && term_Equal(list_NthElement(Scan1,i),list_NthElement(Scan2,i));
		   i--);
	      if (i > 0) {
		RecTerm1 = (TERM)list_NthElement(Scan1,i);
		RecTerm2 = (TERM)list_NthElement(Scan2,i);
	      }
	      else
		return ord_EQUAL;
	    }
	    else {	      
	      while (!list_Empty(Scan1) && term_Equal(list_Car(Scan1),list_Car(Scan2))) {
		Scan1 = list_Cdr(Scan1);
		Scan2 = list_Cdr(Scan2);
	      }
	      if (list_Empty(Scan1)) /* Implies that list_Empty(Scan2)  */
		return ord_EQUAL;
	      else {
		RecTerm1 = (TERM)list_Car(Scan1);
		RecTerm2 = (TERM)list_Car(Scan2);
	      }
	    }	      
	    RecWeightDiff =  kbo_CompVarCondAndWeight(RecTerm1,&T1VarCond,RecTerm2,&T2VarCond);
	    if (RecWeightDiff >= 0 && T1VarCond)
	      return kbo_CompareStruc(RecTerm1, RecTerm2, RecWeightDiff);
	    else
	      return ord_UNCOMPARABLE;
	  }
	  else
	    return ord_UNCOMPARABLE;
    }
    else
      return ord_UNCOMPARABLE;

  return ord_UNCOMPARABLE;
}
  

ord_RESULT kbo_Compare(TERM Term1, TERM Term2)
/**************************************************************
  INPUT:   Two terms.
  RETURNS: ord_UNCOMPARABLE, if Term1 and Term2 are uncomparable because of
                              different variables,
	   ord_EQUAL,        if Term1 and Term2 are comparable and have the
	                      same weight,
	   ord_GREATER_THAN, if Term1 is greater than Term2 wrt the kbo with
	                      the actual precedence and the given symbol weights,
	   ord_SMALLER_THAN, else.
  CAUTION: The precedence from the order module is used to determine
           the precedence of symbols!
***************************************************************/
{
  int        WeightDiff;
  BOOL       T1VarCond, T2VarCond;
  ord_RESULT Result;

#ifdef CHECK
  if (!term_IsTerm(Term1) || !term_IsTerm(Term2)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In kbo_Compare:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif


  WeightDiff =  kbo_CompVarCondAndWeight(Term1,&T1VarCond,Term2,&T2VarCond);

  if (T1VarCond && !T2VarCond)
    return kbo_CompareStruc(Term1,Term2,WeightDiff);

  if (!T1VarCond && T2VarCond)
    return ord_Not(kbo_CompareStruc(Term2,Term1,-WeightDiff));

  if (T1VarCond && T2VarCond) {
    Result = kbo_CompareStruc(Term1,Term2,WeightDiff);
    if (Result == ord_UNCOMPARABLE)
      return ord_Not(kbo_CompareStruc(Term2,Term1,-WeightDiff));
    else
      return Result;
  }

  return ord_UNCOMPARABLE;
}

static ord_RESULT kbo_ContCompareStruc(CONTEXT Context1, TERM Term1,
				       CONTEXT Context2, TERM Term2,
				       int WeightDiff)
/**************************************************************
  INPUT:   Two contexts and two terms where the kbo-variable condition
           for <Term1> and <Term2> is satisfied and <WeightDiff> is the
	   kbo weight difference between <Term1> and <Term2>.
  RETURNS: ord_UNCOMPARABLE, if Term1 and Term2 are uncomparable
	   ord_EQUAL,        if Term1 and Term2 are equal
	   ord_GREATER_THAN, if Term1 is greater than Term2 
	   The Terms are interpreted with respect to the contexts.
  CAUTION: The precedence from the order module is used to determine
           the precedence of symbols!
***************************************************************/
{
  LIST   Scan1,Scan2;
  SYMBOL Top1,Top2;

  Term1      = cont_Deref(&Context1,Term1);
  Term2      = cont_Deref(&Context2,Term2);
  Top1       = term_TopSymbol(Term1);
  Top2       = term_TopSymbol(Term2);

  if (WeightDiff > 0)
    return ord_GREATER_THAN;
  else 
    if (WeightDiff == 0) {
      if (symbol_IsStandardVariable(Top1)) {
	if (symbol_IsStandardVariable(Top2))
	  return ord_EQUAL;
	else
	  return ord_UNCOMPARABLE;
      }
      else
	if (symbol_IsStandardVariable(Top2) ||
	    symbol_PrecedenceGreater(ord_PRECEDENCE, Top1,Top2))
	  return ord_GREATER_THAN;
	else
	  if (Top1 == Top2) {
	    int    RecWeightDiff;
	    BOOL   T1VarCond, T2VarCond;
	    TERM   RecTerm1,RecTerm2;
	    Scan1 = term_ArgumentList(Term1);
	    Scan2 = term_ArgumentList(Term2);
	    if (symbol_HasProperty(Top1,ORDRIGHT)) {
	      int i;
	      for (i = symbol_Arity(Top1);
		   i > 0 && cont_TermEqual(Context1,list_NthElement(Scan1,i),
					   Context2,list_NthElement(Scan2,i));
		   i--);
	      if (i > 0) {
		RecTerm1 = cont_Deref(&Context1,list_NthElement(Scan1,i));
		RecTerm2 = cont_Deref(&Context2,list_NthElement(Scan2,i));
	      }
	      else
		return ord_EQUAL;
	    }
	    else {	      
	      while (!list_Empty(Scan1) && cont_TermEqual(Context1,list_Car(Scan1),Context2,list_Car(Scan2))) {
		Scan1 = list_Cdr(Scan1);
		Scan2 = list_Cdr(Scan2);
	      }
	      if (list_Empty(Scan1)) /* Implies that list_Empty(Scan2)  */
		return ord_EQUAL;
	      else {
		RecTerm1 = cont_Deref(&Context1,list_Car(Scan1));
		RecTerm2 = cont_Deref(&Context2,list_Car(Scan2));
	      }
	    }	      
	    RecWeightDiff =  kbo_ContCompVarCondAndWeight(Context1,RecTerm1,&T1VarCond,
							  Context2,RecTerm2,&T2VarCond);
	    if (RecWeightDiff >= 0 && T1VarCond)
	      return kbo_ContCompareStruc(Context1, RecTerm1, Context2, RecTerm2, RecWeightDiff);
	    else
	      return ord_UNCOMPARABLE;
	  }
	  else
	    return ord_UNCOMPARABLE;
    }
    else
      return ord_UNCOMPARABLE;

  return ord_UNCOMPARABLE;
}
  

ord_RESULT kbo_ContCompare(CONTEXT Context1, TERM Term1, CONTEXT Context2, TERM Term2)
/**************************************************************
  INPUT:   Two contexts and two terms.
  RETURNS: ord_UNCOMPARABLE, if Term1 and Term2 are uncomparable because of
                              different variables,
	   ord_EQUAL,        if Term1 and Term2 are comparable and have the
	                      same weight,
	   ord_GREATER_THAN, if Term1 is greater than Term2 wrt the kbo with
	                      the actual precedence kbo_Prec and the given 
			      symbol_Weights,
	   ord_SMALLER_THAN, else.
	   The Terms are interpreted with respect to the contexts.
  CAUTION: The precedence from the order module is used to determine
           the precedence of symbols!
***************************************************************/
{
  int        WeightDiff;
  BOOL       T1VarCond, T2VarCond;
  ord_RESULT Result;

#ifdef CHECK
  if (!term_IsTerm(Term1) || !term_IsTerm(Term2)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In kbo_Compare:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif


  WeightDiff =  kbo_ContCompVarCondAndWeight(Context1, Term1, &T1VarCond, Context2, Term2, &T2VarCond);

  if (T1VarCond && !T2VarCond)
    return kbo_ContCompareStruc(Context1,Term1,Context2,Term2,WeightDiff);

  if (!T1VarCond && T2VarCond)
    return ord_Not(kbo_ContCompareStruc(Context2,Term2,Context1,Term1,-WeightDiff));

  if (T1VarCond && T2VarCond) {
    Result = kbo_ContCompareStruc(Context1,Term1,Context2,Term2,WeightDiff);
    if (Result == ord_UNCOMPARABLE)
      return ord_Not(kbo_ContCompareStruc(Context2,Term2,Context1,Term1,-WeightDiff));
    else
      return Result;
  }

  return ord_UNCOMPARABLE;
}

static BOOL kbo_ContGreaterCompareStruc(CONTEXT Context1, TERM Term1,
					CONTEXT Context2, TERM Term2)
/**************************************************************
  INPUT:   Two contexts and two terms where the kbo-variable condition
           for <Term1> and <Term2> is satisfied as well as the
	   weight difference between the terms is zero.
  RETURNS: TRUE if Term1 is greater than Term2.
	   The Terms are interpreted with respect to the contexts.
  CAUTION: The precedence from the order module is used to determine
           the precedence of symbols!
***************************************************************/
{
  LIST   Scan1,Scan2;
  SYMBOL Top1,Top2;

  Term1      = cont_Deref(&Context1,Term1);
  Term2      = cont_Deref(&Context2,Term2);
  Top1       = term_TopSymbol(Term1);
  Top2       = term_TopSymbol(Term2);

  if (symbol_IsStandardVariable(Top1)) {
    if (symbol_IsStandardVariable(Top2))
      return FALSE;
    else
      return FALSE;
  }
  else
    if (symbol_IsStandardVariable(Top2) ||
	symbol_PrecedenceGreater(ord_PRECEDENCE, Top1, Top2))
      return TRUE;
    else
      if (Top1 == Top2) {
	int    RecWeightDiff;
	BOOL   T1VarCond, T2VarCond;
	TERM   RecTerm1,RecTerm2;
	Scan1 = term_ArgumentList(Term1);
	Scan2 = term_ArgumentList(Term2);
	if (symbol_HasProperty(Top1,ORDRIGHT)) {
	  int i;
	  for (i = symbol_Arity(Top1);
	       i > 0 && cont_TermEqual(Context1,list_NthElement(Scan1,i),
				       Context2,list_NthElement(Scan2,i));
	       i--);
	  if (i > 0) {
	    RecTerm1 = cont_Deref(&Context1,list_NthElement(Scan1,i));
	    RecTerm2 = cont_Deref(&Context2,list_NthElement(Scan2,i));
	  }
	  else
	    return FALSE;
	}
	else {	      
	  while (!list_Empty(Scan1) && cont_TermEqual(Context1,list_Car(Scan1),Context2,list_Car(Scan2))) {
	    Scan1 = list_Cdr(Scan1);
	    Scan2 = list_Cdr(Scan2);
	  }
	  if (list_Empty(Scan1)) /* Implies that list_Empty(Scan2)  */
	    return FALSE;
	  else {
	    RecTerm1 = cont_Deref(&Context1,list_Car(Scan1));
	    RecTerm2 = cont_Deref(&Context2,list_Car(Scan2));
	  }
	}	      
	RecWeightDiff =  kbo_ContCompVarCondAndWeight(Context1,RecTerm1,&T1VarCond,
						      Context2,RecTerm2,&T2VarCond);

	if (T1VarCond) {
	  if (RecWeightDiff > 0)
	    return TRUE;
	  else
	    if (RecWeightDiff == 0)
	      return kbo_ContGreaterCompareStruc(Context1, RecTerm1, Context2, RecTerm2);
	}
      }
  
  return FALSE;
}


BOOL kbo_ContGreater(CONTEXT Context1, TERM Term1, CONTEXT Context2, TERM Term2)
/**************************************************************
  INPUT:   Two contexts and two terms.
  RETURNS: TRUE, if Term1 is greater than Term2 wrt the kbo with
           the actual precedence kbo_Prec and the given symbol_Weights
  CAUTION: The precedence from the order module is used to determine
           the precedence of symbols!
***************************************************************/
{
  int        WeightDiff;
  BOOL       T1VarCond, T2VarCond;

#ifdef CHECK
  if ((!term_IsTerm(Term1)) || (!term_IsTerm(Term2)) ) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In kbo_ContGreater:");
    misc_ErrorReport("\n Illegal input.");
    misc_FinishErrorReport();
  }
#endif


  WeightDiff =  kbo_ContCompVarCondAndWeight(Context1, Term1, &T1VarCond, Context2, Term2, &T2VarCond);

  if (T1VarCond) {
    if (WeightDiff > 0)
      return TRUE;
    else
      if (WeightDiff == 0) 
	return kbo_ContGreaterCompareStruc(Context1,Term1,Context2,Term2);
  }
  return FALSE;
}
