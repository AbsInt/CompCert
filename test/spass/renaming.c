/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                   RENAMING                             * */
/* *                                                        * */
/* *  $Module:   RENAMING                                   * */ 
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

#include "renaming.h"

static NAT ren_STAMPID;

static BOOL ren_RootDistanceSmaller(RENAMING,RENAMING);
static BOOL ren_AFactorOk(TERM,TERM);
static BOOL ren_BFactorOk(TERM,TERM);
static BOOL ren_AExtraFactorOk(TERM,TERM);
static BOOL ren_BExtraFactorOk(TERM,TERM);
static BOOL ren_AFactorBigger3(TERM,TERM);
static BOOL ren_BFactorBigger3(TERM,TERM);
static TERM ren_FormulaRename(TERM, LIST, PRECEDENCE, LIST*);
static LIST ren_GetRenamings(TERM, TERM, int);
static BOOL ren_HasBenefit(TERM, TERM, int);
static int  ren_Polarity(TERM);
static BOOL ren_PFactorOk(TERM);
static BOOL ren_PExtraFactorOk(TERM);
static BOOL ren_PFactorBigger3(TERM);
static BOOL ren_NotPFactorOk(TERM);
static BOOL ren_NotPExtraFactorOk(TERM);
static BOOL ren_NotPFactorBigger3(TERM);
static void ren_ResetTermStamp(TERM);

void ren_Init(void)
/**********************************************************
  INPUT:   None.
  RETURNS: void.
  EFFECT:  Initializes the renaming module, in particular
           the stamp id used in this module.
***********************************************************/
{
  ren_STAMPID = term_GetStampID();
}

static BOOL ren_RootDistanceSmaller(RENAMING Ren1, RENAMING Ren2)
{
  return term_RootDistanceSmaller(ren_Hit(Ren1), ren_Hit(Ren2));
}


static void ren_ResetTermStamp(TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: void.
  EFFECT:  The Term stamp of term as well as the stamps of 
           all its subterms (up to atom level) are reset.
***********************************************************/
{
  SYMBOL Top;
 
  term_ResetTermStamp(Term);
  Top = term_TopSymbol(Term);

  if (!symbol_IsPredicate(Top)) {
    if (fol_IsQuantifier(Top))
      ren_ResetTermStamp(term_SecondArgument(Term));
    else {
      LIST Scan;
      for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
	ren_ResetTermStamp(list_Car(Scan)); 
    }
  }
}

static BOOL ren_HasNEquivFathers(TERM Term1, TERM Term2, NAT n)
/**********************************************************
  INPUT:   Two terms, where <Term2> is a proper subterm of <Term1>
           and a number.
  RETURNS: TRUE if <Term2> has a <n>-father that are equivalences
           and  below <Term1>
***********************************************************/
{
  Term2 = term_Superterm(Term2);

  while (Term1 != Term2) {
    if (symbol_Equal(term_TopSymbol(Term2),fol_Equiv())) {
      n--;
      if (n == 0)
	return TRUE;
    }
    Term2 = term_Superterm(Term2);
  }

  return FALSE;
}


static BOOL ren_PExtraFactorOk(TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: TRUE if transforming the term <Term> in positive polarity context
           results in more than two clauses.
***********************************************************/
{ 
  SYMBOL Top;
  TERM   T1, T2;
  BOOL   Ok;

  /* if <Term> has the stamp, it will be renamed */
  if (term_HasTermStamp(Term) || term_IsAtom(Term))
    return FALSE;

  Top = term_TopSymbol(Term);
  
  if (fol_IsQuantifier(Top))
    return ren_PExtraFactorOk(term_SecondArgument(Term));

  if (symbol_Equal(Top,fol_Not()))
    return ren_NotPExtraFactorOk(term_FirstArgument(Term));

  if (symbol_Equal(Top,fol_Equiv())) {
    T1 = term_FirstArgument(Term);
    T2 = term_SecondArgument(Term);
    return (ren_PFactorOk(T1) || ren_NotPFactorOk(T2) ||
	    ren_NotPFactorOk(T1) || ren_PFactorOk(T2));
  }
  if (symbol_Equal(Top,fol_And())) {
    return (list_Length(term_ArgumentList(Term)) > 2 ||
	    ren_PFactorOk(term_FirstArgument(Term)) ||
	    ren_PFactorOk(term_SecondArgument(Term)));
  }
  if (symbol_Equal(Top,fol_Implies())) {
    T1 = term_FirstArgument(Term);
    T2 = term_SecondArgument(Term);
    Ok = ren_PFactorOk(T2);
    return ((ren_NotPFactorOk(T1) && (Ok || ren_NotPExtraFactorOk(T1))) ||
	    (Ok && ren_PExtraFactorOk(T2)));
  }

  if (symbol_Equal(Top,fol_Or())) {
    LIST Scan;
    Ok = FALSE; /* is set to TRUE if a subterm with p factor >1 occurred */
    for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
      if (ren_PFactorOk(list_Car(Scan))) {
	if (Ok || ren_PExtraFactorOk(list_Car(Scan)))
	  return TRUE;  /* if two subterms with p>1 or one subterm with p>2 */
	Ok = TRUE;
      }
  }

  return FALSE; /* <Term> is a trivial disjunction */
}

static BOOL ren_PFactorOk(TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: TRUE if transforming the term <Term> in positive polarity context
           results in more than one clause.
***********************************************************/
{ 
  SYMBOL Top;

  /* if <Term> has the stamp, it will be renamed */
  if (term_HasTermStamp(Term) || term_IsAtom(Term))
    return FALSE;

  Top = term_TopSymbol(Term);
  
  if (symbol_Equal(Top,fol_Equiv()) || symbol_Equal(Top,fol_And()))
    return TRUE;

  if (symbol_Equal(Top,fol_Not()))
    return ren_NotPFactorOk(term_FirstArgument(Term));

  if (fol_IsQuantifier(Top))
    return ren_PFactorOk(term_SecondArgument(Term));

  if (symbol_Equal(Top,fol_Implies()))
    return (ren_NotPFactorOk(term_FirstArgument(Term)) ||
	    ren_PFactorOk(term_SecondArgument(Term)));

  if (symbol_Equal(Top,fol_Or())) {
    LIST Scan;
    for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
      if (ren_PFactorOk(list_Car(Scan)))
	return TRUE;
  }

  return FALSE; /* <Term> is a trivial disjunction */
}


static BOOL ren_NotPExtraFactorOk(TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: TRUE if transforming the term <Term> in negative polarity context
           results in more than two clauses.
***********************************************************/
{ 
  SYMBOL Top;

  /* if <Term> has the stamp, it will be renamed */
  if (term_HasTermStamp(Term) || term_IsAtom(Term))
    return FALSE;

  Top = term_TopSymbol(Term);
  
  if (symbol_Equal(Top,fol_Not()))
    return ren_PExtraFactorOk(term_FirstArgument(Term));

  if (fol_IsQuantifier(Top))
    return ren_NotPExtraFactorOk(term_SecondArgument(Term));

  if (symbol_Equal(Top,fol_Equiv())) {
    TERM T1, T2;
    T1 = term_FirstArgument(Term);
    T2 = term_SecondArgument(Term);
    return (ren_PFactorOk(T1) || ren_PFactorOk(T2) ||
	    ren_NotPFactorOk(T1) || ren_NotPFactorOk(T2));
  }
  if (symbol_Equal(Top,fol_Or())) {
    if (list_Length(term_ArgumentList(Term))>2 ||
	ren_NotPFactorOk(term_FirstArgument(Term)) ||
	ren_NotPFactorOk(term_SecondArgument(Term)))
      return TRUE;
    else
      return FALSE;
  }
  if (symbol_Equal(Top,fol_Implies())) {
    if (ren_PFactorOk(term_FirstArgument(Term)) ||
	ren_NotPFactorOk(term_SecondArgument(Term)))
      return TRUE;
    else
      return FALSE;
  }

  if (symbol_Equal(Top,fol_And())) {
    LIST Scan;
    BOOL Ok;
    Ok = FALSE;
    for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
      if (ren_NotPFactorOk(list_Car(Scan))) {
	if (Ok || ren_NotPExtraFactorOk(list_Car(Scan)))
	  return TRUE; /* if two subterms with -p>1 or one subterm with -p>2 */
	Ok = TRUE;
      }
  }

  return FALSE; /* Either <Term> is a trivial conjunction or an atom */
}


static BOOL ren_NotPFactorOk(TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: TRUE if transforming the term <Term> in negative polarity context
           results in more than one clause.
***********************************************************/
{ 
  SYMBOL Top;

  /* if <Term> has the stamp, it will be renamed */
  if (term_HasTermStamp(Term) || term_IsAtom(Term))
    return FALSE;

  Top = term_TopSymbol(Term);
  
  if (symbol_Equal(Top,fol_Equiv()) || symbol_Equal(Top,fol_Or()) ||
      symbol_Equal(Top,fol_Implies()))
    return TRUE;

  if (symbol_Equal(Top,fol_Not()))
    return ren_PFactorOk(term_FirstArgument(Term));

  if (fol_IsQuantifier(Top))
    return ren_NotPFactorOk(term_SecondArgument(Term));

  if (symbol_Equal(Top,fol_And())) {
    LIST Scan;
    for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
      if (ren_NotPFactorOk(list_Car(Scan)))
	return TRUE;
  }

  return FALSE; /* <Term> is a trivial conjunction */
}


static BOOL ren_PFactorBigger3(TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: TRUE if transforming the term <Term> in positive
           polarity context results in more than three clauses.
***********************************************************/
{
  SYMBOL Top;
  TERM   T1, T2;
  LIST   Scan;
  BOOL   Ok;

  /* if <Term> has the stamp, it will be renamed */
 if (term_HasTermStamp(Term) || term_IsAtom(Term))
    return FALSE;

  Top = term_TopSymbol(Term);

  if (fol_IsQuantifier(Top))
    return ren_PFactorBigger3(term_SecondArgument(Term));

  if (symbol_Equal(Top, fol_Not()))
    return ren_NotPFactorBigger3(term_FirstArgument(Term));

  if (symbol_Equal(Top, fol_And())) {
    unsigned char Limit;  /* invariant: p >= Limit */
    Limit = list_Length(term_ArgumentList(Term));
    for (Scan=term_ArgumentList(Term); !list_Empty(Scan) && Limit<=3;
	 Scan=list_Cdr(Scan))
      if (ren_PFactorOk(list_Car(Scan))) {
	Limit++;
	if (Limit<=3 && ren_PExtraFactorOk(list_Car(Scan))) {
	  Limit++;
	  if (Limit<=3 && ren_PFactorBigger3(list_Car(Scan)))
	    Limit++;  /* works for unary conjunction, too */
	}
      }
    return (Limit>3);
  }
  if (symbol_Equal(Top, fol_Or())) {
    Ok = FALSE; /* is set to TRUE if a subterm with p factor >1 occurred */
    for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
      if (ren_PFactorOk(list_Car(Scan))) {
	if (Ok || ren_PFactorBigger3(list_Car(Scan)))
	  return TRUE;  /* if two subterms with p>1 or one subterm with p>3 */
	Ok = TRUE;
      }
    return FALSE;
  }

  T1 = term_FirstArgument(Term);
  T2 = term_SecondArgument(Term);

  if (symbol_Equal(Top, fol_Implies())) {
    Ok = ren_PFactorOk(T2);
    /* return TRUE if -p(T1)>3 || p(T2)>3 || (-p(T1)>1 && p(T2)>1) */
    return ((ren_NotPFactorOk(T1) && (Ok || ren_NotPFactorBigger3(T1))) ||
	    (Ok && ren_PFactorBigger3(T2)));
  }
  if (symbol_Equal(Top, fol_Equiv())) {
    unsigned char T1Limit, T2Limit, NotT1Limit, NotT2Limit;
    T1Limit    = ren_PFactorOk(T1)    ? 1 : 0;
    NotT1Limit = ren_NotPFactorOk(T1) ? 1 : 0;
    T2Limit    = ren_PFactorOk(T2)    ? 1 : 0;
    NotT2Limit = ren_NotPFactorOk(T2) ? 1 : 0;
    /* return TRUE, if p(T1)>2 || p(T2)>2 || -p(T1)>2 || -p(T2)>2 or at */
    /* least two values out of { p(T1),p(T2),-p(T1),-p(T2) } are > 1    */
    return ((T1Limit + NotT2Limit + NotT1Limit + T2Limit >= 2) ||
	    (T1Limit!=0    && ren_PExtraFactorOk(T1)) ||
	    (T2Limit!=0    && ren_PExtraFactorOk(T2)) ||
	    (NotT1Limit!=0 && ren_NotPExtraFactorOk(T1)) ||
	    (NotT2Limit!=0 && ren_NotPExtraFactorOk(T2)));
  }
  misc_StartErrorReport();
  misc_ErrorReport(" \n In ren_PFactorBigger3: unknown first order operator.");
  misc_FinishErrorReport();
  return FALSE;
}


static BOOL ren_NotPFactorBigger3(TERM Term)
/**********************************************************
  INPUT:   A term.
  RETURNS: TRUE if transforming the term <Term> in negative
           polarity context results in more than three clauses.
***********************************************************/
{
  SYMBOL Top;
  TERM   T1, T2;
  LIST   Scan;
  BOOL   Ok;

  /* if <Term> has the stamp, it will be renamed */
  if (term_HasTermStamp(Term) || term_IsAtom(Term))
    return FALSE;

  Top = term_TopSymbol(Term);

  if (fol_IsQuantifier(Top))
    return ren_NotPFactorBigger3(term_SecondArgument(Term));

  if (symbol_Equal(Top, fol_Not()))
    return ren_PFactorBigger3(term_FirstArgument(Term));

  if (symbol_Equal(Top, fol_Or())) {
    unsigned char Limit;  /* invariant: -p >= Limit */
    Limit = list_Length(term_ArgumentList(Term));
    for (Scan=term_ArgumentList(Term); !list_Empty(Scan) && Limit<=3;
	 Scan=list_Cdr(Scan))
      if (ren_NotPFactorOk(list_Car(Scan))) {
	Limit++;
	if (Limit<=3 && ren_NotPExtraFactorOk(list_Car(Scan))) {
	  Limit++;
	  if (Limit<=3 && ren_NotPFactorBigger3(list_Car(Scan)))
	    Limit++;  /* works for unary disjunction, too */
	}
      }
    return (Limit>3);
  }
  if (symbol_Equal(Top, fol_And())) {
    Ok = FALSE; /* is set to TRUE if a subterm with -p factor >1 occurred */
    for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
      if (ren_NotPFactorOk(list_Car(Scan))) {
	if (Ok || ren_NotPFactorBigger3(list_Car(Scan)))
	  return TRUE; /* if two subterms with -p>1 or one subterm with -p>3 */
	Ok = TRUE;
      }
    return FALSE;
  }

  T1 = term_FirstArgument(Term);
  T2 = term_SecondArgument(Term);

  if (symbol_Equal(Top, fol_Implies())) {
    Ok = ren_NotPFactorOk(T2);
    /* return TRUE if p(T1)>2 || -p(T2)>2 || (p(T1)>1 && -p(T2)>1) */
    return ((ren_PFactorOk(T1) && (Ok || ren_PExtraFactorOk(T1))) ||
	    (Ok && ren_NotPExtraFactorOk(T2)));
  }
  if (symbol_Equal(Top, fol_Equiv())) {
    unsigned char T1Limit, T2Limit, NotT1Limit, NotT2Limit;
    T1Limit    = ren_PFactorOk(T1)    ? 1 : 0;
    NotT1Limit = ren_NotPFactorOk(T1) ? 1 : 0;
    T2Limit    = ren_PFactorOk(T2)    ? 1 : 0;
    NotT2Limit = ren_NotPFactorOk(T2) ? 1 : 0;
    /* return TRUE, if p(T1)>2 || p(T2)>2 || -p(T1)>2 || -p(T2)>2 or at */
    /* least two values out of { p(T1),p(T2),-p(T1),-p(T2) } are > 1    */
    return ((T1Limit + NotT2Limit + NotT1Limit + T2Limit >= 2) ||
	    (T1Limit!=0    && ren_PExtraFactorOk(T1)) ||
	    (T2Limit!=0    && ren_PExtraFactorOk(T2)) ||
	    (NotT1Limit!=0 && ren_NotPExtraFactorOk(T1)) ||
	    (NotT2Limit!=0 && ren_NotPExtraFactorOk(T2)));
  }
  misc_StartErrorReport();
  misc_ErrorReport(" \n In ren_NotPFactorBigger3: unknown first order operator.");
  misc_FinishErrorReport();
  return FALSE;
}


static BOOL ren_AFactorOk(TERM Term1, TERM Term2)
/**********************************************************
  INPUT:   Two terms where <Term1> is a superterm of <Term2>
  RETURNS: TRUE if the A-Factor of Term2 in Term1 is larger than one.
***********************************************************/
{ 
  SYMBOL Top;
  TERM   Super;

  if (Term1 == Term2)
    return FALSE;

  Super = term_Superterm(Term2);
  Top   = term_TopSymbol(Super);    
  
  if (symbol_Equal(Top,fol_And()) || fol_IsQuantifier(Top))
    return ren_AFactorOk(Term1, Super);

  if (symbol_Equal(Top,fol_Not()))
    return ren_BFactorOk(Term1, Super);

  if (symbol_Equal(Top,fol_Or())) {
    LIST Scan;
    TERM Sub;
    for (Scan=term_ArgumentList(Super);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
      Sub = (TERM)list_Car(Scan);
      if (Sub != Term2 && ren_PFactorOk(Sub))
	return TRUE;
    }
    return ren_AFactorOk(Term1, Super);
  }

  if (symbol_Equal(Top,fol_Implies())) {
    if (Term2 == term_FirstArgument(Super))
      return ren_BFactorOk(Term1, Super);
    else
      return (ren_NotPFactorOk(term_FirstArgument(Super)) || ren_AFactorOk(Term1, Super));
  }
  if (symbol_Equal(Top,fol_Equiv())) {
    int Pol;
    Pol = ren_Polarity(Super);
    if (Pol == 0)
      return TRUE;
    if (Term2 == term_FirstArgument(Super))
      Term2 = term_SecondArgument(Super);
    else
      Term2 = term_FirstArgument(Super);

    if (Pol == 1)
      return (ren_NotPFactorOk(Term2) || ren_AFactorOk(Term1,Super));
    else
      return (ren_PFactorOk(Term2) || ren_BFactorOk(Term1,Super));
  }
  misc_StartErrorReport();
  misc_ErrorReport("In ren_AFactorOk: Unknown first order operator.");
  misc_FinishErrorReport();
  return FALSE; 
}

static BOOL ren_AExtraFactorOk(TERM Term1, TERM Term2)
/**********************************************************
  INPUT:   Two terms where <Term1> is a superterm of <Term2>
  RETURNS: TRUE if the A-Factor of Term2 in Term1 is larger than two.
***********************************************************/
{ 
  SYMBOL Top;
  TERM   Super;
  BOOL   Ok;

  if (Term1 == Term2)
    return FALSE;

  Super = term_Superterm(Term2);
  Top   = term_TopSymbol(Super);    
  
  if (symbol_Equal(Top,fol_And()) || fol_IsQuantifier(Top))
    return ren_AExtraFactorOk(Term1, Super);

  if (symbol_Equal(Top,fol_Not()))
    return ren_BExtraFactorOk(Term1, Super);

  if (symbol_Equal(Top,fol_Or())) {
    LIST Scan;
    TERM Sub;
    Ok = FALSE;
    for (Scan=term_ArgumentList(Super);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
      Sub = (TERM)list_Car(Scan);
      if (Sub != Term2 && ren_PFactorOk(Sub)) {
	if (Ok || ren_PExtraFactorOk(Sub))
	  return TRUE;
	Ok = TRUE;
      }
    }
    /* return TRUE if (p>1 for one subterm and a>1) or a>2 */
    return (ren_AFactorOk(Term1,Super) &&
	    (Ok || ren_AExtraFactorOk(Term1, Super)));
  }

  if (symbol_Equal(Top,fol_Implies())) {
    if (Term2 == term_FirstArgument(Super))
      return ren_BExtraFactorOk(Term1, Super);
    else {
      TERM T1;
      T1 = term_FirstArgument(Super);
      Ok = ren_AFactorOk(Term1, Super);
      /* return TRUE if (-p>1 and a>1) or -p>2 or a>2 */
      return ((ren_NotPFactorOk(T1) && (Ok || ren_NotPExtraFactorOk(T1))) ||
	      (Ok && ren_AExtraFactorOk(Term1,Super)));
    }
  }
  if (symbol_Equal(Top,fol_Equiv())) {
    if (Term2 == term_FirstArgument(Super))
      Term2 = term_SecondArgument(Super);
    else
      Term2 = term_FirstArgument(Super);

    switch (ren_Polarity(Super)) {
    case 0:
      return (ren_PFactorOk(Term2) ||  ren_NotPFactorOk(Term2) ||
	      ren_AFactorOk(Term1,Super) ||  ren_BFactorOk(Term1,Super));
    case 1:
      Ok = ren_AFactorOk(Term1, Super);
      return ((ren_NotPFactorOk(Term2) && (Ok || ren_NotPExtraFactorOk(Term2))) ||
	      (Ok && ren_AExtraFactorOk(Term1,Super)));
    case -1:
      Ok = ren_BFactorOk(Term1, Super);
      return ((ren_PFactorOk(Term2) && (Ok || ren_PExtraFactorOk(Term2))) ||
	      (Ok && ren_BExtraFactorOk(Term1,Super)));
    }
  }
  misc_StartErrorReport();
  misc_ErrorReport("In ren_AExtraFactorOk: Unknown first order operator.");
  misc_FinishErrorReport();
  return FALSE; 
}


static BOOL ren_AFactorBigger3(TERM Term1, TERM Term2)
/**********************************************************
  INPUT:   Two terms where <Term1> is a superterm of <Term2>
  RETURNS: TRUE if the A-Factor of Term2 in Term1 is larger than three.
***********************************************************/
{
  TERM   Super;
  SYMBOL Top;
  BOOL   Ok;

  if (Term1 == Term2)
    return FALSE;

  Super = term_Superterm(Term2);
  Top   = term_TopSymbol(Super);    
  
  if (symbol_Equal(Top,fol_And()) || fol_IsQuantifier(Top))
    return ren_AFactorBigger3(Term1, Super);

  if (symbol_Equal(Top,fol_Not()))
    return ren_BFactorBigger3(Term1, Super);

  if (symbol_Equal(Top, fol_Or())) {
    LIST Scan;
    TERM Sub;
    Ok = FALSE; /* is set to TRUE if a subterm with p factor >1 occurred */
    for (Scan=term_ArgumentList(Super);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
      Sub = list_Car(Scan);
      if (Term2 != Sub  && ren_PFactorOk(Sub)) {
	if (Ok || ren_PFactorBigger3(Sub))
	  return TRUE;  /* if two subterms with p>1 or one subterm with p>3 */
	Ok = TRUE;
      }
    }
    return (ren_AFactorOk(Term1, Super) &&
	    (Ok || ren_AFactorBigger3(Term1, Super)));
  }
  if (symbol_Equal(Top,fol_Implies())) {
    if (Term2 == term_FirstArgument(Super))
      return ren_BFactorBigger3(Term1, Super);
    else {
      TERM T1;
      T1 = term_FirstArgument(Super);
      Ok = ren_AFactorOk(Term1, Super);
      /* return TRUE if (-p>1 and a>1) or -p>3 or a>3 */
      return ((ren_NotPFactorOk(T1) && (Ok || ren_NotPFactorBigger3(T1))) ||
	      (Ok && ren_AFactorBigger3(Term1, Super)));
    }
  }
  if (symbol_Equal(Top,fol_Equiv())) {
    if (Term2 == term_FirstArgument(Super))
      Term2 = term_SecondArgument(Super);
    else
      Term2 = term_FirstArgument(Super);

    switch (ren_Polarity(Super)) {
    case 0: {
      unsigned ALimit, BLimit, PLimit, NotPLimit;
      ALimit    = ren_AFactorOk(Term1, Super) ? 1 : 0;
      BLimit    = ren_BFactorOk(Term1, Super) ? 1 : 0;
      PLimit    = ren_PFactorOk(Term2)        ? 1 : 0;
      NotPLimit = ren_NotPFactorOk(Term2)     ? 1 : 0;
      /* return TRUE if a>2 || b>2 || p>2 || -p>2 or at least */
      /* two values out of { a, b, p, -p } are > 1            */
      return ((ALimit + BLimit + PLimit + NotPLimit >= 2) ||
	      (PLimit!=0    && ren_PExtraFactorOk(Term2)) ||
	      (NotPLimit!=0 && ren_NotPExtraFactorOk(Term2)) ||
	      (ALimit!=0    && ren_AExtraFactorOk(Term1,Super)) ||
	      (BLimit!=0    && ren_BExtraFactorOk(Term1,Super)));
    }
    case 1:
      Ok = ren_AFactorOk(Term1, Super);
      /* return TRUE if a>3 || -p>3 || (a>1 && -p>1) */
      return ((ren_NotPFactorOk(Term2) && (Ok || ren_NotPFactorBigger3(Term2))) ||
	      (Ok && ren_AFactorBigger3(Term1, Super)));
    case -1:
      Ok = ren_BFactorOk(Term1, Super);
      /* return TRUE if b>3 || p>3 || (b>1 && p>1) */
      return ((ren_PFactorOk(Term2) && (Ok || ren_PFactorBigger3(Term2))) ||
	      (Ok && ren_BFactorBigger3(Term1, Super)));
    }
  }
  misc_StartErrorReport();
  misc_ErrorReport("In ren_AFactorBigger3: Unknown first order operator.");
  misc_FinishErrorReport();
  return FALSE; 
}


static BOOL ren_BFactorOk(TERM Term1, TERM Term2)
/**********************************************************
  INPUT:   Two terms where <Term1> is a superterm of <Term2>
  RETURNS: TRUE if the B-Factor of Term2 in Term1 is larger than one.
***********************************************************/
{ 
  SYMBOL Top;
  TERM   Super;

  if (Term1 == Term2)
    return FALSE;

  Super = term_Superterm(Term2);
  Top   = term_TopSymbol(Super);    
  
  if (symbol_Equal(Top,fol_Or()) || fol_IsQuantifier(Top))
    return ren_BFactorOk(Term1, Super);

  if (symbol_Equal(Top,fol_Not()))
    return ren_AFactorOk(Term1, Super);

  if (symbol_Equal(Top,fol_And())) {
    LIST Scan;
    TERM Sub;
    for (Scan=term_ArgumentList(Super);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
      Sub = (TERM)list_Car(Scan);
      if (Sub != Term2 && ren_NotPFactorOk(Sub))
	return TRUE;
    }
    return ren_BFactorOk(Term1, Super);
  }

  if (symbol_Equal(Top,fol_Implies())) {
    if (Term2 == term_FirstArgument(Super))
      return (ren_PFactorOk(term_SecondArgument(Super)) || ren_AFactorOk(Term1, Super));
    else
      return ren_BFactorOk(Term1, Super);
  }
  if (symbol_Equal(Top,fol_Equiv())) {
    int Pol;
    Pol = ren_Polarity(Super);
    if (Pol == 0)
      return TRUE;
    if (Term2 == term_FirstArgument(Super))
      Term2 = term_SecondArgument(Super);
    else
      Term2 = term_FirstArgument(Super);

    if (Pol == 1)
      return (ren_PFactorOk(Term2) || ren_AFactorOk(Term1,Super));
    else
      return (ren_NotPFactorOk(Term2) || ren_BFactorOk(Term1,Super));
  }
  misc_StartErrorReport();
  misc_ErrorReport("In ren_BFactorOk: Unknown first order operator.");
  misc_FinishErrorReport();
  return FALSE; 
}

static BOOL ren_BExtraFactorOk(TERM Term1, TERM Term2)
/**********************************************************
  INPUT:   Two terms where <Term1> is a superterm of <Term2>
  RETURNS: TRUE if the B-Factor of Term2 in Term1 is larger than two.
***********************************************************/
{ 
  SYMBOL Top;
  TERM   Super;
  BOOL   Ok;

  if (Term1 == Term2)
    return FALSE;

  Super = term_Superterm(Term2);
  Top   = term_TopSymbol(Super);    
  
  if (symbol_Equal(Top,fol_Or()) || fol_IsQuantifier(Top))
    return ren_BExtraFactorOk(Term1, Super);

  if (symbol_Equal(Top,fol_Not()))
    return ren_AExtraFactorOk(Term1, Super);

  if (symbol_Equal(Top,fol_And())) {
    LIST Scan;
    TERM Sub;
    Ok = FALSE;
    for (Scan=term_ArgumentList(Super);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
      Sub = (TERM)list_Car(Scan);
      if (Sub != Term2 && ren_NotPFactorOk(Sub)) {
	if (Ok || ren_NotPExtraFactorOk(Sub))
	  return TRUE;
	Ok = TRUE;
      }
    }
    /* return TRUE if (-p>1 for one subterm and b>1) or b>2 */
    return (ren_BFactorOk(Term1,Super) &&
	    (Ok || ren_BExtraFactorOk(Term1, Super)));
  }

  if (symbol_Equal(Top,fol_Implies())) {
    if (Term2 == term_FirstArgument(Super)) {
      TERM T2;
      T2 = term_SecondArgument(Super);
      Ok = ren_AFactorOk(Term1, Super);
      /* return TRUE if (p>1 and a>1) or p>2 or a>2 */
      return ((ren_PFactorOk(T2) && (Ok || ren_PExtraFactorOk(T2))) ||
	      (Ok && ren_AExtraFactorOk(Term1, Super)));
    }
    else
      return ren_BExtraFactorOk(Term1, Super);
  }
  if (symbol_Equal(Top,fol_Equiv())) {
    if (Term2 == term_FirstArgument(Super))
      Term2 = term_SecondArgument(Super);
    else
      Term2 = term_FirstArgument(Super);

    switch (ren_Polarity(Super)) {
    case 0:
      return (ren_PFactorOk(Term2) ||  ren_NotPFactorOk(Term2) ||
	      ren_AFactorOk(Term1,Super) ||  ren_BFactorOk(Term1,Super));
    case 1:
      Ok = ren_AFactorOk(Term1, Super);
      return ((ren_PFactorOk(Term2) && (Ok || ren_PExtraFactorOk(Term2))) ||
	      (Ok && ren_AExtraFactorOk(Term1,Super)));
    case -1:
      Ok = ren_BFactorOk(Term1, Super);
      return ((ren_NotPFactorOk(Term2) && (Ok || ren_NotPExtraFactorOk(Term2))) ||
	      (Ok && ren_BExtraFactorOk(Term1,Super)));
    }
  }
  misc_StartErrorReport();
  misc_ErrorReport("In ren_BExtraFactorOk: Unknown first order operator.");
  misc_FinishErrorReport();
  return FALSE; 
}

static BOOL ren_BFactorBigger3(TERM Term1, TERM Term2)
/**********************************************************
  INPUT:   Two terms where <Term1> is a superterm of <Term2>
  RETURNS: TRUE if the B-Factor of Term2 in Term1 is larger than three.
***********************************************************/
{
  TERM   Super;
  SYMBOL Top;
  BOOL   Ok;

  if (Term1 == Term2)
    return FALSE;

 Super = term_Superterm(Term2);
 Top   = term_TopSymbol(Super);
 
  if (fol_IsQuantifier(Top) || symbol_Equal(Top, fol_Or()))
    return ren_BFactorBigger3(Term1, Super);

  if (symbol_Equal(Top, fol_Not()))
    return ren_AFactorBigger3(Term1, Super);

  if (symbol_Equal(Top, fol_And())) {
    LIST Scan;
    TERM Sub;
    Ok = FALSE; /* is set to TRUE if a subterm with -p factor >1 occurred */
    for (Scan=term_ArgumentList(Super);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
      Sub = list_Car(Scan);
      if (Term2 != Sub  && ren_NotPFactorOk(Sub)) {
	if (Ok || ren_NotPFactorBigger3(Sub))
	  return TRUE; /* if two subterms with -p>1 or one subterm with -p>3 */
	Ok = TRUE;
      }
    }
    return (ren_BFactorOk(Term1, Super) &&
	    (Ok || ren_BFactorBigger3(Term1, Super)));
  }
  if (symbol_Equal(Top,fol_Implies())) {
    if (Term2 == term_FirstArgument(Super)) {
      TERM T2;
      T2 = term_SecondArgument(Super);
      Ok = ren_AFactorOk(Term1, Super);
      /* return TRUE if (p>1 and a>1) or p>3 or a>3 */
      return ((ren_PFactorOk(T2) && (Ok || ren_PFactorBigger3(T2))) ||
	      (Ok && ren_AFactorBigger3(Term1, Super)));
    }
    else
      return ren_BFactorBigger3(Term1, Super);
  }
  if (symbol_Equal(Top,fol_Equiv())) {
    if (Term2 == term_FirstArgument(Super))
      Term2 = term_SecondArgument(Super);
    else
      Term2 = term_FirstArgument(Super);

    switch (ren_Polarity(Super)) {
    case 0: {
      unsigned ALimit, BLimit, PLimit, NotPLimit;
      ALimit    = ren_AFactorOk(Term1, Super) ? 1 : 0;
      BLimit    = ren_BFactorOk(Term1, Super) ? 1 : 0;
      PLimit    = ren_PFactorOk(Term2)        ? 1 : 0;
      NotPLimit = ren_NotPFactorOk(Term2)     ? 1 : 0;
      /* return TRUE if a>2 || b>2 || p>2 || -p>2 or at least */
      /* two values out of { a, b, p, -p } are > 1            */
      return ((ALimit + BLimit + PLimit + NotPLimit >= 2) ||
	      (PLimit!=0    && ren_PExtraFactorOk(Term2)) ||
	      (NotPLimit!=0 && ren_NotPExtraFactorOk(Term2)) ||
	      (ALimit!=0    && ren_AExtraFactorOk(Term1,Super)) ||
	      (BLimit!=0    && ren_BExtraFactorOk(Term1,Super)));
    }
    case 1:
      Ok = ren_AFactorOk(Term1, Super);
      /* return TRUE if a>3 || -p>3 || (a>1 && -p>1) */
      return ((ren_PFactorOk(Term2) && (Ok || ren_PFactorBigger3(Term2))) ||
	      (Ok && ren_AFactorBigger3(Term1, Super)));
    case -1:
      Ok = ren_BFactorOk(Term1, Super);
      /* return TRUE if b>3 || p>3 || (b>1 && p>1) */
      return ((ren_NotPFactorOk(Term2) && (Ok || ren_NotPFactorBigger3(Term2))) ||
	      (Ok && ren_BFactorBigger3(Term1, Super)));
    }
  }
  misc_StartErrorReport();
  misc_ErrorReport("In ren_BFactorBigger3: Unknown first order operator.");
  misc_FinishErrorReport();
  return FALSE; 
}


static BOOL ren_HasBenefit(TERM Term1, TERM Term2, int Pol)
/**********************************************************
  INPUT:   Two terms and the polarity of the 2nd term in the overall formula.
  RETURNS: TRUE if renaming <Term1> in <Term2> results in a positive benefit.
  CAUTION: It is assumed that all superterms are set !
***********************************************************/
{ 
  BOOL  PFacOk, NotPFacOk, AFacOk, BFacOk;
  
  switch (Pol) {
    
  case 0:
    PFacOk    = ren_PFactorOk(Term2);
    NotPFacOk = ren_NotPFactorOk(Term2);
    AFacOk    = ren_AFactorOk(Term1,Term2);
    BFacOk    = ren_BFactorOk(Term1,Term2);
    return ((AFacOk && BFacOk && PFacOk && NotPFacOk) ||
	    (AFacOk && PFacOk && (ren_PExtraFactorOk(Term2) || ren_AExtraFactorOk(Term1,Term2))) ||
	    (BFacOk && NotPFacOk && (ren_NotPExtraFactorOk(Term2) || ren_BExtraFactorOk(Term1,Term2))));
    break;

  case 1:
    return (ren_PFactorOk(Term2) && ren_AFactorOk(Term1,Term2));
    break;

  case -1:
    return (ren_NotPFactorOk(Term2) && ren_BFactorOk(Term1,Term2));
    break;
  }
  misc_StartErrorReport();
  misc_ErrorReport("In ren_HasBenefit: Unknown polarity.");
  misc_FinishErrorReport();
  return FALSE;  
}

static BOOL ren_HasNonZeroBenefit(TERM Term1, int Pol1, TERM Term2, int Pol2)
/**********************************************************
  INPUT:   Two terms and the polarity of the terms in the overall formula.
  RETURNS: TRUE if renaming <Term1> in <Term2> results in non-zero  positive benefit.
  CAUTION: It is assumed that all superterms are set !
***********************************************************/
{ 
  BOOL  PFacOk, NotPFacOk, AFacOk, BFacOk, PEFacOk, NotPEFacOk, AEFacOk, BEFacOk;
  switch (Pol2) {
  case 0:
    PFacOk     = ren_PFactorOk(Term2);
    NotPFacOk  = ren_NotPFactorOk(Term2);
    AFacOk     = ren_AFactorOk(Term1,Term2);
    BFacOk     = ren_BFactorOk(Term1,Term2);
    PEFacOk    = PFacOk    && ren_PExtraFactorOk(Term2);
    NotPEFacOk = NotPFacOk && ren_NotPExtraFactorOk(Term2);
    AEFacOk    = AFacOk    && ren_AExtraFactorOk(Term1,Term2);
    BEFacOk    = BFacOk    && ren_BExtraFactorOk(Term1,Term2);
    
    return ((AFacOk && BFacOk && PFacOk && NotPFacOk && (AEFacOk || BEFacOk || PEFacOk || NotPEFacOk)) || 
	    (PEFacOk && AEFacOk) || (NotPEFacOk && BEFacOk) ||
	    (AFacOk    && ren_PFactorBigger3(Term2)) ||
	    (BFacOk    && ren_NotPFactorBigger3(Term2)) ||
	    (PFacOk    && ren_AFactorBigger3(Term1, Term2)) ||
	    (NotPFacOk && ren_BFactorBigger3(Term1, Term2)) ||
	    /* The following conditions don't imply benefit > 0, but allow */
	    /* some additional renamings with benefit 0.                   */
	    (Pol1 == 0 && (symbol_Equal(term_TopSymbol(Term2),fol_Equiv()) ||
			   ren_HasNEquivFathers(Term1,Term2,1))) ||
	    ren_HasNEquivFathers(Term1,Term2,2));
    break;

  case 1:
    /* return TRUE if (p>1 && a>2) || (p>2 && a>1) */
    AFacOk = ren_AFactorOk(Term1,Term2);
    return ((ren_PFactorOk(Term2) && (AFacOk || ren_AFactorOk(Term1,Term2))) ||
	    (AFacOk && ren_AExtraFactorOk(Term1,Term2)));
    break;

  case -1:
    /* return TRUE if (-p>1 && b>2) || (-p>2 && b>1) */
    BFacOk = ren_BFactorOk(Term1,Term2);
    return ((ren_NotPFactorOk(Term2) && (BFacOk || ren_NotPExtraFactorOk(Term2))) ||
	    (BFacOk && ren_BExtraFactorOk(Term1,Term2)));
    break;
  }
  misc_StartErrorReport();
  misc_ErrorReport("In ren_HasNonZeroBenefit: Unknown polarity.");
  misc_FinishErrorReport();
  return FALSE;  
}


static LIST ren_GetRenamings(TERM Term1, TERM Term2, int Pol) 
/**********************************************************
  INPUT:   Two terms and the polarity of the 2nd term in the overall formula.
  RETURNS: The list of subterms below <Term2> that have a positive renaming
           benefit.
  EFFECT:  All renamed formulae are stamped.
***********************************************************/
{ 
  SYMBOL Top;
  LIST   Result,Scan;

  Result = list_Nil();

  /* Don't rename formulae starting with "not" */
  while (symbol_Equal(term_TopSymbol(Term2), fol_Not())) {
    Term2 = term_FirstArgument(Term2);
    Pol = -Pol;
  }

  if (term_IsAtom(Term2))
    return Result;

  Top = term_TopSymbol(Term2);

  /* Don't rename arguments of a quantifier */
  if (term_Superterm(Term2) &&
      !fol_IsQuantifier(term_TopSymbol(term_Superterm(Term2))) &&
      ren_HasBenefit(Term1, Term2, Pol)) {
    Result = list_Cons(Term2,Result);
    term_SetTermStamp(Term2);
    Term1 = Term2;
  }

  if (fol_IsQuantifier(Top))
    Result = list_Nconc(Result,ren_GetRenamings(Term1, term_SecondArgument(Term2), Pol));
  else if (symbol_Equal(Top,fol_And()) || symbol_Equal(Top,fol_Or()))
    for (Scan=term_ArgumentList(Term2);!list_Empty(Scan);Scan=list_Cdr(Scan))
      Result = list_Nconc(Result,ren_GetRenamings(Term1,list_Car(Scan),Pol));
  else if (symbol_Equal(Top,fol_Implies())) {
    Result = list_Nconc(Result,ren_GetRenamings(Term1,term_FirstArgument(Term2),-Pol));
    Result = list_Nconc(Result,ren_GetRenamings(Term1,term_SecondArgument(Term2),Pol));
  } else if (symbol_Equal(Top,fol_Equiv())) {
    Result = list_Nconc(Result, ren_GetRenamings(Term1,term_FirstArgument(Term2),0));
    Result = list_Nconc(Result, ren_GetRenamings(Term1,term_SecondArgument(Term2),0));
  } else {
    misc_StartErrorReport();
    misc_ErrorReport("In ren_GetRenamings: Unknown first-order operator.");
    misc_FinishErrorReport();
  }

  return Result;
}

static int ren_Polarity(TERM Term)
/**********************************************************
  INPUT:   A term where the existence of superterms is assumed!.
  RETURNS: The polarity of Term with respect to its superterms.
***********************************************************/
{
  TERM SuperTerm;

  SuperTerm = term_Superterm(Term);

  if (SuperTerm) {
    SYMBOL Top;
    Top = term_TopSymbol(SuperTerm);
    if (symbol_Equal(Top,fol_And()) || symbol_Equal(Top,fol_Or()) ||
	fol_IsQuantifier(Top))
      return ren_Polarity(SuperTerm);
    if (symbol_Equal(Top,fol_Not()))
      return (-ren_Polarity(SuperTerm));
    if (symbol_Equal(Top,fol_Equiv()))
      return 0;
    if (symbol_Equal(Top,fol_Implies())) {
      if (Term == term_FirstArgument(SuperTerm))
	return (-ren_Polarity(SuperTerm));
      else
	return ren_Polarity(SuperTerm);
    }
    misc_StartErrorReport();
    misc_ErrorReport("In ren_Polarity: Unknown first-order operator.");
    misc_FinishErrorReport();
  }

  return 1;
}


static LIST ren_RemoveTerm(TERM Term, LIST Renamings)
/**********************************************************
  INPUT:   A formula and a list of renamings.
  RETURNS: The renaming list where  <Term> is removed from
           the renamings.
  CAUTION: The list and the renamings are destructively changed.
***********************************************************/
{
  LIST     Scan;
  RENAMING Renaming;

  /* Remove the Term from all renamings. In case the Hit term equals <Term> */
  /* turn the renaming into a general renaming */
  for (Scan=Renamings;!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    Renaming = (RENAMING)list_Car(Scan);
    if (ren_Hit(Renaming) == Term) {
      if (list_Empty(ren_Matches(Renaming))) {
	ren_Delete(Renaming);
	list_Rplaca(Scan, NULL);
      }
      else 
	ren_SetGeneral(Renaming, TRUE);
    }
    else
      ren_SetMatches(Renaming, list_PointerDeleteElement(ren_Matches(Renaming), Term));
  }
  
  /* Take care for the NULL pointers */
  Renamings = list_PointerDeleteElement(Renamings, NULL);

  return Renamings;
}

static LIST ren_RemoveAllSubterms(TERM Term, LIST Renamings)
/**********************************************************
  INPUT:   A formula and a list of renamings.
  RETURNS: The renaming list where  <Term> and all its subterms are
           removed from the renamings.
  CAUTION: The list and the renamings are destructively changed.
***********************************************************/
{
  Renamings = ren_RemoveTerm(Term, Renamings);
  
  if (!symbol_IsPredicate(term_TopSymbol(Term))) {
    if (fol_IsQuantifier(term_TopSymbol(Term)))
      Renamings = ren_RemoveAllSubterms(term_SecondArgument(Term), Renamings);
    else {
      LIST Scan;
      for (Scan=term_ArgumentList(Term);!list_Empty(Scan);Scan=list_Cdr(Scan))
	Renamings = ren_RemoveAllSubterms(list_Car(Scan), Renamings);
    }
  }

  return Renamings;
}



static LIST ren_SolveDependencies(LIST Renamings)
/**********************************************************
  INPUT:   A list of renamings sorted by depth of the hits.
  RETURNS: The renaming list where dependences are solved, i.e., if
           a formula occurs in the matches of some renaming, then
	   all its subterms are removed from other renamings, since
	   the formulae of additional matches completely disappear
	   after application of the renaming.
           In case a subterm is the hit of another renaming but this
           renaming has further matches, the further matches are turned
           into new individual renamings.
  CAUTION: The list and the renamings are destructively changed.
***********************************************************/
{
  LIST     Scan;
  RENAMING Renaming;
  TERM     ActMatch;

  if (list_Empty(Renamings))
    return Renamings;

  Renaming = (RENAMING)list_Car(Renamings);
  for (Scan=ren_Matches(Renaming);!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    ActMatch = (TERM)list_Car(Scan);
    list_Rplacd(Renamings, ren_RemoveAllSubterms(ActMatch, list_Cdr(Renamings)));
  }
  list_Rplacd(Renamings, ren_SolveDependencies(list_Cdr(Renamings)));

  return Renamings;
}


static TERM ren_FormulaRename(TERM Term, LIST Renamings, PRECEDENCE Precedence,
			      LIST *SkolemSymbols) 
/**********************************************************
  INPUT:   A term and a list of renamings where all
           dependencies between the renaming terms are
	   solved and a precedence.
  RETURNS: The renamed formula with respect to the renaming
           list and all newly introduced Skolem symbols for
	   renamings are added to <SkolemSymbols>.
  EFFECT:  New Skolem predicates are created, and their precedence
           is set in <Precedence>.
  CAUTION: The formula <Term> is destructively changed.
           The renamings are destructively changed.
***********************************************************/
{
  TERM     Result,ActTerm,Hit,DefTerm,Superterm,NewTerm;
  LIST     Scan,FreeVariables,Args,AllMatches;
  SYMBOL   ActSymbol;
  RENAMING Renaming;
 
  DefTerm    = (TERM)NULL;
  AllMatches = list_Nil();

  if (!list_Empty(Renamings))
    Result = term_Create(fol_And(),list_List(Term));
  else
    return Term;

  ActSymbol = 0;

  while (!list_Empty(Renamings)) {

    Renaming       = (RENAMING)list_Car(Renamings); 
    Renamings      = list_Cdr(Renamings);
    Hit            = ren_Hit(Renaming);
    Superterm      = term_Superterm(Hit);
    FreeVariables  = fol_FreeVariables(Hit);
    ActSymbol      = symbol_CreateSkolemPredicate(list_Length(FreeVariables),
						  Precedence);
    *SkolemSymbols = list_Cons((POINTER)ActSymbol,*SkolemSymbols);

    /* printf("\n");fol_PrettyPrintDFG(ren_Hit(Renaming));printf("\n");*/

    /* Install Definition */
    if (ren_General(Renaming))     /* for general renamings the hit formula will be eventually deleted */
      Hit = term_Copy(Hit);
    NewTerm = term_Create(ActSymbol, term_CopyTermList(FreeVariables));
    switch (ren_OverallPolarity(Renaming)) {
    case 0:
      DefTerm = term_Create(fol_Equiv(),list_Cons(term_Copy(NewTerm),list_List(Hit)));
      break;
	  
    case 1:
      DefTerm = term_Create(fol_Implies(),list_Cons(term_Copy(NewTerm),list_List(Hit)));
      break;
	  
    case -1:
      DefTerm = term_Create(fol_Implies(),list_Cons(Hit,list_List(term_Copy(NewTerm))));
      break;
    }
    term_RplacSuperterm(term_FirstArgument(DefTerm),DefTerm);
    term_RplacSuperterm(term_SecondArgument(DefTerm),DefTerm);
    if (!list_Empty(FreeVariables))
      DefTerm = fol_CreateQuantifier(fol_All(), term_CopyTermList(FreeVariables),
				     list_List(DefTerm));
    term_RplacArgumentList(Result,list_Nconc(term_ArgumentList(Result),list_List(DefTerm)));

    /* Replace hit if renaming is not general */
    if (!ren_General(Renaming)) {
      term_RplacSuperterm(NewTerm, Superterm);
      for (Args=term_ArgumentList(Superterm);!list_Empty(Args); Args=list_Cdr(Args)) 
	if ((TERM)list_Car(Args) == Hit) {
	  list_Rplaca(Args, NewTerm);
	  break;
	}    
    }
    else
      term_Delete(NewTerm);


    for (Scan=ren_Matches(Renaming); !list_Empty(Scan); Scan=list_Cdr(Scan)) {
      
      ActTerm   = (TERM)list_Car(Scan);
      Superterm = term_Superterm(ActTerm);

      /* Always make new predicate term */
      NewTerm   = term_Create(ActSymbol, term_CopyTermList(FreeVariables));
      /* Bind the variables correctly */
      /*puts("\n"); fol_PrettyPrintDFG(Result);
	printf("\n Hit:\n"); term_PrettyPrint(Hit);
	printf("\n ActTerm:\n"); term_PrettyPrint(ActTerm); printf("\n");*/
      cont_StartBinding();
      if (unify_MatchFlexible(cont_LeftContext(), Hit, ActTerm))
	cont_ApplyBindingsModuloMatching(cont_LeftContext(), NewTerm, TRUE);
      else {
	misc_StartErrorReport();
	misc_ErrorReport("\n In ren_FormulaRename: Further match is no instance of hit.\n");
	misc_FinishErrorReport();
      }
      cont_BackTrack();

      /* Now replace match */
      term_RplacSuperterm(NewTerm, Superterm);
      for (Args=term_ArgumentList(Superterm);!list_Empty(Args); Args=list_Cdr(Args)) 
	if (list_Car(Args) == ActTerm) {
	  list_Rplaca(Args, NewTerm);
	  break;
	}  
    }
    AllMatches = list_Nconc(ren_Matches(Renaming), AllMatches); /* Delete later due to dependencies */
    ren_SetMatches(Renaming, list_Nil());
    list_Delete(FreeVariables);
  }
  list_DeleteWithElement(AllMatches, (void (*)(POINTER)) term_Delete);
  return Result;			   
}

static LIST ren_FreeRenaming(LIST Renamings)
/**********************************************************
  INPUT:   A list of  renamings.
  RETURNS: The list of candidates without renamings that have
           benefit zero.
  CAUTION: Destructive.
***********************************************************/
{
  LIST     Scan;
  TERM     Father, Term;
  RENAMING Candidate;

  for (Scan=Renamings;!list_Empty(Scan);Scan=list_Cdr(Scan)) {
    Candidate = (RENAMING)list_Car(Scan);
    if (list_Empty(ren_Matches(Candidate))) {
      Term   = ren_Hit(Candidate);
      Father = term_Superterm(Term);
      while (!term_HasTermStamp(Father) && term_Superterm(Father)) {
	Father = term_Superterm(Father);
      }
	
      term_ResetTermStamp(Term); /* Needed for P-Factor check */
      if (ren_General(Candidate) ||                                /* a general renaming without matches is useless */
	  !ren_HasNonZeroBenefit(Father, ren_Polarity(Father),  
				 Term, ren_OverallPolarity(Candidate))) {
	ren_Delete(Candidate);
	list_Rplaca(Scan,NULL);
      } else {
	/* Term will be renamed */
	term_SetTermStamp(Term); /* Undo temporary change */
      }
    }
  }

  Renamings = list_PointerDeleteElement(Renamings,NULL);

  return Renamings;
}

static LIST ren_FurtherMatches(TERM Formula, LIST Formulas)
/**********************************************************
  INPUT:   A formula and a list of formulas that are candidates
           for renaming inside the formula.
  RETURNS: A list of renamings where additional matches of
           the already found formulas in <Formula> are considered.
	   First the most general formula <Hit> of any renaming inside
	   <Formula> is computed, then all instances of <Hit> inside
	   <Formula> built the actual renaming.
	   No formula occurs twice in the resulting renamings.
***********************************************************/
{
  LIST Scan1, Scan2, Allmatches, Matchables, Renamings;
  TERM Hit;
  int  Polarity, NewPol;

  Allmatches = list_Nil();
  Renamings  = list_Nil();

  for (Scan1=Formulas; !list_Empty(Scan1); Scan1=list_Cdr(Scan1)) {
    Hit = (TERM)list_Car(Scan1);

    if (!list_PointerMember(Allmatches, Hit)) {
      Matchables = list_Cons(Hit, fol_Generalizations(Formula, Hit));
      Hit        = fol_MostGeneralFormula(Matchables); /* Could be further improved: construct it ! */
      list_Delete(Matchables);

      if (!list_PointerMember(Allmatches, Hit)) {  /* Potentially <Hit> is now different */
	Allmatches = list_Cons(Hit,Allmatches);
	Matchables = fol_Instances(Formula, Hit);
	Polarity   = ren_Polarity(Hit);
	
	for (Scan2=Matchables; !list_Empty(Scan2); Scan2=list_Cdr(Scan2)) {
	  if (list_PointerMember(Allmatches, list_Car(Scan2)))
	    list_Rplaca(Scan2, NULL);
	  else {
	    NewPol = ren_Polarity(list_Car(Scan2));
	    if (NewPol != Polarity)
	      Polarity = 0;
	  }
	}
	Matchables = list_PointerDeleteElement(Matchables, NULL);
	Allmatches = list_Nconc(list_Copy(Matchables), Allmatches);
	Renamings  = list_Cons(ren_Create(Hit, Matchables, Polarity),Renamings);
      }
    }
  }
  list_Delete(Allmatches);

  return Renamings;
}


TERM ren_Rename(TERM Term, PRECEDENCE Precedence, LIST *SkolemSymbols,
		BOOL Document, BOOL Match)
/**********************************************************
  INPUT:   A term, a precedence, a pointer to a list of
           Skolem symbols, a flag indicating whether the
	   renamings should be documented and a flag
	   indicating whether matching subterms should be
	   renamed using the same predicate.
  RETURNS: The possibly changed Term where subformulae are renamed
           if this results in a smaller clause normal form, with
	   respect to the number of clauses. The newly introduced
	   Skolem predicates are added to <SkolemSymbols>.
	   The precedence of the new symbols is set in <Precedence>.
  CAUTION: Formulae are changed destructively.
           This function expects that both conjunctions and disjunction
	   have at least two arguments!
***********************************************************/
{
  LIST Renamings, Scan, Formulas;

  Renamings = list_Nil();
  Formulas  = list_Nil();

  if (term_StampOverflow(ren_STAMPID))
    ren_ResetTermStamp(Term);

#ifdef CHECK
  fol_CheckFatherLinks(Term);
#endif

  term_StartStamp();

  Formulas = ren_GetRenamings(Term, Term, 1);

  /* Formulas = list_GreaterNumberSort(Formulas, (NAT (*)(POINTER)) fol_Depth); */

  if (Match)
    Renamings = ren_FurtherMatches(Term, Formulas);
  else {
    for (Scan=Formulas;!list_Empty(Scan);Scan=list_Cdr(Scan))
      Renamings = list_Cons(ren_Create(list_Car(Scan),list_Nil(),ren_Polarity(list_Car(Scan))),Renamings);
  }

  Renamings = ren_FreeRenaming(Renamings);

  Renamings = list_Sort(Renamings, (BOOL (*) (POINTER, POINTER))ren_RootDistanceSmaller);   
                                                       /* for dependencies sort renamings top down */

  Renamings = ren_SolveDependencies(Renamings);  /* dependencies in further matches */

  Renamings = ren_FreeRenaming(Renamings); /* possibly depency solving has created non-zero benefit renamings */

  if (!list_Empty(Renamings) && Document) {
    puts("\n\n\t Renaming term:");
    fol_PrettyPrintDFG(Term);
    for (Scan=Renamings;!list_Empty(Scan);Scan=list_Cdr(Scan)) {
      puts("\n");
      ren_PrettyPrint((RENAMING)list_Car(Scan));
    }
    puts("\n");
  }

  Term = ren_FormulaRename(Term, Renamings, Precedence, SkolemSymbols);
  
  if (!list_Empty(Renamings) && Document) {
    puts("\n\n\t Renamed term:");
    fol_PrettyPrintDFG(Term);
    puts("\n");
  }

  list_DeleteWithElement(Renamings, (void (*)(POINTER)) ren_Delete);
  list_Delete(Formulas);

  term_StopStamp();

  return Term;
}

void ren_PrettyPrint(RENAMING Ren)
/**********************************************************
  INPUT:   A renaming.
  EFFECT:  pretty prints the renaming to <stdout>
***********************************************************/
{
  LIST Matches;

  puts("\t Renaming:");
  puts("\n\t ========= \n");
  fol_PrettyPrintDFG(ren_Hit(Ren));
  puts("\n\n\t Instances:");
  for (Matches=ren_Matches(Ren); !list_Empty(Matches); Matches=list_Cdr(Matches)) {
    fol_PrettyPrintDFG(list_Car(Matches));
    puts("\n");
  }
  printf("\n\t Polarity: %d\n", ren_OverallPolarity(Ren));
  printf("\n\t General : %d\n", (ren_General(Ren) ? 1 : 0));
}
