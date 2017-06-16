/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *              INTERFACE FOR THE DFG PARSER              * */
/* *                                                        * */
/* *  $Module:   DFG                                        * */ 
/* *                                                        * */
/* *  Copyright (C) 1997, 1999, 2000, 2001                  * */
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

#ifndef _DFG_
#define _DFG_

#include <stdio.h>
#include "list.h"
#include "flags.h"
#include "clause.h"

typedef enum { DFG_SATISFIABLE, DFG_UNSATISFIABLE, DFG_UNKNOWNSTATE } DFG_STATE;

/* Parser functions */
LIST        dfg_DFGParser(FILE*, FLAGSTORE, PRECEDENCE, LIST*, LIST*, LIST*, LIST*);
LIST        dfg_ProofParser(FILE*, FLAGSTORE, PRECEDENCE);
LIST        dfg_TermParser(FILE*, FLAGSTORE, PRECEDENCE);


/* Functions for accessing description information */
const char* dfg_ProblemName(void);
const char* dfg_ProblemAuthor(void);
const char* dfg_ProblemVersion(void);
const char* dfg_ProblemLogic(void);
DFG_STATE   dfg_ProblemStatus(void);
const char* dfg_ProblemStatusString(void);
const char* dfg_ProblemDescription(void);
const char* dfg_ProblemDate(void);
NAT         dfg_DescriptionLength(void);

/* Misc functions */
void        dfg_Free(void);   /* Must be called after each parser call */
void        dfg_DeleteFormulaPairList(LIST);
void        dfg_StripLabelsFromList(LIST);
void        dfg_FPrintDescription(FILE*);

void        dfg_DeleteProofList(LIST);

CLAUSE      dfg_CreateClauseFromTerm(TERM, BOOL, FLAGSTORE, PRECEDENCE); 
TERM        dfg_CreateQuantifier(SYMBOL, LIST, TERM);

#endif
