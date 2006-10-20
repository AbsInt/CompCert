/****************************************************************************/
/* GRAV.C: routines to compute gravity. Public routines: hackgrav().        */
/*                                                                          */
/* Copyright (c) 1993 by Joshua E. Barnes, Honolulu, HI.                    */
/* It's free because it's yours.                                            */
/****************************************************************************/

#include "defs.h"

local void treescan(nodeptr);			/* does force calculation   */
local bool subdivp(cellptr);			/* can cell be accepted?    */
local void gravsub(nodeptr);			/* compute grav interaction */

/*
 * HACKGRAV: evaluate gravitational field on body p; checks to be
 * sure self-interaction was handled correctly if intree is true.
 */

local bodyptr pskip;				/* skip in force evaluation */
local vector pos0;				/* point to evaluate field  */
local real phi0;				/* resulting potential      */
local vector acc0;				/* resulting acceleration   */
local bool skipself;				/* self-interaction skipped */
local bool treeincest = FALSE;			/* tree-incest occured      */

void hackgrav(bodyptr p, bool intree)
{
    pskip = p;					/* exclude p from f.c.      */
    SETV(pos0, Pos(p));				/* set field point          */
    phi0 = 0.0;					/* init total potential     */
    CLRV(acc0);					/* and total acceleration   */
    n2bterm = nbcterm = 0;			/* count body & cell terms  */
    skipself = FALSE;				/* watch for tree-incest    */
    treescan((nodeptr) root);			/* scan tree from root	    */
    if (intree && ! skipself) {			/* did tree-incest occur?   */
	if (! scanopt(options, "allow-incest"))	/*   treat as catastrophic? */
	    error("hackgrav: tree-incest detected\n");
	if (! treeincest)			/*   for the first time?    */
	    eprintf("\n[hackgrav: tree-incest detected]\n");
	treeincest = TRUE;			/*   don't repeat warning   */
    }
    Phi(p) = phi0;				/* store total potential    */
    SETV(Acc(p), acc0);				/* and acceleration         */
}

/*
 * TREESCAN: iterative routine to do force calculation, starting
 * with node q, which is typically the root cell.
 */

local void treescan(nodeptr q)
{
    while (q != NULL) {				/* while not at end of scan */
	if (Type(q) == CELL &&			/*   is node a cell and...  */
	    subdivp(node2cell(q)))		/*   too close to accept?   */
	    q = MoreN(q);			/*     follow to next level */
	else {					/*   else accept this term  */
	    if (q == (nodeptr) pskip)		/*     self-interaction?    */
		skipself = TRUE;		/*       then just skip it  */
	    else {				/*     not self-interaction */
		gravsub(q);                     /*       so compute gravity */
		if (Type(q) == BODY)
		    n2bterm++;			/*       count body-body    */
		else
		    nbcterm++;			/*       count body-cell    */
	    }
	    q = Next(q);			/*     follow next link     */
	}
    }
}

/*
 * SUBDIVP: decide if cell q is too close to accept as a single
 * term.  Also sets qmem, dr, and drsq for use by gravsub.
 */

local cellptr qmem;                     	/* data shared with gravsub */
local vector dr;				/* vector from q to pos0    */
local real drsq;				/* squared distance to pos0 */

local bool subdivp(cellptr q)
{
    SUBV(dr, Pos(q), pos0);			/* compute displacement     */
    DOTVP(drsq, dr, dr);			/* and find dist squared    */
    qmem = q;					/* remember we know them    */
    return (drsq < Rcrit2(q));			/* apply standard rule      */
}

/*
 * GRAVSUB: compute contribution of node q to gravitational field at
 * point pos0, and add to running totals phi0 and acc0.
 */

local void gravsub(nodeptr q)
{
    real drab, phii, mor3;
    vector ai, quaddr;
    real dr5inv, phiquad, drquaddr;

    if (q != (nodeptr) qmem) {                  /* cant use memorized data? */
        SUBV(dr, Pos(q), pos0);                 /*   then compute sep.      */
	DOTVP(drsq, dr, dr);			/*   and sep. squared       */
    }
    drsq += eps*eps;                            /* use standard softening   */
    drab = rsqrt(drsq);
    phii = Mass(q) / drab;
    mor3 = phii / drsq;
    MULVS(ai, dr, mor3);
    phi0 -= phii;                               /* add to total grav. pot.  */
    ADDV(acc0, acc0, ai);                       /* ... and to total accel.  */
    if (usequad && Type(q) == CELL) {           /* if cell, add quad term   */
        dr5inv = 1.0/(drsq * drsq * drab);      /*   form dr^-5             */
        MULMV(quaddr, QuadN(q), dr);             /*   form Q * dr            */
        DOTVP(drquaddr, dr, quaddr);            /*   form dr * Q * dr       */
        phiquad = -0.5 * dr5inv * drquaddr;     /*   get quad. part of phi  */
        phi0 = phi0 + phiquad;                  /*   increment potential    */
        phiquad = 5.0 * phiquad / drsq;         /*   save for acceleration  */
        MULVS(ai, dr, phiquad);                 /*   components of acc.     */
        SUBV(acc0, acc0, ai);                   /*   increment              */
        MULVS(quaddr, quaddr, dr5inv);   
        SUBV(acc0, acc0, quaddr);               /*   acceleration           */
    }
}
