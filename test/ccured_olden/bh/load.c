/****************************************************************************/
/* LOAD.C: routines to create tree.  Public routines: maketree().           */
/*                                                                          */
/* Copyright (c) 1993 by Joshua E. Barnes, Honolulu, HI.                    */
/* It's free because it's yours.                                            */
/****************************************************************************/
 
#include "defs.h"
 
local void newtree(void);			/* flush existing tree      */
local cellptr makecell(void);			/* create an empty cell     */
local void expandbox(bodyptr, int);		/* set size of root cell    */
local void loadbody(bodyptr);			/* load body into tree      */
local int subindex(bodyptr, cellptr);		/* compute subcell index    */
local void hackcofm(cellptr, real);		/* find centers of mass     */
local void setrcrit(cellptr, vector, real);	/* set cell's crit. radius  */
local void threadtree(nodeptr, nodeptr);	/* set next and more links  */
local void hackquad(cellptr);			/* compute quad moments     */

/*
 * MAKETREE: initialize tree structure for hierarchical force calculation
 * from body array btab, which contains nbody bodies.
 */
 
local bool bh86, sw93;				/* use alternate criteria   */
 
void maketree(bodyptr btab, int nbody)
{
    bodyptr p;
 
    newtree();                                  /* flush existing tree, etc */
    root = makecell();				/* allocate the root cell   */
    CLRV(Pos(root));				/* initialize the midpoint  */
    expandbox(btab, nbody);                     /* and expand cell to fit   */
    maxlevel = 0;                               /* init count of levels     */
    for (p = btab; p < btab+nbody; p++)         /* loop over bodies...      */
        if (Mass(p) != 0.0)                     /*   exclude test particles */
            loadbody(p);                        /*     and insert into tree */
    bh86 = scanopt(options, "bh86");		/* set flags for alternate  */
    sw93 = scanopt(options, "sw93");		/* ...cell opening criteria */
    if (bh86 && sw93)				/* can't have both at once  */
	error("maketree: options bh86 and sw93 are incompatible\n");
    hackcofm(root, rsize);	                /* find c-of-m coordinates  */
    threadtree((nodeptr) root, NULL);           /* add Next and More links  */
    if (usequad)				/* including quad moments?  */
	hackquad(root);                         /*   assign Quad moments    */
}

/*
 * NEWTREE: reclaim cells in tree, prepare to build new one.
 */
 
local nodeptr freecell = NULL;          	/* list of free cells       */
 
local void newtree(void)
{
    permanent bool firstcall = TRUE;
    nodeptr p;
 
    if (! firstcall) {                          /* tree data to reclaim?    */
        p = (nodeptr) root;                     /*   start with the root    */
        while (p != NULL)                       /*   loop scanning tree     */
            if (Type(p) == CELL) {              /*     found cell to free?  */
                Next(p) = freecell;             /*       link to front of   */
                freecell = p;                   /*       ...existing list   */
                p = MoreN(p);                    /*       scan down tree     */
            } else                              /*     skip over bodies     */
                p = Next(p);                    /*       go on to next      */
    } else                                      /* first time through       */
        firstcall = FALSE;                      /*   so just note it        */
    root = NULL;                                /* flush existing tree      */
    cellused = 0;                               /* reset cell count         */
}
 
/*
 * MAKECELL: return pointer to free cell.
 */
 
local cellptr makecell(void)
{
    cellptr c;
    int i;
 
    if (freecell == NULL) {                     /* no free cells left?      */
        c = (cellptr) allocate(sizeof(cell));   /*   allocate a new one     */
        #ifndef NO_PERF_CHANGES
          Type(c) = CELL;                         /* initialize cell type     */
        #endif
    } else {                                    /* use existing free cell   */
        Type(freecell) = CELL;                  /* initialize cell type     */
        c = node2cell (freecell);               /*   take one on front      */
        freecell = Next(c);                     /*   go on to next one      */
    }
    #ifdef NO_PERF_CHANGES
      Type(c) = CELL;                         /* initialize cell type     */
    #endif
    for (i = 0; i < NSUB; i++)                  /* loop over subcells       */
        Subp(c)[i] = NULL;                      /*   and empty each one     */
    cellused++;                                 /* count one more cell      */
    return (c);
}

/*
 * EXPANDBOX: find range of coordinate values (with respect to root)
 * and expand root cell to fit.  The size is doubled at each step to
 * take advantage of exact representation of powers of two.
 */
 
local void expandbox(bodyptr btab, int nbody)
{
    real xyzmax;
    bodyptr p;
    int k;
 
    xyzmax = 0.0;
    for (p = btab; p < btab+nbody; p++)
	for (k = 0; k < NDIM; k++)
	    xyzmax = MAX(xyzmax, rabs(Pos(p)[k] - Pos(root)[k]));
    while (rsize < 2 * xyzmax)
	rsize = 2 * rsize;
}

/*
 * LOADBODY: descend tree and insert body p in appropriate place.
 */
 
local void loadbody(bodyptr p)
{
    cellptr q, c;
    int qind, lev, k;
    real qsize;
 
    q = root;                                   /* start with tree root     */
    qind = subindex(p, q);			/* get index of subcell     */
    qsize = rsize;                              /* keep track of cell size  */
    lev = 0;                                    /* count levels descended   */
    while (Subp(q)[qind] != NULL) {             /* loop descending tree     */
        if (Type(Subp(q)[qind]) == BODY) {      /*   reached a "leaf"?      */
            c = makecell();                     /*     allocate new cell    */
	    for (k = 0; k < NDIM; k++)		/*     initialize midpoint  */
		Pos(c)[k] = Pos(q)[k] +		/*       offset from parent */
		    (Pos(p)[k] < Pos(q)[k] ? - qsize : qsize) / 4;
            Subp(c)[subindex(node2body(Subp(q)[qind]), c)] = Subp(q)[qind];
                                                /*     put body in cell     */
            Subp(q)[qind] = (nodeptr) c;        /*     link cell in tree    */
        }
        q = node2cell(Subp(q)[qind]);		/*   advance to next level  */
	qind = subindex(p, q);			/*   get index to examine   */
        qsize = qsize / 2;                      /*   shrink current cell    */
        lev++;                                  /*   count another level    */
    }
    Subp(q)[qind] = (nodeptr) p;                /* found place, store p     */
    maxlevel = MAX(maxlevel, lev);		/* remember maximum level   */
}

/*
 * SUBINDEX: compute subcell index for body p in cell q.
 */
 
local int subindex(bodyptr p, cellptr q)
{
    int ind, k;
 
    ind = 0;					/* accumulate subcell index */
    for (k = 0; k < NDIM; k++)			/*   loop over dimensions   */
        if (Pos(q)[k] <= Pos(p)[k])		/*     if beyond midpoint   */
            ind += NSUB >> (k + 1);             /*       skip over subcells */
    return (ind);
}

/*
 * HACKCOFM: descend tree finding center-of-mass coordinates and
 * setting critical cell radii.
 */
 
local void hackcofm(cellptr p, real psize)
{
    vector cmpos, tmpv;
    int i, k;
    nodeptr q;
 
    Mass(p) = 0.0;                              /* init total mass...       */
    CLRV(cmpos);                                /* and center of mass       */
    for (i = 0; i < NSUB; i++)                  /* loop over subnodes       */
	if ((q = Subp(p)[i]) != NULL) {         /*   does subnode exist?    */
	    if (Type(q) == CELL)		/*     and is it a cell?    */
		hackcofm(node2cell(q), psize/2); /*       find subcell cm    */
	    Mass(p) += Mass(q);                 /*     sum total mass       */
	    MULVS(tmpv, Pos(q), Mass(q));       /*     weight pos by mass   */
	    ADDV(cmpos, cmpos, tmpv);           /*     sum c-of-m position  */
	}
    DIVVS(cmpos, cmpos, Mass(p));               /* rescale cms position     */
    for (k = 0; k < NDIM; k++)			/* check tree structure...  */
	if (cmpos[k] < Pos(p)[k] - psize/2 ||   /*   if out of bounds       */
	      Pos(p)[k] + psize/2 <= cmpos[k])	/*   in either direction    */
	    error("hackcofm: tree structure error\n");
    setrcrit(p, cmpos, psize);                  /* set critical radius      */
    SETV(Pos(p), cmpos);			/* and center-of-mass pos   */
}

/*
 * SETRCRIT: assign critical radius for cell p, using center-of-mass
 * position cmpos and cell size psize.
 */

local void setrcrit(cellptr p, vector cmpos, real psize)
{
    real rc, bmax2, dmin;
    int k;

    if (theta == 0.0)				/* exact force calculation? */
	rc = 2 * rsize;				/*   always open cells      */
    else if (bh86)				/* use old BH criterion?    */
	rc = psize / theta;			/*   using size of cell     */
    else if (sw93) {				/* use S&W's criterion?     */
	bmax2 = 0.0;				/*   compute max distance^2 */
	for (k = 0; k < NDIM; k++) {		/*   loop over dimensions   */
	    dmin = cmpos[k] - (Pos(p)[k] - psize/2);
						/*     dist from 1st corner */
	    bmax2 += rsqr(MAX(dmin, psize - dmin));
						/*     sum max distance^2   */
	}
	rc = rsqrt(bmax2) / theta;		/*   using max dist from cm */
    } else {					/* use new criterion?       */
	rc = psize / theta + distv(cmpos, Pos(p));
						/*   use size plus offset   */
    }
    Rcrit2(p) = rsqr(rc);			/* store square of radius   */
}

/*
 * THREADTREE: do a recursive treewalk starting from node p,
 * with next stop n, installing Next and More links.
 */
 
local void threadtree(nodeptr p, nodeptr n)
{
    int ndesc, i;
    nodeptr desc[NSUB+1];
 
    Next(p) = n;                                /* link to next node        */
    if (Type(p) == CELL) {                      /* any children to thread?  */
        ndesc = 0;                              /*   count extant children  */
        for (i = 0; i < NSUB; i++)              /*   loop over subnodes     */
            if (SubpN(p)[i] != NULL)             /*     found a live one?    */
                desc[ndesc++] = SubpN(p)[i];     /*       store in table     */
        MoreN(p) = desc[0];                      /*   link to first child    */
        desc[ndesc] = n;                        /*   end table with next    */
        for (i = 0; i < ndesc; i++)             /*   loop over children     */
            threadtree(desc[i], desc[i+1]);     /*     thread each w/ next  */
    }
}

/*
 * HACKQUAD: descend tree, evaluating quadrupole moments.  Note that this
 * routine is coded so that the Subp() and Quad() components of a cell can
 * share the same memory locations.
 */
 
local void hackquad(cellptr p)
{
    int i;
    nodeptr psub[NSUB], q;
    vector dr;
    real drsq;
    matrix drdr, Idrsq, tmpm;
 
    for (i = 0; i < NSUB; i++)			/* loop over subnodes       */
	psub[i] = Subp(p)[i];			/*   copy each to safety    */
    CLRM(Quad(p));                              /* init quadrupole moment   */
    for (i = 0; i < NSUB; i++)                  /* loop over subnodes       */
	if ((q = psub[i]) != NULL) {		/*   does subnode exist?    */
	    if (Type(q) == CELL)		/*     and is it a call?    */
		hackquad(node2cell(q));		/*       process it first   */
	    SUBV(dr, Pos(q), Pos(p));           /*     displacement vect.   */
	    OUTVP(drdr, dr, dr);                /*     outer prod. of dr    */
	    DOTVP(drsq, dr, dr);                /*     dot prod. dr * dr    */
	    SETMI(Idrsq);                       /*     init unit matrix     */
	    MULMS(Idrsq, Idrsq, drsq);          /*     scale by dr * dr     */
	    MULMS(tmpm, drdr, 3.0);             /*     scale drdr by 3      */
	    SUBM(tmpm, tmpm, Idrsq);            /*     form quad. moment    */
	    MULMS(tmpm, tmpm, Mass(q));         /*     from cm of subnode   */
	    if (Type(q) == CELL)                /*     if subnode is cell   */
		ADDM(tmpm, tmpm, QuadN(q));      /*       add its moment     */
	    ADDM(Quad(p), Quad(p), tmpm);       /*     add to qm of cell    */
	}
}
