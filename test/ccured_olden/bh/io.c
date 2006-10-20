/****************************************************************************/
/* IO.C: I/O routines for export version of hierarchical N-body code.       */
/* Public routines: inputdata(), initoutput(), stopoutput(), output().      */
/*                                                                          */
/* Copyright (c) 1993 by Joshua E. Barnes, Honolulu, HI.                    */
/* It's free because it's yours.                                            */
/****************************************************************************/

#include "code.h"

local void diagnostics(void);
local void in_int(stream, int *);
local void in_real(stream, real *);
local void in_vector(stream, vector);
local void out_int(stream, int);
local void out_real(stream, real);
local void out_vector(stream, vector);
local void printvec(string, vector);

/*
 * INPUTDATA: read initial conditions from input file.
 */

void inputdata(void)
{
    stream instr;
    permanent char headbuf[128];
    int ndim;
    bodyptr p;

    instr = fopen(infile, "r");			/* open input stream        */
    if (instr == NULL)
	error("inputdata: cannot find file %s\n", infile);
    sprintf(headbuf, "Hierarchical code: input file %s", infile);
    headline = headbuf;
    in_int(instr, &nbody);
    if (nbody < 1)
	error("inputdata: nbody = %d is absurd\n", nbody);
    in_int(instr, &ndim);
    if (ndim != NDIM)
	error("inputdata: ndim = %d is absurd\n", ndim);
    in_real(instr, &tnow);
    bodytab = (bodyptr) allocate(nbody * sizeof(body));
    for (p = bodytab; p < bodytab+nbody; p++)	/* loop over new bodies     */
	Type(p) = BODY;				/*   init body type         */
    for (p = bodytab; p < bodytab+nbody; p++)
	in_real(instr, &Mass(p));
    for (p = bodytab; p < bodytab+nbody; p++)
	in_vector(instr, Pos(p));
    for (p = bodytab; p < bodytab+nbody; p++)
	in_vector(instr, Vel(p));
    fclose(instr);				/* close input stream       */
}

/*
 * INITOUTPUT: initialize output routines.
 */

local stream outstr;                  /* output stream pointer */

void initoutput(void)
{
    printf("\n%s\n\n", headline);		/* print headline, params   */
    printf("%10s%10s%10s%10s%10s%10s%10s\n", "nbody", "dtime", "eps",
	   "theta", "usequad", "dtout", "tstop");
    printf("%10d%10.5f%10.4f%10.2f%10s%10.4f%10.4f\n\n", nbody, 1/freq, eps,
	   theta, usequad ? "true" : "false", 1/freqout, tstop);
    if (*options != NULLCHR)                       /* print options, if any    */
	printf("\tOptions: %s\n\n", options);
    printf("\n");
    if (*outfile != NULLCHR) {                     /* output file specified?   */
        outstr = fopen(outfile, "w");           /*   setup output stream    */
	if (outstr == NULL)
	    error("initoutput: cannot open file %s\n", outfile);
    } else
        outstr = NULL;				/*   turn off data output   */
}

/*
 * STOPOUTPUT: finish up after a run.
 */

void stopoutput(void)
{
    if (outstr != NULL)
        fclose(outstr);
}

/*
 * Counters and accumulators for output routines.
 */

local real mtot;                /* total mass of N-body system */
local real etot[3];             /* binding, kinetic, potential energy */
local matrix keten;		/* kinetic energy tensor */
local matrix peten;		/* potential energy tensor */
local vector cmphase[2];	/* center of mass coordinates */
local vector amvec;		/* angular momentum vector */

/*
 * OUTPUT: compute diagnostics and output data.
 */

void output(void)
{
    int nttot, nbavg, ncavg;
    bodyptr p;

    diagnostics();				/* compute std diagnostics  */
    nttot = n2bcalc + nbccalc;
    nbavg = (int) ((real) n2bcalc / (real) nbody);
    ncavg = (int) ((real) nbccalc / (real) nbody);
    printf("%10s%10s%10s%10s%10s%10s%10s\n", "tnow", "T+U",
	   "T/U", "nttot", "nbavg", "ncavg", "cputime");
    printf("%10.3f%10.4f%10.4f%10d%10d%10d%10.2f\n\n", tnow, etot[0],
	   etot[1]/etot[2], nttot, nbavg, ncavg, cputime());
    if (scanopt(options, "tree-report")) {      /* report on tree structure */
	printf("\t  %20s%20s%20s\n", "rsize", "cellused", "maxlevel");
	printf("\t  %20.2f%20d%20d\n\n", rsize, cellused, maxlevel);
    }
    printvec("cm pos", cmphase[0]);
    printvec("cm vel", cmphase[1]);
    printvec("am vec", amvec);
    printf("\n");
    if (outstr != NULL &&			/* output stream open and   */
	  (tout - 0.01 / freq) <= tnow) {	/* ...time for next output? */
	out_int(outstr, nbody);			/*   write particle data    */
	out_int(outstr, NDIM);
	out_real(outstr, tnow);
	for (p = bodytab; p < bodytab+nbody; p++)
	    out_real(outstr, Mass(p));
	for (p = bodytab; p < bodytab+nbody; p++)
	    out_vector(outstr, Pos(p));
	for (p = bodytab; p < bodytab+nbody; p++)
	    out_vector(outstr, Vel(p));
	fflush(outstr);				/*   drain output buffer    */
	printf("\tParticle data written to file %s\n\n", outfile);
	tout += 1 / freqout;			/*   schedule next data out */
    }
}

/*
 * DIAGNOSTICS: compute various dynamical diagnostics.
 */

local void diagnostics(void)
{
    register bodyptr p;
    real velsq;
    vector tmpv;
    matrix tmpt;

    mtot = 0.0;					/* zero total mass          */
    etot[1] = etot[2] = 0.0;			/* zero total KE and PE     */
    CLRM(keten);				/* zero ke tensor           */
    CLRM(peten);				/* zero pe tensor           */
    CLRV(cmphase[0]);				/* zero c. of m. position   */
    CLRV(cmphase[1]);				/* zero c. of m. velocity   */
    CLRV(amvec);				/* zero am vector           */
    for (p = bodytab; p < bodytab+nbody; p++) {	/* loop over all particles  */
	mtot += Mass(p);                        /*   sum particle masses    */
	DOTVP(velsq, Vel(p), Vel(p));		/*   square vel vector      */
	etot[1] += 0.5 * Mass(p) * velsq;	/*   sum current KE         */
	etot[2] += 0.5 * Mass(p) * Phi(p);	/*   and current PE         */
	MULVS(tmpv, Vel(p), 0.5 * Mass(p));	/*   sum 0.5 m v_i v_j      */
	OUTVP(tmpt, tmpv, Vel(p));
	ADDM(keten, keten, tmpt);
	MULVS(tmpv, Pos(p), Mass(p));		/*   sum m r_i a_j          */
	OUTVP(tmpt, tmpv, Acc(p));
	ADDM(peten, peten, tmpt);
	MULVS(tmpv, Pos(p), Mass(p));		/*   sum cm position        */
	ADDV(cmphase[0], cmphase[0], tmpv);
	MULVS(tmpv, Vel(p), Mass(p));		/*   sum cm momentum        */
	ADDV(cmphase[1], cmphase[1], tmpv);
	CROSSVP(tmpv, Pos(p), Vel(p));		/*   sum angular momentum   */
	MULVS(tmpv, tmpv, Mass(p));
	ADDV(amvec, amvec, tmpv);
    }
    etot[0] = etot[1] + etot[2];                /* sum KE and PE            */
    DIVVS(cmphase[0], cmphase[0], mtot);        /* normalize cm coords      */
    DIVVS(cmphase[1], cmphase[1], mtot);
}

/*
 * Low-level input and output operations.
 */

local void in_int(stream str, int *iptr)
{
#ifdef CCURED
  if((resetScanfCount(),
      *iptr = ccured_fscanf_int(str, "%d"),
      getScanfCount()) != 1) 
    error("in_int: input conversion error\n");
#else
  if (fscanf(str, "%d", iptr) != 1)
    error("in_int: input conversion error\n");
#endif    
}

local void in_real(stream str, real *rptr)
{
    double tmp;

#ifdef CCURED
    if((resetScanfCount(),
        tmp = ccured_fscanf_double(str, "%lf"),
        getScanfCount()) != 1) 
#else
    if (fscanf(str, "%lf", &tmp) != 1)
#endif      
      error("in_real: input conversion error\n");
    *rptr = tmp;
}

local void in_vector(stream str, vector vec)
{
    double tmpx, tmpy, tmpz;
#ifdef CCURED
    if((resetScanfCount(),
        tmpx = ccured_fscanf_double(str, "%lf"),
        tmpx = ccured_fscanf_double(str, "%lf"),
        tmpx = ccured_fscanf_double(str, "%lf"),
        getScanfCount()) != 3) 
#else    
      if (fscanf(str, "%lf%lf%lf", &tmpx, &tmpy, &tmpz) != 3)
#endif      
	error("in_vector: input conversion error\n");
    
    vec[0] = tmpx;    vec[1] = tmpy;    vec[2] = tmpz;
}

local void out_int(stream str, int ival)
{
    fprintf(str, "  %d\n", ival);
}

local void out_real(stream str, real rval)
{
    fprintf(str, " %21.14E\n", rval);
}

local void out_vector(stream str, vector vec)
{
    fprintf(str, " %21.14E %21.14E %21.14E\n", vec[0], vec[1], vec[2]);
}

local void printvec(string name, vector vec)
{
    printf("          %10s%10.4f%10.4f%10.4f\n",
	   name, vec[0], vec[1], vec[2]);
}
