/****************************************************************************/
/* CODE.C: hierarchical N-body code.                                        */
/*                                                                          */
/* Copyright (c) 1993 by Joshua E. Barnes, Honolulu, HI.                    */
/* It's free because it's yours.                                            */
/****************************************************************************/

#define global /* nada */

#include <stdlib.h>
#include "code.h"

/*
 * Default values for input parameters.
 */

string defv[] = {

    /* file names for input/output					    */
    "in=",			/* Input file with initial conditions       */
    "out=",			/* Output file of N-body frames             */

    /* params to control N-body integration				    */
    "dtime=0.03125",		/* Integration time-step		    */
    "eps=0.025",		/* Potential softening parameter            */
    "theta=1.0",		/* Cell subdivision tolerence               */
    "usequad=false",		/* If true, use quad moments                */
    "rsize=4.0",		/* Size of initial root cell                */
    "options=",			/* Various control options                  */
    "tstop=2.0",		/* Time to stop integration                 */
    "dtout=0.25",		/* Data output interval			    */

    /* params used if no input specified to make a Plummer model	    */
    "nbody=1024",		/* Number of particles for test run         */
    "seed=123",			/* Random number seed for test run          */

    NULL,
};

string headline = "Hierarchical N-body Code";	/* default id for run       */

local void startrun(void);			/* initialize system state  */
local void stepsystem(void);			/* advance by one time-step */
local void testdata(void);			/* generate test data       */
local void pickshell(vector, real);		/* pick point on shell      */

/*
 * MAIN: toplevel routine for hierarchical N-body code.
 */

int main(int argc, string argv[])
{
    initparam(argv, defv);			/* setup parameter access   */
    startrun();					/* set params, input data   */
    initoutput();				/* begin system output      */
    while (tnow < tstop - 1.0/(1024*freq))	/* while not past tstop     */
	stepsystem();				/*   advance N-body system  */
    stopoutput();				/* finish up output         */
    return 0; // Change this to zero when the running time is 3.8s again
}

/*
 * STARTRUN: startup hierarchical N-body code.
 */

local void startrun(void)
{
    infile = getparam("in");			/* set I/O file names       */
    outfile = getparam("out");
    freq = 1.0 / getrparam("dtime");		/* inverse timestep         */
    eps = getrparam("eps");			/* softening length         */
    theta = getrparam("theta");			/* force accuracy parameter */
    usequad = getbparam("usequad");		/* flag for quad moments    */
    rsize = getrparam("rsize");			/* initial size of root     */
    options = getparam("options");		/* and control options      */
    tstop = getrparam("tstop");			/* time to stop integration */
    freqout = 1.0 / getrparam("dtout");		/* inverse output interval  */
    if (! streq(infile, "")) {			/* was data file given?     */

      inputdata();				/*   read inital data       */
    } else {					/* make initial conds?      */
	nbody = getiparam("nbody");		/*   get nbody parameter    */
	if (nbody < 1)				/*     check input value    */
	    error("startrun: nbody = %d is absurd\n", nbody);
	srand((long) getiparam("seed"));	/*   set random generator   */
	testdata();				/*   make test model        */
    }
    nstep = 0;					/* start counting steps     */
    tout = tnow;				/* schedule first output    */
}

/*
 * TESTDATA: generate Plummer model initial conditions for test runs,
 * scaled to units such that M = -4E = G = 1 (Henon, Hegge, etc).
 * See Aarseth, SJ, Henon, M, & Wielen, R (1974) Astr & Ap, 37, 183.
 */

#define MFRAC  0.999				/* cut off 1-MFRAC of mass  */

local void testdata(void)
{
    real rsc, vsc, r, v, x, y;
    vector cmr, cmv;
    bodyptr p;

    headline = "Hierarchical code: Plummer model";
						/* supply default headline  */
    tnow = 0.0;					/* reset elapsed model time */
    bodytab = (bodyptr) allocate(nbody * sizeof(body));
						/* alloc space for bodies   */
    rsc = 3 * PI / 16;				/* set length scale factor  */
    vsc = rsqrt(1.0 / rsc);			/* and recip. speed scale   */
    CLRV(cmr);					/* init cm pos, vel         */
    CLRV(cmv);
    for (p = bodytab; p < bodytab+nbody; p++) {	/* loop over particles      */
	Type(p) = BODY;				/*   tag as a body          */
	Mass(p) = 1.0 / nbody;			/*   set masses equal       */
	r = 1 / rsqrt(rpow(xrandom(0.0, MFRAC),	/*   pick r in struct units */
			 -2.0/3.0) - 1);
	pickshell(Pos(p), rsc * r);		/*   pick scaled position   */
	ADDV(cmr, cmr, Pos(p));			/*   add to running sum     */
	do {					/*   select from fn g(x)    */
	    x = xrandom(0.0, 1.0);		/*     for x in range 0:1   */
	    y = xrandom(0.0, 0.1);		/*     max of g(x) is 0.092 */
	} while (y > x*x * rpow(1 - x*x, 3.5));	/*   using von Neumann tech */
	v = rsqrt(2.0) * x/rpow(1 + r*r, 0.25);	/*   find v in struct units */
	pickshell(Vel(p), vsc * v);		/*   pick scaled velocity   */
	ADDV(cmv, cmv, Vel(p));			/*   add to running sum     */
    }
    DIVVS(cmr, cmr, (real) nbody);		/* normalize cm coords      */
    DIVVS(cmv, cmv, (real) nbody);
    for (p = bodytab; p < bodytab+nbody; p++) {	/* loop over particles      */
	SUBV(Pos(p), Pos(p), cmr);		/*   offset by cm coords    */
	SUBV(Vel(p), Vel(p), cmv);
    }
}

/*
 * PICKSHELL: pick a random point on a sphere of specified radius.
 */

local void pickshell(vector vec, real rad)
{
    int k;
    real rsq, rsc;

    do {					/* pick point in NDIM-space */
        for (k = 0; k < NDIM; k++)		/*   loop over dimensions   */
            vec[k] = xrandom(-1.0, 1.0);    	/*     pick from unit cube  */
	DOTVP(rsq, vec, vec);			/*   compute radius squared */
    } while (rsq > 1.0);                	/* reject if outside sphere */
    rsc = rad / rsqrt(rsq);			/* compute scaling factor   */
    MULVS(vec, vec, rsc);			/* rescale to radius given  */
}

/*
 * STEPSYSTEM: advance N-body system one time-step.
 */

local void stepsystem(void)
{
    bodyptr p;
    real dt;
    vector dvel, dpos;

    if (nstep == 0) {				/* about to take 1st step?  */
	maketree(bodytab, nbody);		/*   build tree structure   */
	nfcalc = n2bcalc = nbccalc = 0;		/*   zero counters          */
	for (p = bodytab; p < bodytab+nbody; p++) {
						/*   loop over all bodies   */
	    hackgrav(p, Mass(p) > 0.0);		/*     get force on each    */
	    nfcalc++;				/*     count force calcs    */
	    n2bcalc += n2bterm;			/*     and 2-body terms     */
	    nbccalc += nbcterm;			/*     and body-cell terms  */
	}
	output();				/*   do initial output      */
    }
    dt = 1.0 / freq;				/* set basic time-step      */
    for (p = bodytab; p < bodytab+nbody; p++) { /* loop over all bodies     */
	MULVS(dvel, Acc(p), 0.5 * dt);		/*   get velocity increment */
	ADDV(Vel(p), Vel(p), dvel);		/*   advance v by 1/2 step  */
	MULVS(dpos, Vel(p), dt);		/*   get positon increment  */
	ADDV(Pos(p), Pos(p), dpos);		/*   advance r by 1 step    */
    }
    maketree(bodytab, nbody);			/* build tree structure     */
    nfcalc = n2bcalc = nbccalc = 0;		/* zero counters            */
    for (p = bodytab; p < bodytab+nbody; p++) { /* loop over bodies         */
	hackgrav(p, Mass(p) > 0.0);		/*   get force on each      */
	nfcalc++;				/*   count force calcs      */
	n2bcalc += n2bterm;			/*   and 2-body terms       */
	nbccalc += nbcterm;			/*   and body-cell terms    */
    }
    for (p = bodytab; p < bodytab+nbody; p++) {	/* loop over all bodies     */
	MULVS(dvel, Acc(p), 0.5 * dt);          /*   get velocity increment */
	ADDV(Vel(p), Vel(p), dvel);             /*   advance v by 1/2 step  */
    }
    nstep++;					/* count another time step  */
    tnow = tnow + dt;				/* finally, advance time    */
    output();					/* do major or minor output */
}
