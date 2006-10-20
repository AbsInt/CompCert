/****************************************************************************/
/* CODE.H: define various global things for code.c and io.c.                */
/*                                                                          */
/* Copyright (c) 1993 by Joshua E. Barnes, Honolulu, HI.                    */
/* It's free because it's yours.                                            */
/****************************************************************************/

#include "defs.h"

global string infile;			/* file name for snapshot input     */

global string outfile;			/* file name for snapshot output    */

global real freq;			/* inverse of integration timestep  */

global real freqout;			/* output frequency                 */

global real tstop;			/* time to stop calculation         */

extern string headline;			/* message describing calculation   */

global real tnow;			/* current value of time            */

global real tout;			/* time of next output              */

global int nstep;			/* number of time-steps             */

global int nfcalc;			/* count force calculations         */

global int n2bcalc;			/* count body-body interactions     */

global int nbccalc;			/* count body-cell interactions     */

global int nbody;			/* number of bodies in system       */

global bodyptr bodytab;			/* points to array of bodies        */

/*
 * Global function prototypes.
 */

void initoutput(void);				/* open files for output    */
void stopoutput(void);				/* close output files       */
void inputdata(void);				/* read initial data file   */
void maketree(bodyptr, int);			/* construct tree structure */
void hackgrav(bodyptr, bool);			/* compute force on body    */
void output(void);				/* perform output operation */

/*
 * Utility routines used in code.c and io.c.  These are defined in util.c
 * and getparam.c, which must be compiled with same choice of precision.
 */

bool streq(string, string);			/* test string equality     */
real xrandom(real, real);			/* generate a random number */
void initparam(string *, string *);		/* initialize parameter pkg */
string getparam(string);			/* get parameter as string  */
int getiparam(string);				/* get parameter as integer */
bool getbparam(string);				/* get parameter as bool    */
real getrparam(string);				/* get parameter as real    */
