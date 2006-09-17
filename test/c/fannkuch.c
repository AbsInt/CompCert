/*
 * The Computer Lannguage Shootout
 * http://shootout.alioth.debian.org/
 * Contributed by Heiner Marxen
 *
 * "fannkuch"	for C gcc
 *
 * $Id: fannkuch-gcc.code,v 1.33 2006/02/25 16:38:58 igouy-guest Exp $
 */

#include <stdio.h>
#include <stdlib.h>

#define Int	int
#define Aint	int

    static long
fannkuch( int n )
{
    Aint*	perm;
    Aint*	perm1;
    Aint*	count;
    long	flips;
    long	flipsMax;
    Int		r;
    Int		i;
    Int		k;
    Int		didpr;
    const Int	n1	= n - 1;

    if( n < 1 ) return 0;

    perm  = calloc(n, sizeof(*perm ));
    perm1 = calloc(n, sizeof(*perm1));
    count = calloc(n, sizeof(*count));

    for( i=0 ; i<n ; ++i ) perm1[i] = i;	/* initial (trivial) permu */

    r = n; didpr = 0; flipsMax = 0;
    for(;;) {
	if( didpr < 30 ) {
	    for( i=0 ; i<n ; ++i ) printf("%d", (int)(1+perm1[i]));
	    printf("\n");
	    ++didpr;
	}
	for( ; r!=1 ; --r ) {
	    count[r-1] = r;
	}

#define XCH(x,y)	{ Aint t_mp; t_mp=(x); (x)=(y); (y)=t_mp; }

	if( ! (perm1[0]==0 || perm1[n1]==n1) ) {
	    flips = 0;
	    for( i=1 ; i<n ; ++i ) {	/* perm = perm1 */
		perm[i] = perm1[i];
	    }
	    k = perm1[0];		/* cache perm[0] in k */
	    do {			/* k!=0 ==> k>0 */
		Int	j;
		for( i=1, j=k-1 ; i<j ; ++i, --j ) {
		    XCH(perm[i], perm[j])
		}
		++flips;
		/*
		 * Now exchange k (caching perm[0]) and perm[k]... with care!
		 * XCH(k, perm[k]) does NOT work!
		 */
		j=perm[k]; perm[k]=k ; k=j;
	    }while( k );
	    if( flipsMax < flips ) {
		flipsMax = flips;
	    }
	}

	for(;;) {
	    if( r == n ) {
		return flipsMax;
	    }
	    /* rotate down perm[0..r] by one */
	    {
		Int	perm0 = perm1[0];
		i = 0;
		while( i < r ) {
		    k = i+1;
		    perm1[i] = perm1[k];
		    i = k;
		}
		perm1[r] = perm0;
	    }
	    if( (count[r] -= 1) > 0 ) {
		break;
	    }
	    ++r;
	}
    }
}

    int
main( int argc, char* argv[] )
{
    int		n = (argc>1) ? atoi(argv[1]) : 10;

    printf("Pfannkuchen(%d) = %ld\n", n, fannkuch(n));
    return 0;
}
/*****
 build & benchmark results

BUILD COMMANDS FOR: fannkuch.gcc

Thu Sep 14 17:44:44 PDT 2006

/usr/bin/gcc -pipe -Wall -O3 -fomit-frame-pointer -funroll-loops -march=pentium4  fannkuch.c -o fannkuch.gcc_run

=================================================================
COMMAND LINE (%A is single numeric argument):

fannkuch.gcc_run %A
N=10

PROGRAM OUTPUT
==============
12345678910
21345678910
23145678910
32145678910
31245678910
13245678910
23415678910
32415678910
34215678910
43215678910
42315678910
24315678910
34125678910
43125678910
41325678910
14325678910
13425678910
31425678910
41235678910
14235678910
12435678910
21435678910
24135678910
42135678910
23451678910
32451678910
34251678910
43251678910
42351678910
24351678910
Pfannkuchen(10) = 38
*****/
