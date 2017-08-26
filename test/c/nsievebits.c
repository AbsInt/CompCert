/*
 * The Great Computer Language Shootout
 * http://shootout.alioth.debian.org/
 *
 * Written by Dima Dorfman, 2004
 * Compile: gcc -std=c99 -O2 -o nsieve_bits_gcc nsieve_bits.c
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned int bits;
#define	NBITS	(8 * sizeof(bits))

static unsigned int
nsieve(unsigned int m)
{
	unsigned int count, i, j;
	bits * a;
        a = malloc((m / NBITS) * sizeof(bits));
	memset(a, (1 << 8) - 1, (m / NBITS) * sizeof(bits));
	count = 0;
	for (i = 2; i < m; ++i)
		if (a[i / NBITS] & (1 << i % NBITS)) {
			for (j = i + i; j < m; j += i)
				a[j / NBITS] &= ~(1 << j % NBITS);
			++count;
		}
	return (count);
}

#define NITER 2

static void
test(unsigned int n)
{
	unsigned int count, m;
        int i;

	m = (1 << n) * 10000;
        for (i = 0; i < NITER; i++) { count = nsieve(m); }
	printf("Primes up to %8u %8u\n", m, count);
}

int
main(int ac, char **av)
{
	unsigned int n;

	n = ac < 2 ? 9 : atoi(av[1]);
	test(n);
	if (n >= 1)
		test(n - 1);
	if (n >= 2)
		test(n - 2);
	exit(0);
}
/****
 build & benchmark results

BUILD COMMANDS FOR: nsievebits.gcc

Fri Sep 15 06:30:15 PDT 2006

/usr/bin/gcc -pipe -Wall -O3 -fomit-frame-pointer -funroll-loops -march=pentium4  nsievebits.c -o nsievebits.gcc_run

=================================================================
COMMAND LINE (%A is single numeric argument):

nsievebits.gcc_run %A


PROGRAM OUTPUT
==============
Primes up to  5120000   356244
Primes up to  2560000   187134
Primes up to  1280000    98610
*****/
