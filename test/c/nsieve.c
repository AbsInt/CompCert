// The Computer Language Shootout
// http://shootout.alioth.debian.org/
// Precedent C entry modified by bearophile for speed and size, 31 Jan 2006
// Compile with:  -O3 -s -std=c99 -fomit-frame-pointer

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned char boolean;


static void nsieve(int m) {
    unsigned int count = 0, i, j;
    boolean * flags = (boolean *) malloc(m * sizeof(boolean));
    memset(flags, 1, m);

    for (i = 2; i < m; ++i)
        if (flags[i]) {
            ++count;
            for (j = i << 1; j < m; j += i)
                if (flags[j]) flags[j] = 0;
    }

    free(flags);
    printf("Primes up to %8u %8u\n", m, count);
}

int main(int argc, char * argv[]) {
    int m = argc < 2 ? 9 : atoi(argv[1]);
    int i;
    for (i = 0; i < 3; i++)
        nsieve(10000 << (m-i));
    return 0;
}

/********
 build & benchmark results

BUILD COMMANDS FOR: nsieve.gcc

Thu Sep 14 20:51:46 PDT 2006

/usr/bin/gcc -pipe -Wall -O3 -fomit-frame-pointer -funroll-loops -march=pentium4 -s -std=c99 nsieve.c -o nsieve.gcc_run

=================================================================
COMMAND LINE (%A is single numeric argument):

nsieve.gcc_run %A
N=9

PROGRAM OUTPUT
==============
Primes up to  5120000   356244
Primes up to  2560000   187134
Primes up to  1280000    98610
*******/
