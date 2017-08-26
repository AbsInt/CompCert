/* The Computer Language Shootout
   http://shootout.alioth.debian.org/

   contributed by Greg Buchholz

   for the debian (AMD) machine...
   compile flags:  -O3 -ffast-math -march=athlon-xp -funroll-loops

   for the gp4 (Intel) machine...
   compile flags:  -O3 -ffast-math -march=pentium4 -funroll-loops
*/

#include <stdio.h>
#include <stdlib.h>

int main (int argc, char **argv)
{
    int w, h, bit_num = 0;
    char byte_acc = 0;
    int i, iter = 50;
    double x, y, limit = 2.0;
    double Zr, Zi, Cr, Ci, Tr, Ti;

    if (argc < 2) {
      w = h = 1000;
    } else {
      w = h = atoi(argv[1]);
    }

    printf("P4\n%d %d\n",w,h);

    for(y=0;y<h;++y)
    {
        for(x=0;x<w;++x)
        {
            Zr = Zi = Tr = Ti = 0.0;
            Cr = (2.0*x/w - 1.5); Ci=(2.0*y/h - 1.0);

            for (i=0;i<iter && (Tr+Ti <= limit*limit);++i)
            {
                Zi = 2.0*Zr*Zi + Ci;
                Zr = Tr - Ti + Cr;
                Tr = Zr * Zr;
                Ti = Zi * Zi;
            }

            byte_acc <<= 1;
            if(Tr+Ti <= limit*limit) byte_acc |= 0x01;

            ++bit_num;

            if(bit_num == 8)
            {
                putc(byte_acc,stdout);
                byte_acc = 0;
                bit_num = 0;
            }
            else if(x == w-1)
            {
                byte_acc <<= (8-w%8);
                putc(byte_acc,stdout);
                byte_acc = 0;
                bit_num = 0;
            }
        }
    }
    return 0;
}

/***********
 build & benchmark results

BUILD COMMANDS FOR: mandelbrot.gcc-2.gcc

Fri Sep 15 03:05:43 PDT 2006

/usr/bin/gcc -pipe -Wall -O3 -fomit-frame-pointer -funroll-loops -march=pentium4 -D_ISOC9X_SOURCE -mfpmath=sse -msse2 -lm mandelbrot.gcc-2.c -o mandelbrot.gcc-2.gcc_run
mandelbrot.gcc-2.c: In function 'main':
mandelbrot.gcc-2.c:23: warning: implicit declaration of function 'atoi'
mandelbrot.gcc-2.c:62: warning: control reaches end of non-void function

=================================================================
COMMAND LINE (%A is single numeric argument):

mandelbrot.gcc-2.gcc_run %A
N=3000

PROGRAM OUTPUT
==============
P4
3000 3000
****************/
