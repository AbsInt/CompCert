/*
    almabench
    Standard C version
    17 April 2003

    Written by Scott Robert Ladd.
    No rights reserved. This is public domain software, for use by anyone.

    A number-crunching benchmark that can be used as a fitness test for
    evolving optimal compiler options via genetic algorithm.

    This program calculates the daily ephemeris (at noon) for the years
    2000-2099 using an algorithm developed by J.L. Simon, P. Bretagnon, J.
    Chapront, M. Chapront-Touze, G. Francou and J. Laskar of the Bureau des
    Longitudes, Paris, France), as detailed in Astronomy & Astrophysics
    282, 663 (1994)

    Note that the code herein is design for the purpose of testing 
    computational performance; error handling and other such "niceties"
    is virtually non-existent.

    Actual benchmark results can be found at:
            http://www.coyotegulch.com

    Please do not use this information or algorithm in any way that might
    upset the balance of the universe or otherwise cause planets to impact
    upon one another.
*/

#include <math.h>
#include <string.h>

#define PI 3.14159265358979323846
#define J2000 2451545.0
#define JCENTURY 36525.0
#define JMILLENIA 365250.0
#define TWOPI (2.0 * PI)
#define A2R (PI / 648000.0)
#define R2H (12.0 / PI)
#define R2D (180.0 / PI)
#define GAUSSK 0.01720209895
#define TEST_LOOPS 20
#define TEST_LENGTH 36525
#define sineps 0.3977771559319137
#define coseps 0.9174820620691818

extern double amas[8];
extern double a[8][3], dlm[8][3], e[8][3], pi[8][3], dinc[8][3], omega[8][3];
extern double kp[8][9], ca[8][9], sa[8][9], kq[8][10], cl[8][10], sl[8][10];

extern double cos_static(double), sin_static(double),
  atan2_static(double, double), asin_static(double), sqrt_static(double),
  fmod_static(double, double), fabs_static(double);

#define cos cos_static
#define sin sin_static
#define atan2 atan2_static
#define asin asin_static
#define sqrt sqrt_static
#define fmod fmod_static
#define fabs fabs_static

//---------------------------------------------------------------------------
// Normalize angle into the range -pi <= A < +pi.
double anpm (double a)
{
    double w = fmod(a,TWOPI);
    
    if (fabs(w) >= PI) 
        w = w - ((a < 0) ? -TWOPI : TWOPI);
        
    return w;
}

//---------------------------------------------------------------------------    
// The reference frame is equatorial and is with respect to the
//    mean equator and equinox of epoch j2000.
void planetpv (double epoch[2], int np, double pv[2][3])
{
    // working storage
    int i, j, k;
    double t, da, dl, de, dp, di, doh, dmu, arga, argl, am;
    double ae, dae, ae2, at, r, v, si2, xq, xp, tl, xsw;
    double xcw, xm2, xf, ci2, xms, xmc, xpxq2, x, y, z;

    // time: julian millennia since j2000.
    t = ((epoch[0] - J2000) + epoch[1]) / JMILLENIA;

    // compute the mean elements.
    da  = a[np][0] + (a[np][1] + a[np][2] * t ) * t;
    dl  = (3600.0 * dlm[np][0] + (dlm[np][1] + dlm[np][2] * t ) * t ) * A2R;
    de  = e[np][0] + (e[np][1] + e[np][2] * t ) * t;
    dp  = anpm((3600.0 * pi[np][0] + (pi[np][1] + pi[np][2] * t ) * t ) * A2R );
    di  = (3600.0 * dinc[np][0] + (dinc[np][1] + dinc[np][2] * t ) * t ) * A2R;
    doh = anpm((3600.0 * omega[np][0] + (omega[np][1] + omega[np][2] * t ) * t ) * A2R );
    
    // apply the trigonometric terms.
    dmu = 0.35953620 * t;
    
    for (k = 0; k < 8; ++k)
    {
        arga = kp[np][k] * dmu;
        argl = kq[np][k] * dmu;
        da   = da + (ca[np][k] * cos(arga) + sa[np][k] * sin(arga)) * 0.0000001;
        dl   = dl + (cl[np][k] * cos(argl) + sl[np][k] * sin(argl)) * 0.0000001;
    }

    arga = kp[np][8] * dmu;
    da   = da + t * (ca[np][8] * cos(arga) + sa[np][8] * sin(arga)) * 0.0000001;

    for (k = 8; k <= 9; ++k)
    {
        argl = kq[np][k] * dmu;
        dl   = dl + t * ( cl[np][k] * cos(argl) + sl[np][k] * sin(argl) ) * 0.0000001;
    }

    dl = fmod(dl,TWOPI);

    // iterative solution of kepler's equation to get eccentric anomaly.
    am = dl - dp;
    ae = am + de * sin(am);
    k  = 0;

    while (1)
    {
        dae = (am - ae + de * sin(ae)) / (1.0 - de * cos(ae));
        ae  = ae + dae;
        k   = k + 1;
    
        if ((k >= 10) || (fabs(dae) < 1e-12))
            break;
    }

    // true anomaly.
    ae2 = ae / 2.0;
    at  = 2.0 * atan2(sqrt((1.0 + de)/(1.0 - de)) * sin(ae2), cos(ae2));

    // distance (au) and speed (radians per day).
    r = da * (1.0 - de * cos(ae));
    v = GAUSSK * sqrt((1.0 + 1.0 / amas[np] ) / (da * da * da));

    si2   = sin(di / 2.0);
    xq    = si2 * cos(doh);
    xp    = si2 * sin(doh);
    tl    = at + dp;
    xsw   = sin(tl);
    xcw   = cos(tl);
    xm2   = 2.0 * (xp * xcw - xq * xsw );
    xf    = da / sqrt(1.0 - de*de);
    ci2   = cos(di / 2.0);
    xms   = (de * sin(dp) + xsw) * xf;
    xmc   = (de * cos(dp) + xcw) * xf;
    xpxq2 = 2.0 * xp * xq;

    // position (j2000 ecliptic x,y,z in au).
    x = r * (xcw - xm2 * xp);
    y = r * (xsw + xm2 * xq);
    z = r * (-xm2 * ci2);

    // rotate to equatorial.
    pv[0][0] = x;
    pv[0][1] = y * coseps - z * sineps;
    pv[0][2] = y * sineps + z * coseps;

    // velocity (j2000 ecliptic xdot,ydot,zdot in au/d).
    x = v * ((-1.0 + 2.0 * xp * xp) * xms + xpxq2 * xmc);
    y = v * (( 1.0 - 2.0 * xq * xq ) * xmc - xpxq2 * xms);
    z = v * (2.0 * ci2 * (xp * xms + xq * xmc));

    // rotate to equatorial.
    pv[1][0] = x;
    pv[1][1] = y * coseps - z * sineps;
    pv[1][2] = y * sineps + z * coseps;
}

//---------------------------------------------------------------------------
// Computes RA, Declination, and distance from a state vector returned by
// planetpv.
void radecdist(double state[2][3], double rdd[3])
{
    // distance
    rdd[2] = sqrt(state[0][0] * state[0][0] + state[0][1] * state[0][1] + state[0][2] * state[0][2]);

    // RA
    rdd[0] = atan2(state[0][1], state[0][0]) * R2H;
    if (rdd[0] < 0.0) rdd[0] += 24.0;

    // Declination
    rdd[1] = asin(state[0][2] / rdd[2]) * R2D;
}
