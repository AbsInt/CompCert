/****************************************************************************/
/* VECTMATH.H: include file for vector/matrix operations.		    */
/*                                                                          */
/* Copyright (c) 1993 by Joshua E. Barnes, Honolulu, HI.                    */
/* It's free because it's yours.                                            */
/****************************************************************************/

#ifndef THREEDIM
#  ifndef TWODIM
#    ifndef NDIM
#      define THREEDIM
#    endif
#  endif
#endif

#ifdef TWODIM
#  define NDIM 2
#endif

#ifdef THREEDIM
#  define NDIM 3
#endif

typedef real vector[NDIM], matrix[NDIM][NDIM];

/*
 * Vector operations.
 */

#define CLRV(v)			/* CLeaR Vector */			\
{									\
    int _i;								\
    for (_i = 0; _i < NDIM; _i++)					\
        (v)[_i] = 0.0;							\
}

#define UNITV(v,j)		/* UNIT Vector */			\
{									\
    int _i;								\
    for (_i = 0; _i < NDIM; _i++)					\
        (v)[_i] = (_i == (j) ? 1.0 : 0.0);				\
}

#define SETV(v,u)		/* SET Vector */			\
{ 									\
    int _i; 								\
    for (_i = 0; _i < NDIM; _i++) 					\
        (v)[_i] = (u)[_i]; 						\
}

#ifdef THREEDIM

#ifdef NO_PERF_CHANGES

#define ADDV(v,u,w)             /* ADD Vector */                        \
{                                                                       \
    real *_vp = (v), *_up = (u), *_wp = (w);                            \
    *_vp++ = (*_up++) + (*_wp++);                                       \
    *_vp++ = (*_up++) + (*_wp++);                                       \
    *_vp   = (*_up  ) + (*_wp  );                                       \
}

#define SUBV(v,u,w)             /* SUBtract Vector */                   \
{                                                                       \
    real *_vp = (v), *_up = (u), *_wp = (w);                            \
    *_vp++ = (*_up++) - (*_wp++);                                       \
    *_vp++ = (*_up++) - (*_wp++);                                       \
    *_vp   = (*_up  ) - (*_wp  );                                       \
}

#define MULVS(v,u,s)            /* MULtiply Vector by Scalar */         \
{                                                                       \
    real *_vp = (v), *_up = (u);                                        \
    *_vp++ = (*_up++) * (s);                                            \
    *_vp++ = (*_up++) * (s);                                            \
    *_vp   = (*_up  ) * (s);                                            \
}

#else // NO_PERF_CHANGES

#define ADDV(v,u,w)		/* ADD Vector */			\
{									\
    real *_vp = (v), *_up = (u), *_wp = (w);				\
    _vp[2] = _up[2] + _wp[2];                                           \
    _vp[1] = _up[1] + _wp[1];                                           \
    _vp[0] = _up[0] + _wp[0];                                           \
}

#define SUBV(v,u,w)		/* SUBtract Vector */			\
{									\
    real *_vp = (v), *_up = (u), *_wp = (w);				\
    _vp[2] = _up[2] - _wp[2];                                           \
    _vp[1] = _up[1] - _wp[1];                                           \
    _vp[0] = _up[0] - _wp[0];                                           \
}

#define MULVS(v,u,s)		/* MULtiply Vector by Scalar */		\
{									\
    real *_vp = (v), *_up = (u);					\
    _vp[2] = (_up[2]) * (s);					\
    _vp[1] = (_up[1]) * (s);					\
    _vp[0] = (_up[0]) * (s);					\
}
#endif // NO_PERF_CHANGES

#else

#define ADDV(v,u,w)		/* ADD Vector */			\
{									\
    int _i;								\
    for (_i = 0; _i < NDIM; _i++)					\
        (v)[_i] = (u)[_i] + (w)[_i];					\
}

#define SUBV(v,u,w)		/* SUBtract Vector */			\
{									\
    int _i;								\
    for (_i = 0; _i < NDIM; _i++)					\
        (v)[_i] = (u)[_i] - (w)[_i];					\
}

#define MULVS(v,u,s)		/* MULtiply Vector by Scalar */		\
{									\
    int _i;								\
    for (_i = 0; _i < NDIM; _i++)					\
        (v)[_i] = (u)[_i] * (s);					\
}

#endif

#define DIVVS(v,u,s)		/* DIVide Vector by Scalar */		\
{									\
    int _i;								\
    for (_i = 0; _i < NDIM; _i++)					\
        (v)[_i] = (u)[_i] / (s);					\
}

#ifdef THREEDIM

#ifdef NO_PERF_CHANGES

#define DOTVP(s,v,u)            /* DOT Vector Product */                \
{                                                                       \
    real *_vp = (v), *_up = (u);                                        \
    (s)  = (*_vp++) * (*_up++);                                         \
    (s) += (*_vp++) * (*_up++);                                         \
    (s) += (*_vp  ) * (*_up  );                                         \
}

#else // NO_PERF_CHANGES

#define DOTVP(s,v,u)		/* DOT Vector Product */		\
{									\
    real *_vp = (v), *_up = (u);					\
    (s)  = (_vp[2]) * (_up[2]);						\
    (s) += (_vp[1]) * (_up[1]);						\
    (s) += (_vp[0]) * (_up[0]);						\
}

#endif // NO_PERF_CHANGES

#else

#define DOTVP(s,v,u)		/* DOT Vector Product */		\
{									\
    int _i;								\
    (s) = 0.0;								\
    for (_i = 0; _i < NDIM; _i++)					\
        (s) += (v)[_i] * (u)[_i];					\
}

#endif

#define ABSV(s,v)		/* ABSolute value of a Vector */	\
{									\
    real _tmp;		                                                \
    int _i;								\
    _tmp = 0.0;								\
    for (_i = 0; _i < NDIM; _i++)					\
        _tmp += (v)[_i] * (v)[_i];					\
    (s) = rsqrt(_tmp);                                                  \
}

#define DISTV(s,u,v)		/* DISTance between Vectors */        	\
{									\
    real _tmp;                                                		\
    int _i;								\
    _tmp = 0.0;								\
    for (_i = 0; _i < NDIM; _i++)					\
        _tmp += ((u)[_i]-(v)[_i]) * ((u)[_i]-(v)[_i]);		        \
    (s) = rsqrt(_tmp);                                                  \
}

#ifdef TWODIM

#define CROSSVP(s,v,u)		/* CROSS Vector Product */		\
{									\
    (s) = (v)[0]*(u)[1] - (v)[1]*(u)[0];				\
}

#endif

#ifdef THREEDIM

#define CROSSVP(v,u,w)		/* CROSS Vector Product */		\
{									\
    (v)[0] = (u)[1]*(w)[2] - (u)[2]*(w)[1];				\
    (v)[1] = (u)[2]*(w)[0] - (u)[0]*(w)[2];				\
    (v)[2] = (u)[0]*(w)[1] - (u)[1]*(w)[0];				\
}

#endif

#define INCADDV(v,u)             /* INCrementally ADD Vector */         \
{									\
    int _i;                                                   		\
    for (_i = 0; _i < NDIM; _i++)                                       \
        (v)[_i] += (u)[_i];                                             \
}

#define INCSUBV(v,u)             /* INCrementally SUBtract Vector */    \
{									\
    int _i;                                             	        \
    for (_i = 0; _i < NDIM; _i++)                                       \
        (v)[_i] -= (u)[_i];                                             \
}

#define INCMULVS(v,s)	/* INCrementally MULtiply Vector by Scalar */	\
{									\
    int _i;                                                    		\
    for (_i = 0; _i < NDIM; _i++)                                       \
        (v)[_i] *= (s);                                                 \
}

#define INCDIVVS(v,s)	/* INCrementally DIVide Vector by Scalar */	\
{									\
    int _i;                                                   		\
    for (_i = 0; _i < NDIM; _i++)                                       \
        (v)[_i] /= (s);                                                 \
}

/*
 * Matrix operations.
 */

#define CLRM(p)			/* CLeaR Matrix */			\
{									\
    int _i, _j;								\
    for (_i = 0; _i < NDIM; _i++)					\
        for (_j = 0; _j < NDIM; _j++)					\
	    (p)[_i][_j] = 0.0;						\
}

#define SETMI(p)		/* SET Matrix to Identity */		\
{									\
    int _i, _j;								\
    for (_i = 0; _i < NDIM; _i++)					\
        for (_j = 0; _j < NDIM; _j++)					\
	    (p)[_i][_j] = (_i == _j ? 1.0 : 0.0);			\
}

#define SETM(p,q)		/* SET Matrix */			\
{									\
    int _i, _j;								\
    for (_i = 0; _i < NDIM; _i++)					\
        for (_j = 0; _j < NDIM; _j++)					\
	    (p)[_i][_j] = (q)[_i][_j];					\
}

#define TRANM(p,q)		/* TRANspose Matrix */			\
{									\
    int _i, _j;								\
    for (_i = 0; _i < NDIM; _i++)					\
        for (_j = 0; _j < NDIM; _j++)					\
	    (p)[_i][_j] = (q)[_j][_i];					\
}

#define ADDM(p,q,r)		/* ADD Matrix */			\
{									\
    int _i, _j;								\
    for (_i = 0; _i < NDIM; _i++)					\
        for (_j = 0; _j < NDIM; _j++)					\
	    (p)[_i][_j] = (q)[_i][_j] + (r)[_i][_j];			\
}

#define SUBM(p,q,r)		/* SUBtract Matrix */			\
{									\
    int _i, _j;								\
    for (_i = 0; _i < NDIM; _i++)					\
        for (_j = 0; _j < NDIM; _j++)					\
	    (p)[_i][_j] = (q)[_i][_j] - (r)[_i][_j];			\
}

#define MULM(p,q,r)		/* Multiply Matrix */			\
{									\
    int _i, _j, _k;							\
    for (_i = 0; _i < NDIM; _i++)					\
	for (_j = 0; _j < NDIM; _j++) {					\
	    (p)[_i][_j] = 0.0;						\
            for (_k = 0; _k < NDIM; _k++)				\
		(p)[_i][_j] += (q)[_i][_k] * (r)[_k][_j];		\
        }								\
}

#define MULMS(p,q,s)		/* MULtiply Matrix by Scalar */		\
{									\
    int _i, _j;								\
    for (_i = 0; _i < NDIM; _i++)				        \
        for (_j = 0; _j < NDIM; _j++)					\
	    (p)[_i][_j] = (q)[_i][_j] * (s);				\
}

#define DIVMS(p,q,s)		/* DIVide Matrix by Scalar */		\
{									\
    int _i, _j;								\
    for (_i = 0; _i < NDIM; _i++)					\
        for (_j = 0; _j < NDIM; _j++)					\
	    (p)[_i][_j] = (q)[_i][_j] / (s);				\
}

#define MULMV(v,p,u)		/* MULtiply Matrix by Vector */		\
{									\
    int _i, _j;								\
    for (_i = 0; _i < NDIM; _i++) {					\
	(v)[_i] = 0.0;							\
	for (_j = 0; _j < NDIM; _j++)					\
	    (v)[_i] += (p)[_i][_j] * (u)[_j];				\
    }									\
}

#define OUTVP(p,v,u)		/* OUTer Vector Product */		\
{									\
    int _i, _j;								\
    for (_i = 0; _i < NDIM; _i++)					\
        for (_j = 0; _j < NDIM; _j++)					\
	    (p)[_i][_j] = (v)[_i] * (u)[_j];				\
}

#define TRACEM(s,p)		/* TRACE of Matrix */			\
{									\
    int _i;								\
    (s) = 0.0;								\
    for (_i = 0.0; _i < NDIM; _i++)					\
	(s) += (p)[_i][_i];						\
}

/*
 * Misc. impure operations.
 */

#define SETVS(v,s)		/* SET Vector to Scalar */		\
{									\
    int _i;								\
    for (_i = 0; _i < NDIM; _i++)					\
        (v)[_i] = (s);							\
}

#define ADDVS(v,u,s)		/* ADD Vector and Scalar */		\
{									\
    int _i;								\
    for (_i = 0; _i < NDIM; _i++)					\
        (v)[_i] = (u)[_i] + (s);					\
}

#define SETMS(p,s)		/* SET Matrix to Scalar */		\
{									\
    int _i, _j;								\
    for (_i = 0; _i < NDIM; _i++)					\
        for (_j = 0; _j < NDIM; _j++)					\
	    (p)[_i][_j] = (s);						\
}
