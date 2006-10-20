/* For copyright information, see olden_v1.0/COPYRIGHT */

/* compute.c
 *
 * By:  Martin C. Carlisle
 * 6/15/94
 *
 * Implements computation phase of the Power Pricing problem
 * based on code by: Steve Lumetta, Sherry Li, and Ismail Khalil
 * University of California at Berkeley
 *
 */

#include "power.h"
#include <math.h>

/*----------------------------------------------------------------------*/
/* Leaf optimization 'global' variables               */

    static double     P=1.0;
    static double     Q=1.0;


/*----------------------------------------------------------------------*/
/* Leaf optimization procedures                 */

void optimize_node (double pi_R, double pi_I);
double find_g ();
double find_h ();
double find_gradient_f (double pi_R, double pi_I, local double* gradient);
double find_gradient_g (local double* gradient);
double find_gradient_h (local double* gradient);
void find_dd_grad_f (double pi_R, double pi_I, local double* dd_grad);
double make_orthogonal (local double* v_mod, local double* v_static);


void Compute_Tree(Root r) {
  register int i;
  Lateral l;
#ifndef FUTURES
  Demand a;
#else
  future_cell_demand fc[NUM_FEEDERS];
#endif
  Demand tmp;
  double theta_R,theta_I;

  tmp.P = 0.0;
  tmp.Q = 0.0;
#ifndef FUTURES
  for (i=0; i<NUM_FEEDERS; i++) {
    l = r->feeders[i];
    theta_R = r->theta_R;
    theta_I = r->theta_I;
    a = Compute_Lateral(l,theta_R,theta_I,theta_R,theta_I);
    tmp.P += a.P;
    tmp.Q += a.Q;

  }
#else
  for (i=0; i<NUM_FEEDERS; i++) {
    l = r->feeders[i];
    theta_R = r->theta_R;
    theta_I = r->theta_I;
    FUTURE(l,theta_R,theta_I,theta_R,theta_I,Compute_Lateral,&fc[i]);
  }
  for (i=NUM_FEEDERS-1; i>=0; i--) {
    TOUCH(&fc[i]);
    tmp.P += fc[i].value.P;
    tmp.Q += fc[i].value.Q;
  }
#endif
  r->D.P = tmp.P;
  r->D.Q = tmp.Q;
}

Demand Compute_Lateral(Lateral l, double theta_R, double theta_I, 
                       double pi_R, double pi_I) {
#ifndef FUTURES
  Demand a1;
#else
  future_cell_demand fc;
#endif
  Demand a2;
  double new_pi_R, new_pi_I;
  double a,b,c,root;
  Lateral next;
  Branch br;
  
  new_pi_R = pi_R + l->alpha*(theta_R+(theta_I*l->X)/l->R);
  new_pi_I = pi_I + l->beta*(theta_I+(theta_R*l->R)/l->X);

  next = l->next_lateral;
  if (next != NULL) 
#ifndef FUTURES
    a1 = Compute_Lateral(next,theta_R,theta_I,new_pi_R,new_pi_I);
#else
    FUTURE(next,theta_R,theta_I,new_pi_R,new_pi_I,Compute_Lateral,&fc);
#endif

  br = l->branch;
  a2 = Compute_Branch(br,theta_R,theta_I,new_pi_R,new_pi_I);

  if (next != NULL) {
#ifndef FUTURES
    l->D.P = a1.P + a2.P;
    l->D.Q = a1.Q + a2.Q;
#else
    TOUCH(&fc);
    l->D.P = a2.P + fc.value.P;
    l->D.Q = a2.Q + fc.value.Q;
#endif
  } else {
    l->D.P = a2.P;
    l->D.Q = a2.Q;
  }

  /* compute P,Q */
  a = l->R*l->R + l->X*l->X;  
  b = 2*l->R*l->X*l->D.Q - 2*l->X*l->X*l->D.P - l->R;
  c = l->R*l->D.Q - l->X*l->D.P;
  c = c*c + l->R*l->D.P;
  root = (-b-sqrt(b*b-4*a*c))/(2*a);
  l->D.Q = l->D.Q + ((root-l->D.P)*l->X)/l->R;
  l->D.P = root;

  /* compute alpha, beta */
  a = 2*l->R*l->D.P;
  b = 2*l->X*l->D.Q;
  l->alpha = a/(1-a-b);
  l->beta = b/(1-a-b);
  return l->D;
}

Demand Compute_Branch(Branch br, double theta_R, double theta_I, 
                       double pi_R, double pi_I) {
  Demand a2,tmp;
  double new_pi_R, new_pi_I;
  double a,b,c,root;
  Leaf l;
  Branch next;
  int i;
#ifdef FUTURES
  future_cell_demand fc;
#else
  Demand a1;
#endif
  
  new_pi_R = pi_R + br->alpha*(theta_R+(theta_I*br->X)/br->R);
  new_pi_I = pi_I + br->beta*(theta_I+(theta_R*br->R)/br->X);

  next = br->next_branch;
  if (next != NULL)  {
#ifndef FUTURES
    a1 = Compute_Branch(next,theta_R,theta_I,new_pi_R,new_pi_I);
#else
    FUTURE(next,theta_R,theta_I,new_pi_R,new_pi_I,Compute_Branch,&fc);
#endif
  }

  /* Initialize tmp */
  tmp.P = 0.0; tmp.Q = 0.0;

  for (i=0; i<LEAVES_PER_BRANCH; i++) {
    l = br->leaves[i];
    a2 = Compute_Leaf(l,new_pi_R,new_pi_I);
    tmp.P += a2.P;
    tmp.Q += a2.Q;
  }
  if (next != NULL) {
#ifndef FUTURES
    br->D.P = a1.P + tmp.P;
    br->D.Q = a1.Q + tmp.Q;
#else
    TOUCH(&fc);
    br->D.P = fc.value.P + tmp.P;
    br->D.Q = fc.value.Q + tmp.Q;
#endif
  } else {
    br->D.P = tmp.P;
    br->D.Q = tmp.Q;
  }

  /* compute P,Q */
  a = br->R*br->R + br->X*br->X;  
  b = 2*br->R*br->X*br->D.Q - 2*br->X*br->X*br->D.P - br->R;
  c = br->R*br->D.Q - br->X*br->D.P;
  c = c*c + br->R*br->D.P;
  root = (-b-sqrt(b*b-4*a*c))/(2*a);
  br->D.Q = br->D.Q + ((root-br->D.P)*br->X)/br->R;
  br->D.P = root;
  /* compute alpha, beta */
  a = 2*br->R*br->D.P;
  b = 2*br->X*br->D.Q;
  br->alpha = a/(1-a-b);
  br->beta = b/(1-a-b);

  return br->D;
}

Demand Compute_Leaf(Leaf l, double pi_R, double pi_I) {
  P = l->D.P;
  Q = l->D.Q;
  
  optimize_node(pi_R,pi_I);

  if (P<0.0) {
    P = 0.0;
    Q = 0.0;
  }
  l->D.P = P;
  l->D.Q = Q;
  return l->D;
}

/*----------------------------------------------------------------------*/

void optimize_node (double pi_R, double pi_I)
{
    double	    g;
    double	    h;

    double	    grad_f[2];
    double	    grad_g[2];
    double	    grad_h[2];
    double	    dd_grad_f[2];
    double	    magnitude;

    int		    i;
    double	    total;
    double	    max_dist;

    do {
	/* Move onto h=0 line */
	h=find_h ();
	if (fabs (h)>H_EPSILON) {
	    magnitude=find_gradient_h (grad_h);
	    total=h/magnitude;
	    P-=total*grad_h[0];
	    Q-=total*grad_h[1];
	}

	/* Check that g is still valid */
	g=find_g ();
	if (g>G_EPSILON) {
	    magnitude=find_gradient_g (grad_g);
	    find_gradient_h (grad_h);
	    magnitude*=make_orthogonal (grad_g,grad_h);
	    total=g/magnitude;
	    P-=total*grad_g[0];
	    Q-=total*grad_g[1];
	}

	/* Maximize benefit */
	magnitude=find_gradient_f (pi_R,pi_I,grad_f);
	find_dd_grad_f (pi_R,pi_I,dd_grad_f);
	total=0.0;
	for (i=0; i<2; i++)
	    total+=grad_f[i]*dd_grad_f[i];
	magnitude/=fabs (total);
	find_gradient_h (grad_h);
	magnitude*=make_orthogonal (grad_f,grad_h);
	find_gradient_g (grad_g);
	total=0.0;
	for (i=0; i<2; i++)
	    total+=grad_f[i]*grad_g[i];
	if (total>0) {
	    max_dist=-find_g ()/total;
	    if (magnitude>max_dist)
		magnitude=max_dist;
	}
	P+=magnitude*grad_f[0];
	Q+=magnitude*grad_f[1];

	h=find_h ();
	g=find_g ();
	find_gradient_f (pi_R,pi_I,grad_f);
	find_gradient_h (grad_h);

    } while (fabs (h)>H_EPSILON || g>G_EPSILON ||
	    (fabs (g)>G_EPSILON &&
		fabs (grad_f[0]*grad_h[1]-grad_f[1]*grad_h[0])>F_EPSILON));
}

double find_g ()
{
    return (P*P+Q*Q-0.8);
}

double find_h ()
{
    return (P-5*Q);
}

double find_gradient_f (double pi_R, double pi_I, local double* gradient)
{
    int		    i;
    double	    magnitude=0.0;

    gradient[0]=1/(1+P)-pi_R;
    gradient[1]=1/(1+Q)-pi_I;
    for (i=0; i<2; i++)
	magnitude+=gradient[i]*gradient[i];
    magnitude=sqrt (magnitude);
    for (i=0; i<2; i++)
	gradient[i]/=magnitude;

    return magnitude;
}

double find_gradient_g (local double* gradient)
{
    int		    i;
    double	    magnitude=0.0;

    gradient[0]=2*P;
    gradient[1]=2*Q;
    for (i=0; i<2; i++)
	magnitude+=gradient[i]*gradient[i];
    magnitude=sqrt (magnitude);
    for (i=0; i<2; i++)
	gradient[i]/=magnitude;

    return magnitude;
}

double find_gradient_h (local double* gradient)
{
    int		    i;
    double	    magnitude=0.0;

    gradient[0]=1.0;
    gradient[1]=-5.0;
    for (i=0; i<2; i++)
	magnitude+=gradient[i]*gradient[i];
    magnitude=sqrt (magnitude);
    for (i=0; i<2; i++)
	gradient[i]/=magnitude;

    return magnitude;
}

void find_dd_grad_f (double pi_R, double pi_I, local double* dd_grad)
{
    double	    P_plus_1_inv=1/(P+1);
    double	    Q_plus_1_inv=1/(Q+1);
    double	    P_grad_term=P_plus_1_inv-pi_R;
    double	    Q_grad_term=Q_plus_1_inv-pi_I;
    double	    grad_mag;
    
    grad_mag=sqrt (P_grad_term*P_grad_term+Q_grad_term*Q_grad_term);

    dd_grad[0]=-P_plus_1_inv*P_plus_1_inv*P_grad_term/grad_mag;
    dd_grad[1]=-Q_plus_1_inv*Q_plus_1_inv*Q_grad_term/grad_mag;
}

double make_orthogonal (local double* v_mod, local double* v_static)
{
    int		    i;
    double	    total=0.0;
    double	    length=0.0;

    for (i=0; i<2; i++)
	total+=v_mod[i]*v_static[i];
    for (i=0; i<2; i++) {
	v_mod[i]-=total*v_static[i];
	length+=v_mod[i]*v_mod[i];
    }
    length=sqrt (length);
    for (i=0; i<2; i++)
	v_mod[i]/=length;

    if (1-total*total<0)    /* Roundoff error--vectors are parallel */
	return 0;

    return sqrt (1-total*total);
}

/*----------------------------------------------------------------------*/
