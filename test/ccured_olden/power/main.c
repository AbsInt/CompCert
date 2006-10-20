/* For copyright information, see olden_v1.0/COPYRIGHT */

/* main.c
 *
 * By:  Martin C. Carlisle
 * 6/16/94
 *
 * main routine for the Power Pricing problem
 * adapted from code by:  Steve Lumetta, Sherry Li, and Ismail Khalil
 * University of California at Berkeley
 *
 * Cleaned up the CM stuff. George Necula
 */

#include "power.h"

/* Domain of thetaR->P map is 0.65 to 1.00 [index*0.01+0.65] */
double map_P[36] =
{8752.218091048, 8446.106670416, 8107.990680283,
 7776.191574285, 7455.920518777, 7146.602181352,
 6847.709026813, 6558.734204024, 6279.213382291,
 6008.702199986, 5746.786181029, 5493.078256495,
 5247.206333097, 5008.828069358, 4777.615815166,
 4553.258735900, 4335.470002316, 4123.971545694,
 3918.501939675, 3718.817618538, 3524.683625800,
 3335.876573044, 3152.188635673, 2973.421417103,
 2799.382330486, 2629.892542617, 2464.782829705,
 2303.889031418, 2147.054385395, 1994.132771399,
 1844.985347313, 1699.475053321, 1557.474019598,
 1418.860479043, 1283.520126656, 1151.338004216};

#define      MIN_THETA_R       0.65
#define      PER_INDEX_R       0.01
#define      MAX_THETA_R       0.995

/* Domain of thetaI->Q map is 0.130 to 0.200 [index*0.002+0.130] */
double map_Q[36] =
{1768.846590190, 1706.229490046, 1637.253873079,
 1569.637451623, 1504.419525242, 1441.477913810,
 1380.700660446, 1321.980440476, 1265.218982201,
 1210.322424636, 1157.203306183, 1105.780028163,
 1055.974296746, 1007.714103979, 960.930643875,
 915.558722782, 871.538200178, 828.810882006,
 787.322098340, 747.020941334, 707.858376214,
 669.787829741, 632.765987756, 596.751545633,
 561.704466609, 527.587580585, 494.365739051,
 462.004890691, 430.472546686, 399.738429196,
 369.773787595, 340.550287137, 312.041496095,
 284.222260660, 257.068973074, 230.557938283};

#define      MIN_THETA_I       0.13
#define      PER_INDEX_I       0.002
#define      MAX_THETA_I       0.199

#ifdef PLAIN
double wallclock;
#endif

main(int argc,char *argv[])
{
  Root r;
  int i,finished=0;
  double d_theta_R,d_theta_I;
  
  chatting("Past initialization\n");

  timer_start(0);

  /* initial pass */
  r = build_tree();
  chatting("Built tree\n");
  Compute_Tree(r);
  r->last.P = r->D.P;
  r->last.Q = r->D.Q;
  r->last_theta_R = r->theta_R;
  r->last_theta_I = r->theta_I;
  r->theta_R = 0.7;
  r->theta_I = 0.14;
  
  while (!finished) {
    Compute_Tree(r);
    chatting("TR=%13.9f, TI=%13.9f, P0=%13.9f, Q0=%13.9f\n",
           r->theta_R,r->theta_I,r->D.P,r->D.Q);
    if (fabs(r->D.P/10000.0 - r->theta_R) < ROOT_EPSILON &&
        fabs(r->D.Q/10000.0 - r->theta_I) < ROOT_EPSILON) {
      finished = 1;
    } else {
      i = (int)((r->theta_R - MIN_THETA_R) / PER_INDEX_R);
      if (i<0) i=0;
      if (i>35) i=35;
      d_theta_R = -(r->theta_R - r->D.P/10000.0) /
        (1 - (map_P[i+1] - map_P[i]) / (PER_INDEX_R * 10000.0));

      i = (int)((r->theta_I - MIN_THETA_I) / PER_INDEX_I);
      if (i<0) i=0;
      if (i>35) i=35;
      d_theta_I = -(r->theta_I - r->D.Q/10000.0) /
        (1 - (map_Q[i+1] - map_Q[i]) / (PER_INDEX_I * 10000.0));
 
      chatting("D TR-%13.9f, TI=%13.9f\n", d_theta_R,d_theta_I);
      r->last.P = r->D.P;
      r->last.Q = r->D.Q;
      r->last_theta_R = r->theta_R;
      r->last_theta_I = r->theta_I;
      r->theta_R = r->theta_R + d_theta_R;
      r->theta_I = r->theta_I + d_theta_I;
    }
  } /* while */
  timer_stop(0);
  chatting("Elapsed time %f\n", timer_elapsed(0));

#ifdef FUTURES
  __ShutDown(0);
#endif
  return 0;
}
