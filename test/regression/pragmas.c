/* Default sections */

int a;                          /* small data */
const double b = 2.718;         /* ro small data */
int c[4];                       /* large data */
const char d[12];               /* ro large data */

double g(void) { return a + b; }

/* Custom sections */

#pragma section MYCODE ".mycode" ".mycode" standard RX
#pragma section MYDATA ".mydata_i" ".mydata_u" far-absolute RW
#pragma section MYCONST ".myconst" ".myconst" far-absolute R
#pragma section MYSDA ".mysda_i" ".mysda_u" near-data RW
#pragma section MYRDA ".myrda_i" ".myrda_u" far-data RW

#pragma use_section MYDATA x, y
int x;
double y = 3.14;

#pragma use_section MYCONST z
char z[4] = { 'a', 'b', 'c', 'd' };

#pragma use_section MYSDA u
int u;

#pragma use_section MYRDA s
int s = 42;

#pragma use_section MYCODE f
int f(int n)
{
  x += n;
  u -= n;
  s += n;
  return z[n];
}

/* Redefining some standard sections */

#pragma section SCONST ".myconst" ".myconst" far-absolute R
#pragma section CONST ".myconst" ".myconst" far-absolute R
#pragma section DATA ".mysda_i" ".mysda_u" near-data RW
#pragma section CODE ".mycode" ".mycode" standard RX

const double v = 1.414;
int w[10];
const char t[5][5] = { 1, 2, 3 };

double h(int n)
{
  w[0] --;
  w[n] ++;
  return v;
}
