int and1(int x, int y) { return x && y; }

int and2(int x, int y) { return (x == 1) && (y > 0); }

int and3(int x, int y) { if (x == 1 && y > 0) return 12; else return 16; }

extern int f(int);

int and4(int x, int y) { if (f(x) == 1 && f(y) > 0) return 12; else return 16; }

int and5(int x, int y) {
  int z;
  if (x == 1 && y > 0) { z = f(x); return z; } else { return 0; }
}

int and6(int x)
{
  while (x >= 0 && f(x) < 0) x--;
  return x;
}

int and3l(int x, int y, int z) { return (f(x) && f(y)) && f(z); }

int and3r(int x, int y, int z) { return f(x) && (f(y) && f(z)); }

int and4l(int x, int y, int z, int u) { return ((f(x) && f(y)) && f(z)) && f(u); }

int and4r(int x, int y, int z, int u) { return f(x) && (f(y) && (f(z) && f(u))); }

int and4b(int x, int y, int z, int u) { return (f(x) && f(y)) && (f(z) && f(u)); }

int or1(int x, int y) { return x || y; }

int or2(int x, int y) { return (x == 1) || (y > 0); }

int or3(int x, int y) { if (x == 1 || y > 0) return 12; else return 16; }

int or4(int x, int y) { if (f(x) == 1 || f(y) > 0) return 12; else return 16; }

int or5(int x, int y) {
  int z;
  if (x == 1 || y > 0) { z = f(x); return z; } else { return 0; }
}

int or6(int x)
{
  while (x >= 0 || f(x) < 0) x--;
  return x;
}

int or3l(int x, int y, int z) { return (f(x) || f(y)) || f(z); }

int or3r(int x, int y, int z) { return f(x) || (f(y) || f(z)); }

int or4l(int x, int y, int z, int u) { return ((f(x) || f(y)) || f(z)) || f(u); }

int or4r(int x, int y, int z, int u) { return f(x) || (f(y) || (f(z) || f(u))); }

int or4b(int x, int y, int z, int u) { return (f(x) || f(y)) || (f(z) || f(u)); }

int mixed1(int x, int y, int z) { return z && (x || y); }

int mixed2(int x, int y, int z) { return (x == 1 || y > 0) && (z < 0); }

int mixed3(int x, int y, int z) { if (z && (x || y)) return 12; else return 16; }

int mixed4(int x, int y, int z) { if ((f(x) || f(y)) && f(z)) return 12; else return 16; }

int mixed5(int x, int y, int z) {
  if ((x == 1 || y > 0) && z < 0) { z = f(x); return z; } else { return 0; }
}

int mixed6(int x)
{
  while (x == 0 || (x >= 0 && f(x) < 0)) x--;
  return x;
}

int mixed3l(int x, int y, int z) { return (f(x) && f(y)) || f(z); }

int mixed3r(int x, int y, int z) { return f(x) && (f(y) || f(z)); }

int mixed4l(int x, int y, int z, int u) { return ((f(x) && f(y)) || f(z)) && f(u); }

int mixed4r(int x, int y, int z, int u) { return f(x) && (f(y) || (f(z) && f(u))); }

int mixed4b(int x, int y, int z, int u) { return (f(x) && f(y)) || (f(z) && f(u)); }

/* This caused a RTL type error in CompCert 1.11 and 1.12 */
double cond2(int x)
{
  return x == 0 ? 3.1415 : (x > 0 ? 1 : -1);
}
