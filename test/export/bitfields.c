struct s {
  int a: 10;
  char : 6;
  _Bool b : 1;
  int : 0;
  short c: 7;
};

int f(void)
{
  struct s x = { -1, 1, 2 };
  return x.a + x.b + x.c;
}
