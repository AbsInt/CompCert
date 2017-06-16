int printf (const char *, ...);

struct S0 {
  int : 1;
  int f1;
  int : 31;
  int : 4;
  int : 0;
  int : 21;
};

struct S1 {
  struct S0 f2;
  struct S0 f3;
  int f4;
  int f6;
  struct S0 f7;
};

struct S5;

struct S1 g_21;

int g_184;
int *g_367 = &g_184;
int **g_366 = &g_367;

struct S5 *func_27 (struct S1 p_29, struct S5 *p_31)
{
  **g_366 = p_29.f7.f1;
  return p_31;
}

int main (void)
{
  func_27 (g_21, 0);
  printf ("%d\n", g_184);
  return 0;
} 
