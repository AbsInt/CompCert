extern int f(int);

void g(int x)
{
  if (x > 0) {
    (void) f(x - 1);
  }
}
