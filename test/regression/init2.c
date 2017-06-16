/* Initialization of local const array */

int f(int x)
{
  const int dfl = 2;
  const int tbl[3] = { 12, 34, 56 };
  return tbl[x >= 0 && x < 3 ? x : dfl];
}
