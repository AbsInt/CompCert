int f(int x, long y)
{
  __builtin_ais_annot("x is %e1, y is %e2", x, y);
  __builtin_annot("x is %1, y is %2", x, y);
  return __builtin_annot_intval("x was here: %1", x);
}
