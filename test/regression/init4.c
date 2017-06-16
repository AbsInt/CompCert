/* C99-style initializers in the middle of a block */

int g(int x) { return x << 2; }

int f(int x, int y)
{
  int a = x + y;
  {
    y++;
    int b = y - g(x);
    return b * a;
  }
}
