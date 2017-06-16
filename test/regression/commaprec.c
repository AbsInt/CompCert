extern int f(int, int);

int g(int y) {
  int z = (y++, 0);
  return f((z = 1, z), y+2);
}
