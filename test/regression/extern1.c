int x = 5;
int f() {
  int x = 3;
  {
    extern int x;
    return x;
  }
}
