int f() {
  {
    struct B;
    struct B { double d; };
    {
      struct B;
      extern void bar(struct B d);
      struct B  {
        int k;
        short h;
      };
      struct B p = { 1, 2};
      bar(p);
    }
  }
  return 0;
}
