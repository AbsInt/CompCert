int (*pfun1)(int (*)(int), int);
int (*pfun2)(int (*)(int), int);

typedef int (*intfun)(int);
intfun arrfun[5];

int testf(int k) {
  return k;
}

int foo(int (*bar)(int), int n) {

  pfun1 = foo;
  pfun1 = & foo;
  pfun1 = * * * pfun2;

  pfun1 = arrfun[4];
  
  pfun2(* * testf, 5);

  return 1;
}


