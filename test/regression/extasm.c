/* Testing extended asm.
   To run the test, compile with -S and grep "TEST" in the generated .s */

int clobbers(int x, int z)
{
  int y;
  asm("TEST0 out:%0 in:%1" : "=r"(y) : "r"(x) : "cc"
#if defined(__x86_64__)
      , "rax", "rdx", "rbx"
#elif defined(__i386__)
      , "eax", "edx", "ebx"
#elif defined(__arm__)
      , "r0", "r1", "r4"
#elif defined(__PPC__)
      , "r0", "r3", "r4", "r31"
#endif
);
  return y + z;
}

#if (defined(ARCH_x86) && defined(MODEL_64)) \
 || (defined(ARCH_riscV) && defined(MODEL_64)) \
 || (defined(ARCH_powerpc) && defined(MODEL_ppc64)) \
 || (defined(ARCH_powerpc) && defined(MODEL_e5500))
#define SIXTYFOUR
#else
#undef SIXTYFOUR
#endif

int main()
{
  int x;
  void * y;
  long long z;
  double f;
  char c[16];

  /* No inputs, no outputs */
  asm("TEST1 %%");
  /* r inputs */
  asm("TEST2 in:%0" : : "r" (x));
  asm("TEST3 in:%0,%1" : : "r" (x), "r" (f));
  /* r output */
  asm("TEST4 out:%0" : "=r" (x));
  /* r inputs and outputs */
  asm("TEST5 out:%0 in:%1" : "=r" (f) : "r" (y));
  /* m inputs */
  asm("TEST6 in:%0" : : "m" (c[2]));
  asm("TEST7 out:%0 in:%1,%2" : "=r"(x) : "m" (c[0]), "r" (y));
  /* m output */
  asm("TEST8 out:%0 in:%1" : "=m" (c[4]) : "r" (f));
  /* i input */
  asm("TEST9 in:%0,%1,%2" : : "r"(x), "i"(sizeof(x) + 2), "r"(y));
#ifdef FAILURES
  asm("FAIL1 in:%0" : : "i"(x));
#endif
  /* 64-bit output */
#ifndef SIXTYFOUR
  asm("TEST10 out: high %R0,lo %Q0" : "=r" (z));
  /* 64-bit input */
  asm("TEST11 out:%0 in:%1,high %R2,lo %Q2,%3" 
      : "=r"(x) : "r"(y), "r"(z), "r"(f));
#endif
#ifdef FAILURES
  asm("FAIL2 out:%0" : "=r"(z));
  asm("FAIL3 in:%0" : : "r"(z));
#endif
  /* Named arguments */
  asm("TEST12 a:%[a] b:%[b] c:%[c]" : : [a]"i"(12), [b]"i"(34), [c]"i"(56));
  asm("TEST13 a:%[a] x:%[x]" : [x]"=r"(x) : [a]"i"(78));
  asm("TEST14 a:%[a] in2:%1 c:%[c]" : : [a]"i"(12), "i"(34), [c]"i"(56));
#ifdef FAILURES
  asm("FAIL4 a:%[a]" : "=r"(x) : [z]"i"(0));
#endif
  /* Various failures */
#ifdef FAILURES
  asm("FAIL5 out:%0,%1" : "=r"(x), "=r"(y));
  asm("FAIL6 in:%0" : : "g"(x));
  asm("FAIL7 out:%0" : "=r" (x+1));
#endif
  return 0;
}

