#include<stdio.h>
#include<stdlib.h>

#define STR_EXPAND(tok) #tok
#define STR(tok) STR_EXPAND(tok)

#if defined(__ppc__) || defined(__PPC__) || defined(__ARMEB__)
#define ARCH_BIG_ENDIAN
#elif defined(__i386__) || defined(__x86_64__) || defined(__ARMEL__) \
   || defined(__riscv)
#undef ARCH_BIG_ENDIAN
#else
#error "unknown endianness"
#endif

union converter64 {
  double dbl;
  struct {
#ifdef ARCH_BIG_ENDIAN
    unsigned h, l;
#else
    unsigned l, h;
#endif
  } u64;
};

int num_errors = 0;

void comp64(double d, unsigned high, unsigned low, char* s) {
  union converter64 c;
  c.dbl = d;
  if((c.u64.h & 0x7FF00000) == 0x7FF00000 && (c.u64.l | (c.u64.h & 0xFFFFF)) != 0) {
    c.u64.l = 0xFFFFFFFF;
    c.u64.h = 0x7FFFFFFF;
  }
  if((high & 0x7FF00000) == 0x7FF00000 && (low | (high & 0xFFFFF)) != 0) {
    low = 0xFFFFFFFF;
    high = 0x7FFFFFFF;
  }
  if(low != c.u64.l || high != c.u64.h) {
    printf("%s : %08x %08x (%a)\n", s, c.u64.h, c.u64.l, d);
    num_errors++;
  }
}

void compd(double d1, double d2, char* s) {
  union converter64 c1, c2;
  c1.dbl = d1;
  c2.dbl = d2;
  if(c1.u64.l != c2.u64.l || c1.u64.h != c2.u64.h) {
    printf("%s : %a %a\n", s, d1, d2);
    num_errors++;
  }
}

int main(void) {
  comp64(3.518437208883201171875E+013, 0x42c00000, 0x00000002, STR(__LINE__));
  compd(1.50000000000000011102230246251565404236316680908203125, 0x1.8p+0, STR(__LINE__));
  compd(0.500000000000000166533453693773481063544750213623046875, 0x1.0000000000002p-1, STR(__LINE__));
  compd(1.2, 1.20000000000000005, STR(__LINE__));
  compd(1.2f, 1.2000001f, STR(__LINE__));
  compd(1, 1., STR(__LINE__));
  compd(0.5, .5, STR(__LINE__));
  compd(1, 1E0, STR(__LINE__));
  compd(0.5, 0x1p-1, STR(__LINE__));
  compd(0.5, 0x1.p-1, STR(__LINE__));
  compd(0.5, 0x.1p3, STR(__LINE__));
  compd(0.5, 0x.8p0, STR(__LINE__));
  compd(15./16, 0x.fp0, STR(__LINE__));
  compd(15./16, 0x.Fp0, STR(__LINE__));
  compd(15./16, 0x.fP0, STR(__LINE__));
  compd(15./16, 0X.fp0, STR(__LINE__));

  printf("%d error(s) detected.\n", num_errors);
  return 0;
}
