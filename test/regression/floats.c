#include<stdio.h>

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

union converter32 { float f; unsigned u; };

double double_of_bits(unsigned high, unsigned low) {
  union converter64 c;
  c.u64.l = low;
  c.u64.h = high;
  return c.dbl;
}

float single_of_bits(unsigned u) {
  union converter32 c;
  c.u = u;
  return c.f;
}

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

void comp32(float f, unsigned u, char* s) {
  union converter32 c;
  c.f = f;
  if((c.u & 0x78000000) == 0x78000000 && (c.u & 0x07FFFFFF) != 0)
    c.u = 0x7FFFFFFF;
  if((u & 0x78000000) == 0x78000000 && (u & 0x07FFFFFF) != 0)
    u = 0x7FFFFFFF;
  if(u != c.u) {
    printf("%s : %08x (%a)\n", s, c.u, (double)f);
    num_errors++;
  }
}

void compi(unsigned u1, unsigned u2, char* s) {
  if(u1 != u2) {
    printf("%s : %08x\n", s, u1);
    num_errors++;
  }
}

void f0(void) {
  comp64((signed)0x00000001, 0x3ff00000, 0x00000000, STR(__LINE__)); // (signed)0x00000001 = 0x1p+0
  comp64((signed)0x00000000, 0x00000000, 0x00000000, STR(__LINE__)); // (signed)0x00000000 = 0x0p+0
  comp64((signed)0x00000002, 0x40000000, 0x00000000, STR(__LINE__)); // (signed)0x00000002 = 0x1p+1
  comp64((signed)0x00000003, 0x40080000, 0x00000000, STR(__LINE__)); // (signed)0x00000003 = 0x1.8p+1
  comp64((signed)0x00000010, 0x40300000, 0x00000000, STR(__LINE__)); // (signed)0x00000010 = 0x1p+4
  comp64((signed)0x00000100, 0x40700000, 0x00000000, STR(__LINE__)); // (signed)0x00000100 = 0x1p+8
  comp64((signed)0x00010001, 0x40f00010, 0x00000000, STR(__LINE__)); // (signed)0x00010001 = 0x1.0001p+16
  comp64((signed)0x0000ffff, 0x40efffe0, 0x00000000, STR(__LINE__)); // (signed)0x0000ffff = 0x1.fffep+15
  comp64((signed)0x00ffffff, 0x416fffff, 0xe0000000, STR(__LINE__)); // (signed)0x00ffffff = 0x1.fffffep+23
  comp64((signed)0xffffffff, 0xbff00000, 0x00000000, STR(__LINE__)); // (signed)0xffffffff = -0x1p+0
}

void f1(void) {
  comp64((signed)0xfffffff0, 0xc0300000, 0x00000000, STR(__LINE__)); // (signed)0xfffffff0 = -0x1p+4
  comp64((signed)0x80000000, 0xc1e00000, 0x00000000, STR(__LINE__)); // (signed)0x80000000 = -0x1p+31
  comp64(single_of_bits(0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 = 0x0p+0
  comp64(single_of_bits(0x80000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 = -0x0p+0
  comp64(single_of_bits(0x7fc00000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan = nan
  comp64(single_of_bits(0xffc00000), 0xfff80000, 0x00000000, STR(__LINE__)); // -nan = -nan
  comp64(single_of_bits(0x7f800000), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf = inf
  comp64(single_of_bits(0xff800000), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf = -inf
  comp64(single_of_bits(0x3f800000), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x1p+0 = 0x1p+0
  comp64(single_of_bits(0x40000000), 0x40000000, 0x00000000, STR(__LINE__)); // 0x1p+1 = 0x1p+1
}

void f2(void) {
  comp64(single_of_bits(0x40400000), 0x40080000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 = 0x1.8p+1
  comp64(single_of_bits(0x41800000), 0x40300000, 0x00000000, STR(__LINE__)); // 0x1p+4 = 0x1p+4
  comp64(single_of_bits(0x41880000), 0x40310000, 0x00000000, STR(__LINE__)); // 0x1.1p+4 = 0x1.1p+4
  comp64(single_of_bits(0x43800000), 0x40700000, 0x00000000, STR(__LINE__)); // 0x1p+8 = 0x1p+8
  comp64(single_of_bits(0x47800080), 0x40f00010, 0x00000000, STR(__LINE__)); // 0x1.0001p+16 = 0x1.0001p+16
  comp64(single_of_bits(0x477fff00), 0x40efffe0, 0x00000000, STR(__LINE__)); // 0x1.fffep+15 = 0x1.fffep+15
  comp64(single_of_bits(0xbf800000), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x1p+0 = -0x1p+0
  comp64(single_of_bits(0xcf000000), 0xc1e00000, 0x00000000, STR(__LINE__)); // -0x1p+31 = -0x1p+31
  comp64(single_of_bits(0xdf000000), 0xc3e00000, 0x00000000, STR(__LINE__)); // -0x1p+63 = -0x1p+63
  comp64(single_of_bits(0x7f000000), 0x47e00000, 0x00000000, STR(__LINE__)); // 0x1p+127 = 0x1p+127
}

void f3(void) {
  comp64(single_of_bits(0xfe800000), 0xc7d00000, 0x00000000, STR(__LINE__)); // -0x1p+126 = -0x1p+126
  comp64(single_of_bits(0x00800000), 0x38100000, 0x00000000, STR(__LINE__)); // 0x1p-126 = 0x1p-126
  comp64((unsigned)0x00000001, 0x3ff00000, 0x00000000, STR(__LINE__)); // (unsigned)0x00000001 = 0x1p+0
  comp64((unsigned)0x00000000, 0x00000000, 0x00000000, STR(__LINE__)); // (unsigned)0x00000000 = 0x0p+0
  comp64((unsigned)0x00000002, 0x40000000, 0x00000000, STR(__LINE__)); // (unsigned)0x00000002 = 0x1p+1
  comp64((unsigned)0x00000003, 0x40080000, 0x00000000, STR(__LINE__)); // (unsigned)0x00000003 = 0x1.8p+1
  comp64((unsigned)0x00000010, 0x40300000, 0x00000000, STR(__LINE__)); // (unsigned)0x00000010 = 0x1p+4
  comp64((unsigned)0x00000100, 0x40700000, 0x00000000, STR(__LINE__)); // (unsigned)0x00000100 = 0x1p+8
  comp64((unsigned)0x00010001, 0x40f00010, 0x00000000, STR(__LINE__)); // (unsigned)0x00010001 = 0x1.0001p+16
  comp64((unsigned)0x0000ffff, 0x40efffe0, 0x00000000, STR(__LINE__)); // (unsigned)0x0000ffff = 0x1.fffep+15
}

void f4(void) {
  comp64((unsigned)0x00ffffff, 0x416fffff, 0xe0000000, STR(__LINE__)); // (unsigned)0x00ffffff = 0x1.fffffep+23
  comp64((unsigned)0x80000000, 0x41e00000, 0x00000000, STR(__LINE__)); // (unsigned)0x80000000 = 0x1p+31
  compi((signed)double_of_bits(0x00000000, 0x00000000), 0x00000000, STR(__LINE__)); // (signed)0x0p+0 = 00000000
  compi((signed)double_of_bits(0x3ff00000, 0x00000000), 0x00000001, STR(__LINE__)); // (signed)0x1p+0 = 00000001
  compi((signed)double_of_bits(0x40000000, 0x00000000), 0x00000002, STR(__LINE__)); // (signed)0x1p+1 = 00000002
  compi((signed)double_of_bits(0x40080000, 0x00000000), 0x00000003, STR(__LINE__)); // (signed)0x1.8p+1 = 00000003
  compi((signed)double_of_bits(0x40300000, 0x00000000), 0x00000010, STR(__LINE__)); // (signed)0x1p+4 = 00000010
  compi((signed)double_of_bits(0x40700000, 0x00000000), 0x00000100, STR(__LINE__)); // (signed)0x1p+8 = 00000100
  compi((signed)double_of_bits(0x40f00010, 0x00000000), 0x00010001, STR(__LINE__)); // (signed)0x1.0001p+16 = 00010001
  compi((signed)double_of_bits(0x40efffe0, 0x00000000), 0x0000ffff, STR(__LINE__)); // (signed)0x1.fffep+15 = 0000ffff
}

void f5(void) {
  compi((signed)double_of_bits(0xbff00000, 0x00000000), 0xffffffff, STR(__LINE__)); // (signed)-0x1p+0 = ffffffff
  compi((signed)double_of_bits(0xc1e00000, 0x00000000), 0x80000000, STR(__LINE__)); // (signed)-0x1p+31 = 80000000
  compi((signed)double_of_bits(0x41dfffff, 0xffc00000), 0x7fffffff, STR(__LINE__)); // (signed)0x1.fffffffcp+30 = 7fffffff
  compi((signed)double_of_bits(0xc1e00000, 0x00000000), 0x80000000, STR(__LINE__)); // (signed)-0x1p+31 = 80000000
  compi((signed)double_of_bits(0x00000000, 0x00000001), 0x00000000, STR(__LINE__)); // (signed)0x0.0000000000001p-1022 = 00000000
  compi((signed)double_of_bits(0x80000000, 0x00000001), 0x00000000, STR(__LINE__)); // (signed)-0x0.0000000000001p-1022 = 00000000
  compi((signed)double_of_bits(0x00100000, 0x00000000), 0x00000000, STR(__LINE__)); // (signed)0x1p-1022 = 00000000
  compi((signed)double_of_bits(0x80100000, 0x00000000), 0x00000000, STR(__LINE__)); // (signed)-0x1p-1022 = 00000000
  compi((signed)double_of_bits(0x40240000, 0x00000001), 0x0000000a, STR(__LINE__)); // (signed)0x1.4000000000001p+3 = 0000000a
  compi((signed)double_of_bits(0xc0240000, 0x00000001), 0xfffffff6, STR(__LINE__)); // (signed)-0x1.4000000000001p+3 = fffffff6
}

void f6(void) {
  compi((signed)double_of_bits(0x3fefffff, 0xffffffff), 0x00000000, STR(__LINE__)); // (signed)0x1.fffffffffffffp-1 = 00000000
  compi((signed)double_of_bits(0xbfefffff, 0xffffffff), 0x00000000, STR(__LINE__)); // (signed)-0x1.fffffffffffffp-1 = 00000000
  compi((signed)double_of_bits(0x3fffffff, 0xffffffff), 0x00000001, STR(__LINE__)); // (signed)0x1.fffffffffffffp+0 = 00000001
  compi((signed)double_of_bits(0xbfffffff, 0xffffffff), 0xffffffff, STR(__LINE__)); // (signed)-0x1.fffffffffffffp+0 = ffffffff
  compi((signed)double_of_bits(0x3ff80000, 0x00000000), 0x00000001, STR(__LINE__)); // (signed)0x1.8p+0 = 00000001
  compi((signed)double_of_bits(0xbff80000, 0x00000000), 0xffffffff, STR(__LINE__)); // (signed)-0x1.8p+0 = ffffffff
  compi((signed)double_of_bits(0x40040000, 0x00000000), 0x00000002, STR(__LINE__)); // (signed)0x1.4p+1 = 00000002
  compi((signed)double_of_bits(0xc0040000, 0x00000000), 0xfffffffe, STR(__LINE__)); // (signed)-0x1.4p+1 = fffffffe
  compi((signed)double_of_bits(0x3ff80000, 0x00000001), 0x00000001, STR(__LINE__)); // (signed)0x1.8000000000001p+0 = 00000001
  compi((signed)double_of_bits(0xbff80000, 0x00000001), 0xffffffff, STR(__LINE__)); // (signed)-0x1.8000000000001p+0 = ffffffff
}

void f7(void) {
  compi((signed)double_of_bits(0x3ff7ffff, 0xffffffff), 0x00000001, STR(__LINE__)); // (signed)0x1.7ffffffffffffp+0 = 00000001
  compi((signed)double_of_bits(0xbff7ffff, 0xffffffff), 0xffffffff, STR(__LINE__)); // (signed)-0x1.7ffffffffffffp+0 = ffffffff
  compi((signed)double_of_bits(0x41d00000, 0x00400000), 0x40000001, STR(__LINE__)); // (signed)0x1.00000004p+30 = 40000001
  compi((signed)double_of_bits(0x41700000, 0x00000001), 0x01000000, STR(__LINE__)); // (signed)0x1.0000000000001p+24 = 01000000
  compi((signed)double_of_bits(0x416fffff, 0xffffffff), 0x00ffffff, STR(__LINE__)); // (signed)0x1.fffffffffffffp+23 = 00ffffff
  compi((signed)double_of_bits(0x41600000, 0x00000001), 0x00800000, STR(__LINE__)); // (signed)0x1.0000000000001p+23 = 00800000
  compi((signed)double_of_bits(0xc1600000, 0x00000001), 0xff800000, STR(__LINE__)); // (signed)-0x1.0000000000001p+23 = ff800000
  compi((unsigned)double_of_bits(0x00000000, 0x00000000), 0x00000000, STR(__LINE__)); // (unsigned)0x0p+0 = 00000000
  compi((unsigned)double_of_bits(0x3ff00000, 0x00000000), 0x00000001, STR(__LINE__)); // (unsigned)0x1p+0 = 00000001
  compi((unsigned)double_of_bits(0x40000000, 0x00000000), 0x00000002, STR(__LINE__)); // (unsigned)0x1p+1 = 00000002
}

void f8(void) {
  compi((unsigned)double_of_bits(0x40080000, 0x00000000), 0x00000003, STR(__LINE__)); // (unsigned)0x1.8p+1 = 00000003
  compi((unsigned)double_of_bits(0x40300000, 0x00000000), 0x00000010, STR(__LINE__)); // (unsigned)0x1p+4 = 00000010
  compi((unsigned)double_of_bits(0x40700000, 0x00000000), 0x00000100, STR(__LINE__)); // (unsigned)0x1p+8 = 00000100
  compi((unsigned)double_of_bits(0x40f00010, 0x00000000), 0x00010001, STR(__LINE__)); // (unsigned)0x1.0001p+16 = 00010001
  compi((unsigned)double_of_bits(0x40efffe0, 0x00000000), 0x0000ffff, STR(__LINE__)); // (unsigned)0x1.fffep+15 = 0000ffff
  compi((unsigned)double_of_bits(0x41efffff, 0xffe00000), 0xffffffff, STR(__LINE__)); // (unsigned)0x1.fffffffep+31 = ffffffff
  compi((unsigned)double_of_bits(0x00000000, 0x00000001), 0x00000000, STR(__LINE__)); // (unsigned)0x0.0000000000001p-1022 = 00000000
  compi((unsigned)double_of_bits(0x00100000, 0x00000000), 0x00000000, STR(__LINE__)); // (unsigned)0x1p-1022 = 00000000
  compi((unsigned)double_of_bits(0x40240000, 0x00000001), 0x0000000a, STR(__LINE__)); // (unsigned)0x1.4000000000001p+3 = 0000000a
  compi((unsigned)double_of_bits(0x3fefffff, 0xffffffff), 0x00000000, STR(__LINE__)); // (unsigned)0x1.fffffffffffffp-1 = 00000000
}

void f9(void) {
  compi((unsigned)double_of_bits(0x3fffffff, 0xffffffff), 0x00000001, STR(__LINE__)); // (unsigned)0x1.fffffffffffffp+0 = 00000001
  compi((unsigned)double_of_bits(0x3ff80000, 0x00000000), 0x00000001, STR(__LINE__)); // (unsigned)0x1.8p+0 = 00000001
  compi((unsigned)double_of_bits(0x40040000, 0x00000000), 0x00000002, STR(__LINE__)); // (unsigned)0x1.4p+1 = 00000002
  compi((unsigned)double_of_bits(0x3ff80000, 0x00000001), 0x00000001, STR(__LINE__)); // (unsigned)0x1.8000000000001p+0 = 00000001
  compi((unsigned)double_of_bits(0x3ff7ffff, 0xffffffff), 0x00000001, STR(__LINE__)); // (unsigned)0x1.7ffffffffffffp+0 = 00000001
  compi((unsigned)double_of_bits(0x41e00000, 0x00200000), 0x80000001, STR(__LINE__)); // (unsigned)0x1.00000002p+31 = 80000001
  compi((unsigned)double_of_bits(0x41700000, 0x00000001), 0x01000000, STR(__LINE__)); // (unsigned)0x1.0000000000001p+24 = 01000000
  compi((unsigned)double_of_bits(0x416fffff, 0xffffffff), 0x00ffffff, STR(__LINE__)); // (unsigned)0x1.fffffffffffffp+23 = 00ffffff
  compi((unsigned)double_of_bits(0x41600000, 0x00000001), 0x00800000, STR(__LINE__)); // (unsigned)0x1.0000000000001p+23 = 00800000
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // 0x1p+0 + 0x1p+0 = 0x1p+1
}

void f10(void) {
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0xbff00000, 0x00000000), 0xc0000000, 0x00000000, STR(__LINE__)); // -0x1p+0 + -0x1p+0 = -0x1p+1
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x40000000, 0x00000000), 0x40080000, 0x00000000, STR(__LINE__)); // 0x1p+0 + 0x1p+1 = 0x1.8p+1
  comp64(double_of_bits(0x40000000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000000), 0x40080000, 0x00000000, STR(__LINE__)); // 0x1p+1 + 0x1p+0 = 0x1.8p+1
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0xc0000000, 0x00000000), 0xc0080000, 0x00000000, STR(__LINE__)); // -0x1p+0 + -0x1p+1 = -0x1.8p+1
  comp64(double_of_bits(0xc0000000, 0x00000000) + double_of_bits(0xbff00000, 0x00000000), 0xc0080000, 0x00000000, STR(__LINE__)); // -0x1p+1 + -0x1p+0 = -0x1.8p+1
  comp64(double_of_bits(0x40000000, 0x00000000) + double_of_bits(0x40000000, 0x00000000), 0x40100000, 0x00000000, STR(__LINE__)); // 0x1p+1 + 0x1p+1 = 0x1p+2
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x401c0000, 0x00000000), 0x40200000, 0x00000000, STR(__LINE__)); // 0x1p+0 + 0x1.cp+2 = 0x1p+3
  comp64(double_of_bits(0x401c0000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000000), 0x40200000, 0x00000000, STR(__LINE__)); // 0x1.cp+2 + 0x1p+0 = 0x1p+3
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0xc01c0000, 0x00000000), 0xc0200000, 0x00000000, STR(__LINE__)); // -0x1p+0 + -0x1.cp+2 = -0x1p+3
  comp64(double_of_bits(0xc01c0000, 0x00000000) + double_of_bits(0xbff00000, 0x00000000), 0xc0200000, 0x00000000, STR(__LINE__)); // -0x1.cp+2 + -0x1p+0 = -0x1p+3
}

void f11(void) {
  comp64(double_of_bits(0x40140000, 0x00000000) + double_of_bits(0xbff00000, 0x00000000), 0x40100000, 0x00000000, STR(__LINE__)); // 0x1.4p+2 + -0x1p+0 = 0x1p+2
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0x40140000, 0x00000000), 0x40100000, 0x00000000, STR(__LINE__)); // -0x1p+0 + 0x1.4p+2 = 0x1p+2
  comp64(double_of_bits(0xc0140000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000000), 0xc0100000, 0x00000000, STR(__LINE__)); // -0x1.4p+2 + 0x1p+0 = -0x1p+2
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0xc0140000, 0x00000000), 0xc0100000, 0x00000000, STR(__LINE__)); // 0x1p+0 + -0x1.4p+2 = -0x1p+2
  comp64(double_of_bits(0x40000000, 0x00000000) + double_of_bits(0xc0140000, 0x00000000), 0xc0080000, 0x00000000, STR(__LINE__)); // 0x1p+1 + -0x1.4p+2 = -0x1.8p+1
  comp64(double_of_bits(0xc0140000, 0x00000000) + double_of_bits(0x40000000, 0x00000000), 0xc0080000, 0x00000000, STR(__LINE__)); // -0x1.4p+2 + 0x1p+1 = -0x1.8p+1
  comp64(double_of_bits(0xc0000000, 0x00000000) + double_of_bits(0x40140000, 0x00000000), 0x40080000, 0x00000000, STR(__LINE__)); // -0x1p+1 + 0x1.4p+2 = 0x1.8p+1
  comp64(double_of_bits(0x40140000, 0x00000000) + double_of_bits(0xc0000000, 0x00000000), 0x40080000, 0x00000000, STR(__LINE__)); // 0x1.4p+2 + -0x1p+1 = 0x1.8p+1
  comp64(double_of_bits(0x40000000, 0x00000000) + double_of_bits(0xc0100000, 0x00000000), 0xc0000000, 0x00000000, STR(__LINE__)); // 0x1p+1 + -0x1p+2 = -0x1p+1
  comp64(double_of_bits(0xc0100000, 0x00000000) + double_of_bits(0x40000000, 0x00000000), 0xc0000000, 0x00000000, STR(__LINE__)); // -0x1p+2 + 0x1p+1 = -0x1p+1
}

void f12(void) {
  comp64(double_of_bits(0x40100000, 0x00000000) + double_of_bits(0xc0000000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // 0x1p+2 + -0x1p+1 = 0x1p+1
  comp64(double_of_bits(0xc0000000, 0x00000000) + double_of_bits(0x40100000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // -0x1p+1 + 0x1p+2 = 0x1p+1
  comp64(double_of_bits(0x00000000, 0x00000000) + double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 + -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) + double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 + 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) + double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 + 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) + double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 + -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) + double_of_bits(0x000fffff, 0xffffffff), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x0p+0 + 0x0.fffffffffffffp-1022 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x000fffff, 0xffffffff) + double_of_bits(0x00000000, 0x00000000), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x0.fffffffffffffp-1022 + 0x0p+0 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x80000000, 0x00000000) + double_of_bits(0x000fffff, 0xffffffff), 0x000fffff, 0xffffffff, STR(__LINE__)); // -0x0p+0 + 0x0.fffffffffffffp-1022 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x000fffff, 0xffffffff) + double_of_bits(0x80000000, 0x00000000), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x0.fffffffffffffp-1022 + -0x0p+0 = 0x0.fffffffffffffp-1022
}

void f13(void) {
  comp64(double_of_bits(0x00000000, 0x00000000) + double_of_bits(0x800fffff, 0xffffffff), 0x800fffff, 0xffffffff, STR(__LINE__)); // 0x0p+0 + -0x0.fffffffffffffp-1022 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) + double_of_bits(0x00000000, 0x00000000), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x0.fffffffffffffp-1022 + 0x0p+0 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x80000000, 0x00000000) + double_of_bits(0x800fffff, 0xffffffff), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x0p+0 + -0x0.fffffffffffffp-1022 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) + double_of_bits(0x80000000, 0x00000000), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x0.fffffffffffffp-1022 + -0x0p+0 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x00000000, 0x00000003) + double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000003, STR(__LINE__)); // 0x0.0000000000003p-1022 + 0x0p+0 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0x00000000, 0x00000000) + double_of_bits(0x00000000, 0x00000003), 0x00000000, 0x00000003, STR(__LINE__)); // 0x0p+0 + 0x0.0000000000003p-1022 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0x00000000, 0x00000003) + double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000003, STR(__LINE__)); // 0x0.0000000000003p-1022 + -0x0p+0 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0x80000000, 0x00000000) + double_of_bits(0x00000000, 0x00000003), 0x00000000, 0x00000003, STR(__LINE__)); // -0x0p+0 + 0x0.0000000000003p-1022 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0x80000000, 0x00000003) + double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000003, STR(__LINE__)); // -0x0.0000000000003p-1022 + 0x0p+0 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0x00000000, 0x00000000) + double_of_bits(0x80000000, 0x00000003), 0x80000000, 0x00000003, STR(__LINE__)); // 0x0p+0 + -0x0.0000000000003p-1022 = -0x0.0000000000003p-1022
}

void f14(void) {
  comp64(double_of_bits(0x80000000, 0x00000003) + double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000003, STR(__LINE__)); // -0x0.0000000000003p-1022 + -0x0p+0 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0x80000000, 0x00000000) + double_of_bits(0x80000000, 0x00000003), 0x80000000, 0x00000003, STR(__LINE__)); // -0x0p+0 + -0x0.0000000000003p-1022 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0x80000000, 0x00000000) + double_of_bits(0x80100000, 0x00000000), 0x80100000, 0x00000000, STR(__LINE__)); // -0x0p+0 + -0x1p-1022 = -0x1p-1022
  comp64(double_of_bits(0x80100000, 0x00000000) + double_of_bits(0x80000000, 0x00000000), 0x80100000, 0x00000000, STR(__LINE__)); // -0x1p-1022 + -0x0p+0 = -0x1p-1022
  comp64(double_of_bits(0x00100000, 0x00000000) + double_of_bits(0x00000000, 0x00000000), 0x00100000, 0x00000000, STR(__LINE__)); // 0x1p-1022 + 0x0p+0 = 0x1p-1022
  comp64(double_of_bits(0x00000000, 0x00000000) + double_of_bits(0x00100000, 0x00000000), 0x00100000, 0x00000000, STR(__LINE__)); // 0x0p+0 + 0x1p-1022 = 0x1p-1022
  comp64(double_of_bits(0x00000000, 0x00000000) + double_of_bits(0x80100000, 0x00000000), 0x80100000, 0x00000000, STR(__LINE__)); // 0x0p+0 + -0x1p-1022 = -0x1p-1022
  comp64(double_of_bits(0x80100000, 0x00000000) + double_of_bits(0x00000000, 0x00000000), 0x80100000, 0x00000000, STR(__LINE__)); // -0x1p-1022 + 0x0p+0 = -0x1p-1022
  comp64(double_of_bits(0x00000000, 0x00000000) + double_of_bits(0x7fe00000, 0x00000000), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x0p+0 + 0x1p+1023 = 0x1p+1023
  comp64(double_of_bits(0x7fe00000, 0x00000000) + double_of_bits(0x00000000, 0x00000000), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 + 0x0p+0 = 0x1p+1023
}

void f15(void) {
  comp64(double_of_bits(0x80000000, 0x00000000) + double_of_bits(0x7fe00000, 0x00000000), 0x7fe00000, 0x00000000, STR(__LINE__)); // -0x0p+0 + 0x1p+1023 = 0x1p+1023
  comp64(double_of_bits(0x7fe00000, 0x00000000) + double_of_bits(0x80000000, 0x00000000), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 + -0x0p+0 = 0x1p+1023
  comp64(double_of_bits(0xffe00000, 0x00000000) + double_of_bits(0x00000000, 0x00000000), 0xffe00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 + 0x0p+0 = -0x1p+1023
  comp64(double_of_bits(0x00000000, 0x00000000) + double_of_bits(0xffe00000, 0x00000000), 0xffe00000, 0x00000000, STR(__LINE__)); // 0x0p+0 + -0x1p+1023 = -0x1p+1023
  comp64(double_of_bits(0xffe00000, 0x00000000) + double_of_bits(0x80000000, 0x00000000), 0xffe00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 + -0x0p+0 = -0x1p+1023
  comp64(double_of_bits(0x80000000, 0x00000000) + double_of_bits(0xffe00000, 0x00000000), 0xffe00000, 0x00000000, STR(__LINE__)); // -0x0p+0 + -0x1p+1023 = -0x1p+1023
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x80000000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x1p+0 + -0x0p+0 = 0x1p+0
  comp64(double_of_bits(0x80000000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // -0x0p+0 + 0x1p+0 = 0x1p+0
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0x80000000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x1p+0 + -0x0p+0 = -0x1p+0
  comp64(double_of_bits(0x80000000, 0x00000000) + double_of_bits(0xbff00000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x0p+0 + -0x1p+0 = -0x1p+0
}

void f16(void) {
  comp64(double_of_bits(0x00000000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x0p+0 + 0x1p+0 = 0x1p+0
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x00000000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x1p+0 + 0x0p+0 = 0x1p+0
  comp64(double_of_bits(0x40140000, 0x00000000) + double_of_bits(0x80000000, 0x00000000), 0x40140000, 0x00000000, STR(__LINE__)); // 0x1.4p+2 + -0x0p+0 = 0x1.4p+2
  comp64(double_of_bits(0x80000000, 0x00000000) + double_of_bits(0x40140000, 0x00000000), 0x40140000, 0x00000000, STR(__LINE__)); // -0x0p+0 + 0x1.4p+2 = 0x1.4p+2
  comp64(double_of_bits(0x40140000, 0x00000000) + double_of_bits(0x00000000, 0x00000000), 0x40140000, 0x00000000, STR(__LINE__)); // 0x1.4p+2 + 0x0p+0 = 0x1.4p+2
  comp64(double_of_bits(0x00000000, 0x00000000) + double_of_bits(0x40140000, 0x00000000), 0x40140000, 0x00000000, STR(__LINE__)); // 0x0p+0 + 0x1.4p+2 = 0x1.4p+2
  comp64(double_of_bits(0x7ff00000, 0x00000000) + double_of_bits(0x00000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf + 0x0p+0 = inf
  comp64(double_of_bits(0x00000000, 0x00000000) + double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x0p+0 + inf = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) + double_of_bits(0x80000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf + -0x0p+0 = inf
  comp64(double_of_bits(0x80000000, 0x00000000) + double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x0p+0 + inf = inf
}

void f17(void) {
  comp64(double_of_bits(0xfff00000, 0x00000000) + double_of_bits(0x00000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf + 0x0p+0 = -inf
  comp64(double_of_bits(0x00000000, 0x00000000) + double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x0p+0 + -inf = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) + double_of_bits(0x80000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf + -0x0p+0 = -inf
  comp64(double_of_bits(0x80000000, 0x00000000) + double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x0p+0 + -inf = -inf
  comp64(double_of_bits(0x7ff80000, 0x00000000) + double_of_bits(0x00000000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan + 0x0p+0 = nan
  comp64(double_of_bits(0x00000000, 0x00000000) + double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x0p+0 + nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) + double_of_bits(0x80000000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan + -0x0p+0 = nan
  comp64(double_of_bits(0x80000000, 0x00000000) + double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x0p+0 + nan = nan
  comp64(double_of_bits(0x7ff00000, 0x00000000) + double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf + inf = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) + double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf + -inf = -inf
}

void f18(void) {
  comp64(double_of_bits(0xfff00000, 0x00000000) + double_of_bits(0x7ff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -inf + inf = nan
  comp64(double_of_bits(0x7ff00000, 0x00000000) + double_of_bits(0xfff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // inf + -inf = nan
  comp64(double_of_bits(0x7ff00000, 0x00000000) + double_of_bits(0x000fffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf + 0x0.fffffffffffffp-1022 = inf
  comp64(double_of_bits(0x000fffff, 0xffffffff) + double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 + inf = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) + double_of_bits(0x000fffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf + 0x0.fffffffffffffp-1022 = -inf
  comp64(double_of_bits(0x000fffff, 0xffffffff) + double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 + -inf = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) + double_of_bits(0x800fffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf + -0x0.fffffffffffffp-1022 = inf
  comp64(double_of_bits(0x800fffff, 0xffffffff) + double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 + inf = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) + double_of_bits(0x800fffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf + -0x0.fffffffffffffp-1022 = -inf
  comp64(double_of_bits(0x800fffff, 0xffffffff) + double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 + -inf = -inf
}

void f19(void) {
  comp64(double_of_bits(0x00000000, 0x00000003) + double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000003p-1022 + inf = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) + double_of_bits(0x00000000, 0x00000003), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf + 0x0.0000000000003p-1022 = inf
  comp64(double_of_bits(0x00000000, 0x00000003) + double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000003p-1022 + -inf = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) + double_of_bits(0x00000000, 0x00000003), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf + 0x0.0000000000003p-1022 = -inf
  comp64(double_of_bits(0x80000000, 0x00000003) + double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000003p-1022 + inf = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) + double_of_bits(0x80000000, 0x00000003), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf + -0x0.0000000000003p-1022 = inf
  comp64(double_of_bits(0x80000000, 0x00000003) + double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000003p-1022 + -inf = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) + double_of_bits(0x80000000, 0x00000003), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf + -0x0.0000000000003p-1022 = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) + double_of_bits(0x7fe00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf + 0x1p+1023 = inf
  comp64(double_of_bits(0x7fe00000, 0x00000000) + double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 + inf = inf
}

void f20(void) {
  comp64(double_of_bits(0x7ff00000, 0x00000000) + double_of_bits(0xffe00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf + -0x1p+1023 = inf
  comp64(double_of_bits(0xffe00000, 0x00000000) + double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 + inf = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) + double_of_bits(0x7fe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf + 0x1p+1023 = -inf
  comp64(double_of_bits(0x7fe00000, 0x00000000) + double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 + -inf = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) + double_of_bits(0xffe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf + -0x1p+1023 = -inf
  comp64(double_of_bits(0xffe00000, 0x00000000) + double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 + -inf = -inf
  comp64(double_of_bits(0x7ff80000, 0x00000000) + double_of_bits(0x7ff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan + inf = nan
  comp64(double_of_bits(0x7ff00000, 0x00000000) + double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // inf + nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) + double_of_bits(0xfff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan + -inf = nan
  comp64(double_of_bits(0xfff00000, 0x00000000) + double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -inf + nan = nan
}

void f21(void) {
  comp64(double_of_bits(0x7ff80000, 0x00000000) + double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan + nan = nan
  comp64(double_of_bits(0x000fffff, 0xffffffff) + double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 + nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) + double_of_bits(0x000fffff, 0xffffffff), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan + 0x0.fffffffffffffp-1022 = nan
  comp64(double_of_bits(0x800fffff, 0xffffffff) + double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 + nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) + double_of_bits(0x800fffff, 0xffffffff), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan + -0x0.fffffffffffffp-1022 = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) + double_of_bits(0x00000000, 0x00000001), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan + 0x0.0000000000001p-1022 = nan
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 + nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) + double_of_bits(0x80000000, 0x00000001), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan + -0x0.0000000000001p-1022 = nan
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 + nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan + 0x1p+0 = nan
}

void f22(void) {
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x1p+0 + nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) + double_of_bits(0xbff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan + -0x1p+0 = nan
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x1p+0 + nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) + double_of_bits(0x7fefffff, 0xffffffff), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan + 0x1.fffffffffffffp+1023 = nan
  comp64(double_of_bits(0x7fefffff, 0xffffffff) + double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 + nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) + double_of_bits(0xffefffff, 0xffffffff), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan + -0x1.fffffffffffffp+1023 = nan
  comp64(double_of_bits(0xffefffff, 0xffffffff) + double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 + nan = nan
  comp64(double_of_bits(0x7fe00000, 0x00000000) + double_of_bits(0x7fe00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 + 0x1p+1023 = inf
  comp64(double_of_bits(0xffe00000, 0x00000000) + double_of_bits(0xffe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 + -0x1p+1023 = -inf
  comp64(double_of_bits(0x7fefffff, 0xfffffffe) + double_of_bits(0x7fefffff, 0xfffffffe), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffep+1023 + 0x1.ffffffffffffep+1023 = inf
}

void f23(void) {
  comp64(double_of_bits(0xffefffff, 0xfffffffe) + double_of_bits(0xffefffff, 0xfffffffe), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffep+1023 + -0x1.ffffffffffffep+1023 = -inf
  comp64(double_of_bits(0x7fefffff, 0xfffffffe) + double_of_bits(0x7fefffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffep+1023 + 0x1.fffffffffffffp+1023 = inf
  comp64(double_of_bits(0x7fefffff, 0xffffffff) + double_of_bits(0x7fefffff, 0xfffffffe), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 + 0x1.ffffffffffffep+1023 = inf
  comp64(double_of_bits(0xffefffff, 0xfffffffe) + double_of_bits(0xffefffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffep+1023 + -0x1.fffffffffffffp+1023 = -inf
  comp64(double_of_bits(0xffefffff, 0xffffffff) + double_of_bits(0xffefffff, 0xfffffffe), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 + -0x1.ffffffffffffep+1023 = -inf
  comp64(double_of_bits(0x7fe00000, 0x00000001) + double_of_bits(0x7fe00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+1023 + 0x1p+1023 = inf
  comp64(double_of_bits(0x7fe00000, 0x00000000) + double_of_bits(0x7fe00000, 0x00000001), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 + 0x1.0000000000001p+1023 = inf
  comp64(double_of_bits(0xffe00000, 0x00000001) + double_of_bits(0xffe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+1023 + -0x1p+1023 = -inf
  comp64(double_of_bits(0xffe00000, 0x00000000) + double_of_bits(0xffe00000, 0x00000001), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 + -0x1.0000000000001p+1023 = -inf
  comp64(double_of_bits(0x7fefffff, 0xffffffff) + double_of_bits(0x7cb00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 + 0x1p+972 = inf
}

void f24(void) {
  comp64(double_of_bits(0x7cb00000, 0x00000000) + double_of_bits(0x7fefffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p+972 + 0x1.fffffffffffffp+1023 = inf
  comp64(double_of_bits(0xffefffff, 0xffffffff) + double_of_bits(0xfcb00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 + -0x1p+972 = -inf
  comp64(double_of_bits(0xfcb00000, 0x00000000) + double_of_bits(0xffefffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1p+972 + -0x1.fffffffffffffp+1023 = -inf
  comp64(double_of_bits(0x7fefffff, 0xffffffff) + double_of_bits(0x3ff00000, 0x00000000), 0x7fefffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1023 + 0x1p+0 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x7fefffff, 0xffffffff), 0x7fefffff, 0xffffffff, STR(__LINE__)); // 0x1p+0 + 0x1.fffffffffffffp+1023 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xffefffff, 0xffffffff) + double_of_bits(0xbff00000, 0x00000000), 0xffefffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1023 + -0x1p+0 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0xffefffff, 0xffffffff), 0xffefffff, 0xffffffff, STR(__LINE__)); // -0x1p+0 + -0x1.fffffffffffffp+1023 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x7fefffff, 0xffffffff), 0x7fefffff, 0xffffffff, STR(__LINE__)); // 0x0.0000000000001p-1022 + 0x1.fffffffffffffp+1023 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x7fefffff, 0xffffffff) + double_of_bits(0x00000000, 0x00000001), 0x7fefffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1023 + 0x0.0000000000001p-1022 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0xffefffff, 0xffffffff), 0xffefffff, 0xffffffff, STR(__LINE__)); // -0x0.0000000000001p-1022 + -0x1.fffffffffffffp+1023 = -0x1.fffffffffffffp+1023
}

void f25(void) {
  comp64(double_of_bits(0xffefffff, 0xffffffff) + double_of_bits(0x80000000, 0x00000001), 0xffefffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1023 + -0x0.0000000000001p-1022 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x7fefffff, 0xffffffff) + double_of_bits(0x7c800000, 0x00000000), 0x7fefffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1023 + 0x1p+969 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x7c800000, 0x00000000) + double_of_bits(0x7fefffff, 0xffffffff), 0x7fefffff, 0xffffffff, STR(__LINE__)); // 0x1p+969 + 0x1.fffffffffffffp+1023 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xffefffff, 0xffffffff) + double_of_bits(0xfc800000, 0x00000000), 0xffefffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1023 + -0x1p+969 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xfc800000, 0x00000000) + double_of_bits(0xffefffff, 0xffffffff), 0xffefffff, 0xffffffff, STR(__LINE__)); // -0x1p+969 + -0x1.fffffffffffffp+1023 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x7fefffff, 0xffffffff) + double_of_bits(0x7c800000, 0x00000001), 0x7fefffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1023 + 0x1.0000000000001p+969 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x7c800000, 0x00000001) + double_of_bits(0x7fefffff, 0xffffffff), 0x7fefffff, 0xffffffff, STR(__LINE__)); // 0x1.0000000000001p+969 + 0x1.fffffffffffffp+1023 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xffefffff, 0xffffffff) + double_of_bits(0xfc800000, 0x00000001), 0xffefffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1023 + -0x1.0000000000001p+969 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xfc800000, 0x00000001) + double_of_bits(0xffefffff, 0xffffffff), 0xffefffff, 0xffffffff, STR(__LINE__)); // -0x1.0000000000001p+969 + -0x1.fffffffffffffp+1023 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x7fdfffff, 0xffffffff) + double_of_bits(0x7fe00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1022 + 0x1p+1023 = inf
}

void f26(void) {
  comp64(double_of_bits(0x7fe00000, 0x00000000) + double_of_bits(0x7fdfffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 + 0x1.fffffffffffffp+1022 = inf
  comp64(double_of_bits(0xffdfffff, 0xffffffff) + double_of_bits(0xffe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1022 + -0x1p+1023 = -inf
  comp64(double_of_bits(0xffe00000, 0x00000000) + double_of_bits(0xffdfffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 + -0x1.fffffffffffffp+1022 = -inf
  comp64(double_of_bits(0x7fefffff, 0xffffffff) + double_of_bits(0x7c980000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 + 0x1.8p+970 = inf
  comp64(double_of_bits(0x7c980000, 0x00000000) + double_of_bits(0x7fefffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.8p+970 + 0x1.fffffffffffffp+1023 = inf
  comp64(double_of_bits(0xffefffff, 0xffffffff) + double_of_bits(0xfc980000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 + -0x1.8p+970 = -inf
  comp64(double_of_bits(0xfc980000, 0x00000000) + double_of_bits(0xffefffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.8p+970 + -0x1.fffffffffffffp+1023 = -inf
  comp64(double_of_bits(0x7fefffff, 0xffffffff) + double_of_bits(0x7c900000, 0x00000001), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 + 0x1.0000000000001p+970 = inf
  comp64(double_of_bits(0x7c900000, 0x00000001) + double_of_bits(0x7fefffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+970 + 0x1.fffffffffffffp+1023 = inf
  comp64(double_of_bits(0xffefffff, 0xffffffff) + double_of_bits(0xfc900000, 0x00000001), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 + -0x1.0000000000001p+970 = -inf
}

void f27(void) {
  comp64(double_of_bits(0xfc900000, 0x00000001) + double_of_bits(0xffefffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+970 + -0x1.fffffffffffffp+1023 = -inf
  comp64(double_of_bits(0x7fefffff, 0xffffffff) + double_of_bits(0x7c980000, 0x00000001), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 + 0x1.8000000000001p+970 = inf
  comp64(double_of_bits(0x7c980000, 0x00000001) + double_of_bits(0x7fefffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.8000000000001p+970 + 0x1.fffffffffffffp+1023 = inf
  comp64(double_of_bits(0xffefffff, 0xffffffff) + double_of_bits(0xfc980000, 0x00000001), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 + -0x1.8000000000001p+970 = -inf
  comp64(double_of_bits(0xfc980000, 0x00000001) + double_of_bits(0xffefffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.8000000000001p+970 + -0x1.fffffffffffffp+1023 = -inf
  comp64(double_of_bits(0x7fe00000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000000), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 + 0x1p+0 = 0x1p+1023
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x7fe00000, 0x00000000), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x1p+0 + 0x1p+1023 = 0x1p+1023
  comp64(double_of_bits(0xffe00000, 0x00000000) + double_of_bits(0xbff00000, 0x00000000), 0xffe00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 + -0x1p+0 = -0x1p+1023
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0xffe00000, 0x00000000), 0xffe00000, 0x00000000, STR(__LINE__)); // -0x1p+0 + -0x1p+1023 = -0x1p+1023
  comp64(double_of_bits(0x7fdfffff, 0xffffffff) + double_of_bits(0x3ff00000, 0x00000000), 0x7fdfffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1022 + 0x1p+0 = 0x1.fffffffffffffp+1022
}

void f28(void) {
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x7fdfffff, 0xffffffff), 0x7fdfffff, 0xffffffff, STR(__LINE__)); // 0x1p+0 + 0x1.fffffffffffffp+1022 = 0x1.fffffffffffffp+1022
  comp64(double_of_bits(0x7fefffff, 0xfffffffe) + double_of_bits(0x3ff00000, 0x00000000), 0x7fefffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffep+1023 + 0x1p+0 = 0x1.ffffffffffffep+1023
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x7fefffff, 0xfffffffe), 0x7fefffff, 0xfffffffe, STR(__LINE__)); // 0x1p+0 + 0x1.ffffffffffffep+1023 = 0x1.ffffffffffffep+1023
  comp64(double_of_bits(0xffefffff, 0xfffffffe) + double_of_bits(0xbff00000, 0x00000000), 0xffefffff, 0xfffffffe, STR(__LINE__)); // -0x1.ffffffffffffep+1023 + -0x1p+0 = -0x1.ffffffffffffep+1023
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0xffefffff, 0xfffffffe), 0xffefffff, 0xfffffffe, STR(__LINE__)); // -0x1p+0 + -0x1.ffffffffffffep+1023 = -0x1.ffffffffffffep+1023
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x7fe00000, 0x00000000), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 + 0x1p+1023 = 0x1p+1023
  comp64(double_of_bits(0x7fe00000, 0x00000000) + double_of_bits(0x00000000, 0x00000001), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 + 0x0.0000000000001p-1022 = 0x1p+1023
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0xffe00000, 0x00000000), 0xffe00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 + -0x1p+1023 = -0x1p+1023
  comp64(double_of_bits(0xffe00000, 0x00000000) + double_of_bits(0x80000000, 0x00000001), 0xffe00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 + -0x0.0000000000001p-1022 = -0x1p+1023
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x7fdfffff, 0xffffffff), 0x7fdfffff, 0xffffffff, STR(__LINE__)); // 0x0.0000000000001p-1022 + 0x1.fffffffffffffp+1022 = 0x1.fffffffffffffp+1022
}

void f29(void) {
  comp64(double_of_bits(0x7fdfffff, 0xffffffff) + double_of_bits(0x00000000, 0x00000001), 0x7fdfffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1022 + 0x0.0000000000001p-1022 = 0x1.fffffffffffffp+1022
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0xffdfffff, 0xffffffff), 0xffdfffff, 0xffffffff, STR(__LINE__)); // -0x0.0000000000001p-1022 + -0x1.fffffffffffffp+1022 = -0x1.fffffffffffffp+1022
  comp64(double_of_bits(0xffdfffff, 0xffffffff) + double_of_bits(0x80000000, 0x00000001), 0xffdfffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1022 + -0x0.0000000000001p-1022 = -0x1.fffffffffffffp+1022
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x7fefffff, 0xfffffffe), 0x7fefffff, 0xfffffffe, STR(__LINE__)); // 0x0.0000000000001p-1022 + 0x1.ffffffffffffep+1023 = 0x1.ffffffffffffep+1023
  comp64(double_of_bits(0x7fefffff, 0xfffffffe) + double_of_bits(0x00000000, 0x00000001), 0x7fefffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffep+1023 + 0x0.0000000000001p-1022 = 0x1.ffffffffffffep+1023
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0xffefffff, 0xfffffffe), 0xffefffff, 0xfffffffe, STR(__LINE__)); // -0x0.0000000000001p-1022 + -0x1.ffffffffffffep+1023 = -0x1.ffffffffffffep+1023
  comp64(double_of_bits(0xffefffff, 0xfffffffe) + double_of_bits(0x80000000, 0x00000001), 0xffefffff, 0xfffffffe, STR(__LINE__)); // -0x1.ffffffffffffep+1023 + -0x0.0000000000001p-1022 = -0x1.ffffffffffffep+1023
  comp64(double_of_bits(0x7fe00000, 0x00000000) + double_of_bits(0x7ca00000, 0x00000000), 0x7fe00000, 0x00000001, STR(__LINE__)); // 0x1p+1023 + 0x1p+971 = 0x1.0000000000001p+1023
  comp64(double_of_bits(0x7ca00000, 0x00000000) + double_of_bits(0x7fe00000, 0x00000000), 0x7fe00000, 0x00000001, STR(__LINE__)); // 0x1p+971 + 0x1p+1023 = 0x1.0000000000001p+1023
  comp64(double_of_bits(0xffe00000, 0x00000000) + double_of_bits(0xfca00000, 0x00000000), 0xffe00000, 0x00000001, STR(__LINE__)); // -0x1p+1023 + -0x1p+971 = -0x1.0000000000001p+1023
}

void f30(void) {
  comp64(double_of_bits(0xfca00000, 0x00000000) + double_of_bits(0xffe00000, 0x00000000), 0xffe00000, 0x00000001, STR(__LINE__)); // -0x1p+971 + -0x1p+1023 = -0x1.0000000000001p+1023
  comp64(double_of_bits(0x7fdfffff, 0xfffffffe) + double_of_bits(0x7fdfffff, 0xfffffffe), 0x7fefffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffep+1022 + 0x1.ffffffffffffep+1022 = 0x1.ffffffffffffep+1023
  comp64(double_of_bits(0xffdfffff, 0xfffffffe) + double_of_bits(0xffdfffff, 0xfffffffe), 0xffefffff, 0xfffffffe, STR(__LINE__)); // -0x1.ffffffffffffep+1022 + -0x1.ffffffffffffep+1022 = -0x1.ffffffffffffep+1023
  comp64(double_of_bits(0x40080000, 0x00000000) + double_of_bits(0x40080000, 0x00000000), 0x40180000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 + 0x1.8p+1 = 0x1.8p+2
  comp64(double_of_bits(0x00100000, 0x00000000) + double_of_bits(0x00100000, 0x00000000), 0x00200000, 0x00000000, STR(__LINE__)); // 0x1p-1022 + 0x1p-1022 = 0x1p-1021
  comp64(double_of_bits(0x7fd00000, 0x00000000) + double_of_bits(0x7fd00000, 0x00000000), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x1p+1022 + 0x1p+1022 = 0x1p+1023
  comp64(double_of_bits(0x000fffff, 0xffffffff) + double_of_bits(0x000fffff, 0xffffffff), 0x001fffff, 0xfffffffe, STR(__LINE__)); // 0x0.fffffffffffffp-1022 + 0x0.fffffffffffffp-1022 = 0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) + double_of_bits(0x800fffff, 0xffffffff), 0x801fffff, 0xfffffffe, STR(__LINE__)); // -0x0.fffffffffffffp-1022 + -0x0.fffffffffffffp-1022 = -0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x00000000, 0x00000004) + double_of_bits(0x00000000, 0x00000004), 0x00000000, 0x00000008, STR(__LINE__)); // 0x0.0000000000004p-1022 + 0x0.0000000000004p-1022 = 0x0.0000000000008p-1022
  comp64(double_of_bits(0x80000000, 0x00000004) + double_of_bits(0x80000000, 0x00000004), 0x80000000, 0x00000008, STR(__LINE__)); // -0x0.0000000000004p-1022 + -0x0.0000000000004p-1022 = -0x0.0000000000008p-1022
}

void f31(void) {
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000002, STR(__LINE__)); // 0x0.0000000000001p-1022 + 0x0.0000000000001p-1022 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000002, STR(__LINE__)); // -0x0.0000000000001p-1022 + -0x0.0000000000001p-1022 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x40200000, 0x00000000), 0x40220000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1p+3 = 0x1.2p+3
  comp64(double_of_bits(0x40200000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x40220000, 0x00000000, STR(__LINE__)); // 0x1p+3 + 0x1.0000000000001p+0 = 0x1.2p+3
  comp64(double_of_bits(0xbff00000, 0x00000001) + double_of_bits(0xc0200000, 0x00000000), 0xc0220000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+0 + -0x1p+3 = -0x1.2p+3
  comp64(double_of_bits(0xc0200000, 0x00000000) + double_of_bits(0xbff00000, 0x00000001), 0xc0220000, 0x00000000, STR(__LINE__)); // -0x1p+3 + -0x1.0000000000001p+0 = -0x1.2p+3
  comp64(double_of_bits(0x43600000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000000), 0x43600000, 0x00000000, STR(__LINE__)); // 0x1p+55 + 0x1p+0 = 0x1p+55
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x43600000, 0x00000000), 0x43600000, 0x00000000, STR(__LINE__)); // 0x1p+0 + 0x1p+55 = 0x1p+55
  comp64(double_of_bits(0xc3600000, 0x00000000) + double_of_bits(0xbff00000, 0x00000000), 0xc3600000, 0x00000000, STR(__LINE__)); // -0x1p+55 + -0x1p+0 = -0x1p+55
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0xc3600000, 0x00000000), 0xc3600000, 0x00000000, STR(__LINE__)); // -0x1p+0 + -0x1p+55 = -0x1p+55
}

void f32(void) {
  comp64(double_of_bits(0x00400000, 0x00000000) + double_of_bits(0x00000000, 0x00000001), 0x00400000, 0x00000000, STR(__LINE__)); // 0x1p-1019 + 0x0.0000000000001p-1022 = 0x1p-1019
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x00400000, 0x00000000), 0x00400000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 + 0x1p-1019 = 0x1p-1019
  comp64(double_of_bits(0x80400000, 0x00000000) + double_of_bits(0x80000000, 0x00000001), 0x80400000, 0x00000000, STR(__LINE__)); // -0x1p-1019 + -0x0.0000000000001p-1022 = -0x1p-1019
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0x80400000, 0x00000000), 0x80400000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 + -0x1p-1019 = -0x1p-1019
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x3ff00000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 + 0x1p+0 = 0x1p+0
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x00000000, 0x00000001), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x1p+0 + 0x0.0000000000001p-1022 = 0x1p+0
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0xbff00000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 + -0x1p+0 = -0x1p+0
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0x80000000, 0x00000001), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x1p+0 + -0x0.0000000000001p-1022 = -0x1p+0
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x3fefffff, 0xffffffff), 0x3fefffff, 0xffffffff, STR(__LINE__)); // 0x0.0000000000001p-1022 + 0x1.fffffffffffffp-1 = 0x1.fffffffffffffp-1
  comp64(double_of_bits(0x3fefffff, 0xffffffff) + double_of_bits(0x00000000, 0x00000001), 0x3fefffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp-1 + 0x0.0000000000001p-1022 = 0x1.fffffffffffffp-1
}

void f33(void) {
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0xbfefffff, 0xffffffff), 0xbfefffff, 0xffffffff, STR(__LINE__)); // -0x0.0000000000001p-1022 + -0x1.fffffffffffffp-1 = -0x1.fffffffffffffp-1
  comp64(double_of_bits(0xbfefffff, 0xffffffff) + double_of_bits(0x80000000, 0x00000001), 0xbfefffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp-1 + -0x0.0000000000001p-1022 = -0x1.fffffffffffffp-1
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x3fffffff, 0xffffffff), 0x3fffffff, 0xffffffff, STR(__LINE__)); // 0x0.0000000000001p-1022 + 0x1.fffffffffffffp+0 = 0x1.fffffffffffffp+0
  comp64(double_of_bits(0x3fffffff, 0xffffffff) + double_of_bits(0x00000000, 0x00000001), 0x3fffffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+0 + 0x0.0000000000001p-1022 = 0x1.fffffffffffffp+0
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0xbfffffff, 0xffffffff), 0xbfffffff, 0xffffffff, STR(__LINE__)); // -0x0.0000000000001p-1022 + -0x1.fffffffffffffp+0 = -0x1.fffffffffffffp+0
  comp64(double_of_bits(0xbfffffff, 0xffffffff) + double_of_bits(0x80000000, 0x00000001), 0xbfffffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+0 + -0x0.0000000000001p-1022 = -0x1.fffffffffffffp+0
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x3fffffff, 0xfffffffe), 0x3fffffff, 0xfffffffe, STR(__LINE__)); // 0x0.0000000000001p-1022 + 0x1.ffffffffffffep+0 = 0x1.ffffffffffffep+0
  comp64(double_of_bits(0x3fffffff, 0xfffffffe) + double_of_bits(0x00000000, 0x00000001), 0x3fffffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffep+0 + 0x0.0000000000001p-1022 = 0x1.ffffffffffffep+0
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0xbfffffff, 0xfffffffe), 0xbfffffff, 0xfffffffe, STR(__LINE__)); // -0x0.0000000000001p-1022 + -0x1.ffffffffffffep+0 = -0x1.ffffffffffffep+0
  comp64(double_of_bits(0xbfffffff, 0xfffffffe) + double_of_bits(0x80000000, 0x00000001), 0xbfffffff, 0xfffffffe, STR(__LINE__)); // -0x1.ffffffffffffep+0 + -0x0.0000000000001p-1022 = -0x1.ffffffffffffep+0
}

void f34(void) {
  comp64(double_of_bits(0x436fffff, 0xffffffff) + double_of_bits(0x40260000, 0x00000000), 0x43700000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+55 + 0x1.6p+3 = 0x1p+56
  comp64(double_of_bits(0x40260000, 0x00000000) + double_of_bits(0x436fffff, 0xffffffff), 0x43700000, 0x00000000, STR(__LINE__)); // 0x1.6p+3 + 0x1.fffffffffffffp+55 = 0x1p+56
  comp64(double_of_bits(0xc36fffff, 0xffffffff) + double_of_bits(0xc0260000, 0x00000000), 0xc3700000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+55 + -0x1.6p+3 = -0x1p+56
  comp64(double_of_bits(0xc0260000, 0x00000000) + double_of_bits(0xc36fffff, 0xffffffff), 0xc3700000, 0x00000000, STR(__LINE__)); // -0x1.6p+3 + -0x1.fffffffffffffp+55 = -0x1p+56
  comp64(double_of_bits(0x436c0000, 0x00000000) + double_of_bits(0xc01c0000, 0x00000000), 0x436bffff, 0xffffffff, STR(__LINE__)); // 0x1.cp+55 + -0x1.cp+2 = 0x1.bffffffffffffp+55
  comp64(double_of_bits(0xc01c0000, 0x00000000) + double_of_bits(0x436c0000, 0x00000000), 0x436bffff, 0xffffffff, STR(__LINE__)); // -0x1.cp+2 + 0x1.cp+55 = 0x1.bffffffffffffp+55
  comp64(double_of_bits(0x401c0000, 0x00000000) + double_of_bits(0xc36c0000, 0x00000000), 0xc36bffff, 0xffffffff, STR(__LINE__)); // 0x1.cp+2 + -0x1.cp+55 = -0x1.bffffffffffffp+55
  comp64(double_of_bits(0xc36c0000, 0x00000000) + double_of_bits(0x401c0000, 0x00000000), 0xc36bffff, 0xffffffff, STR(__LINE__)); // -0x1.cp+55 + 0x1.cp+2 = -0x1.bffffffffffffp+55
  comp64(double_of_bits(0x00500000, 0x00000000) + double_of_bits(0x80000000, 0x00000007), 0x004fffff, 0xffffffff, STR(__LINE__)); // 0x1p-1018 + -0x0.0000000000007p-1022 = 0x1.fffffffffffffp-1019
  comp64(double_of_bits(0x80000000, 0x00000007) + double_of_bits(0x00500000, 0x00000000), 0x004fffff, 0xffffffff, STR(__LINE__)); // -0x0.0000000000007p-1022 + 0x1p-1018 = 0x1.fffffffffffffp-1019
}

void f35(void) {
  comp64(double_of_bits(0x80500000, 0x00000000) + double_of_bits(0x00000000, 0x00000007), 0x804fffff, 0xffffffff, STR(__LINE__)); // -0x1p-1018 + 0x0.0000000000007p-1022 = -0x1.fffffffffffffp-1019
  comp64(double_of_bits(0x00000000, 0x00000007) + double_of_bits(0x80500000, 0x00000000), 0x804fffff, 0xffffffff, STR(__LINE__)); // 0x0.0000000000007p-1022 + -0x1p-1018 = -0x1.fffffffffffffp-1019
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x40100000, 0x00000000), 0x40140000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1p+2 = 0x1.4p+2
  comp64(double_of_bits(0x40100000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x40140000, 0x00000000, STR(__LINE__)); // 0x1p+2 + 0x1.0000000000001p+0 = 0x1.4p+2
  comp64(double_of_bits(0xbff00000, 0x00000001) + double_of_bits(0xc0100000, 0x00000000), 0xc0140000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+0 + -0x1p+2 = -0x1.4p+2
  comp64(double_of_bits(0xc0100000, 0x00000000) + double_of_bits(0xbff00000, 0x00000001), 0xc0140000, 0x00000000, STR(__LINE__)); // -0x1p+2 + -0x1.0000000000001p+0 = -0x1.4p+2
  comp64(double_of_bits(0x43500000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000000), 0x43500000, 0x00000000, STR(__LINE__)); // 0x1p+54 + 0x1p+0 = 0x1p+54
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x43500000, 0x00000000), 0x43500000, 0x00000000, STR(__LINE__)); // 0x1p+0 + 0x1p+54 = 0x1p+54
  comp64(double_of_bits(0xc3500000, 0x00000000) + double_of_bits(0xbff00000, 0x00000000), 0xc3500000, 0x00000000, STR(__LINE__)); // -0x1p+54 + -0x1p+0 = -0x1p+54
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0xc3500000, 0x00000000), 0xc3500000, 0x00000000, STR(__LINE__)); // -0x1p+0 + -0x1p+54 = -0x1p+54
}

void f36(void) {
  comp64(double_of_bits(0x40240000, 0x00000000) + double_of_bits(0x436fffff, 0xffffffff), 0x43700000, 0x00000000, STR(__LINE__)); // 0x1.4p+3 + 0x1.fffffffffffffp+55 = 0x1p+56
  comp64(double_of_bits(0x436fffff, 0xffffffff) + double_of_bits(0x40240000, 0x00000000), 0x43700000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+55 + 0x1.4p+3 = 0x1p+56
  comp64(double_of_bits(0xc0240000, 0x00000000) + double_of_bits(0xc36fffff, 0xffffffff), 0xc3700000, 0x00000000, STR(__LINE__)); // -0x1.4p+3 + -0x1.fffffffffffffp+55 = -0x1p+56
  comp64(double_of_bits(0xc36fffff, 0xffffffff) + double_of_bits(0xc0240000, 0x00000000), 0xc3700000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+55 + -0x1.4p+3 = -0x1p+56
  comp64(double_of_bits(0x40100000, 0x00000000) + double_of_bits(0xbcb80000, 0x00000000), 0x400fffff, 0xffffffff, STR(__LINE__)); // 0x1p+2 + -0x1.8p-52 = 0x1.fffffffffffffp+1
  comp64(double_of_bits(0xbcb80000, 0x00000000) + double_of_bits(0x40100000, 0x00000000), 0x400fffff, 0xffffffff, STR(__LINE__)); // -0x1.8p-52 + 0x1p+2 = 0x1.fffffffffffffp+1
  comp64(double_of_bits(0x40080000, 0x00000000) + double_of_bits(0xc3600000, 0x00000000), 0xc35fffff, 0xffffffff, STR(__LINE__)); // 0x1.8p+1 + -0x1p+55 = -0x1.fffffffffffffp+54
  comp64(double_of_bits(0xc3600000, 0x00000000) + double_of_bits(0x40080000, 0x00000000), 0xc35fffff, 0xffffffff, STR(__LINE__)); // -0x1p+55 + 0x1.8p+1 = -0x1.fffffffffffffp+54
  comp64(double_of_bits(0xc0100000, 0x00000000) + double_of_bits(0x3cb80000, 0x00000000), 0xc00fffff, 0xffffffff, STR(__LINE__)); // -0x1p+2 + 0x1.8p-52 = -0x1.fffffffffffffp+1
  comp64(double_of_bits(0x3cb80000, 0x00000000) + double_of_bits(0xc0100000, 0x00000000), 0xc00fffff, 0xffffffff, STR(__LINE__)); // 0x1.8p-52 + -0x1p+2 = -0x1.fffffffffffffp+1
}

void f37(void) {
  comp64(double_of_bits(0xc0080000, 0x00000000) + double_of_bits(0x43600000, 0x00000000), 0x435fffff, 0xffffffff, STR(__LINE__)); // -0x1.8p+1 + 0x1p+55 = 0x1.fffffffffffffp+54
  comp64(double_of_bits(0x43600000, 0x00000000) + double_of_bits(0xc0080000, 0x00000000), 0x435fffff, 0xffffffff, STR(__LINE__)); // 0x1p+55 + -0x1.8p+1 = 0x1.fffffffffffffp+54
  comp64(double_of_bits(0x00400000, 0x00000000) + double_of_bits(0x80000000, 0x00000003), 0x003fffff, 0xffffffff, STR(__LINE__)); // 0x1p-1019 + -0x0.0000000000003p-1022 = 0x1.fffffffffffffp-1020
  comp64(double_of_bits(0x80000000, 0x00000003) + double_of_bits(0x00400000, 0x00000000), 0x003fffff, 0xffffffff, STR(__LINE__)); // -0x0.0000000000003p-1022 + 0x1p-1019 = 0x1.fffffffffffffp-1020
  comp64(double_of_bits(0x80400000, 0x00000000) + double_of_bits(0x00000000, 0x00000003), 0x803fffff, 0xffffffff, STR(__LINE__)); // -0x1p-1019 + 0x0.0000000000003p-1022 = -0x1.fffffffffffffp-1020
  comp64(double_of_bits(0x00000000, 0x00000003) + double_of_bits(0x80400000, 0x00000000), 0x803fffff, 0xffffffff, STR(__LINE__)); // 0x0.0000000000003p-1022 + -0x1p-1019 = -0x1.fffffffffffffp-1020
  comp64(double_of_bits(0x3ff00000, 0x00000003) + double_of_bits(0x40200000, 0x00000000), 0x40220000, 0x00000000, STR(__LINE__)); // 0x1.0000000000003p+0 + 0x1p+3 = 0x1.2p+3
  comp64(double_of_bits(0x40200000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000003), 0x40220000, 0x00000000, STR(__LINE__)); // 0x1p+3 + 0x1.0000000000003p+0 = 0x1.2p+3
  comp64(double_of_bits(0xbff00000, 0x00000003) + double_of_bits(0xc0200000, 0x00000000), 0xc0220000, 0x00000000, STR(__LINE__)); // -0x1.0000000000003p+0 + -0x1p+3 = -0x1.2p+3
  comp64(double_of_bits(0xc0200000, 0x00000000) + double_of_bits(0xbff00000, 0x00000003), 0xc0220000, 0x00000000, STR(__LINE__)); // -0x1p+3 + -0x1.0000000000003p+0 = -0x1.2p+3
}

void f38(void) {
  comp64(double_of_bits(0x400fffff, 0xffffffff) + double_of_bits(0x3cafffff, 0xffffffff), 0x400fffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1 + 0x1.fffffffffffffp-53 = 0x1.fffffffffffffp+1
  comp64(double_of_bits(0x3cafffff, 0xffffffff) + double_of_bits(0x400fffff, 0xffffffff), 0x400fffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp-53 + 0x1.fffffffffffffp+1 = 0x1.fffffffffffffp+1
  comp64(double_of_bits(0xc00fffff, 0xffffffff) + double_of_bits(0xbcafffff, 0xffffffff), 0xc00fffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1 + -0x1.fffffffffffffp-53 = -0x1.fffffffffffffp+1
  comp64(double_of_bits(0xbcafffff, 0xffffffff) + double_of_bits(0xc00fffff, 0xffffffff), 0xc00fffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp-53 + -0x1.fffffffffffffp+1 = -0x1.fffffffffffffp+1
  comp64(double_of_bits(0x00400000, 0x00000000) + double_of_bits(0x00000000, 0x00000003), 0x00400000, 0x00000000, STR(__LINE__)); // 0x1p-1019 + 0x0.0000000000003p-1022 = 0x1p-1019
  comp64(double_of_bits(0x00000000, 0x00000003) + double_of_bits(0x00400000, 0x00000000), 0x00400000, 0x00000000, STR(__LINE__)); // 0x0.0000000000003p-1022 + 0x1p-1019 = 0x1p-1019
  comp64(double_of_bits(0x80000000, 0x00000003) + double_of_bits(0x80400000, 0x00000000), 0x80400000, 0x00000000, STR(__LINE__)); // -0x0.0000000000003p-1022 + -0x1p-1019 = -0x1p-1019
  comp64(double_of_bits(0x80400000, 0x00000000) + double_of_bits(0x80000000, 0x00000003), 0x80400000, 0x00000000, STR(__LINE__)); // -0x1p-1019 + -0x0.0000000000003p-1022 = -0x1p-1019
  comp64(double_of_bits(0x402c0000, 0x00000000) + double_of_bits(0x436fffff, 0xffffffff), 0x43700000, 0x00000000, STR(__LINE__)); // 0x1.cp+3 + 0x1.fffffffffffffp+55 = 0x1p+56
  comp64(double_of_bits(0x436fffff, 0xffffffff) + double_of_bits(0x402c0000, 0x00000000), 0x43700000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+55 + 0x1.cp+3 = 0x1p+56
}

void f39(void) {
  comp64(double_of_bits(0xc02c0000, 0x00000000) + double_of_bits(0xc36fffff, 0xffffffff), 0xc3700000, 0x00000000, STR(__LINE__)); // -0x1.cp+3 + -0x1.fffffffffffffp+55 = -0x1p+56
  comp64(double_of_bits(0xc36fffff, 0xffffffff) + double_of_bits(0xc02c0000, 0x00000000), 0xc3700000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+55 + -0x1.cp+3 = -0x1p+56
  comp64(double_of_bits(0x40200000, 0x00000000) + double_of_bits(0xbcc40000, 0x00000000), 0x401fffff, 0xffffffff, STR(__LINE__)); // 0x1p+3 + -0x1.4p-51 = 0x1.fffffffffffffp+2
  comp64(double_of_bits(0xbcc40000, 0x00000000) + double_of_bits(0x40200000, 0x00000000), 0x401fffff, 0xffffffff, STR(__LINE__)); // -0x1.4p-51 + 0x1p+3 = 0x1.fffffffffffffp+2
  comp64(double_of_bits(0x40140000, 0x00000000) + double_of_bits(0xc3700000, 0x00000000), 0xc36fffff, 0xffffffff, STR(__LINE__)); // 0x1.4p+2 + -0x1p+56 = -0x1.fffffffffffffp+55
  comp64(double_of_bits(0xc3700000, 0x00000000) + double_of_bits(0x40140000, 0x00000000), 0xc36fffff, 0xffffffff, STR(__LINE__)); // -0x1p+56 + 0x1.4p+2 = -0x1.fffffffffffffp+55
  comp64(double_of_bits(0xc0200000, 0x00000000) + double_of_bits(0x3cc40000, 0x00000000), 0xc01fffff, 0xffffffff, STR(__LINE__)); // -0x1p+3 + 0x1.4p-51 = -0x1.fffffffffffffp+2
  comp64(double_of_bits(0x3cc40000, 0x00000000) + double_of_bits(0xc0200000, 0x00000000), 0xc01fffff, 0xffffffff, STR(__LINE__)); // 0x1.4p-51 + -0x1p+3 = -0x1.fffffffffffffp+2
  comp64(double_of_bits(0xc0140000, 0x00000000) + double_of_bits(0x43700000, 0x00000000), 0x436fffff, 0xffffffff, STR(__LINE__)); // -0x1.4p+2 + 0x1p+56 = 0x1.fffffffffffffp+55
  comp64(double_of_bits(0x43700000, 0x00000000) + double_of_bits(0xc0140000, 0x00000000), 0x436fffff, 0xffffffff, STR(__LINE__)); // 0x1p+56 + -0x1.4p+2 = 0x1.fffffffffffffp+55
}

void f40(void) {
  comp64(double_of_bits(0x00500000, 0x00000000) + double_of_bits(0x80000000, 0x00000005), 0x004fffff, 0xffffffff, STR(__LINE__)); // 0x1p-1018 + -0x0.0000000000005p-1022 = 0x1.fffffffffffffp-1019
  comp64(double_of_bits(0x80000000, 0x00000005) + double_of_bits(0x00500000, 0x00000000), 0x004fffff, 0xffffffff, STR(__LINE__)); // -0x0.0000000000005p-1022 + 0x1p-1018 = 0x1.fffffffffffffp-1019
  comp64(double_of_bits(0x80500000, 0x00000000) + double_of_bits(0x00000000, 0x00000005), 0x804fffff, 0xffffffff, STR(__LINE__)); // -0x1p-1018 + 0x0.0000000000005p-1022 = -0x1.fffffffffffffp-1019
  comp64(double_of_bits(0x00000000, 0x00000005) + double_of_bits(0x80500000, 0x00000000), 0x804fffff, 0xffffffff, STR(__LINE__)); // 0x0.0000000000005p-1022 + -0x1p-1018 = -0x1.fffffffffffffp-1019
  comp64(double_of_bits(0x3cb00000, 0x00000000) + double_of_bits(0x40000000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // 0x1p-52 + 0x1p+1 = 0x1p+1
  comp64(double_of_bits(0x40000000, 0x00000000) + double_of_bits(0x3cb00000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // 0x1p+1 + 0x1p-52 = 0x1p+1
  comp64(double_of_bits(0xbcb00000, 0x00000000) + double_of_bits(0xc0000000, 0x00000000), 0xc0000000, 0x00000000, STR(__LINE__)); // -0x1p-52 + -0x1p+1 = -0x1p+1
  comp64(double_of_bits(0xc0000000, 0x00000000) + double_of_bits(0xbcb00000, 0x00000000), 0xc0000000, 0x00000000, STR(__LINE__)); // -0x1p+1 + -0x1p-52 = -0x1p+1
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x00200000, 0x00000000), 0x00200000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 + 0x1p-1021 = 0x1p-1021
  comp64(double_of_bits(0x00200000, 0x00000000) + double_of_bits(0x00000000, 0x00000001), 0x00200000, 0x00000000, STR(__LINE__)); // 0x1p-1021 + 0x0.0000000000001p-1022 = 0x1p-1021
}

void f41(void) {
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0x80200000, 0x00000000), 0x80200000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 + -0x1p-1021 = -0x1p-1021
  comp64(double_of_bits(0x80200000, 0x00000000) + double_of_bits(0x80000000, 0x00000001), 0x80200000, 0x00000000, STR(__LINE__)); // -0x1p-1021 + -0x0.0000000000001p-1022 = -0x1p-1021
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x3ff00000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1p+0 = 0x1p+1
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x40000000, 0x00000000, STR(__LINE__)); // 0x1p+0 + 0x1.0000000000001p+0 = 0x1p+1
  comp64(double_of_bits(0xbff00000, 0x00000001) + double_of_bits(0xbff00000, 0x00000000), 0xc0000000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+0 + -0x1p+0 = -0x1p+1
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0xbff00000, 0x00000001), 0xc0000000, 0x00000000, STR(__LINE__)); // -0x1p+0 + -0x1.0000000000001p+0 = -0x1p+1
  comp64(double_of_bits(0x7fd00000, 0x00000001) + double_of_bits(0x7fd00000, 0x00000000), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+1022 + 0x1p+1022 = 0x1p+1023
  comp64(double_of_bits(0x7fd00000, 0x00000000) + double_of_bits(0x7fd00000, 0x00000001), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x1p+1022 + 0x1.0000000000001p+1022 = 0x1p+1023
  comp64(double_of_bits(0x40000000, 0x00000000) + double_of_bits(0x40000000, 0x00000001), 0x40100000, 0x00000000, STR(__LINE__)); // 0x1p+1 + 0x1.0000000000001p+1 = 0x1p+2
  comp64(double_of_bits(0x40000000, 0x00000001) + double_of_bits(0x40000000, 0x00000000), 0x40100000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+1 + 0x1p+1 = 0x1p+2
}

void f42(void) {
  comp64(double_of_bits(0x7fdfffff, 0xfffffffe) + double_of_bits(0x7fdfffff, 0xffffffff), 0x7fefffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffep+1022 + 0x1.fffffffffffffp+1022 = 0x1.ffffffffffffep+1023
  comp64(double_of_bits(0x7fdfffff, 0xffffffff) + double_of_bits(0x7fdfffff, 0xfffffffe), 0x7fefffff, 0xfffffffe, STR(__LINE__)); // 0x1.fffffffffffffp+1022 + 0x1.ffffffffffffep+1022 = 0x1.ffffffffffffep+1023
  comp64(double_of_bits(0xffd00000, 0x00000001) + double_of_bits(0xffd00000, 0x00000000), 0xffe00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+1022 + -0x1p+1022 = -0x1p+1023
  comp64(double_of_bits(0xffd00000, 0x00000000) + double_of_bits(0xffd00000, 0x00000001), 0xffe00000, 0x00000000, STR(__LINE__)); // -0x1p+1022 + -0x1.0000000000001p+1022 = -0x1p+1023
  comp64(double_of_bits(0xc0000000, 0x00000000) + double_of_bits(0xc0000000, 0x00000001), 0xc0100000, 0x00000000, STR(__LINE__)); // -0x1p+1 + -0x1.0000000000001p+1 = -0x1p+2
  comp64(double_of_bits(0xc0000000, 0x00000001) + double_of_bits(0xc0000000, 0x00000000), 0xc0100000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+1 + -0x1p+1 = -0x1p+2
  comp64(double_of_bits(0xffdfffff, 0xfffffffe) + double_of_bits(0xffdfffff, 0xffffffff), 0xffefffff, 0xfffffffe, STR(__LINE__)); // -0x1.ffffffffffffep+1022 + -0x1.fffffffffffffp+1022 = -0x1.ffffffffffffep+1023
  comp64(double_of_bits(0xffdfffff, 0xffffffff) + double_of_bits(0xffdfffff, 0xfffffffe), 0xffefffff, 0xfffffffe, STR(__LINE__)); // -0x1.fffffffffffffp+1022 + -0x1.ffffffffffffep+1022 = -0x1.ffffffffffffep+1023
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0xbca00000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + -0x1p-53 = 0x1p+0
  comp64(double_of_bits(0xbca00000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x3ff00000, 0x00000000, STR(__LINE__)); // -0x1p-53 + 0x1.0000000000001p+0 = 0x1p+0
}

void f43(void) {
  comp64(double_of_bits(0x3ca00000, 0x00000000) + double_of_bits(0xbff00000, 0x00000001), 0xbff00000, 0x00000000, STR(__LINE__)); // 0x1p-53 + -0x1.0000000000001p+0 = -0x1p+0
  comp64(double_of_bits(0xbff00000, 0x00000001) + double_of_bits(0x3ca00000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+0 + 0x1p-53 = -0x1p+0
  comp64(double_of_bits(0x00200000, 0x00000001) + double_of_bits(0x80000000, 0x00000001), 0x00200000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p-1021 + -0x0.0000000000001p-1022 = 0x1p-1021
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0x00200000, 0x00000001), 0x00200000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 + 0x1.0000000000001p-1021 = 0x1p-1021
  comp64(double_of_bits(0x80200000, 0x00000001) + double_of_bits(0x00000000, 0x00000001), 0x80200000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p-1021 + 0x0.0000000000001p-1022 = -0x1p-1021
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x80200000, 0x00000001), 0x80200000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 + -0x1.0000000000001p-1021 = -0x1p-1021
  comp64(double_of_bits(0x3cb00000, 0x00000000) + double_of_bits(0x400fffff, 0xffffffff), 0x40100000, 0x00000000, STR(__LINE__)); // 0x1p-52 + 0x1.fffffffffffffp+1 = 0x1p+2
  comp64(double_of_bits(0x400fffff, 0xffffffff) + double_of_bits(0x3cb00000, 0x00000000), 0x40100000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1 + 0x1p-52 = 0x1p+2
  comp64(double_of_bits(0xbcb00000, 0x00000000) + double_of_bits(0xc00fffff, 0xffffffff), 0xc0100000, 0x00000000, STR(__LINE__)); // -0x1p-52 + -0x1.fffffffffffffp+1 = -0x1p+2
  comp64(double_of_bits(0xc00fffff, 0xffffffff) + double_of_bits(0xbcb00000, 0x00000000), 0xc0100000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1 + -0x1p-52 = -0x1p+2
}

void f44(void) {
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x00200000, 0x00000001), 0x00200000, 0x00000002, STR(__LINE__)); // 0x0.0000000000001p-1022 + 0x1.0000000000001p-1021 = 0x1.0000000000002p-1021
  comp64(double_of_bits(0x00200000, 0x00000001) + double_of_bits(0x00000000, 0x00000001), 0x00200000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p-1021 + 0x0.0000000000001p-1022 = 0x1.0000000000002p-1021
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0x80200000, 0x00000001), 0x80200000, 0x00000002, STR(__LINE__)); // -0x0.0000000000001p-1022 + -0x1.0000000000001p-1021 = -0x1.0000000000002p-1021
  comp64(double_of_bits(0x80200000, 0x00000001) + double_of_bits(0x80000000, 0x00000001), 0x80200000, 0x00000002, STR(__LINE__)); // -0x1.0000000000001p-1021 + -0x0.0000000000001p-1022 = -0x1.0000000000002p-1021
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000003), 0x40000000, 0x00000002, STR(__LINE__)); // 0x1p+0 + 0x1.0000000000003p+0 = 0x1.0000000000002p+1
  comp64(double_of_bits(0x3ff00000, 0x00000003) + double_of_bits(0x3ff00000, 0x00000000), 0x40000000, 0x00000002, STR(__LINE__)); // 0x1.0000000000003p+0 + 0x1p+0 = 0x1.0000000000002p+1
  comp64(double_of_bits(0x40000000, 0x00000001) + double_of_bits(0x40000000, 0x00000002), 0x40100000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+1 + 0x1.0000000000002p+1 = 0x1.0000000000002p+2
  comp64(double_of_bits(0x40000000, 0x00000002) + double_of_bits(0x40000000, 0x00000001), 0x40100000, 0x00000002, STR(__LINE__)); // 0x1.0000000000002p+1 + 0x1.0000000000001p+1 = 0x1.0000000000002p+2
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0xbff00000, 0x00000003), 0xc0000000, 0x00000002, STR(__LINE__)); // -0x1p+0 + -0x1.0000000000003p+0 = -0x1.0000000000002p+1
  comp64(double_of_bits(0xbff00000, 0x00000003) + double_of_bits(0xbff00000, 0x00000000), 0xc0000000, 0x00000002, STR(__LINE__)); // -0x1.0000000000003p+0 + -0x1p+0 = -0x1.0000000000002p+1
}

void f45(void) {
  comp64(double_of_bits(0xc0000000, 0x00000001) + double_of_bits(0xc0000000, 0x00000002), 0xc0100000, 0x00000002, STR(__LINE__)); // -0x1.0000000000001p+1 + -0x1.0000000000002p+1 = -0x1.0000000000002p+2
  comp64(double_of_bits(0xc0000000, 0x00000002) + double_of_bits(0xc0000000, 0x00000001), 0xc0100000, 0x00000002, STR(__LINE__)); // -0x1.0000000000002p+1 + -0x1.0000000000001p+1 = -0x1.0000000000002p+2
  comp64(double_of_bits(0x3cb00000, 0x00000000) + double_of_bits(0x40000000, 0x00000001), 0x40000000, 0x00000002, STR(__LINE__)); // 0x1p-52 + 0x1.0000000000001p+1 = 0x1.0000000000002p+1
  comp64(double_of_bits(0x40000000, 0x00000001) + double_of_bits(0x3cb00000, 0x00000000), 0x40000000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+1 + 0x1p-52 = 0x1.0000000000002p+1
  comp64(double_of_bits(0xbcb00000, 0x00000000) + double_of_bits(0xc0000000, 0x00000001), 0xc0000000, 0x00000002, STR(__LINE__)); // -0x1p-52 + -0x1.0000000000001p+1 = -0x1.0000000000002p+1
  comp64(double_of_bits(0xc0000000, 0x00000001) + double_of_bits(0xbcb00000, 0x00000000), 0xc0000000, 0x00000002, STR(__LINE__)); // -0x1.0000000000001p+1 + -0x1p-52 = -0x1.0000000000002p+1
  comp64(double_of_bits(0x40000000, 0x00000002) + double_of_bits(0xbcb00000, 0x00000000), 0x40000000, 0x00000002, STR(__LINE__)); // 0x1.0000000000002p+1 + -0x1p-52 = 0x1.0000000000002p+1
  comp64(double_of_bits(0xbcb00000, 0x00000000) + double_of_bits(0x40000000, 0x00000002), 0x40000000, 0x00000002, STR(__LINE__)); // -0x1p-52 + 0x1.0000000000002p+1 = 0x1.0000000000002p+1
  comp64(double_of_bits(0x3cb00000, 0x00000000) + double_of_bits(0xc0000000, 0x00000002), 0xc0000000, 0x00000002, STR(__LINE__)); // 0x1p-52 + -0x1.0000000000002p+1 = -0x1.0000000000002p+1
  comp64(double_of_bits(0xc0000000, 0x00000002) + double_of_bits(0x3cb00000, 0x00000000), 0xc0000000, 0x00000002, STR(__LINE__)); // -0x1.0000000000002p+1 + 0x1p-52 = -0x1.0000000000002p+1
}

void f46(void) {
  comp64(double_of_bits(0x00300000, 0x00000002) + double_of_bits(0x80000000, 0x00000001), 0x00300000, 0x00000002, STR(__LINE__)); // 0x1.0000000000002p-1020 + -0x0.0000000000001p-1022 = 0x1.0000000000002p-1020
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0x00300000, 0x00000002), 0x00300000, 0x00000002, STR(__LINE__)); // -0x0.0000000000001p-1022 + 0x1.0000000000002p-1020 = 0x1.0000000000002p-1020
  comp64(double_of_bits(0x80300000, 0x00000002) + double_of_bits(0x00000000, 0x00000001), 0x80300000, 0x00000002, STR(__LINE__)); // -0x1.0000000000002p-1020 + 0x0.0000000000001p-1022 = -0x1.0000000000002p-1020
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x80300000, 0x00000002), 0x80300000, 0x00000002, STR(__LINE__)); // 0x0.0000000000001p-1022 + -0x1.0000000000002p-1020 = -0x1.0000000000002p-1020
  comp64(double_of_bits(0x3ff00000, 0x00000003) + double_of_bits(0x40100000, 0x00000000), 0x40140000, 0x00000001, STR(__LINE__)); // 0x1.0000000000003p+0 + 0x1p+2 = 0x1.4000000000001p+2
  comp64(double_of_bits(0x40100000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000003), 0x40140000, 0x00000001, STR(__LINE__)); // 0x1p+2 + 0x1.0000000000003p+0 = 0x1.4000000000001p+2
  comp64(double_of_bits(0xbff00000, 0x00000003) + double_of_bits(0xc0100000, 0x00000000), 0xc0140000, 0x00000001, STR(__LINE__)); // -0x1.0000000000003p+0 + -0x1p+2 = -0x1.4000000000001p+2
  comp64(double_of_bits(0xc0100000, 0x00000000) + double_of_bits(0xbff00000, 0x00000003), 0xc0140000, 0x00000001, STR(__LINE__)); // -0x1p+2 + -0x1.0000000000003p+0 = -0x1.4000000000001p+2
  comp64(double_of_bits(0x40080000, 0x00000000) + double_of_bits(0x43580000, 0x00000000), 0x43580000, 0x00000001, STR(__LINE__)); // 0x1.8p+1 + 0x1.8p+54 = 0x1.8000000000001p+54
  comp64(double_of_bits(0x43580000, 0x00000000) + double_of_bits(0x40080000, 0x00000000), 0x43580000, 0x00000001, STR(__LINE__)); // 0x1.8p+54 + 0x1.8p+1 = 0x1.8000000000001p+54
}

void f47(void) {
  comp64(double_of_bits(0xc0080000, 0x00000000) + double_of_bits(0xc3580000, 0x00000000), 0xc3580000, 0x00000001, STR(__LINE__)); // -0x1.8p+1 + -0x1.8p+54 = -0x1.8000000000001p+54
  comp64(double_of_bits(0xc3580000, 0x00000000) + double_of_bits(0xc0080000, 0x00000000), 0xc3580000, 0x00000001, STR(__LINE__)); // -0x1.8p+54 + -0x1.8p+1 = -0x1.8000000000001p+54
  comp64(double_of_bits(0x00000000, 0x00000003) + double_of_bits(0x00300000, 0x00000000), 0x00300000, 0x00000001, STR(__LINE__)); // 0x0.0000000000003p-1022 + 0x1p-1020 = 0x1.0000000000001p-1020
  comp64(double_of_bits(0x00300000, 0x00000000) + double_of_bits(0x00000000, 0x00000003), 0x00300000, 0x00000001, STR(__LINE__)); // 0x1p-1020 + 0x0.0000000000003p-1022 = 0x1.0000000000001p-1020
  comp64(double_of_bits(0x80000000, 0x00000003) + double_of_bits(0x80300000, 0x00000000), 0x80300000, 0x00000001, STR(__LINE__)); // -0x0.0000000000003p-1022 + -0x1p-1020 = -0x1.0000000000001p-1020
  comp64(double_of_bits(0x80300000, 0x00000000) + double_of_bits(0x80000000, 0x00000003), 0x80300000, 0x00000001, STR(__LINE__)); // -0x1p-1020 + -0x0.0000000000003p-1022 = -0x1.0000000000001p-1020
  comp64(double_of_bits(0x3fffffff, 0xffffffff) + double_of_bits(0x3cc40000, 0x00000000), 0x40000000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp+0 + 0x1.4p-51 = 0x1.0000000000001p+1
  comp64(double_of_bits(0x3cc40000, 0x00000000) + double_of_bits(0x3fffffff, 0xffffffff), 0x40000000, 0x00000001, STR(__LINE__)); // 0x1.4p-51 + 0x1.fffffffffffffp+0 = 0x1.0000000000001p+1
  comp64(double_of_bits(0xbfffffff, 0xffffffff) + double_of_bits(0xbcc40000, 0x00000000), 0xc0000000, 0x00000001, STR(__LINE__)); // -0x1.fffffffffffffp+0 + -0x1.4p-51 = -0x1.0000000000001p+1
  comp64(double_of_bits(0xbcc40000, 0x00000000) + double_of_bits(0xbfffffff, 0xffffffff), 0xc0000000, 0x00000001, STR(__LINE__)); // -0x1.4p-51 + -0x1.fffffffffffffp+0 = -0x1.0000000000001p+1
}

void f48(void) {
  comp64(double_of_bits(0x43600000, 0x00000000) + double_of_bits(0xbff00000, 0x00000000), 0x43600000, 0x00000000, STR(__LINE__)); // 0x1p+55 + -0x1p+0 = 0x1p+55
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0x43600000, 0x00000000), 0x43600000, 0x00000000, STR(__LINE__)); // -0x1p+0 + 0x1p+55 = 0x1p+55
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0xc3600000, 0x00000000), 0xc3600000, 0x00000000, STR(__LINE__)); // 0x1p+0 + -0x1p+55 = -0x1p+55
  comp64(double_of_bits(0xc3600000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000000), 0xc3600000, 0x00000000, STR(__LINE__)); // -0x1p+55 + 0x1p+0 = -0x1p+55
  comp64(double_of_bits(0x00400000, 0x00000000) + double_of_bits(0x80000000, 0x00000001), 0x00400000, 0x00000000, STR(__LINE__)); // 0x1p-1019 + -0x0.0000000000001p-1022 = 0x1p-1019
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0x00400000, 0x00000000), 0x00400000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 + 0x1p-1019 = 0x1p-1019
  comp64(double_of_bits(0x80400000, 0x00000000) + double_of_bits(0x00000000, 0x00000001), 0x80400000, 0x00000000, STR(__LINE__)); // -0x1p-1019 + 0x0.0000000000001p-1022 = -0x1p-1019
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x80400000, 0x00000000), 0x80400000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 + -0x1p-1019 = -0x1p-1019
  comp64(double_of_bits(0x3ff00000, 0x00000005) + double_of_bits(0x40200000, 0x00000000), 0x40220000, 0x00000001, STR(__LINE__)); // 0x1.0000000000005p+0 + 0x1p+3 = 0x1.2000000000001p+3
  comp64(double_of_bits(0x40200000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000005), 0x40220000, 0x00000001, STR(__LINE__)); // 0x1p+3 + 0x1.0000000000005p+0 = 0x1.2000000000001p+3
}

void f49(void) {
  comp64(double_of_bits(0xbff00000, 0x00000005) + double_of_bits(0xc0200000, 0x00000000), 0xc0220000, 0x00000001, STR(__LINE__)); // -0x1.0000000000005p+0 + -0x1p+3 = -0x1.2000000000001p+3
  comp64(double_of_bits(0xc0200000, 0x00000000) + double_of_bits(0xbff00000, 0x00000005), 0xc0220000, 0x00000001, STR(__LINE__)); // -0x1p+3 + -0x1.0000000000005p+0 = -0x1.2000000000001p+3
  comp64(double_of_bits(0x40140000, 0x00000000) + double_of_bits(0x43600000, 0x00000000), 0x43600000, 0x00000001, STR(__LINE__)); // 0x1.4p+2 + 0x1p+55 = 0x1.0000000000001p+55
  comp64(double_of_bits(0x43600000, 0x00000000) + double_of_bits(0x40140000, 0x00000000), 0x43600000, 0x00000001, STR(__LINE__)); // 0x1p+55 + 0x1.4p+2 = 0x1.0000000000001p+55
  comp64(double_of_bits(0xc0140000, 0x00000000) + double_of_bits(0xc3600000, 0x00000000), 0xc3600000, 0x00000001, STR(__LINE__)); // -0x1.4p+2 + -0x1p+55 = -0x1.0000000000001p+55
  comp64(double_of_bits(0xc3600000, 0x00000000) + double_of_bits(0xc0140000, 0x00000000), 0xc3600000, 0x00000001, STR(__LINE__)); // -0x1p+55 + -0x1.4p+2 = -0x1.0000000000001p+55
  comp64(double_of_bits(0x00000000, 0x00000005) + double_of_bits(0x00400000, 0x00000000), 0x00400000, 0x00000001, STR(__LINE__)); // 0x0.0000000000005p-1022 + 0x1p-1019 = 0x1.0000000000001p-1019
  comp64(double_of_bits(0x00400000, 0x00000000) + double_of_bits(0x00000000, 0x00000005), 0x00400000, 0x00000001, STR(__LINE__)); // 0x1p-1019 + 0x0.0000000000005p-1022 = 0x1.0000000000001p-1019
  comp64(double_of_bits(0x80000000, 0x00000005) + double_of_bits(0x80400000, 0x00000000), 0x80400000, 0x00000001, STR(__LINE__)); // -0x0.0000000000005p-1022 + -0x1p-1019 = -0x1.0000000000001p-1019
  comp64(double_of_bits(0x80400000, 0x00000000) + double_of_bits(0x80000000, 0x00000005), 0x80400000, 0x00000001, STR(__LINE__)); // -0x1p-1019 + -0x0.0000000000005p-1022 = -0x1.0000000000001p-1019
}

void f50(void) {
  comp64(double_of_bits(0x3fffffff, 0xffffffff) + double_of_bits(0x3cc00000, 0x00000001), 0x40000000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp+0 + 0x1.0000000000001p-51 = 0x1.0000000000001p+1
  comp64(double_of_bits(0x3cc00000, 0x00000001) + double_of_bits(0x3fffffff, 0xffffffff), 0x40000000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p-51 + 0x1.fffffffffffffp+0 = 0x1.0000000000001p+1
  comp64(double_of_bits(0xbfffffff, 0xffffffff) + double_of_bits(0xbcc00000, 0x00000001), 0xc0000000, 0x00000001, STR(__LINE__)); // -0x1.fffffffffffffp+0 + -0x1.0000000000001p-51 = -0x1.0000000000001p+1
  comp64(double_of_bits(0xbcc00000, 0x00000001) + double_of_bits(0xbfffffff, 0xffffffff), 0xc0000000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p-51 + -0x1.fffffffffffffp+0 = -0x1.0000000000001p+1
  comp64(double_of_bits(0x43780000, 0x00000000) + double_of_bits(0xc0080000, 0x00000000), 0x43780000, 0x00000000, STR(__LINE__)); // 0x1.8p+56 + -0x1.8p+1 = 0x1.8p+56
  comp64(double_of_bits(0xc0080000, 0x00000000) + double_of_bits(0x43780000, 0x00000000), 0x43780000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 + 0x1.8p+56 = 0x1.8p+56
  comp64(double_of_bits(0x40080000, 0x00000000) + double_of_bits(0xc3780000, 0x00000000), 0xc3780000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 + -0x1.8p+56 = -0x1.8p+56
  comp64(double_of_bits(0xc3780000, 0x00000000) + double_of_bits(0x40080000, 0x00000000), 0xc3780000, 0x00000000, STR(__LINE__)); // -0x1.8p+56 + 0x1.8p+1 = -0x1.8p+56
  comp64(double_of_bits(0x00500000, 0x00000000) + double_of_bits(0x80000000, 0x00000003), 0x00500000, 0x00000000, STR(__LINE__)); // 0x1p-1018 + -0x0.0000000000003p-1022 = 0x1p-1018
  comp64(double_of_bits(0x80000000, 0x00000003) + double_of_bits(0x00500000, 0x00000000), 0x00500000, 0x00000000, STR(__LINE__)); // -0x0.0000000000003p-1022 + 0x1p-1018 = 0x1p-1018
}

void f51(void) {
  comp64(double_of_bits(0x80500000, 0x00000000) + double_of_bits(0x00000000, 0x00000003), 0x80500000, 0x00000000, STR(__LINE__)); // -0x1p-1018 + 0x0.0000000000003p-1022 = -0x1p-1018
  comp64(double_of_bits(0x00000000, 0x00000003) + double_of_bits(0x80500000, 0x00000000), 0x80500000, 0x00000000, STR(__LINE__)); // 0x0.0000000000003p-1022 + -0x1p-1018 = -0x1p-1018
  comp64(double_of_bits(0x3ff00000, 0x00000007) + double_of_bits(0x40200000, 0x00000000), 0x40220000, 0x00000001, STR(__LINE__)); // 0x1.0000000000007p+0 + 0x1p+3 = 0x1.2000000000001p+3
  comp64(double_of_bits(0x40200000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000007), 0x40220000, 0x00000001, STR(__LINE__)); // 0x1p+3 + 0x1.0000000000007p+0 = 0x1.2000000000001p+3
  comp64(double_of_bits(0xbff00000, 0x00000007) + double_of_bits(0xc0200000, 0x00000000), 0xc0220000, 0x00000001, STR(__LINE__)); // -0x1.0000000000007p+0 + -0x1p+3 = -0x1.2000000000001p+3
  comp64(double_of_bits(0xc0200000, 0x00000000) + double_of_bits(0xbff00000, 0x00000007), 0xc0220000, 0x00000001, STR(__LINE__)); // -0x1p+3 + -0x1.0000000000007p+0 = -0x1.2000000000001p+3
  comp64(double_of_bits(0x401c0000, 0x00000000) + double_of_bits(0x436c0000, 0x00000000), 0x436c0000, 0x00000001, STR(__LINE__)); // 0x1.cp+2 + 0x1.cp+55 = 0x1.c000000000001p+55
  comp64(double_of_bits(0x436c0000, 0x00000000) + double_of_bits(0x401c0000, 0x00000000), 0x436c0000, 0x00000001, STR(__LINE__)); // 0x1.cp+55 + 0x1.cp+2 = 0x1.c000000000001p+55
  comp64(double_of_bits(0xc01c0000, 0x00000000) + double_of_bits(0xc36c0000, 0x00000000), 0xc36c0000, 0x00000001, STR(__LINE__)); // -0x1.cp+2 + -0x1.cp+55 = -0x1.c000000000001p+55
  comp64(double_of_bits(0xc36c0000, 0x00000000) + double_of_bits(0xc01c0000, 0x00000000), 0xc36c0000, 0x00000001, STR(__LINE__)); // -0x1.cp+55 + -0x1.cp+2 = -0x1.c000000000001p+55
}

void f52(void) {
  comp64(double_of_bits(0x00000000, 0x00000007) + double_of_bits(0x00400000, 0x00000000), 0x00400000, 0x00000001, STR(__LINE__)); // 0x0.0000000000007p-1022 + 0x1p-1019 = 0x1.0000000000001p-1019
  comp64(double_of_bits(0x00400000, 0x00000000) + double_of_bits(0x00000000, 0x00000007), 0x00400000, 0x00000001, STR(__LINE__)); // 0x1p-1019 + 0x0.0000000000007p-1022 = 0x1.0000000000001p-1019
  comp64(double_of_bits(0x80000000, 0x00000007) + double_of_bits(0x80400000, 0x00000000), 0x80400000, 0x00000001, STR(__LINE__)); // -0x0.0000000000007p-1022 + -0x1p-1019 = -0x1.0000000000001p-1019
  comp64(double_of_bits(0x80400000, 0x00000000) + double_of_bits(0x80000000, 0x00000007), 0x80400000, 0x00000001, STR(__LINE__)); // -0x1p-1019 + -0x0.0000000000007p-1022 = -0x1.0000000000001p-1019
  comp64(double_of_bits(0x3fffffff, 0xffffffff) + double_of_bits(0x3cc40000, 0x00000001), 0x40000000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp+0 + 0x1.4000000000001p-51 = 0x1.0000000000001p+1
  comp64(double_of_bits(0x3cc40000, 0x00000001) + double_of_bits(0x3fffffff, 0xffffffff), 0x40000000, 0x00000001, STR(__LINE__)); // 0x1.4000000000001p-51 + 0x1.fffffffffffffp+0 = 0x1.0000000000001p+1
  comp64(double_of_bits(0xbfffffff, 0xffffffff) + double_of_bits(0xbcc40000, 0x00000001), 0xc0000000, 0x00000001, STR(__LINE__)); // -0x1.fffffffffffffp+0 + -0x1.4000000000001p-51 = -0x1.0000000000001p+1
  comp64(double_of_bits(0xbcc40000, 0x00000001) + double_of_bits(0xbfffffff, 0xffffffff), 0xc0000000, 0x00000001, STR(__LINE__)); // -0x1.4000000000001p-51 + -0x1.fffffffffffffp+0 = -0x1.0000000000001p+1
  comp64(double_of_bits(0x7fe00000, 0x00000000) + double_of_bits(0xbff00000, 0x00000000), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 + -0x1p+0 = 0x1p+1023
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0x7fe00000, 0x00000000), 0x7fe00000, 0x00000000, STR(__LINE__)); // -0x1p+0 + 0x1p+1023 = 0x1p+1023
}

void f53(void) {
  comp64(double_of_bits(0xffe00000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000000), 0xffe00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 + 0x1p+0 = -0x1p+1023
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0xffe00000, 0x00000000), 0xffe00000, 0x00000000, STR(__LINE__)); // 0x1p+0 + -0x1p+1023 = -0x1p+1023
  comp64(double_of_bits(0x7fdfffff, 0xffffffff) + double_of_bits(0xbff00000, 0x00000000), 0x7fdfffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1022 + -0x1p+0 = 0x1.fffffffffffffp+1022
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0x7fdfffff, 0xffffffff), 0x7fdfffff, 0xffffffff, STR(__LINE__)); // -0x1p+0 + 0x1.fffffffffffffp+1022 = 0x1.fffffffffffffp+1022
  comp64(double_of_bits(0xffdfffff, 0xffffffff) + double_of_bits(0x3ff00000, 0x00000000), 0xffdfffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1022 + 0x1p+0 = -0x1.fffffffffffffp+1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0xffdfffff, 0xffffffff), 0xffdfffff, 0xffffffff, STR(__LINE__)); // 0x1p+0 + -0x1.fffffffffffffp+1022 = -0x1.fffffffffffffp+1022
  comp64(double_of_bits(0x7fefffff, 0xffffffff) + double_of_bits(0xbff00000, 0x00000000), 0x7fefffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1023 + -0x1p+0 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0x7fefffff, 0xffffffff), 0x7fefffff, 0xffffffff, STR(__LINE__)); // -0x1p+0 + 0x1.fffffffffffffp+1023 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xffefffff, 0xffffffff) + double_of_bits(0x3ff00000, 0x00000000), 0xffefffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1023 + 0x1p+0 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0xffefffff, 0xffffffff), 0xffefffff, 0xffffffff, STR(__LINE__)); // 0x1p+0 + -0x1.fffffffffffffp+1023 = -0x1.fffffffffffffp+1023
}

void f54(void) {
  comp64(double_of_bits(0x7fefffff, 0xfffffffe) + double_of_bits(0xbff00000, 0x00000000), 0x7fefffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffep+1023 + -0x1p+0 = 0x1.ffffffffffffep+1023
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0x7fefffff, 0xfffffffe), 0x7fefffff, 0xfffffffe, STR(__LINE__)); // -0x1p+0 + 0x1.ffffffffffffep+1023 = 0x1.ffffffffffffep+1023
  comp64(double_of_bits(0xffefffff, 0xfffffffe) + double_of_bits(0x3ff00000, 0x00000000), 0xffefffff, 0xfffffffe, STR(__LINE__)); // -0x1.ffffffffffffep+1023 + 0x1p+0 = -0x1.ffffffffffffep+1023
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0xffefffff, 0xfffffffe), 0xffefffff, 0xfffffffe, STR(__LINE__)); // 0x1p+0 + -0x1.ffffffffffffep+1023 = -0x1.ffffffffffffep+1023
  comp64(double_of_bits(0x7fefffff, 0xffffffff) + double_of_bits(0x80000000, 0x00000001), 0x7fefffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1023 + -0x0.0000000000001p-1022 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0x7fefffff, 0xffffffff), 0x7fefffff, 0xffffffff, STR(__LINE__)); // -0x0.0000000000001p-1022 + 0x1.fffffffffffffp+1023 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xffefffff, 0xffffffff) + double_of_bits(0x00000000, 0x00000001), 0xffefffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1023 + 0x0.0000000000001p-1022 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0xffefffff, 0xffffffff), 0xffefffff, 0xffffffff, STR(__LINE__)); // 0x0.0000000000001p-1022 + -0x1.fffffffffffffp+1023 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x80000000, 0x00000003) + double_of_bits(0x7fe00000, 0x00000000), 0x7fe00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000003p-1022 + 0x1p+1023 = 0x1p+1023
  comp64(double_of_bits(0x7fe00000, 0x00000000) + double_of_bits(0x80000000, 0x00000003), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 + -0x0.0000000000003p-1022 = 0x1p+1023
}

void f55(void) {
  comp64(double_of_bits(0x00000000, 0x00000003) + double_of_bits(0xffe00000, 0x00000000), 0xffe00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000003p-1022 + -0x1p+1023 = -0x1p+1023
  comp64(double_of_bits(0xffe00000, 0x00000000) + double_of_bits(0x00000000, 0x00000003), 0xffe00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 + 0x0.0000000000003p-1022 = -0x1p+1023
  comp64(double_of_bits(0x3fefffff, 0xffffffff) + double_of_bits(0x80000000, 0x00000001), 0x3fefffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp-1 + -0x0.0000000000001p-1022 = 0x1.fffffffffffffp-1
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0x3fefffff, 0xffffffff), 0x3fefffff, 0xffffffff, STR(__LINE__)); // -0x0.0000000000001p-1022 + 0x1.fffffffffffffp-1 = 0x1.fffffffffffffp-1
  comp64(double_of_bits(0xbfffffff, 0xffffffff) + double_of_bits(0x00000000, 0x00000001), 0xbfffffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+0 + 0x0.0000000000001p-1022 = -0x1.fffffffffffffp+0
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0xbfffffff, 0xffffffff), 0xbfffffff, 0xffffffff, STR(__LINE__)); // 0x0.0000000000001p-1022 + -0x1.fffffffffffffp+0 = -0x1.fffffffffffffp+0
  comp64(double_of_bits(0x80000000, 0x00000003) + double_of_bits(0x40080000, 0x00000000), 0x40080000, 0x00000000, STR(__LINE__)); // -0x0.0000000000003p-1022 + 0x1.8p+1 = 0x1.8p+1
  comp64(double_of_bits(0x40080000, 0x00000000) + double_of_bits(0x80000000, 0x00000003), 0x40080000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 + -0x0.0000000000003p-1022 = 0x1.8p+1
  comp64(double_of_bits(0x00000000, 0x00000003) + double_of_bits(0xc0140000, 0x00000000), 0xc0140000, 0x00000000, STR(__LINE__)); // 0x0.0000000000003p-1022 + -0x1.4p+2 = -0x1.4p+2
  comp64(double_of_bits(0xc0140000, 0x00000000) + double_of_bits(0x00000000, 0x00000003), 0xc0140000, 0x00000000, STR(__LINE__)); // -0x1.4p+2 + 0x0.0000000000003p-1022 = -0x1.4p+2
}

void f56(void) {
  comp64(double_of_bits(0x40000000, 0x00000000) + double_of_bits(0xc0000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p+1 + -0x1p+1 = 0x0p+0
  comp64(double_of_bits(0xc0000000, 0x00000000) + double_of_bits(0x40000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p+1 + 0x1p+1 = 0x0p+0
  comp64(double_of_bits(0x40140000, 0x00000000) + double_of_bits(0xc0140000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.4p+2 + -0x1.4p+2 = 0x0p+0
  comp64(double_of_bits(0xc0140000, 0x00000000) + double_of_bits(0x40140000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.4p+2 + 0x1.4p+2 = 0x0p+0
  comp64(double_of_bits(0x7fe00000, 0x00000000) + double_of_bits(0xffe00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p+1023 + -0x1p+1023 = 0x0p+0
  comp64(double_of_bits(0xffe00000, 0x00000000) + double_of_bits(0x7fe00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p+1023 + 0x1p+1023 = 0x0p+0
  comp64(double_of_bits(0xffdfffff, 0xfffffffe) + double_of_bits(0x7fdfffff, 0xfffffffe), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffep+1022 + 0x1.ffffffffffffep+1022 = 0x0p+0
  comp64(double_of_bits(0x7fdfffff, 0xfffffffe) + double_of_bits(0xffdfffff, 0xfffffffe), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffep+1022 + -0x1.ffffffffffffep+1022 = 0x0p+0
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0xbff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p+0 + -0x1p+0 = 0x0p+0
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p+0 + 0x1p+0 = 0x0p+0
}

void f57(void) {
  comp64(double_of_bits(0xc0080000, 0x00000000) + double_of_bits(0x40080000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 + 0x1.8p+1 = 0x0p+0
  comp64(double_of_bits(0x40080000, 0x00000000) + double_of_bits(0xc0080000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 + -0x1.8p+1 = 0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000000) + double_of_bits(0x80100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 + -0x1p-1022 = 0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000000) + double_of_bits(0x00100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 + 0x1p-1022 = 0x0p+0
  comp64(double_of_bits(0x000fffff, 0xfffffffc) + double_of_bits(0x800fffff, 0xfffffffc), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.ffffffffffffcp-1022 + -0x0.ffffffffffffcp-1022 = 0x0p+0
  comp64(double_of_bits(0x800fffff, 0xfffffffc) + double_of_bits(0x000fffff, 0xfffffffc), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.ffffffffffffcp-1022 + 0x0.ffffffffffffcp-1022 = 0x0p+0
  comp64(double_of_bits(0x800fffff, 0xffffffff) + double_of_bits(0x000fffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 + 0x0.fffffffffffffp-1022 = 0x0p+0
  comp64(double_of_bits(0x000fffff, 0xffffffff) + double_of_bits(0x800fffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 + -0x0.fffffffffffffp-1022 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 + -0x0.0000000000001p-1022 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 + 0x0.0000000000001p-1022 = 0x0p+0
}

void f58(void) {
  comp64(double_of_bits(0x7fefffff, 0xffffffff) + double_of_bits(0xffefffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 + -0x1.fffffffffffffp+1023 = 0x0p+0
  comp64(double_of_bits(0xffefffff, 0xffffffff) + double_of_bits(0x7fefffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 + 0x1.fffffffffffffp+1023 = 0x0p+0
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0xbff00000, 0x00000000), 0x3cb00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + -0x1p+0 = 0x1p-52
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x3cb00000, 0x00000000, STR(__LINE__)); // -0x1p+0 + 0x1.0000000000001p+0 = 0x1p-52
  comp64(double_of_bits(0x7fe00000, 0x00000001) + double_of_bits(0xffe00000, 0x00000000), 0x7ca00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+1023 + -0x1p+1023 = 0x1p+971
  comp64(double_of_bits(0xffe00000, 0x00000000) + double_of_bits(0x7fe00000, 0x00000001), 0x7ca00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 + 0x1.0000000000001p+1023 = 0x1p+971
  comp64(double_of_bits(0x00100000, 0x00000001) + double_of_bits(0x80100000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p-1022 + -0x1p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80100000, 0x00000000) + double_of_bits(0x00100000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1p-1022 + 0x1.0000000000001p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xc0000000, 0x00000000) + double_of_bits(0x40000000, 0x00000001), 0x3cc00000, 0x00000000, STR(__LINE__)); // -0x1p+1 + 0x1.0000000000001p+1 = 0x1p-51
  comp64(double_of_bits(0x40000000, 0x00000001) + double_of_bits(0xc0000000, 0x00000000), 0x3cc00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+1 + -0x1p+1 = 0x1p-51
}

void f59(void) {
  comp64(double_of_bits(0xffd00000, 0x00000000) + double_of_bits(0x7fd00000, 0x00000001), 0x7c900000, 0x00000000, STR(__LINE__)); // -0x1p+1022 + 0x1.0000000000001p+1022 = 0x1p+970
  comp64(double_of_bits(0x7fd00000, 0x00000001) + double_of_bits(0xffd00000, 0x00000000), 0x7c900000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+1022 + -0x1p+1022 = 0x1p+970
  comp64(double_of_bits(0xbff00000, 0x00000001) + double_of_bits(0x3ff00000, 0x00000000), 0xbcb00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+0 + 0x1p+0 = -0x1p-52
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0xbff00000, 0x00000001), 0xbcb00000, 0x00000000, STR(__LINE__)); // 0x1p+0 + -0x1.0000000000001p+0 = -0x1p-52
  comp64(double_of_bits(0xffe00000, 0x00000001) + double_of_bits(0x7fe00000, 0x00000000), 0xfca00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+1023 + 0x1p+1023 = -0x1p+971
  comp64(double_of_bits(0x7fe00000, 0x00000000) + double_of_bits(0xffe00000, 0x00000001), 0xfca00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 + -0x1.0000000000001p+1023 = -0x1p+971
  comp64(double_of_bits(0x80100000, 0x00000001) + double_of_bits(0x00100000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p-1022 + 0x1p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00100000, 0x00000000) + double_of_bits(0x80100000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1p-1022 + -0x1.0000000000001p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x40000000, 0x00000000) + double_of_bits(0xc0000000, 0x00000001), 0xbcc00000, 0x00000000, STR(__LINE__)); // 0x1p+1 + -0x1.0000000000001p+1 = -0x1p-51
  comp64(double_of_bits(0xc0000000, 0x00000001) + double_of_bits(0x40000000, 0x00000000), 0xbcc00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+1 + 0x1p+1 = -0x1p-51
}

void f60(void) {
  comp64(double_of_bits(0x7fd00000, 0x00000000) + double_of_bits(0xffd00000, 0x00000001), 0xfc900000, 0x00000000, STR(__LINE__)); // 0x1p+1022 + -0x1.0000000000001p+1022 = -0x1p+970
  comp64(double_of_bits(0xffd00000, 0x00000001) + double_of_bits(0x7fd00000, 0x00000000), 0xfc900000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+1022 + 0x1p+1022 = -0x1p+970
  comp64(double_of_bits(0x00000000, 0x00000002) + double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000002p-1022 + -0x0.0000000000001p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0x00000000, 0x00000002), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000001p-1022 + 0x0.0000000000002p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbff00000, 0x00000001) + double_of_bits(0x3ff00000, 0x00000002), 0x3cb00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+0 + 0x1.0000000000002p+0 = 0x1p-52
  comp64(double_of_bits(0x3ff00000, 0x00000002) + double_of_bits(0xbff00000, 0x00000001), 0x3cb00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000002p+0 + -0x1.0000000000001p+0 = 0x1p-52
  comp64(double_of_bits(0xffe00000, 0x00000001) + double_of_bits(0x7fe00000, 0x00000002), 0x7ca00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+1023 + 0x1.0000000000002p+1023 = 0x1p+971
  comp64(double_of_bits(0x7fe00000, 0x00000002) + double_of_bits(0xffe00000, 0x00000001), 0x7ca00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000002p+1023 + -0x1.0000000000001p+1023 = 0x1p+971
  comp64(double_of_bits(0x80100000, 0x00000001) + double_of_bits(0x00100000, 0x00000002), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p-1022 + 0x1.0000000000002p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x00100000, 0x00000002) + double_of_bits(0x80100000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.0000000000002p-1022 + -0x1.0000000000001p-1022 = 0x0.0000000000001p-1022
}

void f61(void) {
  comp64(double_of_bits(0x80000000, 0x00000002) + double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000002p-1022 + 0x0.0000000000001p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x80000000, 0x00000002), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000001p-1022 + -0x0.0000000000002p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0xbff00000, 0x00000002), 0xbcb00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + -0x1.0000000000002p+0 = -0x1p-52
  comp64(double_of_bits(0xbff00000, 0x00000002) + double_of_bits(0x3ff00000, 0x00000001), 0xbcb00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000002p+0 + 0x1.0000000000001p+0 = -0x1p-52
  comp64(double_of_bits(0x7fe00000, 0x00000001) + double_of_bits(0xffe00000, 0x00000002), 0xfca00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+1023 + -0x1.0000000000002p+1023 = -0x1p+971
  comp64(double_of_bits(0xffe00000, 0x00000002) + double_of_bits(0x7fe00000, 0x00000001), 0xfca00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000002p+1023 + 0x1.0000000000001p+1023 = -0x1p+971
  comp64(double_of_bits(0x00100000, 0x00000001) + double_of_bits(0x80100000, 0x00000002), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p-1022 + -0x1.0000000000002p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x80100000, 0x00000002) + double_of_bits(0x00100000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.0000000000002p-1022 + 0x1.0000000000001p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000003) + double_of_bits(0x00000000, 0x00000002), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000003p-1022 + 0x0.0000000000002p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000002) + double_of_bits(0x80000000, 0x00000003), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000002p-1022 + -0x0.0000000000003p-1022 = -0x0.0000000000001p-1022
}

void f62(void) {
  comp64(double_of_bits(0x00000000, 0x00000003) + double_of_bits(0x80000000, 0x00000002), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000003p-1022 + -0x0.0000000000002p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000002) + double_of_bits(0x00000000, 0x00000003), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000002p-1022 + 0x0.0000000000003p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x40000000, 0x00000004) + double_of_bits(0xc0000000, 0x00000003), 0x3cc00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000004p+1 + -0x1.0000000000003p+1 = 0x1p-51
  comp64(double_of_bits(0xc0000000, 0x00000003) + double_of_bits(0x40000000, 0x00000004), 0x3cc00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000003p+1 + 0x1.0000000000004p+1 = 0x1p-51
  comp64(double_of_bits(0x7fd00000, 0x00000004) + double_of_bits(0xffd00000, 0x00000003), 0x7c900000, 0x00000000, STR(__LINE__)); // 0x1.0000000000004p+1022 + -0x1.0000000000003p+1022 = 0x1p+970
  comp64(double_of_bits(0xffd00000, 0x00000003) + double_of_bits(0x7fd00000, 0x00000004), 0x7c900000, 0x00000000, STR(__LINE__)); // -0x1.0000000000003p+1022 + 0x1.0000000000004p+1022 = 0x1p+970
  comp64(double_of_bits(0xc0000000, 0x00000004) + double_of_bits(0x40000000, 0x00000003), 0xbcc00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000004p+1 + 0x1.0000000000003p+1 = -0x1p-51
  comp64(double_of_bits(0x40000000, 0x00000003) + double_of_bits(0xc0000000, 0x00000004), 0xbcc00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000003p+1 + -0x1.0000000000004p+1 = -0x1p-51
  comp64(double_of_bits(0xffd00000, 0x00000004) + double_of_bits(0x7fd00000, 0x00000003), 0xfc900000, 0x00000000, STR(__LINE__)); // -0x1.0000000000004p+1022 + 0x1.0000000000003p+1022 = -0x1p+970
  comp64(double_of_bits(0x7fd00000, 0x00000003) + double_of_bits(0xffd00000, 0x00000004), 0xfc900000, 0x00000000, STR(__LINE__)); // 0x1.0000000000003p+1022 + -0x1.0000000000004p+1022 = -0x1p+970
}

void f63(void) {
  comp64(double_of_bits(0x400fffff, 0xffffffff) + double_of_bits(0xc00fffff, 0xfffffffe), 0x3cc00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1 + -0x1.ffffffffffffep+1 = 0x1p-51
  comp64(double_of_bits(0xc00fffff, 0xfffffffe) + double_of_bits(0x400fffff, 0xffffffff), 0x3cc00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffep+1 + 0x1.fffffffffffffp+1 = 0x1p-51
  comp64(double_of_bits(0x7fcfffff, 0xffffffff) + double_of_bits(0xffcfffff, 0xfffffffe), 0x7c800000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1021 + -0x1.ffffffffffffep+1021 = 0x1p+969
  comp64(double_of_bits(0xffcfffff, 0xfffffffe) + double_of_bits(0x7fcfffff, 0xffffffff), 0x7c800000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffep+1021 + 0x1.fffffffffffffp+1021 = 0x1p+969
  comp64(double_of_bits(0x000fffff, 0xffffffff) + double_of_bits(0x800fffff, 0xfffffffe), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.fffffffffffffp-1022 + -0x0.ffffffffffffep-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x800fffff, 0xfffffffe) + double_of_bits(0x000fffff, 0xffffffff), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.ffffffffffffep-1022 + 0x0.fffffffffffffp-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xffefffff, 0xfffffffe) + double_of_bits(0x7fefffff, 0xffffffff), 0x7ca00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffep+1023 + 0x1.fffffffffffffp+1023 = 0x1p+971
  comp64(double_of_bits(0x7fefffff, 0xffffffff) + double_of_bits(0xffefffff, 0xfffffffe), 0x7ca00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 + -0x1.ffffffffffffep+1023 = 0x1p+971
  comp64(double_of_bits(0xc00fffff, 0xffffffff) + double_of_bits(0x400fffff, 0xfffffffe), 0xbcc00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1 + 0x1.ffffffffffffep+1 = -0x1p-51
  comp64(double_of_bits(0x400fffff, 0xfffffffe) + double_of_bits(0xc00fffff, 0xffffffff), 0xbcc00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffep+1 + -0x1.fffffffffffffp+1 = -0x1p-51
}

void f64(void) {
  comp64(double_of_bits(0xffcfffff, 0xffffffff) + double_of_bits(0x7fcfffff, 0xfffffffe), 0xfc800000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1021 + 0x1.ffffffffffffep+1021 = -0x1p+969
  comp64(double_of_bits(0x7fcfffff, 0xfffffffe) + double_of_bits(0xffcfffff, 0xffffffff), 0xfc800000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffep+1021 + -0x1.fffffffffffffp+1021 = -0x1p+969
  comp64(double_of_bits(0x800fffff, 0xffffffff) + double_of_bits(0x000fffff, 0xfffffffe), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.fffffffffffffp-1022 + 0x0.ffffffffffffep-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x000fffff, 0xfffffffe) + double_of_bits(0x800fffff, 0xffffffff), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.ffffffffffffep-1022 + -0x0.fffffffffffffp-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x7fefffff, 0xfffffffe) + double_of_bits(0xffefffff, 0xffffffff), 0xfca00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffep+1023 + -0x1.fffffffffffffp+1023 = -0x1p+971
  comp64(double_of_bits(0xffefffff, 0xffffffff) + double_of_bits(0x7fefffff, 0xfffffffe), 0xfca00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 + 0x1.ffffffffffffep+1023 = -0x1p+971
  comp64(double_of_bits(0x000fffff, 0xfffffffd) + double_of_bits(0x800fffff, 0xfffffffe), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.ffffffffffffdp-1022 + -0x0.ffffffffffffep-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x800fffff, 0xfffffffe) + double_of_bits(0x000fffff, 0xfffffffd), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.ffffffffffffep-1022 + 0x0.ffffffffffffdp-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x800fffff, 0xfffffffd) + double_of_bits(0x000fffff, 0xfffffffe), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.ffffffffffffdp-1022 + 0x0.ffffffffffffep-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x000fffff, 0xfffffffe) + double_of_bits(0x800fffff, 0xfffffffd), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.ffffffffffffep-1022 + -0x0.ffffffffffffdp-1022 = 0x0.0000000000001p-1022
}

void f65(void) {
  comp64(double_of_bits(0x3fffffff, 0xfffffffc) + double_of_bits(0xbfffffff, 0xfffffffd), 0xbcb00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffcp+0 + -0x1.ffffffffffffdp+0 = -0x1p-52
  comp64(double_of_bits(0xbfffffff, 0xfffffffd) + double_of_bits(0x3fffffff, 0xfffffffc), 0xbcb00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffdp+0 + 0x1.ffffffffffffcp+0 = -0x1p-52
  comp64(double_of_bits(0xbfffffff, 0xfffffffc) + double_of_bits(0x3fffffff, 0xfffffffd), 0x3cb00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffcp+0 + 0x1.ffffffffffffdp+0 = 0x1p-52
  comp64(double_of_bits(0x3fffffff, 0xfffffffd) + double_of_bits(0xbfffffff, 0xfffffffc), 0x3cb00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffdp+0 + -0x1.ffffffffffffcp+0 = 0x1p-52
  comp64(double_of_bits(0x000fffff, 0xffffffff) + double_of_bits(0x80100000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.fffffffffffffp-1022 + -0x1p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x80100000, 0x00000000) + double_of_bits(0x000fffff, 0xffffffff), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1p-1022 + 0x0.fffffffffffffp-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x3fffffff, 0xffffffff) + double_of_bits(0xc0000000, 0x00000000), 0xbcb00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+0 + -0x1p+1 = -0x1p-52
  comp64(double_of_bits(0xc0000000, 0x00000000) + double_of_bits(0x3fffffff, 0xffffffff), 0xbcb00000, 0x00000000, STR(__LINE__)); // -0x1p+1 + 0x1.fffffffffffffp+0 = -0x1p-52
  comp64(double_of_bits(0x002fffff, 0xffffffff) + double_of_bits(0x80300000, 0x00000000), 0x80000000, 0x00000002, STR(__LINE__)); // 0x1.fffffffffffffp-1021 + -0x1p-1020 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x80300000, 0x00000000) + double_of_bits(0x002fffff, 0xffffffff), 0x80000000, 0x00000002, STR(__LINE__)); // -0x1p-1020 + 0x1.fffffffffffffp-1021 = -0x0.0000000000002p-1022
}

void f66(void) {
  comp64(double_of_bits(0x7fdfffff, 0xffffffff) + double_of_bits(0xffe00000, 0x00000000), 0xfc900000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1022 + -0x1p+1023 = -0x1p+970
  comp64(double_of_bits(0xffe00000, 0x00000000) + double_of_bits(0x7fdfffff, 0xffffffff), 0xfc900000, 0x00000000, STR(__LINE__)); // -0x1p+1023 + 0x1.fffffffffffffp+1022 = -0x1p+970
  comp64(double_of_bits(0x001fffff, 0xffffffff) + double_of_bits(0x80200000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp-1022 + -0x1p-1021 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x80200000, 0x00000000) + double_of_bits(0x001fffff, 0xffffffff), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1p-1021 + 0x1.fffffffffffffp-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0xffd00000, 0x00000000) + double_of_bits(0x7fcfffff, 0xffffffff), 0xfc800000, 0x00000000, STR(__LINE__)); // -0x1p+1022 + 0x1.fffffffffffffp+1021 = -0x1p+969
  comp64(double_of_bits(0x7fcfffff, 0xffffffff) + double_of_bits(0xffd00000, 0x00000000), 0xfc800000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1021 + -0x1p+1022 = -0x1p+969
  comp64(double_of_bits(0x40000000, 0x00000000) + double_of_bits(0xbfffffff, 0xffffffff), 0x3cb00000, 0x00000000, STR(__LINE__)); // 0x1p+1 + -0x1.fffffffffffffp+0 = 0x1p-52
  comp64(double_of_bits(0xbfffffff, 0xffffffff) + double_of_bits(0x40000000, 0x00000000), 0x3cb00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+0 + 0x1p+1 = 0x1p-52
  comp64(double_of_bits(0x7fd00000, 0x00000000) + double_of_bits(0xffcfffff, 0xffffffff), 0x7c800000, 0x00000000, STR(__LINE__)); // 0x1p+1022 + -0x1.fffffffffffffp+1021 = 0x1p+969
  comp64(double_of_bits(0xffcfffff, 0xffffffff) + double_of_bits(0x7fd00000, 0x00000000), 0x7c800000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1021 + 0x1p+1022 = 0x1p+969
}

void f67(void) {
  comp64(double_of_bits(0x00200000, 0x00000000) + double_of_bits(0x801fffff, 0xffffffff), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1p-1021 + -0x1.fffffffffffffp-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x801fffff, 0xffffffff) + double_of_bits(0x00200000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.fffffffffffffp-1022 + 0x1p-1021 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x00300000, 0x00000000) + double_of_bits(0x802fffff, 0xffffffff), 0x00000000, 0x00000002, STR(__LINE__)); // 0x1p-1020 + -0x1.fffffffffffffp-1021 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x802fffff, 0xffffffff) + double_of_bits(0x00300000, 0x00000000), 0x00000000, 0x00000002, STR(__LINE__)); // -0x1.fffffffffffffp-1021 + 0x1p-1020 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) + double_of_bits(0x00100000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.fffffffffffffp-1022 + 0x1p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x00100000, 0x00000000) + double_of_bits(0x800fffff, 0xffffffff), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1p-1022 + -0x0.fffffffffffffp-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xffdfffff, 0xffffffff) + double_of_bits(0x7fe00000, 0x00000000), 0x7c900000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1022 + 0x1p+1023 = 0x1p+970
  comp64(double_of_bits(0x7fe00000, 0x00000000) + double_of_bits(0xffdfffff, 0xffffffff), 0x7c900000, 0x00000000, STR(__LINE__)); // 0x1p+1023 + -0x1.fffffffffffffp+1022 = 0x1p+970
  comp64(double_of_bits(0x400fffff, 0xffffffff) + double_of_bits(0xc0100000, 0x00000001), 0xbcd80000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1 + -0x1.0000000000001p+2 = -0x1.8p-50
  comp64(double_of_bits(0xc0100000, 0x00000001) + double_of_bits(0x400fffff, 0xffffffff), 0xbcd80000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+2 + 0x1.fffffffffffffp+1 = -0x1.8p-50
}

void f68(void) {
  comp64(double_of_bits(0xffb00000, 0x00000001) + double_of_bits(0x7fafffff, 0xffffffff), 0xfc780000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+1020 + 0x1.fffffffffffffp+1019 = -0x1.8p+968
  comp64(double_of_bits(0x7fafffff, 0xffffffff) + double_of_bits(0xffb00000, 0x00000001), 0xfc780000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1019 + -0x1.0000000000001p+1020 = -0x1.8p+968
  comp64(double_of_bits(0x80200000, 0x00000001) + double_of_bits(0x001fffff, 0xffffffff), 0x80000000, 0x00000003, STR(__LINE__)); // -0x1.0000000000001p-1021 + 0x1.fffffffffffffp-1022 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0x001fffff, 0xffffffff) + double_of_bits(0x80200000, 0x00000001), 0x80000000, 0x00000003, STR(__LINE__)); // 0x1.fffffffffffffp-1022 + -0x1.0000000000001p-1021 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0x80300000, 0x00000001) + double_of_bits(0x002fffff, 0xffffffff), 0x80000000, 0x00000006, STR(__LINE__)); // -0x1.0000000000001p-1020 + 0x1.fffffffffffffp-1021 = -0x0.0000000000006p-1022
  comp64(double_of_bits(0x002fffff, 0xffffffff) + double_of_bits(0x80300000, 0x00000001), 0x80000000, 0x00000006, STR(__LINE__)); // 0x1.fffffffffffffp-1021 + -0x1.0000000000001p-1020 = -0x0.0000000000006p-1022
  comp64(double_of_bits(0xc00fffff, 0xffffffff) + double_of_bits(0x40100000, 0x00000001), 0x3cd80000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1 + 0x1.0000000000001p+2 = 0x1.8p-50
  comp64(double_of_bits(0x40100000, 0x00000001) + double_of_bits(0xc00fffff, 0xffffffff), 0x3cd80000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+2 + -0x1.fffffffffffffp+1 = 0x1.8p-50
  comp64(double_of_bits(0x7fb00000, 0x00000001) + double_of_bits(0xffafffff, 0xffffffff), 0x7c780000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+1020 + -0x1.fffffffffffffp+1019 = 0x1.8p+968
  comp64(double_of_bits(0xffafffff, 0xffffffff) + double_of_bits(0x7fb00000, 0x00000001), 0x7c780000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1019 + 0x1.0000000000001p+1020 = 0x1.8p+968
}

void f69(void) {
  comp64(double_of_bits(0x00200000, 0x00000001) + double_of_bits(0x801fffff, 0xffffffff), 0x00000000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p-1021 + -0x1.fffffffffffffp-1022 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0x801fffff, 0xffffffff) + double_of_bits(0x00200000, 0x00000001), 0x00000000, 0x00000003, STR(__LINE__)); // -0x1.fffffffffffffp-1022 + 0x1.0000000000001p-1021 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0x00300000, 0x00000001) + double_of_bits(0x802fffff, 0xffffffff), 0x00000000, 0x00000006, STR(__LINE__)); // 0x1.0000000000001p-1020 + -0x1.fffffffffffffp-1021 = 0x0.0000000000006p-1022
  comp64(double_of_bits(0x802fffff, 0xffffffff) + double_of_bits(0x00300000, 0x00000001), 0x00000000, 0x00000006, STR(__LINE__)); // -0x1.fffffffffffffp-1021 + 0x1.0000000000001p-1020 = 0x0.0000000000006p-1022
  comp64(double_of_bits(0x400fffff, 0xffffffff) + double_of_bits(0xc0100000, 0x00000002), 0xbce40000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1 + -0x1.0000000000002p+2 = -0x1.4p-49
  comp64(double_of_bits(0xc0100000, 0x00000002) + double_of_bits(0x400fffff, 0xffffffff), 0xbce40000, 0x00000000, STR(__LINE__)); // -0x1.0000000000002p+2 + 0x1.fffffffffffffp+1 = -0x1.4p-49
  comp64(double_of_bits(0x7fcfffff, 0xffffffff) + double_of_bits(0xffd00000, 0x00000002), 0xfca40000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1021 + -0x1.0000000000002p+1022 = -0x1.4p+971
  comp64(double_of_bits(0xffd00000, 0x00000002) + double_of_bits(0x7fcfffff, 0xffffffff), 0xfca40000, 0x00000000, STR(__LINE__)); // -0x1.0000000000002p+1022 + 0x1.fffffffffffffp+1021 = -0x1.4p+971
  comp64(double_of_bits(0x001fffff, 0xffffffff) + double_of_bits(0x80200000, 0x00000002), 0x80000000, 0x00000005, STR(__LINE__)); // 0x1.fffffffffffffp-1022 + -0x1.0000000000002p-1021 = -0x0.0000000000005p-1022
  comp64(double_of_bits(0x80200000, 0x00000002) + double_of_bits(0x001fffff, 0xffffffff), 0x80000000, 0x00000005, STR(__LINE__)); // -0x1.0000000000002p-1021 + 0x1.fffffffffffffp-1022 = -0x0.0000000000005p-1022
}

void f70(void) {
  comp64(double_of_bits(0xc00fffff, 0xffffffff) + double_of_bits(0x40100000, 0x00000002), 0x3ce40000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1 + 0x1.0000000000002p+2 = 0x1.4p-49
  comp64(double_of_bits(0x40100000, 0x00000002) + double_of_bits(0xc00fffff, 0xffffffff), 0x3ce40000, 0x00000000, STR(__LINE__)); // 0x1.0000000000002p+2 + -0x1.fffffffffffffp+1 = 0x1.4p-49
  comp64(double_of_bits(0xffcfffff, 0xffffffff) + double_of_bits(0x7fd00000, 0x00000002), 0x7ca40000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1021 + 0x1.0000000000002p+1022 = 0x1.4p+971
  comp64(double_of_bits(0x7fd00000, 0x00000002) + double_of_bits(0xffcfffff, 0xffffffff), 0x7ca40000, 0x00000000, STR(__LINE__)); // 0x1.0000000000002p+1022 + -0x1.fffffffffffffp+1021 = 0x1.4p+971
  comp64(double_of_bits(0x801fffff, 0xffffffff) + double_of_bits(0x00200000, 0x00000002), 0x00000000, 0x00000005, STR(__LINE__)); // -0x1.fffffffffffffp-1022 + 0x1.0000000000002p-1021 = 0x0.0000000000005p-1022
  comp64(double_of_bits(0x00200000, 0x00000002) + double_of_bits(0x801fffff, 0xffffffff), 0x00000000, 0x00000005, STR(__LINE__)); // 0x1.0000000000002p-1021 + -0x1.fffffffffffffp-1022 = 0x0.0000000000005p-1022
  comp64(double_of_bits(0x001fffff, 0xffffffff) + double_of_bits(0x80200000, 0x00000004), 0x80000000, 0x00000009, STR(__LINE__)); // 0x1.fffffffffffffp-1022 + -0x1.0000000000004p-1021 = -0x0.0000000000009p-1022
  comp64(double_of_bits(0x80200000, 0x00000004) + double_of_bits(0x001fffff, 0xffffffff), 0x80000000, 0x00000009, STR(__LINE__)); // -0x1.0000000000004p-1021 + 0x1.fffffffffffffp-1022 = -0x0.0000000000009p-1022
  comp64(double_of_bits(0x801fffff, 0xffffffff) + double_of_bits(0x00200000, 0x00000004), 0x00000000, 0x00000009, STR(__LINE__)); // -0x1.fffffffffffffp-1022 + 0x1.0000000000004p-1021 = 0x0.0000000000009p-1022
  comp64(double_of_bits(0x00200000, 0x00000004) + double_of_bits(0x801fffff, 0xffffffff), 0x00000000, 0x00000009, STR(__LINE__)); // 0x1.0000000000004p-1021 + -0x1.fffffffffffffp-1022 = 0x0.0000000000009p-1022
}

void f71(void) {
  comp64(double_of_bits(0x40000000, 0x00000001) + double_of_bits(0xbff00000, 0x00000001), 0x3ff00000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p+1 + -0x1.0000000000001p+0 = 0x1.0000000000001p+0
  comp64(double_of_bits(0xbff00000, 0x00000001) + double_of_bits(0x40000000, 0x00000001), 0x3ff00000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p+0 + 0x1.0000000000001p+1 = 0x1.0000000000001p+0
  comp64(double_of_bits(0x00200000, 0x00000001) + double_of_bits(0x80100000, 0x00000001), 0x00100000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p-1021 + -0x1.0000000000001p-1022 = 0x1.0000000000001p-1022
  comp64(double_of_bits(0x80100000, 0x00000001) + double_of_bits(0x00200000, 0x00000001), 0x00100000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p-1022 + 0x1.0000000000001p-1021 = 0x1.0000000000001p-1022
  comp64(double_of_bits(0xc0000000, 0x00000001) + double_of_bits(0x3ff00000, 0x00000001), 0xbff00000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p+1 + 0x1.0000000000001p+0 = -0x1.0000000000001p+0
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0xc0000000, 0x00000001), 0xbff00000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p+0 + -0x1.0000000000001p+1 = -0x1.0000000000001p+0
  comp64(double_of_bits(0x80200000, 0x00000001) + double_of_bits(0x00100000, 0x00000001), 0x80100000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p-1021 + 0x1.0000000000001p-1022 = -0x1.0000000000001p-1022
  comp64(double_of_bits(0x00100000, 0x00000001) + double_of_bits(0x80200000, 0x00000001), 0x80100000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p-1022 + -0x1.0000000000001p-1021 = -0x1.0000000000001p-1022
  comp64(double_of_bits(0xffd00000, 0x00000001) + double_of_bits(0x7fe00000, 0x00000001), 0x7fd00000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p+1022 + 0x1.0000000000001p+1023 = 0x1.0000000000001p+1022
  comp64(double_of_bits(0x7fe00000, 0x00000001) + double_of_bits(0xffd00000, 0x00000001), 0x7fd00000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p+1023 + -0x1.0000000000001p+1022 = 0x1.0000000000001p+1022
}

void f72(void) {
  comp64(double_of_bits(0x7fd00000, 0x00000001) + double_of_bits(0xffe00000, 0x00000001), 0xffd00000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p+1022 + -0x1.0000000000001p+1023 = -0x1.0000000000001p+1022
  comp64(double_of_bits(0xffe00000, 0x00000001) + double_of_bits(0x7fd00000, 0x00000001), 0xffd00000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p+1023 + 0x1.0000000000001p+1022 = -0x1.0000000000001p+1022
  comp64(double_of_bits(0x40000000, 0x00000002) + double_of_bits(0xbff00000, 0x00000001), 0x3ff00000, 0x00000003, STR(__LINE__)); // 0x1.0000000000002p+1 + -0x1.0000000000001p+0 = 0x1.0000000000003p+0
  comp64(double_of_bits(0xbff00000, 0x00000001) + double_of_bits(0x40000000, 0x00000002), 0x3ff00000, 0x00000003, STR(__LINE__)); // -0x1.0000000000001p+0 + 0x1.0000000000002p+1 = 0x1.0000000000003p+0
  comp64(double_of_bits(0x7fe00000, 0x00000002) + double_of_bits(0xffd00000, 0x00000001), 0x7fd00000, 0x00000003, STR(__LINE__)); // 0x1.0000000000002p+1023 + -0x1.0000000000001p+1022 = 0x1.0000000000003p+1022
  comp64(double_of_bits(0xffd00000, 0x00000001) + double_of_bits(0x7fe00000, 0x00000002), 0x7fd00000, 0x00000003, STR(__LINE__)); // -0x1.0000000000001p+1022 + 0x1.0000000000002p+1023 = 0x1.0000000000003p+1022
  comp64(double_of_bits(0x00200000, 0x00000002) + double_of_bits(0x80100000, 0x00000001), 0x00100000, 0x00000003, STR(__LINE__)); // 0x1.0000000000002p-1021 + -0x1.0000000000001p-1022 = 0x1.0000000000003p-1022
  comp64(double_of_bits(0x80100000, 0x00000001) + double_of_bits(0x00200000, 0x00000002), 0x00100000, 0x00000003, STR(__LINE__)); // -0x1.0000000000001p-1022 + 0x1.0000000000002p-1021 = 0x1.0000000000003p-1022
  comp64(double_of_bits(0xc0000000, 0x00000002) + double_of_bits(0x3ff00000, 0x00000001), 0xbff00000, 0x00000003, STR(__LINE__)); // -0x1.0000000000002p+1 + 0x1.0000000000001p+0 = -0x1.0000000000003p+0
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0xc0000000, 0x00000002), 0xbff00000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p+0 + -0x1.0000000000002p+1 = -0x1.0000000000003p+0
}

void f73(void) {
  comp64(double_of_bits(0xffe00000, 0x00000002) + double_of_bits(0x7fd00000, 0x00000001), 0xffd00000, 0x00000003, STR(__LINE__)); // -0x1.0000000000002p+1023 + 0x1.0000000000001p+1022 = -0x1.0000000000003p+1022
  comp64(double_of_bits(0x7fd00000, 0x00000001) + double_of_bits(0xffe00000, 0x00000002), 0xffd00000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p+1022 + -0x1.0000000000002p+1023 = -0x1.0000000000003p+1022
  comp64(double_of_bits(0x80200000, 0x00000002) + double_of_bits(0x00100000, 0x00000001), 0x80100000, 0x00000003, STR(__LINE__)); // -0x1.0000000000002p-1021 + 0x1.0000000000001p-1022 = -0x1.0000000000003p-1022
  comp64(double_of_bits(0x00100000, 0x00000001) + double_of_bits(0x80200000, 0x00000002), 0x80100000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p-1022 + -0x1.0000000000002p-1021 = -0x1.0000000000003p-1022
  comp64(double_of_bits(0x40000000, 0x00000002) + double_of_bits(0xbff00000, 0x00000003), 0x3ff00000, 0x00000001, STR(__LINE__)); // 0x1.0000000000002p+1 + -0x1.0000000000003p+0 = 0x1.0000000000001p+0
  comp64(double_of_bits(0xbff00000, 0x00000003) + double_of_bits(0x40000000, 0x00000002), 0x3ff00000, 0x00000001, STR(__LINE__)); // -0x1.0000000000003p+0 + 0x1.0000000000002p+1 = 0x1.0000000000001p+0
  comp64(double_of_bits(0x7fd00000, 0x00000002) + double_of_bits(0xffc00000, 0x00000003), 0x7fc00000, 0x00000001, STR(__LINE__)); // 0x1.0000000000002p+1022 + -0x1.0000000000003p+1021 = 0x1.0000000000001p+1021
  comp64(double_of_bits(0xffc00000, 0x00000003) + double_of_bits(0x7fd00000, 0x00000002), 0x7fc00000, 0x00000001, STR(__LINE__)); // -0x1.0000000000003p+1021 + 0x1.0000000000002p+1022 = 0x1.0000000000001p+1021
  comp64(double_of_bits(0x00300000, 0x00000002) + double_of_bits(0x80200000, 0x00000003), 0x00200000, 0x00000001, STR(__LINE__)); // 0x1.0000000000002p-1020 + -0x1.0000000000003p-1021 = 0x1.0000000000001p-1021
  comp64(double_of_bits(0x80200000, 0x00000003) + double_of_bits(0x00300000, 0x00000002), 0x00200000, 0x00000001, STR(__LINE__)); // -0x1.0000000000003p-1021 + 0x1.0000000000002p-1020 = 0x1.0000000000001p-1021
}

void f74(void) {
  comp64(double_of_bits(0xc0000000, 0x00000002) + double_of_bits(0x3ff00000, 0x00000003), 0xbff00000, 0x00000001, STR(__LINE__)); // -0x1.0000000000002p+1 + 0x1.0000000000003p+0 = -0x1.0000000000001p+0
  comp64(double_of_bits(0x3ff00000, 0x00000003) + double_of_bits(0xc0000000, 0x00000002), 0xbff00000, 0x00000001, STR(__LINE__)); // 0x1.0000000000003p+0 + -0x1.0000000000002p+1 = -0x1.0000000000001p+0
  comp64(double_of_bits(0xffd00000, 0x00000002) + double_of_bits(0x7fc00000, 0x00000003), 0xffc00000, 0x00000001, STR(__LINE__)); // -0x1.0000000000002p+1022 + 0x1.0000000000003p+1021 = -0x1.0000000000001p+1021
  comp64(double_of_bits(0x7fc00000, 0x00000003) + double_of_bits(0xffd00000, 0x00000002), 0xffc00000, 0x00000001, STR(__LINE__)); // 0x1.0000000000003p+1021 + -0x1.0000000000002p+1022 = -0x1.0000000000001p+1021
  comp64(double_of_bits(0x80300000, 0x00000002) + double_of_bits(0x00200000, 0x00000003), 0x80200000, 0x00000001, STR(__LINE__)); // -0x1.0000000000002p-1020 + 0x1.0000000000003p-1021 = -0x1.0000000000001p-1021
  comp64(double_of_bits(0x00200000, 0x00000003) + double_of_bits(0x80300000, 0x00000002), 0x80200000, 0x00000001, STR(__LINE__)); // 0x1.0000000000003p-1021 + -0x1.0000000000002p-1020 = -0x1.0000000000001p-1021
  comp64(double_of_bits(0x3ff00000, 0x00000002) + double_of_bits(0xbff00000, 0x00000000), 0x3cc00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000002p+0 + -0x1p+0 = 0x1p-51
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000002), 0x3cc00000, 0x00000000, STR(__LINE__)); // -0x1p+0 + 0x1.0000000000002p+0 = 0x1p-51
  comp64(double_of_bits(0xbff00000, 0x00000002) + double_of_bits(0x3ff00000, 0x00000000), 0xbcc00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000002p+0 + 0x1p+0 = -0x1p-51
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0xbff00000, 0x00000002), 0xbcc00000, 0x00000000, STR(__LINE__)); // 0x1p+0 + -0x1.0000000000002p+0 = -0x1p-51
}

void f75(void) {
  comp64(double_of_bits(0x3ff00000, 0x00000004) + double_of_bits(0xbff00000, 0x00000000), 0x3cd00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000004p+0 + -0x1p+0 = 0x1p-50
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000004), 0x3cd00000, 0x00000000, STR(__LINE__)); // -0x1p+0 + 0x1.0000000000004p+0 = 0x1p-50
  comp64(double_of_bits(0xbff00000, 0x00000004) + double_of_bits(0x3ff00000, 0x00000000), 0xbcd00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000004p+0 + 0x1p+0 = -0x1p-50
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0xbff00000, 0x00000004), 0xbcd00000, 0x00000000, STR(__LINE__)); // 0x1p+0 + -0x1.0000000000004p+0 = -0x1p-50
  comp64(double_of_bits(0x3ff00000, 0x00000008) + double_of_bits(0xbff00000, 0x00000000), 0x3ce00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000008p+0 + -0x1p+0 = 0x1p-49
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000008), 0x3ce00000, 0x00000000, STR(__LINE__)); // -0x1p+0 + 0x1.0000000000008p+0 = 0x1p-49
  comp64(double_of_bits(0xbff00000, 0x00000008) + double_of_bits(0x3ff00000, 0x00000000), 0xbce00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000008p+0 + 0x1p+0 = -0x1p-49
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0xbff00000, 0x00000008), 0xbce00000, 0x00000000, STR(__LINE__)); // 0x1p+0 + -0x1.0000000000008p+0 = -0x1p-49
  comp64(double_of_bits(0x40310000, 0x00000000) + double_of_bits(0xc0300000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x1.1p+4 + -0x1p+4 = 0x1p+0
  comp64(double_of_bits(0xc0300000, 0x00000000) + double_of_bits(0x40310000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // -0x1p+4 + 0x1.1p+4 = 0x1p+0
}

void f76(void) {
  comp64(double_of_bits(0xc0310000, 0x00000000) + double_of_bits(0x40300000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x1.1p+4 + 0x1p+4 = -0x1p+0
  comp64(double_of_bits(0x40300000, 0x00000000) + double_of_bits(0xc0310000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // 0x1p+4 + -0x1.1p+4 = -0x1p+0
  comp64(double_of_bits(0x40300000, 0x00000000) + double_of_bits(0xc0310000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // 0x1p+4 + -0x1.1p+4 = -0x1p+0
  comp64(double_of_bits(0xc0310000, 0x00000000) + double_of_bits(0x40300000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x1.1p+4 + 0x1p+4 = -0x1p+0
  comp64(double_of_bits(0x40220000, 0x00000000) + double_of_bits(0xc0200000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x1.2p+3 + -0x1p+3 = 0x1p+0
  comp64(double_of_bits(0xc0200000, 0x00000000) + double_of_bits(0x40220000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // -0x1p+3 + 0x1.2p+3 = 0x1p+0
  comp64(double_of_bits(0xc0220000, 0x00000000) + double_of_bits(0x40200000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x1.2p+3 + 0x1p+3 = -0x1p+0
  comp64(double_of_bits(0x40200000, 0x00000000) + double_of_bits(0xc0220000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // 0x1p+3 + -0x1.2p+3 = -0x1p+0
  comp64(double_of_bits(0x40140000, 0x00000000) + double_of_bits(0xc0100000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x1.4p+2 + -0x1p+2 = 0x1p+0
  comp64(double_of_bits(0xc0100000, 0x00000000) + double_of_bits(0x40140000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // -0x1p+2 + 0x1.4p+2 = 0x1p+0
}

void f77(void) {
  comp64(double_of_bits(0xc0140000, 0x00000000) + double_of_bits(0x40100000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x1.4p+2 + 0x1p+2 = -0x1p+0
  comp64(double_of_bits(0x40100000, 0x00000000) + double_of_bits(0xc0140000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // 0x1p+2 + -0x1.4p+2 = -0x1p+0
  comp64(double_of_bits(0x40080000, 0x00000000) + double_of_bits(0xc0000000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 + -0x1p+1 = 0x1p+0
  comp64(double_of_bits(0xc0000000, 0x00000000) + double_of_bits(0x40080000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // -0x1p+1 + 0x1.8p+1 = 0x1p+0
  comp64(double_of_bits(0xc0080000, 0x00000000) + double_of_bits(0x40000000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 + 0x1p+1 = -0x1p+0
  comp64(double_of_bits(0x40000000, 0x00000000) + double_of_bits(0xc0080000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // 0x1p+1 + -0x1.8p+1 = -0x1p+0
  comp64(double_of_bits(0x40000000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x40080000, 0x00000000, STR(__LINE__)); // 0x1p+1 + 0x1.0000000000001p+0 = 0x1.8p+1
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x40000000, 0x00000000), 0x40080000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1p+1 = 0x1.8p+1
  comp64(double_of_bits(0x40240000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x40260000, 0x00000000, STR(__LINE__)); // 0x1.4p+3 + 0x1.0000000000001p+0 = 0x1.6p+3
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x40240000, 0x00000000), 0x40260000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.4p+3 = 0x1.6p+3
}

void f78(void) {
  comp64(double_of_bits(0x40330000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x40340000, 0x00000000, STR(__LINE__)); // 0x1.3p+4 + 0x1.0000000000001p+0 = 0x1.4p+4
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x40330000, 0x00000000), 0x40340000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.3p+4 = 0x1.4p+4
  comp64(double_of_bits(0x40400000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x40408000, 0x00000000, STR(__LINE__)); // 0x1p+5 + 0x1.0000000000001p+0 = 0x1.08p+5
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x40400000, 0x00000000), 0x40408000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1p+5 = 0x1.08p+5
  comp64(double_of_bits(0x40504000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x40508000, 0x00000000, STR(__LINE__)); // 0x1.04p+6 + 0x1.0000000000001p+0 = 0x1.08p+6
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x40504000, 0x00000000), 0x40508000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.04p+6 = 0x1.08p+6
  comp64(double_of_bits(0x4060a000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x4060c000, 0x00000000, STR(__LINE__)); // 0x1.0ap+7 + 0x1.0000000000001p+0 = 0x1.0cp+7
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x4060a000, 0x00000000), 0x4060c000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.0ap+7 = 0x1.0cp+7
  comp64(double_of_bits(0x40704000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x40705000, 0x00000000, STR(__LINE__)); // 0x1.04p+8 + 0x1.0000000000001p+0 = 0x1.05p+8
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x40704000, 0x00000000), 0x40705000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.04p+8 = 0x1.05p+8
}

void f79(void) {
  comp64(double_of_bits(0x4080a800, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x4080b000, 0x00000000, STR(__LINE__)); // 0x1.0a8p+9 + 0x1.0000000000001p+0 = 0x1.0bp+9
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x4080a800, 0x00000000), 0x4080b000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.0a8p+9 = 0x1.0bp+9
  comp64(double_of_bits(0x40901400, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x40901800, 0x00000000, STR(__LINE__)); // 0x1.014p+10 + 0x1.0000000000001p+0 = 0x1.018p+10
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x40901400, 0x00000000), 0x40901800, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.014p+10 = 0x1.018p+10
  comp64(double_of_bits(0x40a00000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x40a00200, 0x00000000, STR(__LINE__)); // 0x1p+11 + 0x1.0000000000001p+0 = 0x1.002p+11
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x40a00000, 0x00000000), 0x40a00200, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1p+11 = 0x1.002p+11
  comp64(double_of_bits(0x40b00100, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x40b00200, 0x00000000, STR(__LINE__)); // 0x1.001p+12 + 0x1.0000000000001p+0 = 0x1.002p+12
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x40b00100, 0x00000000), 0x40b00200, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.001p+12 = 0x1.002p+12
  comp64(double_of_bits(0x40c00080, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x40c00100, 0x00000000, STR(__LINE__)); // 0x1.0008p+13 + 0x1.0000000000001p+0 = 0x1.001p+13
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x40c00080, 0x00000000), 0x40c00100, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.0008p+13 = 0x1.001p+13
}

void f80(void) {
  comp64(double_of_bits(0x40d00000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x40d00040, 0x00000000, STR(__LINE__)); // 0x1p+14 + 0x1.0000000000001p+0 = 0x1.0004p+14
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x40d00000, 0x00000000), 0x40d00040, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1p+14 = 0x1.0004p+14
  comp64(double_of_bits(0x40e00180, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x40e001a0, 0x00000000, STR(__LINE__)); // 0x1.0018p+15 + 0x1.0000000000001p+0 = 0x1.001ap+15
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x40e00180, 0x00000000), 0x40e001a0, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.0018p+15 = 0x1.001ap+15
  comp64(double_of_bits(0x40f00130, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x40f00140, 0x00000000, STR(__LINE__)); // 0x1.0013p+16 + 0x1.0000000000001p+0 = 0x1.0014p+16
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x40f00130, 0x00000000), 0x40f00140, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.0013p+16 = 0x1.0014p+16
  comp64(double_of_bits(0x41000000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x41000008, 0x00000000, STR(__LINE__)); // 0x1p+17 + 0x1.0000000000001p+0 = 0x1.00008p+17
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x41000000, 0x00000000), 0x41000008, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1p+17 = 0x1.00008p+17
  comp64(double_of_bits(0x41100d60, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x41100d64, 0x00000000, STR(__LINE__)); // 0x1.00d6p+18 + 0x1.0000000000001p+0 = 0x1.00d64p+18
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x41100d60, 0x00000000), 0x41100d64, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.00d6p+18 = 0x1.00d64p+18
}

void f81(void) {
  comp64(double_of_bits(0x41200590, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x41200592, 0x00000000, STR(__LINE__)); // 0x1.0059p+19 + 0x1.0000000000001p+0 = 0x1.00592p+19
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x41200590, 0x00000000), 0x41200592, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.0059p+19 = 0x1.00592p+19
  comp64(double_of_bits(0x41300590, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x41300591, 0x00000000, STR(__LINE__)); // 0x1.0059p+20 + 0x1.0000000000001p+0 = 0x1.00591p+20
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x41300590, 0x00000000), 0x41300591, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.0059p+20 = 0x1.00591p+20
  comp64(double_of_bits(0x413fee9c, 0x00000000) + double_of_bits(0x3ff00000, 0x00000001), 0x413fee9d, 0x00000000, STR(__LINE__)); // 0x1.fee9cp+20 + 0x1.0000000000001p+0 = 0x1.fee9dp+20
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x413fee9c, 0x00000000), 0x413fee9d, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.fee9cp+20 = 0x1.fee9dp+20
  comp64(double_of_bits(0x41500000, 0x40000000) + double_of_bits(0x3ff00000, 0x00000001), 0x41500000, 0x80000000, STR(__LINE__)); // 0x1.000004p+22 + 0x1.0000000000001p+0 = 0x1.000008p+22
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x41500000, 0x40000000), 0x41500000, 0x80000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.000004p+22 = 0x1.000008p+22
  comp64(double_of_bits(0x41600000, 0x20000000) + double_of_bits(0x3ff00000, 0x00000001), 0x41600000, 0x40000000, STR(__LINE__)); // 0x1.000002p+23 + 0x1.0000000000001p+0 = 0x1.000004p+23
  comp64(double_of_bits(0x3ff00000, 0x00000001) + double_of_bits(0x41600000, 0x20000000), 0x41600000, 0x40000000, STR(__LINE__)); // 0x1.0000000000001p+0 + 0x1.000002p+23 = 0x1.000004p+23
}

void f82(void) {
  comp64(double_of_bits(0x43400000, 0x00000000) + double_of_bits(0x40100000, 0x00000001), 0x43400000, 0x00000002, STR(__LINE__)); // 0x1p+53 + 0x1.0000000000001p+2 = 0x1.0000000000002p+53
  comp64(double_of_bits(0x40100000, 0x00000001) + double_of_bits(0x43400000, 0x00000000), 0x43400000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+2 + 0x1p+53 = 0x1.0000000000002p+53
  comp64(double_of_bits(0x43400000, 0x00000000) + double_of_bits(0x40000000, 0x00000001), 0x43400000, 0x00000001, STR(__LINE__)); // 0x1p+53 + 0x1.0000000000001p+1 = 0x1.0000000000001p+53
  comp64(double_of_bits(0x40000000, 0x00000001) + double_of_bits(0x43400000, 0x00000000), 0x43400000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p+1 + 0x1p+53 = 0x1.0000000000001p+53
  comp64(double_of_bits(0xc0000000, 0x00000000) + double_of_bits(0xbff00000, 0x00000001), 0xc0080000, 0x00000000, STR(__LINE__)); // -0x1p+1 + -0x1.0000000000001p+0 = -0x1.8p+1
  comp64(double_of_bits(0xbff00000, 0x00000001) + double_of_bits(0xc0000000, 0x00000000), 0xc0080000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+0 + -0x1p+1 = -0x1.8p+1
  comp64(double_of_bits(0xc3400000, 0x00000000) + double_of_bits(0xc0100000, 0x00000001), 0xc3400000, 0x00000002, STR(__LINE__)); // -0x1p+53 + -0x1.0000000000001p+2 = -0x1.0000000000002p+53
  comp64(double_of_bits(0xc0100000, 0x00000001) + double_of_bits(0xc3400000, 0x00000000), 0xc3400000, 0x00000002, STR(__LINE__)); // -0x1.0000000000001p+2 + -0x1p+53 = -0x1.0000000000002p+53
  comp64(double_of_bits(0xc3400000, 0x00000000) + double_of_bits(0xc0000000, 0x00000001), 0xc3400000, 0x00000001, STR(__LINE__)); // -0x1p+53 + -0x1.0000000000001p+1 = -0x1.0000000000001p+53
  comp64(double_of_bits(0xc0000000, 0x00000001) + double_of_bits(0xc3400000, 0x00000000), 0xc3400000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p+1 + -0x1p+53 = -0x1.0000000000001p+53
}

void f83(void) {
  comp64(double_of_bits(0x40dfffc0, 0x00000000) + double_of_bits(0x3ff00000, 0x00000000), 0x40e00000, 0x00000000, STR(__LINE__)); // 0x1.fffcp+14 + 0x1p+0 = 0x1p+15
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x40dfffc0, 0x00000000), 0x40e00000, 0x00000000, STR(__LINE__)); // 0x1p+0 + 0x1.fffcp+14 = 0x1p+15
  comp64(double_of_bits(0xc0dfffc0, 0x00000000) + double_of_bits(0xbff00000, 0x00000000), 0xc0e00000, 0x00000000, STR(__LINE__)); // -0x1.fffcp+14 + -0x1p+0 = -0x1p+15
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0xc0dfffc0, 0x00000000), 0xc0e00000, 0x00000000, STR(__LINE__)); // -0x1p+0 + -0x1.fffcp+14 = -0x1p+15
  comp64(double_of_bits(0x433fffff, 0xffffffff) + double_of_bits(0x3ff00000, 0x00000000), 0x43400000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+52 + 0x1p+0 = 0x1p+53
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x433fffff, 0xffffffff), 0x43400000, 0x00000000, STR(__LINE__)); // 0x1p+0 + 0x1.fffffffffffffp+52 = 0x1p+53
  comp64(double_of_bits(0xc33fffff, 0xffffffff) + double_of_bits(0xbff00000, 0x00000000), 0xc3400000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+52 + -0x1p+0 = -0x1p+53
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0xc33fffff, 0xffffffff), 0xc3400000, 0x00000000, STR(__LINE__)); // -0x1p+0 + -0x1.fffffffffffffp+52 = -0x1p+53
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x402e0000, 0x00000000), 0x40300000, 0x00000000, STR(__LINE__)); // 0x1p+0 + 0x1.ep+3 = 0x1p+4
  comp64(double_of_bits(0x402e0000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000000), 0x40300000, 0x00000000, STR(__LINE__)); // 0x1.ep+3 + 0x1p+0 = 0x1p+4
}

void f84(void) {
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0xc02e0000, 0x00000000), 0xc0300000, 0x00000000, STR(__LINE__)); // -0x1p+0 + -0x1.ep+3 = -0x1p+4
  comp64(double_of_bits(0xc02e0000, 0x00000000) + double_of_bits(0xbff00000, 0x00000000), 0xc0300000, 0x00000000, STR(__LINE__)); // -0x1.ep+3 + -0x1p+0 = -0x1p+4
  comp64(double_of_bits(0x40000000, 0x00000000) + double_of_bits(0x433fffff, 0xfffffffb), 0x433fffff, 0xfffffffd, STR(__LINE__)); // 0x1p+1 + 0x1.ffffffffffffbp+52 = 0x1.ffffffffffffdp+52
  comp64(double_of_bits(0x433fffff, 0xfffffffb) + double_of_bits(0x40000000, 0x00000000), 0x433fffff, 0xfffffffd, STR(__LINE__)); // 0x1.ffffffffffffbp+52 + 0x1p+1 = 0x1.ffffffffffffdp+52
  comp64(double_of_bits(0xc0000000, 0x00000000) + double_of_bits(0xc33fffff, 0xfffffffb), 0xc33fffff, 0xfffffffd, STR(__LINE__)); // -0x1p+1 + -0x1.ffffffffffffbp+52 = -0x1.ffffffffffffdp+52
  comp64(double_of_bits(0xc33fffff, 0xfffffffb) + double_of_bits(0xc0000000, 0x00000000), 0xc33fffff, 0xfffffffd, STR(__LINE__)); // -0x1.ffffffffffffbp+52 + -0x1p+1 = -0x1.ffffffffffffdp+52
  comp64(double_of_bits(0x000fffff, 0xffffffff) + double_of_bits(0x00000000, 0x00000001), 0x00100000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 + 0x0.0000000000001p-1022 = 0x1p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x000fffff, 0xffffffff), 0x00100000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 + 0x0.fffffffffffffp-1022 = 0x1p-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) + double_of_bits(0x80000000, 0x00000001), 0x80100000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 + -0x0.0000000000001p-1022 = -0x1p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0x800fffff, 0xffffffff), 0x80100000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 + -0x0.fffffffffffffp-1022 = -0x1p-1022
}

void f85(void) {
  comp64(double_of_bits(0x000e0000, 0x00000000) + double_of_bits(0x00020000, 0x00000000), 0x00100000, 0x00000000, STR(__LINE__)); // 0x0.ep-1022 + 0x0.2p-1022 = 0x1p-1022
  comp64(double_of_bits(0x00020000, 0x00000000) + double_of_bits(0x000e0000, 0x00000000), 0x00100000, 0x00000000, STR(__LINE__)); // 0x0.2p-1022 + 0x0.ep-1022 = 0x1p-1022
  comp64(double_of_bits(0x800e0000, 0x00000000) + double_of_bits(0x80020000, 0x00000000), 0x80100000, 0x00000000, STR(__LINE__)); // -0x0.ep-1022 + -0x0.2p-1022 = -0x1p-1022
  comp64(double_of_bits(0x80020000, 0x00000000) + double_of_bits(0x800e0000, 0x00000000), 0x80100000, 0x00000000, STR(__LINE__)); // -0x0.2p-1022 + -0x0.ep-1022 = -0x1p-1022
  comp64(double_of_bits(0x40000000, 0x00000000) + double_of_bits(0x40dfff40, 0x00000000), 0x40dfffc0, 0x00000000, STR(__LINE__)); // 0x1p+1 + 0x1.fff4p+14 = 0x1.fffcp+14
  comp64(double_of_bits(0x40dfff40, 0x00000000) + double_of_bits(0x40000000, 0x00000000), 0x40dfffc0, 0x00000000, STR(__LINE__)); // 0x1.fff4p+14 + 0x1p+1 = 0x1.fffcp+14
  comp64(double_of_bits(0xc0000000, 0x00000000) + double_of_bits(0xc0dfff40, 0x00000000), 0xc0dfffc0, 0x00000000, STR(__LINE__)); // -0x1p+1 + -0x1.fff4p+14 = -0x1.fffcp+14
  comp64(double_of_bits(0xc0dfff40, 0x00000000) + double_of_bits(0xc0000000, 0x00000000), 0xc0dfffc0, 0x00000000, STR(__LINE__)); // -0x1.fff4p+14 + -0x1p+1 = -0x1.fffcp+14
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x433fffff, 0xfffffffe), 0x433fffff, 0xffffffff, STR(__LINE__)); // 0x1p+0 + 0x1.ffffffffffffep+52 = 0x1.fffffffffffffp+52
  comp64(double_of_bits(0x433fffff, 0xfffffffe) + double_of_bits(0x3ff00000, 0x00000000), 0x433fffff, 0xffffffff, STR(__LINE__)); // 0x1.ffffffffffffep+52 + 0x1p+0 = 0x1.fffffffffffffp+52
}

void f86(void) {
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0xc33fffff, 0xfffffffe), 0xc33fffff, 0xffffffff, STR(__LINE__)); // -0x1p+0 + -0x1.ffffffffffffep+52 = -0x1.fffffffffffffp+52
  comp64(double_of_bits(0xc33fffff, 0xfffffffe) + double_of_bits(0xbff00000, 0x00000000), 0xc33fffff, 0xffffffff, STR(__LINE__)); // -0x1.ffffffffffffep+52 + -0x1p+0 = -0x1.fffffffffffffp+52
  comp64(double_of_bits(0x40080000, 0x00000000) + double_of_bits(0x433fffff, 0xfffffffa), 0x433fffff, 0xfffffffd, STR(__LINE__)); // 0x1.8p+1 + 0x1.ffffffffffffap+52 = 0x1.ffffffffffffdp+52
  comp64(double_of_bits(0x433fffff, 0xfffffffa) + double_of_bits(0x40080000, 0x00000000), 0x433fffff, 0xfffffffd, STR(__LINE__)); // 0x1.ffffffffffffap+52 + 0x1.8p+1 = 0x1.ffffffffffffdp+52
  comp64(double_of_bits(0xc0080000, 0x00000000) + double_of_bits(0xc33fffff, 0xfffffffa), 0xc33fffff, 0xfffffffd, STR(__LINE__)); // -0x1.8p+1 + -0x1.ffffffffffffap+52 = -0x1.ffffffffffffdp+52
  comp64(double_of_bits(0xc33fffff, 0xfffffffa) + double_of_bits(0xc0080000, 0x00000000), 0xc33fffff, 0xfffffffd, STR(__LINE__)); // -0x1.ffffffffffffap+52 + -0x1.8p+1 = -0x1.ffffffffffffdp+52
  comp64(double_of_bits(0x3ff00000, 0x00000000) + double_of_bits(0x402c0000, 0x00000000), 0x402e0000, 0x00000000, STR(__LINE__)); // 0x1p+0 + 0x1.cp+3 = 0x1.ep+3
  comp64(double_of_bits(0x402c0000, 0x00000000) + double_of_bits(0x3ff00000, 0x00000000), 0x402e0000, 0x00000000, STR(__LINE__)); // 0x1.cp+3 + 0x1p+0 = 0x1.ep+3
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0xc02c0000, 0x00000000), 0xc02e0000, 0x00000000, STR(__LINE__)); // -0x1p+0 + -0x1.cp+3 = -0x1.ep+3
  comp64(double_of_bits(0xc02c0000, 0x00000000) + double_of_bits(0xbff00000, 0x00000000), 0xc02e0000, 0x00000000, STR(__LINE__)); // -0x1.cp+3 + -0x1p+0 = -0x1.ep+3
}

void f87(void) {
  comp64(double_of_bits(0x40000000, 0x00000000) + double_of_bits(0x402a0000, 0x00000000), 0x402e0000, 0x00000000, STR(__LINE__)); // 0x1p+1 + 0x1.ap+3 = 0x1.ep+3
  comp64(double_of_bits(0x402a0000, 0x00000000) + double_of_bits(0x40000000, 0x00000000), 0x402e0000, 0x00000000, STR(__LINE__)); // 0x1.ap+3 + 0x1p+1 = 0x1.ep+3
  comp64(double_of_bits(0xc0000000, 0x00000000) + double_of_bits(0xc02a0000, 0x00000000), 0xc02e0000, 0x00000000, STR(__LINE__)); // -0x1p+1 + -0x1.ap+3 = -0x1.ep+3
  comp64(double_of_bits(0xc02a0000, 0x00000000) + double_of_bits(0xc0000000, 0x00000000), 0xc02e0000, 0x00000000, STR(__LINE__)); // -0x1.ap+3 + -0x1p+1 = -0x1.ep+3
  comp64(double_of_bits(0x000fffff, 0xfffffffe) + double_of_bits(0x00000000, 0x00000001), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x0.ffffffffffffep-1022 + 0x0.0000000000001p-1022 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x00000000, 0x00000001) + double_of_bits(0x000fffff, 0xfffffffe), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x0.0000000000001p-1022 + 0x0.ffffffffffffep-1022 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x800fffff, 0xfffffffe) + double_of_bits(0x80000000, 0x00000001), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x0.ffffffffffffep-1022 + -0x0.0000000000001p-1022 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x80000000, 0x00000001) + double_of_bits(0x800fffff, 0xfffffffe), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x0.0000000000001p-1022 + -0x0.ffffffffffffep-1022 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x000c0000, 0x00000000) + double_of_bits(0x00020000, 0x00000000), 0x000e0000, 0x00000000, STR(__LINE__)); // 0x0.cp-1022 + 0x0.2p-1022 = 0x0.ep-1022
  comp64(double_of_bits(0x00020000, 0x00000000) + double_of_bits(0x000c0000, 0x00000000), 0x000e0000, 0x00000000, STR(__LINE__)); // 0x0.2p-1022 + 0x0.cp-1022 = 0x0.ep-1022
}

void f88(void) {
  comp64(double_of_bits(0x800c0000, 0x00000000) + double_of_bits(0x80020000, 0x00000000), 0x800e0000, 0x00000000, STR(__LINE__)); // -0x0.cp-1022 + -0x0.2p-1022 = -0x0.ep-1022
  comp64(double_of_bits(0x80020000, 0x00000000) + double_of_bits(0x800c0000, 0x00000000), 0x800e0000, 0x00000000, STR(__LINE__)); // -0x0.2p-1022 + -0x0.cp-1022 = -0x0.ep-1022
  comp64(double_of_bits(0xffdfffff, 0xffffffff) + double_of_bits(0xbff00000, 0x00000000), 0xffdfffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1022 + -0x1p+0 = -0x1.fffffffffffffp+1022
  comp64(double_of_bits(0xbff00000, 0x00000000) + double_of_bits(0xffdfffff, 0xffffffff), 0xffdfffff, 0xffffffff, STR(__LINE__)); // -0x1p+0 + -0x1.fffffffffffffp+1022 = -0x1.fffffffffffffp+1022
  comp64(double_of_bits(0x40e00000, 0x00000000) / double_of_bits(0x40400000, 0x00000000), 0x40900000, 0x00000000, STR(__LINE__)); // 0x1p+15 / 0x1p+5 = 0x1p+10
  comp64(double_of_bits(0xc0e00000, 0x00000000) / double_of_bits(0xc0400000, 0x00000000), 0x40900000, 0x00000000, STR(__LINE__)); // -0x1p+15 / -0x1p+5 = 0x1p+10
  comp64(double_of_bits(0x40e00000, 0x00000000) / double_of_bits(0xc0400000, 0x00000000), 0xc0900000, 0x00000000, STR(__LINE__)); // 0x1p+15 / -0x1p+5 = -0x1p+10
  comp64(double_of_bits(0xc0e00000, 0x00000000) / double_of_bits(0x40400000, 0x00000000), 0xc0900000, 0x00000000, STR(__LINE__)); // -0x1p+15 / 0x1p+5 = -0x1p+10
  comp64(double_of_bits(0x47700000, 0x00000000) / double_of_bits(0x41300000, 0x00000000), 0x46300000, 0x00000000, STR(__LINE__)); // 0x1p+120 / 0x1p+20 = 0x1p+100
  comp64(double_of_bits(0xc7700000, 0x00000000) / double_of_bits(0xc1300000, 0x00000000), 0x46300000, 0x00000000, STR(__LINE__)); // -0x1p+120 / -0x1p+20 = 0x1p+100
}

void f89(void) {
  comp64(double_of_bits(0xc7700000, 0x00000000) / double_of_bits(0x41300000, 0x00000000), 0xc6300000, 0x00000000, STR(__LINE__)); // -0x1p+120 / 0x1p+20 = -0x1p+100
  comp64(double_of_bits(0x47700000, 0x00000000) / double_of_bits(0xc1300000, 0x00000000), 0xc6300000, 0x00000000, STR(__LINE__)); // 0x1p+120 / -0x1p+20 = -0x1p+100
  comp64(double_of_bits(0x43e00000, 0x00000000) / double_of_bits(0x41600000, 0x00000000), 0x42700000, 0x00000000, STR(__LINE__)); // 0x1p+63 / 0x1p+23 = 0x1p+40
  comp64(double_of_bits(0xc3e00000, 0x00000000) / double_of_bits(0xc1600000, 0x00000000), 0x42700000, 0x00000000, STR(__LINE__)); // -0x1p+63 / -0x1p+23 = 0x1p+40
  comp64(double_of_bits(0xc3e00000, 0x00000000) / double_of_bits(0x41600000, 0x00000000), 0xc2700000, 0x00000000, STR(__LINE__)); // -0x1p+63 / 0x1p+23 = -0x1p+40
  comp64(double_of_bits(0x43e00000, 0x00000000) / double_of_bits(0xc1600000, 0x00000000), 0xc2700000, 0x00000000, STR(__LINE__)); // 0x1p+63 / -0x1p+23 = -0x1p+40
  comp64(double_of_bits(0x42e00000, 0x00000000) / double_of_bits(0x40c00000, 0x00000000), 0x42100000, 0x00000000, STR(__LINE__)); // 0x1p+47 / 0x1p+13 = 0x1p+34
  comp64(double_of_bits(0xc2e00000, 0x00000000) / double_of_bits(0xc0c00000, 0x00000000), 0x42100000, 0x00000000, STR(__LINE__)); // -0x1p+47 / -0x1p+13 = 0x1p+34
  comp64(double_of_bits(0xc2e00000, 0x00000000) / double_of_bits(0x40c00000, 0x00000000), 0xc2100000, 0x00000000, STR(__LINE__)); // -0x1p+47 / 0x1p+13 = -0x1p+34
  comp64(double_of_bits(0x42e00000, 0x00000000) / double_of_bits(0xc0c00000, 0x00000000), 0xc2100000, 0x00000000, STR(__LINE__)); // 0x1p+47 / -0x1p+13 = -0x1p+34
}

void f90(void) {
  comp64(double_of_bits(0x40440000, 0x00000000) / double_of_bits(0x40240000, 0x00000000), 0x40100000, 0x00000000, STR(__LINE__)); // 0x1.4p+5 / 0x1.4p+3 = 0x1p+2
  comp64(double_of_bits(0xc0440000, 0x00000000) / double_of_bits(0xc0240000, 0x00000000), 0x40100000, 0x00000000, STR(__LINE__)); // -0x1.4p+5 / -0x1.4p+3 = 0x1p+2
  comp64(double_of_bits(0xc0440000, 0x00000000) / double_of_bits(0x40240000, 0x00000000), 0xc0100000, 0x00000000, STR(__LINE__)); // -0x1.4p+5 / 0x1.4p+3 = -0x1p+2
  comp64(double_of_bits(0x40440000, 0x00000000) / double_of_bits(0xc0240000, 0x00000000), 0xc0100000, 0x00000000, STR(__LINE__)); // 0x1.4p+5 / -0x1.4p+3 = -0x1p+2
  comp64(double_of_bits(0x40dffe00, 0x00000000) / double_of_bits(0x40240000, 0x00000000), 0x40a99800, 0x00000000, STR(__LINE__)); // 0x1.ffep+14 / 0x1.4p+3 = 0x1.998p+11
  comp64(double_of_bits(0x40c38800, 0x00000000) / double_of_bits(0x40240000, 0x00000000), 0x408f4000, 0x00000000, STR(__LINE__)); // 0x1.388p+13 / 0x1.4p+3 = 0x1.f4p+9
  comp64(double_of_bits(0x40c38800, 0x00000000) / double_of_bits(0x40590000, 0x00000000), 0x40590000, 0x00000000, STR(__LINE__)); // 0x1.388p+13 / 0x1.9p+6 = 0x1.9p+6
  comp64(double_of_bits(0x40c38800, 0x00000000) / double_of_bits(0x408f4000, 0x00000000), 0x40240000, 0x00000000, STR(__LINE__)); // 0x1.388p+13 / 0x1.f4p+9 = 0x1.4p+3
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0x3ff00000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x1p+0 / 0x1p+0 = 0x1p+0
  comp64(double_of_bits(0xbff00000, 0x00000000) / double_of_bits(0xbff00000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // -0x1p+0 / -0x1p+0 = 0x1p+0
}

void f91(void) {
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0xbff00000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // 0x1p+0 / -0x1p+0 = -0x1p+0
  comp64(double_of_bits(0xbff00000, 0x00000000) / double_of_bits(0x3ff00000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x1p+0 / 0x1p+0 = -0x1p+0
  comp64(double_of_bits(0x40000000, 0x00000000) / double_of_bits(0x3ff00000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // 0x1p+1 / 0x1p+0 = 0x1p+1
  comp64(double_of_bits(0xc0000000, 0x00000000) / double_of_bits(0xbff00000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // -0x1p+1 / -0x1p+0 = 0x1p+1
  comp64(double_of_bits(0xc0000000, 0x00000000) / double_of_bits(0x3ff00000, 0x00000000), 0xc0000000, 0x00000000, STR(__LINE__)); // -0x1p+1 / 0x1p+0 = -0x1p+1
  comp64(double_of_bits(0x40000000, 0x00000000) / double_of_bits(0xbff00000, 0x00000000), 0xc0000000, 0x00000000, STR(__LINE__)); // 0x1p+1 / -0x1p+0 = -0x1p+1
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0x3ff00000, 0x00000000), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / 0x1p+0 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0xbff00000, 0x00000000), 0x800fffff, 0xffffffff, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / -0x1p+0 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0x3ff00000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000001p-1022 / 0x1p+0 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0xbff00000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000001p-1022 / -0x1p+0 = 0x0.0000000000001p-1022
}

void f92(void) {
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0x3ff00000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000001p-1022 / 0x1p+0 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0xbff00000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000001p-1022 / -0x1p+0 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x7fe00000, 0x00000000) / double_of_bits(0x40000000, 0x00000000), 0x7fd00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 / 0x1p+1 = 0x1p+1022
  comp64(double_of_bits(0x7fe00000, 0x00000000) / double_of_bits(0xc0000000, 0x00000000), 0xffd00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 / -0x1p+1 = -0x1p+1022
  comp64(double_of_bits(0xffdfffff, 0xffffffff) / double_of_bits(0x40000000, 0x00000000), 0xffcfffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1022 / 0x1p+1 = -0x1.fffffffffffffp+1021
  comp64(double_of_bits(0x7fdfffff, 0xfffffffd) / double_of_bits(0xc0000000, 0x00000000), 0xffcfffff, 0xfffffffd, STR(__LINE__)); // 0x1.ffffffffffffdp+1022 / -0x1p+1 = -0x1.ffffffffffffdp+1021
  comp64(double_of_bits(0x7fefffff, 0xffffffff) / double_of_bits(0xc0000000, 0x00000000), 0xffdfffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1023 / -0x1p+1 = -0x1.fffffffffffffp+1022
  comp64(double_of_bits(0x40200000, 0x00000000) / double_of_bits(0x40000000, 0x00000000), 0x40100000, 0x00000000, STR(__LINE__)); // 0x1p+3 / 0x1p+1 = 0x1p+2
  comp64(double_of_bits(0xc0200000, 0x00000000) / double_of_bits(0xc0000000, 0x00000000), 0x40100000, 0x00000000, STR(__LINE__)); // -0x1p+3 / -0x1p+1 = 0x1p+2
  comp64(double_of_bits(0xc0200000, 0x00000000) / double_of_bits(0x40000000, 0x00000000), 0xc0100000, 0x00000000, STR(__LINE__)); // -0x1p+3 / 0x1p+1 = -0x1p+2
}

void f93(void) {
  comp64(double_of_bits(0x40200000, 0x00000000) / double_of_bits(0xc0000000, 0x00000000), 0xc0100000, 0x00000000, STR(__LINE__)); // 0x1p+3 / -0x1p+1 = -0x1p+2
  comp64(double_of_bits(0x00200000, 0x00000000) / double_of_bits(0xc0000000, 0x00000000), 0x80100000, 0x00000000, STR(__LINE__)); // 0x1p-1021 / -0x1p+1 = -0x1p-1022
  comp64(double_of_bits(0x00200000, 0x00000003) / double_of_bits(0xc0000000, 0x00000000), 0x80100000, 0x00000003, STR(__LINE__)); // 0x1.0000000000003p-1021 / -0x1p+1 = -0x1.0000000000003p-1022
  comp64(double_of_bits(0x00200000, 0x00000001) / double_of_bits(0xc0000000, 0x00000000), 0x80100000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p-1021 / -0x1p+1 = -0x1.0000000000001p-1022
  comp64(double_of_bits(0x001fffff, 0xfffffffe) / double_of_bits(0x40000000, 0x00000000), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x1.ffffffffffffep-1022 / 0x1p+1 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x00080000, 0x00000000) / double_of_bits(0x40000000, 0x00000000), 0x00040000, 0x00000000, STR(__LINE__)); // 0x0.8p-1022 / 0x1p+1 = 0x0.4p-1022
  comp64(double_of_bits(0x80080000, 0x00000000) / double_of_bits(0xc0000000, 0x00000000), 0x00040000, 0x00000000, STR(__LINE__)); // -0x0.8p-1022 / -0x1p+1 = 0x0.4p-1022
  comp64(double_of_bits(0x80080000, 0x00000000) / double_of_bits(0x40000000, 0x00000000), 0x80040000, 0x00000000, STR(__LINE__)); // -0x0.8p-1022 / 0x1p+1 = -0x0.4p-1022
  comp64(double_of_bits(0x00080000, 0x00000000) / double_of_bits(0xc0000000, 0x00000000), 0x80040000, 0x00000000, STR(__LINE__)); // 0x0.8p-1022 / -0x1p+1 = -0x0.4p-1022
  comp64(double_of_bits(0x00000000, 0x00000002) / double_of_bits(0x40000000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000002p-1022 / 0x1p+1 = 0x0.0000000000001p-1022
}

void f94(void) {
  comp64(double_of_bits(0x80000000, 0x00000002) / double_of_bits(0xc0000000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000002p-1022 / -0x1p+1 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000002) / double_of_bits(0x40000000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000002p-1022 / 0x1p+1 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000002) / double_of_bits(0xc0000000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000002p-1022 / -0x1p+1 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x7fefffff, 0xffffffff) / double_of_bits(0x7fdfffff, 0xffffffff), 0x40000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 / 0x1.fffffffffffffp+1022 = 0x1p+1
  comp64(double_of_bits(0xffe00000, 0x00000001) / double_of_bits(0x7fd00000, 0x00000001), 0xc0000000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+1023 / 0x1.0000000000001p+1022 = -0x1p+1
  comp64(double_of_bits(0x7fe00000, 0x00000003) / double_of_bits(0xffd00000, 0x00000003), 0xc0000000, 0x00000000, STR(__LINE__)); // 0x1.0000000000003p+1023 / -0x1.0000000000003p+1022 = -0x1p+1
  comp64(double_of_bits(0x00200000, 0x00000000) / double_of_bits(0x00100000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // 0x1p-1021 / 0x1p-1022 = 0x1p+1
  comp64(double_of_bits(0x80200000, 0x00000001) / double_of_bits(0x00100000, 0x00000001), 0xc0000000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p-1021 / 0x1.0000000000001p-1022 = -0x1p+1
  comp64(double_of_bits(0x00200000, 0x00000001) / double_of_bits(0x00100000, 0x00000001), 0x40000000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p-1021 / 0x1.0000000000001p-1022 = 0x1p+1
  comp64(double_of_bits(0x00200000, 0x00000003) / double_of_bits(0x80100000, 0x00000003), 0xc0000000, 0x00000000, STR(__LINE__)); // 0x1.0000000000003p-1021 / -0x1.0000000000003p-1022 = -0x1p+1
}

void f95(void) {
  comp64(double_of_bits(0x80200000, 0x00000005) / double_of_bits(0x00100000, 0x00000005), 0xc0000000, 0x00000000, STR(__LINE__)); // -0x1.0000000000005p-1021 / 0x1.0000000000005p-1022 = -0x1p+1
  comp64(double_of_bits(0x00080000, 0x00000000) / double_of_bits(0x00040000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // 0x0.8p-1022 / 0x0.4p-1022 = 0x1p+1
  comp64(double_of_bits(0x80080000, 0x00000000) / double_of_bits(0x80040000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // -0x0.8p-1022 / -0x0.4p-1022 = 0x1p+1
  comp64(double_of_bits(0x80080000, 0x00000000) / double_of_bits(0x00040000, 0x00000000), 0xc0000000, 0x00000000, STR(__LINE__)); // -0x0.8p-1022 / 0x0.4p-1022 = -0x1p+1
  comp64(double_of_bits(0x00080000, 0x00000000) / double_of_bits(0x80040000, 0x00000000), 0xc0000000, 0x00000000, STR(__LINE__)); // 0x0.8p-1022 / -0x0.4p-1022 = -0x1p+1
  comp64(double_of_bits(0x00000000, 0x00000002) / double_of_bits(0x00000000, 0x00000001), 0x40000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000002p-1022 / 0x0.0000000000001p-1022 = 0x1p+1
  comp64(double_of_bits(0x80000000, 0x00000002) / double_of_bits(0x80000000, 0x00000001), 0x40000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000002p-1022 / -0x0.0000000000001p-1022 = 0x1p+1
  comp64(double_of_bits(0x00000000, 0x00000002) / double_of_bits(0x80000000, 0x00000001), 0xc0000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000002p-1022 / -0x0.0000000000001p-1022 = -0x1p+1
  comp64(double_of_bits(0x80000000, 0x00000002) / double_of_bits(0x00000000, 0x00000001), 0xc0000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000002p-1022 / 0x0.0000000000001p-1022 = -0x1p+1
  comp64(double_of_bits(0x40080000, 0x00000000) / double_of_bits(0x3fe00000, 0x00000000), 0x40180000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 / 0x1p-1 = 0x1.8p+2
}

void f96(void) {
  comp64(double_of_bits(0xc0080000, 0x00000000) / double_of_bits(0xbfe00000, 0x00000000), 0x40180000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 / -0x1p-1 = 0x1.8p+2
  comp64(double_of_bits(0xc0080000, 0x00000000) / double_of_bits(0x3fe00000, 0x00000000), 0xc0180000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 / 0x1p-1 = -0x1.8p+2
  comp64(double_of_bits(0x40080000, 0x00000000) / double_of_bits(0xbfe00000, 0x00000000), 0xc0180000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 / -0x1p-1 = -0x1.8p+2
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0x3fe00000, 0x00000000), 0x001fffff, 0xfffffffe, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / 0x1p-1 = 0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0xbfe00000, 0x00000000), 0x001fffff, 0xfffffffe, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / -0x1p-1 = 0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0x3fe00000, 0x00000000), 0x801fffff, 0xfffffffe, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / 0x1p-1 = -0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0xbfe00000, 0x00000000), 0x801fffff, 0xfffffffe, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / -0x1p-1 = -0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0x3fe00000, 0x00000000), 0x00000000, 0x00000002, STR(__LINE__)); // 0x0.0000000000001p-1022 / 0x1p-1 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0xbfe00000, 0x00000000), 0x00000000, 0x00000002, STR(__LINE__)); // -0x0.0000000000001p-1022 / -0x1p-1 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0x3fe00000, 0x00000000), 0x80000000, 0x00000002, STR(__LINE__)); // -0x0.0000000000001p-1022 / 0x1p-1 = -0x0.0000000000002p-1022
}

void f97(void) {
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0xbfe00000, 0x00000000), 0x80000000, 0x00000002, STR(__LINE__)); // 0x0.0000000000001p-1022 / -0x1p-1 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x40080000, 0x00000000) / double_of_bits(0x40180000, 0x00000000), 0x3fe00000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 / 0x1.8p+2 = 0x1p-1
  comp64(double_of_bits(0xc0080000, 0x00000000) / double_of_bits(0xc0180000, 0x00000000), 0x3fe00000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 / -0x1.8p+2 = 0x1p-1
  comp64(double_of_bits(0xc0080000, 0x00000000) / double_of_bits(0x40180000, 0x00000000), 0xbfe00000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 / 0x1.8p+2 = -0x1p-1
  comp64(double_of_bits(0x40080000, 0x00000000) / double_of_bits(0xc0180000, 0x00000000), 0xbfe00000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 / -0x1.8p+2 = -0x1p-1
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0x001fffff, 0xfffffffe), 0x3fe00000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / 0x1.ffffffffffffep-1022 = 0x1p-1
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0x801fffff, 0xfffffffe), 0x3fe00000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / -0x1.ffffffffffffep-1022 = 0x1p-1
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0x001fffff, 0xfffffffe), 0xbfe00000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / 0x1.ffffffffffffep-1022 = -0x1p-1
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0x801fffff, 0xfffffffe), 0xbfe00000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / -0x1.ffffffffffffep-1022 = -0x1p-1
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0x00000000, 0x00000002), 0x3fe00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 / 0x0.0000000000002p-1022 = 0x1p-1
}

void f98(void) {
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0x00000000, 0x00000002), 0xbfe00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 / 0x0.0000000000002p-1022 = -0x1p-1
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0x80000000, 0x00000002), 0x3fe00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 / -0x0.0000000000002p-1022 = 0x1p-1
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0x80000000, 0x00000002), 0xbfe00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 / -0x0.0000000000002p-1022 = -0x1p-1
  comp64(double_of_bits(0x40080000, 0x00000000) / double_of_bits(0x3f600000, 0x00000000), 0x40980000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 / 0x1p-9 = 0x1.8p+10
  comp64(double_of_bits(0xc0080000, 0x00000000) / double_of_bits(0xbf600000, 0x00000000), 0x40980000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 / -0x1p-9 = 0x1.8p+10
  comp64(double_of_bits(0xc0080000, 0x00000000) / double_of_bits(0x3f600000, 0x00000000), 0xc0980000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 / 0x1p-9 = -0x1.8p+10
  comp64(double_of_bits(0x40080000, 0x00000000) / double_of_bits(0xbf600000, 0x00000000), 0xc0980000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 / -0x1p-9 = -0x1.8p+10
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0x3f600000, 0x00000000), 0x009fffff, 0xfffffffe, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / 0x1p-9 = 0x1.ffffffffffffep-1014
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0xbf600000, 0x00000000), 0x009fffff, 0xfffffffe, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / -0x1p-9 = 0x1.ffffffffffffep-1014
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0x3f600000, 0x00000000), 0x809fffff, 0xfffffffe, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / 0x1p-9 = -0x1.ffffffffffffep-1014
}

void f99(void) {
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0xbf600000, 0x00000000), 0x809fffff, 0xfffffffe, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / -0x1p-9 = -0x1.ffffffffffffep-1014
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0x3fc00000, 0x00000000), 0x00000000, 0x00000008, STR(__LINE__)); // 0x0.0000000000001p-1022 / 0x1p-3 = 0x0.0000000000008p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0xbfc00000, 0x00000000), 0x00000000, 0x00000008, STR(__LINE__)); // -0x0.0000000000001p-1022 / -0x1p-3 = 0x0.0000000000008p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0x3fc00000, 0x00000000), 0x80000000, 0x00000008, STR(__LINE__)); // -0x0.0000000000001p-1022 / 0x1p-3 = -0x0.0000000000008p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0xbfc00000, 0x00000000), 0x80000000, 0x00000008, STR(__LINE__)); // 0x0.0000000000001p-1022 / -0x1p-3 = -0x0.0000000000008p-1022
  comp64(double_of_bits(0x40080000, 0x00000000) / double_of_bits(0x40980000, 0x00000000), 0x3f600000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 / 0x1.8p+10 = 0x1p-9
  comp64(double_of_bits(0xc0080000, 0x00000000) / double_of_bits(0x40980000, 0x00000000), 0xbf600000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 / 0x1.8p+10 = -0x1p-9
  comp64(double_of_bits(0xc0080000, 0x00000000) / double_of_bits(0xc0980000, 0x00000000), 0x3f600000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 / -0x1.8p+10 = 0x1p-9
  comp64(double_of_bits(0x40080000, 0x00000000) / double_of_bits(0xc0980000, 0x00000000), 0xbf600000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 / -0x1.8p+10 = -0x1p-9
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0x009fffff, 0xfffffffe), 0x3f600000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / 0x1.ffffffffffffep-1014 = 0x1p-9
}

void f100(void) {
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0x009fffff, 0xfffffffe), 0xbf600000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / 0x1.ffffffffffffep-1014 = -0x1p-9
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0x809fffff, 0xfffffffe), 0x3f600000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / -0x1.ffffffffffffep-1014 = 0x1p-9
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0x809fffff, 0xfffffffe), 0xbf600000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / -0x1.ffffffffffffep-1014 = -0x1p-9
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0x00000000, 0x00000008), 0x3fc00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 / 0x0.0000000000008p-1022 = 0x1p-3
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0x00000000, 0x00000008), 0xbfc00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 / 0x0.0000000000008p-1022 = -0x1p-3
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0x80000000, 0x00000008), 0x3fc00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 / -0x0.0000000000008p-1022 = 0x1p-3
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0x80000000, 0x00000008), 0xbfc00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 / -0x0.0000000000008p-1022 = -0x1p-3
  comp64(double_of_bits(0x40220000, 0x00000000) / double_of_bits(0x40080000, 0x00000000), 0x40080000, 0x00000000, STR(__LINE__)); // 0x1.2p+3 / 0x1.8p+1 = 0x1.8p+1
  comp64(double_of_bits(0xc0220000, 0x00000000) / double_of_bits(0xc0080000, 0x00000000), 0x40080000, 0x00000000, STR(__LINE__)); // -0x1.2p+3 / -0x1.8p+1 = 0x1.8p+1
  comp64(double_of_bits(0xc0220000, 0x00000000) / double_of_bits(0x40080000, 0x00000000), 0xc0080000, 0x00000000, STR(__LINE__)); // -0x1.2p+3 / 0x1.8p+1 = -0x1.8p+1
}

void f101(void) {
  comp64(double_of_bits(0x40220000, 0x00000000) / double_of_bits(0xc0080000, 0x00000000), 0xc0080000, 0x00000000, STR(__LINE__)); // 0x1.2p+3 / -0x1.8p+1 = -0x1.8p+1
  comp64(double_of_bits(0x40180000, 0x00000000) / double_of_bits(0x40080000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // 0x1.8p+2 / 0x1.8p+1 = 0x1p+1
  comp64(double_of_bits(0xc0180000, 0x00000000) / double_of_bits(0xc0080000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // -0x1.8p+2 / -0x1.8p+1 = 0x1p+1
  comp64(double_of_bits(0x40180000, 0x00000000) / double_of_bits(0xc0080000, 0x00000000), 0xc0000000, 0x00000000, STR(__LINE__)); // 0x1.8p+2 / -0x1.8p+1 = -0x1p+1
  comp64(double_of_bits(0xc0180000, 0x00000000) / double_of_bits(0x40080000, 0x00000000), 0xc0000000, 0x00000000, STR(__LINE__)); // -0x1.8p+2 / 0x1.8p+1 = -0x1p+1
  comp64(double_of_bits(0x7fefffff, 0xfffffffd) / double_of_bits(0x40100000, 0x00000000), 0x7fcfffff, 0xfffffffd, STR(__LINE__)); // 0x1.ffffffffffffdp+1023 / 0x1p+2 = 0x1.ffffffffffffdp+1021
  comp64(double_of_bits(0x7fefffff, 0xfffffffd) / double_of_bits(0xc0100000, 0x00000000), 0xffcfffff, 0xfffffffd, STR(__LINE__)); // 0x1.ffffffffffffdp+1023 / -0x1p+2 = -0x1.ffffffffffffdp+1021
  comp64(double_of_bits(0xffefffff, 0xfffffffd) / double_of_bits(0x40100000, 0x00000000), 0xffcfffff, 0xfffffffd, STR(__LINE__)); // -0x1.ffffffffffffdp+1023 / 0x1p+2 = -0x1.ffffffffffffdp+1021
  comp64(double_of_bits(0xffefffff, 0xfffffffd) / double_of_bits(0xc0100000, 0x00000000), 0x7fcfffff, 0xfffffffd, STR(__LINE__)); // -0x1.ffffffffffffdp+1023 / -0x1p+2 = 0x1.ffffffffffffdp+1021
  comp64(double_of_bits(0x00080000, 0x00000000) / double_of_bits(0x40100000, 0x00000000), 0x00020000, 0x00000000, STR(__LINE__)); // 0x0.8p-1022 / 0x1p+2 = 0x0.2p-1022
}

void f102(void) {
  comp64(double_of_bits(0x80080000, 0x00000000) / double_of_bits(0xc0100000, 0x00000000), 0x00020000, 0x00000000, STR(__LINE__)); // -0x0.8p-1022 / -0x1p+2 = 0x0.2p-1022
  comp64(double_of_bits(0x80080000, 0x00000000) / double_of_bits(0x40100000, 0x00000000), 0x80020000, 0x00000000, STR(__LINE__)); // -0x0.8p-1022 / 0x1p+2 = -0x0.2p-1022
  comp64(double_of_bits(0x00080000, 0x00000000) / double_of_bits(0xc0100000, 0x00000000), 0x80020000, 0x00000000, STR(__LINE__)); // 0x0.8p-1022 / -0x1p+2 = -0x0.2p-1022
  comp64(double_of_bits(0x00000000, 0x00000004) / double_of_bits(0x40100000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000004p-1022 / 0x1p+2 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000004) / double_of_bits(0xc0100000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000004p-1022 / -0x1p+2 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000004) / double_of_bits(0x40100000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000004p-1022 / 0x1p+2 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000004) / double_of_bits(0xc0100000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000004p-1022 / -0x1p+2 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x7fefffff, 0xffffffff) / double_of_bits(0x7fcfffff, 0xffffffff), 0x40100000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 / 0x1.fffffffffffffp+1021 = 0x1p+2
  comp64(double_of_bits(0xffefffff, 0xffffffff) / double_of_bits(0x7fcfffff, 0xffffffff), 0xc0100000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 / 0x1.fffffffffffffp+1021 = -0x1p+2
  comp64(double_of_bits(0x7fefffff, 0xffffffff) / double_of_bits(0xffcfffff, 0xffffffff), 0xc0100000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 / -0x1.fffffffffffffp+1021 = -0x1p+2
}

void f103(void) {
  comp64(double_of_bits(0xffefffff, 0xffffffff) / double_of_bits(0xffcfffff, 0xffffffff), 0x40100000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 / -0x1.fffffffffffffp+1021 = 0x1p+2
  comp64(double_of_bits(0x00080000, 0x00000000) / double_of_bits(0x00020000, 0x00000000), 0x40100000, 0x00000000, STR(__LINE__)); // 0x0.8p-1022 / 0x0.2p-1022 = 0x1p+2
  comp64(double_of_bits(0x80080000, 0x00000000) / double_of_bits(0x80020000, 0x00000000), 0x40100000, 0x00000000, STR(__LINE__)); // -0x0.8p-1022 / -0x0.2p-1022 = 0x1p+2
  comp64(double_of_bits(0x80080000, 0x00000000) / double_of_bits(0x00020000, 0x00000000), 0xc0100000, 0x00000000, STR(__LINE__)); // -0x0.8p-1022 / 0x0.2p-1022 = -0x1p+2
  comp64(double_of_bits(0x00080000, 0x00000000) / double_of_bits(0x80020000, 0x00000000), 0xc0100000, 0x00000000, STR(__LINE__)); // 0x0.8p-1022 / -0x0.2p-1022 = -0x1p+2
  comp64(double_of_bits(0x00000000, 0x00000004) / double_of_bits(0x00000000, 0x00000001), 0x40100000, 0x00000000, STR(__LINE__)); // 0x0.0000000000004p-1022 / 0x0.0000000000001p-1022 = 0x1p+2
  comp64(double_of_bits(0x80000000, 0x00000004) / double_of_bits(0x80000000, 0x00000001), 0x40100000, 0x00000000, STR(__LINE__)); // -0x0.0000000000004p-1022 / -0x0.0000000000001p-1022 = 0x1p+2
  comp64(double_of_bits(0x00000000, 0x00000004) / double_of_bits(0x80000000, 0x00000001), 0xc0100000, 0x00000000, STR(__LINE__)); // 0x0.0000000000004p-1022 / -0x0.0000000000001p-1022 = -0x1p+2
  comp64(double_of_bits(0x80000000, 0x00000004) / double_of_bits(0x00000000, 0x00000001), 0xc0100000, 0x00000000, STR(__LINE__)); // -0x0.0000000000004p-1022 / 0x0.0000000000001p-1022 = -0x1p+2
  comp64(double_of_bits(0x40140000, 0x00000000) / double_of_bits(0x40140000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x1.4p+2 / 0x1.4p+2 = 0x1p+0
}

void f104(void) {
  comp64(double_of_bits(0xc0140000, 0x00000000) / double_of_bits(0xc0140000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // -0x1.4p+2 / -0x1.4p+2 = 0x1p+0
  comp64(double_of_bits(0x40140000, 0x00000000) / double_of_bits(0xc0140000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // 0x1.4p+2 / -0x1.4p+2 = -0x1p+0
  comp64(double_of_bits(0xc0140000, 0x00000000) / double_of_bits(0x40140000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x1.4p+2 / 0x1.4p+2 = -0x1p+0
  comp64(double_of_bits(0x40080000, 0x00000000) / double_of_bits(0x40080000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 / 0x1.8p+1 = 0x1p+0
  comp64(double_of_bits(0xc0080000, 0x00000000) / double_of_bits(0xc0080000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 / -0x1.8p+1 = 0x1p+0
  comp64(double_of_bits(0xc0080000, 0x00000000) / double_of_bits(0x40080000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 / 0x1.8p+1 = -0x1p+0
  comp64(double_of_bits(0x40080000, 0x00000000) / double_of_bits(0xc0080000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 / -0x1.8p+1 = -0x1p+0
  comp64(double_of_bits(0x401c0000, 0x00000000) / double_of_bits(0x401c0000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x1.cp+2 / 0x1.cp+2 = 0x1p+0
  comp64(double_of_bits(0xc01c0000, 0x00000000) / double_of_bits(0xc01c0000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // -0x1.cp+2 / -0x1.cp+2 = 0x1p+0
  comp64(double_of_bits(0x401c0000, 0x00000000) / double_of_bits(0xc01c0000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // 0x1.cp+2 / -0x1.cp+2 = -0x1p+0
}

void f105(void) {
  comp64(double_of_bits(0xc01c0000, 0x00000000) / double_of_bits(0x401c0000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x1.cp+2 / 0x1.cp+2 = -0x1p+0
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0x00000000, 0x00000001), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 / 0x0.0000000000001p-1022 = 0x1p+0
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0x80000000, 0x00000001), 0x3ff00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 / -0x0.0000000000001p-1022 = 0x1p+0
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0x80000000, 0x00000001), 0xbff00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 / -0x0.0000000000001p-1022 = -0x1p+0
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0x00000000, 0x00000001), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 / 0x0.0000000000001p-1022 = -0x1p+0
  comp64(double_of_bits(0x00000000, 0x00000009) / double_of_bits(0x40220000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000009p-1022 / 0x1.2p+3 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000009) / double_of_bits(0xc0220000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000009p-1022 / -0x1.2p+3 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0x00000000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x0p+0 = nan
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0x00000000, 0x00000000), 0xfff80000, 0x00000000, STR(__LINE__)); // -0x0p+0 / 0x0p+0 = -nan
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0x80000000, 0x00000000), 0xfff80000, 0x00000000, STR(__LINE__)); // 0x0p+0 / -0x0p+0 = -nan
}

void f106(void) {
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0x80000000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x0p+0 = nan
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x0.0000000000001p-1022 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0x00000000, 0x00000003), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / 0x0.0000000000003p-1022 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0x80000000, 0x00000002), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / -0x0.0000000000002p-1022 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0x80000000, 0x00000004), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x0.0000000000004p-1022 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0x000fffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x0.fffffffffffffp-1022 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0x000fffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / 0x0.fffffffffffffp-1022 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0x800fffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / -0x0.fffffffffffffp-1022 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0x800fffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x0.fffffffffffffp-1022 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0x00000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 / 0x0p+0 = inf
}

void f107(void) {
  comp64(double_of_bits(0x80000000, 0x00000003) / double_of_bits(0x00000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000003p-1022 / 0x0p+0 = -inf
  comp64(double_of_bits(0x00000000, 0x00000002) / double_of_bits(0x80000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000002p-1022 / -0x0p+0 = -inf
  comp64(double_of_bits(0x80000000, 0x00000004) / double_of_bits(0x80000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000004p-1022 / -0x0p+0 = inf
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0x00000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / 0x0p+0 = inf
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0x00000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / 0x0p+0 = -inf
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0x80000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / -0x0p+0 = -inf
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0x80000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / -0x0p+0 = inf
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0x3ff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x1p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0x40000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / 0x1p+1 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0xc0080000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / -0x1.8p+1 = -0x0p+0
}

void f108(void) {
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0xc0100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x1p+2 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0x40140000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x1.4p+2 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0x40180000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / 0x1.8p+2 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0xc01c0000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / -0x1.cp+2 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0xc0200000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x1p+3 = 0x0p+0
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0x00000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p+0 / 0x0p+0 = inf
  comp64(double_of_bits(0xc0000000, 0x00000000) / double_of_bits(0x00000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1p+1 / 0x0p+0 = -inf
  comp64(double_of_bits(0x40080000, 0x00000000) / double_of_bits(0x80000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 / -0x0p+0 = -inf
  comp64(double_of_bits(0xc0100000, 0x00000000) / double_of_bits(0x80000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1p+2 / -0x0p+0 = inf
  comp64(double_of_bits(0x40140000, 0x00000000) / double_of_bits(0x00000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.4p+2 / 0x0p+0 = inf
}

void f109(void) {
  comp64(double_of_bits(0xc0180000, 0x00000000) / double_of_bits(0x00000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.8p+2 / 0x0p+0 = -inf
  comp64(double_of_bits(0x401c0000, 0x00000000) / double_of_bits(0x80000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.cp+2 / -0x0p+0 = -inf
  comp64(double_of_bits(0xc0200000, 0x00000000) / double_of_bits(0x80000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1p+3 / -0x0p+0 = inf
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0x7fe00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x1p+1023 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0x7fd00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / 0x1p+1022 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0xffe00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / -0x1p+1023 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0xffd00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x1p+1022 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0x7fdfffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x1.fffffffffffffp+1022 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0x7fcfffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / 0x1.fffffffffffffp+1021 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0xffcfffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / -0x1.fffffffffffffp+1021 = -0x0p+0
}

void f110(void) {
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0xffdfffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x1.fffffffffffffp+1022 = 0x0p+0
  comp64(double_of_bits(0x7fe00000, 0x00000000) / double_of_bits(0x00000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 / 0x0p+0 = inf
  comp64(double_of_bits(0xffd00000, 0x00000000) / double_of_bits(0x00000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1p+1022 / 0x0p+0 = -inf
  comp64(double_of_bits(0x7fe00000, 0x00000000) / double_of_bits(0x80000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 / -0x0p+0 = -inf
  comp64(double_of_bits(0xffd00000, 0x00000000) / double_of_bits(0x80000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1p+1022 / -0x0p+0 = inf
  comp64(double_of_bits(0x7fdfffff, 0xffffffff) / double_of_bits(0x00000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1022 / 0x0p+0 = inf
  comp64(double_of_bits(0xffcfffff, 0xffffffff) / double_of_bits(0x00000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1021 / 0x0p+0 = -inf
  comp64(double_of_bits(0x7fcfffff, 0xffffffff) / double_of_bits(0x80000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1021 / -0x0p+0 = -inf
  comp64(double_of_bits(0xffdfffff, 0xffffffff) / double_of_bits(0x80000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1022 / -0x0p+0 = inf
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0x00100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x1p-1022 = 0x0p+0
}

void f111(void) {
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0x00200000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / 0x1p-1021 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0x80200000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / -0x1p-1021 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0x80100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x1p-1022 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0x001fffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x1.fffffffffffffp-1022 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0x00100000, 0x00000001), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / 0x1.0000000000001p-1022 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0x80100000, 0x00000001), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / -0x1.0000000000001p-1022 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0x801fffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x1.fffffffffffffp-1022 = 0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000000) / double_of_bits(0x00000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p-1022 / 0x0p+0 = inf
  comp64(double_of_bits(0x80200000, 0x00000000) / double_of_bits(0x00000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1p-1021 / 0x0p+0 = -inf
  comp64(double_of_bits(0x00200000, 0x00000000) / double_of_bits(0x80000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1p-1021 / -0x0p+0 = -inf
}

void f112(void) {
  comp64(double_of_bits(0x80100000, 0x00000000) / double_of_bits(0x80000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1p-1022 / -0x0p+0 = inf
  comp64(double_of_bits(0x001fffff, 0xffffffff) / double_of_bits(0x00000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp-1022 / 0x0p+0 = inf
  comp64(double_of_bits(0x80100000, 0x00000001) / double_of_bits(0x00000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p-1022 / 0x0p+0 = -inf
  comp64(double_of_bits(0x00100000, 0x00000001) / double_of_bits(0x80000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p-1022 / -0x0p+0 = -inf
  comp64(double_of_bits(0x801fffff, 0xffffffff) / double_of_bits(0x80000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp-1022 / -0x0p+0 = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0x00000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf / 0x0p+0 = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0x00000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf / 0x0p+0 = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0x80000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // inf / -0x0p+0 = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0x80000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf / -0x0p+0 = inf
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0x7ff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / inf = 0x0p+0
}

void f113(void) {
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0x7ff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / inf = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0xfff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 / -inf = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0xfff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 / -inf = 0x0p+0
  comp64(double_of_bits(0x7ff80000, 0x00000000) / double_of_bits(0x00000000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan / 0x0p+0 = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) / double_of_bits(0x80000000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan / -0x0p+0 = nan
  comp64(double_of_bits(0x00000000, 0x00000000) / double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x0p+0 / nan = nan
  comp64(double_of_bits(0x80000000, 0x00000000) / double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x0p+0 / nan = nan
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0x7ff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // inf / inf = nan
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0x7ff00000, 0x00000000), 0xfff80000, 0x00000000, STR(__LINE__)); // -inf / inf = -nan
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0xfff00000, 0x00000000), 0xfff80000, 0x00000000, STR(__LINE__)); // inf / -inf = -nan
}

void f114(void) {
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0xfff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -inf / -inf = nan
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0x00000000, 0x00000001), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf / 0x0.0000000000001p-1022 = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0x00000000, 0x00000003), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf / 0x0.0000000000003p-1022 = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0x80000000, 0x00000002), 0xfff00000, 0x00000000, STR(__LINE__)); // inf / -0x0.0000000000002p-1022 = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0x80000000, 0x00000004), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf / -0x0.0000000000004p-1022 = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0x000fffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf / 0x0.fffffffffffffp-1022 = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0x000fffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf / 0x0.fffffffffffffp-1022 = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0x800fffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // inf / -0x0.fffffffffffffp-1022 = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0x800fffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf / -0x0.fffffffffffffp-1022 = inf
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0x7ff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 / inf = 0x0p+0
}

void f115(void) {
  comp64(double_of_bits(0x80000000, 0x00000003) / double_of_bits(0x7ff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000003p-1022 / inf = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000002) / double_of_bits(0xfff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000002p-1022 / -inf = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000004) / double_of_bits(0xfff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000004p-1022 / -inf = 0x0p+0
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0x7ff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / inf = 0x0p+0
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0x7ff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / inf = -0x0p+0
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0xfff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / -inf = -0x0p+0
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0xfff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / -inf = 0x0p+0
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0x3ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf / 0x1p+0 = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0x40000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf / 0x1p+1 = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0xc0080000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // inf / -0x1.8p+1 = -inf
}

void f116(void) {
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0xc0100000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf / -0x1p+2 = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0x40140000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf / 0x1.4p+2 = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0x40180000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf / 0x1.8p+2 = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0xc01c0000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // inf / -0x1.cp+2 = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0xc0200000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf / -0x1p+3 = inf
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0x7ff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p+0 / inf = 0x0p+0
  comp64(double_of_bits(0xc0000000, 0x00000000) / double_of_bits(0x7ff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p+1 / inf = -0x0p+0
  comp64(double_of_bits(0x40080000, 0x00000000) / double_of_bits(0xfff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 / -inf = -0x0p+0
  comp64(double_of_bits(0xc0100000, 0x00000000) / double_of_bits(0xfff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p+2 / -inf = 0x0p+0
  comp64(double_of_bits(0x40140000, 0x00000000) / double_of_bits(0x7ff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.4p+2 / inf = 0x0p+0
}

void f117(void) {
  comp64(double_of_bits(0xc0180000, 0x00000000) / double_of_bits(0x7ff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1.8p+2 / inf = -0x0p+0
  comp64(double_of_bits(0x401c0000, 0x00000000) / double_of_bits(0xfff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.cp+2 / -inf = -0x0p+0
  comp64(double_of_bits(0xc0200000, 0x00000000) / double_of_bits(0xfff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p+3 / -inf = 0x0p+0
  comp64(double_of_bits(0x7fe00000, 0x00000000) / double_of_bits(0x7ff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p+1023 / inf = 0x0p+0
  comp64(double_of_bits(0xffd00000, 0x00000000) / double_of_bits(0x7ff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p+1022 / inf = -0x0p+0
  comp64(double_of_bits(0x7fe00000, 0x00000000) / double_of_bits(0xfff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p+1023 / -inf = -0x0p+0
  comp64(double_of_bits(0xffd00000, 0x00000000) / double_of_bits(0xfff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p+1022 / -inf = 0x0p+0
  comp64(double_of_bits(0x7fdfffff, 0xffffffff) / double_of_bits(0x7ff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1022 / inf = 0x0p+0
  comp64(double_of_bits(0xffcfffff, 0xffffffff) / double_of_bits(0x7ff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1021 / inf = -0x0p+0
  comp64(double_of_bits(0x7fefffff, 0xffffffff) / double_of_bits(0xfff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 / -inf = -0x0p+0
}

void f118(void) {
  comp64(double_of_bits(0xffefffff, 0xffffffff) / double_of_bits(0xfff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 / -inf = 0x0p+0
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0x7fe00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf / 0x1p+1023 = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0x7fd00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf / 0x1p+1022 = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0xffe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // inf / -0x1p+1023 = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0xffd00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf / -0x1p+1022 = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0x7fdfffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf / 0x1.fffffffffffffp+1022 = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0xffcfffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // inf / -0x1.fffffffffffffp+1021 = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0xffefffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // inf / -0x1.fffffffffffffp+1023 = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0xffefffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf / -0x1.fffffffffffffp+1023 = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0x00100000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf / 0x1p-1022 = inf
}

void f119(void) {
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0x00200000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf / 0x1p-1021 = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0x80200000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // inf / -0x1p-1021 = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0x80100000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf / -0x1p-1022 = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0x001fffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf / 0x1.fffffffffffffp-1022 = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0x00100000, 0x00000001), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf / 0x1.0000000000001p-1022 = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0x80100000, 0x00000001), 0xfff00000, 0x00000000, STR(__LINE__)); // inf / -0x1.0000000000001p-1022 = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0x801fffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf / -0x1.fffffffffffffp-1022 = inf
  comp64(double_of_bits(0x00100000, 0x00000000) / double_of_bits(0x7ff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 / inf = 0x0p+0
  comp64(double_of_bits(0x80200000, 0x00000000) / double_of_bits(0x7ff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-1021 / inf = -0x0p+0
  comp64(double_of_bits(0x00200000, 0x00000000) / double_of_bits(0xfff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-1021 / -inf = -0x0p+0
}

void f120(void) {
  comp64(double_of_bits(0x80100000, 0x00000000) / double_of_bits(0xfff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 / -inf = 0x0p+0
  comp64(double_of_bits(0x001fffff, 0xffffffff) / double_of_bits(0x7ff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp-1022 / inf = 0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000001) / double_of_bits(0x7ff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p-1022 / inf = -0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000001) / double_of_bits(0xfff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p-1022 / -inf = -0x0p+0
  comp64(double_of_bits(0x801fffff, 0xffffffff) / double_of_bits(0xfff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp-1022 / -inf = 0x0p+0
  comp64(double_of_bits(0x7ff80000, 0x00000000) / double_of_bits(0x7ff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan / inf = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) / double_of_bits(0xfff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan / -inf = nan
  comp64(double_of_bits(0x7ff00000, 0x00000000) / double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // inf / nan = nan
  comp64(double_of_bits(0xfff00000, 0x00000000) / double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -inf / nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) / double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan / nan = nan
}

void f121(void) {
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / nan = nan
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) / double_of_bits(0x000fffff, 0xffffffff), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan / 0x0.fffffffffffffp-1022 = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) / double_of_bits(0x800fffff, 0xffffffff), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan / -0x0.fffffffffffffp-1022 = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) / double_of_bits(0x00000000, 0x00000001), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan / 0x0.0000000000001p-1022 = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) / double_of_bits(0x80000000, 0x00000001), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan / -0x0.0000000000001p-1022 = nan
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 / nan = nan
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 / nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) / double_of_bits(0x3ff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan / 0x1p+0 = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) / double_of_bits(0xbff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan / -0x1p+0 = nan
}

void f122(void) {
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x1p+0 / nan = nan
  comp64(double_of_bits(0xbff00000, 0x00000000) / double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x1p+0 / nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) / double_of_bits(0x7fefffff, 0xffffffff), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan / 0x1.fffffffffffffp+1023 = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) / double_of_bits(0xffefffff, 0xffffffff), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan / -0x1.fffffffffffffp+1023 = nan
  comp64(double_of_bits(0x7fefffff, 0xffffffff) / double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 / nan = nan
  comp64(double_of_bits(0xffefffff, 0xffffffff) / double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 / nan = nan
  comp64(double_of_bits(0x7fe00000, 0x00000000) / double_of_bits(0x3fe00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 / 0x1p-1 = inf
  comp64(double_of_bits(0xffe00000, 0x00000000) / double_of_bits(0xbfe00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 / -0x1p-1 = inf
  comp64(double_of_bits(0x7fe00000, 0x00000000) / double_of_bits(0xbfe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 / -0x1p-1 = -inf
  comp64(double_of_bits(0xffe00000, 0x00000000) / double_of_bits(0x3fe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 / 0x1p-1 = -inf
}

void f123(void) {
  comp64(double_of_bits(0x7f600000, 0x00000000) / double_of_bits(0x00a00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p+1015 / 0x1p-1013 = inf
  comp64(double_of_bits(0x7fefffff, 0xffffffff) / double_of_bits(0x00000000, 0x00000001), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 / 0x0.0000000000001p-1022 = inf
  comp64(double_of_bits(0x7fe00000, 0x00000000) / double_of_bits(0x000fffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 / 0x0.fffffffffffffp-1022 = inf
  comp64(double_of_bits(0x7fefffff, 0xffffffff) / double_of_bits(0x3fefffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 / 0x1.fffffffffffffp-1 = inf
  comp64(double_of_bits(0x00100000, 0x00000000) / double_of_bits(0x43500000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 / 0x1p+54 = 0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000000) / double_of_bits(0xc3500000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 / -0x1p+54 = 0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000000) / double_of_bits(0xc3500000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 / -0x1p+54 = -0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000000) / double_of_bits(0x43500000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 / 0x1p+54 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0x40100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 / 0x1p+2 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0xc0100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 / -0x1p+2 = 0x0p+0
}

void f124(void) {
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0xc0100000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 / -0x1p+2 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0x40100000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 / 0x1p+2 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0x7fefffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 / 0x1.fffffffffffffp+1023 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0xffefffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 / -0x1.fffffffffffffp+1023 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0xffefffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 / -0x1.fffffffffffffp+1023 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0x7fefffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 / 0x1.fffffffffffffp+1023 = -0x0p+0
  comp64(double_of_bits(0x001fffff, 0xffffffff) / double_of_bits(0x43400000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp-1022 / 0x1p+53 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x801fffff, 0xffffffff) / double_of_bits(0xc3400000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.fffffffffffffp-1022 / -0x1p+53 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x801fffff, 0xffffffff) / double_of_bits(0x43400000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.fffffffffffffp-1022 / 0x1p+53 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x001fffff, 0xffffffff) / double_of_bits(0xc3400000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp-1022 / -0x1p+53 = -0x0.0000000000001p-1022
}

void f125(void) {
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0x43300000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / 0x1p+52 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0xc3300000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / -0x1p+52 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0x43300000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / 0x1p+52 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0xc3300000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / -0x1p+52 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00180000, 0x00000000) / double_of_bits(0x43400000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.8p-1022 / 0x1p+53 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80180000, 0x00000000) / double_of_bits(0xc3400000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.8p-1022 / -0x1p+53 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80180000, 0x00000000) / double_of_bits(0x43400000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.8p-1022 / 0x1p+53 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00180000, 0x00000000) / double_of_bits(0xc3400000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.8p-1022 / -0x1p+53 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000003) / double_of_bits(0x40100000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000003p-1022 / 0x1p+2 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000003) / double_of_bits(0xc0100000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000003p-1022 / -0x1p+2 = 0x0.0000000000001p-1022
}

void f126(void) {
  comp64(double_of_bits(0x80000000, 0x00000003) / double_of_bits(0x40100000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000003p-1022 / 0x1p+2 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000003) / double_of_bits(0xc0100000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000003p-1022 / -0x1p+2 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00140000, 0x00000000) / double_of_bits(0x43400000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.4p-1022 / 0x1p+53 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80140000, 0x00000000) / double_of_bits(0xc3400000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.4p-1022 / -0x1p+53 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80140000, 0x00000000) / double_of_bits(0x43400000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.4p-1022 / 0x1p+53 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00140000, 0x00000000) / double_of_bits(0xc3400000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.4p-1022 / -0x1p+53 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000005) / double_of_bits(0x40200000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000005p-1022 / 0x1p+3 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000005) / double_of_bits(0xc0200000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000005p-1022 / -0x1p+3 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000005) / double_of_bits(0x40200000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000005p-1022 / 0x1p+3 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000005) / double_of_bits(0xc0200000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000005p-1022 / -0x1p+3 = -0x0.0000000000001p-1022
}

void f127(void) {
  comp64(double_of_bits(0x00100000, 0x00000000) / double_of_bits(0x43400000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 / 0x1p+53 = 0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000000) / double_of_bits(0xc3400000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 / -0x1p+53 = 0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000000) / double_of_bits(0x43400000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 / 0x1p+53 = -0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000000) / double_of_bits(0xc3400000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 / -0x1p+53 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0x40000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 / 0x1p+1 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0xc0000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 / -0x1p+1 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000001) / double_of_bits(0x40000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 / 0x1p+1 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) / double_of_bits(0xc0000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 / -0x1p+1 = -0x0p+0
  comp64(double_of_bits(0x00280000, 0x00000000) / double_of_bits(0x43400000, 0x00000000), 0x00000000, 0x00000002, STR(__LINE__)); // 0x1.8p-1021 / 0x1p+53 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x80280000, 0x00000000) / double_of_bits(0xc3400000, 0x00000000), 0x00000000, 0x00000002, STR(__LINE__)); // -0x1.8p-1021 / -0x1p+53 = 0x0.0000000000002p-1022
}

void f128(void) {
  comp64(double_of_bits(0x80280000, 0x00000000) / double_of_bits(0x43400000, 0x00000000), 0x80000000, 0x00000002, STR(__LINE__)); // -0x1.8p-1021 / 0x1p+53 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x00280000, 0x00000000) / double_of_bits(0xc3400000, 0x00000000), 0x80000000, 0x00000002, STR(__LINE__)); // 0x1.8p-1021 / -0x1p+53 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x00000000, 0x00000003) / double_of_bits(0x40000000, 0x00000000), 0x00000000, 0x00000002, STR(__LINE__)); // 0x0.0000000000003p-1022 / 0x1p+1 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x80000000, 0x00000003) / double_of_bits(0xc0000000, 0x00000000), 0x00000000, 0x00000002, STR(__LINE__)); // -0x0.0000000000003p-1022 / -0x1p+1 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x80000000, 0x00000003) / double_of_bits(0x40000000, 0x00000000), 0x80000000, 0x00000002, STR(__LINE__)); // -0x0.0000000000003p-1022 / 0x1p+1 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x00000000, 0x00000003) / double_of_bits(0xc0000000, 0x00000000), 0x80000000, 0x00000002, STR(__LINE__)); // 0x0.0000000000003p-1022 / -0x1p+1 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x001fffff, 0xfffffffd) / double_of_bits(0x40000000, 0x00000000), 0x000fffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffdp-1022 / 0x1p+1 = 0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x801fffff, 0xfffffffd) / double_of_bits(0xc0000000, 0x00000000), 0x000fffff, 0xfffffffe, STR(__LINE__)); // -0x1.ffffffffffffdp-1022 / -0x1p+1 = 0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x801fffff, 0xfffffffd) / double_of_bits(0x40000000, 0x00000000), 0x800fffff, 0xfffffffe, STR(__LINE__)); // -0x1.ffffffffffffdp-1022 / 0x1p+1 = -0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x001fffff, 0xfffffffd) / double_of_bits(0xc0000000, 0x00000000), 0x800fffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffdp-1022 / -0x1p+1 = -0x0.ffffffffffffep-1022
}

void f129(void) {
  comp64(double_of_bits(0x001e0000, 0x00000003) / double_of_bits(0x40180000, 0x00000000), 0x00050000, 0x00000000, STR(__LINE__)); // 0x1.e000000000003p-1022 / 0x1.8p+2 = 0x0.5p-1022
  comp64(double_of_bits(0x001e0000, 0x00000003) / double_of_bits(0x43480000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.e000000000003p-1022 / 0x1.8p+53 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0x40000000, 0x00000000), 0x00080000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / 0x1p+1 = 0x0.8p-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0xc0000000, 0x00000000), 0x00080000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / -0x1p+1 = 0x0.8p-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0x40000000, 0x00000000), 0x80080000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / 0x1p+1 = -0x0.8p-1022
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0xc0000000, 0x00000000), 0x80080000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / -0x1p+1 = -0x0.8p-1022
  comp64(double_of_bits(0x00100000, 0x00000000) / double_of_bits(0x3ff00000, 0x00000001), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x1p-1022 / 0x1.0000000000001p+0 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x80100000, 0x00000000) / double_of_bits(0xbff00000, 0x00000001), 0x000fffff, 0xffffffff, STR(__LINE__)); // -0x1p-1022 / -0x1.0000000000001p+0 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x80100000, 0x00000000) / double_of_bits(0x3ff00000, 0x00000001), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x1p-1022 / 0x1.0000000000001p+0 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x00100000, 0x00000000) / double_of_bits(0xbff00000, 0x00000001), 0x800fffff, 0xffffffff, STR(__LINE__)); // 0x1p-1022 / -0x1.0000000000001p+0 = -0x0.fffffffffffffp-1022
}

void f130(void) {
  comp64(double_of_bits(0x00100000, 0x00000001) / double_of_bits(0x3ff00000, 0x00000002), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x1.0000000000001p-1022 / 0x1.0000000000002p+0 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x00100000, 0x00000002) / double_of_bits(0x3ff00000, 0x00000006), 0x000fffff, 0xfffffffc, STR(__LINE__)); // 0x1.0000000000002p-1022 / 0x1.0000000000006p+0 = 0x0.ffffffffffffcp-1022
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0x3ff00000, 0x00000001), 0x000fffff, 0xfffffffe, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / 0x1.0000000000001p+0 = 0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0xbff00000, 0x00000001), 0x000fffff, 0xfffffffe, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / -0x1.0000000000001p+0 = 0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) / double_of_bits(0x3ff00000, 0x00000001), 0x800fffff, 0xfffffffe, STR(__LINE__)); // -0x0.fffffffffffffp-1022 / 0x1.0000000000001p+0 = -0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0xbff00000, 0x00000001), 0x800fffff, 0xfffffffe, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / -0x1.0000000000001p+0 = -0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x000fffff, 0xfffffffe) / double_of_bits(0x3fefffff, 0xfffffffe), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x0.ffffffffffffep-1022 / 0x1.ffffffffffffep-1 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x000fffff, 0xfffffff7) / double_of_bits(0x3fefffff, 0xfffffffe), 0x000fffff, 0xfffffff8, STR(__LINE__)); // 0x0.ffffffffffff7p-1022 / 0x1.ffffffffffffep-1 = 0x0.ffffffffffff8p-1022
  comp64(double_of_bits(0x800fffff, 0xfffffff8) / double_of_bits(0x3fefffff, 0xfffffffe), 0x800fffff, 0xfffffff9, STR(__LINE__)); // -0x0.ffffffffffff8p-1022 / 0x1.ffffffffffffep-1 = -0x0.ffffffffffff9p-1022
  comp64(double_of_bits(0x000fffff, 0xffffffff) / double_of_bits(0x3ff00000, 0x00000002), 0x000fffff, 0xfffffffd, STR(__LINE__)); // 0x0.fffffffffffffp-1022 / 0x1.0000000000002p+0 = 0x0.ffffffffffffdp-1022
}

void f131(void) {
  comp64(double_of_bits(0x0017ffff, 0xffffffff) / double_of_bits(0x3ff80000, 0x00000000), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x1.7ffffffffffffp-1022 / 0x1.8p+0 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x8017ffff, 0xffffffff) / double_of_bits(0x3ff80000, 0x00000000), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x1.7ffffffffffffp-1022 / 0x1.8p+0 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x3fefffff, 0xffffffff) / double_of_bits(0x7fd00000, 0x00000000), 0x00100000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp-1 / 0x1p+1022 = 0x1p-1022
  comp64(double_of_bits(0xbfefffff, 0xffffffff) / double_of_bits(0x7fd00000, 0x00000000), 0x80100000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp-1 / 0x1p+1022 = -0x1p-1022
  comp64(double_of_bits(0x001fffff, 0xffffffff) / double_of_bits(0x40000000, 0x00000000), 0x00100000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp-1022 / 0x1p+1 = 0x1p-1022
  comp64(double_of_bits(0x801fffff, 0xffffffff) / double_of_bits(0xc0000000, 0x00000000), 0x00100000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp-1022 / -0x1p+1 = 0x1p-1022
  comp64(double_of_bits(0x801fffff, 0xffffffff) / double_of_bits(0x40000000, 0x00000000), 0x80100000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp-1022 / 0x1p+1 = -0x1p-1022
  comp64(double_of_bits(0x001fffff, 0xffffffff) / double_of_bits(0xc0000000, 0x00000000), 0x80100000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp-1022 / -0x1p+1 = -0x1p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0x3ff00000, 0x00000001), 0x3fefffff, 0xfffffffe, STR(__LINE__)); // 0x1p+0 / 0x1.0000000000001p+0 = 0x1.ffffffffffffep-1
  comp64(double_of_bits(0xbff00000, 0x00000000) / double_of_bits(0xbff00000, 0x00000001), 0x3fefffff, 0xfffffffe, STR(__LINE__)); // -0x1p+0 / -0x1.0000000000001p+0 = 0x1.ffffffffffffep-1
}

void f132(void) {
  comp64(double_of_bits(0xbff00000, 0x00000000) / double_of_bits(0x3ff00000, 0x00000001), 0xbfefffff, 0xfffffffe, STR(__LINE__)); // -0x1p+0 / 0x1.0000000000001p+0 = -0x1.ffffffffffffep-1
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0xbff00000, 0x00000001), 0xbfefffff, 0xfffffffe, STR(__LINE__)); // 0x1p+0 / -0x1.0000000000001p+0 = -0x1.ffffffffffffep-1
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0x3ff00000, 0x00000002), 0x3fefffff, 0xfffffffc, STR(__LINE__)); // 0x1p+0 / 0x1.0000000000002p+0 = 0x1.ffffffffffffcp-1
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0x3ff00000, 0x00000003), 0x3fefffff, 0xfffffffa, STR(__LINE__)); // 0x1p+0 / 0x1.0000000000003p+0 = 0x1.ffffffffffffap-1
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0x3ff00000, 0x00000004), 0x3fefffff, 0xfffffff8, STR(__LINE__)); // 0x1p+0 / 0x1.0000000000004p+0 = 0x1.ffffffffffff8p-1
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0x3fefffff, 0xfffffffe), 0x3ff00000, 0x00000001, STR(__LINE__)); // 0x1p+0 / 0x1.ffffffffffffep-1 = 0x1.0000000000001p+0
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0x3fefffff, 0xfffffffc), 0x3ff00000, 0x00000002, STR(__LINE__)); // 0x1p+0 / 0x1.ffffffffffffcp-1 = 0x1.0000000000002p+0
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0x3fefffff, 0xfffffff8), 0x3ff00000, 0x00000004, STR(__LINE__)); // 0x1p+0 / 0x1.ffffffffffff8p-1 = 0x1.0000000000004p+0
  comp64(double_of_bits(0x3ff00000, 0x00000001) / double_of_bits(0x3ff00000, 0x00000002), 0x3fefffff, 0xfffffffe, STR(__LINE__)); // 0x1.0000000000001p+0 / 0x1.0000000000002p+0 = 0x1.ffffffffffffep-1
  comp64(double_of_bits(0x3ff00000, 0x00000001) / double_of_bits(0x3ff00000, 0x00000003), 0x3fefffff, 0xfffffffc, STR(__LINE__)); // 0x1.0000000000001p+0 / 0x1.0000000000003p+0 = 0x1.ffffffffffffcp-1
}

void f133(void) {
  comp64(double_of_bits(0x3ff00000, 0x00000002) / double_of_bits(0x3ff00000, 0x00000003), 0x3fefffff, 0xfffffffe, STR(__LINE__)); // 0x1.0000000000002p+0 / 0x1.0000000000003p+0 = 0x1.ffffffffffffep-1
  comp64(double_of_bits(0x3ff00000, 0x00000004) / double_of_bits(0x3ff00000, 0x00000007), 0x3fefffff, 0xfffffffa, STR(__LINE__)); // 0x1.0000000000004p+0 / 0x1.0000000000007p+0 = 0x1.ffffffffffffap-1
  comp64(double_of_bits(0x3ff00000, 0x00000006) / double_of_bits(0x3ff00000, 0x00000008), 0x3fefffff, 0xfffffffc, STR(__LINE__)); // 0x1.0000000000006p+0 / 0x1.0000000000008p+0 = 0x1.ffffffffffffcp-1
  comp64(double_of_bits(0x3fefffff, 0xffffffff) / double_of_bits(0x3fefffff, 0xfffffffd), 0x3ff00000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp-1 / 0x1.ffffffffffffdp-1 = 0x1.0000000000001p+0
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) / double_of_bits(0x3fefffff, 0xfffffffc), 0x3ff00000, 0x00000001, STR(__LINE__)); // 0x1.ffffffffffffep-1 / 0x1.ffffffffffffcp-1 = 0x1.0000000000001p+0
  comp64(double_of_bits(0x3fefffff, 0xffffffff) / double_of_bits(0x3fefffff, 0xfffffff9), 0x3ff00000, 0x00000003, STR(__LINE__)); // 0x1.fffffffffffffp-1 / 0x1.ffffffffffff9p-1 = 0x1.0000000000003p+0
  comp64(double_of_bits(0x3fefffff, 0xfffffffd) / double_of_bits(0x3fefffff, 0xfffffff9), 0x3ff00000, 0x00000002, STR(__LINE__)); // 0x1.ffffffffffffdp-1 / 0x1.ffffffffffff9p-1 = 0x1.0000000000002p+0
  comp64(double_of_bits(0x3fefffff, 0xfffffffb) / double_of_bits(0x3fefffff, 0xfffffff9), 0x3ff00000, 0x00000001, STR(__LINE__)); // 0x1.ffffffffffffbp-1 / 0x1.ffffffffffff9p-1 = 0x1.0000000000001p+0
  comp64(double_of_bits(0x3ff00000, 0x00000001) / double_of_bits(0x3fefffff, 0xfffffffe), 0x3ff00000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+0 / 0x1.ffffffffffffep-1 = 0x1.0000000000002p+0
  comp64(double_of_bits(0x3ff00000, 0x00000002) / double_of_bits(0x3fefffff, 0xfffffffe), 0x3ff00000, 0x00000003, STR(__LINE__)); // 0x1.0000000000002p+0 / 0x1.ffffffffffffep-1 = 0x1.0000000000003p+0
}

void f134(void) {
  comp64(double_of_bits(0x3ff00000, 0x00000003) / double_of_bits(0x3fefffff, 0xfffffffe), 0x3ff00000, 0x00000004, STR(__LINE__)); // 0x1.0000000000003p+0 / 0x1.ffffffffffffep-1 = 0x1.0000000000004p+0
  comp64(double_of_bits(0x3ff00000, 0x00000002) / double_of_bits(0x3fefffff, 0xfffffffc), 0x3ff00000, 0x00000004, STR(__LINE__)); // 0x1.0000000000002p+0 / 0x1.ffffffffffffcp-1 = 0x1.0000000000004p+0
  comp64(double_of_bits(0x3ff00000, 0x00000004) / double_of_bits(0x3fefffff, 0xfffffffe), 0x3ff00000, 0x00000005, STR(__LINE__)); // 0x1.0000000000004p+0 / 0x1.ffffffffffffep-1 = 0x1.0000000000005p+0
  comp64(double_of_bits(0x3fefffff, 0xffffffff) / double_of_bits(0x3ff00000, 0x00000001), 0x3fefffff, 0xfffffffd, STR(__LINE__)); // 0x1.fffffffffffffp-1 / 0x1.0000000000001p+0 = 0x1.ffffffffffffdp-1
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) / double_of_bits(0x3ff00000, 0x00000001), 0x3fefffff, 0xfffffffc, STR(__LINE__)); // 0x1.ffffffffffffep-1 / 0x1.0000000000001p+0 = 0x1.ffffffffffffcp-1
  comp64(double_of_bits(0x3fefffff, 0xffffffff) / double_of_bits(0x3ff00000, 0x00000002), 0x3fefffff, 0xfffffffb, STR(__LINE__)); // 0x1.fffffffffffffp-1 / 0x1.0000000000002p+0 = 0x1.ffffffffffffbp-1
  comp64(double_of_bits(0x3fefffff, 0xfffffffd) / double_of_bits(0x3ff00000, 0x00000001), 0x3fefffff, 0xfffffffb, STR(__LINE__)); // 0x1.ffffffffffffdp-1 / 0x1.0000000000001p+0 = 0x1.ffffffffffffbp-1
  comp64(double_of_bits(0x3fefffff, 0xffffffff) / double_of_bits(0x3ff00000, 0x00000003), 0x3fefffff, 0xfffffff9, STR(__LINE__)); // 0x1.fffffffffffffp-1 / 0x1.0000000000003p+0 = 0x1.ffffffffffff9p-1
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) / double_of_bits(0x3ff00000, 0x00000002), 0x3fefffff, 0xfffffffa, STR(__LINE__)); // 0x1.ffffffffffffep-1 / 0x1.0000000000002p+0 = 0x1.ffffffffffffap-1
  comp64(double_of_bits(0x3fefffff, 0xfffffffc) / double_of_bits(0x3ff00000, 0x00000001), 0x3fefffff, 0xfffffffa, STR(__LINE__)); // 0x1.ffffffffffffcp-1 / 0x1.0000000000001p+0 = 0x1.ffffffffffffap-1
}

void f135(void) {
  comp64(double_of_bits(0x3fefffff, 0xffffffff) / double_of_bits(0x3ff00000, 0x00000004), 0x3fefffff, 0xfffffff7, STR(__LINE__)); // 0x1.fffffffffffffp-1 / 0x1.0000000000004p+0 = 0x1.ffffffffffff7p-1
  comp64(double_of_bits(0x3fefffff, 0xfffffffd) / double_of_bits(0x3ff00000, 0x00000002), 0x3fefffff, 0xfffffff9, STR(__LINE__)); // 0x1.ffffffffffffdp-1 / 0x1.0000000000002p+0 = 0x1.ffffffffffff9p-1
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) / double_of_bits(0x3ff00000, 0x00000003), 0x3fefffff, 0xfffffff8, STR(__LINE__)); // 0x1.ffffffffffffep-1 / 0x1.0000000000003p+0 = 0x1.ffffffffffff8p-1
  comp64(double_of_bits(0xbfefffff, 0xfffffffc) / double_of_bits(0xbff00000, 0x00000001), 0x3fefffff, 0xfffffffa, STR(__LINE__)); // -0x1.ffffffffffffcp-1 / -0x1.0000000000001p+0 = 0x1.ffffffffffffap-1
  comp64(double_of_bits(0xbfefffff, 0xfffffffc) / double_of_bits(0x3ff00000, 0x00000001), 0xbfefffff, 0xfffffffa, STR(__LINE__)); // -0x1.ffffffffffffcp-1 / 0x1.0000000000001p+0 = -0x1.ffffffffffffap-1
  comp64(double_of_bits(0x3fefffff, 0xfffffffc) / double_of_bits(0xbff00000, 0x00000001), 0xbfefffff, 0xfffffffa, STR(__LINE__)); // 0x1.ffffffffffffcp-1 / -0x1.0000000000001p+0 = -0x1.ffffffffffffap-1
  comp64(double_of_bits(0x3ff7ffff, 0xffffffff) / double_of_bits(0x3fefffff, 0xfffffffe), 0x3ff80000, 0x00000001, STR(__LINE__)); // 0x1.7ffffffffffffp+0 / 0x1.ffffffffffffep-1 = 0x1.8000000000001p+0
  comp64(double_of_bits(0xbff7ffff, 0xffffffff) / double_of_bits(0xbfefffff, 0xfffffffe), 0x3ff80000, 0x00000001, STR(__LINE__)); // -0x1.7ffffffffffffp+0 / -0x1.ffffffffffffep-1 = 0x1.8000000000001p+0
  comp64(double_of_bits(0xbff7ffff, 0xffffffff) / double_of_bits(0x3fefffff, 0xfffffffe), 0xbff80000, 0x00000001, STR(__LINE__)); // -0x1.7ffffffffffffp+0 / 0x1.ffffffffffffep-1 = -0x1.8000000000001p+0
  comp64(double_of_bits(0x3ff7ffff, 0xffffffff) / double_of_bits(0xbfefffff, 0xfffffffe), 0xbff80000, 0x00000001, STR(__LINE__)); // 0x1.7ffffffffffffp+0 / -0x1.ffffffffffffep-1 = -0x1.8000000000001p+0
}

void f136(void) {
  comp64(double_of_bits(0x00080000, 0x00000000) / double_of_bits(0x00100000, 0x00000001), 0x3fdfffff, 0xfffffffe, STR(__LINE__)); // 0x0.8p-1022 / 0x1.0000000000001p-1022 = 0x1.ffffffffffffep-2
  comp64(double_of_bits(0x80080000, 0x00000000) / double_of_bits(0x80100000, 0x00000001), 0x3fdfffff, 0xfffffffe, STR(__LINE__)); // -0x0.8p-1022 / -0x1.0000000000001p-1022 = 0x1.ffffffffffffep-2
  comp64(double_of_bits(0x80080000, 0x00000000) / double_of_bits(0x00100000, 0x00000001), 0xbfdfffff, 0xfffffffe, STR(__LINE__)); // -0x0.8p-1022 / 0x1.0000000000001p-1022 = -0x1.ffffffffffffep-2
  comp64(double_of_bits(0x00080000, 0x00000000) / double_of_bits(0x80100000, 0x00000001), 0xbfdfffff, 0xfffffffe, STR(__LINE__)); // 0x0.8p-1022 / -0x1.0000000000001p-1022 = -0x1.ffffffffffffep-2
  comp64(double_of_bits(0x40080000, 0x00000002) / double_of_bits(0x3ff00000, 0x00000001), 0x40080000, 0x00000000, STR(__LINE__)); // 0x1.8000000000002p+1 / 0x1.0000000000001p+0 = 0x1.8p+1
  comp64(double_of_bits(0xc0080000, 0x00000002) / double_of_bits(0xbff00000, 0x00000001), 0x40080000, 0x00000000, STR(__LINE__)); // -0x1.8000000000002p+1 / -0x1.0000000000001p+0 = 0x1.8p+1
  comp64(double_of_bits(0x40080000, 0x00000002) / double_of_bits(0xbff00000, 0x00000001), 0xc0080000, 0x00000000, STR(__LINE__)); // 0x1.8000000000002p+1 / -0x1.0000000000001p+0 = -0x1.8p+1
  comp64(double_of_bits(0xc0080000, 0x00000002) / double_of_bits(0x3ff00000, 0x00000001), 0xc0080000, 0x00000000, STR(__LINE__)); // -0x1.8000000000002p+1 / 0x1.0000000000001p+0 = -0x1.8p+1
  comp64(double_of_bits(0x000c0000, 0x00000001) / double_of_bits(0x00100000, 0x00000001), 0x3fe80000, 0x00000000, STR(__LINE__)); // 0x0.c000000000001p-1022 / 0x1.0000000000001p-1022 = 0x1.8p-1
  comp64(double_of_bits(0x800c0000, 0x00000001) / double_of_bits(0x80100000, 0x00000001), 0x3fe80000, 0x00000000, STR(__LINE__)); // -0x0.c000000000001p-1022 / -0x1.0000000000001p-1022 = 0x1.8p-1
}

void f137(void) {
  comp64(double_of_bits(0x000c0000, 0x00000001) / double_of_bits(0x80100000, 0x00000001), 0xbfe80000, 0x00000000, STR(__LINE__)); // 0x0.c000000000001p-1022 / -0x1.0000000000001p-1022 = -0x1.8p-1
  comp64(double_of_bits(0x800c0000, 0x00000001) / double_of_bits(0x00100000, 0x00000001), 0xbfe80000, 0x00000000, STR(__LINE__)); // -0x0.c000000000001p-1022 / 0x1.0000000000001p-1022 = -0x1.8p-1
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0x3fefffff, 0xfffffffd), 0x3ff00000, 0x00000002, STR(__LINE__)); // 0x1p+0 / 0x1.ffffffffffffdp-1 = 0x1.0000000000002p+0
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0x3fefffff, 0xfffffffb), 0x3ff00000, 0x00000003, STR(__LINE__)); // 0x1p+0 / 0x1.ffffffffffffbp-1 = 0x1.0000000000003p+0
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0x3fefffff, 0xfffffff7), 0x3ff00000, 0x00000005, STR(__LINE__)); // 0x1p+0 / 0x1.ffffffffffff7p-1 = 0x1.0000000000005p+0
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0x3fefffff, 0xffffffff), 0x3ff00000, 0x00000001, STR(__LINE__)); // 0x1p+0 / 0x1.fffffffffffffp-1 = 0x1.0000000000001p+0
  comp64(double_of_bits(0xbff00000, 0x00000000) / double_of_bits(0xbfefffff, 0xffffffff), 0x3ff00000, 0x00000001, STR(__LINE__)); // -0x1p+0 / -0x1.fffffffffffffp-1 = 0x1.0000000000001p+0
  comp64(double_of_bits(0xbff00000, 0x00000000) / double_of_bits(0x3fefffff, 0xffffffff), 0xbff00000, 0x00000001, STR(__LINE__)); // -0x1p+0 / 0x1.fffffffffffffp-1 = -0x1.0000000000001p+0
  comp64(double_of_bits(0x3ff00000, 0x00000000) / double_of_bits(0xbfefffff, 0xffffffff), 0xbff00000, 0x00000001, STR(__LINE__)); // 0x1p+0 / -0x1.fffffffffffffp-1 = -0x1.0000000000001p+0
  comp64(double_of_bits(0x3fefffff, 0xffffffff) / double_of_bits(0x3fefffff, 0xfffffffe), 0x3ff00000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp-1 / 0x1.ffffffffffffep-1 = 0x1.0000000000001p+0
}

void f138(void) {
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) / double_of_bits(0x3fefffff, 0xfffffffd), 0x3ff00000, 0x00000001, STR(__LINE__)); // 0x1.ffffffffffffep-1 / 0x1.ffffffffffffdp-1 = 0x1.0000000000001p+0
  comp64(double_of_bits(0x3fefffff, 0xffffffff) / double_of_bits(0x3fefffff, 0xfffffffc), 0x3ff00000, 0x00000002, STR(__LINE__)); // 0x1.fffffffffffffp-1 / 0x1.ffffffffffffcp-1 = 0x1.0000000000002p+0
  comp64(double_of_bits(0x3fefffff, 0xfffffffd) / double_of_bits(0x3fefffff, 0xfffffffc), 0x3ff00000, 0x00000001, STR(__LINE__)); // 0x1.ffffffffffffdp-1 / 0x1.ffffffffffffcp-1 = 0x1.0000000000001p+0
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) / double_of_bits(0x3fefffff, 0xfffffff9), 0x3ff00000, 0x00000003, STR(__LINE__)); // 0x1.ffffffffffffep-1 / 0x1.ffffffffffff9p-1 = 0x1.0000000000003p+0
  comp64(double_of_bits(0x3fefffff, 0xfffffffc) / double_of_bits(0x3fefffff, 0xfffffff9), 0x3ff00000, 0x00000002, STR(__LINE__)); // 0x1.ffffffffffffcp-1 / 0x1.ffffffffffff9p-1 = 0x1.0000000000002p+0
  comp64(double_of_bits(0x3fefffff, 0xfffffffa) / double_of_bits(0x3fefffff, 0xfffffff9), 0x3ff00000, 0x00000001, STR(__LINE__)); // 0x1.ffffffffffffap-1 / 0x1.ffffffffffff9p-1 = 0x1.0000000000001p+0
  comp64(double_of_bits(0x3ff00000, 0x00000001) / double_of_bits(0x3fefffff, 0xffffffff), 0x3ff00000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+0 / 0x1.fffffffffffffp-1 = 0x1.0000000000002p+0
  comp64(double_of_bits(0x3ff00000, 0x00000002) / double_of_bits(0x3fefffff, 0xffffffff), 0x3ff00000, 0x00000003, STR(__LINE__)); // 0x1.0000000000002p+0 / 0x1.fffffffffffffp-1 = 0x1.0000000000003p+0
  comp64(double_of_bits(0x3ff00000, 0x00000001) / double_of_bits(0x3fefffff, 0xfffffffd), 0x3ff00000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p+0 / 0x1.ffffffffffffdp-1 = 0x1.0000000000003p+0
  comp64(double_of_bits(0x3ff00000, 0x00000003) / double_of_bits(0x3fefffff, 0xffffffff), 0x3ff00000, 0x00000004, STR(__LINE__)); // 0x1.0000000000003p+0 / 0x1.fffffffffffffp-1 = 0x1.0000000000004p+0
}

void f139(void) {
  comp64(double_of_bits(0x3ff00000, 0x00000002) / double_of_bits(0x3fefffff, 0xfffffffd), 0x3ff00000, 0x00000004, STR(__LINE__)); // 0x1.0000000000002p+0 / 0x1.ffffffffffffdp-1 = 0x1.0000000000004p+0
  comp64(double_of_bits(0x3ff00000, 0x00000003) / double_of_bits(0x3fefffff, 0xfffffffd), 0x3ff00000, 0x00000005, STR(__LINE__)); // 0x1.0000000000003p+0 / 0x1.ffffffffffffdp-1 = 0x1.0000000000005p+0
  comp64(double_of_bits(0x3ff00000, 0x00000001) / double_of_bits(0x3fefffff, 0xfffffffb), 0x3ff00000, 0x00000004, STR(__LINE__)); // 0x1.0000000000001p+0 / 0x1.ffffffffffffbp-1 = 0x1.0000000000004p+0
  comp64(double_of_bits(0x3ff00000, 0x00000005) / double_of_bits(0x3fefffff, 0xffffffff), 0x3ff00000, 0x00000006, STR(__LINE__)); // 0x1.0000000000005p+0 / 0x1.fffffffffffffp-1 = 0x1.0000000000006p+0
  comp64(double_of_bits(0x00080000, 0x00000000) / double_of_bits(0x001fffff, 0xffffffff), 0x3fd00000, 0x00000001, STR(__LINE__)); // 0x0.8p-1022 / 0x1.fffffffffffffp-1022 = 0x1.0000000000001p-2
  comp64(double_of_bits(0x80080000, 0x00000000) / double_of_bits(0x801fffff, 0xffffffff), 0x3fd00000, 0x00000001, STR(__LINE__)); // -0x0.8p-1022 / -0x1.fffffffffffffp-1022 = 0x1.0000000000001p-2
  comp64(double_of_bits(0x80080000, 0x00000000) / double_of_bits(0x001fffff, 0xffffffff), 0xbfd00000, 0x00000001, STR(__LINE__)); // -0x0.8p-1022 / 0x1.fffffffffffffp-1022 = -0x1.0000000000001p-2
  comp64(double_of_bits(0x00080000, 0x00000000) / double_of_bits(0x801fffff, 0xffffffff), 0xbfd00000, 0x00000001, STR(__LINE__)); // 0x0.8p-1022 / -0x1.fffffffffffffp-1022 = -0x1.0000000000001p-2
  comp64(double_of_bits(0x3ff80000, 0x00000001) / double_of_bits(0x3ff00000, 0x00000001), 0x3ff80000, 0x00000000, STR(__LINE__)); // 0x1.8000000000001p+0 / 0x1.0000000000001p+0 = 0x1.8p+0
  comp64(double_of_bits(0xbff80000, 0x00000001) / double_of_bits(0xbff00000, 0x00000001), 0x3ff80000, 0x00000000, STR(__LINE__)); // -0x1.8000000000001p+0 / -0x1.0000000000001p+0 = 0x1.8p+0
}

void f140(void) {
  comp64(double_of_bits(0xbff80000, 0x00000001) / double_of_bits(0x3ff00000, 0x00000001), 0xbff80000, 0x00000000, STR(__LINE__)); // -0x1.8000000000001p+0 / 0x1.0000000000001p+0 = -0x1.8p+0
  comp64(double_of_bits(0x3ff80000, 0x00000001) / double_of_bits(0xbff00000, 0x00000001), 0xbff80000, 0x00000000, STR(__LINE__)); // 0x1.8000000000001p+0 / -0x1.0000000000001p+0 = -0x1.8p+0
  comp64(double_of_bits(0x3ff00000, 0x00000002) / double_of_bits(0x3ff00000, 0x00000001), 0x3ff00000, 0x00000001, STR(__LINE__)); // 0x1.0000000000002p+0 / 0x1.0000000000001p+0 = 0x1.0000000000001p+0
  comp64(double_of_bits(0xbff00000, 0x00000002) / double_of_bits(0xbff00000, 0x00000001), 0x3ff00000, 0x00000001, STR(__LINE__)); // -0x1.0000000000002p+0 / -0x1.0000000000001p+0 = 0x1.0000000000001p+0
  comp64(double_of_bits(0xbff00000, 0x00000002) / double_of_bits(0x3ff00000, 0x00000001), 0xbff00000, 0x00000001, STR(__LINE__)); // -0x1.0000000000002p+0 / 0x1.0000000000001p+0 = -0x1.0000000000001p+0
  comp64(double_of_bits(0x3ff00000, 0x00000002) / double_of_bits(0xbff00000, 0x00000001), 0xbff00000, 0x00000001, STR(__LINE__)); // 0x1.0000000000002p+0 / -0x1.0000000000001p+0 = -0x1.0000000000001p+0
  comp64(double_of_bits(0x3ff00000, 0x00000003) / double_of_bits(0x3ff00000, 0x00000001), 0x3ff00000, 0x00000002, STR(__LINE__)); // 0x1.0000000000003p+0 / 0x1.0000000000001p+0 = 0x1.0000000000002p+0
  comp64(double_of_bits(0x3ff00000, 0x00000004) / double_of_bits(0x3ff00000, 0x00000001), 0x3ff00000, 0x00000003, STR(__LINE__)); // 0x1.0000000000004p+0 / 0x1.0000000000001p+0 = 0x1.0000000000003p+0
  comp64(double_of_bits(0x3ff00000, 0x00000007) / double_of_bits(0x3ff00000, 0x00000002), 0x3ff00000, 0x00000005, STR(__LINE__)); // 0x1.0000000000007p+0 / 0x1.0000000000002p+0 = 0x1.0000000000005p+0
  comp64(double_of_bits(0x3ff00000, 0x00000009) / double_of_bits(0x3ff00000, 0x00000008), 0x3ff00000, 0x00000001, STR(__LINE__)); // 0x1.0000000000009p+0 / 0x1.0000000000008p+0 = 0x1.0000000000001p+0
}

void f141(void) {
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) / double_of_bits(0x3fefffff, 0xffffffff), 0x3fefffff, 0xffffffff, STR(__LINE__)); // 0x1.ffffffffffffep-1 / 0x1.fffffffffffffp-1 = 0x1.fffffffffffffp-1
  comp64(double_of_bits(0x3fefffff, 0xfffffffd) / double_of_bits(0x3fefffff, 0xffffffff), 0x3fefffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffdp-1 / 0x1.fffffffffffffp-1 = 0x1.ffffffffffffep-1
  comp64(double_of_bits(0x3fefffff, 0xfffffffd) / double_of_bits(0x3fefffff, 0xfffffffe), 0x3fefffff, 0xffffffff, STR(__LINE__)); // 0x1.ffffffffffffdp-1 / 0x1.ffffffffffffep-1 = 0x1.fffffffffffffp-1
  comp64(double_of_bits(0x3fefffff, 0xfffffffc) / double_of_bits(0x3fefffff, 0xffffffff), 0x3fefffff, 0xfffffffd, STR(__LINE__)); // 0x1.ffffffffffffcp-1 / 0x1.fffffffffffffp-1 = 0x1.ffffffffffffdp-1
  comp64(double_of_bits(0x3fefffff, 0xfffffffc) / double_of_bits(0x3fefffff, 0xfffffffe), 0x3fefffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffcp-1 / 0x1.ffffffffffffep-1 = 0x1.ffffffffffffep-1
  comp64(double_of_bits(0x3fefffff, 0xfffffffc) / double_of_bits(0x3fefffff, 0xfffffffd), 0x3fefffff, 0xffffffff, STR(__LINE__)); // 0x1.ffffffffffffcp-1 / 0x1.ffffffffffffdp-1 = 0x1.fffffffffffffp-1
  comp64(double_of_bits(0x3fefffff, 0xfffffff8) / double_of_bits(0x3fefffff, 0xfffffffd), 0x3fefffff, 0xfffffffb, STR(__LINE__)); // 0x1.ffffffffffff8p-1 / 0x1.ffffffffffffdp-1 = 0x1.ffffffffffffbp-1
  comp64(double_of_bits(0x3fefffff, 0xfffffff7) / double_of_bits(0x3fefffff, 0xfffffffe), 0x3fefffff, 0xfffffff9, STR(__LINE__)); // 0x1.ffffffffffff7p-1 / 0x1.ffffffffffffep-1 = 0x1.ffffffffffff9p-1
  comp64(double_of_bits(0x3fefffff, 0xfffffff8) / double_of_bits(0x3fefffff, 0xfffffffc), 0x3fefffff, 0xfffffffc, STR(__LINE__)); // 0x1.ffffffffffff8p-1 / 0x1.ffffffffffffcp-1 = 0x1.ffffffffffffcp-1
  comp64(double_of_bits(0x3fefffff, 0xfffffff7) / double_of_bits(0x3fefffff, 0xfffffffb), 0x3fefffff, 0xfffffffc, STR(__LINE__)); // 0x1.ffffffffffff7p-1 / 0x1.ffffffffffffbp-1 = 0x1.ffffffffffffcp-1
}

void f142(void) {
  comp64(double_of_bits(0x000fffff, 0xfffffffe) / double_of_bits(0x001fffff, 0xffffffff), 0x3fdfffff, 0xfffffffd, STR(__LINE__)); // 0x0.ffffffffffffep-1022 / 0x1.fffffffffffffp-1022 = 0x1.ffffffffffffdp-2
  comp64(double_of_bits(0x800fffff, 0xfffffffe) / double_of_bits(0x801fffff, 0xffffffff), 0x3fdfffff, 0xfffffffd, STR(__LINE__)); // -0x0.ffffffffffffep-1022 / -0x1.fffffffffffffp-1022 = 0x1.ffffffffffffdp-2
  comp64(double_of_bits(0x800fffff, 0xfffffffe) / double_of_bits(0x001fffff, 0xffffffff), 0xbfdfffff, 0xfffffffd, STR(__LINE__)); // -0x0.ffffffffffffep-1022 / 0x1.fffffffffffffp-1022 = -0x1.ffffffffffffdp-2
  comp64(double_of_bits(0x000fffff, 0xfffffffe) / double_of_bits(0x801fffff, 0xffffffff), 0xbfdfffff, 0xfffffffd, STR(__LINE__)); // 0x0.ffffffffffffep-1022 / -0x1.fffffffffffffp-1022 = -0x1.ffffffffffffdp-2
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x3ff00000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x1p+0 * 0x1p+0 = 0x1p+0
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0xbff00000, 0x00000000), 0x3ff00000, 0x00000000, STR(__LINE__)); // -0x1p+0 * -0x1p+0 = 0x1p+0
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x3ff00000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x1p+0 * 0x1p+0 = -0x1p+0
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0xbff00000, 0x00000000), 0xbff00000, 0x00000000, STR(__LINE__)); // 0x1p+0 * -0x1p+0 = -0x1p+0
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x40000000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // 0x1p+0 * 0x1p+1 = 0x1p+1
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x3ff00000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // 0x1p+1 * 0x1p+0 = 0x1p+1
}

void f143(void) {
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0xc0000000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // -0x1p+0 * -0x1p+1 = 0x1p+1
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0xbff00000, 0x00000000), 0x40000000, 0x00000000, STR(__LINE__)); // -0x1p+1 * -0x1p+0 = 0x1p+1
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x40000000, 0x00000000), 0xc0000000, 0x00000000, STR(__LINE__)); // -0x1p+0 * 0x1p+1 = -0x1p+1
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0xbff00000, 0x00000000), 0xc0000000, 0x00000000, STR(__LINE__)); // 0x1p+1 * -0x1p+0 = -0x1p+1
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0xc0000000, 0x00000000), 0xc0000000, 0x00000000, STR(__LINE__)); // 0x1p+0 * -0x1p+1 = -0x1p+1
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x3ff00000, 0x00000000), 0xc0000000, 0x00000000, STR(__LINE__)); // -0x1p+1 * 0x1p+0 = -0x1p+1
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x40080000, 0x00000000), 0x40180000, 0x00000000, STR(__LINE__)); // 0x1p+1 * 0x1.8p+1 = 0x1.8p+2
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0x40000000, 0x00000000), 0x40180000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 * 0x1p+1 = 0x1.8p+2
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0xc0080000, 0x00000000), 0x40180000, 0x00000000, STR(__LINE__)); // -0x1p+1 * -0x1.8p+1 = 0x1.8p+2
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0xc0000000, 0x00000000), 0x40180000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 * -0x1p+1 = 0x1.8p+2
}

void f144(void) {
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x40080000, 0x00000000), 0xc0180000, 0x00000000, STR(__LINE__)); // -0x1p+1 * 0x1.8p+1 = -0x1.8p+2
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0xc0000000, 0x00000000), 0xc0180000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 * -0x1p+1 = -0x1.8p+2
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0xc0080000, 0x00000000), 0xc0180000, 0x00000000, STR(__LINE__)); // 0x1p+1 * -0x1.8p+1 = -0x1.8p+2
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0x40000000, 0x00000000), 0xc0180000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 * 0x1p+1 = -0x1.8p+2
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0x40080000, 0x00000000), 0x40220000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 * 0x1.8p+1 = 0x1.2p+3
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0xc0080000, 0x00000000), 0x40220000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 * -0x1.8p+1 = 0x1.2p+3
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0x40080000, 0x00000000), 0xc0220000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 * 0x1.8p+1 = -0x1.2p+3
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0xc0080000, 0x00000000), 0xc0220000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 * -0x1.8p+1 = -0x1.2p+3
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x3ff00000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1p+0 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1p+0 * 0x0.0000000000001p-1022 = 0x0.0000000000001p-1022
}

void f145(void) {
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xbff00000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1p+0 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1p+0 * -0x0.0000000000001p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x3ff00000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1p+0 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1p+0 * -0x0.0000000000001p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1p+0 * 0x0.0000000000001p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xbff00000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1p+0 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000002) * double_of_bits(0x3ff00000, 0x00000000), 0x00000000, 0x00000002, STR(__LINE__)); // 0x0.0000000000002p-1022 * 0x1p+0 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000002), 0x00000000, 0x00000002, STR(__LINE__)); // 0x1p+0 * 0x0.0000000000002p-1022 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x80000000, 0x00000002) * double_of_bits(0xbff00000, 0x00000000), 0x00000000, 0x00000002, STR(__LINE__)); // -0x0.0000000000002p-1022 * -0x1p+0 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000002), 0x00000000, 0x00000002, STR(__LINE__)); // -0x1p+0 * -0x0.0000000000002p-1022 = 0x0.0000000000002p-1022
}

void f146(void) {
  comp64(double_of_bits(0x80000000, 0x00000002) * double_of_bits(0x3ff00000, 0x00000000), 0x80000000, 0x00000002, STR(__LINE__)); // -0x0.0000000000002p-1022 * 0x1p+0 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000002), 0x80000000, 0x00000002, STR(__LINE__)); // 0x1p+0 * -0x0.0000000000002p-1022 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000002), 0x80000000, 0x00000002, STR(__LINE__)); // -0x1p+0 * 0x0.0000000000002p-1022 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x00000000, 0x00000002) * double_of_bits(0xbff00000, 0x00000000), 0x80000000, 0x00000002, STR(__LINE__)); // 0x0.0000000000002p-1022 * -0x1p+0 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x00000000, 0x00000004) * double_of_bits(0x3ff00000, 0x00000000), 0x00000000, 0x00000004, STR(__LINE__)); // 0x0.0000000000004p-1022 * 0x1p+0 = 0x0.0000000000004p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000004), 0x00000000, 0x00000004, STR(__LINE__)); // 0x1p+0 * 0x0.0000000000004p-1022 = 0x0.0000000000004p-1022
  comp64(double_of_bits(0x80000000, 0x00000004) * double_of_bits(0xbff00000, 0x00000000), 0x00000000, 0x00000004, STR(__LINE__)); // -0x0.0000000000004p-1022 * -0x1p+0 = 0x0.0000000000004p-1022
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000004), 0x00000000, 0x00000004, STR(__LINE__)); // -0x1p+0 * -0x0.0000000000004p-1022 = 0x0.0000000000004p-1022
  comp64(double_of_bits(0x80000000, 0x00000004) * double_of_bits(0x3ff00000, 0x00000000), 0x80000000, 0x00000004, STR(__LINE__)); // -0x0.0000000000004p-1022 * 0x1p+0 = -0x0.0000000000004p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000004), 0x80000000, 0x00000004, STR(__LINE__)); // 0x1p+0 * -0x0.0000000000004p-1022 = -0x0.0000000000004p-1022
}

void f147(void) {
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000004), 0x80000000, 0x00000004, STR(__LINE__)); // -0x1p+0 * 0x0.0000000000004p-1022 = -0x0.0000000000004p-1022
  comp64(double_of_bits(0x00000000, 0x00000004) * double_of_bits(0xbff00000, 0x00000000), 0x80000000, 0x00000004, STR(__LINE__)); // 0x0.0000000000004p-1022 * -0x1p+0 = -0x0.0000000000004p-1022
  comp64(double_of_bits(0x001fffff, 0xfffffffe) * double_of_bits(0x3ff00000, 0x00000000), 0x001fffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffep-1022 * 0x1p+0 = 0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x001fffff, 0xfffffffe), 0x001fffff, 0xfffffffe, STR(__LINE__)); // 0x1p+0 * 0x1.ffffffffffffep-1022 = 0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x801fffff, 0xfffffffe) * double_of_bits(0xbff00000, 0x00000000), 0x001fffff, 0xfffffffe, STR(__LINE__)); // -0x1.ffffffffffffep-1022 * -0x1p+0 = 0x1.ffffffffffffep-1022
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x801fffff, 0xfffffffe), 0x001fffff, 0xfffffffe, STR(__LINE__)); // -0x1p+0 * -0x1.ffffffffffffep-1022 = 0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x801fffff, 0xfffffffe) * double_of_bits(0x3ff00000, 0x00000000), 0x801fffff, 0xfffffffe, STR(__LINE__)); // -0x1.ffffffffffffep-1022 * 0x1p+0 = -0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x801fffff, 0xfffffffe), 0x801fffff, 0xfffffffe, STR(__LINE__)); // 0x1p+0 * -0x1.ffffffffffffep-1022 = -0x1.ffffffffffffep-1022
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x001fffff, 0xfffffffe), 0x801fffff, 0xfffffffe, STR(__LINE__)); // -0x1p+0 * 0x1.ffffffffffffep-1022 = -0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x001fffff, 0xfffffffe) * double_of_bits(0xbff00000, 0x00000000), 0x801fffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffep-1022 * -0x1p+0 = -0x1.ffffffffffffep-1022
}

void f148(void) {
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000009), 0x80000000, 0x00000009, STR(__LINE__)); // 0x1p+0 * -0x0.0000000000009p-1022 = -0x0.0000000000009p-1022
  comp64(double_of_bits(0x80000000, 0x00000009) * double_of_bits(0x3ff00000, 0x00000000), 0x80000000, 0x00000009, STR(__LINE__)); // -0x0.0000000000009p-1022 * 0x1p+0 = -0x0.0000000000009p-1022
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000009), 0x80000000, 0x00000009, STR(__LINE__)); // -0x1p+0 * 0x0.0000000000009p-1022 = -0x0.0000000000009p-1022
  comp64(double_of_bits(0x00000000, 0x00000009) * double_of_bits(0xbff00000, 0x00000000), 0x80000000, 0x00000009, STR(__LINE__)); // 0x0.0000000000009p-1022 * -0x1p+0 = -0x0.0000000000009p-1022
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000009), 0x00000000, 0x00000009, STR(__LINE__)); // -0x1p+0 * -0x0.0000000000009p-1022 = 0x0.0000000000009p-1022
  comp64(double_of_bits(0x80000000, 0x00000009) * double_of_bits(0xbff00000, 0x00000000), 0x00000000, 0x00000009, STR(__LINE__)); // -0x0.0000000000009p-1022 * -0x1p+0 = 0x0.0000000000009p-1022
  comp64(double_of_bits(0x00000000, 0x00000009) * double_of_bits(0x3ff00000, 0x00000000), 0x00000000, 0x00000009, STR(__LINE__)); // 0x0.0000000000009p-1022 * 0x1p+0 = 0x0.0000000000009p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000009), 0x00000000, 0x00000009, STR(__LINE__)); // 0x1p+0 * 0x0.0000000000009p-1022 = 0x0.0000000000009p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x800fffff, 0xffffffff), 0x800fffff, 0xffffffff, STR(__LINE__)); // 0x1p+0 * -0x0.fffffffffffffp-1022 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) * double_of_bits(0x3ff00000, 0x00000000), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x0.fffffffffffffp-1022 * 0x1p+0 = -0x0.fffffffffffffp-1022
}

void f149(void) {
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x000fffff, 0xffffffff), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x1p+0 * 0x0.fffffffffffffp-1022 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x000fffff, 0xffffffff) * double_of_bits(0xbff00000, 0x00000000), 0x800fffff, 0xffffffff, STR(__LINE__)); // 0x0.fffffffffffffp-1022 * -0x1p+0 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x800fffff, 0xffffffff), 0x000fffff, 0xffffffff, STR(__LINE__)); // -0x1p+0 * -0x0.fffffffffffffp-1022 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) * double_of_bits(0xbff00000, 0x00000000), 0x000fffff, 0xffffffff, STR(__LINE__)); // -0x0.fffffffffffffp-1022 * -0x1p+0 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x000fffff, 0xffffffff) * double_of_bits(0x3ff00000, 0x00000000), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x0.fffffffffffffp-1022 * 0x1p+0 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x000fffff, 0xffffffff), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x1p+0 * 0x0.fffffffffffffp-1022 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x80100000, 0x00000001), 0x80100000, 0x00000001, STR(__LINE__)); // 0x1p+0 * -0x1.0000000000001p-1022 = -0x1.0000000000001p-1022
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0x3ff00000, 0x00000000), 0x80100000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p-1022 * 0x1p+0 = -0x1.0000000000001p-1022
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x00100000, 0x00000001), 0x80100000, 0x00000001, STR(__LINE__)); // -0x1p+0 * 0x1.0000000000001p-1022 = -0x1.0000000000001p-1022
  comp64(double_of_bits(0x00100000, 0x00000001) * double_of_bits(0xbff00000, 0x00000000), 0x80100000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p-1022 * -0x1p+0 = -0x1.0000000000001p-1022
}

void f150(void) {
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x80100000, 0x00000001), 0x00100000, 0x00000001, STR(__LINE__)); // -0x1p+0 * -0x1.0000000000001p-1022 = 0x1.0000000000001p-1022
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0xbff00000, 0x00000000), 0x00100000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p-1022 * -0x1p+0 = 0x1.0000000000001p-1022
  comp64(double_of_bits(0x00100000, 0x00000001) * double_of_bits(0x3ff00000, 0x00000000), 0x00100000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p-1022 * 0x1p+0 = 0x1.0000000000001p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x00100000, 0x00000001), 0x00100000, 0x00000001, STR(__LINE__)); // 0x1p+0 * 0x1.0000000000001p-1022 = 0x1.0000000000001p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x00200000, 0x00000003), 0x00200000, 0x00000003, STR(__LINE__)); // 0x1p+0 * 0x1.0000000000003p-1021 = 0x1.0000000000003p-1021
  comp64(double_of_bits(0x00200000, 0x00000003) * double_of_bits(0x3ff00000, 0x00000000), 0x00200000, 0x00000003, STR(__LINE__)); // 0x1.0000000000003p-1021 * 0x1p+0 = 0x1.0000000000003p-1021
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x00100000, 0x00000009), 0x80100000, 0x00000009, STR(__LINE__)); // -0x1p+0 * 0x1.0000000000009p-1022 = -0x1.0000000000009p-1022
  comp64(double_of_bits(0x00100000, 0x00000009) * double_of_bits(0xbff00000, 0x00000000), 0x80100000, 0x00000009, STR(__LINE__)); // 0x1.0000000000009p-1022 * -0x1p+0 = -0x1.0000000000009p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x000fffff, 0xfffffffd), 0x000fffff, 0xfffffffd, STR(__LINE__)); // 0x1p+0 * 0x0.ffffffffffffdp-1022 = 0x0.ffffffffffffdp-1022
  comp64(double_of_bits(0x000fffff, 0xfffffffd) * double_of_bits(0x3ff00000, 0x00000000), 0x000fffff, 0xfffffffd, STR(__LINE__)); // 0x0.ffffffffffffdp-1022 * 0x1p+0 = 0x0.ffffffffffffdp-1022
}

void f151(void) {
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x7fdfffff, 0xffffffff), 0x7fefffff, 0xffffffff, STR(__LINE__)); // 0x1p+1 * 0x1.fffffffffffffp+1022 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x7fdfffff, 0xffffffff) * double_of_bits(0x40000000, 0x00000000), 0x7fefffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1022 * 0x1p+1 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0xffdfffff, 0xffffffff), 0x7fefffff, 0xffffffff, STR(__LINE__)); // -0x1p+1 * -0x1.fffffffffffffp+1022 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xffdfffff, 0xffffffff) * double_of_bits(0xc0000000, 0x00000000), 0x7fefffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1022 * -0x1p+1 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x7fdfffff, 0xffffffff) * double_of_bits(0xc0000000, 0x00000000), 0xffefffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1022 * -0x1p+1 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x7fdfffff, 0xffffffff), 0xffefffff, 0xffffffff, STR(__LINE__)); // -0x1p+1 * 0x1.fffffffffffffp+1022 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xffdfffff, 0xffffffff) * double_of_bits(0x40000000, 0x00000000), 0xffefffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1022 * 0x1p+1 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0xffdfffff, 0xffffffff), 0xffefffff, 0xffffffff, STR(__LINE__)); // 0x1p+1 * -0x1.fffffffffffffp+1022 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x7fd00000, 0x00000003), 0x7fe00000, 0x00000003, STR(__LINE__)); // 0x1p+1 * 0x1.0000000000003p+1022 = 0x1.0000000000003p+1023
  comp64(double_of_bits(0x7fd00000, 0x00000003) * double_of_bits(0x40000000, 0x00000000), 0x7fe00000, 0x00000003, STR(__LINE__)); // 0x1.0000000000003p+1022 * 0x1p+1 = 0x1.0000000000003p+1023
}

void f152(void) {
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0xffd00000, 0x00000003), 0x7fe00000, 0x00000003, STR(__LINE__)); // -0x1p+1 * -0x1.0000000000003p+1022 = 0x1.0000000000003p+1023
  comp64(double_of_bits(0xffd00000, 0x00000003) * double_of_bits(0xc0000000, 0x00000000), 0x7fe00000, 0x00000003, STR(__LINE__)); // -0x1.0000000000003p+1022 * -0x1p+1 = 0x1.0000000000003p+1023
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0xffd00000, 0x00000003), 0xffe00000, 0x00000003, STR(__LINE__)); // 0x1p+1 * -0x1.0000000000003p+1022 = -0x1.0000000000003p+1023
  comp64(double_of_bits(0xffd00000, 0x00000003) * double_of_bits(0x40000000, 0x00000000), 0xffe00000, 0x00000003, STR(__LINE__)); // -0x1.0000000000003p+1022 * 0x1p+1 = -0x1.0000000000003p+1023
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x7fd00000, 0x00000003), 0xffe00000, 0x00000003, STR(__LINE__)); // -0x1p+1 * 0x1.0000000000003p+1022 = -0x1.0000000000003p+1023
  comp64(double_of_bits(0x7fd00000, 0x00000003) * double_of_bits(0xc0000000, 0x00000000), 0xffe00000, 0x00000003, STR(__LINE__)); // 0x1.0000000000003p+1022 * -0x1p+1 = -0x1.0000000000003p+1023
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x7fd00000, 0x00000001), 0x7fe00000, 0x00000001, STR(__LINE__)); // 0x1p+1 * 0x1.0000000000001p+1022 = 0x1.0000000000001p+1023
  comp64(double_of_bits(0x7fd00000, 0x00000001) * double_of_bits(0x40000000, 0x00000000), 0x7fe00000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p+1022 * 0x1p+1 = 0x1.0000000000001p+1023
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0xffd00000, 0x00000001), 0x7fe00000, 0x00000001, STR(__LINE__)); // -0x1p+1 * -0x1.0000000000001p+1022 = 0x1.0000000000001p+1023
  comp64(double_of_bits(0xffd00000, 0x00000001) * double_of_bits(0xc0000000, 0x00000000), 0x7fe00000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p+1022 * -0x1p+1 = 0x1.0000000000001p+1023
}

void f153(void) {
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x7fd00000, 0x00000001), 0xffe00000, 0x00000001, STR(__LINE__)); // -0x1p+1 * 0x1.0000000000001p+1022 = -0x1.0000000000001p+1023
  comp64(double_of_bits(0x7fd00000, 0x00000001) * double_of_bits(0xc0000000, 0x00000000), 0xffe00000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p+1022 * -0x1p+1 = -0x1.0000000000001p+1023
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0xffd00000, 0x00000001), 0xffe00000, 0x00000001, STR(__LINE__)); // 0x1p+1 * -0x1.0000000000001p+1022 = -0x1.0000000000001p+1023
  comp64(double_of_bits(0xffd00000, 0x00000001) * double_of_bits(0x40000000, 0x00000000), 0xffe00000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p+1022 * 0x1p+1 = -0x1.0000000000001p+1023
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x7fd00000, 0x00000000), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x1p+1 * 0x1p+1022 = 0x1p+1023
  comp64(double_of_bits(0x7fd00000, 0x00000000) * double_of_bits(0x40000000, 0x00000000), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x1p+1022 * 0x1p+1 = 0x1p+1023
  comp64(double_of_bits(0x7fd00000, 0x00000000) * double_of_bits(0xc0000000, 0x00000000), 0xffe00000, 0x00000000, STR(__LINE__)); // 0x1p+1022 * -0x1p+1 = -0x1p+1023
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x7fd00000, 0x00000000), 0xffe00000, 0x00000000, STR(__LINE__)); // -0x1p+1 * 0x1p+1022 = -0x1p+1023
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x7fcfffff, 0xffffffff), 0x7fdfffff, 0xffffffff, STR(__LINE__)); // 0x1p+1 * 0x1.fffffffffffffp+1021 = 0x1.fffffffffffffp+1022
  comp64(double_of_bits(0x7fcfffff, 0xffffffff) * double_of_bits(0x40000000, 0x00000000), 0x7fdfffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1021 * 0x1p+1 = 0x1.fffffffffffffp+1022
}

void f154(void) {
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0xffcfffff, 0xffffffff), 0x7fdfffff, 0xffffffff, STR(__LINE__)); // -0x1p+1 * -0x1.fffffffffffffp+1021 = 0x1.fffffffffffffp+1022
  comp64(double_of_bits(0xffcfffff, 0xffffffff) * double_of_bits(0xc0000000, 0x00000000), 0x7fdfffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1021 * -0x1p+1 = 0x1.fffffffffffffp+1022
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x7fcfffff, 0xffffffff), 0xffdfffff, 0xffffffff, STR(__LINE__)); // -0x1p+1 * 0x1.fffffffffffffp+1021 = -0x1.fffffffffffffp+1022
  comp64(double_of_bits(0x7fcfffff, 0xffffffff) * double_of_bits(0xc0000000, 0x00000000), 0xffdfffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1021 * -0x1p+1 = -0x1.fffffffffffffp+1022
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0xffcfffff, 0xffffffff), 0xffdfffff, 0xffffffff, STR(__LINE__)); // 0x1p+1 * -0x1.fffffffffffffp+1021 = -0x1.fffffffffffffp+1022
  comp64(double_of_bits(0xffcfffff, 0xffffffff) * double_of_bits(0x40000000, 0x00000000), 0xffdfffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1021 * 0x1p+1 = -0x1.fffffffffffffp+1022
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x7fcfffff, 0xfffffffd), 0x7fdfffff, 0xfffffffd, STR(__LINE__)); // 0x1p+1 * 0x1.ffffffffffffdp+1021 = 0x1.ffffffffffffdp+1022
  comp64(double_of_bits(0x7fcfffff, 0xfffffffd) * double_of_bits(0x40000000, 0x00000000), 0x7fdfffff, 0xfffffffd, STR(__LINE__)); // 0x1.ffffffffffffdp+1021 * 0x1p+1 = 0x1.ffffffffffffdp+1022
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0xffcfffff, 0xfffffffd), 0x7fdfffff, 0xfffffffd, STR(__LINE__)); // -0x1p+1 * -0x1.ffffffffffffdp+1021 = 0x1.ffffffffffffdp+1022
  comp64(double_of_bits(0xffcfffff, 0xfffffffd) * double_of_bits(0xc0000000, 0x00000000), 0x7fdfffff, 0xfffffffd, STR(__LINE__)); // -0x1.ffffffffffffdp+1021 * -0x1p+1 = 0x1.ffffffffffffdp+1022
}

void f155(void) {
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0xffcfffff, 0xfffffffd), 0xffdfffff, 0xfffffffd, STR(__LINE__)); // 0x1p+1 * -0x1.ffffffffffffdp+1021 = -0x1.ffffffffffffdp+1022
  comp64(double_of_bits(0xffcfffff, 0xfffffffd) * double_of_bits(0x40000000, 0x00000000), 0xffdfffff, 0xfffffffd, STR(__LINE__)); // -0x1.ffffffffffffdp+1021 * 0x1p+1 = -0x1.ffffffffffffdp+1022
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x7fcfffff, 0xfffffffd), 0xffdfffff, 0xfffffffd, STR(__LINE__)); // -0x1p+1 * 0x1.ffffffffffffdp+1021 = -0x1.ffffffffffffdp+1022
  comp64(double_of_bits(0x7fcfffff, 0xfffffffd) * double_of_bits(0xc0000000, 0x00000000), 0xffdfffff, 0xfffffffd, STR(__LINE__)); // 0x1.ffffffffffffdp+1021 * -0x1p+1 = -0x1.ffffffffffffdp+1022
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x00200000, 0x00000000, STR(__LINE__)); // 0x1p+1 * 0x1p-1022 = 0x1p-1021
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0x40000000, 0x00000000), 0x00200000, 0x00000000, STR(__LINE__)); // 0x1p-1022 * 0x1p+1 = 0x1p-1021
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x00200000, 0x00000000, STR(__LINE__)); // -0x1p+1 * -0x1p-1022 = 0x1p-1021
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0xc0000000, 0x00000000), 0x00200000, 0x00000000, STR(__LINE__)); // -0x1p-1022 * -0x1p+1 = 0x1p-1021
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0xc0000000, 0x00000000), 0x80200000, 0x00000000, STR(__LINE__)); // 0x1p-1022 * -0x1p+1 = -0x1p-1021
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x80200000, 0x00000000, STR(__LINE__)); // -0x1p+1 * 0x1p-1022 = -0x1p-1021
}

void f156(void) {
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0x40000000, 0x00000000), 0x80200000, 0x00000000, STR(__LINE__)); // -0x1p-1022 * 0x1p+1 = -0x1p-1021
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x80200000, 0x00000000, STR(__LINE__)); // 0x1p+1 * -0x1p-1022 = -0x1p-1021
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x00100000, 0x00000001), 0x00200000, 0x00000001, STR(__LINE__)); // 0x1p+1 * 0x1.0000000000001p-1022 = 0x1.0000000000001p-1021
  comp64(double_of_bits(0x00100000, 0x00000001) * double_of_bits(0x40000000, 0x00000000), 0x00200000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p-1022 * 0x1p+1 = 0x1.0000000000001p-1021
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x80100000, 0x00000001), 0x00200000, 0x00000001, STR(__LINE__)); // -0x1p+1 * -0x1.0000000000001p-1022 = 0x1.0000000000001p-1021
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0xc0000000, 0x00000000), 0x00200000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p-1022 * -0x1p+1 = 0x1.0000000000001p-1021
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x00100000, 0x00000001), 0x80200000, 0x00000001, STR(__LINE__)); // -0x1p+1 * 0x1.0000000000001p-1022 = -0x1.0000000000001p-1021
  comp64(double_of_bits(0x00100000, 0x00000001) * double_of_bits(0xc0000000, 0x00000000), 0x80200000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p-1022 * -0x1p+1 = -0x1.0000000000001p-1021
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x80100000, 0x00000001), 0x80200000, 0x00000001, STR(__LINE__)); // 0x1p+1 * -0x1.0000000000001p-1022 = -0x1.0000000000001p-1021
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0x40000000, 0x00000000), 0x80200000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p-1022 * 0x1p+1 = -0x1.0000000000001p-1021
}

void f157(void) {
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x00100000, 0x00000003), 0x00200000, 0x00000003, STR(__LINE__)); // 0x1p+1 * 0x1.0000000000003p-1022 = 0x1.0000000000003p-1021
  comp64(double_of_bits(0x00100000, 0x00000003) * double_of_bits(0x40000000, 0x00000000), 0x00200000, 0x00000003, STR(__LINE__)); // 0x1.0000000000003p-1022 * 0x1p+1 = 0x1.0000000000003p-1021
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x80100000, 0x00000003), 0x00200000, 0x00000003, STR(__LINE__)); // -0x1p+1 * -0x1.0000000000003p-1022 = 0x1.0000000000003p-1021
  comp64(double_of_bits(0x80100000, 0x00000003) * double_of_bits(0xc0000000, 0x00000000), 0x00200000, 0x00000003, STR(__LINE__)); // -0x1.0000000000003p-1022 * -0x1p+1 = 0x1.0000000000003p-1021
  comp64(double_of_bits(0x80100000, 0x00000003) * double_of_bits(0xc0000000, 0x00000000), 0x00200000, 0x00000003, STR(__LINE__)); // -0x1.0000000000003p-1022 * -0x1p+1 = 0x1.0000000000003p-1021
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x80100000, 0x00000003), 0x00200000, 0x00000003, STR(__LINE__)); // -0x1p+1 * -0x1.0000000000003p-1022 = 0x1.0000000000003p-1021
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x80100000, 0x00000003), 0x80200000, 0x00000003, STR(__LINE__)); // 0x1p+1 * -0x1.0000000000003p-1022 = -0x1.0000000000003p-1021
  comp64(double_of_bits(0x80100000, 0x00000003) * double_of_bits(0x40000000, 0x00000000), 0x80200000, 0x00000003, STR(__LINE__)); // -0x1.0000000000003p-1022 * 0x1p+1 = -0x1.0000000000003p-1021
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x00100000, 0x00000003), 0x80200000, 0x00000003, STR(__LINE__)); // -0x1p+1 * 0x1.0000000000003p-1022 = -0x1.0000000000003p-1021
  comp64(double_of_bits(0x00100000, 0x00000003) * double_of_bits(0xc0000000, 0x00000000), 0x80200000, 0x00000003, STR(__LINE__)); // 0x1.0000000000003p-1022 * -0x1p+1 = -0x1.0000000000003p-1021
}

void f158(void) {
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x00100000, 0x00000005), 0x00200000, 0x00000005, STR(__LINE__)); // 0x1p+1 * 0x1.0000000000005p-1022 = 0x1.0000000000005p-1021
  comp64(double_of_bits(0x00100000, 0x00000005) * double_of_bits(0x40000000, 0x00000000), 0x00200000, 0x00000005, STR(__LINE__)); // 0x1.0000000000005p-1022 * 0x1p+1 = 0x1.0000000000005p-1021
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x80100000, 0x00000005), 0x00200000, 0x00000005, STR(__LINE__)); // -0x1p+1 * -0x1.0000000000005p-1022 = 0x1.0000000000005p-1021
  comp64(double_of_bits(0x80100000, 0x00000005) * double_of_bits(0xc0000000, 0x00000000), 0x00200000, 0x00000005, STR(__LINE__)); // -0x1.0000000000005p-1022 * -0x1p+1 = 0x1.0000000000005p-1021
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x80100000, 0x00000005), 0x80200000, 0x00000005, STR(__LINE__)); // 0x1p+1 * -0x1.0000000000005p-1022 = -0x1.0000000000005p-1021
  comp64(double_of_bits(0x80100000, 0x00000005) * double_of_bits(0x40000000, 0x00000000), 0x80200000, 0x00000005, STR(__LINE__)); // -0x1.0000000000005p-1022 * 0x1p+1 = -0x1.0000000000005p-1021
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x00100000, 0x00000005), 0x80200000, 0x00000005, STR(__LINE__)); // -0x1p+1 * 0x1.0000000000005p-1022 = -0x1.0000000000005p-1021
  comp64(double_of_bits(0x00100000, 0x00000005) * double_of_bits(0xc0000000, 0x00000000), 0x80200000, 0x00000005, STR(__LINE__)); // 0x1.0000000000005p-1022 * -0x1p+1 = -0x1.0000000000005p-1021
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x00100000, 0x00000009), 0x00200000, 0x00000009, STR(__LINE__)); // 0x1p+1 * 0x1.0000000000009p-1022 = 0x1.0000000000009p-1021
  comp64(double_of_bits(0x00100000, 0x00000009) * double_of_bits(0x40000000, 0x00000000), 0x00200000, 0x00000009, STR(__LINE__)); // 0x1.0000000000009p-1022 * 0x1p+1 = 0x1.0000000000009p-1021
}

void f159(void) {
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x80100000, 0x00000009), 0x00200000, 0x00000009, STR(__LINE__)); // -0x1p+1 * -0x1.0000000000009p-1022 = 0x1.0000000000009p-1021
  comp64(double_of_bits(0x80100000, 0x00000009) * double_of_bits(0xc0000000, 0x00000000), 0x00200000, 0x00000009, STR(__LINE__)); // -0x1.0000000000009p-1022 * -0x1p+1 = 0x1.0000000000009p-1021
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x00100000, 0x00000009), 0x80200000, 0x00000009, STR(__LINE__)); // -0x1p+1 * 0x1.0000000000009p-1022 = -0x1.0000000000009p-1021
  comp64(double_of_bits(0x00100000, 0x00000009) * double_of_bits(0xc0000000, 0x00000000), 0x80200000, 0x00000009, STR(__LINE__)); // 0x1.0000000000009p-1022 * -0x1p+1 = -0x1.0000000000009p-1021
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x80100000, 0x00000009), 0x80200000, 0x00000009, STR(__LINE__)); // 0x1p+1 * -0x1.0000000000009p-1022 = -0x1.0000000000009p-1021
  comp64(double_of_bits(0x80100000, 0x00000009) * double_of_bits(0x40000000, 0x00000000), 0x80200000, 0x00000009, STR(__LINE__)); // -0x1.0000000000009p-1022 * 0x1p+1 = -0x1.0000000000009p-1021
  comp64(double_of_bits(0x40100000, 0x00000000) * double_of_bits(0x7fcfffff, 0xffffffff), 0x7fefffff, 0xffffffff, STR(__LINE__)); // 0x1p+2 * 0x1.fffffffffffffp+1021 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x7fcfffff, 0xffffffff) * double_of_bits(0x40100000, 0x00000000), 0x7fefffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1021 * 0x1p+2 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xc0100000, 0x00000000) * double_of_bits(0x7fcfffff, 0xffffffff), 0xffefffff, 0xffffffff, STR(__LINE__)); // -0x1p+2 * 0x1.fffffffffffffp+1021 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x7fcfffff, 0xffffffff) * double_of_bits(0xc0100000, 0x00000000), 0xffefffff, 0xffffffff, STR(__LINE__)); // 0x1.fffffffffffffp+1021 * -0x1p+2 = -0x1.fffffffffffffp+1023
}

void f160(void) {
  comp64(double_of_bits(0x40100000, 0x00000000) * double_of_bits(0xffcfffff, 0xffffffff), 0xffefffff, 0xffffffff, STR(__LINE__)); // 0x1p+2 * -0x1.fffffffffffffp+1021 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xffcfffff, 0xffffffff) * double_of_bits(0x40100000, 0x00000000), 0xffefffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1021 * 0x1p+2 = -0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xc0100000, 0x00000000) * double_of_bits(0xffcfffff, 0xffffffff), 0x7fefffff, 0xffffffff, STR(__LINE__)); // -0x1p+2 * -0x1.fffffffffffffp+1021 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0xffcfffff, 0xffffffff) * double_of_bits(0xc0100000, 0x00000000), 0x7fefffff, 0xffffffff, STR(__LINE__)); // -0x1.fffffffffffffp+1021 * -0x1p+2 = 0x1.fffffffffffffp+1023
  comp64(double_of_bits(0x7fcfffff, 0xfffffffd) * double_of_bits(0x40100000, 0x00000000), 0x7fefffff, 0xfffffffd, STR(__LINE__)); // 0x1.ffffffffffffdp+1021 * 0x1p+2 = 0x1.ffffffffffffdp+1023
  comp64(double_of_bits(0x40100000, 0x00000000) * double_of_bits(0x7fcfffff, 0xfffffffd), 0x7fefffff, 0xfffffffd, STR(__LINE__)); // 0x1p+2 * 0x1.ffffffffffffdp+1021 = 0x1.ffffffffffffdp+1023
  comp64(double_of_bits(0x7fcfffff, 0xfffffffd) * double_of_bits(0xc0100000, 0x00000000), 0xffefffff, 0xfffffffd, STR(__LINE__)); // 0x1.ffffffffffffdp+1021 * -0x1p+2 = -0x1.ffffffffffffdp+1023
  comp64(double_of_bits(0xc0100000, 0x00000000) * double_of_bits(0x7fcfffff, 0xfffffffd), 0xffefffff, 0xfffffffd, STR(__LINE__)); // -0x1p+2 * 0x1.ffffffffffffdp+1021 = -0x1.ffffffffffffdp+1023
  comp64(double_of_bits(0xffcfffff, 0xfffffffd) * double_of_bits(0x40100000, 0x00000000), 0xffefffff, 0xfffffffd, STR(__LINE__)); // -0x1.ffffffffffffdp+1021 * 0x1p+2 = -0x1.ffffffffffffdp+1023
  comp64(double_of_bits(0x40100000, 0x00000000) * double_of_bits(0xffcfffff, 0xfffffffd), 0xffefffff, 0xfffffffd, STR(__LINE__)); // 0x1p+2 * -0x1.ffffffffffffdp+1021 = -0x1.ffffffffffffdp+1023
}

void f161(void) {
  comp64(double_of_bits(0xffcfffff, 0xfffffffd) * double_of_bits(0xc0100000, 0x00000000), 0x7fefffff, 0xfffffffd, STR(__LINE__)); // -0x1.ffffffffffffdp+1021 * -0x1p+2 = 0x1.ffffffffffffdp+1023
  comp64(double_of_bits(0xc0100000, 0x00000000) * double_of_bits(0xffcfffff, 0xfffffffd), 0x7fefffff, 0xfffffffd, STR(__LINE__)); // -0x1p+2 * -0x1.ffffffffffffdp+1021 = 0x1.ffffffffffffdp+1023
  comp64(double_of_bits(0x3f600000, 0x00000000) * double_of_bits(0x40700000, 0x00000000), 0x3fe00000, 0x00000000, STR(__LINE__)); // 0x1p-9 * 0x1p+8 = 0x1p-1
  comp64(double_of_bits(0x40700000, 0x00000000) * double_of_bits(0x3f600000, 0x00000000), 0x3fe00000, 0x00000000, STR(__LINE__)); // 0x1p+8 * 0x1p-9 = 0x1p-1
  comp64(double_of_bits(0xbf600000, 0x00000000) * double_of_bits(0xc0700000, 0x00000000), 0x3fe00000, 0x00000000, STR(__LINE__)); // -0x1p-9 * -0x1p+8 = 0x1p-1
  comp64(double_of_bits(0xc0700000, 0x00000000) * double_of_bits(0xbf600000, 0x00000000), 0x3fe00000, 0x00000000, STR(__LINE__)); // -0x1p+8 * -0x1p-9 = 0x1p-1
  comp64(double_of_bits(0xbf600000, 0x00000000) * double_of_bits(0x40700000, 0x00000000), 0xbfe00000, 0x00000000, STR(__LINE__)); // -0x1p-9 * 0x1p+8 = -0x1p-1
  comp64(double_of_bits(0x40700000, 0x00000000) * double_of_bits(0xbf600000, 0x00000000), 0xbfe00000, 0x00000000, STR(__LINE__)); // 0x1p+8 * -0x1p-9 = -0x1p-1
  comp64(double_of_bits(0xc0700000, 0x00000000) * double_of_bits(0x3f600000, 0x00000000), 0xbfe00000, 0x00000000, STR(__LINE__)); // -0x1p+8 * 0x1p-9 = -0x1p-1
  comp64(double_of_bits(0x3f600000, 0x00000000) * double_of_bits(0xc0700000, 0x00000000), 0xbfe00000, 0x00000000, STR(__LINE__)); // 0x1p-9 * -0x1p+8 = -0x1p-1
}

void f162(void) {
  comp64(double_of_bits(0x3fc00000, 0x00000000) * double_of_bits(0x3f900000, 0x00000000), 0x3f600000, 0x00000000, STR(__LINE__)); // 0x1p-3 * 0x1p-6 = 0x1p-9
  comp64(double_of_bits(0x3f900000, 0x00000000) * double_of_bits(0x3fc00000, 0x00000000), 0x3f600000, 0x00000000, STR(__LINE__)); // 0x1p-6 * 0x1p-3 = 0x1p-9
  comp64(double_of_bits(0xbfc00000, 0x00000000) * double_of_bits(0xbf900000, 0x00000000), 0x3f600000, 0x00000000, STR(__LINE__)); // -0x1p-3 * -0x1p-6 = 0x1p-9
  comp64(double_of_bits(0xbf900000, 0x00000000) * double_of_bits(0xbfc00000, 0x00000000), 0x3f600000, 0x00000000, STR(__LINE__)); // -0x1p-6 * -0x1p-3 = 0x1p-9
  comp64(double_of_bits(0xbfc00000, 0x00000000) * double_of_bits(0x3f900000, 0x00000000), 0xbf600000, 0x00000000, STR(__LINE__)); // -0x1p-3 * 0x1p-6 = -0x1p-9
  comp64(double_of_bits(0x3f900000, 0x00000000) * double_of_bits(0xbfc00000, 0x00000000), 0xbf600000, 0x00000000, STR(__LINE__)); // 0x1p-6 * -0x1p-3 = -0x1p-9
  comp64(double_of_bits(0xbf900000, 0x00000000) * double_of_bits(0x3fc00000, 0x00000000), 0xbf600000, 0x00000000, STR(__LINE__)); // -0x1p-6 * 0x1p-3 = -0x1p-9
  comp64(double_of_bits(0x3fc00000, 0x00000000) * double_of_bits(0xbf900000, 0x00000000), 0xbf600000, 0x00000000, STR(__LINE__)); // 0x1p-3 * -0x1p-6 = -0x1p-9
  comp64(double_of_bits(0x40200000, 0x00000000) * double_of_bits(0x40800000, 0x00000000), 0x40b00000, 0x00000000, STR(__LINE__)); // 0x1p+3 * 0x1p+9 = 0x1p+12
  comp64(double_of_bits(0x40800000, 0x00000000) * double_of_bits(0x40200000, 0x00000000), 0x40b00000, 0x00000000, STR(__LINE__)); // 0x1p+9 * 0x1p+3 = 0x1p+12
}

void f163(void) {
  comp64(double_of_bits(0xc0200000, 0x00000000) * double_of_bits(0xc0800000, 0x00000000), 0x40b00000, 0x00000000, STR(__LINE__)); // -0x1p+3 * -0x1p+9 = 0x1p+12
  comp64(double_of_bits(0xc0800000, 0x00000000) * double_of_bits(0xc0200000, 0x00000000), 0x40b00000, 0x00000000, STR(__LINE__)); // -0x1p+9 * -0x1p+3 = 0x1p+12
  comp64(double_of_bits(0xc0200000, 0x00000000) * double_of_bits(0x40800000, 0x00000000), 0xc0b00000, 0x00000000, STR(__LINE__)); // -0x1p+3 * 0x1p+9 = -0x1p+12
  comp64(double_of_bits(0x40800000, 0x00000000) * double_of_bits(0xc0200000, 0x00000000), 0xc0b00000, 0x00000000, STR(__LINE__)); // 0x1p+9 * -0x1p+3 = -0x1p+12
  comp64(double_of_bits(0xc0800000, 0x00000000) * double_of_bits(0x40200000, 0x00000000), 0xc0b00000, 0x00000000, STR(__LINE__)); // -0x1p+9 * 0x1p+3 = -0x1p+12
  comp64(double_of_bits(0x40200000, 0x00000000) * double_of_bits(0xc0800000, 0x00000000), 0xc0b00000, 0x00000000, STR(__LINE__)); // 0x1p+3 * -0x1p+9 = -0x1p+12
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x0p+0 = 0x0p+0
}

void f164(void) {
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x0.0000000000001p-1022 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x0.0000000000001p-1022 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x0.0000000000001p-1022 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x0.0000000000001p-1022 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x00000000, 0x00000002), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x0.0000000000002p-1022 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000002) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000002p-1022 * 0x0p+0 = 0x0p+0
}

void f165(void) {
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x80000000, 0x00000002), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x0.0000000000002p-1022 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000002) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000002p-1022 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x80000000, 0x00000002), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x0.0000000000002p-1022 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000002) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000002p-1022 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x00000000, 0x00000002), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x0.0000000000002p-1022 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000002) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000002p-1022 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000003) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000003p-1022 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x00000000, 0x00000003), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x0.0000000000003p-1022 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000003) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000003p-1022 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x80000000, 0x00000003), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x0.0000000000003p-1022 = 0x0p+0
}

void f166(void) {
  comp64(double_of_bits(0x80000000, 0x00000003) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000003p-1022 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x80000000, 0x00000003), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x0.0000000000003p-1022 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000003) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000003p-1022 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x00000000, 0x00000003), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x0.0000000000003p-1022 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x00000000, 0x00000004), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x0.0000000000004p-1022 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000004) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000004p-1022 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x80000000, 0x00000004), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x0.0000000000004p-1022 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000004) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000004p-1022 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000004) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000004p-1022 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x00000000, 0x00000004), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x0.0000000000004p-1022 = -0x0p+0
}

void f167(void) {
  comp64(double_of_bits(0x80000000, 0x00000004) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000004p-1022 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x80000000, 0x00000004), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x0.0000000000004p-1022 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x000fffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x0.fffffffffffffp-1022 = 0x0p+0
  comp64(double_of_bits(0x000fffff, 0xffffffff) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x800fffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x0.fffffffffffffp-1022 = 0x0p+0
  comp64(double_of_bits(0x800fffff, 0xffffffff) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x800fffff, 0xffffffff) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x800fffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x0.fffffffffffffp-1022 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x3ff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p+0 = 0x0p+0
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p+0 * 0x0p+0 = 0x0p+0
}

void f168(void) {
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0xbff00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p+0 = 0x0p+0
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p+0 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x3ff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x1p+0 = -0x0p+0
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p+0 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p+0 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0xbff00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1p+0 = -0x0p+0
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p+1 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0xc0000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1p+1 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x40080000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.8p+1 = 0x0p+0
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 * 0x0p+0 = 0x0p+0
}

void f169(void) {
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0xc0080000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.8p+1 = 0x0p+0
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0xc0080000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1.8p+1 = -0x0p+0
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x40080000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x1.8p+1 = -0x0p+0
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.8p+1 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x40100000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p+2 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x40100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p+2 = 0x0p+0
  comp64(double_of_bits(0xc0100000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p+2 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0xc0100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p+2 = 0x0p+0
}

void f170(void) {
  comp64(double_of_bits(0xc0100000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p+2 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0xc0100000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1p+2 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x40100000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x1p+2 = -0x0p+0
  comp64(double_of_bits(0x40100000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p+2 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x40140000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.4p+2 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x40140000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.4p+2 = 0x0p+0
  comp64(double_of_bits(0xc0140000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.4p+2 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0xc0140000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.4p+2 = 0x0p+0
  comp64(double_of_bits(0xc0140000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1.4p+2 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0xc0140000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1.4p+2 = -0x0p+0
}

void f171(void) {
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x40140000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x1.4p+2 = -0x0p+0
  comp64(double_of_bits(0x40140000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.4p+2 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x40180000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.8p+2 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x40180000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.8p+2 = 0x0p+0
  comp64(double_of_bits(0xc0180000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.8p+2 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0xc0180000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.8p+2 = 0x0p+0
  comp64(double_of_bits(0xc0180000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1.8p+2 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0xc0180000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1.8p+2 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x40180000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x1.8p+2 = -0x0p+0
  comp64(double_of_bits(0x40180000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.8p+2 * -0x0p+0 = -0x0p+0
}

void f172(void) {
  comp64(double_of_bits(0x401c0000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.cp+2 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x401c0000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.cp+2 = 0x0p+0
  comp64(double_of_bits(0xc01c0000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.cp+2 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0xc01c0000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.cp+2 = 0x0p+0
  comp64(double_of_bits(0xc01c0000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1.cp+2 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0xc01c0000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1.cp+2 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x401c0000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x1.cp+2 = -0x0p+0
  comp64(double_of_bits(0x401c0000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.cp+2 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x40200000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p+3 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x40200000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p+3 = 0x0p+0
}

void f173(void) {
  comp64(double_of_bits(0xc0200000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p+3 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0xc0200000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p+3 = 0x0p+0
  comp64(double_of_bits(0xc0200000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p+3 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0xc0200000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1p+3 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x40200000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x1p+3 = -0x0p+0
  comp64(double_of_bits(0x40200000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p+3 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x7fe00000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p+1023 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x7fe00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p+1023 = 0x0p+0
  comp64(double_of_bits(0xffe00000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p+1023 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0xffe00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p+1023 = 0x0p+0
}

void f174(void) {
  comp64(double_of_bits(0xffe00000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p+1023 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0xffe00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1p+1023 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x7fe00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x1p+1023 = -0x0p+0
  comp64(double_of_bits(0x7fe00000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p+1023 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x7fd00000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p+1022 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x7fd00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p+1022 = 0x0p+0
  comp64(double_of_bits(0xffd00000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p+1022 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0xffd00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p+1022 = 0x0p+0
  comp64(double_of_bits(0xffd00000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p+1022 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0xffd00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1p+1022 = -0x0p+0
}

void f175(void) {
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x7fd00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x1p+1022 = -0x0p+0
  comp64(double_of_bits(0x7fd00000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p+1022 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x7fdfffff, 0xffffffff) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1022 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x7fdfffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.fffffffffffffp+1022 = 0x0p+0
  comp64(double_of_bits(0xffdfffff, 0xffffffff) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1022 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0xffdfffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.fffffffffffffp+1022 = 0x0p+0
  comp64(double_of_bits(0xffdfffff, 0xffffffff) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1022 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0xffdfffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1.fffffffffffffp+1022 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x7fdfffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x1.fffffffffffffp+1022 = -0x0p+0
  comp64(double_of_bits(0x7fdfffff, 0xffffffff) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1022 * -0x0p+0 = -0x0p+0
}

void f176(void) {
  comp64(double_of_bits(0x7fcfffff, 0xffffffff) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1021 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x7fcfffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.fffffffffffffp+1021 = 0x0p+0
  comp64(double_of_bits(0xffcfffff, 0xffffffff) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1021 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0xffcfffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.fffffffffffffp+1021 = 0x0p+0
  comp64(double_of_bits(0xffcfffff, 0xffffffff) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1021 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0xffcfffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1.fffffffffffffp+1021 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x7fcfffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x1.fffffffffffffp+1021 = -0x0p+0
  comp64(double_of_bits(0x7fcfffff, 0xffffffff) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1021 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x7fefffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.fffffffffffffp+1023 = 0x0p+0
  comp64(double_of_bits(0x7fefffff, 0xffffffff) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 * 0x0p+0 = 0x0p+0
}

void f177(void) {
  comp64(double_of_bits(0xffefffff, 0xffffffff) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0xffefffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.fffffffffffffp+1023 = 0x0p+0
  comp64(double_of_bits(0xffefffff, 0xffffffff) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0xffefffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1.fffffffffffffp+1023 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x7fefffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x1.fffffffffffffp+1023 = -0x0p+0
  comp64(double_of_bits(0x7fefffff, 0xffffffff) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p-1022 = 0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p-1022 = 0x0p+0
}

void f178(void) {
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1p-1022 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x1p-1022 = -0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x00200000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p-1021 = 0x0p+0
  comp64(double_of_bits(0x00200000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-1021 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80200000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-1021 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x80200000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p-1021 = 0x0p+0
  comp64(double_of_bits(0x80200000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-1021 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x80200000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1p-1021 = -0x0p+0
}

void f179(void) {
  comp64(double_of_bits(0x00200000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-1021 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x00200000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x1p-1021 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x001fffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.fffffffffffffp-1022 = 0x0p+0
  comp64(double_of_bits(0x001fffff, 0xffffffff) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp-1022 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x801fffff, 0xffffffff) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp-1022 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x801fffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.fffffffffffffp-1022 = 0x0p+0
  comp64(double_of_bits(0x801fffff, 0xffffffff) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp-1022 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x801fffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1.fffffffffffffp-1022 = -0x0p+0
  comp64(double_of_bits(0x001fffff, 0xffffffff) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp-1022 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x001fffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x1.fffffffffffffp-1022 = -0x0p+0
}

void f180(void) {
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x00100000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.0000000000001p-1022 = 0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000001) * double_of_bits(0x00000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p-1022 * 0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0x80000000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p-1022 * -0x0p+0 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x80100000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.0000000000001p-1022 = 0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0x00000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p-1022 * 0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x80100000, 0x00000001), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -0x1.0000000000001p-1022 = -0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000001) * double_of_bits(0x80000000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p-1022 * -0x0p+0 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x00100000, 0x00000001), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0p+0 * 0x1.0000000000001p-1022 = -0x0p+0
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // inf * 0x0p+0 = nan
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x7ff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x0p+0 * inf = nan
}

void f181(void) {
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0xfff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x0p+0 * -inf = nan
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -inf * -0x0p+0 = nan
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x7ff00000, 0x00000000), 0xfff80000, 0x00000000, STR(__LINE__)); // -0x0p+0 * inf = -nan
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0xfff80000, 0x00000000, STR(__LINE__)); // inf * -0x0p+0 = -nan
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0xfff00000, 0x00000000), 0xfff80000, 0x00000000, STR(__LINE__)); // 0x0p+0 * -inf = -nan
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0xfff80000, 0x00000000, STR(__LINE__)); // -inf * 0x0p+0 = -nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) * double_of_bits(0x00000000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan * 0x0p+0 = nan
  comp64(double_of_bits(0x00000000, 0x00000000) * double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x0p+0 * nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) * double_of_bits(0x80000000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan * -0x0p+0 = nan
  comp64(double_of_bits(0x80000000, 0x00000000) * double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x0p+0 * nan = nan
}

void f182(void) {
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf * inf = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x7ff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf * inf = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // inf * -inf = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0xfff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf * -inf = inf
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * inf = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf * 0x0.0000000000001p-1022 = inf
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xfff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * -inf = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf * -0x0.0000000000001p-1022 = inf
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x7ff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * inf = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0xfff00000, 0x00000000, STR(__LINE__)); // inf * -0x0.0000000000001p-1022 = -inf
}

void f183(void) {
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf * 0x0.0000000000001p-1022 = -inf
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * -inf = -inf
  comp64(double_of_bits(0x00000000, 0x00000002) * double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000002p-1022 * inf = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000002), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf * 0x0.0000000000002p-1022 = inf
  comp64(double_of_bits(0x80000000, 0x00000002) * double_of_bits(0xfff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000002p-1022 * -inf = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000002), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf * -0x0.0000000000002p-1022 = inf
  comp64(double_of_bits(0x80000000, 0x00000002) * double_of_bits(0x7ff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000002p-1022 * inf = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000002), 0xfff00000, 0x00000000, STR(__LINE__)); // inf * -0x0.0000000000002p-1022 = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000002), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf * 0x0.0000000000002p-1022 = -inf
  comp64(double_of_bits(0x00000000, 0x00000002) * double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000002p-1022 * -inf = -inf
}

void f184(void) {
  comp64(double_of_bits(0x00000000, 0x00000003) * double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000003p-1022 * inf = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000003), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf * 0x0.0000000000003p-1022 = inf
  comp64(double_of_bits(0x80000000, 0x00000003) * double_of_bits(0xfff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000003p-1022 * -inf = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000003), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf * -0x0.0000000000003p-1022 = inf
  comp64(double_of_bits(0x80000000, 0x00000003) * double_of_bits(0x7ff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000003p-1022 * inf = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000003), 0xfff00000, 0x00000000, STR(__LINE__)); // inf * -0x0.0000000000003p-1022 = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000003), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf * 0x0.0000000000003p-1022 = -inf
  comp64(double_of_bits(0x00000000, 0x00000003) * double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000003p-1022 * -inf = -inf
  comp64(double_of_bits(0x00000000, 0x00000004) * double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000004p-1022 * inf = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000004), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf * 0x0.0000000000004p-1022 = inf
}

void f185(void) {
  comp64(double_of_bits(0x80000000, 0x00000004) * double_of_bits(0xfff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000004p-1022 * -inf = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000004), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf * -0x0.0000000000004p-1022 = inf
  comp64(double_of_bits(0x80000000, 0x00000004) * double_of_bits(0x7ff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x0.0000000000004p-1022 * inf = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x80000000, 0x00000004), 0xfff00000, 0x00000000, STR(__LINE__)); // inf * -0x0.0000000000004p-1022 = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x00000000, 0x00000004), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf * 0x0.0000000000004p-1022 = -inf
  comp64(double_of_bits(0x00000000, 0x00000004) * double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x0.0000000000004p-1022 * -inf = -inf
  comp64(double_of_bits(0x000fffff, 0xffffffff) * double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 * inf = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x000fffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf * 0x0.fffffffffffffp-1022 = inf
  comp64(double_of_bits(0x800fffff, 0xffffffff) * double_of_bits(0xfff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 * -inf = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x800fffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf * -0x0.fffffffffffffp-1022 = inf
}

void f186(void) {
  comp64(double_of_bits(0x800fffff, 0xffffffff) * double_of_bits(0x7ff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 * inf = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x800fffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // inf * -0x0.fffffffffffffp-1022 = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x000fffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf * 0x0.fffffffffffffp-1022 = -inf
  comp64(double_of_bits(0x000fffff, 0xffffffff) * double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 * -inf = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x3ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf * 0x1p+0 = inf
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p+0 * inf = inf
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x7ff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1p+1 * inf = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0xc0000000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // inf * -0x1p+1 = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0xc0080000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // inf * -0x1.8p+1 = -inf
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0x7ff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 * inf = -inf
}

void f187(void) {
  comp64(double_of_bits(0xc0100000, 0x00000000) * double_of_bits(0xfff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1p+2 * -inf = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0xc0100000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf * -0x1p+2 = inf
  comp64(double_of_bits(0x40140000, 0x00000000) * double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.4p+2 * inf = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x40140000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf * 0x1.4p+2 = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x40180000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf * 0x1.8p+2 = -inf
  comp64(double_of_bits(0x40180000, 0x00000000) * double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.8p+2 * -inf = -inf
  comp64(double_of_bits(0x401c0000, 0x00000000) * double_of_bits(0xfff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.cp+2 * -inf = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x401c0000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -inf * 0x1.cp+2 = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0xc0200000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf * -0x1p+3 = inf
  comp64(double_of_bits(0xc0200000, 0x00000000) * double_of_bits(0xfff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1p+3 * -inf = inf
}

void f188(void) {
  comp64(double_of_bits(0x7fe00000, 0x00000000) * double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 * inf = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x7fe00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf * 0x1p+1023 = inf
  comp64(double_of_bits(0xffd00000, 0x00000000) * double_of_bits(0x7ff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1p+1022 * inf = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0xffd00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // inf * -0x1p+1022 = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0xffe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // inf * -0x1p+1023 = -inf
  comp64(double_of_bits(0xffe00000, 0x00000000) * double_of_bits(0x7ff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 * inf = -inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0xffd00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf * -0x1p+1022 = inf
  comp64(double_of_bits(0xffd00000, 0x00000000) * double_of_bits(0xfff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1p+1022 * -inf = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x7fdfffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf * 0x1.fffffffffffffp+1022 = inf
  comp64(double_of_bits(0x7fdfffff, 0xffffffff) * double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1022 * inf = inf
}

void f189(void) {
  comp64(double_of_bits(0xffcfffff, 0xffffffff) * double_of_bits(0x7ff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1021 * inf = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0xffcfffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // inf * -0x1.fffffffffffffp+1021 = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0xffefffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // inf * -0x1.fffffffffffffp+1023 = -inf
  comp64(double_of_bits(0xffefffff, 0xffffffff) * double_of_bits(0x7ff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 * inf = -inf
  comp64(double_of_bits(0xffefffff, 0xffffffff) * double_of_bits(0xfff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 * -inf = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0xffefffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf * -0x1.fffffffffffffp+1023 = inf
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p-1022 * inf = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf * 0x1p-1022 = inf
  comp64(double_of_bits(0x80200000, 0x00000000) * double_of_bits(0x7ff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1p-1021 * inf = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x80200000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // inf * -0x1p-1021 = -inf
}

void f190(void) {
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf * -0x1p-1022 = inf
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0xfff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1p-1022 * -inf = inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x001fffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // inf * 0x1.fffffffffffffp-1022 = inf
  comp64(double_of_bits(0x001fffff, 0xffffffff) * double_of_bits(0x7ff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp-1022 * inf = inf
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0x7ff00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p-1022 * inf = -inf
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x80100000, 0x00000001), 0xfff00000, 0x00000000, STR(__LINE__)); // inf * -0x1.0000000000001p-1022 = -inf
  comp64(double_of_bits(0x801fffff, 0xffffffff) * double_of_bits(0xfff00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp-1022 * -inf = inf
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x801fffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // -inf * -0x1.fffffffffffffp-1022 = inf
  comp64(double_of_bits(0x7ff80000, 0x00000000) * double_of_bits(0x7ff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan * inf = nan
  comp64(double_of_bits(0x7ff00000, 0x00000000) * double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // inf * nan = nan
}

void f191(void) {
  comp64(double_of_bits(0x7ff80000, 0x00000000) * double_of_bits(0xfff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan * -inf = nan
  comp64(double_of_bits(0xfff00000, 0x00000000) * double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -inf * nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) * double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan * nan = nan
  comp64(double_of_bits(0x000fffff, 0xffffffff) * double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 * nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) * double_of_bits(0x000fffff, 0xffffffff), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan * 0x0.fffffffffffffp-1022 = nan
  comp64(double_of_bits(0x800fffff, 0xffffffff) * double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 * nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) * double_of_bits(0x800fffff, 0xffffffff), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan * -0x0.fffffffffffffp-1022 = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan * 0x0.0000000000001p-1022 = nan
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan * -0x0.0000000000001p-1022 = nan
}

void f192(void) {
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) * double_of_bits(0x3ff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan * 0x1p+0 = nan
  comp64(double_of_bits(0x3ff00000, 0x00000000) * double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x1p+0 * nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) * double_of_bits(0xbff00000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan * -0x1p+0 = nan
  comp64(double_of_bits(0xbff00000, 0x00000000) * double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x1p+0 * nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) * double_of_bits(0x7fefffff, 0xffffffff), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan * 0x1.fffffffffffffp+1023 = nan
  comp64(double_of_bits(0x7fefffff, 0xffffffff) * double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 * nan = nan
  comp64(double_of_bits(0x7ff80000, 0x00000000) * double_of_bits(0xffefffff, 0xffffffff), 0x7ff80000, 0x00000000, STR(__LINE__)); // nan * -0x1.fffffffffffffp+1023 = nan
  comp64(double_of_bits(0xffefffff, 0xffffffff) * double_of_bits(0x7ff80000, 0x00000000), 0x7ff80000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 * nan = nan
  comp64(double_of_bits(0x7fe00000, 0x00000000) * double_of_bits(0x40000000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 * 0x1p+1 = inf
}

void f193(void) {
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x7fe00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p+1 * 0x1p+1023 = inf
  comp64(double_of_bits(0x7fe00000, 0x00000000) * double_of_bits(0x7fe00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 * 0x1p+1023 = inf
  comp64(double_of_bits(0x7fe00000, 0x00000009) * double_of_bits(0x7fefffff, 0xfffffffa), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000009p+1023 * 0x1.ffffffffffffap+1023 = inf
  comp64(double_of_bits(0x7fefffff, 0xfffffffa) * double_of_bits(0x7fe00000, 0x00000009), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffap+1023 * 0x1.0000000000009p+1023 = inf
  comp64(double_of_bits(0x7fe00000, 0x00000000) * double_of_bits(0x7fefffff, 0xfffffffe), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 * 0x1.ffffffffffffep+1023 = inf
  comp64(double_of_bits(0x7fefffff, 0xfffffffe) * double_of_bits(0x7fe00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffep+1023 * 0x1p+1023 = inf
  comp64(double_of_bits(0xc013ffff, 0xfffffffe) * double_of_bits(0xffe00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.3fffffffffffep+2 * -0x1p+1023 = inf
  comp64(double_of_bits(0xffe00000, 0x00000000) * double_of_bits(0xc013ffff, 0xfffffffe), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 * -0x1.3fffffffffffep+2 = inf
  comp64(double_of_bits(0xc0220000, 0x00000001) * double_of_bits(0xffe00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.2000000000001p+3 * -0x1p+1023 = inf
  comp64(double_of_bits(0xffe00000, 0x00000000) * double_of_bits(0xc0220000, 0x00000001), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 * -0x1.2000000000001p+3 = inf
}

void f194(void) {
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0xffe00000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.8p+1 * -0x1p+1023 = inf
  comp64(double_of_bits(0xffe00000, 0x00000000) * double_of_bits(0xc0080000, 0x00000000), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 * -0x1.8p+1 = inf
  comp64(double_of_bits(0xffe00000, 0x00000005) * double_of_bits(0xffe00000, 0x00000001), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000005p+1023 * -0x1.0000000000001p+1023 = inf
  comp64(double_of_bits(0xffe00000, 0x00000001) * double_of_bits(0xffe00000, 0x00000005), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+1023 * -0x1.0000000000005p+1023 = inf
  comp64(double_of_bits(0xffefffff, 0xffffffff) * double_of_bits(0xffefffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 * -0x1.fffffffffffffp+1023 = inf
  comp64(double_of_bits(0xffefffff, 0xfffffffd) * double_of_bits(0xffe00000, 0x00000001), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffdp+1023 * -0x1.0000000000001p+1023 = inf
  comp64(double_of_bits(0xffe00000, 0x00000001) * double_of_bits(0xffefffff, 0xfffffffd), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+1023 * -0x1.ffffffffffffdp+1023 = inf
  comp64(double_of_bits(0xffefffff, 0xfffffffd) * double_of_bits(0xc0080000, 0x00000001), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffdp+1023 * -0x1.8000000000001p+1 = inf
  comp64(double_of_bits(0xc0080000, 0x00000001) * double_of_bits(0xffefffff, 0xfffffffd), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.8000000000001p+1 * -0x1.ffffffffffffdp+1023 = inf
  comp64(double_of_bits(0xc007ffff, 0xfffffffe) * double_of_bits(0x7fe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.7fffffffffffep+1 * 0x1p+1023 = -inf
}

void f195(void) {
  comp64(double_of_bits(0x7fe00000, 0x00000000) * double_of_bits(0xc007ffff, 0xfffffffe), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 * -0x1.7fffffffffffep+1 = -inf
  comp64(double_of_bits(0xc01bffff, 0xfffffff9) * double_of_bits(0x7fe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.bfffffffffff9p+2 * 0x1p+1023 = -inf
  comp64(double_of_bits(0x7fe00000, 0x00000000) * double_of_bits(0xc01bffff, 0xfffffff9), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 * -0x1.bfffffffffff9p+2 = -inf
  comp64(double_of_bits(0xc0220000, 0x00000000) * double_of_bits(0x7fe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.2p+3 * 0x1p+1023 = -inf
  comp64(double_of_bits(0x7fe00000, 0x00000000) * double_of_bits(0xc0220000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 * -0x1.2p+3 = -inf
  comp64(double_of_bits(0xffefffff, 0xfffffffd) * double_of_bits(0x7fe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffdp+1023 * 0x1p+1023 = -inf
  comp64(double_of_bits(0x7fe00000, 0x00000000) * double_of_bits(0xffefffff, 0xfffffffd), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 * -0x1.ffffffffffffdp+1023 = -inf
  comp64(double_of_bits(0xffcfffff, 0xfffffff9) * double_of_bits(0x7fe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffff9p+1021 * 0x1p+1023 = -inf
  comp64(double_of_bits(0x7fe00000, 0x00000000) * double_of_bits(0xffcfffff, 0xfffffff9), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 * -0x1.ffffffffffff9p+1021 = -inf
  comp64(double_of_bits(0xffdfffff, 0xfffffff7) * double_of_bits(0x7fd00000, 0x00000001), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffff7p+1022 * 0x1.0000000000001p+1022 = -inf
}

void f196(void) {
  comp64(double_of_bits(0x7fd00000, 0x00000001) * double_of_bits(0xffdfffff, 0xfffffff7), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+1022 * -0x1.ffffffffffff7p+1022 = -inf
  comp64(double_of_bits(0x7fe00000, 0x00000000) * double_of_bits(0xffd00000, 0x00000004), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 * -0x1.0000000000004p+1022 = -inf
  comp64(double_of_bits(0xffd00000, 0x00000004) * double_of_bits(0x7fe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000004p+1022 * 0x1p+1023 = -inf
  comp64(double_of_bits(0x7fe00000, 0x00000000) * double_of_bits(0xffd00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 * -0x1p+1022 = -inf
  comp64(double_of_bits(0xffd00000, 0x00000000) * double_of_bits(0x7fe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1p+1022 * 0x1p+1023 = -inf
  comp64(double_of_bits(0x7fe00000, 0x00000000) * double_of_bits(0xffe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1p+1023 * -0x1p+1023 = -inf
  comp64(double_of_bits(0xffe00000, 0x00000000) * double_of_bits(0x7fe00000, 0x00000000), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1p+1023 * 0x1p+1023 = -inf
  comp64(double_of_bits(0x7fe00000, 0x00000009) * double_of_bits(0xc0180000, 0x00000002), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000009p+1023 * -0x1.8000000000002p+2 = -inf
  comp64(double_of_bits(0xc0180000, 0x00000002) * double_of_bits(0x7fe00000, 0x00000009), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.8000000000002p+2 * 0x1.0000000000009p+1023 = -inf
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x7fefffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 * 0x1.fffffffffffffp+1023 = inf
}

void f197(void) {
  comp64(double_of_bits(0x7fefffff, 0xffffffff) * double_of_bits(0x3ff00000, 0x00000001), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 * 0x1.0000000000001p+0 = inf
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0xffefffff, 0xffffffff), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+0 * -0x1.fffffffffffffp+1023 = inf
  comp64(double_of_bits(0xffefffff, 0xffffffff) * double_of_bits(0xbff00000, 0x00000001), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 * -0x1.0000000000001p+0 = inf
  comp64(double_of_bits(0x3ff00000, 0x00000002) * double_of_bits(0x7fefffff, 0xfffffffe), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000002p+0 * 0x1.ffffffffffffep+1023 = inf
  comp64(double_of_bits(0x7fefffff, 0xfffffffe) * double_of_bits(0x3ff00000, 0x00000002), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffep+1023 * 0x1.0000000000002p+0 = inf
  comp64(double_of_bits(0xbff00000, 0x00000002) * double_of_bits(0xffefffff, 0xfffffffe), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000002p+0 * -0x1.ffffffffffffep+1023 = inf
  comp64(double_of_bits(0xffefffff, 0xfffffffe) * double_of_bits(0xbff00000, 0x00000002), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffep+1023 * -0x1.0000000000002p+0 = inf
  comp64(double_of_bits(0x3ff00000, 0x00000004) * double_of_bits(0x7fefffff, 0xfffffffc), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000004p+0 * 0x1.ffffffffffffcp+1023 = inf
  comp64(double_of_bits(0x7fefffff, 0xfffffffc) * double_of_bits(0x3ff00000, 0x00000004), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffcp+1023 * 0x1.0000000000004p+0 = inf
  comp64(double_of_bits(0xbff00000, 0x00000004) * double_of_bits(0xffefffff, 0xfffffffc), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000004p+0 * -0x1.ffffffffffffcp+1023 = inf
}

void f198(void) {
  comp64(double_of_bits(0xffefffff, 0xfffffffc) * double_of_bits(0xbff00000, 0x00000004), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffcp+1023 * -0x1.0000000000004p+0 = inf
  comp64(double_of_bits(0x3ff00000, 0x00000008) * double_of_bits(0x7fefffff, 0xfffffff8), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000008p+0 * 0x1.ffffffffffff8p+1023 = inf
  comp64(double_of_bits(0x7fefffff, 0xfffffff8) * double_of_bits(0x3ff00000, 0x00000008), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffff8p+1023 * 0x1.0000000000008p+0 = inf
  comp64(double_of_bits(0xbff00000, 0x00000008) * double_of_bits(0xffefffff, 0xfffffff8), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000008p+0 * -0x1.ffffffffffff8p+1023 = inf
  comp64(double_of_bits(0xffefffff, 0xfffffff8) * double_of_bits(0xbff00000, 0x00000008), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffff8p+1023 * -0x1.0000000000008p+0 = inf
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x7fefffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+0 * 0x1.fffffffffffffp+1023 = -inf
  comp64(double_of_bits(0x7fefffff, 0xffffffff) * double_of_bits(0xbff00000, 0x00000001), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1023 * -0x1.0000000000001p+0 = -inf
  comp64(double_of_bits(0xffefffff, 0xffffffff) * double_of_bits(0x3ff00000, 0x00000001), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1023 * 0x1.0000000000001p+0 = -inf
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0xffefffff, 0xffffffff), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 * -0x1.fffffffffffffp+1023 = -inf
  comp64(double_of_bits(0xbff00000, 0x00000002) * double_of_bits(0x7fefffff, 0xfffffffe), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000002p+0 * 0x1.ffffffffffffep+1023 = -inf
}

void f199(void) {
  comp64(double_of_bits(0x7fefffff, 0xfffffffe) * double_of_bits(0xbff00000, 0x00000002), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffep+1023 * -0x1.0000000000002p+0 = -inf
  comp64(double_of_bits(0xffefffff, 0xfffffffe) * double_of_bits(0x3ff00000, 0x00000002), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffep+1023 * 0x1.0000000000002p+0 = -inf
  comp64(double_of_bits(0x3ff00000, 0x00000002) * double_of_bits(0xffefffff, 0xfffffffe), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000002p+0 * -0x1.ffffffffffffep+1023 = -inf
  comp64(double_of_bits(0xbff00000, 0x00000004) * double_of_bits(0x7fefffff, 0xfffffffc), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000004p+0 * 0x1.ffffffffffffcp+1023 = -inf
  comp64(double_of_bits(0x7fefffff, 0xfffffffc) * double_of_bits(0xbff00000, 0x00000004), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffcp+1023 * -0x1.0000000000004p+0 = -inf
  comp64(double_of_bits(0xffefffff, 0xfffffffc) * double_of_bits(0x3ff00000, 0x00000004), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffcp+1023 * 0x1.0000000000004p+0 = -inf
  comp64(double_of_bits(0x3ff00000, 0x00000004) * double_of_bits(0xffefffff, 0xfffffffc), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000004p+0 * -0x1.ffffffffffffcp+1023 = -inf
  comp64(double_of_bits(0xbff00000, 0x00000008) * double_of_bits(0x7fefffff, 0xfffffff8), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000008p+0 * 0x1.ffffffffffff8p+1023 = -inf
  comp64(double_of_bits(0x7fefffff, 0xfffffff8) * double_of_bits(0xbff00000, 0x00000008), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffff8p+1023 * -0x1.0000000000008p+0 = -inf
  comp64(double_of_bits(0xffefffff, 0xfffffff8) * double_of_bits(0x3ff00000, 0x00000008), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffff8p+1023 * 0x1.0000000000008p+0 = -inf
}

void f200(void) {
  comp64(double_of_bits(0x3ff00000, 0x00000008) * double_of_bits(0xffefffff, 0xfffffff8), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000008p+0 * -0x1.ffffffffffff8p+1023 = -inf
  comp64(double_of_bits(0x7fdfffff, 0xfffffffd) * double_of_bits(0xc0000000, 0x00000008), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffdp+1022 * -0x1.0000000000008p+1 = -inf
  comp64(double_of_bits(0xc0000000, 0x00000008) * double_of_bits(0x7fdfffff, 0xfffffffd), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000008p+1 * 0x1.ffffffffffffdp+1022 = -inf
  comp64(double_of_bits(0x3fffffff, 0xfffffffc) * double_of_bits(0x7fe00000, 0x00000002), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffcp+0 * 0x1.0000000000002p+1023 = inf
  comp64(double_of_bits(0x7fe00000, 0x00000002) * double_of_bits(0x3fffffff, 0xfffffffc), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000002p+1023 * 0x1.ffffffffffffcp+0 = inf
  comp64(double_of_bits(0xbfffffff, 0xfffffffc) * double_of_bits(0xffe00000, 0x00000002), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffcp+0 * -0x1.0000000000002p+1023 = inf
  comp64(double_of_bits(0xffe00000, 0x00000002) * double_of_bits(0xbfffffff, 0xfffffffc), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000002p+1023 * -0x1.ffffffffffffcp+0 = inf
  comp64(double_of_bits(0xbfffffff, 0xfffffffc) * double_of_bits(0x7fe00000, 0x00000002), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffcp+0 * 0x1.0000000000002p+1023 = -inf
  comp64(double_of_bits(0x7fe00000, 0x00000002) * double_of_bits(0xbfffffff, 0xfffffffc), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000002p+1023 * -0x1.ffffffffffffcp+0 = -inf
  comp64(double_of_bits(0xffe00000, 0x00000002) * double_of_bits(0x3fffffff, 0xfffffffc), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000002p+1023 * 0x1.ffffffffffffcp+0 = -inf
}

void f201(void) {
  comp64(double_of_bits(0x3fffffff, 0xfffffffc) * double_of_bits(0xffe00000, 0x00000002), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffcp+0 * -0x1.0000000000002p+1023 = -inf
  comp64(double_of_bits(0x3fffffff, 0xfffffffe) * double_of_bits(0x7fe00000, 0x00000001), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffep+0 * 0x1.0000000000001p+1023 = inf
  comp64(double_of_bits(0x7fe00000, 0x00000001) * double_of_bits(0x3fffffff, 0xfffffffe), 0x7ff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+1023 * 0x1.ffffffffffffep+0 = inf
  comp64(double_of_bits(0xbfffffff, 0xfffffffe) * double_of_bits(0xffe00000, 0x00000001), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffep+0 * -0x1.0000000000001p+1023 = inf
  comp64(double_of_bits(0xffe00000, 0x00000001) * double_of_bits(0xbfffffff, 0xfffffffe), 0x7ff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+1023 * -0x1.ffffffffffffep+0 = inf
  comp64(double_of_bits(0xbfffffff, 0xfffffffe) * double_of_bits(0x7fe00000, 0x00000001), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffep+0 * 0x1.0000000000001p+1023 = -inf
  comp64(double_of_bits(0x7fe00000, 0x00000001) * double_of_bits(0xbfffffff, 0xfffffffe), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+1023 * -0x1.ffffffffffffep+0 = -inf
  comp64(double_of_bits(0xffe00000, 0x00000001) * double_of_bits(0x3fffffff, 0xfffffffe), 0xfff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+1023 * 0x1.ffffffffffffep+0 = -inf
  comp64(double_of_bits(0x3fffffff, 0xfffffffe) * double_of_bits(0xffe00000, 0x00000001), 0xfff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffep+0 * -0x1.0000000000001p+1023 = -inf
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 * 0x1p-1022 = 0x0p+0
}

void f202(void) {
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 * -0x1p-1022 = 0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 * 0x1p-1022 = -0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 * -0x1p-1022 = -0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0x00200000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 * 0x1p-1021 = 0x0p+0
  comp64(double_of_bits(0x00200000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-1021 * 0x1p-1022 = 0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0x80200000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 * -0x1p-1021 = 0x0p+0
  comp64(double_of_bits(0x80200000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-1021 * -0x1p-1022 = 0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0x00200000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 * 0x1p-1021 = -0x0p+0
  comp64(double_of_bits(0x00200000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-1021 * -0x1p-1022 = -0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0x80200000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 * -0x1p-1021 = -0x0p+0
}

void f203(void) {
  comp64(double_of_bits(0x80200000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-1021 * 0x1p-1022 = -0x0p+0
  comp64(double_of_bits(0x00200000, 0x00000000) * double_of_bits(0x00200000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-1021 * 0x1p-1021 = 0x0p+0
  comp64(double_of_bits(0x80200000, 0x00000000) * double_of_bits(0x80200000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-1021 * -0x1p-1021 = 0x0p+0
  comp64(double_of_bits(0x80200000, 0x00000000) * double_of_bits(0x00200000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-1021 * 0x1p-1021 = -0x0p+0
  comp64(double_of_bits(0x00200000, 0x00000000) * double_of_bits(0x80200000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-1021 * -0x1p-1021 = -0x0p+0
  comp64(double_of_bits(0x3c800000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-55 * 0x1p-1022 = 0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0x3c800000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 * 0x1p-55 = 0x0p+0
  comp64(double_of_bits(0xbc800000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-55 * -0x1p-1022 = 0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0xbc800000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 * -0x1p-55 = 0x0p+0
  comp64(double_of_bits(0xbc800000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-55 * 0x1p-1022 = -0x0p+0
}

void f204(void) {
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0xbc800000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 * -0x1p-55 = -0x0p+0
  comp64(double_of_bits(0x3c800000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-55 * -0x1p-1022 = -0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0x3c800000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 * 0x1p-55 = -0x0p+0
  comp64(double_of_bits(0x800fffff, 0xfffffff7) * double_of_bits(0x00200000, 0x00000003), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.ffffffffffff7p-1022 * 0x1.0000000000003p-1021 = -0x0p+0
  comp64(double_of_bits(0x00200000, 0x00000003) * double_of_bits(0x800fffff, 0xfffffff7), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.0000000000003p-1021 * -0x0.ffffffffffff7p-1022 = -0x0p+0
  comp64(double_of_bits(0x000fffff, 0xfffffff7) * double_of_bits(0x80200000, 0x00000003), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0.ffffffffffff7p-1022 * -0x1.0000000000003p-1021 = -0x0p+0
  comp64(double_of_bits(0x80200000, 0x00000003) * double_of_bits(0x000fffff, 0xfffffff7), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1.0000000000003p-1021 * 0x0.ffffffffffff7p-1022 = -0x0p+0
  comp64(double_of_bits(0x000fffff, 0xfffffff7) * double_of_bits(0x00200000, 0x00000003), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.ffffffffffff7p-1022 * 0x1.0000000000003p-1021 = 0x0p+0
  comp64(double_of_bits(0x00200000, 0x00000003) * double_of_bits(0x000fffff, 0xfffffff7), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.0000000000003p-1021 * 0x0.ffffffffffff7p-1022 = 0x0p+0
  comp64(double_of_bits(0x800fffff, 0xfffffff7) * double_of_bits(0x80200000, 0x00000003), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.ffffffffffff7p-1022 * -0x1.0000000000003p-1021 = 0x0p+0
}

void f205(void) {
  comp64(double_of_bits(0x80200000, 0x00000003) * double_of_bits(0x800fffff, 0xfffffff7), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.0000000000003p-1021 * -0x0.ffffffffffff7p-1022 = 0x0p+0
  comp64(double_of_bits(0x000fffff, 0xffffffff) * double_of_bits(0x000fffff, 0xfffffffe), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 * 0x0.ffffffffffffep-1022 = 0x0p+0
  comp64(double_of_bits(0x000fffff, 0xfffffffe) * double_of_bits(0x000fffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.ffffffffffffep-1022 * 0x0.fffffffffffffp-1022 = 0x0p+0
  comp64(double_of_bits(0x800fffff, 0xffffffff) * double_of_bits(0x800fffff, 0xfffffffe), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 * -0x0.ffffffffffffep-1022 = 0x0p+0
  comp64(double_of_bits(0x800fffff, 0xfffffffe) * double_of_bits(0x800fffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.ffffffffffffep-1022 * -0x0.fffffffffffffp-1022 = 0x0p+0
  comp64(double_of_bits(0x800fffff, 0xffffffff) * double_of_bits(0x000fffff, 0xfffffffe), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 * 0x0.ffffffffffffep-1022 = -0x0p+0
  comp64(double_of_bits(0x000fffff, 0xfffffffe) * double_of_bits(0x800fffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0.ffffffffffffep-1022 * -0x0.fffffffffffffp-1022 = -0x0p+0
  comp64(double_of_bits(0x000fffff, 0xffffffff) * double_of_bits(0x800fffff, 0xfffffffe), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 * -0x0.ffffffffffffep-1022 = -0x0p+0
  comp64(double_of_bits(0x800fffff, 0xfffffffe) * double_of_bits(0x000fffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.ffffffffffffep-1022 * 0x0.fffffffffffffp-1022 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x3fc00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1p-3 = 0x0p+0
}

void f206(void) {
  comp64(double_of_bits(0x3fc00000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-3 * 0x0.0000000000001p-1022 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xbfc00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1p-3 = 0x0p+0
  comp64(double_of_bits(0xbfc00000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-3 * -0x0.0000000000001p-1022 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x3fc00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1p-3 = -0x0p+0
  comp64(double_of_bits(0x3fc00000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-3 * -0x0.0000000000001p-1022 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xbfc00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1p-3 = -0x0p+0
  comp64(double_of_bits(0xbfc00000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-3 * 0x0.0000000000001p-1022 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x0.0000000000001p-1022 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x0.0000000000001p-1022 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x0.0000000000001p-1022 = -0x0p+0
}

void f207(void) {
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x0.0000000000001p-1022 = 0x0p+0
  comp64(double_of_bits(0x3c8fffff, 0xffffffff) * double_of_bits(0x00100000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp-55 * 0x1.0000000000001p-1022 = 0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000001) * double_of_bits(0x3c8fffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p-1022 * 0x1.fffffffffffffp-55 = 0x0p+0
  comp64(double_of_bits(0xbc8fffff, 0xffffffff) * double_of_bits(0x80100000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp-55 * -0x1.0000000000001p-1022 = 0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0xbc8fffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p-1022 * -0x1.fffffffffffffp-55 = 0x0p+0
  comp64(double_of_bits(0xbc8fffff, 0xffffffff) * double_of_bits(0x00100000, 0x00000001), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp-55 * 0x1.0000000000001p-1022 = -0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000001) * double_of_bits(0xbc8fffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p-1022 * -0x1.fffffffffffffp-55 = -0x0p+0
  comp64(double_of_bits(0x3c8fffff, 0xffffffff) * double_of_bits(0x80100000, 0x00000001), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp-55 * -0x1.0000000000001p-1022 = -0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0x3c8fffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p-1022 * 0x1.fffffffffffffp-55 = -0x0p+0
  comp64(double_of_bits(0x3c9fffff, 0xffffffff) * double_of_bits(0x00100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp-54 * 0x1p-1022 = 0x0p+0
}

void f208(void) {
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0x3c9fffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 * 0x1.fffffffffffffp-54 = 0x0p+0
  comp64(double_of_bits(0xbc9fffff, 0xffffffff) * double_of_bits(0x80100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp-54 * -0x1p-1022 = 0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0xbc9fffff, 0xffffffff), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 * -0x1.fffffffffffffp-54 = 0x0p+0
  comp64(double_of_bits(0xbc9fffff, 0xffffffff) * double_of_bits(0x00100000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp-54 * 0x1p-1022 = -0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0xbc9fffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 * -0x1.fffffffffffffp-54 = -0x0p+0
  comp64(double_of_bits(0x3c9fffff, 0xffffffff) * double_of_bits(0x80100000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp-54 * -0x1p-1022 = -0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0x3c9fffff, 0xffffffff), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 * 0x1.fffffffffffffp-54 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x3fd00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1p-2 = 0x0p+0
  comp64(double_of_bits(0x3fd00000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-2 * 0x0.0000000000001p-1022 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xbfd00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1p-2 = 0x0p+0
}

void f209(void) {
  comp64(double_of_bits(0xbfd00000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-2 * -0x0.0000000000001p-1022 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x3fd00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1p-2 = -0x0p+0
  comp64(double_of_bits(0x3fd00000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-2 * -0x0.0000000000001p-1022 = -0x0p+0
  comp64(double_of_bits(0xbfd00000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-2 * 0x0.0000000000001p-1022 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xbfd00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1p-2 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x3ff7ffff, 0xffffffff), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1.7ffffffffffffp+0 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x3ff7ffff, 0xffffffff) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.7ffffffffffffp+0 * 0x0.0000000000001p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xbff7ffff, 0xffffffff), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1.7ffffffffffffp+0 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbff7ffff, 0xffffffff) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.7ffffffffffffp+0 * -0x0.0000000000001p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x3ff7ffff, 0xffffffff), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1.7ffffffffffffp+0 = -0x0.0000000000001p-1022
}

void f210(void) {
  comp64(double_of_bits(0x3ff7ffff, 0xffffffff) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.7ffffffffffffp+0 * -0x0.0000000000001p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0xbff7ffff, 0xffffffff) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.7ffffffffffffp+0 * 0x0.0000000000001p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xbff7ffff, 0xffffffff), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1.7ffffffffffffp+0 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x400bffff, 0xffffffff), 0x00000000, 0x00000003, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1.bffffffffffffp+1 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0x400bffff, 0xffffffff) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000003, STR(__LINE__)); // 0x1.bffffffffffffp+1 * 0x0.0000000000001p-1022 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xc00bffff, 0xffffffff), 0x00000000, 0x00000003, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1.bffffffffffffp+1 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0xc00bffff, 0xffffffff) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000003, STR(__LINE__)); // -0x1.bffffffffffffp+1 * -0x0.0000000000001p-1022 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x400bffff, 0xffffffff), 0x80000000, 0x00000003, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1.bffffffffffffp+1 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0x400bffff, 0xffffffff) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000003, STR(__LINE__)); // 0x1.bffffffffffffp+1 * -0x0.0000000000001p-1022 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0xc00bffff, 0xffffffff) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000003, STR(__LINE__)); // -0x1.bffffffffffffp+1 * 0x0.0000000000001p-1022 = -0x0.0000000000003p-1022
}

void f211(void) {
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xc00bffff, 0xffffffff), 0x80000000, 0x00000003, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1.bffffffffffffp+1 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0x3ca00000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-53 * 0x1p-1022 = 0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0x3ca00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 * 0x1p-53 = 0x0p+0
  comp64(double_of_bits(0xbca00000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-53 * -0x1p-1022 = 0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0xbca00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 * -0x1p-53 = 0x0p+0
  comp64(double_of_bits(0xbca00000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-53 * 0x1p-1022 = -0x0p+0
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0xbca00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-1022 * -0x1p-53 = -0x0p+0
  comp64(double_of_bits(0x3ca00000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-53 * -0x1p-1022 = -0x0p+0
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0x3ca00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-1022 * 0x1p-53 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x3fe00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1p-1 = 0x0p+0
}

void f212(void) {
  comp64(double_of_bits(0x3fe00000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // 0x1p-1 * 0x0.0000000000001p-1022 = 0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xbfe00000, 0x00000000), 0x00000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1p-1 = 0x0p+0
  comp64(double_of_bits(0xbfe00000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000000, STR(__LINE__)); // -0x1p-1 * -0x0.0000000000001p-1022 = 0x0p+0
  comp64(double_of_bits(0x3fe00000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000000, STR(__LINE__)); // 0x1p-1 * -0x0.0000000000001p-1022 = -0x0p+0
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x3fe00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1p-1 = -0x0p+0
  comp64(double_of_bits(0xbfe00000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000000, STR(__LINE__)); // -0x1p-1 * 0x0.0000000000001p-1022 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xbfe00000, 0x00000000), 0x80000000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1p-1 = -0x0p+0
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x3ff80000, 0x00000000), 0x00000000, 0x00000002, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1.8p+0 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x3ff80000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000002, STR(__LINE__)); // 0x1.8p+0 * 0x0.0000000000001p-1022 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xbff80000, 0x00000000), 0x00000000, 0x00000002, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1.8p+0 = 0x0.0000000000002p-1022
}

void f213(void) {
  comp64(double_of_bits(0xbff80000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000002, STR(__LINE__)); // -0x1.8p+0 * -0x0.0000000000001p-1022 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x3ff80000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000002, STR(__LINE__)); // 0x1.8p+0 * -0x0.0000000000001p-1022 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x3ff80000, 0x00000000), 0x80000000, 0x00000002, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1.8p+0 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0xbff80000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000002, STR(__LINE__)); // -0x1.8p+0 * 0x0.0000000000001p-1022 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xbff80000, 0x00000000), 0x80000000, 0x00000002, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1.8p+0 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x40040000, 0x00000000), 0x00000000, 0x00000002, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1.4p+1 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x40040000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000002, STR(__LINE__)); // 0x1.4p+1 * 0x0.0000000000001p-1022 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xc0040000, 0x00000000), 0x00000000, 0x00000002, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1.4p+1 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0xc0040000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000002, STR(__LINE__)); // -0x1.4p+1 * -0x0.0000000000001p-1022 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x40040000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000002, STR(__LINE__)); // 0x1.4p+1 * -0x0.0000000000001p-1022 = -0x0.0000000000002p-1022
}

void f214(void) {
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x40040000, 0x00000000), 0x80000000, 0x00000002, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1.4p+1 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0xc0040000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000002, STR(__LINE__)); // -0x1.4p+1 * 0x0.0000000000001p-1022 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xc0040000, 0x00000000), 0x80000000, 0x00000002, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1.4p+1 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x400c0000, 0x00000000), 0x00000000, 0x00000004, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1.cp+1 = 0x0.0000000000004p-1022
  comp64(double_of_bits(0x400c0000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000004, STR(__LINE__)); // 0x1.cp+1 * 0x0.0000000000001p-1022 = 0x0.0000000000004p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xc00c0000, 0x00000000), 0x00000000, 0x00000004, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1.cp+1 = 0x0.0000000000004p-1022
  comp64(double_of_bits(0xc00c0000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000004, STR(__LINE__)); // -0x1.cp+1 * -0x0.0000000000001p-1022 = 0x0.0000000000004p-1022
  comp64(double_of_bits(0x400c0000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000004, STR(__LINE__)); // 0x1.cp+1 * -0x0.0000000000001p-1022 = -0x0.0000000000004p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x400c0000, 0x00000000), 0x80000000, 0x00000004, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1.cp+1 = -0x0.0000000000004p-1022
  comp64(double_of_bits(0xc00c0000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000004, STR(__LINE__)); // -0x1.cp+1 * 0x0.0000000000001p-1022 = -0x0.0000000000004p-1022
}

void f215(void) {
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xc00c0000, 0x00000000), 0x80000000, 0x00000004, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1.cp+1 = -0x0.0000000000004p-1022
  comp64(double_of_bits(0x3ca40000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.4p-53 * 0x1p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0x3ca40000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1p-1022 * 0x1.4p-53 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbca40000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.4p-53 * -0x1p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0xbca40000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1p-1022 * -0x1.4p-53 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbca40000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.4p-53 * 0x1p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0xbca40000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1p-1022 * -0x1.4p-53 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0x3ca40000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1p-1022 * 0x1.4p-53 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x3ca40000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.4p-53 * -0x1p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x3fe00000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1.0000000000001p-1 = 0x0.0000000000001p-1022
}

void f216(void) {
  comp64(double_of_bits(0x3fe00000, 0x00000001) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p-1 * 0x0.0000000000001p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xbfe00000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1.0000000000001p-1 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbfe00000, 0x00000001) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p-1 * -0x0.0000000000001p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x3fe00000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1.0000000000001p-1 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x3fe00000, 0x00000001) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p-1 * -0x0.0000000000001p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0xbfe00000, 0x00000001) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p-1 * 0x0.0000000000001p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xbfe00000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1.0000000000001p-1 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x40040000, 0x00000001) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000003, STR(__LINE__)); // 0x1.4000000000001p+1 * 0x0.0000000000001p-1022 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x40040000, 0x00000001), 0x00000000, 0x00000003, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1.4000000000001p+1 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0xc0040000, 0x00000001) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000003, STR(__LINE__)); // -0x1.4000000000001p+1 * -0x0.0000000000001p-1022 = 0x0.0000000000003p-1022
}

void f217(void) {
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xc0040000, 0x00000001), 0x00000000, 0x00000003, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1.4000000000001p+1 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0xc0040000, 0x00000001) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000003, STR(__LINE__)); // -0x1.4000000000001p+1 * 0x0.0000000000001p-1022 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xc0040000, 0x00000001), 0x80000000, 0x00000003, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1.4000000000001p+1 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x40040000, 0x00000001), 0x80000000, 0x00000003, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1.4000000000001p+1 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0x40040000, 0x00000001) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000003, STR(__LINE__)); // 0x1.4000000000001p+1 * -0x0.0000000000001p-1022 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0x3c900000, 0x00000001) * double_of_bits(0x001fffff, 0xffffffff), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p-54 * 0x1.fffffffffffffp-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x001fffff, 0xffffffff) * double_of_bits(0x3c900000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp-1022 * 0x1.0000000000001p-54 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbc900000, 0x00000001) * double_of_bits(0x801fffff, 0xffffffff), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p-54 * -0x1.fffffffffffffp-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x801fffff, 0xffffffff) * double_of_bits(0xbc900000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.fffffffffffffp-1022 * -0x1.0000000000001p-54 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbc900000, 0x00000001) * double_of_bits(0x001fffff, 0xffffffff), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p-54 * 0x1.fffffffffffffp-1022 = -0x0.0000000000001p-1022
}

void f218(void) {
  comp64(double_of_bits(0x001fffff, 0xffffffff) * double_of_bits(0xbc900000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp-1022 * -0x1.0000000000001p-54 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x801fffff, 0xffffffff) * double_of_bits(0x3c900000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.fffffffffffffp-1022 * 0x1.0000000000001p-54 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x3c900000, 0x00000001) * double_of_bits(0x801fffff, 0xffffffff), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p-54 * -0x1.fffffffffffffp-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x3ca80000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.8p-53 * 0x1p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0x3ca80000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1p-1022 * 0x1.8p-53 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbca80000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.8p-53 * -0x1p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0xbca80000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1p-1022 * -0x1.8p-53 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbca80000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.8p-53 * 0x1p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0xbca80000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1p-1022 * -0x1.8p-53 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0x3ca80000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1p-1022 * 0x1.8p-53 = -0x0.0000000000001p-1022
}

void f219(void) {
  comp64(double_of_bits(0x3ca80000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.8p-53 * -0x1p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x3fe80000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1.8p-1 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x3fe80000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.8p-1 * 0x0.0000000000001p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xbfe80000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1.8p-1 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbfe80000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.8p-1 * -0x0.0000000000001p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x3fe80000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1.8p-1 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x3fe80000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.8p-1 * -0x0.0000000000001p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0xbfe80000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.8p-1 * 0x0.0000000000001p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xbfe80000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1.8p-1 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x3cac0000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.cp-53 * 0x1p-1022 = 0x0.0000000000001p-1022
}

void f220(void) {
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0x3cac0000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1p-1022 * 0x1.cp-53 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbcac0000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.cp-53 * -0x1p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0xbcac0000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1p-1022 * -0x1.cp-53 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbcac0000, 0x00000000) * double_of_bits(0x00100000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.cp-53 * 0x1p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0xbcac0000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1p-1022 * -0x1.cp-53 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0x3cac0000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1p-1022 * 0x1.cp-53 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x3cac0000, 0x00000000) * double_of_bits(0x80100000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.cp-53 * -0x1p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x3fe80000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1.8000000000001p-1 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x3fe80000, 0x00000001) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.8000000000001p-1 * 0x0.0000000000001p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xbfe80000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1.8000000000001p-1 = 0x0.0000000000001p-1022
}

void f221(void) {
  comp64(double_of_bits(0xbfe80000, 0x00000001) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.8000000000001p-1 * -0x0.0000000000001p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x3fe80000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1.8000000000001p-1 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x3fe80000, 0x00000001) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.8000000000001p-1 * -0x0.0000000000001p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0xbfe80000, 0x00000001) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.8000000000001p-1 * 0x0.0000000000001p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xbfe80000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1.8000000000001p-1 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x3fefffff, 0xffffffff), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1.fffffffffffffp-1 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x3fefffff, 0xffffffff) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp-1 * 0x0.0000000000001p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xbfefffff, 0xffffffff), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1.fffffffffffffp-1 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbfefffff, 0xffffffff) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.fffffffffffffp-1 * -0x0.0000000000001p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x3fefffff, 0xffffffff), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1.fffffffffffffp-1 = -0x0.0000000000001p-1022
}

void f222(void) {
  comp64(double_of_bits(0x3fefffff, 0xffffffff) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp-1 * -0x0.0000000000001p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xbfefffff, 0xffffffff), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1.fffffffffffffp-1 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0xbfefffff, 0xffffffff) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.fffffffffffffp-1 * 0x0.0000000000001p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x3c9fffff, 0xffffffff) * double_of_bits(0x001fffff, 0xffffffff), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp-54 * 0x1.fffffffffffffp-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x001fffff, 0xffffffff) * double_of_bits(0x3c9fffff, 0xffffffff), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp-1022 * 0x1.fffffffffffffp-54 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbc9fffff, 0xffffffff) * double_of_bits(0x801fffff, 0xffffffff), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.fffffffffffffp-54 * -0x1.fffffffffffffp-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x801fffff, 0xffffffff) * double_of_bits(0xbc9fffff, 0xffffffff), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1.fffffffffffffp-1022 * -0x1.fffffffffffffp-54 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbc9fffff, 0xffffffff) * double_of_bits(0x001fffff, 0xffffffff), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.fffffffffffffp-54 * 0x1.fffffffffffffp-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x001fffff, 0xffffffff) * double_of_bits(0xbc9fffff, 0xffffffff), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp-1022 * -0x1.fffffffffffffp-54 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x801fffff, 0xffffffff) * double_of_bits(0x3c9fffff, 0xffffffff), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1.fffffffffffffp-1022 * 0x1.fffffffffffffp-54 = -0x0.0000000000001p-1022
}

void f223(void) {
  comp64(double_of_bits(0x3c9fffff, 0xffffffff) * double_of_bits(0x801fffff, 0xffffffff), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp-54 * -0x1.fffffffffffffp-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x000fffff, 0xfffffffc) * double_of_bits(0x3ff00000, 0x00000001), 0x000fffff, 0xfffffffd, STR(__LINE__)); // 0x0.ffffffffffffcp-1022 * 0x1.0000000000001p+0 = 0x0.ffffffffffffdp-1022
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x000fffff, 0xfffffffc), 0x000fffff, 0xfffffffd, STR(__LINE__)); // 0x1.0000000000001p+0 * 0x0.ffffffffffffcp-1022 = 0x0.ffffffffffffdp-1022
  comp64(double_of_bits(0x800fffff, 0xfffffffc) * double_of_bits(0xbff00000, 0x00000001), 0x000fffff, 0xfffffffd, STR(__LINE__)); // -0x0.ffffffffffffcp-1022 * -0x1.0000000000001p+0 = 0x0.ffffffffffffdp-1022
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x800fffff, 0xfffffffc), 0x000fffff, 0xfffffffd, STR(__LINE__)); // -0x1.0000000000001p+0 * -0x0.ffffffffffffcp-1022 = 0x0.ffffffffffffdp-1022
  comp64(double_of_bits(0x800fffff, 0xfffffffc) * double_of_bits(0x3ff00000, 0x00000001), 0x800fffff, 0xfffffffd, STR(__LINE__)); // -0x0.ffffffffffffcp-1022 * 0x1.0000000000001p+0 = -0x0.ffffffffffffdp-1022
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x800fffff, 0xfffffffc), 0x800fffff, 0xfffffffd, STR(__LINE__)); // 0x1.0000000000001p+0 * -0x0.ffffffffffffcp-1022 = -0x0.ffffffffffffdp-1022
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x000fffff, 0xfffffffc), 0x800fffff, 0xfffffffd, STR(__LINE__)); // -0x1.0000000000001p+0 * 0x0.ffffffffffffcp-1022 = -0x0.ffffffffffffdp-1022
  comp64(double_of_bits(0x000fffff, 0xfffffffc) * double_of_bits(0xbff00000, 0x00000001), 0x800fffff, 0xfffffffd, STR(__LINE__)); // 0x0.ffffffffffffcp-1022 * -0x1.0000000000001p+0 = -0x0.ffffffffffffdp-1022
  comp64(double_of_bits(0x3fe80000, 0x00000000) * double_of_bits(0x00100000, 0x00000001), 0x000c0000, 0x00000001, STR(__LINE__)); // 0x1.8p-1 * 0x1.0000000000001p-1022 = 0x0.c000000000001p-1022
}

void f224(void) {
  comp64(double_of_bits(0x00100000, 0x00000001) * double_of_bits(0x3fe80000, 0x00000000), 0x000c0000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p-1022 * 0x1.8p-1 = 0x0.c000000000001p-1022
  comp64(double_of_bits(0xbfe80000, 0x00000000) * double_of_bits(0x80100000, 0x00000001), 0x000c0000, 0x00000001, STR(__LINE__)); // -0x1.8p-1 * -0x1.0000000000001p-1022 = 0x0.c000000000001p-1022
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0xbfe80000, 0x00000000), 0x000c0000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p-1022 * -0x1.8p-1 = 0x0.c000000000001p-1022
  comp64(double_of_bits(0xbfe80000, 0x00000000) * double_of_bits(0x00100000, 0x00000001), 0x800c0000, 0x00000001, STR(__LINE__)); // -0x1.8p-1 * 0x1.0000000000001p-1022 = -0x0.c000000000001p-1022
  comp64(double_of_bits(0x00100000, 0x00000001) * double_of_bits(0xbfe80000, 0x00000000), 0x800c0000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p-1022 * -0x1.8p-1 = -0x0.c000000000001p-1022
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0x3fe80000, 0x00000000), 0x800c0000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p-1022 * 0x1.8p-1 = -0x0.c000000000001p-1022
  comp64(double_of_bits(0x3fe80000, 0x00000000) * double_of_bits(0x80100000, 0x00000001), 0x800c0000, 0x00000001, STR(__LINE__)); // 0x1.8p-1 * -0x1.0000000000001p-1022 = -0x0.c000000000001p-1022
  comp64(double_of_bits(0x000fffff, 0xfffffffe) * double_of_bits(0x3ff00000, 0x00000001), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x0.ffffffffffffep-1022 * 0x1.0000000000001p+0 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x000fffff, 0xfffffffe), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x1.0000000000001p+0 * 0x0.ffffffffffffep-1022 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x800fffff, 0xfffffffe) * double_of_bits(0xbff00000, 0x00000001), 0x000fffff, 0xffffffff, STR(__LINE__)); // -0x0.ffffffffffffep-1022 * -0x1.0000000000001p+0 = 0x0.fffffffffffffp-1022
}

void f225(void) {
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x800fffff, 0xfffffffe), 0x000fffff, 0xffffffff, STR(__LINE__)); // -0x1.0000000000001p+0 * -0x0.ffffffffffffep-1022 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x800fffff, 0xfffffffe) * double_of_bits(0x3ff00000, 0x00000001), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x0.ffffffffffffep-1022 * 0x1.0000000000001p+0 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x800fffff, 0xfffffffe), 0x800fffff, 0xffffffff, STR(__LINE__)); // 0x1.0000000000001p+0 * -0x0.ffffffffffffep-1022 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x000fffff, 0xfffffffe), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x1.0000000000001p+0 * 0x0.ffffffffffffep-1022 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x000fffff, 0xfffffffe) * double_of_bits(0xbff00000, 0x00000001), 0x800fffff, 0xffffffff, STR(__LINE__)); // 0x0.ffffffffffffep-1022 * -0x1.0000000000001p+0 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x000fffff, 0xfffffff8) * double_of_bits(0x3ff00000, 0x00000001), 0x000fffff, 0xfffffff9, STR(__LINE__)); // 0x0.ffffffffffff8p-1022 * 0x1.0000000000001p+0 = 0x0.ffffffffffff9p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x000fffff, 0xfffffff8), 0x000fffff, 0xfffffff9, STR(__LINE__)); // 0x1.0000000000001p+0 * 0x0.ffffffffffff8p-1022 = 0x0.ffffffffffff9p-1022
  comp64(double_of_bits(0x800fffff, 0xfffffff8) * double_of_bits(0xbff00000, 0x00000001), 0x000fffff, 0xfffffff9, STR(__LINE__)); // -0x0.ffffffffffff8p-1022 * -0x1.0000000000001p+0 = 0x0.ffffffffffff9p-1022
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x800fffff, 0xfffffff8), 0x000fffff, 0xfffffff9, STR(__LINE__)); // -0x1.0000000000001p+0 * -0x0.ffffffffffff8p-1022 = 0x0.ffffffffffff9p-1022
  comp64(double_of_bits(0x800fffff, 0xfffffff8) * double_of_bits(0x3ff00000, 0x00000001), 0x800fffff, 0xfffffff9, STR(__LINE__)); // -0x0.ffffffffffff8p-1022 * 0x1.0000000000001p+0 = -0x0.ffffffffffff9p-1022
}

void f226(void) {
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x800fffff, 0xfffffff8), 0x800fffff, 0xfffffff9, STR(__LINE__)); // 0x1.0000000000001p+0 * -0x0.ffffffffffff8p-1022 = -0x0.ffffffffffff9p-1022
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x000fffff, 0xfffffff8), 0x800fffff, 0xfffffff9, STR(__LINE__)); // -0x1.0000000000001p+0 * 0x0.ffffffffffff8p-1022 = -0x0.ffffffffffff9p-1022
  comp64(double_of_bits(0x000fffff, 0xfffffff8) * double_of_bits(0xbff00000, 0x00000001), 0x800fffff, 0xfffffff9, STR(__LINE__)); // 0x0.ffffffffffff8p-1022 * -0x1.0000000000001p+0 = -0x0.ffffffffffff9p-1022
  comp64(double_of_bits(0x000fffff, 0xfffffff7) * double_of_bits(0x3ff00000, 0x00000001), 0x000fffff, 0xfffffff8, STR(__LINE__)); // 0x0.ffffffffffff7p-1022 * 0x1.0000000000001p+0 = 0x0.ffffffffffff8p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x000fffff, 0xfffffff7), 0x000fffff, 0xfffffff8, STR(__LINE__)); // 0x1.0000000000001p+0 * 0x0.ffffffffffff7p-1022 = 0x0.ffffffffffff8p-1022
  comp64(double_of_bits(0x800fffff, 0xfffffff7) * double_of_bits(0xbff00000, 0x00000001), 0x000fffff, 0xfffffff8, STR(__LINE__)); // -0x0.ffffffffffff7p-1022 * -0x1.0000000000001p+0 = 0x0.ffffffffffff8p-1022
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x800fffff, 0xfffffff7), 0x000fffff, 0xfffffff8, STR(__LINE__)); // -0x1.0000000000001p+0 * -0x0.ffffffffffff7p-1022 = 0x0.ffffffffffff8p-1022
  comp64(double_of_bits(0x800fffff, 0xfffffff7) * double_of_bits(0x3ff00000, 0x00000001), 0x800fffff, 0xfffffff8, STR(__LINE__)); // -0x0.ffffffffffff7p-1022 * 0x1.0000000000001p+0 = -0x0.ffffffffffff8p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x800fffff, 0xfffffff7), 0x800fffff, 0xfffffff8, STR(__LINE__)); // 0x1.0000000000001p+0 * -0x0.ffffffffffff7p-1022 = -0x0.ffffffffffff8p-1022
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x000fffff, 0xfffffff7), 0x800fffff, 0xfffffff8, STR(__LINE__)); // -0x1.0000000000001p+0 * 0x0.ffffffffffff7p-1022 = -0x0.ffffffffffff8p-1022
}

void f227(void) {
  comp64(double_of_bits(0x000fffff, 0xfffffff7) * double_of_bits(0xbff00000, 0x00000001), 0x800fffff, 0xfffffff8, STR(__LINE__)); // 0x0.ffffffffffff7p-1022 * -0x1.0000000000001p+0 = -0x0.ffffffffffff8p-1022
  comp64(double_of_bits(0x00100000, 0x00000001) * double_of_bits(0x3fefffff, 0xfffffffa), 0x000fffff, 0xfffffffe, STR(__LINE__)); // 0x1.0000000000001p-1022 * 0x1.ffffffffffffap-1 = 0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x3fefffff, 0xfffffffa) * double_of_bits(0x00100000, 0x00000001), 0x000fffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffap-1 * 0x1.0000000000001p-1022 = 0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0xbfefffff, 0xfffffffa), 0x000fffff, 0xfffffffe, STR(__LINE__)); // -0x1.0000000000001p-1022 * -0x1.ffffffffffffap-1 = 0x0.ffffffffffffep-1022
  comp64(double_of_bits(0xbfefffff, 0xfffffffa) * double_of_bits(0x80100000, 0x00000001), 0x000fffff, 0xfffffffe, STR(__LINE__)); // -0x1.ffffffffffffap-1 * -0x1.0000000000001p-1022 = 0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0x3fefffff, 0xfffffffa), 0x800fffff, 0xfffffffe, STR(__LINE__)); // -0x1.0000000000001p-1022 * 0x1.ffffffffffffap-1 = -0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x3fefffff, 0xfffffffa) * double_of_bits(0x80100000, 0x00000001), 0x800fffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffap-1 * -0x1.0000000000001p-1022 = -0x0.ffffffffffffep-1022
  comp64(double_of_bits(0xbfefffff, 0xfffffffa) * double_of_bits(0x00100000, 0x00000001), 0x800fffff, 0xfffffffe, STR(__LINE__)); // -0x1.ffffffffffffap-1 * 0x1.0000000000001p-1022 = -0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x00100000, 0x00000001) * double_of_bits(0xbfefffff, 0xfffffffa), 0x800fffff, 0xfffffffe, STR(__LINE__)); // 0x1.0000000000001p-1022 * -0x1.ffffffffffffap-1 = -0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x000fffff, 0xfffffffe) * double_of_bits(0x3fefffff, 0xfffffffc), 0x000fffff, 0xfffffffc, STR(__LINE__)); // 0x0.ffffffffffffep-1022 * 0x1.ffffffffffffcp-1 = 0x0.ffffffffffffcp-1022
}

void f228(void) {
  comp64(double_of_bits(0x3fefffff, 0xfffffffc) * double_of_bits(0x000fffff, 0xfffffffe), 0x000fffff, 0xfffffffc, STR(__LINE__)); // 0x1.ffffffffffffcp-1 * 0x0.ffffffffffffep-1022 = 0x0.ffffffffffffcp-1022
  comp64(double_of_bits(0x800fffff, 0xfffffffe) * double_of_bits(0xbfefffff, 0xfffffffc), 0x000fffff, 0xfffffffc, STR(__LINE__)); // -0x0.ffffffffffffep-1022 * -0x1.ffffffffffffcp-1 = 0x0.ffffffffffffcp-1022
  comp64(double_of_bits(0xbfefffff, 0xfffffffc) * double_of_bits(0x800fffff, 0xfffffffe), 0x000fffff, 0xfffffffc, STR(__LINE__)); // -0x1.ffffffffffffcp-1 * -0x0.ffffffffffffep-1022 = 0x0.ffffffffffffcp-1022
  comp64(double_of_bits(0x800fffff, 0xfffffffe) * double_of_bits(0x3fefffff, 0xfffffffc), 0x800fffff, 0xfffffffc, STR(__LINE__)); // -0x0.ffffffffffffep-1022 * 0x1.ffffffffffffcp-1 = -0x0.ffffffffffffcp-1022
  comp64(double_of_bits(0x3fefffff, 0xfffffffc) * double_of_bits(0x800fffff, 0xfffffffe), 0x800fffff, 0xfffffffc, STR(__LINE__)); // 0x1.ffffffffffffcp-1 * -0x0.ffffffffffffep-1022 = -0x0.ffffffffffffcp-1022
  comp64(double_of_bits(0xbfefffff, 0xfffffffc) * double_of_bits(0x000fffff, 0xfffffffe), 0x800fffff, 0xfffffffc, STR(__LINE__)); // -0x1.ffffffffffffcp-1 * 0x0.ffffffffffffep-1022 = -0x0.ffffffffffffcp-1022
  comp64(double_of_bits(0x000fffff, 0xfffffffe) * double_of_bits(0xbfefffff, 0xfffffffc), 0x800fffff, 0xfffffffc, STR(__LINE__)); // 0x0.ffffffffffffep-1022 * -0x1.ffffffffffffcp-1 = -0x0.ffffffffffffcp-1022
  comp64(double_of_bits(0x3fdfffff, 0xffffffff) * double_of_bits(0x00100000, 0x00000003), 0x00080000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp-2 * 0x1.0000000000003p-1022 = 0x0.8000000000001p-1022
  comp64(double_of_bits(0x00100000, 0x00000003) * double_of_bits(0x3fdfffff, 0xffffffff), 0x00080000, 0x00000001, STR(__LINE__)); // 0x1.0000000000003p-1022 * 0x1.fffffffffffffp-2 = 0x0.8000000000001p-1022
  comp64(double_of_bits(0xbfdfffff, 0xffffffff) * double_of_bits(0x80100000, 0x00000003), 0x00080000, 0x00000001, STR(__LINE__)); // -0x1.fffffffffffffp-2 * -0x1.0000000000003p-1022 = 0x0.8000000000001p-1022
}

void f229(void) {
  comp64(double_of_bits(0x80100000, 0x00000003) * double_of_bits(0xbfdfffff, 0xffffffff), 0x00080000, 0x00000001, STR(__LINE__)); // -0x1.0000000000003p-1022 * -0x1.fffffffffffffp-2 = 0x0.8000000000001p-1022
  comp64(double_of_bits(0xbfdfffff, 0xffffffff) * double_of_bits(0x00100000, 0x00000003), 0x80080000, 0x00000001, STR(__LINE__)); // -0x1.fffffffffffffp-2 * 0x1.0000000000003p-1022 = -0x0.8000000000001p-1022
  comp64(double_of_bits(0x00100000, 0x00000003) * double_of_bits(0xbfdfffff, 0xffffffff), 0x80080000, 0x00000001, STR(__LINE__)); // 0x1.0000000000003p-1022 * -0x1.fffffffffffffp-2 = -0x0.8000000000001p-1022
  comp64(double_of_bits(0x80100000, 0x00000003) * double_of_bits(0x3fdfffff, 0xffffffff), 0x80080000, 0x00000001, STR(__LINE__)); // -0x1.0000000000003p-1022 * 0x1.fffffffffffffp-2 = -0x0.8000000000001p-1022
  comp64(double_of_bits(0x3fdfffff, 0xffffffff) * double_of_bits(0x80100000, 0x00000003), 0x80080000, 0x00000001, STR(__LINE__)); // 0x1.fffffffffffffp-2 * -0x1.0000000000003p-1022 = -0x0.8000000000001p-1022
  comp64(double_of_bits(0x000fffff, 0xffffffff) * double_of_bits(0x3ff00000, 0x00000001), 0x00100000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 * 0x1.0000000000001p+0 = 0x1p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x000fffff, 0xffffffff), 0x00100000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 * 0x0.fffffffffffffp-1022 = 0x1p-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) * double_of_bits(0xbff00000, 0x00000001), 0x00100000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 * -0x1.0000000000001p+0 = 0x1p-1022
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x800fffff, 0xffffffff), 0x00100000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+0 * -0x0.fffffffffffffp-1022 = 0x1p-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) * double_of_bits(0x3ff00000, 0x00000001), 0x80100000, 0x00000000, STR(__LINE__)); // -0x0.fffffffffffffp-1022 * 0x1.0000000000001p+0 = -0x1p-1022
}

void f230(void) {
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x800fffff, 0xffffffff), 0x80100000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 * -0x0.fffffffffffffp-1022 = -0x1p-1022
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x000fffff, 0xffffffff), 0x80100000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+0 * 0x0.fffffffffffffp-1022 = -0x1p-1022
  comp64(double_of_bits(0x000fffff, 0xffffffff) * double_of_bits(0xbff00000, 0x00000001), 0x80100000, 0x00000000, STR(__LINE__)); // 0x0.fffffffffffffp-1022 * -0x1.0000000000001p+0 = -0x1p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000008) * double_of_bits(0x000fffff, 0xfffffff8), 0x00100000, 0x00000000, STR(__LINE__)); // 0x1.0000000000008p+0 * 0x0.ffffffffffff8p-1022 = 0x1p-1022
  comp64(double_of_bits(0x000fffff, 0xfffffff8) * double_of_bits(0x3ff00000, 0x00000008), 0x00100000, 0x00000000, STR(__LINE__)); // 0x0.ffffffffffff8p-1022 * 0x1.0000000000008p+0 = 0x1p-1022
  comp64(double_of_bits(0x800fffff, 0xfffffff8) * double_of_bits(0xbff00000, 0x00000008), 0x00100000, 0x00000000, STR(__LINE__)); // -0x0.ffffffffffff8p-1022 * -0x1.0000000000008p+0 = 0x1p-1022
  comp64(double_of_bits(0xbff00000, 0x00000008) * double_of_bits(0x800fffff, 0xfffffff8), 0x00100000, 0x00000000, STR(__LINE__)); // -0x1.0000000000008p+0 * -0x0.ffffffffffff8p-1022 = 0x1p-1022
  comp64(double_of_bits(0x800fffff, 0xfffffff8) * double_of_bits(0x3ff00000, 0x00000008), 0x80100000, 0x00000000, STR(__LINE__)); // -0x0.ffffffffffff8p-1022 * 0x1.0000000000008p+0 = -0x1p-1022
  comp64(double_of_bits(0x3ff00000, 0x00000008) * double_of_bits(0x800fffff, 0xfffffff8), 0x80100000, 0x00000000, STR(__LINE__)); // 0x1.0000000000008p+0 * -0x0.ffffffffffff8p-1022 = -0x1p-1022
  comp64(double_of_bits(0xbff00000, 0x00000008) * double_of_bits(0x000fffff, 0xfffffff8), 0x80100000, 0x00000000, STR(__LINE__)); // -0x1.0000000000008p+0 * 0x0.ffffffffffff8p-1022 = -0x1p-1022
}

void f231(void) {
  comp64(double_of_bits(0x000fffff, 0xfffffff8) * double_of_bits(0xbff00000, 0x00000008), 0x80100000, 0x00000000, STR(__LINE__)); // 0x0.ffffffffffff8p-1022 * -0x1.0000000000008p+0 = -0x1p-1022
  comp64(double_of_bits(0x00100000, 0x00000001) * double_of_bits(0x3fefffff, 0xfffffffe), 0x00100000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p-1022 * 0x1.ffffffffffffep-1 = 0x1p-1022
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) * double_of_bits(0x00100000, 0x00000001), 0x00100000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffep-1 * 0x1.0000000000001p-1022 = 0x1p-1022
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0xbfefffff, 0xfffffffe), 0x00100000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p-1022 * -0x1.ffffffffffffep-1 = 0x1p-1022
  comp64(double_of_bits(0xbfefffff, 0xfffffffe) * double_of_bits(0x80100000, 0x00000001), 0x00100000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffep-1 * -0x1.0000000000001p-1022 = 0x1p-1022
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0x3fefffff, 0xfffffffe), 0x80100000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p-1022 * 0x1.ffffffffffffep-1 = -0x1p-1022
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) * double_of_bits(0x80100000, 0x00000001), 0x80100000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffep-1 * -0x1.0000000000001p-1022 = -0x1p-1022
  comp64(double_of_bits(0xbfefffff, 0xfffffffe) * double_of_bits(0x00100000, 0x00000001), 0x80100000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffep-1 * 0x1.0000000000001p-1022 = -0x1p-1022
  comp64(double_of_bits(0x00100000, 0x00000001) * double_of_bits(0xbfefffff, 0xfffffffe), 0x80100000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p-1022 * -0x1.ffffffffffffep-1 = -0x1p-1022
  comp64(double_of_bits(0x00100000, 0x00000002) * double_of_bits(0x3fefffff, 0xfffffffc), 0x00100000, 0x00000000, STR(__LINE__)); // 0x1.0000000000002p-1022 * 0x1.ffffffffffffcp-1 = 0x1p-1022
}

void f232(void) {
  comp64(double_of_bits(0x3fefffff, 0xfffffffc) * double_of_bits(0x00100000, 0x00000002), 0x00100000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffcp-1 * 0x1.0000000000002p-1022 = 0x1p-1022
  comp64(double_of_bits(0x80100000, 0x00000002) * double_of_bits(0xbfefffff, 0xfffffffc), 0x00100000, 0x00000000, STR(__LINE__)); // -0x1.0000000000002p-1022 * -0x1.ffffffffffffcp-1 = 0x1p-1022
  comp64(double_of_bits(0xbfefffff, 0xfffffffc) * double_of_bits(0x80100000, 0x00000002), 0x00100000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffcp-1 * -0x1.0000000000002p-1022 = 0x1p-1022
  comp64(double_of_bits(0x80100000, 0x00000002) * double_of_bits(0x3fefffff, 0xfffffffc), 0x80100000, 0x00000000, STR(__LINE__)); // -0x1.0000000000002p-1022 * 0x1.ffffffffffffcp-1 = -0x1p-1022
  comp64(double_of_bits(0x3fefffff, 0xfffffffc) * double_of_bits(0x80100000, 0x00000002), 0x80100000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffcp-1 * -0x1.0000000000002p-1022 = -0x1p-1022
  comp64(double_of_bits(0xbfefffff, 0xfffffffc) * double_of_bits(0x00100000, 0x00000002), 0x80100000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffcp-1 * 0x1.0000000000002p-1022 = -0x1p-1022
  comp64(double_of_bits(0x00100000, 0x00000002) * double_of_bits(0xbfefffff, 0xfffffffc), 0x80100000, 0x00000000, STR(__LINE__)); // 0x1.0000000000002p-1022 * -0x1.ffffffffffffcp-1 = -0x1p-1022
  comp64(double_of_bits(0x3fe00000, 0x00000002) * double_of_bits(0x001fffff, 0xfffffffb), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x1.0000000000002p-1 * 0x1.ffffffffffffbp-1022 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x001fffff, 0xfffffffb) * double_of_bits(0x3fe00000, 0x00000002), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x1.ffffffffffffbp-1022 * 0x1.0000000000002p-1 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0xbfe00000, 0x00000002) * double_of_bits(0x801fffff, 0xfffffffb), 0x000fffff, 0xffffffff, STR(__LINE__)); // -0x1.0000000000002p-1 * -0x1.ffffffffffffbp-1022 = 0x0.fffffffffffffp-1022
}

void f233(void) {
  comp64(double_of_bits(0x801fffff, 0xfffffffb) * double_of_bits(0xbfe00000, 0x00000002), 0x000fffff, 0xffffffff, STR(__LINE__)); // -0x1.ffffffffffffbp-1022 * -0x1.0000000000002p-1 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0xbfe00000, 0x00000002) * double_of_bits(0x001fffff, 0xfffffffb), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x1.0000000000002p-1 * 0x1.ffffffffffffbp-1022 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x001fffff, 0xfffffffb) * double_of_bits(0xbfe00000, 0x00000002), 0x800fffff, 0xffffffff, STR(__LINE__)); // 0x1.ffffffffffffbp-1022 * -0x1.0000000000002p-1 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x801fffff, 0xfffffffb) * double_of_bits(0x3fe00000, 0x00000002), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x1.ffffffffffffbp-1022 * 0x1.0000000000002p-1 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x3fe00000, 0x00000002) * double_of_bits(0x801fffff, 0xfffffffb), 0x800fffff, 0xffffffff, STR(__LINE__)); // 0x1.0000000000002p-1 * -0x1.ffffffffffffbp-1022 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x001fffff, 0xffffffff) * double_of_bits(0x3fe00000, 0x00000000), 0x00100000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp-1022 * 0x1p-1 = 0x1p-1022
  comp64(double_of_bits(0x3fe00000, 0x00000000) * double_of_bits(0x001fffff, 0xffffffff), 0x00100000, 0x00000000, STR(__LINE__)); // 0x1p-1 * 0x1.fffffffffffffp-1022 = 0x1p-1022
  comp64(double_of_bits(0x801fffff, 0xffffffff) * double_of_bits(0xbfe00000, 0x00000000), 0x00100000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp-1022 * -0x1p-1 = 0x1p-1022
  comp64(double_of_bits(0xbfe00000, 0x00000000) * double_of_bits(0x801fffff, 0xffffffff), 0x00100000, 0x00000000, STR(__LINE__)); // -0x1p-1 * -0x1.fffffffffffffp-1022 = 0x1p-1022
  comp64(double_of_bits(0x801fffff, 0xffffffff) * double_of_bits(0x3fe00000, 0x00000000), 0x80100000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp-1022 * 0x1p-1 = -0x1p-1022
}

void f234(void) {
  comp64(double_of_bits(0x3fe00000, 0x00000000) * double_of_bits(0x801fffff, 0xffffffff), 0x80100000, 0x00000000, STR(__LINE__)); // 0x1p-1 * -0x1.fffffffffffffp-1022 = -0x1p-1022
  comp64(double_of_bits(0xbfe00000, 0x00000000) * double_of_bits(0x001fffff, 0xffffffff), 0x80100000, 0x00000000, STR(__LINE__)); // -0x1p-1 * 0x1.fffffffffffffp-1022 = -0x1p-1022
  comp64(double_of_bits(0x001fffff, 0xffffffff) * double_of_bits(0xbfe00000, 0x00000000), 0x80100000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp-1022 * -0x1p-1 = -0x1p-1022
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0x3fefffff, 0xfffffffe), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x1p-1022 * 0x1.ffffffffffffep-1 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) * double_of_bits(0x00100000, 0x00000000), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x1.ffffffffffffep-1 * 0x1p-1022 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0xbfefffff, 0xfffffffe), 0x000fffff, 0xffffffff, STR(__LINE__)); // -0x1p-1022 * -0x1.ffffffffffffep-1 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0xbfefffff, 0xfffffffe) * double_of_bits(0x80100000, 0x00000000), 0x000fffff, 0xffffffff, STR(__LINE__)); // -0x1.ffffffffffffep-1 * -0x1p-1022 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x80100000, 0x00000000) * double_of_bits(0x3fefffff, 0xfffffffe), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x1p-1022 * 0x1.ffffffffffffep-1 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) * double_of_bits(0x80100000, 0x00000000), 0x800fffff, 0xffffffff, STR(__LINE__)); // 0x1.ffffffffffffep-1 * -0x1p-1022 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0xbfefffff, 0xfffffffe) * double_of_bits(0x00100000, 0x00000000), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x1.ffffffffffffep-1 * 0x1p-1022 = -0x0.fffffffffffffp-1022
}

void f235(void) {
  comp64(double_of_bits(0x00100000, 0x00000000) * double_of_bits(0xbfefffff, 0xfffffffe), 0x800fffff, 0xffffffff, STR(__LINE__)); // 0x1p-1022 * -0x1.ffffffffffffep-1 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x001fffff, 0xfffffffe) * double_of_bits(0x3fe00000, 0x00000000), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x1.ffffffffffffep-1022 * 0x1p-1 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x3fe00000, 0x00000000) * double_of_bits(0x001fffff, 0xfffffffe), 0x000fffff, 0xffffffff, STR(__LINE__)); // 0x1p-1 * 0x1.ffffffffffffep-1022 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x801fffff, 0xfffffffe) * double_of_bits(0xbfe00000, 0x00000000), 0x000fffff, 0xffffffff, STR(__LINE__)); // -0x1.ffffffffffffep-1022 * -0x1p-1 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0xbfe00000, 0x00000000) * double_of_bits(0x801fffff, 0xfffffffe), 0x000fffff, 0xffffffff, STR(__LINE__)); // -0x1p-1 * -0x1.ffffffffffffep-1022 = 0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x801fffff, 0xfffffffe) * double_of_bits(0x3fe00000, 0x00000000), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x1.ffffffffffffep-1022 * 0x1p-1 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x3fe00000, 0x00000000) * double_of_bits(0x801fffff, 0xfffffffe), 0x800fffff, 0xffffffff, STR(__LINE__)); // 0x1p-1 * -0x1.ffffffffffffep-1022 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0xbfe00000, 0x00000000) * double_of_bits(0x001fffff, 0xfffffffe), 0x800fffff, 0xffffffff, STR(__LINE__)); // -0x1p-1 * 0x1.ffffffffffffep-1022 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x001fffff, 0xfffffffe) * double_of_bits(0xbfe00000, 0x00000000), 0x800fffff, 0xffffffff, STR(__LINE__)); // 0x1.ffffffffffffep-1022 * -0x1p-1 = -0x0.fffffffffffffp-1022
  comp64(double_of_bits(0x001fffff, 0xfffffffc) * double_of_bits(0x3fe00000, 0x00000000), 0x000fffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffcp-1022 * 0x1p-1 = 0x0.ffffffffffffep-1022
}

void f236(void) {
  comp64(double_of_bits(0x3fe00000, 0x00000000) * double_of_bits(0x001fffff, 0xfffffffc), 0x000fffff, 0xfffffffe, STR(__LINE__)); // 0x1p-1 * 0x1.ffffffffffffcp-1022 = 0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x801fffff, 0xfffffffc) * double_of_bits(0xbfe00000, 0x00000000), 0x000fffff, 0xfffffffe, STR(__LINE__)); // -0x1.ffffffffffffcp-1022 * -0x1p-1 = 0x0.ffffffffffffep-1022
  comp64(double_of_bits(0xbfe00000, 0x00000000) * double_of_bits(0x801fffff, 0xfffffffc), 0x000fffff, 0xfffffffe, STR(__LINE__)); // -0x1p-1 * -0x1.ffffffffffffcp-1022 = 0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x801fffff, 0xfffffffc) * double_of_bits(0x3fe00000, 0x00000000), 0x800fffff, 0xfffffffe, STR(__LINE__)); // -0x1.ffffffffffffcp-1022 * 0x1p-1 = -0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x3fe00000, 0x00000000) * double_of_bits(0x801fffff, 0xfffffffc), 0x800fffff, 0xfffffffe, STR(__LINE__)); // 0x1p-1 * -0x1.ffffffffffffcp-1022 = -0x0.ffffffffffffep-1022
  comp64(double_of_bits(0xbfe00000, 0x00000000) * double_of_bits(0x001fffff, 0xfffffffc), 0x800fffff, 0xfffffffe, STR(__LINE__)); // -0x1p-1 * 0x1.ffffffffffffcp-1022 = -0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x001fffff, 0xfffffffc) * double_of_bits(0xbfe00000, 0x00000000), 0x800fffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffcp-1022 * -0x1p-1 = -0x0.ffffffffffffep-1022
  comp64(double_of_bits(0x001fffff, 0xfffffff8) * double_of_bits(0x3fe00000, 0x00000000), 0x000fffff, 0xfffffffc, STR(__LINE__)); // 0x1.ffffffffffff8p-1022 * 0x1p-1 = 0x0.ffffffffffffcp-1022
  comp64(double_of_bits(0x3fe00000, 0x00000000) * double_of_bits(0x001fffff, 0xfffffff8), 0x000fffff, 0xfffffffc, STR(__LINE__)); // 0x1p-1 * 0x1.ffffffffffff8p-1022 = 0x0.ffffffffffffcp-1022
  comp64(double_of_bits(0x801fffff, 0xfffffff8) * double_of_bits(0xbfe00000, 0x00000000), 0x000fffff, 0xfffffffc, STR(__LINE__)); // -0x1.ffffffffffff8p-1022 * -0x1p-1 = 0x0.ffffffffffffcp-1022
}

void f237(void) {
  comp64(double_of_bits(0xbfe00000, 0x00000000) * double_of_bits(0x801fffff, 0xfffffff8), 0x000fffff, 0xfffffffc, STR(__LINE__)); // -0x1p-1 * -0x1.ffffffffffff8p-1022 = 0x0.ffffffffffffcp-1022
  comp64(double_of_bits(0x801fffff, 0xfffffff8) * double_of_bits(0x3fe00000, 0x00000000), 0x800fffff, 0xfffffffc, STR(__LINE__)); // -0x1.ffffffffffff8p-1022 * 0x1p-1 = -0x0.ffffffffffffcp-1022
  comp64(double_of_bits(0x3fe00000, 0x00000000) * double_of_bits(0x801fffff, 0xfffffff8), 0x800fffff, 0xfffffffc, STR(__LINE__)); // 0x1p-1 * -0x1.ffffffffffff8p-1022 = -0x0.ffffffffffffcp-1022
  comp64(double_of_bits(0xbfe00000, 0x00000000) * double_of_bits(0x001fffff, 0xfffffff8), 0x800fffff, 0xfffffffc, STR(__LINE__)); // -0x1p-1 * 0x1.ffffffffffff8p-1022 = -0x0.ffffffffffffcp-1022
  comp64(double_of_bits(0x001fffff, 0xfffffff8) * double_of_bits(0xbfe00000, 0x00000000), 0x800fffff, 0xfffffffc, STR(__LINE__)); // 0x1.ffffffffffff8p-1022 * -0x1p-1 = -0x0.ffffffffffffcp-1022
  comp64(double_of_bits(0x00000000, 0x00000008) * double_of_bits(0x3fc00000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000008p-1022 * 0x1p-3 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x3fc00000, 0x00000000) * double_of_bits(0x00000000, 0x00000008), 0x00000000, 0x00000001, STR(__LINE__)); // 0x1p-3 * 0x0.0000000000008p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000008) * double_of_bits(0xbfc00000, 0x00000000), 0x00000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000008p-1022 * -0x1p-3 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0xbfc00000, 0x00000000) * double_of_bits(0x80000000, 0x00000008), 0x00000000, 0x00000001, STR(__LINE__)); // -0x1p-3 * -0x0.0000000000008p-1022 = 0x0.0000000000001p-1022
  comp64(double_of_bits(0x80000000, 0x00000008) * double_of_bits(0x3fc00000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // -0x0.0000000000008p-1022 * 0x1p-3 = -0x0.0000000000001p-1022
}

void f238(void) {
  comp64(double_of_bits(0x3fc00000, 0x00000000) * double_of_bits(0x80000000, 0x00000008), 0x80000000, 0x00000001, STR(__LINE__)); // 0x1p-3 * -0x0.0000000000008p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0xbfc00000, 0x00000000) * double_of_bits(0x00000000, 0x00000008), 0x80000000, 0x00000001, STR(__LINE__)); // -0x1p-3 * 0x0.0000000000008p-1022 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000008) * double_of_bits(0xbfc00000, 0x00000000), 0x80000000, 0x00000001, STR(__LINE__)); // 0x0.0000000000008p-1022 * -0x1p-3 = -0x0.0000000000001p-1022
  comp64(double_of_bits(0x00000000, 0x00000006) * double_of_bits(0x3fe00000, 0x00000000), 0x00000000, 0x00000003, STR(__LINE__)); // 0x0.0000000000006p-1022 * 0x1p-1 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0x3fe00000, 0x00000000) * double_of_bits(0x00000000, 0x00000006), 0x00000000, 0x00000003, STR(__LINE__)); // 0x1p-1 * 0x0.0000000000006p-1022 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0x80000000, 0x00000006) * double_of_bits(0xbfe00000, 0x00000000), 0x00000000, 0x00000003, STR(__LINE__)); // -0x0.0000000000006p-1022 * -0x1p-1 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0xbfe00000, 0x00000000) * double_of_bits(0x80000000, 0x00000006), 0x00000000, 0x00000003, STR(__LINE__)); // -0x1p-1 * -0x0.0000000000006p-1022 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0x80000000, 0x00000006) * double_of_bits(0x3fe00000, 0x00000000), 0x80000000, 0x00000003, STR(__LINE__)); // -0x0.0000000000006p-1022 * 0x1p-1 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0x3fe00000, 0x00000000) * double_of_bits(0x80000000, 0x00000006), 0x80000000, 0x00000003, STR(__LINE__)); // 0x1p-1 * -0x0.0000000000006p-1022 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0xbfe00000, 0x00000000) * double_of_bits(0x00000000, 0x00000006), 0x80000000, 0x00000003, STR(__LINE__)); // -0x1p-1 * 0x0.0000000000006p-1022 = -0x0.0000000000003p-1022
}

void f239(void) {
  comp64(double_of_bits(0x00000000, 0x00000006) * double_of_bits(0xbfe00000, 0x00000000), 0x80000000, 0x00000003, STR(__LINE__)); // 0x0.0000000000006p-1022 * -0x1p-1 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0x4007ffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xffffffff), 0x4007ffff, 0xfffffffe, STR(__LINE__)); // 0x1.7ffffffffffffp+1 * 0x1.fffffffffffffp-1 = 0x1.7fffffffffffep+1
  comp64(double_of_bits(0x3fefffff, 0xffffffff) * double_of_bits(0x4007ffff, 0xffffffff), 0x4007ffff, 0xfffffffe, STR(__LINE__)); // 0x1.fffffffffffffp-1 * 0x1.7ffffffffffffp+1 = 0x1.7fffffffffffep+1
  comp64(double_of_bits(0xc007ffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xffffffff), 0x4007ffff, 0xfffffffe, STR(__LINE__)); // -0x1.7ffffffffffffp+1 * -0x1.fffffffffffffp-1 = 0x1.7fffffffffffep+1
  comp64(double_of_bits(0xbfefffff, 0xffffffff) * double_of_bits(0xc007ffff, 0xffffffff), 0x4007ffff, 0xfffffffe, STR(__LINE__)); // -0x1.fffffffffffffp-1 * -0x1.7ffffffffffffp+1 = 0x1.7fffffffffffep+1
  comp64(double_of_bits(0xc007ffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xffffffff), 0xc007ffff, 0xfffffffe, STR(__LINE__)); // -0x1.7ffffffffffffp+1 * 0x1.fffffffffffffp-1 = -0x1.7fffffffffffep+1
  comp64(double_of_bits(0x3fefffff, 0xffffffff) * double_of_bits(0xc007ffff, 0xffffffff), 0xc007ffff, 0xfffffffe, STR(__LINE__)); // 0x1.fffffffffffffp-1 * -0x1.7ffffffffffffp+1 = -0x1.7fffffffffffep+1
  comp64(double_of_bits(0xbfefffff, 0xffffffff) * double_of_bits(0x4007ffff, 0xffffffff), 0xc007ffff, 0xfffffffe, STR(__LINE__)); // -0x1.fffffffffffffp-1 * 0x1.7ffffffffffffp+1 = -0x1.7fffffffffffep+1
  comp64(double_of_bits(0x4007ffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xffffffff), 0xc007ffff, 0xfffffffe, STR(__LINE__)); // 0x1.7ffffffffffffp+1 * -0x1.fffffffffffffp-1 = -0x1.7fffffffffffep+1
  comp64(double_of_bits(0x4013ffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xffffffff), 0x4013ffff, 0xfffffffe, STR(__LINE__)); // 0x1.3ffffffffffffp+2 * 0x1.fffffffffffffp-1 = 0x1.3fffffffffffep+2
}

void f240(void) {
  comp64(double_of_bits(0x3fefffff, 0xffffffff) * double_of_bits(0x4013ffff, 0xffffffff), 0x4013ffff, 0xfffffffe, STR(__LINE__)); // 0x1.fffffffffffffp-1 * 0x1.3ffffffffffffp+2 = 0x1.3fffffffffffep+2
  comp64(double_of_bits(0xc013ffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xffffffff), 0x4013ffff, 0xfffffffe, STR(__LINE__)); // -0x1.3ffffffffffffp+2 * -0x1.fffffffffffffp-1 = 0x1.3fffffffffffep+2
  comp64(double_of_bits(0xbfefffff, 0xffffffff) * double_of_bits(0xc013ffff, 0xffffffff), 0x4013ffff, 0xfffffffe, STR(__LINE__)); // -0x1.fffffffffffffp-1 * -0x1.3ffffffffffffp+2 = 0x1.3fffffffffffep+2
  comp64(double_of_bits(0xc013ffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xffffffff), 0xc013ffff, 0xfffffffe, STR(__LINE__)); // -0x1.3ffffffffffffp+2 * 0x1.fffffffffffffp-1 = -0x1.3fffffffffffep+2
  comp64(double_of_bits(0x3fefffff, 0xffffffff) * double_of_bits(0xc013ffff, 0xffffffff), 0xc013ffff, 0xfffffffe, STR(__LINE__)); // 0x1.fffffffffffffp-1 * -0x1.3ffffffffffffp+2 = -0x1.3fffffffffffep+2
  comp64(double_of_bits(0x4013ffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xffffffff), 0xc013ffff, 0xfffffffe, STR(__LINE__)); // 0x1.3ffffffffffffp+2 * -0x1.fffffffffffffp-1 = -0x1.3fffffffffffep+2
  comp64(double_of_bits(0xbfefffff, 0xffffffff) * double_of_bits(0x4013ffff, 0xffffffff), 0xc013ffff, 0xfffffffe, STR(__LINE__)); // -0x1.fffffffffffffp-1 * 0x1.3ffffffffffffp+2 = -0x1.3fffffffffffep+2
  comp64(double_of_bits(0x401bffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xffffffff), 0x401bffff, 0xfffffffe, STR(__LINE__)); // 0x1.bffffffffffffp+2 * 0x1.fffffffffffffp-1 = 0x1.bfffffffffffep+2
  comp64(double_of_bits(0x3fefffff, 0xffffffff) * double_of_bits(0x401bffff, 0xffffffff), 0x401bffff, 0xfffffffe, STR(__LINE__)); // 0x1.fffffffffffffp-1 * 0x1.bffffffffffffp+2 = 0x1.bfffffffffffep+2
  comp64(double_of_bits(0xc01bffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xffffffff), 0x401bffff, 0xfffffffe, STR(__LINE__)); // -0x1.bffffffffffffp+2 * -0x1.fffffffffffffp-1 = 0x1.bfffffffffffep+2
}

void f241(void) {
  comp64(double_of_bits(0xbfefffff, 0xffffffff) * double_of_bits(0xc01bffff, 0xffffffff), 0x401bffff, 0xfffffffe, STR(__LINE__)); // -0x1.fffffffffffffp-1 * -0x1.bffffffffffffp+2 = 0x1.bfffffffffffep+2
  comp64(double_of_bits(0xc01bffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xffffffff), 0xc01bffff, 0xfffffffe, STR(__LINE__)); // -0x1.bffffffffffffp+2 * 0x1.fffffffffffffp-1 = -0x1.bfffffffffffep+2
  comp64(double_of_bits(0x3fefffff, 0xffffffff) * double_of_bits(0xc01bffff, 0xffffffff), 0xc01bffff, 0xfffffffe, STR(__LINE__)); // 0x1.fffffffffffffp-1 * -0x1.bffffffffffffp+2 = -0x1.bfffffffffffep+2
  comp64(double_of_bits(0xbfefffff, 0xffffffff) * double_of_bits(0x401bffff, 0xffffffff), 0xc01bffff, 0xfffffffe, STR(__LINE__)); // -0x1.fffffffffffffp-1 * 0x1.bffffffffffffp+2 = -0x1.bfffffffffffep+2
  comp64(double_of_bits(0x401bffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xffffffff), 0xc01bffff, 0xfffffffe, STR(__LINE__)); // 0x1.bffffffffffffp+2 * -0x1.fffffffffffffp-1 = -0x1.bfffffffffffep+2
  comp64(double_of_bits(0x001fffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xffffffff), 0x001fffff, 0xfffffffe, STR(__LINE__)); // 0x1.fffffffffffffp-1022 * 0x1.fffffffffffffp-1 = 0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x3fefffff, 0xffffffff) * double_of_bits(0x001fffff, 0xffffffff), 0x001fffff, 0xfffffffe, STR(__LINE__)); // 0x1.fffffffffffffp-1 * 0x1.fffffffffffffp-1022 = 0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x801fffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xffffffff), 0x001fffff, 0xfffffffe, STR(__LINE__)); // -0x1.fffffffffffffp-1022 * -0x1.fffffffffffffp-1 = 0x1.ffffffffffffep-1022
  comp64(double_of_bits(0xbfefffff, 0xffffffff) * double_of_bits(0x801fffff, 0xffffffff), 0x001fffff, 0xfffffffe, STR(__LINE__)); // -0x1.fffffffffffffp-1 * -0x1.fffffffffffffp-1022 = 0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x801fffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xffffffff), 0x801fffff, 0xfffffffe, STR(__LINE__)); // -0x1.fffffffffffffp-1022 * 0x1.fffffffffffffp-1 = -0x1.ffffffffffffep-1022
}

void f242(void) {
  comp64(double_of_bits(0x3fefffff, 0xffffffff) * double_of_bits(0x801fffff, 0xffffffff), 0x801fffff, 0xfffffffe, STR(__LINE__)); // 0x1.fffffffffffffp-1 * -0x1.fffffffffffffp-1022 = -0x1.ffffffffffffep-1022
  comp64(double_of_bits(0xbfefffff, 0xffffffff) * double_of_bits(0x001fffff, 0xffffffff), 0x801fffff, 0xfffffffe, STR(__LINE__)); // -0x1.fffffffffffffp-1 * 0x1.fffffffffffffp-1022 = -0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x001fffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xffffffff), 0x801fffff, 0xfffffffe, STR(__LINE__)); // 0x1.fffffffffffffp-1022 * -0x1.fffffffffffffp-1 = -0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x7fcfffff, 0xfffffff9) * double_of_bits(0x400fffff, 0xffffffff), 0x7fefffff, 0xfffffff8, STR(__LINE__)); // 0x1.ffffffffffff9p+1021 * 0x1.fffffffffffffp+1 = 0x1.ffffffffffff8p+1023
  comp64(double_of_bits(0x400fffff, 0xffffffff) * double_of_bits(0x7fcfffff, 0xfffffff9), 0x7fefffff, 0xfffffff8, STR(__LINE__)); // 0x1.fffffffffffffp+1 * 0x1.ffffffffffff9p+1021 = 0x1.ffffffffffff8p+1023
  comp64(double_of_bits(0xffcfffff, 0xfffffff9) * double_of_bits(0xc00fffff, 0xffffffff), 0x7fefffff, 0xfffffff8, STR(__LINE__)); // -0x1.ffffffffffff9p+1021 * -0x1.fffffffffffffp+1 = 0x1.ffffffffffff8p+1023
  comp64(double_of_bits(0xc00fffff, 0xffffffff) * double_of_bits(0xffcfffff, 0xfffffff9), 0x7fefffff, 0xfffffff8, STR(__LINE__)); // -0x1.fffffffffffffp+1 * -0x1.ffffffffffff9p+1021 = 0x1.ffffffffffff8p+1023
  comp64(double_of_bits(0xffcfffff, 0xfffffff9) * double_of_bits(0x400fffff, 0xffffffff), 0xffefffff, 0xfffffff8, STR(__LINE__)); // -0x1.ffffffffffff9p+1021 * 0x1.fffffffffffffp+1 = -0x1.ffffffffffff8p+1023
  comp64(double_of_bits(0x400fffff, 0xffffffff) * double_of_bits(0xffcfffff, 0xfffffff9), 0xffefffff, 0xfffffff8, STR(__LINE__)); // 0x1.fffffffffffffp+1 * -0x1.ffffffffffff9p+1021 = -0x1.ffffffffffff8p+1023
  comp64(double_of_bits(0xc00fffff, 0xffffffff) * double_of_bits(0x7fcfffff, 0xfffffff9), 0xffefffff, 0xfffffff8, STR(__LINE__)); // -0x1.fffffffffffffp+1 * 0x1.ffffffffffff9p+1021 = -0x1.ffffffffffff8p+1023
}

void f243(void) {
  comp64(double_of_bits(0x7fcfffff, 0xfffffff9) * double_of_bits(0xc00fffff, 0xffffffff), 0xffefffff, 0xfffffff8, STR(__LINE__)); // 0x1.ffffffffffff9p+1021 * -0x1.fffffffffffffp+1 = -0x1.ffffffffffff8p+1023
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x3ff00000, 0x00000001), 0x3ff00000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+0 * 0x1.0000000000001p+0 = 0x1.0000000000002p+0
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0xbff00000, 0x00000001), 0x3ff00000, 0x00000002, STR(__LINE__)); // -0x1.0000000000001p+0 * -0x1.0000000000001p+0 = 0x1.0000000000002p+0
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x3ff00000, 0x00000001), 0xbff00000, 0x00000002, STR(__LINE__)); // -0x1.0000000000001p+0 * 0x1.0000000000001p+0 = -0x1.0000000000002p+0
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0xbff00000, 0x00000001), 0xbff00000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+0 * -0x1.0000000000001p+0 = -0x1.0000000000002p+0
  comp64(double_of_bits(0x3ff00000, 0x00000002) * double_of_bits(0x3ff00000, 0x00000001), 0x3ff00000, 0x00000003, STR(__LINE__)); // 0x1.0000000000002p+0 * 0x1.0000000000001p+0 = 0x1.0000000000003p+0
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x3ff00000, 0x00000002), 0x3ff00000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p+0 * 0x1.0000000000002p+0 = 0x1.0000000000003p+0
  comp64(double_of_bits(0xbff00000, 0x00000002) * double_of_bits(0xbff00000, 0x00000001), 0x3ff00000, 0x00000003, STR(__LINE__)); // -0x1.0000000000002p+0 * -0x1.0000000000001p+0 = 0x1.0000000000003p+0
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0xbff00000, 0x00000002), 0x3ff00000, 0x00000003, STR(__LINE__)); // -0x1.0000000000001p+0 * -0x1.0000000000002p+0 = 0x1.0000000000003p+0
  comp64(double_of_bits(0xbff00000, 0x00000002) * double_of_bits(0x3ff00000, 0x00000001), 0xbff00000, 0x00000003, STR(__LINE__)); // -0x1.0000000000002p+0 * 0x1.0000000000001p+0 = -0x1.0000000000003p+0
}

void f244(void) {
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0xbff00000, 0x00000002), 0xbff00000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p+0 * -0x1.0000000000002p+0 = -0x1.0000000000003p+0
  comp64(double_of_bits(0x3ff00000, 0x00000002) * double_of_bits(0xbff00000, 0x00000001), 0xbff00000, 0x00000003, STR(__LINE__)); // 0x1.0000000000002p+0 * -0x1.0000000000001p+0 = -0x1.0000000000003p+0
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x3ff00000, 0x00000002), 0xbff00000, 0x00000003, STR(__LINE__)); // -0x1.0000000000001p+0 * 0x1.0000000000002p+0 = -0x1.0000000000003p+0
  comp64(double_of_bits(0xbfefffff, 0xffffffff) * double_of_bits(0xffefffff, 0xffffffff), 0x7fefffff, 0xfffffffe, STR(__LINE__)); // -0x1.fffffffffffffp-1 * -0x1.fffffffffffffp+1023 = 0x1.ffffffffffffep+1023
  comp64(double_of_bits(0xffefffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xffffffff), 0x7fefffff, 0xfffffffe, STR(__LINE__)); // -0x1.fffffffffffffp+1023 * -0x1.fffffffffffffp-1 = 0x1.ffffffffffffep+1023
  comp64(double_of_bits(0x00080000, 0x00000001) * double_of_bits(0x40000000, 0x00000001), 0x00100000, 0x00000003, STR(__LINE__)); // 0x0.8000000000001p-1022 * 0x1.0000000000001p+1 = 0x1.0000000000003p-1022
  comp64(double_of_bits(0x40000000, 0x00000001) * double_of_bits(0x00080000, 0x00000001), 0x00100000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p+1 * 0x0.8000000000001p-1022 = 0x1.0000000000003p-1022
  comp64(double_of_bits(0x80080000, 0x00000001) * double_of_bits(0xc0000000, 0x00000001), 0x00100000, 0x00000003, STR(__LINE__)); // -0x0.8000000000001p-1022 * -0x1.0000000000001p+1 = 0x1.0000000000003p-1022
  comp64(double_of_bits(0xc0000000, 0x00000001) * double_of_bits(0x80080000, 0x00000001), 0x00100000, 0x00000003, STR(__LINE__)); // -0x1.0000000000001p+1 * -0x0.8000000000001p-1022 = 0x1.0000000000003p-1022
  comp64(double_of_bits(0x80080000, 0x00000001) * double_of_bits(0x40000000, 0x00000001), 0x80100000, 0x00000003, STR(__LINE__)); // -0x0.8000000000001p-1022 * 0x1.0000000000001p+1 = -0x1.0000000000003p-1022
}

void f245(void) {
  comp64(double_of_bits(0x40000000, 0x00000001) * double_of_bits(0x80080000, 0x00000001), 0x80100000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p+1 * -0x0.8000000000001p-1022 = -0x1.0000000000003p-1022
  comp64(double_of_bits(0xc0000000, 0x00000001) * double_of_bits(0x00080000, 0x00000001), 0x80100000, 0x00000003, STR(__LINE__)); // -0x1.0000000000001p+1 * 0x0.8000000000001p-1022 = -0x1.0000000000003p-1022
  comp64(double_of_bits(0x00080000, 0x00000001) * double_of_bits(0xc0000000, 0x00000001), 0x80100000, 0x00000003, STR(__LINE__)); // 0x0.8000000000001p-1022 * -0x1.0000000000001p+1 = -0x1.0000000000003p-1022
  comp64(double_of_bits(0x4007ffff, 0xffffffff) * double_of_bits(0x40080000, 0x00000000), 0x4021ffff, 0xffffffff, STR(__LINE__)); // 0x1.7ffffffffffffp+1 * 0x1.8p+1 = 0x1.1ffffffffffffp+3
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0x4007ffff, 0xffffffff), 0x4021ffff, 0xffffffff, STR(__LINE__)); // 0x1.8p+1 * 0x1.7ffffffffffffp+1 = 0x1.1ffffffffffffp+3
  comp64(double_of_bits(0xc007ffff, 0xffffffff) * double_of_bits(0xc0080000, 0x00000000), 0x4021ffff, 0xffffffff, STR(__LINE__)); // -0x1.7ffffffffffffp+1 * -0x1.8p+1 = 0x1.1ffffffffffffp+3
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0xc007ffff, 0xffffffff), 0x4021ffff, 0xffffffff, STR(__LINE__)); // -0x1.8p+1 * -0x1.7ffffffffffffp+1 = 0x1.1ffffffffffffp+3
  comp64(double_of_bits(0xc007ffff, 0xffffffff) * double_of_bits(0x40080000, 0x00000000), 0xc021ffff, 0xffffffff, STR(__LINE__)); // -0x1.7ffffffffffffp+1 * 0x1.8p+1 = -0x1.1ffffffffffffp+3
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0xc007ffff, 0xffffffff), 0xc021ffff, 0xffffffff, STR(__LINE__)); // 0x1.8p+1 * -0x1.7ffffffffffffp+1 = -0x1.1ffffffffffffp+3
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0x4007ffff, 0xffffffff), 0xc021ffff, 0xffffffff, STR(__LINE__)); // -0x1.8p+1 * 0x1.7ffffffffffffp+1 = -0x1.1ffffffffffffp+3
}

void f246(void) {
  comp64(double_of_bits(0x4007ffff, 0xffffffff) * double_of_bits(0xc0080000, 0x00000000), 0xc021ffff, 0xffffffff, STR(__LINE__)); // 0x1.7ffffffffffffp+1 * -0x1.8p+1 = -0x1.1ffffffffffffp+3
  comp64(double_of_bits(0x40140000, 0x00000000) * double_of_bits(0x7fc00000, 0x00000001), 0x7fe40000, 0x00000001, STR(__LINE__)); // 0x1.4p+2 * 0x1.0000000000001p+1021 = 0x1.4000000000001p+1023
  comp64(double_of_bits(0x7fc00000, 0x00000001) * double_of_bits(0x40140000, 0x00000000), 0x7fe40000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p+1021 * 0x1.4p+2 = 0x1.4000000000001p+1023
  comp64(double_of_bits(0xc0140000, 0x00000000) * double_of_bits(0xffc00000, 0x00000001), 0x7fe40000, 0x00000001, STR(__LINE__)); // -0x1.4p+2 * -0x1.0000000000001p+1021 = 0x1.4000000000001p+1023
  comp64(double_of_bits(0xffc00000, 0x00000001) * double_of_bits(0xc0140000, 0x00000000), 0x7fe40000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p+1021 * -0x1.4p+2 = 0x1.4000000000001p+1023
  comp64(double_of_bits(0xc0140000, 0x00000000) * double_of_bits(0x7fc00000, 0x00000001), 0xffe40000, 0x00000001, STR(__LINE__)); // -0x1.4p+2 * 0x1.0000000000001p+1021 = -0x1.4000000000001p+1023
  comp64(double_of_bits(0x7fc00000, 0x00000001) * double_of_bits(0xc0140000, 0x00000000), 0xffe40000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p+1021 * -0x1.4p+2 = -0x1.4000000000001p+1023
  comp64(double_of_bits(0xffc00000, 0x00000001) * double_of_bits(0x40140000, 0x00000000), 0xffe40000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p+1021 * 0x1.4p+2 = -0x1.4000000000001p+1023
  comp64(double_of_bits(0x40140000, 0x00000000) * double_of_bits(0xffc00000, 0x00000001), 0xffe40000, 0x00000001, STR(__LINE__)); // 0x1.4p+2 * -0x1.0000000000001p+1021 = -0x1.4000000000001p+1023
  comp64(double_of_bits(0x00240000, 0x00000000) * double_of_bits(0x40000000, 0x00000001), 0x00340000, 0x00000001, STR(__LINE__)); // 0x1.4p-1021 * 0x1.0000000000001p+1 = 0x1.4000000000001p-1020
}

void f247(void) {
  comp64(double_of_bits(0x40000000, 0x00000001) * double_of_bits(0x00240000, 0x00000000), 0x00340000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p+1 * 0x1.4p-1021 = 0x1.4000000000001p-1020
  comp64(double_of_bits(0x80240000, 0x00000000) * double_of_bits(0xc0000000, 0x00000001), 0x00340000, 0x00000001, STR(__LINE__)); // -0x1.4p-1021 * -0x1.0000000000001p+1 = 0x1.4000000000001p-1020
  comp64(double_of_bits(0xc0000000, 0x00000001) * double_of_bits(0x80240000, 0x00000000), 0x00340000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p+1 * -0x1.4p-1021 = 0x1.4000000000001p-1020
  comp64(double_of_bits(0x80240000, 0x00000000) * double_of_bits(0x40000000, 0x00000001), 0x80340000, 0x00000001, STR(__LINE__)); // -0x1.4p-1021 * 0x1.0000000000001p+1 = -0x1.4000000000001p-1020
  comp64(double_of_bits(0x40000000, 0x00000001) * double_of_bits(0x80240000, 0x00000000), 0x80340000, 0x00000001, STR(__LINE__)); // 0x1.0000000000001p+1 * -0x1.4p-1021 = -0x1.4000000000001p-1020
  comp64(double_of_bits(0xc0000000, 0x00000001) * double_of_bits(0x00240000, 0x00000000), 0x80340000, 0x00000001, STR(__LINE__)); // -0x1.0000000000001p+1 * 0x1.4p-1021 = -0x1.4000000000001p-1020
  comp64(double_of_bits(0x00240000, 0x00000000) * double_of_bits(0xc0000000, 0x00000001), 0x80340000, 0x00000001, STR(__LINE__)); // 0x1.4p-1021 * -0x1.0000000000001p+1 = -0x1.4000000000001p-1020
  comp64(double_of_bits(0x40140000, 0x00000001) * double_of_bits(0x3ff00000, 0x00000001), 0x40140000, 0x00000002, STR(__LINE__)); // 0x1.4000000000001p+2 * 0x1.0000000000001p+0 = 0x1.4000000000002p+2
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x40140000, 0x00000001), 0x40140000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+0 * 0x1.4000000000001p+2 = 0x1.4000000000002p+2
  comp64(double_of_bits(0xc0140000, 0x00000001) * double_of_bits(0xbff00000, 0x00000001), 0x40140000, 0x00000002, STR(__LINE__)); // -0x1.4000000000001p+2 * -0x1.0000000000001p+0 = 0x1.4000000000002p+2
}

void f248(void) {
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0xc0140000, 0x00000001), 0x40140000, 0x00000002, STR(__LINE__)); // -0x1.0000000000001p+0 * -0x1.4000000000001p+2 = 0x1.4000000000002p+2
  comp64(double_of_bits(0xc0140000, 0x00000001) * double_of_bits(0x3ff00000, 0x00000001), 0xc0140000, 0x00000002, STR(__LINE__)); // -0x1.4000000000001p+2 * 0x1.0000000000001p+0 = -0x1.4000000000002p+2
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0xc0140000, 0x00000001), 0xc0140000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+0 * -0x1.4000000000001p+2 = -0x1.4000000000002p+2
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x40140000, 0x00000001), 0xc0140000, 0x00000002, STR(__LINE__)); // -0x1.0000000000001p+0 * 0x1.4000000000001p+2 = -0x1.4000000000002p+2
  comp64(double_of_bits(0x40140000, 0x00000001) * double_of_bits(0xbff00000, 0x00000001), 0xc0140000, 0x00000002, STR(__LINE__)); // 0x1.4000000000001p+2 * -0x1.0000000000001p+0 = -0x1.4000000000002p+2
  comp64(double_of_bits(0x401bffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xfffffffe), 0x401bffff, 0xfffffffd, STR(__LINE__)); // 0x1.bffffffffffffp+2 * 0x1.ffffffffffffep-1 = 0x1.bfffffffffffdp+2
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) * double_of_bits(0x401bffff, 0xffffffff), 0x401bffff, 0xfffffffd, STR(__LINE__)); // 0x1.ffffffffffffep-1 * 0x1.bffffffffffffp+2 = 0x1.bfffffffffffdp+2
  comp64(double_of_bits(0xc01bffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xfffffffe), 0x401bffff, 0xfffffffd, STR(__LINE__)); // -0x1.bffffffffffffp+2 * -0x1.ffffffffffffep-1 = 0x1.bfffffffffffdp+2
  comp64(double_of_bits(0xbfefffff, 0xfffffffe) * double_of_bits(0xc01bffff, 0xffffffff), 0x401bffff, 0xfffffffd, STR(__LINE__)); // -0x1.ffffffffffffep-1 * -0x1.bffffffffffffp+2 = 0x1.bfffffffffffdp+2
  comp64(double_of_bits(0xc01bffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xfffffffe), 0xc01bffff, 0xfffffffd, STR(__LINE__)); // -0x1.bffffffffffffp+2 * 0x1.ffffffffffffep-1 = -0x1.bfffffffffffdp+2
}

void f249(void) {
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) * double_of_bits(0xc01bffff, 0xffffffff), 0xc01bffff, 0xfffffffd, STR(__LINE__)); // 0x1.ffffffffffffep-1 * -0x1.bffffffffffffp+2 = -0x1.bfffffffffffdp+2
  comp64(double_of_bits(0xbfefffff, 0xfffffffe) * double_of_bits(0x401bffff, 0xffffffff), 0xc01bffff, 0xfffffffd, STR(__LINE__)); // -0x1.ffffffffffffep-1 * 0x1.bffffffffffffp+2 = -0x1.bfffffffffffdp+2
  comp64(double_of_bits(0x401bffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xfffffffe), 0xc01bffff, 0xfffffffd, STR(__LINE__)); // 0x1.bffffffffffffp+2 * -0x1.ffffffffffffep-1 = -0x1.bfffffffffffdp+2
  comp64(double_of_bits(0x3fefffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xfffffffe), 0x3fefffff, 0xfffffffd, STR(__LINE__)); // 0x1.fffffffffffffp-1 * 0x1.ffffffffffffep-1 = 0x1.ffffffffffffdp-1
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) * double_of_bits(0x3fefffff, 0xffffffff), 0x3fefffff, 0xfffffffd, STR(__LINE__)); // 0x1.ffffffffffffep-1 * 0x1.fffffffffffffp-1 = 0x1.ffffffffffffdp-1
  comp64(double_of_bits(0xbfefffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xfffffffe), 0x3fefffff, 0xfffffffd, STR(__LINE__)); // -0x1.fffffffffffffp-1 * -0x1.ffffffffffffep-1 = 0x1.ffffffffffffdp-1
  comp64(double_of_bits(0xbfefffff, 0xfffffffe) * double_of_bits(0xbfefffff, 0xffffffff), 0x3fefffff, 0xfffffffd, STR(__LINE__)); // -0x1.ffffffffffffep-1 * -0x1.fffffffffffffp-1 = 0x1.ffffffffffffdp-1
  comp64(double_of_bits(0xbfefffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xfffffffe), 0xbfefffff, 0xfffffffd, STR(__LINE__)); // -0x1.fffffffffffffp-1 * 0x1.ffffffffffffep-1 = -0x1.ffffffffffffdp-1
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) * double_of_bits(0xbfefffff, 0xffffffff), 0xbfefffff, 0xfffffffd, STR(__LINE__)); // 0x1.ffffffffffffep-1 * -0x1.fffffffffffffp-1 = -0x1.ffffffffffffdp-1
  comp64(double_of_bits(0x3fefffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xfffffffe), 0xbfefffff, 0xfffffffd, STR(__LINE__)); // 0x1.fffffffffffffp-1 * -0x1.ffffffffffffep-1 = -0x1.ffffffffffffdp-1
}

void f250(void) {
  comp64(double_of_bits(0xbfefffff, 0xfffffffe) * double_of_bits(0x3fefffff, 0xffffffff), 0xbfefffff, 0xfffffffd, STR(__LINE__)); // -0x1.ffffffffffffep-1 * 0x1.fffffffffffffp-1 = -0x1.ffffffffffffdp-1
  comp64(double_of_bits(0x7fdfffff, 0xffffffff) * double_of_bits(0x3ff00000, 0x00000001), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1022 * 0x1.0000000000001p+0 = 0x1p+1023
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x7fdfffff, 0xffffffff), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 * 0x1.fffffffffffffp+1022 = 0x1p+1023
  comp64(double_of_bits(0xffdfffff, 0xffffffff) * double_of_bits(0xbff00000, 0x00000001), 0x7fe00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1022 * -0x1.0000000000001p+0 = 0x1p+1023
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0xffdfffff, 0xffffffff), 0x7fe00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+0 * -0x1.fffffffffffffp+1022 = 0x1p+1023
  comp64(double_of_bits(0xffdfffff, 0xffffffff) * double_of_bits(0x3ff00000, 0x00000001), 0xffe00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1022 * 0x1.0000000000001p+0 = -0x1p+1023
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0xffdfffff, 0xffffffff), 0xffe00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 * -0x1.fffffffffffffp+1022 = -0x1p+1023
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x7fdfffff, 0xffffffff), 0xffe00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+0 * 0x1.fffffffffffffp+1022 = -0x1p+1023
  comp64(double_of_bits(0x7fdfffff, 0xffffffff) * double_of_bits(0xbff00000, 0x00000001), 0xffe00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1022 * -0x1.0000000000001p+0 = -0x1p+1023
  comp64(double_of_bits(0x7fcfffff, 0xffffffff) * double_of_bits(0x40000000, 0x00000001), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1021 * 0x1.0000000000001p+1 = 0x1p+1023
}

void f251(void) {
  comp64(double_of_bits(0x40000000, 0x00000001) * double_of_bits(0x7fcfffff, 0xffffffff), 0x7fe00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+1 * 0x1.fffffffffffffp+1021 = 0x1p+1023
  comp64(double_of_bits(0xffcfffff, 0xffffffff) * double_of_bits(0xc0000000, 0x00000001), 0x7fe00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1021 * -0x1.0000000000001p+1 = 0x1p+1023
  comp64(double_of_bits(0xc0000000, 0x00000001) * double_of_bits(0xffcfffff, 0xffffffff), 0x7fe00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+1 * -0x1.fffffffffffffp+1021 = 0x1p+1023
  comp64(double_of_bits(0xffcfffff, 0xffffffff) * double_of_bits(0x40000000, 0x00000001), 0xffe00000, 0x00000000, STR(__LINE__)); // -0x1.fffffffffffffp+1021 * 0x1.0000000000001p+1 = -0x1p+1023
  comp64(double_of_bits(0x40000000, 0x00000001) * double_of_bits(0xffcfffff, 0xffffffff), 0xffe00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+1 * -0x1.fffffffffffffp+1021 = -0x1p+1023
  comp64(double_of_bits(0xc0000000, 0x00000001) * double_of_bits(0x7fcfffff, 0xffffffff), 0xffe00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+1 * 0x1.fffffffffffffp+1021 = -0x1p+1023
  comp64(double_of_bits(0x7fcfffff, 0xffffffff) * double_of_bits(0xc0000000, 0x00000001), 0xffe00000, 0x00000000, STR(__LINE__)); // 0x1.fffffffffffffp+1021 * -0x1.0000000000001p+1 = -0x1p+1023
  comp64(double_of_bits(0x00240000, 0x00000001) * double_of_bits(0x40000000, 0x00000001), 0x00340000, 0x00000002, STR(__LINE__)); // 0x1.4000000000001p-1021 * 0x1.0000000000001p+1 = 0x1.4000000000002p-1020
  comp64(double_of_bits(0x40000000, 0x00000001) * double_of_bits(0x00240000, 0x00000001), 0x00340000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+1 * 0x1.4000000000001p-1021 = 0x1.4000000000002p-1020
  comp64(double_of_bits(0x80240000, 0x00000001) * double_of_bits(0xc0000000, 0x00000001), 0x00340000, 0x00000002, STR(__LINE__)); // -0x1.4000000000001p-1021 * -0x1.0000000000001p+1 = 0x1.4000000000002p-1020
}

void f252(void) {
  comp64(double_of_bits(0xc0000000, 0x00000001) * double_of_bits(0x80240000, 0x00000001), 0x00340000, 0x00000002, STR(__LINE__)); // -0x1.0000000000001p+1 * -0x1.4000000000001p-1021 = 0x1.4000000000002p-1020
  comp64(double_of_bits(0x80240000, 0x00000001) * double_of_bits(0x40000000, 0x00000001), 0x80340000, 0x00000002, STR(__LINE__)); // -0x1.4000000000001p-1021 * 0x1.0000000000001p+1 = -0x1.4000000000002p-1020
  comp64(double_of_bits(0x40000000, 0x00000001) * double_of_bits(0x80240000, 0x00000001), 0x80340000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+1 * -0x1.4000000000001p-1021 = -0x1.4000000000002p-1020
  comp64(double_of_bits(0xc0000000, 0x00000001) * double_of_bits(0x00240000, 0x00000001), 0x80340000, 0x00000002, STR(__LINE__)); // -0x1.0000000000001p+1 * 0x1.4000000000001p-1021 = -0x1.4000000000002p-1020
  comp64(double_of_bits(0x00240000, 0x00000001) * double_of_bits(0xc0000000, 0x00000001), 0x80340000, 0x00000002, STR(__LINE__)); // 0x1.4000000000001p-1021 * -0x1.0000000000001p+1 = -0x1.4000000000002p-1020
  comp64(double_of_bits(0x40080000, 0x00000004) * double_of_bits(0x401c0000, 0x00000000), 0x40350000, 0x00000004, STR(__LINE__)); // 0x1.8000000000004p+1 * 0x1.cp+2 = 0x1.5000000000004p+4
  comp64(double_of_bits(0x401c0000, 0x00000000) * double_of_bits(0x40080000, 0x00000004), 0x40350000, 0x00000004, STR(__LINE__)); // 0x1.cp+2 * 0x1.8000000000004p+1 = 0x1.5000000000004p+4
  comp64(double_of_bits(0xc0080000, 0x00000004) * double_of_bits(0xc01c0000, 0x00000000), 0x40350000, 0x00000004, STR(__LINE__)); // -0x1.8000000000004p+1 * -0x1.cp+2 = 0x1.5000000000004p+4
  comp64(double_of_bits(0xc01c0000, 0x00000000) * double_of_bits(0xc0080000, 0x00000004), 0x40350000, 0x00000004, STR(__LINE__)); // -0x1.cp+2 * -0x1.8000000000004p+1 = 0x1.5000000000004p+4
  comp64(double_of_bits(0xc0080000, 0x00000004) * double_of_bits(0x401c0000, 0x00000000), 0xc0350000, 0x00000004, STR(__LINE__)); // -0x1.8000000000004p+1 * 0x1.cp+2 = -0x1.5000000000004p+4
}

void f253(void) {
  comp64(double_of_bits(0x401c0000, 0x00000000) * double_of_bits(0xc0080000, 0x00000004), 0xc0350000, 0x00000004, STR(__LINE__)); // 0x1.cp+2 * -0x1.8000000000004p+1 = -0x1.5000000000004p+4
  comp64(double_of_bits(0xc01c0000, 0x00000000) * double_of_bits(0x40080000, 0x00000004), 0xc0350000, 0x00000004, STR(__LINE__)); // -0x1.cp+2 * 0x1.8000000000004p+1 = -0x1.5000000000004p+4
  comp64(double_of_bits(0x40080000, 0x00000004) * double_of_bits(0xc01c0000, 0x00000000), 0xc0350000, 0x00000004, STR(__LINE__)); // 0x1.8000000000004p+1 * -0x1.cp+2 = -0x1.5000000000004p+4
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0x3ff00000, 0x00000001), 0x40080000, 0x00000002, STR(__LINE__)); // 0x1.8p+1 * 0x1.0000000000001p+0 = 0x1.8000000000002p+1
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x40080000, 0x00000000), 0x40080000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+0 * 0x1.8p+1 = 0x1.8000000000002p+1
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0xbff00000, 0x00000001), 0x40080000, 0x00000002, STR(__LINE__)); // -0x1.8p+1 * -0x1.0000000000001p+0 = 0x1.8000000000002p+1
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0xc0080000, 0x00000000), 0x40080000, 0x00000002, STR(__LINE__)); // -0x1.0000000000001p+0 * -0x1.8p+1 = 0x1.8000000000002p+1
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0x3ff00000, 0x00000001), 0xc0080000, 0x00000002, STR(__LINE__)); // -0x1.8p+1 * 0x1.0000000000001p+0 = -0x1.8000000000002p+1
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0xc0080000, 0x00000000), 0xc0080000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+0 * -0x1.8p+1 = -0x1.8000000000002p+1
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x40080000, 0x00000000), 0xc0080000, 0x00000002, STR(__LINE__)); // -0x1.0000000000001p+0 * 0x1.8p+1 = -0x1.8000000000002p+1
}

void f254(void) {
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0xbff00000, 0x00000001), 0xc0080000, 0x00000002, STR(__LINE__)); // 0x1.8p+1 * -0x1.0000000000001p+0 = -0x1.8000000000002p+1
  comp64(double_of_bits(0x3fe00000, 0x00000000) * double_of_bits(0x00100000, 0x00000003), 0x00080000, 0x00000002, STR(__LINE__)); // 0x1p-1 * 0x1.0000000000003p-1022 = 0x0.8000000000002p-1022
  comp64(double_of_bits(0x00100000, 0x00000003) * double_of_bits(0x3fe00000, 0x00000000), 0x00080000, 0x00000002, STR(__LINE__)); // 0x1.0000000000003p-1022 * 0x1p-1 = 0x0.8000000000002p-1022
  comp64(double_of_bits(0xbfe00000, 0x00000000) * double_of_bits(0x80100000, 0x00000003), 0x00080000, 0x00000002, STR(__LINE__)); // -0x1p-1 * -0x1.0000000000003p-1022 = 0x0.8000000000002p-1022
  comp64(double_of_bits(0x80100000, 0x00000003) * double_of_bits(0xbfe00000, 0x00000000), 0x00080000, 0x00000002, STR(__LINE__)); // -0x1.0000000000003p-1022 * -0x1p-1 = 0x0.8000000000002p-1022
  comp64(double_of_bits(0xbfe00000, 0x00000000) * double_of_bits(0x00100000, 0x00000003), 0x80080000, 0x00000002, STR(__LINE__)); // -0x1p-1 * 0x1.0000000000003p-1022 = -0x0.8000000000002p-1022
  comp64(double_of_bits(0x00100000, 0x00000003) * double_of_bits(0xbfe00000, 0x00000000), 0x80080000, 0x00000002, STR(__LINE__)); // 0x1.0000000000003p-1022 * -0x1p-1 = -0x0.8000000000002p-1022
  comp64(double_of_bits(0x80100000, 0x00000003) * double_of_bits(0x3fe00000, 0x00000000), 0x80080000, 0x00000002, STR(__LINE__)); // -0x1.0000000000003p-1022 * 0x1p-1 = -0x0.8000000000002p-1022
  comp64(double_of_bits(0x3fe00000, 0x00000000) * double_of_bits(0x80100000, 0x00000003), 0x80080000, 0x00000002, STR(__LINE__)); // 0x1p-1 * -0x1.0000000000003p-1022 = -0x0.8000000000002p-1022
  comp64(double_of_bits(0x40080000, 0x0000000c) * double_of_bits(0x401c0000, 0x00000000), 0x40350000, 0x0000000a, STR(__LINE__)); // 0x1.800000000000cp+1 * 0x1.cp+2 = 0x1.500000000000ap+4
}

void f255(void) {
  comp64(double_of_bits(0x401c0000, 0x00000000) * double_of_bits(0x40080000, 0x0000000c), 0x40350000, 0x0000000a, STR(__LINE__)); // 0x1.cp+2 * 0x1.800000000000cp+1 = 0x1.500000000000ap+4
  comp64(double_of_bits(0xc0080000, 0x0000000c) * double_of_bits(0xc01c0000, 0x00000000), 0x40350000, 0x0000000a, STR(__LINE__)); // -0x1.800000000000cp+1 * -0x1.cp+2 = 0x1.500000000000ap+4
  comp64(double_of_bits(0xc01c0000, 0x00000000) * double_of_bits(0xc0080000, 0x0000000c), 0x40350000, 0x0000000a, STR(__LINE__)); // -0x1.cp+2 * -0x1.800000000000cp+1 = 0x1.500000000000ap+4
  comp64(double_of_bits(0xc0080000, 0x0000000c) * double_of_bits(0x401c0000, 0x00000000), 0xc0350000, 0x0000000a, STR(__LINE__)); // -0x1.800000000000cp+1 * 0x1.cp+2 = -0x1.500000000000ap+4
  comp64(double_of_bits(0x401c0000, 0x00000000) * double_of_bits(0xc0080000, 0x0000000c), 0xc0350000, 0x0000000a, STR(__LINE__)); // 0x1.cp+2 * -0x1.800000000000cp+1 = -0x1.500000000000ap+4
  comp64(double_of_bits(0xc01c0000, 0x00000000) * double_of_bits(0x40080000, 0x0000000c), 0xc0350000, 0x0000000a, STR(__LINE__)); // -0x1.cp+2 * 0x1.800000000000cp+1 = -0x1.500000000000ap+4
  comp64(double_of_bits(0x40080000, 0x0000000c) * double_of_bits(0xc01c0000, 0x00000000), 0xc0350000, 0x0000000a, STR(__LINE__)); // 0x1.800000000000cp+1 * -0x1.cp+2 = -0x1.500000000000ap+4
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0x3ff00000, 0x00000003), 0x40080000, 0x00000004, STR(__LINE__)); // 0x1.8p+1 * 0x1.0000000000003p+0 = 0x1.8000000000004p+1
  comp64(double_of_bits(0x3ff00000, 0x00000003) * double_of_bits(0x40080000, 0x00000000), 0x40080000, 0x00000004, STR(__LINE__)); // 0x1.0000000000003p+0 * 0x1.8p+1 = 0x1.8000000000004p+1
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0xbff00000, 0x00000003), 0x40080000, 0x00000004, STR(__LINE__)); // -0x1.8p+1 * -0x1.0000000000003p+0 = 0x1.8000000000004p+1
}

void f256(void) {
  comp64(double_of_bits(0xbff00000, 0x00000003) * double_of_bits(0xc0080000, 0x00000000), 0x40080000, 0x00000004, STR(__LINE__)); // -0x1.0000000000003p+0 * -0x1.8p+1 = 0x1.8000000000004p+1
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0x3ff00000, 0x00000003), 0xc0080000, 0x00000004, STR(__LINE__)); // -0x1.8p+1 * 0x1.0000000000003p+0 = -0x1.8000000000004p+1
  comp64(double_of_bits(0x3ff00000, 0x00000003) * double_of_bits(0xc0080000, 0x00000000), 0xc0080000, 0x00000004, STR(__LINE__)); // 0x1.0000000000003p+0 * -0x1.8p+1 = -0x1.8000000000004p+1
  comp64(double_of_bits(0xbff00000, 0x00000003) * double_of_bits(0x40080000, 0x00000000), 0xc0080000, 0x00000004, STR(__LINE__)); // -0x1.0000000000003p+0 * 0x1.8p+1 = -0x1.8000000000004p+1
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0xbff00000, 0x00000003), 0xc0080000, 0x00000004, STR(__LINE__)); // 0x1.8p+1 * -0x1.0000000000003p+0 = -0x1.8000000000004p+1
  comp64(double_of_bits(0x3fe00000, 0x00000000) * double_of_bits(0x00100000, 0x00000001), 0x00080000, 0x00000000, STR(__LINE__)); // 0x1p-1 * 0x1.0000000000001p-1022 = 0x0.8p-1022
  comp64(double_of_bits(0x00100000, 0x00000001) * double_of_bits(0x3fe00000, 0x00000000), 0x00080000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p-1022 * 0x1p-1 = 0x0.8p-1022
  comp64(double_of_bits(0xbfe00000, 0x00000000) * double_of_bits(0x80100000, 0x00000001), 0x00080000, 0x00000000, STR(__LINE__)); // -0x1p-1 * -0x1.0000000000001p-1022 = 0x0.8p-1022
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0xbfe00000, 0x00000000), 0x00080000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p-1022 * -0x1p-1 = 0x0.8p-1022
  comp64(double_of_bits(0xbfe00000, 0x00000000) * double_of_bits(0x00100000, 0x00000001), 0x80080000, 0x00000000, STR(__LINE__)); // -0x1p-1 * 0x1.0000000000001p-1022 = -0x0.8p-1022
}

void f257(void) {
  comp64(double_of_bits(0x00100000, 0x00000001) * double_of_bits(0xbfe00000, 0x00000000), 0x80080000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p-1022 * -0x1p-1 = -0x0.8p-1022
  comp64(double_of_bits(0x80100000, 0x00000001) * double_of_bits(0x3fe00000, 0x00000000), 0x80080000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p-1022 * 0x1p-1 = -0x0.8p-1022
  comp64(double_of_bits(0x3fe00000, 0x00000000) * double_of_bits(0x80100000, 0x00000001), 0x80080000, 0x00000000, STR(__LINE__)); // 0x1p-1 * -0x1.0000000000001p-1022 = -0x0.8p-1022
  comp64(double_of_bits(0x3ff40000, 0x00000000) * double_of_bits(0x3fffffff, 0xfffffffe), 0x4003ffff, 0xffffffff, STR(__LINE__)); // 0x1.4p+0 * 0x1.ffffffffffffep+0 = 0x1.3ffffffffffffp+1
  comp64(double_of_bits(0x3fffffff, 0xfffffffe) * double_of_bits(0x3ff40000, 0x00000000), 0x4003ffff, 0xffffffff, STR(__LINE__)); // 0x1.ffffffffffffep+0 * 0x1.4p+0 = 0x1.3ffffffffffffp+1
  comp64(double_of_bits(0xbff40000, 0x00000000) * double_of_bits(0xbfffffff, 0xfffffffe), 0x4003ffff, 0xffffffff, STR(__LINE__)); // -0x1.4p+0 * -0x1.ffffffffffffep+0 = 0x1.3ffffffffffffp+1
  comp64(double_of_bits(0xbfffffff, 0xfffffffe) * double_of_bits(0xbff40000, 0x00000000), 0x4003ffff, 0xffffffff, STR(__LINE__)); // -0x1.ffffffffffffep+0 * -0x1.4p+0 = 0x1.3ffffffffffffp+1
  comp64(double_of_bits(0xbff40000, 0x00000000) * double_of_bits(0x3fffffff, 0xfffffffe), 0xc003ffff, 0xffffffff, STR(__LINE__)); // -0x1.4p+0 * 0x1.ffffffffffffep+0 = -0x1.3ffffffffffffp+1
  comp64(double_of_bits(0x3fffffff, 0xfffffffe) * double_of_bits(0xbff40000, 0x00000000), 0xc003ffff, 0xffffffff, STR(__LINE__)); // 0x1.ffffffffffffep+0 * -0x1.4p+0 = -0x1.3ffffffffffffp+1
  comp64(double_of_bits(0xbfffffff, 0xfffffffe) * double_of_bits(0x3ff40000, 0x00000000), 0xc003ffff, 0xffffffff, STR(__LINE__)); // -0x1.ffffffffffffep+0 * 0x1.4p+0 = -0x1.3ffffffffffffp+1
}

void f258(void) {
  comp64(double_of_bits(0x3ff40000, 0x00000000) * double_of_bits(0xbfffffff, 0xfffffffe), 0xc003ffff, 0xffffffff, STR(__LINE__)); // 0x1.4p+0 * -0x1.ffffffffffffep+0 = -0x1.3ffffffffffffp+1
  comp64(double_of_bits(0x401c0000, 0x00000000) * double_of_bits(0x3ff00000, 0x00000001), 0x401c0000, 0x00000002, STR(__LINE__)); // 0x1.cp+2 * 0x1.0000000000001p+0 = 0x1.c000000000002p+2
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x401c0000, 0x00000000), 0x401c0000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+0 * 0x1.cp+2 = 0x1.c000000000002p+2
  comp64(double_of_bits(0xc01c0000, 0x00000000) * double_of_bits(0xbff00000, 0x00000001), 0x401c0000, 0x00000002, STR(__LINE__)); // -0x1.cp+2 * -0x1.0000000000001p+0 = 0x1.c000000000002p+2
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0xc01c0000, 0x00000000), 0x401c0000, 0x00000002, STR(__LINE__)); // -0x1.0000000000001p+0 * -0x1.cp+2 = 0x1.c000000000002p+2
  comp64(double_of_bits(0xc01c0000, 0x00000000) * double_of_bits(0x3ff00000, 0x00000001), 0xc01c0000, 0x00000002, STR(__LINE__)); // -0x1.cp+2 * 0x1.0000000000001p+0 = -0x1.c000000000002p+2
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0xc01c0000, 0x00000000), 0xc01c0000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+0 * -0x1.cp+2 = -0x1.c000000000002p+2
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x401c0000, 0x00000000), 0xc01c0000, 0x00000002, STR(__LINE__)); // -0x1.0000000000001p+0 * 0x1.cp+2 = -0x1.c000000000002p+2
  comp64(double_of_bits(0x401c0000, 0x00000000) * double_of_bits(0xbff00000, 0x00000001), 0xc01c0000, 0x00000002, STR(__LINE__)); // 0x1.cp+2 * -0x1.0000000000001p+0 = -0x1.c000000000002p+2
  comp64(double_of_bits(0x002c0000, 0x00000000) * double_of_bits(0x40100000, 0x00000001), 0x004c0000, 0x00000002, STR(__LINE__)); // 0x1.cp-1021 * 0x1.0000000000001p+2 = 0x1.c000000000002p-1019
}

void f259(void) {
  comp64(double_of_bits(0x40100000, 0x00000001) * double_of_bits(0x002c0000, 0x00000000), 0x004c0000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+2 * 0x1.cp-1021 = 0x1.c000000000002p-1019
  comp64(double_of_bits(0x802c0000, 0x00000000) * double_of_bits(0xc0100000, 0x00000001), 0x004c0000, 0x00000002, STR(__LINE__)); // -0x1.cp-1021 * -0x1.0000000000001p+2 = 0x1.c000000000002p-1019
  comp64(double_of_bits(0xc0100000, 0x00000001) * double_of_bits(0x802c0000, 0x00000000), 0x004c0000, 0x00000002, STR(__LINE__)); // -0x1.0000000000001p+2 * -0x1.cp-1021 = 0x1.c000000000002p-1019
  comp64(double_of_bits(0x802c0000, 0x00000000) * double_of_bits(0x40100000, 0x00000001), 0x804c0000, 0x00000002, STR(__LINE__)); // -0x1.cp-1021 * 0x1.0000000000001p+2 = -0x1.c000000000002p-1019
  comp64(double_of_bits(0x40100000, 0x00000001) * double_of_bits(0x802c0000, 0x00000000), 0x804c0000, 0x00000002, STR(__LINE__)); // 0x1.0000000000001p+2 * -0x1.cp-1021 = -0x1.c000000000002p-1019
  comp64(double_of_bits(0xc0100000, 0x00000001) * double_of_bits(0x002c0000, 0x00000000), 0x804c0000, 0x00000002, STR(__LINE__)); // -0x1.0000000000001p+2 * 0x1.cp-1021 = -0x1.c000000000002p-1019
  comp64(double_of_bits(0x002c0000, 0x00000000) * double_of_bits(0xc0100000, 0x00000001), 0x804c0000, 0x00000002, STR(__LINE__)); // 0x1.cp-1021 * -0x1.0000000000001p+2 = -0x1.c000000000002p-1019
  comp64(double_of_bits(0x40080000, 0x00000001) * double_of_bits(0x3ff00000, 0x00000001), 0x40080000, 0x00000003, STR(__LINE__)); // 0x1.8000000000001p+1 * 0x1.0000000000001p+0 = 0x1.8000000000003p+1
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x40080000, 0x00000001), 0x40080000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p+0 * 0x1.8000000000001p+1 = 0x1.8000000000003p+1
  comp64(double_of_bits(0xc0080000, 0x00000001) * double_of_bits(0xbff00000, 0x00000001), 0x40080000, 0x00000003, STR(__LINE__)); // -0x1.8000000000001p+1 * -0x1.0000000000001p+0 = 0x1.8000000000003p+1
}

void f260(void) {
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0xc0080000, 0x00000001), 0x40080000, 0x00000003, STR(__LINE__)); // -0x1.0000000000001p+0 * -0x1.8000000000001p+1 = 0x1.8000000000003p+1
  comp64(double_of_bits(0xc0080000, 0x00000001) * double_of_bits(0x3ff00000, 0x00000001), 0xc0080000, 0x00000003, STR(__LINE__)); // -0x1.8000000000001p+1 * 0x1.0000000000001p+0 = -0x1.8000000000003p+1
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0xc0080000, 0x00000001), 0xc0080000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p+0 * -0x1.8000000000001p+1 = -0x1.8000000000003p+1
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x40080000, 0x00000001), 0xc0080000, 0x00000003, STR(__LINE__)); // -0x1.0000000000001p+0 * 0x1.8000000000001p+1 = -0x1.8000000000003p+1
  comp64(double_of_bits(0x40080000, 0x00000001) * double_of_bits(0xbff00000, 0x00000001), 0xc0080000, 0x00000003, STR(__LINE__)); // 0x1.8000000000001p+1 * -0x1.0000000000001p+0 = -0x1.8000000000003p+1
  comp64(double_of_bits(0x40080000, 0x00000001) * double_of_bits(0x3ff00000, 0x00000003), 0x40080000, 0x00000006, STR(__LINE__)); // 0x1.8000000000001p+1 * 0x1.0000000000003p+0 = 0x1.8000000000006p+1
  comp64(double_of_bits(0x3ff00000, 0x00000003) * double_of_bits(0x40080000, 0x00000001), 0x40080000, 0x00000006, STR(__LINE__)); // 0x1.0000000000003p+0 * 0x1.8000000000001p+1 = 0x1.8000000000006p+1
  comp64(double_of_bits(0xc0080000, 0x00000001) * double_of_bits(0xbff00000, 0x00000003), 0x40080000, 0x00000006, STR(__LINE__)); // -0x1.8000000000001p+1 * -0x1.0000000000003p+0 = 0x1.8000000000006p+1
  comp64(double_of_bits(0xbff00000, 0x00000003) * double_of_bits(0xc0080000, 0x00000001), 0x40080000, 0x00000006, STR(__LINE__)); // -0x1.0000000000003p+0 * -0x1.8000000000001p+1 = 0x1.8000000000006p+1
  comp64(double_of_bits(0xc0080000, 0x00000001) * double_of_bits(0x3ff00000, 0x00000003), 0xc0080000, 0x00000006, STR(__LINE__)); // -0x1.8000000000001p+1 * 0x1.0000000000003p+0 = -0x1.8000000000006p+1
}

void f261(void) {
  comp64(double_of_bits(0x3ff00000, 0x00000003) * double_of_bits(0xc0080000, 0x00000001), 0xc0080000, 0x00000006, STR(__LINE__)); // 0x1.0000000000003p+0 * -0x1.8000000000001p+1 = -0x1.8000000000006p+1
  comp64(double_of_bits(0xbff00000, 0x00000003) * double_of_bits(0x40080000, 0x00000001), 0xc0080000, 0x00000006, STR(__LINE__)); // -0x1.0000000000003p+0 * 0x1.8000000000001p+1 = -0x1.8000000000006p+1
  comp64(double_of_bits(0x40080000, 0x00000001) * double_of_bits(0xbff00000, 0x00000003), 0xc0080000, 0x00000006, STR(__LINE__)); // 0x1.8000000000001p+1 * -0x1.0000000000003p+0 = -0x1.8000000000006p+1
  comp64(double_of_bits(0x4007ffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xfffffffe), 0x4007ffff, 0xfffffffe, STR(__LINE__)); // 0x1.7ffffffffffffp+1 * 0x1.ffffffffffffep-1 = 0x1.7fffffffffffep+1
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) * double_of_bits(0x4007ffff, 0xffffffff), 0x4007ffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffep-1 * 0x1.7ffffffffffffp+1 = 0x1.7fffffffffffep+1
  comp64(double_of_bits(0xc007ffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xfffffffe), 0x4007ffff, 0xfffffffe, STR(__LINE__)); // -0x1.7ffffffffffffp+1 * -0x1.ffffffffffffep-1 = 0x1.7fffffffffffep+1
  comp64(double_of_bits(0xbfefffff, 0xfffffffe) * double_of_bits(0xc007ffff, 0xffffffff), 0x4007ffff, 0xfffffffe, STR(__LINE__)); // -0x1.ffffffffffffep-1 * -0x1.7ffffffffffffp+1 = 0x1.7fffffffffffep+1
  comp64(double_of_bits(0xc007ffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xfffffffe), 0xc007ffff, 0xfffffffe, STR(__LINE__)); // -0x1.7ffffffffffffp+1 * 0x1.ffffffffffffep-1 = -0x1.7fffffffffffep+1
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) * double_of_bits(0xc007ffff, 0xffffffff), 0xc007ffff, 0xfffffffe, STR(__LINE__)); // 0x1.ffffffffffffep-1 * -0x1.7ffffffffffffp+1 = -0x1.7fffffffffffep+1
  comp64(double_of_bits(0xbfefffff, 0xfffffffe) * double_of_bits(0x4007ffff, 0xffffffff), 0xc007ffff, 0xfffffffe, STR(__LINE__)); // -0x1.ffffffffffffep-1 * 0x1.7ffffffffffffp+1 = -0x1.7fffffffffffep+1
}

void f262(void) {
  comp64(double_of_bits(0x4007ffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xfffffffe), 0xc007ffff, 0xfffffffe, STR(__LINE__)); // 0x1.7ffffffffffffp+1 * -0x1.ffffffffffffep-1 = -0x1.7fffffffffffep+1
  comp64(double_of_bits(0x401bffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xfffffffc), 0x401bffff, 0xfffffffc, STR(__LINE__)); // 0x1.bffffffffffffp+2 * 0x1.ffffffffffffcp-1 = 0x1.bfffffffffffcp+2
  comp64(double_of_bits(0x3fefffff, 0xfffffffc) * double_of_bits(0x401bffff, 0xffffffff), 0x401bffff, 0xfffffffc, STR(__LINE__)); // 0x1.ffffffffffffcp-1 * 0x1.bffffffffffffp+2 = 0x1.bfffffffffffcp+2
  comp64(double_of_bits(0xc01bffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xfffffffc), 0x401bffff, 0xfffffffc, STR(__LINE__)); // -0x1.bffffffffffffp+2 * -0x1.ffffffffffffcp-1 = 0x1.bfffffffffffcp+2
  comp64(double_of_bits(0xbfefffff, 0xfffffffc) * double_of_bits(0xc01bffff, 0xffffffff), 0x401bffff, 0xfffffffc, STR(__LINE__)); // -0x1.ffffffffffffcp-1 * -0x1.bffffffffffffp+2 = 0x1.bfffffffffffcp+2
  comp64(double_of_bits(0xc01bffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xfffffffc), 0xc01bffff, 0xfffffffc, STR(__LINE__)); // -0x1.bffffffffffffp+2 * 0x1.ffffffffffffcp-1 = -0x1.bfffffffffffcp+2
  comp64(double_of_bits(0x3fefffff, 0xfffffffc) * double_of_bits(0xc01bffff, 0xffffffff), 0xc01bffff, 0xfffffffc, STR(__LINE__)); // 0x1.ffffffffffffcp-1 * -0x1.bffffffffffffp+2 = -0x1.bfffffffffffcp+2
  comp64(double_of_bits(0xbfefffff, 0xfffffffc) * double_of_bits(0x401bffff, 0xffffffff), 0xc01bffff, 0xfffffffc, STR(__LINE__)); // -0x1.ffffffffffffcp-1 * 0x1.bffffffffffffp+2 = -0x1.bfffffffffffcp+2
  comp64(double_of_bits(0x401bffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xfffffffc), 0xc01bffff, 0xfffffffc, STR(__LINE__)); // 0x1.bffffffffffffp+2 * -0x1.ffffffffffffcp-1 = -0x1.bfffffffffffcp+2
  comp64(double_of_bits(0x00180000, 0x00000001) * double_of_bits(0x40100000, 0x00000001), 0x00380000, 0x00000003, STR(__LINE__)); // 0x1.8000000000001p-1022 * 0x1.0000000000001p+2 = 0x1.8000000000003p-1020
}

void f263(void) {
  comp64(double_of_bits(0x40100000, 0x00000001) * double_of_bits(0x00180000, 0x00000001), 0x00380000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p+2 * 0x1.8000000000001p-1022 = 0x1.8000000000003p-1020
  comp64(double_of_bits(0x80180000, 0x00000001) * double_of_bits(0xc0100000, 0x00000001), 0x00380000, 0x00000003, STR(__LINE__)); // -0x1.8000000000001p-1022 * -0x1.0000000000001p+2 = 0x1.8000000000003p-1020
  comp64(double_of_bits(0xc0100000, 0x00000001) * double_of_bits(0x80180000, 0x00000001), 0x00380000, 0x00000003, STR(__LINE__)); // -0x1.0000000000001p+2 * -0x1.8000000000001p-1022 = 0x1.8000000000003p-1020
  comp64(double_of_bits(0x80180000, 0x00000001) * double_of_bits(0x40100000, 0x00000001), 0x80380000, 0x00000003, STR(__LINE__)); // -0x1.8000000000001p-1022 * 0x1.0000000000001p+2 = -0x1.8000000000003p-1020
  comp64(double_of_bits(0x40100000, 0x00000001) * double_of_bits(0x80180000, 0x00000001), 0x80380000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p+2 * -0x1.8000000000001p-1022 = -0x1.8000000000003p-1020
  comp64(double_of_bits(0xc0100000, 0x00000001) * double_of_bits(0x00180000, 0x00000001), 0x80380000, 0x00000003, STR(__LINE__)); // -0x1.0000000000001p+2 * 0x1.8000000000001p-1022 = -0x1.8000000000003p-1020
  comp64(double_of_bits(0x00180000, 0x00000001) * double_of_bits(0xc0100000, 0x00000001), 0x80380000, 0x00000003, STR(__LINE__)); // 0x1.8000000000001p-1022 * -0x1.0000000000001p+2 = -0x1.8000000000003p-1020
  comp64(double_of_bits(0x401c0000, 0x00000001) * double_of_bits(0x3ff00000, 0x00000001), 0x401c0000, 0x00000003, STR(__LINE__)); // 0x1.c000000000001p+2 * 0x1.0000000000001p+0 = 0x1.c000000000003p+2
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x401c0000, 0x00000001), 0x401c0000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p+0 * 0x1.c000000000001p+2 = 0x1.c000000000003p+2
  comp64(double_of_bits(0xc01c0000, 0x00000001) * double_of_bits(0xbff00000, 0x00000001), 0x401c0000, 0x00000003, STR(__LINE__)); // -0x1.c000000000001p+2 * -0x1.0000000000001p+0 = 0x1.c000000000003p+2
}

void f264(void) {
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0xc01c0000, 0x00000001), 0x401c0000, 0x00000003, STR(__LINE__)); // -0x1.0000000000001p+0 * -0x1.c000000000001p+2 = 0x1.c000000000003p+2
  comp64(double_of_bits(0xc01c0000, 0x00000001) * double_of_bits(0x3ff00000, 0x00000001), 0xc01c0000, 0x00000003, STR(__LINE__)); // -0x1.c000000000001p+2 * 0x1.0000000000001p+0 = -0x1.c000000000003p+2
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0xc01c0000, 0x00000001), 0xc01c0000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p+0 * -0x1.c000000000001p+2 = -0x1.c000000000003p+2
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x401c0000, 0x00000001), 0xc01c0000, 0x00000003, STR(__LINE__)); // -0x1.0000000000001p+0 * 0x1.c000000000001p+2 = -0x1.c000000000003p+2
  comp64(double_of_bits(0x401c0000, 0x00000001) * double_of_bits(0xbff00000, 0x00000001), 0xc01c0000, 0x00000003, STR(__LINE__)); // 0x1.c000000000001p+2 * -0x1.0000000000001p+0 = -0x1.c000000000003p+2
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) * double_of_bits(0x3ff00000, 0x00000001), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffep-1 * 0x1.0000000000001p+0 = 0x1p+0
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0x3fefffff, 0xfffffffe), 0x3ff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 * 0x1.ffffffffffffep-1 = 0x1p+0
  comp64(double_of_bits(0xbfefffff, 0xfffffffe) * double_of_bits(0xbff00000, 0x00000001), 0x3ff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffep-1 * -0x1.0000000000001p+0 = 0x1p+0
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0xbfefffff, 0xfffffffe), 0x3ff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+0 * -0x1.ffffffffffffep-1 = 0x1p+0
  comp64(double_of_bits(0xbfefffff, 0xfffffffe) * double_of_bits(0x3ff00000, 0x00000001), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x1.ffffffffffffep-1 * 0x1.0000000000001p+0 = -0x1p+0
}

void f265(void) {
  comp64(double_of_bits(0x3ff00000, 0x00000001) * double_of_bits(0xbfefffff, 0xfffffffe), 0xbff00000, 0x00000000, STR(__LINE__)); // 0x1.0000000000001p+0 * -0x1.ffffffffffffep-1 = -0x1p+0
  comp64(double_of_bits(0xbff00000, 0x00000001) * double_of_bits(0x3fefffff, 0xfffffffe), 0xbff00000, 0x00000000, STR(__LINE__)); // -0x1.0000000000001p+0 * 0x1.ffffffffffffep-1 = -0x1p+0
  comp64(double_of_bits(0x3fefffff, 0xfffffffe) * double_of_bits(0xbff00000, 0x00000001), 0xbff00000, 0x00000000, STR(__LINE__)); // 0x1.ffffffffffffep-1 * -0x1.0000000000001p+0 = -0x1p+0
  comp64(double_of_bits(0x4007ffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xfffffffd), 0x4007ffff, 0xfffffffd, STR(__LINE__)); // 0x1.7ffffffffffffp+1 * 0x1.ffffffffffffdp-1 = 0x1.7fffffffffffdp+1
  comp64(double_of_bits(0x3fefffff, 0xfffffffd) * double_of_bits(0x4007ffff, 0xffffffff), 0x4007ffff, 0xfffffffd, STR(__LINE__)); // 0x1.ffffffffffffdp-1 * 0x1.7ffffffffffffp+1 = 0x1.7fffffffffffdp+1
  comp64(double_of_bits(0xc007ffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xfffffffd), 0x4007ffff, 0xfffffffd, STR(__LINE__)); // -0x1.7ffffffffffffp+1 * -0x1.ffffffffffffdp-1 = 0x1.7fffffffffffdp+1
  comp64(double_of_bits(0xbfefffff, 0xfffffffd) * double_of_bits(0xc007ffff, 0xffffffff), 0x4007ffff, 0xfffffffd, STR(__LINE__)); // -0x1.ffffffffffffdp-1 * -0x1.7ffffffffffffp+1 = 0x1.7fffffffffffdp+1
  comp64(double_of_bits(0xc007ffff, 0xffffffff) * double_of_bits(0x3fefffff, 0xfffffffd), 0xc007ffff, 0xfffffffd, STR(__LINE__)); // -0x1.7ffffffffffffp+1 * 0x1.ffffffffffffdp-1 = -0x1.7fffffffffffdp+1
  comp64(double_of_bits(0x3fefffff, 0xfffffffd) * double_of_bits(0xc007ffff, 0xffffffff), 0xc007ffff, 0xfffffffd, STR(__LINE__)); // 0x1.ffffffffffffdp-1 * -0x1.7ffffffffffffp+1 = -0x1.7fffffffffffdp+1
  comp64(double_of_bits(0xbfefffff, 0xfffffffd) * double_of_bits(0x4007ffff, 0xffffffff), 0xc007ffff, 0xfffffffd, STR(__LINE__)); // -0x1.ffffffffffffdp-1 * 0x1.7ffffffffffffp+1 = -0x1.7fffffffffffdp+1
}

void f266(void) {
  comp64(double_of_bits(0x4007ffff, 0xffffffff) * double_of_bits(0xbfefffff, 0xfffffffd), 0xc007ffff, 0xfffffffd, STR(__LINE__)); // 0x1.7ffffffffffffp+1 * -0x1.ffffffffffffdp-1 = -0x1.7fffffffffffdp+1
  comp64(double_of_bits(0x002c0000, 0x00000001) * double_of_bits(0x40100000, 0x00000001), 0x004c0000, 0x00000003, STR(__LINE__)); // 0x1.c000000000001p-1021 * 0x1.0000000000001p+2 = 0x1.c000000000003p-1019
  comp64(double_of_bits(0x40100000, 0x00000001) * double_of_bits(0x002c0000, 0x00000001), 0x004c0000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p+2 * 0x1.c000000000001p-1021 = 0x1.c000000000003p-1019
  comp64(double_of_bits(0x802c0000, 0x00000001) * double_of_bits(0xc0100000, 0x00000001), 0x004c0000, 0x00000003, STR(__LINE__)); // -0x1.c000000000001p-1021 * -0x1.0000000000001p+2 = 0x1.c000000000003p-1019
  comp64(double_of_bits(0xc0100000, 0x00000001) * double_of_bits(0x802c0000, 0x00000001), 0x004c0000, 0x00000003, STR(__LINE__)); // -0x1.0000000000001p+2 * -0x1.c000000000001p-1021 = 0x1.c000000000003p-1019
  comp64(double_of_bits(0x802c0000, 0x00000001) * double_of_bits(0x40100000, 0x00000001), 0x804c0000, 0x00000003, STR(__LINE__)); // -0x1.c000000000001p-1021 * 0x1.0000000000001p+2 = -0x1.c000000000003p-1019
  comp64(double_of_bits(0x40100000, 0x00000001) * double_of_bits(0x802c0000, 0x00000001), 0x804c0000, 0x00000003, STR(__LINE__)); // 0x1.0000000000001p+2 * -0x1.c000000000001p-1021 = -0x1.c000000000003p-1019
  comp64(double_of_bits(0xc0100000, 0x00000001) * double_of_bits(0x002c0000, 0x00000001), 0x804c0000, 0x00000003, STR(__LINE__)); // -0x1.0000000000001p+2 * 0x1.c000000000001p-1021 = -0x1.c000000000003p-1019
  comp64(double_of_bits(0x002c0000, 0x00000001) * double_of_bits(0xc0100000, 0x00000001), 0x804c0000, 0x00000003, STR(__LINE__)); // 0x1.c000000000001p-1021 * -0x1.0000000000001p+2 = -0x1.c000000000003p-1019
  comp64(double_of_bits(0x000fffff, 0xffffffff) * double_of_bits(0x40000000, 0x00000000), 0x001fffff, 0xfffffffe, STR(__LINE__)); // 0x0.fffffffffffffp-1022 * 0x1p+1 = 0x1.ffffffffffffep-1022
}

void f267(void) {
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x000fffff, 0xffffffff), 0x001fffff, 0xfffffffe, STR(__LINE__)); // 0x1p+1 * 0x0.fffffffffffffp-1022 = 0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) * double_of_bits(0xc0000000, 0x00000000), 0x001fffff, 0xfffffffe, STR(__LINE__)); // -0x0.fffffffffffffp-1022 * -0x1p+1 = 0x1.ffffffffffffep-1022
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x800fffff, 0xffffffff), 0x001fffff, 0xfffffffe, STR(__LINE__)); // -0x1p+1 * -0x0.fffffffffffffp-1022 = 0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x800fffff, 0xffffffff) * double_of_bits(0x40000000, 0x00000000), 0x801fffff, 0xfffffffe, STR(__LINE__)); // -0x0.fffffffffffffp-1022 * 0x1p+1 = -0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x800fffff, 0xffffffff), 0x801fffff, 0xfffffffe, STR(__LINE__)); // 0x1p+1 * -0x0.fffffffffffffp-1022 = -0x1.ffffffffffffep-1022
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x000fffff, 0xffffffff), 0x801fffff, 0xfffffffe, STR(__LINE__)); // -0x1p+1 * 0x0.fffffffffffffp-1022 = -0x1.ffffffffffffep-1022
  comp64(double_of_bits(0x000fffff, 0xffffffff) * double_of_bits(0xc0000000, 0x00000000), 0x801fffff, 0xfffffffe, STR(__LINE__)); // 0x0.fffffffffffffp-1022 * -0x1p+1 = -0x1.ffffffffffffep-1022
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x000fffff, 0xfffffffd), 0x801fffff, 0xfffffffa, STR(__LINE__)); // -0x1p+1 * 0x0.ffffffffffffdp-1022 = -0x1.ffffffffffffap-1022
  comp64(double_of_bits(0x000fffff, 0xfffffffd) * double_of_bits(0xc0000000, 0x00000000), 0x801fffff, 0xfffffffa, STR(__LINE__)); // 0x0.ffffffffffffdp-1022 * -0x1p+1 = -0x1.ffffffffffffap-1022
  comp64(double_of_bits(0x800fffff, 0xfffffffd) * double_of_bits(0xc0000000, 0x00000000), 0x001fffff, 0xfffffffa, STR(__LINE__)); // -0x0.ffffffffffffdp-1022 * -0x1p+1 = 0x1.ffffffffffffap-1022
}

void f268(void) {
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x800fffff, 0xfffffffd), 0x001fffff, 0xfffffffa, STR(__LINE__)); // -0x1p+1 * -0x0.ffffffffffffdp-1022 = 0x1.ffffffffffffap-1022
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x800fffff, 0xfffffffd), 0x801fffff, 0xfffffffa, STR(__LINE__)); // 0x1p+1 * -0x0.ffffffffffffdp-1022 = -0x1.ffffffffffffap-1022
  comp64(double_of_bits(0x800fffff, 0xfffffffd) * double_of_bits(0x40000000, 0x00000000), 0x801fffff, 0xfffffffa, STR(__LINE__)); // -0x0.ffffffffffffdp-1022 * 0x1p+1 = -0x1.ffffffffffffap-1022
  comp64(double_of_bits(0x000fffff, 0xfffffffd) * double_of_bits(0x40000000, 0x00000000), 0x001fffff, 0xfffffffa, STR(__LINE__)); // 0x0.ffffffffffffdp-1022 * 0x1p+1 = 0x1.ffffffffffffap-1022
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x000fffff, 0xfffffffd), 0x001fffff, 0xfffffffa, STR(__LINE__)); // 0x1p+1 * 0x0.ffffffffffffdp-1022 = 0x1.ffffffffffffap-1022
  comp64(double_of_bits(0x000fffff, 0xfffffffc) * double_of_bits(0x40000000, 0x00000000), 0x001fffff, 0xfffffff8, STR(__LINE__)); // 0x0.ffffffffffffcp-1022 * 0x1p+1 = 0x1.ffffffffffff8p-1022
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x000fffff, 0xfffffffc), 0x001fffff, 0xfffffff8, STR(__LINE__)); // 0x1p+1 * 0x0.ffffffffffffcp-1022 = 0x1.ffffffffffff8p-1022
  comp64(double_of_bits(0x800fffff, 0xfffffffc) * double_of_bits(0xc0000000, 0x00000000), 0x001fffff, 0xfffffff8, STR(__LINE__)); // -0x0.ffffffffffffcp-1022 * -0x1p+1 = 0x1.ffffffffffff8p-1022
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x800fffff, 0xfffffffc), 0x001fffff, 0xfffffff8, STR(__LINE__)); // -0x1p+1 * -0x0.ffffffffffffcp-1022 = 0x1.ffffffffffff8p-1022
  comp64(double_of_bits(0x000fffff, 0xfffffffc) * double_of_bits(0xc0000000, 0x00000000), 0x801fffff, 0xfffffff8, STR(__LINE__)); // 0x0.ffffffffffffcp-1022 * -0x1p+1 = -0x1.ffffffffffff8p-1022
}

void f269(void) {
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x000fffff, 0xfffffffc), 0x801fffff, 0xfffffff8, STR(__LINE__)); // -0x1p+1 * 0x0.ffffffffffffcp-1022 = -0x1.ffffffffffff8p-1022
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x800fffff, 0xfffffffc), 0x801fffff, 0xfffffff8, STR(__LINE__)); // 0x1p+1 * -0x0.ffffffffffffcp-1022 = -0x1.ffffffffffff8p-1022
  comp64(double_of_bits(0x800fffff, 0xfffffffc) * double_of_bits(0x40000000, 0x00000000), 0x801fffff, 0xfffffff8, STR(__LINE__)); // -0x0.ffffffffffffcp-1022 * 0x1p+1 = -0x1.ffffffffffff8p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x40000000, 0x00000000), 0x00000000, 0x00000002, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1p+1 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000002, STR(__LINE__)); // 0x1p+1 * 0x0.0000000000001p-1022 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xc0000000, 0x00000000), 0x00000000, 0x00000002, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1p+1 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000002, STR(__LINE__)); // -0x1p+1 * -0x0.0000000000001p-1022 = 0x0.0000000000002p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xc0000000, 0x00000000), 0x80000000, 0x00000002, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1p+1 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000002, STR(__LINE__)); // -0x1p+1 * 0x0.0000000000001p-1022 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000002, STR(__LINE__)); // 0x1p+1 * -0x0.0000000000001p-1022 = -0x0.0000000000002p-1022
}

void f270(void) {
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x40000000, 0x00000000), 0x80000000, 0x00000002, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1p+1 = -0x0.0000000000002p-1022
  comp64(double_of_bits(0x00000000, 0x00000002) * double_of_bits(0x40000000, 0x00000000), 0x00000000, 0x00000004, STR(__LINE__)); // 0x0.0000000000002p-1022 * 0x1p+1 = 0x0.0000000000004p-1022
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x00000000, 0x00000002), 0x00000000, 0x00000004, STR(__LINE__)); // 0x1p+1 * 0x0.0000000000002p-1022 = 0x0.0000000000004p-1022
  comp64(double_of_bits(0x80000000, 0x00000002) * double_of_bits(0xc0000000, 0x00000000), 0x00000000, 0x00000004, STR(__LINE__)); // -0x0.0000000000002p-1022 * -0x1p+1 = 0x0.0000000000004p-1022
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x80000000, 0x00000002), 0x00000000, 0x00000004, STR(__LINE__)); // -0x1p+1 * -0x0.0000000000002p-1022 = 0x0.0000000000004p-1022
  comp64(double_of_bits(0x00000000, 0x00000002) * double_of_bits(0xc0000000, 0x00000000), 0x80000000, 0x00000004, STR(__LINE__)); // 0x0.0000000000002p-1022 * -0x1p+1 = -0x0.0000000000004p-1022
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x00000000, 0x00000002), 0x80000000, 0x00000004, STR(__LINE__)); // -0x1p+1 * 0x0.0000000000002p-1022 = -0x0.0000000000004p-1022
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x80000000, 0x00000002), 0x80000000, 0x00000004, STR(__LINE__)); // 0x1p+1 * -0x0.0000000000002p-1022 = -0x0.0000000000004p-1022
  comp64(double_of_bits(0x80000000, 0x00000002) * double_of_bits(0x40000000, 0x00000000), 0x80000000, 0x00000004, STR(__LINE__)); // -0x0.0000000000002p-1022 * 0x1p+1 = -0x0.0000000000004p-1022
  comp64(double_of_bits(0x00000000, 0x00000003) * double_of_bits(0x40000000, 0x00000000), 0x00000000, 0x00000006, STR(__LINE__)); // 0x0.0000000000003p-1022 * 0x1p+1 = 0x0.0000000000006p-1022
}

void f271(void) {
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x00000000, 0x00000003), 0x00000000, 0x00000006, STR(__LINE__)); // 0x1p+1 * 0x0.0000000000003p-1022 = 0x0.0000000000006p-1022
  comp64(double_of_bits(0x80000000, 0x00000003) * double_of_bits(0xc0000000, 0x00000000), 0x00000000, 0x00000006, STR(__LINE__)); // -0x0.0000000000003p-1022 * -0x1p+1 = 0x0.0000000000006p-1022
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x80000000, 0x00000003), 0x00000000, 0x00000006, STR(__LINE__)); // -0x1p+1 * -0x0.0000000000003p-1022 = 0x0.0000000000006p-1022
  comp64(double_of_bits(0x00000000, 0x00000003) * double_of_bits(0xc0000000, 0x00000000), 0x80000000, 0x00000006, STR(__LINE__)); // 0x0.0000000000003p-1022 * -0x1p+1 = -0x0.0000000000006p-1022
  comp64(double_of_bits(0xc0000000, 0x00000000) * double_of_bits(0x00000000, 0x00000003), 0x80000000, 0x00000006, STR(__LINE__)); // -0x1p+1 * 0x0.0000000000003p-1022 = -0x0.0000000000006p-1022
  comp64(double_of_bits(0x40000000, 0x00000000) * double_of_bits(0x80000000, 0x00000003), 0x80000000, 0x00000006, STR(__LINE__)); // 0x1p+1 * -0x0.0000000000003p-1022 = -0x0.0000000000006p-1022
  comp64(double_of_bits(0x80000000, 0x00000003) * double_of_bits(0x40000000, 0x00000000), 0x80000000, 0x00000006, STR(__LINE__)); // -0x0.0000000000003p-1022 * 0x1p+1 = -0x0.0000000000006p-1022
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000003, STR(__LINE__)); // 0x1.8p+1 * 0x0.0000000000001p-1022 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x40080000, 0x00000000), 0x00000000, 0x00000003, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1.8p+1 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000003, STR(__LINE__)); // -0x1.8p+1 * -0x0.0000000000001p-1022 = 0x0.0000000000003p-1022
}

void f272(void) {
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xc0080000, 0x00000000), 0x00000000, 0x00000003, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1.8p+1 = 0x0.0000000000003p-1022
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000003, STR(__LINE__)); // 0x1.8p+1 * -0x0.0000000000001p-1022 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x40080000, 0x00000000), 0x80000000, 0x00000003, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1.8p+1 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xc0080000, 0x00000000), 0x80000000, 0x00000003, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1.8p+1 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000003, STR(__LINE__)); // -0x1.8p+1 * 0x0.0000000000001p-1022 = -0x0.0000000000003p-1022
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0x00000000, 0x00000002), 0x00000000, 0x00000006, STR(__LINE__)); // 0x1.8p+1 * 0x0.0000000000002p-1022 = 0x0.0000000000006p-1022
  comp64(double_of_bits(0x00000000, 0x00000002) * double_of_bits(0x40080000, 0x00000000), 0x00000000, 0x00000006, STR(__LINE__)); // 0x0.0000000000002p-1022 * 0x1.8p+1 = 0x0.0000000000006p-1022
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0x80000000, 0x00000002), 0x00000000, 0x00000006, STR(__LINE__)); // -0x1.8p+1 * -0x0.0000000000002p-1022 = 0x0.0000000000006p-1022
  comp64(double_of_bits(0x80000000, 0x00000002) * double_of_bits(0xc0080000, 0x00000000), 0x00000000, 0x00000006, STR(__LINE__)); // -0x0.0000000000002p-1022 * -0x1.8p+1 = 0x0.0000000000006p-1022
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0x80000000, 0x00000002), 0x80000000, 0x00000006, STR(__LINE__)); // 0x1.8p+1 * -0x0.0000000000002p-1022 = -0x0.0000000000006p-1022
}

void f273(void) {
  comp64(double_of_bits(0x80000000, 0x00000002) * double_of_bits(0x40080000, 0x00000000), 0x80000000, 0x00000006, STR(__LINE__)); // -0x0.0000000000002p-1022 * 0x1.8p+1 = -0x0.0000000000006p-1022
  comp64(double_of_bits(0x00000000, 0x00000002) * double_of_bits(0xc0080000, 0x00000000), 0x80000000, 0x00000006, STR(__LINE__)); // 0x0.0000000000002p-1022 * -0x1.8p+1 = -0x0.0000000000006p-1022
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0x00000000, 0x00000002), 0x80000000, 0x00000006, STR(__LINE__)); // -0x1.8p+1 * 0x0.0000000000002p-1022 = -0x0.0000000000006p-1022
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0x00000000, 0x00000003), 0x00000000, 0x00000009, STR(__LINE__)); // 0x1.8p+1 * 0x0.0000000000003p-1022 = 0x0.0000000000009p-1022
  comp64(double_of_bits(0x00000000, 0x00000003) * double_of_bits(0x40080000, 0x00000000), 0x00000000, 0x00000009, STR(__LINE__)); // 0x0.0000000000003p-1022 * 0x1.8p+1 = 0x0.0000000000009p-1022
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0x80000000, 0x00000003), 0x00000000, 0x00000009, STR(__LINE__)); // -0x1.8p+1 * -0x0.0000000000003p-1022 = 0x0.0000000000009p-1022
  comp64(double_of_bits(0x80000000, 0x00000003) * double_of_bits(0xc0080000, 0x00000000), 0x00000000, 0x00000009, STR(__LINE__)); // -0x0.0000000000003p-1022 * -0x1.8p+1 = 0x0.0000000000009p-1022
  comp64(double_of_bits(0x40080000, 0x00000000) * double_of_bits(0x80000000, 0x00000003), 0x80000000, 0x00000009, STR(__LINE__)); // 0x1.8p+1 * -0x0.0000000000003p-1022 = -0x0.0000000000009p-1022
  comp64(double_of_bits(0x80000000, 0x00000003) * double_of_bits(0x40080000, 0x00000000), 0x80000000, 0x00000009, STR(__LINE__)); // -0x0.0000000000003p-1022 * 0x1.8p+1 = -0x0.0000000000009p-1022
  comp64(double_of_bits(0x00000000, 0x00000003) * double_of_bits(0xc0080000, 0x00000000), 0x80000000, 0x00000009, STR(__LINE__)); // 0x0.0000000000003p-1022 * -0x1.8p+1 = -0x0.0000000000009p-1022
}

void f274(void) {
  comp64(double_of_bits(0xc0080000, 0x00000000) * double_of_bits(0x00000000, 0x00000003), 0x80000000, 0x00000009, STR(__LINE__)); // -0x1.8p+1 * 0x0.0000000000003p-1022 = -0x0.0000000000009p-1022
  comp64(double_of_bits(0x40100000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000004, STR(__LINE__)); // 0x1p+2 * 0x0.0000000000001p-1022 = 0x0.0000000000004p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x40100000, 0x00000000), 0x00000000, 0x00000004, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1p+2 = 0x0.0000000000004p-1022
  comp64(double_of_bits(0x40100000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000004, STR(__LINE__)); // 0x1p+2 * -0x0.0000000000001p-1022 = -0x0.0000000000004p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x40100000, 0x00000000), 0x80000000, 0x00000004, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1p+2 = -0x0.0000000000004p-1022
  comp64(double_of_bits(0xc0100000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000004, STR(__LINE__)); // -0x1p+2 * -0x0.0000000000001p-1022 = 0x0.0000000000004p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xc0100000, 0x00000000), 0x00000000, 0x00000004, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1p+2 = 0x0.0000000000004p-1022
  comp64(double_of_bits(0xc0100000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000004, STR(__LINE__)); // -0x1p+2 * 0x0.0000000000001p-1022 = -0x0.0000000000004p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xc0100000, 0x00000000), 0x80000000, 0x00000004, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1p+2 = -0x0.0000000000004p-1022
  comp64(double_of_bits(0x40100000, 0x00000000) * double_of_bits(0x00000000, 0x00000002), 0x00000000, 0x00000008, STR(__LINE__)); // 0x1p+2 * 0x0.0000000000002p-1022 = 0x0.0000000000008p-1022
}

void f275(void) {
  comp64(double_of_bits(0x00000000, 0x00000002) * double_of_bits(0x40100000, 0x00000000), 0x00000000, 0x00000008, STR(__LINE__)); // 0x0.0000000000002p-1022 * 0x1p+2 = 0x0.0000000000008p-1022
  comp64(double_of_bits(0x40100000, 0x00000000) * double_of_bits(0x80000000, 0x00000002), 0x80000000, 0x00000008, STR(__LINE__)); // 0x1p+2 * -0x0.0000000000002p-1022 = -0x0.0000000000008p-1022
  comp64(double_of_bits(0x80000000, 0x00000002) * double_of_bits(0x40100000, 0x00000000), 0x80000000, 0x00000008, STR(__LINE__)); // -0x0.0000000000002p-1022 * 0x1p+2 = -0x0.0000000000008p-1022
  comp64(double_of_bits(0xc0100000, 0x00000000) * double_of_bits(0x80000000, 0x00000002), 0x00000000, 0x00000008, STR(__LINE__)); // -0x1p+2 * -0x0.0000000000002p-1022 = 0x0.0000000000008p-1022
  comp64(double_of_bits(0x80000000, 0x00000002) * double_of_bits(0xc0100000, 0x00000000), 0x00000000, 0x00000008, STR(__LINE__)); // -0x0.0000000000002p-1022 * -0x1p+2 = 0x0.0000000000008p-1022
  comp64(double_of_bits(0xc0100000, 0x00000000) * double_of_bits(0x00000000, 0x00000002), 0x80000000, 0x00000008, STR(__LINE__)); // -0x1p+2 * 0x0.0000000000002p-1022 = -0x0.0000000000008p-1022
  comp64(double_of_bits(0x00000000, 0x00000002) * double_of_bits(0xc0100000, 0x00000000), 0x80000000, 0x00000008, STR(__LINE__)); // 0x0.0000000000002p-1022 * -0x1p+2 = -0x0.0000000000008p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xc0140000, 0x00000000), 0x00000000, 0x00000005, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1.4p+2 = 0x0.0000000000005p-1022
  comp64(double_of_bits(0xc0140000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x00000000, 0x00000005, STR(__LINE__)); // -0x1.4p+2 * -0x0.0000000000001p-1022 = 0x0.0000000000005p-1022
  comp64(double_of_bits(0x40140000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x00000000, 0x00000005, STR(__LINE__)); // 0x1.4p+2 * 0x0.0000000000001p-1022 = 0x0.0000000000005p-1022
}

void f276(void) {
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x40140000, 0x00000000), 0x00000000, 0x00000005, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1.4p+2 = 0x0.0000000000005p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x40140000, 0x00000000), 0x80000000, 0x00000005, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1.4p+2 = -0x0.0000000000005p-1022
  comp64(double_of_bits(0x40140000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x80000000, 0x00000005, STR(__LINE__)); // 0x1.4p+2 * -0x0.0000000000001p-1022 = -0x0.0000000000005p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xc0140000, 0x00000000), 0x80000000, 0x00000005, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1.4p+2 = -0x0.0000000000005p-1022
  comp64(double_of_bits(0xc0140000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x80000000, 0x00000005, STR(__LINE__)); // -0x1.4p+2 * 0x0.0000000000001p-1022 = -0x0.0000000000005p-1022
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x43500000, 0x00000000), 0x00300000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1p+54 = 0x1p-1020
  comp64(double_of_bits(0x43500000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x00300000, 0x00000000, STR(__LINE__)); // 0x1p+54 * 0x0.0000000000001p-1022 = 0x1p-1020
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xc3500000, 0x00000000), 0x00300000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1p+54 = 0x1p-1020
  comp64(double_of_bits(0xc3500000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x00300000, 0x00000000, STR(__LINE__)); // -0x1p+54 * -0x0.0000000000001p-1022 = 0x1p-1020
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x43500000, 0x00000000), 0x80300000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1p+54 = -0x1p-1020
}

void f277(void) {
  comp64(double_of_bits(0x43500000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x80300000, 0x00000000, STR(__LINE__)); // 0x1p+54 * -0x0.0000000000001p-1022 = -0x1p-1020
  comp64(double_of_bits(0xc3500000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x80300000, 0x00000000, STR(__LINE__)); // -0x1p+54 * 0x0.0000000000001p-1022 = -0x1p-1020
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xc3500000, 0x00000000), 0x80300000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1p+54 = -0x1p-1020
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0x43300000, 0x00000000), 0x00100000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * 0x1p+52 = 0x1p-1022
  comp64(double_of_bits(0x43300000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x00100000, 0x00000000, STR(__LINE__)); // 0x1p+52 * 0x0.0000000000001p-1022 = 0x1p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0xc3300000, 0x00000000), 0x00100000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * -0x1p+52 = 0x1p-1022
  comp64(double_of_bits(0xc3300000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x00100000, 0x00000000, STR(__LINE__)); // -0x1p+52 * -0x0.0000000000001p-1022 = 0x1p-1022
  comp64(double_of_bits(0x80000000, 0x00000001) * double_of_bits(0x43300000, 0x00000000), 0x80100000, 0x00000000, STR(__LINE__)); // -0x0.0000000000001p-1022 * 0x1p+52 = -0x1p-1022
  comp64(double_of_bits(0x43300000, 0x00000000) * double_of_bits(0x80000000, 0x00000001), 0x80100000, 0x00000000, STR(__LINE__)); // 0x1p+52 * -0x0.0000000000001p-1022 = -0x1p-1022
  comp64(double_of_bits(0xc3300000, 0x00000000) * double_of_bits(0x00000000, 0x00000001), 0x80100000, 0x00000000, STR(__LINE__)); // -0x1p+52 * 0x0.0000000000001p-1022 = -0x1p-1022
}

void f278(void) {
  comp64(double_of_bits(0x00000000, 0x00000001) * double_of_bits(0xc3300000, 0x00000000), 0x80100000, 0x00000000, STR(__LINE__)); // 0x0.0000000000001p-1022 * -0x1p+52 = -0x1p-1022
  comp32((signed)0x00000001, 0x3f800000, STR(__LINE__)); // (signed)0x00000001 = 0x1p+0
  comp32((signed)0x00000000, 0x00000000, STR(__LINE__)); // (signed)0x00000000 = 0x0p+0
  comp32((signed)0x00000002, 0x40000000, STR(__LINE__)); // (signed)0x00000002 = 0x1p+1
  comp32((signed)0x00000003, 0x40400000, STR(__LINE__)); // (signed)0x00000003 = 0x1.8p+1
  comp32((signed)0x00000010, 0x41800000, STR(__LINE__)); // (signed)0x00000010 = 0x1p+4
  comp32((signed)0x00000100, 0x43800000, STR(__LINE__)); // (signed)0x00000100 = 0x1p+8
  comp32((signed)0x00010001, 0x47800080, STR(__LINE__)); // (signed)0x00010001 = 0x1.0001p+16
  comp32((signed)0x0000ffff, 0x477fff00, STR(__LINE__)); // (signed)0x0000ffff = 0x1.fffep+15
  comp32((signed)0x00ffffff, 0x4b7fffff, STR(__LINE__)); // (signed)0x00ffffff = 0x1.fffffep+23
}

void f279(void) {
  comp32((signed)0xffffffff, 0xbf800000, STR(__LINE__)); // (signed)0xffffffff = -0x1p+0
  comp32((signed)0xfffffff0, 0xc1800000, STR(__LINE__)); // (signed)0xfffffff0 = -0x1p+4
  comp32((signed)0x80000000, 0xcf000000, STR(__LINE__)); // (signed)0x80000000 = -0x1p+31
  comp32((signed)0x01000001, 0x4b800000, STR(__LINE__)); // (signed)0x01000001 = 0x1p+24
  comp32((signed)0x02000003, 0x4c000001, STR(__LINE__)); // (signed)0x02000003 = 0x1.000002p+25
  comp32((unsigned)0x00000001, 0x3f800000, STR(__LINE__)); // (unsigned)0x00000001 = 0x1p+0
  comp32((unsigned)0x00000000, 0x00000000, STR(__LINE__)); // (unsigned)0x00000000 = 0x0p+0
  comp32((unsigned)0x00000002, 0x40000000, STR(__LINE__)); // (unsigned)0x00000002 = 0x1p+1
  comp32((unsigned)0x00000003, 0x40400000, STR(__LINE__)); // (unsigned)0x00000003 = 0x1.8p+1
  comp32((unsigned)0x00000010, 0x41800000, STR(__LINE__)); // (unsigned)0x00000010 = 0x1p+4
}

void f280(void) {
  comp32((unsigned)0x00000100, 0x43800000, STR(__LINE__)); // (unsigned)0x00000100 = 0x1p+8
  comp32((unsigned)0x00010001, 0x47800080, STR(__LINE__)); // (unsigned)0x00010001 = 0x1.0001p+16
  comp32((unsigned)0x0000ffff, 0x477fff00, STR(__LINE__)); // (unsigned)0x0000ffff = 0x1.fffep+15
  comp32((unsigned)0x00ffffff, 0x4b7fffff, STR(__LINE__)); // (unsigned)0x00ffffff = 0x1.fffffep+23
  comp32((unsigned)0x80000000, 0x4f000000, STR(__LINE__)); // (unsigned)0x80000000 = 0x1p+31
  comp32((unsigned)0x01000001, 0x4b800000, STR(__LINE__)); // (unsigned)0x01000001 = 0x1p+24
  comp32((unsigned)0x02000003, 0x4c000001, STR(__LINE__)); // (unsigned)0x02000003 = 0x1.000002p+25
  compi((signed)single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // (signed)0x0p+0 = 00000000
  compi((signed)single_of_bits(0x3f800000), 0x00000001, STR(__LINE__)); // (signed)0x1p+0 = 00000001
  compi((signed)single_of_bits(0x40000000), 0x00000002, STR(__LINE__)); // (signed)0x1p+1 = 00000002
}

void f281(void) {
  compi((signed)single_of_bits(0x40400000), 0x00000003, STR(__LINE__)); // (signed)0x1.8p+1 = 00000003
  compi((signed)single_of_bits(0x41800000), 0x00000010, STR(__LINE__)); // (signed)0x1p+4 = 00000010
  compi((signed)single_of_bits(0x43800000), 0x00000100, STR(__LINE__)); // (signed)0x1p+8 = 00000100
  compi((signed)single_of_bits(0x47800080), 0x00010001, STR(__LINE__)); // (signed)0x1.0001p+16 = 00010001
  compi((signed)single_of_bits(0x477fff00), 0x0000ffff, STR(__LINE__)); // (signed)0x1.fffep+15 = 0000ffff
  compi((signed)single_of_bits(0xbf800000), 0xffffffff, STR(__LINE__)); // (signed)-0x1p+0 = ffffffff
  compi((signed)single_of_bits(0xcf000000), 0x80000000, STR(__LINE__)); // (signed)-0x1p+31 = 80000000
  compi((signed)single_of_bits(0x4effffff), 0x7fffff80, STR(__LINE__)); // (signed)0x1.fffffep+30 = 7fffff80
  compi((signed)single_of_bits(0xcf000000), 0x80000000, STR(__LINE__)); // (signed)-0x1p+31 = 80000000
  compi((signed)single_of_bits(0x00000001), 0x00000000, STR(__LINE__)); // (signed)0x1p-149 = 00000000
}

void f282(void) {
  compi((signed)single_of_bits(0x80000001), 0x00000000, STR(__LINE__)); // (signed)-0x1p-149 = 00000000
  compi((signed)single_of_bits(0x00800000), 0x00000000, STR(__LINE__)); // (signed)0x1p-126 = 00000000
  compi((signed)single_of_bits(0x80800000), 0x00000000, STR(__LINE__)); // (signed)-0x1p-126 = 00000000
  compi((signed)single_of_bits(0x41200001), 0x0000000a, STR(__LINE__)); // (signed)0x1.400002p+3 = 0000000a
  compi((signed)single_of_bits(0xc1200001), 0xfffffff6, STR(__LINE__)); // (signed)-0x1.400002p+3 = fffffff6
  compi((signed)single_of_bits(0x3f7fffff), 0x00000000, STR(__LINE__)); // (signed)0x1.fffffep-1 = 00000000
  compi((signed)single_of_bits(0xbf7fffff), 0x00000000, STR(__LINE__)); // (signed)-0x1.fffffep-1 = 00000000
  compi((signed)single_of_bits(0x3fffffff), 0x00000001, STR(__LINE__)); // (signed)0x1.fffffep+0 = 00000001
  compi((signed)single_of_bits(0xbfffffff), 0xffffffff, STR(__LINE__)); // (signed)-0x1.fffffep+0 = ffffffff
  compi((signed)single_of_bits(0x3fc00000), 0x00000001, STR(__LINE__)); // (signed)0x1.8p+0 = 00000001
}

void f283(void) {
  compi((signed)single_of_bits(0xbfc00000), 0xffffffff, STR(__LINE__)); // (signed)-0x1.8p+0 = ffffffff
  compi((signed)single_of_bits(0x40200000), 0x00000002, STR(__LINE__)); // (signed)0x1.4p+1 = 00000002
  compi((signed)single_of_bits(0xc0200000), 0xfffffffe, STR(__LINE__)); // (signed)-0x1.4p+1 = fffffffe
  compi((signed)single_of_bits(0x3fc00001), 0x00000001, STR(__LINE__)); // (signed)0x1.800002p+0 = 00000001
  compi((signed)single_of_bits(0xbfc00001), 0xffffffff, STR(__LINE__)); // (signed)-0x1.800002p+0 = ffffffff
  compi((signed)single_of_bits(0x3fbfffff), 0x00000001, STR(__LINE__)); // (signed)0x1.7ffffep+0 = 00000001
  compi((signed)single_of_bits(0xbfbfffff), 0xffffffff, STR(__LINE__)); // (signed)-0x1.7ffffep+0 = ffffffff
  compi((signed)single_of_bits(0x4b800001), 0x01000002, STR(__LINE__)); // (signed)0x1.000002p+24 = 01000002
  compi((signed)single_of_bits(0x4b7fffff), 0x00ffffff, STR(__LINE__)); // (signed)0x1.fffffep+23 = 00ffffff
  compi((signed)single_of_bits(0x4b000001), 0x00800001, STR(__LINE__)); // (signed)0x1.000002p+23 = 00800001
}

void f284(void) {
  compi((signed)single_of_bits(0xcb000001), 0xff7fffff, STR(__LINE__)); // (signed)-0x1.000002p+23 = ff7fffff
  compi((signed)single_of_bits(0x4a800001), 0x00400000, STR(__LINE__)); // (signed)0x1.000002p+22 = 00400000
  comp32(double_of_bits(0x00000000, 0x00000000), 0x00000000, STR(__LINE__)); // 0x0p+0 = 0x0p+0
  comp32(double_of_bits(0x80000000, 0x00000000), 0x80000000, STR(__LINE__)); // -0x0p+0 = -0x0p+0
  comp32(double_of_bits(0x7ff80000, 0x00000000), 0x7fc00000, STR(__LINE__)); // nan = nan
  comp32(double_of_bits(0xfff80000, 0x00000000), 0xffc00000, STR(__LINE__)); // -nan = -nan
  comp32(double_of_bits(0x7ff00000, 0x00000000), 0x7f800000, STR(__LINE__)); // inf = inf
  comp32(double_of_bits(0xfff00000, 0x00000000), 0xff800000, STR(__LINE__)); // -inf = -inf
  comp32(double_of_bits(0x47e00000, 0x10000000), 0x7f000000, STR(__LINE__)); // 0x1.000001p+127 = 0x1p+127
  comp32(double_of_bits(0x47f00000, 0x00000000), 0x7f800000, STR(__LINE__)); // 0x1p+128 = inf
}

void f285(void) {
  comp32(double_of_bits(0xc7f00000, 0x00000000), 0xff800000, STR(__LINE__)); // -0x1p+128 = -inf
  comp32(double_of_bits(0x47efffff, 0xffffffff), 0x7f800000, STR(__LINE__)); // 0x1.fffffffffffffp+127 = inf
  comp32(double_of_bits(0xc7efffff, 0xffffffff), 0xff800000, STR(__LINE__)); // -0x1.fffffffffffffp+127 = -inf
  comp32(double_of_bits(0x7fe00000, 0x00000000), 0x7f800000, STR(__LINE__)); // 0x1p+1023 = inf
  comp32(double_of_bits(0xffe00000, 0x00000000), 0xff800000, STR(__LINE__)); // -0x1p+1023 = -inf
  comp32(double_of_bits(0x47e00000, 0x00000000), 0x7f000000, STR(__LINE__)); // 0x1p+127 = 0x1p+127
  comp32(double_of_bits(0xc7e00000, 0x00000000), 0xff000000, STR(__LINE__)); // -0x1p+127 = -0x1p+127
  comp32(double_of_bits(0x38000000, 0x00000000), 0x00400000, STR(__LINE__)); // 0x1p-127 = 0x1p-127
  comp32(double_of_bits(0xb8000000, 0x00000000), 0x80400000, STR(__LINE__)); // -0x1p-127 = -0x1p-127
  comp32(double_of_bits(0x38100000, 0x00000000), 0x00800000, STR(__LINE__)); // 0x1p-126 = 0x1p-126
}

void f286(void) {
  comp32(double_of_bits(0xb8100000, 0x00000000), 0x80800000, STR(__LINE__)); // -0x1p-126 = -0x1p-126
  comp32(double_of_bits(0x36a00000, 0x00000000), 0x00000001, STR(__LINE__)); // 0x1p-149 = 0x1p-149
  comp32(double_of_bits(0xb6a00000, 0x00000000), 0x80000001, STR(__LINE__)); // -0x1p-149 = -0x1p-149
  comp32(double_of_bits(0x380fffff, 0xffffffff), 0x00800000, STR(__LINE__)); // 0x1.fffffffffffffp-127 = 0x1p-126
  comp32(double_of_bits(0xb80fffff, 0xffffffff), 0x80800000, STR(__LINE__)); // -0x1.fffffffffffffp-127 = -0x1p-126
  comp32(double_of_bits(0x38000000, 0x38000000), 0x00400001, STR(__LINE__)); // 0x1.0000038p-127 = 0x1.000004p-127
  comp32(double_of_bits(0xb8000000, 0x38000000), 0x80400001, STR(__LINE__)); // -0x1.0000038p-127 = -0x1.000004p-127
  comp32(double_of_bits(0x36980000, 0x00000000), 0x00000001, STR(__LINE__)); // 0x1.8p-150 = 0x1p-149
  comp32(double_of_bits(0xb6980000, 0x00000000), 0x80000001, STR(__LINE__)); // -0x1.8p-150 = -0x1p-149
  comp32(double_of_bits(0x369c0000, 0x00000000), 0x00000001, STR(__LINE__)); // 0x1.cp-150 = 0x1p-149
}

void f287(void) {
  comp32(double_of_bits(0xb69c0000, 0x00000000), 0x80000001, STR(__LINE__)); // -0x1.cp-150 = -0x1p-149
  comp32(double_of_bits(0x37f00000, 0x60000000), 0x00200001, STR(__LINE__)); // 0x1.000006p-128 = 0x1.000008p-128
  comp32(double_of_bits(0xb7f00000, 0x60000000), 0x80200001, STR(__LINE__)); // -0x1.000006p-128 = -0x1.000008p-128
  comp32(double_of_bits(0x36a80000, 0x00000000), 0x00000002, STR(__LINE__)); // 0x1.8p-149 = 0x1p-148
  comp32(double_of_bits(0xb6a80000, 0x00000000), 0x80000002, STR(__LINE__)); // -0x1.8p-149 = -0x1p-148
  comp32(double_of_bits(0x38000000, 0x60000000), 0x00400002, STR(__LINE__)); // 0x1.000006p-127 = 0x1.000008p-127
  comp32(double_of_bits(0xb8000000, 0x60000000), 0x80400002, STR(__LINE__)); // -0x1.000006p-127 = -0x1.000008p-127
  comp32(double_of_bits(0x36800000, 0x00000000), 0x00000000, STR(__LINE__)); // 0x1p-151 = 0x0p+0
  comp32(double_of_bits(0xb6800000, 0x00000000), 0x80000000, STR(__LINE__)); // -0x1p-151 = -0x0p+0
  comp32(double_of_bits(0x38000000, 0x20000000), 0x00400000, STR(__LINE__)); // 0x1.000002p-127 = 0x1p-127
}

void f288(void) {
  comp32(double_of_bits(0xb8000000, 0x20000000), 0x80400000, STR(__LINE__)); // -0x1.000002p-127 = -0x1p-127
  comp32(double_of_bits(0x36700000, 0x00000000), 0x00000000, STR(__LINE__)); // 0x1p-152 = 0x0p+0
  comp32(double_of_bits(0xb6700000, 0x00000000), 0x80000000, STR(__LINE__)); // -0x1p-152 = -0x0p+0
  comp32(double_of_bits(0x37e00000, 0x60000000), 0x00100000, STR(__LINE__)); // 0x1.000006p-129 = 0x1p-129
  comp32(double_of_bits(0xb7e00000, 0x60000000), 0x80100000, STR(__LINE__)); // -0x1.000006p-129 = -0x1p-129
  comp32(double_of_bits(0x37f00000, 0x20000000), 0x00200000, STR(__LINE__)); // 0x1.000002p-128 = 0x1p-128
  comp32(double_of_bits(0xb7f00000, 0x20000000), 0x80200000, STR(__LINE__)); // -0x1.000002p-128 = -0x1p-128
  comp32(double_of_bits(0x37e00000, 0x20000000), 0x00100000, STR(__LINE__)); // 0x1.000002p-129 = 0x1p-129
  comp32(double_of_bits(0xb7e00000, 0x20000000), 0x80100000, STR(__LINE__)); // -0x1.000002p-129 = -0x1p-129
  comp32(double_of_bits(0x36880000, 0x00000000), 0x00000000, STR(__LINE__)); // 0x1.8p-151 = 0x0p+0
}

void f289(void) {
  comp32(double_of_bits(0xb6880000, 0x00000000), 0x80000000, STR(__LINE__)); // -0x1.8p-151 = -0x0p+0
  comp32(double_of_bits(0x36700000, 0x00000000), 0x00000000, STR(__LINE__)); // 0x1p-152 = 0x0p+0
  comp32(double_of_bits(0xb6700000, 0x00000000), 0x80000000, STR(__LINE__)); // -0x1p-152 = -0x0p+0
  comp32(double_of_bits(0x3ff00000, 0x00000000), 0x3f800000, STR(__LINE__)); // 0x1p+0 = 0x1p+0
  comp32(double_of_bits(0x40000000, 0x00000000), 0x40000000, STR(__LINE__)); // 0x1p+1 = 0x1p+1
  comp32(double_of_bits(0x40080000, 0x00000000), 0x40400000, STR(__LINE__)); // 0x1.8p+1 = 0x1.8p+1
  comp32(double_of_bits(0x40300000, 0x00000000), 0x41800000, STR(__LINE__)); // 0x1p+4 = 0x1p+4
  comp32(double_of_bits(0x40310000, 0x00000000), 0x41880000, STR(__LINE__)); // 0x1.1p+4 = 0x1.1p+4
  comp32(double_of_bits(0x40700000, 0x00000000), 0x43800000, STR(__LINE__)); // 0x1p+8 = 0x1p+8
  comp32(double_of_bits(0x40f00010, 0x00000000), 0x47800080, STR(__LINE__)); // 0x1.0001p+16 = 0x1.0001p+16
}

void f290(void) {
  comp32(double_of_bits(0x40efffe0, 0x00000000), 0x477fff00, STR(__LINE__)); // 0x1.fffep+15 = 0x1.fffep+15
  comp32(double_of_bits(0xbff00000, 0x00000000), 0xbf800000, STR(__LINE__)); // -0x1p+0 = -0x1p+0
  comp32(double_of_bits(0xc1e00000, 0x00000000), 0xcf000000, STR(__LINE__)); // -0x1p+31 = -0x1p+31
  comp32(double_of_bits(0xc3e00000, 0x00000000), 0xdf000000, STR(__LINE__)); // -0x1p+63 = -0x1p+63
  comp32(double_of_bits(0x3ff00000, 0x18000000), 0x3f800001, STR(__LINE__)); // 0x1.0000018p+0 = 0x1.000002p+0
  comp32(double_of_bits(0x3ff00000, 0x10000001), 0x3f800001, STR(__LINE__)); // 0x1.0000010000001p+0 = 0x1.000002p+0
  comp32(double_of_bits(0xbfefffff, 0xffffffff), 0xbf800000, STR(__LINE__)); // -0x1.fffffffffffffp-1 = -0x1p+0
  comp32(double_of_bits(0x3ff00000, 0x30000000), 0x3f800002, STR(__LINE__)); // 0x1.000003p+0 = 0x1.000004p+0
  comp32(double_of_bits(0x3ff00000, 0x10000000), 0x3f800000, STR(__LINE__)); // 0x1.000001p+0 = 0x1p+0
  comp32(double_of_bits(0x3ff00000, 0x00000001), 0x3f800000, STR(__LINE__)); // 0x1.0000000000001p+0 = 0x1p+0
}

void f291(void) {
  compi((unsigned)single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // (unsigned)0x0p+0 = 00000000
  compi((unsigned)single_of_bits(0x3f800000), 0x00000001, STR(__LINE__)); // (unsigned)0x1p+0 = 00000001
  compi((unsigned)single_of_bits(0x40000000), 0x00000002, STR(__LINE__)); // (unsigned)0x1p+1 = 00000002
  compi((unsigned)single_of_bits(0x40400000), 0x00000003, STR(__LINE__)); // (unsigned)0x1.8p+1 = 00000003
  compi((unsigned)single_of_bits(0x41800000), 0x00000010, STR(__LINE__)); // (unsigned)0x1p+4 = 00000010
  compi((unsigned)single_of_bits(0x43800000), 0x00000100, STR(__LINE__)); // (unsigned)0x1p+8 = 00000100
  compi((unsigned)single_of_bits(0x47800080), 0x00010001, STR(__LINE__)); // (unsigned)0x1.0001p+16 = 00010001
  compi((unsigned)single_of_bits(0x477fff00), 0x0000ffff, STR(__LINE__)); // (unsigned)0x1.fffep+15 = 0000ffff
  compi((unsigned)single_of_bits(0x4f7fffff), 0xffffff00, STR(__LINE__)); // (unsigned)0x1.fffffep+31 = ffffff00
  compi((unsigned)single_of_bits(0x00000001), 0x00000000, STR(__LINE__)); // (unsigned)0x1p-149 = 00000000
}

void f292(void) {
  compi((unsigned)single_of_bits(0x00800000), 0x00000000, STR(__LINE__)); // (unsigned)0x1p-126 = 00000000
  compi((unsigned)single_of_bits(0x41200001), 0x0000000a, STR(__LINE__)); // (unsigned)0x1.400002p+3 = 0000000a
  compi((unsigned)single_of_bits(0x3f7fffff), 0x00000000, STR(__LINE__)); // (unsigned)0x1.fffffep-1 = 00000000
  compi((unsigned)single_of_bits(0x3fffffff), 0x00000001, STR(__LINE__)); // (unsigned)0x1.fffffep+0 = 00000001
  compi((unsigned)single_of_bits(0x3fc00000), 0x00000001, STR(__LINE__)); // (unsigned)0x1.8p+0 = 00000001
  compi((unsigned)single_of_bits(0x40200000), 0x00000002, STR(__LINE__)); // (unsigned)0x1.4p+1 = 00000002
  compi((unsigned)single_of_bits(0x3fc00001), 0x00000001, STR(__LINE__)); // (unsigned)0x1.800002p+0 = 00000001
  compi((unsigned)single_of_bits(0x3fbfffff), 0x00000001, STR(__LINE__)); // (unsigned)0x1.7ffffep+0 = 00000001
  compi((unsigned)single_of_bits(0x4b800001), 0x01000002, STR(__LINE__)); // (unsigned)0x1.000002p+24 = 01000002
  compi((unsigned)single_of_bits(0x4b7fffff), 0x00ffffff, STR(__LINE__)); // (unsigned)0x1.fffffep+23 = 00ffffff
}

void f293(void) {
  compi((unsigned)single_of_bits(0x4b000001), 0x00800001, STR(__LINE__)); // (unsigned)0x1.000002p+23 = 00800001
  compi((unsigned)single_of_bits(0x4a800001), 0x00400000, STR(__LINE__)); // (unsigned)0x1.000002p+22 = 00400000
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x3f800000), 0x40000000, STR(__LINE__)); // 0x1p+0 + 0x1p+0 = 0x1p+1
  comp32(single_of_bits(0xbf800000) + single_of_bits(0xbf800000), 0xc0000000, STR(__LINE__)); // -0x1p+0 + -0x1p+0 = -0x1p+1
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x40000000), 0x40400000, STR(__LINE__)); // 0x1p+0 + 0x1p+1 = 0x1.8p+1
  comp32(single_of_bits(0x40000000) + single_of_bits(0x3f800000), 0x40400000, STR(__LINE__)); // 0x1p+1 + 0x1p+0 = 0x1.8p+1
  comp32(single_of_bits(0xbf800000) + single_of_bits(0xc0000000), 0xc0400000, STR(__LINE__)); // -0x1p+0 + -0x1p+1 = -0x1.8p+1
  comp32(single_of_bits(0xc0000000) + single_of_bits(0xbf800000), 0xc0400000, STR(__LINE__)); // -0x1p+1 + -0x1p+0 = -0x1.8p+1
  comp32(single_of_bits(0x40000000) + single_of_bits(0x40000000), 0x40800000, STR(__LINE__)); // 0x1p+1 + 0x1p+1 = 0x1p+2
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x40e00000), 0x41000000, STR(__LINE__)); // 0x1p+0 + 0x1.cp+2 = 0x1p+3
}

void f294(void) {
  comp32(single_of_bits(0x40e00000) + single_of_bits(0x3f800000), 0x41000000, STR(__LINE__)); // 0x1.cp+2 + 0x1p+0 = 0x1p+3
  comp32(single_of_bits(0xbf800000) + single_of_bits(0xc0e00000), 0xc1000000, STR(__LINE__)); // -0x1p+0 + -0x1.cp+2 = -0x1p+3
  comp32(single_of_bits(0xc0e00000) + single_of_bits(0xbf800000), 0xc1000000, STR(__LINE__)); // -0x1.cp+2 + -0x1p+0 = -0x1p+3
  comp32(single_of_bits(0x40a00000) + single_of_bits(0xbf800000), 0x40800000, STR(__LINE__)); // 0x1.4p+2 + -0x1p+0 = 0x1p+2
  comp32(single_of_bits(0xbf800000) + single_of_bits(0x40a00000), 0x40800000, STR(__LINE__)); // -0x1p+0 + 0x1.4p+2 = 0x1p+2
  comp32(single_of_bits(0xc0a00000) + single_of_bits(0x3f800000), 0xc0800000, STR(__LINE__)); // -0x1.4p+2 + 0x1p+0 = -0x1p+2
  comp32(single_of_bits(0x3f800000) + single_of_bits(0xc0a00000), 0xc0800000, STR(__LINE__)); // 0x1p+0 + -0x1.4p+2 = -0x1p+2
  comp32(single_of_bits(0x40000000) + single_of_bits(0xc0a00000), 0xc0400000, STR(__LINE__)); // 0x1p+1 + -0x1.4p+2 = -0x1.8p+1
  comp32(single_of_bits(0xc0a00000) + single_of_bits(0x40000000), 0xc0400000, STR(__LINE__)); // -0x1.4p+2 + 0x1p+1 = -0x1.8p+1
  comp32(single_of_bits(0xc0000000) + single_of_bits(0x40a00000), 0x40400000, STR(__LINE__)); // -0x1p+1 + 0x1.4p+2 = 0x1.8p+1
}

void f295(void) {
  comp32(single_of_bits(0x40a00000) + single_of_bits(0xc0000000), 0x40400000, STR(__LINE__)); // 0x1.4p+2 + -0x1p+1 = 0x1.8p+1
  comp32(single_of_bits(0x40000000) + single_of_bits(0xc0800000), 0xc0000000, STR(__LINE__)); // 0x1p+1 + -0x1p+2 = -0x1p+1
  comp32(single_of_bits(0xc0800000) + single_of_bits(0x40000000), 0xc0000000, STR(__LINE__)); // -0x1p+2 + 0x1p+1 = -0x1p+1
  comp32(single_of_bits(0x40800000) + single_of_bits(0xc0000000), 0x40000000, STR(__LINE__)); // 0x1p+2 + -0x1p+1 = 0x1p+1
  comp32(single_of_bits(0xc0000000) + single_of_bits(0x40800000), 0x40000000, STR(__LINE__)); // -0x1p+1 + 0x1p+2 = 0x1p+1
  comp32(single_of_bits(0x00000000) + single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // 0x0p+0 + -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) + single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // -0x0p+0 + 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x00000000) + single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x0p+0 + 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) + single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // -0x0p+0 + -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) + single_of_bits(0x007fffff), 0x007fffff, STR(__LINE__)); // 0x0p+0 + 0x1.fffffcp-127 = 0x1.fffffcp-127
}

void f296(void) {
  comp32(single_of_bits(0x007fffff) + single_of_bits(0x00000000), 0x007fffff, STR(__LINE__)); // 0x1.fffffcp-127 + 0x0p+0 = 0x1.fffffcp-127
  comp32(single_of_bits(0x80000000) + single_of_bits(0x007fffff), 0x007fffff, STR(__LINE__)); // -0x0p+0 + 0x1.fffffcp-127 = 0x1.fffffcp-127
  comp32(single_of_bits(0x007fffff) + single_of_bits(0x80000000), 0x007fffff, STR(__LINE__)); // 0x1.fffffcp-127 + -0x0p+0 = 0x1.fffffcp-127
  comp32(single_of_bits(0x00000000) + single_of_bits(0x807fffff), 0x807fffff, STR(__LINE__)); // 0x0p+0 + -0x1.fffffcp-127 = -0x1.fffffcp-127
  comp32(single_of_bits(0x807fffff) + single_of_bits(0x00000000), 0x807fffff, STR(__LINE__)); // -0x1.fffffcp-127 + 0x0p+0 = -0x1.fffffcp-127
  comp32(single_of_bits(0x80000000) + single_of_bits(0x807fffff), 0x807fffff, STR(__LINE__)); // -0x0p+0 + -0x1.fffffcp-127 = -0x1.fffffcp-127
  comp32(single_of_bits(0x807fffff) + single_of_bits(0x80000000), 0x807fffff, STR(__LINE__)); // -0x1.fffffcp-127 + -0x0p+0 = -0x1.fffffcp-127
  comp32(single_of_bits(0x00000003) + single_of_bits(0x00000000), 0x00000003, STR(__LINE__)); // 0x1.8p-148 + 0x0p+0 = 0x1.8p-148
  comp32(single_of_bits(0x00000000) + single_of_bits(0x00000003), 0x00000003, STR(__LINE__)); // 0x0p+0 + 0x1.8p-148 = 0x1.8p-148
  comp32(single_of_bits(0x00000003) + single_of_bits(0x80000000), 0x00000003, STR(__LINE__)); // 0x1.8p-148 + -0x0p+0 = 0x1.8p-148
}

void f297(void) {
  comp32(single_of_bits(0x80000000) + single_of_bits(0x00000003), 0x00000003, STR(__LINE__)); // -0x0p+0 + 0x1.8p-148 = 0x1.8p-148
  comp32(single_of_bits(0x80000003) + single_of_bits(0x00000000), 0x80000003, STR(__LINE__)); // -0x1.8p-148 + 0x0p+0 = -0x1.8p-148
  comp32(single_of_bits(0x00000000) + single_of_bits(0x80000003), 0x80000003, STR(__LINE__)); // 0x0p+0 + -0x1.8p-148 = -0x1.8p-148
  comp32(single_of_bits(0x80000003) + single_of_bits(0x80000000), 0x80000003, STR(__LINE__)); // -0x1.8p-148 + -0x0p+0 = -0x1.8p-148
  comp32(single_of_bits(0x80000000) + single_of_bits(0x80000003), 0x80000003, STR(__LINE__)); // -0x0p+0 + -0x1.8p-148 = -0x1.8p-148
  comp32(single_of_bits(0x80000000) + single_of_bits(0x80800000), 0x80800000, STR(__LINE__)); // -0x0p+0 + -0x1p-126 = -0x1p-126
  comp32(single_of_bits(0x80800000) + single_of_bits(0x80000000), 0x80800000, STR(__LINE__)); // -0x1p-126 + -0x0p+0 = -0x1p-126
  comp32(single_of_bits(0x00800000) + single_of_bits(0x00000000), 0x00800000, STR(__LINE__)); // 0x1p-126 + 0x0p+0 = 0x1p-126
  comp32(single_of_bits(0x00000000) + single_of_bits(0x00800000), 0x00800000, STR(__LINE__)); // 0x0p+0 + 0x1p-126 = 0x1p-126
  comp32(single_of_bits(0x00000000) + single_of_bits(0x80800000), 0x80800000, STR(__LINE__)); // 0x0p+0 + -0x1p-126 = -0x1p-126
}

void f298(void) {
  comp32(single_of_bits(0x80800000) + single_of_bits(0x00000000), 0x80800000, STR(__LINE__)); // -0x1p-126 + 0x0p+0 = -0x1p-126
  comp32(single_of_bits(0x00000000) + single_of_bits(0x7f000000), 0x7f000000, STR(__LINE__)); // 0x0p+0 + 0x1p+127 = 0x1p+127
  comp32(single_of_bits(0x7f000000) + single_of_bits(0x00000000), 0x7f000000, STR(__LINE__)); // 0x1p+127 + 0x0p+0 = 0x1p+127
  comp32(single_of_bits(0x80000000) + single_of_bits(0x7f000000), 0x7f000000, STR(__LINE__)); // -0x0p+0 + 0x1p+127 = 0x1p+127
  comp32(single_of_bits(0x7f000000) + single_of_bits(0x80000000), 0x7f000000, STR(__LINE__)); // 0x1p+127 + -0x0p+0 = 0x1p+127
  comp32(single_of_bits(0xff000000) + single_of_bits(0x00000000), 0xff000000, STR(__LINE__)); // -0x1p+127 + 0x0p+0 = -0x1p+127
  comp32(single_of_bits(0x00000000) + single_of_bits(0xff000000), 0xff000000, STR(__LINE__)); // 0x0p+0 + -0x1p+127 = -0x1p+127
  comp32(single_of_bits(0xff000000) + single_of_bits(0x80000000), 0xff000000, STR(__LINE__)); // -0x1p+127 + -0x0p+0 = -0x1p+127
  comp32(single_of_bits(0x80000000) + single_of_bits(0xff000000), 0xff000000, STR(__LINE__)); // -0x0p+0 + -0x1p+127 = -0x1p+127
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x80000000), 0x3f800000, STR(__LINE__)); // 0x1p+0 + -0x0p+0 = 0x1p+0
}

void f299(void) {
  comp32(single_of_bits(0x80000000) + single_of_bits(0x3f800000), 0x3f800000, STR(__LINE__)); // -0x0p+0 + 0x1p+0 = 0x1p+0
  comp32(single_of_bits(0xbf800000) + single_of_bits(0x80000000), 0xbf800000, STR(__LINE__)); // -0x1p+0 + -0x0p+0 = -0x1p+0
  comp32(single_of_bits(0x80000000) + single_of_bits(0xbf800000), 0xbf800000, STR(__LINE__)); // -0x0p+0 + -0x1p+0 = -0x1p+0
  comp32(single_of_bits(0x00000000) + single_of_bits(0x3f800000), 0x3f800000, STR(__LINE__)); // 0x0p+0 + 0x1p+0 = 0x1p+0
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x00000000), 0x3f800000, STR(__LINE__)); // 0x1p+0 + 0x0p+0 = 0x1p+0
  comp32(single_of_bits(0x40a00000) + single_of_bits(0x80000000), 0x40a00000, STR(__LINE__)); // 0x1.4p+2 + -0x0p+0 = 0x1.4p+2
  comp32(single_of_bits(0x80000000) + single_of_bits(0x40a00000), 0x40a00000, STR(__LINE__)); // -0x0p+0 + 0x1.4p+2 = 0x1.4p+2
  comp32(single_of_bits(0x40a00000) + single_of_bits(0x00000000), 0x40a00000, STR(__LINE__)); // 0x1.4p+2 + 0x0p+0 = 0x1.4p+2
  comp32(single_of_bits(0x00000000) + single_of_bits(0x40a00000), 0x40a00000, STR(__LINE__)); // 0x0p+0 + 0x1.4p+2 = 0x1.4p+2
  comp32(single_of_bits(0x7f800000) + single_of_bits(0x00000000), 0x7f800000, STR(__LINE__)); // inf + 0x0p+0 = inf
}

void f300(void) {
  comp32(single_of_bits(0x00000000) + single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // 0x0p+0 + inf = inf
  comp32(single_of_bits(0x7f800000) + single_of_bits(0x80000000), 0x7f800000, STR(__LINE__)); // inf + -0x0p+0 = inf
  comp32(single_of_bits(0x80000000) + single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // -0x0p+0 + inf = inf
  comp32(single_of_bits(0xff800000) + single_of_bits(0x00000000), 0xff800000, STR(__LINE__)); // -inf + 0x0p+0 = -inf
  comp32(single_of_bits(0x00000000) + single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // 0x0p+0 + -inf = -inf
  comp32(single_of_bits(0xff800000) + single_of_bits(0x80000000), 0xff800000, STR(__LINE__)); // -inf + -0x0p+0 = -inf
  comp32(single_of_bits(0x80000000) + single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // -0x0p+0 + -inf = -inf
  comp32(single_of_bits(0x7fc00000) + single_of_bits(0x00000000), 0x7fc00000, STR(__LINE__)); // nan + 0x0p+0 = nan
  comp32(single_of_bits(0x00000000) + single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // 0x0p+0 + nan = nan
  comp32(single_of_bits(0x7fc00000) + single_of_bits(0x80000000), 0x7fc00000, STR(__LINE__)); // nan + -0x0p+0 = nan
}

void f301(void) {
  comp32(single_of_bits(0x80000000) + single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -0x0p+0 + nan = nan
  comp32(single_of_bits(0x7f800000) + single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // inf + inf = inf
  comp32(single_of_bits(0xff800000) + single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // -inf + -inf = -inf
  comp32(single_of_bits(0xff800000) + single_of_bits(0x7f800000), 0x7fc00000, STR(__LINE__)); // -inf + inf = nan
  comp32(single_of_bits(0x7f800000) + single_of_bits(0xff800000), 0x7fc00000, STR(__LINE__)); // inf + -inf = nan
  comp32(single_of_bits(0x7f800000) + single_of_bits(0x007fffff), 0x7f800000, STR(__LINE__)); // inf + 0x1.fffffcp-127 = inf
  comp32(single_of_bits(0x007fffff) + single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // 0x1.fffffcp-127 + inf = inf
  comp32(single_of_bits(0xff800000) + single_of_bits(0x007fffff), 0xff800000, STR(__LINE__)); // -inf + 0x1.fffffcp-127 = -inf
  comp32(single_of_bits(0x007fffff) + single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // 0x1.fffffcp-127 + -inf = -inf
  comp32(single_of_bits(0x7f800000) + single_of_bits(0x807fffff), 0x7f800000, STR(__LINE__)); // inf + -0x1.fffffcp-127 = inf
}

void f302(void) {
  comp32(single_of_bits(0x807fffff) + single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // -0x1.fffffcp-127 + inf = inf
  comp32(single_of_bits(0xff800000) + single_of_bits(0x807fffff), 0xff800000, STR(__LINE__)); // -inf + -0x1.fffffcp-127 = -inf
  comp32(single_of_bits(0x807fffff) + single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // -0x1.fffffcp-127 + -inf = -inf
  comp32(single_of_bits(0x00000003) + single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // 0x1.8p-148 + inf = inf
  comp32(single_of_bits(0x7f800000) + single_of_bits(0x00000003), 0x7f800000, STR(__LINE__)); // inf + 0x1.8p-148 = inf
  comp32(single_of_bits(0x00000003) + single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // 0x1.8p-148 + -inf = -inf
  comp32(single_of_bits(0xff800000) + single_of_bits(0x00000003), 0xff800000, STR(__LINE__)); // -inf + 0x1.8p-148 = -inf
  comp32(single_of_bits(0x80000003) + single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // -0x1.8p-148 + inf = inf
  comp32(single_of_bits(0x7f800000) + single_of_bits(0x80000003), 0x7f800000, STR(__LINE__)); // inf + -0x1.8p-148 = inf
  comp32(single_of_bits(0x80000003) + single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // -0x1.8p-148 + -inf = -inf
}

void f303(void) {
  comp32(single_of_bits(0xff800000) + single_of_bits(0x80000003), 0xff800000, STR(__LINE__)); // -inf + -0x1.8p-148 = -inf
  comp32(single_of_bits(0x7f800000) + single_of_bits(0x7f000000), 0x7f800000, STR(__LINE__)); // inf + 0x1p+127 = inf
  comp32(single_of_bits(0x7f000000) + single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // 0x1p+127 + inf = inf
  comp32(single_of_bits(0x7f800000) + single_of_bits(0xff000000), 0x7f800000, STR(__LINE__)); // inf + -0x1p+127 = inf
  comp32(single_of_bits(0xff000000) + single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // -0x1p+127 + inf = inf
  comp32(single_of_bits(0xff800000) + single_of_bits(0x7f000000), 0xff800000, STR(__LINE__)); // -inf + 0x1p+127 = -inf
  comp32(single_of_bits(0x7f000000) + single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // 0x1p+127 + -inf = -inf
  comp32(single_of_bits(0xff800000) + single_of_bits(0xff000000), 0xff800000, STR(__LINE__)); // -inf + -0x1p+127 = -inf
  comp32(single_of_bits(0xff000000) + single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // -0x1p+127 + -inf = -inf
  comp32(single_of_bits(0x7fc00000) + single_of_bits(0x7f800000), 0x7fc00000, STR(__LINE__)); // nan + inf = nan
}

void f304(void) {
  comp32(single_of_bits(0x7f800000) + single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // inf + nan = nan
  comp32(single_of_bits(0x7fc00000) + single_of_bits(0xff800000), 0x7fc00000, STR(__LINE__)); // nan + -inf = nan
  comp32(single_of_bits(0xff800000) + single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -inf + nan = nan
  comp32(single_of_bits(0x7fc00000) + single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // nan + nan = nan
  comp32(single_of_bits(0x007fffff) + single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // 0x1.fffffcp-127 + nan = nan
  comp32(single_of_bits(0x7fc00000) + single_of_bits(0x007fffff), 0x7fc00000, STR(__LINE__)); // nan + 0x1.fffffcp-127 = nan
  comp32(single_of_bits(0x807fffff) + single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -0x1.fffffcp-127 + nan = nan
  comp32(single_of_bits(0x7fc00000) + single_of_bits(0x807fffff), 0x7fc00000, STR(__LINE__)); // nan + -0x1.fffffcp-127 = nan
  comp32(single_of_bits(0x7fc00000) + single_of_bits(0x00000001), 0x7fc00000, STR(__LINE__)); // nan + 0x1p-149 = nan
  comp32(single_of_bits(0x00000001) + single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // 0x1p-149 + nan = nan
}

void f305(void) {
  comp32(single_of_bits(0x7fc00000) + single_of_bits(0x80000001), 0x7fc00000, STR(__LINE__)); // nan + -0x1p-149 = nan
  comp32(single_of_bits(0x80000001) + single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -0x1p-149 + nan = nan
  comp32(single_of_bits(0x7fc00000) + single_of_bits(0x3f800000), 0x7fc00000, STR(__LINE__)); // nan + 0x1p+0 = nan
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // 0x1p+0 + nan = nan
  comp32(single_of_bits(0x7fc00000) + single_of_bits(0xbf800000), 0x7fc00000, STR(__LINE__)); // nan + -0x1p+0 = nan
  comp32(single_of_bits(0xbf800000) + single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -0x1p+0 + nan = nan
  comp32(single_of_bits(0x7fc00000) + single_of_bits(0x7f7fffff), 0x7fc00000, STR(__LINE__)); // nan + 0x1.fffffep+127 = nan
  comp32(single_of_bits(0x7f7fffff) + single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // 0x1.fffffep+127 + nan = nan
  comp32(single_of_bits(0x7fc00000) + single_of_bits(0xff7fffff), 0x7fc00000, STR(__LINE__)); // nan + -0x1.fffffep+127 = nan
  comp32(single_of_bits(0xff7fffff) + single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -0x1.fffffep+127 + nan = nan
}

void f306(void) {
  comp32(single_of_bits(0x7f000000) + single_of_bits(0x7f000000), 0x7f800000, STR(__LINE__)); // 0x1p+127 + 0x1p+127 = inf
  comp32(single_of_bits(0xff000000) + single_of_bits(0xff000000), 0xff800000, STR(__LINE__)); // -0x1p+127 + -0x1p+127 = -inf
  comp32(single_of_bits(0x7f7ffffe) + single_of_bits(0x7f7ffffe), 0x7f800000, STR(__LINE__)); // 0x1.fffffcp+127 + 0x1.fffffcp+127 = inf
  comp32(single_of_bits(0xff7ffffe) + single_of_bits(0xff7ffffe), 0xff800000, STR(__LINE__)); // -0x1.fffffcp+127 + -0x1.fffffcp+127 = -inf
  comp32(single_of_bits(0x7f7ffffe) + single_of_bits(0x7f7fffff), 0x7f800000, STR(__LINE__)); // 0x1.fffffcp+127 + 0x1.fffffep+127 = inf
  comp32(single_of_bits(0x7f7fffff) + single_of_bits(0x7f7ffffe), 0x7f800000, STR(__LINE__)); // 0x1.fffffep+127 + 0x1.fffffcp+127 = inf
  comp32(single_of_bits(0xff7ffffe) + single_of_bits(0xff7fffff), 0xff800000, STR(__LINE__)); // -0x1.fffffcp+127 + -0x1.fffffep+127 = -inf
  comp32(single_of_bits(0xff7fffff) + single_of_bits(0xff7ffffe), 0xff800000, STR(__LINE__)); // -0x1.fffffep+127 + -0x1.fffffcp+127 = -inf
  comp32(single_of_bits(0x7f000001) + single_of_bits(0x7f000000), 0x7f800000, STR(__LINE__)); // 0x1.000002p+127 + 0x1p+127 = inf
  comp32(single_of_bits(0x7f000000) + single_of_bits(0x7f000001), 0x7f800000, STR(__LINE__)); // 0x1p+127 + 0x1.000002p+127 = inf
}

void f307(void) {
  comp32(single_of_bits(0xff000001) + single_of_bits(0xff000000), 0xff800000, STR(__LINE__)); // -0x1.000002p+127 + -0x1p+127 = -inf
  comp32(single_of_bits(0xff000000) + single_of_bits(0xff000001), 0xff800000, STR(__LINE__)); // -0x1p+127 + -0x1.000002p+127 = -inf
  comp32(single_of_bits(0x7f7fffff) + single_of_bits(0x74000000), 0x7f800000, STR(__LINE__)); // 0x1.fffffep+127 + 0x1p+105 = inf
  comp32(single_of_bits(0x74000000) + single_of_bits(0x7f7fffff), 0x7f800000, STR(__LINE__)); // 0x1p+105 + 0x1.fffffep+127 = inf
  comp32(single_of_bits(0xff7fffff) + single_of_bits(0xf4000000), 0xff800000, STR(__LINE__)); // -0x1.fffffep+127 + -0x1p+105 = -inf
  comp32(single_of_bits(0xf4000000) + single_of_bits(0xff7fffff), 0xff800000, STR(__LINE__)); // -0x1p+105 + -0x1.fffffep+127 = -inf
  comp32(single_of_bits(0x7f7fffff) + single_of_bits(0x3f800000), 0x7f7fffff, STR(__LINE__)); // 0x1.fffffep+127 + 0x1p+0 = 0x1.fffffep+127
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x7f7fffff), 0x7f7fffff, STR(__LINE__)); // 0x1p+0 + 0x1.fffffep+127 = 0x1.fffffep+127
  comp32(single_of_bits(0xff7fffff) + single_of_bits(0xbf800000), 0xff7fffff, STR(__LINE__)); // -0x1.fffffep+127 + -0x1p+0 = -0x1.fffffep+127
  comp32(single_of_bits(0xbf800000) + single_of_bits(0xff7fffff), 0xff7fffff, STR(__LINE__)); // -0x1p+0 + -0x1.fffffep+127 = -0x1.fffffep+127
}

void f308(void) {
  comp32(single_of_bits(0x00000001) + single_of_bits(0x7f7fffff), 0x7f7fffff, STR(__LINE__)); // 0x1p-149 + 0x1.fffffep+127 = 0x1.fffffep+127
  comp32(single_of_bits(0x7f7fffff) + single_of_bits(0x00000001), 0x7f7fffff, STR(__LINE__)); // 0x1.fffffep+127 + 0x1p-149 = 0x1.fffffep+127
  comp32(single_of_bits(0x80000001) + single_of_bits(0xff7fffff), 0xff7fffff, STR(__LINE__)); // -0x1p-149 + -0x1.fffffep+127 = -0x1.fffffep+127
  comp32(single_of_bits(0xff7fffff) + single_of_bits(0x80000001), 0xff7fffff, STR(__LINE__)); // -0x1.fffffep+127 + -0x1p-149 = -0x1.fffffep+127
  comp32(single_of_bits(0x7f7fffff) + single_of_bits(0x72800000), 0x7f7fffff, STR(__LINE__)); // 0x1.fffffep+127 + 0x1p+102 = 0x1.fffffep+127
  comp32(single_of_bits(0x72800000) + single_of_bits(0x7f7fffff), 0x7f7fffff, STR(__LINE__)); // 0x1p+102 + 0x1.fffffep+127 = 0x1.fffffep+127
  comp32(single_of_bits(0xff7fffff) + single_of_bits(0xf2800000), 0xff7fffff, STR(__LINE__)); // -0x1.fffffep+127 + -0x1p+102 = -0x1.fffffep+127
  comp32(single_of_bits(0xf2800000) + single_of_bits(0xff7fffff), 0xff7fffff, STR(__LINE__)); // -0x1p+102 + -0x1.fffffep+127 = -0x1.fffffep+127
  comp32(single_of_bits(0x7f7fffff) + single_of_bits(0x72800001), 0x7f7fffff, STR(__LINE__)); // 0x1.fffffep+127 + 0x1.000002p+102 = 0x1.fffffep+127
  comp32(single_of_bits(0x72800001) + single_of_bits(0x7f7fffff), 0x7f7fffff, STR(__LINE__)); // 0x1.000002p+102 + 0x1.fffffep+127 = 0x1.fffffep+127
}

void f309(void) {
  comp32(single_of_bits(0xff7fffff) + single_of_bits(0xf2800001), 0xff7fffff, STR(__LINE__)); // -0x1.fffffep+127 + -0x1.000002p+102 = -0x1.fffffep+127
  comp32(single_of_bits(0xf2800001) + single_of_bits(0xff7fffff), 0xff7fffff, STR(__LINE__)); // -0x1.000002p+102 + -0x1.fffffep+127 = -0x1.fffffep+127
  comp32(single_of_bits(0x7effffff) + single_of_bits(0x7f000000), 0x7f800000, STR(__LINE__)); // 0x1.fffffep+126 + 0x1p+127 = inf
  comp32(single_of_bits(0x7f000000) + single_of_bits(0x7effffff), 0x7f800000, STR(__LINE__)); // 0x1p+127 + 0x1.fffffep+126 = inf
  comp32(single_of_bits(0xfeffffff) + single_of_bits(0xff000000), 0xff800000, STR(__LINE__)); // -0x1.fffffep+126 + -0x1p+127 = -inf
  comp32(single_of_bits(0xff000000) + single_of_bits(0xfeffffff), 0xff800000, STR(__LINE__)); // -0x1p+127 + -0x1.fffffep+126 = -inf
  comp32(single_of_bits(0x7f7fffff) + single_of_bits(0x73400000), 0x7f800000, STR(__LINE__)); // 0x1.fffffep+127 + 0x1.8p+103 = inf
  comp32(single_of_bits(0x73400000) + single_of_bits(0x7f7fffff), 0x7f800000, STR(__LINE__)); // 0x1.8p+103 + 0x1.fffffep+127 = inf
  comp32(single_of_bits(0xff7fffff) + single_of_bits(0xf3400000), 0xff800000, STR(__LINE__)); // -0x1.fffffep+127 + -0x1.8p+103 = -inf
  comp32(single_of_bits(0xf3400000) + single_of_bits(0xff7fffff), 0xff800000, STR(__LINE__)); // -0x1.8p+103 + -0x1.fffffep+127 = -inf
}

void f310(void) {
  comp32(single_of_bits(0x7f7fffff) + single_of_bits(0x73000001), 0x7f800000, STR(__LINE__)); // 0x1.fffffep+127 + 0x1.000002p+103 = inf
  comp32(single_of_bits(0x73000001) + single_of_bits(0x7f7fffff), 0x7f800000, STR(__LINE__)); // 0x1.000002p+103 + 0x1.fffffep+127 = inf
  comp32(single_of_bits(0xff7fffff) + single_of_bits(0xf3000001), 0xff800000, STR(__LINE__)); // -0x1.fffffep+127 + -0x1.000002p+103 = -inf
  comp32(single_of_bits(0xf3000001) + single_of_bits(0xff7fffff), 0xff800000, STR(__LINE__)); // -0x1.000002p+103 + -0x1.fffffep+127 = -inf
  comp32(single_of_bits(0x7f7fffff) + single_of_bits(0x73400001), 0x7f800000, STR(__LINE__)); // 0x1.fffffep+127 + 0x1.800002p+103 = inf
  comp32(single_of_bits(0x73400001) + single_of_bits(0x7f7fffff), 0x7f800000, STR(__LINE__)); // 0x1.800002p+103 + 0x1.fffffep+127 = inf
  comp32(single_of_bits(0xff7fffff) + single_of_bits(0xf3400001), 0xff800000, STR(__LINE__)); // -0x1.fffffep+127 + -0x1.800002p+103 = -inf
  comp32(single_of_bits(0xf3400001) + single_of_bits(0xff7fffff), 0xff800000, STR(__LINE__)); // -0x1.800002p+103 + -0x1.fffffep+127 = -inf
  comp32(single_of_bits(0x7f000000) + single_of_bits(0x3f800000), 0x7f000000, STR(__LINE__)); // 0x1p+127 + 0x1p+0 = 0x1p+127
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x7f000000), 0x7f000000, STR(__LINE__)); // 0x1p+0 + 0x1p+127 = 0x1p+127
}

void f311(void) {
  comp32(single_of_bits(0xff000000) + single_of_bits(0xbf800000), 0xff000000, STR(__LINE__)); // -0x1p+127 + -0x1p+0 = -0x1p+127
  comp32(single_of_bits(0xbf800000) + single_of_bits(0xff000000), 0xff000000, STR(__LINE__)); // -0x1p+0 + -0x1p+127 = -0x1p+127
  comp32(single_of_bits(0x7effffff) + single_of_bits(0x3f800000), 0x7effffff, STR(__LINE__)); // 0x1.fffffep+126 + 0x1p+0 = 0x1.fffffep+126
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x7effffff), 0x7effffff, STR(__LINE__)); // 0x1p+0 + 0x1.fffffep+126 = 0x1.fffffep+126
  comp32(single_of_bits(0x7f7ffffe) + single_of_bits(0x3f800000), 0x7f7ffffe, STR(__LINE__)); // 0x1.fffffcp+127 + 0x1p+0 = 0x1.fffffcp+127
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x7f7ffffe), 0x7f7ffffe, STR(__LINE__)); // 0x1p+0 + 0x1.fffffcp+127 = 0x1.fffffcp+127
  comp32(single_of_bits(0xff7ffffe) + single_of_bits(0xbf800000), 0xff7ffffe, STR(__LINE__)); // -0x1.fffffcp+127 + -0x1p+0 = -0x1.fffffcp+127
  comp32(single_of_bits(0xbf800000) + single_of_bits(0xff7ffffe), 0xff7ffffe, STR(__LINE__)); // -0x1p+0 + -0x1.fffffcp+127 = -0x1.fffffcp+127
  comp32(single_of_bits(0x00000001) + single_of_bits(0x7f000000), 0x7f000000, STR(__LINE__)); // 0x1p-149 + 0x1p+127 = 0x1p+127
  comp32(single_of_bits(0x7f000000) + single_of_bits(0x00000001), 0x7f000000, STR(__LINE__)); // 0x1p+127 + 0x1p-149 = 0x1p+127
}

void f312(void) {
  comp32(single_of_bits(0x80000001) + single_of_bits(0xff000000), 0xff000000, STR(__LINE__)); // -0x1p-149 + -0x1p+127 = -0x1p+127
  comp32(single_of_bits(0xff000000) + single_of_bits(0x80000001), 0xff000000, STR(__LINE__)); // -0x1p+127 + -0x1p-149 = -0x1p+127
  comp32(single_of_bits(0x00000001) + single_of_bits(0x7effffff), 0x7effffff, STR(__LINE__)); // 0x1p-149 + 0x1.fffffep+126 = 0x1.fffffep+126
  comp32(single_of_bits(0x7effffff) + single_of_bits(0x00000001), 0x7effffff, STR(__LINE__)); // 0x1.fffffep+126 + 0x1p-149 = 0x1.fffffep+126
  comp32(single_of_bits(0x80000001) + single_of_bits(0xfeffffff), 0xfeffffff, STR(__LINE__)); // -0x1p-149 + -0x1.fffffep+126 = -0x1.fffffep+126
  comp32(single_of_bits(0xfeffffff) + single_of_bits(0x80000001), 0xfeffffff, STR(__LINE__)); // -0x1.fffffep+126 + -0x1p-149 = -0x1.fffffep+126
  comp32(single_of_bits(0x00000001) + single_of_bits(0x7f7ffffe), 0x7f7ffffe, STR(__LINE__)); // 0x1p-149 + 0x1.fffffcp+127 = 0x1.fffffcp+127
  comp32(single_of_bits(0x7f7ffffe) + single_of_bits(0x00000001), 0x7f7ffffe, STR(__LINE__)); // 0x1.fffffcp+127 + 0x1p-149 = 0x1.fffffcp+127
  comp32(single_of_bits(0x80000001) + single_of_bits(0xff7ffffe), 0xff7ffffe, STR(__LINE__)); // -0x1p-149 + -0x1.fffffcp+127 = -0x1.fffffcp+127
  comp32(single_of_bits(0xff7ffffe) + single_of_bits(0x80000001), 0xff7ffffe, STR(__LINE__)); // -0x1.fffffcp+127 + -0x1p-149 = -0x1.fffffcp+127
}

void f313(void) {
  comp32(single_of_bits(0x7f000000) + single_of_bits(0x73800000), 0x7f000001, STR(__LINE__)); // 0x1p+127 + 0x1p+104 = 0x1.000002p+127
  comp32(single_of_bits(0x73800000) + single_of_bits(0x7f000000), 0x7f000001, STR(__LINE__)); // 0x1p+104 + 0x1p+127 = 0x1.000002p+127
  comp32(single_of_bits(0xff000000) + single_of_bits(0xf3800000), 0xff000001, STR(__LINE__)); // -0x1p+127 + -0x1p+104 = -0x1.000002p+127
  comp32(single_of_bits(0xf3800000) + single_of_bits(0xff000000), 0xff000001, STR(__LINE__)); // -0x1p+104 + -0x1p+127 = -0x1.000002p+127
  comp32(single_of_bits(0x7efffffe) + single_of_bits(0x7efffffe), 0x7f7ffffe, STR(__LINE__)); // 0x1.fffffcp+126 + 0x1.fffffcp+126 = 0x1.fffffcp+127
  comp32(single_of_bits(0xfefffffe) + single_of_bits(0xfefffffe), 0xff7ffffe, STR(__LINE__)); // -0x1.fffffcp+126 + -0x1.fffffcp+126 = -0x1.fffffcp+127
  comp32(single_of_bits(0x40400000) + single_of_bits(0x40400000), 0x40c00000, STR(__LINE__)); // 0x1.8p+1 + 0x1.8p+1 = 0x1.8p+2
  comp32(single_of_bits(0x00800000) + single_of_bits(0x00800000), 0x01000000, STR(__LINE__)); // 0x1p-126 + 0x1p-126 = 0x1p-125
  comp32(single_of_bits(0x7e800000) + single_of_bits(0x7e800000), 0x7f000000, STR(__LINE__)); // 0x1p+126 + 0x1p+126 = 0x1p+127
  comp32(single_of_bits(0x007fffff) + single_of_bits(0x007fffff), 0x00fffffe, STR(__LINE__)); // 0x1.fffffcp-127 + 0x1.fffffcp-127 = 0x1.fffffcp-126
}

void f314(void) {
  comp32(single_of_bits(0x807fffff) + single_of_bits(0x807fffff), 0x80fffffe, STR(__LINE__)); // -0x1.fffffcp-127 + -0x1.fffffcp-127 = -0x1.fffffcp-126
  comp32(single_of_bits(0x00000004) + single_of_bits(0x00000004), 0x00000008, STR(__LINE__)); // 0x1p-147 + 0x1p-147 = 0x1p-146
  comp32(single_of_bits(0x80000004) + single_of_bits(0x80000004), 0x80000008, STR(__LINE__)); // -0x1p-147 + -0x1p-147 = -0x1p-146
  comp32(single_of_bits(0x00000001) + single_of_bits(0x00000001), 0x00000002, STR(__LINE__)); // 0x1p-149 + 0x1p-149 = 0x1p-148
  comp32(single_of_bits(0x80000001) + single_of_bits(0x80000001), 0x80000002, STR(__LINE__)); // -0x1p-149 + -0x1p-149 = -0x1p-148
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x41000000), 0x41100000, STR(__LINE__)); // 0x1.000002p+0 + 0x1p+3 = 0x1.2p+3
  comp32(single_of_bits(0x41000000) + single_of_bits(0x3f800001), 0x41100000, STR(__LINE__)); // 0x1p+3 + 0x1.000002p+0 = 0x1.2p+3
  comp32(single_of_bits(0xbf800001) + single_of_bits(0xc1000000), 0xc1100000, STR(__LINE__)); // -0x1.000002p+0 + -0x1p+3 = -0x1.2p+3
  comp32(single_of_bits(0xc1000000) + single_of_bits(0xbf800001), 0xc1100000, STR(__LINE__)); // -0x1p+3 + -0x1.000002p+0 = -0x1.2p+3
  comp32(single_of_bits(0x4c800000) + single_of_bits(0x3f800000), 0x4c800000, STR(__LINE__)); // 0x1p+26 + 0x1p+0 = 0x1p+26
}

void f315(void) {
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x4c800000), 0x4c800000, STR(__LINE__)); // 0x1p+0 + 0x1p+26 = 0x1p+26
  comp32(single_of_bits(0xcc800000) + single_of_bits(0xbf800000), 0xcc800000, STR(__LINE__)); // -0x1p+26 + -0x1p+0 = -0x1p+26
  comp32(single_of_bits(0xbf800000) + single_of_bits(0xcc800000), 0xcc800000, STR(__LINE__)); // -0x1p+0 + -0x1p+26 = -0x1p+26
  comp32(single_of_bits(0x02000000) + single_of_bits(0x00000001), 0x02000000, STR(__LINE__)); // 0x1p-123 + 0x1p-149 = 0x1p-123
  comp32(single_of_bits(0x00000001) + single_of_bits(0x02000000), 0x02000000, STR(__LINE__)); // 0x1p-149 + 0x1p-123 = 0x1p-123
  comp32(single_of_bits(0x82000000) + single_of_bits(0x80000001), 0x82000000, STR(__LINE__)); // -0x1p-123 + -0x1p-149 = -0x1p-123
  comp32(single_of_bits(0x80000001) + single_of_bits(0x82000000), 0x82000000, STR(__LINE__)); // -0x1p-149 + -0x1p-123 = -0x1p-123
  comp32(single_of_bits(0x00000001) + single_of_bits(0x3f800000), 0x3f800000, STR(__LINE__)); // 0x1p-149 + 0x1p+0 = 0x1p+0
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x00000001), 0x3f800000, STR(__LINE__)); // 0x1p+0 + 0x1p-149 = 0x1p+0
  comp32(single_of_bits(0x80000001) + single_of_bits(0xbf800000), 0xbf800000, STR(__LINE__)); // -0x1p-149 + -0x1p+0 = -0x1p+0
}

void f316(void) {
  comp32(single_of_bits(0xbf800000) + single_of_bits(0x80000001), 0xbf800000, STR(__LINE__)); // -0x1p+0 + -0x1p-149 = -0x1p+0
  comp32(single_of_bits(0x00000001) + single_of_bits(0x3f7fffff), 0x3f7fffff, STR(__LINE__)); // 0x1p-149 + 0x1.fffffep-1 = 0x1.fffffep-1
  comp32(single_of_bits(0x3f7fffff) + single_of_bits(0x00000001), 0x3f7fffff, STR(__LINE__)); // 0x1.fffffep-1 + 0x1p-149 = 0x1.fffffep-1
  comp32(single_of_bits(0x80000001) + single_of_bits(0xbf7fffff), 0xbf7fffff, STR(__LINE__)); // -0x1p-149 + -0x1.fffffep-1 = -0x1.fffffep-1
  comp32(single_of_bits(0xbf7fffff) + single_of_bits(0x80000001), 0xbf7fffff, STR(__LINE__)); // -0x1.fffffep-1 + -0x1p-149 = -0x1.fffffep-1
  comp32(single_of_bits(0x00000001) + single_of_bits(0x3fffffff), 0x3fffffff, STR(__LINE__)); // 0x1p-149 + 0x1.fffffep+0 = 0x1.fffffep+0
  comp32(single_of_bits(0x3fffffff) + single_of_bits(0x00000001), 0x3fffffff, STR(__LINE__)); // 0x1.fffffep+0 + 0x1p-149 = 0x1.fffffep+0
  comp32(single_of_bits(0x80000001) + single_of_bits(0xbfffffff), 0xbfffffff, STR(__LINE__)); // -0x1p-149 + -0x1.fffffep+0 = -0x1.fffffep+0
  comp32(single_of_bits(0xbfffffff) + single_of_bits(0x80000001), 0xbfffffff, STR(__LINE__)); // -0x1.fffffep+0 + -0x1p-149 = -0x1.fffffep+0
  comp32(single_of_bits(0x00000001) + single_of_bits(0x3ffffffe), 0x3ffffffe, STR(__LINE__)); // 0x1p-149 + 0x1.fffffcp+0 = 0x1.fffffcp+0
}

void f317(void) {
  comp32(single_of_bits(0x3ffffffe) + single_of_bits(0x00000001), 0x3ffffffe, STR(__LINE__)); // 0x1.fffffcp+0 + 0x1p-149 = 0x1.fffffcp+0
  comp32(single_of_bits(0x80000001) + single_of_bits(0xbffffffe), 0xbffffffe, STR(__LINE__)); // -0x1p-149 + -0x1.fffffcp+0 = -0x1.fffffcp+0
  comp32(single_of_bits(0xbffffffe) + single_of_bits(0x80000001), 0xbffffffe, STR(__LINE__)); // -0x1.fffffcp+0 + -0x1p-149 = -0x1.fffffcp+0
  comp32(single_of_bits(0x4cffffff) + single_of_bits(0x41300000), 0x4d000000, STR(__LINE__)); // 0x1.fffffep+26 + 0x1.6p+3 = 0x1p+27
  comp32(single_of_bits(0x41300000) + single_of_bits(0x4cffffff), 0x4d000000, STR(__LINE__)); // 0x1.6p+3 + 0x1.fffffep+26 = 0x1p+27
  comp32(single_of_bits(0xccffffff) + single_of_bits(0xc1300000), 0xcd000000, STR(__LINE__)); // -0x1.fffffep+26 + -0x1.6p+3 = -0x1p+27
  comp32(single_of_bits(0xc1300000) + single_of_bits(0xccffffff), 0xcd000000, STR(__LINE__)); // -0x1.6p+3 + -0x1.fffffep+26 = -0x1p+27
  comp32(single_of_bits(0x4ce00000) + single_of_bits(0xc0e00000), 0x4cdfffff, STR(__LINE__)); // 0x1.cp+26 + -0x1.cp+2 = 0x1.bffffep+26
  comp32(single_of_bits(0xc0e00000) + single_of_bits(0x4ce00000), 0x4cdfffff, STR(__LINE__)); // -0x1.cp+2 + 0x1.cp+26 = 0x1.bffffep+26
  comp32(single_of_bits(0x40e00000) + single_of_bits(0xcce00000), 0xccdfffff, STR(__LINE__)); // 0x1.cp+2 + -0x1.cp+26 = -0x1.bffffep+26
}

void f318(void) {
  comp32(single_of_bits(0xcce00000) + single_of_bits(0x40e00000), 0xccdfffff, STR(__LINE__)); // -0x1.cp+26 + 0x1.cp+2 = -0x1.bffffep+26
  comp32(single_of_bits(0x02800000) + single_of_bits(0x80000007), 0x027fffff, STR(__LINE__)); // 0x1p-122 + -0x1.cp-147 = 0x1.fffffep-123
  comp32(single_of_bits(0x80000007) + single_of_bits(0x02800000), 0x027fffff, STR(__LINE__)); // -0x1.cp-147 + 0x1p-122 = 0x1.fffffep-123
  comp32(single_of_bits(0x82800000) + single_of_bits(0x00000007), 0x827fffff, STR(__LINE__)); // -0x1p-122 + 0x1.cp-147 = -0x1.fffffep-123
  comp32(single_of_bits(0x00000007) + single_of_bits(0x82800000), 0x827fffff, STR(__LINE__)); // 0x1.cp-147 + -0x1p-122 = -0x1.fffffep-123
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x40800000), 0x40a00000, STR(__LINE__)); // 0x1.000002p+0 + 0x1p+2 = 0x1.4p+2
  comp32(single_of_bits(0x40800000) + single_of_bits(0x3f800001), 0x40a00000, STR(__LINE__)); // 0x1p+2 + 0x1.000002p+0 = 0x1.4p+2
  comp32(single_of_bits(0xbf800001) + single_of_bits(0xc0800000), 0xc0a00000, STR(__LINE__)); // -0x1.000002p+0 + -0x1p+2 = -0x1.4p+2
  comp32(single_of_bits(0xc0800000) + single_of_bits(0xbf800001), 0xc0a00000, STR(__LINE__)); // -0x1p+2 + -0x1.000002p+0 = -0x1.4p+2
  comp32(single_of_bits(0x4c000000) + single_of_bits(0x3f800000), 0x4c000000, STR(__LINE__)); // 0x1p+25 + 0x1p+0 = 0x1p+25
}

void f319(void) {
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x4c000000), 0x4c000000, STR(__LINE__)); // 0x1p+0 + 0x1p+25 = 0x1p+25
  comp32(single_of_bits(0xcc000000) + single_of_bits(0xbf800000), 0xcc000000, STR(__LINE__)); // -0x1p+25 + -0x1p+0 = -0x1p+25
  comp32(single_of_bits(0xbf800000) + single_of_bits(0xcc000000), 0xcc000000, STR(__LINE__)); // -0x1p+0 + -0x1p+25 = -0x1p+25
  comp32(single_of_bits(0x41200000) + single_of_bits(0x4cffffff), 0x4d000000, STR(__LINE__)); // 0x1.4p+3 + 0x1.fffffep+26 = 0x1p+27
  comp32(single_of_bits(0x4cffffff) + single_of_bits(0x41200000), 0x4d000000, STR(__LINE__)); // 0x1.fffffep+26 + 0x1.4p+3 = 0x1p+27
  comp32(single_of_bits(0xc1200000) + single_of_bits(0xccffffff), 0xcd000000, STR(__LINE__)); // -0x1.4p+3 + -0x1.fffffep+26 = -0x1p+27
  comp32(single_of_bits(0xccffffff) + single_of_bits(0xc1200000), 0xcd000000, STR(__LINE__)); // -0x1.fffffep+26 + -0x1.4p+3 = -0x1p+27
  comp32(single_of_bits(0x40800000) + single_of_bits(0xb4400000), 0x407fffff, STR(__LINE__)); // 0x1p+2 + -0x1.8p-23 = 0x1.fffffep+1
  comp32(single_of_bits(0xb4400000) + single_of_bits(0x40800000), 0x407fffff, STR(__LINE__)); // -0x1.8p-23 + 0x1p+2 = 0x1.fffffep+1
  comp32(single_of_bits(0x40400000) + single_of_bits(0xcc800000), 0xcc7fffff, STR(__LINE__)); // 0x1.8p+1 + -0x1p+26 = -0x1.fffffep+25
}

void f320(void) {
  comp32(single_of_bits(0xcc800000) + single_of_bits(0x40400000), 0xcc7fffff, STR(__LINE__)); // -0x1p+26 + 0x1.8p+1 = -0x1.fffffep+25
  comp32(single_of_bits(0xc0800000) + single_of_bits(0x34400000), 0xc07fffff, STR(__LINE__)); // -0x1p+2 + 0x1.8p-23 = -0x1.fffffep+1
  comp32(single_of_bits(0x34400000) + single_of_bits(0xc0800000), 0xc07fffff, STR(__LINE__)); // 0x1.8p-23 + -0x1p+2 = -0x1.fffffep+1
  comp32(single_of_bits(0xc0400000) + single_of_bits(0x4c800000), 0x4c7fffff, STR(__LINE__)); // -0x1.8p+1 + 0x1p+26 = 0x1.fffffep+25
  comp32(single_of_bits(0x4c800000) + single_of_bits(0xc0400000), 0x4c7fffff, STR(__LINE__)); // 0x1p+26 + -0x1.8p+1 = 0x1.fffffep+25
  comp32(single_of_bits(0x02000000) + single_of_bits(0x80000003), 0x01ffffff, STR(__LINE__)); // 0x1p-123 + -0x1.8p-148 = 0x1.fffffep-124
  comp32(single_of_bits(0x80000003) + single_of_bits(0x02000000), 0x01ffffff, STR(__LINE__)); // -0x1.8p-148 + 0x1p-123 = 0x1.fffffep-124
  comp32(single_of_bits(0x82000000) + single_of_bits(0x00000003), 0x81ffffff, STR(__LINE__)); // -0x1p-123 + 0x1.8p-148 = -0x1.fffffep-124
  comp32(single_of_bits(0x00000003) + single_of_bits(0x82000000), 0x81ffffff, STR(__LINE__)); // 0x1.8p-148 + -0x1p-123 = -0x1.fffffep-124
  comp32(single_of_bits(0x3f800003) + single_of_bits(0x41000000), 0x41100000, STR(__LINE__)); // 0x1.000006p+0 + 0x1p+3 = 0x1.2p+3
}

void f321(void) {
  comp32(single_of_bits(0x41000000) + single_of_bits(0x3f800003), 0x41100000, STR(__LINE__)); // 0x1p+3 + 0x1.000006p+0 = 0x1.2p+3
  comp32(single_of_bits(0xbf800003) + single_of_bits(0xc1000000), 0xc1100000, STR(__LINE__)); // -0x1.000006p+0 + -0x1p+3 = -0x1.2p+3
  comp32(single_of_bits(0xc1000000) + single_of_bits(0xbf800003), 0xc1100000, STR(__LINE__)); // -0x1p+3 + -0x1.000006p+0 = -0x1.2p+3
  comp32(single_of_bits(0x407fffff) + single_of_bits(0x33ffffff), 0x407fffff, STR(__LINE__)); // 0x1.fffffep+1 + 0x1.fffffep-24 = 0x1.fffffep+1
  comp32(single_of_bits(0x33ffffff) + single_of_bits(0x407fffff), 0x407fffff, STR(__LINE__)); // 0x1.fffffep-24 + 0x1.fffffep+1 = 0x1.fffffep+1
  comp32(single_of_bits(0xc07fffff) + single_of_bits(0xb3ffffff), 0xc07fffff, STR(__LINE__)); // -0x1.fffffep+1 + -0x1.fffffep-24 = -0x1.fffffep+1
  comp32(single_of_bits(0xb3ffffff) + single_of_bits(0xc07fffff), 0xc07fffff, STR(__LINE__)); // -0x1.fffffep-24 + -0x1.fffffep+1 = -0x1.fffffep+1
  comp32(single_of_bits(0x02000000) + single_of_bits(0x00000003), 0x02000000, STR(__LINE__)); // 0x1p-123 + 0x1.8p-148 = 0x1p-123
  comp32(single_of_bits(0x00000003) + single_of_bits(0x02000000), 0x02000000, STR(__LINE__)); // 0x1.8p-148 + 0x1p-123 = 0x1p-123
  comp32(single_of_bits(0x80000003) + single_of_bits(0x82000000), 0x82000000, STR(__LINE__)); // -0x1.8p-148 + -0x1p-123 = -0x1p-123
}

void f322(void) {
  comp32(single_of_bits(0x82000000) + single_of_bits(0x80000003), 0x82000000, STR(__LINE__)); // -0x1p-123 + -0x1.8p-148 = -0x1p-123
  comp32(single_of_bits(0x41600000) + single_of_bits(0x4cffffff), 0x4d000000, STR(__LINE__)); // 0x1.cp+3 + 0x1.fffffep+26 = 0x1p+27
  comp32(single_of_bits(0x4cffffff) + single_of_bits(0x41600000), 0x4d000000, STR(__LINE__)); // 0x1.fffffep+26 + 0x1.cp+3 = 0x1p+27
  comp32(single_of_bits(0xc1600000) + single_of_bits(0xccffffff), 0xcd000000, STR(__LINE__)); // -0x1.cp+3 + -0x1.fffffep+26 = -0x1p+27
  comp32(single_of_bits(0xccffffff) + single_of_bits(0xc1600000), 0xcd000000, STR(__LINE__)); // -0x1.fffffep+26 + -0x1.cp+3 = -0x1p+27
  comp32(single_of_bits(0x41000000) + single_of_bits(0xb4a00000), 0x40ffffff, STR(__LINE__)); // 0x1p+3 + -0x1.4p-22 = 0x1.fffffep+2
  comp32(single_of_bits(0xb4a00000) + single_of_bits(0x41000000), 0x40ffffff, STR(__LINE__)); // -0x1.4p-22 + 0x1p+3 = 0x1.fffffep+2
  comp32(single_of_bits(0x40a00000) + single_of_bits(0xcd000000), 0xccffffff, STR(__LINE__)); // 0x1.4p+2 + -0x1p+27 = -0x1.fffffep+26
  comp32(single_of_bits(0xcd000000) + single_of_bits(0x40a00000), 0xccffffff, STR(__LINE__)); // -0x1p+27 + 0x1.4p+2 = -0x1.fffffep+26
  comp32(single_of_bits(0xc1000000) + single_of_bits(0x34a00000), 0xc0ffffff, STR(__LINE__)); // -0x1p+3 + 0x1.4p-22 = -0x1.fffffep+2
}

void f323(void) {
  comp32(single_of_bits(0x34a00000) + single_of_bits(0xc1000000), 0xc0ffffff, STR(__LINE__)); // 0x1.4p-22 + -0x1p+3 = -0x1.fffffep+2
  comp32(single_of_bits(0xc0a00000) + single_of_bits(0x4d000000), 0x4cffffff, STR(__LINE__)); // -0x1.4p+2 + 0x1p+27 = 0x1.fffffep+26
  comp32(single_of_bits(0x4d000000) + single_of_bits(0xc0a00000), 0x4cffffff, STR(__LINE__)); // 0x1p+27 + -0x1.4p+2 = 0x1.fffffep+26
  comp32(single_of_bits(0x02800000) + single_of_bits(0x80000005), 0x027fffff, STR(__LINE__)); // 0x1p-122 + -0x1.4p-147 = 0x1.fffffep-123
  comp32(single_of_bits(0x80000005) + single_of_bits(0x02800000), 0x027fffff, STR(__LINE__)); // -0x1.4p-147 + 0x1p-122 = 0x1.fffffep-123
  comp32(single_of_bits(0x82800000) + single_of_bits(0x00000005), 0x827fffff, STR(__LINE__)); // -0x1p-122 + 0x1.4p-147 = -0x1.fffffep-123
  comp32(single_of_bits(0x00000005) + single_of_bits(0x82800000), 0x827fffff, STR(__LINE__)); // 0x1.4p-147 + -0x1p-122 = -0x1.fffffep-123
  comp32(single_of_bits(0x34000000) + single_of_bits(0x40000000), 0x40000000, STR(__LINE__)); // 0x1p-23 + 0x1p+1 = 0x1p+1
  comp32(single_of_bits(0x40000000) + single_of_bits(0x34000000), 0x40000000, STR(__LINE__)); // 0x1p+1 + 0x1p-23 = 0x1p+1
  comp32(single_of_bits(0xb4000000) + single_of_bits(0xc0000000), 0xc0000000, STR(__LINE__)); // -0x1p-23 + -0x1p+1 = -0x1p+1
}

void f324(void) {
  comp32(single_of_bits(0xc0000000) + single_of_bits(0xb4000000), 0xc0000000, STR(__LINE__)); // -0x1p+1 + -0x1p-23 = -0x1p+1
  comp32(single_of_bits(0x00000001) + single_of_bits(0x01000000), 0x01000000, STR(__LINE__)); // 0x1p-149 + 0x1p-125 = 0x1p-125
  comp32(single_of_bits(0x01000000) + single_of_bits(0x00000001), 0x01000000, STR(__LINE__)); // 0x1p-125 + 0x1p-149 = 0x1p-125
  comp32(single_of_bits(0x80000001) + single_of_bits(0x81000000), 0x81000000, STR(__LINE__)); // -0x1p-149 + -0x1p-125 = -0x1p-125
  comp32(single_of_bits(0x81000000) + single_of_bits(0x80000001), 0x81000000, STR(__LINE__)); // -0x1p-125 + -0x1p-149 = -0x1p-125
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x3f800000), 0x40000000, STR(__LINE__)); // 0x1.000002p+0 + 0x1p+0 = 0x1p+1
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x3f800001), 0x40000000, STR(__LINE__)); // 0x1p+0 + 0x1.000002p+0 = 0x1p+1
  comp32(single_of_bits(0xbf800001) + single_of_bits(0xbf800000), 0xc0000000, STR(__LINE__)); // -0x1.000002p+0 + -0x1p+0 = -0x1p+1
  comp32(single_of_bits(0xbf800000) + single_of_bits(0xbf800001), 0xc0000000, STR(__LINE__)); // -0x1p+0 + -0x1.000002p+0 = -0x1p+1
  comp32(single_of_bits(0x7e800001) + single_of_bits(0x7e800000), 0x7f000000, STR(__LINE__)); // 0x1.000002p+126 + 0x1p+126 = 0x1p+127
}

void f325(void) {
  comp32(single_of_bits(0x7e800000) + single_of_bits(0x7e800001), 0x7f000000, STR(__LINE__)); // 0x1p+126 + 0x1.000002p+126 = 0x1p+127
  comp32(single_of_bits(0x40000000) + single_of_bits(0x40000001), 0x40800000, STR(__LINE__)); // 0x1p+1 + 0x1.000002p+1 = 0x1p+2
  comp32(single_of_bits(0x40000001) + single_of_bits(0x40000000), 0x40800000, STR(__LINE__)); // 0x1.000002p+1 + 0x1p+1 = 0x1p+2
  comp32(single_of_bits(0x7efffffe) + single_of_bits(0x7effffff), 0x7f7ffffe, STR(__LINE__)); // 0x1.fffffcp+126 + 0x1.fffffep+126 = 0x1.fffffcp+127
  comp32(single_of_bits(0x7effffff) + single_of_bits(0x7efffffe), 0x7f7ffffe, STR(__LINE__)); // 0x1.fffffep+126 + 0x1.fffffcp+126 = 0x1.fffffcp+127
  comp32(single_of_bits(0xfe800001) + single_of_bits(0xfe800000), 0xff000000, STR(__LINE__)); // -0x1.000002p+126 + -0x1p+126 = -0x1p+127
  comp32(single_of_bits(0xfe800000) + single_of_bits(0xfe800001), 0xff000000, STR(__LINE__)); // -0x1p+126 + -0x1.000002p+126 = -0x1p+127
  comp32(single_of_bits(0xc0000000) + single_of_bits(0xc0000001), 0xc0800000, STR(__LINE__)); // -0x1p+1 + -0x1.000002p+1 = -0x1p+2
  comp32(single_of_bits(0xc0000001) + single_of_bits(0xc0000000), 0xc0800000, STR(__LINE__)); // -0x1.000002p+1 + -0x1p+1 = -0x1p+2
  comp32(single_of_bits(0xfefffffe) + single_of_bits(0xfeffffff), 0xff7ffffe, STR(__LINE__)); // -0x1.fffffcp+126 + -0x1.fffffep+126 = -0x1.fffffcp+127
}

void f326(void) {
  comp32(single_of_bits(0xfeffffff) + single_of_bits(0xfefffffe), 0xff7ffffe, STR(__LINE__)); // -0x1.fffffep+126 + -0x1.fffffcp+126 = -0x1.fffffcp+127
  comp32(single_of_bits(0x3f800001) + single_of_bits(0xb3800000), 0x3f800000, STR(__LINE__)); // 0x1.000002p+0 + -0x1p-24 = 0x1p+0
  comp32(single_of_bits(0xb3800000) + single_of_bits(0x3f800001), 0x3f800000, STR(__LINE__)); // -0x1p-24 + 0x1.000002p+0 = 0x1p+0
  comp32(single_of_bits(0x33800000) + single_of_bits(0xbf800001), 0xbf800000, STR(__LINE__)); // 0x1p-24 + -0x1.000002p+0 = -0x1p+0
  comp32(single_of_bits(0xbf800001) + single_of_bits(0x33800000), 0xbf800000, STR(__LINE__)); // -0x1.000002p+0 + 0x1p-24 = -0x1p+0
  comp32(single_of_bits(0x01000001) + single_of_bits(0x80000001), 0x01000000, STR(__LINE__)); // 0x1.000002p-125 + -0x1p-149 = 0x1p-125
  comp32(single_of_bits(0x80000001) + single_of_bits(0x01000001), 0x01000000, STR(__LINE__)); // -0x1p-149 + 0x1.000002p-125 = 0x1p-125
  comp32(single_of_bits(0x81000001) + single_of_bits(0x00000001), 0x81000000, STR(__LINE__)); // -0x1.000002p-125 + 0x1p-149 = -0x1p-125
  comp32(single_of_bits(0x00000001) + single_of_bits(0x81000001), 0x81000000, STR(__LINE__)); // 0x1p-149 + -0x1.000002p-125 = -0x1p-125
  comp32(single_of_bits(0x34000000) + single_of_bits(0x407fffff), 0x40800000, STR(__LINE__)); // 0x1p-23 + 0x1.fffffep+1 = 0x1p+2
}

void f327(void) {
  comp32(single_of_bits(0x407fffff) + single_of_bits(0x34000000), 0x40800000, STR(__LINE__)); // 0x1.fffffep+1 + 0x1p-23 = 0x1p+2
  comp32(single_of_bits(0xb4000000) + single_of_bits(0xc07fffff), 0xc0800000, STR(__LINE__)); // -0x1p-23 + -0x1.fffffep+1 = -0x1p+2
  comp32(single_of_bits(0xc07fffff) + single_of_bits(0xb4000000), 0xc0800000, STR(__LINE__)); // -0x1.fffffep+1 + -0x1p-23 = -0x1p+2
  comp32(single_of_bits(0x00000001) + single_of_bits(0x01000001), 0x01000002, STR(__LINE__)); // 0x1p-149 + 0x1.000002p-125 = 0x1.000004p-125
  comp32(single_of_bits(0x01000001) + single_of_bits(0x00000001), 0x01000002, STR(__LINE__)); // 0x1.000002p-125 + 0x1p-149 = 0x1.000004p-125
  comp32(single_of_bits(0x80000001) + single_of_bits(0x81000001), 0x81000002, STR(__LINE__)); // -0x1p-149 + -0x1.000002p-125 = -0x1.000004p-125
  comp32(single_of_bits(0x81000001) + single_of_bits(0x80000001), 0x81000002, STR(__LINE__)); // -0x1.000002p-125 + -0x1p-149 = -0x1.000004p-125
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x3f800003), 0x40000002, STR(__LINE__)); // 0x1p+0 + 0x1.000006p+0 = 0x1.000004p+1
  comp32(single_of_bits(0x3f800003) + single_of_bits(0x3f800000), 0x40000002, STR(__LINE__)); // 0x1.000006p+0 + 0x1p+0 = 0x1.000004p+1
  comp32(single_of_bits(0x40000001) + single_of_bits(0x40000002), 0x40800002, STR(__LINE__)); // 0x1.000002p+1 + 0x1.000004p+1 = 0x1.000004p+2
}

void f328(void) {
  comp32(single_of_bits(0x40000002) + single_of_bits(0x40000001), 0x40800002, STR(__LINE__)); // 0x1.000004p+1 + 0x1.000002p+1 = 0x1.000004p+2
  comp32(single_of_bits(0xbf800000) + single_of_bits(0xbf800003), 0xc0000002, STR(__LINE__)); // -0x1p+0 + -0x1.000006p+0 = -0x1.000004p+1
  comp32(single_of_bits(0xbf800003) + single_of_bits(0xbf800000), 0xc0000002, STR(__LINE__)); // -0x1.000006p+0 + -0x1p+0 = -0x1.000004p+1
  comp32(single_of_bits(0xc0000001) + single_of_bits(0xc0000002), 0xc0800002, STR(__LINE__)); // -0x1.000002p+1 + -0x1.000004p+1 = -0x1.000004p+2
  comp32(single_of_bits(0xc0000002) + single_of_bits(0xc0000001), 0xc0800002, STR(__LINE__)); // -0x1.000004p+1 + -0x1.000002p+1 = -0x1.000004p+2
  comp32(single_of_bits(0x34000000) + single_of_bits(0x40000001), 0x40000002, STR(__LINE__)); // 0x1p-23 + 0x1.000002p+1 = 0x1.000004p+1
  comp32(single_of_bits(0x40000001) + single_of_bits(0x34000000), 0x40000002, STR(__LINE__)); // 0x1.000002p+1 + 0x1p-23 = 0x1.000004p+1
  comp32(single_of_bits(0xb4000000) + single_of_bits(0xc0000001), 0xc0000002, STR(__LINE__)); // -0x1p-23 + -0x1.000002p+1 = -0x1.000004p+1
  comp32(single_of_bits(0xc0000001) + single_of_bits(0xb4000000), 0xc0000002, STR(__LINE__)); // -0x1.000002p+1 + -0x1p-23 = -0x1.000004p+1
  comp32(single_of_bits(0x40000002) + single_of_bits(0xb4000000), 0x40000002, STR(__LINE__)); // 0x1.000004p+1 + -0x1p-23 = 0x1.000004p+1
}

void f329(void) {
  comp32(single_of_bits(0xb4000000) + single_of_bits(0x40000002), 0x40000002, STR(__LINE__)); // -0x1p-23 + 0x1.000004p+1 = 0x1.000004p+1
  comp32(single_of_bits(0x34000000) + single_of_bits(0xc0000002), 0xc0000002, STR(__LINE__)); // 0x1p-23 + -0x1.000004p+1 = -0x1.000004p+1
  comp32(single_of_bits(0xc0000002) + single_of_bits(0x34000000), 0xc0000002, STR(__LINE__)); // -0x1.000004p+1 + 0x1p-23 = -0x1.000004p+1
  comp32(single_of_bits(0x01800002) + single_of_bits(0x80000001), 0x01800002, STR(__LINE__)); // 0x1.000004p-124 + -0x1p-149 = 0x1.000004p-124
  comp32(single_of_bits(0x80000001) + single_of_bits(0x01800002), 0x01800002, STR(__LINE__)); // -0x1p-149 + 0x1.000004p-124 = 0x1.000004p-124
  comp32(single_of_bits(0x81800002) + single_of_bits(0x00000001), 0x81800002, STR(__LINE__)); // -0x1.000004p-124 + 0x1p-149 = -0x1.000004p-124
  comp32(single_of_bits(0x00000001) + single_of_bits(0x81800002), 0x81800002, STR(__LINE__)); // 0x1p-149 + -0x1.000004p-124 = -0x1.000004p-124
  comp32(single_of_bits(0x3f800003) + single_of_bits(0x40800000), 0x40a00001, STR(__LINE__)); // 0x1.000006p+0 + 0x1p+2 = 0x1.400002p+2
  comp32(single_of_bits(0x40800000) + single_of_bits(0x3f800003), 0x40a00001, STR(__LINE__)); // 0x1p+2 + 0x1.000006p+0 = 0x1.400002p+2
  comp32(single_of_bits(0xbf800003) + single_of_bits(0xc0800000), 0xc0a00001, STR(__LINE__)); // -0x1.000006p+0 + -0x1p+2 = -0x1.400002p+2
}

void f330(void) {
  comp32(single_of_bits(0xc0800000) + single_of_bits(0xbf800003), 0xc0a00001, STR(__LINE__)); // -0x1p+2 + -0x1.000006p+0 = -0x1.400002p+2
  comp32(single_of_bits(0x40400000) + single_of_bits(0x4c400000), 0x4c400001, STR(__LINE__)); // 0x1.8p+1 + 0x1.8p+25 = 0x1.800002p+25
  comp32(single_of_bits(0x4c400000) + single_of_bits(0x40400000), 0x4c400001, STR(__LINE__)); // 0x1.8p+25 + 0x1.8p+1 = 0x1.800002p+25
  comp32(single_of_bits(0xc0400000) + single_of_bits(0xcc400000), 0xcc400001, STR(__LINE__)); // -0x1.8p+1 + -0x1.8p+25 = -0x1.800002p+25
  comp32(single_of_bits(0xcc400000) + single_of_bits(0xc0400000), 0xcc400001, STR(__LINE__)); // -0x1.8p+25 + -0x1.8p+1 = -0x1.800002p+25
  comp32(single_of_bits(0x00000003) + single_of_bits(0x01800000), 0x01800001, STR(__LINE__)); // 0x1.8p-148 + 0x1p-124 = 0x1.000002p-124
  comp32(single_of_bits(0x01800000) + single_of_bits(0x00000003), 0x01800001, STR(__LINE__)); // 0x1p-124 + 0x1.8p-148 = 0x1.000002p-124
  comp32(single_of_bits(0x80000003) + single_of_bits(0x81800000), 0x81800001, STR(__LINE__)); // -0x1.8p-148 + -0x1p-124 = -0x1.000002p-124
  comp32(single_of_bits(0x81800000) + single_of_bits(0x80000003), 0x81800001, STR(__LINE__)); // -0x1p-124 + -0x1.8p-148 = -0x1.000002p-124
  comp32(single_of_bits(0x3fffffff) + single_of_bits(0x34a00000), 0x40000001, STR(__LINE__)); // 0x1.fffffep+0 + 0x1.4p-22 = 0x1.000002p+1
}

void f331(void) {
  comp32(single_of_bits(0x34a00000) + single_of_bits(0x3fffffff), 0x40000001, STR(__LINE__)); // 0x1.4p-22 + 0x1.fffffep+0 = 0x1.000002p+1
  comp32(single_of_bits(0xbfffffff) + single_of_bits(0xb4a00000), 0xc0000001, STR(__LINE__)); // -0x1.fffffep+0 + -0x1.4p-22 = -0x1.000002p+1
  comp32(single_of_bits(0xb4a00000) + single_of_bits(0xbfffffff), 0xc0000001, STR(__LINE__)); // -0x1.4p-22 + -0x1.fffffep+0 = -0x1.000002p+1
  comp32(single_of_bits(0x4c800000) + single_of_bits(0xbf800000), 0x4c800000, STR(__LINE__)); // 0x1p+26 + -0x1p+0 = 0x1p+26
  comp32(single_of_bits(0xbf800000) + single_of_bits(0x4c800000), 0x4c800000, STR(__LINE__)); // -0x1p+0 + 0x1p+26 = 0x1p+26
  comp32(single_of_bits(0x3f800000) + single_of_bits(0xcc800000), 0xcc800000, STR(__LINE__)); // 0x1p+0 + -0x1p+26 = -0x1p+26
  comp32(single_of_bits(0xcc800000) + single_of_bits(0x3f800000), 0xcc800000, STR(__LINE__)); // -0x1p+26 + 0x1p+0 = -0x1p+26
  comp32(single_of_bits(0x02000000) + single_of_bits(0x80000001), 0x02000000, STR(__LINE__)); // 0x1p-123 + -0x1p-149 = 0x1p-123
  comp32(single_of_bits(0x80000001) + single_of_bits(0x02000000), 0x02000000, STR(__LINE__)); // -0x1p-149 + 0x1p-123 = 0x1p-123
  comp32(single_of_bits(0x82000000) + single_of_bits(0x00000001), 0x82000000, STR(__LINE__)); // -0x1p-123 + 0x1p-149 = -0x1p-123
}

void f332(void) {
  comp32(single_of_bits(0x00000001) + single_of_bits(0x82000000), 0x82000000, STR(__LINE__)); // 0x1p-149 + -0x1p-123 = -0x1p-123
  comp32(single_of_bits(0x3f800005) + single_of_bits(0x41000000), 0x41100001, STR(__LINE__)); // 0x1.00000ap+0 + 0x1p+3 = 0x1.200002p+3
  comp32(single_of_bits(0x41000000) + single_of_bits(0x3f800005), 0x41100001, STR(__LINE__)); // 0x1p+3 + 0x1.00000ap+0 = 0x1.200002p+3
  comp32(single_of_bits(0xbf800005) + single_of_bits(0xc1000000), 0xc1100001, STR(__LINE__)); // -0x1.00000ap+0 + -0x1p+3 = -0x1.200002p+3
  comp32(single_of_bits(0xc1000000) + single_of_bits(0xbf800005), 0xc1100001, STR(__LINE__)); // -0x1p+3 + -0x1.00000ap+0 = -0x1.200002p+3
  comp32(single_of_bits(0x40a00000) + single_of_bits(0x4c800000), 0x4c800001, STR(__LINE__)); // 0x1.4p+2 + 0x1p+26 = 0x1.000002p+26
  comp32(single_of_bits(0x4c800000) + single_of_bits(0x40a00000), 0x4c800001, STR(__LINE__)); // 0x1p+26 + 0x1.4p+2 = 0x1.000002p+26
  comp32(single_of_bits(0xc0a00000) + single_of_bits(0xcc800000), 0xcc800001, STR(__LINE__)); // -0x1.4p+2 + -0x1p+26 = -0x1.000002p+26
  comp32(single_of_bits(0xcc800000) + single_of_bits(0xc0a00000), 0xcc800001, STR(__LINE__)); // -0x1p+26 + -0x1.4p+2 = -0x1.000002p+26
  comp32(single_of_bits(0x00000005) + single_of_bits(0x02000000), 0x02000001, STR(__LINE__)); // 0x1.4p-147 + 0x1p-123 = 0x1.000002p-123
}

void f333(void) {
  comp32(single_of_bits(0x02000000) + single_of_bits(0x00000005), 0x02000001, STR(__LINE__)); // 0x1p-123 + 0x1.4p-147 = 0x1.000002p-123
  comp32(single_of_bits(0x80000005) + single_of_bits(0x82000000), 0x82000001, STR(__LINE__)); // -0x1.4p-147 + -0x1p-123 = -0x1.000002p-123
  comp32(single_of_bits(0x82000000) + single_of_bits(0x80000005), 0x82000001, STR(__LINE__)); // -0x1p-123 + -0x1.4p-147 = -0x1.000002p-123
  comp32(single_of_bits(0x3fffffff) + single_of_bits(0x34800001), 0x40000001, STR(__LINE__)); // 0x1.fffffep+0 + 0x1.000002p-22 = 0x1.000002p+1
  comp32(single_of_bits(0x34800001) + single_of_bits(0x3fffffff), 0x40000001, STR(__LINE__)); // 0x1.000002p-22 + 0x1.fffffep+0 = 0x1.000002p+1
  comp32(single_of_bits(0xbfffffff) + single_of_bits(0xb4800001), 0xc0000001, STR(__LINE__)); // -0x1.fffffep+0 + -0x1.000002p-22 = -0x1.000002p+1
  comp32(single_of_bits(0xb4800001) + single_of_bits(0xbfffffff), 0xc0000001, STR(__LINE__)); // -0x1.000002p-22 + -0x1.fffffep+0 = -0x1.000002p+1
  comp32(single_of_bits(0x4d400000) + single_of_bits(0xc0400000), 0x4d400000, STR(__LINE__)); // 0x1.8p+27 + -0x1.8p+1 = 0x1.8p+27
  comp32(single_of_bits(0xc0400000) + single_of_bits(0x4d400000), 0x4d400000, STR(__LINE__)); // -0x1.8p+1 + 0x1.8p+27 = 0x1.8p+27
  comp32(single_of_bits(0x40400000) + single_of_bits(0xcd400000), 0xcd400000, STR(__LINE__)); // 0x1.8p+1 + -0x1.8p+27 = -0x1.8p+27
}

void f334(void) {
  comp32(single_of_bits(0xcd400000) + single_of_bits(0x40400000), 0xcd400000, STR(__LINE__)); // -0x1.8p+27 + 0x1.8p+1 = -0x1.8p+27
  comp32(single_of_bits(0x02800000) + single_of_bits(0x80000003), 0x02800000, STR(__LINE__)); // 0x1p-122 + -0x1.8p-148 = 0x1p-122
  comp32(single_of_bits(0x80000003) + single_of_bits(0x02800000), 0x02800000, STR(__LINE__)); // -0x1.8p-148 + 0x1p-122 = 0x1p-122
  comp32(single_of_bits(0x82800000) + single_of_bits(0x00000003), 0x82800000, STR(__LINE__)); // -0x1p-122 + 0x1.8p-148 = -0x1p-122
  comp32(single_of_bits(0x00000003) + single_of_bits(0x82800000), 0x82800000, STR(__LINE__)); // 0x1.8p-148 + -0x1p-122 = -0x1p-122
  comp32(single_of_bits(0x3f800007) + single_of_bits(0x41000000), 0x41100001, STR(__LINE__)); // 0x1.00000ep+0 + 0x1p+3 = 0x1.200002p+3
  comp32(single_of_bits(0x41000000) + single_of_bits(0x3f800007), 0x41100001, STR(__LINE__)); // 0x1p+3 + 0x1.00000ep+0 = 0x1.200002p+3
  comp32(single_of_bits(0xbf800007) + single_of_bits(0xc1000000), 0xc1100001, STR(__LINE__)); // -0x1.00000ep+0 + -0x1p+3 = -0x1.200002p+3
  comp32(single_of_bits(0xc1000000) + single_of_bits(0xbf800007), 0xc1100001, STR(__LINE__)); // -0x1p+3 + -0x1.00000ep+0 = -0x1.200002p+3
  comp32(single_of_bits(0x40e00000) + single_of_bits(0x4ce00000), 0x4ce00001, STR(__LINE__)); // 0x1.cp+2 + 0x1.cp+26 = 0x1.c00002p+26
}

void f335(void) {
  comp32(single_of_bits(0x4ce00000) + single_of_bits(0x40e00000), 0x4ce00001, STR(__LINE__)); // 0x1.cp+26 + 0x1.cp+2 = 0x1.c00002p+26
  comp32(single_of_bits(0xc0e00000) + single_of_bits(0xcce00000), 0xcce00001, STR(__LINE__)); // -0x1.cp+2 + -0x1.cp+26 = -0x1.c00002p+26
  comp32(single_of_bits(0xcce00000) + single_of_bits(0xc0e00000), 0xcce00001, STR(__LINE__)); // -0x1.cp+26 + -0x1.cp+2 = -0x1.c00002p+26
  comp32(single_of_bits(0x00000007) + single_of_bits(0x02000000), 0x02000001, STR(__LINE__)); // 0x1.cp-147 + 0x1p-123 = 0x1.000002p-123
  comp32(single_of_bits(0x02000000) + single_of_bits(0x00000007), 0x02000001, STR(__LINE__)); // 0x1p-123 + 0x1.cp-147 = 0x1.000002p-123
  comp32(single_of_bits(0x80000007) + single_of_bits(0x82000000), 0x82000001, STR(__LINE__)); // -0x1.cp-147 + -0x1p-123 = -0x1.000002p-123
  comp32(single_of_bits(0x82000000) + single_of_bits(0x80000007), 0x82000001, STR(__LINE__)); // -0x1p-123 + -0x1.cp-147 = -0x1.000002p-123
  comp32(single_of_bits(0x3fffffff) + single_of_bits(0x34a00001), 0x40000001, STR(__LINE__)); // 0x1.fffffep+0 + 0x1.400002p-22 = 0x1.000002p+1
  comp32(single_of_bits(0x34a00001) + single_of_bits(0x3fffffff), 0x40000001, STR(__LINE__)); // 0x1.400002p-22 + 0x1.fffffep+0 = 0x1.000002p+1
  comp32(single_of_bits(0xbfffffff) + single_of_bits(0xb4a00001), 0xc0000001, STR(__LINE__)); // -0x1.fffffep+0 + -0x1.400002p-22 = -0x1.000002p+1
}

void f336(void) {
  comp32(single_of_bits(0xb4a00001) + single_of_bits(0xbfffffff), 0xc0000001, STR(__LINE__)); // -0x1.400002p-22 + -0x1.fffffep+0 = -0x1.000002p+1
  comp32(single_of_bits(0x7f000000) + single_of_bits(0xbf800000), 0x7f000000, STR(__LINE__)); // 0x1p+127 + -0x1p+0 = 0x1p+127
  comp32(single_of_bits(0xbf800000) + single_of_bits(0x7f000000), 0x7f000000, STR(__LINE__)); // -0x1p+0 + 0x1p+127 = 0x1p+127
  comp32(single_of_bits(0xff000000) + single_of_bits(0x3f800000), 0xff000000, STR(__LINE__)); // -0x1p+127 + 0x1p+0 = -0x1p+127
  comp32(single_of_bits(0x3f800000) + single_of_bits(0xff000000), 0xff000000, STR(__LINE__)); // 0x1p+0 + -0x1p+127 = -0x1p+127
  comp32(single_of_bits(0x7effffff) + single_of_bits(0xbf800000), 0x7effffff, STR(__LINE__)); // 0x1.fffffep+126 + -0x1p+0 = 0x1.fffffep+126
  comp32(single_of_bits(0xbf800000) + single_of_bits(0x7effffff), 0x7effffff, STR(__LINE__)); // -0x1p+0 + 0x1.fffffep+126 = 0x1.fffffep+126
  comp32(single_of_bits(0xfeffffff) + single_of_bits(0x3f800000), 0xfeffffff, STR(__LINE__)); // -0x1.fffffep+126 + 0x1p+0 = -0x1.fffffep+126
  comp32(single_of_bits(0x3f800000) + single_of_bits(0xfeffffff), 0xfeffffff, STR(__LINE__)); // 0x1p+0 + -0x1.fffffep+126 = -0x1.fffffep+126
  comp32(single_of_bits(0x7f7fffff) + single_of_bits(0xbf800000), 0x7f7fffff, STR(__LINE__)); // 0x1.fffffep+127 + -0x1p+0 = 0x1.fffffep+127
}

void f337(void) {
  comp32(single_of_bits(0xbf800000) + single_of_bits(0x7f7fffff), 0x7f7fffff, STR(__LINE__)); // -0x1p+0 + 0x1.fffffep+127 = 0x1.fffffep+127
  comp32(single_of_bits(0xff7fffff) + single_of_bits(0x3f800000), 0xff7fffff, STR(__LINE__)); // -0x1.fffffep+127 + 0x1p+0 = -0x1.fffffep+127
  comp32(single_of_bits(0x3f800000) + single_of_bits(0xff7fffff), 0xff7fffff, STR(__LINE__)); // 0x1p+0 + -0x1.fffffep+127 = -0x1.fffffep+127
  comp32(single_of_bits(0x7f7ffffe) + single_of_bits(0xbf800000), 0x7f7ffffe, STR(__LINE__)); // 0x1.fffffcp+127 + -0x1p+0 = 0x1.fffffcp+127
  comp32(single_of_bits(0xbf800000) + single_of_bits(0x7f7ffffe), 0x7f7ffffe, STR(__LINE__)); // -0x1p+0 + 0x1.fffffcp+127 = 0x1.fffffcp+127
  comp32(single_of_bits(0xff7ffffe) + single_of_bits(0x3f800000), 0xff7ffffe, STR(__LINE__)); // -0x1.fffffcp+127 + 0x1p+0 = -0x1.fffffcp+127
  comp32(single_of_bits(0x3f800000) + single_of_bits(0xff7ffffe), 0xff7ffffe, STR(__LINE__)); // 0x1p+0 + -0x1.fffffcp+127 = -0x1.fffffcp+127
  comp32(single_of_bits(0x7f7fffff) + single_of_bits(0x80000001), 0x7f7fffff, STR(__LINE__)); // 0x1.fffffep+127 + -0x1p-149 = 0x1.fffffep+127
  comp32(single_of_bits(0x80000001) + single_of_bits(0x7f7fffff), 0x7f7fffff, STR(__LINE__)); // -0x1p-149 + 0x1.fffffep+127 = 0x1.fffffep+127
  comp32(single_of_bits(0xff7fffff) + single_of_bits(0x00000001), 0xff7fffff, STR(__LINE__)); // -0x1.fffffep+127 + 0x1p-149 = -0x1.fffffep+127
}

void f338(void) {
  comp32(single_of_bits(0x00000001) + single_of_bits(0xff7fffff), 0xff7fffff, STR(__LINE__)); // 0x1p-149 + -0x1.fffffep+127 = -0x1.fffffep+127
  comp32(single_of_bits(0x80000003) + single_of_bits(0x7f000000), 0x7f000000, STR(__LINE__)); // -0x1.8p-148 + 0x1p+127 = 0x1p+127
  comp32(single_of_bits(0x7f000000) + single_of_bits(0x80000003), 0x7f000000, STR(__LINE__)); // 0x1p+127 + -0x1.8p-148 = 0x1p+127
  comp32(single_of_bits(0x00000003) + single_of_bits(0xff000000), 0xff000000, STR(__LINE__)); // 0x1.8p-148 + -0x1p+127 = -0x1p+127
  comp32(single_of_bits(0xff000000) + single_of_bits(0x00000003), 0xff000000, STR(__LINE__)); // -0x1p+127 + 0x1.8p-148 = -0x1p+127
  comp32(single_of_bits(0x3f7fffff) + single_of_bits(0x80000001), 0x3f7fffff, STR(__LINE__)); // 0x1.fffffep-1 + -0x1p-149 = 0x1.fffffep-1
  comp32(single_of_bits(0x80000001) + single_of_bits(0x3f7fffff), 0x3f7fffff, STR(__LINE__)); // -0x1p-149 + 0x1.fffffep-1 = 0x1.fffffep-1
  comp32(single_of_bits(0xbfffffff) + single_of_bits(0x00000001), 0xbfffffff, STR(__LINE__)); // -0x1.fffffep+0 + 0x1p-149 = -0x1.fffffep+0
  comp32(single_of_bits(0x00000001) + single_of_bits(0xbfffffff), 0xbfffffff, STR(__LINE__)); // 0x1p-149 + -0x1.fffffep+0 = -0x1.fffffep+0
  comp32(single_of_bits(0x80000003) + single_of_bits(0x40400000), 0x40400000, STR(__LINE__)); // -0x1.8p-148 + 0x1.8p+1 = 0x1.8p+1
}

void f339(void) {
  comp32(single_of_bits(0x40400000) + single_of_bits(0x80000003), 0x40400000, STR(__LINE__)); // 0x1.8p+1 + -0x1.8p-148 = 0x1.8p+1
  comp32(single_of_bits(0x00000003) + single_of_bits(0xc0a00000), 0xc0a00000, STR(__LINE__)); // 0x1.8p-148 + -0x1.4p+2 = -0x1.4p+2
  comp32(single_of_bits(0xc0a00000) + single_of_bits(0x00000003), 0xc0a00000, STR(__LINE__)); // -0x1.4p+2 + 0x1.8p-148 = -0x1.4p+2
  comp32(single_of_bits(0x40000000) + single_of_bits(0xc0000000), 0x00000000, STR(__LINE__)); // 0x1p+1 + -0x1p+1 = 0x0p+0
  comp32(single_of_bits(0xc0000000) + single_of_bits(0x40000000), 0x00000000, STR(__LINE__)); // -0x1p+1 + 0x1p+1 = 0x0p+0
  comp32(single_of_bits(0x40a00000) + single_of_bits(0xc0a00000), 0x00000000, STR(__LINE__)); // 0x1.4p+2 + -0x1.4p+2 = 0x0p+0
  comp32(single_of_bits(0xc0a00000) + single_of_bits(0x40a00000), 0x00000000, STR(__LINE__)); // -0x1.4p+2 + 0x1.4p+2 = 0x0p+0
  comp32(single_of_bits(0x7f000000) + single_of_bits(0xff000000), 0x00000000, STR(__LINE__)); // 0x1p+127 + -0x1p+127 = 0x0p+0
  comp32(single_of_bits(0xff000000) + single_of_bits(0x7f000000), 0x00000000, STR(__LINE__)); // -0x1p+127 + 0x1p+127 = 0x0p+0
  comp32(single_of_bits(0xfefffffe) + single_of_bits(0x7efffffe), 0x00000000, STR(__LINE__)); // -0x1.fffffcp+126 + 0x1.fffffcp+126 = 0x0p+0
}

void f340(void) {
  comp32(single_of_bits(0x7efffffe) + single_of_bits(0xfefffffe), 0x00000000, STR(__LINE__)); // 0x1.fffffcp+126 + -0x1.fffffcp+126 = 0x0p+0
  comp32(single_of_bits(0x3f800000) + single_of_bits(0xbf800000), 0x00000000, STR(__LINE__)); // 0x1p+0 + -0x1p+0 = 0x0p+0
  comp32(single_of_bits(0xbf800000) + single_of_bits(0x3f800000), 0x00000000, STR(__LINE__)); // -0x1p+0 + 0x1p+0 = 0x0p+0
  comp32(single_of_bits(0xc0400000) + single_of_bits(0x40400000), 0x00000000, STR(__LINE__)); // -0x1.8p+1 + 0x1.8p+1 = 0x0p+0
  comp32(single_of_bits(0x40400000) + single_of_bits(0xc0400000), 0x00000000, STR(__LINE__)); // 0x1.8p+1 + -0x1.8p+1 = 0x0p+0
  comp32(single_of_bits(0x00800000) + single_of_bits(0x80800000), 0x00000000, STR(__LINE__)); // 0x1p-126 + -0x1p-126 = 0x0p+0
  comp32(single_of_bits(0x80800000) + single_of_bits(0x00800000), 0x00000000, STR(__LINE__)); // -0x1p-126 + 0x1p-126 = 0x0p+0
  comp32(single_of_bits(0x007ffffc) + single_of_bits(0x807ffffc), 0x00000000, STR(__LINE__)); // 0x1.fffffp-127 + -0x1.fffffp-127 = 0x0p+0
  comp32(single_of_bits(0x807ffffc) + single_of_bits(0x007ffffc), 0x00000000, STR(__LINE__)); // -0x1.fffffp-127 + 0x1.fffffp-127 = 0x0p+0
  comp32(single_of_bits(0x807fffff) + single_of_bits(0x007fffff), 0x00000000, STR(__LINE__)); // -0x1.fffffcp-127 + 0x1.fffffcp-127 = 0x0p+0
}

void f341(void) {
  comp32(single_of_bits(0x007fffff) + single_of_bits(0x807fffff), 0x00000000, STR(__LINE__)); // 0x1.fffffcp-127 + -0x1.fffffcp-127 = 0x0p+0
  comp32(single_of_bits(0x00000001) + single_of_bits(0x80000001), 0x00000000, STR(__LINE__)); // 0x1p-149 + -0x1p-149 = 0x0p+0
  comp32(single_of_bits(0x80000001) + single_of_bits(0x00000001), 0x00000000, STR(__LINE__)); // -0x1p-149 + 0x1p-149 = 0x0p+0
  comp32(single_of_bits(0x7f7fffff) + single_of_bits(0xff7fffff), 0x00000000, STR(__LINE__)); // 0x1.fffffep+127 + -0x1.fffffep+127 = 0x0p+0
  comp32(single_of_bits(0xff7fffff) + single_of_bits(0x7f7fffff), 0x00000000, STR(__LINE__)); // -0x1.fffffep+127 + 0x1.fffffep+127 = 0x0p+0
  comp32(single_of_bits(0x3f800001) + single_of_bits(0xbf800000), 0x34000000, STR(__LINE__)); // 0x1.000002p+0 + -0x1p+0 = 0x1p-23
  comp32(single_of_bits(0xbf800000) + single_of_bits(0x3f800001), 0x34000000, STR(__LINE__)); // -0x1p+0 + 0x1.000002p+0 = 0x1p-23
  comp32(single_of_bits(0x7f000001) + single_of_bits(0xff000000), 0x73800000, STR(__LINE__)); // 0x1.000002p+127 + -0x1p+127 = 0x1p+104
  comp32(single_of_bits(0xff000000) + single_of_bits(0x7f000001), 0x73800000, STR(__LINE__)); // -0x1p+127 + 0x1.000002p+127 = 0x1p+104
  comp32(single_of_bits(0x00800001) + single_of_bits(0x80800000), 0x00000001, STR(__LINE__)); // 0x1.000002p-126 + -0x1p-126 = 0x1p-149
}

void f342(void) {
  comp32(single_of_bits(0x80800000) + single_of_bits(0x00800001), 0x00000001, STR(__LINE__)); // -0x1p-126 + 0x1.000002p-126 = 0x1p-149
  comp32(single_of_bits(0xc0000000) + single_of_bits(0x40000001), 0x34800000, STR(__LINE__)); // -0x1p+1 + 0x1.000002p+1 = 0x1p-22
  comp32(single_of_bits(0x40000001) + single_of_bits(0xc0000000), 0x34800000, STR(__LINE__)); // 0x1.000002p+1 + -0x1p+1 = 0x1p-22
  comp32(single_of_bits(0xfe800000) + single_of_bits(0x7e800001), 0x73000000, STR(__LINE__)); // -0x1p+126 + 0x1.000002p+126 = 0x1p+103
  comp32(single_of_bits(0x7e800001) + single_of_bits(0xfe800000), 0x73000000, STR(__LINE__)); // 0x1.000002p+126 + -0x1p+126 = 0x1p+103
  comp32(single_of_bits(0xbf800001) + single_of_bits(0x3f800000), 0xb4000000, STR(__LINE__)); // -0x1.000002p+0 + 0x1p+0 = -0x1p-23
  comp32(single_of_bits(0x3f800000) + single_of_bits(0xbf800001), 0xb4000000, STR(__LINE__)); // 0x1p+0 + -0x1.000002p+0 = -0x1p-23
  comp32(single_of_bits(0xff000001) + single_of_bits(0x7f000000), 0xf3800000, STR(__LINE__)); // -0x1.000002p+127 + 0x1p+127 = -0x1p+104
  comp32(single_of_bits(0x7f000000) + single_of_bits(0xff000001), 0xf3800000, STR(__LINE__)); // 0x1p+127 + -0x1.000002p+127 = -0x1p+104
  comp32(single_of_bits(0x80800001) + single_of_bits(0x00800000), 0x80000001, STR(__LINE__)); // -0x1.000002p-126 + 0x1p-126 = -0x1p-149
}

void f343(void) {
  comp32(single_of_bits(0x00800000) + single_of_bits(0x80800001), 0x80000001, STR(__LINE__)); // 0x1p-126 + -0x1.000002p-126 = -0x1p-149
  comp32(single_of_bits(0x40000000) + single_of_bits(0xc0000001), 0xb4800000, STR(__LINE__)); // 0x1p+1 + -0x1.000002p+1 = -0x1p-22
  comp32(single_of_bits(0xc0000001) + single_of_bits(0x40000000), 0xb4800000, STR(__LINE__)); // -0x1.000002p+1 + 0x1p+1 = -0x1p-22
  comp32(single_of_bits(0x7e800000) + single_of_bits(0xfe800001), 0xf3000000, STR(__LINE__)); // 0x1p+126 + -0x1.000002p+126 = -0x1p+103
  comp32(single_of_bits(0xfe800001) + single_of_bits(0x7e800000), 0xf3000000, STR(__LINE__)); // -0x1.000002p+126 + 0x1p+126 = -0x1p+103
  comp32(single_of_bits(0x00000002) + single_of_bits(0x80000001), 0x00000001, STR(__LINE__)); // 0x1p-148 + -0x1p-149 = 0x1p-149
  comp32(single_of_bits(0x80000001) + single_of_bits(0x00000002), 0x00000001, STR(__LINE__)); // -0x1p-149 + 0x1p-148 = 0x1p-149
  comp32(single_of_bits(0xbf800001) + single_of_bits(0x3f800002), 0x34000000, STR(__LINE__)); // -0x1.000002p+0 + 0x1.000004p+0 = 0x1p-23
  comp32(single_of_bits(0x3f800002) + single_of_bits(0xbf800001), 0x34000000, STR(__LINE__)); // 0x1.000004p+0 + -0x1.000002p+0 = 0x1p-23
  comp32(single_of_bits(0xff000001) + single_of_bits(0x7f000002), 0x73800000, STR(__LINE__)); // -0x1.000002p+127 + 0x1.000004p+127 = 0x1p+104
}

void f344(void) {
  comp32(single_of_bits(0x7f000002) + single_of_bits(0xff000001), 0x73800000, STR(__LINE__)); // 0x1.000004p+127 + -0x1.000002p+127 = 0x1p+104
  comp32(single_of_bits(0x80800001) + single_of_bits(0x00800002), 0x00000001, STR(__LINE__)); // -0x1.000002p-126 + 0x1.000004p-126 = 0x1p-149
  comp32(single_of_bits(0x00800002) + single_of_bits(0x80800001), 0x00000001, STR(__LINE__)); // 0x1.000004p-126 + -0x1.000002p-126 = 0x1p-149
  comp32(single_of_bits(0x80000002) + single_of_bits(0x00000001), 0x80000001, STR(__LINE__)); // -0x1p-148 + 0x1p-149 = -0x1p-149
  comp32(single_of_bits(0x00000001) + single_of_bits(0x80000002), 0x80000001, STR(__LINE__)); // 0x1p-149 + -0x1p-148 = -0x1p-149
  comp32(single_of_bits(0x3f800001) + single_of_bits(0xbf800002), 0xb4000000, STR(__LINE__)); // 0x1.000002p+0 + -0x1.000004p+0 = -0x1p-23
  comp32(single_of_bits(0xbf800002) + single_of_bits(0x3f800001), 0xb4000000, STR(__LINE__)); // -0x1.000004p+0 + 0x1.000002p+0 = -0x1p-23
  comp32(single_of_bits(0x7f000001) + single_of_bits(0xff000002), 0xf3800000, STR(__LINE__)); // 0x1.000002p+127 + -0x1.000004p+127 = -0x1p+104
  comp32(single_of_bits(0xff000002) + single_of_bits(0x7f000001), 0xf3800000, STR(__LINE__)); // -0x1.000004p+127 + 0x1.000002p+127 = -0x1p+104
  comp32(single_of_bits(0x00800001) + single_of_bits(0x80800002), 0x80000001, STR(__LINE__)); // 0x1.000002p-126 + -0x1.000004p-126 = -0x1p-149
}

void f345(void) {
  comp32(single_of_bits(0x80800002) + single_of_bits(0x00800001), 0x80000001, STR(__LINE__)); // -0x1.000004p-126 + 0x1.000002p-126 = -0x1p-149
  comp32(single_of_bits(0x80000003) + single_of_bits(0x00000002), 0x80000001, STR(__LINE__)); // -0x1.8p-148 + 0x1p-148 = -0x1p-149
  comp32(single_of_bits(0x00000002) + single_of_bits(0x80000003), 0x80000001, STR(__LINE__)); // 0x1p-148 + -0x1.8p-148 = -0x1p-149
  comp32(single_of_bits(0x00000003) + single_of_bits(0x80000002), 0x00000001, STR(__LINE__)); // 0x1.8p-148 + -0x1p-148 = 0x1p-149
  comp32(single_of_bits(0x80000002) + single_of_bits(0x00000003), 0x00000001, STR(__LINE__)); // -0x1p-148 + 0x1.8p-148 = 0x1p-149
  comp32(single_of_bits(0x40000004) + single_of_bits(0xc0000003), 0x34800000, STR(__LINE__)); // 0x1.000008p+1 + -0x1.000006p+1 = 0x1p-22
  comp32(single_of_bits(0xc0000003) + single_of_bits(0x40000004), 0x34800000, STR(__LINE__)); // -0x1.000006p+1 + 0x1.000008p+1 = 0x1p-22
  comp32(single_of_bits(0x7e800004) + single_of_bits(0xfe800003), 0x73000000, STR(__LINE__)); // 0x1.000008p+126 + -0x1.000006p+126 = 0x1p+103
  comp32(single_of_bits(0xfe800003) + single_of_bits(0x7e800004), 0x73000000, STR(__LINE__)); // -0x1.000006p+126 + 0x1.000008p+126 = 0x1p+103
  comp32(single_of_bits(0xc0000004) + single_of_bits(0x40000003), 0xb4800000, STR(__LINE__)); // -0x1.000008p+1 + 0x1.000006p+1 = -0x1p-22
}

void f346(void) {
  comp32(single_of_bits(0x40000003) + single_of_bits(0xc0000004), 0xb4800000, STR(__LINE__)); // 0x1.000006p+1 + -0x1.000008p+1 = -0x1p-22
  comp32(single_of_bits(0xfe800004) + single_of_bits(0x7e800003), 0xf3000000, STR(__LINE__)); // -0x1.000008p+126 + 0x1.000006p+126 = -0x1p+103
  comp32(single_of_bits(0x7e800003) + single_of_bits(0xfe800004), 0xf3000000, STR(__LINE__)); // 0x1.000006p+126 + -0x1.000008p+126 = -0x1p+103
  comp32(single_of_bits(0x407fffff) + single_of_bits(0xc07ffffe), 0x34800000, STR(__LINE__)); // 0x1.fffffep+1 + -0x1.fffffcp+1 = 0x1p-22
  comp32(single_of_bits(0xc07ffffe) + single_of_bits(0x407fffff), 0x34800000, STR(__LINE__)); // -0x1.fffffcp+1 + 0x1.fffffep+1 = 0x1p-22
  comp32(single_of_bits(0x7e7fffff) + single_of_bits(0xfe7ffffe), 0x72800000, STR(__LINE__)); // 0x1.fffffep+125 + -0x1.fffffcp+125 = 0x1p+102
  comp32(single_of_bits(0xfe7ffffe) + single_of_bits(0x7e7fffff), 0x72800000, STR(__LINE__)); // -0x1.fffffcp+125 + 0x1.fffffep+125 = 0x1p+102
  comp32(single_of_bits(0x007fffff) + single_of_bits(0x807ffffe), 0x00000001, STR(__LINE__)); // 0x1.fffffcp-127 + -0x1.fffff8p-127 = 0x1p-149
  comp32(single_of_bits(0x807ffffe) + single_of_bits(0x007fffff), 0x00000001, STR(__LINE__)); // -0x1.fffff8p-127 + 0x1.fffffcp-127 = 0x1p-149
  comp32(single_of_bits(0xff7ffffe) + single_of_bits(0x7f7fffff), 0x73800000, STR(__LINE__)); // -0x1.fffffcp+127 + 0x1.fffffep+127 = 0x1p+104
}

void f347(void) {
  comp32(single_of_bits(0x7f7fffff) + single_of_bits(0xff7ffffe), 0x73800000, STR(__LINE__)); // 0x1.fffffep+127 + -0x1.fffffcp+127 = 0x1p+104
  comp32(single_of_bits(0xc07fffff) + single_of_bits(0x407ffffe), 0xb4800000, STR(__LINE__)); // -0x1.fffffep+1 + 0x1.fffffcp+1 = -0x1p-22
  comp32(single_of_bits(0x407ffffe) + single_of_bits(0xc07fffff), 0xb4800000, STR(__LINE__)); // 0x1.fffffcp+1 + -0x1.fffffep+1 = -0x1p-22
  comp32(single_of_bits(0xfe7fffff) + single_of_bits(0x7e7ffffe), 0xf2800000, STR(__LINE__)); // -0x1.fffffep+125 + 0x1.fffffcp+125 = -0x1p+102
  comp32(single_of_bits(0x7e7ffffe) + single_of_bits(0xfe7fffff), 0xf2800000, STR(__LINE__)); // 0x1.fffffcp+125 + -0x1.fffffep+125 = -0x1p+102
  comp32(single_of_bits(0x807fffff) + single_of_bits(0x007ffffe), 0x80000001, STR(__LINE__)); // -0x1.fffffcp-127 + 0x1.fffff8p-127 = -0x1p-149
  comp32(single_of_bits(0x007ffffe) + single_of_bits(0x807fffff), 0x80000001, STR(__LINE__)); // 0x1.fffff8p-127 + -0x1.fffffcp-127 = -0x1p-149
  comp32(single_of_bits(0x7f7ffffe) + single_of_bits(0xff7fffff), 0xf3800000, STR(__LINE__)); // 0x1.fffffcp+127 + -0x1.fffffep+127 = -0x1p+104
  comp32(single_of_bits(0xff7fffff) + single_of_bits(0x7f7ffffe), 0xf3800000, STR(__LINE__)); // -0x1.fffffep+127 + 0x1.fffffcp+127 = -0x1p+104
  comp32(single_of_bits(0x007ffffd) + single_of_bits(0x807ffffe), 0x80000001, STR(__LINE__)); // 0x1.fffff4p-127 + -0x1.fffff8p-127 = -0x1p-149
}

void f348(void) {
  comp32(single_of_bits(0x807ffffe) + single_of_bits(0x007ffffd), 0x80000001, STR(__LINE__)); // -0x1.fffff8p-127 + 0x1.fffff4p-127 = -0x1p-149
  comp32(single_of_bits(0x807ffffd) + single_of_bits(0x007ffffe), 0x00000001, STR(__LINE__)); // -0x1.fffff4p-127 + 0x1.fffff8p-127 = 0x1p-149
  comp32(single_of_bits(0x007ffffe) + single_of_bits(0x807ffffd), 0x00000001, STR(__LINE__)); // 0x1.fffff8p-127 + -0x1.fffff4p-127 = 0x1p-149
  comp32(single_of_bits(0x3ffffffc) + single_of_bits(0xbffffffd), 0xb4000000, STR(__LINE__)); // 0x1.fffff8p+0 + -0x1.fffffap+0 = -0x1p-23
  comp32(single_of_bits(0xbffffffd) + single_of_bits(0x3ffffffc), 0xb4000000, STR(__LINE__)); // -0x1.fffffap+0 + 0x1.fffff8p+0 = -0x1p-23
  comp32(single_of_bits(0xbffffffc) + single_of_bits(0x3ffffffd), 0x34000000, STR(__LINE__)); // -0x1.fffff8p+0 + 0x1.fffffap+0 = 0x1p-23
  comp32(single_of_bits(0x3ffffffd) + single_of_bits(0xbffffffc), 0x34000000, STR(__LINE__)); // 0x1.fffffap+0 + -0x1.fffff8p+0 = 0x1p-23
  comp32(single_of_bits(0x007fffff) + single_of_bits(0x80800000), 0x80000001, STR(__LINE__)); // 0x1.fffffcp-127 + -0x1p-126 = -0x1p-149
  comp32(single_of_bits(0x80800000) + single_of_bits(0x007fffff), 0x80000001, STR(__LINE__)); // -0x1p-126 + 0x1.fffffcp-127 = -0x1p-149
  comp32(single_of_bits(0x3fffffff) + single_of_bits(0xc0000000), 0xb4000000, STR(__LINE__)); // 0x1.fffffep+0 + -0x1p+1 = -0x1p-23
}

void f349(void) {
  comp32(single_of_bits(0xc0000000) + single_of_bits(0x3fffffff), 0xb4000000, STR(__LINE__)); // -0x1p+1 + 0x1.fffffep+0 = -0x1p-23
  comp32(single_of_bits(0x017fffff) + single_of_bits(0x81800000), 0x80000002, STR(__LINE__)); // 0x1.fffffep-125 + -0x1p-124 = -0x1p-148
  comp32(single_of_bits(0x81800000) + single_of_bits(0x017fffff), 0x80000002, STR(__LINE__)); // -0x1p-124 + 0x1.fffffep-125 = -0x1p-148
  comp32(single_of_bits(0x7effffff) + single_of_bits(0xff000000), 0xf3000000, STR(__LINE__)); // 0x1.fffffep+126 + -0x1p+127 = -0x1p+103
  comp32(single_of_bits(0xff000000) + single_of_bits(0x7effffff), 0xf3000000, STR(__LINE__)); // -0x1p+127 + 0x1.fffffep+126 = -0x1p+103
  comp32(single_of_bits(0x00ffffff) + single_of_bits(0x81000000), 0x80000001, STR(__LINE__)); // 0x1.fffffep-126 + -0x1p-125 = -0x1p-149
  comp32(single_of_bits(0x81000000) + single_of_bits(0x00ffffff), 0x80000001, STR(__LINE__)); // -0x1p-125 + 0x1.fffffep-126 = -0x1p-149
  comp32(single_of_bits(0xfe800000) + single_of_bits(0x7e7fffff), 0xf2800000, STR(__LINE__)); // -0x1p+126 + 0x1.fffffep+125 = -0x1p+102
  comp32(single_of_bits(0x7e7fffff) + single_of_bits(0xfe800000), 0xf2800000, STR(__LINE__)); // 0x1.fffffep+125 + -0x1p+126 = -0x1p+102
  comp32(single_of_bits(0x40000000) + single_of_bits(0xbfffffff), 0x34000000, STR(__LINE__)); // 0x1p+1 + -0x1.fffffep+0 = 0x1p-23
}

void f350(void) {
  comp32(single_of_bits(0xbfffffff) + single_of_bits(0x40000000), 0x34000000, STR(__LINE__)); // -0x1.fffffep+0 + 0x1p+1 = 0x1p-23
  comp32(single_of_bits(0x7e800000) + single_of_bits(0xfe7fffff), 0x72800000, STR(__LINE__)); // 0x1p+126 + -0x1.fffffep+125 = 0x1p+102
  comp32(single_of_bits(0xfe7fffff) + single_of_bits(0x7e800000), 0x72800000, STR(__LINE__)); // -0x1.fffffep+125 + 0x1p+126 = 0x1p+102
  comp32(single_of_bits(0x01000000) + single_of_bits(0x80ffffff), 0x00000001, STR(__LINE__)); // 0x1p-125 + -0x1.fffffep-126 = 0x1p-149
  comp32(single_of_bits(0x80ffffff) + single_of_bits(0x01000000), 0x00000001, STR(__LINE__)); // -0x1.fffffep-126 + 0x1p-125 = 0x1p-149
  comp32(single_of_bits(0x01800000) + single_of_bits(0x817fffff), 0x00000002, STR(__LINE__)); // 0x1p-124 + -0x1.fffffep-125 = 0x1p-148
  comp32(single_of_bits(0x817fffff) + single_of_bits(0x01800000), 0x00000002, STR(__LINE__)); // -0x1.fffffep-125 + 0x1p-124 = 0x1p-148
  comp32(single_of_bits(0x807fffff) + single_of_bits(0x00800000), 0x00000001, STR(__LINE__)); // -0x1.fffffcp-127 + 0x1p-126 = 0x1p-149
  comp32(single_of_bits(0x00800000) + single_of_bits(0x807fffff), 0x00000001, STR(__LINE__)); // 0x1p-126 + -0x1.fffffcp-127 = 0x1p-149
  comp32(single_of_bits(0xfeffffff) + single_of_bits(0x7f000000), 0x73000000, STR(__LINE__)); // -0x1.fffffep+126 + 0x1p+127 = 0x1p+103
}

void f351(void) {
  comp32(single_of_bits(0x7f000000) + single_of_bits(0xfeffffff), 0x73000000, STR(__LINE__)); // 0x1p+127 + -0x1.fffffep+126 = 0x1p+103
  comp32(single_of_bits(0x407fffff) + single_of_bits(0xc0800001), 0xb5400000, STR(__LINE__)); // 0x1.fffffep+1 + -0x1.000002p+2 = -0x1.8p-21
  comp32(single_of_bits(0xc0800001) + single_of_bits(0x407fffff), 0xb5400000, STR(__LINE__)); // -0x1.000002p+2 + 0x1.fffffep+1 = -0x1.8p-21
  comp32(single_of_bits(0xfd800001) + single_of_bits(0x7d7fffff), 0xf2400000, STR(__LINE__)); // -0x1.000002p+124 + 0x1.fffffep+123 = -0x1.8p+101
  comp32(single_of_bits(0x7d7fffff) + single_of_bits(0xfd800001), 0xf2400000, STR(__LINE__)); // 0x1.fffffep+123 + -0x1.000002p+124 = -0x1.8p+101
  comp32(single_of_bits(0x81000001) + single_of_bits(0x00ffffff), 0x80000003, STR(__LINE__)); // -0x1.000002p-125 + 0x1.fffffep-126 = -0x1.8p-148
  comp32(single_of_bits(0x00ffffff) + single_of_bits(0x81000001), 0x80000003, STR(__LINE__)); // 0x1.fffffep-126 + -0x1.000002p-125 = -0x1.8p-148
  comp32(single_of_bits(0x81800001) + single_of_bits(0x017fffff), 0x80000006, STR(__LINE__)); // -0x1.000002p-124 + 0x1.fffffep-125 = -0x1.8p-147
  comp32(single_of_bits(0x017fffff) + single_of_bits(0x81800001), 0x80000006, STR(__LINE__)); // 0x1.fffffep-125 + -0x1.000002p-124 = -0x1.8p-147
  comp32(single_of_bits(0xc07fffff) + single_of_bits(0x40800001), 0x35400000, STR(__LINE__)); // -0x1.fffffep+1 + 0x1.000002p+2 = 0x1.8p-21
}

void f352(void) {
  comp32(single_of_bits(0x40800001) + single_of_bits(0xc07fffff), 0x35400000, STR(__LINE__)); // 0x1.000002p+2 + -0x1.fffffep+1 = 0x1.8p-21
  comp32(single_of_bits(0x7d800001) + single_of_bits(0xfd7fffff), 0x72400000, STR(__LINE__)); // 0x1.000002p+124 + -0x1.fffffep+123 = 0x1.8p+101
  comp32(single_of_bits(0xfd7fffff) + single_of_bits(0x7d800001), 0x72400000, STR(__LINE__)); // -0x1.fffffep+123 + 0x1.000002p+124 = 0x1.8p+101
  comp32(single_of_bits(0x01000001) + single_of_bits(0x80ffffff), 0x00000003, STR(__LINE__)); // 0x1.000002p-125 + -0x1.fffffep-126 = 0x1.8p-148
  comp32(single_of_bits(0x80ffffff) + single_of_bits(0x01000001), 0x00000003, STR(__LINE__)); // -0x1.fffffep-126 + 0x1.000002p-125 = 0x1.8p-148
  comp32(single_of_bits(0x01800001) + single_of_bits(0x817fffff), 0x00000006, STR(__LINE__)); // 0x1.000002p-124 + -0x1.fffffep-125 = 0x1.8p-147
  comp32(single_of_bits(0x817fffff) + single_of_bits(0x01800001), 0x00000006, STR(__LINE__)); // -0x1.fffffep-125 + 0x1.000002p-124 = 0x1.8p-147
  comp32(single_of_bits(0x407fffff) + single_of_bits(0xc0800002), 0xb5a00000, STR(__LINE__)); // 0x1.fffffep+1 + -0x1.000004p+2 = -0x1.4p-20
  comp32(single_of_bits(0xc0800002) + single_of_bits(0x407fffff), 0xb5a00000, STR(__LINE__)); // -0x1.000004p+2 + 0x1.fffffep+1 = -0x1.4p-20
  comp32(single_of_bits(0x7e7fffff) + single_of_bits(0xfe800002), 0xf3a00000, STR(__LINE__)); // 0x1.fffffep+125 + -0x1.000004p+126 = -0x1.4p+104
}

void f353(void) {
  comp32(single_of_bits(0xfe800002) + single_of_bits(0x7e7fffff), 0xf3a00000, STR(__LINE__)); // -0x1.000004p+126 + 0x1.fffffep+125 = -0x1.4p+104
  comp32(single_of_bits(0x00ffffff) + single_of_bits(0x81000002), 0x80000005, STR(__LINE__)); // 0x1.fffffep-126 + -0x1.000004p-125 = -0x1.4p-147
  comp32(single_of_bits(0x81000002) + single_of_bits(0x00ffffff), 0x80000005, STR(__LINE__)); // -0x1.000004p-125 + 0x1.fffffep-126 = -0x1.4p-147
  comp32(single_of_bits(0xc07fffff) + single_of_bits(0x40800002), 0x35a00000, STR(__LINE__)); // -0x1.fffffep+1 + 0x1.000004p+2 = 0x1.4p-20
  comp32(single_of_bits(0x40800002) + single_of_bits(0xc07fffff), 0x35a00000, STR(__LINE__)); // 0x1.000004p+2 + -0x1.fffffep+1 = 0x1.4p-20
  comp32(single_of_bits(0xfe7fffff) + single_of_bits(0x7e800002), 0x73a00000, STR(__LINE__)); // -0x1.fffffep+125 + 0x1.000004p+126 = 0x1.4p+104
  comp32(single_of_bits(0x7e800002) + single_of_bits(0xfe7fffff), 0x73a00000, STR(__LINE__)); // 0x1.000004p+126 + -0x1.fffffep+125 = 0x1.4p+104
  comp32(single_of_bits(0x80ffffff) + single_of_bits(0x01000002), 0x00000005, STR(__LINE__)); // -0x1.fffffep-126 + 0x1.000004p-125 = 0x1.4p-147
  comp32(single_of_bits(0x01000002) + single_of_bits(0x80ffffff), 0x00000005, STR(__LINE__)); // 0x1.000004p-125 + -0x1.fffffep-126 = 0x1.4p-147
  comp32(single_of_bits(0x00ffffff) + single_of_bits(0x81000004), 0x80000009, STR(__LINE__)); // 0x1.fffffep-126 + -0x1.000008p-125 = -0x1.2p-146
}

void f354(void) {
  comp32(single_of_bits(0x81000004) + single_of_bits(0x00ffffff), 0x80000009, STR(__LINE__)); // -0x1.000008p-125 + 0x1.fffffep-126 = -0x1.2p-146
  comp32(single_of_bits(0x80ffffff) + single_of_bits(0x01000004), 0x00000009, STR(__LINE__)); // -0x1.fffffep-126 + 0x1.000008p-125 = 0x1.2p-146
  comp32(single_of_bits(0x01000004) + single_of_bits(0x80ffffff), 0x00000009, STR(__LINE__)); // 0x1.000008p-125 + -0x1.fffffep-126 = 0x1.2p-146
  comp32(single_of_bits(0x40000001) + single_of_bits(0xbf800001), 0x3f800001, STR(__LINE__)); // 0x1.000002p+1 + -0x1.000002p+0 = 0x1.000002p+0
  comp32(single_of_bits(0xbf800001) + single_of_bits(0x40000001), 0x3f800001, STR(__LINE__)); // -0x1.000002p+0 + 0x1.000002p+1 = 0x1.000002p+0
  comp32(single_of_bits(0x01000001) + single_of_bits(0x80800001), 0x00800001, STR(__LINE__)); // 0x1.000002p-125 + -0x1.000002p-126 = 0x1.000002p-126
  comp32(single_of_bits(0x80800001) + single_of_bits(0x01000001), 0x00800001, STR(__LINE__)); // -0x1.000002p-126 + 0x1.000002p-125 = 0x1.000002p-126
  comp32(single_of_bits(0xc0000001) + single_of_bits(0x3f800001), 0xbf800001, STR(__LINE__)); // -0x1.000002p+1 + 0x1.000002p+0 = -0x1.000002p+0
  comp32(single_of_bits(0x3f800001) + single_of_bits(0xc0000001), 0xbf800001, STR(__LINE__)); // 0x1.000002p+0 + -0x1.000002p+1 = -0x1.000002p+0
  comp32(single_of_bits(0x81000001) + single_of_bits(0x00800001), 0x80800001, STR(__LINE__)); // -0x1.000002p-125 + 0x1.000002p-126 = -0x1.000002p-126
}

void f355(void) {
  comp32(single_of_bits(0x00800001) + single_of_bits(0x81000001), 0x80800001, STR(__LINE__)); // 0x1.000002p-126 + -0x1.000002p-125 = -0x1.000002p-126
  comp32(single_of_bits(0xfe800001) + single_of_bits(0x7f000001), 0x7e800001, STR(__LINE__)); // -0x1.000002p+126 + 0x1.000002p+127 = 0x1.000002p+126
  comp32(single_of_bits(0x7f000001) + single_of_bits(0xfe800001), 0x7e800001, STR(__LINE__)); // 0x1.000002p+127 + -0x1.000002p+126 = 0x1.000002p+126
  comp32(single_of_bits(0x7e800001) + single_of_bits(0xff000001), 0xfe800001, STR(__LINE__)); // 0x1.000002p+126 + -0x1.000002p+127 = -0x1.000002p+126
  comp32(single_of_bits(0xff000001) + single_of_bits(0x7e800001), 0xfe800001, STR(__LINE__)); // -0x1.000002p+127 + 0x1.000002p+126 = -0x1.000002p+126
  comp32(single_of_bits(0x40000002) + single_of_bits(0xbf800001), 0x3f800003, STR(__LINE__)); // 0x1.000004p+1 + -0x1.000002p+0 = 0x1.000006p+0
  comp32(single_of_bits(0xbf800001) + single_of_bits(0x40000002), 0x3f800003, STR(__LINE__)); // -0x1.000002p+0 + 0x1.000004p+1 = 0x1.000006p+0
  comp32(single_of_bits(0x7f000002) + single_of_bits(0xfe800001), 0x7e800003, STR(__LINE__)); // 0x1.000004p+127 + -0x1.000002p+126 = 0x1.000006p+126
  comp32(single_of_bits(0xfe800001) + single_of_bits(0x7f000002), 0x7e800003, STR(__LINE__)); // -0x1.000002p+126 + 0x1.000004p+127 = 0x1.000006p+126
  comp32(single_of_bits(0x01000002) + single_of_bits(0x80800001), 0x00800003, STR(__LINE__)); // 0x1.000004p-125 + -0x1.000002p-126 = 0x1.000006p-126
}

void f356(void) {
  comp32(single_of_bits(0x80800001) + single_of_bits(0x01000002), 0x00800003, STR(__LINE__)); // -0x1.000002p-126 + 0x1.000004p-125 = 0x1.000006p-126
  comp32(single_of_bits(0xc0000002) + single_of_bits(0x3f800001), 0xbf800003, STR(__LINE__)); // -0x1.000004p+1 + 0x1.000002p+0 = -0x1.000006p+0
  comp32(single_of_bits(0x3f800001) + single_of_bits(0xc0000002), 0xbf800003, STR(__LINE__)); // 0x1.000002p+0 + -0x1.000004p+1 = -0x1.000006p+0
  comp32(single_of_bits(0xff000002) + single_of_bits(0x7e800001), 0xfe800003, STR(__LINE__)); // -0x1.000004p+127 + 0x1.000002p+126 = -0x1.000006p+126
  comp32(single_of_bits(0x7e800001) + single_of_bits(0xff000002), 0xfe800003, STR(__LINE__)); // 0x1.000002p+126 + -0x1.000004p+127 = -0x1.000006p+126
  comp32(single_of_bits(0x81000002) + single_of_bits(0x00800001), 0x80800003, STR(__LINE__)); // -0x1.000004p-125 + 0x1.000002p-126 = -0x1.000006p-126
  comp32(single_of_bits(0x00800001) + single_of_bits(0x81000002), 0x80800003, STR(__LINE__)); // 0x1.000002p-126 + -0x1.000004p-125 = -0x1.000006p-126
  comp32(single_of_bits(0x40000002) + single_of_bits(0xbf800003), 0x3f800001, STR(__LINE__)); // 0x1.000004p+1 + -0x1.000006p+0 = 0x1.000002p+0
  comp32(single_of_bits(0xbf800003) + single_of_bits(0x40000002), 0x3f800001, STR(__LINE__)); // -0x1.000006p+0 + 0x1.000004p+1 = 0x1.000002p+0
  comp32(single_of_bits(0x7e800002) + single_of_bits(0xfe000003), 0x7e000001, STR(__LINE__)); // 0x1.000004p+126 + -0x1.000006p+125 = 0x1.000002p+125
}

void f357(void) {
  comp32(single_of_bits(0xfe000003) + single_of_bits(0x7e800002), 0x7e000001, STR(__LINE__)); // -0x1.000006p+125 + 0x1.000004p+126 = 0x1.000002p+125
  comp32(single_of_bits(0x01800002) + single_of_bits(0x81000003), 0x01000001, STR(__LINE__)); // 0x1.000004p-124 + -0x1.000006p-125 = 0x1.000002p-125
  comp32(single_of_bits(0x81000003) + single_of_bits(0x01800002), 0x01000001, STR(__LINE__)); // -0x1.000006p-125 + 0x1.000004p-124 = 0x1.000002p-125
  comp32(single_of_bits(0xc0000002) + single_of_bits(0x3f800003), 0xbf800001, STR(__LINE__)); // -0x1.000004p+1 + 0x1.000006p+0 = -0x1.000002p+0
  comp32(single_of_bits(0x3f800003) + single_of_bits(0xc0000002), 0xbf800001, STR(__LINE__)); // 0x1.000006p+0 + -0x1.000004p+1 = -0x1.000002p+0
  comp32(single_of_bits(0xfe800002) + single_of_bits(0x7e000003), 0xfe000001, STR(__LINE__)); // -0x1.000004p+126 + 0x1.000006p+125 = -0x1.000002p+125
  comp32(single_of_bits(0x7e000003) + single_of_bits(0xfe800002), 0xfe000001, STR(__LINE__)); // 0x1.000006p+125 + -0x1.000004p+126 = -0x1.000002p+125
  comp32(single_of_bits(0x81800002) + single_of_bits(0x01000003), 0x81000001, STR(__LINE__)); // -0x1.000004p-124 + 0x1.000006p-125 = -0x1.000002p-125
  comp32(single_of_bits(0x01000003) + single_of_bits(0x81800002), 0x81000001, STR(__LINE__)); // 0x1.000006p-125 + -0x1.000004p-124 = -0x1.000002p-125
  comp32(single_of_bits(0x3f800002) + single_of_bits(0xbf800000), 0x34800000, STR(__LINE__)); // 0x1.000004p+0 + -0x1p+0 = 0x1p-22
}

void f358(void) {
  comp32(single_of_bits(0xbf800000) + single_of_bits(0x3f800002), 0x34800000, STR(__LINE__)); // -0x1p+0 + 0x1.000004p+0 = 0x1p-22
  comp32(single_of_bits(0xbf800002) + single_of_bits(0x3f800000), 0xb4800000, STR(__LINE__)); // -0x1.000004p+0 + 0x1p+0 = -0x1p-22
  comp32(single_of_bits(0x3f800000) + single_of_bits(0xbf800002), 0xb4800000, STR(__LINE__)); // 0x1p+0 + -0x1.000004p+0 = -0x1p-22
  comp32(single_of_bits(0x3f800004) + single_of_bits(0xbf800000), 0x35000000, STR(__LINE__)); // 0x1.000008p+0 + -0x1p+0 = 0x1p-21
  comp32(single_of_bits(0xbf800000) + single_of_bits(0x3f800004), 0x35000000, STR(__LINE__)); // -0x1p+0 + 0x1.000008p+0 = 0x1p-21
  comp32(single_of_bits(0xbf800004) + single_of_bits(0x3f800000), 0xb5000000, STR(__LINE__)); // -0x1.000008p+0 + 0x1p+0 = -0x1p-21
  comp32(single_of_bits(0x3f800000) + single_of_bits(0xbf800004), 0xb5000000, STR(__LINE__)); // 0x1p+0 + -0x1.000008p+0 = -0x1p-21
  comp32(single_of_bits(0x3f800008) + single_of_bits(0xbf800000), 0x35800000, STR(__LINE__)); // 0x1.00001p+0 + -0x1p+0 = 0x1p-20
  comp32(single_of_bits(0xbf800000) + single_of_bits(0x3f800008), 0x35800000, STR(__LINE__)); // -0x1p+0 + 0x1.00001p+0 = 0x1p-20
  comp32(single_of_bits(0xbf800008) + single_of_bits(0x3f800000), 0xb5800000, STR(__LINE__)); // -0x1.00001p+0 + 0x1p+0 = -0x1p-20
}

void f359(void) {
  comp32(single_of_bits(0x3f800000) + single_of_bits(0xbf800008), 0xb5800000, STR(__LINE__)); // 0x1p+0 + -0x1.00001p+0 = -0x1p-20
  comp32(single_of_bits(0x41880000) + single_of_bits(0xc1800000), 0x3f800000, STR(__LINE__)); // 0x1.1p+4 + -0x1p+4 = 0x1p+0
  comp32(single_of_bits(0xc1800000) + single_of_bits(0x41880000), 0x3f800000, STR(__LINE__)); // -0x1p+4 + 0x1.1p+4 = 0x1p+0
  comp32(single_of_bits(0xc1880000) + single_of_bits(0x41800000), 0xbf800000, STR(__LINE__)); // -0x1.1p+4 + 0x1p+4 = -0x1p+0
  comp32(single_of_bits(0x41800000) + single_of_bits(0xc1880000), 0xbf800000, STR(__LINE__)); // 0x1p+4 + -0x1.1p+4 = -0x1p+0
  comp32(single_of_bits(0x41800000) + single_of_bits(0xc1880000), 0xbf800000, STR(__LINE__)); // 0x1p+4 + -0x1.1p+4 = -0x1p+0
  comp32(single_of_bits(0xc1880000) + single_of_bits(0x41800000), 0xbf800000, STR(__LINE__)); // -0x1.1p+4 + 0x1p+4 = -0x1p+0
  comp32(single_of_bits(0x41100000) + single_of_bits(0xc1000000), 0x3f800000, STR(__LINE__)); // 0x1.2p+3 + -0x1p+3 = 0x1p+0
  comp32(single_of_bits(0xc1000000) + single_of_bits(0x41100000), 0x3f800000, STR(__LINE__)); // -0x1p+3 + 0x1.2p+3 = 0x1p+0
  comp32(single_of_bits(0xc1100000) + single_of_bits(0x41000000), 0xbf800000, STR(__LINE__)); // -0x1.2p+3 + 0x1p+3 = -0x1p+0
}

void f360(void) {
  comp32(single_of_bits(0x41000000) + single_of_bits(0xc1100000), 0xbf800000, STR(__LINE__)); // 0x1p+3 + -0x1.2p+3 = -0x1p+0
  comp32(single_of_bits(0x40a00000) + single_of_bits(0xc0800000), 0x3f800000, STR(__LINE__)); // 0x1.4p+2 + -0x1p+2 = 0x1p+0
  comp32(single_of_bits(0xc0800000) + single_of_bits(0x40a00000), 0x3f800000, STR(__LINE__)); // -0x1p+2 + 0x1.4p+2 = 0x1p+0
  comp32(single_of_bits(0xc0a00000) + single_of_bits(0x40800000), 0xbf800000, STR(__LINE__)); // -0x1.4p+2 + 0x1p+2 = -0x1p+0
  comp32(single_of_bits(0x40800000) + single_of_bits(0xc0a00000), 0xbf800000, STR(__LINE__)); // 0x1p+2 + -0x1.4p+2 = -0x1p+0
  comp32(single_of_bits(0x40400000) + single_of_bits(0xc0000000), 0x3f800000, STR(__LINE__)); // 0x1.8p+1 + -0x1p+1 = 0x1p+0
  comp32(single_of_bits(0xc0000000) + single_of_bits(0x40400000), 0x3f800000, STR(__LINE__)); // -0x1p+1 + 0x1.8p+1 = 0x1p+0
  comp32(single_of_bits(0xc0400000) + single_of_bits(0x40000000), 0xbf800000, STR(__LINE__)); // -0x1.8p+1 + 0x1p+1 = -0x1p+0
  comp32(single_of_bits(0x40000000) + single_of_bits(0xc0400000), 0xbf800000, STR(__LINE__)); // 0x1p+1 + -0x1.8p+1 = -0x1p+0
  comp32(single_of_bits(0x40000000) + single_of_bits(0x3f800001), 0x40400000, STR(__LINE__)); // 0x1p+1 + 0x1.000002p+0 = 0x1.8p+1
}

void f361(void) {
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x40000000), 0x40400000, STR(__LINE__)); // 0x1.000002p+0 + 0x1p+1 = 0x1.8p+1
  comp32(single_of_bits(0x41200000) + single_of_bits(0x3f800001), 0x41300000, STR(__LINE__)); // 0x1.4p+3 + 0x1.000002p+0 = 0x1.6p+3
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x41200000), 0x41300000, STR(__LINE__)); // 0x1.000002p+0 + 0x1.4p+3 = 0x1.6p+3
  comp32(single_of_bits(0x41980000) + single_of_bits(0x3f800001), 0x41a00000, STR(__LINE__)); // 0x1.3p+4 + 0x1.000002p+0 = 0x1.4p+4
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x41980000), 0x41a00000, STR(__LINE__)); // 0x1.000002p+0 + 0x1.3p+4 = 0x1.4p+4
  comp32(single_of_bits(0x42000000) + single_of_bits(0x3f800001), 0x42040000, STR(__LINE__)); // 0x1p+5 + 0x1.000002p+0 = 0x1.08p+5
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x42000000), 0x42040000, STR(__LINE__)); // 0x1.000002p+0 + 0x1p+5 = 0x1.08p+5
  comp32(single_of_bits(0x42820000) + single_of_bits(0x3f800001), 0x42840000, STR(__LINE__)); // 0x1.04p+6 + 0x1.000002p+0 = 0x1.08p+6
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x42820000), 0x42840000, STR(__LINE__)); // 0x1.000002p+0 + 0x1.04p+6 = 0x1.08p+6
  comp32(single_of_bits(0x43050000) + single_of_bits(0x3f800001), 0x43060000, STR(__LINE__)); // 0x1.0ap+7 + 0x1.000002p+0 = 0x1.0cp+7
}

void f362(void) {
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x43050000), 0x43060000, STR(__LINE__)); // 0x1.000002p+0 + 0x1.0ap+7 = 0x1.0cp+7
  comp32(single_of_bits(0x43820000) + single_of_bits(0x3f800001), 0x43828000, STR(__LINE__)); // 0x1.04p+8 + 0x1.000002p+0 = 0x1.05p+8
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x43820000), 0x43828000, STR(__LINE__)); // 0x1.000002p+0 + 0x1.04p+8 = 0x1.05p+8
  comp32(single_of_bits(0x44054000) + single_of_bits(0x3f800001), 0x44058000, STR(__LINE__)); // 0x1.0a8p+9 + 0x1.000002p+0 = 0x1.0bp+9
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x44054000), 0x44058000, STR(__LINE__)); // 0x1.000002p+0 + 0x1.0a8p+9 = 0x1.0bp+9
  comp32(single_of_bits(0x4480a000) + single_of_bits(0x3f800001), 0x4480c000, STR(__LINE__)); // 0x1.014p+10 + 0x1.000002p+0 = 0x1.018p+10
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x4480a000), 0x4480c000, STR(__LINE__)); // 0x1.000002p+0 + 0x1.014p+10 = 0x1.018p+10
  comp32(single_of_bits(0x45000000) + single_of_bits(0x3f800001), 0x45001000, STR(__LINE__)); // 0x1p+11 + 0x1.000002p+0 = 0x1.002p+11
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x45000000), 0x45001000, STR(__LINE__)); // 0x1.000002p+0 + 0x1p+11 = 0x1.002p+11
  comp32(single_of_bits(0x45800800) + single_of_bits(0x3f800001), 0x45801000, STR(__LINE__)); // 0x1.001p+12 + 0x1.000002p+0 = 0x1.002p+12
}

void f363(void) {
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x45800800), 0x45801000, STR(__LINE__)); // 0x1.000002p+0 + 0x1.001p+12 = 0x1.002p+12
  comp32(single_of_bits(0x46000400) + single_of_bits(0x3f800001), 0x46000800, STR(__LINE__)); // 0x1.0008p+13 + 0x1.000002p+0 = 0x1.001p+13
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x46000400), 0x46000800, STR(__LINE__)); // 0x1.000002p+0 + 0x1.0008p+13 = 0x1.001p+13
  comp32(single_of_bits(0x46800000) + single_of_bits(0x3f800001), 0x46800200, STR(__LINE__)); // 0x1p+14 + 0x1.000002p+0 = 0x1.0004p+14
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x46800000), 0x46800200, STR(__LINE__)); // 0x1.000002p+0 + 0x1p+14 = 0x1.0004p+14
  comp32(single_of_bits(0x47000c00) + single_of_bits(0x3f800001), 0x47000d00, STR(__LINE__)); // 0x1.0018p+15 + 0x1.000002p+0 = 0x1.001ap+15
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x47000c00), 0x47000d00, STR(__LINE__)); // 0x1.000002p+0 + 0x1.0018p+15 = 0x1.001ap+15
  comp32(single_of_bits(0x47800980) + single_of_bits(0x3f800001), 0x47800a00, STR(__LINE__)); // 0x1.0013p+16 + 0x1.000002p+0 = 0x1.0014p+16
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x47800980), 0x47800a00, STR(__LINE__)); // 0x1.000002p+0 + 0x1.0013p+16 = 0x1.0014p+16
  comp32(single_of_bits(0x48000000) + single_of_bits(0x3f800001), 0x48000040, STR(__LINE__)); // 0x1p+17 + 0x1.000002p+0 = 0x1.00008p+17
}

void f364(void) {
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x48000000), 0x48000040, STR(__LINE__)); // 0x1.000002p+0 + 0x1p+17 = 0x1.00008p+17
  comp32(single_of_bits(0x48806b00) + single_of_bits(0x3f800001), 0x48806b20, STR(__LINE__)); // 0x1.00d6p+18 + 0x1.000002p+0 = 0x1.00d64p+18
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x48806b00), 0x48806b20, STR(__LINE__)); // 0x1.000002p+0 + 0x1.00d6p+18 = 0x1.00d64p+18
  comp32(single_of_bits(0x49002c80) + single_of_bits(0x3f800001), 0x49002c90, STR(__LINE__)); // 0x1.0059p+19 + 0x1.000002p+0 = 0x1.00592p+19
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x49002c80), 0x49002c90, STR(__LINE__)); // 0x1.000002p+0 + 0x1.0059p+19 = 0x1.00592p+19
  comp32(single_of_bits(0x49802c80) + single_of_bits(0x3f800001), 0x49802c88, STR(__LINE__)); // 0x1.0059p+20 + 0x1.000002p+0 = 0x1.00591p+20
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x49802c80), 0x49802c88, STR(__LINE__)); // 0x1.000002p+0 + 0x1.0059p+20 = 0x1.00591p+20
  comp32(single_of_bits(0x49ff74e0) + single_of_bits(0x3f800001), 0x49ff74e8, STR(__LINE__)); // 0x1.fee9cp+20 + 0x1.000002p+0 = 0x1.fee9dp+20
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x49ff74e0), 0x49ff74e8, STR(__LINE__)); // 0x1.000002p+0 + 0x1.fee9cp+20 = 0x1.fee9dp+20
  comp32(single_of_bits(0x4a800002) + single_of_bits(0x3f800001), 0x4a800004, STR(__LINE__)); // 0x1.000004p+22 + 0x1.000002p+0 = 0x1.000008p+22
}

void f365(void) {
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x4a800002), 0x4a800004, STR(__LINE__)); // 0x1.000002p+0 + 0x1.000004p+22 = 0x1.000008p+22
  comp32(single_of_bits(0x4b000001) + single_of_bits(0x3f800001), 0x4b000002, STR(__LINE__)); // 0x1.000002p+23 + 0x1.000002p+0 = 0x1.000004p+23
  comp32(single_of_bits(0x3f800001) + single_of_bits(0x4b000001), 0x4b000002, STR(__LINE__)); // 0x1.000002p+0 + 0x1.000002p+23 = 0x1.000004p+23
  comp32(single_of_bits(0x4b800000) + single_of_bits(0x40800001), 0x4b800002, STR(__LINE__)); // 0x1p+24 + 0x1.000002p+2 = 0x1.000004p+24
  comp32(single_of_bits(0x40800001) + single_of_bits(0x4b800000), 0x4b800002, STR(__LINE__)); // 0x1.000002p+2 + 0x1p+24 = 0x1.000004p+24
  comp32(single_of_bits(0x4b800000) + single_of_bits(0x40000001), 0x4b800001, STR(__LINE__)); // 0x1p+24 + 0x1.000002p+1 = 0x1.000002p+24
  comp32(single_of_bits(0x40000001) + single_of_bits(0x4b800000), 0x4b800001, STR(__LINE__)); // 0x1.000002p+1 + 0x1p+24 = 0x1.000002p+24
  comp32(single_of_bits(0xc0000000) + single_of_bits(0xbf800001), 0xc0400000, STR(__LINE__)); // -0x1p+1 + -0x1.000002p+0 = -0x1.8p+1
  comp32(single_of_bits(0xbf800001) + single_of_bits(0xc0000000), 0xc0400000, STR(__LINE__)); // -0x1.000002p+0 + -0x1p+1 = -0x1.8p+1
  comp32(single_of_bits(0xcb800000) + single_of_bits(0xc0800001), 0xcb800002, STR(__LINE__)); // -0x1p+24 + -0x1.000002p+2 = -0x1.000004p+24
}

void f366(void) {
  comp32(single_of_bits(0xc0800001) + single_of_bits(0xcb800000), 0xcb800002, STR(__LINE__)); // -0x1.000002p+2 + -0x1p+24 = -0x1.000004p+24
  comp32(single_of_bits(0xcb800000) + single_of_bits(0xc0000001), 0xcb800001, STR(__LINE__)); // -0x1p+24 + -0x1.000002p+1 = -0x1.000002p+24
  comp32(single_of_bits(0xc0000001) + single_of_bits(0xcb800000), 0xcb800001, STR(__LINE__)); // -0x1.000002p+1 + -0x1p+24 = -0x1.000002p+24
  comp32(single_of_bits(0x46fffe00) + single_of_bits(0x3f800000), 0x47000000, STR(__LINE__)); // 0x1.fffcp+14 + 0x1p+0 = 0x1p+15
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x46fffe00), 0x47000000, STR(__LINE__)); // 0x1p+0 + 0x1.fffcp+14 = 0x1p+15
  comp32(single_of_bits(0xc6fffe00) + single_of_bits(0xbf800000), 0xc7000000, STR(__LINE__)); // -0x1.fffcp+14 + -0x1p+0 = -0x1p+15
  comp32(single_of_bits(0xbf800000) + single_of_bits(0xc6fffe00), 0xc7000000, STR(__LINE__)); // -0x1p+0 + -0x1.fffcp+14 = -0x1p+15
  comp32(single_of_bits(0x4b7fffff) + single_of_bits(0x3f800000), 0x4b800000, STR(__LINE__)); // 0x1.fffffep+23 + 0x1p+0 = 0x1p+24
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x4b7fffff), 0x4b800000, STR(__LINE__)); // 0x1p+0 + 0x1.fffffep+23 = 0x1p+24
  comp32(single_of_bits(0xcb7fffff) + single_of_bits(0xbf800000), 0xcb800000, STR(__LINE__)); // -0x1.fffffep+23 + -0x1p+0 = -0x1p+24
}

void f367(void) {
  comp32(single_of_bits(0xbf800000) + single_of_bits(0xcb7fffff), 0xcb800000, STR(__LINE__)); // -0x1p+0 + -0x1.fffffep+23 = -0x1p+24
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x41700000), 0x41800000, STR(__LINE__)); // 0x1p+0 + 0x1.ep+3 = 0x1p+4
  comp32(single_of_bits(0x41700000) + single_of_bits(0x3f800000), 0x41800000, STR(__LINE__)); // 0x1.ep+3 + 0x1p+0 = 0x1p+4
  comp32(single_of_bits(0xbf800000) + single_of_bits(0xc1700000), 0xc1800000, STR(__LINE__)); // -0x1p+0 + -0x1.ep+3 = -0x1p+4
  comp32(single_of_bits(0xc1700000) + single_of_bits(0xbf800000), 0xc1800000, STR(__LINE__)); // -0x1.ep+3 + -0x1p+0 = -0x1p+4
  comp32(single_of_bits(0x40000000) + single_of_bits(0x4b7ffffb), 0x4b7ffffd, STR(__LINE__)); // 0x1p+1 + 0x1.fffff6p+23 = 0x1.fffffap+23
  comp32(single_of_bits(0x4b7ffffb) + single_of_bits(0x40000000), 0x4b7ffffd, STR(__LINE__)); // 0x1.fffff6p+23 + 0x1p+1 = 0x1.fffffap+23
  comp32(single_of_bits(0xc0000000) + single_of_bits(0xcb7ffffb), 0xcb7ffffd, STR(__LINE__)); // -0x1p+1 + -0x1.fffff6p+23 = -0x1.fffffap+23
  comp32(single_of_bits(0xcb7ffffb) + single_of_bits(0xc0000000), 0xcb7ffffd, STR(__LINE__)); // -0x1.fffff6p+23 + -0x1p+1 = -0x1.fffffap+23
  comp32(single_of_bits(0x007fffff) + single_of_bits(0x00000001), 0x00800000, STR(__LINE__)); // 0x1.fffffcp-127 + 0x1p-149 = 0x1p-126
}

void f368(void) {
  comp32(single_of_bits(0x00000001) + single_of_bits(0x007fffff), 0x00800000, STR(__LINE__)); // 0x1p-149 + 0x1.fffffcp-127 = 0x1p-126
  comp32(single_of_bits(0x807fffff) + single_of_bits(0x80000001), 0x80800000, STR(__LINE__)); // -0x1.fffffcp-127 + -0x1p-149 = -0x1p-126
  comp32(single_of_bits(0x80000001) + single_of_bits(0x807fffff), 0x80800000, STR(__LINE__)); // -0x1p-149 + -0x1.fffffcp-127 = -0x1p-126
  comp32(single_of_bits(0x00700000) + single_of_bits(0x00100000), 0x00800000, STR(__LINE__)); // 0x1.cp-127 + 0x1p-129 = 0x1p-126
  comp32(single_of_bits(0x00100000) + single_of_bits(0x00700000), 0x00800000, STR(__LINE__)); // 0x1p-129 + 0x1.cp-127 = 0x1p-126
  comp32(single_of_bits(0x80700000) + single_of_bits(0x80100000), 0x80800000, STR(__LINE__)); // -0x1.cp-127 + -0x1p-129 = -0x1p-126
  comp32(single_of_bits(0x80100000) + single_of_bits(0x80700000), 0x80800000, STR(__LINE__)); // -0x1p-129 + -0x1.cp-127 = -0x1p-126
  comp32(single_of_bits(0x40000000) + single_of_bits(0x46fffa00), 0x46fffe00, STR(__LINE__)); // 0x1p+1 + 0x1.fff4p+14 = 0x1.fffcp+14
  comp32(single_of_bits(0x46fffa00) + single_of_bits(0x40000000), 0x46fffe00, STR(__LINE__)); // 0x1.fff4p+14 + 0x1p+1 = 0x1.fffcp+14
  comp32(single_of_bits(0xc0000000) + single_of_bits(0xc6fffa00), 0xc6fffe00, STR(__LINE__)); // -0x1p+1 + -0x1.fff4p+14 = -0x1.fffcp+14
}

void f369(void) {
  comp32(single_of_bits(0xc6fffa00) + single_of_bits(0xc0000000), 0xc6fffe00, STR(__LINE__)); // -0x1.fff4p+14 + -0x1p+1 = -0x1.fffcp+14
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x4b7ffffe), 0x4b7fffff, STR(__LINE__)); // 0x1p+0 + 0x1.fffffcp+23 = 0x1.fffffep+23
  comp32(single_of_bits(0x4b7ffffe) + single_of_bits(0x3f800000), 0x4b7fffff, STR(__LINE__)); // 0x1.fffffcp+23 + 0x1p+0 = 0x1.fffffep+23
  comp32(single_of_bits(0xbf800000) + single_of_bits(0xcb7ffffe), 0xcb7fffff, STR(__LINE__)); // -0x1p+0 + -0x1.fffffcp+23 = -0x1.fffffep+23
  comp32(single_of_bits(0xcb7ffffe) + single_of_bits(0xbf800000), 0xcb7fffff, STR(__LINE__)); // -0x1.fffffcp+23 + -0x1p+0 = -0x1.fffffep+23
  comp32(single_of_bits(0x40400000) + single_of_bits(0x4b7ffffa), 0x4b7ffffd, STR(__LINE__)); // 0x1.8p+1 + 0x1.fffff4p+23 = 0x1.fffffap+23
  comp32(single_of_bits(0x4b7ffffa) + single_of_bits(0x40400000), 0x4b7ffffd, STR(__LINE__)); // 0x1.fffff4p+23 + 0x1.8p+1 = 0x1.fffffap+23
  comp32(single_of_bits(0xc0400000) + single_of_bits(0xcb7ffffa), 0xcb7ffffd, STR(__LINE__)); // -0x1.8p+1 + -0x1.fffff4p+23 = -0x1.fffffap+23
  comp32(single_of_bits(0xcb7ffffa) + single_of_bits(0xc0400000), 0xcb7ffffd, STR(__LINE__)); // -0x1.fffff4p+23 + -0x1.8p+1 = -0x1.fffffap+23
  comp32(single_of_bits(0x3f800000) + single_of_bits(0x41600000), 0x41700000, STR(__LINE__)); // 0x1p+0 + 0x1.cp+3 = 0x1.ep+3
}

void f370(void) {
  comp32(single_of_bits(0x41600000) + single_of_bits(0x3f800000), 0x41700000, STR(__LINE__)); // 0x1.cp+3 + 0x1p+0 = 0x1.ep+3
  comp32(single_of_bits(0xbf800000) + single_of_bits(0xc1600000), 0xc1700000, STR(__LINE__)); // -0x1p+0 + -0x1.cp+3 = -0x1.ep+3
  comp32(single_of_bits(0xc1600000) + single_of_bits(0xbf800000), 0xc1700000, STR(__LINE__)); // -0x1.cp+3 + -0x1p+0 = -0x1.ep+3
  comp32(single_of_bits(0x40000000) + single_of_bits(0x41500000), 0x41700000, STR(__LINE__)); // 0x1p+1 + 0x1.ap+3 = 0x1.ep+3
  comp32(single_of_bits(0x41500000) + single_of_bits(0x40000000), 0x41700000, STR(__LINE__)); // 0x1.ap+3 + 0x1p+1 = 0x1.ep+3
  comp32(single_of_bits(0xc0000000) + single_of_bits(0xc1500000), 0xc1700000, STR(__LINE__)); // -0x1p+1 + -0x1.ap+3 = -0x1.ep+3
  comp32(single_of_bits(0xc1500000) + single_of_bits(0xc0000000), 0xc1700000, STR(__LINE__)); // -0x1.ap+3 + -0x1p+1 = -0x1.ep+3
  comp32(single_of_bits(0x007ffffe) + single_of_bits(0x00000001), 0x007fffff, STR(__LINE__)); // 0x1.fffff8p-127 + 0x1p-149 = 0x1.fffffcp-127
  comp32(single_of_bits(0x00000001) + single_of_bits(0x007ffffe), 0x007fffff, STR(__LINE__)); // 0x1p-149 + 0x1.fffff8p-127 = 0x1.fffffcp-127
  comp32(single_of_bits(0x807ffffe) + single_of_bits(0x80000001), 0x807fffff, STR(__LINE__)); // -0x1.fffff8p-127 + -0x1p-149 = -0x1.fffffcp-127
}

void f371(void) {
  comp32(single_of_bits(0x80000001) + single_of_bits(0x807ffffe), 0x807fffff, STR(__LINE__)); // -0x1p-149 + -0x1.fffff8p-127 = -0x1.fffffcp-127
  comp32(single_of_bits(0x00600000) + single_of_bits(0x00100000), 0x00700000, STR(__LINE__)); // 0x1.8p-127 + 0x1p-129 = 0x1.cp-127
  comp32(single_of_bits(0x00100000) + single_of_bits(0x00600000), 0x00700000, STR(__LINE__)); // 0x1p-129 + 0x1.8p-127 = 0x1.cp-127
  comp32(single_of_bits(0x80600000) + single_of_bits(0x80100000), 0x80700000, STR(__LINE__)); // -0x1.8p-127 + -0x1p-129 = -0x1.cp-127
  comp32(single_of_bits(0x80100000) + single_of_bits(0x80600000), 0x80700000, STR(__LINE__)); // -0x1p-129 + -0x1.8p-127 = -0x1.cp-127
  comp32(single_of_bits(0xfeffffff) + single_of_bits(0xbf800000), 0xfeffffff, STR(__LINE__)); // -0x1.fffffep+126 + -0x1p+0 = -0x1.fffffep+126
  comp32(single_of_bits(0xbf800000) + single_of_bits(0xfeffffff), 0xfeffffff, STR(__LINE__)); // -0x1p+0 + -0x1.fffffep+126 = -0x1.fffffep+126
  comp32(single_of_bits(0x47000000) / single_of_bits(0x42000000), 0x44800000, STR(__LINE__)); // 0x1p+15 / 0x1p+5 = 0x1p+10
  comp32(single_of_bits(0xc7000000) / single_of_bits(0xc2000000), 0x44800000, STR(__LINE__)); // -0x1p+15 / -0x1p+5 = 0x1p+10
  comp32(single_of_bits(0x47000000) / single_of_bits(0xc2000000), 0xc4800000, STR(__LINE__)); // 0x1p+15 / -0x1p+5 = -0x1p+10
}

void f372(void) {
  comp32(single_of_bits(0xc7000000) / single_of_bits(0x42000000), 0xc4800000, STR(__LINE__)); // -0x1p+15 / 0x1p+5 = -0x1p+10
  comp32(single_of_bits(0x7b800000) / single_of_bits(0x49800000), 0x71800000, STR(__LINE__)); // 0x1p+120 / 0x1p+20 = 0x1p+100
  comp32(single_of_bits(0xfb800000) / single_of_bits(0xc9800000), 0x71800000, STR(__LINE__)); // -0x1p+120 / -0x1p+20 = 0x1p+100
  comp32(single_of_bits(0xfb800000) / single_of_bits(0x49800000), 0xf1800000, STR(__LINE__)); // -0x1p+120 / 0x1p+20 = -0x1p+100
  comp32(single_of_bits(0x7b800000) / single_of_bits(0xc9800000), 0xf1800000, STR(__LINE__)); // 0x1p+120 / -0x1p+20 = -0x1p+100
  comp32(single_of_bits(0x5f000000) / single_of_bits(0x4b000000), 0x53800000, STR(__LINE__)); // 0x1p+63 / 0x1p+23 = 0x1p+40
  comp32(single_of_bits(0xdf000000) / single_of_bits(0xcb000000), 0x53800000, STR(__LINE__)); // -0x1p+63 / -0x1p+23 = 0x1p+40
  comp32(single_of_bits(0xdf000000) / single_of_bits(0x4b000000), 0xd3800000, STR(__LINE__)); // -0x1p+63 / 0x1p+23 = -0x1p+40
  comp32(single_of_bits(0x5f000000) / single_of_bits(0xcb000000), 0xd3800000, STR(__LINE__)); // 0x1p+63 / -0x1p+23 = -0x1p+40
  comp32(single_of_bits(0x57000000) / single_of_bits(0x46000000), 0x50800000, STR(__LINE__)); // 0x1p+47 / 0x1p+13 = 0x1p+34
}

void f373(void) {
  comp32(single_of_bits(0xd7000000) / single_of_bits(0xc6000000), 0x50800000, STR(__LINE__)); // -0x1p+47 / -0x1p+13 = 0x1p+34
  comp32(single_of_bits(0xd7000000) / single_of_bits(0x46000000), 0xd0800000, STR(__LINE__)); // -0x1p+47 / 0x1p+13 = -0x1p+34
  comp32(single_of_bits(0x57000000) / single_of_bits(0xc6000000), 0xd0800000, STR(__LINE__)); // 0x1p+47 / -0x1p+13 = -0x1p+34
  comp32(single_of_bits(0x42200000) / single_of_bits(0x41200000), 0x40800000, STR(__LINE__)); // 0x1.4p+5 / 0x1.4p+3 = 0x1p+2
  comp32(single_of_bits(0xc2200000) / single_of_bits(0xc1200000), 0x40800000, STR(__LINE__)); // -0x1.4p+5 / -0x1.4p+3 = 0x1p+2
  comp32(single_of_bits(0xc2200000) / single_of_bits(0x41200000), 0xc0800000, STR(__LINE__)); // -0x1.4p+5 / 0x1.4p+3 = -0x1p+2
  comp32(single_of_bits(0x42200000) / single_of_bits(0xc1200000), 0xc0800000, STR(__LINE__)); // 0x1.4p+5 / -0x1.4p+3 = -0x1p+2
  comp32(single_of_bits(0x46fff000) / single_of_bits(0x41200000), 0x454cc000, STR(__LINE__)); // 0x1.ffep+14 / 0x1.4p+3 = 0x1.998p+11
  comp32(single_of_bits(0x461c4000) / single_of_bits(0x41200000), 0x447a0000, STR(__LINE__)); // 0x1.388p+13 / 0x1.4p+3 = 0x1.f4p+9
  comp32(single_of_bits(0x461c4000) / single_of_bits(0x42c80000), 0x42c80000, STR(__LINE__)); // 0x1.388p+13 / 0x1.9p+6 = 0x1.9p+6
}

void f374(void) {
  comp32(single_of_bits(0x461c4000) / single_of_bits(0x447a0000), 0x41200000, STR(__LINE__)); // 0x1.388p+13 / 0x1.f4p+9 = 0x1.4p+3
  comp32(single_of_bits(0x3f800000) / single_of_bits(0x3f800000), 0x3f800000, STR(__LINE__)); // 0x1p+0 / 0x1p+0 = 0x1p+0
  comp32(single_of_bits(0xbf800000) / single_of_bits(0xbf800000), 0x3f800000, STR(__LINE__)); // -0x1p+0 / -0x1p+0 = 0x1p+0
  comp32(single_of_bits(0x3f800000) / single_of_bits(0xbf800000), 0xbf800000, STR(__LINE__)); // 0x1p+0 / -0x1p+0 = -0x1p+0
  comp32(single_of_bits(0xbf800000) / single_of_bits(0x3f800000), 0xbf800000, STR(__LINE__)); // -0x1p+0 / 0x1p+0 = -0x1p+0
  comp32(single_of_bits(0x40000000) / single_of_bits(0x3f800000), 0x40000000, STR(__LINE__)); // 0x1p+1 / 0x1p+0 = 0x1p+1
  comp32(single_of_bits(0xc0000000) / single_of_bits(0xbf800000), 0x40000000, STR(__LINE__)); // -0x1p+1 / -0x1p+0 = 0x1p+1
  comp32(single_of_bits(0xc0000000) / single_of_bits(0x3f800000), 0xc0000000, STR(__LINE__)); // -0x1p+1 / 0x1p+0 = -0x1p+1
  comp32(single_of_bits(0x40000000) / single_of_bits(0xbf800000), 0xc0000000, STR(__LINE__)); // 0x1p+1 / -0x1p+0 = -0x1p+1
  comp32(single_of_bits(0x007fffff) / single_of_bits(0x3f800000), 0x007fffff, STR(__LINE__)); // 0x1.fffffcp-127 / 0x1p+0 = 0x1.fffffcp-127
}

void f375(void) {
  comp32(single_of_bits(0x007fffff) / single_of_bits(0xbf800000), 0x807fffff, STR(__LINE__)); // 0x1.fffffcp-127 / -0x1p+0 = -0x1.fffffcp-127
  comp32(single_of_bits(0x00000001) / single_of_bits(0x3f800000), 0x00000001, STR(__LINE__)); // 0x1p-149 / 0x1p+0 = 0x1p-149
  comp32(single_of_bits(0x80000001) / single_of_bits(0xbf800000), 0x00000001, STR(__LINE__)); // -0x1p-149 / -0x1p+0 = 0x1p-149
  comp32(single_of_bits(0x80000001) / single_of_bits(0x3f800000), 0x80000001, STR(__LINE__)); // -0x1p-149 / 0x1p+0 = -0x1p-149
  comp32(single_of_bits(0x00000001) / single_of_bits(0xbf800000), 0x80000001, STR(__LINE__)); // 0x1p-149 / -0x1p+0 = -0x1p-149
  comp32(single_of_bits(0x7f000000) / single_of_bits(0x40000000), 0x7e800000, STR(__LINE__)); // 0x1p+127 / 0x1p+1 = 0x1p+126
  comp32(single_of_bits(0x7f000000) / single_of_bits(0xc0000000), 0xfe800000, STR(__LINE__)); // 0x1p+127 / -0x1p+1 = -0x1p+126
  comp32(single_of_bits(0xfeffffff) / single_of_bits(0x40000000), 0xfe7fffff, STR(__LINE__)); // -0x1.fffffep+126 / 0x1p+1 = -0x1.fffffep+125
  comp32(single_of_bits(0x7efffffd) / single_of_bits(0xc0000000), 0xfe7ffffd, STR(__LINE__)); // 0x1.fffffap+126 / -0x1p+1 = -0x1.fffffap+125
  comp32(single_of_bits(0x7f7fffff) / single_of_bits(0xc0000000), 0xfeffffff, STR(__LINE__)); // 0x1.fffffep+127 / -0x1p+1 = -0x1.fffffep+126
}

void f376(void) {
  comp32(single_of_bits(0x41000000) / single_of_bits(0x40000000), 0x40800000, STR(__LINE__)); // 0x1p+3 / 0x1p+1 = 0x1p+2
  comp32(single_of_bits(0xc1000000) / single_of_bits(0xc0000000), 0x40800000, STR(__LINE__)); // -0x1p+3 / -0x1p+1 = 0x1p+2
  comp32(single_of_bits(0xc1000000) / single_of_bits(0x40000000), 0xc0800000, STR(__LINE__)); // -0x1p+3 / 0x1p+1 = -0x1p+2
  comp32(single_of_bits(0x41000000) / single_of_bits(0xc0000000), 0xc0800000, STR(__LINE__)); // 0x1p+3 / -0x1p+1 = -0x1p+2
  comp32(single_of_bits(0x01000000) / single_of_bits(0xc0000000), 0x80800000, STR(__LINE__)); // 0x1p-125 / -0x1p+1 = -0x1p-126
  comp32(single_of_bits(0x01000003) / single_of_bits(0xc0000000), 0x80800003, STR(__LINE__)); // 0x1.000006p-125 / -0x1p+1 = -0x1.000006p-126
  comp32(single_of_bits(0x01000001) / single_of_bits(0xc0000000), 0x80800001, STR(__LINE__)); // 0x1.000002p-125 / -0x1p+1 = -0x1.000002p-126
  comp32(single_of_bits(0x00fffffe) / single_of_bits(0x40000000), 0x007fffff, STR(__LINE__)); // 0x1.fffffcp-126 / 0x1p+1 = 0x1.fffffcp-127
  comp32(single_of_bits(0x00400000) / single_of_bits(0x40000000), 0x00200000, STR(__LINE__)); // 0x1p-127 / 0x1p+1 = 0x1p-128
  comp32(single_of_bits(0x80400000) / single_of_bits(0xc0000000), 0x00200000, STR(__LINE__)); // -0x1p-127 / -0x1p+1 = 0x1p-128
}

void f377(void) {
  comp32(single_of_bits(0x80400000) / single_of_bits(0x40000000), 0x80200000, STR(__LINE__)); // -0x1p-127 / 0x1p+1 = -0x1p-128
  comp32(single_of_bits(0x00400000) / single_of_bits(0xc0000000), 0x80200000, STR(__LINE__)); // 0x1p-127 / -0x1p+1 = -0x1p-128
  comp32(single_of_bits(0x00000002) / single_of_bits(0x40000000), 0x00000001, STR(__LINE__)); // 0x1p-148 / 0x1p+1 = 0x1p-149
  comp32(single_of_bits(0x80000002) / single_of_bits(0xc0000000), 0x00000001, STR(__LINE__)); // -0x1p-148 / -0x1p+1 = 0x1p-149
  comp32(single_of_bits(0x80000002) / single_of_bits(0x40000000), 0x80000001, STR(__LINE__)); // -0x1p-148 / 0x1p+1 = -0x1p-149
  comp32(single_of_bits(0x00000002) / single_of_bits(0xc0000000), 0x80000001, STR(__LINE__)); // 0x1p-148 / -0x1p+1 = -0x1p-149
  comp32(single_of_bits(0x7f7fffff) / single_of_bits(0x7effffff), 0x40000000, STR(__LINE__)); // 0x1.fffffep+127 / 0x1.fffffep+126 = 0x1p+1
  comp32(single_of_bits(0xff000001) / single_of_bits(0x7e800001), 0xc0000000, STR(__LINE__)); // -0x1.000002p+127 / 0x1.000002p+126 = -0x1p+1
  comp32(single_of_bits(0x7f000003) / single_of_bits(0xfe800003), 0xc0000000, STR(__LINE__)); // 0x1.000006p+127 / -0x1.000006p+126 = -0x1p+1
  comp32(single_of_bits(0x01000000) / single_of_bits(0x00800000), 0x40000000, STR(__LINE__)); // 0x1p-125 / 0x1p-126 = 0x1p+1
}

void f378(void) {
  comp32(single_of_bits(0x81000001) / single_of_bits(0x00800001), 0xc0000000, STR(__LINE__)); // -0x1.000002p-125 / 0x1.000002p-126 = -0x1p+1
  comp32(single_of_bits(0x01000001) / single_of_bits(0x00800001), 0x40000000, STR(__LINE__)); // 0x1.000002p-125 / 0x1.000002p-126 = 0x1p+1
  comp32(single_of_bits(0x01000003) / single_of_bits(0x80800003), 0xc0000000, STR(__LINE__)); // 0x1.000006p-125 / -0x1.000006p-126 = -0x1p+1
  comp32(single_of_bits(0x81000005) / single_of_bits(0x00800005), 0xc0000000, STR(__LINE__)); // -0x1.00000ap-125 / 0x1.00000ap-126 = -0x1p+1
  comp32(single_of_bits(0x00400000) / single_of_bits(0x00200000), 0x40000000, STR(__LINE__)); // 0x1p-127 / 0x1p-128 = 0x1p+1
  comp32(single_of_bits(0x80400000) / single_of_bits(0x80200000), 0x40000000, STR(__LINE__)); // -0x1p-127 / -0x1p-128 = 0x1p+1
  comp32(single_of_bits(0x80400000) / single_of_bits(0x00200000), 0xc0000000, STR(__LINE__)); // -0x1p-127 / 0x1p-128 = -0x1p+1
  comp32(single_of_bits(0x00400000) / single_of_bits(0x80200000), 0xc0000000, STR(__LINE__)); // 0x1p-127 / -0x1p-128 = -0x1p+1
  comp32(single_of_bits(0x00000002) / single_of_bits(0x00000001), 0x40000000, STR(__LINE__)); // 0x1p-148 / 0x1p-149 = 0x1p+1
  comp32(single_of_bits(0x80000002) / single_of_bits(0x80000001), 0x40000000, STR(__LINE__)); // -0x1p-148 / -0x1p-149 = 0x1p+1
}

void f379(void) {
  comp32(single_of_bits(0x00000002) / single_of_bits(0x80000001), 0xc0000000, STR(__LINE__)); // 0x1p-148 / -0x1p-149 = -0x1p+1
  comp32(single_of_bits(0x80000002) / single_of_bits(0x00000001), 0xc0000000, STR(__LINE__)); // -0x1p-148 / 0x1p-149 = -0x1p+1
  comp32(single_of_bits(0x40400000) / single_of_bits(0x3f000000), 0x40c00000, STR(__LINE__)); // 0x1.8p+1 / 0x1p-1 = 0x1.8p+2
  comp32(single_of_bits(0xc0400000) / single_of_bits(0xbf000000), 0x40c00000, STR(__LINE__)); // -0x1.8p+1 / -0x1p-1 = 0x1.8p+2
  comp32(single_of_bits(0xc0400000) / single_of_bits(0x3f000000), 0xc0c00000, STR(__LINE__)); // -0x1.8p+1 / 0x1p-1 = -0x1.8p+2
  comp32(single_of_bits(0x40400000) / single_of_bits(0xbf000000), 0xc0c00000, STR(__LINE__)); // 0x1.8p+1 / -0x1p-1 = -0x1.8p+2
  comp32(single_of_bits(0x007fffff) / single_of_bits(0x3f000000), 0x00fffffe, STR(__LINE__)); // 0x1.fffffcp-127 / 0x1p-1 = 0x1.fffffcp-126
  comp32(single_of_bits(0x807fffff) / single_of_bits(0xbf000000), 0x00fffffe, STR(__LINE__)); // -0x1.fffffcp-127 / -0x1p-1 = 0x1.fffffcp-126
  comp32(single_of_bits(0x807fffff) / single_of_bits(0x3f000000), 0x80fffffe, STR(__LINE__)); // -0x1.fffffcp-127 / 0x1p-1 = -0x1.fffffcp-126
  comp32(single_of_bits(0x007fffff) / single_of_bits(0xbf000000), 0x80fffffe, STR(__LINE__)); // 0x1.fffffcp-127 / -0x1p-1 = -0x1.fffffcp-126
}

void f380(void) {
  comp32(single_of_bits(0x00000001) / single_of_bits(0x3f000000), 0x00000002, STR(__LINE__)); // 0x1p-149 / 0x1p-1 = 0x1p-148
  comp32(single_of_bits(0x80000001) / single_of_bits(0xbf000000), 0x00000002, STR(__LINE__)); // -0x1p-149 / -0x1p-1 = 0x1p-148
  comp32(single_of_bits(0x80000001) / single_of_bits(0x3f000000), 0x80000002, STR(__LINE__)); // -0x1p-149 / 0x1p-1 = -0x1p-148
  comp32(single_of_bits(0x00000001) / single_of_bits(0xbf000000), 0x80000002, STR(__LINE__)); // 0x1p-149 / -0x1p-1 = -0x1p-148
  comp32(single_of_bits(0x40400000) / single_of_bits(0x40c00000), 0x3f000000, STR(__LINE__)); // 0x1.8p+1 / 0x1.8p+2 = 0x1p-1
  comp32(single_of_bits(0xc0400000) / single_of_bits(0xc0c00000), 0x3f000000, STR(__LINE__)); // -0x1.8p+1 / -0x1.8p+2 = 0x1p-1
  comp32(single_of_bits(0xc0400000) / single_of_bits(0x40c00000), 0xbf000000, STR(__LINE__)); // -0x1.8p+1 / 0x1.8p+2 = -0x1p-1
  comp32(single_of_bits(0x40400000) / single_of_bits(0xc0c00000), 0xbf000000, STR(__LINE__)); // 0x1.8p+1 / -0x1.8p+2 = -0x1p-1
  comp32(single_of_bits(0x007fffff) / single_of_bits(0x00fffffe), 0x3f000000, STR(__LINE__)); // 0x1.fffffcp-127 / 0x1.fffffcp-126 = 0x1p-1
  comp32(single_of_bits(0x807fffff) / single_of_bits(0x80fffffe), 0x3f000000, STR(__LINE__)); // -0x1.fffffcp-127 / -0x1.fffffcp-126 = 0x1p-1
}

void f381(void) {
  comp32(single_of_bits(0x807fffff) / single_of_bits(0x00fffffe), 0xbf000000, STR(__LINE__)); // -0x1.fffffcp-127 / 0x1.fffffcp-126 = -0x1p-1
  comp32(single_of_bits(0x007fffff) / single_of_bits(0x80fffffe), 0xbf000000, STR(__LINE__)); // 0x1.fffffcp-127 / -0x1.fffffcp-126 = -0x1p-1
  comp32(single_of_bits(0x00000001) / single_of_bits(0x00000002), 0x3f000000, STR(__LINE__)); // 0x1p-149 / 0x1p-148 = 0x1p-1
  comp32(single_of_bits(0x80000001) / single_of_bits(0x00000002), 0xbf000000, STR(__LINE__)); // -0x1p-149 / 0x1p-148 = -0x1p-1
  comp32(single_of_bits(0x80000001) / single_of_bits(0x80000002), 0x3f000000, STR(__LINE__)); // -0x1p-149 / -0x1p-148 = 0x1p-1
  comp32(single_of_bits(0x00000001) / single_of_bits(0x80000002), 0xbf000000, STR(__LINE__)); // 0x1p-149 / -0x1p-148 = -0x1p-1
  comp32(single_of_bits(0x40400000) / single_of_bits(0x3b000000), 0x44c00000, STR(__LINE__)); // 0x1.8p+1 / 0x1p-9 = 0x1.8p+10
  comp32(single_of_bits(0xc0400000) / single_of_bits(0xbb000000), 0x44c00000, STR(__LINE__)); // -0x1.8p+1 / -0x1p-9 = 0x1.8p+10
  comp32(single_of_bits(0xc0400000) / single_of_bits(0x3b000000), 0xc4c00000, STR(__LINE__)); // -0x1.8p+1 / 0x1p-9 = -0x1.8p+10
  comp32(single_of_bits(0x40400000) / single_of_bits(0xbb000000), 0xc4c00000, STR(__LINE__)); // 0x1.8p+1 / -0x1p-9 = -0x1.8p+10
}

void f382(void) {
  comp32(single_of_bits(0x007fffff) / single_of_bits(0x3b000000), 0x04fffffe, STR(__LINE__)); // 0x1.fffffcp-127 / 0x1p-9 = 0x1.fffffcp-118
  comp32(single_of_bits(0x807fffff) / single_of_bits(0xbb000000), 0x04fffffe, STR(__LINE__)); // -0x1.fffffcp-127 / -0x1p-9 = 0x1.fffffcp-118
  comp32(single_of_bits(0x807fffff) / single_of_bits(0x3b000000), 0x84fffffe, STR(__LINE__)); // -0x1.fffffcp-127 / 0x1p-9 = -0x1.fffffcp-118
  comp32(single_of_bits(0x007fffff) / single_of_bits(0xbb000000), 0x84fffffe, STR(__LINE__)); // 0x1.fffffcp-127 / -0x1p-9 = -0x1.fffffcp-118
  comp32(single_of_bits(0x00000001) / single_of_bits(0x3e000000), 0x00000008, STR(__LINE__)); // 0x1p-149 / 0x1p-3 = 0x1p-146
  comp32(single_of_bits(0x80000001) / single_of_bits(0xbe000000), 0x00000008, STR(__LINE__)); // -0x1p-149 / -0x1p-3 = 0x1p-146
  comp32(single_of_bits(0x80000001) / single_of_bits(0x3e000000), 0x80000008, STR(__LINE__)); // -0x1p-149 / 0x1p-3 = -0x1p-146
  comp32(single_of_bits(0x00000001) / single_of_bits(0xbe000000), 0x80000008, STR(__LINE__)); // 0x1p-149 / -0x1p-3 = -0x1p-146
  comp32(single_of_bits(0x40400000) / single_of_bits(0x44c00000), 0x3b000000, STR(__LINE__)); // 0x1.8p+1 / 0x1.8p+10 = 0x1p-9
  comp32(single_of_bits(0xc0400000) / single_of_bits(0x44c00000), 0xbb000000, STR(__LINE__)); // -0x1.8p+1 / 0x1.8p+10 = -0x1p-9
}

void f383(void) {
  comp32(single_of_bits(0xc0400000) / single_of_bits(0xc4c00000), 0x3b000000, STR(__LINE__)); // -0x1.8p+1 / -0x1.8p+10 = 0x1p-9
  comp32(single_of_bits(0x40400000) / single_of_bits(0xc4c00000), 0xbb000000, STR(__LINE__)); // 0x1.8p+1 / -0x1.8p+10 = -0x1p-9
  comp32(single_of_bits(0x007fffff) / single_of_bits(0x04fffffe), 0x3b000000, STR(__LINE__)); // 0x1.fffffcp-127 / 0x1.fffffcp-118 = 0x1p-9
  comp32(single_of_bits(0x807fffff) / single_of_bits(0x04fffffe), 0xbb000000, STR(__LINE__)); // -0x1.fffffcp-127 / 0x1.fffffcp-118 = -0x1p-9
  comp32(single_of_bits(0x807fffff) / single_of_bits(0x84fffffe), 0x3b000000, STR(__LINE__)); // -0x1.fffffcp-127 / -0x1.fffffcp-118 = 0x1p-9
  comp32(single_of_bits(0x007fffff) / single_of_bits(0x84fffffe), 0xbb000000, STR(__LINE__)); // 0x1.fffffcp-127 / -0x1.fffffcp-118 = -0x1p-9
  comp32(single_of_bits(0x00000001) / single_of_bits(0x00000008), 0x3e000000, STR(__LINE__)); // 0x1p-149 / 0x1p-146 = 0x1p-3
  comp32(single_of_bits(0x80000001) / single_of_bits(0x00000008), 0xbe000000, STR(__LINE__)); // -0x1p-149 / 0x1p-146 = -0x1p-3
  comp32(single_of_bits(0x80000001) / single_of_bits(0x80000008), 0x3e000000, STR(__LINE__)); // -0x1p-149 / -0x1p-146 = 0x1p-3
  comp32(single_of_bits(0x00000001) / single_of_bits(0x80000008), 0xbe000000, STR(__LINE__)); // 0x1p-149 / -0x1p-146 = -0x1p-3
}

void f384(void) {
  comp32(single_of_bits(0x41100000) / single_of_bits(0x40400000), 0x40400000, STR(__LINE__)); // 0x1.2p+3 / 0x1.8p+1 = 0x1.8p+1
  comp32(single_of_bits(0xc1100000) / single_of_bits(0xc0400000), 0x40400000, STR(__LINE__)); // -0x1.2p+3 / -0x1.8p+1 = 0x1.8p+1
  comp32(single_of_bits(0xc1100000) / single_of_bits(0x40400000), 0xc0400000, STR(__LINE__)); // -0x1.2p+3 / 0x1.8p+1 = -0x1.8p+1
  comp32(single_of_bits(0x41100000) / single_of_bits(0xc0400000), 0xc0400000, STR(__LINE__)); // 0x1.2p+3 / -0x1.8p+1 = -0x1.8p+1
  comp32(single_of_bits(0x40c00000) / single_of_bits(0x40400000), 0x40000000, STR(__LINE__)); // 0x1.8p+2 / 0x1.8p+1 = 0x1p+1
  comp32(single_of_bits(0xc0c00000) / single_of_bits(0xc0400000), 0x40000000, STR(__LINE__)); // -0x1.8p+2 / -0x1.8p+1 = 0x1p+1
  comp32(single_of_bits(0x40c00000) / single_of_bits(0xc0400000), 0xc0000000, STR(__LINE__)); // 0x1.8p+2 / -0x1.8p+1 = -0x1p+1
  comp32(single_of_bits(0xc0c00000) / single_of_bits(0x40400000), 0xc0000000, STR(__LINE__)); // -0x1.8p+2 / 0x1.8p+1 = -0x1p+1
  comp32(single_of_bits(0x7f7ffffd) / single_of_bits(0x40800000), 0x7e7ffffd, STR(__LINE__)); // 0x1.fffffap+127 / 0x1p+2 = 0x1.fffffap+125
  comp32(single_of_bits(0x7f7ffffd) / single_of_bits(0xc0800000), 0xfe7ffffd, STR(__LINE__)); // 0x1.fffffap+127 / -0x1p+2 = -0x1.fffffap+125
}

void f385(void) {
  comp32(single_of_bits(0xff7ffffd) / single_of_bits(0x40800000), 0xfe7ffffd, STR(__LINE__)); // -0x1.fffffap+127 / 0x1p+2 = -0x1.fffffap+125
  comp32(single_of_bits(0xff7ffffd) / single_of_bits(0xc0800000), 0x7e7ffffd, STR(__LINE__)); // -0x1.fffffap+127 / -0x1p+2 = 0x1.fffffap+125
  comp32(single_of_bits(0x00400000) / single_of_bits(0x40800000), 0x00100000, STR(__LINE__)); // 0x1p-127 / 0x1p+2 = 0x1p-129
  comp32(single_of_bits(0x80400000) / single_of_bits(0xc0800000), 0x00100000, STR(__LINE__)); // -0x1p-127 / -0x1p+2 = 0x1p-129
  comp32(single_of_bits(0x80400000) / single_of_bits(0x40800000), 0x80100000, STR(__LINE__)); // -0x1p-127 / 0x1p+2 = -0x1p-129
  comp32(single_of_bits(0x00400000) / single_of_bits(0xc0800000), 0x80100000, STR(__LINE__)); // 0x1p-127 / -0x1p+2 = -0x1p-129
  comp32(single_of_bits(0x00000004) / single_of_bits(0x40800000), 0x00000001, STR(__LINE__)); // 0x1p-147 / 0x1p+2 = 0x1p-149
  comp32(single_of_bits(0x80000004) / single_of_bits(0xc0800000), 0x00000001, STR(__LINE__)); // -0x1p-147 / -0x1p+2 = 0x1p-149
  comp32(single_of_bits(0x80000004) / single_of_bits(0x40800000), 0x80000001, STR(__LINE__)); // -0x1p-147 / 0x1p+2 = -0x1p-149
  comp32(single_of_bits(0x00000004) / single_of_bits(0xc0800000), 0x80000001, STR(__LINE__)); // 0x1p-147 / -0x1p+2 = -0x1p-149
}

void f386(void) {
  comp32(single_of_bits(0x7f7fffff) / single_of_bits(0x7e7fffff), 0x40800000, STR(__LINE__)); // 0x1.fffffep+127 / 0x1.fffffep+125 = 0x1p+2
  comp32(single_of_bits(0xff7fffff) / single_of_bits(0x7e7fffff), 0xc0800000, STR(__LINE__)); // -0x1.fffffep+127 / 0x1.fffffep+125 = -0x1p+2
  comp32(single_of_bits(0x7f7fffff) / single_of_bits(0xfe7fffff), 0xc0800000, STR(__LINE__)); // 0x1.fffffep+127 / -0x1.fffffep+125 = -0x1p+2
  comp32(single_of_bits(0xff7fffff) / single_of_bits(0xfe7fffff), 0x40800000, STR(__LINE__)); // -0x1.fffffep+127 / -0x1.fffffep+125 = 0x1p+2
  comp32(single_of_bits(0x00400000) / single_of_bits(0x00100000), 0x40800000, STR(__LINE__)); // 0x1p-127 / 0x1p-129 = 0x1p+2
  comp32(single_of_bits(0x80400000) / single_of_bits(0x80100000), 0x40800000, STR(__LINE__)); // -0x1p-127 / -0x1p-129 = 0x1p+2
  comp32(single_of_bits(0x80400000) / single_of_bits(0x00100000), 0xc0800000, STR(__LINE__)); // -0x1p-127 / 0x1p-129 = -0x1p+2
  comp32(single_of_bits(0x00400000) / single_of_bits(0x80100000), 0xc0800000, STR(__LINE__)); // 0x1p-127 / -0x1p-129 = -0x1p+2
  comp32(single_of_bits(0x00000004) / single_of_bits(0x00000001), 0x40800000, STR(__LINE__)); // 0x1p-147 / 0x1p-149 = 0x1p+2
  comp32(single_of_bits(0x80000004) / single_of_bits(0x80000001), 0x40800000, STR(__LINE__)); // -0x1p-147 / -0x1p-149 = 0x1p+2
}

void f387(void) {
  comp32(single_of_bits(0x00000004) / single_of_bits(0x80000001), 0xc0800000, STR(__LINE__)); // 0x1p-147 / -0x1p-149 = -0x1p+2
  comp32(single_of_bits(0x80000004) / single_of_bits(0x00000001), 0xc0800000, STR(__LINE__)); // -0x1p-147 / 0x1p-149 = -0x1p+2
  comp32(single_of_bits(0x40a00000) / single_of_bits(0x40a00000), 0x3f800000, STR(__LINE__)); // 0x1.4p+2 / 0x1.4p+2 = 0x1p+0
  comp32(single_of_bits(0xc0a00000) / single_of_bits(0xc0a00000), 0x3f800000, STR(__LINE__)); // -0x1.4p+2 / -0x1.4p+2 = 0x1p+0
  comp32(single_of_bits(0x40a00000) / single_of_bits(0xc0a00000), 0xbf800000, STR(__LINE__)); // 0x1.4p+2 / -0x1.4p+2 = -0x1p+0
  comp32(single_of_bits(0xc0a00000) / single_of_bits(0x40a00000), 0xbf800000, STR(__LINE__)); // -0x1.4p+2 / 0x1.4p+2 = -0x1p+0
  comp32(single_of_bits(0x40400000) / single_of_bits(0x40400000), 0x3f800000, STR(__LINE__)); // 0x1.8p+1 / 0x1.8p+1 = 0x1p+0
  comp32(single_of_bits(0xc0400000) / single_of_bits(0xc0400000), 0x3f800000, STR(__LINE__)); // -0x1.8p+1 / -0x1.8p+1 = 0x1p+0
  comp32(single_of_bits(0xc0400000) / single_of_bits(0x40400000), 0xbf800000, STR(__LINE__)); // -0x1.8p+1 / 0x1.8p+1 = -0x1p+0
  comp32(single_of_bits(0x40400000) / single_of_bits(0xc0400000), 0xbf800000, STR(__LINE__)); // 0x1.8p+1 / -0x1.8p+1 = -0x1p+0
}

void f388(void) {
  comp32(single_of_bits(0x40e00000) / single_of_bits(0x40e00000), 0x3f800000, STR(__LINE__)); // 0x1.cp+2 / 0x1.cp+2 = 0x1p+0
  comp32(single_of_bits(0xc0e00000) / single_of_bits(0xc0e00000), 0x3f800000, STR(__LINE__)); // -0x1.cp+2 / -0x1.cp+2 = 0x1p+0
  comp32(single_of_bits(0x40e00000) / single_of_bits(0xc0e00000), 0xbf800000, STR(__LINE__)); // 0x1.cp+2 / -0x1.cp+2 = -0x1p+0
  comp32(single_of_bits(0xc0e00000) / single_of_bits(0x40e00000), 0xbf800000, STR(__LINE__)); // -0x1.cp+2 / 0x1.cp+2 = -0x1p+0
  comp32(single_of_bits(0x00000001) / single_of_bits(0x00000001), 0x3f800000, STR(__LINE__)); // 0x1p-149 / 0x1p-149 = 0x1p+0
  comp32(single_of_bits(0x80000001) / single_of_bits(0x80000001), 0x3f800000, STR(__LINE__)); // -0x1p-149 / -0x1p-149 = 0x1p+0
  comp32(single_of_bits(0x00000001) / single_of_bits(0x80000001), 0xbf800000, STR(__LINE__)); // 0x1p-149 / -0x1p-149 = -0x1p+0
  comp32(single_of_bits(0x80000001) / single_of_bits(0x00000001), 0xbf800000, STR(__LINE__)); // -0x1p-149 / 0x1p-149 = -0x1p+0
  comp32(single_of_bits(0x00000009) / single_of_bits(0x41100000), 0x00000001, STR(__LINE__)); // 0x1.2p-146 / 0x1.2p+3 = 0x1p-149
  comp32(single_of_bits(0x00000009) / single_of_bits(0xc1100000), 0x80000001, STR(__LINE__)); // 0x1.2p-146 / -0x1.2p+3 = -0x1p-149
}

void f389(void) {
  comp32(single_of_bits(0x00000000) / single_of_bits(0x00000000), 0x7fc00000, STR(__LINE__)); // 0x0p+0 / 0x0p+0 = nan
  comp32(single_of_bits(0x80000000) / single_of_bits(0x00000000), 0xffc00000, STR(__LINE__)); // -0x0p+0 / 0x0p+0 = -nan
  comp32(single_of_bits(0x00000000) / single_of_bits(0x80000000), 0xffc00000, STR(__LINE__)); // 0x0p+0 / -0x0p+0 = -nan
  comp32(single_of_bits(0x80000000) / single_of_bits(0x80000000), 0x7fc00000, STR(__LINE__)); // -0x0p+0 / -0x0p+0 = nan
  comp32(single_of_bits(0x00000000) / single_of_bits(0x00000001), 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x1p-149 = 0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0x00000003), 0x80000000, STR(__LINE__)); // -0x0p+0 / 0x1.8p-148 = -0x0p+0
  comp32(single_of_bits(0x00000000) / single_of_bits(0x80000002), 0x80000000, STR(__LINE__)); // 0x0p+0 / -0x1p-148 = -0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0x80000004), 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x1p-147 = 0x0p+0
  comp32(single_of_bits(0x00000000) / single_of_bits(0x007fffff), 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x1.fffffcp-127 = 0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0x007fffff), 0x80000000, STR(__LINE__)); // -0x0p+0 / 0x1.fffffcp-127 = -0x0p+0
}

void f390(void) {
  comp32(single_of_bits(0x00000000) / single_of_bits(0x807fffff), 0x80000000, STR(__LINE__)); // 0x0p+0 / -0x1.fffffcp-127 = -0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0x807fffff), 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x1.fffffcp-127 = 0x0p+0
  comp32(single_of_bits(0x00000001) / single_of_bits(0x00000000), 0x7f800000, STR(__LINE__)); // 0x1p-149 / 0x0p+0 = inf
  comp32(single_of_bits(0x80000003) / single_of_bits(0x00000000), 0xff800000, STR(__LINE__)); // -0x1.8p-148 / 0x0p+0 = -inf
  comp32(single_of_bits(0x00000002) / single_of_bits(0x80000000), 0xff800000, STR(__LINE__)); // 0x1p-148 / -0x0p+0 = -inf
  comp32(single_of_bits(0x80000004) / single_of_bits(0x80000000), 0x7f800000, STR(__LINE__)); // -0x1p-147 / -0x0p+0 = inf
  comp32(single_of_bits(0x007fffff) / single_of_bits(0x00000000), 0x7f800000, STR(__LINE__)); // 0x1.fffffcp-127 / 0x0p+0 = inf
  comp32(single_of_bits(0x807fffff) / single_of_bits(0x00000000), 0xff800000, STR(__LINE__)); // -0x1.fffffcp-127 / 0x0p+0 = -inf
  comp32(single_of_bits(0x007fffff) / single_of_bits(0x80000000), 0xff800000, STR(__LINE__)); // 0x1.fffffcp-127 / -0x0p+0 = -inf
  comp32(single_of_bits(0x807fffff) / single_of_bits(0x80000000), 0x7f800000, STR(__LINE__)); // -0x1.fffffcp-127 / -0x0p+0 = inf
}

void f391(void) {
  comp32(single_of_bits(0x00000000) / single_of_bits(0x3f800000), 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x1p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0x40000000), 0x80000000, STR(__LINE__)); // -0x0p+0 / 0x1p+1 = -0x0p+0
  comp32(single_of_bits(0x00000000) / single_of_bits(0xc0400000), 0x80000000, STR(__LINE__)); // 0x0p+0 / -0x1.8p+1 = -0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0xc0800000), 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x1p+2 = 0x0p+0
  comp32(single_of_bits(0x00000000) / single_of_bits(0x40a00000), 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x1.4p+2 = 0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0x40c00000), 0x80000000, STR(__LINE__)); // -0x0p+0 / 0x1.8p+2 = -0x0p+0
  comp32(single_of_bits(0x00000000) / single_of_bits(0xc0e00000), 0x80000000, STR(__LINE__)); // 0x0p+0 / -0x1.cp+2 = -0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0xc1000000), 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x1p+3 = 0x0p+0
  comp32(single_of_bits(0x3f800000) / single_of_bits(0x00000000), 0x7f800000, STR(__LINE__)); // 0x1p+0 / 0x0p+0 = inf
  comp32(single_of_bits(0xc0000000) / single_of_bits(0x00000000), 0xff800000, STR(__LINE__)); // -0x1p+1 / 0x0p+0 = -inf
}

void f392(void) {
  comp32(single_of_bits(0x40400000) / single_of_bits(0x80000000), 0xff800000, STR(__LINE__)); // 0x1.8p+1 / -0x0p+0 = -inf
  comp32(single_of_bits(0xc0800000) / single_of_bits(0x80000000), 0x7f800000, STR(__LINE__)); // -0x1p+2 / -0x0p+0 = inf
  comp32(single_of_bits(0x40a00000) / single_of_bits(0x00000000), 0x7f800000, STR(__LINE__)); // 0x1.4p+2 / 0x0p+0 = inf
  comp32(single_of_bits(0xc0c00000) / single_of_bits(0x00000000), 0xff800000, STR(__LINE__)); // -0x1.8p+2 / 0x0p+0 = -inf
  comp32(single_of_bits(0x40e00000) / single_of_bits(0x80000000), 0xff800000, STR(__LINE__)); // 0x1.cp+2 / -0x0p+0 = -inf
  comp32(single_of_bits(0xc1000000) / single_of_bits(0x80000000), 0x7f800000, STR(__LINE__)); // -0x1p+3 / -0x0p+0 = inf
  comp32(single_of_bits(0x00000000) / single_of_bits(0x7f000000), 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x1p+127 = 0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0x7e800000), 0x80000000, STR(__LINE__)); // -0x0p+0 / 0x1p+126 = -0x0p+0
  comp32(single_of_bits(0x00000000) / single_of_bits(0xff000000), 0x80000000, STR(__LINE__)); // 0x0p+0 / -0x1p+127 = -0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0xfe800000), 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x1p+126 = 0x0p+0
}

void f393(void) {
  comp32(single_of_bits(0x00000000) / single_of_bits(0x7effffff), 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x1.fffffep+126 = 0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0x7e7fffff), 0x80000000, STR(__LINE__)); // -0x0p+0 / 0x1.fffffep+125 = -0x0p+0
  comp32(single_of_bits(0x00000000) / single_of_bits(0xfe7fffff), 0x80000000, STR(__LINE__)); // 0x0p+0 / -0x1.fffffep+125 = -0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0xfeffffff), 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x1.fffffep+126 = 0x0p+0
  comp32(single_of_bits(0x7f000000) / single_of_bits(0x00000000), 0x7f800000, STR(__LINE__)); // 0x1p+127 / 0x0p+0 = inf
  comp32(single_of_bits(0xfe800000) / single_of_bits(0x00000000), 0xff800000, STR(__LINE__)); // -0x1p+126 / 0x0p+0 = -inf
  comp32(single_of_bits(0x7f000000) / single_of_bits(0x80000000), 0xff800000, STR(__LINE__)); // 0x1p+127 / -0x0p+0 = -inf
  comp32(single_of_bits(0xfe800000) / single_of_bits(0x80000000), 0x7f800000, STR(__LINE__)); // -0x1p+126 / -0x0p+0 = inf
  comp32(single_of_bits(0x7effffff) / single_of_bits(0x00000000), 0x7f800000, STR(__LINE__)); // 0x1.fffffep+126 / 0x0p+0 = inf
  comp32(single_of_bits(0xfe7fffff) / single_of_bits(0x00000000), 0xff800000, STR(__LINE__)); // -0x1.fffffep+125 / 0x0p+0 = -inf
}

void f394(void) {
  comp32(single_of_bits(0x7e7fffff) / single_of_bits(0x80000000), 0xff800000, STR(__LINE__)); // 0x1.fffffep+125 / -0x0p+0 = -inf
  comp32(single_of_bits(0xfeffffff) / single_of_bits(0x80000000), 0x7f800000, STR(__LINE__)); // -0x1.fffffep+126 / -0x0p+0 = inf
  comp32(single_of_bits(0x00000000) / single_of_bits(0x00800000), 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x1p-126 = 0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0x01000000), 0x80000000, STR(__LINE__)); // -0x0p+0 / 0x1p-125 = -0x0p+0
  comp32(single_of_bits(0x00000000) / single_of_bits(0x81000000), 0x80000000, STR(__LINE__)); // 0x0p+0 / -0x1p-125 = -0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0x80800000), 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x1p-126 = 0x0p+0
  comp32(single_of_bits(0x00000000) / single_of_bits(0x00ffffff), 0x00000000, STR(__LINE__)); // 0x0p+0 / 0x1.fffffep-126 = 0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0x00800001), 0x80000000, STR(__LINE__)); // -0x0p+0 / 0x1.000002p-126 = -0x0p+0
  comp32(single_of_bits(0x00000000) / single_of_bits(0x80800001), 0x80000000, STR(__LINE__)); // 0x0p+0 / -0x1.000002p-126 = -0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0x80ffffff), 0x00000000, STR(__LINE__)); // -0x0p+0 / -0x1.fffffep-126 = 0x0p+0
}

void f395(void) {
  comp32(single_of_bits(0x00800000) / single_of_bits(0x00000000), 0x7f800000, STR(__LINE__)); // 0x1p-126 / 0x0p+0 = inf
  comp32(single_of_bits(0x81000000) / single_of_bits(0x00000000), 0xff800000, STR(__LINE__)); // -0x1p-125 / 0x0p+0 = -inf
  comp32(single_of_bits(0x01000000) / single_of_bits(0x80000000), 0xff800000, STR(__LINE__)); // 0x1p-125 / -0x0p+0 = -inf
  comp32(single_of_bits(0x80800000) / single_of_bits(0x80000000), 0x7f800000, STR(__LINE__)); // -0x1p-126 / -0x0p+0 = inf
  comp32(single_of_bits(0x00ffffff) / single_of_bits(0x00000000), 0x7f800000, STR(__LINE__)); // 0x1.fffffep-126 / 0x0p+0 = inf
  comp32(single_of_bits(0x80800001) / single_of_bits(0x00000000), 0xff800000, STR(__LINE__)); // -0x1.000002p-126 / 0x0p+0 = -inf
  comp32(single_of_bits(0x00800001) / single_of_bits(0x80000000), 0xff800000, STR(__LINE__)); // 0x1.000002p-126 / -0x0p+0 = -inf
  comp32(single_of_bits(0x80ffffff) / single_of_bits(0x80000000), 0x7f800000, STR(__LINE__)); // -0x1.fffffep-126 / -0x0p+0 = inf
  comp32(single_of_bits(0x7f800000) / single_of_bits(0x00000000), 0x7f800000, STR(__LINE__)); // inf / 0x0p+0 = inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0x00000000), 0xff800000, STR(__LINE__)); // -inf / 0x0p+0 = -inf
}

void f396(void) {
  comp32(single_of_bits(0x7f800000) / single_of_bits(0x80000000), 0xff800000, STR(__LINE__)); // inf / -0x0p+0 = -inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0x80000000), 0x7f800000, STR(__LINE__)); // -inf / -0x0p+0 = inf
  comp32(single_of_bits(0x00000000) / single_of_bits(0x7f800000), 0x00000000, STR(__LINE__)); // 0x0p+0 / inf = 0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0x7f800000), 0x80000000, STR(__LINE__)); // -0x0p+0 / inf = -0x0p+0
  comp32(single_of_bits(0x00000000) / single_of_bits(0xff800000), 0x80000000, STR(__LINE__)); // 0x0p+0 / -inf = -0x0p+0
  comp32(single_of_bits(0x80000000) / single_of_bits(0xff800000), 0x00000000, STR(__LINE__)); // -0x0p+0 / -inf = 0x0p+0
  comp32(single_of_bits(0x7fc00000) / single_of_bits(0x00000000), 0x7fc00000, STR(__LINE__)); // nan / 0x0p+0 = nan
  comp32(single_of_bits(0x7fc00000) / single_of_bits(0x80000000), 0x7fc00000, STR(__LINE__)); // nan / -0x0p+0 = nan
  comp32(single_of_bits(0x00000000) / single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // 0x0p+0 / nan = nan
  comp32(single_of_bits(0x80000000) / single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -0x0p+0 / nan = nan
}

void f397(void) {
  comp32(single_of_bits(0x7f800000) / single_of_bits(0x7f800000), 0x7fc00000, STR(__LINE__)); // inf / inf = nan
  comp32(single_of_bits(0xff800000) / single_of_bits(0x7f800000), 0xffc00000, STR(__LINE__)); // -inf / inf = -nan
  comp32(single_of_bits(0x7f800000) / single_of_bits(0xff800000), 0xffc00000, STR(__LINE__)); // inf / -inf = -nan
  comp32(single_of_bits(0xff800000) / single_of_bits(0xff800000), 0x7fc00000, STR(__LINE__)); // -inf / -inf = nan
  comp32(single_of_bits(0x7f800000) / single_of_bits(0x00000001), 0x7f800000, STR(__LINE__)); // inf / 0x1p-149 = inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0x00000003), 0xff800000, STR(__LINE__)); // -inf / 0x1.8p-148 = -inf
  comp32(single_of_bits(0x7f800000) / single_of_bits(0x80000002), 0xff800000, STR(__LINE__)); // inf / -0x1p-148 = -inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0x80000004), 0x7f800000, STR(__LINE__)); // -inf / -0x1p-147 = inf
  comp32(single_of_bits(0x7f800000) / single_of_bits(0x007fffff), 0x7f800000, STR(__LINE__)); // inf / 0x1.fffffcp-127 = inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0x007fffff), 0xff800000, STR(__LINE__)); // -inf / 0x1.fffffcp-127 = -inf
}

void f398(void) {
  comp32(single_of_bits(0x7f800000) / single_of_bits(0x807fffff), 0xff800000, STR(__LINE__)); // inf / -0x1.fffffcp-127 = -inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0x807fffff), 0x7f800000, STR(__LINE__)); // -inf / -0x1.fffffcp-127 = inf
  comp32(single_of_bits(0x00000001) / single_of_bits(0x7f800000), 0x00000000, STR(__LINE__)); // 0x1p-149 / inf = 0x0p+0
  comp32(single_of_bits(0x80000003) / single_of_bits(0x7f800000), 0x80000000, STR(__LINE__)); // -0x1.8p-148 / inf = -0x0p+0
  comp32(single_of_bits(0x00000002) / single_of_bits(0xff800000), 0x80000000, STR(__LINE__)); // 0x1p-148 / -inf = -0x0p+0
  comp32(single_of_bits(0x80000004) / single_of_bits(0xff800000), 0x00000000, STR(__LINE__)); // -0x1p-147 / -inf = 0x0p+0
  comp32(single_of_bits(0x007fffff) / single_of_bits(0x7f800000), 0x00000000, STR(__LINE__)); // 0x1.fffffcp-127 / inf = 0x0p+0
  comp32(single_of_bits(0x807fffff) / single_of_bits(0x7f800000), 0x80000000, STR(__LINE__)); // -0x1.fffffcp-127 / inf = -0x0p+0
  comp32(single_of_bits(0x007fffff) / single_of_bits(0xff800000), 0x80000000, STR(__LINE__)); // 0x1.fffffcp-127 / -inf = -0x0p+0
  comp32(single_of_bits(0x807fffff) / single_of_bits(0xff800000), 0x00000000, STR(__LINE__)); // -0x1.fffffcp-127 / -inf = 0x0p+0
}

void f399(void) {
  comp32(single_of_bits(0x7f800000) / single_of_bits(0x3f800000), 0x7f800000, STR(__LINE__)); // inf / 0x1p+0 = inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0x40000000), 0xff800000, STR(__LINE__)); // -inf / 0x1p+1 = -inf
  comp32(single_of_bits(0x7f800000) / single_of_bits(0xc0400000), 0xff800000, STR(__LINE__)); // inf / -0x1.8p+1 = -inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0xc0800000), 0x7f800000, STR(__LINE__)); // -inf / -0x1p+2 = inf
  comp32(single_of_bits(0x7f800000) / single_of_bits(0x40a00000), 0x7f800000, STR(__LINE__)); // inf / 0x1.4p+2 = inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0x40c00000), 0xff800000, STR(__LINE__)); // -inf / 0x1.8p+2 = -inf
  comp32(single_of_bits(0x7f800000) / single_of_bits(0xc0e00000), 0xff800000, STR(__LINE__)); // inf / -0x1.cp+2 = -inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0xc1000000), 0x7f800000, STR(__LINE__)); // -inf / -0x1p+3 = inf
  comp32(single_of_bits(0x3f800000) / single_of_bits(0x7f800000), 0x00000000, STR(__LINE__)); // 0x1p+0 / inf = 0x0p+0
  comp32(single_of_bits(0xc0000000) / single_of_bits(0x7f800000), 0x80000000, STR(__LINE__)); // -0x1p+1 / inf = -0x0p+0
}

void f400(void) {
  comp32(single_of_bits(0x40400000) / single_of_bits(0xff800000), 0x80000000, STR(__LINE__)); // 0x1.8p+1 / -inf = -0x0p+0
  comp32(single_of_bits(0xc0800000) / single_of_bits(0xff800000), 0x00000000, STR(__LINE__)); // -0x1p+2 / -inf = 0x0p+0
  comp32(single_of_bits(0x40a00000) / single_of_bits(0x7f800000), 0x00000000, STR(__LINE__)); // 0x1.4p+2 / inf = 0x0p+0
  comp32(single_of_bits(0xc0c00000) / single_of_bits(0x7f800000), 0x80000000, STR(__LINE__)); // -0x1.8p+2 / inf = -0x0p+0
  comp32(single_of_bits(0x40e00000) / single_of_bits(0xff800000), 0x80000000, STR(__LINE__)); // 0x1.cp+2 / -inf = -0x0p+0
  comp32(single_of_bits(0xc1000000) / single_of_bits(0xff800000), 0x00000000, STR(__LINE__)); // -0x1p+3 / -inf = 0x0p+0
  comp32(single_of_bits(0x7f000000) / single_of_bits(0x7f800000), 0x00000000, STR(__LINE__)); // 0x1p+127 / inf = 0x0p+0
  comp32(single_of_bits(0xfe800000) / single_of_bits(0x7f800000), 0x80000000, STR(__LINE__)); // -0x1p+126 / inf = -0x0p+0
  comp32(single_of_bits(0x7f000000) / single_of_bits(0xff800000), 0x80000000, STR(__LINE__)); // 0x1p+127 / -inf = -0x0p+0
  comp32(single_of_bits(0xfe800000) / single_of_bits(0xff800000), 0x00000000, STR(__LINE__)); // -0x1p+126 / -inf = 0x0p+0
}

void f401(void) {
  comp32(single_of_bits(0x7effffff) / single_of_bits(0x7f800000), 0x00000000, STR(__LINE__)); // 0x1.fffffep+126 / inf = 0x0p+0
  comp32(single_of_bits(0xfe7fffff) / single_of_bits(0x7f800000), 0x80000000, STR(__LINE__)); // -0x1.fffffep+125 / inf = -0x0p+0
  comp32(single_of_bits(0x7f7fffff) / single_of_bits(0xff800000), 0x80000000, STR(__LINE__)); // 0x1.fffffep+127 / -inf = -0x0p+0
  comp32(single_of_bits(0xff7fffff) / single_of_bits(0xff800000), 0x00000000, STR(__LINE__)); // -0x1.fffffep+127 / -inf = 0x0p+0
  comp32(single_of_bits(0x7f800000) / single_of_bits(0x7f000000), 0x7f800000, STR(__LINE__)); // inf / 0x1p+127 = inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0x7e800000), 0xff800000, STR(__LINE__)); // -inf / 0x1p+126 = -inf
  comp32(single_of_bits(0x7f800000) / single_of_bits(0xff000000), 0xff800000, STR(__LINE__)); // inf / -0x1p+127 = -inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0xfe800000), 0x7f800000, STR(__LINE__)); // -inf / -0x1p+126 = inf
  comp32(single_of_bits(0x7f800000) / single_of_bits(0x7effffff), 0x7f800000, STR(__LINE__)); // inf / 0x1.fffffep+126 = inf
  comp32(single_of_bits(0x7f800000) / single_of_bits(0xfe7fffff), 0xff800000, STR(__LINE__)); // inf / -0x1.fffffep+125 = -inf
}

void f402(void) {
  comp32(single_of_bits(0x7f800000) / single_of_bits(0xff7fffff), 0xff800000, STR(__LINE__)); // inf / -0x1.fffffep+127 = -inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0xff7fffff), 0x7f800000, STR(__LINE__)); // -inf / -0x1.fffffep+127 = inf
  comp32(single_of_bits(0x7f800000) / single_of_bits(0x00800000), 0x7f800000, STR(__LINE__)); // inf / 0x1p-126 = inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0x01000000), 0xff800000, STR(__LINE__)); // -inf / 0x1p-125 = -inf
  comp32(single_of_bits(0x7f800000) / single_of_bits(0x81000000), 0xff800000, STR(__LINE__)); // inf / -0x1p-125 = -inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0x80800000), 0x7f800000, STR(__LINE__)); // -inf / -0x1p-126 = inf
  comp32(single_of_bits(0x7f800000) / single_of_bits(0x00ffffff), 0x7f800000, STR(__LINE__)); // inf / 0x1.fffffep-126 = inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0x00800001), 0xff800000, STR(__LINE__)); // -inf / 0x1.000002p-126 = -inf
  comp32(single_of_bits(0x7f800000) / single_of_bits(0x80800001), 0xff800000, STR(__LINE__)); // inf / -0x1.000002p-126 = -inf
  comp32(single_of_bits(0xff800000) / single_of_bits(0x80ffffff), 0x7f800000, STR(__LINE__)); // -inf / -0x1.fffffep-126 = inf
}

void f403(void) {
  comp32(single_of_bits(0x00800000) / single_of_bits(0x7f800000), 0x00000000, STR(__LINE__)); // 0x1p-126 / inf = 0x0p+0
  comp32(single_of_bits(0x81000000) / single_of_bits(0x7f800000), 0x80000000, STR(__LINE__)); // -0x1p-125 / inf = -0x0p+0
  comp32(single_of_bits(0x01000000) / single_of_bits(0xff800000), 0x80000000, STR(__LINE__)); // 0x1p-125 / -inf = -0x0p+0
  comp32(single_of_bits(0x80800000) / single_of_bits(0xff800000), 0x00000000, STR(__LINE__)); // -0x1p-126 / -inf = 0x0p+0
  comp32(single_of_bits(0x00ffffff) / single_of_bits(0x7f800000), 0x00000000, STR(__LINE__)); // 0x1.fffffep-126 / inf = 0x0p+0
  comp32(single_of_bits(0x80800001) / single_of_bits(0x7f800000), 0x80000000, STR(__LINE__)); // -0x1.000002p-126 / inf = -0x0p+0
  comp32(single_of_bits(0x00800001) / single_of_bits(0xff800000), 0x80000000, STR(__LINE__)); // 0x1.000002p-126 / -inf = -0x0p+0
  comp32(single_of_bits(0x80ffffff) / single_of_bits(0xff800000), 0x00000000, STR(__LINE__)); // -0x1.fffffep-126 / -inf = 0x0p+0
  comp32(single_of_bits(0x7fc00000) / single_of_bits(0x7f800000), 0x7fc00000, STR(__LINE__)); // nan / inf = nan
  comp32(single_of_bits(0x7fc00000) / single_of_bits(0xff800000), 0x7fc00000, STR(__LINE__)); // nan / -inf = nan
}

void f404(void) {
  comp32(single_of_bits(0x7f800000) / single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // inf / nan = nan
  comp32(single_of_bits(0xff800000) / single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -inf / nan = nan
  comp32(single_of_bits(0x7fc00000) / single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // nan / nan = nan
  comp32(single_of_bits(0x007fffff) / single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // 0x1.fffffcp-127 / nan = nan
  comp32(single_of_bits(0x807fffff) / single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -0x1.fffffcp-127 / nan = nan
  comp32(single_of_bits(0x7fc00000) / single_of_bits(0x007fffff), 0x7fc00000, STR(__LINE__)); // nan / 0x1.fffffcp-127 = nan
  comp32(single_of_bits(0x7fc00000) / single_of_bits(0x807fffff), 0x7fc00000, STR(__LINE__)); // nan / -0x1.fffffcp-127 = nan
  comp32(single_of_bits(0x7fc00000) / single_of_bits(0x00000001), 0x7fc00000, STR(__LINE__)); // nan / 0x1p-149 = nan
  comp32(single_of_bits(0x7fc00000) / single_of_bits(0x80000001), 0x7fc00000, STR(__LINE__)); // nan / -0x1p-149 = nan
  comp32(single_of_bits(0x00000001) / single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // 0x1p-149 / nan = nan
}

void f405(void) {
  comp32(single_of_bits(0x80000001) / single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -0x1p-149 / nan = nan
  comp32(single_of_bits(0x7fc00000) / single_of_bits(0x3f800000), 0x7fc00000, STR(__LINE__)); // nan / 0x1p+0 = nan
  comp32(single_of_bits(0x7fc00000) / single_of_bits(0xbf800000), 0x7fc00000, STR(__LINE__)); // nan / -0x1p+0 = nan
  comp32(single_of_bits(0x3f800000) / single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // 0x1p+0 / nan = nan
  comp32(single_of_bits(0xbf800000) / single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -0x1p+0 / nan = nan
  comp32(single_of_bits(0x7fc00000) / single_of_bits(0x7f7fffff), 0x7fc00000, STR(__LINE__)); // nan / 0x1.fffffep+127 = nan
  comp32(single_of_bits(0x7fc00000) / single_of_bits(0xff7fffff), 0x7fc00000, STR(__LINE__)); // nan / -0x1.fffffep+127 = nan
  comp32(single_of_bits(0x7f7fffff) / single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // 0x1.fffffep+127 / nan = nan
  comp32(single_of_bits(0xff7fffff) / single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -0x1.fffffep+127 / nan = nan
  comp32(single_of_bits(0x7f000000) / single_of_bits(0x3f000000), 0x7f800000, STR(__LINE__)); // 0x1p+127 / 0x1p-1 = inf
}

void f406(void) {
  comp32(single_of_bits(0xff000000) / single_of_bits(0xbf000000), 0x7f800000, STR(__LINE__)); // -0x1p+127 / -0x1p-1 = inf
  comp32(single_of_bits(0x7f000000) / single_of_bits(0xbf000000), 0xff800000, STR(__LINE__)); // 0x1p+127 / -0x1p-1 = -inf
  comp32(single_of_bits(0xff000000) / single_of_bits(0x3f000000), 0xff800000, STR(__LINE__)); // -0x1p+127 / 0x1p-1 = -inf
  comp32(single_of_bits(0x7b000000) / single_of_bits(0x05000000), 0x7f800000, STR(__LINE__)); // 0x1p+119 / 0x1p-117 = inf
  comp32(single_of_bits(0x7f7fffff) / single_of_bits(0x00000001), 0x7f800000, STR(__LINE__)); // 0x1.fffffep+127 / 0x1p-149 = inf
  comp32(single_of_bits(0x7f000000) / single_of_bits(0x007fffff), 0x7f800000, STR(__LINE__)); // 0x1p+127 / 0x1.fffffcp-127 = inf
  comp32(single_of_bits(0x7f7fffff) / single_of_bits(0x3f7fffff), 0x7f800000, STR(__LINE__)); // 0x1.fffffep+127 / 0x1.fffffep-1 = inf
  comp32(single_of_bits(0x00800000) / single_of_bits(0x4c000000), 0x00000000, STR(__LINE__)); // 0x1p-126 / 0x1p+25 = 0x0p+0
  comp32(single_of_bits(0x80800000) / single_of_bits(0xcc000000), 0x00000000, STR(__LINE__)); // -0x1p-126 / -0x1p+25 = 0x0p+0
  comp32(single_of_bits(0x00800000) / single_of_bits(0xcc000000), 0x80000000, STR(__LINE__)); // 0x1p-126 / -0x1p+25 = -0x0p+0
}

void f407(void) {
  comp32(single_of_bits(0x80800000) / single_of_bits(0x4c000000), 0x80000000, STR(__LINE__)); // -0x1p-126 / 0x1p+25 = -0x0p+0
  comp32(single_of_bits(0x00000001) / single_of_bits(0x40800000), 0x00000000, STR(__LINE__)); // 0x1p-149 / 0x1p+2 = 0x0p+0
  comp32(single_of_bits(0x80000001) / single_of_bits(0xc0800000), 0x00000000, STR(__LINE__)); // -0x1p-149 / -0x1p+2 = 0x0p+0
  comp32(single_of_bits(0x00000001) / single_of_bits(0xc0800000), 0x80000000, STR(__LINE__)); // 0x1p-149 / -0x1p+2 = -0x0p+0
  comp32(single_of_bits(0x80000001) / single_of_bits(0x40800000), 0x80000000, STR(__LINE__)); // -0x1p-149 / 0x1p+2 = -0x0p+0
  comp32(single_of_bits(0x00000001) / single_of_bits(0x7f7fffff), 0x00000000, STR(__LINE__)); // 0x1p-149 / 0x1.fffffep+127 = 0x0p+0
  comp32(single_of_bits(0x80000001) / single_of_bits(0xff7fffff), 0x00000000, STR(__LINE__)); // -0x1p-149 / -0x1.fffffep+127 = 0x0p+0
  comp32(single_of_bits(0x00000001) / single_of_bits(0xff7fffff), 0x80000000, STR(__LINE__)); // 0x1p-149 / -0x1.fffffep+127 = -0x0p+0
  comp32(single_of_bits(0x80000001) / single_of_bits(0x7f7fffff), 0x80000000, STR(__LINE__)); // -0x1p-149 / 0x1.fffffep+127 = -0x0p+0
  comp32(single_of_bits(0x00ffffff) / single_of_bits(0x4b800000), 0x00000001, STR(__LINE__)); // 0x1.fffffep-126 / 0x1p+24 = 0x1p-149
}

void f408(void) {
  comp32(single_of_bits(0x80ffffff) / single_of_bits(0xcb800000), 0x00000001, STR(__LINE__)); // -0x1.fffffep-126 / -0x1p+24 = 0x1p-149
  comp32(single_of_bits(0x80ffffff) / single_of_bits(0x4b800000), 0x80000001, STR(__LINE__)); // -0x1.fffffep-126 / 0x1p+24 = -0x1p-149
  comp32(single_of_bits(0x00ffffff) / single_of_bits(0xcb800000), 0x80000001, STR(__LINE__)); // 0x1.fffffep-126 / -0x1p+24 = -0x1p-149
  comp32(single_of_bits(0x007fffff) / single_of_bits(0x4b000000), 0x00000001, STR(__LINE__)); // 0x1.fffffcp-127 / 0x1p+23 = 0x1p-149
  comp32(single_of_bits(0x807fffff) / single_of_bits(0xcb000000), 0x00000001, STR(__LINE__)); // -0x1.fffffcp-127 / -0x1p+23 = 0x1p-149
  comp32(single_of_bits(0x807fffff) / single_of_bits(0x4b000000), 0x80000001, STR(__LINE__)); // -0x1.fffffcp-127 / 0x1p+23 = -0x1p-149
  comp32(single_of_bits(0x007fffff) / single_of_bits(0xcb000000), 0x80000001, STR(__LINE__)); // 0x1.fffffcp-127 / -0x1p+23 = -0x1p-149
  comp32(single_of_bits(0x00c00000) / single_of_bits(0x4b800000), 0x00000001, STR(__LINE__)); // 0x1.8p-126 / 0x1p+24 = 0x1p-149
  comp32(single_of_bits(0x80c00000) / single_of_bits(0xcb800000), 0x00000001, STR(__LINE__)); // -0x1.8p-126 / -0x1p+24 = 0x1p-149
  comp32(single_of_bits(0x80c00000) / single_of_bits(0x4b800000), 0x80000001, STR(__LINE__)); // -0x1.8p-126 / 0x1p+24 = -0x1p-149
}

void f409(void) {
  comp32(single_of_bits(0x00c00000) / single_of_bits(0xcb800000), 0x80000001, STR(__LINE__)); // 0x1.8p-126 / -0x1p+24 = -0x1p-149
  comp32(single_of_bits(0x00000003) / single_of_bits(0x40800000), 0x00000001, STR(__LINE__)); // 0x1.8p-148 / 0x1p+2 = 0x1p-149
  comp32(single_of_bits(0x80000003) / single_of_bits(0xc0800000), 0x00000001, STR(__LINE__)); // -0x1.8p-148 / -0x1p+2 = 0x1p-149
  comp32(single_of_bits(0x80000003) / single_of_bits(0x40800000), 0x80000001, STR(__LINE__)); // -0x1.8p-148 / 0x1p+2 = -0x1p-149
  comp32(single_of_bits(0x00000003) / single_of_bits(0xc0800000), 0x80000001, STR(__LINE__)); // 0x1.8p-148 / -0x1p+2 = -0x1p-149
  comp32(single_of_bits(0x00a00000) / single_of_bits(0x4b800000), 0x00000001, STR(__LINE__)); // 0x1.4p-126 / 0x1p+24 = 0x1p-149
  comp32(single_of_bits(0x80a00000) / single_of_bits(0xcb800000), 0x00000001, STR(__LINE__)); // -0x1.4p-126 / -0x1p+24 = 0x1p-149
  comp32(single_of_bits(0x80a00000) / single_of_bits(0x4b800000), 0x80000001, STR(__LINE__)); // -0x1.4p-126 / 0x1p+24 = -0x1p-149
  comp32(single_of_bits(0x00a00000) / single_of_bits(0xcb800000), 0x80000001, STR(__LINE__)); // 0x1.4p-126 / -0x1p+24 = -0x1p-149
  comp32(single_of_bits(0x00000005) / single_of_bits(0x41000000), 0x00000001, STR(__LINE__)); // 0x1.4p-147 / 0x1p+3 = 0x1p-149
}

void f410(void) {
  comp32(single_of_bits(0x80000005) / single_of_bits(0xc1000000), 0x00000001, STR(__LINE__)); // -0x1.4p-147 / -0x1p+3 = 0x1p-149
  comp32(single_of_bits(0x80000005) / single_of_bits(0x41000000), 0x80000001, STR(__LINE__)); // -0x1.4p-147 / 0x1p+3 = -0x1p-149
  comp32(single_of_bits(0x00000005) / single_of_bits(0xc1000000), 0x80000001, STR(__LINE__)); // 0x1.4p-147 / -0x1p+3 = -0x1p-149
  comp32(single_of_bits(0x00800000) / single_of_bits(0x4b800000), 0x00000000, STR(__LINE__)); // 0x1p-126 / 0x1p+24 = 0x0p+0
  comp32(single_of_bits(0x80800000) / single_of_bits(0xcb800000), 0x00000000, STR(__LINE__)); // -0x1p-126 / -0x1p+24 = 0x0p+0
  comp32(single_of_bits(0x80800000) / single_of_bits(0x4b800000), 0x80000000, STR(__LINE__)); // -0x1p-126 / 0x1p+24 = -0x0p+0
  comp32(single_of_bits(0x00800000) / single_of_bits(0xcb800000), 0x80000000, STR(__LINE__)); // 0x1p-126 / -0x1p+24 = -0x0p+0
  comp32(single_of_bits(0x00000001) / single_of_bits(0x40000000), 0x00000000, STR(__LINE__)); // 0x1p-149 / 0x1p+1 = 0x0p+0
  comp32(single_of_bits(0x80000001) / single_of_bits(0xc0000000), 0x00000000, STR(__LINE__)); // -0x1p-149 / -0x1p+1 = 0x0p+0
  comp32(single_of_bits(0x80000001) / single_of_bits(0x40000000), 0x80000000, STR(__LINE__)); // -0x1p-149 / 0x1p+1 = -0x0p+0
}

void f411(void) {
  comp32(single_of_bits(0x00000001) / single_of_bits(0xc0000000), 0x80000000, STR(__LINE__)); // 0x1p-149 / -0x1p+1 = -0x0p+0
  comp32(single_of_bits(0x01400000) / single_of_bits(0x4b800000), 0x00000002, STR(__LINE__)); // 0x1.8p-125 / 0x1p+24 = 0x1p-148
  comp32(single_of_bits(0x81400000) / single_of_bits(0xcb800000), 0x00000002, STR(__LINE__)); // -0x1.8p-125 / -0x1p+24 = 0x1p-148
  comp32(single_of_bits(0x81400000) / single_of_bits(0x4b800000), 0x80000002, STR(__LINE__)); // -0x1.8p-125 / 0x1p+24 = -0x1p-148
  comp32(single_of_bits(0x01400000) / single_of_bits(0xcb800000), 0x80000002, STR(__LINE__)); // 0x1.8p-125 / -0x1p+24 = -0x1p-148
  comp32(single_of_bits(0x00000003) / single_of_bits(0x40000000), 0x00000002, STR(__LINE__)); // 0x1.8p-148 / 0x1p+1 = 0x1p-148
  comp32(single_of_bits(0x80000003) / single_of_bits(0xc0000000), 0x00000002, STR(__LINE__)); // -0x1.8p-148 / -0x1p+1 = 0x1p-148
  comp32(single_of_bits(0x80000003) / single_of_bits(0x40000000), 0x80000002, STR(__LINE__)); // -0x1.8p-148 / 0x1p+1 = -0x1p-148
  comp32(single_of_bits(0x00000003) / single_of_bits(0xc0000000), 0x80000002, STR(__LINE__)); // 0x1.8p-148 / -0x1p+1 = -0x1p-148
  comp32(single_of_bits(0x00fffffd) / single_of_bits(0x40000000), 0x007ffffe, STR(__LINE__)); // 0x1.fffffap-126 / 0x1p+1 = 0x1.fffff8p-127
}

void f412(void) {
  comp32(single_of_bits(0x80fffffd) / single_of_bits(0xc0000000), 0x007ffffe, STR(__LINE__)); // -0x1.fffffap-126 / -0x1p+1 = 0x1.fffff8p-127
  comp32(single_of_bits(0x80fffffd) / single_of_bits(0x40000000), 0x807ffffe, STR(__LINE__)); // -0x1.fffffap-126 / 0x1p+1 = -0x1.fffff8p-127
  comp32(single_of_bits(0x00fffffd) / single_of_bits(0xc0000000), 0x807ffffe, STR(__LINE__)); // 0x1.fffffap-126 / -0x1p+1 = -0x1.fffff8p-127
  comp32(single_of_bits(0x00f00003) / single_of_bits(0x40c00000), 0x00280000, STR(__LINE__)); // 0x1.e00006p-126 / 0x1.8p+2 = 0x1.4p-128
  comp32(single_of_bits(0x00f00003) / single_of_bits(0x4bc00000), 0x00000001, STR(__LINE__)); // 0x1.e00006p-126 / 0x1.8p+24 = 0x1p-149
  comp32(single_of_bits(0x007fffff) / single_of_bits(0x40000000), 0x00400000, STR(__LINE__)); // 0x1.fffffcp-127 / 0x1p+1 = 0x1p-127
  comp32(single_of_bits(0x807fffff) / single_of_bits(0xc0000000), 0x00400000, STR(__LINE__)); // -0x1.fffffcp-127 / -0x1p+1 = 0x1p-127
  comp32(single_of_bits(0x807fffff) / single_of_bits(0x40000000), 0x80400000, STR(__LINE__)); // -0x1.fffffcp-127 / 0x1p+1 = -0x1p-127
  comp32(single_of_bits(0x007fffff) / single_of_bits(0xc0000000), 0x80400000, STR(__LINE__)); // 0x1.fffffcp-127 / -0x1p+1 = -0x1p-127
  comp32(single_of_bits(0x00800000) / single_of_bits(0x3f800001), 0x007fffff, STR(__LINE__)); // 0x1p-126 / 0x1.000002p+0 = 0x1.fffffcp-127
}

void f413(void) {
  comp32(single_of_bits(0x80800000) / single_of_bits(0xbf800001), 0x007fffff, STR(__LINE__)); // -0x1p-126 / -0x1.000002p+0 = 0x1.fffffcp-127
  comp32(single_of_bits(0x80800000) / single_of_bits(0x3f800001), 0x807fffff, STR(__LINE__)); // -0x1p-126 / 0x1.000002p+0 = -0x1.fffffcp-127
  comp32(single_of_bits(0x00800000) / single_of_bits(0xbf800001), 0x807fffff, STR(__LINE__)); // 0x1p-126 / -0x1.000002p+0 = -0x1.fffffcp-127
  comp32(single_of_bits(0x00800001) / single_of_bits(0x3f800002), 0x007fffff, STR(__LINE__)); // 0x1.000002p-126 / 0x1.000004p+0 = 0x1.fffffcp-127
  comp32(single_of_bits(0x00800002) / single_of_bits(0x3f800006), 0x007ffffc, STR(__LINE__)); // 0x1.000004p-126 / 0x1.00000cp+0 = 0x1.fffffp-127
  comp32(single_of_bits(0x007fffff) / single_of_bits(0x3f800001), 0x007ffffe, STR(__LINE__)); // 0x1.fffffcp-127 / 0x1.000002p+0 = 0x1.fffff8p-127
  comp32(single_of_bits(0x807fffff) / single_of_bits(0xbf800001), 0x007ffffe, STR(__LINE__)); // -0x1.fffffcp-127 / -0x1.000002p+0 = 0x1.fffff8p-127
  comp32(single_of_bits(0x807fffff) / single_of_bits(0x3f800001), 0x807ffffe, STR(__LINE__)); // -0x1.fffffcp-127 / 0x1.000002p+0 = -0x1.fffff8p-127
  comp32(single_of_bits(0x007fffff) / single_of_bits(0xbf800001), 0x807ffffe, STR(__LINE__)); // 0x1.fffffcp-127 / -0x1.000002p+0 = -0x1.fffff8p-127
  comp32(single_of_bits(0x007ffffe) / single_of_bits(0x3f7ffffe), 0x007fffff, STR(__LINE__)); // 0x1.fffff8p-127 / 0x1.fffffcp-1 = 0x1.fffffcp-127
}

void f414(void) {
  comp32(single_of_bits(0x007ffff7) / single_of_bits(0x3f7ffffe), 0x007ffff8, STR(__LINE__)); // 0x1.ffffdcp-127 / 0x1.fffffcp-1 = 0x1.ffffep-127
  comp32(single_of_bits(0x807ffff8) / single_of_bits(0x3f7ffffe), 0x807ffff9, STR(__LINE__)); // -0x1.ffffep-127 / 0x1.fffffcp-1 = -0x1.ffffe4p-127
  comp32(single_of_bits(0x007fffff) / single_of_bits(0x3f800002), 0x007ffffd, STR(__LINE__)); // 0x1.fffffcp-127 / 0x1.000004p+0 = 0x1.fffff4p-127
  comp32(single_of_bits(0x00bfffff) / single_of_bits(0x3fc00000), 0x007fffff, STR(__LINE__)); // 0x1.7ffffep-126 / 0x1.8p+0 = 0x1.fffffcp-127
  comp32(single_of_bits(0x80bfffff) / single_of_bits(0x3fc00000), 0x807fffff, STR(__LINE__)); // -0x1.7ffffep-126 / 0x1.8p+0 = -0x1.fffffcp-127
  comp32(single_of_bits(0x3f7fffff) / single_of_bits(0x7e800000), 0x00800000, STR(__LINE__)); // 0x1.fffffep-1 / 0x1p+126 = 0x1p-126
  comp32(single_of_bits(0xbf7fffff) / single_of_bits(0x7e800000), 0x80800000, STR(__LINE__)); // -0x1.fffffep-1 / 0x1p+126 = -0x1p-126
  comp32(single_of_bits(0x00ffffff) / single_of_bits(0x40000000), 0x00800000, STR(__LINE__)); // 0x1.fffffep-126 / 0x1p+1 = 0x1p-126
  comp32(single_of_bits(0x80ffffff) / single_of_bits(0xc0000000), 0x00800000, STR(__LINE__)); // -0x1.fffffep-126 / -0x1p+1 = 0x1p-126
  comp32(single_of_bits(0x80ffffff) / single_of_bits(0x40000000), 0x80800000, STR(__LINE__)); // -0x1.fffffep-126 / 0x1p+1 = -0x1p-126
}

void f415(void) {
  comp32(single_of_bits(0x00ffffff) / single_of_bits(0xc0000000), 0x80800000, STR(__LINE__)); // 0x1.fffffep-126 / -0x1p+1 = -0x1p-126
  comp32(single_of_bits(0x3f800000) / single_of_bits(0x3f800001), 0x3f7ffffe, STR(__LINE__)); // 0x1p+0 / 0x1.000002p+0 = 0x1.fffffcp-1
  comp32(single_of_bits(0xbf800000) / single_of_bits(0xbf800001), 0x3f7ffffe, STR(__LINE__)); // -0x1p+0 / -0x1.000002p+0 = 0x1.fffffcp-1
  comp32(single_of_bits(0xbf800000) / single_of_bits(0x3f800001), 0xbf7ffffe, STR(__LINE__)); // -0x1p+0 / 0x1.000002p+0 = -0x1.fffffcp-1
  comp32(single_of_bits(0x3f800000) / single_of_bits(0xbf800001), 0xbf7ffffe, STR(__LINE__)); // 0x1p+0 / -0x1.000002p+0 = -0x1.fffffcp-1
  comp32(single_of_bits(0x3f800000) / single_of_bits(0x3f800002), 0x3f7ffffc, STR(__LINE__)); // 0x1p+0 / 0x1.000004p+0 = 0x1.fffff8p-1
  comp32(single_of_bits(0x3f800000) / single_of_bits(0x3f800003), 0x3f7ffffa, STR(__LINE__)); // 0x1p+0 / 0x1.000006p+0 = 0x1.fffff4p-1
  comp32(single_of_bits(0x3f800000) / single_of_bits(0x3f800004), 0x3f7ffff8, STR(__LINE__)); // 0x1p+0 / 0x1.000008p+0 = 0x1.fffffp-1
  comp32(single_of_bits(0x3f800000) / single_of_bits(0x3f7ffffe), 0x3f800001, STR(__LINE__)); // 0x1p+0 / 0x1.fffffcp-1 = 0x1.000002p+0
  comp32(single_of_bits(0x3f800000) / single_of_bits(0x3f7ffffc), 0x3f800002, STR(__LINE__)); // 0x1p+0 / 0x1.fffff8p-1 = 0x1.000004p+0
}

void f416(void) {
  comp32(single_of_bits(0x3f800000) / single_of_bits(0x3f7ffff8), 0x3f800004, STR(__LINE__)); // 0x1p+0 / 0x1.fffffp-1 = 0x1.000008p+0
  comp32(single_of_bits(0x3f800001) / single_of_bits(0x3f800002), 0x3f7ffffe, STR(__LINE__)); // 0x1.000002p+0 / 0x1.000004p+0 = 0x1.fffffcp-1
  comp32(single_of_bits(0x3f800001) / single_of_bits(0x3f800003), 0x3f7ffffc, STR(__LINE__)); // 0x1.000002p+0 / 0x1.000006p+0 = 0x1.fffff8p-1
  comp32(single_of_bits(0x3f800002) / single_of_bits(0x3f800003), 0x3f7ffffe, STR(__LINE__)); // 0x1.000004p+0 / 0x1.000006p+0 = 0x1.fffffcp-1
  comp32(single_of_bits(0x3f800004) / single_of_bits(0x3f800007), 0x3f7ffffa, STR(__LINE__)); // 0x1.000008p+0 / 0x1.00000ep+0 = 0x1.fffff4p-1
  comp32(single_of_bits(0x3f800006) / single_of_bits(0x3f800008), 0x3f7ffffc, STR(__LINE__)); // 0x1.00000cp+0 / 0x1.00001p+0 = 0x1.fffff8p-1
  comp32(single_of_bits(0x3f7fffff) / single_of_bits(0x3f7ffffd), 0x3f800001, STR(__LINE__)); // 0x1.fffffep-1 / 0x1.fffffap-1 = 0x1.000002p+0
  comp32(single_of_bits(0x3f7ffffe) / single_of_bits(0x3f7ffffc), 0x3f800001, STR(__LINE__)); // 0x1.fffffcp-1 / 0x1.fffff8p-1 = 0x1.000002p+0
  comp32(single_of_bits(0x3f7fffff) / single_of_bits(0x3f7ffff9), 0x3f800003, STR(__LINE__)); // 0x1.fffffep-1 / 0x1.fffff2p-1 = 0x1.000006p+0
  comp32(single_of_bits(0x3f7ffffd) / single_of_bits(0x3f7ffff9), 0x3f800002, STR(__LINE__)); // 0x1.fffffap-1 / 0x1.fffff2p-1 = 0x1.000004p+0
}

void f417(void) {
  comp32(single_of_bits(0x3f7ffffb) / single_of_bits(0x3f7ffff9), 0x3f800001, STR(__LINE__)); // 0x1.fffff6p-1 / 0x1.fffff2p-1 = 0x1.000002p+0
  comp32(single_of_bits(0x3f800001) / single_of_bits(0x3f7ffffe), 0x3f800002, STR(__LINE__)); // 0x1.000002p+0 / 0x1.fffffcp-1 = 0x1.000004p+0
  comp32(single_of_bits(0x3f800002) / single_of_bits(0x3f7ffffe), 0x3f800003, STR(__LINE__)); // 0x1.000004p+0 / 0x1.fffffcp-1 = 0x1.000006p+0
  comp32(single_of_bits(0x3f800003) / single_of_bits(0x3f7ffffe), 0x3f800004, STR(__LINE__)); // 0x1.000006p+0 / 0x1.fffffcp-1 = 0x1.000008p+0
  comp32(single_of_bits(0x3f800002) / single_of_bits(0x3f7ffffc), 0x3f800004, STR(__LINE__)); // 0x1.000004p+0 / 0x1.fffff8p-1 = 0x1.000008p+0
  comp32(single_of_bits(0x3f800004) / single_of_bits(0x3f7ffffe), 0x3f800005, STR(__LINE__)); // 0x1.000008p+0 / 0x1.fffffcp-1 = 0x1.00000ap+0
  comp32(single_of_bits(0x3f7fffff) / single_of_bits(0x3f800001), 0x3f7ffffd, STR(__LINE__)); // 0x1.fffffep-1 / 0x1.000002p+0 = 0x1.fffffap-1
  comp32(single_of_bits(0x3f7ffffe) / single_of_bits(0x3f800001), 0x3f7ffffc, STR(__LINE__)); // 0x1.fffffcp-1 / 0x1.000002p+0 = 0x1.fffff8p-1
  comp32(single_of_bits(0x3f7fffff) / single_of_bits(0x3f800002), 0x3f7ffffb, STR(__LINE__)); // 0x1.fffffep-1 / 0x1.000004p+0 = 0x1.fffff6p-1
  comp32(single_of_bits(0x3f7ffffd) / single_of_bits(0x3f800001), 0x3f7ffffb, STR(__LINE__)); // 0x1.fffffap-1 / 0x1.000002p+0 = 0x1.fffff6p-1
}

void f418(void) {
  comp32(single_of_bits(0x3f7fffff) / single_of_bits(0x3f800003), 0x3f7ffff9, STR(__LINE__)); // 0x1.fffffep-1 / 0x1.000006p+0 = 0x1.fffff2p-1
  comp32(single_of_bits(0x3f7ffffe) / single_of_bits(0x3f800002), 0x3f7ffffa, STR(__LINE__)); // 0x1.fffffcp-1 / 0x1.000004p+0 = 0x1.fffff4p-1
  comp32(single_of_bits(0x3f7ffffc) / single_of_bits(0x3f800001), 0x3f7ffffa, STR(__LINE__)); // 0x1.fffff8p-1 / 0x1.000002p+0 = 0x1.fffff4p-1
  comp32(single_of_bits(0x3f7fffff) / single_of_bits(0x3f800004), 0x3f7ffff7, STR(__LINE__)); // 0x1.fffffep-1 / 0x1.000008p+0 = 0x1.ffffeep-1
  comp32(single_of_bits(0x3f7ffffd) / single_of_bits(0x3f800002), 0x3f7ffff9, STR(__LINE__)); // 0x1.fffffap-1 / 0x1.000004p+0 = 0x1.fffff2p-1
  comp32(single_of_bits(0x3f7ffffe) / single_of_bits(0x3f800003), 0x3f7ffff8, STR(__LINE__)); // 0x1.fffffcp-1 / 0x1.000006p+0 = 0x1.fffffp-1
  comp32(single_of_bits(0xbf7ffffc) / single_of_bits(0xbf800001), 0x3f7ffffa, STR(__LINE__)); // -0x1.fffff8p-1 / -0x1.000002p+0 = 0x1.fffff4p-1
  comp32(single_of_bits(0xbf7ffffc) / single_of_bits(0x3f800001), 0xbf7ffffa, STR(__LINE__)); // -0x1.fffff8p-1 / 0x1.000002p+0 = -0x1.fffff4p-1
  comp32(single_of_bits(0x3f7ffffc) / single_of_bits(0xbf800001), 0xbf7ffffa, STR(__LINE__)); // 0x1.fffff8p-1 / -0x1.000002p+0 = -0x1.fffff4p-1
  comp32(single_of_bits(0x3fbfffff) / single_of_bits(0x3f7ffffe), 0x3fc00001, STR(__LINE__)); // 0x1.7ffffep+0 / 0x1.fffffcp-1 = 0x1.800002p+0
}

void f419(void) {
  comp32(single_of_bits(0xbfbfffff) / single_of_bits(0xbf7ffffe), 0x3fc00001, STR(__LINE__)); // -0x1.7ffffep+0 / -0x1.fffffcp-1 = 0x1.800002p+0
  comp32(single_of_bits(0xbfbfffff) / single_of_bits(0x3f7ffffe), 0xbfc00001, STR(__LINE__)); // -0x1.7ffffep+0 / 0x1.fffffcp-1 = -0x1.800002p+0
  comp32(single_of_bits(0x3fbfffff) / single_of_bits(0xbf7ffffe), 0xbfc00001, STR(__LINE__)); // 0x1.7ffffep+0 / -0x1.fffffcp-1 = -0x1.800002p+0
  comp32(single_of_bits(0x00400000) / single_of_bits(0x00800001), 0x3efffffe, STR(__LINE__)); // 0x1p-127 / 0x1.000002p-126 = 0x1.fffffcp-2
  comp32(single_of_bits(0x80400000) / single_of_bits(0x80800001), 0x3efffffe, STR(__LINE__)); // -0x1p-127 / -0x1.000002p-126 = 0x1.fffffcp-2
  comp32(single_of_bits(0x80400000) / single_of_bits(0x00800001), 0xbefffffe, STR(__LINE__)); // -0x1p-127 / 0x1.000002p-126 = -0x1.fffffcp-2
  comp32(single_of_bits(0x00400000) / single_of_bits(0x80800001), 0xbefffffe, STR(__LINE__)); // 0x1p-127 / -0x1.000002p-126 = -0x1.fffffcp-2
  comp32(single_of_bits(0x40400002) / single_of_bits(0x3f800001), 0x40400000, STR(__LINE__)); // 0x1.800004p+1 / 0x1.000002p+0 = 0x1.8p+1
  comp32(single_of_bits(0xc0400002) / single_of_bits(0xbf800001), 0x40400000, STR(__LINE__)); // -0x1.800004p+1 / -0x1.000002p+0 = 0x1.8p+1
  comp32(single_of_bits(0x40400002) / single_of_bits(0xbf800001), 0xc0400000, STR(__LINE__)); // 0x1.800004p+1 / -0x1.000002p+0 = -0x1.8p+1
}

void f420(void) {
  comp32(single_of_bits(0xc0400002) / single_of_bits(0x3f800001), 0xc0400000, STR(__LINE__)); // -0x1.800004p+1 / 0x1.000002p+0 = -0x1.8p+1
  comp32(single_of_bits(0x00600001) / single_of_bits(0x00800001), 0x3f400000, STR(__LINE__)); // 0x1.800004p-127 / 0x1.000002p-126 = 0x1.8p-1
  comp32(single_of_bits(0x80600001) / single_of_bits(0x80800001), 0x3f400000, STR(__LINE__)); // -0x1.800004p-127 / -0x1.000002p-126 = 0x1.8p-1
  comp32(single_of_bits(0x00600001) / single_of_bits(0x80800001), 0xbf400000, STR(__LINE__)); // 0x1.800004p-127 / -0x1.000002p-126 = -0x1.8p-1
  comp32(single_of_bits(0x80600001) / single_of_bits(0x00800001), 0xbf400000, STR(__LINE__)); // -0x1.800004p-127 / 0x1.000002p-126 = -0x1.8p-1
  comp32(single_of_bits(0x3f800000) / single_of_bits(0x3f7ffffd), 0x3f800002, STR(__LINE__)); // 0x1p+0 / 0x1.fffffap-1 = 0x1.000004p+0
  comp32(single_of_bits(0x3f800000) / single_of_bits(0x3f7ffffb), 0x3f800003, STR(__LINE__)); // 0x1p+0 / 0x1.fffff6p-1 = 0x1.000006p+0
  comp32(single_of_bits(0x3f800000) / single_of_bits(0x3f7ffff7), 0x3f800005, STR(__LINE__)); // 0x1p+0 / 0x1.ffffeep-1 = 0x1.00000ap+0
  comp32(single_of_bits(0x3f800000) / single_of_bits(0x3f7fffff), 0x3f800001, STR(__LINE__)); // 0x1p+0 / 0x1.fffffep-1 = 0x1.000002p+0
  comp32(single_of_bits(0xbf800000) / single_of_bits(0xbf7fffff), 0x3f800001, STR(__LINE__)); // -0x1p+0 / -0x1.fffffep-1 = 0x1.000002p+0
}

void f421(void) {
  comp32(single_of_bits(0xbf800000) / single_of_bits(0x3f7fffff), 0xbf800001, STR(__LINE__)); // -0x1p+0 / 0x1.fffffep-1 = -0x1.000002p+0
  comp32(single_of_bits(0x3f800000) / single_of_bits(0xbf7fffff), 0xbf800001, STR(__LINE__)); // 0x1p+0 / -0x1.fffffep-1 = -0x1.000002p+0
  comp32(single_of_bits(0x3f7fffff) / single_of_bits(0x3f7ffffe), 0x3f800001, STR(__LINE__)); // 0x1.fffffep-1 / 0x1.fffffcp-1 = 0x1.000002p+0
  comp32(single_of_bits(0x3f7ffffe) / single_of_bits(0x3f7ffffd), 0x3f800001, STR(__LINE__)); // 0x1.fffffcp-1 / 0x1.fffffap-1 = 0x1.000002p+0
  comp32(single_of_bits(0x3f7fffff) / single_of_bits(0x3f7ffffc), 0x3f800002, STR(__LINE__)); // 0x1.fffffep-1 / 0x1.fffff8p-1 = 0x1.000004p+0
  comp32(single_of_bits(0x3f7ffffd) / single_of_bits(0x3f7ffffc), 0x3f800001, STR(__LINE__)); // 0x1.fffffap-1 / 0x1.fffff8p-1 = 0x1.000002p+0
  comp32(single_of_bits(0x3f7ffffe) / single_of_bits(0x3f7ffff9), 0x3f800003, STR(__LINE__)); // 0x1.fffffcp-1 / 0x1.fffff2p-1 = 0x1.000006p+0
  comp32(single_of_bits(0x3f7ffffc) / single_of_bits(0x3f7ffff9), 0x3f800002, STR(__LINE__)); // 0x1.fffff8p-1 / 0x1.fffff2p-1 = 0x1.000004p+0
  comp32(single_of_bits(0x3f7ffffa) / single_of_bits(0x3f7ffff9), 0x3f800001, STR(__LINE__)); // 0x1.fffff4p-1 / 0x1.fffff2p-1 = 0x1.000002p+0
  comp32(single_of_bits(0x3f800001) / single_of_bits(0x3f7fffff), 0x3f800002, STR(__LINE__)); // 0x1.000002p+0 / 0x1.fffffep-1 = 0x1.000004p+0
}

void f422(void) {
  comp32(single_of_bits(0x3f800002) / single_of_bits(0x3f7fffff), 0x3f800003, STR(__LINE__)); // 0x1.000004p+0 / 0x1.fffffep-1 = 0x1.000006p+0
  comp32(single_of_bits(0x3f800001) / single_of_bits(0x3f7ffffd), 0x3f800003, STR(__LINE__)); // 0x1.000002p+0 / 0x1.fffffap-1 = 0x1.000006p+0
  comp32(single_of_bits(0x3f800003) / single_of_bits(0x3f7fffff), 0x3f800004, STR(__LINE__)); // 0x1.000006p+0 / 0x1.fffffep-1 = 0x1.000008p+0
  comp32(single_of_bits(0x3f800002) / single_of_bits(0x3f7ffffd), 0x3f800004, STR(__LINE__)); // 0x1.000004p+0 / 0x1.fffffap-1 = 0x1.000008p+0
  comp32(single_of_bits(0x3f800003) / single_of_bits(0x3f7ffffd), 0x3f800005, STR(__LINE__)); // 0x1.000006p+0 / 0x1.fffffap-1 = 0x1.00000ap+0
  comp32(single_of_bits(0x3f800001) / single_of_bits(0x3f7ffffb), 0x3f800004, STR(__LINE__)); // 0x1.000002p+0 / 0x1.fffff6p-1 = 0x1.000008p+0
  comp32(single_of_bits(0x3f800005) / single_of_bits(0x3f7fffff), 0x3f800006, STR(__LINE__)); // 0x1.00000ap+0 / 0x1.fffffep-1 = 0x1.00000cp+0
  comp32(single_of_bits(0x00400000) / single_of_bits(0x00ffffff), 0x3e800001, STR(__LINE__)); // 0x1p-127 / 0x1.fffffep-126 = 0x1.000002p-2
  comp32(single_of_bits(0x80400000) / single_of_bits(0x80ffffff), 0x3e800001, STR(__LINE__)); // -0x1p-127 / -0x1.fffffep-126 = 0x1.000002p-2
  comp32(single_of_bits(0x80400000) / single_of_bits(0x00ffffff), 0xbe800001, STR(__LINE__)); // -0x1p-127 / 0x1.fffffep-126 = -0x1.000002p-2
}

void f423(void) {
  comp32(single_of_bits(0x00400000) / single_of_bits(0x80ffffff), 0xbe800001, STR(__LINE__)); // 0x1p-127 / -0x1.fffffep-126 = -0x1.000002p-2
  comp32(single_of_bits(0x3fc00001) / single_of_bits(0x3f800001), 0x3fc00000, STR(__LINE__)); // 0x1.800002p+0 / 0x1.000002p+0 = 0x1.8p+0
  comp32(single_of_bits(0xbfc00001) / single_of_bits(0xbf800001), 0x3fc00000, STR(__LINE__)); // -0x1.800002p+0 / -0x1.000002p+0 = 0x1.8p+0
  comp32(single_of_bits(0xbfc00001) / single_of_bits(0x3f800001), 0xbfc00000, STR(__LINE__)); // -0x1.800002p+0 / 0x1.000002p+0 = -0x1.8p+0
  comp32(single_of_bits(0x3fc00001) / single_of_bits(0xbf800001), 0xbfc00000, STR(__LINE__)); // 0x1.800002p+0 / -0x1.000002p+0 = -0x1.8p+0
  comp32(single_of_bits(0x3f800002) / single_of_bits(0x3f800001), 0x3f800001, STR(__LINE__)); // 0x1.000004p+0 / 0x1.000002p+0 = 0x1.000002p+0
  comp32(single_of_bits(0xbf800002) / single_of_bits(0xbf800001), 0x3f800001, STR(__LINE__)); // -0x1.000004p+0 / -0x1.000002p+0 = 0x1.000002p+0
  comp32(single_of_bits(0xbf800002) / single_of_bits(0x3f800001), 0xbf800001, STR(__LINE__)); // -0x1.000004p+0 / 0x1.000002p+0 = -0x1.000002p+0
  comp32(single_of_bits(0x3f800002) / single_of_bits(0xbf800001), 0xbf800001, STR(__LINE__)); // 0x1.000004p+0 / -0x1.000002p+0 = -0x1.000002p+0
  comp32(single_of_bits(0x3f800003) / single_of_bits(0x3f800001), 0x3f800002, STR(__LINE__)); // 0x1.000006p+0 / 0x1.000002p+0 = 0x1.000004p+0
}

void f424(void) {
  comp32(single_of_bits(0x3f800004) / single_of_bits(0x3f800001), 0x3f800003, STR(__LINE__)); // 0x1.000008p+0 / 0x1.000002p+0 = 0x1.000006p+0
  comp32(single_of_bits(0x3f800007) / single_of_bits(0x3f800002), 0x3f800005, STR(__LINE__)); // 0x1.00000ep+0 / 0x1.000004p+0 = 0x1.00000ap+0
  comp32(single_of_bits(0x3f800009) / single_of_bits(0x3f800008), 0x3f800001, STR(__LINE__)); // 0x1.000012p+0 / 0x1.00001p+0 = 0x1.000002p+0
  comp32(single_of_bits(0x3f7ffffe) / single_of_bits(0x3f7fffff), 0x3f7fffff, STR(__LINE__)); // 0x1.fffffcp-1 / 0x1.fffffep-1 = 0x1.fffffep-1
  comp32(single_of_bits(0x3f7ffffd) / single_of_bits(0x3f7fffff), 0x3f7ffffe, STR(__LINE__)); // 0x1.fffffap-1 / 0x1.fffffep-1 = 0x1.fffffcp-1
  comp32(single_of_bits(0x3f7ffffd) / single_of_bits(0x3f7ffffe), 0x3f7fffff, STR(__LINE__)); // 0x1.fffffap-1 / 0x1.fffffcp-1 = 0x1.fffffep-1
  comp32(single_of_bits(0x3f7ffffc) / single_of_bits(0x3f7fffff), 0x3f7ffffd, STR(__LINE__)); // 0x1.fffff8p-1 / 0x1.fffffep-1 = 0x1.fffffap-1
  comp32(single_of_bits(0x3f7ffffc) / single_of_bits(0x3f7ffffe), 0x3f7ffffe, STR(__LINE__)); // 0x1.fffff8p-1 / 0x1.fffffcp-1 = 0x1.fffffcp-1
  comp32(single_of_bits(0x3f7ffffc) / single_of_bits(0x3f7ffffd), 0x3f7fffff, STR(__LINE__)); // 0x1.fffff8p-1 / 0x1.fffffap-1 = 0x1.fffffep-1
  comp32(single_of_bits(0x3f7ffff8) / single_of_bits(0x3f7ffffd), 0x3f7ffffb, STR(__LINE__)); // 0x1.fffffp-1 / 0x1.fffffap-1 = 0x1.fffff6p-1
}

void f425(void) {
  comp32(single_of_bits(0x3f7ffff7) / single_of_bits(0x3f7ffffe), 0x3f7ffff9, STR(__LINE__)); // 0x1.ffffeep-1 / 0x1.fffffcp-1 = 0x1.fffff2p-1
  comp32(single_of_bits(0x3f7ffff8) / single_of_bits(0x3f7ffffc), 0x3f7ffffc, STR(__LINE__)); // 0x1.fffffp-1 / 0x1.fffff8p-1 = 0x1.fffff8p-1
  comp32(single_of_bits(0x3f7ffff7) / single_of_bits(0x3f7ffffb), 0x3f7ffffc, STR(__LINE__)); // 0x1.ffffeep-1 / 0x1.fffff6p-1 = 0x1.fffff8p-1
  comp32(single_of_bits(0x007ffffe) / single_of_bits(0x00ffffff), 0x3efffffd, STR(__LINE__)); // 0x1.fffff8p-127 / 0x1.fffffep-126 = 0x1.fffffap-2
  comp32(single_of_bits(0x807ffffe) / single_of_bits(0x80ffffff), 0x3efffffd, STR(__LINE__)); // -0x1.fffff8p-127 / -0x1.fffffep-126 = 0x1.fffffap-2
  comp32(single_of_bits(0x807ffffe) / single_of_bits(0x00ffffff), 0xbefffffd, STR(__LINE__)); // -0x1.fffff8p-127 / 0x1.fffffep-126 = -0x1.fffffap-2
  comp32(single_of_bits(0x007ffffe) / single_of_bits(0x80ffffff), 0xbefffffd, STR(__LINE__)); // 0x1.fffff8p-127 / -0x1.fffffep-126 = -0x1.fffffap-2
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x3f800000), 0x3f800000, STR(__LINE__)); // 0x1p+0 * 0x1p+0 = 0x1p+0
  comp32(single_of_bits(0xbf800000) * single_of_bits(0xbf800000), 0x3f800000, STR(__LINE__)); // -0x1p+0 * -0x1p+0 = 0x1p+0
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x3f800000), 0xbf800000, STR(__LINE__)); // -0x1p+0 * 0x1p+0 = -0x1p+0
}

void f426(void) {
  comp32(single_of_bits(0x3f800000) * single_of_bits(0xbf800000), 0xbf800000, STR(__LINE__)); // 0x1p+0 * -0x1p+0 = -0x1p+0
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x40000000), 0x40000000, STR(__LINE__)); // 0x1p+0 * 0x1p+1 = 0x1p+1
  comp32(single_of_bits(0x40000000) * single_of_bits(0x3f800000), 0x40000000, STR(__LINE__)); // 0x1p+1 * 0x1p+0 = 0x1p+1
  comp32(single_of_bits(0xbf800000) * single_of_bits(0xc0000000), 0x40000000, STR(__LINE__)); // -0x1p+0 * -0x1p+1 = 0x1p+1
  comp32(single_of_bits(0xc0000000) * single_of_bits(0xbf800000), 0x40000000, STR(__LINE__)); // -0x1p+1 * -0x1p+0 = 0x1p+1
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x40000000), 0xc0000000, STR(__LINE__)); // -0x1p+0 * 0x1p+1 = -0x1p+1
  comp32(single_of_bits(0x40000000) * single_of_bits(0xbf800000), 0xc0000000, STR(__LINE__)); // 0x1p+1 * -0x1p+0 = -0x1p+1
  comp32(single_of_bits(0x3f800000) * single_of_bits(0xc0000000), 0xc0000000, STR(__LINE__)); // 0x1p+0 * -0x1p+1 = -0x1p+1
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x3f800000), 0xc0000000, STR(__LINE__)); // -0x1p+1 * 0x1p+0 = -0x1p+1
  comp32(single_of_bits(0x40000000) * single_of_bits(0x40400000), 0x40c00000, STR(__LINE__)); // 0x1p+1 * 0x1.8p+1 = 0x1.8p+2
}

void f427(void) {
  comp32(single_of_bits(0x40400000) * single_of_bits(0x40000000), 0x40c00000, STR(__LINE__)); // 0x1.8p+1 * 0x1p+1 = 0x1.8p+2
  comp32(single_of_bits(0xc0000000) * single_of_bits(0xc0400000), 0x40c00000, STR(__LINE__)); // -0x1p+1 * -0x1.8p+1 = 0x1.8p+2
  comp32(single_of_bits(0xc0400000) * single_of_bits(0xc0000000), 0x40c00000, STR(__LINE__)); // -0x1.8p+1 * -0x1p+1 = 0x1.8p+2
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x40400000), 0xc0c00000, STR(__LINE__)); // -0x1p+1 * 0x1.8p+1 = -0x1.8p+2
  comp32(single_of_bits(0x40400000) * single_of_bits(0xc0000000), 0xc0c00000, STR(__LINE__)); // 0x1.8p+1 * -0x1p+1 = -0x1.8p+2
  comp32(single_of_bits(0x40000000) * single_of_bits(0xc0400000), 0xc0c00000, STR(__LINE__)); // 0x1p+1 * -0x1.8p+1 = -0x1.8p+2
  comp32(single_of_bits(0xc0400000) * single_of_bits(0x40000000), 0xc0c00000, STR(__LINE__)); // -0x1.8p+1 * 0x1p+1 = -0x1.8p+2
  comp32(single_of_bits(0x40400000) * single_of_bits(0x40400000), 0x41100000, STR(__LINE__)); // 0x1.8p+1 * 0x1.8p+1 = 0x1.2p+3
  comp32(single_of_bits(0xc0400000) * single_of_bits(0xc0400000), 0x41100000, STR(__LINE__)); // -0x1.8p+1 * -0x1.8p+1 = 0x1.2p+3
  comp32(single_of_bits(0xc0400000) * single_of_bits(0x40400000), 0xc1100000, STR(__LINE__)); // -0x1.8p+1 * 0x1.8p+1 = -0x1.2p+3
}

void f428(void) {
  comp32(single_of_bits(0x40400000) * single_of_bits(0xc0400000), 0xc1100000, STR(__LINE__)); // 0x1.8p+1 * -0x1.8p+1 = -0x1.2p+3
  comp32(single_of_bits(0x00000001) * single_of_bits(0x3f800000), 0x00000001, STR(__LINE__)); // 0x1p-149 * 0x1p+0 = 0x1p-149
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x00000001), 0x00000001, STR(__LINE__)); // 0x1p+0 * 0x1p-149 = 0x1p-149
  comp32(single_of_bits(0x80000001) * single_of_bits(0xbf800000), 0x00000001, STR(__LINE__)); // -0x1p-149 * -0x1p+0 = 0x1p-149
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x80000001), 0x00000001, STR(__LINE__)); // -0x1p+0 * -0x1p-149 = 0x1p-149
  comp32(single_of_bits(0x80000001) * single_of_bits(0x3f800000), 0x80000001, STR(__LINE__)); // -0x1p-149 * 0x1p+0 = -0x1p-149
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x80000001), 0x80000001, STR(__LINE__)); // 0x1p+0 * -0x1p-149 = -0x1p-149
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x00000001), 0x80000001, STR(__LINE__)); // -0x1p+0 * 0x1p-149 = -0x1p-149
  comp32(single_of_bits(0x00000001) * single_of_bits(0xbf800000), 0x80000001, STR(__LINE__)); // 0x1p-149 * -0x1p+0 = -0x1p-149
  comp32(single_of_bits(0x00000002) * single_of_bits(0x3f800000), 0x00000002, STR(__LINE__)); // 0x1p-148 * 0x1p+0 = 0x1p-148
}

void f429(void) {
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x00000002), 0x00000002, STR(__LINE__)); // 0x1p+0 * 0x1p-148 = 0x1p-148
  comp32(single_of_bits(0x80000002) * single_of_bits(0xbf800000), 0x00000002, STR(__LINE__)); // -0x1p-148 * -0x1p+0 = 0x1p-148
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x80000002), 0x00000002, STR(__LINE__)); // -0x1p+0 * -0x1p-148 = 0x1p-148
  comp32(single_of_bits(0x80000002) * single_of_bits(0x3f800000), 0x80000002, STR(__LINE__)); // -0x1p-148 * 0x1p+0 = -0x1p-148
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x80000002), 0x80000002, STR(__LINE__)); // 0x1p+0 * -0x1p-148 = -0x1p-148
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x00000002), 0x80000002, STR(__LINE__)); // -0x1p+0 * 0x1p-148 = -0x1p-148
  comp32(single_of_bits(0x00000002) * single_of_bits(0xbf800000), 0x80000002, STR(__LINE__)); // 0x1p-148 * -0x1p+0 = -0x1p-148
  comp32(single_of_bits(0x00000004) * single_of_bits(0x3f800000), 0x00000004, STR(__LINE__)); // 0x1p-147 * 0x1p+0 = 0x1p-147
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x00000004), 0x00000004, STR(__LINE__)); // 0x1p+0 * 0x1p-147 = 0x1p-147
  comp32(single_of_bits(0x80000004) * single_of_bits(0xbf800000), 0x00000004, STR(__LINE__)); // -0x1p-147 * -0x1p+0 = 0x1p-147
}

void f430(void) {
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x80000004), 0x00000004, STR(__LINE__)); // -0x1p+0 * -0x1p-147 = 0x1p-147
  comp32(single_of_bits(0x80000004) * single_of_bits(0x3f800000), 0x80000004, STR(__LINE__)); // -0x1p-147 * 0x1p+0 = -0x1p-147
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x80000004), 0x80000004, STR(__LINE__)); // 0x1p+0 * -0x1p-147 = -0x1p-147
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x00000004), 0x80000004, STR(__LINE__)); // -0x1p+0 * 0x1p-147 = -0x1p-147
  comp32(single_of_bits(0x00000004) * single_of_bits(0xbf800000), 0x80000004, STR(__LINE__)); // 0x1p-147 * -0x1p+0 = -0x1p-147
  comp32(single_of_bits(0x00fffffe) * single_of_bits(0x3f800000), 0x00fffffe, STR(__LINE__)); // 0x1.fffffcp-126 * 0x1p+0 = 0x1.fffffcp-126
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x00fffffe), 0x00fffffe, STR(__LINE__)); // 0x1p+0 * 0x1.fffffcp-126 = 0x1.fffffcp-126
  comp32(single_of_bits(0x80fffffe) * single_of_bits(0xbf800000), 0x00fffffe, STR(__LINE__)); // -0x1.fffffcp-126 * -0x1p+0 = 0x1.fffffcp-126
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x80fffffe), 0x00fffffe, STR(__LINE__)); // -0x1p+0 * -0x1.fffffcp-126 = 0x1.fffffcp-126
  comp32(single_of_bits(0x80fffffe) * single_of_bits(0x3f800000), 0x80fffffe, STR(__LINE__)); // -0x1.fffffcp-126 * 0x1p+0 = -0x1.fffffcp-126
}

void f431(void) {
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x80fffffe), 0x80fffffe, STR(__LINE__)); // 0x1p+0 * -0x1.fffffcp-126 = -0x1.fffffcp-126
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x00fffffe), 0x80fffffe, STR(__LINE__)); // -0x1p+0 * 0x1.fffffcp-126 = -0x1.fffffcp-126
  comp32(single_of_bits(0x00fffffe) * single_of_bits(0xbf800000), 0x80fffffe, STR(__LINE__)); // 0x1.fffffcp-126 * -0x1p+0 = -0x1.fffffcp-126
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x80000009), 0x80000009, STR(__LINE__)); // 0x1p+0 * -0x1.2p-146 = -0x1.2p-146
  comp32(single_of_bits(0x80000009) * single_of_bits(0x3f800000), 0x80000009, STR(__LINE__)); // -0x1.2p-146 * 0x1p+0 = -0x1.2p-146
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x00000009), 0x80000009, STR(__LINE__)); // -0x1p+0 * 0x1.2p-146 = -0x1.2p-146
  comp32(single_of_bits(0x00000009) * single_of_bits(0xbf800000), 0x80000009, STR(__LINE__)); // 0x1.2p-146 * -0x1p+0 = -0x1.2p-146
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x80000009), 0x00000009, STR(__LINE__)); // -0x1p+0 * -0x1.2p-146 = 0x1.2p-146
  comp32(single_of_bits(0x80000009) * single_of_bits(0xbf800000), 0x00000009, STR(__LINE__)); // -0x1.2p-146 * -0x1p+0 = 0x1.2p-146
  comp32(single_of_bits(0x00000009) * single_of_bits(0x3f800000), 0x00000009, STR(__LINE__)); // 0x1.2p-146 * 0x1p+0 = 0x1.2p-146
}

void f432(void) {
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x00000009), 0x00000009, STR(__LINE__)); // 0x1p+0 * 0x1.2p-146 = 0x1.2p-146
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x807fffff), 0x807fffff, STR(__LINE__)); // 0x1p+0 * -0x1.fffffcp-127 = -0x1.fffffcp-127
  comp32(single_of_bits(0x807fffff) * single_of_bits(0x3f800000), 0x807fffff, STR(__LINE__)); // -0x1.fffffcp-127 * 0x1p+0 = -0x1.fffffcp-127
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x007fffff), 0x807fffff, STR(__LINE__)); // -0x1p+0 * 0x1.fffffcp-127 = -0x1.fffffcp-127
  comp32(single_of_bits(0x007fffff) * single_of_bits(0xbf800000), 0x807fffff, STR(__LINE__)); // 0x1.fffffcp-127 * -0x1p+0 = -0x1.fffffcp-127
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x807fffff), 0x007fffff, STR(__LINE__)); // -0x1p+0 * -0x1.fffffcp-127 = 0x1.fffffcp-127
  comp32(single_of_bits(0x807fffff) * single_of_bits(0xbf800000), 0x007fffff, STR(__LINE__)); // -0x1.fffffcp-127 * -0x1p+0 = 0x1.fffffcp-127
  comp32(single_of_bits(0x007fffff) * single_of_bits(0x3f800000), 0x007fffff, STR(__LINE__)); // 0x1.fffffcp-127 * 0x1p+0 = 0x1.fffffcp-127
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x007fffff), 0x007fffff, STR(__LINE__)); // 0x1p+0 * 0x1.fffffcp-127 = 0x1.fffffcp-127
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x80800001), 0x80800001, STR(__LINE__)); // 0x1p+0 * -0x1.000002p-126 = -0x1.000002p-126
}

void f433(void) {
  comp32(single_of_bits(0x80800001) * single_of_bits(0x3f800000), 0x80800001, STR(__LINE__)); // -0x1.000002p-126 * 0x1p+0 = -0x1.000002p-126
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x00800001), 0x80800001, STR(__LINE__)); // -0x1p+0 * 0x1.000002p-126 = -0x1.000002p-126
  comp32(single_of_bits(0x00800001) * single_of_bits(0xbf800000), 0x80800001, STR(__LINE__)); // 0x1.000002p-126 * -0x1p+0 = -0x1.000002p-126
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x80800001), 0x00800001, STR(__LINE__)); // -0x1p+0 * -0x1.000002p-126 = 0x1.000002p-126
  comp32(single_of_bits(0x80800001) * single_of_bits(0xbf800000), 0x00800001, STR(__LINE__)); // -0x1.000002p-126 * -0x1p+0 = 0x1.000002p-126
  comp32(single_of_bits(0x00800001) * single_of_bits(0x3f800000), 0x00800001, STR(__LINE__)); // 0x1.000002p-126 * 0x1p+0 = 0x1.000002p-126
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x00800001), 0x00800001, STR(__LINE__)); // 0x1p+0 * 0x1.000002p-126 = 0x1.000002p-126
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x01000003), 0x01000003, STR(__LINE__)); // 0x1p+0 * 0x1.000006p-125 = 0x1.000006p-125
  comp32(single_of_bits(0x01000003) * single_of_bits(0x3f800000), 0x01000003, STR(__LINE__)); // 0x1.000006p-125 * 0x1p+0 = 0x1.000006p-125
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x00800009), 0x80800009, STR(__LINE__)); // -0x1p+0 * 0x1.000012p-126 = -0x1.000012p-126
}

void f434(void) {
  comp32(single_of_bits(0x00800009) * single_of_bits(0xbf800000), 0x80800009, STR(__LINE__)); // 0x1.000012p-126 * -0x1p+0 = -0x1.000012p-126
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x007ffffd), 0x007ffffd, STR(__LINE__)); // 0x1p+0 * 0x1.fffff4p-127 = 0x1.fffff4p-127
  comp32(single_of_bits(0x007ffffd) * single_of_bits(0x3f800000), 0x007ffffd, STR(__LINE__)); // 0x1.fffff4p-127 * 0x1p+0 = 0x1.fffff4p-127
  comp32(single_of_bits(0x40000000) * single_of_bits(0x7effffff), 0x7f7fffff, STR(__LINE__)); // 0x1p+1 * 0x1.fffffep+126 = 0x1.fffffep+127
  comp32(single_of_bits(0x7effffff) * single_of_bits(0x40000000), 0x7f7fffff, STR(__LINE__)); // 0x1.fffffep+126 * 0x1p+1 = 0x1.fffffep+127
  comp32(single_of_bits(0xc0000000) * single_of_bits(0xfeffffff), 0x7f7fffff, STR(__LINE__)); // -0x1p+1 * -0x1.fffffep+126 = 0x1.fffffep+127
  comp32(single_of_bits(0xfeffffff) * single_of_bits(0xc0000000), 0x7f7fffff, STR(__LINE__)); // -0x1.fffffep+126 * -0x1p+1 = 0x1.fffffep+127
  comp32(single_of_bits(0x7effffff) * single_of_bits(0xc0000000), 0xff7fffff, STR(__LINE__)); // 0x1.fffffep+126 * -0x1p+1 = -0x1.fffffep+127
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x7effffff), 0xff7fffff, STR(__LINE__)); // -0x1p+1 * 0x1.fffffep+126 = -0x1.fffffep+127
  comp32(single_of_bits(0xfeffffff) * single_of_bits(0x40000000), 0xff7fffff, STR(__LINE__)); // -0x1.fffffep+126 * 0x1p+1 = -0x1.fffffep+127
}

void f435(void) {
  comp32(single_of_bits(0x40000000) * single_of_bits(0xfeffffff), 0xff7fffff, STR(__LINE__)); // 0x1p+1 * -0x1.fffffep+126 = -0x1.fffffep+127
  comp32(single_of_bits(0x40000000) * single_of_bits(0x7e800003), 0x7f000003, STR(__LINE__)); // 0x1p+1 * 0x1.000006p+126 = 0x1.000006p+127
  comp32(single_of_bits(0x7e800003) * single_of_bits(0x40000000), 0x7f000003, STR(__LINE__)); // 0x1.000006p+126 * 0x1p+1 = 0x1.000006p+127
  comp32(single_of_bits(0xc0000000) * single_of_bits(0xfe800003), 0x7f000003, STR(__LINE__)); // -0x1p+1 * -0x1.000006p+126 = 0x1.000006p+127
  comp32(single_of_bits(0xfe800003) * single_of_bits(0xc0000000), 0x7f000003, STR(__LINE__)); // -0x1.000006p+126 * -0x1p+1 = 0x1.000006p+127
  comp32(single_of_bits(0x40000000) * single_of_bits(0xfe800003), 0xff000003, STR(__LINE__)); // 0x1p+1 * -0x1.000006p+126 = -0x1.000006p+127
  comp32(single_of_bits(0xfe800003) * single_of_bits(0x40000000), 0xff000003, STR(__LINE__)); // -0x1.000006p+126 * 0x1p+1 = -0x1.000006p+127
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x7e800003), 0xff000003, STR(__LINE__)); // -0x1p+1 * 0x1.000006p+126 = -0x1.000006p+127
  comp32(single_of_bits(0x7e800003) * single_of_bits(0xc0000000), 0xff000003, STR(__LINE__)); // 0x1.000006p+126 * -0x1p+1 = -0x1.000006p+127
  comp32(single_of_bits(0x40000000) * single_of_bits(0x7e800001), 0x7f000001, STR(__LINE__)); // 0x1p+1 * 0x1.000002p+126 = 0x1.000002p+127
}

void f436(void) {
  comp32(single_of_bits(0x7e800001) * single_of_bits(0x40000000), 0x7f000001, STR(__LINE__)); // 0x1.000002p+126 * 0x1p+1 = 0x1.000002p+127
  comp32(single_of_bits(0xc0000000) * single_of_bits(0xfe800001), 0x7f000001, STR(__LINE__)); // -0x1p+1 * -0x1.000002p+126 = 0x1.000002p+127
  comp32(single_of_bits(0xfe800001) * single_of_bits(0xc0000000), 0x7f000001, STR(__LINE__)); // -0x1.000002p+126 * -0x1p+1 = 0x1.000002p+127
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x7e800001), 0xff000001, STR(__LINE__)); // -0x1p+1 * 0x1.000002p+126 = -0x1.000002p+127
  comp32(single_of_bits(0x7e800001) * single_of_bits(0xc0000000), 0xff000001, STR(__LINE__)); // 0x1.000002p+126 * -0x1p+1 = -0x1.000002p+127
  comp32(single_of_bits(0x40000000) * single_of_bits(0xfe800001), 0xff000001, STR(__LINE__)); // 0x1p+1 * -0x1.000002p+126 = -0x1.000002p+127
  comp32(single_of_bits(0xfe800001) * single_of_bits(0x40000000), 0xff000001, STR(__LINE__)); // -0x1.000002p+126 * 0x1p+1 = -0x1.000002p+127
  comp32(single_of_bits(0x40000000) * single_of_bits(0x7e800000), 0x7f000000, STR(__LINE__)); // 0x1p+1 * 0x1p+126 = 0x1p+127
  comp32(single_of_bits(0x7e800000) * single_of_bits(0x40000000), 0x7f000000, STR(__LINE__)); // 0x1p+126 * 0x1p+1 = 0x1p+127
  comp32(single_of_bits(0x7e800000) * single_of_bits(0xc0000000), 0xff000000, STR(__LINE__)); // 0x1p+126 * -0x1p+1 = -0x1p+127
}

void f437(void) {
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x7e800000), 0xff000000, STR(__LINE__)); // -0x1p+1 * 0x1p+126 = -0x1p+127
  comp32(single_of_bits(0x40000000) * single_of_bits(0x7e7fffff), 0x7effffff, STR(__LINE__)); // 0x1p+1 * 0x1.fffffep+125 = 0x1.fffffep+126
  comp32(single_of_bits(0x7e7fffff) * single_of_bits(0x40000000), 0x7effffff, STR(__LINE__)); // 0x1.fffffep+125 * 0x1p+1 = 0x1.fffffep+126
  comp32(single_of_bits(0xc0000000) * single_of_bits(0xfe7fffff), 0x7effffff, STR(__LINE__)); // -0x1p+1 * -0x1.fffffep+125 = 0x1.fffffep+126
  comp32(single_of_bits(0xfe7fffff) * single_of_bits(0xc0000000), 0x7effffff, STR(__LINE__)); // -0x1.fffffep+125 * -0x1p+1 = 0x1.fffffep+126
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x7e7fffff), 0xfeffffff, STR(__LINE__)); // -0x1p+1 * 0x1.fffffep+125 = -0x1.fffffep+126
  comp32(single_of_bits(0x7e7fffff) * single_of_bits(0xc0000000), 0xfeffffff, STR(__LINE__)); // 0x1.fffffep+125 * -0x1p+1 = -0x1.fffffep+126
  comp32(single_of_bits(0x40000000) * single_of_bits(0xfe7fffff), 0xfeffffff, STR(__LINE__)); // 0x1p+1 * -0x1.fffffep+125 = -0x1.fffffep+126
  comp32(single_of_bits(0xfe7fffff) * single_of_bits(0x40000000), 0xfeffffff, STR(__LINE__)); // -0x1.fffffep+125 * 0x1p+1 = -0x1.fffffep+126
  comp32(single_of_bits(0x40000000) * single_of_bits(0x7e7ffffd), 0x7efffffd, STR(__LINE__)); // 0x1p+1 * 0x1.fffffap+125 = 0x1.fffffap+126
}

void f438(void) {
  comp32(single_of_bits(0x7e7ffffd) * single_of_bits(0x40000000), 0x7efffffd, STR(__LINE__)); // 0x1.fffffap+125 * 0x1p+1 = 0x1.fffffap+126
  comp32(single_of_bits(0xc0000000) * single_of_bits(0xfe7ffffd), 0x7efffffd, STR(__LINE__)); // -0x1p+1 * -0x1.fffffap+125 = 0x1.fffffap+126
  comp32(single_of_bits(0xfe7ffffd) * single_of_bits(0xc0000000), 0x7efffffd, STR(__LINE__)); // -0x1.fffffap+125 * -0x1p+1 = 0x1.fffffap+126
  comp32(single_of_bits(0x40000000) * single_of_bits(0xfe7ffffd), 0xfefffffd, STR(__LINE__)); // 0x1p+1 * -0x1.fffffap+125 = -0x1.fffffap+126
  comp32(single_of_bits(0xfe7ffffd) * single_of_bits(0x40000000), 0xfefffffd, STR(__LINE__)); // -0x1.fffffap+125 * 0x1p+1 = -0x1.fffffap+126
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x7e7ffffd), 0xfefffffd, STR(__LINE__)); // -0x1p+1 * 0x1.fffffap+125 = -0x1.fffffap+126
  comp32(single_of_bits(0x7e7ffffd) * single_of_bits(0xc0000000), 0xfefffffd, STR(__LINE__)); // 0x1.fffffap+125 * -0x1p+1 = -0x1.fffffap+126
  comp32(single_of_bits(0x40000000) * single_of_bits(0x00800000), 0x01000000, STR(__LINE__)); // 0x1p+1 * 0x1p-126 = 0x1p-125
  comp32(single_of_bits(0x00800000) * single_of_bits(0x40000000), 0x01000000, STR(__LINE__)); // 0x1p-126 * 0x1p+1 = 0x1p-125
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x80800000), 0x01000000, STR(__LINE__)); // -0x1p+1 * -0x1p-126 = 0x1p-125
}

void f439(void) {
  comp32(single_of_bits(0x80800000) * single_of_bits(0xc0000000), 0x01000000, STR(__LINE__)); // -0x1p-126 * -0x1p+1 = 0x1p-125
  comp32(single_of_bits(0x00800000) * single_of_bits(0xc0000000), 0x81000000, STR(__LINE__)); // 0x1p-126 * -0x1p+1 = -0x1p-125
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x00800000), 0x81000000, STR(__LINE__)); // -0x1p+1 * 0x1p-126 = -0x1p-125
  comp32(single_of_bits(0x80800000) * single_of_bits(0x40000000), 0x81000000, STR(__LINE__)); // -0x1p-126 * 0x1p+1 = -0x1p-125
  comp32(single_of_bits(0x40000000) * single_of_bits(0x80800000), 0x81000000, STR(__LINE__)); // 0x1p+1 * -0x1p-126 = -0x1p-125
  comp32(single_of_bits(0x40000000) * single_of_bits(0x00800001), 0x01000001, STR(__LINE__)); // 0x1p+1 * 0x1.000002p-126 = 0x1.000002p-125
  comp32(single_of_bits(0x00800001) * single_of_bits(0x40000000), 0x01000001, STR(__LINE__)); // 0x1.000002p-126 * 0x1p+1 = 0x1.000002p-125
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x80800001), 0x01000001, STR(__LINE__)); // -0x1p+1 * -0x1.000002p-126 = 0x1.000002p-125
  comp32(single_of_bits(0x80800001) * single_of_bits(0xc0000000), 0x01000001, STR(__LINE__)); // -0x1.000002p-126 * -0x1p+1 = 0x1.000002p-125
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x00800001), 0x81000001, STR(__LINE__)); // -0x1p+1 * 0x1.000002p-126 = -0x1.000002p-125
}

void f440(void) {
  comp32(single_of_bits(0x00800001) * single_of_bits(0xc0000000), 0x81000001, STR(__LINE__)); // 0x1.000002p-126 * -0x1p+1 = -0x1.000002p-125
  comp32(single_of_bits(0x40000000) * single_of_bits(0x80800001), 0x81000001, STR(__LINE__)); // 0x1p+1 * -0x1.000002p-126 = -0x1.000002p-125
  comp32(single_of_bits(0x80800001) * single_of_bits(0x40000000), 0x81000001, STR(__LINE__)); // -0x1.000002p-126 * 0x1p+1 = -0x1.000002p-125
  comp32(single_of_bits(0x40000000) * single_of_bits(0x00800003), 0x01000003, STR(__LINE__)); // 0x1p+1 * 0x1.000006p-126 = 0x1.000006p-125
  comp32(single_of_bits(0x00800003) * single_of_bits(0x40000000), 0x01000003, STR(__LINE__)); // 0x1.000006p-126 * 0x1p+1 = 0x1.000006p-125
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x80800003), 0x01000003, STR(__LINE__)); // -0x1p+1 * -0x1.000006p-126 = 0x1.000006p-125
  comp32(single_of_bits(0x80800003) * single_of_bits(0xc0000000), 0x01000003, STR(__LINE__)); // -0x1.000006p-126 * -0x1p+1 = 0x1.000006p-125
  comp32(single_of_bits(0x80800003) * single_of_bits(0xc0000000), 0x01000003, STR(__LINE__)); // -0x1.000006p-126 * -0x1p+1 = 0x1.000006p-125
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x80800003), 0x01000003, STR(__LINE__)); // -0x1p+1 * -0x1.000006p-126 = 0x1.000006p-125
  comp32(single_of_bits(0x40000000) * single_of_bits(0x80800003), 0x81000003, STR(__LINE__)); // 0x1p+1 * -0x1.000006p-126 = -0x1.000006p-125
}

void f441(void) {
  comp32(single_of_bits(0x80800003) * single_of_bits(0x40000000), 0x81000003, STR(__LINE__)); // -0x1.000006p-126 * 0x1p+1 = -0x1.000006p-125
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x00800003), 0x81000003, STR(__LINE__)); // -0x1p+1 * 0x1.000006p-126 = -0x1.000006p-125
  comp32(single_of_bits(0x00800003) * single_of_bits(0xc0000000), 0x81000003, STR(__LINE__)); // 0x1.000006p-126 * -0x1p+1 = -0x1.000006p-125
  comp32(single_of_bits(0x40000000) * single_of_bits(0x00800005), 0x01000005, STR(__LINE__)); // 0x1p+1 * 0x1.00000ap-126 = 0x1.00000ap-125
  comp32(single_of_bits(0x00800005) * single_of_bits(0x40000000), 0x01000005, STR(__LINE__)); // 0x1.00000ap-126 * 0x1p+1 = 0x1.00000ap-125
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x80800005), 0x01000005, STR(__LINE__)); // -0x1p+1 * -0x1.00000ap-126 = 0x1.00000ap-125
  comp32(single_of_bits(0x80800005) * single_of_bits(0xc0000000), 0x01000005, STR(__LINE__)); // -0x1.00000ap-126 * -0x1p+1 = 0x1.00000ap-125
  comp32(single_of_bits(0x40000000) * single_of_bits(0x80800005), 0x81000005, STR(__LINE__)); // 0x1p+1 * -0x1.00000ap-126 = -0x1.00000ap-125
  comp32(single_of_bits(0x80800005) * single_of_bits(0x40000000), 0x81000005, STR(__LINE__)); // -0x1.00000ap-126 * 0x1p+1 = -0x1.00000ap-125
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x00800005), 0x81000005, STR(__LINE__)); // -0x1p+1 * 0x1.00000ap-126 = -0x1.00000ap-125
}

void f442(void) {
  comp32(single_of_bits(0x00800005) * single_of_bits(0xc0000000), 0x81000005, STR(__LINE__)); // 0x1.00000ap-126 * -0x1p+1 = -0x1.00000ap-125
  comp32(single_of_bits(0x40000000) * single_of_bits(0x00800009), 0x01000009, STR(__LINE__)); // 0x1p+1 * 0x1.000012p-126 = 0x1.000012p-125
  comp32(single_of_bits(0x00800009) * single_of_bits(0x40000000), 0x01000009, STR(__LINE__)); // 0x1.000012p-126 * 0x1p+1 = 0x1.000012p-125
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x80800009), 0x01000009, STR(__LINE__)); // -0x1p+1 * -0x1.000012p-126 = 0x1.000012p-125
  comp32(single_of_bits(0x80800009) * single_of_bits(0xc0000000), 0x01000009, STR(__LINE__)); // -0x1.000012p-126 * -0x1p+1 = 0x1.000012p-125
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x00800009), 0x81000009, STR(__LINE__)); // -0x1p+1 * 0x1.000012p-126 = -0x1.000012p-125
  comp32(single_of_bits(0x00800009) * single_of_bits(0xc0000000), 0x81000009, STR(__LINE__)); // 0x1.000012p-126 * -0x1p+1 = -0x1.000012p-125
  comp32(single_of_bits(0x40000000) * single_of_bits(0x80800009), 0x81000009, STR(__LINE__)); // 0x1p+1 * -0x1.000012p-126 = -0x1.000012p-125
  comp32(single_of_bits(0x80800009) * single_of_bits(0x40000000), 0x81000009, STR(__LINE__)); // -0x1.000012p-126 * 0x1p+1 = -0x1.000012p-125
  comp32(single_of_bits(0x40800000) * single_of_bits(0x7e7fffff), 0x7f7fffff, STR(__LINE__)); // 0x1p+2 * 0x1.fffffep+125 = 0x1.fffffep+127
}

void f443(void) {
  comp32(single_of_bits(0x7e7fffff) * single_of_bits(0x40800000), 0x7f7fffff, STR(__LINE__)); // 0x1.fffffep+125 * 0x1p+2 = 0x1.fffffep+127
  comp32(single_of_bits(0xc0800000) * single_of_bits(0x7e7fffff), 0xff7fffff, STR(__LINE__)); // -0x1p+2 * 0x1.fffffep+125 = -0x1.fffffep+127
  comp32(single_of_bits(0x7e7fffff) * single_of_bits(0xc0800000), 0xff7fffff, STR(__LINE__)); // 0x1.fffffep+125 * -0x1p+2 = -0x1.fffffep+127
  comp32(single_of_bits(0x40800000) * single_of_bits(0xfe7fffff), 0xff7fffff, STR(__LINE__)); // 0x1p+2 * -0x1.fffffep+125 = -0x1.fffffep+127
  comp32(single_of_bits(0xfe7fffff) * single_of_bits(0x40800000), 0xff7fffff, STR(__LINE__)); // -0x1.fffffep+125 * 0x1p+2 = -0x1.fffffep+127
  comp32(single_of_bits(0xc0800000) * single_of_bits(0xfe7fffff), 0x7f7fffff, STR(__LINE__)); // -0x1p+2 * -0x1.fffffep+125 = 0x1.fffffep+127
  comp32(single_of_bits(0xfe7fffff) * single_of_bits(0xc0800000), 0x7f7fffff, STR(__LINE__)); // -0x1.fffffep+125 * -0x1p+2 = 0x1.fffffep+127
  comp32(single_of_bits(0x7e7ffffd) * single_of_bits(0x40800000), 0x7f7ffffd, STR(__LINE__)); // 0x1.fffffap+125 * 0x1p+2 = 0x1.fffffap+127
  comp32(single_of_bits(0x40800000) * single_of_bits(0x7e7ffffd), 0x7f7ffffd, STR(__LINE__)); // 0x1p+2 * 0x1.fffffap+125 = 0x1.fffffap+127
  comp32(single_of_bits(0x7e7ffffd) * single_of_bits(0xc0800000), 0xff7ffffd, STR(__LINE__)); // 0x1.fffffap+125 * -0x1p+2 = -0x1.fffffap+127
}

void f444(void) {
  comp32(single_of_bits(0xc0800000) * single_of_bits(0x7e7ffffd), 0xff7ffffd, STR(__LINE__)); // -0x1p+2 * 0x1.fffffap+125 = -0x1.fffffap+127
  comp32(single_of_bits(0xfe7ffffd) * single_of_bits(0x40800000), 0xff7ffffd, STR(__LINE__)); // -0x1.fffffap+125 * 0x1p+2 = -0x1.fffffap+127
  comp32(single_of_bits(0x40800000) * single_of_bits(0xfe7ffffd), 0xff7ffffd, STR(__LINE__)); // 0x1p+2 * -0x1.fffffap+125 = -0x1.fffffap+127
  comp32(single_of_bits(0xfe7ffffd) * single_of_bits(0xc0800000), 0x7f7ffffd, STR(__LINE__)); // -0x1.fffffap+125 * -0x1p+2 = 0x1.fffffap+127
  comp32(single_of_bits(0xc0800000) * single_of_bits(0xfe7ffffd), 0x7f7ffffd, STR(__LINE__)); // -0x1p+2 * -0x1.fffffap+125 = 0x1.fffffap+127
  comp32(single_of_bits(0x3b000000) * single_of_bits(0x43800000), 0x3f000000, STR(__LINE__)); // 0x1p-9 * 0x1p+8 = 0x1p-1
  comp32(single_of_bits(0x43800000) * single_of_bits(0x3b000000), 0x3f000000, STR(__LINE__)); // 0x1p+8 * 0x1p-9 = 0x1p-1
  comp32(single_of_bits(0xbb000000) * single_of_bits(0xc3800000), 0x3f000000, STR(__LINE__)); // -0x1p-9 * -0x1p+8 = 0x1p-1
  comp32(single_of_bits(0xc3800000) * single_of_bits(0xbb000000), 0x3f000000, STR(__LINE__)); // -0x1p+8 * -0x1p-9 = 0x1p-1
  comp32(single_of_bits(0xbb000000) * single_of_bits(0x43800000), 0xbf000000, STR(__LINE__)); // -0x1p-9 * 0x1p+8 = -0x1p-1
}

void f445(void) {
  comp32(single_of_bits(0x43800000) * single_of_bits(0xbb000000), 0xbf000000, STR(__LINE__)); // 0x1p+8 * -0x1p-9 = -0x1p-1
  comp32(single_of_bits(0xc3800000) * single_of_bits(0x3b000000), 0xbf000000, STR(__LINE__)); // -0x1p+8 * 0x1p-9 = -0x1p-1
  comp32(single_of_bits(0x3b000000) * single_of_bits(0xc3800000), 0xbf000000, STR(__LINE__)); // 0x1p-9 * -0x1p+8 = -0x1p-1
  comp32(single_of_bits(0x3e000000) * single_of_bits(0x3c800000), 0x3b000000, STR(__LINE__)); // 0x1p-3 * 0x1p-6 = 0x1p-9
  comp32(single_of_bits(0x3c800000) * single_of_bits(0x3e000000), 0x3b000000, STR(__LINE__)); // 0x1p-6 * 0x1p-3 = 0x1p-9
  comp32(single_of_bits(0xbe000000) * single_of_bits(0xbc800000), 0x3b000000, STR(__LINE__)); // -0x1p-3 * -0x1p-6 = 0x1p-9
  comp32(single_of_bits(0xbc800000) * single_of_bits(0xbe000000), 0x3b000000, STR(__LINE__)); // -0x1p-6 * -0x1p-3 = 0x1p-9
  comp32(single_of_bits(0xbe000000) * single_of_bits(0x3c800000), 0xbb000000, STR(__LINE__)); // -0x1p-3 * 0x1p-6 = -0x1p-9
  comp32(single_of_bits(0x3c800000) * single_of_bits(0xbe000000), 0xbb000000, STR(__LINE__)); // 0x1p-6 * -0x1p-3 = -0x1p-9
  comp32(single_of_bits(0xbc800000) * single_of_bits(0x3e000000), 0xbb000000, STR(__LINE__)); // -0x1p-6 * 0x1p-3 = -0x1p-9
}

void f446(void) {
  comp32(single_of_bits(0x3e000000) * single_of_bits(0xbc800000), 0xbb000000, STR(__LINE__)); // 0x1p-3 * -0x1p-6 = -0x1p-9
  comp32(single_of_bits(0x41000000) * single_of_bits(0x44000000), 0x45800000, STR(__LINE__)); // 0x1p+3 * 0x1p+9 = 0x1p+12
  comp32(single_of_bits(0x44000000) * single_of_bits(0x41000000), 0x45800000, STR(__LINE__)); // 0x1p+9 * 0x1p+3 = 0x1p+12
  comp32(single_of_bits(0xc1000000) * single_of_bits(0xc4000000), 0x45800000, STR(__LINE__)); // -0x1p+3 * -0x1p+9 = 0x1p+12
  comp32(single_of_bits(0xc4000000) * single_of_bits(0xc1000000), 0x45800000, STR(__LINE__)); // -0x1p+9 * -0x1p+3 = 0x1p+12
  comp32(single_of_bits(0xc1000000) * single_of_bits(0x44000000), 0xc5800000, STR(__LINE__)); // -0x1p+3 * 0x1p+9 = -0x1p+12
  comp32(single_of_bits(0x44000000) * single_of_bits(0xc1000000), 0xc5800000, STR(__LINE__)); // 0x1p+9 * -0x1p+3 = -0x1p+12
  comp32(single_of_bits(0xc4000000) * single_of_bits(0x41000000), 0xc5800000, STR(__LINE__)); // -0x1p+9 * 0x1p+3 = -0x1p+12
  comp32(single_of_bits(0x41000000) * single_of_bits(0xc4000000), 0xc5800000, STR(__LINE__)); // 0x1p+3 * -0x1p+9 = -0x1p+12
  comp32(single_of_bits(0x00000000) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x0p+0 = 0x0p+0
}

void f447(void) {
  comp32(single_of_bits(0x80000000) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x00000001) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1p-149 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x00000001), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p-149 = 0x0p+0
  comp32(single_of_bits(0x80000001) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1p-149 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x80000001), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p-149 = 0x0p+0
  comp32(single_of_bits(0x80000001) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1p-149 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x80000001), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1p-149 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x00000001), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1p-149 = -0x0p+0
}

void f448(void) {
  comp32(single_of_bits(0x00000001) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1p-149 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x00000002), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p-148 = 0x0p+0
  comp32(single_of_bits(0x00000002) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1p-148 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x80000002), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p-148 = 0x0p+0
  comp32(single_of_bits(0x80000002) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1p-148 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x80000002), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1p-148 = -0x0p+0
  comp32(single_of_bits(0x80000002) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1p-148 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x00000002), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1p-148 = -0x0p+0
  comp32(single_of_bits(0x00000002) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1p-148 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000003) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1.8p-148 * 0x0p+0 = 0x0p+0
}

void f449(void) {
  comp32(single_of_bits(0x00000000) * single_of_bits(0x00000003), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.8p-148 = 0x0p+0
  comp32(single_of_bits(0x80000003) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1.8p-148 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x80000003), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.8p-148 = 0x0p+0
  comp32(single_of_bits(0x80000003) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1.8p-148 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x80000003), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1.8p-148 = -0x0p+0
  comp32(single_of_bits(0x00000003) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1.8p-148 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x00000003), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1.8p-148 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x00000004), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p-147 = 0x0p+0
  comp32(single_of_bits(0x00000004) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1p-147 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x80000004), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p-147 = 0x0p+0
}

void f450(void) {
  comp32(single_of_bits(0x80000004) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1p-147 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x00000004) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1p-147 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x00000004), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1p-147 = -0x0p+0
  comp32(single_of_bits(0x80000004) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1p-147 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x80000004), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1p-147 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x007fffff), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.fffffcp-127 = 0x0p+0
  comp32(single_of_bits(0x007fffff) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1.fffffcp-127 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x807fffff), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.fffffcp-127 = 0x0p+0
  comp32(single_of_bits(0x807fffff) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1.fffffcp-127 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x807fffff) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1.fffffcp-127 * 0x0p+0 = -0x0p+0
}

void f451(void) {
  comp32(single_of_bits(0x00000000) * single_of_bits(0x807fffff), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1.fffffcp-127 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x3f800000), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p+0 = 0x0p+0
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1p+0 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0xbf800000), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p+0 = 0x0p+0
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1p+0 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x3f800000), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1p+0 = -0x0p+0
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1p+0 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1p+0 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0xbf800000), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1p+0 = -0x0p+0
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1p+1 * 0x0p+0 = -0x0p+0
}

void f452(void) {
  comp32(single_of_bits(0x00000000) * single_of_bits(0xc0000000), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1p+1 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x40400000), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.8p+1 = 0x0p+0
  comp32(single_of_bits(0x40400000) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1.8p+1 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0xc0400000), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.8p+1 = 0x0p+0
  comp32(single_of_bits(0xc0400000) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1.8p+1 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0xc0400000), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1.8p+1 = -0x0p+0
  comp32(single_of_bits(0xc0400000) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1.8p+1 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x40400000), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1.8p+1 = -0x0p+0
  comp32(single_of_bits(0x40400000) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1.8p+1 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x40800000) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1p+2 * 0x0p+0 = 0x0p+0
}

void f453(void) {
  comp32(single_of_bits(0x00000000) * single_of_bits(0x40800000), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p+2 = 0x0p+0
  comp32(single_of_bits(0xc0800000) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1p+2 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0xc0800000), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p+2 = 0x0p+0
  comp32(single_of_bits(0xc0800000) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1p+2 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0xc0800000), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1p+2 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x40800000), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1p+2 = -0x0p+0
  comp32(single_of_bits(0x40800000) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1p+2 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x40a00000) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1.4p+2 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x40a00000), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.4p+2 = 0x0p+0
  comp32(single_of_bits(0xc0a00000) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1.4p+2 * -0x0p+0 = 0x0p+0
}

void f454(void) {
  comp32(single_of_bits(0x80000000) * single_of_bits(0xc0a00000), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.4p+2 = 0x0p+0
  comp32(single_of_bits(0xc0a00000) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1.4p+2 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0xc0a00000), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1.4p+2 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x40a00000), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1.4p+2 = -0x0p+0
  comp32(single_of_bits(0x40a00000) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1.4p+2 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x40c00000) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1.8p+2 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x40c00000), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.8p+2 = 0x0p+0
  comp32(single_of_bits(0xc0c00000) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1.8p+2 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0xc0c00000), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.8p+2 = 0x0p+0
  comp32(single_of_bits(0xc0c00000) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1.8p+2 * 0x0p+0 = -0x0p+0
}

void f455(void) {
  comp32(single_of_bits(0x00000000) * single_of_bits(0xc0c00000), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1.8p+2 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x40c00000), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1.8p+2 = -0x0p+0
  comp32(single_of_bits(0x40c00000) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1.8p+2 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x40e00000) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1.cp+2 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x40e00000), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.cp+2 = 0x0p+0
  comp32(single_of_bits(0xc0e00000) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1.cp+2 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0xc0e00000), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.cp+2 = 0x0p+0
  comp32(single_of_bits(0xc0e00000) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1.cp+2 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0xc0e00000), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1.cp+2 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x40e00000), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1.cp+2 = -0x0p+0
}

void f456(void) {
  comp32(single_of_bits(0x40e00000) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1.cp+2 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x41000000) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1p+3 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x41000000), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p+3 = 0x0p+0
  comp32(single_of_bits(0xc1000000) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1p+3 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0xc1000000), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p+3 = 0x0p+0
  comp32(single_of_bits(0xc1000000) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1p+3 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0xc1000000), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1p+3 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x41000000), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1p+3 = -0x0p+0
  comp32(single_of_bits(0x41000000) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1p+3 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x7f000000) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1p+127 * 0x0p+0 = 0x0p+0
}

void f457(void) {
  comp32(single_of_bits(0x00000000) * single_of_bits(0x7f000000), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p+127 = 0x0p+0
  comp32(single_of_bits(0xff000000) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1p+127 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0xff000000), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p+127 = 0x0p+0
  comp32(single_of_bits(0xff000000) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1p+127 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0xff000000), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1p+127 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x7f000000), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1p+127 = -0x0p+0
  comp32(single_of_bits(0x7f000000) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1p+127 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x7e800000) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1p+126 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x7e800000), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p+126 = 0x0p+0
  comp32(single_of_bits(0xfe800000) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1p+126 * -0x0p+0 = 0x0p+0
}

void f458(void) {
  comp32(single_of_bits(0x80000000) * single_of_bits(0xfe800000), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p+126 = 0x0p+0
  comp32(single_of_bits(0xfe800000) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1p+126 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0xfe800000), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1p+126 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x7e800000), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1p+126 = -0x0p+0
  comp32(single_of_bits(0x7e800000) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1p+126 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x7effffff) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1.fffffep+126 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x7effffff), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.fffffep+126 = 0x0p+0
  comp32(single_of_bits(0xfeffffff) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1.fffffep+126 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0xfeffffff), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.fffffep+126 = 0x0p+0
  comp32(single_of_bits(0xfeffffff) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1.fffffep+126 * 0x0p+0 = -0x0p+0
}

void f459(void) {
  comp32(single_of_bits(0x00000000) * single_of_bits(0xfeffffff), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1.fffffep+126 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x7effffff), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1.fffffep+126 = -0x0p+0
  comp32(single_of_bits(0x7effffff) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1.fffffep+126 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x7e7fffff) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1.fffffep+125 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x7e7fffff), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.fffffep+125 = 0x0p+0
  comp32(single_of_bits(0xfe7fffff) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1.fffffep+125 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0xfe7fffff), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.fffffep+125 = 0x0p+0
  comp32(single_of_bits(0xfe7fffff) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1.fffffep+125 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0xfe7fffff), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1.fffffep+125 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x7e7fffff), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1.fffffep+125 = -0x0p+0
}

void f460(void) {
  comp32(single_of_bits(0x7e7fffff) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1.fffffep+125 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x7f7fffff), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.fffffep+127 = 0x0p+0
  comp32(single_of_bits(0x7f7fffff) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1.fffffep+127 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0xff7fffff) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1.fffffep+127 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0xff7fffff), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.fffffep+127 = 0x0p+0
  comp32(single_of_bits(0xff7fffff) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1.fffffep+127 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0xff7fffff), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1.fffffep+127 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x7f7fffff), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1.fffffep+127 = -0x0p+0
  comp32(single_of_bits(0x7f7fffff) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1.fffffep+127 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x00800000), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p-126 = 0x0p+0
}

void f461(void) {
  comp32(single_of_bits(0x00800000) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1p-126 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80800000) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1p-126 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x80800000), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p-126 = 0x0p+0
  comp32(single_of_bits(0x80800000) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1p-126 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x80800000), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1p-126 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x00800000), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1p-126 = -0x0p+0
  comp32(single_of_bits(0x00800000) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1p-126 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x01000000), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1p-125 = 0x0p+0
  comp32(single_of_bits(0x01000000) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1p-125 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x81000000) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1p-125 * -0x0p+0 = 0x0p+0
}

void f462(void) {
  comp32(single_of_bits(0x80000000) * single_of_bits(0x81000000), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1p-125 = 0x0p+0
  comp32(single_of_bits(0x81000000) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1p-125 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x81000000), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1p-125 = -0x0p+0
  comp32(single_of_bits(0x01000000) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1p-125 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x01000000), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1p-125 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x00ffffff), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.fffffep-126 = 0x0p+0
  comp32(single_of_bits(0x00ffffff) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1.fffffep-126 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80ffffff) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1.fffffep-126 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x80ffffff), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.fffffep-126 = 0x0p+0
  comp32(single_of_bits(0x80ffffff) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1.fffffep-126 * 0x0p+0 = -0x0p+0
}

void f463(void) {
  comp32(single_of_bits(0x00000000) * single_of_bits(0x80ffffff), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1.fffffep-126 = -0x0p+0
  comp32(single_of_bits(0x00ffffff) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1.fffffep-126 * -0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x00ffffff), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1.fffffep-126 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x00800001), 0x00000000, STR(__LINE__)); // 0x0p+0 * 0x1.000002p-126 = 0x0p+0
  comp32(single_of_bits(0x00800001) * single_of_bits(0x00000000), 0x00000000, STR(__LINE__)); // 0x1.000002p-126 * 0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80800001) * single_of_bits(0x80000000), 0x00000000, STR(__LINE__)); // -0x1.000002p-126 * -0x0p+0 = 0x0p+0
  comp32(single_of_bits(0x80000000) * single_of_bits(0x80800001), 0x00000000, STR(__LINE__)); // -0x0p+0 * -0x1.000002p-126 = 0x0p+0
  comp32(single_of_bits(0x80800001) * single_of_bits(0x00000000), 0x80000000, STR(__LINE__)); // -0x1.000002p-126 * 0x0p+0 = -0x0p+0
  comp32(single_of_bits(0x00000000) * single_of_bits(0x80800001), 0x80000000, STR(__LINE__)); // 0x0p+0 * -0x1.000002p-126 = -0x0p+0
  comp32(single_of_bits(0x00800001) * single_of_bits(0x80000000), 0x80000000, STR(__LINE__)); // 0x1.000002p-126 * -0x0p+0 = -0x0p+0
}

void f464(void) {
  comp32(single_of_bits(0x80000000) * single_of_bits(0x00800001), 0x80000000, STR(__LINE__)); // -0x0p+0 * 0x1.000002p-126 = -0x0p+0
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x00000000), 0x7fc00000, STR(__LINE__)); // inf * 0x0p+0 = nan
  comp32(single_of_bits(0x00000000) * single_of_bits(0x7f800000), 0x7fc00000, STR(__LINE__)); // 0x0p+0 * inf = nan
  comp32(single_of_bits(0x80000000) * single_of_bits(0xff800000), 0x7fc00000, STR(__LINE__)); // -0x0p+0 * -inf = nan
  comp32(single_of_bits(0xff800000) * single_of_bits(0x80000000), 0x7fc00000, STR(__LINE__)); // -inf * -0x0p+0 = nan
  comp32(single_of_bits(0x80000000) * single_of_bits(0x7f800000), 0xffc00000, STR(__LINE__)); // -0x0p+0 * inf = -nan
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x80000000), 0xffc00000, STR(__LINE__)); // inf * -0x0p+0 = -nan
  comp32(single_of_bits(0x00000000) * single_of_bits(0xff800000), 0xffc00000, STR(__LINE__)); // 0x0p+0 * -inf = -nan
  comp32(single_of_bits(0xff800000) * single_of_bits(0x00000000), 0xffc00000, STR(__LINE__)); // -inf * 0x0p+0 = -nan
  comp32(single_of_bits(0x7fc00000) * single_of_bits(0x00000000), 0x7fc00000, STR(__LINE__)); // nan * 0x0p+0 = nan
}

void f465(void) {
  comp32(single_of_bits(0x00000000) * single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // 0x0p+0 * nan = nan
  comp32(single_of_bits(0x7fc00000) * single_of_bits(0x80000000), 0x7fc00000, STR(__LINE__)); // nan * -0x0p+0 = nan
  comp32(single_of_bits(0x80000000) * single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -0x0p+0 * nan = nan
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // inf * inf = inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0x7f800000), 0xff800000, STR(__LINE__)); // -inf * inf = -inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // inf * -inf = -inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0xff800000), 0x7f800000, STR(__LINE__)); // -inf * -inf = inf
  comp32(single_of_bits(0x00000001) * single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // 0x1p-149 * inf = inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x00000001), 0x7f800000, STR(__LINE__)); // inf * 0x1p-149 = inf
  comp32(single_of_bits(0x80000001) * single_of_bits(0xff800000), 0x7f800000, STR(__LINE__)); // -0x1p-149 * -inf = inf
}

void f466(void) {
  comp32(single_of_bits(0xff800000) * single_of_bits(0x80000001), 0x7f800000, STR(__LINE__)); // -inf * -0x1p-149 = inf
  comp32(single_of_bits(0x80000001) * single_of_bits(0x7f800000), 0xff800000, STR(__LINE__)); // -0x1p-149 * inf = -inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x80000001), 0xff800000, STR(__LINE__)); // inf * -0x1p-149 = -inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0x00000001), 0xff800000, STR(__LINE__)); // -inf * 0x1p-149 = -inf
  comp32(single_of_bits(0x00000001) * single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // 0x1p-149 * -inf = -inf
  comp32(single_of_bits(0x00000002) * single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // 0x1p-148 * inf = inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x00000002), 0x7f800000, STR(__LINE__)); // inf * 0x1p-148 = inf
  comp32(single_of_bits(0x80000002) * single_of_bits(0xff800000), 0x7f800000, STR(__LINE__)); // -0x1p-148 * -inf = inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0x80000002), 0x7f800000, STR(__LINE__)); // -inf * -0x1p-148 = inf
  comp32(single_of_bits(0x80000002) * single_of_bits(0x7f800000), 0xff800000, STR(__LINE__)); // -0x1p-148 * inf = -inf
}

void f467(void) {
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x80000002), 0xff800000, STR(__LINE__)); // inf * -0x1p-148 = -inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0x00000002), 0xff800000, STR(__LINE__)); // -inf * 0x1p-148 = -inf
  comp32(single_of_bits(0x00000002) * single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // 0x1p-148 * -inf = -inf
  comp32(single_of_bits(0x00000003) * single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // 0x1.8p-148 * inf = inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x00000003), 0x7f800000, STR(__LINE__)); // inf * 0x1.8p-148 = inf
  comp32(single_of_bits(0x80000003) * single_of_bits(0xff800000), 0x7f800000, STR(__LINE__)); // -0x1.8p-148 * -inf = inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0x80000003), 0x7f800000, STR(__LINE__)); // -inf * -0x1.8p-148 = inf
  comp32(single_of_bits(0x80000003) * single_of_bits(0x7f800000), 0xff800000, STR(__LINE__)); // -0x1.8p-148 * inf = -inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x80000003), 0xff800000, STR(__LINE__)); // inf * -0x1.8p-148 = -inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0x00000003), 0xff800000, STR(__LINE__)); // -inf * 0x1.8p-148 = -inf
}

void f468(void) {
  comp32(single_of_bits(0x00000003) * single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // 0x1.8p-148 * -inf = -inf
  comp32(single_of_bits(0x00000004) * single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // 0x1p-147 * inf = inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x00000004), 0x7f800000, STR(__LINE__)); // inf * 0x1p-147 = inf
  comp32(single_of_bits(0x80000004) * single_of_bits(0xff800000), 0x7f800000, STR(__LINE__)); // -0x1p-147 * -inf = inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0x80000004), 0x7f800000, STR(__LINE__)); // -inf * -0x1p-147 = inf
  comp32(single_of_bits(0x80000004) * single_of_bits(0x7f800000), 0xff800000, STR(__LINE__)); // -0x1p-147 * inf = -inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x80000004), 0xff800000, STR(__LINE__)); // inf * -0x1p-147 = -inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0x00000004), 0xff800000, STR(__LINE__)); // -inf * 0x1p-147 = -inf
  comp32(single_of_bits(0x00000004) * single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // 0x1p-147 * -inf = -inf
  comp32(single_of_bits(0x007fffff) * single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // 0x1.fffffcp-127 * inf = inf
}

void f469(void) {
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x007fffff), 0x7f800000, STR(__LINE__)); // inf * 0x1.fffffcp-127 = inf
  comp32(single_of_bits(0x807fffff) * single_of_bits(0xff800000), 0x7f800000, STR(__LINE__)); // -0x1.fffffcp-127 * -inf = inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0x807fffff), 0x7f800000, STR(__LINE__)); // -inf * -0x1.fffffcp-127 = inf
  comp32(single_of_bits(0x807fffff) * single_of_bits(0x7f800000), 0xff800000, STR(__LINE__)); // -0x1.fffffcp-127 * inf = -inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x807fffff), 0xff800000, STR(__LINE__)); // inf * -0x1.fffffcp-127 = -inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0x007fffff), 0xff800000, STR(__LINE__)); // -inf * 0x1.fffffcp-127 = -inf
  comp32(single_of_bits(0x007fffff) * single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // 0x1.fffffcp-127 * -inf = -inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x3f800000), 0x7f800000, STR(__LINE__)); // inf * 0x1p+0 = inf
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // 0x1p+0 * inf = inf
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x7f800000), 0xff800000, STR(__LINE__)); // -0x1p+1 * inf = -inf
}

void f470(void) {
  comp32(single_of_bits(0x7f800000) * single_of_bits(0xc0000000), 0xff800000, STR(__LINE__)); // inf * -0x1p+1 = -inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0xc0400000), 0xff800000, STR(__LINE__)); // inf * -0x1.8p+1 = -inf
  comp32(single_of_bits(0xc0400000) * single_of_bits(0x7f800000), 0xff800000, STR(__LINE__)); // -0x1.8p+1 * inf = -inf
  comp32(single_of_bits(0xc0800000) * single_of_bits(0xff800000), 0x7f800000, STR(__LINE__)); // -0x1p+2 * -inf = inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0xc0800000), 0x7f800000, STR(__LINE__)); // -inf * -0x1p+2 = inf
  comp32(single_of_bits(0x40a00000) * single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // 0x1.4p+2 * inf = inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x40a00000), 0x7f800000, STR(__LINE__)); // inf * 0x1.4p+2 = inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0x40c00000), 0xff800000, STR(__LINE__)); // -inf * 0x1.8p+2 = -inf
  comp32(single_of_bits(0x40c00000) * single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // 0x1.8p+2 * -inf = -inf
  comp32(single_of_bits(0x40e00000) * single_of_bits(0xff800000), 0xff800000, STR(__LINE__)); // 0x1.cp+2 * -inf = -inf
}

void f471(void) {
  comp32(single_of_bits(0xff800000) * single_of_bits(0x40e00000), 0xff800000, STR(__LINE__)); // -inf * 0x1.cp+2 = -inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0xc1000000), 0x7f800000, STR(__LINE__)); // -inf * -0x1p+3 = inf
  comp32(single_of_bits(0xc1000000) * single_of_bits(0xff800000), 0x7f800000, STR(__LINE__)); // -0x1p+3 * -inf = inf
  comp32(single_of_bits(0x7f000000) * single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // 0x1p+127 * inf = inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x7f000000), 0x7f800000, STR(__LINE__)); // inf * 0x1p+127 = inf
  comp32(single_of_bits(0xfe800000) * single_of_bits(0x7f800000), 0xff800000, STR(__LINE__)); // -0x1p+126 * inf = -inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0xfe800000), 0xff800000, STR(__LINE__)); // inf * -0x1p+126 = -inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0xff000000), 0xff800000, STR(__LINE__)); // inf * -0x1p+127 = -inf
  comp32(single_of_bits(0xff000000) * single_of_bits(0x7f800000), 0xff800000, STR(__LINE__)); // -0x1p+127 * inf = -inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0xfe800000), 0x7f800000, STR(__LINE__)); // -inf * -0x1p+126 = inf
}

void f472(void) {
  comp32(single_of_bits(0xfe800000) * single_of_bits(0xff800000), 0x7f800000, STR(__LINE__)); // -0x1p+126 * -inf = inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x7effffff), 0x7f800000, STR(__LINE__)); // inf * 0x1.fffffep+126 = inf
  comp32(single_of_bits(0x7effffff) * single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // 0x1.fffffep+126 * inf = inf
  comp32(single_of_bits(0xfe7fffff) * single_of_bits(0x7f800000), 0xff800000, STR(__LINE__)); // -0x1.fffffep+125 * inf = -inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0xfe7fffff), 0xff800000, STR(__LINE__)); // inf * -0x1.fffffep+125 = -inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0xff7fffff), 0xff800000, STR(__LINE__)); // inf * -0x1.fffffep+127 = -inf
  comp32(single_of_bits(0xff7fffff) * single_of_bits(0x7f800000), 0xff800000, STR(__LINE__)); // -0x1.fffffep+127 * inf = -inf
  comp32(single_of_bits(0xff7fffff) * single_of_bits(0xff800000), 0x7f800000, STR(__LINE__)); // -0x1.fffffep+127 * -inf = inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0xff7fffff), 0x7f800000, STR(__LINE__)); // -inf * -0x1.fffffep+127 = inf
  comp32(single_of_bits(0x00800000) * single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // 0x1p-126 * inf = inf
}

void f473(void) {
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x00800000), 0x7f800000, STR(__LINE__)); // inf * 0x1p-126 = inf
  comp32(single_of_bits(0x81000000) * single_of_bits(0x7f800000), 0xff800000, STR(__LINE__)); // -0x1p-125 * inf = -inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x81000000), 0xff800000, STR(__LINE__)); // inf * -0x1p-125 = -inf
  comp32(single_of_bits(0xff800000) * single_of_bits(0x80800000), 0x7f800000, STR(__LINE__)); // -inf * -0x1p-126 = inf
  comp32(single_of_bits(0x80800000) * single_of_bits(0xff800000), 0x7f800000, STR(__LINE__)); // -0x1p-126 * -inf = inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x00ffffff), 0x7f800000, STR(__LINE__)); // inf * 0x1.fffffep-126 = inf
  comp32(single_of_bits(0x00ffffff) * single_of_bits(0x7f800000), 0x7f800000, STR(__LINE__)); // 0x1.fffffep-126 * inf = inf
  comp32(single_of_bits(0x80800001) * single_of_bits(0x7f800000), 0xff800000, STR(__LINE__)); // -0x1.000002p-126 * inf = -inf
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x80800001), 0xff800000, STR(__LINE__)); // inf * -0x1.000002p-126 = -inf
  comp32(single_of_bits(0x80ffffff) * single_of_bits(0xff800000), 0x7f800000, STR(__LINE__)); // -0x1.fffffep-126 * -inf = inf
}

void f474(void) {
  comp32(single_of_bits(0xff800000) * single_of_bits(0x80ffffff), 0x7f800000, STR(__LINE__)); // -inf * -0x1.fffffep-126 = inf
  comp32(single_of_bits(0x7fc00000) * single_of_bits(0x7f800000), 0x7fc00000, STR(__LINE__)); // nan * inf = nan
  comp32(single_of_bits(0x7f800000) * single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // inf * nan = nan
  comp32(single_of_bits(0x7fc00000) * single_of_bits(0xff800000), 0x7fc00000, STR(__LINE__)); // nan * -inf = nan
  comp32(single_of_bits(0xff800000) * single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -inf * nan = nan
  comp32(single_of_bits(0x7fc00000) * single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // nan * nan = nan
  comp32(single_of_bits(0x007fffff) * single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // 0x1.fffffcp-127 * nan = nan
  comp32(single_of_bits(0x7fc00000) * single_of_bits(0x007fffff), 0x7fc00000, STR(__LINE__)); // nan * 0x1.fffffcp-127 = nan
  comp32(single_of_bits(0x807fffff) * single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -0x1.fffffcp-127 * nan = nan
  comp32(single_of_bits(0x7fc00000) * single_of_bits(0x807fffff), 0x7fc00000, STR(__LINE__)); // nan * -0x1.fffffcp-127 = nan
}

void f475(void) {
  comp32(single_of_bits(0x7fc00000) * single_of_bits(0x00000001), 0x7fc00000, STR(__LINE__)); // nan * 0x1p-149 = nan
  comp32(single_of_bits(0x00000001) * single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // 0x1p-149 * nan = nan
  comp32(single_of_bits(0x7fc00000) * single_of_bits(0x80000001), 0x7fc00000, STR(__LINE__)); // nan * -0x1p-149 = nan
  comp32(single_of_bits(0x80000001) * single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -0x1p-149 * nan = nan
  comp32(single_of_bits(0x7fc00000) * single_of_bits(0x3f800000), 0x7fc00000, STR(__LINE__)); // nan * 0x1p+0 = nan
  comp32(single_of_bits(0x3f800000) * single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // 0x1p+0 * nan = nan
  comp32(single_of_bits(0x7fc00000) * single_of_bits(0xbf800000), 0x7fc00000, STR(__LINE__)); // nan * -0x1p+0 = nan
  comp32(single_of_bits(0xbf800000) * single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -0x1p+0 * nan = nan
  comp32(single_of_bits(0x7fc00000) * single_of_bits(0x7f7fffff), 0x7fc00000, STR(__LINE__)); // nan * 0x1.fffffep+127 = nan
  comp32(single_of_bits(0x7f7fffff) * single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // 0x1.fffffep+127 * nan = nan
}

void f476(void) {
  comp32(single_of_bits(0x7fc00000) * single_of_bits(0xff7fffff), 0x7fc00000, STR(__LINE__)); // nan * -0x1.fffffep+127 = nan
  comp32(single_of_bits(0xff7fffff) * single_of_bits(0x7fc00000), 0x7fc00000, STR(__LINE__)); // -0x1.fffffep+127 * nan = nan
  comp32(single_of_bits(0x7f000000) * single_of_bits(0x40000000), 0x7f800000, STR(__LINE__)); // 0x1p+127 * 0x1p+1 = inf
  comp32(single_of_bits(0x40000000) * single_of_bits(0x7f000000), 0x7f800000, STR(__LINE__)); // 0x1p+1 * 0x1p+127 = inf
  comp32(single_of_bits(0x7f000000) * single_of_bits(0x7f000000), 0x7f800000, STR(__LINE__)); // 0x1p+127 * 0x1p+127 = inf
  comp32(single_of_bits(0x7f000009) * single_of_bits(0x7f7ffffa), 0x7f800000, STR(__LINE__)); // 0x1.000012p+127 * 0x1.fffff4p+127 = inf
  comp32(single_of_bits(0x7f7ffffa) * single_of_bits(0x7f000009), 0x7f800000, STR(__LINE__)); // 0x1.fffff4p+127 * 0x1.000012p+127 = inf
  comp32(single_of_bits(0x7f000000) * single_of_bits(0x7f7ffffe), 0x7f800000, STR(__LINE__)); // 0x1p+127 * 0x1.fffffcp+127 = inf
  comp32(single_of_bits(0x7f7ffffe) * single_of_bits(0x7f000000), 0x7f800000, STR(__LINE__)); // 0x1.fffffcp+127 * 0x1p+127 = inf
  comp32(single_of_bits(0xc09ffffe) * single_of_bits(0xff000000), 0x7f800000, STR(__LINE__)); // -0x1.3ffffcp+2 * -0x1p+127 = inf
}

void f477(void) {
  comp32(single_of_bits(0xff000000) * single_of_bits(0xc09ffffe), 0x7f800000, STR(__LINE__)); // -0x1p+127 * -0x1.3ffffcp+2 = inf
  comp32(single_of_bits(0xc1100001) * single_of_bits(0xff000000), 0x7f800000, STR(__LINE__)); // -0x1.200002p+3 * -0x1p+127 = inf
  comp32(single_of_bits(0xff000000) * single_of_bits(0xc1100001), 0x7f800000, STR(__LINE__)); // -0x1p+127 * -0x1.200002p+3 = inf
  comp32(single_of_bits(0xc0400000) * single_of_bits(0xff000000), 0x7f800000, STR(__LINE__)); // -0x1.8p+1 * -0x1p+127 = inf
  comp32(single_of_bits(0xff000000) * single_of_bits(0xc0400000), 0x7f800000, STR(__LINE__)); // -0x1p+127 * -0x1.8p+1 = inf
  comp32(single_of_bits(0xff000005) * single_of_bits(0xff000001), 0x7f800000, STR(__LINE__)); // -0x1.00000ap+127 * -0x1.000002p+127 = inf
  comp32(single_of_bits(0xff000001) * single_of_bits(0xff000005), 0x7f800000, STR(__LINE__)); // -0x1.000002p+127 * -0x1.00000ap+127 = inf
  comp32(single_of_bits(0xff7fffff) * single_of_bits(0xff7fffff), 0x7f800000, STR(__LINE__)); // -0x1.fffffep+127 * -0x1.fffffep+127 = inf
  comp32(single_of_bits(0xff7ffffd) * single_of_bits(0xff000001), 0x7f800000, STR(__LINE__)); // -0x1.fffffap+127 * -0x1.000002p+127 = inf
  comp32(single_of_bits(0xff000001) * single_of_bits(0xff7ffffd), 0x7f800000, STR(__LINE__)); // -0x1.000002p+127 * -0x1.fffffap+127 = inf
}

void f478(void) {
  comp32(single_of_bits(0xff7ffffd) * single_of_bits(0xc0400001), 0x7f800000, STR(__LINE__)); // -0x1.fffffap+127 * -0x1.800002p+1 = inf
  comp32(single_of_bits(0xc0400001) * single_of_bits(0xff7ffffd), 0x7f800000, STR(__LINE__)); // -0x1.800002p+1 * -0x1.fffffap+127 = inf
  comp32(single_of_bits(0xc03ffffe) * single_of_bits(0x7f000000), 0xff800000, STR(__LINE__)); // -0x1.7ffffcp+1 * 0x1p+127 = -inf
  comp32(single_of_bits(0x7f000000) * single_of_bits(0xc03ffffe), 0xff800000, STR(__LINE__)); // 0x1p+127 * -0x1.7ffffcp+1 = -inf
  comp32(single_of_bits(0xc0dffff9) * single_of_bits(0x7f000000), 0xff800000, STR(__LINE__)); // -0x1.bffff2p+2 * 0x1p+127 = -inf
  comp32(single_of_bits(0x7f000000) * single_of_bits(0xc0dffff9), 0xff800000, STR(__LINE__)); // 0x1p+127 * -0x1.bffff2p+2 = -inf
  comp32(single_of_bits(0xc1100000) * single_of_bits(0x7f000000), 0xff800000, STR(__LINE__)); // -0x1.2p+3 * 0x1p+127 = -inf
  comp32(single_of_bits(0x7f000000) * single_of_bits(0xc1100000), 0xff800000, STR(__LINE__)); // 0x1p+127 * -0x1.2p+3 = -inf
  comp32(single_of_bits(0xff7ffffd) * single_of_bits(0x7f000000), 0xff800000, STR(__LINE__)); // -0x1.fffffap+127 * 0x1p+127 = -inf
  comp32(single_of_bits(0x7f000000) * single_of_bits(0xff7ffffd), 0xff800000, STR(__LINE__)); // 0x1p+127 * -0x1.fffffap+127 = -inf
}

void f479(void) {
  comp32(single_of_bits(0xfe7ffff9) * single_of_bits(0x7f000000), 0xff800000, STR(__LINE__)); // -0x1.fffff2p+125 * 0x1p+127 = -inf
  comp32(single_of_bits(0x7f000000) * single_of_bits(0xfe7ffff9), 0xff800000, STR(__LINE__)); // 0x1p+127 * -0x1.fffff2p+125 = -inf
  comp32(single_of_bits(0xfefffff7) * single_of_bits(0x7e800001), 0xff800000, STR(__LINE__)); // -0x1.ffffeep+126 * 0x1.000002p+126 = -inf
  comp32(single_of_bits(0x7e800001) * single_of_bits(0xfefffff7), 0xff800000, STR(__LINE__)); // 0x1.000002p+126 * -0x1.ffffeep+126 = -inf
  comp32(single_of_bits(0x7f000000) * single_of_bits(0xfe800004), 0xff800000, STR(__LINE__)); // 0x1p+127 * -0x1.000008p+126 = -inf
  comp32(single_of_bits(0xfe800004) * single_of_bits(0x7f000000), 0xff800000, STR(__LINE__)); // -0x1.000008p+126 * 0x1p+127 = -inf
  comp32(single_of_bits(0x7f000000) * single_of_bits(0xfe800000), 0xff800000, STR(__LINE__)); // 0x1p+127 * -0x1p+126 = -inf
  comp32(single_of_bits(0xfe800000) * single_of_bits(0x7f000000), 0xff800000, STR(__LINE__)); // -0x1p+126 * 0x1p+127 = -inf
  comp32(single_of_bits(0x7f000000) * single_of_bits(0xff000000), 0xff800000, STR(__LINE__)); // 0x1p+127 * -0x1p+127 = -inf
  comp32(single_of_bits(0xff000000) * single_of_bits(0x7f000000), 0xff800000, STR(__LINE__)); // -0x1p+127 * 0x1p+127 = -inf
}

void f480(void) {
  comp32(single_of_bits(0x7f000009) * single_of_bits(0xc0c00002), 0xff800000, STR(__LINE__)); // 0x1.000012p+127 * -0x1.800004p+2 = -inf
  comp32(single_of_bits(0xc0c00002) * single_of_bits(0x7f000009), 0xff800000, STR(__LINE__)); // -0x1.800004p+2 * 0x1.000012p+127 = -inf
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x7f7fffff), 0x7f800000, STR(__LINE__)); // 0x1.000002p+0 * 0x1.fffffep+127 = inf
  comp32(single_of_bits(0x7f7fffff) * single_of_bits(0x3f800001), 0x7f800000, STR(__LINE__)); // 0x1.fffffep+127 * 0x1.000002p+0 = inf
  comp32(single_of_bits(0xbf800001) * single_of_bits(0xff7fffff), 0x7f800000, STR(__LINE__)); // -0x1.000002p+0 * -0x1.fffffep+127 = inf
  comp32(single_of_bits(0xff7fffff) * single_of_bits(0xbf800001), 0x7f800000, STR(__LINE__)); // -0x1.fffffep+127 * -0x1.000002p+0 = inf
  comp32(single_of_bits(0x3f800002) * single_of_bits(0x7f7ffffe), 0x7f800000, STR(__LINE__)); // 0x1.000004p+0 * 0x1.fffffcp+127 = inf
  comp32(single_of_bits(0x7f7ffffe) * single_of_bits(0x3f800002), 0x7f800000, STR(__LINE__)); // 0x1.fffffcp+127 * 0x1.000004p+0 = inf
  comp32(single_of_bits(0xbf800002) * single_of_bits(0xff7ffffe), 0x7f800000, STR(__LINE__)); // -0x1.000004p+0 * -0x1.fffffcp+127 = inf
  comp32(single_of_bits(0xff7ffffe) * single_of_bits(0xbf800002), 0x7f800000, STR(__LINE__)); // -0x1.fffffcp+127 * -0x1.000004p+0 = inf
}

void f481(void) {
  comp32(single_of_bits(0x3f800004) * single_of_bits(0x7f7ffffc), 0x7f800000, STR(__LINE__)); // 0x1.000008p+0 * 0x1.fffff8p+127 = inf
  comp32(single_of_bits(0x7f7ffffc) * single_of_bits(0x3f800004), 0x7f800000, STR(__LINE__)); // 0x1.fffff8p+127 * 0x1.000008p+0 = inf
  comp32(single_of_bits(0xbf800004) * single_of_bits(0xff7ffffc), 0x7f800000, STR(__LINE__)); // -0x1.000008p+0 * -0x1.fffff8p+127 = inf
  comp32(single_of_bits(0xff7ffffc) * single_of_bits(0xbf800004), 0x7f800000, STR(__LINE__)); // -0x1.fffff8p+127 * -0x1.000008p+0 = inf
  comp32(single_of_bits(0x3f800008) * single_of_bits(0x7f7ffff8), 0x7f800000, STR(__LINE__)); // 0x1.00001p+0 * 0x1.fffffp+127 = inf
  comp32(single_of_bits(0x7f7ffff8) * single_of_bits(0x3f800008), 0x7f800000, STR(__LINE__)); // 0x1.fffffp+127 * 0x1.00001p+0 = inf
  comp32(single_of_bits(0xbf800008) * single_of_bits(0xff7ffff8), 0x7f800000, STR(__LINE__)); // -0x1.00001p+0 * -0x1.fffffp+127 = inf
  comp32(single_of_bits(0xff7ffff8) * single_of_bits(0xbf800008), 0x7f800000, STR(__LINE__)); // -0x1.fffffp+127 * -0x1.00001p+0 = inf
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x7f7fffff), 0xff800000, STR(__LINE__)); // -0x1.000002p+0 * 0x1.fffffep+127 = -inf
  comp32(single_of_bits(0x7f7fffff) * single_of_bits(0xbf800001), 0xff800000, STR(__LINE__)); // 0x1.fffffep+127 * -0x1.000002p+0 = -inf
}

void f482(void) {
  comp32(single_of_bits(0xff7fffff) * single_of_bits(0x3f800001), 0xff800000, STR(__LINE__)); // -0x1.fffffep+127 * 0x1.000002p+0 = -inf
  comp32(single_of_bits(0x3f800001) * single_of_bits(0xff7fffff), 0xff800000, STR(__LINE__)); // 0x1.000002p+0 * -0x1.fffffep+127 = -inf
  comp32(single_of_bits(0xbf800002) * single_of_bits(0x7f7ffffe), 0xff800000, STR(__LINE__)); // -0x1.000004p+0 * 0x1.fffffcp+127 = -inf
  comp32(single_of_bits(0x7f7ffffe) * single_of_bits(0xbf800002), 0xff800000, STR(__LINE__)); // 0x1.fffffcp+127 * -0x1.000004p+0 = -inf
  comp32(single_of_bits(0xff7ffffe) * single_of_bits(0x3f800002), 0xff800000, STR(__LINE__)); // -0x1.fffffcp+127 * 0x1.000004p+0 = -inf
  comp32(single_of_bits(0x3f800002) * single_of_bits(0xff7ffffe), 0xff800000, STR(__LINE__)); // 0x1.000004p+0 * -0x1.fffffcp+127 = -inf
  comp32(single_of_bits(0xbf800004) * single_of_bits(0x7f7ffffc), 0xff800000, STR(__LINE__)); // -0x1.000008p+0 * 0x1.fffff8p+127 = -inf
  comp32(single_of_bits(0x7f7ffffc) * single_of_bits(0xbf800004), 0xff800000, STR(__LINE__)); // 0x1.fffff8p+127 * -0x1.000008p+0 = -inf
  comp32(single_of_bits(0xff7ffffc) * single_of_bits(0x3f800004), 0xff800000, STR(__LINE__)); // -0x1.fffff8p+127 * 0x1.000008p+0 = -inf
  comp32(single_of_bits(0x3f800004) * single_of_bits(0xff7ffffc), 0xff800000, STR(__LINE__)); // 0x1.000008p+0 * -0x1.fffff8p+127 = -inf
}

void f483(void) {
  comp32(single_of_bits(0xbf800008) * single_of_bits(0x7f7ffff8), 0xff800000, STR(__LINE__)); // -0x1.00001p+0 * 0x1.fffffp+127 = -inf
  comp32(single_of_bits(0x7f7ffff8) * single_of_bits(0xbf800008), 0xff800000, STR(__LINE__)); // 0x1.fffffp+127 * -0x1.00001p+0 = -inf
  comp32(single_of_bits(0xff7ffff8) * single_of_bits(0x3f800008), 0xff800000, STR(__LINE__)); // -0x1.fffffp+127 * 0x1.00001p+0 = -inf
  comp32(single_of_bits(0x3f800008) * single_of_bits(0xff7ffff8), 0xff800000, STR(__LINE__)); // 0x1.00001p+0 * -0x1.fffffp+127 = -inf
  comp32(single_of_bits(0x7efffffd) * single_of_bits(0xc0000008), 0xff800000, STR(__LINE__)); // 0x1.fffffap+126 * -0x1.00001p+1 = -inf
  comp32(single_of_bits(0xc0000008) * single_of_bits(0x7efffffd), 0xff800000, STR(__LINE__)); // -0x1.00001p+1 * 0x1.fffffap+126 = -inf
  comp32(single_of_bits(0x3ffffffc) * single_of_bits(0x7f000002), 0x7f800000, STR(__LINE__)); // 0x1.fffff8p+0 * 0x1.000004p+127 = inf
  comp32(single_of_bits(0x7f000002) * single_of_bits(0x3ffffffc), 0x7f800000, STR(__LINE__)); // 0x1.000004p+127 * 0x1.fffff8p+0 = inf
  comp32(single_of_bits(0xbffffffc) * single_of_bits(0xff000002), 0x7f800000, STR(__LINE__)); // -0x1.fffff8p+0 * -0x1.000004p+127 = inf
  comp32(single_of_bits(0xff000002) * single_of_bits(0xbffffffc), 0x7f800000, STR(__LINE__)); // -0x1.000004p+127 * -0x1.fffff8p+0 = inf
}

void f484(void) {
  comp32(single_of_bits(0xbffffffc) * single_of_bits(0x7f000002), 0xff800000, STR(__LINE__)); // -0x1.fffff8p+0 * 0x1.000004p+127 = -inf
  comp32(single_of_bits(0x7f000002) * single_of_bits(0xbffffffc), 0xff800000, STR(__LINE__)); // 0x1.000004p+127 * -0x1.fffff8p+0 = -inf
  comp32(single_of_bits(0xff000002) * single_of_bits(0x3ffffffc), 0xff800000, STR(__LINE__)); // -0x1.000004p+127 * 0x1.fffff8p+0 = -inf
  comp32(single_of_bits(0x3ffffffc) * single_of_bits(0xff000002), 0xff800000, STR(__LINE__)); // 0x1.fffff8p+0 * -0x1.000004p+127 = -inf
  comp32(single_of_bits(0x3ffffffe) * single_of_bits(0x7f000001), 0x7f800000, STR(__LINE__)); // 0x1.fffffcp+0 * 0x1.000002p+127 = inf
  comp32(single_of_bits(0x7f000001) * single_of_bits(0x3ffffffe), 0x7f800000, STR(__LINE__)); // 0x1.000002p+127 * 0x1.fffffcp+0 = inf
  comp32(single_of_bits(0xbffffffe) * single_of_bits(0xff000001), 0x7f800000, STR(__LINE__)); // -0x1.fffffcp+0 * -0x1.000002p+127 = inf
  comp32(single_of_bits(0xff000001) * single_of_bits(0xbffffffe), 0x7f800000, STR(__LINE__)); // -0x1.000002p+127 * -0x1.fffffcp+0 = inf
  comp32(single_of_bits(0xbffffffe) * single_of_bits(0x7f000001), 0xff800000, STR(__LINE__)); // -0x1.fffffcp+0 * 0x1.000002p+127 = -inf
  comp32(single_of_bits(0x7f000001) * single_of_bits(0xbffffffe), 0xff800000, STR(__LINE__)); // 0x1.000002p+127 * -0x1.fffffcp+0 = -inf
}

void f485(void) {
  comp32(single_of_bits(0xff000001) * single_of_bits(0x3ffffffe), 0xff800000, STR(__LINE__)); // -0x1.000002p+127 * 0x1.fffffcp+0 = -inf
  comp32(single_of_bits(0x3ffffffe) * single_of_bits(0xff000001), 0xff800000, STR(__LINE__)); // 0x1.fffffcp+0 * -0x1.000002p+127 = -inf
  comp32(single_of_bits(0x00800000) * single_of_bits(0x00800000), 0x00000000, STR(__LINE__)); // 0x1p-126 * 0x1p-126 = 0x0p+0
  comp32(single_of_bits(0x80800000) * single_of_bits(0x80800000), 0x00000000, STR(__LINE__)); // -0x1p-126 * -0x1p-126 = 0x0p+0
  comp32(single_of_bits(0x80800000) * single_of_bits(0x00800000), 0x80000000, STR(__LINE__)); // -0x1p-126 * 0x1p-126 = -0x0p+0
  comp32(single_of_bits(0x00800000) * single_of_bits(0x80800000), 0x80000000, STR(__LINE__)); // 0x1p-126 * -0x1p-126 = -0x0p+0
  comp32(single_of_bits(0x00800000) * single_of_bits(0x01000000), 0x00000000, STR(__LINE__)); // 0x1p-126 * 0x1p-125 = 0x0p+0
  comp32(single_of_bits(0x01000000) * single_of_bits(0x00800000), 0x00000000, STR(__LINE__)); // 0x1p-125 * 0x1p-126 = 0x0p+0
  comp32(single_of_bits(0x80800000) * single_of_bits(0x81000000), 0x00000000, STR(__LINE__)); // -0x1p-126 * -0x1p-125 = 0x0p+0
  comp32(single_of_bits(0x81000000) * single_of_bits(0x80800000), 0x00000000, STR(__LINE__)); // -0x1p-125 * -0x1p-126 = 0x0p+0
}

void f486(void) {
  comp32(single_of_bits(0x80800000) * single_of_bits(0x01000000), 0x80000000, STR(__LINE__)); // -0x1p-126 * 0x1p-125 = -0x0p+0
  comp32(single_of_bits(0x01000000) * single_of_bits(0x80800000), 0x80000000, STR(__LINE__)); // 0x1p-125 * -0x1p-126 = -0x0p+0
  comp32(single_of_bits(0x00800000) * single_of_bits(0x81000000), 0x80000000, STR(__LINE__)); // 0x1p-126 * -0x1p-125 = -0x0p+0
  comp32(single_of_bits(0x81000000) * single_of_bits(0x00800000), 0x80000000, STR(__LINE__)); // -0x1p-125 * 0x1p-126 = -0x0p+0
  comp32(single_of_bits(0x01000000) * single_of_bits(0x01000000), 0x00000000, STR(__LINE__)); // 0x1p-125 * 0x1p-125 = 0x0p+0
  comp32(single_of_bits(0x81000000) * single_of_bits(0x81000000), 0x00000000, STR(__LINE__)); // -0x1p-125 * -0x1p-125 = 0x0p+0
  comp32(single_of_bits(0x81000000) * single_of_bits(0x01000000), 0x80000000, STR(__LINE__)); // -0x1p-125 * 0x1p-125 = -0x0p+0
  comp32(single_of_bits(0x01000000) * single_of_bits(0x81000000), 0x80000000, STR(__LINE__)); // 0x1p-125 * -0x1p-125 = -0x0p+0
  comp32(single_of_bits(0x32800000) * single_of_bits(0x00800000), 0x00000000, STR(__LINE__)); // 0x1p-26 * 0x1p-126 = 0x0p+0
  comp32(single_of_bits(0x00800000) * single_of_bits(0x32800000), 0x00000000, STR(__LINE__)); // 0x1p-126 * 0x1p-26 = 0x0p+0
}

void f487(void) {
  comp32(single_of_bits(0xb2800000) * single_of_bits(0x80800000), 0x00000000, STR(__LINE__)); // -0x1p-26 * -0x1p-126 = 0x0p+0
  comp32(single_of_bits(0x80800000) * single_of_bits(0xb2800000), 0x00000000, STR(__LINE__)); // -0x1p-126 * -0x1p-26 = 0x0p+0
  comp32(single_of_bits(0xb2800000) * single_of_bits(0x00800000), 0x80000000, STR(__LINE__)); // -0x1p-26 * 0x1p-126 = -0x0p+0
  comp32(single_of_bits(0x00800000) * single_of_bits(0xb2800000), 0x80000000, STR(__LINE__)); // 0x1p-126 * -0x1p-26 = -0x0p+0
  comp32(single_of_bits(0x32800000) * single_of_bits(0x80800000), 0x80000000, STR(__LINE__)); // 0x1p-26 * -0x1p-126 = -0x0p+0
  comp32(single_of_bits(0x80800000) * single_of_bits(0x32800000), 0x80000000, STR(__LINE__)); // -0x1p-126 * 0x1p-26 = -0x0p+0
  comp32(single_of_bits(0x807ffff7) * single_of_bits(0x01000003), 0x80000000, STR(__LINE__)); // -0x1.ffffdcp-127 * 0x1.000006p-125 = -0x0p+0
  comp32(single_of_bits(0x01000003) * single_of_bits(0x807ffff7), 0x80000000, STR(__LINE__)); // 0x1.000006p-125 * -0x1.ffffdcp-127 = -0x0p+0
  comp32(single_of_bits(0x007ffff7) * single_of_bits(0x81000003), 0x80000000, STR(__LINE__)); // 0x1.ffffdcp-127 * -0x1.000006p-125 = -0x0p+0
  comp32(single_of_bits(0x81000003) * single_of_bits(0x007ffff7), 0x80000000, STR(__LINE__)); // -0x1.000006p-125 * 0x1.ffffdcp-127 = -0x0p+0
}

void f488(void) {
  comp32(single_of_bits(0x007ffff7) * single_of_bits(0x01000003), 0x00000000, STR(__LINE__)); // 0x1.ffffdcp-127 * 0x1.000006p-125 = 0x0p+0
  comp32(single_of_bits(0x01000003) * single_of_bits(0x007ffff7), 0x00000000, STR(__LINE__)); // 0x1.000006p-125 * 0x1.ffffdcp-127 = 0x0p+0
  comp32(single_of_bits(0x807ffff7) * single_of_bits(0x81000003), 0x00000000, STR(__LINE__)); // -0x1.ffffdcp-127 * -0x1.000006p-125 = 0x0p+0
  comp32(single_of_bits(0x81000003) * single_of_bits(0x807ffff7), 0x00000000, STR(__LINE__)); // -0x1.000006p-125 * -0x1.ffffdcp-127 = 0x0p+0
  comp32(single_of_bits(0x007fffff) * single_of_bits(0x007ffffe), 0x00000000, STR(__LINE__)); // 0x1.fffffcp-127 * 0x1.fffff8p-127 = 0x0p+0
  comp32(single_of_bits(0x007ffffe) * single_of_bits(0x007fffff), 0x00000000, STR(__LINE__)); // 0x1.fffff8p-127 * 0x1.fffffcp-127 = 0x0p+0
  comp32(single_of_bits(0x807fffff) * single_of_bits(0x807ffffe), 0x00000000, STR(__LINE__)); // -0x1.fffffcp-127 * -0x1.fffff8p-127 = 0x0p+0
  comp32(single_of_bits(0x807ffffe) * single_of_bits(0x807fffff), 0x00000000, STR(__LINE__)); // -0x1.fffff8p-127 * -0x1.fffffcp-127 = 0x0p+0
  comp32(single_of_bits(0x807fffff) * single_of_bits(0x007ffffe), 0x80000000, STR(__LINE__)); // -0x1.fffffcp-127 * 0x1.fffff8p-127 = -0x0p+0
  comp32(single_of_bits(0x007ffffe) * single_of_bits(0x807fffff), 0x80000000, STR(__LINE__)); // 0x1.fffff8p-127 * -0x1.fffffcp-127 = -0x0p+0
}

void f489(void) {
  comp32(single_of_bits(0x007fffff) * single_of_bits(0x807ffffe), 0x80000000, STR(__LINE__)); // 0x1.fffffcp-127 * -0x1.fffff8p-127 = -0x0p+0
  comp32(single_of_bits(0x807ffffe) * single_of_bits(0x007fffff), 0x80000000, STR(__LINE__)); // -0x1.fffff8p-127 * 0x1.fffffcp-127 = -0x0p+0
  comp32(single_of_bits(0x00000001) * single_of_bits(0x3e000000), 0x00000000, STR(__LINE__)); // 0x1p-149 * 0x1p-3 = 0x0p+0
  comp32(single_of_bits(0x3e000000) * single_of_bits(0x00000001), 0x00000000, STR(__LINE__)); // 0x1p-3 * 0x1p-149 = 0x0p+0
  comp32(single_of_bits(0x80000001) * single_of_bits(0xbe000000), 0x00000000, STR(__LINE__)); // -0x1p-149 * -0x1p-3 = 0x0p+0
  comp32(single_of_bits(0xbe000000) * single_of_bits(0x80000001), 0x00000000, STR(__LINE__)); // -0x1p-3 * -0x1p-149 = 0x0p+0
  comp32(single_of_bits(0x80000001) * single_of_bits(0x3e000000), 0x80000000, STR(__LINE__)); // -0x1p-149 * 0x1p-3 = -0x0p+0
  comp32(single_of_bits(0x3e000000) * single_of_bits(0x80000001), 0x80000000, STR(__LINE__)); // 0x1p-3 * -0x1p-149 = -0x0p+0
  comp32(single_of_bits(0x00000001) * single_of_bits(0xbe000000), 0x80000000, STR(__LINE__)); // 0x1p-149 * -0x1p-3 = -0x0p+0
  comp32(single_of_bits(0xbe000000) * single_of_bits(0x00000001), 0x80000000, STR(__LINE__)); // -0x1p-3 * 0x1p-149 = -0x0p+0
}

void f490(void) {
  comp32(single_of_bits(0x00000001) * single_of_bits(0x00000001), 0x00000000, STR(__LINE__)); // 0x1p-149 * 0x1p-149 = 0x0p+0
  comp32(single_of_bits(0x80000001) * single_of_bits(0x00000001), 0x80000000, STR(__LINE__)); // -0x1p-149 * 0x1p-149 = -0x0p+0
  comp32(single_of_bits(0x00000001) * single_of_bits(0x80000001), 0x80000000, STR(__LINE__)); // 0x1p-149 * -0x1p-149 = -0x0p+0
  comp32(single_of_bits(0x80000001) * single_of_bits(0x80000001), 0x00000000, STR(__LINE__)); // -0x1p-149 * -0x1p-149 = 0x0p+0
  comp32(single_of_bits(0x32ffffff) * single_of_bits(0x00800001), 0x00000000, STR(__LINE__)); // 0x1.fffffep-26 * 0x1.000002p-126 = 0x0p+0
  comp32(single_of_bits(0x00800001) * single_of_bits(0x32ffffff), 0x00000000, STR(__LINE__)); // 0x1.000002p-126 * 0x1.fffffep-26 = 0x0p+0
  comp32(single_of_bits(0xb2ffffff) * single_of_bits(0x80800001), 0x00000000, STR(__LINE__)); // -0x1.fffffep-26 * -0x1.000002p-126 = 0x0p+0
  comp32(single_of_bits(0x80800001) * single_of_bits(0xb2ffffff), 0x00000000, STR(__LINE__)); // -0x1.000002p-126 * -0x1.fffffep-26 = 0x0p+0
  comp32(single_of_bits(0xb2ffffff) * single_of_bits(0x00800001), 0x80000000, STR(__LINE__)); // -0x1.fffffep-26 * 0x1.000002p-126 = -0x0p+0
  comp32(single_of_bits(0x00800001) * single_of_bits(0xb2ffffff), 0x80000000, STR(__LINE__)); // 0x1.000002p-126 * -0x1.fffffep-26 = -0x0p+0
}

void f491(void) {
  comp32(single_of_bits(0x32ffffff) * single_of_bits(0x80800001), 0x80000000, STR(__LINE__)); // 0x1.fffffep-26 * -0x1.000002p-126 = -0x0p+0
  comp32(single_of_bits(0x80800001) * single_of_bits(0x32ffffff), 0x80000000, STR(__LINE__)); // -0x1.000002p-126 * 0x1.fffffep-26 = -0x0p+0
  comp32(single_of_bits(0x337fffff) * single_of_bits(0x00800000), 0x00000000, STR(__LINE__)); // 0x1.fffffep-25 * 0x1p-126 = 0x0p+0
  comp32(single_of_bits(0x00800000) * single_of_bits(0x337fffff), 0x00000000, STR(__LINE__)); // 0x1p-126 * 0x1.fffffep-25 = 0x0p+0
  comp32(single_of_bits(0xb37fffff) * single_of_bits(0x80800000), 0x00000000, STR(__LINE__)); // -0x1.fffffep-25 * -0x1p-126 = 0x0p+0
  comp32(single_of_bits(0x80800000) * single_of_bits(0xb37fffff), 0x00000000, STR(__LINE__)); // -0x1p-126 * -0x1.fffffep-25 = 0x0p+0
  comp32(single_of_bits(0xb37fffff) * single_of_bits(0x00800000), 0x80000000, STR(__LINE__)); // -0x1.fffffep-25 * 0x1p-126 = -0x0p+0
  comp32(single_of_bits(0x00800000) * single_of_bits(0xb37fffff), 0x80000000, STR(__LINE__)); // 0x1p-126 * -0x1.fffffep-25 = -0x0p+0
  comp32(single_of_bits(0x337fffff) * single_of_bits(0x80800000), 0x80000000, STR(__LINE__)); // 0x1.fffffep-25 * -0x1p-126 = -0x0p+0
  comp32(single_of_bits(0x80800000) * single_of_bits(0x337fffff), 0x80000000, STR(__LINE__)); // -0x1p-126 * 0x1.fffffep-25 = -0x0p+0
}

void f492(void) {
  comp32(single_of_bits(0x00000001) * single_of_bits(0x3e800000), 0x00000000, STR(__LINE__)); // 0x1p-149 * 0x1p-2 = 0x0p+0
  comp32(single_of_bits(0x3e800000) * single_of_bits(0x00000001), 0x00000000, STR(__LINE__)); // 0x1p-2 * 0x1p-149 = 0x0p+0
  comp32(single_of_bits(0x80000001) * single_of_bits(0xbe800000), 0x00000000, STR(__LINE__)); // -0x1p-149 * -0x1p-2 = 0x0p+0
  comp32(single_of_bits(0xbe800000) * single_of_bits(0x80000001), 0x00000000, STR(__LINE__)); // -0x1p-2 * -0x1p-149 = 0x0p+0
  comp32(single_of_bits(0x80000001) * single_of_bits(0x3e800000), 0x80000000, STR(__LINE__)); // -0x1p-149 * 0x1p-2 = -0x0p+0
  comp32(single_of_bits(0x3e800000) * single_of_bits(0x80000001), 0x80000000, STR(__LINE__)); // 0x1p-2 * -0x1p-149 = -0x0p+0
  comp32(single_of_bits(0xbe800000) * single_of_bits(0x00000001), 0x80000000, STR(__LINE__)); // -0x1p-2 * 0x1p-149 = -0x0p+0
  comp32(single_of_bits(0x00000001) * single_of_bits(0xbe800000), 0x80000000, STR(__LINE__)); // 0x1p-149 * -0x1p-2 = -0x0p+0
  comp32(single_of_bits(0x00000001) * single_of_bits(0x3fbfffff), 0x00000001, STR(__LINE__)); // 0x1p-149 * 0x1.7ffffep+0 = 0x1p-149
  comp32(single_of_bits(0x3fbfffff) * single_of_bits(0x00000001), 0x00000001, STR(__LINE__)); // 0x1.7ffffep+0 * 0x1p-149 = 0x1p-149
}

void f493(void) {
  comp32(single_of_bits(0x80000001) * single_of_bits(0xbfbfffff), 0x00000001, STR(__LINE__)); // -0x1p-149 * -0x1.7ffffep+0 = 0x1p-149
  comp32(single_of_bits(0xbfbfffff) * single_of_bits(0x80000001), 0x00000001, STR(__LINE__)); // -0x1.7ffffep+0 * -0x1p-149 = 0x1p-149
  comp32(single_of_bits(0x80000001) * single_of_bits(0x3fbfffff), 0x80000001, STR(__LINE__)); // -0x1p-149 * 0x1.7ffffep+0 = -0x1p-149
  comp32(single_of_bits(0x3fbfffff) * single_of_bits(0x80000001), 0x80000001, STR(__LINE__)); // 0x1.7ffffep+0 * -0x1p-149 = -0x1p-149
  comp32(single_of_bits(0xbfbfffff) * single_of_bits(0x00000001), 0x80000001, STR(__LINE__)); // -0x1.7ffffep+0 * 0x1p-149 = -0x1p-149
  comp32(single_of_bits(0x00000001) * single_of_bits(0xbfbfffff), 0x80000001, STR(__LINE__)); // 0x1p-149 * -0x1.7ffffep+0 = -0x1p-149
  comp32(single_of_bits(0x00000001) * single_of_bits(0x405fffff), 0x00000003, STR(__LINE__)); // 0x1p-149 * 0x1.bffffep+1 = 0x1.8p-148
  comp32(single_of_bits(0x405fffff) * single_of_bits(0x00000001), 0x00000003, STR(__LINE__)); // 0x1.bffffep+1 * 0x1p-149 = 0x1.8p-148
  comp32(single_of_bits(0x80000001) * single_of_bits(0xc05fffff), 0x00000003, STR(__LINE__)); // -0x1p-149 * -0x1.bffffep+1 = 0x1.8p-148
  comp32(single_of_bits(0xc05fffff) * single_of_bits(0x80000001), 0x00000003, STR(__LINE__)); // -0x1.bffffep+1 * -0x1p-149 = 0x1.8p-148
}

void f494(void) {
  comp32(single_of_bits(0x80000001) * single_of_bits(0x405fffff), 0x80000003, STR(__LINE__)); // -0x1p-149 * 0x1.bffffep+1 = -0x1.8p-148
  comp32(single_of_bits(0x405fffff) * single_of_bits(0x80000001), 0x80000003, STR(__LINE__)); // 0x1.bffffep+1 * -0x1p-149 = -0x1.8p-148
  comp32(single_of_bits(0xc05fffff) * single_of_bits(0x00000001), 0x80000003, STR(__LINE__)); // -0x1.bffffep+1 * 0x1p-149 = -0x1.8p-148
  comp32(single_of_bits(0x00000001) * single_of_bits(0xc05fffff), 0x80000003, STR(__LINE__)); // 0x1p-149 * -0x1.bffffep+1 = -0x1.8p-148
  comp32(single_of_bits(0x33800000) * single_of_bits(0x00800000), 0x00000000, STR(__LINE__)); // 0x1p-24 * 0x1p-126 = 0x0p+0
  comp32(single_of_bits(0x00800000) * single_of_bits(0x33800000), 0x00000000, STR(__LINE__)); // 0x1p-126 * 0x1p-24 = 0x0p+0
  comp32(single_of_bits(0xb3800000) * single_of_bits(0x80800000), 0x00000000, STR(__LINE__)); // -0x1p-24 * -0x1p-126 = 0x0p+0
  comp32(single_of_bits(0x80800000) * single_of_bits(0xb3800000), 0x00000000, STR(__LINE__)); // -0x1p-126 * -0x1p-24 = 0x0p+0
  comp32(single_of_bits(0xb3800000) * single_of_bits(0x00800000), 0x80000000, STR(__LINE__)); // -0x1p-24 * 0x1p-126 = -0x0p+0
  comp32(single_of_bits(0x00800000) * single_of_bits(0xb3800000), 0x80000000, STR(__LINE__)); // 0x1p-126 * -0x1p-24 = -0x0p+0
}

void f495(void) {
  comp32(single_of_bits(0x33800000) * single_of_bits(0x80800000), 0x80000000, STR(__LINE__)); // 0x1p-24 * -0x1p-126 = -0x0p+0
  comp32(single_of_bits(0x80800000) * single_of_bits(0x33800000), 0x80000000, STR(__LINE__)); // -0x1p-126 * 0x1p-24 = -0x0p+0
  comp32(single_of_bits(0x00000001) * single_of_bits(0x3f000000), 0x00000000, STR(__LINE__)); // 0x1p-149 * 0x1p-1 = 0x0p+0
  comp32(single_of_bits(0x3f000000) * single_of_bits(0x00000001), 0x00000000, STR(__LINE__)); // 0x1p-1 * 0x1p-149 = 0x0p+0
  comp32(single_of_bits(0x80000001) * single_of_bits(0xbf000000), 0x00000000, STR(__LINE__)); // -0x1p-149 * -0x1p-1 = 0x0p+0
  comp32(single_of_bits(0xbf000000) * single_of_bits(0x80000001), 0x00000000, STR(__LINE__)); // -0x1p-1 * -0x1p-149 = 0x0p+0
  comp32(single_of_bits(0x3f000000) * single_of_bits(0x80000001), 0x80000000, STR(__LINE__)); // 0x1p-1 * -0x1p-149 = -0x0p+0
  comp32(single_of_bits(0x80000001) * single_of_bits(0x3f000000), 0x80000000, STR(__LINE__)); // -0x1p-149 * 0x1p-1 = -0x0p+0
  comp32(single_of_bits(0xbf000000) * single_of_bits(0x00000001), 0x80000000, STR(__LINE__)); // -0x1p-1 * 0x1p-149 = -0x0p+0
  comp32(single_of_bits(0x00000001) * single_of_bits(0xbf000000), 0x80000000, STR(__LINE__)); // 0x1p-149 * -0x1p-1 = -0x0p+0
}

void f496(void) {
  comp32(single_of_bits(0x00000001) * single_of_bits(0x3fc00000), 0x00000002, STR(__LINE__)); // 0x1p-149 * 0x1.8p+0 = 0x1p-148
  comp32(single_of_bits(0x3fc00000) * single_of_bits(0x00000001), 0x00000002, STR(__LINE__)); // 0x1.8p+0 * 0x1p-149 = 0x1p-148
  comp32(single_of_bits(0x80000001) * single_of_bits(0xbfc00000), 0x00000002, STR(__LINE__)); // -0x1p-149 * -0x1.8p+0 = 0x1p-148
  comp32(single_of_bits(0xbfc00000) * single_of_bits(0x80000001), 0x00000002, STR(__LINE__)); // -0x1.8p+0 * -0x1p-149 = 0x1p-148
  comp32(single_of_bits(0x3fc00000) * single_of_bits(0x80000001), 0x80000002, STR(__LINE__)); // 0x1.8p+0 * -0x1p-149 = -0x1p-148
  comp32(single_of_bits(0x80000001) * single_of_bits(0x3fc00000), 0x80000002, STR(__LINE__)); // -0x1p-149 * 0x1.8p+0 = -0x1p-148
  comp32(single_of_bits(0xbfc00000) * single_of_bits(0x00000001), 0x80000002, STR(__LINE__)); // -0x1.8p+0 * 0x1p-149 = -0x1p-148
  comp32(single_of_bits(0x00000001) * single_of_bits(0xbfc00000), 0x80000002, STR(__LINE__)); // 0x1p-149 * -0x1.8p+0 = -0x1p-148
  comp32(single_of_bits(0x00000001) * single_of_bits(0x40200000), 0x00000002, STR(__LINE__)); // 0x1p-149 * 0x1.4p+1 = 0x1p-148
  comp32(single_of_bits(0x40200000) * single_of_bits(0x00000001), 0x00000002, STR(__LINE__)); // 0x1.4p+1 * 0x1p-149 = 0x1p-148
}

void f497(void) {
  comp32(single_of_bits(0x80000001) * single_of_bits(0xc0200000), 0x00000002, STR(__LINE__)); // -0x1p-149 * -0x1.4p+1 = 0x1p-148
  comp32(single_of_bits(0xc0200000) * single_of_bits(0x80000001), 0x00000002, STR(__LINE__)); // -0x1.4p+1 * -0x1p-149 = 0x1p-148
  comp32(single_of_bits(0x40200000) * single_of_bits(0x80000001), 0x80000002, STR(__LINE__)); // 0x1.4p+1 * -0x1p-149 = -0x1p-148
  comp32(single_of_bits(0x80000001) * single_of_bits(0x40200000), 0x80000002, STR(__LINE__)); // -0x1p-149 * 0x1.4p+1 = -0x1p-148
  comp32(single_of_bits(0xc0200000) * single_of_bits(0x00000001), 0x80000002, STR(__LINE__)); // -0x1.4p+1 * 0x1p-149 = -0x1p-148
  comp32(single_of_bits(0x00000001) * single_of_bits(0xc0200000), 0x80000002, STR(__LINE__)); // 0x1p-149 * -0x1.4p+1 = -0x1p-148
  comp32(single_of_bits(0x00000001) * single_of_bits(0x40600000), 0x00000004, STR(__LINE__)); // 0x1p-149 * 0x1.cp+1 = 0x1p-147
  comp32(single_of_bits(0x40600000) * single_of_bits(0x00000001), 0x00000004, STR(__LINE__)); // 0x1.cp+1 * 0x1p-149 = 0x1p-147
  comp32(single_of_bits(0x80000001) * single_of_bits(0xc0600000), 0x00000004, STR(__LINE__)); // -0x1p-149 * -0x1.cp+1 = 0x1p-147
  comp32(single_of_bits(0xc0600000) * single_of_bits(0x80000001), 0x00000004, STR(__LINE__)); // -0x1.cp+1 * -0x1p-149 = 0x1p-147
}

void f498(void) {
  comp32(single_of_bits(0x40600000) * single_of_bits(0x80000001), 0x80000004, STR(__LINE__)); // 0x1.cp+1 * -0x1p-149 = -0x1p-147
  comp32(single_of_bits(0x80000001) * single_of_bits(0x40600000), 0x80000004, STR(__LINE__)); // -0x1p-149 * 0x1.cp+1 = -0x1p-147
  comp32(single_of_bits(0xc0600000) * single_of_bits(0x00000001), 0x80000004, STR(__LINE__)); // -0x1.cp+1 * 0x1p-149 = -0x1p-147
  comp32(single_of_bits(0x00000001) * single_of_bits(0xc0600000), 0x80000004, STR(__LINE__)); // 0x1p-149 * -0x1.cp+1 = -0x1p-147
  comp32(single_of_bits(0x33a00000) * single_of_bits(0x00800000), 0x00000001, STR(__LINE__)); // 0x1.4p-24 * 0x1p-126 = 0x1p-149
  comp32(single_of_bits(0x00800000) * single_of_bits(0x33a00000), 0x00000001, STR(__LINE__)); // 0x1p-126 * 0x1.4p-24 = 0x1p-149
  comp32(single_of_bits(0xb3a00000) * single_of_bits(0x80800000), 0x00000001, STR(__LINE__)); // -0x1.4p-24 * -0x1p-126 = 0x1p-149
  comp32(single_of_bits(0x80800000) * single_of_bits(0xb3a00000), 0x00000001, STR(__LINE__)); // -0x1p-126 * -0x1.4p-24 = 0x1p-149
  comp32(single_of_bits(0xb3a00000) * single_of_bits(0x00800000), 0x80000001, STR(__LINE__)); // -0x1.4p-24 * 0x1p-126 = -0x1p-149
  comp32(single_of_bits(0x00800000) * single_of_bits(0xb3a00000), 0x80000001, STR(__LINE__)); // 0x1p-126 * -0x1.4p-24 = -0x1p-149
}

void f499(void) {
  comp32(single_of_bits(0x80800000) * single_of_bits(0x33a00000), 0x80000001, STR(__LINE__)); // -0x1p-126 * 0x1.4p-24 = -0x1p-149
  comp32(single_of_bits(0x33a00000) * single_of_bits(0x80800000), 0x80000001, STR(__LINE__)); // 0x1.4p-24 * -0x1p-126 = -0x1p-149
  comp32(single_of_bits(0x00000001) * single_of_bits(0x3f000001), 0x00000001, STR(__LINE__)); // 0x1p-149 * 0x1.000002p-1 = 0x1p-149
  comp32(single_of_bits(0x3f000001) * single_of_bits(0x00000001), 0x00000001, STR(__LINE__)); // 0x1.000002p-1 * 0x1p-149 = 0x1p-149
  comp32(single_of_bits(0x80000001) * single_of_bits(0xbf000001), 0x00000001, STR(__LINE__)); // -0x1p-149 * -0x1.000002p-1 = 0x1p-149
  comp32(single_of_bits(0xbf000001) * single_of_bits(0x80000001), 0x00000001, STR(__LINE__)); // -0x1.000002p-1 * -0x1p-149 = 0x1p-149
  comp32(single_of_bits(0x80000001) * single_of_bits(0x3f000001), 0x80000001, STR(__LINE__)); // -0x1p-149 * 0x1.000002p-1 = -0x1p-149
  comp32(single_of_bits(0x3f000001) * single_of_bits(0x80000001), 0x80000001, STR(__LINE__)); // 0x1.000002p-1 * -0x1p-149 = -0x1p-149
  comp32(single_of_bits(0xbf000001) * single_of_bits(0x00000001), 0x80000001, STR(__LINE__)); // -0x1.000002p-1 * 0x1p-149 = -0x1p-149
  comp32(single_of_bits(0x00000001) * single_of_bits(0xbf000001), 0x80000001, STR(__LINE__)); // 0x1p-149 * -0x1.000002p-1 = -0x1p-149
}

void f500(void) {
  comp32(single_of_bits(0x40200001) * single_of_bits(0x00000001), 0x00000003, STR(__LINE__)); // 0x1.400002p+1 * 0x1p-149 = 0x1.8p-148
  comp32(single_of_bits(0x00000001) * single_of_bits(0x40200001), 0x00000003, STR(__LINE__)); // 0x1p-149 * 0x1.400002p+1 = 0x1.8p-148
  comp32(single_of_bits(0xc0200001) * single_of_bits(0x80000001), 0x00000003, STR(__LINE__)); // -0x1.400002p+1 * -0x1p-149 = 0x1.8p-148
  comp32(single_of_bits(0x80000001) * single_of_bits(0xc0200001), 0x00000003, STR(__LINE__)); // -0x1p-149 * -0x1.400002p+1 = 0x1.8p-148
  comp32(single_of_bits(0xc0200001) * single_of_bits(0x00000001), 0x80000003, STR(__LINE__)); // -0x1.400002p+1 * 0x1p-149 = -0x1.8p-148
  comp32(single_of_bits(0x00000001) * single_of_bits(0xc0200001), 0x80000003, STR(__LINE__)); // 0x1p-149 * -0x1.400002p+1 = -0x1.8p-148
  comp32(single_of_bits(0x80000001) * single_of_bits(0x40200001), 0x80000003, STR(__LINE__)); // -0x1p-149 * 0x1.400002p+1 = -0x1.8p-148
  comp32(single_of_bits(0x40200001) * single_of_bits(0x80000001), 0x80000003, STR(__LINE__)); // 0x1.400002p+1 * -0x1p-149 = -0x1.8p-148
  comp32(single_of_bits(0x33000001) * single_of_bits(0x00ffffff), 0x00000001, STR(__LINE__)); // 0x1.000002p-25 * 0x1.fffffep-126 = 0x1p-149
  comp32(single_of_bits(0x00ffffff) * single_of_bits(0x33000001), 0x00000001, STR(__LINE__)); // 0x1.fffffep-126 * 0x1.000002p-25 = 0x1p-149
}

void f501(void) {
  comp32(single_of_bits(0xb3000001) * single_of_bits(0x80ffffff), 0x00000001, STR(__LINE__)); // -0x1.000002p-25 * -0x1.fffffep-126 = 0x1p-149
  comp32(single_of_bits(0x80ffffff) * single_of_bits(0xb3000001), 0x00000001, STR(__LINE__)); // -0x1.fffffep-126 * -0x1.000002p-25 = 0x1p-149
  comp32(single_of_bits(0xb3000001) * single_of_bits(0x00ffffff), 0x80000001, STR(__LINE__)); // -0x1.000002p-25 * 0x1.fffffep-126 = -0x1p-149
  comp32(single_of_bits(0x00ffffff) * single_of_bits(0xb3000001), 0x80000001, STR(__LINE__)); // 0x1.fffffep-126 * -0x1.000002p-25 = -0x1p-149
  comp32(single_of_bits(0x80ffffff) * single_of_bits(0x33000001), 0x80000001, STR(__LINE__)); // -0x1.fffffep-126 * 0x1.000002p-25 = -0x1p-149
  comp32(single_of_bits(0x33000001) * single_of_bits(0x80ffffff), 0x80000001, STR(__LINE__)); // 0x1.000002p-25 * -0x1.fffffep-126 = -0x1p-149
  comp32(single_of_bits(0x33c00000) * single_of_bits(0x00800000), 0x00000001, STR(__LINE__)); // 0x1.8p-24 * 0x1p-126 = 0x1p-149
  comp32(single_of_bits(0x00800000) * single_of_bits(0x33c00000), 0x00000001, STR(__LINE__)); // 0x1p-126 * 0x1.8p-24 = 0x1p-149
  comp32(single_of_bits(0xb3c00000) * single_of_bits(0x80800000), 0x00000001, STR(__LINE__)); // -0x1.8p-24 * -0x1p-126 = 0x1p-149
  comp32(single_of_bits(0x80800000) * single_of_bits(0xb3c00000), 0x00000001, STR(__LINE__)); // -0x1p-126 * -0x1.8p-24 = 0x1p-149
}

void f502(void) {
  comp32(single_of_bits(0xb3c00000) * single_of_bits(0x00800000), 0x80000001, STR(__LINE__)); // -0x1.8p-24 * 0x1p-126 = -0x1p-149
  comp32(single_of_bits(0x00800000) * single_of_bits(0xb3c00000), 0x80000001, STR(__LINE__)); // 0x1p-126 * -0x1.8p-24 = -0x1p-149
  comp32(single_of_bits(0x80800000) * single_of_bits(0x33c00000), 0x80000001, STR(__LINE__)); // -0x1p-126 * 0x1.8p-24 = -0x1p-149
  comp32(single_of_bits(0x33c00000) * single_of_bits(0x80800000), 0x80000001, STR(__LINE__)); // 0x1.8p-24 * -0x1p-126 = -0x1p-149
  comp32(single_of_bits(0x00000001) * single_of_bits(0x3f400000), 0x00000001, STR(__LINE__)); // 0x1p-149 * 0x1.8p-1 = 0x1p-149
  comp32(single_of_bits(0x3f400000) * single_of_bits(0x00000001), 0x00000001, STR(__LINE__)); // 0x1.8p-1 * 0x1p-149 = 0x1p-149
  comp32(single_of_bits(0x80000001) * single_of_bits(0xbf400000), 0x00000001, STR(__LINE__)); // -0x1p-149 * -0x1.8p-1 = 0x1p-149
  comp32(single_of_bits(0xbf400000) * single_of_bits(0x80000001), 0x00000001, STR(__LINE__)); // -0x1.8p-1 * -0x1p-149 = 0x1p-149
  comp32(single_of_bits(0x80000001) * single_of_bits(0x3f400000), 0x80000001, STR(__LINE__)); // -0x1p-149 * 0x1.8p-1 = -0x1p-149
  comp32(single_of_bits(0x3f400000) * single_of_bits(0x80000001), 0x80000001, STR(__LINE__)); // 0x1.8p-1 * -0x1p-149 = -0x1p-149
}

void f503(void) {
  comp32(single_of_bits(0xbf400000) * single_of_bits(0x00000001), 0x80000001, STR(__LINE__)); // -0x1.8p-1 * 0x1p-149 = -0x1p-149
  comp32(single_of_bits(0x00000001) * single_of_bits(0xbf400000), 0x80000001, STR(__LINE__)); // 0x1p-149 * -0x1.8p-1 = -0x1p-149
  comp32(single_of_bits(0x33e00000) * single_of_bits(0x00800000), 0x00000001, STR(__LINE__)); // 0x1.cp-24 * 0x1p-126 = 0x1p-149
  comp32(single_of_bits(0x00800000) * single_of_bits(0x33e00000), 0x00000001, STR(__LINE__)); // 0x1p-126 * 0x1.cp-24 = 0x1p-149
  comp32(single_of_bits(0xb3e00000) * single_of_bits(0x80800000), 0x00000001, STR(__LINE__)); // -0x1.cp-24 * -0x1p-126 = 0x1p-149
  comp32(single_of_bits(0x80800000) * single_of_bits(0xb3e00000), 0x00000001, STR(__LINE__)); // -0x1p-126 * -0x1.cp-24 = 0x1p-149
  comp32(single_of_bits(0xb3e00000) * single_of_bits(0x00800000), 0x80000001, STR(__LINE__)); // -0x1.cp-24 * 0x1p-126 = -0x1p-149
  comp32(single_of_bits(0x00800000) * single_of_bits(0xb3e00000), 0x80000001, STR(__LINE__)); // 0x1p-126 * -0x1.cp-24 = -0x1p-149
  comp32(single_of_bits(0x80800000) * single_of_bits(0x33e00000), 0x80000001, STR(__LINE__)); // -0x1p-126 * 0x1.cp-24 = -0x1p-149
  comp32(single_of_bits(0x33e00000) * single_of_bits(0x80800000), 0x80000001, STR(__LINE__)); // 0x1.cp-24 * -0x1p-126 = -0x1p-149
}

void f504(void) {
  comp32(single_of_bits(0x00000001) * single_of_bits(0x3f400001), 0x00000001, STR(__LINE__)); // 0x1p-149 * 0x1.800002p-1 = 0x1p-149
  comp32(single_of_bits(0x3f400001) * single_of_bits(0x00000001), 0x00000001, STR(__LINE__)); // 0x1.800002p-1 * 0x1p-149 = 0x1p-149
  comp32(single_of_bits(0x80000001) * single_of_bits(0xbf400001), 0x00000001, STR(__LINE__)); // -0x1p-149 * -0x1.800002p-1 = 0x1p-149
  comp32(single_of_bits(0xbf400001) * single_of_bits(0x80000001), 0x00000001, STR(__LINE__)); // -0x1.800002p-1 * -0x1p-149 = 0x1p-149
  comp32(single_of_bits(0x80000001) * single_of_bits(0x3f400001), 0x80000001, STR(__LINE__)); // -0x1p-149 * 0x1.800002p-1 = -0x1p-149
  comp32(single_of_bits(0x3f400001) * single_of_bits(0x80000001), 0x80000001, STR(__LINE__)); // 0x1.800002p-1 * -0x1p-149 = -0x1p-149
  comp32(single_of_bits(0xbf400001) * single_of_bits(0x00000001), 0x80000001, STR(__LINE__)); // -0x1.800002p-1 * 0x1p-149 = -0x1p-149
  comp32(single_of_bits(0x00000001) * single_of_bits(0xbf400001), 0x80000001, STR(__LINE__)); // 0x1p-149 * -0x1.800002p-1 = -0x1p-149
  comp32(single_of_bits(0x00000001) * single_of_bits(0x3f7fffff), 0x00000001, STR(__LINE__)); // 0x1p-149 * 0x1.fffffep-1 = 0x1p-149
  comp32(single_of_bits(0x3f7fffff) * single_of_bits(0x00000001), 0x00000001, STR(__LINE__)); // 0x1.fffffep-1 * 0x1p-149 = 0x1p-149
}

void f505(void) {
  comp32(single_of_bits(0x80000001) * single_of_bits(0xbf7fffff), 0x00000001, STR(__LINE__)); // -0x1p-149 * -0x1.fffffep-1 = 0x1p-149
  comp32(single_of_bits(0xbf7fffff) * single_of_bits(0x80000001), 0x00000001, STR(__LINE__)); // -0x1.fffffep-1 * -0x1p-149 = 0x1p-149
  comp32(single_of_bits(0x80000001) * single_of_bits(0x3f7fffff), 0x80000001, STR(__LINE__)); // -0x1p-149 * 0x1.fffffep-1 = -0x1p-149
  comp32(single_of_bits(0x3f7fffff) * single_of_bits(0x80000001), 0x80000001, STR(__LINE__)); // 0x1.fffffep-1 * -0x1p-149 = -0x1p-149
  comp32(single_of_bits(0x00000001) * single_of_bits(0xbf7fffff), 0x80000001, STR(__LINE__)); // 0x1p-149 * -0x1.fffffep-1 = -0x1p-149
  comp32(single_of_bits(0xbf7fffff) * single_of_bits(0x00000001), 0x80000001, STR(__LINE__)); // -0x1.fffffep-1 * 0x1p-149 = -0x1p-149
  comp32(single_of_bits(0x337fffff) * single_of_bits(0x00ffffff), 0x00000001, STR(__LINE__)); // 0x1.fffffep-25 * 0x1.fffffep-126 = 0x1p-149
  comp32(single_of_bits(0x00ffffff) * single_of_bits(0x337fffff), 0x00000001, STR(__LINE__)); // 0x1.fffffep-126 * 0x1.fffffep-25 = 0x1p-149
  comp32(single_of_bits(0xb37fffff) * single_of_bits(0x80ffffff), 0x00000001, STR(__LINE__)); // -0x1.fffffep-25 * -0x1.fffffep-126 = 0x1p-149
  comp32(single_of_bits(0x80ffffff) * single_of_bits(0xb37fffff), 0x00000001, STR(__LINE__)); // -0x1.fffffep-126 * -0x1.fffffep-25 = 0x1p-149
}

void f506(void) {
  comp32(single_of_bits(0xb37fffff) * single_of_bits(0x00ffffff), 0x80000001, STR(__LINE__)); // -0x1.fffffep-25 * 0x1.fffffep-126 = -0x1p-149
  comp32(single_of_bits(0x00ffffff) * single_of_bits(0xb37fffff), 0x80000001, STR(__LINE__)); // 0x1.fffffep-126 * -0x1.fffffep-25 = -0x1p-149
  comp32(single_of_bits(0x80ffffff) * single_of_bits(0x337fffff), 0x80000001, STR(__LINE__)); // -0x1.fffffep-126 * 0x1.fffffep-25 = -0x1p-149
  comp32(single_of_bits(0x337fffff) * single_of_bits(0x80ffffff), 0x80000001, STR(__LINE__)); // 0x1.fffffep-25 * -0x1.fffffep-126 = -0x1p-149
  comp32(single_of_bits(0x007ffffc) * single_of_bits(0x3f800001), 0x007ffffd, STR(__LINE__)); // 0x1.fffffp-127 * 0x1.000002p+0 = 0x1.fffff4p-127
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x007ffffc), 0x007ffffd, STR(__LINE__)); // 0x1.000002p+0 * 0x1.fffffp-127 = 0x1.fffff4p-127
  comp32(single_of_bits(0x807ffffc) * single_of_bits(0xbf800001), 0x007ffffd, STR(__LINE__)); // -0x1.fffffp-127 * -0x1.000002p+0 = 0x1.fffff4p-127
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x807ffffc), 0x007ffffd, STR(__LINE__)); // -0x1.000002p+0 * -0x1.fffffp-127 = 0x1.fffff4p-127
  comp32(single_of_bits(0x807ffffc) * single_of_bits(0x3f800001), 0x807ffffd, STR(__LINE__)); // -0x1.fffffp-127 * 0x1.000002p+0 = -0x1.fffff4p-127
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x807ffffc), 0x807ffffd, STR(__LINE__)); // 0x1.000002p+0 * -0x1.fffffp-127 = -0x1.fffff4p-127
}

void f507(void) {
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x007ffffc), 0x807ffffd, STR(__LINE__)); // -0x1.000002p+0 * 0x1.fffffp-127 = -0x1.fffff4p-127
  comp32(single_of_bits(0x007ffffc) * single_of_bits(0xbf800001), 0x807ffffd, STR(__LINE__)); // 0x1.fffffp-127 * -0x1.000002p+0 = -0x1.fffff4p-127
  comp32(single_of_bits(0x3f400000) * single_of_bits(0x00800001), 0x00600001, STR(__LINE__)); // 0x1.8p-1 * 0x1.000002p-126 = 0x1.800004p-127
  comp32(single_of_bits(0x00800001) * single_of_bits(0x3f400000), 0x00600001, STR(__LINE__)); // 0x1.000002p-126 * 0x1.8p-1 = 0x1.800004p-127
  comp32(single_of_bits(0xbf400000) * single_of_bits(0x80800001), 0x00600001, STR(__LINE__)); // -0x1.8p-1 * -0x1.000002p-126 = 0x1.800004p-127
  comp32(single_of_bits(0x80800001) * single_of_bits(0xbf400000), 0x00600001, STR(__LINE__)); // -0x1.000002p-126 * -0x1.8p-1 = 0x1.800004p-127
  comp32(single_of_bits(0xbf400000) * single_of_bits(0x00800001), 0x80600001, STR(__LINE__)); // -0x1.8p-1 * 0x1.000002p-126 = -0x1.800004p-127
  comp32(single_of_bits(0x00800001) * single_of_bits(0xbf400000), 0x80600001, STR(__LINE__)); // 0x1.000002p-126 * -0x1.8p-1 = -0x1.800004p-127
  comp32(single_of_bits(0x80800001) * single_of_bits(0x3f400000), 0x80600001, STR(__LINE__)); // -0x1.000002p-126 * 0x1.8p-1 = -0x1.800004p-127
  comp32(single_of_bits(0x3f400000) * single_of_bits(0x80800001), 0x80600001, STR(__LINE__)); // 0x1.8p-1 * -0x1.000002p-126 = -0x1.800004p-127
}

void f508(void) {
  comp32(single_of_bits(0x007ffffe) * single_of_bits(0x3f800001), 0x007fffff, STR(__LINE__)); // 0x1.fffff8p-127 * 0x1.000002p+0 = 0x1.fffffcp-127
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x007ffffe), 0x007fffff, STR(__LINE__)); // 0x1.000002p+0 * 0x1.fffff8p-127 = 0x1.fffffcp-127
  comp32(single_of_bits(0x807ffffe) * single_of_bits(0xbf800001), 0x007fffff, STR(__LINE__)); // -0x1.fffff8p-127 * -0x1.000002p+0 = 0x1.fffffcp-127
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x807ffffe), 0x007fffff, STR(__LINE__)); // -0x1.000002p+0 * -0x1.fffff8p-127 = 0x1.fffffcp-127
  comp32(single_of_bits(0x807ffffe) * single_of_bits(0x3f800001), 0x807fffff, STR(__LINE__)); // -0x1.fffff8p-127 * 0x1.000002p+0 = -0x1.fffffcp-127
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x807ffffe), 0x807fffff, STR(__LINE__)); // 0x1.000002p+0 * -0x1.fffff8p-127 = -0x1.fffffcp-127
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x007ffffe), 0x807fffff, STR(__LINE__)); // -0x1.000002p+0 * 0x1.fffff8p-127 = -0x1.fffffcp-127
  comp32(single_of_bits(0x007ffffe) * single_of_bits(0xbf800001), 0x807fffff, STR(__LINE__)); // 0x1.fffff8p-127 * -0x1.000002p+0 = -0x1.fffffcp-127
  comp32(single_of_bits(0x007ffff8) * single_of_bits(0x3f800001), 0x007ffff9, STR(__LINE__)); // 0x1.ffffep-127 * 0x1.000002p+0 = 0x1.ffffe4p-127
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x007ffff8), 0x007ffff9, STR(__LINE__)); // 0x1.000002p+0 * 0x1.ffffep-127 = 0x1.ffffe4p-127
}

void f509(void) {
  comp32(single_of_bits(0x807ffff8) * single_of_bits(0xbf800001), 0x007ffff9, STR(__LINE__)); // -0x1.ffffep-127 * -0x1.000002p+0 = 0x1.ffffe4p-127
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x807ffff8), 0x007ffff9, STR(__LINE__)); // -0x1.000002p+0 * -0x1.ffffep-127 = 0x1.ffffe4p-127
  comp32(single_of_bits(0x807ffff8) * single_of_bits(0x3f800001), 0x807ffff9, STR(__LINE__)); // -0x1.ffffep-127 * 0x1.000002p+0 = -0x1.ffffe4p-127
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x807ffff8), 0x807ffff9, STR(__LINE__)); // 0x1.000002p+0 * -0x1.ffffep-127 = -0x1.ffffe4p-127
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x007ffff8), 0x807ffff9, STR(__LINE__)); // -0x1.000002p+0 * 0x1.ffffep-127 = -0x1.ffffe4p-127
  comp32(single_of_bits(0x007ffff8) * single_of_bits(0xbf800001), 0x807ffff9, STR(__LINE__)); // 0x1.ffffep-127 * -0x1.000002p+0 = -0x1.ffffe4p-127
  comp32(single_of_bits(0x007ffff7) * single_of_bits(0x3f800001), 0x007ffff8, STR(__LINE__)); // 0x1.ffffdcp-127 * 0x1.000002p+0 = 0x1.ffffep-127
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x007ffff7), 0x007ffff8, STR(__LINE__)); // 0x1.000002p+0 * 0x1.ffffdcp-127 = 0x1.ffffep-127
  comp32(single_of_bits(0x807ffff7) * single_of_bits(0xbf800001), 0x007ffff8, STR(__LINE__)); // -0x1.ffffdcp-127 * -0x1.000002p+0 = 0x1.ffffep-127
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x807ffff7), 0x007ffff8, STR(__LINE__)); // -0x1.000002p+0 * -0x1.ffffdcp-127 = 0x1.ffffep-127
}

void f510(void) {
  comp32(single_of_bits(0x807ffff7) * single_of_bits(0x3f800001), 0x807ffff8, STR(__LINE__)); // -0x1.ffffdcp-127 * 0x1.000002p+0 = -0x1.ffffep-127
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x807ffff7), 0x807ffff8, STR(__LINE__)); // 0x1.000002p+0 * -0x1.ffffdcp-127 = -0x1.ffffep-127
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x007ffff7), 0x807ffff8, STR(__LINE__)); // -0x1.000002p+0 * 0x1.ffffdcp-127 = -0x1.ffffep-127
  comp32(single_of_bits(0x007ffff7) * single_of_bits(0xbf800001), 0x807ffff8, STR(__LINE__)); // 0x1.ffffdcp-127 * -0x1.000002p+0 = -0x1.ffffep-127
  comp32(single_of_bits(0x00800001) * single_of_bits(0x3f7ffffa), 0x007ffffe, STR(__LINE__)); // 0x1.000002p-126 * 0x1.fffff4p-1 = 0x1.fffff8p-127
  comp32(single_of_bits(0x3f7ffffa) * single_of_bits(0x00800001), 0x007ffffe, STR(__LINE__)); // 0x1.fffff4p-1 * 0x1.000002p-126 = 0x1.fffff8p-127
  comp32(single_of_bits(0x80800001) * single_of_bits(0xbf7ffffa), 0x007ffffe, STR(__LINE__)); // -0x1.000002p-126 * -0x1.fffff4p-1 = 0x1.fffff8p-127
  comp32(single_of_bits(0xbf7ffffa) * single_of_bits(0x80800001), 0x007ffffe, STR(__LINE__)); // -0x1.fffff4p-1 * -0x1.000002p-126 = 0x1.fffff8p-127
  comp32(single_of_bits(0x80800001) * single_of_bits(0x3f7ffffa), 0x807ffffe, STR(__LINE__)); // -0x1.000002p-126 * 0x1.fffff4p-1 = -0x1.fffff8p-127
  comp32(single_of_bits(0x3f7ffffa) * single_of_bits(0x80800001), 0x807ffffe, STR(__LINE__)); // 0x1.fffff4p-1 * -0x1.000002p-126 = -0x1.fffff8p-127
}

void f511(void) {
  comp32(single_of_bits(0xbf7ffffa) * single_of_bits(0x00800001), 0x807ffffe, STR(__LINE__)); // -0x1.fffff4p-1 * 0x1.000002p-126 = -0x1.fffff8p-127
  comp32(single_of_bits(0x00800001) * single_of_bits(0xbf7ffffa), 0x807ffffe, STR(__LINE__)); // 0x1.000002p-126 * -0x1.fffff4p-1 = -0x1.fffff8p-127
  comp32(single_of_bits(0x007ffffe) * single_of_bits(0x3f7ffffc), 0x007ffffc, STR(__LINE__)); // 0x1.fffff8p-127 * 0x1.fffff8p-1 = 0x1.fffffp-127
  comp32(single_of_bits(0x3f7ffffc) * single_of_bits(0x007ffffe), 0x007ffffc, STR(__LINE__)); // 0x1.fffff8p-1 * 0x1.fffff8p-127 = 0x1.fffffp-127
  comp32(single_of_bits(0x807ffffe) * single_of_bits(0xbf7ffffc), 0x007ffffc, STR(__LINE__)); // -0x1.fffff8p-127 * -0x1.fffff8p-1 = 0x1.fffffp-127
  comp32(single_of_bits(0xbf7ffffc) * single_of_bits(0x807ffffe), 0x007ffffc, STR(__LINE__)); // -0x1.fffff8p-1 * -0x1.fffff8p-127 = 0x1.fffffp-127
  comp32(single_of_bits(0x807ffffe) * single_of_bits(0x3f7ffffc), 0x807ffffc, STR(__LINE__)); // -0x1.fffff8p-127 * 0x1.fffff8p-1 = -0x1.fffffp-127
  comp32(single_of_bits(0x3f7ffffc) * single_of_bits(0x807ffffe), 0x807ffffc, STR(__LINE__)); // 0x1.fffff8p-1 * -0x1.fffff8p-127 = -0x1.fffffp-127
  comp32(single_of_bits(0xbf7ffffc) * single_of_bits(0x007ffffe), 0x807ffffc, STR(__LINE__)); // -0x1.fffff8p-1 * 0x1.fffff8p-127 = -0x1.fffffp-127
  comp32(single_of_bits(0x007ffffe) * single_of_bits(0xbf7ffffc), 0x807ffffc, STR(__LINE__)); // 0x1.fffff8p-127 * -0x1.fffff8p-1 = -0x1.fffffp-127
}

void f512(void) {
  comp32(single_of_bits(0x3effffff) * single_of_bits(0x00800003), 0x00400001, STR(__LINE__)); // 0x1.fffffep-2 * 0x1.000006p-126 = 0x1.000004p-127
  comp32(single_of_bits(0x00800003) * single_of_bits(0x3effffff), 0x00400001, STR(__LINE__)); // 0x1.000006p-126 * 0x1.fffffep-2 = 0x1.000004p-127
  comp32(single_of_bits(0xbeffffff) * single_of_bits(0x80800003), 0x00400001, STR(__LINE__)); // -0x1.fffffep-2 * -0x1.000006p-126 = 0x1.000004p-127
  comp32(single_of_bits(0x80800003) * single_of_bits(0xbeffffff), 0x00400001, STR(__LINE__)); // -0x1.000006p-126 * -0x1.fffffep-2 = 0x1.000004p-127
  comp32(single_of_bits(0xbeffffff) * single_of_bits(0x00800003), 0x80400001, STR(__LINE__)); // -0x1.fffffep-2 * 0x1.000006p-126 = -0x1.000004p-127
  comp32(single_of_bits(0x00800003) * single_of_bits(0xbeffffff), 0x80400001, STR(__LINE__)); // 0x1.000006p-126 * -0x1.fffffep-2 = -0x1.000004p-127
  comp32(single_of_bits(0x80800003) * single_of_bits(0x3effffff), 0x80400001, STR(__LINE__)); // -0x1.000006p-126 * 0x1.fffffep-2 = -0x1.000004p-127
  comp32(single_of_bits(0x3effffff) * single_of_bits(0x80800003), 0x80400001, STR(__LINE__)); // 0x1.fffffep-2 * -0x1.000006p-126 = -0x1.000004p-127
  comp32(single_of_bits(0x007fffff) * single_of_bits(0x3f800001), 0x00800000, STR(__LINE__)); // 0x1.fffffcp-127 * 0x1.000002p+0 = 0x1p-126
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x007fffff), 0x00800000, STR(__LINE__)); // 0x1.000002p+0 * 0x1.fffffcp-127 = 0x1p-126
}

void f513(void) {
  comp32(single_of_bits(0x807fffff) * single_of_bits(0xbf800001), 0x00800000, STR(__LINE__)); // -0x1.fffffcp-127 * -0x1.000002p+0 = 0x1p-126
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x807fffff), 0x00800000, STR(__LINE__)); // -0x1.000002p+0 * -0x1.fffffcp-127 = 0x1p-126
  comp32(single_of_bits(0x807fffff) * single_of_bits(0x3f800001), 0x80800000, STR(__LINE__)); // -0x1.fffffcp-127 * 0x1.000002p+0 = -0x1p-126
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x807fffff), 0x80800000, STR(__LINE__)); // 0x1.000002p+0 * -0x1.fffffcp-127 = -0x1p-126
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x007fffff), 0x80800000, STR(__LINE__)); // -0x1.000002p+0 * 0x1.fffffcp-127 = -0x1p-126
  comp32(single_of_bits(0x007fffff) * single_of_bits(0xbf800001), 0x80800000, STR(__LINE__)); // 0x1.fffffcp-127 * -0x1.000002p+0 = -0x1p-126
  comp32(single_of_bits(0x3f800008) * single_of_bits(0x007ffff8), 0x00800000, STR(__LINE__)); // 0x1.00001p+0 * 0x1.ffffep-127 = 0x1p-126
  comp32(single_of_bits(0x007ffff8) * single_of_bits(0x3f800008), 0x00800000, STR(__LINE__)); // 0x1.ffffep-127 * 0x1.00001p+0 = 0x1p-126
  comp32(single_of_bits(0x807ffff8) * single_of_bits(0xbf800008), 0x00800000, STR(__LINE__)); // -0x1.ffffep-127 * -0x1.00001p+0 = 0x1p-126
  comp32(single_of_bits(0xbf800008) * single_of_bits(0x807ffff8), 0x00800000, STR(__LINE__)); // -0x1.00001p+0 * -0x1.ffffep-127 = 0x1p-126
}

void f514(void) {
  comp32(single_of_bits(0x807ffff8) * single_of_bits(0x3f800008), 0x80800000, STR(__LINE__)); // -0x1.ffffep-127 * 0x1.00001p+0 = -0x1p-126
  comp32(single_of_bits(0x3f800008) * single_of_bits(0x807ffff8), 0x80800000, STR(__LINE__)); // 0x1.00001p+0 * -0x1.ffffep-127 = -0x1p-126
  comp32(single_of_bits(0xbf800008) * single_of_bits(0x007ffff8), 0x80800000, STR(__LINE__)); // -0x1.00001p+0 * 0x1.ffffep-127 = -0x1p-126
  comp32(single_of_bits(0x007ffff8) * single_of_bits(0xbf800008), 0x80800000, STR(__LINE__)); // 0x1.ffffep-127 * -0x1.00001p+0 = -0x1p-126
  comp32(single_of_bits(0x00800001) * single_of_bits(0x3f7ffffe), 0x00800000, STR(__LINE__)); // 0x1.000002p-126 * 0x1.fffffcp-1 = 0x1p-126
  comp32(single_of_bits(0x3f7ffffe) * single_of_bits(0x00800001), 0x00800000, STR(__LINE__)); // 0x1.fffffcp-1 * 0x1.000002p-126 = 0x1p-126
  comp32(single_of_bits(0x80800001) * single_of_bits(0xbf7ffffe), 0x00800000, STR(__LINE__)); // -0x1.000002p-126 * -0x1.fffffcp-1 = 0x1p-126
  comp32(single_of_bits(0xbf7ffffe) * single_of_bits(0x80800001), 0x00800000, STR(__LINE__)); // -0x1.fffffcp-1 * -0x1.000002p-126 = 0x1p-126
  comp32(single_of_bits(0x80800001) * single_of_bits(0x3f7ffffe), 0x80800000, STR(__LINE__)); // -0x1.000002p-126 * 0x1.fffffcp-1 = -0x1p-126
  comp32(single_of_bits(0x3f7ffffe) * single_of_bits(0x80800001), 0x80800000, STR(__LINE__)); // 0x1.fffffcp-1 * -0x1.000002p-126 = -0x1p-126
}

void f515(void) {
  comp32(single_of_bits(0xbf7ffffe) * single_of_bits(0x00800001), 0x80800000, STR(__LINE__)); // -0x1.fffffcp-1 * 0x1.000002p-126 = -0x1p-126
  comp32(single_of_bits(0x00800001) * single_of_bits(0xbf7ffffe), 0x80800000, STR(__LINE__)); // 0x1.000002p-126 * -0x1.fffffcp-1 = -0x1p-126
  comp32(single_of_bits(0x00800002) * single_of_bits(0x3f7ffffc), 0x00800000, STR(__LINE__)); // 0x1.000004p-126 * 0x1.fffff8p-1 = 0x1p-126
  comp32(single_of_bits(0x3f7ffffc) * single_of_bits(0x00800002), 0x00800000, STR(__LINE__)); // 0x1.fffff8p-1 * 0x1.000004p-126 = 0x1p-126
  comp32(single_of_bits(0x80800002) * single_of_bits(0xbf7ffffc), 0x00800000, STR(__LINE__)); // -0x1.000004p-126 * -0x1.fffff8p-1 = 0x1p-126
  comp32(single_of_bits(0xbf7ffffc) * single_of_bits(0x80800002), 0x00800000, STR(__LINE__)); // -0x1.fffff8p-1 * -0x1.000004p-126 = 0x1p-126
  comp32(single_of_bits(0x80800002) * single_of_bits(0x3f7ffffc), 0x80800000, STR(__LINE__)); // -0x1.000004p-126 * 0x1.fffff8p-1 = -0x1p-126
  comp32(single_of_bits(0x3f7ffffc) * single_of_bits(0x80800002), 0x80800000, STR(__LINE__)); // 0x1.fffff8p-1 * -0x1.000004p-126 = -0x1p-126
  comp32(single_of_bits(0xbf7ffffc) * single_of_bits(0x00800002), 0x80800000, STR(__LINE__)); // -0x1.fffff8p-1 * 0x1.000004p-126 = -0x1p-126
  comp32(single_of_bits(0x00800002) * single_of_bits(0xbf7ffffc), 0x80800000, STR(__LINE__)); // 0x1.000004p-126 * -0x1.fffff8p-1 = -0x1p-126
}

void f516(void) {
  comp32(single_of_bits(0x3f000002) * single_of_bits(0x00fffffb), 0x007fffff, STR(__LINE__)); // 0x1.000004p-1 * 0x1.fffff6p-126 = 0x1.fffffcp-127
  comp32(single_of_bits(0x00fffffb) * single_of_bits(0x3f000002), 0x007fffff, STR(__LINE__)); // 0x1.fffff6p-126 * 0x1.000004p-1 = 0x1.fffffcp-127
  comp32(single_of_bits(0xbf000002) * single_of_bits(0x80fffffb), 0x007fffff, STR(__LINE__)); // -0x1.000004p-1 * -0x1.fffff6p-126 = 0x1.fffffcp-127
  comp32(single_of_bits(0x80fffffb) * single_of_bits(0xbf000002), 0x007fffff, STR(__LINE__)); // -0x1.fffff6p-126 * -0x1.000004p-1 = 0x1.fffffcp-127
  comp32(single_of_bits(0xbf000002) * single_of_bits(0x00fffffb), 0x807fffff, STR(__LINE__)); // -0x1.000004p-1 * 0x1.fffff6p-126 = -0x1.fffffcp-127
  comp32(single_of_bits(0x00fffffb) * single_of_bits(0xbf000002), 0x807fffff, STR(__LINE__)); // 0x1.fffff6p-126 * -0x1.000004p-1 = -0x1.fffffcp-127
  comp32(single_of_bits(0x80fffffb) * single_of_bits(0x3f000002), 0x807fffff, STR(__LINE__)); // -0x1.fffff6p-126 * 0x1.000004p-1 = -0x1.fffffcp-127
  comp32(single_of_bits(0x3f000002) * single_of_bits(0x80fffffb), 0x807fffff, STR(__LINE__)); // 0x1.000004p-1 * -0x1.fffff6p-126 = -0x1.fffffcp-127
  comp32(single_of_bits(0x00ffffff) * single_of_bits(0x3f000000), 0x00800000, STR(__LINE__)); // 0x1.fffffep-126 * 0x1p-1 = 0x1p-126
  comp32(single_of_bits(0x3f000000) * single_of_bits(0x00ffffff), 0x00800000, STR(__LINE__)); // 0x1p-1 * 0x1.fffffep-126 = 0x1p-126
}

void f517(void) {
  comp32(single_of_bits(0x80ffffff) * single_of_bits(0xbf000000), 0x00800000, STR(__LINE__)); // -0x1.fffffep-126 * -0x1p-1 = 0x1p-126
  comp32(single_of_bits(0xbf000000) * single_of_bits(0x80ffffff), 0x00800000, STR(__LINE__)); // -0x1p-1 * -0x1.fffffep-126 = 0x1p-126
  comp32(single_of_bits(0x80ffffff) * single_of_bits(0x3f000000), 0x80800000, STR(__LINE__)); // -0x1.fffffep-126 * 0x1p-1 = -0x1p-126
  comp32(single_of_bits(0x3f000000) * single_of_bits(0x80ffffff), 0x80800000, STR(__LINE__)); // 0x1p-1 * -0x1.fffffep-126 = -0x1p-126
  comp32(single_of_bits(0xbf000000) * single_of_bits(0x00ffffff), 0x80800000, STR(__LINE__)); // -0x1p-1 * 0x1.fffffep-126 = -0x1p-126
  comp32(single_of_bits(0x00ffffff) * single_of_bits(0xbf000000), 0x80800000, STR(__LINE__)); // 0x1.fffffep-126 * -0x1p-1 = -0x1p-126
  comp32(single_of_bits(0x00800000) * single_of_bits(0x3f7ffffe), 0x007fffff, STR(__LINE__)); // 0x1p-126 * 0x1.fffffcp-1 = 0x1.fffffcp-127
  comp32(single_of_bits(0x3f7ffffe) * single_of_bits(0x00800000), 0x007fffff, STR(__LINE__)); // 0x1.fffffcp-1 * 0x1p-126 = 0x1.fffffcp-127
  comp32(single_of_bits(0x80800000) * single_of_bits(0xbf7ffffe), 0x007fffff, STR(__LINE__)); // -0x1p-126 * -0x1.fffffcp-1 = 0x1.fffffcp-127
  comp32(single_of_bits(0xbf7ffffe) * single_of_bits(0x80800000), 0x007fffff, STR(__LINE__)); // -0x1.fffffcp-1 * -0x1p-126 = 0x1.fffffcp-127
}

void f518(void) {
  comp32(single_of_bits(0x80800000) * single_of_bits(0x3f7ffffe), 0x807fffff, STR(__LINE__)); // -0x1p-126 * 0x1.fffffcp-1 = -0x1.fffffcp-127
  comp32(single_of_bits(0x3f7ffffe) * single_of_bits(0x80800000), 0x807fffff, STR(__LINE__)); // 0x1.fffffcp-1 * -0x1p-126 = -0x1.fffffcp-127
  comp32(single_of_bits(0xbf7ffffe) * single_of_bits(0x00800000), 0x807fffff, STR(__LINE__)); // -0x1.fffffcp-1 * 0x1p-126 = -0x1.fffffcp-127
  comp32(single_of_bits(0x00800000) * single_of_bits(0xbf7ffffe), 0x807fffff, STR(__LINE__)); // 0x1p-126 * -0x1.fffffcp-1 = -0x1.fffffcp-127
  comp32(single_of_bits(0x00fffffe) * single_of_bits(0x3f000000), 0x007fffff, STR(__LINE__)); // 0x1.fffffcp-126 * 0x1p-1 = 0x1.fffffcp-127
  comp32(single_of_bits(0x3f000000) * single_of_bits(0x00fffffe), 0x007fffff, STR(__LINE__)); // 0x1p-1 * 0x1.fffffcp-126 = 0x1.fffffcp-127
  comp32(single_of_bits(0x80fffffe) * single_of_bits(0xbf000000), 0x007fffff, STR(__LINE__)); // -0x1.fffffcp-126 * -0x1p-1 = 0x1.fffffcp-127
  comp32(single_of_bits(0xbf000000) * single_of_bits(0x80fffffe), 0x007fffff, STR(__LINE__)); // -0x1p-1 * -0x1.fffffcp-126 = 0x1.fffffcp-127
  comp32(single_of_bits(0x80fffffe) * single_of_bits(0x3f000000), 0x807fffff, STR(__LINE__)); // -0x1.fffffcp-126 * 0x1p-1 = -0x1.fffffcp-127
  comp32(single_of_bits(0x3f000000) * single_of_bits(0x80fffffe), 0x807fffff, STR(__LINE__)); // 0x1p-1 * -0x1.fffffcp-126 = -0x1.fffffcp-127
}

void f519(void) {
  comp32(single_of_bits(0xbf000000) * single_of_bits(0x00fffffe), 0x807fffff, STR(__LINE__)); // -0x1p-1 * 0x1.fffffcp-126 = -0x1.fffffcp-127
  comp32(single_of_bits(0x00fffffe) * single_of_bits(0xbf000000), 0x807fffff, STR(__LINE__)); // 0x1.fffffcp-126 * -0x1p-1 = -0x1.fffffcp-127
  comp32(single_of_bits(0x00fffffc) * single_of_bits(0x3f000000), 0x007ffffe, STR(__LINE__)); // 0x1.fffff8p-126 * 0x1p-1 = 0x1.fffff8p-127
  comp32(single_of_bits(0x3f000000) * single_of_bits(0x00fffffc), 0x007ffffe, STR(__LINE__)); // 0x1p-1 * 0x1.fffff8p-126 = 0x1.fffff8p-127
  comp32(single_of_bits(0x80fffffc) * single_of_bits(0xbf000000), 0x007ffffe, STR(__LINE__)); // -0x1.fffff8p-126 * -0x1p-1 = 0x1.fffff8p-127
  comp32(single_of_bits(0xbf000000) * single_of_bits(0x80fffffc), 0x007ffffe, STR(__LINE__)); // -0x1p-1 * -0x1.fffff8p-126 = 0x1.fffff8p-127
  comp32(single_of_bits(0x80fffffc) * single_of_bits(0x3f000000), 0x807ffffe, STR(__LINE__)); // -0x1.fffff8p-126 * 0x1p-1 = -0x1.fffff8p-127
  comp32(single_of_bits(0x3f000000) * single_of_bits(0x80fffffc), 0x807ffffe, STR(__LINE__)); // 0x1p-1 * -0x1.fffff8p-126 = -0x1.fffff8p-127
  comp32(single_of_bits(0xbf000000) * single_of_bits(0x00fffffc), 0x807ffffe, STR(__LINE__)); // -0x1p-1 * 0x1.fffff8p-126 = -0x1.fffff8p-127
  comp32(single_of_bits(0x00fffffc) * single_of_bits(0xbf000000), 0x807ffffe, STR(__LINE__)); // 0x1.fffff8p-126 * -0x1p-1 = -0x1.fffff8p-127
}

void f520(void) {
  comp32(single_of_bits(0x00fffff8) * single_of_bits(0x3f000000), 0x007ffffc, STR(__LINE__)); // 0x1.fffffp-126 * 0x1p-1 = 0x1.fffffp-127
  comp32(single_of_bits(0x3f000000) * single_of_bits(0x00fffff8), 0x007ffffc, STR(__LINE__)); // 0x1p-1 * 0x1.fffffp-126 = 0x1.fffffp-127
  comp32(single_of_bits(0x80fffff8) * single_of_bits(0xbf000000), 0x007ffffc, STR(__LINE__)); // -0x1.fffffp-126 * -0x1p-1 = 0x1.fffffp-127
  comp32(single_of_bits(0xbf000000) * single_of_bits(0x80fffff8), 0x007ffffc, STR(__LINE__)); // -0x1p-1 * -0x1.fffffp-126 = 0x1.fffffp-127
  comp32(single_of_bits(0x80fffff8) * single_of_bits(0x3f000000), 0x807ffffc, STR(__LINE__)); // -0x1.fffffp-126 * 0x1p-1 = -0x1.fffffp-127
  comp32(single_of_bits(0x3f000000) * single_of_bits(0x80fffff8), 0x807ffffc, STR(__LINE__)); // 0x1p-1 * -0x1.fffffp-126 = -0x1.fffffp-127
  comp32(single_of_bits(0xbf000000) * single_of_bits(0x00fffff8), 0x807ffffc, STR(__LINE__)); // -0x1p-1 * 0x1.fffffp-126 = -0x1.fffffp-127
  comp32(single_of_bits(0x00fffff8) * single_of_bits(0xbf000000), 0x807ffffc, STR(__LINE__)); // 0x1.fffffp-126 * -0x1p-1 = -0x1.fffffp-127
  comp32(single_of_bits(0x00000008) * single_of_bits(0x3e000000), 0x00000001, STR(__LINE__)); // 0x1p-146 * 0x1p-3 = 0x1p-149
  comp32(single_of_bits(0x3e000000) * single_of_bits(0x00000008), 0x00000001, STR(__LINE__)); // 0x1p-3 * 0x1p-146 = 0x1p-149
}

void f521(void) {
  comp32(single_of_bits(0x80000008) * single_of_bits(0xbe000000), 0x00000001, STR(__LINE__)); // -0x1p-146 * -0x1p-3 = 0x1p-149
  comp32(single_of_bits(0xbe000000) * single_of_bits(0x80000008), 0x00000001, STR(__LINE__)); // -0x1p-3 * -0x1p-146 = 0x1p-149
  comp32(single_of_bits(0x80000008) * single_of_bits(0x3e000000), 0x80000001, STR(__LINE__)); // -0x1p-146 * 0x1p-3 = -0x1p-149
  comp32(single_of_bits(0x3e000000) * single_of_bits(0x80000008), 0x80000001, STR(__LINE__)); // 0x1p-3 * -0x1p-146 = -0x1p-149
  comp32(single_of_bits(0xbe000000) * single_of_bits(0x00000008), 0x80000001, STR(__LINE__)); // -0x1p-3 * 0x1p-146 = -0x1p-149
  comp32(single_of_bits(0x00000008) * single_of_bits(0xbe000000), 0x80000001, STR(__LINE__)); // 0x1p-146 * -0x1p-3 = -0x1p-149
  comp32(single_of_bits(0x00000006) * single_of_bits(0x3f000000), 0x00000003, STR(__LINE__)); // 0x1.8p-147 * 0x1p-1 = 0x1.8p-148
  comp32(single_of_bits(0x3f000000) * single_of_bits(0x00000006), 0x00000003, STR(__LINE__)); // 0x1p-1 * 0x1.8p-147 = 0x1.8p-148
  comp32(single_of_bits(0x80000006) * single_of_bits(0xbf000000), 0x00000003, STR(__LINE__)); // -0x1.8p-147 * -0x1p-1 = 0x1.8p-148
  comp32(single_of_bits(0xbf000000) * single_of_bits(0x80000006), 0x00000003, STR(__LINE__)); // -0x1p-1 * -0x1.8p-147 = 0x1.8p-148
}

void f522(void) {
  comp32(single_of_bits(0x80000006) * single_of_bits(0x3f000000), 0x80000003, STR(__LINE__)); // -0x1.8p-147 * 0x1p-1 = -0x1.8p-148
  comp32(single_of_bits(0x3f000000) * single_of_bits(0x80000006), 0x80000003, STR(__LINE__)); // 0x1p-1 * -0x1.8p-147 = -0x1.8p-148
  comp32(single_of_bits(0xbf000000) * single_of_bits(0x00000006), 0x80000003, STR(__LINE__)); // -0x1p-1 * 0x1.8p-147 = -0x1.8p-148
  comp32(single_of_bits(0x00000006) * single_of_bits(0xbf000000), 0x80000003, STR(__LINE__)); // 0x1.8p-147 * -0x1p-1 = -0x1.8p-148
  comp32(single_of_bits(0x403fffff) * single_of_bits(0x3f7fffff), 0x403ffffe, STR(__LINE__)); // 0x1.7ffffep+1 * 0x1.fffffep-1 = 0x1.7ffffcp+1
  comp32(single_of_bits(0x3f7fffff) * single_of_bits(0x403fffff), 0x403ffffe, STR(__LINE__)); // 0x1.fffffep-1 * 0x1.7ffffep+1 = 0x1.7ffffcp+1
  comp32(single_of_bits(0xc03fffff) * single_of_bits(0xbf7fffff), 0x403ffffe, STR(__LINE__)); // -0x1.7ffffep+1 * -0x1.fffffep-1 = 0x1.7ffffcp+1
  comp32(single_of_bits(0xbf7fffff) * single_of_bits(0xc03fffff), 0x403ffffe, STR(__LINE__)); // -0x1.fffffep-1 * -0x1.7ffffep+1 = 0x1.7ffffcp+1
  comp32(single_of_bits(0xc03fffff) * single_of_bits(0x3f7fffff), 0xc03ffffe, STR(__LINE__)); // -0x1.7ffffep+1 * 0x1.fffffep-1 = -0x1.7ffffcp+1
  comp32(single_of_bits(0x3f7fffff) * single_of_bits(0xc03fffff), 0xc03ffffe, STR(__LINE__)); // 0x1.fffffep-1 * -0x1.7ffffep+1 = -0x1.7ffffcp+1
}

void f523(void) {
  comp32(single_of_bits(0xbf7fffff) * single_of_bits(0x403fffff), 0xc03ffffe, STR(__LINE__)); // -0x1.fffffep-1 * 0x1.7ffffep+1 = -0x1.7ffffcp+1
  comp32(single_of_bits(0x403fffff) * single_of_bits(0xbf7fffff), 0xc03ffffe, STR(__LINE__)); // 0x1.7ffffep+1 * -0x1.fffffep-1 = -0x1.7ffffcp+1
  comp32(single_of_bits(0x409fffff) * single_of_bits(0x3f7fffff), 0x409ffffe, STR(__LINE__)); // 0x1.3ffffep+2 * 0x1.fffffep-1 = 0x1.3ffffcp+2
  comp32(single_of_bits(0x3f7fffff) * single_of_bits(0x409fffff), 0x409ffffe, STR(__LINE__)); // 0x1.fffffep-1 * 0x1.3ffffep+2 = 0x1.3ffffcp+2
  comp32(single_of_bits(0xc09fffff) * single_of_bits(0xbf7fffff), 0x409ffffe, STR(__LINE__)); // -0x1.3ffffep+2 * -0x1.fffffep-1 = 0x1.3ffffcp+2
  comp32(single_of_bits(0xbf7fffff) * single_of_bits(0xc09fffff), 0x409ffffe, STR(__LINE__)); // -0x1.fffffep-1 * -0x1.3ffffep+2 = 0x1.3ffffcp+2
  comp32(single_of_bits(0xc09fffff) * single_of_bits(0x3f7fffff), 0xc09ffffe, STR(__LINE__)); // -0x1.3ffffep+2 * 0x1.fffffep-1 = -0x1.3ffffcp+2
  comp32(single_of_bits(0x3f7fffff) * single_of_bits(0xc09fffff), 0xc09ffffe, STR(__LINE__)); // 0x1.fffffep-1 * -0x1.3ffffep+2 = -0x1.3ffffcp+2
  comp32(single_of_bits(0x409fffff) * single_of_bits(0xbf7fffff), 0xc09ffffe, STR(__LINE__)); // 0x1.3ffffep+2 * -0x1.fffffep-1 = -0x1.3ffffcp+2
  comp32(single_of_bits(0xbf7fffff) * single_of_bits(0x409fffff), 0xc09ffffe, STR(__LINE__)); // -0x1.fffffep-1 * 0x1.3ffffep+2 = -0x1.3ffffcp+2
}

void f524(void) {
  comp32(single_of_bits(0x40dfffff) * single_of_bits(0x3f7fffff), 0x40dffffe, STR(__LINE__)); // 0x1.bffffep+2 * 0x1.fffffep-1 = 0x1.bffffcp+2
  comp32(single_of_bits(0x3f7fffff) * single_of_bits(0x40dfffff), 0x40dffffe, STR(__LINE__)); // 0x1.fffffep-1 * 0x1.bffffep+2 = 0x1.bffffcp+2
  comp32(single_of_bits(0xc0dfffff) * single_of_bits(0xbf7fffff), 0x40dffffe, STR(__LINE__)); // -0x1.bffffep+2 * -0x1.fffffep-1 = 0x1.bffffcp+2
  comp32(single_of_bits(0xbf7fffff) * single_of_bits(0xc0dfffff), 0x40dffffe, STR(__LINE__)); // -0x1.fffffep-1 * -0x1.bffffep+2 = 0x1.bffffcp+2
  comp32(single_of_bits(0xc0dfffff) * single_of_bits(0x3f7fffff), 0xc0dffffe, STR(__LINE__)); // -0x1.bffffep+2 * 0x1.fffffep-1 = -0x1.bffffcp+2
  comp32(single_of_bits(0x3f7fffff) * single_of_bits(0xc0dfffff), 0xc0dffffe, STR(__LINE__)); // 0x1.fffffep-1 * -0x1.bffffep+2 = -0x1.bffffcp+2
  comp32(single_of_bits(0xbf7fffff) * single_of_bits(0x40dfffff), 0xc0dffffe, STR(__LINE__)); // -0x1.fffffep-1 * 0x1.bffffep+2 = -0x1.bffffcp+2
  comp32(single_of_bits(0x40dfffff) * single_of_bits(0xbf7fffff), 0xc0dffffe, STR(__LINE__)); // 0x1.bffffep+2 * -0x1.fffffep-1 = -0x1.bffffcp+2
  comp32(single_of_bits(0x00ffffff) * single_of_bits(0x3f7fffff), 0x00fffffe, STR(__LINE__)); // 0x1.fffffep-126 * 0x1.fffffep-1 = 0x1.fffffcp-126
  comp32(single_of_bits(0x3f7fffff) * single_of_bits(0x00ffffff), 0x00fffffe, STR(__LINE__)); // 0x1.fffffep-1 * 0x1.fffffep-126 = 0x1.fffffcp-126
}

void f525(void) {
  comp32(single_of_bits(0x80ffffff) * single_of_bits(0xbf7fffff), 0x00fffffe, STR(__LINE__)); // -0x1.fffffep-126 * -0x1.fffffep-1 = 0x1.fffffcp-126
  comp32(single_of_bits(0xbf7fffff) * single_of_bits(0x80ffffff), 0x00fffffe, STR(__LINE__)); // -0x1.fffffep-1 * -0x1.fffffep-126 = 0x1.fffffcp-126
  comp32(single_of_bits(0x80ffffff) * single_of_bits(0x3f7fffff), 0x80fffffe, STR(__LINE__)); // -0x1.fffffep-126 * 0x1.fffffep-1 = -0x1.fffffcp-126
  comp32(single_of_bits(0x3f7fffff) * single_of_bits(0x80ffffff), 0x80fffffe, STR(__LINE__)); // 0x1.fffffep-1 * -0x1.fffffep-126 = -0x1.fffffcp-126
  comp32(single_of_bits(0xbf7fffff) * single_of_bits(0x00ffffff), 0x80fffffe, STR(__LINE__)); // -0x1.fffffep-1 * 0x1.fffffep-126 = -0x1.fffffcp-126
  comp32(single_of_bits(0x00ffffff) * single_of_bits(0xbf7fffff), 0x80fffffe, STR(__LINE__)); // 0x1.fffffep-126 * -0x1.fffffep-1 = -0x1.fffffcp-126
  comp32(single_of_bits(0x7e7ffff9) * single_of_bits(0x407fffff), 0x7f7ffff8, STR(__LINE__)); // 0x1.fffff2p+125 * 0x1.fffffep+1 = 0x1.fffffp+127
  comp32(single_of_bits(0x407fffff) * single_of_bits(0x7e7ffff9), 0x7f7ffff8, STR(__LINE__)); // 0x1.fffffep+1 * 0x1.fffff2p+125 = 0x1.fffffp+127
  comp32(single_of_bits(0xfe7ffff9) * single_of_bits(0xc07fffff), 0x7f7ffff8, STR(__LINE__)); // -0x1.fffff2p+125 * -0x1.fffffep+1 = 0x1.fffffp+127
  comp32(single_of_bits(0xc07fffff) * single_of_bits(0xfe7ffff9), 0x7f7ffff8, STR(__LINE__)); // -0x1.fffffep+1 * -0x1.fffff2p+125 = 0x1.fffffp+127
}

void f526(void) {
  comp32(single_of_bits(0xfe7ffff9) * single_of_bits(0x407fffff), 0xff7ffff8, STR(__LINE__)); // -0x1.fffff2p+125 * 0x1.fffffep+1 = -0x1.fffffp+127
  comp32(single_of_bits(0x407fffff) * single_of_bits(0xfe7ffff9), 0xff7ffff8, STR(__LINE__)); // 0x1.fffffep+1 * -0x1.fffff2p+125 = -0x1.fffffp+127
  comp32(single_of_bits(0xc07fffff) * single_of_bits(0x7e7ffff9), 0xff7ffff8, STR(__LINE__)); // -0x1.fffffep+1 * 0x1.fffff2p+125 = -0x1.fffffp+127
  comp32(single_of_bits(0x7e7ffff9) * single_of_bits(0xc07fffff), 0xff7ffff8, STR(__LINE__)); // 0x1.fffff2p+125 * -0x1.fffffep+1 = -0x1.fffffp+127
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x3f800001), 0x3f800002, STR(__LINE__)); // 0x1.000002p+0 * 0x1.000002p+0 = 0x1.000004p+0
  comp32(single_of_bits(0xbf800001) * single_of_bits(0xbf800001), 0x3f800002, STR(__LINE__)); // -0x1.000002p+0 * -0x1.000002p+0 = 0x1.000004p+0
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x3f800001), 0xbf800002, STR(__LINE__)); // -0x1.000002p+0 * 0x1.000002p+0 = -0x1.000004p+0
  comp32(single_of_bits(0x3f800001) * single_of_bits(0xbf800001), 0xbf800002, STR(__LINE__)); // 0x1.000002p+0 * -0x1.000002p+0 = -0x1.000004p+0
  comp32(single_of_bits(0x3f800002) * single_of_bits(0x3f800001), 0x3f800003, STR(__LINE__)); // 0x1.000004p+0 * 0x1.000002p+0 = 0x1.000006p+0
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x3f800002), 0x3f800003, STR(__LINE__)); // 0x1.000002p+0 * 0x1.000004p+0 = 0x1.000006p+0
}

void f527(void) {
  comp32(single_of_bits(0xbf800002) * single_of_bits(0xbf800001), 0x3f800003, STR(__LINE__)); // -0x1.000004p+0 * -0x1.000002p+0 = 0x1.000006p+0
  comp32(single_of_bits(0xbf800001) * single_of_bits(0xbf800002), 0x3f800003, STR(__LINE__)); // -0x1.000002p+0 * -0x1.000004p+0 = 0x1.000006p+0
  comp32(single_of_bits(0xbf800002) * single_of_bits(0x3f800001), 0xbf800003, STR(__LINE__)); // -0x1.000004p+0 * 0x1.000002p+0 = -0x1.000006p+0
  comp32(single_of_bits(0x3f800001) * single_of_bits(0xbf800002), 0xbf800003, STR(__LINE__)); // 0x1.000002p+0 * -0x1.000004p+0 = -0x1.000006p+0
  comp32(single_of_bits(0x3f800002) * single_of_bits(0xbf800001), 0xbf800003, STR(__LINE__)); // 0x1.000004p+0 * -0x1.000002p+0 = -0x1.000006p+0
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x3f800002), 0xbf800003, STR(__LINE__)); // -0x1.000002p+0 * 0x1.000004p+0 = -0x1.000006p+0
  comp32(single_of_bits(0xbf7fffff) * single_of_bits(0xff7fffff), 0x7f7ffffe, STR(__LINE__)); // -0x1.fffffep-1 * -0x1.fffffep+127 = 0x1.fffffcp+127
  comp32(single_of_bits(0xff7fffff) * single_of_bits(0xbf7fffff), 0x7f7ffffe, STR(__LINE__)); // -0x1.fffffep+127 * -0x1.fffffep-1 = 0x1.fffffcp+127
  comp32(single_of_bits(0x00400001) * single_of_bits(0x40000001), 0x00800003, STR(__LINE__)); // 0x1.000004p-127 * 0x1.000002p+1 = 0x1.000006p-126
  comp32(single_of_bits(0x40000001) * single_of_bits(0x00400001), 0x00800003, STR(__LINE__)); // 0x1.000002p+1 * 0x1.000004p-127 = 0x1.000006p-126
}

void f528(void) {
  comp32(single_of_bits(0x80400001) * single_of_bits(0xc0000001), 0x00800003, STR(__LINE__)); // -0x1.000004p-127 * -0x1.000002p+1 = 0x1.000006p-126
  comp32(single_of_bits(0xc0000001) * single_of_bits(0x80400001), 0x00800003, STR(__LINE__)); // -0x1.000002p+1 * -0x1.000004p-127 = 0x1.000006p-126
  comp32(single_of_bits(0x80400001) * single_of_bits(0x40000001), 0x80800003, STR(__LINE__)); // -0x1.000004p-127 * 0x1.000002p+1 = -0x1.000006p-126
  comp32(single_of_bits(0x40000001) * single_of_bits(0x80400001), 0x80800003, STR(__LINE__)); // 0x1.000002p+1 * -0x1.000004p-127 = -0x1.000006p-126
  comp32(single_of_bits(0xc0000001) * single_of_bits(0x00400001), 0x80800003, STR(__LINE__)); // -0x1.000002p+1 * 0x1.000004p-127 = -0x1.000006p-126
  comp32(single_of_bits(0x00400001) * single_of_bits(0xc0000001), 0x80800003, STR(__LINE__)); // 0x1.000004p-127 * -0x1.000002p+1 = -0x1.000006p-126
  comp32(single_of_bits(0x403fffff) * single_of_bits(0x40400000), 0x410fffff, STR(__LINE__)); // 0x1.7ffffep+1 * 0x1.8p+1 = 0x1.1ffffep+3
  comp32(single_of_bits(0x40400000) * single_of_bits(0x403fffff), 0x410fffff, STR(__LINE__)); // 0x1.8p+1 * 0x1.7ffffep+1 = 0x1.1ffffep+3
  comp32(single_of_bits(0xc03fffff) * single_of_bits(0xc0400000), 0x410fffff, STR(__LINE__)); // -0x1.7ffffep+1 * -0x1.8p+1 = 0x1.1ffffep+3
  comp32(single_of_bits(0xc0400000) * single_of_bits(0xc03fffff), 0x410fffff, STR(__LINE__)); // -0x1.8p+1 * -0x1.7ffffep+1 = 0x1.1ffffep+3
}

void f529(void) {
  comp32(single_of_bits(0xc03fffff) * single_of_bits(0x40400000), 0xc10fffff, STR(__LINE__)); // -0x1.7ffffep+1 * 0x1.8p+1 = -0x1.1ffffep+3
  comp32(single_of_bits(0x40400000) * single_of_bits(0xc03fffff), 0xc10fffff, STR(__LINE__)); // 0x1.8p+1 * -0x1.7ffffep+1 = -0x1.1ffffep+3
  comp32(single_of_bits(0xc0400000) * single_of_bits(0x403fffff), 0xc10fffff, STR(__LINE__)); // -0x1.8p+1 * 0x1.7ffffep+1 = -0x1.1ffffep+3
  comp32(single_of_bits(0x403fffff) * single_of_bits(0xc0400000), 0xc10fffff, STR(__LINE__)); // 0x1.7ffffep+1 * -0x1.8p+1 = -0x1.1ffffep+3
  comp32(single_of_bits(0x40a00000) * single_of_bits(0x7e000001), 0x7f200001, STR(__LINE__)); // 0x1.4p+2 * 0x1.000002p+125 = 0x1.400002p+127
  comp32(single_of_bits(0x7e000001) * single_of_bits(0x40a00000), 0x7f200001, STR(__LINE__)); // 0x1.000002p+125 * 0x1.4p+2 = 0x1.400002p+127
  comp32(single_of_bits(0xc0a00000) * single_of_bits(0xfe000001), 0x7f200001, STR(__LINE__)); // -0x1.4p+2 * -0x1.000002p+125 = 0x1.400002p+127
  comp32(single_of_bits(0xfe000001) * single_of_bits(0xc0a00000), 0x7f200001, STR(__LINE__)); // -0x1.000002p+125 * -0x1.4p+2 = 0x1.400002p+127
  comp32(single_of_bits(0xc0a00000) * single_of_bits(0x7e000001), 0xff200001, STR(__LINE__)); // -0x1.4p+2 * 0x1.000002p+125 = -0x1.400002p+127
  comp32(single_of_bits(0x7e000001) * single_of_bits(0xc0a00000), 0xff200001, STR(__LINE__)); // 0x1.000002p+125 * -0x1.4p+2 = -0x1.400002p+127
}

void f530(void) {
  comp32(single_of_bits(0xfe000001) * single_of_bits(0x40a00000), 0xff200001, STR(__LINE__)); // -0x1.000002p+125 * 0x1.4p+2 = -0x1.400002p+127
  comp32(single_of_bits(0x40a00000) * single_of_bits(0xfe000001), 0xff200001, STR(__LINE__)); // 0x1.4p+2 * -0x1.000002p+125 = -0x1.400002p+127
  comp32(single_of_bits(0x01200000) * single_of_bits(0x40000001), 0x01a00001, STR(__LINE__)); // 0x1.4p-125 * 0x1.000002p+1 = 0x1.400002p-124
  comp32(single_of_bits(0x40000001) * single_of_bits(0x01200000), 0x01a00001, STR(__LINE__)); // 0x1.000002p+1 * 0x1.4p-125 = 0x1.400002p-124
  comp32(single_of_bits(0x81200000) * single_of_bits(0xc0000001), 0x01a00001, STR(__LINE__)); // -0x1.4p-125 * -0x1.000002p+1 = 0x1.400002p-124
  comp32(single_of_bits(0xc0000001) * single_of_bits(0x81200000), 0x01a00001, STR(__LINE__)); // -0x1.000002p+1 * -0x1.4p-125 = 0x1.400002p-124
  comp32(single_of_bits(0x81200000) * single_of_bits(0x40000001), 0x81a00001, STR(__LINE__)); // -0x1.4p-125 * 0x1.000002p+1 = -0x1.400002p-124
  comp32(single_of_bits(0x40000001) * single_of_bits(0x81200000), 0x81a00001, STR(__LINE__)); // 0x1.000002p+1 * -0x1.4p-125 = -0x1.400002p-124
  comp32(single_of_bits(0xc0000001) * single_of_bits(0x01200000), 0x81a00001, STR(__LINE__)); // -0x1.000002p+1 * 0x1.4p-125 = -0x1.400002p-124
  comp32(single_of_bits(0x01200000) * single_of_bits(0xc0000001), 0x81a00001, STR(__LINE__)); // 0x1.4p-125 * -0x1.000002p+1 = -0x1.400002p-124
}

void f531(void) {
  comp32(single_of_bits(0x40a00001) * single_of_bits(0x3f800001), 0x40a00002, STR(__LINE__)); // 0x1.400002p+2 * 0x1.000002p+0 = 0x1.400004p+2
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x40a00001), 0x40a00002, STR(__LINE__)); // 0x1.000002p+0 * 0x1.400002p+2 = 0x1.400004p+2
  comp32(single_of_bits(0xc0a00001) * single_of_bits(0xbf800001), 0x40a00002, STR(__LINE__)); // -0x1.400002p+2 * -0x1.000002p+0 = 0x1.400004p+2
  comp32(single_of_bits(0xbf800001) * single_of_bits(0xc0a00001), 0x40a00002, STR(__LINE__)); // -0x1.000002p+0 * -0x1.400002p+2 = 0x1.400004p+2
  comp32(single_of_bits(0xc0a00001) * single_of_bits(0x3f800001), 0xc0a00002, STR(__LINE__)); // -0x1.400002p+2 * 0x1.000002p+0 = -0x1.400004p+2
  comp32(single_of_bits(0x3f800001) * single_of_bits(0xc0a00001), 0xc0a00002, STR(__LINE__)); // 0x1.000002p+0 * -0x1.400002p+2 = -0x1.400004p+2
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x40a00001), 0xc0a00002, STR(__LINE__)); // -0x1.000002p+0 * 0x1.400002p+2 = -0x1.400004p+2
  comp32(single_of_bits(0x40a00001) * single_of_bits(0xbf800001), 0xc0a00002, STR(__LINE__)); // 0x1.400002p+2 * -0x1.000002p+0 = -0x1.400004p+2
  comp32(single_of_bits(0x40dfffff) * single_of_bits(0x3f7ffffe), 0x40dffffd, STR(__LINE__)); // 0x1.bffffep+2 * 0x1.fffffcp-1 = 0x1.bffffap+2
  comp32(single_of_bits(0x3f7ffffe) * single_of_bits(0x40dfffff), 0x40dffffd, STR(__LINE__)); // 0x1.fffffcp-1 * 0x1.bffffep+2 = 0x1.bffffap+2
}

void f532(void) {
  comp32(single_of_bits(0xc0dfffff) * single_of_bits(0xbf7ffffe), 0x40dffffd, STR(__LINE__)); // -0x1.bffffep+2 * -0x1.fffffcp-1 = 0x1.bffffap+2
  comp32(single_of_bits(0xbf7ffffe) * single_of_bits(0xc0dfffff), 0x40dffffd, STR(__LINE__)); // -0x1.fffffcp-1 * -0x1.bffffep+2 = 0x1.bffffap+2
  comp32(single_of_bits(0xc0dfffff) * single_of_bits(0x3f7ffffe), 0xc0dffffd, STR(__LINE__)); // -0x1.bffffep+2 * 0x1.fffffcp-1 = -0x1.bffffap+2
  comp32(single_of_bits(0x3f7ffffe) * single_of_bits(0xc0dfffff), 0xc0dffffd, STR(__LINE__)); // 0x1.fffffcp-1 * -0x1.bffffep+2 = -0x1.bffffap+2
  comp32(single_of_bits(0xbf7ffffe) * single_of_bits(0x40dfffff), 0xc0dffffd, STR(__LINE__)); // -0x1.fffffcp-1 * 0x1.bffffep+2 = -0x1.bffffap+2
  comp32(single_of_bits(0x40dfffff) * single_of_bits(0xbf7ffffe), 0xc0dffffd, STR(__LINE__)); // 0x1.bffffep+2 * -0x1.fffffcp-1 = -0x1.bffffap+2
  comp32(single_of_bits(0x3f7fffff) * single_of_bits(0x3f7ffffe), 0x3f7ffffd, STR(__LINE__)); // 0x1.fffffep-1 * 0x1.fffffcp-1 = 0x1.fffffap-1
  comp32(single_of_bits(0x3f7ffffe) * single_of_bits(0x3f7fffff), 0x3f7ffffd, STR(__LINE__)); // 0x1.fffffcp-1 * 0x1.fffffep-1 = 0x1.fffffap-1
  comp32(single_of_bits(0xbf7fffff) * single_of_bits(0xbf7ffffe), 0x3f7ffffd, STR(__LINE__)); // -0x1.fffffep-1 * -0x1.fffffcp-1 = 0x1.fffffap-1
  comp32(single_of_bits(0xbf7ffffe) * single_of_bits(0xbf7fffff), 0x3f7ffffd, STR(__LINE__)); // -0x1.fffffcp-1 * -0x1.fffffep-1 = 0x1.fffffap-1
}

void f533(void) {
  comp32(single_of_bits(0xbf7fffff) * single_of_bits(0x3f7ffffe), 0xbf7ffffd, STR(__LINE__)); // -0x1.fffffep-1 * 0x1.fffffcp-1 = -0x1.fffffap-1
  comp32(single_of_bits(0x3f7ffffe) * single_of_bits(0xbf7fffff), 0xbf7ffffd, STR(__LINE__)); // 0x1.fffffcp-1 * -0x1.fffffep-1 = -0x1.fffffap-1
  comp32(single_of_bits(0x3f7fffff) * single_of_bits(0xbf7ffffe), 0xbf7ffffd, STR(__LINE__)); // 0x1.fffffep-1 * -0x1.fffffcp-1 = -0x1.fffffap-1
  comp32(single_of_bits(0xbf7ffffe) * single_of_bits(0x3f7fffff), 0xbf7ffffd, STR(__LINE__)); // -0x1.fffffcp-1 * 0x1.fffffep-1 = -0x1.fffffap-1
  comp32(single_of_bits(0x7effffff) * single_of_bits(0x3f800001), 0x7f000000, STR(__LINE__)); // 0x1.fffffep+126 * 0x1.000002p+0 = 0x1p+127
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x7effffff), 0x7f000000, STR(__LINE__)); // 0x1.000002p+0 * 0x1.fffffep+126 = 0x1p+127
  comp32(single_of_bits(0xfeffffff) * single_of_bits(0xbf800001), 0x7f000000, STR(__LINE__)); // -0x1.fffffep+126 * -0x1.000002p+0 = 0x1p+127
  comp32(single_of_bits(0xbf800001) * single_of_bits(0xfeffffff), 0x7f000000, STR(__LINE__)); // -0x1.000002p+0 * -0x1.fffffep+126 = 0x1p+127
  comp32(single_of_bits(0xfeffffff) * single_of_bits(0x3f800001), 0xff000000, STR(__LINE__)); // -0x1.fffffep+126 * 0x1.000002p+0 = -0x1p+127
  comp32(single_of_bits(0x3f800001) * single_of_bits(0xfeffffff), 0xff000000, STR(__LINE__)); // 0x1.000002p+0 * -0x1.fffffep+126 = -0x1p+127
}

void f534(void) {
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x7effffff), 0xff000000, STR(__LINE__)); // -0x1.000002p+0 * 0x1.fffffep+126 = -0x1p+127
  comp32(single_of_bits(0x7effffff) * single_of_bits(0xbf800001), 0xff000000, STR(__LINE__)); // 0x1.fffffep+126 * -0x1.000002p+0 = -0x1p+127
  comp32(single_of_bits(0x7e7fffff) * single_of_bits(0x40000001), 0x7f000000, STR(__LINE__)); // 0x1.fffffep+125 * 0x1.000002p+1 = 0x1p+127
  comp32(single_of_bits(0x40000001) * single_of_bits(0x7e7fffff), 0x7f000000, STR(__LINE__)); // 0x1.000002p+1 * 0x1.fffffep+125 = 0x1p+127
  comp32(single_of_bits(0xfe7fffff) * single_of_bits(0xc0000001), 0x7f000000, STR(__LINE__)); // -0x1.fffffep+125 * -0x1.000002p+1 = 0x1p+127
  comp32(single_of_bits(0xc0000001) * single_of_bits(0xfe7fffff), 0x7f000000, STR(__LINE__)); // -0x1.000002p+1 * -0x1.fffffep+125 = 0x1p+127
  comp32(single_of_bits(0xfe7fffff) * single_of_bits(0x40000001), 0xff000000, STR(__LINE__)); // -0x1.fffffep+125 * 0x1.000002p+1 = -0x1p+127
  comp32(single_of_bits(0x40000001) * single_of_bits(0xfe7fffff), 0xff000000, STR(__LINE__)); // 0x1.000002p+1 * -0x1.fffffep+125 = -0x1p+127
  comp32(single_of_bits(0xc0000001) * single_of_bits(0x7e7fffff), 0xff000000, STR(__LINE__)); // -0x1.000002p+1 * 0x1.fffffep+125 = -0x1p+127
  comp32(single_of_bits(0x7e7fffff) * single_of_bits(0xc0000001), 0xff000000, STR(__LINE__)); // 0x1.fffffep+125 * -0x1.000002p+1 = -0x1p+127
}

void f535(void) {
  comp32(single_of_bits(0x01200001) * single_of_bits(0x40000001), 0x01a00002, STR(__LINE__)); // 0x1.400002p-125 * 0x1.000002p+1 = 0x1.400004p-124
  comp32(single_of_bits(0x40000001) * single_of_bits(0x01200001), 0x01a00002, STR(__LINE__)); // 0x1.000002p+1 * 0x1.400002p-125 = 0x1.400004p-124
  comp32(single_of_bits(0x81200001) * single_of_bits(0xc0000001), 0x01a00002, STR(__LINE__)); // -0x1.400002p-125 * -0x1.000002p+1 = 0x1.400004p-124
  comp32(single_of_bits(0xc0000001) * single_of_bits(0x81200001), 0x01a00002, STR(__LINE__)); // -0x1.000002p+1 * -0x1.400002p-125 = 0x1.400004p-124
  comp32(single_of_bits(0x81200001) * single_of_bits(0x40000001), 0x81a00002, STR(__LINE__)); // -0x1.400002p-125 * 0x1.000002p+1 = -0x1.400004p-124
  comp32(single_of_bits(0x40000001) * single_of_bits(0x81200001), 0x81a00002, STR(__LINE__)); // 0x1.000002p+1 * -0x1.400002p-125 = -0x1.400004p-124
  comp32(single_of_bits(0xc0000001) * single_of_bits(0x01200001), 0x81a00002, STR(__LINE__)); // -0x1.000002p+1 * 0x1.400002p-125 = -0x1.400004p-124
  comp32(single_of_bits(0x01200001) * single_of_bits(0xc0000001), 0x81a00002, STR(__LINE__)); // 0x1.400002p-125 * -0x1.000002p+1 = -0x1.400004p-124
  comp32(single_of_bits(0x40400004) * single_of_bits(0x40e00000), 0x41a80004, STR(__LINE__)); // 0x1.800008p+1 * 0x1.cp+2 = 0x1.500008p+4
  comp32(single_of_bits(0x40e00000) * single_of_bits(0x40400004), 0x41a80004, STR(__LINE__)); // 0x1.cp+2 * 0x1.800008p+1 = 0x1.500008p+4
}

void f536(void) {
  comp32(single_of_bits(0xc0400004) * single_of_bits(0xc0e00000), 0x41a80004, STR(__LINE__)); // -0x1.800008p+1 * -0x1.cp+2 = 0x1.500008p+4
  comp32(single_of_bits(0xc0e00000) * single_of_bits(0xc0400004), 0x41a80004, STR(__LINE__)); // -0x1.cp+2 * -0x1.800008p+1 = 0x1.500008p+4
  comp32(single_of_bits(0xc0400004) * single_of_bits(0x40e00000), 0xc1a80004, STR(__LINE__)); // -0x1.800008p+1 * 0x1.cp+2 = -0x1.500008p+4
  comp32(single_of_bits(0x40e00000) * single_of_bits(0xc0400004), 0xc1a80004, STR(__LINE__)); // 0x1.cp+2 * -0x1.800008p+1 = -0x1.500008p+4
  comp32(single_of_bits(0xc0e00000) * single_of_bits(0x40400004), 0xc1a80004, STR(__LINE__)); // -0x1.cp+2 * 0x1.800008p+1 = -0x1.500008p+4
  comp32(single_of_bits(0x40400004) * single_of_bits(0xc0e00000), 0xc1a80004, STR(__LINE__)); // 0x1.800008p+1 * -0x1.cp+2 = -0x1.500008p+4
  comp32(single_of_bits(0x40400000) * single_of_bits(0x3f800001), 0x40400002, STR(__LINE__)); // 0x1.8p+1 * 0x1.000002p+0 = 0x1.800004p+1
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x40400000), 0x40400002, STR(__LINE__)); // 0x1.000002p+0 * 0x1.8p+1 = 0x1.800004p+1
  comp32(single_of_bits(0xc0400000) * single_of_bits(0xbf800001), 0x40400002, STR(__LINE__)); // -0x1.8p+1 * -0x1.000002p+0 = 0x1.800004p+1
  comp32(single_of_bits(0xbf800001) * single_of_bits(0xc0400000), 0x40400002, STR(__LINE__)); // -0x1.000002p+0 * -0x1.8p+1 = 0x1.800004p+1
}

void f537(void) {
  comp32(single_of_bits(0xc0400000) * single_of_bits(0x3f800001), 0xc0400002, STR(__LINE__)); // -0x1.8p+1 * 0x1.000002p+0 = -0x1.800004p+1
  comp32(single_of_bits(0x3f800001) * single_of_bits(0xc0400000), 0xc0400002, STR(__LINE__)); // 0x1.000002p+0 * -0x1.8p+1 = -0x1.800004p+1
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x40400000), 0xc0400002, STR(__LINE__)); // -0x1.000002p+0 * 0x1.8p+1 = -0x1.800004p+1
  comp32(single_of_bits(0x40400000) * single_of_bits(0xbf800001), 0xc0400002, STR(__LINE__)); // 0x1.8p+1 * -0x1.000002p+0 = -0x1.800004p+1
  comp32(single_of_bits(0x3f000000) * single_of_bits(0x00800003), 0x00400002, STR(__LINE__)); // 0x1p-1 * 0x1.000006p-126 = 0x1.000008p-127
  comp32(single_of_bits(0x00800003) * single_of_bits(0x3f000000), 0x00400002, STR(__LINE__)); // 0x1.000006p-126 * 0x1p-1 = 0x1.000008p-127
  comp32(single_of_bits(0xbf000000) * single_of_bits(0x80800003), 0x00400002, STR(__LINE__)); // -0x1p-1 * -0x1.000006p-126 = 0x1.000008p-127
  comp32(single_of_bits(0x80800003) * single_of_bits(0xbf000000), 0x00400002, STR(__LINE__)); // -0x1.000006p-126 * -0x1p-1 = 0x1.000008p-127
  comp32(single_of_bits(0xbf000000) * single_of_bits(0x00800003), 0x80400002, STR(__LINE__)); // -0x1p-1 * 0x1.000006p-126 = -0x1.000008p-127
  comp32(single_of_bits(0x00800003) * single_of_bits(0xbf000000), 0x80400002, STR(__LINE__)); // 0x1.000006p-126 * -0x1p-1 = -0x1.000008p-127
}

void f538(void) {
  comp32(single_of_bits(0x80800003) * single_of_bits(0x3f000000), 0x80400002, STR(__LINE__)); // -0x1.000006p-126 * 0x1p-1 = -0x1.000008p-127
  comp32(single_of_bits(0x3f000000) * single_of_bits(0x80800003), 0x80400002, STR(__LINE__)); // 0x1p-1 * -0x1.000006p-126 = -0x1.000008p-127
  comp32(single_of_bits(0x4040000c) * single_of_bits(0x40e00000), 0x41a8000a, STR(__LINE__)); // 0x1.800018p+1 * 0x1.cp+2 = 0x1.500014p+4
  comp32(single_of_bits(0x40e00000) * single_of_bits(0x4040000c), 0x41a8000a, STR(__LINE__)); // 0x1.cp+2 * 0x1.800018p+1 = 0x1.500014p+4
  comp32(single_of_bits(0xc040000c) * single_of_bits(0xc0e00000), 0x41a8000a, STR(__LINE__)); // -0x1.800018p+1 * -0x1.cp+2 = 0x1.500014p+4
  comp32(single_of_bits(0xc0e00000) * single_of_bits(0xc040000c), 0x41a8000a, STR(__LINE__)); // -0x1.cp+2 * -0x1.800018p+1 = 0x1.500014p+4
  comp32(single_of_bits(0xc040000c) * single_of_bits(0x40e00000), 0xc1a8000a, STR(__LINE__)); // -0x1.800018p+1 * 0x1.cp+2 = -0x1.500014p+4
  comp32(single_of_bits(0x40e00000) * single_of_bits(0xc040000c), 0xc1a8000a, STR(__LINE__)); // 0x1.cp+2 * -0x1.800018p+1 = -0x1.500014p+4
  comp32(single_of_bits(0xc0e00000) * single_of_bits(0x4040000c), 0xc1a8000a, STR(__LINE__)); // -0x1.cp+2 * 0x1.800018p+1 = -0x1.500014p+4
  comp32(single_of_bits(0x4040000c) * single_of_bits(0xc0e00000), 0xc1a8000a, STR(__LINE__)); // 0x1.800018p+1 * -0x1.cp+2 = -0x1.500014p+4
}

void f539(void) {
  comp32(single_of_bits(0x40400000) * single_of_bits(0x3f800003), 0x40400004, STR(__LINE__)); // 0x1.8p+1 * 0x1.000006p+0 = 0x1.800008p+1
  comp32(single_of_bits(0x3f800003) * single_of_bits(0x40400000), 0x40400004, STR(__LINE__)); // 0x1.000006p+0 * 0x1.8p+1 = 0x1.800008p+1
  comp32(single_of_bits(0xc0400000) * single_of_bits(0xbf800003), 0x40400004, STR(__LINE__)); // -0x1.8p+1 * -0x1.000006p+0 = 0x1.800008p+1
  comp32(single_of_bits(0xbf800003) * single_of_bits(0xc0400000), 0x40400004, STR(__LINE__)); // -0x1.000006p+0 * -0x1.8p+1 = 0x1.800008p+1
  comp32(single_of_bits(0xc0400000) * single_of_bits(0x3f800003), 0xc0400004, STR(__LINE__)); // -0x1.8p+1 * 0x1.000006p+0 = -0x1.800008p+1
  comp32(single_of_bits(0x3f800003) * single_of_bits(0xc0400000), 0xc0400004, STR(__LINE__)); // 0x1.000006p+0 * -0x1.8p+1 = -0x1.800008p+1
  comp32(single_of_bits(0xbf800003) * single_of_bits(0x40400000), 0xc0400004, STR(__LINE__)); // -0x1.000006p+0 * 0x1.8p+1 = -0x1.800008p+1
  comp32(single_of_bits(0x40400000) * single_of_bits(0xbf800003), 0xc0400004, STR(__LINE__)); // 0x1.8p+1 * -0x1.000006p+0 = -0x1.800008p+1
  comp32(single_of_bits(0x3f000000) * single_of_bits(0x00800001), 0x00400000, STR(__LINE__)); // 0x1p-1 * 0x1.000002p-126 = 0x1p-127
  comp32(single_of_bits(0x00800001) * single_of_bits(0x3f000000), 0x00400000, STR(__LINE__)); // 0x1.000002p-126 * 0x1p-1 = 0x1p-127
}

void f540(void) {
  comp32(single_of_bits(0xbf000000) * single_of_bits(0x80800001), 0x00400000, STR(__LINE__)); // -0x1p-1 * -0x1.000002p-126 = 0x1p-127
  comp32(single_of_bits(0x80800001) * single_of_bits(0xbf000000), 0x00400000, STR(__LINE__)); // -0x1.000002p-126 * -0x1p-1 = 0x1p-127
  comp32(single_of_bits(0xbf000000) * single_of_bits(0x00800001), 0x80400000, STR(__LINE__)); // -0x1p-1 * 0x1.000002p-126 = -0x1p-127
  comp32(single_of_bits(0x00800001) * single_of_bits(0xbf000000), 0x80400000, STR(__LINE__)); // 0x1.000002p-126 * -0x1p-1 = -0x1p-127
  comp32(single_of_bits(0x80800001) * single_of_bits(0x3f000000), 0x80400000, STR(__LINE__)); // -0x1.000002p-126 * 0x1p-1 = -0x1p-127
  comp32(single_of_bits(0x3f000000) * single_of_bits(0x80800001), 0x80400000, STR(__LINE__)); // 0x1p-1 * -0x1.000002p-126 = -0x1p-127
  comp32(single_of_bits(0x3fa00000) * single_of_bits(0x3ffffffe), 0x401fffff, STR(__LINE__)); // 0x1.4p+0 * 0x1.fffffcp+0 = 0x1.3ffffep+1
  comp32(single_of_bits(0x3ffffffe) * single_of_bits(0x3fa00000), 0x401fffff, STR(__LINE__)); // 0x1.fffffcp+0 * 0x1.4p+0 = 0x1.3ffffep+1
  comp32(single_of_bits(0xbfa00000) * single_of_bits(0xbffffffe), 0x401fffff, STR(__LINE__)); // -0x1.4p+0 * -0x1.fffffcp+0 = 0x1.3ffffep+1
  comp32(single_of_bits(0xbffffffe) * single_of_bits(0xbfa00000), 0x401fffff, STR(__LINE__)); // -0x1.fffffcp+0 * -0x1.4p+0 = 0x1.3ffffep+1
}

void f541(void) {
  comp32(single_of_bits(0xbfa00000) * single_of_bits(0x3ffffffe), 0xc01fffff, STR(__LINE__)); // -0x1.4p+0 * 0x1.fffffcp+0 = -0x1.3ffffep+1
  comp32(single_of_bits(0x3ffffffe) * single_of_bits(0xbfa00000), 0xc01fffff, STR(__LINE__)); // 0x1.fffffcp+0 * -0x1.4p+0 = -0x1.3ffffep+1
  comp32(single_of_bits(0xbffffffe) * single_of_bits(0x3fa00000), 0xc01fffff, STR(__LINE__)); // -0x1.fffffcp+0 * 0x1.4p+0 = -0x1.3ffffep+1
  comp32(single_of_bits(0x3fa00000) * single_of_bits(0xbffffffe), 0xc01fffff, STR(__LINE__)); // 0x1.4p+0 * -0x1.fffffcp+0 = -0x1.3ffffep+1
  comp32(single_of_bits(0x40e00000) * single_of_bits(0x3f800001), 0x40e00002, STR(__LINE__)); // 0x1.cp+2 * 0x1.000002p+0 = 0x1.c00004p+2
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x40e00000), 0x40e00002, STR(__LINE__)); // 0x1.000002p+0 * 0x1.cp+2 = 0x1.c00004p+2
  comp32(single_of_bits(0xc0e00000) * single_of_bits(0xbf800001), 0x40e00002, STR(__LINE__)); // -0x1.cp+2 * -0x1.000002p+0 = 0x1.c00004p+2
  comp32(single_of_bits(0xbf800001) * single_of_bits(0xc0e00000), 0x40e00002, STR(__LINE__)); // -0x1.000002p+0 * -0x1.cp+2 = 0x1.c00004p+2
  comp32(single_of_bits(0xc0e00000) * single_of_bits(0x3f800001), 0xc0e00002, STR(__LINE__)); // -0x1.cp+2 * 0x1.000002p+0 = -0x1.c00004p+2
  comp32(single_of_bits(0x3f800001) * single_of_bits(0xc0e00000), 0xc0e00002, STR(__LINE__)); // 0x1.000002p+0 * -0x1.cp+2 = -0x1.c00004p+2
}

void f542(void) {
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x40e00000), 0xc0e00002, STR(__LINE__)); // -0x1.000002p+0 * 0x1.cp+2 = -0x1.c00004p+2
  comp32(single_of_bits(0x40e00000) * single_of_bits(0xbf800001), 0xc0e00002, STR(__LINE__)); // 0x1.cp+2 * -0x1.000002p+0 = -0x1.c00004p+2
  comp32(single_of_bits(0x01600000) * single_of_bits(0x40800001), 0x02600002, STR(__LINE__)); // 0x1.cp-125 * 0x1.000002p+2 = 0x1.c00004p-123
  comp32(single_of_bits(0x40800001) * single_of_bits(0x01600000), 0x02600002, STR(__LINE__)); // 0x1.000002p+2 * 0x1.cp-125 = 0x1.c00004p-123
  comp32(single_of_bits(0x81600000) * single_of_bits(0xc0800001), 0x02600002, STR(__LINE__)); // -0x1.cp-125 * -0x1.000002p+2 = 0x1.c00004p-123
  comp32(single_of_bits(0xc0800001) * single_of_bits(0x81600000), 0x02600002, STR(__LINE__)); // -0x1.000002p+2 * -0x1.cp-125 = 0x1.c00004p-123
  comp32(single_of_bits(0x81600000) * single_of_bits(0x40800001), 0x82600002, STR(__LINE__)); // -0x1.cp-125 * 0x1.000002p+2 = -0x1.c00004p-123
  comp32(single_of_bits(0x40800001) * single_of_bits(0x81600000), 0x82600002, STR(__LINE__)); // 0x1.000002p+2 * -0x1.cp-125 = -0x1.c00004p-123
  comp32(single_of_bits(0xc0800001) * single_of_bits(0x01600000), 0x82600002, STR(__LINE__)); // -0x1.000002p+2 * 0x1.cp-125 = -0x1.c00004p-123
  comp32(single_of_bits(0x01600000) * single_of_bits(0xc0800001), 0x82600002, STR(__LINE__)); // 0x1.cp-125 * -0x1.000002p+2 = -0x1.c00004p-123
}

void f543(void) {
  comp32(single_of_bits(0x40400001) * single_of_bits(0x3f800001), 0x40400003, STR(__LINE__)); // 0x1.800002p+1 * 0x1.000002p+0 = 0x1.800006p+1
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x40400001), 0x40400003, STR(__LINE__)); // 0x1.000002p+0 * 0x1.800002p+1 = 0x1.800006p+1
  comp32(single_of_bits(0xc0400001) * single_of_bits(0xbf800001), 0x40400003, STR(__LINE__)); // -0x1.800002p+1 * -0x1.000002p+0 = 0x1.800006p+1
  comp32(single_of_bits(0xbf800001) * single_of_bits(0xc0400001), 0x40400003, STR(__LINE__)); // -0x1.000002p+0 * -0x1.800002p+1 = 0x1.800006p+1
  comp32(single_of_bits(0xc0400001) * single_of_bits(0x3f800001), 0xc0400003, STR(__LINE__)); // -0x1.800002p+1 * 0x1.000002p+0 = -0x1.800006p+1
  comp32(single_of_bits(0x3f800001) * single_of_bits(0xc0400001), 0xc0400003, STR(__LINE__)); // 0x1.000002p+0 * -0x1.800002p+1 = -0x1.800006p+1
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x40400001), 0xc0400003, STR(__LINE__)); // -0x1.000002p+0 * 0x1.800002p+1 = -0x1.800006p+1
  comp32(single_of_bits(0x40400001) * single_of_bits(0xbf800001), 0xc0400003, STR(__LINE__)); // 0x1.800002p+1 * -0x1.000002p+0 = -0x1.800006p+1
  comp32(single_of_bits(0x40400001) * single_of_bits(0x3f800003), 0x40400006, STR(__LINE__)); // 0x1.800002p+1 * 0x1.000006p+0 = 0x1.80000cp+1
  comp32(single_of_bits(0x3f800003) * single_of_bits(0x40400001), 0x40400006, STR(__LINE__)); // 0x1.000006p+0 * 0x1.800002p+1 = 0x1.80000cp+1
}

void f544(void) {
  comp32(single_of_bits(0xc0400001) * single_of_bits(0xbf800003), 0x40400006, STR(__LINE__)); // -0x1.800002p+1 * -0x1.000006p+0 = 0x1.80000cp+1
  comp32(single_of_bits(0xbf800003) * single_of_bits(0xc0400001), 0x40400006, STR(__LINE__)); // -0x1.000006p+0 * -0x1.800002p+1 = 0x1.80000cp+1
  comp32(single_of_bits(0xc0400001) * single_of_bits(0x3f800003), 0xc0400006, STR(__LINE__)); // -0x1.800002p+1 * 0x1.000006p+0 = -0x1.80000cp+1
  comp32(single_of_bits(0x3f800003) * single_of_bits(0xc0400001), 0xc0400006, STR(__LINE__)); // 0x1.000006p+0 * -0x1.800002p+1 = -0x1.80000cp+1
  comp32(single_of_bits(0xbf800003) * single_of_bits(0x40400001), 0xc0400006, STR(__LINE__)); // -0x1.000006p+0 * 0x1.800002p+1 = -0x1.80000cp+1
  comp32(single_of_bits(0x40400001) * single_of_bits(0xbf800003), 0xc0400006, STR(__LINE__)); // 0x1.800002p+1 * -0x1.000006p+0 = -0x1.80000cp+1
  comp32(single_of_bits(0x403fffff) * single_of_bits(0x3f7ffffe), 0x403ffffe, STR(__LINE__)); // 0x1.7ffffep+1 * 0x1.fffffcp-1 = 0x1.7ffffcp+1
  comp32(single_of_bits(0x3f7ffffe) * single_of_bits(0x403fffff), 0x403ffffe, STR(__LINE__)); // 0x1.fffffcp-1 * 0x1.7ffffep+1 = 0x1.7ffffcp+1
  comp32(single_of_bits(0xc03fffff) * single_of_bits(0xbf7ffffe), 0x403ffffe, STR(__LINE__)); // -0x1.7ffffep+1 * -0x1.fffffcp-1 = 0x1.7ffffcp+1
  comp32(single_of_bits(0xbf7ffffe) * single_of_bits(0xc03fffff), 0x403ffffe, STR(__LINE__)); // -0x1.fffffcp-1 * -0x1.7ffffep+1 = 0x1.7ffffcp+1
}

void f545(void) {
  comp32(single_of_bits(0xc03fffff) * single_of_bits(0x3f7ffffe), 0xc03ffffe, STR(__LINE__)); // -0x1.7ffffep+1 * 0x1.fffffcp-1 = -0x1.7ffffcp+1
  comp32(single_of_bits(0x3f7ffffe) * single_of_bits(0xc03fffff), 0xc03ffffe, STR(__LINE__)); // 0x1.fffffcp-1 * -0x1.7ffffep+1 = -0x1.7ffffcp+1
  comp32(single_of_bits(0xbf7ffffe) * single_of_bits(0x403fffff), 0xc03ffffe, STR(__LINE__)); // -0x1.fffffcp-1 * 0x1.7ffffep+1 = -0x1.7ffffcp+1
  comp32(single_of_bits(0x403fffff) * single_of_bits(0xbf7ffffe), 0xc03ffffe, STR(__LINE__)); // 0x1.7ffffep+1 * -0x1.fffffcp-1 = -0x1.7ffffcp+1
  comp32(single_of_bits(0x40dfffff) * single_of_bits(0x3f7ffffc), 0x40dffffc, STR(__LINE__)); // 0x1.bffffep+2 * 0x1.fffff8p-1 = 0x1.bffff8p+2
  comp32(single_of_bits(0x3f7ffffc) * single_of_bits(0x40dfffff), 0x40dffffc, STR(__LINE__)); // 0x1.fffff8p-1 * 0x1.bffffep+2 = 0x1.bffff8p+2
  comp32(single_of_bits(0xc0dfffff) * single_of_bits(0xbf7ffffc), 0x40dffffc, STR(__LINE__)); // -0x1.bffffep+2 * -0x1.fffff8p-1 = 0x1.bffff8p+2
  comp32(single_of_bits(0xbf7ffffc) * single_of_bits(0xc0dfffff), 0x40dffffc, STR(__LINE__)); // -0x1.fffff8p-1 * -0x1.bffffep+2 = 0x1.bffff8p+2
  comp32(single_of_bits(0xc0dfffff) * single_of_bits(0x3f7ffffc), 0xc0dffffc, STR(__LINE__)); // -0x1.bffffep+2 * 0x1.fffff8p-1 = -0x1.bffff8p+2
  comp32(single_of_bits(0x3f7ffffc) * single_of_bits(0xc0dfffff), 0xc0dffffc, STR(__LINE__)); // 0x1.fffff8p-1 * -0x1.bffffep+2 = -0x1.bffff8p+2
}

void f546(void) {
  comp32(single_of_bits(0xbf7ffffc) * single_of_bits(0x40dfffff), 0xc0dffffc, STR(__LINE__)); // -0x1.fffff8p-1 * 0x1.bffffep+2 = -0x1.bffff8p+2
  comp32(single_of_bits(0x40dfffff) * single_of_bits(0xbf7ffffc), 0xc0dffffc, STR(__LINE__)); // 0x1.bffffep+2 * -0x1.fffff8p-1 = -0x1.bffff8p+2
  comp32(single_of_bits(0x00c00001) * single_of_bits(0x40800001), 0x01c00003, STR(__LINE__)); // 0x1.800002p-126 * 0x1.000002p+2 = 0x1.800006p-124
  comp32(single_of_bits(0x40800001) * single_of_bits(0x00c00001), 0x01c00003, STR(__LINE__)); // 0x1.000002p+2 * 0x1.800002p-126 = 0x1.800006p-124
  comp32(single_of_bits(0x80c00001) * single_of_bits(0xc0800001), 0x01c00003, STR(__LINE__)); // -0x1.800002p-126 * -0x1.000002p+2 = 0x1.800006p-124
  comp32(single_of_bits(0xc0800001) * single_of_bits(0x80c00001), 0x01c00003, STR(__LINE__)); // -0x1.000002p+2 * -0x1.800002p-126 = 0x1.800006p-124
  comp32(single_of_bits(0x80c00001) * single_of_bits(0x40800001), 0x81c00003, STR(__LINE__)); // -0x1.800002p-126 * 0x1.000002p+2 = -0x1.800006p-124
  comp32(single_of_bits(0x40800001) * single_of_bits(0x80c00001), 0x81c00003, STR(__LINE__)); // 0x1.000002p+2 * -0x1.800002p-126 = -0x1.800006p-124
  comp32(single_of_bits(0xc0800001) * single_of_bits(0x00c00001), 0x81c00003, STR(__LINE__)); // -0x1.000002p+2 * 0x1.800002p-126 = -0x1.800006p-124
  comp32(single_of_bits(0x00c00001) * single_of_bits(0xc0800001), 0x81c00003, STR(__LINE__)); // 0x1.800002p-126 * -0x1.000002p+2 = -0x1.800006p-124
}

void f547(void) {
  comp32(single_of_bits(0x40e00001) * single_of_bits(0x3f800001), 0x40e00003, STR(__LINE__)); // 0x1.c00002p+2 * 0x1.000002p+0 = 0x1.c00006p+2
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x40e00001), 0x40e00003, STR(__LINE__)); // 0x1.000002p+0 * 0x1.c00002p+2 = 0x1.c00006p+2
  comp32(single_of_bits(0xc0e00001) * single_of_bits(0xbf800001), 0x40e00003, STR(__LINE__)); // -0x1.c00002p+2 * -0x1.000002p+0 = 0x1.c00006p+2
  comp32(single_of_bits(0xbf800001) * single_of_bits(0xc0e00001), 0x40e00003, STR(__LINE__)); // -0x1.000002p+0 * -0x1.c00002p+2 = 0x1.c00006p+2
  comp32(single_of_bits(0xc0e00001) * single_of_bits(0x3f800001), 0xc0e00003, STR(__LINE__)); // -0x1.c00002p+2 * 0x1.000002p+0 = -0x1.c00006p+2
  comp32(single_of_bits(0x3f800001) * single_of_bits(0xc0e00001), 0xc0e00003, STR(__LINE__)); // 0x1.000002p+0 * -0x1.c00002p+2 = -0x1.c00006p+2
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x40e00001), 0xc0e00003, STR(__LINE__)); // -0x1.000002p+0 * 0x1.c00002p+2 = -0x1.c00006p+2
  comp32(single_of_bits(0x40e00001) * single_of_bits(0xbf800001), 0xc0e00003, STR(__LINE__)); // 0x1.c00002p+2 * -0x1.000002p+0 = -0x1.c00006p+2
  comp32(single_of_bits(0x3f7ffffe) * single_of_bits(0x3f800001), 0x3f800000, STR(__LINE__)); // 0x1.fffffcp-1 * 0x1.000002p+0 = 0x1p+0
  comp32(single_of_bits(0x3f800001) * single_of_bits(0x3f7ffffe), 0x3f800000, STR(__LINE__)); // 0x1.000002p+0 * 0x1.fffffcp-1 = 0x1p+0
}

void f548(void) {
  comp32(single_of_bits(0xbf7ffffe) * single_of_bits(0xbf800001), 0x3f800000, STR(__LINE__)); // -0x1.fffffcp-1 * -0x1.000002p+0 = 0x1p+0
  comp32(single_of_bits(0xbf800001) * single_of_bits(0xbf7ffffe), 0x3f800000, STR(__LINE__)); // -0x1.000002p+0 * -0x1.fffffcp-1 = 0x1p+0
  comp32(single_of_bits(0xbf7ffffe) * single_of_bits(0x3f800001), 0xbf800000, STR(__LINE__)); // -0x1.fffffcp-1 * 0x1.000002p+0 = -0x1p+0
  comp32(single_of_bits(0x3f800001) * single_of_bits(0xbf7ffffe), 0xbf800000, STR(__LINE__)); // 0x1.000002p+0 * -0x1.fffffcp-1 = -0x1p+0
  comp32(single_of_bits(0xbf800001) * single_of_bits(0x3f7ffffe), 0xbf800000, STR(__LINE__)); // -0x1.000002p+0 * 0x1.fffffcp-1 = -0x1p+0
  comp32(single_of_bits(0x3f7ffffe) * single_of_bits(0xbf800001), 0xbf800000, STR(__LINE__)); // 0x1.fffffcp-1 * -0x1.000002p+0 = -0x1p+0
  comp32(single_of_bits(0x403fffff) * single_of_bits(0x3f7ffffd), 0x403ffffd, STR(__LINE__)); // 0x1.7ffffep+1 * 0x1.fffffap-1 = 0x1.7ffffap+1
  comp32(single_of_bits(0x3f7ffffd) * single_of_bits(0x403fffff), 0x403ffffd, STR(__LINE__)); // 0x1.fffffap-1 * 0x1.7ffffep+1 = 0x1.7ffffap+1
  comp32(single_of_bits(0xc03fffff) * single_of_bits(0xbf7ffffd), 0x403ffffd, STR(__LINE__)); // -0x1.7ffffep+1 * -0x1.fffffap-1 = 0x1.7ffffap+1
  comp32(single_of_bits(0xbf7ffffd) * single_of_bits(0xc03fffff), 0x403ffffd, STR(__LINE__)); // -0x1.fffffap-1 * -0x1.7ffffep+1 = 0x1.7ffffap+1
}

void f549(void) {
  comp32(single_of_bits(0xc03fffff) * single_of_bits(0x3f7ffffd), 0xc03ffffd, STR(__LINE__)); // -0x1.7ffffep+1 * 0x1.fffffap-1 = -0x1.7ffffap+1
  comp32(single_of_bits(0x3f7ffffd) * single_of_bits(0xc03fffff), 0xc03ffffd, STR(__LINE__)); // 0x1.fffffap-1 * -0x1.7ffffep+1 = -0x1.7ffffap+1
  comp32(single_of_bits(0xbf7ffffd) * single_of_bits(0x403fffff), 0xc03ffffd, STR(__LINE__)); // -0x1.fffffap-1 * 0x1.7ffffep+1 = -0x1.7ffffap+1
  comp32(single_of_bits(0x403fffff) * single_of_bits(0xbf7ffffd), 0xc03ffffd, STR(__LINE__)); // 0x1.7ffffep+1 * -0x1.fffffap-1 = -0x1.7ffffap+1
  comp32(single_of_bits(0x01600001) * single_of_bits(0x40800001), 0x02600003, STR(__LINE__)); // 0x1.c00002p-125 * 0x1.000002p+2 = 0x1.c00006p-123
  comp32(single_of_bits(0x40800001) * single_of_bits(0x01600001), 0x02600003, STR(__LINE__)); // 0x1.000002p+2 * 0x1.c00002p-125 = 0x1.c00006p-123
  comp32(single_of_bits(0x81600001) * single_of_bits(0xc0800001), 0x02600003, STR(__LINE__)); // -0x1.c00002p-125 * -0x1.000002p+2 = 0x1.c00006p-123
  comp32(single_of_bits(0xc0800001) * single_of_bits(0x81600001), 0x02600003, STR(__LINE__)); // -0x1.000002p+2 * -0x1.c00002p-125 = 0x1.c00006p-123
  comp32(single_of_bits(0x81600001) * single_of_bits(0x40800001), 0x82600003, STR(__LINE__)); // -0x1.c00002p-125 * 0x1.000002p+2 = -0x1.c00006p-123
  comp32(single_of_bits(0x40800001) * single_of_bits(0x81600001), 0x82600003, STR(__LINE__)); // 0x1.000002p+2 * -0x1.c00002p-125 = -0x1.c00006p-123
}

void f550(void) {
  comp32(single_of_bits(0xc0800001) * single_of_bits(0x01600001), 0x82600003, STR(__LINE__)); // -0x1.000002p+2 * 0x1.c00002p-125 = -0x1.c00006p-123
  comp32(single_of_bits(0x01600001) * single_of_bits(0xc0800001), 0x82600003, STR(__LINE__)); // 0x1.c00002p-125 * -0x1.000002p+2 = -0x1.c00006p-123
  comp32(single_of_bits(0x007fffff) * single_of_bits(0x40000000), 0x00fffffe, STR(__LINE__)); // 0x1.fffffcp-127 * 0x1p+1 = 0x1.fffffcp-126
  comp32(single_of_bits(0x40000000) * single_of_bits(0x007fffff), 0x00fffffe, STR(__LINE__)); // 0x1p+1 * 0x1.fffffcp-127 = 0x1.fffffcp-126
  comp32(single_of_bits(0x807fffff) * single_of_bits(0xc0000000), 0x00fffffe, STR(__LINE__)); // -0x1.fffffcp-127 * -0x1p+1 = 0x1.fffffcp-126
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x807fffff), 0x00fffffe, STR(__LINE__)); // -0x1p+1 * -0x1.fffffcp-127 = 0x1.fffffcp-126
  comp32(single_of_bits(0x807fffff) * single_of_bits(0x40000000), 0x80fffffe, STR(__LINE__)); // -0x1.fffffcp-127 * 0x1p+1 = -0x1.fffffcp-126
  comp32(single_of_bits(0x40000000) * single_of_bits(0x807fffff), 0x80fffffe, STR(__LINE__)); // 0x1p+1 * -0x1.fffffcp-127 = -0x1.fffffcp-126
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x007fffff), 0x80fffffe, STR(__LINE__)); // -0x1p+1 * 0x1.fffffcp-127 = -0x1.fffffcp-126
  comp32(single_of_bits(0x007fffff) * single_of_bits(0xc0000000), 0x80fffffe, STR(__LINE__)); // 0x1.fffffcp-127 * -0x1p+1 = -0x1.fffffcp-126
}

void f551(void) {
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x007ffffd), 0x80fffffa, STR(__LINE__)); // -0x1p+1 * 0x1.fffff4p-127 = -0x1.fffff4p-126
  comp32(single_of_bits(0x007ffffd) * single_of_bits(0xc0000000), 0x80fffffa, STR(__LINE__)); // 0x1.fffff4p-127 * -0x1p+1 = -0x1.fffff4p-126
  comp32(single_of_bits(0x807ffffd) * single_of_bits(0xc0000000), 0x00fffffa, STR(__LINE__)); // -0x1.fffff4p-127 * -0x1p+1 = 0x1.fffff4p-126
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x807ffffd), 0x00fffffa, STR(__LINE__)); // -0x1p+1 * -0x1.fffff4p-127 = 0x1.fffff4p-126
  comp32(single_of_bits(0x40000000) * single_of_bits(0x807ffffd), 0x80fffffa, STR(__LINE__)); // 0x1p+1 * -0x1.fffff4p-127 = -0x1.fffff4p-126
  comp32(single_of_bits(0x807ffffd) * single_of_bits(0x40000000), 0x80fffffa, STR(__LINE__)); // -0x1.fffff4p-127 * 0x1p+1 = -0x1.fffff4p-126
  comp32(single_of_bits(0x007ffffd) * single_of_bits(0x40000000), 0x00fffffa, STR(__LINE__)); // 0x1.fffff4p-127 * 0x1p+1 = 0x1.fffff4p-126
  comp32(single_of_bits(0x40000000) * single_of_bits(0x007ffffd), 0x00fffffa, STR(__LINE__)); // 0x1p+1 * 0x1.fffff4p-127 = 0x1.fffff4p-126
  comp32(single_of_bits(0x007ffffc) * single_of_bits(0x40000000), 0x00fffff8, STR(__LINE__)); // 0x1.fffffp-127 * 0x1p+1 = 0x1.fffffp-126
  comp32(single_of_bits(0x40000000) * single_of_bits(0x007ffffc), 0x00fffff8, STR(__LINE__)); // 0x1p+1 * 0x1.fffffp-127 = 0x1.fffffp-126
}

void f552(void) {
  comp32(single_of_bits(0x807ffffc) * single_of_bits(0xc0000000), 0x00fffff8, STR(__LINE__)); // -0x1.fffffp-127 * -0x1p+1 = 0x1.fffffp-126
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x807ffffc), 0x00fffff8, STR(__LINE__)); // -0x1p+1 * -0x1.fffffp-127 = 0x1.fffffp-126
  comp32(single_of_bits(0x007ffffc) * single_of_bits(0xc0000000), 0x80fffff8, STR(__LINE__)); // 0x1.fffffp-127 * -0x1p+1 = -0x1.fffffp-126
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x007ffffc), 0x80fffff8, STR(__LINE__)); // -0x1p+1 * 0x1.fffffp-127 = -0x1.fffffp-126
  comp32(single_of_bits(0x40000000) * single_of_bits(0x807ffffc), 0x80fffff8, STR(__LINE__)); // 0x1p+1 * -0x1.fffffp-127 = -0x1.fffffp-126
  comp32(single_of_bits(0x807ffffc) * single_of_bits(0x40000000), 0x80fffff8, STR(__LINE__)); // -0x1.fffffp-127 * 0x1p+1 = -0x1.fffffp-126
  comp32(single_of_bits(0x00000001) * single_of_bits(0x40000000), 0x00000002, STR(__LINE__)); // 0x1p-149 * 0x1p+1 = 0x1p-148
  comp32(single_of_bits(0x40000000) * single_of_bits(0x00000001), 0x00000002, STR(__LINE__)); // 0x1p+1 * 0x1p-149 = 0x1p-148
  comp32(single_of_bits(0x80000001) * single_of_bits(0xc0000000), 0x00000002, STR(__LINE__)); // -0x1p-149 * -0x1p+1 = 0x1p-148
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x80000001), 0x00000002, STR(__LINE__)); // -0x1p+1 * -0x1p-149 = 0x1p-148
}

void f553(void) {
  comp32(single_of_bits(0x00000001) * single_of_bits(0xc0000000), 0x80000002, STR(__LINE__)); // 0x1p-149 * -0x1p+1 = -0x1p-148
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x00000001), 0x80000002, STR(__LINE__)); // -0x1p+1 * 0x1p-149 = -0x1p-148
  comp32(single_of_bits(0x40000000) * single_of_bits(0x80000001), 0x80000002, STR(__LINE__)); // 0x1p+1 * -0x1p-149 = -0x1p-148
  comp32(single_of_bits(0x80000001) * single_of_bits(0x40000000), 0x80000002, STR(__LINE__)); // -0x1p-149 * 0x1p+1 = -0x1p-148
  comp32(single_of_bits(0x00000002) * single_of_bits(0x40000000), 0x00000004, STR(__LINE__)); // 0x1p-148 * 0x1p+1 = 0x1p-147
  comp32(single_of_bits(0x40000000) * single_of_bits(0x00000002), 0x00000004, STR(__LINE__)); // 0x1p+1 * 0x1p-148 = 0x1p-147
  comp32(single_of_bits(0x80000002) * single_of_bits(0xc0000000), 0x00000004, STR(__LINE__)); // -0x1p-148 * -0x1p+1 = 0x1p-147
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x80000002), 0x00000004, STR(__LINE__)); // -0x1p+1 * -0x1p-148 = 0x1p-147
  comp32(single_of_bits(0x00000002) * single_of_bits(0xc0000000), 0x80000004, STR(__LINE__)); // 0x1p-148 * -0x1p+1 = -0x1p-147
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x00000002), 0x80000004, STR(__LINE__)); // -0x1p+1 * 0x1p-148 = -0x1p-147
}

void f554(void) {
  comp32(single_of_bits(0x40000000) * single_of_bits(0x80000002), 0x80000004, STR(__LINE__)); // 0x1p+1 * -0x1p-148 = -0x1p-147
  comp32(single_of_bits(0x80000002) * single_of_bits(0x40000000), 0x80000004, STR(__LINE__)); // -0x1p-148 * 0x1p+1 = -0x1p-147
  comp32(single_of_bits(0x00000003) * single_of_bits(0x40000000), 0x00000006, STR(__LINE__)); // 0x1.8p-148 * 0x1p+1 = 0x1.8p-147
  comp32(single_of_bits(0x40000000) * single_of_bits(0x00000003), 0x00000006, STR(__LINE__)); // 0x1p+1 * 0x1.8p-148 = 0x1.8p-147
  comp32(single_of_bits(0x80000003) * single_of_bits(0xc0000000), 0x00000006, STR(__LINE__)); // -0x1.8p-148 * -0x1p+1 = 0x1.8p-147
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x80000003), 0x00000006, STR(__LINE__)); // -0x1p+1 * -0x1.8p-148 = 0x1.8p-147
  comp32(single_of_bits(0x00000003) * single_of_bits(0xc0000000), 0x80000006, STR(__LINE__)); // 0x1.8p-148 * -0x1p+1 = -0x1.8p-147
  comp32(single_of_bits(0xc0000000) * single_of_bits(0x00000003), 0x80000006, STR(__LINE__)); // -0x1p+1 * 0x1.8p-148 = -0x1.8p-147
  comp32(single_of_bits(0x40000000) * single_of_bits(0x80000003), 0x80000006, STR(__LINE__)); // 0x1p+1 * -0x1.8p-148 = -0x1.8p-147
  comp32(single_of_bits(0x80000003) * single_of_bits(0x40000000), 0x80000006, STR(__LINE__)); // -0x1.8p-148 * 0x1p+1 = -0x1.8p-147
}

void f555(void) {
  comp32(single_of_bits(0x40400000) * single_of_bits(0x00000001), 0x00000003, STR(__LINE__)); // 0x1.8p+1 * 0x1p-149 = 0x1.8p-148
  comp32(single_of_bits(0x00000001) * single_of_bits(0x40400000), 0x00000003, STR(__LINE__)); // 0x1p-149 * 0x1.8p+1 = 0x1.8p-148
  comp32(single_of_bits(0xc0400000) * single_of_bits(0x80000001), 0x00000003, STR(__LINE__)); // -0x1.8p+1 * -0x1p-149 = 0x1.8p-148
  comp32(single_of_bits(0x80000001) * single_of_bits(0xc0400000), 0x00000003, STR(__LINE__)); // -0x1p-149 * -0x1.8p+1 = 0x1.8p-148
  comp32(single_of_bits(0x40400000) * single_of_bits(0x80000001), 0x80000003, STR(__LINE__)); // 0x1.8p+1 * -0x1p-149 = -0x1.8p-148
  comp32(single_of_bits(0x80000001) * single_of_bits(0x40400000), 0x80000003, STR(__LINE__)); // -0x1p-149 * 0x1.8p+1 = -0x1.8p-148
  comp32(single_of_bits(0x00000001) * single_of_bits(0xc0400000), 0x80000003, STR(__LINE__)); // 0x1p-149 * -0x1.8p+1 = -0x1.8p-148
  comp32(single_of_bits(0xc0400000) * single_of_bits(0x00000001), 0x80000003, STR(__LINE__)); // -0x1.8p+1 * 0x1p-149 = -0x1.8p-148
  comp32(single_of_bits(0x40400000) * single_of_bits(0x00000002), 0x00000006, STR(__LINE__)); // 0x1.8p+1 * 0x1p-148 = 0x1.8p-147
  comp32(single_of_bits(0x00000002) * single_of_bits(0x40400000), 0x00000006, STR(__LINE__)); // 0x1p-148 * 0x1.8p+1 = 0x1.8p-147
}

void f556(void) {
  comp32(single_of_bits(0xc0400000) * single_of_bits(0x80000002), 0x00000006, STR(__LINE__)); // -0x1.8p+1 * -0x1p-148 = 0x1.8p-147
  comp32(single_of_bits(0x80000002) * single_of_bits(0xc0400000), 0x00000006, STR(__LINE__)); // -0x1p-148 * -0x1.8p+1 = 0x1.8p-147
  comp32(single_of_bits(0x40400000) * single_of_bits(0x80000002), 0x80000006, STR(__LINE__)); // 0x1.8p+1 * -0x1p-148 = -0x1.8p-147
  comp32(single_of_bits(0x80000002) * single_of_bits(0x40400000), 0x80000006, STR(__LINE__)); // -0x1p-148 * 0x1.8p+1 = -0x1.8p-147
  comp32(single_of_bits(0x00000002) * single_of_bits(0xc0400000), 0x80000006, STR(__LINE__)); // 0x1p-148 * -0x1.8p+1 = -0x1.8p-147
  comp32(single_of_bits(0xc0400000) * single_of_bits(0x00000002), 0x80000006, STR(__LINE__)); // -0x1.8p+1 * 0x1p-148 = -0x1.8p-147
  comp32(single_of_bits(0x40400000) * single_of_bits(0x00000003), 0x00000009, STR(__LINE__)); // 0x1.8p+1 * 0x1.8p-148 = 0x1.2p-146
  comp32(single_of_bits(0x00000003) * single_of_bits(0x40400000), 0x00000009, STR(__LINE__)); // 0x1.8p-148 * 0x1.8p+1 = 0x1.2p-146
  comp32(single_of_bits(0xc0400000) * single_of_bits(0x80000003), 0x00000009, STR(__LINE__)); // -0x1.8p+1 * -0x1.8p-148 = 0x1.2p-146
  comp32(single_of_bits(0x80000003) * single_of_bits(0xc0400000), 0x00000009, STR(__LINE__)); // -0x1.8p-148 * -0x1.8p+1 = 0x1.2p-146
}

void f557(void) {
  comp32(single_of_bits(0x40400000) * single_of_bits(0x80000003), 0x80000009, STR(__LINE__)); // 0x1.8p+1 * -0x1.8p-148 = -0x1.2p-146
  comp32(single_of_bits(0x80000003) * single_of_bits(0x40400000), 0x80000009, STR(__LINE__)); // -0x1.8p-148 * 0x1.8p+1 = -0x1.2p-146
  comp32(single_of_bits(0x00000003) * single_of_bits(0xc0400000), 0x80000009, STR(__LINE__)); // 0x1.8p-148 * -0x1.8p+1 = -0x1.2p-146
  comp32(single_of_bits(0xc0400000) * single_of_bits(0x00000003), 0x80000009, STR(__LINE__)); // -0x1.8p+1 * 0x1.8p-148 = -0x1.2p-146
  comp32(single_of_bits(0x40800000) * single_of_bits(0x00000001), 0x00000004, STR(__LINE__)); // 0x1p+2 * 0x1p-149 = 0x1p-147
  comp32(single_of_bits(0x00000001) * single_of_bits(0x40800000), 0x00000004, STR(__LINE__)); // 0x1p-149 * 0x1p+2 = 0x1p-147
  comp32(single_of_bits(0x40800000) * single_of_bits(0x80000001), 0x80000004, STR(__LINE__)); // 0x1p+2 * -0x1p-149 = -0x1p-147
  comp32(single_of_bits(0x80000001) * single_of_bits(0x40800000), 0x80000004, STR(__LINE__)); // -0x1p-149 * 0x1p+2 = -0x1p-147
  comp32(single_of_bits(0xc0800000) * single_of_bits(0x80000001), 0x00000004, STR(__LINE__)); // -0x1p+2 * -0x1p-149 = 0x1p-147
  comp32(single_of_bits(0x80000001) * single_of_bits(0xc0800000), 0x00000004, STR(__LINE__)); // -0x1p-149 * -0x1p+2 = 0x1p-147
}

void f558(void) {
  comp32(single_of_bits(0xc0800000) * single_of_bits(0x00000001), 0x80000004, STR(__LINE__)); // -0x1p+2 * 0x1p-149 = -0x1p-147
  comp32(single_of_bits(0x00000001) * single_of_bits(0xc0800000), 0x80000004, STR(__LINE__)); // 0x1p-149 * -0x1p+2 = -0x1p-147
  comp32(single_of_bits(0x40800000) * single_of_bits(0x00000002), 0x00000008, STR(__LINE__)); // 0x1p+2 * 0x1p-148 = 0x1p-146
  comp32(single_of_bits(0x00000002) * single_of_bits(0x40800000), 0x00000008, STR(__LINE__)); // 0x1p-148 * 0x1p+2 = 0x1p-146
  comp32(single_of_bits(0x40800000) * single_of_bits(0x80000002), 0x80000008, STR(__LINE__)); // 0x1p+2 * -0x1p-148 = -0x1p-146
  comp32(single_of_bits(0x80000002) * single_of_bits(0x40800000), 0x80000008, STR(__LINE__)); // -0x1p-148 * 0x1p+2 = -0x1p-146
  comp32(single_of_bits(0xc0800000) * single_of_bits(0x80000002), 0x00000008, STR(__LINE__)); // -0x1p+2 * -0x1p-148 = 0x1p-146
  comp32(single_of_bits(0x80000002) * single_of_bits(0xc0800000), 0x00000008, STR(__LINE__)); // -0x1p-148 * -0x1p+2 = 0x1p-146
  comp32(single_of_bits(0xc0800000) * single_of_bits(0x00000002), 0x80000008, STR(__LINE__)); // -0x1p+2 * 0x1p-148 = -0x1p-146
  comp32(single_of_bits(0x00000002) * single_of_bits(0xc0800000), 0x80000008, STR(__LINE__)); // 0x1p-148 * -0x1p+2 = -0x1p-146
}

void f559(void) {
  comp32(single_of_bits(0x80000001) * single_of_bits(0xc0a00000), 0x00000005, STR(__LINE__)); // -0x1p-149 * -0x1.4p+2 = 0x1.4p-147
  comp32(single_of_bits(0xc0a00000) * single_of_bits(0x80000001), 0x00000005, STR(__LINE__)); // -0x1.4p+2 * -0x1p-149 = 0x1.4p-147
  comp32(single_of_bits(0x40a00000) * single_of_bits(0x00000001), 0x00000005, STR(__LINE__)); // 0x1.4p+2 * 0x1p-149 = 0x1.4p-147
  comp32(single_of_bits(0x00000001) * single_of_bits(0x40a00000), 0x00000005, STR(__LINE__)); // 0x1p-149 * 0x1.4p+2 = 0x1.4p-147
  comp32(single_of_bits(0x80000001) * single_of_bits(0x40a00000), 0x80000005, STR(__LINE__)); // -0x1p-149 * 0x1.4p+2 = -0x1.4p-147
  comp32(single_of_bits(0x40a00000) * single_of_bits(0x80000001), 0x80000005, STR(__LINE__)); // 0x1.4p+2 * -0x1p-149 = -0x1.4p-147
  comp32(single_of_bits(0x00000001) * single_of_bits(0xc0a00000), 0x80000005, STR(__LINE__)); // 0x1p-149 * -0x1.4p+2 = -0x1.4p-147
  comp32(single_of_bits(0xc0a00000) * single_of_bits(0x00000001), 0x80000005, STR(__LINE__)); // -0x1.4p+2 * 0x1p-149 = -0x1.4p-147
  comp32(single_of_bits(0x00000001) * single_of_bits(0x4c000000), 0x01800000, STR(__LINE__)); // 0x1p-149 * 0x1p+25 = 0x1p-124
  comp32(single_of_bits(0x4c000000) * single_of_bits(0x00000001), 0x01800000, STR(__LINE__)); // 0x1p+25 * 0x1p-149 = 0x1p-124
}

void f560(void) {
  comp32(single_of_bits(0x80000001) * single_of_bits(0xcc000000), 0x01800000, STR(__LINE__)); // -0x1p-149 * -0x1p+25 = 0x1p-124
  comp32(single_of_bits(0xcc000000) * single_of_bits(0x80000001), 0x01800000, STR(__LINE__)); // -0x1p+25 * -0x1p-149 = 0x1p-124
  comp32(single_of_bits(0x80000001) * single_of_bits(0x4c000000), 0x81800000, STR(__LINE__)); // -0x1p-149 * 0x1p+25 = -0x1p-124
  comp32(single_of_bits(0x4c000000) * single_of_bits(0x80000001), 0x81800000, STR(__LINE__)); // 0x1p+25 * -0x1p-149 = -0x1p-124
  comp32(single_of_bits(0xcc000000) * single_of_bits(0x00000001), 0x81800000, STR(__LINE__)); // -0x1p+25 * 0x1p-149 = -0x1p-124
  comp32(single_of_bits(0x00000001) * single_of_bits(0xcc000000), 0x81800000, STR(__LINE__)); // 0x1p-149 * -0x1p+25 = -0x1p-124
  comp32(single_of_bits(0x00000001) * single_of_bits(0x4b000000), 0x00800000, STR(__LINE__)); // 0x1p-149 * 0x1p+23 = 0x1p-126
  comp32(single_of_bits(0x4b000000) * single_of_bits(0x00000001), 0x00800000, STR(__LINE__)); // 0x1p+23 * 0x1p-149 = 0x1p-126
  comp32(single_of_bits(0x80000001) * single_of_bits(0xcb000000), 0x00800000, STR(__LINE__)); // -0x1p-149 * -0x1p+23 = 0x1p-126
  comp32(single_of_bits(0xcb000000) * single_of_bits(0x80000001), 0x00800000, STR(__LINE__)); // -0x1p+23 * -0x1p-149 = 0x1p-126
}

void f561(void) {
  comp32(single_of_bits(0x80000001) * single_of_bits(0x4b000000), 0x80800000, STR(__LINE__)); // -0x1p-149 * 0x1p+23 = -0x1p-126
  comp32(single_of_bits(0x4b000000) * single_of_bits(0x80000001), 0x80800000, STR(__LINE__)); // 0x1p+23 * -0x1p-149 = -0x1p-126
  comp32(single_of_bits(0xcb000000) * single_of_bits(0x00000001), 0x80800000, STR(__LINE__)); // -0x1p+23 * 0x1p-149 = -0x1p-126
  comp32(single_of_bits(0x00000001) * single_of_bits(0xcb000000), 0x80800000, STR(__LINE__)); // 0x1p-149 * -0x1p+23 = -0x1p-126
}

int main(void) {
  f0();
  f1();
  f2();
  f3();
  f4();
  f5();
  f6();
  f7();
  f8();
  f9();
  f10();
  f11();
  f12();
  f13();
  f14();
  f15();
  f16();
  f17();
  f18();
  f19();
  f20();
  f21();
  f22();
  f23();
  f24();
  f25();
  f26();
  f27();
  f28();
  f29();
  f30();
  f31();
  f32();
  f33();
  f34();
  f35();
  f36();
  f37();
  f38();
  f39();
  f40();
  f41();
  f42();
  f43();
  f44();
  f45();
  f46();
  f47();
  f48();
  f49();
  f50();
  f51();
  f52();
  f53();
  f54();
  f55();
  f56();
  f57();
  f58();
  f59();
  f60();
  f61();
  f62();
  f63();
  f64();
  f65();
  f66();
  f67();
  f68();
  f69();
  f70();
  f71();
  f72();
  f73();
  f74();
  f75();
  f76();
  f77();
  f78();
  f79();
  f80();
  f81();
  f82();
  f83();
  f84();
  f85();
  f86();
  f87();
  f88();
  f89();
  f90();
  f91();
  f92();
  f93();
  f94();
  f95();
  f96();
  f97();
  f98();
  f99();
  f100();
  f101();
  f102();
  f103();
  f104();
  f105();
  f106();
  f107();
  f108();
  f109();
  f110();
  f111();
  f112();
  f113();
  f114();
  f115();
  f116();
  f117();
  f118();
  f119();
  f120();
  f121();
  f122();
  f123();
  f124();
  f125();
  f126();
  f127();
  f128();
  f129();
  f130();
  f131();
  f132();
  f133();
  f134();
  f135();
  f136();
  f137();
  f138();
  f139();
  f140();
  f141();
  f142();
  f143();
  f144();
  f145();
  f146();
  f147();
  f148();
  f149();
  f150();
  f151();
  f152();
  f153();
  f154();
  f155();
  f156();
  f157();
  f158();
  f159();
  f160();
  f161();
  f162();
  f163();
  f164();
  f165();
  f166();
  f167();
  f168();
  f169();
  f170();
  f171();
  f172();
  f173();
  f174();
  f175();
  f176();
  f177();
  f178();
  f179();
  f180();
  f181();
  f182();
  f183();
  f184();
  f185();
  f186();
  f187();
  f188();
  f189();
  f190();
  f191();
  f192();
  f193();
  f194();
  f195();
  f196();
  f197();
  f198();
  f199();
  f200();
  f201();
  f202();
  f203();
  f204();
  f205();
  f206();
  f207();
  f208();
  f209();
  f210();
  f211();
  f212();
  f213();
  f214();
  f215();
  f216();
  f217();
  f218();
  f219();
  f220();
  f221();
  f222();
  f223();
  f224();
  f225();
  f226();
  f227();
  f228();
  f229();
  f230();
  f231();
  f232();
  f233();
  f234();
  f235();
  f236();
  f237();
  f238();
  f239();
  f240();
  f241();
  f242();
  f243();
  f244();
  f245();
  f246();
  f247();
  f248();
  f249();
  f250();
  f251();
  f252();
  f253();
  f254();
  f255();
  f256();
  f257();
  f258();
  f259();
  f260();
  f261();
  f262();
  f263();
  f264();
  f265();
  f266();
  f267();
  f268();
  f269();
  f270();
  f271();
  f272();
  f273();
  f274();
  f275();
  f276();
  f277();
  f278();
  f279();
  f280();
  f281();
  f282();
  f283();
  f284();
  f285();
  f286();
  f287();
  f288();
  f289();
  f290();
  f291();
  f292();
  f293();
  f294();
  f295();
  f296();
  f297();
  f298();
  f299();
  f300();
  f301();
  f302();
  f303();
  f304();
  f305();
  f306();
  f307();
  f308();
  f309();
  f310();
  f311();
  f312();
  f313();
  f314();
  f315();
  f316();
  f317();
  f318();
  f319();
  f320();
  f321();
  f322();
  f323();
  f324();
  f325();
  f326();
  f327();
  f328();
  f329();
  f330();
  f331();
  f332();
  f333();
  f334();
  f335();
  f336();
  f337();
  f338();
  f339();
  f340();
  f341();
  f342();
  f343();
  f344();
  f345();
  f346();
  f347();
  f348();
  f349();
  f350();
  f351();
  f352();
  f353();
  f354();
  f355();
  f356();
  f357();
  f358();
  f359();
  f360();
  f361();
  f362();
  f363();
  f364();
  f365();
  f366();
  f367();
  f368();
  f369();
  f370();
  f371();
  f372();
  f373();
  f374();
  f375();
  f376();
  f377();
  f378();
  f379();
  f380();
  f381();
  f382();
  f383();
  f384();
  f385();
  f386();
  f387();
  f388();
  f389();
  f390();
  f391();
  f392();
  f393();
  f394();
  f395();
  f396();
  f397();
  f398();
  f399();
  f400();
  f401();
  f402();
  f403();
  f404();
  f405();
  f406();
  f407();
  f408();
  f409();
  f410();
  f411();
  f412();
  f413();
  f414();
  f415();
  f416();
  f417();
  f418();
  f419();
  f420();
  f421();
  f422();
  f423();
  f424();
  f425();
  f426();
  f427();
  f428();
  f429();
  f430();
  f431();
  f432();
  f433();
  f434();
  f435();
  f436();
  f437();
  f438();
  f439();
  f440();
  f441();
  f442();
  f443();
  f444();
  f445();
  f446();
  f447();
  f448();
  f449();
  f450();
  f451();
  f452();
  f453();
  f454();
  f455();
  f456();
  f457();
  f458();
  f459();
  f460();
  f461();
  f462();
  f463();
  f464();
  f465();
  f466();
  f467();
  f468();
  f469();
  f470();
  f471();
  f472();
  f473();
  f474();
  f475();
  f476();
  f477();
  f478();
  f479();
  f480();
  f481();
  f482();
  f483();
  f484();
  f485();
  f486();
  f487();
  f488();
  f489();
  f490();
  f491();
  f492();
  f493();
  f494();
  f495();
  f496();
  f497();
  f498();
  f499();
  f500();
  f501();
  f502();
  f503();
  f504();
  f505();
  f506();
  f507();
  f508();
  f509();
  f510();
  f511();
  f512();
  f513();
  f514();
  f515();
  f516();
  f517();
  f518();
  f519();
  f520();
  f521();
  f522();
  f523();
  f524();
  f525();
  f526();
  f527();
  f528();
  f529();
  f530();
  f531();
  f532();
  f533();
  f534();
  f535();
  f536();
  f537();
  f538();
  f539();
  f540();
  f541();
  f542();
  f543();
  f544();
  f545();
  f546();
  f547();
  f548();
  f549();
  f550();
  f551();
  f552();
  f553();
  f554();
  f555();
  f556();
  f557();
  f558();
  f559();
  f560();
  f561();
  printf("%d error(s) detected.\n", num_errors);
  return 0;
}
