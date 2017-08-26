/* A bytecode interpreter for a simple virtual machine */

#include <stdio.h>
#include <stdlib.h>

#define STACKSIZE 256

enum wordcode_instruct {
  WCALL1, WCALL1_pop1, WCONST, WCONST_pop1, WBRANCHIF, WBRANCHIF_pop1,
  WCALL3, WRETURN, WBRANCH, WLTINT, WADDINT, WOFFSETINT, WDUP, WGRAB, WSTOP
};

#define Opcode (instr & 0xFF)
#define Byte1 ((instr >> 8) & 0xFF)
#define Byte2 ((instr >> 16) & 0xFF)
#define Byte3 (instr >> 24)
#define Op1 sp[Byte1]
#define Op2 sp[Byte2]
#define Op3 sp[Byte3]
#define Imm8s ((int)instr >> 24)
#define Imm16u (instr >> 16)
#define Imm16s ((int)instr >> 16)
#define Imm24u (instr >> 8)
#define Imm24s ((int)instr >> 8)
#define Adjust1 (sp += instr & 1)
#define Adjust2 (sp += instr & 3)
#define Adjustbyte1 (sp += Byte1)
#define Adjustbyte2 (sp += Byte2)
#define Adjustbyte3 (sp += Byte3)
#define Extrabyte1(w) (w & 0xFF)
#define Extrabyte2(w) ((w >> 8) & 0xFF)
#define Extrabyte3(w) ((w >> 16) & 0xFF)
#define Extrabyte4(w) (w >> 24)
#define Extraop1(w) sp[Extrabyte1(w)]
#define Extraop2(w) sp[Extrabyte2(w)]
#define Extraop3(w) sp[Extrabyte3(w)]
#define Extraop4(w) sp[Extrabyte4(w)]
#define Push1(x) \
  sp-=1, sp[0]=x
#define Push2(x,y) \
  sp-=2, sp[1]=x, sp[0]=y
#define Push3(x,y,z) \
  sp-=3, sp[2]=x, sp[1]=y, sp[0]=z
#define Push4(x,y,z,t) \
  sp-=4, sp[3]=x, sp[2]=y, sp[1]=z, sp[0]=t
#define Push5(x,y,z,t,u) \
  sp-=5, sp[4]=x, sp[3]=y, sp[2]=z, sp[1]=t, sp[0]=u
#define Push6(x,y,z,t,u,v) \
  sp-=6, sp[5]=x, sp[4]=y, sp[3]=z, sp[2]=t, sp[1]=u, sp[0]=v
#define Push7(x,y,z,t,u,v,w) \
  sp-=7, sp[6]=x, sp[5]=y, sp[4]=z, sp[3]=t, sp[2]=u, sp[1]=v, sp[0]=w

long stack[STACKSIZE];

long wordcode_interp(unsigned int* code)
{
  long * sp;
  unsigned int * pc;
  unsigned int instr;
  int extra_args = 0;

  sp = stack + STACKSIZE;
  pc = code;
  while (1) {
    instr = *pc++;
    switch (Opcode) {

    case WCALL1: case WCALL1_pop1: {
      long arg = Op1;
      Adjust1;
      Push3((long)pc, extra_args, arg);
      pc += Imm16s;
      extra_args = 0;
      break;
    }
    case WCONST: case WCONST_pop1: {
      Adjust1;
      Push1(Imm24s);
      break;
    }
    case WBRANCHIF: case WBRANCHIF_pop1: {
      long arg = Op1;
      Adjust1;
      if (arg) pc += Imm16s;
      break;
    }
    case WCALL3: {
      unsigned int ext = *pc++;
      long arg1 = Extraop1(ext);
      long arg2 = Extraop2(ext);
      long arg3 = Extraop3(ext);
      Adjustbyte1;
      Push5((long)pc, extra_args, arg3, arg2, arg1);
      pc += Imm16s;
      extra_args = 2;
      break;
    }
    case WRETURN: {
      long res = Op1;
      Adjustbyte2;
      if (extra_args > 0) {
        printf("Over-application.\n");
        exit(2);
      } else {
        extra_args = sp[0];
        pc = (unsigned int *) sp[1];
        sp += 1;
        *sp = res;
      }
      break;
    }
    case WBRANCH: {
      Adjustbyte1;
      pc += Imm16s;
      break;
    }
    case WLTINT: {
      long arg1 = Op1, arg2 = Op2;
      Adjustbyte3;
      Push1(arg1 < arg2);
      break;
    }
    case WADDINT: {
      long arg1 = Op1, arg2 = Op2;
      Adjustbyte3;
      Push1(arg1 + arg2);
      break;
    }
    case WOFFSETINT: {
      long arg = Op1;
      Adjustbyte2;
      Push1(arg + Imm8s);
      break;
    }
    case WDUP: {
      long arg = Op1;
      Push1(arg);
      break;
    }
    case WGRAB: {
      int required = Byte1;
      if (extra_args >= required) {
        extra_args -= required;
      } else {
        printf("Partial application.\n");
        exit(2);
      }
      break;
    }
    case WSTOP: {
      long res = Op1;
      Adjustbyte2;
      return res;
      break;
    }
    }
  }
}

#define I(a,b,c,d) ((a) + ((b) << 8) + ((c) << 16) + ((d) << 24))

unsigned int wordcode_fib[] = {
/* 0 */ I(WCONST, 30, 0, 0),
/* 1 */ I(WCALL1_pop1, 0, 3-1-1, 0),
/* 2 */ I(WSTOP, 0, 1, 0),
/* 3 */ I(WCONST, 2, 0, 0),
/* 4 */ I(WLTINT, 1, 0, 1),
/* 5 */ I(WBRANCHIF_pop1, 0, 12-5-1, 0),
/* 6 */ I(WOFFSETINT, 0, 0, -1),
/* 7 */ I(WCALL1_pop1, 0, 3-7-1, 0),
/* 8 */ I(WOFFSETINT, 1, 0, -2),
/* 9 */ I(WCALL1_pop1, 0, 3-9-1, 0),
/* 10 */ I(WADDINT, 0, 1, 2),
/* 11 */ I(WRETURN, 0, 2, 0),
/* 12 */ I(WCONST, 1, 0, 0),
/* 13 */ I(WRETURN, 0, 2, 0)
};
unsigned int wordcode_tak[] = {
/* 0 */ I(WCONST, 6, 0, 0),
/* 1 */ I(WCONST, 12, 0, 0),
/* 2 */ I(WCONST, 18, 0, 0),
/* 3 */ I(WCALL3, 3, 6-3-2, 0),
/* 4 */ I(0, 1, 2, 0),
/* 5 */ I(WSTOP, 0, 1, 0),
/* 6 */ I(WGRAB, 2, 0, 0),              /* z y x */
/* 7 */ I(WLTINT, 1, 0, 0),             /* z y x (y<x) */
/* 8 */ I(WBRANCHIF_pop1, 0, 11-8-1, 0),
/* 9 */ I(WDUP, 2, 0, 0),
/* 10 */ I(WRETURN, 0, 4, 0),
/* 11 */ I(WOFFSETINT, 0, 0, -1),        /* z y x (x-1) */
/* 12 */ I(WCALL3, 1, 6-12-2, 0),
/* 13 */ I(0, 2, 3, 0),                  /* z y x tx */
/* 14 */ I(WOFFSETINT, 2, 0, -1),        /* z y x tx (y-1) */
/* 15 */ I(WCALL3, 1, 6-15-2, 0),
/* 16 */ I(0, 4, 2, 0),                  /* z y x tx ty */
/* 17 */ I(WOFFSETINT, 4, 0, -1),        /* z y x tx ty (z-1) */
/* 18 */ I(WCALL3, 1, 6-18-2, 0),
/* 19 */ I(0, 3, 4, 0),                  /* z y x tx ty tz */
/* 20 */ I(WCALL3, 3, 6-20-2, 0),
/* 21 */ I(2, 1, 0, 0),                  /* z y x res */
/* 22 */ I(WRETURN, 0, 4, 0),
};

int main(int argc, char ** argv)
{
  printf("fib(30) = %ld\n", wordcode_interp(wordcode_fib));
  printf("tak(18, 12, 6) = %ld\n", wordcode_interp(wordcode_tak));

  return 0;
}

