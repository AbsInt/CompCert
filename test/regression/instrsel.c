/* Testing instruction selection and cast optimizations */

typedef unsigned char U8;
typedef signed char S8;
typedef unsigned short U16;
typedef signed short S16;

U8 b, bres[20];
S8 sb, sbres[20];
U16 s, sres[20];
S16 ss, ssres[20];
int i, res[50];
unsigned int ui;
float f, fres[20];
double d, dres[20];

#ifdef __COMPCERT__
#define TEST(x) __builtin_annot(#x); x
#else
#define TEST(x) x
#endif

void test(void)
{
  /* Telescoping casts */
  TEST(res[0] = (U8) (U8) i);
  TEST(res[1] = (S8) (U8) i);
  TEST(res[2] = (U8) (S8) i);
  TEST(res[3] = (S8) (S8) i);
  TEST(res[4] = (U16) (U16) i);
  TEST(res[5] = (S16) (U16) i);
  TEST(res[6] = (U16) (S16) i);
  TEST(res[7] = (S16) (S16) i);
  TEST(res[8] = (U16) (U8) i);
  TEST(res[9] = (U8) (U16) i);
  TEST(res[10] = (S16) (S8) i);
  TEST(res[11] = (S8) (S16) i);
  TEST(res[12] = (S16) (U8) i);
  TEST(res[13] = (U8) (S16) i);
  TEST(res[14] = (S8) (U16) i);
  TEST(res[15] = (U16) (S8) i);
  TEST(dres[0] = (float) (float) d);
  /* Redundant casts after a load */
  TEST(res[16] = (U8) b);
  TEST(res[17] = (U16) b);
  TEST(res[18] = (S16) b);
  TEST(res[19] = (S8) sb);
  TEST(res[20] = (S16) sb);
  TEST(res[21] = (U16) s);
  TEST(res[22] = (S16) ss);
  TEST(dres[1] = (float) f);
  /* Redundant casts before a store */
  TEST(bres[0] = b);
  TEST(bres[1] = sb);
  TEST(bres[2] = s);
  TEST(bres[3] = ss);
  TEST(bres[4] = i);
  TEST(bres[5] = (U8) i);
  TEST(bres[6] = (S8) i);
  TEST(bres[7] = (U16) i);
  TEST(bres[8] = (S16) i);
  TEST(bres[9] = i & 0xFF);
  TEST(sbres[0] = b);
  TEST(sbres[1] = sb);
  TEST(sbres[2] = s);
  TEST(sbres[3] = ss);
  TEST(sbres[4] = i);
  TEST(sbres[5] = (U8) i);
  TEST(sbres[6] = (S8) i);
  TEST(sbres[7] = (U16) i);
  TEST(sbres[8] = (S16) i);
  TEST(sres[0] = b);
  TEST(sres[1] = sb);
  TEST(sres[2] = s);
  TEST(sres[3] = ss);
  TEST(sres[4] = i);
  TEST(sres[5] = (U8) i);
  TEST(sres[6] = (S8) i);
  TEST(sres[7] = (U16) i);
  TEST(sres[8] = (S16) i);
  TEST(sres[9] = i & 0xFF);
  TEST(sres[10] = i & 0xFFFF);
  TEST(ssres[0] = b);
  TEST(ssres[1] = sb);
  TEST(ssres[2] = s);
  TEST(ssres[3] = ss);
  TEST(ssres[4] = i);
  TEST(ssres[5] = (U8) i);
  TEST(ssres[6] = (S8) i);
  TEST(ssres[7] = (U16) i);
  TEST(ssres[8] = (S16) i);
  TEST(fres[0] = f);
  TEST(fres[1] = d);
  TEST(fres[2] = (float) d);
  /* Bitwise operations */
  TEST(res[23] = (U8) (b & 1));
  TEST(res[24] = (U8) (i & 0xFF));
  TEST(res[25] = (U8) (b & 0xFFFF));
  TEST(res[26] = (U8) (b & b));
  TEST(res[27] = (U8) (b | b));
  TEST(res[28] = (U8) (b | 0x8));
  TEST(res[29] = (U8) (b & b));
  TEST(res[30] = (U8) (b ^ 0xFF));
  TEST(res[31] = (U8) (b ^ b));
  /* Combining unsigned shifts */
  TEST(res[32] = (ui << 8) >> 16);
  TEST(res[33] = (ui >> 16) & 0xFF);
  /* Combining signed shifts */
  TEST(res[34] = (U8) ((i >> 8) & 0xFF));
  TEST(res[35] = (U8) (i >> 24));
}

#include <stdio.h>

int main()
{
  int n;
  b = 12; sb = -4; s = 1234; ss = -257; i = 1234567; ui = 0xDEADBEEF;
  f = 2.5; d = -3.14159;
  test();
  printf("bres = ");
  for (n = 0; n < 20; n++) printf("%d ", bres[n]);
  printf("\n");
  printf("sbres = ");
  for (n = 0; n < 20; n++) printf("%d ", sbres[n]);
  printf("\n");
  printf("sres = ");
  for (n = 0; n < 20; n++) printf("%d ", sres[n]);
  printf("\n");
  printf("ssres = ");
  for (n = 0; n < 20; n++) printf("%d ", ssres[n]);
  printf("\n");
  printf("res = ");
  for (n = 0; n < 50; n++) printf("%d ", res[n]);
  printf("\n");
  printf("fres = ");
  for (n = 0; n < 20; n++) printf("%g ", fres[n]);
  printf("\n");
  return 0;
}
