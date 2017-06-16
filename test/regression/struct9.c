struct S1 {
  unsigned char  f0;
  short  f1;
};

struct S1 g_77 = {0x73,9};
struct S1 * volatile g_85 = &g_77;
struct S1 g_204 = {0xAD,0x9086};

void func_1(void)
{
   *g_85 = g_204;
}
