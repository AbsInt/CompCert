#include <stdlib.h>
#include <stdio.h>

/* Unstructured switch statements */

/* Duff's device */

void send(char * to, char * from, int count)
{
  register int n = (count + 7) / 8;
  switch (count % 8) {
    case 0: do { *to++ = *from++;
    case 7:      *to++ = *from++;
    case 6:      *to++ = *from++;
    case 5:      *to++ = *from++;
    case 4:      *to++ = *from++;
    case 3:      *to++ = *from++;
    case 2:      *to++ = *from++;
    case 1:      *to++ = *from++;
            } while (--n > 0);
  }
}

/* OpenBSD, usr.bin/locale */

void quotestring(char * value, int double_quoted)
{
  char c;
  while ((c = *value++) != '\0')
    switch (c) {
    case ' ': case '\t': case '\n': case '\'':
    case '(': case ')': case '<': case '>':
    case '&': case ';': case '|': case '~':
      if (!double_quoted)
    case '"': case '\\': case '$': case '`':
        putchar('\\');
    default:
      putchar(c);
      break;
    }
}

/* Simon Tatham's coroutines */

int nextchar(void)
{
  static unsigned char input[] = {
    'a', 'b', 0xFF, 3, 'c', 'd', 0xFF, 2, 'e', '\n', 0
  };
  static unsigned char * next = input;
  if (*next == 0)
    return EOF;
  else
    return *next++;
}

#define crBegin static int state=0; switch(state) { case 0:
#define crReturn(x) do { state=__LINE__; return x; \
                         case __LINE__:; } while (0)
#define crFinish }

int decompressor(void) {
  static int c, len;
  crBegin;
  while (1) {
    c = nextchar();
    if (c == EOF)
      break;
    if (c == 0xFF) {
      len = nextchar();
      c = nextchar();
      while (len--)
        crReturn(c);
    } else
      crReturn(c);
  }
  crReturn(EOF);
  crFinish;
}

/* Pigeon's device */

static enum { REVDFWDT, FORWARD, REVERSE } sorting_mode;

#define DAYOF(stamp)  ((stamp) / 10000)
#define TIMEOF(stamp) ((stamp) % 10000)

static inline int intcmp(unsigned int x, unsigned int y)
{
  if (x < y) return -1;
  if (x > y) return 1;
  return 0;
}

int lfdcmp(const void *a, const void *b) {
  unsigned int ta = *((unsigned int *) a);
  unsigned int tb = *((unsigned int *) b);
                  /* Isn't C a wonderful language? */
  switch (sorting_mode) {
    case REVDFWDT: if (DAYOF(ta) == DAYOF(tb)) {
    case FORWARD :     return intcmp(ta, tb);
                   } else {
    case REVERSE :     return intcmp(tb, ta);
                   }
  }
  return 0;
}

void testpigeon(int mode)
{
  unsigned int data[6] = {
    10001, 10004, 20022, 20002, 30008, 30007
  };
  sorting_mode = mode;
  qsort(data, 6, sizeof(unsigned int), lfdcmp);
  for (int i = 0; i < 6; i++) printf("%5u ", data[i]);
  printf("\n");
}

/* Delicate cases: unstructured switch containing
     early break
     loop w/ break
     regular switch
*/

void torture(int a, int b)
{
  switch(a) {
    L1: printf("L1 "); /*fallthrough*/
    L2: printf("L2 "); break;
    case 0:
      printf("0 "); /*fallthrough*/
    case 1:
      printf("1 "); break;
    case 2:
      printf("2 "); goto L1;
    case 3:
    L3:
      printf("3 "); goto L2;
    case 4:
      printf("4 "); goto L3;
    case 5:
      while (1) { printf("5"); b--; if (b <= 0) { printf(" "); break; }};
      break;
    case 6:
      switch (b) {
        case 1: printf("60"); break;
        case 2: printf("61"); break;
        default: printf("6X");
      }
      printf("Y ");
      break;
    default:
      printf("? ");
  }
}

int main()
{
  char dest[16];
  send(dest, "0123456789AB", 13);
  printf("%s\n", dest);

  quotestring("(ab$cd)", 0); putchar('\n');
  quotestring("(ab$cd)", 1); putchar('\n');

  int c;
  while ((c = decompressor()) != EOF) putchar(c);

  testpigeon(FORWARD);
  testpigeon(REVERSE);
  testpigeon(REVDFWDT);

  torture(0, 0); torture(1, 0); torture(2, 0); torture(3, 0); torture(4, 0);
  printf("\n");
  for (int b = 1; b <= 3; b++) torture(5, b);
  printf("\n");
  for (int b = 1; b <= 3; b++) torture(6, b);
  printf("\n");

  return 0;
}
