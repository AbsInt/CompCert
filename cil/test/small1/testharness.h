#ifndef printf
  /* sm: this works with gcc-2.95 */
  extern int printf(const char * format, ...);
# ifdef CCURED
   #pragma ccuredvararg("printf", printf(1))
# endif
#else
  /* but in gcc-3 headers it's a macro.. */
  #include <stdio.h>        /* printf */
#endif

extern void exit(int);

/* Always call E with a non-zero number */
#define E(n) { printf("Error %d\n", n); exit(n); }
#define SUCCESS { printf("Success\n"); exit(0); }

