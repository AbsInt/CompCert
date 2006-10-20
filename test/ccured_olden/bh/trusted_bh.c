#include "defs.h"
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <sys/types.h>
#ifndef _MSVC
#include <sys/times.h>
#include <sys/param.h>
#endif


#ifndef NO_PERF_CHANGES
///*
// * ALLOCATE: memory allocation with error checking.
// */
//void *allocate(int nb)
//{
//    void *mem;
//
//    mem = (void *) calloc(nb, 1);		/* calloc zeros memory      */
//    if (mem == NULL) {
//        fprintf(stderr, "allocate: not enuf memory (%d bytes)\n", nb);
//        exit(1);
//    }
//    return (mem);
//}
#endif // NO_PERF_CHANGES



// Now some wrappers
typedef struct {
  void *_p;
  void *_b;
} fatp_void;

//fatp_void strcpy_fss(char *dest, char *src) {
//  fatp_void res;
//  strcpy(dest, src);
//  res._p = (void*)dest;
//  res._b = (void*)(dest + strlen(dest));
//  return res;
//}

#ifndef NO_PERF_CHANGES
  #ifdef node2body
  #undef node2body
  #endif
  bodyptr node2body(nodeptr x) {
    return (bodyptr)x;
  }
#endif

// And the wild version. I'm being lazy about types
fatp_void node2body_ww(fatp_void x) {
  return x;
}

typedef struct {
  nodeptr *_p;
  void *_b;
  void *_e;
} seqp_node;
bodyptr node2body_sq(seqp_node x) {
  if((void*)x._p < x._b || (void*)((char*)x._p + sizeof(body)) > x._e) {
    fprintf(stderr, "Bounds check failed in node2body_sq\n");
    exit(1);
  }
  return (bodyptr)x._p;
}

#ifndef NO_PERF_CHANGES
  #ifdef node2cell
  #undef node2cell
  #endif
  cellptr node2cell(nodeptr x) {
    return (cellptr)x;
  }
#endif

// And the wild version.. I'm being lazy about types
fatp_void node2cell_ww(fatp_void x) {
  return x;
}

cellptr node2cell_sq(seqp_node x) {
  //  if((void*)x._p < x._b || (void*)((char*)x._p + sizeof(cell)) > x._e) {
  //    fprintf(stderr, "Bounds check failed in node2cell_sq\n");
  //    exit(1);
  //  }
  return (cellptr)x._p;
}
