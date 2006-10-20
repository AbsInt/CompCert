/* For copyright information, see olden_v1.0/COPYRIGHT */

/* ========== PROCEDURE TYPES/NUMS ================== */


HANDLE *RandTree();

void SwapValue();
void SwapValLeft();
void SwapValRight();
int Bimerge();
int Bisort();
#define DD_EXIT 0


/* ================= PROC NAMES ==============*/

#ifdef EXTERN 
  extern char *procnames[]; 
#else 
  static char *procnames[] = 
  {
    "EXIT"
  };
#endif
