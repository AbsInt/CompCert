struct obj {
  int tag;
  union {
    struct { struct obj * car, * cdr; } cons;
    struct { char * name; struct obj * plist; } atom;
  } u;
};

struct obj some_obj;
