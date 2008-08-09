struct vector {
  flt dx, dy, dz;
};

flt dotproduct(struct vector * a, struct vector * b);
void between(struct point * p, struct point * q,
             /*out*/ struct vector * v);
void opposite(struct vector * v,
              /*out*/ struct vector * w);
void point_along(struct point * p, struct vector * v,
                 flt ac,
                 /*out*/ struct point * q);
void product(struct vector * a, struct vector * b,
             /*out*/ struct vector * v);
flt vlength2(struct vector * a);
flt vlength(struct vector * a);

void vscale(struct vector * a, flt s,
            /*out*/ struct vector * v);
void vnormalize(struct vector * a, /*out*/ struct vector * v);
void vsub(struct vector * a, struct vector * b,
          /*out*/ struct vector * v);
  
