struct matrix {
  flt xx, xy, xz, xt;
  flt yx, yy, yz, yt;
  flt zx, zy, zz, zt;
};

void apply_to_point(struct matrix * m, struct point * p,
                    /*out*/ struct point * r);
void apply_to_vect(struct matrix * m, struct vector * v,
                   /*out*/ struct vector * r);
extern struct matrix * mid;
struct matrix * mtranslate(flt sx, flt sy, flt sz);
struct matrix * mscale(flt sx, flt sy, flt sz);
struct matrix * mrotatex(flt a);
struct matrix * mrotatey(flt a);
struct matrix * mrotatez(flt a);
struct matrix * mcompose(struct matrix * m, struct matrix * n);
