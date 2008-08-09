struct point {
  flt x, y, z;
};

#if 0
static inline flt dist2(struct point * p1, struct point * p2)
{
  flt dx = p2->x - p1->x;
  flt dy = p2->y - p1->y;
  flt dz = p2->z - p1->z;
  return dx * dx + dy * dy + dz * dz;
}
#else
#define dist2(p1,p2) \
  (((p2)->x - (p1)->x) * ((p2)->x - (p1)->x) + \
   ((p2)->y - (p1)->y) * ((p2)->y - (p1)->y) + \
   ((p2)->z - (p1)->z) * ((p2)->z - (p1)->z))
#endif
