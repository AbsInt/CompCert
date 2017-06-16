struct point {
  flt x, y, z;
};

static inline flt dist2(struct point * p1, struct point * p2)
{
  flt dx = p2->x - p1->x;
  flt dy = p2->y - p1->y;
  flt dz = p2->z - p1->z;
  return dx * dx + dy * dy + dz * dz;
}

