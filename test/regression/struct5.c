typedef struct HPointStruct
{
  double x;
  double y;
  double z;
  double w;
}HPoint;

typedef struct ObjPointStruct
{
  double x;
  double y;
  double z;
  double tx;
  double ty;
  double tz;
}ObjPoint;

HPoint PointToHPoint(ObjPoint P);

HPoint PointToHPoint(ObjPoint P)
{
  HPoint res;
  res.x = P.x;
  res.y = P.y;
  res.z = P.z;
  res.w = 1;
  return res;
}

double test1(HPoint (*f)(ObjPoint), double x)
{
  ObjPoint P;
  HPoint HP;
  P.x = x;
  HP = f(P);
  return HP.x;
}

double test2(double x)
{
  return test1(PointToHPoint, x);
}
