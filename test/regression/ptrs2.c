#include <stdlib.h>

typedef double Matrix[4][4];

Matrix * CopyMatrix(Matrix * Mat) {
  int i,j;
  Matrix * Res = NULL;
  if (Mat == 0) return Mat;
  Res = malloc(sizeof(Matrix));
  for(i=0;i<4;i++){
    for(j=0;j<4;j++){
      (*Res)[i][j] = (*Mat)[i][j];
    }
  }
  return Res;
}

Matrix * IdentMatrix(void)
{
  Matrix SI = { { 1.00, 0.00, 0.00, 0.00 }, 
		{ 0.00, 1.00, 0.00, 0.00 },
		{ 0.00, 0.00, 1.00, 0.00 },
		{ 0.00, 0.00, 0.00, 1.00 }};
  return CopyMatrix(&SI);
}

