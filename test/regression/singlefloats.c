/* This caused an internal compiler error in CompCert 2.2.
   (RTLtyping failure, because y is used both as a float32 and a float64). */

typedef union
{
  float value;
  unsigned int word;
} shape;

float
expf(float x)
{
        float y,hi;

        y = 1/hi;

        shape A;
        A.value = y;

        shape B;
        B.word = A.word;
        y = B.value;

        return y;
}

/* Another internal compiler error in CompCert 2.2.  */

void store(volatile float * p, double x)
{
  *p = x + 1.0;
}
