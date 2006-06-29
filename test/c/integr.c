static double square(double x)
{
  return x * x;
}

static double integr(double (*f)(double), double low, double high, int n)
{
  double h, x, s;
  int i;

  h = (high - low) / n;
  s = 0;
  for (i = n, x = low; i > 0; i--, x += h) s += f(x);
  return s * h;
}

double test(int n)
{
  return integr(square, 0.0, 1.0, n);
}

    
  
