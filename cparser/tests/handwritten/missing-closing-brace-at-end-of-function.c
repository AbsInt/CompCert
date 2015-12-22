int main (void)
{
  int x = 0;
  x++;
  /* missing closing brace, here */
  /* unfortunately, the error is detected only after the declaration of f */
  
void f (void)
{
}
