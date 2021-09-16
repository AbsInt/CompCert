/* Dollar signs in identifiers */

int c$d = 42;

int a$b(int x$$) {
  return c$d + x$$;
}

int main(int argc, const char *argv[])
{
  return a$b(6);
}
