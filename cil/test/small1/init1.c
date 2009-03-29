extern void exit(int);

struct {
  struct {
    int *f1;
    int *f2;
  } s1;
  struct {
    int *f3;
  } s2;
} memory[10] = { 1 };

int main() {
  if(memory[0].s1.f1 != (int*)1)
    exit(1);
  exit(0);
}
