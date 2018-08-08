struct pair {
  int a;
  int b;
};

int nondet_int();
struct pair __CPROVER_uninterpreted_f(int);

int main(void) {
  int i = nondet_int();
  struct pair x = __CPROVER_uninterpreted_f(i);
  struct pair y = __CPROVER_uninterpreted_f(i);
  __CPROVER_assert(x.a == y.a, "member a");
  __CPROVER_assert(x.b == y.b, "member b");
  return 0;
}
