struct pair {
  int a;
  int b;
};

int nondet_int();
struct pair __CPROVER_uninterpreted_f(int);

int main(void) {
  int i = nondet_int();
  __CPROVER_assume(__CPROVER_uninterpreted_f(i).a == __CPROVER_uninterpreted_f(i).b);
  struct pair x = __CPROVER_uninterpreted_f(i);
  __CPROVER_assert(x.a == x.b, "Equality");
  return 0;
}
