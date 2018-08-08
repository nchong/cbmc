int nondet_int();
int __CPROVER_uninterpreted_f(int);

int main(void) {
  int i = nondet_int();
  int x = __CPROVER_uninterpreted_f(i);
  int y = __CPROVER_uninterpreted_f(i);
  __CPROVER_assert(x == y, "Equality");
  return 0;
}
