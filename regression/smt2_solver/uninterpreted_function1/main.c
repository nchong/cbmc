int __CPROVER_uninterpreted_func(int);

int main() {
  int x = __CPROVER_uninterpreted_func(42);
  __CPROVER_assert(0 == 1, "Always fail");
}
