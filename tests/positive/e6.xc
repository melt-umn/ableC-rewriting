#include <rewriting.xh>

datatype Foo { Foo (const struct Bar *, int x); };

_Bool test(struct Bar *p) {
  datatype Foo f = Foo(p, 23);
  _Bool success;
  with_arena ar {
    success = rewrite(one(rule (int) { i -> i + 1; }, ar), f, NULL);
  }
  return success;
}

struct Bar { int y; };

int main() {
  struct Bar b = {42};
  if (!test(&b)) {
    return 1;
  }
}
