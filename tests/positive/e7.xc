#include <rewriting.xh>

datatype Foo { Foo (int (*)(float, int), int x); };

int fn(float x, int y) {
  return (int)(x * y);
}

int main() {
  datatype Foo f = Foo(fn, 23);
  with_arena ar {
    if (!rewrite(one(rule (int) { i -> i + 1; }, ar), f, NULL)) {
      return 1;
    }
  }
}
