#include <rewriting.xh>

datatype Foo { Foo (int (*)(float, int), int x); };

int fn(float x, int y) {
  return (int)(x * y);
}

int main() {
  datatype Foo f = Foo(fn, 23);
  if (!rewrite(one(rule (int) { i -> i + 1; }), f, NULL)) {
    return 1;
  }
}
