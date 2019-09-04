#include <rewriting.xh>
#include <string.xh>

struct bar {
  int x, y;
};

struct foo {
  int a;
  struct bar b;
  struct {
    int c;
  };
};

int main() {
  strategy inc = rule (int) { i -> i + 1; };

  struct foo f = {1, {2, 3}, {4}};
  struct foo result;
  if (!rewrite(bottomUp(try(inc)), f, &result)) {
    return 1;
  }

  printf("%s -> %s\n", show(f).text, show(result).text);

  if (result.a != 2) {
    return 2;
  }
  if (result.b.x != 3) {
    return 3;
  }
  if (result.b.y != 4) {
    return 4;
  }
  if (result.c != 5) {
    return 5;
  }
  
  return 0;
}
