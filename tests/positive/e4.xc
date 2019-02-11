#include <rewriting.xh>
#include <unification.xh>
#include <list.xh>
#include <string.xh>
#include <stdbool.h>

template<a>
struct item {
  a val;
  size_t count;
};

template<a>
item<a> ?entry(a val) {
  return boundvar((item<a>){val, 1}, GC_malloc);
}

template<a>
strategy compress(void) {
  return innermost(rule (list<item<a> ?> ?) {
      ?&[?&{v1, c1}, ?&{v2, c2} | t] @ when(v1 == v2) ->
        cons(GC_malloc, boundvar((item<a>){v1, c1 + c2}, GC_malloc), t);
    });
}

int main() {
  list<item<int> ?> ?l1, ?l2;
  if (!rewrite(compress<int>(), newlist(GC_malloc)[entry(1), entry(1), entry(2), entry(3), entry(3)], &l1)) {
    return 1;
  }
  printf("%s\n", show(l1).text);
  if (!rewrite(compress<int>(), newlist(GC_malloc)[entry(3), entry(4), entry(5), entry(1), entry(1)], &l2)) {
    return 2;
  }
  printf("%s\n", show(l2).text);

  /*
  if (!query A is l1, B is l2, append(A, B, C) {
      list<item<int> ?> ?l3;
      if (!rewrite(compress<int>(), C, &l3)) {
        return false;
      }
      printf("%s\n", show(l3).text);
      
      
      
      return true;
    }) {
    return 3;
    }*/

  return 0;
}
