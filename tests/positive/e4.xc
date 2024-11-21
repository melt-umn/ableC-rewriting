#include <rewriting.xh>
#include <unification.xh>
#include <list.xh>
#include <string.xh>
#include <stdbool.h>

template<typename a>
struct item {
  a val;
  size_t count;
};

template<typename a>
item<a> ?entry(a val, arena_t ar) {
  allocate_using arena ar;
  return new var((item<a>){val, 1});
}

template<typename a>
strategy compress(arena_t ar) {
  allocate_using arena ar;
  return innermost(rule (list<item<a> ?> ?) {
      ?&[?&{v1, c1}, ?&{v2, c2} | t] @ when(v1 == v2) ->
        newlist[new var((item<a>){v1, c1 + c2}) | t];
    }, ar);
}

template<typename a>
strategy decompress(arena_t ar) {
  allocate_using arena ar;
  return innermost(rule (list<item<a> ?> ?) {
      ?&[?&{v, c} | t] @ when(c > 1) ->
        newlist[new var((item<a>){v, 1}),
                new var((item<a>){v, c - 1}) | t];
    }, ar);
}

int main() {
  with_arena ar {
    // Construct list
    list<item<int> ?> ?l1 = newlist[entry(1, ar), entry(1, ar), entry(2, ar), entry(3, ar), entry(3, ar), entry(3, ar)];
    printf("%s\n", show(l1).text);
    match (l1) {
      ?&[?&{1, 1}, ?&{1, 1}, ?&{2, 1}, ?&{3, 1}, ?&{3, 1}, ?&{3, 1}] -> {}
      _ -> { return 1; }
    }

    // Compress list
    list<item<int> ?> ?l2, ?l3;
    if (!rewrite(compress<int>(ar), l1, &l2)) {
      return 2;
    }
    printf("%s\n", show(l2).text);
    match (l2) {
      ?&[?&{1, 2}, ?&{2, 1}, ?&{3, 3}] -> {}
      _ -> { return 3; }
    }

    // Decompress list
    if (!rewrite(decompress<int>(ar), l1, &l3)) {
      return 4;
    }
    printf("%s\n", show(l3).text);
    match (l3) {
      ?&[?&{1, 1}, ?&{1, 1}, ?&{2, 1}, ?&{3, 1}, ?&{3, 1}, ?&{3, 1}] -> {}
      _ -> { return 5; }
    }

    // Reverse and decompress list
    if (!query A is l1, reverse(A, B) {
        list<item<int> ?> ?l4;
        if (!rewrite(decompress<int>(ar), B, &l4)) {
          return false;
        }
        printf("%s\n", show(l4).text);
        match (l4) {
          ?&[?&{3, 1}, ?&{3, 1}, ?&{3, 1}, ?&{2, 1}, ?&{1, 1}, ?&{1, 1}] -> {}
          _ -> { return false; }
        }
        return true;
      }) {
      return 6;
    }
  }

  return 0;
}
