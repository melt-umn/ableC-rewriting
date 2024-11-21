#include <rewriting.xh>
#include <stdio.h>
#include <stdbool.h>
#include <alloca.h>

template<typename a, int (*cmp)(a, a)>
datatype Set {
  Node(a item, Set<a, cmp> *left, Set<a, cmp> *right);
  Leaf();
};

template<typename a, int (*cmp)(a, a)>
bool setContains(Set<a, cmp> *set, a item) {
  match (set) {
    &Node(item1, left, right) -> {
      int diff = cmp(item, item1);
      if (diff < 0) {
        return setContains(left, item);
      } else if (diff > 0) {
        return setContains(right, item);
      } else {
        return true;
      }
    }
    &Leaf() -> { return false; }
  }
}

template<typename a, int (*cmp)(a, a)>
Set<a, cmp> *setEmpty(arena_t ar) {
  allocate_using arena ar;
  return new Leaf<a, cmp>();
}

template<typename a, int (*cmp)(a, a)>
Set<a, cmp> *setUnion(Set<a, cmp> *set1, Set<a, cmp> *set2, arena_t ar) {
  allocate_using arena ar;
  match (set1, set2) {
    &Node(item1, left1, right1), &Node(item2, left2, right2) -> {
      int diff = cmp(item1, item2);
      if (diff < 0) {
        return new Node(item1, setUnion(left1, set2, ar), right1);
      } else if (diff > 0) {
        return new Node(item1, left1, setUnion(right1, set2, ar));
      } else {
        // Both sets contain the same root item
        return new Node(item1, setUnion(left1, left2, ar), setUnion(right1, right2, ar));
      }
    }
    _, &Leaf() -> {
      return set1;
    }
    &Leaf(), _ -> {
      return set2;
    }
  }
}

template<typename a, int (*cmp)(a, a)>
Set<a, cmp> *setInsert(Set<a, cmp> *set, a item, arena_t ar) {
  allocate_using arena ar;
  match (set) {
    &Node(item1, left, right) -> {
      int diff = cmp(item1, item);
      if (diff < 0) {
        return setInsert(left, item, ar);
      } else if (diff > 0) {
        return setInsert(right, item, ar);
      } else {
        // item found in set
        return set;
      }
    }
    &Leaf() -> {
      // item not in set
      return new Node(item, set, set);
    }
  }
}

template<typename a, int (*cmp)(a, a)>
Set<a, cmp> *setRemove(Set<a, cmp> *set, a item, arena_t ar) {
  allocate_using arena ar;
  match (set) {
    &Node(item1, left, right) -> {
      int diff = cmp(item1, item);
      if (diff < 0) {
        return setRemove(left, item, ar);
      } else if (diff > 0) {
        return setRemove(right, item, ar);
      } else {
        // item found in set
        return setUnion(left, right, ar);
      }
    }
    &Leaf() -> {
      // item not in set
      return set;
    }
  }
}

typedef datatype Term Term;

datatype Term {
  Var(const char *n);
  Apply(Term *a, Term *b);
  Lambda(const char *n, Term *a);
}

size_t showTermMaxLen(Term *term);
size_t showTermToBuf(char *buf, Term *term);

show (Term*) with showTermMaxLen, showTermToBuf;

size_t showTermMaxLen(Term *term) {
  return match (term)
    (&Var(n) -> strlen(n);
     &Apply(a, b) -> 5 + showMaxLen(a) + showMaxLen(b);
     &Lambda(n, a) -> 3 + strlen(n) + showMaxLen(a););
}

size_t showTermToBuf(char *buf, Term *term) {
  match (term) {
    &Lambda(n, e) -> {
      size_t len = sprintf(buf, "\\%s", n);
      bool matched = true;
      while (matched) {
        match (e) {
          &Lambda(n, e1) -> {
            len += sprintf(buf + len, " %s", n);
            e = e1;
          }
          _ -> { matched = false; }
        }
      }
      len += sprintf(buf + len, ". ");
      len += showToBuf(buf + len, e);
      return len;
    }
    &Apply(e1, e2) -> {
      size_t len = match(e1)
        (&Lambda(_, _) -> buildStr(buf, "(" + show(e1) + ")");
         _ -> showToBuf(buf, e1););
      buf[len++] = ' ';
      len += match(e2)
        (&Lambda(_, _) -> buildStr(buf + len, "(" + show(e2) + ")");
         &Apply(_, _) -> buildStr(buf + len, "(" + show(e2) + ")");
         _-> showToBuf(buf + len, e2););
      return len;
    }
    &Var(n) -> { return sprintf(buf, "%s", n); }
  }
}

Set<const char *, strcmp> *getFreeVars(Term *term, arena_t ar) {
  allocate_using arena ar;
  return match (term)
    (&Var(n) -> setInsert(setEmpty<const char *, strcmp>(ar), n, ar);
     &Apply(a, b) -> setUnion(getFreeVars(a, ar), getFreeVars(b, ar), ar);
     &Lambda(n, a) -> setRemove(getFreeVars(a, ar), n, ar););
}

// term[n/a]
strategy substitute(const char *n, Term *a, arena_t ar) {
  allocate_using arena ar;
  Set<const char *, strcmp> *freeVars = getFreeVars(a, ar);
  
  strategy alphaRename = rule (Term) {
    Lambda(m, b) @ when(setContains(freeVars, m)) -> ({
        static unsigned count = 0;
        char *freshVar = arena_malloc(ar, 10);
        sprintf(freshVar, "_%u", count++);
        Term *freshTerm;
        rewrite(substitute(m, new Var(freshVar), ar), b, &freshTerm);
        Lambda(freshVar, freshTerm);
      });
  };
  
  strategy sub = rule (Term *) {
    &Var(m) @ when(!strcmp(n, m)) -> a;
    t @ &Lambda(m, _) @ when(!strcmp(n, m)) -> t;
  };
  
  return rec(lambda (strategy self) -> try(alphaRename, ar) <* (sub <+ try(all(self, ar), ar)), ar);
}

strategy betaReduce(arena_t ar) {
  allocate_using arena ar;
  return rule (Term *) {
    &Apply(&Lambda(n, a), b) -> ({
        Term *result;
        rewrite(substitute(n, b, ar), a, &result);
        result;
      });
  };
}

Term *normalize(Term *term, arena_t ar) {
  Term *result;
  rewrite(outermost(betaReduce(ar), ar), term, &result);
  return result;
}

int main() {
  allocate_using heap;
  Term *succ = new Lambda("n", new Lambda("f", new Lambda("x", new Apply(new Var("f"), new Apply(new Apply(new Var("n"), new Var("f")), new Var("x"))))));
  Term *plus = new Lambda("m", new Lambda("n", new Lambda("f", new Lambda("x", new Apply(new Apply(new Var("m"), new Var("f")), new Apply(new Apply(new Var("n"), new Var("f")), new Var("x")))))));

  Term *zero = new Lambda("f", new Lambda("x", new Var("x")));
  Term *one = new Apply(succ, zero);
  Term *two = new Apply(succ, one);
  Term *three = new Apply(succ, two);
  
  Term *terms[] = {
    new Apply(new Lambda("foo", new Var("foo")), new Lambda("a", new Var("a"))),
    new Apply(new Lambda("a", new Lambda("b", new Var("a"))), new Var("b")),
    new Lambda("a", new Lambda("b", new Apply(new Lambda("a", new Var("b")), new Var("a")))),
    plus,
    zero, one, two, three,
    new Apply(new Apply(plus, two), three)
  };
  const char *expected[] = {
    "\\a. a",
    "\\_0. b",
    "\\a b. b",
    "\\m n f x. m f (n f x)",
    "\\f x. x",
    "\\f x. f x",
    "\\f x. f (f x)",
    "\\f x. f (f (f x))",
    "\\f x. f (f (f (f (f x))))"
  };
  for (int i = 0; i < sizeof(terms) / sizeof(Term*); i++) {
    printf("%s: ", show(terms[i]).text);
    with_arena ar {
      Term *res = normalize(terms[i], ar);
      if (res != NULL) {
        printf("%s\n", show(res).text);
        if (show(res) != expected[i]) {
          return i + 1;
        }
      } else {
        return i + 1;
      }
    }
  }
}
