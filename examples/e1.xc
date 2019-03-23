#include <rewriting.xh>
#include <stdio.h>
#include <stdbool.h>
#include <alloca.h>

template<typename a, int (*cmp)(a, a)>
datatype Set {
  Node(a item, Set<a, cmp> *left, Set<a, cmp> *right);
  Leaf();
};

template allocate datatype Set with GC_malloc;

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
Set<a, cmp> *setEmpty(void) {
  return GC_malloc_Leaf<a, cmp>();
}

template<typename a, int (*cmp)(a, a)>
Set<a, cmp> *setUnion(Set<a, cmp> *set1, Set<a, cmp> *set2) {
  match (set1, set2) {
    &Node(item1, left1, right1), &Node(item2, left2, right2) -> {
      int diff = cmp(item1, item2);
      if (diff < 0) {
        return GC_malloc_Node(item1, setUnion(left1, set2), right1);
      } else if (diff > 0) {
        return GC_malloc_Node(item1, left1, setUnion(right1, set2));
      } else {
        // Both sets contain the same root item
        return GC_malloc_Node(item1, setUnion(left1, left2), setUnion(right1, right2));
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
Set<a, cmp> *setInsert(Set<a, cmp> *set, a item) {
  match (set) {
    &Node(item1, left, right) -> {
      int diff = cmp(item1, item);
      if (diff < 0) {
        return setInsert(left, item);
      } else if (diff > 0) {
        return setInsert(right, item);
      } else {
        // item found in set
        return set;
      }
    }
    &Leaf() -> {
      // item not in set
      return GC_malloc_Node(item, set, set);
    }
  }
}

template<typename a, int (*cmp)(a, a)>
Set<a, cmp> *setRemove(Set<a, cmp> *set, a item) {
  match (set) {
    &Node(item1, left, right) -> {
      int diff = cmp(item1, item);
      if (diff < 0) {
        return setRemove(left, item);
      } else if (diff > 0) {
        return setRemove(right, item);
      } else {
        // item found in set
        return setUnion(left, right);
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

allocate datatype Term with GC_malloc;

Set<const char *, strcmp> *getFreeVars(Term *term) {
  return match (term)
    (&Var(n) -> setInsert(setEmpty<const char *, strcmp>(), n);
     &Apply(a, b) -> setUnion(getFreeVars(a), getFreeVars(b));
     &Lambda(n, a) -> setRemove(getFreeVars(a), n););
}

// term[n/a]
strategy substitute(const char *n, Term *a) {
  Set<const char *, strcmp> *freeVars = getFreeVars(a);
  
  strategy alphaRename = rule (Term) {
    Lambda(m, b) @ when(setContains(freeVars, m)) -> ({
        static unsigned count = 0;
        char *freshVar = GC_malloc(10);
        sprintf(freshVar, "_%u", count++);
        Term *freshTerm;
        rewrite(substitute(m, GC_malloc_Var(freshVar)), b, &freshTerm);
        Lambda(freshVar, freshTerm);
      });
  };
  
  strategy sub = rule (Term *) {
    &Var(m) @ when(!strcmp(n, m)) -> a;
    t @ &Lambda(m, _) @ when(!strcmp(n, m)) -> t;
  };
  
  return rec(lambda (strategy self) -> try(alphaRename) <* (sub <+ try(all(self))));
}

strategy betaReduce() {
  return rule (Term *) {
    &Apply(&Lambda(n, a), b) -> ({
        Term *result;
        rewrite(substitute(n, b), a, &result);
        result;
      });
  };
}

Term *normalize(Term *term) {
  Term *result;
  rewrite(outermost(betaReduce()), term, &result);
  return result;
}

void printTerm(Term *term) {
  match (term) {
    &Lambda(n, e) -> {
      char params[100];
      strcpy(params, n);
      bool matched = true;
      while (matched) {
        match(e) {
          &Lambda(n, e1) -> {
            strcat(params, " ");
            strcat(params, n);
            e = e1;
          }
          _ -> { matched = false; }
        }
      }
      printf("\\%s. ", params);
      printTerm(e);
    }
    &Apply(e1, e2) -> {
      match(e1) {
        &Lambda(_, _) -> {
          printf("(");
          printTerm(e1);
          printf(")");
        }
        _ -> { printTerm(e1); }
      }
      printf(" ");
      match(e2) {
        &Lambda(_, _) -> {
          printf("(");
          printTerm(e2);
          printf(")");
        }
        &Apply(_, _) -> {
          printf("(");
          printTerm(e2);
          printf(")");
        }
        _-> { printTerm(e2); }
      }
    }
    &Var(n) -> { printf("%s", n); }
  }
}

allocate datatype Term with alloca;

int main() {
  Term *succ = alloca_Lambda("n", alloca_Lambda("f", alloca_Lambda("x", alloca_Apply(alloca_Var("f"), alloca_Apply(alloca_Apply(alloca_Var("n"), alloca_Var("f")), alloca_Var("x"))))));
  Term *plus = alloca_Lambda("m", alloca_Lambda("n", alloca_Lambda("f", alloca_Lambda("x", alloca_Apply(alloca_Apply(alloca_Var("m"), alloca_Var("f")), alloca_Apply(alloca_Apply(alloca_Var("n"), alloca_Var("f")), alloca_Var("x")))))));

  Term *zero = alloca_Lambda("f", alloca_Lambda("x", alloca_Var("x")));
  Term *one = alloca_Apply(succ, zero);
  Term *two = alloca_Apply(succ, one);
  Term *three = alloca_Apply(succ, two);
  
  Term *terms[] = {alloca_Apply(alloca_Lambda("foo", alloca_Var("foo")), alloca_Lambda("a", alloca_Var("a"))),
                   alloca_Apply(alloca_Lambda("a", alloca_Lambda("b", alloca_Var("a"))), alloca_Var("b")),
                   alloca_Lambda("a", alloca_Lambda("b", alloca_Apply(alloca_Lambda("a", alloca_Var("b")), alloca_Var("a")))),
                   plus,
                   zero, one, two, three,
                   alloca_Apply(alloca_Apply(plus, two), three)};
  for (int i = 0; i < sizeof(terms) / sizeof(Term*); i++) {
    printTerm(terms[i]);
    printf(": ");
    Term *res = normalize(terms[i]);
    if (res != NULL)
      printTerm(res);
    else 
      printf("Fail");
    printf("\n");
  }
}
