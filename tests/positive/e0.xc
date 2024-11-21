#include <rewriting.xh>
#include <string.xh>

typedef datatype Expr Expr;

datatype Expr {
  Add (Expr*, Expr*);
  Sub (Expr*, Expr*);
  Mul (Expr*, Expr*);
  Div (Expr*, Expr*);
  Const (int);
};

Expr *evalExpr(Expr *e, arena_t ar) {
  allocate_using arena ar;
  strategy eval = innermost(rule (Expr) {
      // Simplify
      Mul(_, &Const(0)) -> Const(0);
      Mul(&Const(0), _) -> Const(0);
      Mul(&e1, &Const(1)) -> e1;
      Mul(&Const(1), &e2) -> e2;
      Div(&Const(0), _) -> Const(0);
      Div(&e1, &Const(1)) -> e1;
      
      // Evaluate
      Add(&Const(a), &Const(b)) -> Const(a + b);
      Sub(&Const(a), &Const(b)) -> Const(a - b);
      Mul(&Const(a), &Const(b)) -> Const(a * b);
      Div(&Const(a), &Const(b@!0)) -> Const(a / b);
    }, ar);
  Expr *result;
  if (rewrite(eval, e, &result)) {
    return result;
  } else {
    return NULL;
  }
}

int main() {
  allocate_using heap;
  Expr *exprs[] = {new Add(new Const(1), new Const(2)),
                   new Add(new Const(3), new Mul(new Const(2), new Const(4))),
                   new Sub(new Const(7), new Div(new Const(6), new Const(7))),
                   new Mul(new Const(7), new Div(new Const(7), new Const(0))),
                   new Mul(new Const(1), new Div(new Const(7), new Const(0))),
                   new Mul(new Const(1), new Add(new Div(new Const(7), new Const(1)), new Const(4)))};
  Expr *expected[] = {
    new Const(3),
    new Const(11),
    new Const(7),
    new Mul(new Const(7), new Div(new Const(7), new Const(0))),
    new Div(new Const(7), new Const(0)),
    new Const(11)
  };
  for (int i = 0; i < sizeof(exprs) / sizeof(Expr*); i++) {
    with_arena ar {
      printf("%s: ", show(exprs[i]).text);
      Expr *res = evalExpr(exprs[i], ar);
      printf("%s\n", show(res).text);
      if (show(res) != show(expected[i])) {
        return i + 1;
      }
    }
  }
}
