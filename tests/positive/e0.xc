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

allocate datatype Expr with GC_malloc;

Expr *evalExpr(Expr *e) {
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
    });
  Expr *result;
  if (rewrite(eval, e, &result)) {
    return result;
  } else {
    return NULL;
  }
}

int main() {
  Expr *exprs[] = {GC_malloc_Add(GC_malloc_Const(1), GC_malloc_Const(2)),
                   GC_malloc_Add(GC_malloc_Const(3), GC_malloc_Mul(GC_malloc_Const(2), GC_malloc_Const(4))),
                   GC_malloc_Sub(GC_malloc_Const(7), GC_malloc_Div(GC_malloc_Const(6), GC_malloc_Const(7))),
                   GC_malloc_Mul(GC_malloc_Const(7), GC_malloc_Div(GC_malloc_Const(7), GC_malloc_Const(0))),
                   GC_malloc_Mul(GC_malloc_Const(1), GC_malloc_Div(GC_malloc_Const(7), GC_malloc_Const(0))),
                   GC_malloc_Mul(GC_malloc_Const(1), GC_malloc_Add(GC_malloc_Div(GC_malloc_Const(7), GC_malloc_Const(1)), GC_malloc_Const(4)))};
  for (int i = 0; i < sizeof(exprs) / sizeof(Expr*); i++) {
    printf("%s: ", show(exprs[i]).text);
    Expr *res = evalExpr(exprs[i]);
    if (res != NULL)
      printf("%s", show(res).text);
    else 
      printf("Fail");
    printf("\n");
  }
}
