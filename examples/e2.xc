#include <rewriting.xh>
#include <string.xh>
#include <stdio.h>
#include <stdbool.h>
#include <stdarg.h>

template<a>
datatype List {
  Cons(a head, List<a> *tail);
  Nil();
};

template allocate datatype List with GC_malloc;

template<a>
List<a> *append(List<a> *l1, List<a> *l2) {
  return match (l1)
    (&Cons(h, t) -> GC_malloc_Cons(h, append(t, l2));
     &Nil() -> l2;);
}

template<a>
List<a> *buildList(size_t n, ...) {
  va_list args;
  va_start(args, n);
  a inputs[n];
  for (size_t i = 0; i < n; i++) {
    inputs[i] = va_arg(args, a);
  }
  va_end(args);
  List<a> *result = GC_malloc_Nil<a>();
  for (size_t i = 0; i < n; i++) {
    result = GC_malloc_Cons(inputs[n - (i + 1)], result);
  }
  return result;
}

typedef datatype Value Value;
typedef datatype Expr Expr;
typedef datatype Stmt Stmt;

datatype Value {
  Int(int);
  String(const char *);
};

datatype Expr {
  Const(Value);
  Var(const char *n);
  ToString(Expr *e);
  Minus(Expr *e);
  Add(Expr *e1, Expr *e2);
  Sub(Expr *e1, Expr *e2);
  Mul(Expr *e1, Expr *e2);
  Div(Expr *e1, Expr *e2);
  Equals(Expr *e1, Expr *e2);
  Not(Expr *e);
  And(Expr *e1, Expr *e2);
  Or(Expr *e1, Expr *e2);
};

datatype Stmt {
  Assign(const char *n, Expr e);
  Print(Expr e);
  If(Expr c, List<Stmt> *t, List<Stmt> *e);
  While(Expr c, List<Stmt> *b);
};

allocate datatype Expr with GC_malloc;
allocate datatype Stmt with GC_malloc;

bool stmtListHasBinding(const char *n, List<Stmt> *s);
bool stmtHasBinding(const char *n, Stmt s) {
  return match (s)
    (Assign(n1, _) @ when(!strcmp(n, n1)) -> true;
     If(_, t, e) -> stmtListHasBinding(n, t) || stmtListHasBinding(n, e);
     While(_, b) -> stmtListHasBinding(n, b);
     _ -> false;);
}

bool stmtListHasBinding(const char *n, List<Stmt> *s) {
  return match (s)
    (&Cons(h, t) -> stmtHasBinding(n, h) || stmtListHasBinding(n, t);
     &Nil() -> false;);
}

bool exprHasFreeVar(const char *n, Expr e) {
  return match (e)
    (Const(_) -> false;
     Var(n1) -> !strcmp(n, n1);
     ToString(&e1) -> exprHasFreeVar(n, e1);
     Minus(&e1) -> exprHasFreeVar(n, e1);
     Add(&e1, &e2) -> exprHasFreeVar(n, e1) || exprHasFreeVar(n, e2);
     Sub(&e1, &e2) -> exprHasFreeVar(n, e1) || exprHasFreeVar(n, e2);
     Mul(&e1, &e2) -> exprHasFreeVar(n, e1) || exprHasFreeVar(n, e2);
     Div(&e1, &e2) -> exprHasFreeVar(n, e1) || exprHasFreeVar(n, e2);
     Equals(&e1, &e2) -> exprHasFreeVar(n, e1) || exprHasFreeVar(n, e2);
     Not(&e1) -> exprHasFreeVar(n, e1);
     And(&e1, &e2) -> exprHasFreeVar(n, e1) || exprHasFreeVar(n, e2);
     Or(&e1, &e2) -> exprHasFreeVar(n, e1) || exprHasFreeVar(n, e2););
}

bool stmtListHasFreeVar(const char *n, List<Stmt> *s);
bool stmtHasFreeVar(const char *n, Stmt s) {
  return match (s)
    (Assign(n1, e) -> exprHasFreeVar(n, e);
     Print(e) -> exprHasFreeVar(n, e);
     If(c, t, e) -> exprHasFreeVar(n, c) || stmtListHasFreeVar(n, t) || stmtListHasFreeVar(n, e);
     While(c, b) -> exprHasFreeVar(n, c) || stmtListHasFreeVar(n, b););
}

bool stmtListHasFreeVar(const char *n, List<Stmt> *s) {
  return match (s)
    (&Cons(h, t) -> stmtHasFreeVar(n, h) || (!stmtHasBinding(n, h) && stmtListHasFreeVar(n, t));
     &Nil() -> false;);
}

Expr substituteExpr(Expr e, const char *n, Value v) {
  strategy sub = rule (Expr) {
    Var(n1) @ when(!strcmp(n, n1)) -> Const(v);
  };

  Expr result;
  rewrite(bottomUp(try(sub)), e, &result);
  return result;
}

List<Stmt> *substituteStmtList(List<Stmt> *s, const char *n, Value v);
Stmt substituteStmt(Stmt s, const char *n, Value v) {
  return match (s)
    (Assign(n1, e) -> Assign(n1, substituteExpr(e, n, v));
     Print(e) -> Print(substituteExpr(e, n, v));
     If(c, t, e) -> If(substituteExpr(c, n, v),
                       substituteStmtList(t, n, v),
                       substituteStmtList(e, n, v));
     w @ While(c, b) @ when(stmtListHasBinding(n, b)) -> If(substituteExpr(c, n, v),
                                                            append(substituteStmtList(b, n, v),
                                                                   GC_malloc_Cons(w, GC_malloc_Nil<Stmt>())),
                                                            GC_malloc_Nil<Stmt>());
     While(c, b) -> While(substituteExpr(c, n, v), substituteStmtList(b, n, v)););
}

List<Stmt> *substituteStmtList(List<Stmt> *s, const char *n, Value v) {
  return match (s)
    (&Cons(h, t) -> GC_malloc_Cons(substituteStmt(h, n, v),
                                   stmtHasBinding(n, h)? t : substituteStmtList(t, n, v));
     &Nil() -> s;);
}

void evaluate(List<Stmt> *prog) {
  strategy eval = outermost(rule (List<Stmt> *) {
        &Cons(Assign(n, e), s) @when(!stmtListHasFreeVar(n, s)) -> s;
        &Cons(a@Assign(n, Const(v)), s) -> substituteStmtList(s, n, v);
        &Cons(Print(Const(String(a1))), &Cons(Print(Const(String(a2))), s)) -> ({
            char *a3 = GC_malloc(strlen(a1) + strlen(a2) + 2);
            sprintf(a3, "%s\n%s", a1, a2);
            GC_malloc_Cons(Print(Const(String(a3))), s);
          });
        &Cons(a@Assign(_, _), &Cons(p@Print(Const(_)), s)) -> GC_malloc_Cons(p, GC_malloc_Cons(a, s));
        &Cons(If(Const(Int(0)), _, s1), s2) -> append(s1, s2);
        &Cons(If(Const(Int(_)), s1, _), s2) -> append(s1, s2);
      } <+ rule (Expr) {
        ToString(&Const(Int(a1))) -> ({
            char *a2 = GC_malloc(20);
            sprintf(a2, "%d", a1);
            Const(String(a2));
          });
        Minus(&Const(Int(a1))) -> Const(Int(-a1));
        Add(&Const(Int(a1)), &Const(Int(a2))) -> Const(Int(a1 + a2));
        Add(&Const(String(a1)), &Const(String(a2))) -> ({
            char *a3 = GC_malloc(strlen(a1) + strlen(a2) + 1);
            sprintf(a3, "%s%s", a1, a2);
            Const(String(a3));
          });
        Sub(&Const(Int(a1)), &Const(Int(a2))) -> Const(Int(a1 - a2));
        Mul(&Const(Int(a1)), &Const(Int(a2))) -> Const(Int(a1 * a2));
        Div(&Const(Int(a1)), &Const(Int(a2))) -> Const(Int(a1 / a2));
        Equals(&Const(Int(a1)), &Const(Int(a2))) -> Const(Int(a1 == a2));
        Not(&Const(Int(a1))) -> Const(Int(!a1));
        And(&Const(Int(a1)), &Const(Int(a2))) -> Const(Int(a1 && a2));
        Or(&Const(Int(a1)), &Const(Int(a2))) -> Const(Int(a1 || a2));
      });

  List<Stmt> *result;
  if (!rewrite(eval, prog, &result)) {
    printf("Fail\n");
  } else match (result) {
    &Cons(Print(Const(String(a))), &Nil()) -> {
      printf("Output:\n%s\n", a);
    }
    _ -> {
      printf("Result: %s\n", show(result).text);
    }
  }
}

int main() {
  List<Stmt> *progs[] = {
    buildList<Stmt>(2, Assign("a", Const(String("Hello, world!"))), Print(Var("a"))),
    buildList<Stmt>(2,
                    Assign("n", Const(Int(0))),
                    While(Not(GC_malloc_Equals(GC_malloc_Var("n"), GC_malloc_Const(Int(10)))),
                          buildList<Stmt>(2,
                                          Print(ToString(GC_malloc_Var("n"))),
                                          Assign("n", Add(GC_malloc_Var("n"), GC_malloc_Const(Int(1))))))),
    buildList<Stmt>(4,
                    Assign("a", Const(Int(0))),
                    Assign("b", Const(Int(1))),
                    Assign("n", Const(Int(10))),
                    While(Var("n"),
                          buildList<Stmt>(5,
                                          Print(ToString(GC_malloc_Var("a"))),
                                          Assign("c", Add(GC_malloc_Var("a"), GC_malloc_Var("b"))),
                                          Assign("a", Var("b")),
                                          Assign("b", Var("c")),
                                          Assign("n", Sub(GC_malloc_Var("n"), GC_malloc_Const(Int(1))))))),
    buildList<Stmt>(2, Print(Var("x")), Assign("y", Const(Int(2))))};
  for (int i = 0; i < sizeof(progs) / sizeof(Stmt*); i++) {
    printf("%s\n", show(progs[i]).text);
    evaluate(progs[i]);
  }
}
