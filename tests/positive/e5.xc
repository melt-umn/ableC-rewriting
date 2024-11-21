#include <rewriting.xh>
#include <substitution.xh>
#include <string.xh>

typedef datatype Type ?Type;

datatype Type {
  Fn(Type, Type);
  List(Type);
  Int();
  Bool();
};

size_t showTypeMaxLen(Type t);
size_t showType(char *buf, Type t);
show Type with showTypeMaxLen, showType;

size_t showTypeMaxLen(Type t) {
  match (t) {
    ?&Fn(param, res) -> {
      return showMaxLen(param) + showMaxLen(res) + 6;
    }
    ?&List(elem) -> {
      return showMaxLen(elem) + 2;
    }
    _ -> {
      return 5;
    }
  }
}

size_t showType(char *buf, Type t) {
  match (t) {
    freevar -> {
      return sprintf(buf, "a%hx", (union {Type t; short n;}){.t = t}.n);
    }
    ?&Fn(param@?&Fn(_, _), res) -> {
      return buildStr(buf, "(" + show(param) + ") -> " + show(res));
    }
    ?&Fn(param, res) -> {
      return buildStr(buf, show(param) + " -> " + show(res));
    }
    ?&List(elem) -> {
      return buildStr(buf, "[" + show(elem) + "]");
    }
    ?&Int() -> {
      return sprintf(buf, "int");
    }
    ?&Bool() -> {
      return sprintf(buf, "bool");
    }
  }
}

Type freshType(arena_t ar) {
  allocate_using arena ar;
  return new var<datatype Type>();
}

Type freshenType(Type t, arena_t ar) {
  return freshen<Type, datatype Type>(t, ar);
}

Type appType(Type f, Type a, arena_t ar) {
  Type res = freshType(ar);
  if (!unify(f, Fn(a, res))) {
    allocate_using stack;
    printf("Type error applying %s to %s\n", show(f).text, show(a).text);
    exit(1);
  }
  return res;
}

int main() {
  with_arena ar {
    Type foldr = term<Type> { Fn(Fn(A, Fn(B, B)), Fn(B, Fn(List(A), B))) };
    Type add = term<Type> { Fn(Int(), Fn(Int(), Int())) };
    Type map = term<Type> { Fn(Fn(A, B), Fn(List(A), List(B))) };
    Type null = term<Type> { Fn(List(A), Bool()) };
    
    printf("foldr :: %s\n", show(foldr).text);
    printf("add :: %s\n", show(add).text);
    printf("map :: %s\n", show(map).text);
    printf("null :: %s\n", show(null).text);

    Type sum = appType(appType(freshenType(foldr, ar), freshenType(add, ar), ar), term<Type>{ Int() }, ar);
    Type innerSum = appType(freshenType(map, ar), appType(freshenType(map, ar), freshenType(sum, ar), ar), ar);
    printf("sum :: %s\n", show(sum).text);
    printf("innerSum :: %s\n", show(innerSum).text);

    if (!unify(innerSum, term<Type> { Fn(List(List(List(Int()))), List(List(Int()))) })) {
      return 1;
    }
    if (unify(null, term<Type> { Fn(Bool(), A) })) {
      return 2; // Should fail
    }
  }
  return 0;
}
