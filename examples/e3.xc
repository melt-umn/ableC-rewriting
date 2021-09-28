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

string showType(Type t) {
  match (t) {
    freevar -> {
      char buffer[sizeof(short) * 2 + 2];
      sprintf(buffer, "a%hx", (union {Type t; short n;}){.t = t}.n);
      return str(buffer);
    }
    ?&Fn(param@?&Fn(_, _), res) -> {
      return "(" + showType(param) + ") -> " + showType(res);
    }
    ?&Fn(param, res) -> {
      return showType(param) + " -> " + showType(res);
    }
    ?&List(elem) -> {
      return "[" + showType(elem) + "]";
    }
    ?&Int() -> {
      return str("int");
    }
    ?&Bool() -> {
      return str("bool");
    }
  }
}

show Type with showType;

Type freshType() {
  return freevar<datatype Type>(GC_malloc);
}

Type freshenType(Type t) {
  return freshen<Type, datatype Type>(t);
}

Type appType(Type f, Type a) {
  Type res = freshType();
  if (!unify(f, Fn(a, res))) {
    printf("Type error applying %s to %s\n", show(f).text, show(a).text);
    exit(1);
  }
  return res;
}

int main() {
  Type foldr = term<Type>(alloca) { Fn(Fn(A, Fn(B, B)), Fn(B, Fn(List(A), B))) };
  Type add = term<Type>(alloca) { Fn(Int(), Fn(Int(), Int())) };
  Type map = term<Type>(alloca) { Fn(Fn(A, B), Fn(List(A), List(B))) };
  Type null = term<Type>(alloca) { Fn(List(A), Bool()) };
  
  printf("foldr :: %s\n", show(foldr).text);
  printf("add :: %s\n", show(add).text);
  printf("map :: %s\n", show(map).text);
  printf("null :: %s\n", show(null).text);

  Type sum = appType(appType(freshenType(foldr), freshenType(add)), term<Type>(alloca){ Int() });
  Type innerSum = appType(freshenType(map), appType(freshenType(map), freshenType(sum)));
  printf("sum :: %s\n", show(sum).text);
  printf("innerSum :: %s\n", show(innerSum).text);

  // Type error
  //appType(freshenType(innerSum), term<Type>(alloca){ Int() });
}
