grammar edu:umn:cs:melt:exts:ableC:rewriting:abstractsyntax;

synthesized attribute shallowCopyProd::(Expr ::= Expr) occurs on Type, ExtType;

type TraversalImpl = (Expr ::= (Expr ::= Expr Expr) Expr Expr Expr Expr);
synthesized attribute traversalProd::TraversalImpl occurs on Type, ExtType;

fun idTraversal
Expr ::= comb::(Expr ::= Expr Expr) defaultVal::Expr strat::Expr term::Expr result::Expr =
  defaultVal;

fun combineTraversal
TraversalImpl ::= t1::TraversalImpl t2::TraversalImpl =
  \ comb::(Expr ::= Expr Expr) defaultVal::Expr strat::Expr term::Expr result::Expr ->
    comb(t1(comb, defaultVal, strat, term, result), t2(comb, defaultVal, strat, term, result));

aspect default production
top::Type ::=
{
  top.shallowCopyProd = id;
  top.traversalProd = idTraversal;
}

aspect production pointerType
top::Type ::= quals::Qualifiers sub::Type
{
  top.shallowCopyProd =
    if traversable(^sub)
    then
      \ e::Expr ->
        ableC_Expr {
          ({$directTypeExpr{^sub} *_result = (void*)0;
            if ($Expr{e}) {
              _result = allocate(sizeof($directTypeExpr{^sub}));
              *_result = *$Expr{e};
            }
            _result;})
        }
    else \ e::Expr -> e;
  top.traversalProd =
    if traversable(^sub)
    then
      \ comb::(Expr ::= Expr Expr) nil::Expr strat::Expr term::Expr result::Expr ->
        ableC_Expr {
          ({proto_typedef strategy;
            template<typename a> _Bool rewrite(const strategy s, const a term, a *const result);
            $Expr{term}?
              rewrite($Expr{strat}, *$Expr{term}, $Expr{result}? *$Expr{result} : (void*)0) :
              $Expr{nil};})
        }
    else idTraversal;
}

aspect production extType
top::Type ::= quals::Qualifiers sub::ExtType
{
  top.shallowCopyProd = sub.shallowCopyProd;
  top.traversalProd = sub.traversalProd;
}

aspect default production
top::ExtType ::=
{
  top.shallowCopyProd = id;
  top.traversalProd = idTraversal;
}

aspect production refIdExtType
top::ExtType ::= kwd::StructOrEnumOrUnion  tagName::Maybe<String>  refId::String
{
  top.traversalProd =
    case kwd of
    | structSEU() -> traverseStruct(tagName, refId, _, _, _, _, _)
    | _ -> idTraversal
    end;
}

aspect production adtExtType
top::ExtType ::= adtName::String adtDeclName::String refId::String
{
  top.traversalProd = traverseADT(adtName, refId, _, _, _, _, _);
}

aspect production varType
top::ExtType ::= sub::Type
{
  top.shallowCopyProd =
    if traversable(^sub)
    then
      \ e::Expr ->
        ableC_Expr {
          ({template<typename a> _Bool is_bound();
            template<typename a> _Bool value();
            is_bound($Expr{e})? new var<$directTypeExpr{^sub}>(value($Expr{e})) : $Expr{e};})
        }
    else \ e::Expr -> e;
  top.traversalProd =
    if traversable(^sub)
    then \ comb::(Expr ::= Expr Expr) nil::Expr strat::Expr term::Expr result::Expr ->
      ableC_Expr {
        ({proto_typedef strategy;
          template<typename a> _Bool rewrite(const strategy s, const a term, a *const result);
          template<typename a> struct _var_d;
          template<typename a> _Bool is_bound();
          template<typename a> a value();
          is_bound($Expr{term})?
            rewrite(
              $Expr{strat},
              value($Expr{term}),
              $Expr{result}?
                &(((_var_d<$directTypeExpr{^sub}> *)*$Expr{result})->contents._Bound.val) :
                (void*)0) :
            $Expr{nil};})
      }
    else idTraversal;
}

aspect production listType
top::ExtType ::= sub::Type
{
  top.traversalProd =
    if traversable(^sub)
    then \ comb::(Expr ::= Expr Expr) nil::Expr strat::Expr term::Expr result::Expr ->
      ableC_Expr {
        ({proto_typedef strategy;
          template<typename a> _Bool rewrite(const strategy s, const a term, a *const result);
          $Expr{term}.tag == _list_d__Nil?
            $Expr{nil} :
            $Expr{
              comb(
                ableC_Expr {
                  rewrite(
                    $Expr{strat},
                    $Expr{term}.contents._Cons.head,
                    $Expr{result}?
                      &($Expr{result}->contents._Cons.head) :
                      (void *)0)
                },
                ableC_Expr {
                  rewrite(
                    $Expr{strat},
                    $Expr{term}.contents._Cons.tail,
                    $Expr{result}?
                      &($Expr{result}->contents._Cons.tail) :
                      (void *)0)
                })};})
      }
    else idTraversal;
}

fun traversable Boolean ::= t::Type =
  case t of
  | functionType(_, _, _) -> false
  | _ -> !containsQualifier(constQualifier(), t)
  end;
