grammar edu:umn:cs:melt:exts:ableC:rewriting:abstractsyntax;

import edu:umn:cs:melt:ableC:abstractsyntax:overloadable;

inherited attribute componentRewriteCombineProd::(Expr ::= Expr Expr Location) occurs on Type, ExtType;
inherited attribute componentRewriteDefault::Expr occurs on Type, ExtType;
propagate componentRewriteCombineProd, componentRewriteDefault on Type, ExtType;

synthesized attribute shallowCopyProd::(Expr ::= Expr Location) occurs on Type, ExtType;
synthesized attribute componentRewriteProd::(Expr ::= Expr Expr Expr Location) occurs on Type, ExtType;

aspect default production
top::Type ::=
{
  top.shallowCopyProd = \ e::Expr Location -> e;
  top.componentRewriteProd = \ Expr Expr Expr Location -> top.componentRewriteDefault;
}

aspect production pointerType
top::Type ::= quals::Qualifiers sub::Type
{
  top.shallowCopyProd =
    if traversable(sub)
    then
      \ e::Expr Location ->
        ableC_Expr {
          ({$directTypeExpr{sub} *_result = (void*)0;
            if ($Expr{e}) {
              _result = GC_malloc(sizeof($directTypeExpr{sub}));
              *_result = *$Expr{e};
            }
            _result;})
        }
    else \ e::Expr Location -> e;
  top.componentRewriteProd =
    if traversable(sub)
    then
      \ strat::Expr term::Expr result::Expr Location ->
        ableC_Expr {
          ({proto_typedef strategy;
            template<typename a> _Bool rewrite(const strategy s, const a term, a *const result);
            $Expr{term}?
              rewrite($Expr{strat}, *$Expr{term}, $Expr{result}? *$Expr{result} : (void*)0) :
              $Expr{top.componentRewriteDefault};})
        }
    else \ Expr Expr Expr Location -> top.componentRewriteDefault;
}

aspect production extType
top::Type ::= quals::Qualifiers sub::ExtType
{
  top.shallowCopyProd = sub.shallowCopyProd;
  top.componentRewriteProd = sub.componentRewriteProd;
}

aspect default production
top::ExtType ::=
{
  top.shallowCopyProd = \ e::Expr Location -> e;
  top.componentRewriteProd = \ Expr Expr Expr Location -> top.componentRewriteDefault;
}

aspect production refIdExtType
top::ExtType ::= kwd::StructOrEnumOrUnion  _  _
{
  top.componentRewriteProd =
    case kwd of
    | structSEU() ->
      rewriteStruct(top.componentRewriteCombineProd, top.componentRewriteDefault, _, _, _, location=_)
    | _ -> \ Expr Expr Expr Location -> top.componentRewriteDefault
    end;
}

aspect production adtExtType
top::ExtType ::= adtName::String adtDeclName::String refId::String
{
  top.componentRewriteProd =
    rewriteADT(top.componentRewriteCombineProd, top.componentRewriteDefault, _, _, _, location=_);
}

aspect production varType
top::ExtType ::= sub::Type
{
  top.shallowCopyProd =
    if traversable(sub)
    then
      \ e::Expr Location ->
        ableC_Expr {
          ({template<typename a> _Bool is_bound();
            template<typename a> _Bool value();
            is_bound($Expr{e})?
              $Expr{
                boundVarExpr(
                  ableC_Expr { GC_malloc },
                  ableC_Expr { value($Expr{e}) },
                  location=builtin)} : $Expr{e};})
        }
    else \ e::Expr Location -> e;
  top.componentRewriteProd =
    if traversable(sub)
    then
      \ strat::Expr term::Expr result::Expr Location ->
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
                  &(((_var_d<$directTypeExpr{sub}> *)*$Expr{result})->contents._Bound.val) :
                  (void*)0) :
              $Expr{top.componentRewriteDefault};})
        }
    else \ Expr Expr Expr Location -> top.componentRewriteDefault;
}

aspect production listType
top::ExtType ::= sub::Type
{
  top.componentRewriteProd =
    if traversable(sub)
    then
      \ strat::Expr term::Expr result::Expr Location ->
        ableC_Expr {
          ({proto_typedef strategy;
            template<typename a> _Bool rewrite(const strategy s, const a term, a *const result);
            $Expr{term}.tag == _list_d__Nil?
              $Expr{top.componentRewriteDefault} :
              $Expr{
                top.componentRewriteCombineProd(
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
                  },
                  builtin)};})
        }
    else \ Expr Expr Expr Location -> top.componentRewriteDefault;
}

function traversable
Boolean ::= t::Type
{
  return
    case t of
    | functionType(_, _, _) -> false
    | _ -> !containsQualifier(constQualifier(location=builtin), t)
    end;
}
