grammar edu:umn:cs:melt:exts:ableC:rewriting:abstractsyntax;

import edu:umn:cs:melt:ableC:abstractsyntax:overloadable;

autocopy attribute componentRewriteCombineProd::(Expr ::= Expr Expr Location) occurs on Type, ExtType;
autocopy attribute componentRewriteDefault::Expr occurs on Type, ExtType;

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
    if containsQualifier(constQualifier(location=builtin), sub)
    then \ e::Expr Location -> e
    else
      \ e::Expr Location ->
        ableC_Expr {
          ({$directTypeExpr{sub} *_result = (void*)0;
            if ($Expr{e}) {
              _result = GC_malloc(sizeof($directTypeExpr{sub}));
              *_result = *$Expr{e};
            }
            _result;})
        };
  top.componentRewriteProd =
    if containsQualifier(constQualifier(location=builtin), sub)
    then \ Expr Expr Expr Location -> top.componentRewriteDefault
    else
      \ strategy::Expr term::Expr result::Expr Location ->
        ableC_Expr {
          ({proto_typedef strategy;
            template<a> _Bool rewrite(const strategy s, const a term, a *const result);
            $Expr{term}?
              rewrite($Expr{strategy}, *$Expr{term}, $Expr{result}? *$Expr{result} : (void*)0) :
              $Expr{top.componentRewriteDefault};})
        };
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

aspect production adtExtType
top::ExtType ::= adtName::String adtDeclName::String refId::String
{
  top.componentRewriteProd =
    rewriteADT(top.componentRewriteCombineProd, top.componentRewriteDefault, _, _, _, location=_);
}
