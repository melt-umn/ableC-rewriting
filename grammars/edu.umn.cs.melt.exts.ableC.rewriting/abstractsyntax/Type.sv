grammar edu:umn:cs:melt:exts:ableC:rewriting:abstractsyntax;

import edu:umn:cs:melt:ableC:abstractsyntax:overloadable;

synthesized attribute shallowCopyProd::(Expr ::= Expr Location) occurs on Type, ExtType;
synthesized attribute componentRewriteProds::[(Expr ::= Expr Expr Expr Location)] occurs on Type, ExtType;

aspect default production
top::Type ::=
{
  top.shallowCopyProd = \ e::Expr Location -> e;
  top.componentRewriteProds = [];
}

aspect production pointerType
top::Type ::= quals::Qualifiers sub::Type
{
  top.shallowCopyProd =
    \ e::Expr Location ->
      ableC_Expr {
        ({$directTypeExpr{sub} *_result = 0;
          if ($Expr{e}) {
            _result = GC_malloc(sizeof($directTypeExpr{sub}));
            *_result = $Expr{e};
          }
          _result;})
      }; 
  top.componentRewriteProds =
    [\ strategy::Expr term::Expr result::Expr Location ->
       ableC_Expr {
         $Expr{term}? rewrite($Expr{strategy}, *$Expr{term}, *$Expr{result}) : (_Bool)0
       }];
}

aspect production extType
top::Type ::= quals::Qualifiers sub::ExtType
{
  top.shallowCopyProd = sub.shallowCopyProd;
  top.componentRewriteProds = sub.componentRewriteProds;
}

aspect default production
top::ExtType ::=
{
  top.shallowCopyProd = \ e::Expr Location -> e;
  top.componentRewriteProds = [];
}

