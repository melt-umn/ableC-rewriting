grammar edu:umn:cs:melt:exts:ableC:rewriting:concretesyntax;

imports silver:langutil;

imports edu:umn:cs:melt:ableC:concretesyntax;
imports edu:umn:cs:melt:ableC:abstractsyntax:host;

imports edu:umn:cs:melt:exts:ableC:rewriting:abstractsyntax;

exports edu:umn:cs:melt:exts:ableC:algebraicDataTypes:patternmatching:concretesyntax;

-- Operators
marking terminal ChoiceOp_t '<+' lexer classes {Csymbol};
marking terminal SeqeOp_t   '<*' lexer classes {Csymbol};

concrete productions top::AdditiveOp_c
| '<+'
  { top.ast = choiceExpr(top.leftExpr, top.rightExpr, location=top.exprLocation); }

concrete productions top::AddMulLeftOp_c
| '<*'
  { top.ast = seqExpr(top.leftExpr, top.rightExpr, location=top.exprLocation); }

-- Other special syntax
marking terminal Visit_t  'rule'    lexer classes {Cidentifier}, font=font_all;
marking terminal TypeId_t '_type_id' lexer classes {Cidentifier};

aspect parser attribute context
  action {
    context = addIdentsToScope([name("rule", location=builtin)], Visit_t, context);
    context = addIdentsToScope([name("_type_id", location=builtin)], TypeId_t, context);
  };

concrete productions top::PrimaryExpr_c
| 'rule' '(' ty::TypeName_c ')' '{' cs::ExprClauses_c '}'
  { top.ast = ruleExpr(ty.ast, cs.ast, location=top.location); }
| '_type_id' LParen_t ty::TypeName_c ')'
  { top.ast = typeIdExpr(ty.ast, location=top.location); }
