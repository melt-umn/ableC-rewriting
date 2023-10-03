grammar edu:umn:cs:melt:exts:ableC:rewriting:concretesyntax;

imports silver:langutil;

imports edu:umn:cs:melt:ableC:concretesyntax;
imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;

imports edu:umn:cs:melt:exts:ableC:rewriting:abstractsyntax;

exports edu:umn:cs:melt:exts:ableC:algebraicDataTypes:patternmatching:concretesyntax;

-- Operators
marking terminal ChoiceOp_t '<+' lexer classes {Operator};
marking terminal SeqeOp_t   '<*' lexer classes {Operator};

concrete productions top::AdditiveOp_c
| '<+'
  { top.ast = choiceExpr(top.leftExpr, top.rightExpr); }

concrete productions top::AddMulLeftOp_c
| '<*'
  { top.ast = seqExpr(top.leftExpr, top.rightExpr); }

-- Other special syntax
marking terminal Action_t 'action'   lexer classes {Keyword, Global};
marking terminal Rule_t   'rule'     lexer classes {Keyword, Global};
marking terminal TypeId_t '_type_id' lexer classes {Global};

concrete productions top::PrimaryExpr_c
| 'action' '(' p::ParameterDeclaration_c ')' '{' s::BlockItemList_c '}'
  {
    top.ast = actionExpr(p.ast, foldStmt(s.ast));
  }
| 'rule' '(' ty::TypeName_c ')' '{' cs::ExprClauses_c '}'
  { top.ast = ruleExpr(ty.ast, cs.ast); }
| '_type_id' LParen_t ty::TypeName_c ')'
  { top.ast = typeIdExpr(ty.ast); }
