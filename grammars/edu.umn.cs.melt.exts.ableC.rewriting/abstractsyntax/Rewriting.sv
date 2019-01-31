grammar edu:umn:cs:melt:exts:ableC:rewriting:abstractsyntax;

abstract production choiceExpr
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp} <+ ${e2.pp}";
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    checkRewritingHeaderDef("GC_malloc_Choice", top.location, top.env) ++
    checkStrategyType(e1.typerep, "<+", e1.location) ++
    checkStrategyType(e2.typerep, "<+", e2.location);
  
  e2.env = addEnv(e1.defs, e1.env);
  
  local fwrd::Expr =
    ableC_Expr {
      GC_malloc_Choice($Expr{decExpr(e1, location=builtin)}, $Expr{decExpr(e2, location=builtin)})
    };
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production seqExpr
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp} <* ${e2.pp}";
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    checkRewritingHeaderDef("GC_malloc_Seq", top.location, top.env) ++
    checkStrategyType(e1.typerep, "<*", e1.location) ++
    checkStrategyType(e2.typerep, "<*", e2.location);
  
  e2.env = addEnv(e1.defs, e1.env);
  
  local fwrd::Expr =
    ableC_Expr {
      GC_malloc_Seq($Expr{decExpr(e1, location=builtin)}, $Expr{decExpr(e2, location=builtin)})
    };
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production ruleExpr
top::Expr ::= ty::TypeName es::ExprClauses
{
  propagate substituted;
  top.pp = pp"rule (${ty.pp}) ${nestlines(2, es.pp)}";
  
  local localErrors::[Message] = ty.errors ++ es.errors;
  
  local typeIdDefs::Pair<Integer [Def]> = getTypeIdDefs(ty.typerep, addEnv(ty.defs, ty.env));
  
  es.env = addEnv(ty.defs ++ typeIdDefs.snd, ty.env);
  es.matchLocation = top.location;
  es.expectedTypes = [ty.typerep];
  es.scrutineesIn = [ableC_Expr { _term }];
  es.transformIn = ableC_Stmt { _success = false; };
  
  local fwrd::Expr =
    ableC_Expr {
      GC_malloc_Rule(
        $intLiteralExpr{typeIdDefs.fst},
        lambda ($BaseTypeExpr{typeModifierTypeExpr(ty.bty, ty.mty)} _term,
                $directTypeExpr{ty.typerep} *_result) -> _Bool {
          _Bool _success = 1;
          $directTypeExpr{ty.typerep} _match_result;
          $Stmt{es.transform};
          if (_success) {
            *_result = _match_result;
          }
          return _success;
        })
    };
}

aspect function getInitialEnvDefs
[Def] ::=
{
  d <-
    [valueDef(
       "_rewrite_one",
       builtinFunctionValueItem(
         builtinType(nilQualifier(), voidType()),
         rewriteCombinatorHandler(_, _, _, rewriteOneExpr(_, _, _, location=_)))),
     valueDef(
       "_rewrite_all",
       builtinFunctionValueItem(
         builtinType(nilQualifier(), voidType()),
         rewriteCombinatorHandler(_, _, _, rewriteAllExpr(_, _, _, location=_))))];
}

function rewriteCombinatorHandler
Expr ::= f::Name a::Exprs loc::Location prod::(Expr ::= Expr Expr Expr Location)
{
  return
    case a of
    | consExpr(strategy, consExpr(term, consExpr(result, nilExpr()))) ->
      prod(strategy, term, result, loc)
    | _ -> errorExpr([err(loc, s"Wrong number of arguments to ${f.name}")], location=loc)
    end;
}

-- These are only used internally by the rewrite library, so no error checking.
-- For simplicity, it is assumed that all expressions referenced here contain no definitions.
abstract production rewriteOneExpr
top::Expr ::= strategy::Expr term::Expr result::Expr
{
  propagate substituted;
  top.pp = pp"_rewrite_one(${strategy.pp}, ${term.pp}, ${result.pp})";
  
  forwards to
    ableC_Expr {
      ({if ($Expr{result}) {
          *$Expr{result} = $Expr{term.typerep.shallowCopyProd(term, top.location)};
        }
        $Expr{
          foldr(
            orExpr(_, _, location=builtin),
            ableC_Expr {(_Bool)0},
            map(
              \ prod::(Expr ::= Expr Expr Expr Location) ->
                prod(strategy, term, result, top.location),
              term.typerep.componentRewriteProds))};})
    };
}

abstract production rewriteAllExpr
top::Expr ::= strategy::Expr term::Expr result::Expr
{
  propagate substituted;
  top.pp = pp"_rewrite_all(${strategy.pp}, ${term.pp}, ${result.pp})";
  
  forwards to
    ableC_Expr {
      ({if ($Expr{result}) {
          *$Expr{result} = $Expr{term.typerep.shallowCopyProd(term, top.location)};
        }
        $Expr{
          foldr(
            andExpr(_, _, location=builtin),
            ableC_Expr {(_Bool)1},
            map(
              \ prod::(Expr ::= Expr Expr Expr Location) ->
                prod(strategy, term, result, top.location),
              term.typerep.componentRewriteProds))};})
    };
}

abstract production typeIdExpr
top::Expr ::= ty::TypeName
{
  propagate substituted;
  top.pp = pp"_type_id(${ty.pp})";
  
  local typeIdDefs::Pair<Integer [Def]> = getTypeIdDefs(ty.typerep, top.env);
  
  forwards to
    ableC_Expr {
      ({$Decl{
          decls(
            foldDecl(
              injectGlobalDeclsDecl(foldDecl([defsDecl(typeIdDefs.snd)])) ::
              ty.decls))}
        $intLiteralExpr{typeIdDefs.fst};})
    };
}

-- Check the given env for the given function name
function checkRewritingHeaderDef
[Message] ::= n::String loc::Location env::Decorated Env
{
  return
    if !null(lookupValue(n, env))
    then []
    else [err(loc, "Missing include of rewriting.xh")];
}

-- Check that operand has rewriting type
function checkStrategyType
[Message] ::= t::Type op::String loc::Location
{
  local maybeRefId::Maybe<String> =
    case t.defaultFunctionArrayLvalueConversion of
    | pointerType(_, t1) -> t1.maybeRefId
    | _ -> nothing()
    end;
  return
    case maybeRefId of
    | just("edu:umn:cs:melt:exts:ableC:rewriting:strategy") -> []
    | _ -> [err(loc, s"Operand to ${op} expected strategy type (got ${showType(t)})")]
    end;
}
