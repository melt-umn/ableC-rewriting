grammar edu:umn:cs:melt:exts:ableC:rewriting:abstractsyntax;

abstract production choiceExpr
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp} <+ ${e2.pp}";
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    checkRewritingHeaderDef(top.location, top.env) ++
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
    checkRewritingHeaderDef(top.location, top.env) ++
    checkStrategyType(e1.typerep, "<*", e1.location) ++
    checkStrategyType(e2.typerep, "<*", e2.location);
  
  e2.env = addEnv(e1.defs, e1.env);
  
  local fwrd::Expr =
    ableC_Expr {
      GC_malloc_Sequence($Expr{decExpr(e1, location=builtin)}, $Expr{decExpr(e2, location=builtin)})
    };
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production actionExpr
top::Expr ::= p::ParameterDecl s::Stmt
{
  propagate substituted;
  top.pp = pp"action (${p.pp}) ${nestlines(2, s.pp)}";
  
  local localErrors::[Message] =
    p.errors ++ s.errors ++
    checkRewritingHeaderDef(top.location, top.env);
  
  local typeIdDefs::Pair<Integer [Def]> = getTypeIdDefs(p.typerep, addEnv(p.defs, p.env));
  
  p.env = openScopeEnv(top.env);
  p.position = 0;
  s.env = addEnv(globalDefsDef(typeIdDefs.snd) :: p.defs ++ p.functionDefs ++ s.functionDefs, capturedEnv(top.env));
  s.returnType = nothing();
  
  local fwrd::Expr =
    injectGlobalDeclsExpr(
      foldDecl([defsDecl(typeIdDefs.snd)]),
      ableC_Expr {
        proto_typedef type_id;
        GC_malloc_Action(
          $intLiteralExpr{typeIdDefs.fst},
          ({closure<($Parameters{foldParameterDecl([p])}) -> void> _fn =
              lambda (
                $Parameters{foldParameterDecl([
                  parameterDecl(
                    nilStorageClass(),
                    directTypeExpr(p.typerep),
                    baseTypeExpr(),
                    case p.paramname of
                    | just(n) -> justName(n)
                    | nothing() -> nothingName()
                    end,
                    nilAttribute())])}) -> void {
                $Stmt{decStmt(s)};
              };
            // Need to cast as a pointer due to C's restrictions on directly casting structs
            *(struct generic_closure*)&_fn;}))
      },
      location=builtin);
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production ruleExpr
top::Expr ::= ty::TypeName es::ExprClauses
{
  propagate substituted;
  top.pp = pp"rule (${ty.pp}) ${nestlines(2, es.pp)}";
  
  local localErrors::[Message] =
    ty.errors ++ es.errors ++
    (if !typeAssignableTo(ty.typerep, es.typerep)
     then [err(top.location, s"Rule has type ${showType(ty.typerep)} but rhs has type ${showType(es.typerep)}")]
     else []) ++
    checkRewritingHeaderDef(top.location, top.env);
  
  local typeIdDefs::Pair<Integer [Def]> = getTypeIdDefs(ty.typerep, addEnv(ty.defs, ty.env));
  
  es.env = addEnv(globalDefsDef(typeIdDefs.snd) :: ty.defs, ty.env);
  es.matchLocation = top.location;
  es.expectedTypes = [ty.typerep];
  es.transformIn = [ableC_Expr { _term }];
  es.endLabelName = "_end"; -- Only one in the function, so no unique id
  
  local fwrd::Expr =
    injectGlobalDeclsExpr(
      foldDecl([defsDecl(typeIdDefs.snd)]),
      ableC_Expr {
        proto_typedef type_id;
        GC_malloc_Rule(
          $intLiteralExpr{typeIdDefs.fst},
          ({closure<($BaseTypeExpr{typeModifierTypeExpr(ty.bty, ty.mty)},
                     $directTypeExpr{ty.typerep}*) -> _Bool> _fn =
              lambda ($directTypeExpr{ty.typerep} _term,
                      $directTypeExpr{ty.typerep} *_result) -> _Bool {
                $directTypeExpr{ty.typerep} _match_result;
                $Stmt{es.transform};
                return 0;
                _end:
                if (_result) {
                  *_result = _match_result;
                }
                return 1;
              };
            // Need to cast as a pointer due to C's restrictions on directly casting structs
            *(struct generic_closure*)&_fn;}))
      },
      location=builtin);
  
  forwards to mkErrorCheck(localErrors, fwrd);
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
-- For simplicity, it is assumed that all children here contain no definitions.
abstract production rewriteOneExpr
top::Expr ::= strategy::Expr term::Expr result::Expr
{
  propagate substituted;
  top.pp = pp"_rewrite_one(${strategy.pp}, ${term.pp}, ${result.pp})";
  
  local t::Type = term.typerep;
  t.componentRewriteCombineProd = orExpr(_, _, location=_);
  t.componentRewriteDefault = ableC_Expr { (_Bool)0 };
  
  forwards to
    ableC_Expr {
      ({if ($Expr{result}) {
          *$Expr{result} = $Expr{t.shallowCopyProd(term, top.location)};
        }
        $Expr{t.componentRewriteProd(strategy, term, result, top.location)};})
    };
}

abstract production rewriteAllExpr
top::Expr ::= strategy::Expr term::Expr result::Expr
{
  propagate substituted;
  top.pp = pp"_rewrite_all(${strategy.pp}, ${term.pp}, ${result.pp})";
  
  local t::Type = term.typerep;
  t.componentRewriteCombineProd = andExpr(_, _, location=_);
  t.componentRewriteDefault = ableC_Expr { (_Bool)1 };
  
  forwards to
    ableC_Expr {
      ({if ($Expr{result}) {
          *$Expr{result} = $Expr{t.shallowCopyProd(term, top.location)};
        }
        $Expr{t.componentRewriteProd(strategy, term, result, top.location)};})
    };
}

abstract production typeIdExpr
top::Expr ::= ty::TypeName
{
  propagate substituted;
  top.pp = pp"_type_id(${ty.pp})";
  
  local typeIdDefs::Pair<Integer [Def]> = getTypeIdDefs(ty.typerep, addEnv(ty.defs, ty.env));
  
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

-- Component rewrite overload productions
autocopy attribute componentRewriteStrategy::Expr;
autocopy attribute componentRewriteTerm::Expr;
autocopy attribute componentRewriteResult::Expr;
synthesized attribute componentRewriteTransform::Expr;
inherited attribute componentRewriteTransformIn::Expr;

abstract production rewriteADT
top::Expr ::= combineProd::(Expr ::= Expr Expr Location) defaultVal::Expr strategy::Expr term::Expr result::Expr
{
  propagate substituted;
  top.pp = pp"rewriteADT(${strategy.pp}, ${term.pp}, ${result.pp})";
  
  local adtName::Maybe<String> = term.typerep.adtName;
  
  local adtLookup::[RefIdItem] =
    case term.typerep.maybeRefId of
    | just(rid) -> lookupRefId(rid, top.env)
    | nothing() -> []
    end;
  
  local adt::Decorated ADTDecl =
    case adtLookup of
    | adtRefIdItem(adt) :: _ -> adt
    end;
  local newADT::ADTDecl = new(adt);
  newADT.isTopLevel = adt.isTopLevel;
  newADT.env = adt.env;
  newADT.returnType = adt.returnType;
  newADT.givenRefId = just(adt.refId);
  newADT.adtGivenName = adt.adtGivenName;
  newADT.componentRewriteCombineProd = combineProd;
  newADT.componentRewriteDefault = defaultVal;
  newADT.componentRewriteStrategy = strategy;
  newADT.componentRewriteTerm = term;
  newADT.componentRewriteResult = result;
  
  local localErrors::[Message] =
    case term.typerep, adtName, adtLookup of
    | errorType(), _, _ -> []
    -- Check that parameter type is an ADT of some sort
    | t, nothing(), _ -> [err(top.location, s"rewrite expected a datatype (got ${showType(t)}).")]
    -- Check that this ADT has a definition
    | _, just(id), [] -> [err(top.location, s"datatype ${id} does not have a definition.")]
    | _, just(id), _ -> []
    end ++
    checkRewritingHeaderDef(top.location, top.env);
  local fwrd::Expr = newADT.componentRewriteTransform;
  forwards to mkErrorCheck(localErrors, fwrd);
}

attribute componentRewriteCombineProd occurs on ADTDecl, ConstructorList, Constructor, Parameters, ParameterDecl;
attribute componentRewriteDefault occurs on ADTDecl, ConstructorList, Constructor, Parameters, ParameterDecl;
attribute componentRewriteStrategy occurs on ADTDecl, ConstructorList, Constructor, Parameters, ParameterDecl;
attribute componentRewriteTerm occurs on ADTDecl, ConstructorList, Constructor, Parameters, ParameterDecl;
attribute componentRewriteResult occurs on ADTDecl, ConstructorList, Constructor, Parameters, ParameterDecl;
attribute componentRewriteTransform occurs on ADTDecl, ConstructorList, Constructor, Parameters, ParameterDecl;
attribute componentRewriteTransformIn occurs on Constructor;

aspect production adtDecl
top::ADTDecl ::= attrs::Attributes n::Name cs::ConstructorList
{
  top.componentRewriteTransform = cs.componentRewriteTransform;
}

aspect production consConstructor
top::ConstructorList ::= c::Constructor cl::ConstructorList
{
  top.componentRewriteTransform = c.componentRewriteTransform;
  c.componentRewriteTransformIn = cl.componentRewriteTransform;
}

aspect production nilConstructor
top::ConstructorList ::=
{
  top.componentRewriteTransform = top.componentRewriteDefault;
}

aspect production constructor
top::Constructor ::= n::Name ps::Parameters
{
  top.componentRewriteTransform =
    ableC_Expr {
      $Expr{top.componentRewriteTerm}.tag == $name{enumItemName}?
        $Expr{ps.componentRewriteTransform} :
        $Expr{top.componentRewriteTransformIn}
    };
}

aspect production consParameters
top::Parameters ::= h::ParameterDecl t::Parameters
{
  top.componentRewriteTransform =
    top.componentRewriteCombineProd(
      h.componentRewriteTransform,
      t.componentRewriteTransform,
      h.sourceLocation);
}

aspect production nilParameters
top::Parameters ::=
{
  top.componentRewriteTransform = top.componentRewriteDefault;
}

aspect production parameterDecl
top::ParameterDecl ::= storage::StorageClasses  bty::BaseTypeExpr  mty::TypeModifierExpr  n::MaybeName  attrs::Attributes
{
  local fieldAccess::Expr =
    parenExpr(
      ableC_Expr {
        $Expr{top.componentRewriteResult}.contents.$name{top.constructorName}.$Name{fieldName}
      },
      location=top.sourceLocation);
  top.componentRewriteTransform =
    ableC_Expr {
      inst rewrite<$directTypeExpr{mty.typerep}>(
        $Expr{top.componentRewriteStrategy},
        $Expr{top.componentRewriteTerm}.contents.$name{top.constructorName}.$Name{fieldName},
        $Expr{top.componentRewriteResult}?
          &($Expr{top.componentRewriteResult}->contents.$name{top.constructorName}.$Name{fieldName}) :
          (void *)0)
    };
}

-- Check the given env for the given function name
function checkRewritingHeaderDef
[Message] ::= loc::Location env::Decorated Env
{
  return
    if !null(lookupTemplate("rewrite", env))
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
