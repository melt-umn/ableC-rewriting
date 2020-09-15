grammar edu:umn:cs:melt:exts:ableC:rewriting:abstractsyntax;

abstract production choiceExpr
top::Expr ::= e1::Expr e2::Expr
{
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
  top.pp = pp"action (${p.pp}) ${nestlines(2, s.pp)}";
  
  local localErrors::[Message] =
    p.errors ++ s.errors ++
    checkRewritingHeaderDef(top.location, top.env);
  
  local typeIdDefs::Pair<Integer [Def]> = getTypeIdDefs(p.typerep, addEnv(p.defs, p.env));
  
  p.env = openScopeEnv(top.env);
  p.position = 0;
  
  local fnTypeExpr::BaseTypeExpr =
    ableC_BaseTypeExpr { closure<($directTypeExpr{p.typerep}) -> void> };
  fnTypeExpr.env = addEnv(p.defs, p.env);
  fnTypeExpr.returnType = nothing();
  fnTypeExpr.givenRefId = nothing();
  
  s.env = addEnv(globalDefsDef(typeIdDefs.snd) :: fnTypeExpr.defs ++ p.functionDefs ++ s.functionDefs, capturedEnv(top.env));
  s.returnType = nothing();
  
  local fwrd::Expr =
    injectGlobalDeclsExpr(
      foldDecl([defsDecl(typeIdDefs.snd)]),
      ableC_Expr {
        proto_typedef type_id;
        GC_malloc_Action(
          $intLiteralExpr{typeIdDefs.fst},
          ({$BaseTypeExpr{decTypeExpr(fnTypeExpr)} _fn =
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
  top.pp = pp"rule (${ty.pp}) ${nestlines(2, es.pp)}";
  
  local localErrors::[Message] =
    ty.errors ++ es.errors ++
    (if !typeAssignableTo(ty.typerep, es.typerep)
     then [err(top.location, s"Rule has type ${showType(ty.typerep)} but rhs has type ${showType(es.typerep)}")]
     else []) ++
    checkRewritingHeaderDef(top.location, top.env);
  
  local typeIdDefs::Pair<Integer [Def]> = getTypeIdDefs(ty.typerep, addEnv(ty.defs, ty.env));
  
  local fnTypeExpr::BaseTypeExpr =
    ableC_BaseTypeExpr {
      closure<($BaseTypeExpr{typeModifierTypeExpr(ty.bty, ty.mty)} _term,
               $directTypeExpr{ty.typerep} *_result) -> _Bool>
    };
  fnTypeExpr.env = openScopeEnv(top.env);
  fnTypeExpr.returnType = nothing();
  fnTypeExpr.givenRefId = nothing();
  
  es.env =
    addEnv(
      globalDefsDef(typeIdDefs.snd) ::
      fnTypeExpr.defs ++
      case fnTypeExpr of
      | closureTypeExpr(_, ps, _) -> ps.functionDefs
      end,
      fnTypeExpr.env);
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
          ({$BaseTypeExpr{decTypeExpr(fnTypeExpr)} _fn =
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
    | consExpr(strat, consExpr(term, consExpr(result, nilExpr()))) ->
      prod(strat, term, result, loc)
    | _ -> errorExpr([err(loc, s"Wrong number of arguments to ${f.name}")], location=loc)
    end;
}

-- These are only used internally by the rewrite library, so no error checking.
-- For simplicity, it is assumed that all children here contain no definitions.
abstract production rewriteOneExpr
top::Expr ::= strat::Expr term::Expr result::Expr
{
  top.pp = pp"_rewrite_one(${strat.pp}, ${term.pp}, ${result.pp})";
  
  local t::Type = term.typerep;
  t.componentRewriteCombineProd = orExpr(_, _, location=_);
  t.componentRewriteDefault = ableC_Expr { (_Bool)0 };
  
  forwards to
    ableC_Expr {
      ({if ($Expr{result}) {
          *$Expr{result} = $Expr{t.shallowCopyProd(term, top.location)};
        }
        $Expr{t.componentRewriteProd(strat, term, result, top.location)};})
    };
}

abstract production rewriteAllExpr
top::Expr ::= strat::Expr term::Expr result::Expr
{
  top.pp = pp"_rewrite_all(${strat.pp}, ${term.pp}, ${result.pp})";
  
  local t::Type = term.typerep;
  t.componentRewriteCombineProd = andExpr(_, _, location=_);
  t.componentRewriteDefault = ableC_Expr { (_Bool)1 };
  
  forwards to
    ableC_Expr {
      ({if ($Expr{result}) {
          *$Expr{result} = $Expr{t.shallowCopyProd(term, top.location)};
        }
        $Expr{t.componentRewriteProd(strat, term, result, top.location)};})
    };
}

abstract production typeIdExpr
top::Expr ::= ty::TypeName
{
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

abstract production rewriteStruct
top::Expr ::= combineProd::(Expr ::= Expr Expr Location) defaultVal::Expr strat::Expr term::Expr result::Expr
{
  top.pp = pp"rewriteADT(${strat.pp}, ${term.pp}, ${result.pp})";
  
  local structLookup::[RefIdItem] =
    case term.typerep.maybeRefId of
    | just(rid) -> lookupRefId(rid, top.env)
    | nothing() -> []
    end;
  
  local struct::Decorated StructDecl =
    case structLookup of
    | structRefIdItem(s) :: _ -> s
    end;
  local newStruct::StructDecl = new(struct);
  newStruct.isLast = struct.isLast;
  newStruct.env = struct.env;
  newStruct.returnType = struct.returnType;
  newStruct.givenRefId = just(struct.refId);
  newStruct.componentRewriteCombineProd = combineProd;
  newStruct.componentRewriteDefault = defaultVal;
  newStruct.componentRewriteStrategy = strat;
  newStruct.componentRewriteTerm = term;
  newStruct.componentRewriteResult = result;
  
  local localErrors::[Message] =
    case term.typerep, structLookup of
    | errorType(), _ -> []
    -- Check that this struct has a definition
    | extType(_, refIdExtType(_, id, _)), [] ->
      [err(top.location, s"struct ${id} does not have a definition.")]
    | _, _ -> []
    end ++
    checkRewritingHeaderDef(top.location, top.env);
  local fwrd::Expr = newStruct.componentRewriteTransform;
  forwards to mkErrorCheck(localErrors, fwrd);
}

attribute componentRewriteCombineProd occurs on StructDecl, StructItemList, StructItem, StructDeclarators, StructDeclarator;
attribute componentRewriteDefault occurs on StructDecl, StructItemList, StructItem, StructDeclarators, StructDeclarator;
attribute componentRewriteStrategy occurs on StructDecl, StructItemList, StructItem, StructDeclarators, StructDeclarator;
attribute componentRewriteTerm occurs on StructDecl, StructItemList, StructItem, StructDeclarators, StructDeclarator;
attribute componentRewriteResult occurs on StructDecl, StructItemList, StructItem, StructDeclarators, StructDeclarator;
attribute componentRewriteTransform occurs on StructDecl, StructItemList, StructItem, StructDeclarators, StructDeclarator;

aspect production structDecl
top::StructDecl ::= attrs::Attributes  name::MaybeName  dcls::StructItemList
{
  top.componentRewriteTransform = dcls.componentRewriteTransform;
}

aspect production consStructItem
top::StructItemList ::= h::StructItem  t::StructItemList
{
  top.componentRewriteTransform = 
    top.componentRewriteCombineProd(
      h.componentRewriteTransform, t.componentRewriteTransform, builtin);
}
aspect production nilStructItem
top::StructItemList ::=
{
  top.componentRewriteTransform = top.componentRewriteDefault;
}

aspect production structItem
top::StructItem ::= attrs::Attributes  ty::BaseTypeExpr  dcls::StructDeclarators
{
  top.componentRewriteTransform = dcls.componentRewriteTransform;
}
aspect production structItems
top::StructItem ::= dcls::StructItemList
{
  top.componentRewriteTransform = dcls.componentRewriteTransform;
}
aspect production anonStructStructItem
top::StructItem ::= d::StructDecl
{
  top.componentRewriteTransform = d.componentRewriteTransform;
}
aspect production anonUnionStructItem
top::StructItem ::= d::UnionDecl
{
  top.componentRewriteTransform = top.componentRewriteDefault;
}
aspect production warnStructItem
top::StructItem ::= msg::[Message]
{
  top.componentRewriteTransform = top.componentRewriteDefault;
}

aspect production consStructDeclarator
top::StructDeclarators ::= h::StructDeclarator  t::StructDeclarators
{
  top.componentRewriteTransform = 
    top.componentRewriteCombineProd(
      h.componentRewriteTransform, t.componentRewriteTransform, h.sourceLocation);
}
aspect production nilStructDeclarator
top::StructDeclarators ::=
{
  top.componentRewriteTransform = top.componentRewriteDefault;
}

aspect production structField
top::StructDeclarator ::= name::Name  ty::TypeModifierExpr  attrs::Attributes
{
  top.componentRewriteTransform =
    if containsQualifier(constQualifier(location=builtin), ty.typerep)
    then top.componentRewriteDefault
    else
      ableC_Expr {
        ({proto_typedef strategy;
          template<typename a> _Bool rewrite(const strategy s, const a term, a *const result);
          rewrite(
            $Expr{top.componentRewriteStrategy},
            $Expr{top.componentRewriteTerm}.$Name{name},
            $Expr{top.componentRewriteResult}?
              &($Expr{top.componentRewriteResult}->$Name{name}) :
              (void *)0);})
      };
}
aspect production structBitfield
top::StructDeclarator ::= name::MaybeName  ty::TypeModifierExpr  e::Expr  attrs::Attributes
{
  -- Just ignore bitfields for now
  top.componentRewriteTransform = top.componentRewriteDefault;
}
aspect production warnStructField
top::StructDeclarator ::= msg::[Message]
{
  top.componentRewriteTransform = top.componentRewriteDefault;
}

abstract production rewriteADT
top::Expr ::= combineProd::(Expr ::= Expr Expr Location) defaultVal::Expr strat::Expr term::Expr result::Expr
{
  top.pp = pp"rewriteADT(${strat.pp}, ${term.pp}, ${result.pp})";
  
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
  newADT.componentRewriteStrategy = strat;
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
      h.componentRewriteTransform, t.componentRewriteTransform, h.sourceLocation);
}

aspect production nilParameters
top::Parameters ::=
{
  top.componentRewriteTransform = top.componentRewriteDefault;
}

aspect production parameterDecl
top::ParameterDecl ::= storage::StorageClasses  bty::BaseTypeExpr  mty::TypeModifierExpr  n::MaybeName  attrs::Attributes
{
  top.componentRewriteTransform =
    if containsQualifier(constQualifier(location=builtin), mty.typerep)
    then top.componentRewriteDefault
    else
      ableC_Expr {
        ({proto_typedef strategy;
          template<typename a> _Bool rewrite(const strategy s, const a term, a *const result);
          rewrite(
            $Expr{top.componentRewriteStrategy},
            $Expr{top.componentRewriteTerm}.contents.$name{top.constructorName}.$Name{fieldName},
            $Expr{top.componentRewriteResult}?
              &($Expr{top.componentRewriteResult}->contents.$name{top.constructorName}.$Name{fieldName}) :
              (void *)0);})
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
    case t, maybeRefId of
    | errorType(), _ -> []
    | _, just("edu:umn:cs:melt:exts:ableC:rewriting:strategy") -> []
    | _, _ -> [err(loc, s"Operand to ${op} expected strategy type (got ${showType(t)})")]
    end;
}
