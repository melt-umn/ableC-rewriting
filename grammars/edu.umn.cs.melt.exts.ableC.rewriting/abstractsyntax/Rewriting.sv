grammar edu:umn:cs:melt:exts:ableC:rewriting:abstractsyntax;

abstract production choiceExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"${e1.pp} <+ ${e2.pp}";
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    checkRewritingHeaderDef(top.env) ++
    allocErrors(top.env) ++
    attachNote logicalLocationFromOrigin(e1) on
      checkStrategyType(e1.typerep, "<+")
    end ++
    attachNote logicalLocationFromOrigin(e2) on
      checkStrategyType(e2.typerep, "<+")
    end;

  forward fwrd =
    ableC_Expr {
      new Choice($Expr{@e1}, $Expr{@e2})
    };
  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}

abstract production seqExpr
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"${e1.pp} <* ${e2.pp}";
  
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    allocErrors(top.env) ++
    checkRewritingHeaderDef(top.env) ++
    attachNote logicalLocationFromOrigin(e1) on
      checkStrategyType(e1.typerep, "<*")
    end ++
    attachNote logicalLocationFromOrigin(e2) on
      checkStrategyType(e2.typerep, "<*")
    end;
  
  forward fwrd =
    ableC_Expr {
      new Sequence($Expr{@e1}, $Expr{@e2})
    };
  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}

abstract production actionExpr
top::Expr ::= p::ParameterDecl s::Stmt
{
  top.pp = pp"action (${p.pp}) ${nestlines(2, s.pp)}";
  
  local localErrors::[Message] =
    p.errors ++ s.errors ++
    allocErrors(top.env) ++
    checkRewritingHeaderDef(top.env);
  
  local typeIdDefs::Pair<Integer [Def]> = getTypeIdDefs(p.typerep, addEnv(p.defs, p.env));
  
  p.env = openScopeEnv(top.env);
  p.controlStmtContext = initialControlStmtContext;
  p.position = 0;

  forward fwrd =
    injectGlobalDeclsExpr(
      foldDecl([defsDecl(typeIdDefs.snd)]),
      ableC_Expr {
        proto_typedef type_id;
        new Action(
          $intLiteralExpr{typeIdDefs.fst},
          ({closure<($directTypeExpr{p.typerep}) -> void> _fn =
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
                $Stmt{@s};
              };
            // Need to cast as a pointer due to C's restrictions on directly casting structs
            *(struct generic_closure*)&_fn;}))
      });
  
  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}

abstract production ruleExpr
top::Expr ::= ty::TypeName es::ExprClauses
{
  top.pp = pp"rule (${ty.pp}) ${nestlines(2, es.pp)}";
  
  local localErrors::[Message] =
    ty.errors ++ es.errors ++
    (if !typeAssignableTo(ty.typerep, es.typerep)
     then [errFromOrigin(top, s"Rule has type ${show(80, ty.typerep)} but rhs has type ${show(80, es.typerep)}")]
     else []) ++
    allocErrors(top.env) ++
    checkRewritingHeaderDef(top.env);
  
  local typeIdDefs::Pair<Integer [Def]> = getTypeIdDefs(ty.typerep, addEnv(ty.defs, ty.env));

  es.initialEnv = es.transform.env;
  es.expectedTypes = [ty.typerep];
  es.transformIn = [ableC_Expr { _term }];
  es.endLabelName = "_end"; -- Only one in the function, so no unique id
  
  forward fwrd =
    injectGlobalDeclsExpr(
      consDecl(typePreDecls(@ty), consDecl(defsDecl(typeIdDefs.2), nilDecl())),
      ableC_Expr {
        proto_typedef type_id;
        new Rule(
          $intLiteralExpr{typeIdDefs.fst},
          ({closure<($directTypeExpr{ty.typerep} _term,
                    $directTypeExpr{ty.typerep} *_result) -> _Bool> _fn =
              lambda ($directTypeExpr{ty.typerep} _term,
                      $directTypeExpr{ty.typerep} *_result) -> _Bool {
                $directTypeExpr{ty.typerep} _match_result;
                $Stmt{@es.transform}
                return 0;
                _end:
                if (_result) {
                  *_result = _match_result;
                }
                return 1;
              };
            // Need to cast as a pointer due to C's restrictions on directly casting structs
            *(struct generic_closure*)&_fn;}))
        });
  
  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}

aspect function getInitialEnvDefs
[Def] ::=
{
  d <-
    [valueDef(
       "_rewrite_one",
       builtinFunctionValueItem(
         builtinType(nilQualifier(), voidType()),
         rewriteCombinatorHandler(rewriteOneExpr))),
     valueDef(
       "_rewrite_all",
       builtinFunctionValueItem(
         builtinType(nilQualifier(), voidType()),
         rewriteCombinatorHandler(rewriteAllExpr)))];
}

production rewriteCombinatorHandler implements ReferenceCall
top::Expr ::= f::Name a::Exprs prod::(Expr ::= Expr Expr Expr Type)
{
  top.pp = pp"${f.pp}(${ppImplode(pp", ", a.pps)})";
  forwards to bindDirectCallExpr(@f, @a,
    case a.bindRefExprs of
    | [strat, term, result] -> prod(strat, term, result, head(tail(a.typereps)))
    | _ -> errorExpr([errFromOrigin(a, s"${f.name} expected 3 arguments")])
    end);
}

-- These are only used internally by the rewrite library, so no error checking.
-- For simplicity, it is assumed that all children here contain no definitions.
abstract production rewriteOneExpr
top::Expr ::= strat::Expr term::Expr result::Expr t::Type
{
  top.pp = pp"_rewrite_one(${strat.pp}, ${term.pp}, ${result.pp})";
  
  nondecorated local traverseImpl::Expr =
    t.traversalProd(
      orExpr,  ableC_Expr { (_Bool)0 },
      ^strat, ^term, ^result);
  
  forwards to
    ableC_Expr {
      ({if ($Expr{^result}) {
          *$Expr{^result} = $Expr{t.shallowCopyProd(^term)};
        }
        $Expr{traverseImpl};})
    };
}

abstract production rewriteAllExpr
top::Expr ::= strat::Expr term::Expr result::Expr t::Type
{
  top.pp = pp"_rewrite_all(${strat.pp}, ${term.pp}, ${result.pp})";
  
  nondecorated local traverseImpl::Expr =
    t.traversalProd(
      andExpr,  ableC_Expr { (_Bool)1 },
      ^strat, ^term, ^result);
  
  forwards to
    ableC_Expr {
      ({if ($Expr{^result}) {
          *$Expr{^result} = $Expr{t.shallowCopyProd(^term)};
        }
        $Expr{traverseImpl};})
    };
}

abstract production typeIdExpr
top::Expr ::= ty::TypeName
{
  top.pp = pp"_type_id(${ty.pp})";
  
  local typeIdDefs::Pair<Integer [Def]> = getTypeIdDefs(ty.typerep, addEnv(ty.defs, ty.env));
  
  forwards to
    ableC_Expr {
      ({$Decl{typePreDecls(@ty)}
        $Decl{injectGlobalDeclsDecl(foldDecl([defsDecl(typeIdDefs.snd)]))}
        $intLiteralExpr{typeIdDefs.fst};})
    };
}

-- Component rewrite overload productions
abstract production traverseStruct
top::Expr ::= tagName::Maybe<String> refId::String combineProd::(Expr ::= Expr Expr) defaultVal::Expr strat::Expr term::Expr result::Expr
{
  top.pp = pp"traverseStruct(${strat.pp}, ${term.pp}, ${result.pp})";

  forwards to
    case lookupRefId(refId, top.env) of
    | structRefIdItem(s) :: _ ->
      s.traversalProd(combineProd, ^defaultVal, ^strat, ^term, ^result)
    -- Check that this struct has a definition
    | _ -> errorExpr([errFromOrigin(top, s"struct ${fromMaybe("<anon>", tagName)} does not have a definition.")])
    end;
}

attribute traversalProd occurs on StructDecl, StructItemList, StructItem, StructDeclarators, StructDeclarator;

aspect production structDecl
top::StructDecl ::= attrs::Attributes  name::MaybeName  dcls::StructItemList
{
  top.traversalProd = dcls.traversalProd;
}

aspect production consStructItem
top::StructItemList ::= h::StructItem  t::StructItemList
{
  top.traversalProd = combineTraversal(h.traversalProd, t.traversalProd);
}
aspect production nilStructItem
top::StructItemList ::=
{
  top.traversalProd = idTraversal;
}

aspect production structItem
top::StructItem ::= attrs::Attributes  ty::BaseTypeExpr  dcls::StructDeclarators
{
  top.traversalProd = dcls.traversalProd;
}
aspect production structItems
top::StructItem ::= dcls::StructItemList
{
  top.traversalProd = dcls.traversalProd;
}
aspect production anonStructStructItem
top::StructItem ::= d::StructDecl
{
  top.traversalProd = d.traversalProd;
}
aspect production anonUnionStructItem
top::StructItem ::= d::UnionDecl
{
  top.traversalProd = idTraversal;
}
aspect production warnStructItem
top::StructItem ::= msg::[Message]
{
  top.traversalProd = idTraversal;
}

aspect production consStructDeclarator
top::StructDeclarators ::= h::StructDeclarator  t::StructDeclarators
{
  top.traversalProd = combineTraversal(h.traversalProd, t.traversalProd);
}
aspect production nilStructDeclarator
top::StructDeclarators ::=
{
  top.traversalProd = idTraversal;
}

aspect production structField
top::StructDeclarator ::= name::Name  ty::TypeModifierExpr  attrs::Attributes
{
  top.traversalProd =
    if containsQualifier(constQualifier(), ty.typerep)
    then idTraversal
    else \ combineProd defaultVal strat term result ->
      ableC_Expr {
        ({proto_typedef strategy;
          template<typename a> _Bool rewrite(const strategy s, const a term, a *const result);
          rewrite($Expr{strat}, $Expr{term}.$Name{^name},
            $Expr{result}? &($Expr{result}->$Name{^name}) : (void *)0);})
      };
}
aspect production structBitfield
top::StructDeclarator ::= name::MaybeName  ty::TypeModifierExpr  e::Expr  attrs::Attributes
{
  -- Just ignore bitfields for now
  top.traversalProd = idTraversal;
}
aspect production warnStructField
top::StructDeclarator ::= msg::[Message]
{
  top.traversalProd = idTraversal;
}

abstract production traverseADT
top::Expr ::= adtName::String refId::String combineProd::(Expr ::= Expr Expr) defaultVal::Expr strat::Expr term::Expr result::Expr
{
  top.pp = pp"traverseADT(${strat.pp}, ${term.pp}, ${result.pp})";

  forwards to
    case lookupRefId(refId, top.env) of
    | adtRefIdItem(adt) :: _ ->
      adt.traversalProd(combineProd, ^defaultVal, ^strat, ^term, ^result)
    -- Check that this struct has a definition
    | _ -> errorExpr([errFromOrigin(top, s"datatype ${adtName} does not have a definition.")])
    end;
}

attribute traversalProd occurs on ADTDecl, ConstructorList, Constructor, Parameters, ParameterDecl;
inherited attribute traversalProdIn::TraversalImpl occurs on Constructor;

aspect production adtDecl
top::ADTDecl ::= attrs::Attributes n::Name cs::ConstructorList
{
  top.traversalProd = cs.traversalProd;
}

aspect production consConstructor
top::ConstructorList ::= c::Constructor cl::ConstructorList
{
  top.traversalProd = c.traversalProd;
  c.traversalProdIn = cl.traversalProd;
}
aspect production nilConstructor
top::ConstructorList ::=
{
  top.traversalProd = idTraversal;
}

aspect production constructor
top::Constructor ::= n::Name ps::Parameters
{
  top.traversalProd = \ combineProd defaultVal strat term result ->
    ableC_Expr {
      $Expr{term}.tag == $name{enumItemName}?
        $Expr{ps.traversalProd(combineProd, defaultVal, strat, term, result)} :
        $Expr{top.traversalProdIn(combineProd, defaultVal, strat, term, result)}
    };
}

aspect production consParameters
top::Parameters ::= h::ParameterDecl t::Parameters
{
  top.traversalProd = combineTraversal(h.traversalProd, t.traversalProd);
}

aspect production nilParameters
top::Parameters ::=
{
  top.traversalProd = idTraversal;
}

aspect production parameterDecl
top::ParameterDecl ::= storage::StorageClasses  bty::BaseTypeExpr  mty::TypeModifierExpr  n::MaybeName  attrs::Attributes
{
  top.traversalProd =
    if containsQualifier(constQualifier(), mty.typerep)
    then idTraversal
    else \ combineProd defaultVal strat term result ->
      ableC_Expr {
        ({proto_typedef strategy;
          template<typename a> _Bool rewrite(const strategy s, const a term, a *const result);
          rewrite($Expr{strat},
            $Expr{term}.contents.$name{top.constructorName}.$Name{fieldName},
            $Expr{result}?
              &($Expr{result}->contents.$name{top.constructorName}.$Name{fieldName}) :
              (void *)0);})
      };
}

-- Check the given env for the given function name
fun checkRewritingHeaderDef [Message] ::= env::Env =
  if !null(lookupTemplate("rewrite", env))
  then []
  else [errFromOrigin(ambientOrigin(), "Missing include of rewriting.xh")];

-- Check that operand has rewriting type
function checkStrategyType
[Message] ::= t::Type op::String
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
    | _, _ -> [errFromOrigin(ambientOrigin(), s"Operand to ${op} expected strategy type (got ${show(80, ^t)})")]
    end;
}
