grammar edu:umn:cs:melt:exts:ableC:rewriting:abstractsyntax;

-- Track in the global environment the run-time type identifiers assigned statically to each type.
synthesized attribute typeIds::Scopes<Integer> occurs on Env;

aspect production emptyEnv_i
top::Env ::=
{
  top.typeIds = emptyScope();
}
aspect production addEnv_i
top::Env ::= d::Defs  e::Decorated Env
{
  top.typeIds = addGlobalScope(gd.typeIdContribs, addScope(d.typeIdContribs, e.typeIds));
}
aspect production openScopeEnv_i
top::Env ::= e::Decorated Env
{
  top.typeIds = openScope(e.typeIds);
}
aspect production globalEnv_i
top::Env ::= e::Decorated Env
{
  top.typeIds = globalScope(e.typeIds);
}
aspect production nonGlobalEnv_i
top::Env ::= e::Decorated Env
{
  top.typeIds = nonGlobalScope(e.typeIds);
}
aspect production functionEnv_i
top::Env ::= e::Decorated Env
{
  top.typeIds = functionScope(e.typeIds);
}

synthesized attribute typeIdContribs::Contribs<Integer> occurs on Defs, Def;

aspect production nilDefs
top::Defs ::=
{
  top.typeIdContribs = [];
}
aspect production consDefs
top::Defs ::= h::Def  t::Defs
{
  top.typeIdContribs = h.typeIdContribs ++ t.typeIdContribs;
}

aspect default production
top::Def ::=
{
  top.typeIdContribs = [];
}

abstract production typeIdDef
top::Def ::= s::String  t::Integer
{
  top.typeIdContribs = [(s, t)];
}

function getTypeIdDefs
Pair<Integer [Def]> ::= t::Type  e::Decorated Env
{
  local typeIds::[Integer] = lookupScope(t.mangledName, e.typeIds);
  local typeId::Integer =
    case typeIds of
    | [] -> genInt()
    -- TODO: Theoretically the id should only be in the environment once, but there is a bug
    -- somewhere with lifting
    --| [id] -> id
    --| ids -> error(s"Found multiple type id entires for ${showType(t)}: ${hackUnparse(ids)}")
    | id :: _ -> id
    end;
  
  return
    (typeId,
     if null(typeIds)
     then [typeIdDef(t.mangledName, typeId)]
     else []);
}
