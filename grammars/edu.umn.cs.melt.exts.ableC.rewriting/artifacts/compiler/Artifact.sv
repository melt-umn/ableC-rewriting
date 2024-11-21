grammar edu:umn:cs:melt:exts:ableC:rewriting:artifacts:compiler;

{- This Silver specification does litte more than list the desired
   extensions, albeit in a somewhat stylized way.

   Files like this can easily be generated automatically from a simple
   list of the desired extensions.
 -}

import edu:umn:cs:melt:ableC:concretesyntax as cst;
import edu:umn:cs:melt:ableC:drivers:compile;


parser extendedParser :: cst:Root {
  edu:umn:cs:melt:ableC:concretesyntax;
  edu:umn:cs:melt:exts:ableC:rewriting;
  edu:umn:cs:melt:exts:ableC:string;
  edu:umn:cs:melt:exts:ableC:templateAlgebraicDataTypes;
  edu:umn:cs:melt:exts:ableC:templateConstructor;
  edu:umn:cs:melt:exts:ableC:unification;
  edu:umn:cs:melt:exts:ableC:prolog;
} 

fun main IO<Integer> ::= args::[String] = driver(args, extendedParser);
