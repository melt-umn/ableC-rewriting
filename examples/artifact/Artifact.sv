grammar artifact;

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
  edu:umn:cs:melt:exts:ableC:algebraicDataTypes;
  edu:umn:cs:melt:exts:ableC:templating;
  edu:umn:cs:melt:exts:ableC:templateAlgebraicDataTypes;
  edu:umn:cs:melt:exts:ableC:string;
  edu:umn:cs:melt:exts:ableC:unification;
  edu:umn:cs:melt:exts:ableC:prolog;
}

function main
IOVal<Integer> ::= args::[String] io_in::IOToken
{
  return driver(args, io_in, extendedParser);
}
