grammar edu:umn:cs:melt:exts:ableC:rewriting:artifacts:silver_compiler;

{- This Silver specification defines the extended verison of Silver
   needed to build this extension.
 -}

import edu:umn:cs:melt:ableC:concretesyntax as cst;
import edu:umn:cs:melt:ableC:drivers:compile;
import silver:compiler:host;

parser svParse::Root {
  silver:compiler:host;
  edu:umn:cs:melt:ableC:silverconstruction;
  edu:umn:cs:melt:ableC:concretesyntax;
  edu:umn:cs:melt:exts:ableC:algebraicDataTypes;
  edu:umn:cs:melt:exts:ableC:templating;
  edu:umn:cs:melt:exts:ableC:allocation;
  edu:umn:cs:melt:exts:ableC:constructor;
  edu:umn:cs:melt:exts:ableC:templateConstructor;
  edu:umn:cs:melt:exts:ableC:templateAlgebraicDataTypes;
  edu:umn:cs:melt:exts:ableC:closure;
  edu:umn:cs:melt:exts:ableC:string;
  edu:umn:cs:melt:exts:ableC:vector;
  edu:umn:cs:melt:exts:ableC:unification;
}

fun main IO<Integer> ::= args::[String] = cmdLineRun(args, svParse); 