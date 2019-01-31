grammar determinism;

{- This Silver specification does not generate a useful working 
   compiler, it only serves as a grammar for running the modular
   determinism analysis.
 -}

import edu:umn:cs:melt:ableC:host;

copper_mda testConcreteSyntax(ablecParser) {
  edu:umn:cs:melt:exts:ableC:rewriting:concretesyntax;
}
