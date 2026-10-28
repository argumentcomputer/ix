/-
  Ix.Compile.Canon: the condensation of the reference graph, as a total pure
  function.

  The compiler uses it through a thin adapter that only converts data:
  `Ix.CondenseM.run` (the split of the whole reference graph) is
  `condensation`, presented in the compiler's traversal order so that block
  representatives and map iteration orders are kept. A block's members are
  compiled in Lean's order (`Ix.CompileM.sourceMembers`).
-/
module
public import Ix.Compile.Canon.Graph
