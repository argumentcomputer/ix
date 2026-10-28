/-
  Ix.Compile.Canon: the canonical order of a block's members (classes and
  their order) and the condensation, as total pure functions.

  The compiler uses this package through thin adapters that only convert
  data:
  * `Ix.CondenseM.run` (the split of the whole reference graph) is
    `condensation`, presented in the compiler's traversal order so that
    block representatives and map iteration orders are kept;
  * `Ix.CompileM.sortConsts` (classes and canonical order of a block) is
    `sortClasses Rules.compiler`, with external addresses from
    `Ix.CompileM.constAddrLookup`.

  The comparator (`Order.lean`) compares levels after `canonUniv`, external
  constants by compiled address and kinds by tag; `Rules` carry only the
  refinement's seed, `Rules.compiler` the name-hash seed.
-/
module
public import Ix.Compile.Canon.Expr
public import Ix.Compile.Canon.Graph
public import Ix.Compile.Canon.Order
public import Ix.Compile.Canon.Classes
