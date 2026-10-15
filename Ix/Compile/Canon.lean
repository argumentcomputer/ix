/-
  Ix.Compile.Canon: Pass 1 of the Lean compiler (canonical form of inductive
  blocks and definition cliques) as total pure functions.

  The compiler's Step 1 uses this package through thin adapters that only
  convert data:
  * `Ix.CondenseM.run` (the split of the whole reference graph) is
    `condensation`, presented in the compiler's traversal order so that
    block representatives and map iteration orders are kept;
  * `Ix.CompileM.sortConsts` (classes and canonical order of every block,
    primary and auxiliary) is `sortClasses Rules.compiler`, with external
    addresses from `Ix.CompileM.constAddrLookup`;
  * `Ix.AuxGen.sortAuxByPartitionRefinement` takes its order from
    `structuralAuxClasses` and `Ix.AuxGen.computeAuxPerm` is `computePerm`,
    both on `Ix.AuxGen.ExpandedBlock.toCanon`.
  The compiler's nested expansion (`expandNestedBlock`, locally nameless)
  and the evaporation probe (`positionClaimedBySpecScc`) are still its own.

  `Rules.compiler` is the compiler's former rules with the two port fixes
  (`Order.lean`), which change no class and no order on Lean input.
  `Rules.phaseA` computes the Phase A canonical form; the compiler does not
  run it yet. `Tests/Ix/Compile/Canon.lean` (`canon-pass1`) checks the
  compiler's path against these functions on the fixtures;
  `Tests/Ix/Compile/CanonClique.lean` (`canon-clique`) the clique order.

  Further entry points, not called by the compiler:
  * `canonBlock rules env all : Except String BlockCanon` per Lean block;
  * `expand`, `canonicalAuxOrder`;
  * `cliqueClasses rules addr? clique`.
-/
module
public import Ix.Compile.Canon.Expr
public import Ix.Compile.Canon.Graph
public import Ix.Compile.Canon.Order
public import Ix.Compile.Canon.Classes
public import Ix.Compile.Canon.Nested
public import Ix.Compile.Canon.Block
public import Ix.Compile.Canon.Clique
