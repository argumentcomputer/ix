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
  * the nested auxiliaries are in the discovery order of the canonical
    expansion (`Nested.lean`; the compiler applies no sort), and
    `Ix.AuxGen.computeAuxPerm` is `computePerm` on
    `Ix.AuxGen.ExpandedBlock.toCanon`.
  The compiler's nested expansion (`expandNestedBlock`, locally nameless)
  and the evaporation probe (`positionClaimedBySpecScc`) are still its own;
  both deduplicate occurrences by `Nested.SeenKey`.

  The comparator (`Order.lean`) compares levels after `canonUniv`, external
  constants by compiled address and kinds by tag; `Rules` carry only the
  refinement's seed, `Rules.compiler` the name-hash seed.
  `Tests/Ix/Compile/Canon.lean` (`canon-pass1`) checks the compiler's path
  against these functions on the fixtures;
  `Tests/Ix/Compile/CanonClique.lean` (`canon-clique`) the clique order.

  Further entry points, not called by the compiler:
  * `canonBlock rules env all : Except String BlockCanon` per Lean block;
  * `expand`;
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
