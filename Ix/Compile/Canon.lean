/-
  Ix.Compile.Canon: Pass 1 of the Lean compiler (canonical form of inductive
  blocks and definition cliques) as total pure functions.

  The compiler calls only `Graph` so far: `Ix.CondenseM.run` (the split of
  the whole reference graph) is `condensation`. The rest restates the
  compiler's Step 1 as total functions:
  * `sortClasses` (`Classes.lean`) with the comparator of `Order.lean`: the
    classes and canonical order of a block (the compiler's
    `Ix.CompileM.sortConsts`);
  * `structuralAuxClasses` and `computePerm` (`Nested.lean`): the order of a
    block's nested auxiliaries and the permutation of Lean's source
    positions (`Ix.AuxGen.sortAuxByPartitionRefinement`, `computeAuxPerm`),
    on `Ix.AuxGen.ExpandedBlock.toCanon`.

  `Rules.compiler` is the compiler's rules with the two port fixes
  (`Order.lean`), which change no class and no order on Lean input;
  `Rules.today` leaves them off. `Rules.phaseA` computes the Phase A
  canonical form. `Tests/Ix/Compile/Canon.lean` (`canon-pass1`) checks the
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
