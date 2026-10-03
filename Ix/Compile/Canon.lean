/-
  Ix.Compile.Canon: Pass 1 of the Lean compiler (canonical form of inductive
  blocks and definition cliques) as total pure functions.

  **Wired into the compiler under `Rules.compiler`** (today's rules with the
  two Lean-port comparator fixes, which change no byte; A2's byte-neutral
  half). The compiler's Step 1 calls into this package through thin
  adapters that only convert data:
  * `Ix.CondenseM.run` (the split of the whole reference graph) is
    `condensation`, presented in today's traversal order so that block
    representatives and map iteration orders are unchanged;
  * `Ix.CompileM.sortConsts` (classes and canonical order of every block,
    primary and auxiliary) is `sortClasses Rules.compiler`, with external
    addresses from `Ix.CompileM.constAddrLookup`;
  * `Ix.AuxGen.sortAuxByPartitionRefinement` takes its order from
    `structuralAuxClasses` and `Ix.AuxGen.computeAuxPerm` is `computePerm`,
    both on `Ix.AuxGen.ExpandedBlock.toCanon`.
  The compiler's nested expansion (`expandNestedBlock`, locally nameless)
  and the evaporation probe (`positionClaimedBySpecScc`) are still its own.

  Under `Rules.phaseA` the functions compute the Phase A canonical form
  (`plans/PLAN-A-compiler-design.md` §3.1). The census executable
  `canon-census` (`Benchmarks/Canon/Census.lean`) runs both on libraries;
  `Tests/Ix/Compile/Canon.lean` (`canon-pass1`) checks the wired path.

  Further entry points (A2 proper and later):
  * `canonBlock rules env all : Except String BlockCanon` per Lean block;
  * `expand`, `canonicalAuxOrder` (discovery order under `Rules.phaseA`);
  * `cliqueClasses rules addr? clique`;
  * `blockNameMap`, `cliqueNameMap`.
-/
module
public import Ix.Compile.Canon.Expr
public import Ix.Compile.Canon.Graph
public import Ix.Compile.Canon.Order
public import Ix.Compile.Canon.Classes
public import Ix.Compile.Canon.Nested
public import Ix.Compile.Canon.Block
public import Ix.Compile.Canon.Clique
public import Ix.Compile.Canon.NameMap
