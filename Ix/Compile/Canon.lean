/-
  Ix.Compile.Canon: Pass 1 of the Lean compiler (canonical form of inductive
  blocks and definition cliques) as total pure functions.

  Not imported by the compiler: `Ix.CompileM` and the driver still use
  `sortConsts`, `CondenseM` and `Ix.AuxGen.Nested`. Under `Rules.today` these
  functions reproduce them (checked by `Tests/Ix/Compile/Canon.lean`); under
  `Rules.phaseA` they compute the Phase A canonical form
  (`plans/PLAN-A-compiler-design.md` §3.1). The census executable
  `canon-census` (`Benchmarks/Canon/Census.lean`) runs both on libraries.

  Proposed entry points for the compiler (A2):
  * `canonBlock rules env all : Except String BlockCanon` per Lean block;
  * `sortClasses rules addr? members` for any component (replaces
    `sortConsts`);
  * `sccsOf names refs` / `tarjan adj` (replaces `CondenseM`);
  * `expand`, `canonicalAuxOrder`, `computePerm` (replace
    `expandNestedBlock`, `sortAuxByPartitionRefinement`, `computeAuxPerm`);
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
