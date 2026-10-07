import Ix.CompileCert.Canon.Basic
import Ix.CompileCert.Canon.Level
import Ix.CompileCert.Canon.Ref
import Ix.CompileCert.Canon.Expr
import Ix.CompileCert.Canon.Const
import Ix.CompileCert.Canon.Rel
import Ix.CompileCert.Canon.Cache
import Ix.CompileCert.Canon.QSort
import Ix.CompileCert.Canon.SccMain
import Ix.CompileCert.Canon.SccNames
import Ix.CompileCert.Canon.Sort
import Ix.CompileCert.Canon.Group
import Ix.CompileCert.Canon.Ctx
import Ix.CompileCert.Canon.Refine
import Ix.CompileCert.Canon.Round
import Ix.CompileCert.Canon.Coarsest
import Ix.CompileCert.Canon.Seed
import Ix.CompileCert.Canon.SortOk
import Ix.CompileCert.Canon.SeedFree
import Ix.CompileCert.Canon.BlockComp

/-!
# M7 L1: Pass 1 proved

Theorem 4.2 of `plans/PLAN-B-certification.md` §2.3 over `Ix/Compile/Canon/**` (Pass 1 of the
Lean compiler: components, classes, canonical order, nested auxiliaries, cliques, name map),
stated against the code as it is. The modules:

* `Basic`: total preorders on the ok-domain of a comparison that can fail (`PreOn`), and the
  lexicographic, list and tag combinators;
* `Level`, `Ref`, `Expr`, `Const`: the comparator is a total preorder at a fixed context, at
  every level (design document §3.2);
* `Rel`: comparisons under two contexts: strong results do not depend on the class indices
  (§3.2 "Strength", §3.4 C3), and equality is kept by a coarser identification (§3.3 (b));
* `Cache`: the strong-result cache returns the comparator's own results (§3.4 C2), so the
  comparison the code runs (`compareFresh`, `compareConst`) is the pure one and a total
  preorder;
* `QSort`, `SccState`, `Scc`, `SccStep`, `SccMain`: `condensation` (Tarjan with an explicit
  call stack) returns the strongly connected components, each node once, in reverse
  topological order (§2.1, Def 2.1); `SccNames`: `sccsOf` over names;
* `Sort`, `Group`: the natural merge sort and the adjacent grouping the refinement runs;
* `Ctx`: the context a partition induces (`MutConst.ctx`);
* `Refine`, `Round`, `Coarsest`: the refinement is a pure function of its input and returns the
  coarsest consistent partition (Def 2.2, §3.3 (b));
* `Seed`: under the compiler's name-hash seed, the refinement does not depend on the order of
  its input (§3.3 (c));
* `SortOk`, `SeedFree`: for any seed, the classes and their order do not depend on the seed or
  the input order, only the order inside a class does (§3.3 (c));
* `BlockComp`: `blockComponents` returns the strongly connected components of the block's
  reference graph restricted to the members; a permuted block has the same components and the
  same classes; a component declared on its own is one component (Def 4.3).
-/
