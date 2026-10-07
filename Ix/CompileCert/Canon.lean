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
import Ix.CompileCert.Canon.Simulate
import Ix.CompileCert.Canon.Rename
import Ix.CompileCert.Canon.Collapse
import Ix.CompileCert.Canon.CliqueMap
import Ix.CompileCert.Canon.SccFuel
import Ix.CompileCert.Canon.Total
import Ix.CompileCert.Canon.Refs
import Ix.CompileCert.Canon.Terminate

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
  same classes; a component declared on its own is one component (Def 4.3);
* `Simulate`, `Rename`: the refinement under a change of presentation (a restriction and a map of
  the members); renamed members have the same classes in the same order (Def 4.3, renaming);
* `Collapse`: the quotient block (one member per class, references redirected) has the same classes
  restricted to the kept members, each a singleton (Def 4.3, collapse and equal members);
* `CliqueMap`: the clique name map sends each member to its class position;
* `SccFuel`, `Total`: Tarjan's fuel suffices, so `condensation`, `sccsOf` and `blockComponents` always
  return;
* `Refs`: `refsExpr`/`refsConst` return the names a constant references (sound always, complete on
  collision-free cached hashes), so the reference graph is the graph of occurrence;
* `Terminate`: the refinement returns when no comparison of distinct members fails (§3.5 (ii)).

## Theorem 4.2 (L1), clause by clause

* the components are the strongly connected components, with acyclic condensation:
  `condensation_scc`, `condensation_acyclic` (graph), `sccsOf_scc` (names), `blockComponents_scc`,
  `blockComponents_acyclic` (block); they always return (`condensation_isSome`, `blockComponents_ok`);
  the graph is the occurrence graph on collision-free input (`refsConst_sound`, `refsConst_complete`);
* the comparison is a total preorder at a fixed context: `compareFresh_total`, `constOrd_total`;
* the classes are the coarsest consistent partition: `sortClasses_coarsest`; the refinement terminates:
  `sortClasses_ok`;
* the class order does not depend on the seed: `sortClasses_setEq` (any seed), `sortClasses_perm`
  (the name-hash seed: the whole output);
* the name map is well defined: `cliqueNameMap_spec` (cliques); `blockNameMap` is open (it carries the
  `native_decide` auxiliaries of `Ix.Name.mkStr`);
* collapse decisions are theorems: `sortClasses_collapse_single`;
* canonicity under Def 4.3: member order (`canon_member_order_total`, `sortClasses_perm`,
  `sortClasses_setEq`), separate declaration (`blockComponents_separate_total`), renaming
  (`sortClasses_rename`), collapse and equal members (`sortClasses_collapse`);
* clique order: `sortClasses` over the specifications, so the statements above apply to it; the nested
  auxiliaries' discovery order is open (`expand` carries the same auxiliaries).
-/
