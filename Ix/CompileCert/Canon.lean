import Ix.CompileCert.Canon.Basic
import Ix.CompileCert.Canon.Level
import Ix.CompileCert.Canon.Ref
import Ix.CompileCert.Canon.Expr
import Ix.CompileCert.Canon.Const
import Ix.CompileCert.Canon.Rel
import Ix.CompileCert.Canon.Cache

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
  preorder.
-/
