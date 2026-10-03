/-
  Ix.Compile.Clique: the transport `Φ_σ` of definition cliques (design
  document `docs/compiler-passes.md` §5; Phase A plan §3.3 and package A5) as
  total pure functions over `Ix.Expr`.

  * `Basic`: term representation (and how Lean names are carried), the monad,
    levels as `MetaM` builds them, comparisons up to binder names;
  * `Packing`: the right-nested `PSum`/`PProd` packings (types, injections,
    case trees, tuples, projection paths), decoded and rebuilt with Lean's own
    construction (step (A));
  * `Telescope`: the fixed-parameter telescope in the first member's order
    (O13b);
  * `WF`: well-founded recursion (§5.1);
  * `Structural`: structural recursion (§5.3);
  * `PartialFixpoint`: `partial_fixpoint` (§5.2), with the regeneration (G);
  * `Transport`: the interface, the fallbacks and the causes it records.

  Not imported by the compiler (A5 proper wires it in). No `MetaM`, no
  kernel, no `partial`.
-/
module
public import Ix.Compile.Clique.Basic
public import Ix.Compile.Clique.Packing
public import Ix.Compile.Clique.Telescope
public import Ix.Compile.Clique.WF
public import Ix.Compile.Clique.Whnf
public import Ix.Compile.Clique.Structural
public import Ix.Compile.Clique.PartialFixpoint
public import Ix.Compile.Clique.Transport
