/-
  Ix.Compile.Pass.Clique: the transport `Φ_σ` of definition cliques, as
  total pure functions over `Ix.Expr`.

  * `Bounds`: every fuel and depth bound of the transport, named once;
  * `Dag`: the de Bruijn and locally nameless helpers, walked over distinct
    subterms;
  * `Basic`: term representation (and how Lean names are carried), the
    monad, levels as `MetaM` builds them, the comparison up to binder names
    and `mdata`, constant walks, permutations;
  * `Packing`: the right-nested `PSum`/`PProd` packings (types, injections,
    case trees, tuples, projection paths), decoded and rebuilt with Lean's
    own construction;
  * `PackingMatch`: a packing's leaves recognised up to a consistent renaming
    of their external variables;
  * `Telescope`: the fixed-parameter telescope in the first member's order;
  * `Whnf`: the small weak-head reducer that types paths into `below`.

  Not imported by the compiler (`Ix.Compile.Pass` does not import it). No
  `MetaM`, no kernel, no `partial`.
-/
module
public import Ix.Compile.Pass.Clique.Bounds
public import Ix.Compile.Pass.Clique.Dag
public import Ix.Compile.Pass.Clique.Basic
public import Ix.Compile.Pass.Clique.Packing
public import Ix.Compile.Pass.Clique.PackingMatch
public import Ix.Compile.Pass.Clique.Telescope
public import Ix.Compile.Pass.Clique.Whnf
