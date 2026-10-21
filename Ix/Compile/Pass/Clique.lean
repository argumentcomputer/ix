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
  * `Whnf`: the small weak-head reducer that types paths into `below`;
  * `WF`: the layout of a well-founded clique, the proofs' fixed-parameter
    scan, the prologue and epilogue both packed transports share, and the
    pieces of the packed equation lemma's regeneration;
  * `WFSchema`: the exact `WellFounded.fix`/`Nat.fix` root and the positions
    it owns (the recursive telescope, the decreasing obligations);
  * `WFMatcher`: the declaration-checked `Nat` dispatcher the transport may
    follow;
  * `WFConjugation`: the decoder-owned well-founded transport (`transportWF`);
  * `StructuralEq`: the regeneration of a structural member's equation proof
    over the transported definitions;
  * `Structural`: the structural transport (`transportStructural`), over the
    block's authenticated `below`/`brecOn` family and the below matchers
    recognised by their declarations;
  * `Plan`: the plan of a changed clique as data (encodings, the order's
    source, the transported members and canonical constants, the outcome),
    and its side-car record `_ix.clique`, typed data only;
  * `Table`: the input's cliques, their carried equation lemmas, the
    encoding roots, and the scheduling edges (`scheduleCliques`).

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
public import Ix.Compile.Pass.Clique.WF
public import Ix.Compile.Pass.Clique.WFSchema
public import Ix.Compile.Pass.Clique.WFMatcher
public import Ix.Compile.Pass.Clique.WFConjugation
public import Ix.Compile.Pass.Clique.StructuralEq
public import Ix.Compile.Pass.Clique.Structural
public import Ix.Compile.Pass.Clique.Plan
public import Ix.Compile.Pass.Clique.Table
