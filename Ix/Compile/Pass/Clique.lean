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
  * `PartialFixpoint`: the layout of a `partial_fixpoint` clique, and the
    decoding and regeneration of its instance trees, packed paths,
    `solveMonoCall`'s path proofs and the `monotone_mk` tree;
  * `PFConjugation`: the decoder-owned `partial_fixpoint` transport
    (`transportPF`);
  * `Plan`: the plan of a changed clique as data (encodings, the order's
    source, the transported members and canonical constants, the outcome),
    and its side-car record `_ix.clique`, typed data only;
  * `Table`: the input's cliques, their carried equation lemmas, the
    encoding roots, and the scheduling edges (`scheduleCliques`);
  * `Order`: the canonical order of a theorem clique by its statements
    (`statementOrder`);
  * `Transport`: the transport's entry point (`transport`): its input (the
    clique, its encoding, `σ`, the authenticated structural family), the
    dispatch to the three transports, the baseline and the causes;
  * `Recover`: the recovered specification of a clique (each member's body
    with its recursion made explicit again, checked by re-encoding), its
    normalised form (`normalisedSpecs`) and the canonical order it gives
    (`cliqueOrder`);
  * `PlanClique`: the plan of a clique (`planClique`: the encoding, the
    authenticated structural family, the order, the transport, the checks),
    and the canonical constants and transported members as input constants
    (`canonConst`, `withValue`);
  * `Hook`: the hook's per-block computation as pure functions over a
    `HookEnv` (`cliquePlanFor`, `cliqueCallers`, `prepareCliques` →
    `CliquePrep`), unwired;
  * `Row`: the equation rows of a transported well-founded clique
    (`rowsOf`: the faithful copies `n._ix.src` of its encoding set, then
    the rows `f._ix.row : lhs = f`, Lean's value against the transported
    member, with a term proof), and the rows' sort computation (`sortOf?`).

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
public import Ix.Compile.Pass.Clique.PartialFixpoint
public import Ix.Compile.Pass.Clique.PFConjugation
public import Ix.Compile.Pass.Clique.Plan
public import Ix.Compile.Pass.Clique.Table
public import Ix.Compile.Pass.Clique.Order
public import Ix.Compile.Pass.Clique.Transport
public import Ix.Compile.Pass.Clique.Recover
public import Ix.Compile.Pass.Clique.PlanClique
public import Ix.Compile.Pass.Clique.Hook
public import Ix.Compile.Pass.Clique.Row
