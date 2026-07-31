# WHNF verification modules

The WHNF formalization is organized by proof responsibility rather than by
project milestone.  The directories are conceptual layers; imports retain the
precise proof-dependency order needed by Lean.

- `RuntimeContracts.lean` defines the common state, callback, and result
  contracts used by the reducer proofs.
- `Iota/` verifies rule recognition and selection, literal preprocessing,
  substitution, constructor synthesis, request closure, and optional iota
  reduction.
- `StructEta/` verifies scoped recursion classification and structure-eta
  rebuilding.
- `Structural/` verifies the cache shell and the structural reducer's variable,
  projection, application, and beta-dispatch branches.
- `Beta/` gives the constructive semantics of general multi-argument beta
  reduction.
- `Projection/` verifies projection and string-expansion callbacks used by the
  no-acceleration path.
- `Runtime/` connects the generic callback contracts to anonymous lazy
  ingress.
- `NoDelta/` assembles all active outer reductions that do not unfold
  definitions.
- `Driver/` verifies the full-WHNF step and public reducer entry points,
  including the explicit contract boundary for the compact symbolic-Nat
  guard.
- `Delta/` verifies trusted unfolding, cache semantics, spine rebuilding, and
  optional delta reduction.
- `Closure.lean` assembles the four fixed-universe WHNF contracts and records
  the boundary with the later `infer`/`isDefEq` closure work.

The foundational semantic definitions remain in the sibling module
`Ix.Tc.Verify.Whnf` (`../Whnf.lean`).
