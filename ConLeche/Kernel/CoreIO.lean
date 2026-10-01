module

public import ConLeche.Kernel.TypeChecker

@[expose] public section

/-!
# The io lane: infer at the licensed infer-only grade (task #161, stage 2)

**Status (task #172 B4): the io lane is LIVE in the executable's gated
mode.**  `inferBodyIO` lives in `ConLeche/Kernel/Core.lean` (moved
byte-identical, so the knot can tie it); the executable knot's
`inferIO` slot runs it at `mode.betaGate` and the full body everywhere
else (task #170: R ignores the flag).  The leaf lane below
(`coreKnotIO` / `inferTypeCoreIO`) remains the *statement subject* the
`InferClaimIO` family and the io-gate kernel fixtures are phrased
at; `Verify/Knot.lean`'s `inferTypeIO_on` identifies the executable
slot with it at the gated mode, and `inferTypeIO_off` collapses the
slot to `inferTypeCore` at every gate-off mode.  The stage-2
stop-and-name ("the knot boundary", DESIGN.md "Task #161 STAGE 2
BATCH 1") was dissolved by the R/P separation: the P tower no longer
routes through the R derivation tier, so a P-mode io call site
invalidates no R claim.

## What the lane is

The reference kernels type-check a declaration *once*, at the front
door, and let the inferences that reduction and definitional equality
perform on their own intermediate terms re-derive types **without
re-checking application arguments** (`infer_type_core(e, infer_only)`,
lean4lean's `inferType (inferOnly := true)`).  ConLeche cannot copy that
wholesale: `Typable e → InferOnly e t → (e really has type t)` is refuted
(spike `inferonly-metatheory`), and its semantic residue survives at
the *squash* regime — closed `V`-values satisfy every premise of the
premise-form io claim with `app ⟦f⟧ ⟦a⟧ ∉ ⟦B'⟧⟦a⟧`
(`io_membership_fails_at_squash`, the round-D study's probe 2; the
wall is model-class-wide, since any proof-irrelevant set model erases
Prop-side type identity).

What *is* licensed — mechanized, side-condition-free, at the graph
regime — is the skip at a binder whose **validated** annotation is
`never`: `io_domain_transfer`/`io_app_mem` recover the skipped
membership from the redex's own hereditary app slot through
`piR_dom_unique`, with no nonemptiness and no freshness premise.  So
the io lane's application clause skips the per-argument certificate
**iff**

* the ∀'s stored `pw` is `.never` (`PropWhen.isNever`, the ∀-`φ`
  uniform form of the claims' positive branch — exact, by
  `isNever_iff_forall_pwBit_ne_zero`), **and**
* `μ.verifiedChecks = true` — the mode gate, which is part of the amended
  law 1's text (clause (i)): the gate may fire only in the modes where
  the licensing theorems' hypotheses hold.  At `.trusted` the
  annotations are not validated at all, so the datum means nothing
  there and the certificate runs.

Everything else is `inferBody` verbatim, clause for clause: the λ/∀
domain-sort checks, the λ codomain-sort validation, the `letE`
conformance and the projection typing all **stay** — they are the
suppliers the P2 validation sites consume, and a deviation in the
strict direction needs no argument.

## The knot boundary

`coreKnotIO` is a **leaf** lane: its `whnfCore`/`whnf`/`defeq`/
`annotate` are the *full* knot's, unchanged, so every certificate the
reduction and definitional-equality bodies run is the certified one and
every claim tier that models those bodies (`Red`/`Infer`/`DefEq` in
`SetR/Rel.lean`, the `denoteAnnot` D lane, the graded P lane) keeps its
present subject.  Only `infer` is the io body, and only the io body
calls it.  Consequently

* the new statement surface is **exactly one family**
  (`InferClaimIO`), and the step assembly goes five-way:
  `{whnfCore, whnf, defeq, infer, inferIO}` at `fuel` give the same
  five at `fuel + 1`;
* nothing in the full lane can reach an io conclusion, which is the
  mode-provenance discipline enforced by construction rather than by
  review;
* and — the price, named here so it is not rediscovered — **the lane
  is unreachable from the executable**.  Making it reachable means
  letting a body the R tier models premise-exactly call `r.infer` at io
  grade, and that is the wall the seal records.
-/

namespace ConLeche

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)

/-- **The io knot** (the leaf lane).  `whnfCore`/`whnf`/`defeq`/
`annotate` are the *full* knot's at the same fuel — the io lane
consumes the certified reduction and definitional equality and never
supplies them — and `infer` is `inferBodyIO` tied to the io knot one
level down.  The full knot never mentions this one: that asymmetry is
the mode-provenance discipline, engineered rather than reviewed.

Task #172 B4: `inferBodyIO` itself moved to `ConLeche/Kernel/Core.lean`
(byte-identical) so the executable knot's io slot can tie it; this
leaf lane stays as the *statement subject* the io claims and the io
gate's kernel fixtures are phrased at, and the knot equations
(`Verify/Knot.lean`) identify the executable slot with it at the
gated mode.  Its own `inferIO` slot is the io body again — the io
grade is idempotent (there is nothing below io to select). -/
def coreKnotIO (env : Env) : Nat → CoreFns m
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate")
      inferIO := fun _ _ => throw (.internal "fuel exhausted: infer") }
  | fuel + 1 =>
    { whnfCore := (coreKnot mode env id (fuel + 1)).whnfCore
      whnf := (coreKnot mode env id (fuel + 1)).whnf
      defeq := (coreKnot mode env id (fuel + 1)).defeq
      annotate := (coreKnot mode env id (fuel + 1)).annotate
      infer := fun d e => inferBodyIO mode (coreKnotIO env fuel) env d e
      inferIO := fun d e => inferBodyIO mode (coreKnotIO env fuel) env d e }

/-- The io core, tied at `CheckM`: the specification the
`InferClaimIO` family is stated at. -/
def pureFnsIO (env : Env) : Nat → CoreFns CheckM :=
  coreKnotIO mode env

/-- Infer-only (io-grade) type inference, fueled — the io lane's single
entry point. -/
def inferTypeCoreIO (env : Env) (fuel depth : Nat) (e : Expr) :
    CheckM Expr :=
  (pureFnsIO mode env fuel).infer depth e

end ConLeche
