import Ix.Tc.Verify.Check.PublicStandalone
import Ix.Tc.Verify.Check.PublicBlocks
import Ix.Tc.Verify.Driver.BooleanAcceptance
import Ix.Tc.Verify.Ingress.SerializedBoolean
import Ix.Tc.Verify.RecursiveMethods.Public

/-!
# Public checker theorem frontier

All seven public theorem roots now use the concrete verification relations and
a finite, fuel-indexed production call schedule:

* `TcM.whnf.wf`, `TcM.infer.wf`, and `TcM.isDefEq.wf` are the C1A adapters
  from `RecursiveMethods/Public.lean`;
* `TcM.checkConst.wf` is K3's standalone axiom/definition-family theorem,
  starting from `PendingDecl` and untyped validator ingress and producing a
  real `StandaloneCheckResult`, a `VDecl.WF`-backed trusted-world promotion,
  and the promoted post-state invariant; and
* `TcM.checkConst.blockDisposition` is E0's exhaustive successful-dispatch
  theorem: the production call either performs one exact atomic coordinated
  admission or takes the separately verified standalone branch; and
* `BooleanEnumerationFixture.subjectWF` is the E3-S acceptance root: the
  production serial driver successfully checks the exact six-entry Boolean
  source environment, and its two coordinated work rows satisfy `SubjectWF`
  through transparent run-scoped K3/E0 resources, an explicit empty
  assumption set, and certificate-backed E2 inductive evidence.
* `BooleanSerialized.subjectWF` is the T0-S representation root: the same
  semantic result is connected to a successful pure Ixon byte decode, exact
  hash-verified eager and cold-lazy ingress, serialized dependency refs, and
  a successful run of the production anonymous driver.

The K3 statement deliberately exposes `StandaloneRoute`.  E0 now closes the
coordinated transaction, physical/ghost identity, and cache-publication
layers.  Singleton definition blocks are constructive.  Inductive and
recursor bodies remain relative in the generic adapter to an explicitly
supplied `InductiveOracle` resource; the public E3-S root instantiates both
resources from the Lean4Lean Boolean generation certificate.  Quotient
semantics, mutual/nested inductives, indexed or parameterized families, and
multi-definition blocks remain outside this certificate-backed release
fragment.  Collision, finite-resource, lazy-ingress, source-to-router
agreement, projection, and upstream metatheory obligations remain visible in
`SupportedCheckRun` and its transparent body constructors. There are no
opaque semantic statement stubs and no local `sorry` frontier in this module.

The public root is defined at the end of the production proof itself rather
than copied or proof-erased here.  This module is only the stable import
frontier, so its exported statement cannot drift from the actual validator,
bounded full-inference pipeline, fresh lookup, routing, atomic publication,
and rollback-aware checker implementation. The bounded roots are audited
against any dependency on the legacy all-depth
`RecursiveMethodClosureContext`.
-/
