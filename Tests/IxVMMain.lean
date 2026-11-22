import Tests.Ix.Kernel.Arena
import Tests.Ix.Kernel.StringReduction
import Tests.Ix.Compile.Mutual
import Tests.Ix.IxVM
import Tests.Ix.IxVM.Eval
import Tests.Ix.IxVM.Exploits
import Tests.Ix.IxVM.DefinitionDependencies
import Tests.Ix.IxVM.BindingAnchors
import Tests.Ix.IxVM.BindingFrontier
import Tests.Ix.IxVM.TagN
import Tests.Ix.IxVM.Codec
import Tests.Ix.IxVM.UserAxioms
import Tests.Ix.IxVM.DecisionRoles
import Tests.Ix.IxVM.CircuitVerdict
import Tests.Ix.IxVM.ClaimSafety
import Tests.Ix.IxVM.SafeReferences
import Tests.Ix.IxVM.RecursorParentRoute
import Tests.Ix.IxVM.ShapeGuards
import Tests.Ix.IxVM.PwHints
import Tests.Ix.IxVM.ModelAdvice
import Tests.Ix.IxVM.ModeledProj
import Tests.Ix.IxVM.FieldReduction
import Tests.Ix.IxVM.SyntheticRegressions
import Tests.Ix.IOIngress
import Tests.Registry
import Ix.Meta

/-!
  IxVM circuit-verdict & FFT-pin test runner (`IxVMTests`).
  Kept separate from `IxTests` (`Tests/Main.lean`) so host-only PRs and
  `host-build` do not compile or link the 22 IxVM circuit test modules.
-/

open Tests.Registry in
/-- The CI jobs owned by `IxVMTests`. -/
def ownedJobs : List CiJob := [.ixvm, .nightlyIxvm]

open Tests.Registry in
/-- Every IxVM circuit-verdict entry and its tier (`ci:ixvm`, `ci:nightly-ixvm`,
or opt-in `manual`). -/
def registry : List Entry := [
  -- Claims through the formal IxVM program (`ixvm-proof test` on the claim
  -- artifact; `Tests.Ix.IxVM.Harness`), each verdict pinned: completeness,
  -- FFT cost pins, and Rust-host/FFI/circuit-verdict boundary checks.
  -- Kernel verdicts and exact FFT costs for constants, the binding claim and a shard.
  .env "ixvm-kernel-checks" (.ci .ixvm) Tests.Ix.IxVM.kernelChecks,
  -- Prover-authored malformed Ixon, each exploit with its controls (PR subset
  -- focused on unproved boundaries, positive controls, and host smokes).
  .env "ixvm-exploits" (.ci .ixvm) Tests.Ix.IxVM.Exploits.run,
  -- Opt-in full `.binding` exploit sweep: formally covered unconditionally by
  -- `IxVM.Refinement.Endpoint.circuitComposed` (`ClosureManifest.lean`) plus
  -- `ixvm-kernel-checks` completeness and PR `ixvm-exploits` host smoke.
  .env "ixvm-exploits-full" (.manual "opt-in `.binding` exploit sweep; formally covered by `circuitComposed` (`ClosureManifest.lean`) + `ixvm-kernel-checks`") Tests.Ix.IxVM.Exploits.runFull,
  -- The lean-kernel-arena tutorial fixtures: good + native_decide + bad smokes on PR.
  .env "ixvm-arena" (.ci .ixvm) Tests.Ix.Kernel.Arena.run,
  -- Opt-in full 100+ `bad_*` arena sweep: PR `ixvm-arena` + `ixvm-exploits`
  -- probe the `asm = some _` boundary while subject type-checking is proved in
  -- `KernelCheck::check_const`.
  .env "ixvm-arena-full" (.manual "opt-in 100+ `bad_*` lean-kernel-arena sweep; PR `ixvm-arena` + `ixvm-exploits` probe `asm = some _`") Tests.Ix.Kernel.Arena.runFull,
  -- The program's TagN codec against the host's (`Ixon.putTagN`/`getTagN`).
  .runner "ixvm-tagn" (.ci .ixvm) Tests.Ix.IxVM.TagN.run,
  -- Opt-in 4,128-claim exhaustive TagN decode sweep: formally covered by
  -- `getTagN{0,2,4}_refines` + `get_constant_spec` (pinned in `Audit.lean` &
  -- `ClosureAudit.lean`), while PR `ixvm-tagn` covers unproved `put_tagn`,
  -- `Reveal`, deferred range checks, and Rust FFI parity.
  .runner "ixvm-tagn-sweep" (.manual "opt-in 4,128-claim TagN decode sweep; formally covered by `getTagN{0,2,4}_refines` + `get_constant_spec`") Tests.Ix.IxVM.TagN.runSweep,
  -- The program's Ixon codec (`ixon-tests`' vectors) and claim boundary.
  .runner "ixvm-codec" (.ci .ixvm) Tests.Ix.IxVM.Codec.run,
  -- Evaluation claims against Lean's own reduction and generated arithmetic
  -- (PR fast subset; full 24-term generated arithmetic suite runs nightly in
  -- `ci:nightly-ixvm` because `Claim.eval` is not yet formally proved).
  .env "ixvm-eval" (.ci .ixvm) Tests.Ix.IxVM.Eval.run,
  .env "ixvm-eval-full" (.ci .nightlyIxvm) Tests.Ix.IxVM.Eval.runFull,
  -- Every leaf of a claim's axioms tree type-checked, used or not.
  .runner "ixvm-user-axioms" (.ci .ixvm) Tests.Ix.IxVM.UserAxioms.run,
  -- A decision's `of_decide_eq_*` roles bound by a compiled binding
  -- (`Array.extract_append._proof_1_1`).
  .env "ixvm-decision-roles" (.ci .ixvm) Tests.Ix.IxVM.DecisionRoles.run,
  -- Circular definitions, binding anchors and the lazy binding frontier.
  .runner "ixvm-definition-dependencies" (.ci .ixvm) Tests.Ix.IxVM.DefinitionDependencies.run,
  .runner "ixvm-binding-anchors" (.ci .ixvm) Tests.Ix.IxVM.BindingAnchors.run,
  .runner "ixvm-binding-frontier" (.ci .ixvm) Tests.Ix.IxVM.BindingFrontier.run,
  -- A constant byte out of range is refused.
  .runner "ixvm-io-ingress" (.ci .ixvm) Tests.IOIngress.run,
  .env "ixvm-model-advice" (.ci .ixvm) Tests.Ix.IxVM.ModelAdvice.run,
  .env "ixvm-modeled-proj" (.ci .ixvm) Tests.Ix.IxVM.ModeledProj.run,
  .env "ixvm-model-report" (.manual "model advice per mutual or nested block of IX_MODEL_IXE") Tests.Ix.IxVM.ModelAdvice.report,
  .env "ixvm-model-coverage" (.manual "every modeled block of IX_MODEL_IXE through IxVM") Tests.Ix.IxVM.ModelAdvice.coverage,
  .env "ixvm-model-proj" (.manual "records of IX_MODEL_IXE that project at a modeled block") Tests.Ix.IxVM.ModelAdvice.projUse,
  -- Execution with every assertion checked gives the circuit's verdict on a witness;
  -- default execution skips the deferred range checks and can accept what the
  -- circuit cannot prove.
  .env "ixvm-circuit-verdict" (.ci .ixvm) Tests.Ix.IxVM.CircuitVerdict.run,
  -- Recursors of inductive types whose field or index types reduce in the context
  -- of earlier binders.
  .env "ixvm-field-reduction" (.ci .ixvm) Tests.Ix.IxVM.FieldReduction.run,
  -- Typing claims refuse seeds outside Lean's logic (unsafe or partial); the claim
  -- builders leave them out.
  .runner "ixvm-claim-safety" (.ci .ixvm) Tests.Ix.IxVM.ClaimSafety.run,
  .runner "ixvm-safe-references" (.ci .ixvm) Tests.Ix.IxVM.SafeReferences.run,
  -- Opt-in `.binding` + `assumed = false` reference-safety sweep: formally
  -- covered by `circuitComposed` + `RecordRefsIn.safe` (pinned in
  -- `ClosureAudit.lean`), while PR `ixvm-safe-references` keeps `asm = some _`
  -- and host smokes.
  .runner "ixvm-safe-references-full" (.manual "opt-in `.binding` + `assumed = false` reference-safety sweep; formally covered by `circuitComposed` + `RecordRefsIn.safe`") Tests.Ix.IxVM.SafeReferences.runFull,
  .runner "ixvm-unsafe-origin-walks" (.manual "IX_AIUR_WALK_ARTIFACT: a verify_transitive artifact") Tests.Ix.IxVM.SafeReferences.runUnsafeOrigins,
  .runner "ixvm-recursor-parent-route" (.ci .ixvm) Tests.Ix.IxVM.RecursorParentRoute.run,
  -- The declaration checker's shape guards: one kind of member per inductive block, no later
  -- use of a recursive field, a recursor header free of `let`.
  .env "ixvm-shape-guards" (.ci .ixvm) Tests.Ix.IxVM.ShapeGuards.run,
  -- Corpus-driven and synthetic 3-way IxVM / IxC regressions: modeled extract closure,
  -- Lean 4.34 native_decide inert classification, dead-let universe bounds, multi-container
  -- and mutual AST modeled families, semantic imax, and adversarial boundary controls.
  .env "ixvm-synthetic-regressions" (.ci .ixvm) Tests.Ix.IxVM.SyntheticRegressions.run,
  .runner "ixvm-claim-safety-corpus" (.manual "walk closure of what stays owned on a compiled corpus; IX_SAFETY_IXE, IX_SAFETY_IXES") Tests.Ix.IxVM.ClaimSafety.corpus,
  -- A wrong datum is rejected and a missing one a host error, through the program
  -- (runs once the program reads the data).
  .runner "ixvm-pw-circuit" (.ci .ixvm) Tests.Ix.IxVM.PwHints.circuit,
  .env "ixvm-fixture" (.manual "rebuild the dev fixture IxVM/IxVM/fixtures/nat-add-comm.ixf; IX_FIXTURE_OUT") Tests.Ix.IxVM.PwHints.fixture,
  .env "ixvm-pw-diag" (.manual "why the kernel refuses records of a claim; IX_PW_NAME") Tests.Ix.IxVM.PwHints.diag,
  .runner "ixvm-pw-corpus" (.manual "the binder-data annotator on a compiled corpus; IX_PW_IXE, IX_PW_IXES") Tests.Ix.IxVM.PwHints.corpus,
  .runner "binder-data-corpus" (.manual "a compiled artifact's binder-data sections: canonical, recomputed equal; IX_BD_IXE") Tests.Ix.IxVM.BinderData.corpus
]

/-- The IxVM entries that must stay registered once, in their tier. -/
def required : List (String × String) := [
  ("ixvm-kernel-checks", "ci:ixvm"),
  ("ixvm-exploits", "ci:ixvm"),
  ("ixvm-arena", "ci:ixvm"),
  ("ixvm-tagn", "ci:ixvm"),
  ("ixvm-codec", "ci:ixvm"),
  ("ixvm-eval", "ci:ixvm"),
  ("ixvm-user-axioms", "ci:ixvm"),
  ("ixvm-decision-roles", "ci:ixvm"),
  ("ixvm-io-ingress", "ci:ixvm"),
  ("ixvm-model-advice", "ci:ixvm"),
  ("ixvm-modeled-proj", "ci:ixvm"),
  ("ixvm-circuit-verdict", "ci:ixvm"),
  ("ixvm-field-reduction", "ci:ixvm"),
  ("ixvm-claim-safety", "ci:ixvm"),
  ("ixvm-safe-references", "ci:ixvm"),
  ("ixvm-recursor-parent-route", "ci:ixvm"),
  ("ixvm-shape-guards", "ci:ixvm"),
  ("ixvm-synthetic-regressions", "ci:ixvm"),
  ("ixvm-pw-circuit", "ci:ixvm"),
  ("ixvm-eval-full", "ci:nightly-ixvm")]

def main (args : List String) : IO UInt32 :=
  Tests.Registry.runScoped "ixvmtests-registry" (.ci .ixvm) false ownedJobs registry required get_env! args
