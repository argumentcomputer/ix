import Lean.Elab.Command
import Lean.PrivateName
import Lean.Util.FoldConsts
import Ix.Theory.Named.Std.AxiomAudit

/-!
# Exact trust-boundary auditing for `Ix.Kernel.Verify`

The audit traverses the checked declarations directly, including types,
theorem bodies, and inductive constructors. Imported axiom summaries can
omit dependencies of recursive declaration groups, so they are not the
source of truth here. The audit checks:

* an exact, per-root allowlist split into ordinary Lean axioms, explicitly
  named implementation bridge axioms, quarantined pending metatheory axioms,
  and generated `native_decide` axioms;
* an exact list of the reachable declarations that use `sorryAx` directly,
  so permitting `sorryAx` cannot hide where that debt entered the proof.

The executable manifests live in sibling modules.  Keeping the mechanism
separate lets us audit the temporary statement skeletons in a different
import context from the concrete translation relations with which their
opaque names currently collide.
-/

namespace Ix.Kernel.Verify.Audit

open Lean
open Lean.Elab.Command

/-- The complete permitted trust boundary for one exported theorem root.

Lean usually gives generated native axioms private names such as
`_private.Ix.Kernel.Expr.0....`; a public theorem proved directly by
`native_decide` can instead expose a public generated axiom.  Use
`nativeAxiom` below for the private case.  `sorryOrigins` is checked by
traversing the root's dependency graph. -/
structure RootAllowance where
  root : Lean.Name
  standardAxioms : Array Lean.Name := #[]
  /-- Nonlogical implementation bridge axioms retained in the local proof
  support. These remain separate from Lean's three permitted logical axioms
  so an executable fixture cannot silently widen `standardAxioms`. -/
  implementationAxioms : Array Lean.Name := #[]
  /-- Temporary local witnesses for unfinished metatheory proofs.
  Only the quarantined `Ix.Kernel.Frontier.Pending` namespace may occur
  here; completed theorem roots must leave this category empty. -/
  pendingAxioms : Array Lean.Name := #[]
  nativeAxioms : Array Lean.Name := #[]
  sorryOrigins : Array Lean.Name := #[]
  /-- Constants that must not occur anywhere in the root's transitive
  dependency graph.  This is used for architectural quarantine in addition
  to axiom accounting. -/
  forbiddenDependencies : Array Lean.Name := #[]

/-- Reconstruct the kernel name of a private generated native axiom.  This
avoids comparing pretty-printed names: the manifest and environment are
checked as `Lean.Name` values all the way through. -/
def nativeAxiom (moduleName userName : Lean.Name) : Lean.Name :=
  Lean.mkPrivateNameCore moduleName userName

private def permittedStandardAxioms : Array Lean.Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

private def sortNames (xs : Array Name) : Array Name :=
  xs.qsort Name.lt

namespace DependencyAudit

abbrev State := Ix.Theory.Named.AxiomAudit.State
abbrev collect := Ix.Theory.Named.AxiomAudit.collect

end DependencyAudit

private def validateCategories (allowance : RootAllowance) :
    CommandElabM Unit := do
  for axiomName in allowance.standardAxioms do
    unless permittedStandardAxioms.contains axiomName do
      throwError m!"{allowance.root}: {axiomName} is not a permitted standard Lean axiom"
  for axiomName in allowance.implementationAxioms do
    let rendered := axiomName.toString
    unless rendered.startsWith "Lean." || rendered.startsWith "Std." ||
        rendered.startsWith "Ix.Theory.Named." do
      throwError m!"{allowance.root}: implementation axiom is outside Lean/Std/Ix.Theory.Named: {axiomName}"
    if permittedStandardAxioms.contains axiomName then
      throwError m!"{allowance.root}: standard axiom misclassified as implementation: {axiomName}"
    if axiomName == ``sorryAx then
      throwError m!"{allowance.root}: sorryAx must be accounted for by sorryOrigins"
    if Lean.isPrivateName axiomName then
      throwError m!"{allowance.root}: private axiom must be accounted for as native: {axiomName}"
  for axiomName in allowance.pendingAxioms do
    unless axiomName.toString.startsWith "Ix.Kernel.Frontier.Pending." do
      throwError m!"{allowance.root}: pending axiom is outside Ix.Kernel.Frontier.Pending: {axiomName}"
    if permittedStandardAxioms.contains axiomName then
      throwError m!"{allowance.root}: standard axiom misclassified as pending: {axiomName}"
    if axiomName == ``sorryAx then
      throwError m!"{allowance.root}: sorryAx must be accounted for by sorryOrigins"
    if Lean.isPrivateName axiomName then
      throwError m!"{allowance.root}: private axiom must be accounted for as native: {axiomName}"
  for axiomName in allowance.nativeAxioms do
    unless (axiomName.toString.splitOn "._native.native_decide.").length == 2 do
      throwError m!"{allowance.root}: malformed native_decide axiom: {axiomName}"

private def expectedAxioms (allowance : RootAllowance) : Array Lean.Name :=
  let expected := allowance.standardAxioms ++ allowance.implementationAxioms ++
    allowance.pendingAxioms ++ allowance.nativeAxioms
  sortNames <| if allowance.sorryOrigins.isEmpty then expected
    else expected.push ``sorryAx

private def checkOne (allowance : RootAllowance) (dependencyAudit : DependencyAudit.State) :
    CommandElabM Unit := do
  validateCategories allowance
  let env ← getEnv
  unless env.contains allowance.root do
    throwError m!"axiom-audit root does not exist: {allowance.root}"

  let actualAxioms := sortNames dependencyAudit.axioms
  let expectedAxioms := expectedAxioms allowance
  unless actualAxioms == expectedAxioms do
    let missing := expectedAxioms.filter fun name =>
      !actualAxioms.contains name
    let unexpected := actualAxioms.filter fun name =>
      !expectedAxioms.contains name
    throwError m!"axiom allowlist mismatch for {allowance.root}\n\
      expected but absent: {repr (missing.map Name.toString).toList}\n\
      actual but unlisted: {repr (unexpected.map Name.toString).toList}"

  -- Origin and architectural-quarantine checks consume the same transitive
  -- dependency graph. Keep one exact traversal per root: large generated
  -- recursor proofs make two independent walks unnecessarily expensive.
  let actualOrigins := sortNames dependencyAudit.origins
  let expectedOrigins := sortNames allowance.sorryOrigins
  unless actualOrigins == expectedOrigins do
    throwError m!"sorryAx origin mismatch for {allowance.root}\n\
      expected direct origins: {repr expectedOrigins.toList}\n\
      actual direct origins:   {repr actualOrigins.toList}"

  -- A root is unconditional exactly when it has no explicitly enumerated
  -- pending metatheory axioms.  Such a root must not reach even axiom-free
  -- helper definitions from the quarantine module: otherwise replacing a
  -- pending witness could silently change the completed proof surface.
  if allowance.pendingAxioms.isEmpty then
    for dependency in dependencyAudit.names do
      if dependency.toString.startsWith "Ix.Kernel.Frontier.Pending." then
        throwError m!"{allowance.root}: unconditional root reaches quarantined dependency {dependency}"

  for forbidden in allowance.forbiddenDependencies do
    if dependencyAudit.names.contains forbidden then
      throwError m!"{allowance.root}: forbidden transitive dependency {forbidden}"

/-- Check a complete executable trust manifest.  Duplicate roots are rejected
instead of being silently audited twice. -/
def check (allowances : Array RootAllowance) : CommandElabM Unit := do
  let env ← getEnv
  let mut roots : NameSet := {}
  let mut cache : Ix.Theory.Named.AxiomAudit.Cache := {}
  for allowance in allowances do
    if roots.contains allowance.root then
      throwError m!"duplicate axiom-audit root: {allowance.root}"
    roots := roots.insert allowance.root
    let (dependencies, nextCache) :=
      Ix.Theory.Named.AxiomAudit.collectCached env allowance.root cache
    cache := nextCache
    checkOne allowance dependencies
  logInfo m!"Ix.Kernel verification trust audit passed for {allowances.size} theorem roots"

end Ix.Kernel.Verify.Audit
