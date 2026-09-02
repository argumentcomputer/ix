import Lean.Elab.Command
import Lean.PrivateName
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-!
# Exact trust-boundary auditing for `Ix.Tc.Verify`

`Lean.collectAxioms` gives the kernel-computed, transitive axiom set for a
declaration.  This module adds two pieces needed by the verification plan:

* an exact, per-root allowlist split into ordinary Lean axioms, explicitly
  named upstream implementation axioms, quarantined pending-upstream axioms,
  and generated `native_decide` axioms;
* an exact list of the reachable declarations that use `sorryAx` directly,
  so permitting `sorryAx` cannot hide where that debt entered the proof.

The executable manifests live in sibling modules.  Keeping the mechanism
separate lets us audit the temporary statement skeletons in a different
import context from the concrete translation relations with which their
opaque names currently collide.
-/

namespace Ix.Tc.Verify.Audit

open Lean
open Lean.Elab.Command

/-- The complete permitted trust boundary for one exported theorem root.

Lean usually gives generated native axioms private names such as
`_private.Ix.Tc.Expr.0....`; a public theorem proved directly by
`native_decide` can instead expose a public generated axiom.  Use
`nativeAxiom` below for the private case.  `sorryOrigins` is checked by
traversing the root's dependency graph. -/
structure RootAllowance where
  root : Lean.Name
  standardAxioms : Array Lean.Name := #[]
  /-- Nonlogical implementation bridge axioms inherited from an upstream
  package.  These remain separate from Lean's three permitted logical axioms
  so an executable upstream fixture cannot silently widen `standardAxioms`. -/
  upstreamAxioms : Array Lean.Name := #[]
  /-- Temporary local witnesses for facts expected from a future upstream
  release.  Only the quarantined `Ix.Tc.Upstream.Pending` namespace may occur
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

/-- Direct constant references, following the same declaration cases as
`Lean.collectAxioms`.  In particular, opaque theorem values and inductive
constructors are included. -/
private def directConstants : ConstantInfo → Array Name
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors

namespace DependencyAudit

structure State where
  visited : NameSet := {}
  names : Array Name := #[]
  origins : Array Name := #[]

abbrev M := ReaderT Environment (StateM State)

/-- Traverse the checked kernel environment and record each reachable
declaration whose type or value directly mentions `sorryAx`. -/
partial def visit (declName : Name) : M Unit := do
  let state ← get
  unless state.visited.contains declName do
    modify fun s =>
      { s with
        visited := s.visited.insert declName
        names := s.names.push declName }
    let env ← read
    match env.checked.get.find? declName with
    | none => pure ()
    | some info =>
      let dependencies := directConstants info
      if declName != ``sorryAx && dependencies.contains ``sorryAx then
        modify fun s => { s with origins := s.origins.push declName }
      dependencies.forM visit

def collect (env : Environment) (root : Name) : State :=
  let (_, state) := ((visit root).run env).run {}
  state

end DependencyAudit

private def validateCategories (allowance : RootAllowance) :
    CommandElabM Unit := do
  for axiomName in allowance.standardAxioms do
    unless permittedStandardAxioms.contains axiomName do
      throwError m!"{allowance.root}: {axiomName} is not a permitted standard Lean axiom"
  for axiomName in allowance.upstreamAxioms do
    let rendered := axiomName.toString
    unless rendered.startsWith "Lean." || rendered.startsWith "Std." ||
        rendered.startsWith "Lean4Lean." do
      throwError m!"{allowance.root}: upstream axiom is outside Lean/Std/Lean4Lean: {axiomName}"
    if permittedStandardAxioms.contains axiomName then
      throwError m!"{allowance.root}: standard axiom misclassified as upstream: {axiomName}"
    if axiomName == ``sorryAx then
      throwError m!"{allowance.root}: sorryAx must be accounted for by sorryOrigins"
    if Lean.isPrivateName axiomName then
      throwError m!"{allowance.root}: private axiom must be accounted for as native: {axiomName}"
  for axiomName in allowance.pendingAxioms do
    unless axiomName.toString.startsWith "Ix.Tc.Upstream.Pending." do
      throwError m!"{allowance.root}: pending axiom is outside Ix.Tc.Upstream.Pending: {axiomName}"
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
  let expected := allowance.standardAxioms ++ allowance.upstreamAxioms ++
    allowance.pendingAxioms ++ allowance.nativeAxioms
  sortNames <| if allowance.sorryOrigins.isEmpty then expected
    else expected.push ``sorryAx

private def checkOne (allowance : RootAllowance) : CommandElabM Unit := do
  validateCategories allowance
  let env ← getEnv
  unless env.contains allowance.root do
    throwError m!"axiom-audit root does not exist: {allowance.root}"

  let actualAxioms := sortNames (← Lean.collectAxioms allowance.root)
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
  let dependencyAudit := DependencyAudit.collect env allowance.root
  let actualOrigins := sortNames dependencyAudit.origins
  let expectedOrigins := sortNames allowance.sorryOrigins
  unless actualOrigins == expectedOrigins do
    throwError m!"sorryAx origin mismatch for {allowance.root}\n\
      expected direct origins: {repr expectedOrigins.toList}\n\
      actual direct origins:   {repr actualOrigins.toList}"

  -- A root is unconditional exactly when it has no explicitly enumerated
  -- pending-upstream axioms.  Such a root must not reach even axiom-free
  -- helper definitions from the quarantine module: otherwise replacing a
  -- pending witness could silently change the completed proof surface.
  if allowance.pendingAxioms.isEmpty then
    for dependency in dependencyAudit.names do
      if dependency.toString.startsWith "Ix.Tc.Upstream.Pending." then
        throwError m!"{allowance.root}: unconditional root reaches quarantined dependency {dependency}"

  for forbidden in allowance.forbiddenDependencies do
    if dependencyAudit.names.contains forbidden then
      throwError m!"{allowance.root}: forbidden transitive dependency {forbidden}"

/-- Check a complete executable trust manifest.  Duplicate roots are rejected
instead of being silently audited twice. -/
def check (allowances : Array RootAllowance) : CommandElabM Unit := do
  let mut roots : NameSet := {}
  for allowance in allowances do
    if roots.contains allowance.root then
      throwError m!"duplicate axiom-audit root: {allowance.root}"
    roots := roots.insert allowance.root
    checkOne allowance
  logInfo m!"Ix.Tc verification trust audit passed for {allowances.size} theorem roots"

end Ix.Tc.Verify.Audit
