import Ix.HostAdmission
import Ix.RoleBinding.ArtifactTheorems
import Ix.RoleBinding.ArtifactTieredTheorems

namespace Ix.HostAdmission

theorem Checked.bindingAndMain {statement : Statement} {artifact : Ixon.Env}
    {limits : Ix.Kernel.Admission.Limits} (checked : Checked statement artifact limits) :
    statement.bindingHash = checked.run.prepared.binding.address ∧ statement.main = artifact.main := by
  rcases checked with ⟨run, derived⟩
  unfold statementOf at derived
  cases result : componentsOf artifact limits run with
  | error error => simp [result, Except.map] at derived
  | ok value =>
    obtain ⟨kind, spec, root, _⟩ := value
    simp only [result, Except.map, Except.ok.injEq] at derived
    cases derived
    exact ⟨rfl, rfl⟩

theorem Checked.facts {statement : Statement} {artifact : Ixon.Env}
    {limits : Ix.Kernel.Admission.Limits} (checked : Checked statement artifact limits) :
    Facts artifact limits checked.run statement.kind statement.hostSpecDigest statement.contentRoot := by
  rcases checked with ⟨run, derived⟩
  unfold statementOf at derived
  cases result : componentsOf artifact limits run with
  | error error => simp [result, Except.map] at derived
  | ok value =>
    simp only [result, Except.map, Except.ok.injEq] at derived
    cases derived
    exact value.facts

theorem Checked.currentSpec {statement : Statement} {artifact : Ixon.Env}
    {limits : Ix.Kernel.Admission.Limits} (checked : Checked statement artifact limits) :
    Ix.SpecDigest.specDigest = .ok statement.hostSpecDigest := checked.facts.currentSpec

theorem Checked.contentRoot {statement : Statement} {artifact : Ixon.Env}
    {limits : Ix.Kernel.Admission.Limits} (checked : Checked statement artifact limits) :
    Merkle.root (checked.run.prepared.records.map (·.1)).toArray = .ok (some statement.contentRoot) :=
  checked.facts.contentRoot

theorem Checked.closed {statement : Statement} {artifact : Ixon.Env}
    {limits : Ix.Kernel.Admission.Limits} (checked : Checked statement artifact limits) :
    artifact.assumptions.isEmpty = true ∧ statement.policy = .noExternalArtifactAssumptions :=
  ⟨checked.facts.closed, by cases statement.policy; rfl⟩

theorem Checked.mainMember {statement : Statement} {artifact : Ixon.Env}
    {limits : Ix.Kernel.Admission.Limits} (checked : Checked statement artifact limits)
    (main : Address) (atMain : statement.main = some main) :
    main ∈ checked.run.prepared.records.map (·.1) := by
  have member := checked.facts.mainMember
  rw [← checked.bindingAndMain.2, atMain] at member
  exact member

theorem Checked.kindAgreement {statement : Statement} {artifact : Ixon.Env}
    {limits : Ix.Kernel.Admission.Limits} (checked : Checked statement artifact limits) :
    KindAgreement limits checked.run.prepared.records statement.kind := checked.facts.kindAgreement

theorem Checked.logicalModel (V : Type u) [Ix.Kernel.SetTheory V]
    {statement : Statement} {artifact : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    (checked : Checked statement artifact limits) :
    Nonempty (Ix.Kernel.Cached.StrongModel V checked.run.logicalEnv) := by
  rcases checked with ⟨run, _⟩
  cases run with
  | logical receipt => exact receipt.strongModel V
  | tiered receipt => exact receipt.strongModel V

theorem Checked.authentic {statement : Statement} {artifact : Ixon.Env}
    {limits : Ix.Kernel.Admission.Limits} (checked : Checked statement artifact limits) :
    Ix.Kernel.Admission.Authentic Address.admissionHash checked.run.prepared.records checked.run.prepared.blobs ∧
      Address.admissionHash checked.run.prepared.binding.bytes = statement.bindingHash := by
  rw [checked.bindingAndMain.1]
  rcases checked with ⟨run, _⟩
  cases run with
  | logical receipt => exact receipt.authentic
  | tiered receipt => exact receipt.authentic

/-- The tier conclusion is typing over an opaque scope, not a model for those
constants (which may include the tier's permitted unsafe axioms). -/
theorem Checked.tierTyped (V : Type u) [Ix.Kernel.SetTheory V]
    {statement : Statement} {artifact : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    (checked : Checked statement artifact limits) :
    ∃ declarations : List (Ix.Kernel.Tier.TierDecl .anon),
      ∀ c ∈ checked.run.typed, Ix.Kernel.Tier.TypedIn checked.run.logicalEnv declarations checked.run.typed c := by
  rcases checked with ⟨run, _⟩
  cases run with
  | logical _ => exact ⟨[], by simp [Run.typed]⟩
  | tiered receipt => exact (receipt.typed V).2.2

end Ix.HostAdmission
