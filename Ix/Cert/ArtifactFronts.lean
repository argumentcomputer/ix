import Ix.RoleBinding.Artifact
import Ix.Cert.DefinitionSnapshots
import Ix.Cert.TheoremSnapshots

/-! Fronts of the existing actual artifact admission. The view repeats pure
preparation because Artifact.Prepared does not retain ev/ds; it never reruns
the kernel, loads a default prelude, reorders records or chooses a model. -/
namespace Ix.Cert.ArtifactFronts
open Ix.Kernel Ix.Kernel.Admission Ix.Kernel.Reader
open Ix.Cert.DefinitionSnapshots Ix.Cert.ReferenceFronts
universe w

def view {artifact : Ixon.Env} {limits : Limits}
    (receipt : Ix.RoleBinding.Artifact.Receipt artifact limits) : Except Admission.Error DefinitionSnapshots.Receipt := do
  let (ev,ds) ← prepareWith Address.admissionHash receipt.prepared.binding receipt.prepared.pre limits
    receipt.prepared.records receipt.prepared.blobs receipt.prepared.hints.lookup
  pure ⟨receipt.prepared.table,receipt.prepared.pre,ev,ds,mkFEnv receipt.target⟩

structure Facts {artifact : Ixon.Env} {limits : Limits}
    (receipt : Ix.RoleBinding.Artifact.Receipt artifact limits) (v : DefinitionSnapshots.Receipt) : Prop where
  table : v.table = receipt.prepared.table
  pre : v.pre = receipt.prepared.pre
  index : v.index = mkFEnv receipt.target
  prepared : prepareWith Address.admissionHash receipt.prepared.binding receipt.prepared.pre limits
    receipt.prepared.records receipt.prepared.blobs receipt.prepared.hints.lookup = .ok (v.ev,v.ds)
  checked : Cached.checkDecls .verified v.ev v.ds = .ok receipt.target

/-- The supplied artifact receipt already proves this exact preparation
succeeds, with this exact accepted target. No new checker success is assumed. -/
theorem view_exists {artifact : Ixon.Env} {limits : Limits}
    (receipt : Ix.RoleBinding.Artifact.Receipt artifact limits) :
    ∃ v, view receipt = .ok v ∧ Facts receipt v := by
  obtain ⟨ev,ds,prepared,checked⟩ := checkBytesWith_checkDecls receipt.checked
  refine ⟨⟨receipt.prepared.table,receipt.prepared.pre,ev,ds,mkFEnv receipt.target⟩,?_,
    ⟨rfl,rfl,rfl,prepared,checked⟩⟩
  simp [view,prepared,pure,Except.pure,bind,Except.bind]

theorem view_facts {artifact : Ixon.Env} {limits : Limits}
    {receipt : Ix.RoleBinding.Artifact.Receipt artifact limits} {v : DefinitionSnapshots.Receipt}
    (ran : view receipt = .ok v) : Facts receipt v := by
  obtain ⟨actual,run,facts⟩ := view_exists receipt
  rw [ran] at run
  cases run
  exact facts

theorem Facts.env {artifact : Ixon.Env} {limits : Limits}
    {receipt : Ix.RoleBinding.Artifact.Receipt artifact limits} {v : DefinitionSnapshots.Receipt}
    (facts : Facts receipt v) : v.env = receipt.target := by
  unfold DefinitionSnapshots.Receipt.env
  rw [facts.index]
  rfl

/-- The only model adaptation is transport along the proved equality of the
view environment with receipt.target. Its supplied interpretation is unchanged. -/
def suppliedModel {V : Type w} [SetTheory V] {artifact : Ixon.Env} {limits : Limits}
    {receipt : Ix.RoleBinding.Artifact.Receipt artifact limits} {v : DefinitionSnapshots.Receipt}
    (facts : Facts receipt v) (M : Cached.StrongModel V receipt.target) : Cached.StrongModel V v.env :=
  facts.env.symm ▸ M

private theorem cast_acval {V : Type w} [SetTheory V] {a b : Env .anon}
    (same : a = b) (M : Cached.StrongModel V a) :
    (same ▸ M).internal.base2.acval = M.internal.base2.acval := by cases same; rfl
private theorem cast_cval {V : Type w} [SetTheory V] {a b : Env .anon}
    (same : a = b) (M : Cached.StrongModel V a) :
    (same ▸ M).model.cval = M.model.cval := by cases same; rfl

theorem supplied_interpretation {V : Type w} [SetTheory V] {artifact : Ixon.Env} {limits : Limits}
    {receipt : Ix.RoleBinding.Artifact.Receipt artifact limits} {v : DefinitionSnapshots.Receipt}
    (facts : Facts receipt v) (M : Cached.StrongModel V receipt.target) :
    (suppliedModel facts M).internal.base2.acval = M.internal.base2.acval ∧
      (suppliedModel facts M).model.cval = M.model.cval :=
  ⟨cast_acval facts.env.symm M,cast_cval facts.env.symm M⟩

/-- Every actual definition uses its own preparation/index/prefix and the
existing artifact target. This includes generated declarations in that stream. -/
theorem definition_snapshot (V : Type w) [SetTheory V] {artifact : Ixon.Env} {limits : Limits}
    {receipt : Ix.RoleBinding.Artifact.Receipt artifact limits} {v : DefinitionSnapshots.Receipt}
    (ran : view receipt = .ok v) {i : Nat} {cv : Ix.Kernel.ConstantVal .anon} {raw : Ix.Kernel.Expr .anon} {hint : ReducibilityHint}
    (atDecl : v.ds.toList[i]? = some (.defnDecl cv raw hint)) :
    ∃ F before expected checked,
      let snap : DefinitionSnapshots.Snapshot := ⟨i,cv,raw,hint,before.consts.length,expected,checked,
        v.index.restrictTo before.consts.length⟩
      DefinitionFrontAt v.ev v.ds.toList receipt.target i cv raw hint F before expected checked ∧
      v.snapshot i = .ok snap ∧ snap.before = before ∧ snap.view.env = receipt.target ∧
      (∀ key, snap.view.find? key = before.find? key) ∧ snap.view.find? cv.name = none := by
  have facts := view_facts ran
  obtain ⟨F,before,expected,checked,front,counter,logical,_,lookup,hidden⟩ :=
    DefinitionSnapshots.checked_context V facts.checked atDecl
  have indexed : v.index.idx[cv.name]? = some (before.consts.length,
      .defnInfo ⟨cv.name,cv.levelParams,expected⟩ checked hint) := by rw [facts.index]; exact counter
  have atArray : v.ds[i]? = some (.defnDecl cv raw hint) := by simpa using atDecl
  refine ⟨F,before,expected,checked,front,?_,?_,?_,?_,?_⟩
  · simp [DefinitionSnapshots.Receipt.snapshot,atArray,indexed,pure,Except.pure]
  · change v.index.env.prefixTo before.consts.length = before
    rw [facts.index]; exact logical
  · change v.index.env = receipt.target
    rw [facts.index]; rfl
  · intro key; rw [facts.index]; exact lookup key
  · rw [facts.index]; exact hidden

theorem theorem_snapshot (V : Type w) [SetTheory V] {artifact : Ixon.Env} {limits : Limits}
    {receipt : Ix.RoleBinding.Artifact.Receipt artifact limits} {v : DefinitionSnapshots.Receipt}
    (ran : view receipt = .ok v) {i : Nat} {cv : Ix.Kernel.ConstantVal .anon} {raw : Ix.Kernel.Expr .anon}
    (atDecl : v.ds.toList[i]? = some (.thmDecl cv raw)) :
    ∃ F before expected checkedProof,
      let snap : TheoremSnapshots.Snapshot := ⟨i,cv,raw,before.consts.length,expected,
        v.index.restrictTo before.consts.length⟩
      TheoremSnapshots.TheoremFrontAt v.ev v.ds.toList receipt.target i cv raw F before expected checkedProof ∧
      TheoremSnapshots.snapshot v i = .ok snap ∧ snap.before = before ∧ snap.view.env = receipt.target ∧
      (∀ key, snap.view.find? key = before.find? key) ∧ snap.view.find? cv.name = none := by
  have facts := view_facts ran
  obtain ⟨F,before,expected,checkedProof,front,counter,logical,_,lookup,hidden⟩ :=
    TheoremSnapshots.checked_context V facts.checked atDecl
  have indexed : v.index.idx[cv.name]? = some (before.consts.length,
      .thmInfo ⟨cv.name,cv.levelParams,expected⟩ raw) := by rw [facts.index]; exact counter
  have atArray : v.ds[i]? = some (.thmDecl cv raw) := by simpa using atDecl
  refine ⟨F,before,expected,checkedProof,front,?_,?_,?_,?_,?_⟩
  · simp [TheoremSnapshots.snapshot,atArray,indexed,pure,Except.pure]
  · change v.index.env.prefixTo before.consts.length = before
    rw [facts.index]; exact logical
  · change v.index.env = receipt.target
    rw [facts.index]; rfl
  · intro key; rw [facts.index]; exact lookup key
  · rw [facts.index]; exact hidden

/-- The definition's stored value law uses the original supplied model
directly, at receipt.target and all level/variable valuations. -/
theorem definition_denotes {V : Type w} [SetTheory V] {artifact : Ixon.Env} {limits : Limits}
    {receipt : Ix.RoleBinding.Artifact.Receipt artifact limits} {v : DefinitionSnapshots.Receipt}
    (ran : view receipt = .ok v) (M : Cached.StrongModel V receipt.target)
    {i : Nat} {cv : Ix.Kernel.ConstantVal .anon} {raw : Ix.Kernel.Expr .anon} {hint : ReducibilityHint}
    (atDecl : v.ds.toList[i]? = some (.defnDecl cv raw hint)) :
    ∃ F before expected checked,
      DefinitionFrontAt v.ev v.ds.toList receipt.target i cv raw hint F before expected checked ∧
      ∀ φ ρ, Denotes M.model.cval receipt.target φ ρ checked (M.model.cval cv.name φ) := by
  obtain ⟨F,before,expected,checked,front,_⟩ := definition_snapshot V ran atDecl
  exact ⟨F,before,expected,checked,front,fun φ ρ => front.denotes M φ ρ⟩

/-- info: 'Ix.Cert.ArtifactFronts.view_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms view_exists
/-- info: 'Ix.Cert.ArtifactFronts.supplied_interpretation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms supplied_interpretation
/-- info: 'Ix.Cert.ArtifactFronts.definition_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms definition_snapshot
/-- info: 'Ix.Cert.ArtifactFronts.theorem_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms theorem_snapshot
/-- info: 'Ix.Cert.ArtifactFronts.definition_denotes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms definition_denotes

end Ix.Cert.ArtifactFronts
