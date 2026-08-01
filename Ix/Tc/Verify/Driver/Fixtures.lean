import Ix.Tc.Verify.Driver.Serial

/-!
# Adversarial E1 fixtures

These small, Blake3-independent fixtures exercise the checked-set contracts
themselves.  They deliberately use fixed distinct addresses so failures in
coverage, dependency closure, or graph well-foundedness cannot be hidden by
content-address computation.
-/

namespace Ix.Tc.E1Fixture

def address (byte : UInt8) : Address :=
  ⟨⟨Array.replicate 32 byte⟩⟩

def first : Address := address 41
def second : Address := address 42
def external : Address := address 43
def unresolved : Address := address 44

theorem address_ne {left right : UInt8} (h : left ≠ right) :
    address left ≠ address right := by
  intro heq
  have hbyte := congrArg (fun value : Address => value.hash.get! 0) heq
  simp [address] at hbyte
  exact h hbyte

@[simp] theorem first_ne_second : first ≠ second :=
  address_ne (by decide)

@[simp] theorem second_ne_first : second ≠ first :=
  Ne.symm first_ne_second

@[simp] theorem first_ne_external : first ≠ external :=
  address_ne (by decide)

@[simp] theorem external_ne_first : external ≠ first :=
  Ne.symm first_ne_external

@[simp] theorem second_ne_external : second ≠ external :=
  address_ne (by decide)

@[simp] theorem external_ne_second : external ≠ second :=
  Ne.symm second_ne_external

@[simp] theorem unresolved_ne_first : unresolved ≠ first :=
  address_ne (by decide)

@[simp] theorem unresolved_ne_second : unresolved ≠ second :=
  address_ne (by decide)

@[simp] theorem unresolved_ne_external : unresolved ≠ external :=
  address_ne (by decide)

def firstItem : AnonWorkItem := .standalone first
def secondItem : AnonWorkItem := .standalone second

def work : Array AnonWorkItem := #[firstItem, secondItem]

def subjects : FiniteAddressSet :=
  ⟨[first, second], by simp⟩

def assumptions : FiniteAddressSet :=
  ⟨[external], by simp⟩

/-- The positive fixture: `first` depends on one external assumption and
`second` depends on `first`. -/
def catalog : DependencyCatalog where
  blockOf := id
  dependsOn := fun source target =>
    (source = first ∧ target = external) ∨
      (source = second ∧ target = first)
  blockOf_idem := fun _ => rfl

@[simp] theorem mem_subjects {addr : Address} :
    addr ∈ subjects ↔ addr = first ∨ addr = second := by
  simp [subjects]

@[simp] theorem mem_assumptions {addr : Address} :
    addr ∈ assumptions ↔ addr = external := by
  simp [assumptions]

/-- The two standalone work items cover exactly the advertised subject set. -/
theorem workCovers : WorkCovers work subjects := by
  refine ⟨?_, ?_, ?_⟩
  · intro addr
    simp [work, firstItem, secondItem, subjects,
      AnonWorkItem.Covers,
      AnonWorkItem.provenTargets]
  · simp [work, firstItem, secondItem]
  · intro addr left right hleft hright hleftCovered hrightCovered
    simp [work] at hleft hright
    rcases hleft with rfl | rfl <;>
      rcases hright with rfl | rfl <;>
      simp [firstItem, secondItem, AnonWorkItem.Covers,
        AnonWorkItem.provenTargets] at hleftCovered hrightCovered ⊢
    exact False.elim (first_ne_second
      (hleftCovered.symm.trans hrightCovered))
    exact False.elim (second_ne_first
      (hleftCovered.symm.trans hrightCovered))

/-- Every positive-fixture dependency lies in the exact `S ∪ A`: the only
external edge is `first → external`. -/
theorem depsClosed : DepsClosed catalog work subjects assumptions := by
  intro item hitem target hdependency
  simp [work] at hitem
  rcases hitem with rfl | rfl
  · right
    simp [catalog, firstItem, AnonWorkItem.root] at hdependency ⊢
    exact hdependency
  · left
    simp [catalog, secondItem, AnonWorkItem.root] at hdependency ⊢
    exact .inl hdependency

/-- Bundled positive acceptance witness: a multi-declaration fixture has the
exact abstract subject and external-assumption domains claimed above. -/
theorem exactSubjectsAndAssumptions :
    WorkCovers work subjects ∧
      DepsClosed catalog work subjects assumptions ∧
      (∀ addr, addr ∈ subjects ↔ addr = first ∨ addr = second) ∧
      (∀ addr, addr ∈ assumptions ↔ addr = external) :=
  ⟨workCovers, depsClosed, fun _ => mem_subjects,
    fun _ => mem_assumptions⟩

/-- Dropping the second item leaves its subject uncovered. -/
theorem droppingWorkItem_breaks_coverage :
    ¬WorkCovers #[firstItem] subjects := by
  intro hcover
  have hsecond : second ∈ subjects := by simp
  obtain ⟨item, hitem, hcovered⟩ := hcover.covered hsecond
  simp only [Array.mem_singleton] at hitem
  subst item
  simp [firstItem, AnonWorkItem.Covers,
    AnonWorkItem.provenTargets] at hcovered

/-- Add one edge whose target is in neither `S` nor `A`. -/
def unresolvedCatalog : DependencyCatalog where
  blockOf := id
  dependsOn := fun source target =>
    catalog.dependsOn source target ∨
      (source = first ∧ target = unresolved)
  blockOf_idem := fun _ => rfl

/-- The extra unresolved edge makes dependency closure impossible. -/
theorem unresolvedDependency_breaks_closure :
    ¬DepsClosed unresolvedCatalog work subjects assumptions := by
  intro hclosed
  have hdependency : unresolvedCatalog.dependsOn first unresolved := by
    exact .inr ⟨rfl, rfl⟩
  have hresult := hclosed (item := firstItem) (target := unresolved)
    (by simp [work, firstItem]) hdependency
  rcases hresult with hsubject | hassumption
  · simp at hsubject
  · simp at hassumption

/-- Two distinct standalone nodes depending on one another. -/
def cyclicCatalog : DependencyCatalog where
  blockOf := id
  dependsOn := fun source target =>
    (source = first ∧ target = second) ∨
      (source = second ∧ target = first)
  blockOf_idem := fun _ => rfl

/-- No rank/schedule certificate can exist for the two-node cycle. -/
theorem cyclicStandalones_not_wellFounded :
    WellFoundedBlocks cyclicCatalog work subjects → False := by
  intro hwf
  apply hwf.noTwoCycle
    (left := firstItem) (right := secondItem)
  · simp [work, firstItem]
  · simp [work, secondItem]
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩
  · simp [firstItem, AnonWorkItem.root]
  · simp [secondItem, AnonWorkItem.root]
  · rfl
  · rfl
  · simp [firstItem, secondItem, AnonWorkItem.root]

end Ix.Tc.E1Fixture
