import Ix.Tc.Verify.Check.BlockIdentity

/-!
# Workset and dependency model

This file is the semantic half of E1.  It deliberately keeps three address
roles distinct while representing all of them with the production `Address`
type:

* `AnonWorkItem.provenTargets` describes serialized input coverage;
* `AnonWorkItem.targets` describes declarations actually checked/admitted;
* `DependencyCatalog.dependsOn` describes semantic declaration references.

A mutual block is one atomic dependency node.  Its serialized block address
and every projection address have the same `blockOf` image.  Standalones map
to themselves.
-/

namespace Ix.Tc

/-! ## Canonical finite address sets -/

/-- A duplicate-free finite address collection.  The list is retained as the
canonical representative later bound to a claim root; semantic membership is
ordinary propositional list membership. -/
structure FiniteAddressSet where
  entries : List Address
  nodup : entries.Nodup

namespace FiniteAddressSet

def Contains (set : FiniteAddressSet) (addr : Address) : Prop :=
  addr ∈ set.entries

instance : Membership Address FiniteAddressSet := ⟨Contains⟩

def Disjoint (left right : FiniteAddressSet) : Prop :=
  ∀ ⦃addr⦄, addr ∈ left → addr ∈ right → False

@[simp] theorem mem_mk {entries : List Address} {nodup : entries.Nodup}
    {addr : Address} :
    addr ∈ (⟨entries, nodup⟩ : FiniteAddressSet) ↔ addr ∈ entries :=
  Iff.rfl

end FiniteAddressSet

/-! ## Work coverage -/

namespace AnonWorkItem

/-- The collapsed dependency node represented by this work item. -/
def root : AnonWorkItem → Address
  | .standalone addr => addr
  | .block blockAddr _ _ => blockAddr

/-- Propositional coverage by the production `provenTargets` array. -/
def Covers (item : AnonWorkItem) (addr : Address) : Prop :=
  addr ∈ item.provenTargets

end AnonWorkItem

/-- `subjects` is exactly the union of the production work items' serialized
coverage.  The second field rules out duplicate work entries, and the third
rules out assigning one address to two distinct work items. -/
structure WorkCovers (work : Array AnonWorkItem)
    (subjects : FiniteAddressSet) : Prop where
  exact : ∀ addr, addr ∈ subjects ↔
    ∃ item, item ∈ work ∧ item.Covers addr
  workNodup : work.toList.Nodup
  unique : ∀ {addr left right},
    left ∈ work → right ∈ work →
    left.Covers addr → right.Covers addr → left = right

namespace WorkCovers

theorem covered {work : Array AnonWorkItem} {subjects : FiniteAddressSet}
    (h : WorkCovers work subjects) {addr : Address}
    (haddr : addr ∈ subjects) :
    ∃ item, item ∈ work ∧ item.Covers addr :=
  (h.exact addr).1 haddr

theorem subjectOfCovered {work : Array AnonWorkItem}
    {subjects : FiniteAddressSet} (h : WorkCovers work subjects)
    {item : AnonWorkItem} (hitem : item ∈ work) {addr : Address}
    (haddr : item.Covers addr) : addr ∈ subjects :=
  (h.exact addr).2 ⟨item, hitem, haddr⟩

end WorkCovers

/-! ## Semantic dependencies and collapsed blocks -/

/-- Abstract semantic reference catalog.  Both fields use the exact
production `Address` domain.  `blockOf` collapses projection addresses to
their owning Muts address and fixes already-collapsed nodes. -/
structure DependencyCatalog where
  blockOf : Address → Address
  dependsOn : Address → Address → Prop
  blockOf_idem : ∀ addr, blockOf (blockOf addr) = blockOf addr

/-- Every serialized address covered by an item collapses to that item's
single dependency node. -/
def WorkMatchesCatalog (catalog : DependencyCatalog)
    (work : Array AnonWorkItem) : Prop :=
  ∀ {item}, item ∈ work → ∀ {addr}, item.Covers addr →
    catalog.blockOf addr = item.root

/-- A dependency edge between distinct collapsed subject nodes.  The edge is
oriented from the prerequisite node to the dependent node, matching Lean's
`WellFounded` convention. -/
def CollapsedDependency (catalog : DependencyCatalog)
    (work : Array AnonWorkItem) (prerequisite dependent : Address) : Prop :=
  ∃ item, item ∈ work ∧ item.root = dependent ∧
    ∃ target, catalog.dependsOn dependent target ∧
      catalog.blockOf target = prerequisite ∧ prerequisite ≠ dependent

/-- Every semantic dependency of every selected subject item is either
another exact subject address or an explicit external assumption. -/
def DepsClosed (catalog : DependencyCatalog) (work : Array AnonWorkItem)
    (subjects assumptions : FiniteAddressSet) : Prop :=
  ∀ {item}, item ∈ work → ∀ {target},
    catalog.dependsOn item.root target →
      target ∈ subjects ∨ target ∈ assumptions

/-! ## Semantic acceptance of work items -/

namespace VerifyWorld

/-- Semantic acceptance for a raw address.  Declaration projection and
standalone addresses are accepted by `trusted`; a Muts envelope address is
accepted by the atomic `AcceptedBlock` fact established in E0. -/
def AcceptsAddress (world : VerifyWorld) (addr : Address) : Prop :=
  world.trusted (⟨addr, ()⟩ : KId .anon) ∨
    world.AcceptedBlock (⟨addr, ()⟩ : KId .anon)

theorem AcceptsAddress.mono {before after : VerifyWorld}
    (hle : before ≤ after) {addr : Address}
    (h : before.AcceptsAddress addr) : after.AcceptsAddress addr := by
  rcases h with htrusted | hblock
  · exact .inl (hle.trusted htrusted)
  · exact .inr (hblock.mono hle)

end VerifyWorld

/-- Exact semantic meaning of accepting one production work item.  A block
must publish its atomic block fact and trust every checker target; the Muts
envelope itself is intentionally not inserted into `VerifyWorld.trusted`. -/
def WorkItemAccepted (world : VerifyWorld) : AnonWorkItem → Prop
  | .standalone addr => world.trusted (⟨addr, ()⟩ : KId .anon)
  | .block blockAddr _ targets =>
      world.AcceptedBlock (⟨blockAddr, ()⟩ : KId .anon) ∧
        ∀ addr, addr ∈ targets →
          world.trusted (⟨addr, ()⟩ : KId .anon)

namespace WorkItemAccepted

theorem mono {before after : VerifyWorld} (hle : before ≤ after)
    {item : AnonWorkItem} (h : WorkItemAccepted before item) :
    WorkItemAccepted after item := by
  cases item with
  | standalone addr => exact hle.trusted h
  | block blockAddr primary targets =>
      exact ⟨h.1.mono hle, fun addr haddr => hle.trusted (h.2 addr haddr)⟩

/-- Semantic item acceptance covers every raw address in `provenTargets`,
using block acceptance for the envelope and declaration trust elsewhere. -/
theorem acceptsAddress {world : VerifyWorld} {item : AnonWorkItem}
    (h : WorkItemAccepted world item) {addr : Address}
    (haddr : item.Covers addr) : world.AcceptsAddress addr := by
  cases item with
  | standalone target =>
      simp only [AnonWorkItem.Covers, AnonWorkItem.provenTargets,
        Array.mem_singleton] at haddr
      subst addr
      exact .inl h
  | block blockAddr primary targets =>
      simp only [AnonWorkItem.Covers, AnonWorkItem.provenTargets,
        Array.mem_append, Array.mem_singleton] at haddr
      rcases haddr with haddr | haddr
      · subst addr
        exact .inr h.1
      · exact .inl (h.2 addr haddr)

end WorkItemAccepted

/-- The external assumptions already have semantic meaning in the baseline
Theory world. -/
def AssumptionsWF (baseline : VerifyWorld)
    (assumptions : FiniteAddressSet) : Prop :=
  ∀ {addr}, addr ∈ assumptions → baseline.AcceptsAddress addr

/-- Per-item C2 consequence needed by composition.  The rule is reusable at
any extension of `baseline`: once every dependency outside the item's own
collapsed block is accepted, the item can be admitted atomically. -/
def AllAccepted (baseline : VerifyWorld) (catalog : DependencyCatalog)
    (work : Array AnonWorkItem) : Prop :=
  ∀ item, item ∈ work → ∀ before, baseline ≤ before →
    (∀ {target}, catalog.dependsOn item.root target →
      catalog.blockOf target ≠ item.root → before.AcceptsAddress target) →
    ∃ after, before ≤ after ∧ WorkItemAccepted after item

/-! ## Constructive well-founded block schedules -/

/-- An item is ready after `done` when every subject dependency is either
internal to its own collapsed block or covered by an already completed item.
External assumptions are handled separately by `DepsClosed` and
`AssumptionsWF`. -/
def WorkReadyAfter (catalog : DependencyCatalog)
    (subjects : FiniteAddressSet) (done : List AnonWorkItem)
    (item : AnonWorkItem) : Prop :=
  ∀ {target}, catalog.dependsOn item.root target → target ∈ subjects →
    catalog.blockOf target = item.root ∨
      ∃ prior, prior ∈ done ∧ prior.Covers target

/-- An executable topological certificate, indexed by the reverse list of
items already completed. -/
inductive TopologicalFrom (catalog : DependencyCatalog)
    (subjects : FiniteAddressSet) :
    List AnonWorkItem → List AnonWorkItem → Prop
  | nil (done) : TopologicalFrom catalog subjects done []
  | cons {done item rest} :
      WorkReadyAfter catalog subjects done item →
      TopologicalFrom catalog subjects (item :: done) rest →
      TopologicalFrom catalog subjects done (item :: rest)

/-- Finite well-foundedness certificate for the collapsed dependency graph.
The schedule is a permutation of the work array and is directly usable by
the composition proof.  The rank field separately exposes the mathematical
decrease used to rule out dependency cycles. -/
structure WellFoundedBlocks (catalog : DependencyCatalog)
    (work : Array AnonWorkItem) (subjects : FiniteAddressSet) where
  schedule : List AnonWorkItem
  permutation : schedule.Perm work.toList
  topological : TopologicalFrom catalog subjects [] schedule
  rank : Address → Nat
  decreases : ∀ {item target}, item ∈ work →
    catalog.dependsOn item.root target → target ∈ subjects →
    catalog.blockOf target ≠ item.root →
      rank (catalog.blockOf target) < rank item.root

namespace WellFoundedBlocks

/-- Two distinct collapsed nodes cannot depend on each other. -/
theorem noTwoCycle {catalog : DependencyCatalog}
    {work : Array AnonWorkItem} {subjects : FiniteAddressSet}
    (h : WellFoundedBlocks catalog work subjects)
    {left right : AnonWorkItem}
    (hleft : left ∈ work) (hright : right ∈ work)
    (hlr : catalog.dependsOn left.root right.root)
    (hrl : catalog.dependsOn right.root left.root)
    (hsubjectLeft : left.root ∈ subjects)
    (hsubjectRight : right.root ∈ subjects)
    (hleftFixed : catalog.blockOf left.root = left.root)
    (hrightFixed : catalog.blockOf right.root = right.root)
    (hne : left.root ≠ right.root) : False := by
  have hrightLeft : catalog.blockOf right.root ≠ left.root := by
    simpa [hrightFixed] using hne.symm
  have hleftRight : catalog.blockOf left.root ≠ right.root := by
    simpa [hleftFixed] using hne
  have h₁ := h.decreases hleft hlr hsubjectRight hrightLeft
  have h₂ := h.decreases hright hrl hsubjectLeft hleftRight
  rw [hrightFixed] at h₁
  rw [hleftFixed] at h₂
  exact (Nat.not_lt_of_ge (Nat.le_of_lt h₂)) h₁

end WellFoundedBlocks

/-! ## Checked-set composition -/

/-- C3's semantic result: some final Theory world extends the baseline,
accepts exactly the advertised subject domain at the raw-address interface,
retains every explicit assumption, and records the closure/disjointness
contracts needed for later claim-root binding. -/
def SubjectWF (baseline : VerifyWorld) (catalog : DependencyCatalog)
    (work : Array AnonWorkItem) (subjects assumptions : FiniteAddressSet) :
    Prop :=
  ∃ finalWorld : VerifyWorld,
    baseline ≤ finalWorld ∧
    (∀ {addr}, addr ∈ subjects → finalWorld.AcceptsAddress addr) ∧
    (∀ {addr}, addr ∈ assumptions → finalWorld.AcceptsAddress addr) ∧
    WorkCovers work subjects ∧
    DepsClosed catalog work subjects assumptions ∧
    subjects.Disjoint assumptions

private theorem composeTopological
    {baseline : VerifyWorld} {catalog : DependencyCatalog}
    {work : Array AnonWorkItem} {subjects assumptions : FiniteAddressSet}
    (hall : AllAccepted baseline catalog work)
    (hdeps : DepsClosed catalog work subjects assumptions)
    (hassumptions : AssumptionsWF baseline assumptions)
    {done schedule : List AnonWorkItem} {current : VerifyWorld}
    (hcurrent : baseline ≤ current)
    (hdone : ∀ {item}, item ∈ done → WorkItemAccepted current item)
    (hschedule : ∀ {item}, item ∈ schedule → item ∈ work)
    (htopo : TopologicalFrom catalog subjects done schedule) :
    ∃ final, current ≤ final ∧
      ∀ {item}, item ∈ done ∨ item ∈ schedule →
        WorkItemAccepted final item := by
  induction htopo generalizing current with
  | nil done =>
      exact ⟨current, VerifyWorld.LE.rfl, fun hitem => by
        rcases hitem with hitem | hitem
        · exact hdone hitem
        · simp at hitem⟩
  | @cons done item rest hready hrest ih =>
      have hitemWork : item ∈ work := hschedule (by simp)
      have hdependencies : ∀ {target},
          catalog.dependsOn item.root target →
          catalog.blockOf target ≠ item.root →
          current.AcceptsAddress target := by
        intro target htarget houtside
        rcases hdeps hitemWork htarget with hsubject | hassumption
        · rcases hready htarget hsubject with hinternal | hprior
          · exact False.elim (houtside hinternal)
          · obtain ⟨prior, hpriorDone, hpriorTarget⟩ := hprior
            exact (hdone hpriorDone).acceptsAddress hpriorTarget
        · exact (hassumptions hassumption).mono hcurrent
      obtain ⟨next, hnext, haccepted⟩ :=
        hall item hitemWork current hcurrent hdependencies
      have hdoneNext : ∀ {candidate}, candidate ∈ item :: done →
          WorkItemAccepted next candidate := by
        intro candidate hcandidate
        rcases List.mem_cons.mp hcandidate with hcandidate | hcandidate
        · subst candidate
          exact haccepted
        · exact (hdone hcandidate).mono hnext
      have hrestWork : ∀ {candidate}, candidate ∈ rest → candidate ∈ work := by
        intro candidate hcandidate
        exact hschedule (by simp [hcandidate])
      obtain ⟨final, hfinal, hallFinal⟩ :=
        ih (hcurrent.trans hnext) hdoneNext hrestWork
      refine ⟨final, hnext.trans hfinal, ?_⟩
      intro candidate hcandidate
      apply hallFinal
      rcases hcandidate with hdoneOld | hscheduleAll
      · exact .inl (.tail _ hdoneOld)
      · rcases List.mem_cons.mp hscheduleAll with hhead | hrestMember
        · subst candidate
          exact .inl (.head _)
        · exact .inr hrestMember

/-- The E1 checked-set theorem.  Successful per-item C2 rules are reordered
by the constructive collapsed-block schedule; runtime address order is not
assumed to be topological. -/
theorem acceptedWorkset_subjectWF
    {baseline : VerifyWorld} {catalog : DependencyCatalog}
    {work : Array AnonWorkItem} {subjects assumptions : FiniteAddressSet}
    (hall : AllAccepted baseline catalog work)
    (hcovers : WorkCovers work subjects)
    (hdeps : DepsClosed catalog work subjects assumptions)
    (hwf : WellFoundedBlocks catalog work subjects)
    (hassumptions : AssumptionsWF baseline assumptions)
    (hdisjoint : subjects.Disjoint assumptions) :
    SubjectWF baseline catalog work subjects assumptions := by
  have hschedule : ∀ {item}, item ∈ hwf.schedule → item ∈ work := by
    intro item hitem
    have hlist : item ∈ work.toList := (hwf.permutation.mem_iff).1 hitem
    simpa using hlist
  obtain ⟨final, hfinal, haccepted⟩ := composeTopological hall hdeps
    hassumptions VerifyWorld.LE.rfl (by simp) hschedule hwf.topological
  refine ⟨final, hfinal, ?_, ?_, hcovers, hdeps, hdisjoint⟩
  · intro addr haddr
    obtain ⟨item, hitem, hcovered⟩ := hcovers.covered haddr
    have hitemList : item ∈ work.toList := by simpa using hitem
    exact (haccepted (.inr ((hwf.permutation.mem_iff).2 hitemList)))
      |>.acceptsAddress hcovered
  · intro addr haddr
    exact (hassumptions haddr).mono hfinal

end Ix.Tc
