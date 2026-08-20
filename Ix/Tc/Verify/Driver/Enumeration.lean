import Ix.Tc.Verify.Driver.Dependencies

/-!
# Exact `buildAnonWork` enumeration

The work builder operates on a serialized `Ixon.Env`, so its theorem needs an
explicit input-integrity contract.  `AnonWorkEnvWF` says every sorted source
key materializes with an agreeing cheap tag, every generated projection is
stored, every stored projection is owned by a stored Muts block, and Muts
blocks are nonempty.  None of these fields grants typing authority.

Under that structural contract, the production builder succeeds, its
`provenTargets` partition is exactly the source-key domain, and every target
collapses to its work item's root.
-/

namespace Ix.Tc

/-- `Except` carries no `DecidableEq` instance, so the `get`/`peekTag`
equations of `ExactAnonEntry` cannot otherwise build the instance the
`native_decide` fixtures need. -/
instance {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .error _, .ok _ => isFalse (by simp)
  | .ok _, .error _ => isFalse (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)

/-- Exact lazy entry used by the production classifier.  This is a
proposition, rather than a data-bearing structure, so the lazy implementation
witness cannot escape the structural environment contract. -/
def ExactAnonEntry (env : Ixon.Env) (addr : Address)
    (constant : Ixon.Constant) : Prop :=
  addr ∈ orderedAnonConstAddrs env ∧
    ∃ lazy, env.consts.get? addr = some lazy ∧
      lazy.get = .ok constant ∧
      lazy.peekTag = .ok (constantInfoTag constant.info)

namespace ExactAnonEntry

theorem getConst {env : Ixon.Env} {addr : Address}
    {constant : Ixon.Constant} (h : ExactAnonEntry env addr constant) :
    env.getConst? addr = some constant := by
  obtain ⟨_, lazy, hlookup, hmaterialize, _⟩ := h
  simp only [Ixon.Env.getConst?]
  rw [hlookup]
  simp only [Option.bind_some]
  unfold Ixon.LazyConstant.get? at ⊢
  unfold Ixon.LazyConstant.get at hmaterialize
  cases hcache : lazy.cache with
  | none =>
      simp only [hcache] at hmaterialize ⊢
      simpa [Except.toOption] using congrArg Except.toOption hmaterialize
  | some cached =>
      simp only [hcache] at hmaterialize ⊢
      cases hmaterialize
      rfl

theorem constant_unique {env : Ixon.Env} {addr : Address}
    {left right : Ixon.Constant}
    (hleft : ExactAnonEntry env addr left)
    (hright : ExactAnonEntry env addr right) : left = right := by
  obtain ⟨_, leftLazy, hleftLookup, hleftGet, _⟩ := hleft
  obtain ⟨_, rightLazy, hrightLookup, hrightGet, _⟩ := hright
  have hlazy : leftLazy = rightLazy :=
    Option.some.inj (hleftLookup.symm.trans hrightLookup)
  subst rightLazy
  exact Except.ok.inj (hleftGet.symm.trans hrightGet)

end ExactAnonEntry

/-- Owning Muts address of a projection record. -/
def projectionOwner? : Ixon.ConstantInfo → Option Address
  | .iPrj projection => some projection.block
  | .cPrj projection => some projection.block
  | .rPrj projection => some projection.block
  | .dPrj projection => some projection.block
  | _ => none

/-- Structural source-environment contract sufficient for exact work
enumeration.  It is deliberately separate from hash collision assumptions:
if two generated projection addresses collide, `projectionComplete` would
force the one map entry to materialize as two different projection records,
which `ExactAnonEntry.constant_unique` rules out. -/
structure AnonWorkEnvWF (env : Ixon.Env) : Prop where
  keysNodup : (orderedAnonConstAddrs env).toList.Nodup
  entry : ∀ {addr}, addr ∈ orderedAnonConstAddrs env →
    ∃ constant, ExactAnonEntry env addr constant
  blocksNonempty : ∀ {addr constant members},
    ExactAnonEntry env addr constant →
    constant.info = .muts members →
    (anonBlockTargets addr members).size > 0
  projectionComplete : ∀ {block constant members target},
    ExactAnonEntry env block constant →
    constant.info = .muts members →
    target ∈ anonBlockTargets block members →
    ∃ projectionConstant,
      ExactAnonEntry env target projectionConstant ∧
      projectionOwner? projectionConstant.info = some block
  projectionOwned : ∀ {addr constant owner},
    ExactAnonEntry env addr constant →
    projectionOwner? constant.info = some owner →
    ∃ blockConstant members,
      ExactAnonEntry env owner blockConstant ∧
      blockConstant.info = .muts members ∧
      addr ∈ anonBlockTargets owner members

namespace ExactAnonEntry

/-- Exact entries make the cheap production classifier equal the pure
materialized classifier. -/
theorem buildAnonWorkItem_eq {env : Ixon.Env} {addr : Address}
    {constant : Ixon.Constant} (h : ExactAnonEntry env addr constant) :
    buildAnonWorkItem env addr =
      .ok (AnonWorkItem.ofConstantInfo addr constant.info) := by
  obtain ⟨_, lazy, hlookup, hmaterialize, htag⟩ := h
  unfold buildAnonWorkItem
  simp only [hlookup]
  rw [htag]
  cases hinfo : constant.info <;>
    simp [hmaterialize, constantInfoTag, AnonWorkItem.ofConstantInfo,
      hinfo]
  all_goals
    change Except.ok _ = Except.ok _
    rfl

end ExactAnonEntry

/-- Pure materialized normal form of production work enumeration. -/
def expectedAnonWork (env : Ixon.Env) : Array AnonWorkItem :=
  (orderedAnonConstAddrs env).filterMap fun addr =>
    (env.getConst? addr).bind fun constant =>
      AnonWorkItem.ofConstantInfo addr constant.info

namespace AnonWorkEnvWF

private theorem list_filterMapM_eq_filterMap
    {α β : Type} {xs : List α}
    {f : α → Except IngressErr (Option β)} {g : α → Option β}
    (h : ∀ x, x ∈ xs → f x = .ok (g x)) :
    xs.filterMapM f = .ok (xs.filterMap g) := by
  induction xs with
  | nil =>
      change Except.ok [] = Except.ok []
      rfl
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs : ∀ y, y ∈ xs → f y = .ok (g y) := by
        intro y hy
        exact h y (by simp [hy])
      rw [List.filterMapM_cons, hx, ih hxs]
      cases hresult : g x with
      | none =>
          simp [hresult]
          change Except.ok (List.filterMap g xs) =
            Except.ok (List.filterMap g xs)
          rfl
      | some result =>
          simp [hresult]
          change Except.ok (result :: List.filterMap g xs) =
            Except.ok (result :: List.filterMap g xs)
          rfl

private theorem array_filterMapM_eq_filterMap
    {α β : Type} {xs : Array α}
    {f : α → Except IngressErr (Option β)} {g : α → Option β}
    (h : ∀ x, x ∈ xs → f x = .ok (g x)) :
    xs.filterMapM f = .ok (xs.filterMap g) := by
  have hlist : xs.toList.filterMapM f =
      .ok (xs.toList.filterMap g) := by
    apply list_filterMapM_eq_filterMap
    intro x hx
    exact h x (by simpa using hx)
  rw [← Array.toArray_toList (xs := xs), List.filterMapM_toArray, hlist]
  exact congrArg Except.ok
    (by simpa using (List.filterMap_toArray (l := xs.toList) (f := g)).symm)

theorem buildItem_eq_expected {env : Ixon.Env} (h : AnonWorkEnvWF env)
    {addr : Address} (haddr : addr ∈ orderedAnonConstAddrs env) :
    buildAnonWorkItem env addr = .ok
      ((env.getConst? addr).bind fun constant =>
        AnonWorkItem.ofConstantInfo addr constant.info) := by
  obtain ⟨constant, hentry⟩ := h.entry haddr
  rw [hentry.buildAnonWorkItem_eq, hentry.getConst]
  rfl

/-- The optimized tag-dispatch implementation has the exact pure
materialized normal form on structurally valid inputs. -/
theorem buildAnonWork_eq_expected {env : Ixon.Env}
    (h : AnonWorkEnvWF env) :
    buildAnonWork env = .ok (expectedAnonWork env) := by
  unfold buildAnonWork expectedAnonWork
  apply array_filterMapM_eq_filterMap
  intro addr haddr
  exact h.buildItem_eq_expected haddr

/-! ## Exact source-domain coverage -/

/-- The canonical source-key set certified by an environment contract. -/
def subjects {env : Ixon.Env} (h : AnonWorkEnvWF env) :
    FiniteAddressSet :=
  ⟨(orderedAnonConstAddrs env).toList, h.keysNodup⟩

@[simp] theorem mem_subjects {env : Ixon.Env} (h : AnonWorkEnvWF env)
    {addr : Address} :
    addr ∈ h.subjects ↔ addr ∈ orderedAnonConstAddrs env := by
  simp [subjects]

/-- Membership in the pure workset has an exact materialized source entry. -/
theorem mem_expectedAnonWork_iff {env : Ixon.Env}
    (h : AnonWorkEnvWF env) {item : AnonWorkItem} :
    item ∈ expectedAnonWork env ↔
      ∃ addr constant,
        ExactAnonEntry env addr constant ∧
          AnonWorkItem.ofConstantInfo addr constant.info = some item := by
  rw [expectedAnonWork, Array.mem_filterMap]
  constructor
  · rintro ⟨addr, haddr, hemitted⟩
    obtain ⟨constant, hentry⟩ := h.entry haddr
    refine ⟨addr, constant, hentry, ?_⟩
    rw [hentry.getConst] at hemitted
    exact hemitted
  · rintro ⟨addr, constant, hentry, hemitted⟩
    refine ⟨addr, hentry.1, ?_⟩
    rw [hentry.getConst]
    exact hemitted

end AnonWorkEnvWF

namespace AnonWorkItem

/-- Every emitted item is rooted at the source key which emitted it. -/
theorem ofConstantInfo_root {addr : Address} {info : Ixon.ConstantInfo}
    {item : AnonWorkItem}
    (h : ofConstantInfo addr info = some item) : item.root = addr := by
  cases info with
  | defn _ | recr _ | axio _ | quot _ =>
      have heq : standalone addr = item := by
        simpa [ofConstantInfo] using h
      rw [← heq]
      rfl
  | cPrj _ | rPrj _ | iPrj _ | dPrj _ =>
      simp [ofConstantInfo] at h
  | muts members =>
      cases hprimary : (anonBlockTargets addr members)[0]? with
      | none => simp [ofConstantInfo, hprimary] at h
      | some primary =>
          have heq : block addr primary (anonBlockTargets addr members) =
              item := by
            simpa [ofConstantInfo, hprimary] using h
          rw [← heq]
          rfl

@[simp] theorem covers_root (item : AnonWorkItem) :
    item.Covers item.root := by
  cases item <;>
    simp [Covers, root, provenTargets]

/-- Classification emits only items whose primary is an actual checker
target. -/
theorem ofConstantInfo_primary_mem_targets {addr : Address}
    {info : Ixon.ConstantInfo} {item : AnonWorkItem}
    (h : ofConstantInfo addr info = some item) :
    item.primary ∈ item.targets := by
  cases info with
  | defn _ | recr _ | axio _ | quot _ =>
      have heq : standalone addr = item := by
        simpa [ofConstantInfo] using h
      rw [← heq]
      simp [primary, targets]
  | cPrj _ | rPrj _ | iPrj _ | dPrj _ =>
      simp [ofConstantInfo] at h
  | muts members =>
      cases hprimary : (anonBlockTargets addr members)[0]? with
      | none => simp [ofConstantInfo, hprimary] at h
      | some primaryAddr =>
          have heq : block addr primaryAddr (anonBlockTargets addr members) =
              item := by
            simpa [ofConstantInfo, hprimary] using h
          rw [← heq]
          simp only [primary, targets]
          obtain ⟨hbound, hget⟩ := Array.getElem?_eq_some_iff.mp hprimary
          exact Array.mem_iff_getElem.mpr ⟨0, hbound, hget⟩

end AnonWorkItem

namespace AnonWorkEnvWF

private theorem covered_of_emitted {env : Ixon.Env}
    (h : AnonWorkEnvWF env) {addr : Address}
    {constant : Ixon.Constant} (hentry : ExactAnonEntry env addr constant)
    {item : AnonWorkItem}
    (hemitted : AnonWorkItem.ofConstantInfo addr constant.info = some item) :
    item ∈ expectedAnonWork env ∧ item.Covers addr := by
  constructor
  · exact (h.mem_expectedAnonWork_iff).2
      ⟨addr, constant, hentry, hemitted⟩
  · have hroot := AnonWorkItem.ofConstantInfo_root hemitted
    rw [← hroot]
    exact item.covers_root

private theorem block_primary {env : Ixon.Env}
    (h : AnonWorkEnvWF env) {addr : Address}
    {constant : Ixon.Constant} {members : Array Ixon.MutConst}
    (hentry : ExactAnonEntry env addr constant)
    (hinfo : constant.info = .muts members) :
    ∃ primary, (anonBlockTargets addr members)[0]? = some primary := by
  cases hprimary : (anonBlockTargets addr members)[0]? with
  | none =>
      have hle := Array.getElem?_eq_none_iff.mp hprimary
      have hpos := h.blocksNonempty hentry hinfo
      omega
  | some primary => exact ⟨primary, rfl⟩

private theorem projection_source_covered {env : Ixon.Env}
    (h : AnonWorkEnvWF env) {addr owner : Address}
    {constant : Ixon.Constant} (hentry : ExactAnonEntry env addr constant)
    (howner : projectionOwner? constant.info = some owner) :
    ∃ item, item ∈ expectedAnonWork env ∧ item.Covers addr := by
  obtain ⟨blockConstant, members, hblock, hblockInfo, htarget⟩ :=
    h.projectionOwned hentry howner
  obtain ⟨primary, hprimary⟩ := h.block_primary hblock hblockInfo
  let item := AnonWorkItem.block owner primary
    (anonBlockTargets owner members)
  refine ⟨item, ?_, ?_⟩
  · exact (h.mem_expectedAnonWork_iff).2 ⟨owner, blockConstant, hblock, by
      simp [item, AnonWorkItem.ofConstantInfo, hblockInfo, hprimary]⟩
  · simp [item, AnonWorkItem.Covers, AnonWorkItem.provenTargets,
      htarget]

/-- Every serialized source key is covered by a production work item.  Pure
projection records are covered by their owning block rather than emitted a
second time. -/
theorem source_covered {env : Ixon.Env} (h : AnonWorkEnvWF env)
    {addr : Address} (haddr : addr ∈ orderedAnonConstAddrs env) :
    ∃ item, item ∈ expectedAnonWork env ∧ item.Covers addr := by
  obtain ⟨constant, hentry⟩ := h.entry haddr
  cases hinfo : constant.info with
  | defn | recr | axio | quot =>
      let item := AnonWorkItem.standalone addr
      exact ⟨item, h.covered_of_emitted hentry (by
        simp [item, AnonWorkItem.ofConstantInfo, hinfo])⟩
  | muts members =>
      obtain ⟨primary, hprimary⟩ := h.block_primary hentry hinfo
      let item := AnonWorkItem.block addr primary
        (anonBlockTargets addr members)
      exact ⟨item, h.covered_of_emitted hentry (by
        simp [item, AnonWorkItem.ofConstantInfo, hinfo, hprimary])⟩
  | iPrj projection =>
      exact h.projection_source_covered (owner := projection.block) hentry (by
        simp [projectionOwner?, hinfo])
  | cPrj projection =>
      exact h.projection_source_covered (owner := projection.block) hentry (by
        simp [projectionOwner?, hinfo])
  | rPrj projection =>
      exact h.projection_source_covered (owner := projection.block) hentry (by
        simp [projectionOwner?, hinfo])
  | dPrj projection =>
      exact h.projection_source_covered (owner := projection.block) hentry (by
        simp [projectionOwner?, hinfo])

/-- Conversely, an emitted item's `provenTargets` cannot certify an address
outside the serialized source-key domain. -/
theorem covered_is_source {env : Ixon.Env} (h : AnonWorkEnvWF env)
    {item : AnonWorkItem} (hitem : item ∈ expectedAnonWork env)
    {addr : Address} (hcovered : item.Covers addr) :
    addr ∈ orderedAnonConstAddrs env := by
  obtain ⟨source, constant, hentry, hemitted⟩ :=
    (h.mem_expectedAnonWork_iff).1 hitem
  cases hinfo : constant.info with
  | defn | recr | axio | quot =>
      have hitemEq : item = .standalone source := by
        simpa [AnonWorkItem.ofConstantInfo, hinfo] using hemitted.symm
      subst item
      simp [AnonWorkItem.Covers, AnonWorkItem.provenTargets] at hcovered
      subst addr
      exact hentry.1
  | iPrj | cPrj | rPrj | dPrj =>
      simp [AnonWorkItem.ofConstantInfo, hinfo] at hemitted
  | muts members =>
      cases hprimary : (anonBlockTargets source members)[0]? with
      | none =>
          simp [AnonWorkItem.ofConstantInfo, hinfo, hprimary] at hemitted
      | some primary =>
          have hitemEq : item = .block source primary
              (anonBlockTargets source members) := by
            simpa [AnonWorkItem.ofConstantInfo, hinfo, hprimary] using
              hemitted.symm
          subst item
          simp [AnonWorkItem.Covers, AnonWorkItem.provenTargets] at hcovered
          rcases hcovered with rfl | htarget
          · exact hentry.1
          · obtain ⟨projectionConstant, hprojection, _⟩ :=
              h.projectionComplete hentry hinfo htarget
            exact hprojection.1

/-- Every production-normalized work item emits at least its primary checker
target. -/
theorem expected_primary_mem_targets {env : Ixon.Env}
    (h : AnonWorkEnvWF env) {item : AnonWorkItem}
    (hitem : item ∈ expectedAnonWork env) : item.primary ∈ item.targets := by
  obtain ⟨_, _, _, hemitted⟩ := (h.mem_expectedAnonWork_iff).1 hitem
  exact AnonWorkItem.ofConstantInfo_primary_mem_targets hemitted

/-! ## Collapsed-address alignment and uniqueness -/

end AnonWorkEnvWF

namespace ExactAnonEntry

theorem blockOfAddr_eq_owner {env : Ixon.Env}
    {addr owner : Address} {constant : Ixon.Constant}
    (h : ExactAnonEntry env addr constant)
    (howner : projectionOwner? constant.info = some owner) :
    blockOfAddr env addr = owner := by
  cases hinfo : constant.info <;>
    simp [blockOfAddr, h.getConst, projectionOwner?, hinfo] at howner ⊢ <;>
    assumption

theorem blockOfAddr_eq_self {env : Ixon.Env}
    {addr : Address} {constant : Ixon.Constant}
    (h : ExactAnonEntry env addr constant)
    (hnone : projectionOwner? constant.info = none) :
    blockOfAddr env addr = addr := by
  cases hinfo : constant.info <;>
    simp [blockOfAddr, h.getConst, projectionOwner?, hinfo] at hnone ⊢

end ExactAnonEntry

namespace AnonWorkEnvWF

/-- `provenTargets` and production dependency collapsing use exactly the same
`Address` domain: every covered target collapses to its work item's root. -/
theorem matches_blockOfAddr {env : Ixon.Env} (h : AnonWorkEnvWF env)
    {item : AnonWorkItem} (hitem : item ∈ expectedAnonWork env)
    {addr : Address} (hcovered : item.Covers addr) :
    blockOfAddr env addr = item.root := by
  obtain ⟨source, constant, hentry, hemitted⟩ :=
    (h.mem_expectedAnonWork_iff).1 hitem
  cases hinfo : constant.info with
  | defn | recr | axio | quot =>
      have hitemEq : item = .standalone source := by
        simpa [AnonWorkItem.ofConstantInfo, hinfo] using hemitted.symm
      subst item
      simp [AnonWorkItem.Covers, AnonWorkItem.provenTargets] at hcovered
      subst addr
      exact ExactAnonEntry.blockOfAddr_eq_self hentry (by
        simp [projectionOwner?, hinfo])
  | cPrj | rPrj | iPrj | dPrj =>
      simp [AnonWorkItem.ofConstantInfo, hinfo] at hemitted
  | muts members =>
      cases hprimary : (anonBlockTargets source members)[0]? with
      | none =>
          simp [AnonWorkItem.ofConstantInfo, hinfo, hprimary] at hemitted
      | some primary =>
          have hitemEq : item = .block source primary
              (anonBlockTargets source members) := by
            simpa [AnonWorkItem.ofConstantInfo, hinfo, hprimary] using
              hemitted.symm
          subst item
          simp [AnonWorkItem.Covers, AnonWorkItem.provenTargets] at hcovered
          rcases hcovered with rfl | htarget
          · exact ExactAnonEntry.blockOfAddr_eq_self hentry (by
              simp [projectionOwner?, hinfo])
          · obtain ⟨projectionConstant, hprojection, howner⟩ :=
              h.projectionComplete hentry hinfo htarget
            exact ExactAnonEntry.blockOfAddr_eq_owner hprojection howner

private theorem item_unique_of_root_eq {env : Ixon.Env}
    (h : AnonWorkEnvWF env) {left right : AnonWorkItem}
    (hleft : left ∈ expectedAnonWork env)
    (hright : right ∈ expectedAnonWork env)
    (hroot : left.root = right.root) : left = right := by
  obtain ⟨leftSource, leftConstant, hleftEntry, hleftEmitted⟩ :=
    (h.mem_expectedAnonWork_iff).1 hleft
  obtain ⟨rightSource, rightConstant, hrightEntry, hrightEmitted⟩ :=
    (h.mem_expectedAnonWork_iff).1 hright
  have hleftRoot := AnonWorkItem.ofConstantInfo_root hleftEmitted
  have hrightRoot := AnonWorkItem.ofConstantInfo_root hrightEmitted
  have hsources : leftSource = rightSource :=
    hleftRoot.symm.trans (hroot.trans hrightRoot)
  rw [← hsources] at hrightEntry hrightEmitted
  have hconstants : leftConstant = rightConstant :=
    ExactAnonEntry.constant_unique hleftEntry hrightEntry
  rw [← hconstants] at hrightEmitted
  exact Option.some.inj (hleftEmitted.symm.trans hrightEmitted)

private theorem list_filterMap_nodup_of_root
    {xs : List Address} (hxs : xs.Nodup)
    (f : Address → Option AnonWorkItem)
    (hroot : ∀ {source item}, source ∈ xs → f source = some item →
      item.root = source) :
    (xs.filterMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons source rest ih =>
      obtain ⟨hnotMem, hrestNodup⟩ := List.nodup_cons.mp hxs
      rw [List.filterMap_cons]
      cases hemitted : f source with
      | none =>
          apply ih hrestNodup
          intro other item hother hitem
          exact hroot (by simp [hother]) hitem
      | some item =>
          rw [List.nodup_cons]
          constructor
          · intro hitemMem
            obtain ⟨other, hother, hotherEmitted⟩ :=
              List.mem_filterMap.mp hitemMem
            have hsourceRoot := hroot (by simp) hemitted
            have hotherRoot := hroot (by simp [hother]) hotherEmitted
            have hsources : source = other :=
              hsourceRoot.symm.trans hotherRoot
            apply hnotMem
            rw [hsources]
            exact hother
          · apply ih hrestNodup
            intro other result hother hresult
            exact hroot (by simp [hother]) hresult

private theorem expectedAnonWork_nodup {env : Ixon.Env}
    (h : AnonWorkEnvWF env) :
    (expectedAnonWork env).toList.Nodup := by
  rw [expectedAnonWork, Array.toList_filterMap]
  apply list_filterMap_nodup_of_root h.keysNodup
  intro source item hsource hemitted
  obtain ⟨constant, hentry⟩ := h.entry (by simpa using hsource)
  rw [hentry.getConst] at hemitted
  exact AnonWorkItem.ofConstantInfo_root hemitted

/-- Exact partition theorem for the pure normal form of production
enumeration.  Removing any emitted item falsifies `WorkCovers.exact` for its
root, while overlapping work items are ruled out by collapsed-address
alignment and deterministic source classification. -/
theorem expectedAnonWork_covers {env : Ixon.Env}
    (h : AnonWorkEnvWF env) :
    WorkCovers (expectedAnonWork env) h.subjects where
  exact addr := by
    rw [h.mem_subjects]
    constructor
    · exact h.source_covered
    · rintro ⟨item, hitem, hcovered⟩
      exact h.covered_is_source hitem hcovered
  workNodup := h.expectedAnonWork_nodup
  unique := by
    intro addr left right hleft hright hleftCovered hrightCovered
    apply h.item_unique_of_root_eq hleft hright
    exact (h.matches_blockOfAddr hleft hleftCovered).symm.trans
      (h.matches_blockOfAddr hright hrightCovered)

/-- Exact workset/collapsed-catalog alignment for the production dependency
catalog. -/
theorem expectedAnonWork_matchesCatalog {env : Ixon.Env}
    (h : AnonWorkEnvWF env) (hblock : IxonEnv.BlockOfIdempotent env) :
    WorkMatchesCatalog (IxonEnv.dependencyCatalog env hblock)
      (expectedAnonWork env) := by
  intro item hitem addr hcovered
  exact h.matches_blockOfAddr hitem hcovered

/-- Public production-facing E1 enumeration result. -/
theorem buildAnonWork_exact {env : Ixon.Env}
    (h : AnonWorkEnvWF env) (hblock : IxonEnv.BlockOfIdempotent env) :
    ∃ work,
      buildAnonWork env = .ok work ∧
      WorkCovers work h.subjects ∧
      WorkMatchesCatalog (IxonEnv.dependencyCatalog env hblock) work := by
  refine ⟨expectedAnonWork env, h.buildAnonWork_eq_expected,
    h.expectedAnonWork_covers, ?_⟩
  exact h.expectedAnonWork_matchesCatalog hblock

end AnonWorkEnvWF

end Ix.Tc
