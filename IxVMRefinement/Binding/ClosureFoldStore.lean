import IxVMRefinement.Binding.ClosureFold
import IxVMRefinement.Binding.ReadsAgree
import IxVMRefinement.Binding.UnitDefn

/-! # The closure's store

The closure of group `g` installs every record the group adds but the record of its role unit.
Its store is the group's store `R'` without that record, where the record is new in the group
(`closureStore`). What the fold reads of it:

* `closureStore_spec`: it is a `ClosureStore` (between `R` and `R'`, with `R'`'s blobs, lacking
  only role-unit records);
* `closureStore_usedClosed`: it is closed under what its records use, the record of a new role
  unit being a definition or an axiom, which no record of the group uses, and which is neither a
  block nor a projection;
* `closureStore_hashed`, `closureStore_committed`, `closureStore_zeroFree`: `R'`'s store clauses;
* `reads_closureStore`: a reading over `R'` of an address holding no new role-unit record is a
  reading over the closure's store (`readsIn_of_agree`: a reading looks into the store only at
  its record, blocks and inductive projections);
* `keptIn_closureStore`: what a constant keeps of a record of `R` it keeps over the closure's
  store;
* `constAddr_record`, `constAddr_same`: in a store closed under block members, a constant
  address is its record's own address or holds a projection record of the block, and two
  records sharing a constant address are one record. -/

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing

set_option linter.unusedVariables false

/-- **A role unit of a group is at one address.** -/
theorem roleUnitAt_unique {t : Ix.Kernel.RoleTable} {g : Nat} {a a' : _root_.Address}
    (h : RoleUnitAt t g a) (h' : RoleUnitAt t g a') : a = a' := by
  obtain ⟨r, hr, ha, hk⟩ := h
  obtain ⟨r', hr', ha', -⟩ := h'
  have hs := roleGroup_unit hr hk
  rw [hs, List.mem_singleton] at hr'
  subst hr'
  rw [ha] at ha'
  exact Option.some.inj ha'

/-- **The record of a role unit of group `g`, new in the group.** -/
def NewUnit (t : Ix.Kernel.RoleTable) (g : Nat) (R R' : Ixon.Env) (a : _root_.Address) : Prop :=
  RoleUnitAt t g a ∧ New R R' a

open Classical in
/-- **The closure's store** (module docstring). -/
noncomputable def closureStore (t : Ix.Kernel.RoleTable) (g : Nat) (R R' : Ixon.Env) :
    Ixon.Env :=
  if h : ∃ a, NewUnit t g R R' a then
    { R' with consts := R'.consts.erase (Classical.choose h) }
  else R'

/-- A record that is not a projection is its own owner. -/
theorem isProj_of_ownerOf_ne {a : _root_.Address} {c : Ixon.Constant}
    (h : Ix.Cert.ownerOf a c ≠ a) : IsProj c := by
  unfold Ix.Cert.ownerOf at h
  cases hi : c.info with
  | dPrj p => exact Or.inl ⟨p, hi⟩
  | iPrj p => exact Or.inr (Or.inl ⟨p, hi⟩)
  | cPrj p => exact Or.inr (Or.inr (Or.inl ⟨p, hi⟩))
  | rPrj p => exact Or.inr (Or.inr (Or.inr ⟨p, hi⟩))
  | defn _ => rw [hi] at h; exact (h rfl).elim
  | axio _ => rw [hi] at h; exact (h rfl).elim
  | quot _ => rw [hi] at h; exact (h rfl).elim
  | recr _ => rw [hi] at h; exact (h rfl).elim
  | muts _ => rw [hi] at h; exact (h rfl).elim

section Store

variable {t : Ix.Kernel.RoleTable} {g : Nat} {R R' : Ixon.Env}

theorem closureStore_blobs : (closureStore t g R R').blobs = R'.blobs := by
  unfold closureStore
  split <;> rfl

theorem closureStore_none {x : _root_.Address} (hx : NewUnit t g R R' x) :
    (closureStore t g R R').consts.get? x = none := by
  have hex : ∃ a, NewUnit t g R R' a := ⟨x, hx⟩
  have e : Classical.choose hex = x := roleUnitAt_unique (Classical.choose_spec hex).1 hx.1
  unfold closureStore
  rw [dif_pos hex]
  show (R'.consts.erase (Classical.choose hex)).get? x = none
  rw [e, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_erase]
  simp

theorem closureStore_get {x : _root_.Address} (hx : ¬ NewUnit t g R R' x) :
    (closureStore t g R R').consts.get? x = R'.consts.get? x := by
  unfold closureStore
  split
  · next h =>
    have hne : (Classical.choose h == x) = false := by
      rw [beq_eq_false_iff_ne]
      intro e
      exact hx (e ▸ Classical.choose_spec h)
    show (R'.consts.erase (Classical.choose h)).get? x = R'.consts.get? x
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_erase, hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← Std.HashMap.get?_eq_getElem?]
  · rfl

theorem recordOf_closureStore_none {x : _root_.Address} (hx : NewUnit t g R R' x) :
    recordOf (closureStore t g R R') x = none := by
  unfold recordOf
  rw [closureStore_none hx]
  rfl

theorem recordOf_closureStore {x : _root_.Address} (hx : ¬ NewUnit t g R R' x) :
    recordOf (closureStore t g R R') x = recordOf R' x := by
  unfold recordOf
  rw [closureStore_get hx]

/-- The closure's store holds no more than `R'`. -/
theorem closureStore_le : StoreLe (closureStore t g R R') R' := by
  refine ⟨fun a lc h => ?_, fun a b h => ?_⟩
  · by_cases hu : NewUnit t g R R' a
    · rw [closureStore_none hu] at h
      cases h
    · rw [closureStore_get hu] at h
      exact h
  · rw [closureStore_blobs] at h
    exact h

/-- A record of the closure's store is `R'`'s, at an address holding no new role-unit record. -/
theorem recordOf_closureStore_down {x : _root_.Address} {c : Ixon.Constant}
    (h : recordOf (closureStore t g R R') x = some c) :
    recordOf R' x = some c ∧ ¬ NewUnit t g R R' x := by
  by_cases hu : NewUnit t g R R' x
  · rw [recordOf_closureStore_none hu] at h
    cases h
  · exact ⟨(recordOf_closureStore hu).symm.trans h, hu⟩

variable {ρ : BRun}

/-- A record new in the group has no bytes in `R`. -/
theorem new_get_none (hadm : Admits ρ t g R R') {a : _root_.Address} (h : New R R' a) :
    R.consts.get? a = none := by
  cases hR : R.consts.get? a with
  | none => rfl
  | some lc =>
    exfalso
    have h' := hadm.mono a lc hR
    have e : recordOf R' a = recordOf R a := by
      unfold recordOf
      rw [h', hR]
    obtain ⟨h1, h2⟩ := h
    rw [e, h2] at h1
    simp at h1

theorem not_newUnit_of_get (hadm : Admits ρ t g R R') {a : _root_.Address}
    {lc : Ixon.LazyConstant} (h : R.consts.get? a = some lc) : ¬ NewUnit t g R R' a := by
  intro hu
  rw [new_get_none hadm hu.2] at h
  cases h

theorem not_newUnit_of_record {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf R a = some c) : ¬ NewUnit t g R R' a := by
  intro hu
  rw [hu.2.2] at h
  cases h

theorem recordOf_closureStore_of_R (hadm : Admits ρ t g R R') {x : _root_.Address}
    {c : Ixon.Constant} (h : recordOf R x = some c) :
    recordOf (closureStore t g R R') x = some c := by
  rw [recordOf_closureStore (not_newUnit_of_record h)]
  exact recordOf_of_loaded hadm.mono h

/-- **The closure's store is a `ClosureStore`.** -/
theorem closureStore_spec (hadm : Admits ρ t g R R') :
    ClosureStore t g R R' (closureStore t g R R') where
  le₁ := ⟨fun a lc h => by
      rw [closureStore_get (not_newUnit_of_get hadm h)]
      exact hadm.mono a lc h,
    fun a b h => by
      rw [closureStore_blobs]
      exact hadm.monoBlobs a b h⟩
  le₂ := closureStore_le
  blobs := fun x b h => by
    rw [closureStore_blobs]
    exact h
  units := fun a h1 h2 => by
    by_cases hu : NewUnit t g R R' a
    · exact hu.1
    · rw [closureStore_get hu] at h2
      rw [h2] at h1
      cases h1

/-- A record new in the closure's store is new in the group and no new role unit's. -/
theorem new_of_closureStore {a : _root_.Address} (h : New R (closureStore t g R R') a) :
    New R R' a ∧ ¬ NewUnit t g R R' a := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨hc', hu⟩ := recordOf_closureStore_down hc
  exact ⟨⟨by rw [hc']; rfl, h2⟩, hu⟩

theorem new_closureStore_of {a : _root_.Address} (h : New R R' a)
    (hu : ¬ NewUnit t g R R' a) : New R (closureStore t g R R') a :=
  ⟨by rw [recordOf_closureStore hu]; exact h.1, h.2⟩

/-- The record of a new role unit, a definition or an axiom, is no projection and no block. -/
theorem newUnit_not_proj_block
    (hform : ∀ a c, RoleUnitAt t g a → New R R' a → recordOf R' a = some c →
      (∃ d, c.info = .defn d) ∨ ∃ ax, c.info = .axio ax)
    {a : _root_.Address} {c : Ixon.Constant} (hu : NewUnit t g R R' a)
    (hc : recordOf R' a = some c) : ¬ IsProj c ∧ ¬ IsBlock c := by
  rcases hform a c hu.1 hu.2 hc with ⟨d, hd⟩ | ⟨ax, hax⟩
  · exact ⟨fun hp => standalone_not_proj (Or.inl ⟨d, hd⟩) hp,
      fun hb => standalone_not_block (Or.inl ⟨d, hd⟩) hb⟩
  · exact ⟨fun hp => standalone_not_proj (Or.inr (Or.inr (Or.inl ⟨ax, hax⟩))) hp,
      fun hb => standalone_not_block (Or.inr (Or.inr (Or.inl ⟨ax, hax⟩))) hb⟩

/-- **The closure's store is closed under what its records use** (module docstring). -/
theorem closureStore_usedClosed (hadm : Admits ρ t g R R') (hR : UsedClosed R)
    (hform : ∀ a c, RoleUnitAt t g a → New R R' a → recordOf R' a = some c →
      (∃ d, c.info = .defn d) ∨ ∃ ax, c.info = .axio ax) :
    UsedClosed (closureStore t g R R') := by
  have hup : ∀ x, ¬ NewUnit t g R R' x → (recordOf R' x).isSome = true →
      (recordOf (closureStore t g R R') x).isSome = true := by
    intro x hx h
    rw [recordOf_closureStore hx]
    exact h
  have hR'c := hadm.usedClosed
  refine ⟨fun a c hc => ?_, fun B c ms hc hms i m hm => ?_⟩
  · obtain ⟨hc', hna⟩ := recordOf_closureStore_down hc
    obtain ⟨hown, hrefs⟩ := hR'c.1 a c hc'
    refine ⟨hup _ ?_ hown, fun i hi x hx => hup _ ?_ (hrefs i hi x hx)⟩
    · intro hu
      obtain ⟨cO, hcO⟩ := Option.isSome_iff_exists.mp hown
      by_cases hoa : Ix.Cert.ownerOf a c = a
      · rw [hoa] at hu
        exact hna hu
      · have hp : IsProj c := isProj_of_ownerOf_ne hoa
        cases hRa : recordOf R a with
        | some c₀ =>
          have hcc : c₀ = c := Option.some.inj ((recordOf_of_loaded hadm.mono hRa).symm.trans hc')
          subst hcc
          obtain ⟨hownR, -⟩ := hR.1 a c₀ hRa
          rw [hu.2.2] at hownR
          cases hownR
        | none =>
          have hnew : New R R' a := ⟨by rw [hc']; rfl, hRa⟩
          obtain ⟨cb, hcb, hconst⟩ := hadm.projMember a c hnew hc' hp
          rw [hcO] at hcb
          have hcc : cO = cb := Option.some.inj hcb
          subst hcc
          rcases hconst with ⟨he, -⟩ | ⟨ms, -, -, hms, -, -⟩
          · exact hoa he.symm
          · exact (newUnit_not_proj_block hform hu hcO).2 ⟨ms, hms⟩
    · intro hu
      cases hRa : recordOf R a with
      | some c₀ =>
        have hcc : c₀ = c := Option.some.inj ((recordOf_of_loaded hadm.mono hRa).symm.trans hc')
        subst hcc
        obtain ⟨-, hrefsR⟩ := hR.1 a c₀ hRa
        have hxR := hrefsR i hi x hx
        rw [hu.2.2] at hxR
        cases hxR
      | none =>
        have hnew : New R R' a := ⟨by rw [hc']; rfl, hRa⟩
        exact hadm.unitsLast a x hnew ⟨c, i, hc', hi, hx⟩ hu.1
  · obtain ⟨hc', -⟩ := recordOf_closureStore_down hc
    obtain ⟨hmem, hctor⟩ := hR'c.2 B c ms hc' hms i m hm
    have hnot : ∀ y p, recordOf R' y = some p → IsProj p → ¬ NewUnit t g R R' y :=
      fun y p hy hp hu => (newUnit_not_proj_block hform hu hy).1 hp
    refine ⟨?_, fun ind hind j hj => ?_⟩
    · rw [recordOf_closureStore (hnot _ _ hmem (memberProjection_isProj B i m))]
      exact hmem
    · have h2 := hctor ind hind j hj
      rw [recordOf_closureStore (hnot _ _ h2 (constructorProjection_isProj B i j))]
      exact h2

theorem closureStore_hashed (hadm : Admits ρ t g R R') :
    EnvSelfHashed (closureStore t g R R') :=
  ⟨fun a lc h => hadm.hashed.1 a lc (closureStore_le.1 a lc h),
    fun a b h => hadm.hashed.2 a b (closureStore_le.2 a b h)⟩

theorem closureStore_committed (hadm : Admits ρ t g R R') :
    AgreesCommitted (closureStore t g R R') :=
  fun p hp lc h => hadm.committed p hp lc (closureStore_le.1 _ lc h)

theorem closureStore_zeroFree (hadm : Admits ρ t g R R') :
    (closureStore t g R R').consts.get? Ix.HostAdmission.Merkle.padding = none ∧
      (closureStore t g R R').blobs.get? Ix.HostAdmission.Merkle.padding = none := by
  refine ⟨?_, ?_⟩
  · cases h : (closureStore t g R R').consts.get? Ix.HostAdmission.Merkle.padding with
    | none => rfl
    | some lc =>
      have h' := closureStore_le.1 _ lc h
      rw [hadm.zeroFree.1] at h'
      cases h'
  · rw [closureStore_blobs]
    exact hadm.zeroFree.2

/-- **A reading over `R'` of an address with no new role-unit record is a reading over the
closure's store.** -/
theorem reads_closureStore
    (hform : ∀ a c, RoleUnitAt t g a → New R R' a → recordOf R' a = some c →
      (∃ d, c.info = .defn d) ∨ ∃ ax, c.info = .axio ax)
    {x : _root_.Address} {ci₀ : Ix.Kernel.ConstantInfo .anon} (hx : ¬ NewUnit t g R R' x)
    (h : Reads t R' x ci₀) : Reads t (closureStore t g R R') x ci₀ := by
  unfold Reads at h ⊢
  refine readsIn_of_agree (fun y c hy hk => ?_) (fun y b hb => ?_) (fun c hc => ?_) h
  · have hny : ¬ NewUnit t g R R' y := by
      intro hu
      rcases hform y c hu.1 hu.2 hy with ⟨d, hd⟩ | ⟨ax, hd⟩ <;>
        rcases hk with ⟨ms, hk⟩ | ⟨p, hk⟩ <;> (rw [hd] at hk; cases hk)
    rw [recordOf_closureStore hny]
    exact hy
  · show (closureStore t g R R').blobs.get? y = some b
    rw [closureStore_blobs]
    exact hb
  · rw [recordOf_closureStore hx]
    exact hc

/-- **What a constant keeps of a record of `R` it keeps over the closure's store.** -/
theorem keptIn_closureStore (hadm : Admits ρ t g R R') {x : _root_.Address}
    {ci : Ix.Kernel.ConstantInfo .anon}
    (h : KeptIn t (recordOf R) (fun y => R.blobs.get? y) x ci) :
    KeptIn t (recordOf (closureStore t g R R')) (fun y => (closureStore t g R R').blobs.get? y)
      x ci := by
  obtain ⟨hax, ci₀, hr, hst⟩ := h
  refine ⟨fun c ax hc hinfo => ?_, ci₀,
    ReadsIn.mono (fun y c hy => recordOf_closureStore_of_R hadm hy)
      (fun y b hb => by
        show (closureStore t g R R').blobs.get? y = some b
        rw [closureStore_blobs]
        exact hadm.monoBlobs y b hb) hr, hst⟩
  obtain ⟨c₀, hc₀, -⟩ := hr
  rw [recordOf_closureStore_of_R hadm hc₀] at hc
  have hcc : c₀ = c := Option.some.inj hc
  rw [← hcc] at hinfo
  exact hax c₀ ax hc₀ hinfo

/-- A reading over `R` is a reading over the closure's store. -/
theorem reads_closureStore_of_R (hadm : Admits ρ t g R R') {x : _root_.Address}
    {ci₀ : Ix.Kernel.ConstantInfo .anon} (h : Reads t R x ci₀) :
    Reads t (closureStore t g R R') x ci₀ :=
  ReadsIn.mono (fun y c hy => recordOf_closureStore_of_R hadm hy)
    (fun y b hb => by
      show (closureStore t g R R').blobs.get? y = some b
      rw [closureStore_blobs]
      exact hadm.monoBlobs y b hb) h

end Store

/-! ## Constant addresses in a store closed under block members -/

section ConstAddr

variable {S : Ixon.Env}

/-- **A constant address is its record's own address, or holds a projection record of the
block.** -/
theorem constAddr_record (hS : UsedClosed S) {A x : _root_.Address} {c : Ixon.Constant}
    (hc : recordOf S A = some c) (hx : ConstAddrOf A c x) :
    (x = A ∧ Standalone c) ∨
      (IsBlock c ∧ ∃ P, recordOf S x = some P ∧ IsProj P ∧ Ix.Cert.ownerOf x P = A) := by
  rcases hx with h | ⟨ms, i, m, hms, hm, hxm⟩
  · exact Or.inl h
  · refine Or.inr ⟨⟨ms, hms⟩, ?_⟩
    obtain ⟨hmem, hctor⟩ := hS.2 A c ms hc hms i m hm
    rcases hxm with hxe | ⟨ind, j, hind, hj, hxe⟩
    · rw [hxe]
      exact ⟨_, hmem, memberProjection_isProj A i m, ownerOf_memberProjection _ A i m⟩
    · rw [hxe]
      exact ⟨_, hctor ind hind j hj, constructorProjection_isProj A i j,
        ownerOf_constructorProjection _ A i j⟩

/-- **Two records of the store with a constant address in common are one record.** -/
theorem constAddr_same (hS : UsedClosed S) {A A' x : _root_.Address} {c c' : Ixon.Constant}
    (hc : recordOf S A = some c) (hc' : recordOf S A' = some c') (hx : ConstAddrOf A c x)
    (hx' : ConstAddrOf A' c' x) : A = A' := by
  rcases constAddr_record hS hc hx with ⟨h1, hs⟩ | ⟨hb, P, hP, hPp, hPo⟩
  · rcases constAddr_record hS hc' hx' with ⟨h1', hs'⟩ | ⟨hb', P', hP', hPp', hPo'⟩
    · exact h1.symm.trans h1'
    · rw [h1, hc] at hP'
      have hcc : c = P' := Option.some.inj hP'
      rw [hcc] at hs
      exact (standalone_not_proj hs hPp').elim
  · rcases constAddr_record hS hc' hx' with ⟨h1', hs'⟩ | ⟨hb', P', hP', hPp', hPo'⟩
    · rw [h1', hc'] at hP
      have hcc : c' = P := Option.some.inj hP
      rw [hcc] at hs'
      exact (standalone_not_proj hs' hPp).elim
    · rw [hP] at hP'
      have hPP : P = P' := Option.some.inj hP'
      rw [← hPP] at hPo'
      exact hPo.symm.trans hPo'

end ConstAddr

end IxVM.Refinement.Binding
