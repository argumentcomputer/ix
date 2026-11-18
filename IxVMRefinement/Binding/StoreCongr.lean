import IxVMRefinement.Binding.Defs

/-! # The boundary invariant depends on the store only through its entries

Every field of `Bnd X t G R env` reads the store `R` only through `R.consts.get?`,
`R.blobs.get?` and `recordOf R` (itself a function of `R.consts.get?`). So two stores with the
same entries, at every address, carry the same invariant, given the extra clause's congruence.

* `recordOf_storeCongr`, `store_subst`: the records and blobs of two such stores are equal as
  functions, so any property of them transfers.
* `recordsFor_storeCongr`, `envSelfHashed_storeCongr`, `usedClosed_storeCongr`,
  `readingOf_storeCongr`, `tableShape_storeCongr`, `bfacts_storeCongr`: the pieces.
* `bnd_storeCongr`: the boundary invariant.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing

section StoreCongr

variable {R R' : Ixon.Env}

/-- **`recordOf` reads a store only through `consts.get?`.** -/
theorem recordOf_storeCongr (hc : ∀ a, R.consts.get? a = R'.consts.get? a) :
    recordOf R = recordOf R' := by
  funext a
  unfold recordOf
  rw [hc a]

/-- **A property of a store's records and blobs holds of a store with the same entries.** -/
theorem store_subst (hc : ∀ a, R.consts.get? a = R'.consts.get? a)
    (hb : ∀ a, R.blobs.get? a = R'.blobs.get? a)
    (P : (_root_.Address → Option Ixon.Constant) → (_root_.Address → Option ByteArray) → Prop)
    (h : P (recordOf R) (fun x => R.blobs.get? x)) :
    P (recordOf R') (fun x => R'.blobs.get? x) :=
  Eq.subst (motive := fun s => P s (fun x => R'.blobs.get? x)) (recordOf_storeCongr hc)
    (Eq.subst (motive := fun b => P (recordOf R) b)
      (show (fun x => R.blobs.get? x) = (fun x => R'.blobs.get? x) from funext hb) h)

/-- **A record store for `R` is one for `R'`.** -/
theorem recordsFor_storeCongr (hc : ∀ a, R.consts.get? a = R'.consts.get? a)
    (hb : ∀ a, R.blobs.get? a = R'.blobs.get? a) {E : Ixon.Env} (h : RecordsFor R E) :
    RecordsFor R' E := by
  unfold RecordsFor at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun a c ha => h2 a c ?_, fun x b hx => h3 x b ?_, h4⟩
  · rw [recordOf_storeCongr hc]
    exact ha
  · rw [hb x]
    exact hx

theorem envSelfHashed_storeCongr (hc : ∀ a, R.consts.get? a = R'.consts.get? a)
    (hb : ∀ a, R.blobs.get? a = R'.blobs.get? a) (h : EnvSelfHashed R) : EnvSelfHashed R' :=
  ⟨fun a lc ha => h.1 a lc ((hc a).trans ha), fun a b ha => h.2 a b ((hb a).trans ha)⟩

theorem usedClosed_storeCongr (hc : ∀ a, R.consts.get? a = R'.consts.get? a)
    (h : UsedClosed R) : UsedClosed R' := by
  unfold UsedClosed at h ⊢
  rw [recordOf_storeCongr hc] at h
  exact h

theorem readingOf_storeCongr {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    (hc : ∀ a, R.consts.get? a = R'.consts.get? a)
    (hb : ∀ a, R.blobs.get? a = R'.blobs.get? a) (h : ReadingOf t R env) :
    ReadingOf t R' env where
  nodup := h.nodup
  provenance := store_subst hc hb
    (fun s b => ∀ ci ∈ (claimedEnv env).consts,
      (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨ ∃ a, KeptIn t s b a ci)
    h.provenance
  stored := store_subst hc hb
    (fun s b => ∀ a, (∃ ci₀, ReadsIn t s b a ci₀) →
      ∃ ci, env.find? (keyOf t a) = some ci ∧
        (PinnedBasis ci ∨ ∃ ci₀, ReadsIn t s b a ci₀ ∧ StoredAs ci ci₀))
    h.stored

/-- **The public shape depends on the store only through its entries.** -/
theorem tableShape_storeCongr {t : Ix.Kernel.RoleTable} {G : Nat → Prop}
    {env : Ix.Kernel.Env .anon}
    (hc : ∀ a, R.consts.get? a = R'.consts.get? a)
    (hb : ∀ a, R.blobs.get? a = R'.blobs.get? a) (h : TableShape.{u} t G R env) :
    TableShape.{u} t G R' env where
  needsClosed := h.needsClosed
  bound := h.bound
  prelude := h.prelude
  literals := h.literals
  hashed := envSelfHashed_storeCongr hc hb h.hashed
  usedClosed := usedClosed_storeCongr hc h.usedClosed
  committed := fun p hp lc h' => h.committed p hp lc ((hc p.1).trans h')
  zeroFree := ⟨(hc _).symm.trans h.zeroFree.1, (hb _).symm.trans h.zeroFree.2⟩
  kept := fun g r a hg hr hk ha => store_subst hc hb
    (fun s b => ∃ ci, env.find? (Ix.Kernel.Key.role r) = some ci ∧
      (PinnedBasis ci ∨ KeptIn t s b a ci))
    (h.kept g r a hg hr hk ha)
  reading := readingOf_storeCongr hc hb h.reading
  pins := h.pins
  preludeKept := fun g r a hg hr hp ha => store_subst hc hb
    (fun s b => ∃ ci, env.find? (Ix.Kernel.Key.role r) = some ci ∧
      (PinnedBasis ci ∨ KeptIn t s b a ci))
    (h.preludeKept g r a hg hr hp ha)
  model := h.model

/-- **The internal part depends on the store only through its entries**: every field reads the
store through `RecordsFor`. -/
theorem bfacts_storeCongr {t : Ix.Kernel.RoleTable} {G : Nat → Prop}
    {env : Ix.Kernel.Env .anon}
    (hc : ∀ a, R.consts.get? a = R'.consts.get? a)
    (hb : ∀ a, R.blobs.get? a = R'.blobs.get? a) (h : BFacts.{u} t G R env) :
    BFacts.{u} t G R' env where
  inv := fun E hE =>
    h.inv E (recordsFor_storeCongr (fun a => (hc a).symm) (fun a => (hb a).symm) hE)
  whole := fun E hE =>
    h.whole E (recordsFor_storeCongr (fun a => (hc a).symm) (fun a => (hb a).symm) hE)
  opsPinned := h.opsPinned
  opsAdmitted := h.opsAdmitted
  shapes := h.shapes

end StoreCongr

/-- **The boundary invariant depends on the store only through its entries**, given that the
extra clause does. -/
theorem bnd_storeCongr
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R R' : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (hc : ∀ a, R.consts.get? a = R'.consts.get? a)
    (hb : ∀ a, R.blobs.get? a = R'.blobs.get? a) (hX : X t G R env → X t G R' env)
    (h : Bnd.{u} X t G R env) : Bnd.{u} X t G R' env :=
  ⟨tableShape_storeCongr hc hb h.shape, bfacts_storeCongr hc hb h.facts, hX h.extra⟩

end IxVM.Refinement.Binding
