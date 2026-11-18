import IxVMRefinement.FamilyGraph.ProducersGraph

/-! # The family graph's rank from an acyclic relation over the run's store

`FamilyRanked` asks a rank of strict comparisons: the walk's edges (a used reference and a
projection record's block below the record), advice below its block, a block below its family
record and its twins, and, for what a family record or an inner record uses, an owner below the
block or the record. Any relation `E` that contains these comparisons and has no cycle gives such
a rank: the number of addresses of the run's store strictly below an address in `E`
(`belowCount`), which grows strictly along `E` because the store is finite and a relation without
a cycle never puts an address below itself.

* `belowCount`, `belowCount_lt`: the rank and its strictness along `Relation.TransGen E`;
* `RankEdges`: what a relation must contain and that it has no cycle;
* `familyRanked_of_edges`: `FamilyRanked` at `belowCount E` from `RankEdges` and the walk. -/

namespace IxVM.Refinement.Typing

open IxVM.Consistency

set_option linter.unusedVariables false

/-! ## The rank below a relation -/

/-- An address the store holds a record at is one of the store's keys. -/
theorem mem_keys_of_recordOf {E₀ : Ixon.Env} {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf E₀ a = some c) : a ∈ E₀.consts.keys := by
  rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains, Std.HashMap.contains_eq_isSome_getElem?]
  unfold recordOf at h
  rw [Std.HashMap.get?_eq_getElem?] at h
  cases e : E₀.consts[a]? with
  | none => rw [e] at h; cases h
  | some _ => rfl

theorem transGen_trans {E : _root_.Address → _root_.Address → Prop} {a b c : _root_.Address}
    (h₁ : Relation.TransGen E a b) (h₂ : Relation.TransGen E b c) : Relation.TransGen E a c := by
  induction h₂ with
  | single h => exact .tail h₁ h
  | tail _ h ih => exact .tail ih h

/-- The first step of a chain. -/
theorem transGen_head {E : _root_.Address → _root_.Address → Prop} {a c : _root_.Address}
    (h : Relation.TransGen E a c) : ∃ b, E a b := by
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ _ ih => exact ih

theorem countP_lt_of_imp {α : Type} {L : List α} {p q : α → Bool}
    (hqp : ∀ x, q x = true → p x = true) {y : α} (hy : y ∈ L) (hp : p y = true)
    (hq : q y = false) : L.countP q < L.countP p := by
  induction L with
  | nil => cases hy
  | cons x L ih =>
    rw [List.countP_cons, List.countP_cons]
    have hle : L.countP q ≤ L.countP p := List.countP_mono_left fun x _ h => hqp x h
    have hx : (if q x = true then 1 else 0) ≤ (if p x = true then 1 else 0) := by
      by_cases h : q x = true
      · simp [h, hqp x h]
      · simp [h]
    rcases List.mem_cons.mp hy with rfl | hy
    · simp [hq, hp]; omega
    · have := ih hy; omega

open Classical in
/-- **The rank of `y` below the relation `E` over the addresses `S`**: how many addresses of `S`
lie strictly below `y` (`Relation.TransGen E`). -/
noncomputable def belowCount (E : _root_.Address → _root_.Address → Prop)
    (S : List _root_.Address) (y : _root_.Address) : Nat :=
  S.countP fun z => decide (Relation.TransGen E z y)

/-- **The rank grows strictly along the relation** at an address of `S` that is not below
itself. -/
theorem belowCount_lt {E : _root_.Address → _root_.Address → Prop} {S : List _root_.Address}
    {z y : _root_.Address} (h : Relation.TransGen E z y) (hz : z ∈ S)
    (hacyc : ¬ Relation.TransGen E z z) : belowCount E S z < belowCount E S y := by
  unfold belowCount
  refine countP_lt_of_imp (y := z) ?_ hz ?_ ?_
  · intro x hx
    simp only [decide_eq_true_eq] at hx ⊢
    exact transGen_trans hx h
  · simpa using h
  · simpa using hacyc

/-! ## A relation that orders the family graph -/

/-- **A relation that orders the family graph at the choices `K`** (module docstring): it has no
cycle, every address below another holds a record of the run's store, and it puts below each other
a top-walked used reference that is not covered and its user (a covered one needs no rank), a
top-walked projection record's block and the record,
an advice record and its block, a block and its family record where that is checked, a block with
a family record and its twin; and what a family record or an inner record uses is stored,
covered, its own (for a family record also its block's), or owned by a checked unclaimed record
below the block or the inner record. -/
structure RankEdges (K : FamRunCtx) (E : _root_.Address → _root_.Address → Prop) : Prop where
  acyclic : ∀ z, ¬ Relation.TransGen E z z
  source : ∀ z y, E z y → ∃ c, recordOf K.E₀ z = some c
  walkUse : ∀ a x, K.Top a → K.Top x → ¬ Covered K.t x → UsedRef K.E₀ a x → E x a
  walkOwner : ∀ a c, K.Top a → recordOf K.E₀ a = some c → IsProj c → E (Ix.Cert.ownerOf a c) a
  after : ∀ B rb, K.fam B = some rb → Walked K.Top K.Inner rb → E B rb
  advBelow : ∀ B a, K.adv B a → E a B
  twinAfter : ∀ rb' B rb, K.twin rb' = some B → K.fam B = some rb → E B rb'
  famClosed : ∀ B rb x, K.fam B = some rb → UsedRef K.E₀ rb x → NeedOk K.E₀ x →
    StoredAt K.t K.envT x ∨ Covered K.t x ∨
      (∃ cb, recordOf K.E₀ B = some cb ∧ ConstAddrOf B cb x) ∨
      (∃ crb, recordOf K.E₀ rb = some crb ∧ ConstAddrOf rb crb x) ∨
      ∃ D, Walked K.Top K.Inner D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
        Relation.TransGen E D B
  innerClosed : ∀ a x, K.Inner a → UsedRef K.E₀ a x → NeedOk K.E₀ x →
    StoredAt K.t K.envT x ∨ Covered K.t x ∨
      (∃ c, recordOf K.E₀ a = some c ∧ ConstAddrOf a c x) ∨
      ∃ D, Walked K.Top K.Inner D ∧ Unclaimed K.fam D ∧ FamOwns K.E₀ K.fam D x ∧
        Relation.TransGen E D a

/-- **The rank of the family graph from a relation that orders it**: the number of the run's
store's addresses below an address (`belowCount`). The walk gives that a used reference of a
top-walked record is top-walked or covered and that a projection record's block is top-walked. -/
theorem familyRanked_of_edges {K : FamRunCtx} {E : _root_.Address → _root_.Address → Prop}
    {seeds : List _root_.Address} {rank : _root_.Address → Nat}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    (hE : RankEdges K E) : FamilyRanked K (belowCount E K.E₀.consts.keys) := by
  have lt : ∀ {z y}, Relation.TransGen E z y →
      belowCount E K.E₀.consts.keys z < belowCount E K.E₀.consts.keys y := by
    intro z y h
    obtain ⟨b, hb⟩ := transGen_head h
    obtain ⟨c, hc⟩ := hE.source z b hb
    exact belowCount_lt h (mem_keys_of_recordOf hc) (hE.acyclic z)
  have owned : ∀ {x n}, (∃ D, Walked K.Top K.Inner D ∧ Unclaimed K.fam D ∧
      FamOwns K.E₀ K.fam D x ∧ Relation.TransGen E D n) →
      OwnedBelow K.E₀ K.Top K.Inner (belowCount E K.E₀.consts.keys) K.fam
        (belowCount E K.E₀.consts.keys n) x := by
    rintro x n ⟨D, hWD, hU, hown, hD⟩
    exact ⟨D, hWD, hU, lt hD, hown⟩
  refine
    { closed := fun a x hT hu => ?_
      owner := fun a c hT hc hp => ?_
      after := fun B rb h hw => lt (.single (hE.after B rb h hw))
      advBelow := fun B a h => lt (.single (hE.advBelow B a h))
      twinAfter := fun rb' B rb h h' => lt (.single (hE.twinAfter rb' B rb h h'))
      famClosed := fun B rb x h hu hok => ?_
      innerClosed := fun a x h hu hok => ?_ }
  · by_cases hcov : Covered K.t x
    · exact Or.inr hcov
    · rcases hW.closed a x hT hu with ⟨hTx, -⟩ | hcov'
      · exact Or.inl ⟨hTx, lt (.single (hE.walkUse a x hT hTx hcov hu))⟩
      · exact absurd hcov' hcov
  · exact ⟨(hW.owner a c hT hc hp).1, lt (.single (hE.walkOwner a c hT hc hp))⟩
  · rcases hE.famClosed B rb x h hu hok with h1 | h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (owned h1))))
  · rcases hE.innerClosed a x h hu hok with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (owned h1)))

end IxVM.Refinement.Typing
