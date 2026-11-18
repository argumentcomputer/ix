import Aiur.Tiling.PeriodicRows

/-!
# Copy consistency per shard

A shard's copy labels and multiplicities are those of its layout's shadow
system (the physical cells as a v1 system). The shard circuit packs label `n`
into the bus key `copyKey (n + labelOffset k)`, and label ranges of distinct
shards are disjoint, so the coefficient of a shard's packed key is the v1 copy
coefficient of the shadow system (`copyLedger_key`), and the v1 copy argument
(`System.CellsValid.copy`) gives every physical cell the value at its slot's
anchor (`Sharded.consistent`).
-/

namespace Aiur.Tiling.Periodic

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type} [Field F] [DecidableEq F]

/-- The copy label of cell `j` of physical row `p`, as a natural (0 when unlabelled). -/
def labelNat (sys : System F) (p j : Nat) : Nat :=
  match sys.copyKey p j with
  | some (f, i, s) => sys.label f i s
  | none => 0

theorem labelAt_nat (sys : System F) (p j : Nat) : sys.labelAt p j = (labelNat sys p j : F) := by
  unfold System.labelAt labelNat
  rcases sys.copyKey p j with _ | ⟨f, i, s⟩ <;> simp

theorem labelNat_le {sys : System F} (valid : sys.CellsValid) (p j : Nat) :
    labelNat sys p j ≤ sys.keys.length := by
  unfold labelNat
  split
  · rename_i f i s h
    have := sys.label_lt (valid.copyKey_mem h)
    omega
  · omega

theorem shadow_cellsValid {W : Nat} {buses : Buses F} {L : Layout F}
    (ok : ∀ T ∈ L.templates, T.width = W ∧ T.checkPhysical buses = true) : (L.shadow W).CellsValid := by
  refine ⟨fun f hf => ?_⟩
  simp only [Layout.shadow, List.length_map] at hf
  have mem := List.getElem_mem hf
  obtain ⟨w, phys⟩ := ok _ mem
  simp only [Template2.checkPhysical, Bool.and_eq_true, List.all_eq_true] at phys
  refine ⟨by simp [Layout.shadow, Template2.shadow, w], ?_⟩
  intro row hrow cell hcell s hs
  simp only [Layout.shadow, List.getElem_map, Template2.shadow, List.mem_map] at hrow ⊢
  obtain ⟨r, hr, rfl⟩ := hrow
  have := phys.1.1.1.1 r hr cell hcell
  simp only [Option.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  exact (this s hs).1

namespace Sharded

variable (S : Sharded F)

theorem placed_of_place {k p f i r : Nat} (h : ((S.layout k).shadow S.width).places[p]? = some (f, i, r)) :
    ∃ T row, Placed S k p f i r T row := by
  have mem := List.mem_of_getElem? h
  obtain ⟨hf, _, hr⟩ := ((S.layout k).shadow S.width).mem_places.mp mem
  have hf' : f < (S.layout k).templates.length := by simpa [Layout.shadow] using hf
  have hr' : r < ((S.layout k).templates[f]).rows.length := by
    simpa [System.rowCount, Layout.shadow, Template2.shadow, List.getElem?_eq_getElem hf'] using hr
  exact ⟨_, _, h, List.getElem?_eq_getElem hf', List.getElem?_eq_getElem hr'⟩

theorem fixedAt_unplaced {k p : Nat} (h : ((S.layout k).shadow S.width).places[p]? = none) (c : Nat) :
    S.fixedAt (S.layout k) p c = 0 := by
  simp [fixedAt, h]

theorem assign_label {k : Nat} {main : Nat → Nat → F} (p : Nat) {j : Nat} (hj : j < S.width) :
    S.assign k main p (S.width + labelCol S.width j) = ((S.layout k).shadow S.width).labelAt p j := by
  cases h : ((S.layout k).shadow S.width).places[p]? with
  | none =>
      rw [System.labelAt_unplaced _ h]
      simp [assign, S.fixedAt_unplaced h]
  | some x =>
      obtain ⟨f, i, r⟩ := x
      obtain ⟨T, row, placed⟩ := S.placed_of_place h
      exact placed.label hj

theorem assign_mult {k : Nat} {main : Nat → Nat → F} (p : Nat) {j : Nat} (hj : j < S.width) :
    S.assign k main p (S.width + multCol S.width j) = ((S.layout k).shadow S.width).multAt p j := by
  cases h : ((S.layout k).shadow S.width).places[p]? with
  | none =>
      rw [System.multAt_unplaced _ h]
      simp [assign, S.fixedAt_unplaced h]
  | some x =>
      obtain ⟨f, i, r⟩ := x
      obtain ⟨T, row, placed⟩ := S.placed_of_place h
      exact placed.mult hj

/-- The copy lookups of shard `k` over its `H` rows. -/
noncomputable def copyLedger (k H : Nat) (main : Nat → Nat → F) : Ledger F :=
  ∑ p ∈ Finset.range H, ∑ j ∈ Finset.range S.width,
    (copyLookup S.width (S.labelOffset k) j).entry (S.assign k main p)

theorem copyLedger_apply (k H : Nat) (main : Nat → Nat → F) (t : List F) :
    S.copyLedger k H main t = ∑ p ∈ Finset.range H, ∑ j ∈ Finset.range S.width,
      if [((copyKey (labelNat ((S.layout k).shadow S.width) p j + S.labelOffset k) : Nat) : F), main p j] = t
      then ((S.layout k).shadow S.width).multAt p j else 0 := by
  simp only [copyLedger, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro j hj
  have hj := Finset.mem_range.mp hj
  rw [copyLookup_entry _ _ _ _ (labelNat ((S.layout k).shadow S.width) p j)
    (by rw [S.assign_label p hj, labelAt_nat]), S.assign_mult p hj,
    Sharded.assign_main hj, Finsupp.single_apply]

/-- The coefficient of shard `k`'s packed key of label `n` is the shadow
system's copy coefficient of label `n`. -/
theorem copyLedger_key {k H : Nat} {main : Nat → Nat → F} {bound : Nat} (small : SmallCast F bound)
    (valid : ((S.layout k).shadow S.width).CellsValid)
    (hb : copyKey (((S.layout k).shadow S.width).keys.length + S.labelOffset k) < bound)
    {n : Nat} (hn : n ≤ ((S.layout k).shadow S.width).keys.length) (v : F) :
    S.copyLedger k H main [((copyKey (n + S.labelOffset k) : Nat) : F), v] =
      ((S.layout k).shadow S.width).copyCoefficient H main (n : F) v := by
  rw [copyLedger_apply, System.copyCoefficient]
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro j _
  have le := labelNat_le valid p j
  have keysBound : ((S.layout k).shadow S.width).keys.length < bound := by
    simp only [copyKey, COPY] at hb; omega
  congr 1
  apply propext
  rw [labelAt_nat]
  simp only [List.cons.injEq, and_true]
  constructor
  · rintro ⟨e, rfl⟩
    have := copyKey_inj small (by simp only [copyKey, COPY] at hb ⊢; omega)
      (by simp only [copyKey, COPY] at hb ⊢; omega) e
    exact ⟨by rw [show labelNat _ p j = n by omega], rfl⟩
  · rintro ⟨e, rfl⟩
    have := small.inj (by omega) (by omega) e
    rw [this]
    exact ⟨rfl, rfl⟩

/-- **Per-shard copy consistency.** If every packed key of shard `k`'s labels
balances on the shard's copy lookups, every physical cell of a slot holds the
value at the slot's anchor. -/
theorem consistent {k H : Nat} {main : Nat → Nat → F} {bound : Nat} (small : SmallCast F bound)
    (valid : ((S.layout k).shadow S.width).CellsValid)
    (smallShadow : SmallCast F ((S.layout k).shadow S.width).bound)
    (hb : copyKey (((S.layout k).shadow S.width).keys.length + S.labelOffset k) < bound)
    (tall : ((S.layout k).shadow S.width).places.length ≤ H)
    (balanced : ∀ n, n ≤ ((S.layout k).shadow S.width).keys.length → ∀ v,
      S.copyLedger k H main [((copyKey (n + S.labelOffset k) : Nat) : F), v] = 0)
    {f i r j s : Nat} (place : (f, i, r) ∈ ((S.layout k).shadow S.width).places) {T : Template F}
    (hT : ((S.layout k).shadow S.width).templates[f]? = some T) (hj : j < S.width)
    (cell : T.cell r j = some s) :
    main (((S.layout k).shadow S.width).row f i r) j = ((S.layout k).shadow S.width).slotValue main f i s := by
  obtain ⟨ra, ja, anchor, eq⟩ := valid.copy smallShadow tall (fun key hk v => by
      have lt := ((S.layout k).shadow S.width).label_lt (f := key.1) (i := key.2.1) (s := key.2.2) hk
      rw [← S.copyLedger_key small valid hb (by omega) v]
      exact balanced _ (by omega) v) place hT hj cell
  have lt : s < T.slots.length := by
    obtain ⟨hf, _, _⟩ := ((S.layout k).shadow S.width).mem_places.mp place
    have := (valid.templates f hf).2
    rw [show ((S.layout k).shadow S.width).templates[f] = T by
      have := List.getElem?_eq_getElem hf; rw [hT] at this; exact (Option.some.inj this).symm] at this
    obtain ⟨row, hrow, hcell⟩ := Template.cell_some cell
    exact this row (List.mem_of_getElem? hrow) _ (List.mem_of_getElem? hcell) s rfl
  have ne : s ≠ T.idVar := by simp [Template.idVar]; omega
  simp [System.slotValue, hT, anchor, eq, ne]

end Sharded

end Aiur.Tiling.Periodic
