import IxAIRefine.Fixed.StepSpecs

/-! # The magnitudes of one SGD step

`step_spec` needs every value a step rounds or sign-tests to be below `2^55` in magnitude
(`StepBounds`). `stepBounds_of_weights` derives that from three small bounds:

* every parameter is below `2^13` (`ModelW`), which `Fixed::upd` checks of every parameter a
  step returns, so `step_spec` re-establishes it for the next step;
* every input and target is at most `2^12` (`AllLe 4096`);
* `|lr| ≤ 2^8`.

Every intermediate integer of the step is a short sum of products of bounded numbers, and
`⌊s / 256⌋` is at most `M` when `|s| ≤ 256 M` (`ediv256_le`):

| value | bound |
|---|---|
| `w1 · x` (8 terms) | `2^28` |
| hidden pre-activation `z`, activation `h` | `Z = 2^20 + 2^13` |
| `w2 · h` (16 terms) | `2^17 Z = 256 · 2^9 Z` |
| output `o`, error `dout` | `D = 2^9 Z + 2^13 + 2^12` |
| `w2ᵀ · dout` (11 terms) | `11 · 2^13 D = 256 · 352 D` |
| `dz` | `352 D` |
| `dz · x`, `dout · h` (20 terms each) and `lr · g` | below `1.6 · 10^16 < 2^55` |

`step_dims` shows that a step keeps the model's shape. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace IxAIStep.Fixed.Specs

open IxAICore (Fx Model)

/-! ## Bounded lists -/

/-- Every entry of `l` is at most `B` in magnitude. -/
def AllLe (B : ℤ) (l : List Fx) : Prop := ∀ a ∈ l, |a.raw| ≤ B

theorem allLe_of_vecW {l : List Fx} (h : VecW l) : AllLe 8192 l :=
  fun a ha => (h a ha).le.trans (by norm_num)

theorem mem_zipWith' {α β γ : Type} {f : α → β → γ} :
    ∀ {l1 : List α} {l2 : List β} {c : γ}, c ∈ List.zipWith f l1 l2 →
      ∃ a ∈ l1, ∃ b ∈ l2, c = f a b
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l1, b :: l2, c, h => by
    rw [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, by simp, b, by simp, rfl⟩
    · obtain ⟨x, hx, y, hy, rfl⟩ := mem_zipWith' h
      exact ⟨x, by simp [hx], y, by simp [hy], rfl⟩

/-- An exact dot product is at most the length times the product of the entries' bounds. -/
theorem dotRaw_le {A B : ℤ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ (as bs : List Fx), AllLe A as → AllLe B bs →
      |Fx.dotRaw as bs| ≤ as.length * (A * B)
  | [], bs, _, _ => by
    have e : Fx.dotRaw [] bs = 0 := by cases bs <;> rfl
    rw [e, abs_zero]
    simp
  | a :: as, [], _, _ => by
    have e : Fx.dotRaw (a :: as) [] = 0 := rfl
    rw [e, abs_zero]
    exact mul_nonneg (by positivity) (mul_nonneg hA hB)
  | a :: as, b :: bs, ha, hb => by
    have h1 : |a.raw * b.raw| ≤ A * B := by
      rw [abs_mul]
      exact mul_le_mul (ha a (by simp)) (hb b (by simp)) (abs_nonneg _) hA
    have h2 := dotRaw_le hA hB as bs (fun x hx => ha x (by simp [hx]))
      (fun x hx => hb x (by simp [hx]))
    rw [dotRaw_cons]
    calc |a.raw * b.raw + Fx.dotRaw as bs| ≤ |a.raw * b.raw| + |Fx.dotRaw as bs| :=
          abs_add_le _ _
      _ ≤ A * B + as.length * (A * B) := add_le_add h1 h2
      _ = ((a :: as).length : ℤ) * (A * B) := by push_cast [List.length_cons]; ring

/-- An exact sum is at most the length times the entries' bound. -/
theorem sumRaw_le {A : ℤ} (hA : 0 ≤ A) :
    ∀ (as : List Fx), AllLe A as → |Fx.sumRaw as| ≤ as.length * A
  | [], _ => by
    rw [sumRaw_nil, abs_zero]
    simp
  | a :: as, ha => by
    have h1 := ha a (by simp)
    have h2 := sumRaw_le hA as (fun x hx => ha x (by simp [hx]))
    rw [sumRaw_cons]
    calc |a.raw + Fx.sumRaw as| ≤ |a.raw| + |Fx.sumRaw as| := abs_add_le _ _
      _ ≤ A + as.length * A := add_le_add h1 h2
      _ = ((a :: as).length : ℤ) * A := by push_cast [List.length_cons]; ring

theorem ediv256_le {x M : ℤ} (h : |x| ≤ 256 * M) : |x / 256| ≤ M := by
  rw [abs_le] at h ⊢
  constructor <;> omega

/-- Rounding divides the bound by `256`. -/
theorem dot_le {as bs : List Fx} {M : ℤ} (h : |Fx.dotRaw as bs| ≤ 256 * M) :
    |(Fx.dot as bs).raw| ≤ M := by
  simp only [IxAICore.Fx.dot, shr8_eq]
  exact ediv256_le h

theorem lr_mul_le {lr : Fx} {y Y : ℤ} (hlr : |lr.raw| ≤ 256) (hy : |y| ≤ Y) :
    |lr.raw * y| ≤ 256 * Y := by
  rw [abs_mul]
  exact mul_le_mul hlr hy (abs_nonneg _) (by norm_num)

theorem relu_le (a : Fx) : |(Fx.relu a).raw| ≤ |a.raw| := by
  unfold IxAICore.Fx.relu
  split
  · exact le_refl _
  · simp [IxAICore.Fx.zero]

theorem relu_map_le {B : ℤ} {l : List Fx} (h : AllLe B l) : AllLe B (l.map Fx.relu) := by
  intro a ha
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
  exact (relu_le z).trans (h z hz)

/-- `transposeN` keeps a bound on the entries: every entry of a column is an entry of a row or
zero. -/
theorem transposeN_le {B : ℤ} (hB : 0 ≤ B) :
    ∀ (n : ℕ) (rows : List (List Fx)), (∀ r ∈ rows, AllLe B r) →
      ∀ c ∈ IxAICore.transposeN n rows, AllLe B c
  | 0, _, _, c, hc => by first | cases hc | simp [IxAICore.transposeN] at hc
  | n + 1, rows, h, c, hc => by
    rcases List.mem_cons.mp hc with rfl | hc
    · intro a ha
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
      cases r with
      | nil => simpa [IxAICore.Fx.zero] using hB
      | cons x xs => exact h _ hr x (by simp)
    · refine transposeN_le hB n (rows.map (·.tail)) ?_ c hc
      intro r hr a ha
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      exact h r' hr' a (List.mem_of_mem_tail ha)

/-! ## One example -/

/-- The hidden layer: `|w1 · x| ≤ 2^28` and `|z| ≤ 2^20 + 2^13`. -/
theorem hidden_le {w1 : List (List Fx)} {b1 x : List Fx}
    (hw : ∀ row ∈ w1, row.length = 8) (hwb : ∀ row ∈ w1, AllLe 8192 row) (hb : AllLe 8192 b1)
    (hx : AllLe 4096 x) :
    (∀ row ∈ w1, |Fx.dotRaw row x| ≤ 268435456) ∧ AllLe 1056768 (hiddenZ w1 b1 x) := by
  have hd : ∀ row ∈ w1, |Fx.dotRaw row x| ≤ 268435456 := by
    intro row hr
    have h := dotRaw_le (by norm_num) (by norm_num) row x (hwb row hr) hx
    rw [hw row hr] at h
    exact h.trans (by norm_num)
  refine ⟨hd, ?_⟩
  intro z hz
  obtain ⟨row, hr, b, hb', rfl⟩ := mem_zipWith' hz
  have h1 : |(Fx.dot row x).raw| ≤ 1048576 := dot_le ((hd row hr).trans (by norm_num))
  have h2 := hb b hb'
  show |(Fx.dot row x).raw + b.raw| ≤ 1056768
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith

/-- The outputs and errors: `|w2 · h| ≤ 2^17 Z` and `|dout| ≤ D`. -/
theorem dout_le {w2 : List (List Fx)} {b2 hv t : List Fx}
    (hw : ∀ row ∈ w2, row.length = 16) (hwb : ∀ row ∈ w2, AllLe 8192 row) (hb : AllLe 8192 b2)
    (hh : AllLe 1056768 hv) (ht : AllLe 4096 t) :
    (∀ row ∈ w2, |Fx.dotRaw row hv| ≤ 138512695296) ∧
      AllLe 541077504 (List.zipWith Fx.sub (outputsOf w2 b2 hv) t) := by
  have hd : ∀ row ∈ w2, |Fx.dotRaw row hv| ≤ 138512695296 := by
    intro row hr
    have h := dotRaw_le (by norm_num) (by norm_num) row hv (hwb row hr) hh
    rw [hw row hr] at h
    exact h.trans (by norm_num)
  refine ⟨hd, ?_⟩
  intro d hd'
  obtain ⟨o, ho, tt, htt, rfl⟩ := mem_zipWith' hd'
  obtain ⟨row, hr, b, hb', rfl⟩ := mem_zipWith' ho
  have h1 : |(Fx.dot row hv).raw| ≤ 541065216 := dot_le ((hd row hr).trans (by norm_num))
  have h2 := hb b hb'
  have h3 := ht tt htt
  show |(Fx.dot row hv).raw + b.raw - tt.raw| ≤ 541077504
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith

/-- The hidden errors: `|w2ᵀ · dout| ≤ 256 · 352 D` and `|dz| ≤ 352 D`. -/
theorem dz_le {w2T : List (List Fx)} {z dout : List Fx}
    (hT : ∀ c ∈ w2T, c.length = 11) (hTb : ∀ c ∈ w2T, AllLe 8192 c)
    (hd : AllLe 541077504 dout) :
    (∀ c ∈ w2T, |Fx.dotRaw c dout| ≤ 48757576040448) ∧
      AllLe 190459281408
        (List.zipWith (fun zj col => if Fx.pos zj then Fx.dot col dout else Fx.zero) z w2T) := by
  have hd3 : ∀ c ∈ w2T, |Fx.dotRaw c dout| ≤ 48757576040448 := by
    intro c hc
    have h := dotRaw_le (by norm_num) (by norm_num) c dout (hTb c hc) hd
    rw [hT c hc] at h
    exact h.trans (by norm_num)
  refine ⟨hd3, ?_⟩
  intro a ha
  obtain ⟨zj, -, c, hc, rfl⟩ := mem_zipWith' ha
  show |(if Fx.pos zj then Fx.dot c dout else Fx.zero).raw| ≤ 190459281408
  split
  · exact dot_le ((hd3 c hc).trans (by norm_num))
  · norm_num [IxAICore.Fx.zero]

/-- **One example's bounds**: `DeltaBounds`, and the bounds of the example's `h`, `dout` and
`dz`, which the update reads. -/
theorem delta_le {m : Model} {w2T : List (List Fx)} {x t : List Fx}
    (hw1r : ∀ row ∈ m.w1, row.length = 8) (hw2r : ∀ row ∈ m.w2, row.length = 16)
    (hT : ∀ c ∈ w2T, c.length = 11) (hTb : ∀ c ∈ w2T, AllLe 8192 c)
    (hm : ModelW m) (hx : AllLe 4096 x) (ht : AllLe 4096 t) :
    DeltaBounds m w2T x t ∧ AllLe 1056768 (m.delta w2T x t).h ∧
      AllLe 541077504 (m.delta w2T x t).dout ∧ AllLe 190459281408 (m.delta w2T x t).dz := by
  obtain ⟨hm1, hm2, hm3, hm4⟩ := hm
  have hw1b : ∀ row ∈ m.w1, AllLe 8192 row := fun row hr => allLe_of_vecW (hm1 row hr)
  have hw2b : ∀ row ∈ m.w2, AllLe 8192 row := fun row hr => allLe_of_vecW (hm3 row hr)
  obtain ⟨d1, hz⟩ := hidden_le hw1r hw1b (allLe_of_vecW hm2) hx
  have hh := relu_map_le hz
  obtain ⟨d2, hdo⟩ := dout_le hw2r hw2b (allLe_of_vecW hm4) hh ht
  obtain ⟨d3, hdz⟩ := dz_le (z := hiddenZ m.w1 m.b1 x) hT hTb hdo
  exact ⟨⟨fun row hr => lt_of_le_of_lt (d1 row hr) (by norm_num),
    fun z hz' => lt_of_le_of_lt (hz z hz') (by norm_num),
    fun row hr => lt_of_le_of_lt (d2 row hr) (by norm_num),
    fun c hc => lt_of_le_of_lt (d3 c hc) (by norm_num)⟩, hh, hdo, hdz⟩

/-! ## One step -/

/-- **Small parameters and data keep one step below `2^55`.** With every parameter below
`2^13`, every input and target at most `2^12` and `|lr| ≤ 2^8`, every value the step rounds or
sign-tests is below `2^55` in magnitude. -/
theorem stepBounds_of_weights {lr : Fx} {m : Model} {batch : List (List Fx × List Fx)}
    (hw1r : ∀ row ∈ m.w1, row.length = 8) (hw2 : m.w2.length = 11)
    (hw2r : ∀ row ∈ m.w2, row.length = 16) (hn : batch.length = 20) (hm : ModelW m)
    (hx : ∀ p ∈ batch, AllLe 4096 p.1 ∧ AllLe 4096 p.2) (hlr : |lr.raw| ≤ 256) :
    StepBounds lr m batch := by
  have hm' := hm
  obtain ⟨hm1, hm2, hm3, hm4⟩ := hm'
  have hT : ∀ c ∈ w2TOf m, c.length = 11 :=
    fun c hc => (col_length_transposeN _ _ c hc).trans hw2
  have hTb : ∀ c ∈ w2TOf m, AllLe 8192 c :=
    transposeN_le (by norm_num) _ _ (fun row hr => allLe_of_vecW (hm3 row hr))
  have hds : ∀ d ∈ deltasOf m (w2TOf m) batch,
      AllLe 1056768 d.h ∧ AllLe 541077504 d.dout ∧ AllLe 190459281408 d.dz ∧ AllLe 4096 d.x := by
    intro d hd
    obtain ⟨⟨x, t⟩, hp, rfl⟩ := List.mem_map.mp hd
    obtain ⟨-, h1, h2, h3⟩ := delta_le hw1r hw2r hT hTb hm (hx _ hp).1 (hx _ hp).2
    exact ⟨h1, h2, h3, (hx _ hp).1⟩
  have hlen : (deltasOf m (w2TOf m) batch).length = 20 := by simp [deltasOf, hn]
  have rows_le : ∀ {B : ℤ} (f : IxAICore.Delta → List Fx), 0 ≤ B →
      (∀ d ∈ deltasOf m (w2TOf m) batch, AllLe B (f d)) → ∀ n : ℕ,
      ∀ c ∈ IxAICore.transposeN n ((deltasOf m (w2TOf m) batch).map f),
        AllLe B c ∧ c.length = 20 := by
    intro B f hB hf n c hc
    refine ⟨transposeN_le hB n _ ?_ c hc, ?_⟩
    · intro r hr
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hr
      exact hf d hd
    · rw [col_length_transposeN _ _ c hc, List.length_map, hlen]
  have hdzT := rows_le (·.dz) (by norm_num) (fun d hd => (hds d hd).2.2.1) m.b1.length
  have hxT := rows_le (·.x) (by norm_num) (fun d hd => (hds d hd).2.2.2)
    (IxAICore.getD m.w1 0 []).length
  have hhT := rows_le (·.h) (by norm_num) (fun d hd => (hds d hd).1) m.b1.length
  have hoT := rows_le (·.dout) (by norm_num) (fun d hd => (hds d hd).2.1) m.b2.length
  refine ⟨fun p hp => (delta_le hw1r hw2r hT hTb hm (hx p hp).1 (hx p hp).2).1, ?_, ?_, ?_, ?_⟩
  · intro d hd c hc
    obtain ⟨hdb, hdl⟩ := hdzT d hd
    obtain ⟨hcb, -⟩ := hxT c hc
    have h := dotRaw_le (by norm_num) (by norm_num) d c hdb hcb
    rw [hdl] at h
    have h' : |Fx.dotRaw d c| ≤ 256 * 60946970050560 := h.trans (by norm_num)
    exact ⟨lt_of_le_of_lt h' (by norm_num),
      lt_of_le_of_lt (lr_mul_le hlr (dot_le h')) (by norm_num)⟩
  · intro d hd
    obtain ⟨hdb, hdl⟩ := hdzT d hd
    have h := sumRaw_le (by norm_num) d hdb
    rw [hdl] at h
    exact lt_of_le_of_lt (lr_mul_le (y := (Fx.sum d).raw) hlr h) (by norm_num)
  · intro d hd c hc
    obtain ⟨hdb, hdl⟩ := hoT d hd
    obtain ⟨hcb, -⟩ := hhT c hc
    have h := dotRaw_le (by norm_num) (by norm_num) d c hdb hcb
    rw [hdl] at h
    have h' : |Fx.dotRaw d c| ≤ 256 * 44671358730240 := h.trans (by norm_num)
    exact ⟨lt_of_le_of_lt h' (by norm_num),
      lt_of_le_of_lt (lr_mul_le hlr (dot_le h')) (by norm_num)⟩
  · intro d hd
    obtain ⟨hdb, hdl⟩ := hoT d hd
    have h := sumRaw_le (by norm_num) d hdb
    rw [hdl] at h
    exact lt_of_le_of_lt (lr_mul_le (y := (Fx.sum d).raw) hlr h) (by norm_num)

/-- **A step keeps the model's shape.** -/
theorem step_dims {lr : Fx} {m : Model} {batch : List (List Fx × List Fx)}
    (hw1 : m.w1.length = 16) (hw1r : ∀ row ∈ m.w1, row.length = 8) (hb1 : m.b1.length = 16)
    (hw2 : m.w2.length = 11) (hw2r : ∀ row ∈ m.w2, row.length = 16) (hb2 : m.b2.length = 11)
    (hn : batch.length = 20) :
    (m.step lr batch).w1.length = 16 ∧ (∀ row ∈ (m.step lr batch).w1, row.length = 8) ∧
      (m.step lr batch).b1.length = 16 ∧ (m.step lr batch).w2.length = 11 ∧
      (∀ row ∈ (m.step lr batch).w2, row.length = 16) ∧ (m.step lr batch).b2.length = 11 := by
  have hne : batch.isEmpty = false := by
    cases batch with
    | nil => simp at hn
    | cons _ _ => rfl
  have hI : (IxAICore.getD m.w1 0 []).length = 8 := by
    cases hm : m.w1 with
    | nil => rw [hm] at hw1; simp at hw1
    | cons row rows => exact hw1r row (by rw [hm]; simp)
  rw [step_of_ne hne]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_zipWith, hw1, dzTOf, length_transposeN, hb1, min_self]
  · intro row hr
    obtain ⟨r, hr', d, -, rfl⟩ := mem_zipWith' hr
    simp only [updRow, List.length_zipWith, hw1r r hr', xTOf, length_transposeN, hI, min_self]
  · simp only [updBias, List.length_zipWith, hb1, dzTOf, length_transposeN, min_self]
  · simp only [List.length_zipWith, hw2, doutTOf, length_transposeN, hb2, min_self]
  · intro row hr
    obtain ⟨r, hr', d, -, rfl⟩ := mem_zipWith' hr
    simp only [updRow, List.length_zipWith, hw2r r hr', hTOf, length_transposeN, hb1, min_self]
  · simp only [updBias, List.length_zipWith, hb2, doutTOf, length_transposeN, min_self]

end IxAIStep.Fixed.Specs
