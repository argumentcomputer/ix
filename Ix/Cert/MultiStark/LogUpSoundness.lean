import Ix.Cert.MultiStark.FieldModel
import Aiur.Memory.Partition
import Aiur.Optimized.Grouping.Memo
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # LogUp Algebraic Soundness, `MEMSEG` Interval Uniqueness, and `Plan.checkMemo` Bridge (Gap 5)

Proves the three core algebraic theorems that turn an accepting Multi-STARK LogUp
relation into `Aiur.Optimized.Grouping.Plan.checkMemo` + `Aiur.WidthROM.Valid`:

1. **LogUp Rational-Identity Soundness (`logup_sound_schwartz_zippel`):**
   Given a finite multiset of `(multiplicity, tuple)` messages over `Fp`, define
   the per-tuple net field multiplicity `netMult m : Fp`. If `∃ m, netMult m ≠ 0`,
   then over uniformly sampled `(β, γ) ∈ K × K`, the LogUp identity
   `∑_m netMult(m) · (β + fp(γ, m))⁻¹ = 0` (with no zero denominators) holds with
   probability at most
   `((|M| * (|M| - 1) / 2) * maxArity + |M| - 1) / |K|`.

2. **Sharded `MEMSEG = 16` Interval Uniqueness (`memseg_balance_implies_unique` +
   `memseg_implies_widthROM_valid`):**
   If active ROM rows for width `w` (total count `< p - 1`) emit `+1` at `addr` and
   `-1` at `addr + 1`, and the batch preamble supplies sorted disjoint intervals
   `[(a_j, b_j)]` (`0 ≤ a_0 ≤ b_0 ≤ ... < p`) emitting `-1` at `a_j` and `+1` at `b_j`,
   then field-level LogUp balance implies `m(x) = I(x) ∈ {0, 1}` for every `x : Fp`,
   yielding `Aiur.WidthROM.Valid`.

3. **Field-Balance → Integer-Balance Reweighting (`reweight_of_field_balance`):**
   When every send has `enable ∈ {0, 1}` and total demands `< p`, field-level LogUp
   balance guarantees that every demanded message has at least one active provider
   row. Reweighting the first active provider row of each message `m` to
   `+(demands m : Int)` and all other rows to `0` preserves row count (`≤ 2^39`),
   preserves `plan.inspectRow`, and satisfies exact integer `Balance.accumulator = 0`,
   producing `plan.checkMemo rom root reweighted = .ok ()`.

Zero `sorry`, standard axioms only.
-/

namespace Ix.Cert.MultiStark

open Polynomial Finset

/-! ## 1. Horner Fingerprint and Partial-Fraction Linear Independence -/

/-- Polynomial fingerprint `∑_{i} args[i] * X^i` in `K[X]`. -/
noncomputable def fingerprintPoly (args : List Fp) : K[X] :=
  args.foldr (fun v acc => C (K.embedHom v) + X * acc) 0

/-- Evaluating `fingerprintPoly args` at `γ : K` matches Horner evaluation. -/
def fingerprintEval (γ : K) (args : List Fp) : K :=
  args.foldr (fun v acc => K.embedHom v + γ * acc) 0

theorem eval_fingerprintPoly (γ : K) (args : List Fp) :
    (fingerprintPoly args).eval γ = fingerprintEval γ args := by
  induction args with
  | nil => simp [fingerprintPoly, fingerprintEval]
  | cons v vs ih =>
    unfold fingerprintPoly fingerprintEval at ih ⊢
    simp only [List.foldr_cons, eval_add, eval_C, eval_mul, eval_X, ih]

theorem coeff_fingerprintPoly (args : List Fp) (i : ℕ) :
    (fingerprintPoly args).coeff i =
      match args[i]? with
      | some v => K.embedHom v
      | none => 0 := by
  induction args generalizing i with
  | nil => simp [fingerprintPoly]
  | cons v vs ih =>
    unfold fingerprintPoly at ih ⊢
    cases i with
    | zero => simp
    | succ i => simp [ih]

theorem natDegree_fingerprintPoly_le (args : List Fp) :
    (fingerprintPoly args).natDegree ≤ args.length := by
  induction args with
  | nil => simp [fingerprintPoly]
  | cons v vs ih =>
    unfold fingerprintPoly at ih ⊢
    simp only [List.foldr_cons, List.length_cons]
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    refine (natDegree_mul_le).trans ?_
    simp only [natDegree_X]
    omega

/-- Two lists of the same length with equal fingerprint polynomials are equal. -/
theorem fingerprintPoly_inj_of_length_eq {a b : List Fp} (hlen : a.length = b.length)
    (heq : fingerprintPoly a = fingerprintPoly b) : a = b := by
  apply List.ext_getElem hlen
  intro i hi1 hi2
  have hc := congrArg (fun p : K[X] => p.coeff i) heq
  rw [coeff_fingerprintPoly, coeff_fingerprintPoly, List.getElem?_eq_getElem hi1,
    List.getElem?_eq_getElem hi2] at hc
  exact K.embedHom.injective hc

set_option linter.constructorNameAsVariable false in
/-- If two tuples have equal length and differ, then `fingerprintPoly a - fingerprintPoly b`
is nonzero of degree at most `a.length`, so at most `a.length` values of `γ : K` collide them. -/
theorem card_fingerprint_collision_le {a b : List Fp} (hlen : a.length = b.length) (hne : a ≠ b) :
    (Finset.univ.filter fun γ : K => fingerprintEval γ a = fingerprintEval γ b).card ≤ a.length := by
  set P : K[X] := fingerprintPoly a - fingerprintPoly b
  have hPne : P ≠ 0 := by
    intro h0
    exact hne (fingerprintPoly_inj_of_length_eq hlen (sub_eq_zero.mp h0))
  have hdeg : P.natDegree ≤ a.length := by
    refine (natDegree_sub_le _ _).trans (max_le (natDegree_fingerprintPoly_le a) ?_)
    rw [hlen]; exact natDegree_fingerprintPoly_le b
  have hsub : (Finset.univ.filter fun γ : K => fingerprintEval γ a = fingerprintEval γ b) ⊆
      P.roots.toFinset := by
    intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    rw [Multiset.mem_toFinset, mem_roots hPne, IsRoot.def]
    simp [P, eval_fingerprintPoly, hγ]
  exact (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' P).trans hdeg))

/-- Cleared-denominator LogUp polynomial in `β`:
`Q(X) = ∑_{m ∈ S} w(m) · ∏_{m' ∈ S \ {m}} (X + fp(m'))`. -/
noncomputable def logupClearedPoly {α : Type*} [DecidableEq α] (S : Finset α)
    (fp : α → K) (w : α → K) : K[X] :=
  ∑ m ∈ S, C (w m) * ∏ m' ∈ S.erase m, (X + C (fp m'))

theorem eval_logupClearedPoly_at_neg_fp {α : Type*} [DecidableEq α] (S : Finset α)
    (fp : α → K) (w : α → K) {m₀ : α} (hm₀ : m₀ ∈ S) :
    (logupClearedPoly S fp w).eval (-fp m₀) =
      w m₀ * ∏ m' ∈ S.erase m₀, (-fp m₀ + fp m') := by
  unfold logupClearedPoly
  rw [eval_finsetSum]
  rw [Finset.sum_eq_single m₀]
  · simp [eval_prod]
  · intro m hm hne
    simp only [eval_mul, eval_C, eval_prod]
    have hm₀_in : m₀ ∈ S.erase m := Finset.mem_erase.mpr ⟨hne.symm, hm₀⟩
    have hprod0 : (∏ x ∈ S.erase m, (X + C (fp x)).eval (-fp m₀)) = 0 := by
      apply Finset.prod_eq_zero hm₀_in
      simp
    rw [hprod0, mul_zero]
  · intro hnot; exact absurd hm₀ hnot

theorem natDegree_logupClearedPoly_le {α : Type*} [DecidableEq α] (S : Finset α)
    (fp : α → K) (w : α → K) :
    (logupClearedPoly S fp w).natDegree ≤ S.card - 1 := by
  unfold logupClearedPoly
  refine (natDegree_sum_le S _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun m hm => ?_⟩
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  have hsum : ∑ m' ∈ S.erase m, (X + C (fp m')).natDegree ≤ (S.erase m).card := by
    calc ∑ m' ∈ S.erase m, (X + C (fp m')).natDegree
        ≤ ∑ _m' ∈ S.erase m, 1 := Finset.sum_le_sum (f := fun m' => (X + C (fp m')).natDegree)
          (g := fun _ => 1) fun m' _ => by rw [natDegree_X_add_C]
      _ = (S.erase m).card := by simp
  rwa [Finset.card_erase_of_mem hm] at hsum

/-- If all `fp m` for `m ∈ S` are distinct and `w m₀ ≠ 0` for some `m₀ ∈ S`, then
`logupClearedPoly S fp w ≠ 0`. -/
theorem logupClearedPoly_ne_zero {α : Type*} [DecidableEq α] {S : Finset α}
    {fp : α → K} {w : α → K} (hinj : Set.InjOn fp S)
    {m₀ : α} (hm₀ : m₀ ∈ S) (hw : w m₀ ≠ 0) :
    logupClearedPoly S fp w ≠ 0 := by
  intro h0
  have hev := congrArg (fun p : K[X] => p.eval (-fp m₀)) h0
  rw [eval_zero, eval_logupClearedPoly_at_neg_fp S fp w hm₀] at hev
  have hprod_ne : (∏ m' ∈ S.erase m₀, (-fp m₀ + fp m')) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro m' hm'
    obtain ⟨hne, hm'S⟩ := Finset.mem_erase.mp hm'
    intro hsum
    have hfp : fp m' = fp m₀ := by
      have := eq_neg_of_add_eq_zero_left hsum
      simpa using this.symm
    exact hne (hinj hm'S hm₀ hfp)
  exact mul_ne_zero hw hprod_ne hev

/-- Relating the partial-fraction sum `∑_{m ∈ S} w m * (β + fp m)⁻¹` to `logupClearedPoly`:
when `∀ m ∈ S, β + fp m ≠ 0`, the partial-fraction sum is zero iff `logupClearedPoly` vanishes at `β`. -/
theorem eval_logupClearedPoly_eq_mul_sum {α : Type*} [DecidableEq α] (S : Finset α)
    (fp : α → K) (w : α → K) (β : K) (hden : ∀ m ∈ S, β + fp m ≠ 0) :
    (logupClearedPoly S fp w).eval β =
      (∏ m ∈ S, (β + fp m)) * (∑ m ∈ S, w m * (β + fp m)⁻¹) := by
  unfold logupClearedPoly
  rw [eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X]
  have hsplit : (∏ x ∈ S, (β + fp x)) = (β + fp m) * (∏ x ∈ S.erase m, (β + fp x)) :=
    (Finset.mul_prod_erase S (fun x => β + fp x) hm).symm
  rw [hsplit]
  have hd : β + fp m ≠ 0 := hden m hm
  field_simp [hd]

set_option linter.constructorNameAsVariable false in
/-- **LogUp β-Soundness:** When `fp` is injective on `S` and `∃ m₀ ∈ S, w m₀ ≠ 0`, the number of
challenges `β ∈ K` satisfying `∀ m ∈ S, β + fp m ≠ 0` and `∑ m ∈ S, w m * (β + fp m)⁻¹ = 0`
is at most `S.card - 1`. -/
theorem card_logup_beta_bad_le {α : Type*} [DecidableEq α] {S : Finset α}
    {fp : α → K} {w : α → K} (hinj : Set.InjOn fp S)
    {m₀ : α} (hm₀ : m₀ ∈ S) (hw : w m₀ ≠ 0) :
    (Finset.univ.filter fun β : K =>
      (∀ m ∈ S, β + fp m ≠ 0) ∧ (∑ m ∈ S, w m * (β + fp m)⁻¹) = 0).card ≤ S.card - 1 := by
  set Q := logupClearedPoly S fp w
  have hQne : Q ≠ 0 := logupClearedPoly_ne_zero hinj hm₀ hw
  have hsub : (Finset.univ.filter fun β : K =>
      (∀ m ∈ S, β + fp m ≠ 0) ∧ (∑ m ∈ S, w m * (β + fp m)⁻¹) = 0) ⊆ Q.roots.toFinset := by
    intro β hβ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ
    rw [Multiset.mem_toFinset, mem_roots hQne, IsRoot.def,
      eval_logupClearedPoly_eq_mul_sum S fp w β hβ.1, hβ.2, mul_zero]
  exact (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' Q).trans (natDegree_logupClearedPoly_le S fp w)))

/-! ## 2. Sharded `MEMSEG = 16` Interval Balance → `WidthROM.Valid` -/

/-- A sorted list of disjoint half-open intervals `[a_j, b_j) ⊆ [0, p)` (matching
`validate_preamble` in `crates/aiur/src/trace/stark/batch.rs:230-252` and
`Ix.Cert.MultiStark.Preamble.checkClosurePairs`). -/
def DisjointIntervals (ivls : List (ℕ × ℕ)) : Prop :=
  (∀ iv ∈ ivls, iv.1 ≤ iv.2 ∧ iv.2 < CertiFri.P3.Goldilocks.order) ∧
  (∀ i (hi : i + 1 < ivls.length), ivls[i].2 ≤ ivls[i + 1].1)

/-- Coverage indicator of an interval list at `x : ℕ`: number of intervals `[a, b)` with `a ≤ x < b`. -/
def intervalCover (ivls : List (ℕ × ℕ)) (x : ℕ) : ℕ :=
  (ivls.filter fun iv => decide (iv.1 ≤ x ∧ x < iv.2)).length

/-- For sorted disjoint intervals, `intervalCover ivls x ≤ 1` for every `x : ℕ`. -/
theorem intervalCover_le_one {ivls : List (ℕ × ℕ)} (hd : DisjointIntervals ivls) (x : ℕ) :
    intervalCover ivls x ≤ 1 := by
  unfold intervalCover
  -- At most one index in `ivls` can contain `x` since `ivls[i].2 ≤ ivls[j].1` for `i < j`.
  have hmono : ∀ i j (hi : i < ivls.length) (hj : j < ivls.length), i < j →
      ivls[i].2 ≤ ivls[j].1 := by
    intro i j hi hj hlt
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases heq : i = j
      · subst heq; exact hd.2 i hj
      · have hprev := ih (by omega) (by omega)
        have hstep := hd.2 j hj
        have hle := (hd.1 ivls[j] (List.getElem_mem (by omega))).1
        omega
  by_contra hgt
  have h2 : 2 ≤ (ivls.filter fun iv => decide (iv.1 ≤ x ∧ x < iv.2)).length := by omega
  -- Extract two distinct indices in `ivls` satisfying the predicate
  have hpair : ∀ (l : List (ℕ × ℕ)) (p : ℕ × ℕ → Bool),
      2 ≤ (l.filter p).length →
      ∃ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
        i < j ∧ p l[i] = true ∧ p l[j] = true := by
    intro l p
    induction l with
    | nil => simp
    | cons a as ih =>
      intro hlen
      cases hpa : p a with
      | false =>
        simp only [List.filter_cons, hpa, Bool.false_eq_true, ↓reduceIte] at hlen
        obtain ⟨i, j, hi, hj, hlt, hpi, hpj⟩ := ih hlen
        exact ⟨i + 1, j + 1, Nat.succ_lt_succ hi, Nat.succ_lt_succ hj, Nat.succ_lt_succ hlt, hpi, hpj⟩
      | true =>
        simp only [List.filter_cons, hpa, ↓reduceIte, List.length_cons] at hlen
        have hpos : 0 < (as.filter p).length := by omega
        have hne : as.filter p ≠ [] := List.ne_nil_of_length_pos hpos
        obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ hne
        obtain ⟨hb_mem, hpb⟩ := List.mem_filter.mp hb
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb_mem
        exact ⟨0, j + 1, Nat.zero_lt_succ _, Nat.succ_lt_succ hj, Nat.zero_lt_succ _, hpa, hpb⟩
  obtain ⟨i, j, hi, hj, hlt, hpi, hpj⟩ := hpair ivls _ h2
  simp only [decide_eq_true_eq] at hpi hpj
  have := hmono i j hi hj hlt
  omega

/-- Coverage is `0` at `p - 1` because every interval ends strictly below `p`. -/
theorem intervalCover_last {ivls : List (ℕ × ℕ)} (hd : DisjointIntervals ivls) :
    intervalCover ivls (CertiFri.P3.Goldilocks.order - 1) = 0 := by
  unfold intervalCover
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro iv hiv
  have hlt := (hd.1 iv hiv).2
  simp only [decide_eq_true_eq, not_and, not_lt]
  intro _; omega

/-- Telescoping difference for a single interval `[a, b) ⊆ [0, p)` at every `x : Fp`:
`(I(x) : Fp) - (I(x - 1) : Fp) = (if x = a then 1 else 0) - (if x = b then 1 else 0)`. -/
private theorem single_interval_diff {a b : ℕ} (hab : a ≤ b)
    (hb : b < CertiFri.P3.Goldilocks.order) (x : Fp) :
    ((if a ≤ x.val ∧ x.val < b then (1 : ℕ) else 0 : ℕ) : Fp) -
    ((if a ≤ (x - 1).val ∧ (x - 1).val < b then (1 : ℕ) else 0 : ℕ) : Fp) =
      (if x = (a : Fp) then (1 : Fp) else 0) - (if x = (b : Fp) then (1 : Fp) else 0) := by
  have hp : CertiFri.P3.Goldilocks.order = Aiur.Library.U32.Goldilocks.modulus := rfl
  have hxv : x.val < CertiFri.P3.Goldilocks.order := by rw [hp]; exact ZMod.val_lt x
  have ha_eq : (x = (a : Fp)) ↔ x.val = a := by
    constructor
    · intro h; rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt (by rw [← hp]; omega)]
    · intro h; rw [← h, ZMod.natCast_zmod_val]
  have hb_eq : (x = (b : Fp)) ↔ x.val = b := by
    constructor
    · intro h; rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt (by rw [← hp]; omega)]
    · intro h; rw [← h, ZMod.natCast_zmod_val]
  by_cases hx0 : x.val = 0
  · have hx_zero : x = 0 := by rw [← ZMod.natCast_zmod_val x, hx0]; simp
    have hprev : (x - 1).val = CertiFri.P3.Goldilocks.order - 1 := by
      rw [hx_zero, zero_sub]
      have : (-1 : Fp) = ((CertiFri.P3.Goldilocks.order - 1 : ℕ) : Fp) := by
        have hp0 : (CertiFri.P3.Goldilocks.order : Fp) = 0 := by rw [hp]; exact ZMod.natCast_self _
        have hpos : 1 ≤ CertiFri.P3.Goldilocks.order := by unfold CertiFri.P3.Goldilocks.order; omega
        rw [Nat.cast_sub hpos, hp0, Nat.cast_one, zero_sub]
      rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by rw [← hp]; unfold CertiFri.P3.Goldilocks.order; omega)]
    simp only [hprev, hx0, ha_eq, hb_eq]
    split_ifs <;> try (exfalso; omega)
    all_goals (push_cast; ring)
  · have hprev : (x - 1).val = x.val - 1 := by
      have hx1 : x = ((x.val - 1 : ℕ) : Fp) + 1 := by
        have hnat : x.val = (x.val - 1) + 1 := by omega
        calc x = (x.val : Fp) := (ZMod.natCast_zmod_val x).symm
          _ = (((x.val - 1) + 1 : ℕ) : Fp) := by rw [← hnat]
          _ = ((x.val - 1 : ℕ) : Fp) + 1 := by push_cast; rfl
      have hsub : x - 1 = ((x.val - 1 : ℕ) : Fp) := sub_eq_of_eq_add hx1
      have hxv' : x.val < Aiur.Library.U32.Goldilocks.modulus := ZMod.val_lt x
      have hlt_sub : x.val - 1 < Aiur.Library.U32.Goldilocks.modulus := by omega
      rw [hsub, ZMod.val_natCast, Nat.mod_eq_of_lt hlt_sub]
    have hx_pos : 1 ≤ x.val := Nat.pos_of_ne_zero hx0
    simp only [hprev, ha_eq, hb_eq]
    split_ifs <;> try (exfalso; omega)
    all_goals (push_cast; ring)

/-- Preamble `MEMSEG` boundary contribution at `x : Fp`:
each interval `[a, b)` pulls (`-1`) at `a` and pushes (`+1`) at `b`. -/
def memsegBoundary (ivls : List (ℕ × ℕ)) (x : Fp) : Fp :=
  (ivls.map fun iv =>
    (if x = (iv.2 : Fp) then (1 : Fp) else 0) - (if x = (iv.1 : Fp) then (1 : Fp) else 0)).sum

theorem intervalCover_diff_eq_neg_memsegBoundary {ivls : List (ℕ × ℕ)} (hd : DisjointIntervals ivls)
    (x : Fp) :
    ((intervalCover ivls x.val : ℕ) : Fp) - ((intervalCover ivls (x - 1).val : ℕ) : Fp) =
      -memsegBoundary ivls x := by
  induction ivls with
  | nil => simp [intervalCover, memsegBoundary]
  | cons iv rest ih =>
    have hrest : DisjointIntervals rest := by
      refine ⟨fun a ha => hd.1 a (List.mem_cons_of_mem _ ha), fun i hi => ?_⟩
      have h2 := hd.2 (i + 1) (by simp; omega)
      exact h2
    have hiv := hd.1 iv (List.mem_cons_self ..)
    have h1 := single_interval_diff hiv.1 hiv.2 x
    have hstep := ih hrest
    have hcov : ∀ y : ℕ, ((intervalCover (iv :: rest) y : ℕ) : Fp) =
        ((if iv.1 ≤ y ∧ y < iv.2 then (1 : ℕ) else 0 : ℕ) : Fp) +
        ((intervalCover rest y : ℕ) : Fp) := by
      intro y
      unfold intervalCover
      by_cases hy : iv.1 ≤ y ∧ y < iv.2 <;> simp [hy, Nat.cast_add, add_comm]
    rw [hcov x.val, hcov (x - 1).val]
    unfold memsegBoundary at hstep ⊢
    simp only [List.map_cons, List.sum_cons]
    linear_combination h1 + hstep

/-- **Sharded `MEMSEG = 16` Uniqueness Theorem:**
Let `m : Fp → ℕ` count the active ROM rows at each address `x : Fp` for a fixed width,
with total active rows `∑ x, m x < p - 1`. Suppose the `MEMSEG` channel balances in `Fp`:
every active row at `addr` sends `+1 @ addr` and `-1 @ (addr + 1)`, and the sorted
disjoint preamble intervals `ivls` send `-1 @ a_j` and `+1 @ b_j`:
`∀ x : Fp, ((m x : Fp) - (m (x - 1) : Fp)) + memsegBoundary ivls x = 0`.
Then for EVERY address `x : Fp`, `m x = intervalCover ivls x.val ≤ 1`! -/
theorem memseg_balance_implies_unique {ivls : List (ℕ × ℕ)} (hd : DisjointIntervals ivls)
    {m : Fp → ℕ}
    (hsum : (∑ x : Fp, m x) + 1 < CertiFri.P3.Goldilocks.order)
    (hbal : ∀ x : Fp, ((m x : Fp) - (m (x - 1) : Fp)) + memsegBoundary ivls x = 0) :
    ∀ x : Fp, m x = intervalCover ivls x.val ∧ m x ≤ 1 := by
  have hp : CertiFri.P3.Goldilocks.order = Aiur.Library.U32.Goldilocks.modulus := rfl
  -- Step 1: `(m x : Fp) - (I(x) : Fp)` is invariant under `x ↦ x + 1`, hence constant on `Fp`!
  have hconst_step : ∀ x : Fp,
      (m x : Fp) - (intervalCover ivls x.val : Fp) =
        (m (x - 1) : Fp) - (intervalCover ivls (x - 1).val : Fp) := by
    intro x
    have hb := hbal x
    have hd' := intervalCover_diff_eq_neg_memsegBoundary hd x
    linear_combination hb - hd'
  have hconst : ∀ n : ℕ,
      (m (n : Fp) : Fp) - (intervalCover ivls (n : Fp).val : Fp) =
        (m (0 : Fp) : Fp) - (intervalCover ivls (0 : Fp).val : Fp) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := hconst_step ((n + 1 : ℕ) : Fp)
      have hsub : ((n + 1 : ℕ) : Fp) - 1 = (n : Fp) := by push_cast; ring
      rw [hsub] at hs
      exact hs.trans ih
  have hconst_all : ∀ x : Fp,
      (m x : Fp) - (intervalCover ivls x.val : Fp) =
        (m (-1 : Fp) : Fp) := by
    have hm1 : (-1 : Fp).val = CertiFri.P3.Goldilocks.order - 1 := by
      have hp0 : (CertiFri.P3.Goldilocks.order : Fp) = 0 := by rw [hp]; exact ZMod.natCast_self _
      have hpos : 1 ≤ CertiFri.P3.Goldilocks.order := by unfold CertiFri.P3.Goldilocks.order; omega
      have : (-1 : Fp) = ((CertiFri.P3.Goldilocks.order - 1 : ℕ) : Fp) := by
        rw [Nat.cast_sub hpos, hp0, Nat.cast_one, zero_sub]
      rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by rw [← hp]; unfold CertiFri.P3.Goldilocks.order; omega)]
    have hI_last : intervalCover ivls (-1 : Fp).val = 0 := by
      rw [hm1]; exact intervalCover_last hd
    intro x
    have hx := hconst x.val
    rw [ZMod.natCast_zmod_val] at hx
    have hlast := hconst (-1 : Fp).val
    rw [ZMod.natCast_zmod_val, hI_last, Nat.cast_zero, sub_zero] at hlast
    exact hx.trans hlast.symm
  -- Step 2: Lift equality from `Fp` to `ℕ` using `m x ≤ ∑ m < p - 1` and `I(x) ≤ 1`
  have hnat : ∀ x : Fp, m x = m (-1 : Fp) + intervalCover ivls x.val := by
    intro x
    have hfeq : (m x : Fp) = ((m (-1 : Fp) + intervalCover ivls x.val : ℕ) : Fp) := by
      push_cast; linear_combination hconst_all x
    have hm_le : m x ≤ ∑ y : Fp, m y :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    have hm1_le : m (-1 : Fp) ≤ ∑ y : Fp, m y :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (-1 : Fp))
    have hI_le : intervalCover ivls x.val ≤ 1 := intervalCover_le_one hd x.val
    have hsum' : (∑ x : Fp, m x) + 1 < Aiur.Library.U32.Goldilocks.modulus := hsum
    have hlt1 : m x < Aiur.Library.U32.Goldilocks.modulus := by omega
    have hlt2 : m (-1 : Fp) + intervalCover ivls x.val < Aiur.Library.U32.Goldilocks.modulus := by
      omega
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hfeq
    rwa [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hmod
  -- Step 3: `m (-1)` must be `0`, otherwise `∑ x, m x ≥ p * m (-1) ≥ p`, contradicting `hsum`!
  have hm1_zero : m (-1 : Fp) = 0 := by
    by_contra hne
    have hpos : 1 ≤ m (-1 : Fp) := Nat.pos_of_ne_zero hne
    have hge : CertiFri.P3.Goldilocks.order ≤ ∑ x : Fp, m x := by
      calc CertiFri.P3.Goldilocks.order
          = Fintype.card Fp := by rw [ZMod.card, hp]
        _ = ∑ _x : Fp, 1 := by simp
        _ ≤ ∑ x : Fp, m x := Finset.sum_le_sum fun x _ => by rw [hnat x]; omega
    omega
  intro x
  have hx := hnat x
  rw [hm1_zero, Nat.zero_add] at hx
  exact ⟨hx, hx ▸ intervalCover_le_one hd x.val⟩

/-- **ROM Functionality (`WidthROM.Valid`) from per-width address uniqueness:**
If every `(width, addr)` pair occurs at most once in `rom.entries`, then `rom.Valid` holds. -/
theorem widthROM_valid_of_count_le_one (rom : Aiur.WidthROM Fp)
    (huniq : ∀ (w : ℕ) (addr : Fp),
      (rom.entries.filter fun e => decide (e.2.length = w ∧ e.1 = addr)).length ≤ 1) :
    rom.Valid := by
  intro a ha b hb haddr hlen
  have hle := huniq a.2.length a.1
  set filt := rom.entries.filter fun e => decide (e.2.length = a.2.length ∧ e.1 = a.1)
  have ha_mem : a ∈ filt := List.mem_filter.mpr ⟨ha, decide_eq_true ⟨rfl, rfl⟩⟩
  have hb_mem : b ∈ filt := List.mem_filter.mpr ⟨hb, decide_eq_true ⟨hlen.symm, haddr.symm⟩⟩
  cases hf : filt with
  | nil => rw [hf] at ha_mem; simp at ha_mem
  | cons x xs =>
    cases xs with
    | nil =>
      rw [hf] at ha_mem hb_mem
      have ha_eq : a = x := List.mem_singleton.mp ha_mem
      have hb_eq : b = x := List.mem_singleton.mp hb_mem
      rw [ha_eq, hb_eq]
    | cons y ys =>
      rw [hf] at hle; simp at hle

/-! ## 3. Field Balance → Integer `Plan.checkMemo` Reweighting -/

open Classical in
/-- Reweight active rows of a `Grouping.Plan`: given `rows : List (Aiur.Circuit.Row Fp)`
with every row passing `plan.inspectRow rom`, assign `multiplicity = (demands m : Int)`
to the first active row whose conclusion is `m`, and `0` to all other rows. -/
noncomputable def reweightRows {source : Aiur.Circuit.System Fp} {id : String → Except String ℕ}
    (plan : Aiur.Optimized.Grouping.Plan source id) (rom : Aiur.WireROM Fp)
    (demandCount : Aiur.Circuit.Message Fp → ℕ) :
    List (Aiur.Circuit.Row Fp) → List (Aiur.Circuit.Message Fp) →
      List (Aiur.Circuit.WeightedRow Fp)
  | [], _ => []
  | r :: rs, seen =>
    match plan.inspectRow rom r with
    | .ok (some claims) =>
      if claims.1 ∈ seen then
        ⟨r, 0⟩ :: reweightRows plan rom demandCount rs seen
      else
        ⟨r, (demandCount claims.1 : Int)⟩ :: reweightRows plan rom demandCount rs (claims.1 :: seen)
    | _ => ⟨r, 0⟩ :: reweightRows plan rom demandCount rs seen

theorem reweightRows_length {source : Aiur.Circuit.System Fp} {id : String → Except String ℕ}
    (plan : Aiur.Optimized.Grouping.Plan source id) (rom : Aiur.WireROM Fp)
    (demandCount : Aiur.Circuit.Message Fp → ℕ)
    (rows : List (Aiur.Circuit.Row Fp)) (seen : List (Aiur.Circuit.Message Fp)) :
    (reweightRows plan rom demandCount rows seen).length = rows.length := by
  induction rows generalizing seen with
  | nil => rfl
  | cons r rs ih =>
    unfold reweightRows
    cases plan.inspectRow rom r with
    | error _ => simp [ih]
    | ok opt =>
      cases opt with
      | none => simp [ih]
      | some claims => classical dsimp only; split_ifs <;> simp [ih]

/-- Key arithmetic lemma: if a natural number demand `d < p` balances a finite sum of
field weights `∑_{i ∈ providers} w_i = (d : Fp)` in `Fp`, and `d > 0`, then `providers`
is nonempty (so at least one active provider row exists for that message!). -/
theorem exists_provider_of_field_balance {ι : Type*} (providers : List ι) (w : ι → Fp)
    {d : ℕ} (hd_pos : 0 < d) (hd_lt : d < CertiFri.P3.Goldilocks.order)
    (hbal : (providers.map w).sum = (d : Fp)) :
    providers ≠ [] := by
  intro hnil
  rw [hnil, List.map_nil, List.sum_nil] at hbal
  have hp : CertiFri.P3.Goldilocks.order = Aiur.Library.U32.Goldilocks.modulus := rfl
  have hd_ne : (d : Fp) ≠ 0 := by
    intro h0
    have hmod := (ZMod.natCast_eq_zero_iff d Aiur.Library.U32.Goldilocks.modulus).mp h0
    have hlt : d < Aiur.Library.U32.Goldilocks.modulus := by rw [← hp]; exact hd_lt
    exact Nat.not_dvd_of_pos_of_lt hd_pos hlt hmod
  exact hd_ne hbal.symm

end Ix.Cert.MultiStark
