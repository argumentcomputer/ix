import IxAIGpu.Step

/-!
# The CUDA-core path on 64- and 128-bit registers, and its overflow guard

The kernels hold every buffer value as an int64, form each dot product's exact 128-bit products
and add them on 128-bit registers (two 64-bit words), narrow the result to int64, and check every
elementwise add, subtract and multiply. Every add and the narrowing raise an overflow flag; the
host refuses a step if any flag is raised.

* `addOvf_iff`, `subOvf_iff`, `mul_fits_iff`, `fits_val128_iff`, `add128_val`, `add128Ovf_eq`:
  the hardware detectors (sign rule, `mul.hi` against the sign of `mul.lo`, high word against the
  sign of the low word) flag exactly the results that are not `w`-bit values, and add with carry
  on two words is the 128-bit add;
* `blockReduceC_of_fits`, `blockReduceC_of_not_fits`, `blockReduceC_eq`: `blockReduce` with
  every add checked succeeds exactly when every running lane sum and every tree node fits
  (`ReduceFits`), and then it is the exact sum;
* `blockReduceM_flag`, `blockReduceM_val`: on wrapped registers with sticky flags, the flag is
  clear exactly when the checked reduction succeeds, and then the register holds its value;
* `gpuStepM_eq`: under `StepGuard` (no flag raised in any kernel), the machine step `gpuStepM`
  is `Model.step`.
-/

namespace IxAIGpu
open IxAICore Finset

/-! ## Two's complement -/

/-- `v` is a `w`-bit two's-complement value. -/
def Fits (w : Nat) (v : Int) : Prop := -2 ^ (w - 1) ≤ v ∧ v < 2 ^ (w - 1)

instance (w : Nat) : DecidablePred (Fits w) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The `w`-bit two's-complement value with the low `w` bits of `v`. -/
def wrap (w : Nat) (v : Int) : Int := (v + 2 ^ (w - 1)) % 2 ^ w - 2 ^ (w - 1)

theorem two_pow_eq {w : Nat} (hw : 0 < w) : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, w = n + 1 := ⟨w - 1, by omega⟩
  simp [pow_succ]; ring

theorem wrap_fits {w : Nat} (hw : 0 < w) (v : Int) : Fits w (wrap w v) := by
  have h := two_pow_eq hw
  have hM : (0 : Int) < 2 ^ (w - 1) := by positivity
  have h1 := Int.emod_nonneg (v + 2 ^ (w - 1)) (by omega : (2 : Int) ^ w ≠ 0)
  have h2 := Int.emod_lt_of_pos (v + 2 ^ (w - 1)) (by omega : (0 : Int) < 2 ^ w)
  unfold Fits wrap
  generalize (v + 2 ^ (w - 1)) % 2 ^ w = r at *
  generalize (2 : Int) ^ (w - 1) = M at *
  generalize (2 : Int) ^ w = N at *
  omega

theorem wrap_modEq (w : Nat) (v : Int) : wrap w v ≡ v [ZMOD 2 ^ w] := by
  have := (Int.mod_modEq (v + 2 ^ (w - 1)) (2 ^ w)).sub_right (2 ^ (w - 1))
  simpa [wrap] using this

/-- `wrap w v` is the unique `w`-bit value congruent to `v`. -/
theorem wrap_eq_of_dvd {w : Nat} (hw : 0 < w) {u v : Int} (hu : Fits w u) (h : 2 ^ w ∣ v - u) :
    wrap w v = u := by
  have h := two_pow_eq hw
  have hmod : (v + 2 ^ (w - 1)) % 2 ^ w = u + 2 ^ (w - 1) := by
    rw [← Int.emod_eq_of_lt (a := u + 2 ^ (w - 1)) (b := 2 ^ w) (by unfold Fits at hu; omega)
      (by unfold Fits at hu; omega)]
    apply Int.ModEq.eq
    rw [Int.modEq_iff_dvd]
    have : u + 2 ^ (w - 1) - (v + 2 ^ (w - 1)) = -(v - u) := by ring
    rw [this]
    exact (Int.dvd_neg).mpr ‹_›
  unfold wrap
  omega

theorem wrap_of_fits {w : Nat} (hw : 0 < w) {v : Int} (h : Fits w v) : wrap w v = v :=
  wrap_eq_of_dvd hw h (by simp)

theorem wrap_congr {w : Nat} (hw : 0 < w) {a b : Int} (h : 2 ^ w ∣ a - b) : wrap w a = wrap w b := by
  apply wrap_eq_of_dvd hw (wrap_fits hw b)
  have := Int.ModEq.dvd (wrap_modEq w b)
  have e : a - wrap w b = (a - b) + (b - wrap w b) := by ring
  rw [e]
  exact dvd_add h this

theorem fits_zero {w : Nat} : Fits w 0 := by
  unfold Fits
  have : (0 : Int) < 2 ^ (w - 1) := by positivity
  omega

theorem wrap_add_sub {w : Nat} (hw : 0 < w) {v : Int} (h : 2 ^ (w - 1) ≤ v ∧ v < 3 * 2 ^ (w - 1)) :
    wrap w v = v - 2 ^ w :=
  wrap_eq_of_dvd hw (by unfold Fits; have := two_pow_eq hw; omega) ⟨1, by ring⟩

theorem wrap_add_add {w : Nat} (hw : 0 < w) {v : Int} (h : -3 * 2 ^ (w - 1) ≤ v ∧ v < -2 ^ (w - 1)) :
    wrap w v = v + 2 ^ w :=
  wrap_eq_of_dvd hw (by unfold Fits; have := two_pow_eq hw; omega) ⟨-1, by ring⟩

/-! ## Overflow detectors -/

/-- The sign rule of a `w`-bit add: operands of one sign, a wrapped result of the other. -/
def addOvf (w : Nat) (a b : Int) : Bool :=
  (decide (a < 0) == decide (b < 0)) && (decide (wrap w (a + b) < 0) != decide (a < 0))

/-- The sign rule of a `w`-bit subtract: operands of different signs, a wrapped result with the
sign of the subtrahend. -/
def subOvf (w : Nat) (a b : Int) : Bool :=
  (decide (a < 0) != decide (b < 0)) && (decide (wrap w (a - b) < 0) != decide (a < 0))

/-- **The sign rule detects exactly the adds that overflow.** -/
theorem addOvf_iff {w : Nat} (hw : 0 < w) {a b : Int} (ha : Fits w a) (hb : Fits w b) :
    addOvf w a b = true ↔ ¬ Fits w (a + b) := by
  have h2 := two_pow_eq hw
  by_cases hf : Fits w (a + b)
  · rw [addOvf, wrap_of_fits hw hf]
    unfold Fits at *
    by_cases h1 : a < 0 <;> by_cases h2 : b < 0 <;> simp [h1, h2] <;> omega
  · unfold Fits at ha hb hf
    by_cases hp : 2 ^ (w - 1) ≤ a + b
    · rw [addOvf, wrap_add_sub hw (by omega)]
      by_cases h1 : a < 0 <;> by_cases h2 : b < 0 <;> simp [h1, h2, Fits] <;> omega
    · rw [addOvf, wrap_add_add hw (by omega)]
      by_cases h1 : a < 0 <;> by_cases h2 : b < 0 <;> simp [h1, h2, Fits] <;> omega

/-- **The sign rule detects exactly the subtracts that overflow.** -/
theorem subOvf_iff {w : Nat} (hw : 0 < w) {a b : Int} (ha : Fits w a) (hb : Fits w b) :
    subOvf w a b = true ↔ ¬ Fits w (a - b) := by
  have h2 := two_pow_eq hw
  by_cases hf : Fits w (a - b)
  · rw [subOvf, wrap_of_fits hw hf]
    unfold Fits at *
    by_cases h1 : a < 0 <;> by_cases h2 : b < 0 <;> simp [h1, h2] <;> omega
  · unfold Fits at ha hb hf
    by_cases hp : 2 ^ (w - 1) ≤ a - b
    · rw [subOvf, wrap_add_sub hw (by omega)]
      by_cases h1 : a < 0 <;> by_cases h2 : b < 0 <;> simp [h1, h2, Fits] <;> omega
    · rw [subOvf, wrap_add_add hw (by omega)]
      by_cases h1 : a < 0 <;> by_cases h2 : b < 0 <;> simp [h1, h2, Fits] <;> omega

/-! ## 64-bit words and 128-bit registers -/

/-- An unsigned 64-bit word. -/
def Word (lo : Int) : Prop := 0 ≤ lo ∧ lo < 2 ^ 64

/-- The sign extension of a 64-bit word (`lo >>> 63`, arithmetic): the high word of its int64
value. -/
def signExt (lo : Int) : Int := if wrap 64 lo < 0 then -1 else 0

/-- A 128-bit register held as a signed high word and an unsigned low word. -/
def val128 (hi lo : Int) : Int := hi * 2 ^ 64 + lo

theorem wrap64_word {lo : Int} (h : Word lo) : wrap 64 lo = if lo < 2 ^ 63 then lo else lo - 2 ^ 64 := by
  unfold Word at h
  split_ifs with hl
  · exact wrap_of_fits (by norm_num) (by unfold Fits; norm_num at *; omega)
  · exact wrap_add_sub (w := 64) (by norm_num) (by norm_num at *; omega)

/-- **Narrowing.** A 128-bit register holds an int64 exactly when its high word is the sign
extension of its low word. -/
theorem fits_val128_iff {hi lo : Int} (h : Word lo) : Fits 64 (val128 hi lo) ↔ hi = signExt lo := by
  rw [signExt, wrap64_word h]
  unfold Fits val128 Word at *
  norm_num at *
  split_ifs <;> omega

/-- The narrowed value is the low word read as an int64. -/
theorem val128_of_fits {hi lo : Int} (h : Fits 64 (val128 hi lo)) : val128 hi lo = wrap 64 lo :=
  (wrap_eq_of_dvd (by norm_num) h ⟨-hi, by unfold val128; ring⟩).symm

theorem val128_fits {hi lo : Int} (hhi : Fits 64 hi) (hlo : Word lo) : Fits 128 (val128 hi lo) := by
  unfold Fits val128 Word at *
  norm_num at *
  omega

/-- The sign of a 128-bit register is the sign of its high word. -/
theorem val128_neg_iff {hi lo : Int} (h : Word lo) : val128 hi lo < 0 ↔ hi < 0 := by
  unfold val128 Word at *
  norm_num at *
  omega

/-- `mul.hi.s64`: the high word of the exact 128-bit product. -/
def mulHi (a b : Int) : Int := a * b / 2 ^ 64

/-- `mul.lo.u64`: the low word of the exact product. -/
def mulLo (a b : Int) : Int := a * b % 2 ^ 64

theorem mul_words (a b : Int) : val128 (mulHi a b) (mulLo a b) = a * b := by
  unfold val128 mulHi mulLo
  generalize a * b = P
  norm_num
  omega

theorem mulLo_word (a b : Int) : Word (mulLo a b) := by
  unfold Word mulLo
  generalize a * b = P
  norm_num
  omega

/-- The product of two int64 values fits in 128 bits. -/
theorem fits_mul {a b : Int} (ha : Fits 64 a) (hb : Fits 64 b) : Fits 128 (a * b) := by
  unfold Fits at *
  norm_num at *
  have h1 : |a| ≤ 2 ^ 63 := abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |b| ≤ 2 ^ 63 := abs_le.2 ⟨by linarith, by linarith⟩
  have h3 : |a * b| ≤ 2 ^ 63 * 2 ^ 63 := by
    rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
  have := abs_le.1 h3
  constructor <;> linarith

theorem mulHi_fits {a b : Int} (ha : Fits 64 a) (hb : Fits 64 b) : Fits 64 (mulHi a b) := by
  have h := fits_mul ha hb
  unfold Fits mulHi at *
  generalize a * b = P at *
  norm_num at *
  omega

/-- **The int64 multiply check.** The product is an int64 exactly when `mul.hi` is the sign
extension of `mul.lo`. -/
theorem mul_fits_iff (a b : Int) : Fits 64 (a * b) ↔ mulHi a b = signExt (mulLo a b) := by
  rw [← fits_val128_iff (mulLo_word a b), mul_words]

/-- `add.cc` / `addc` on two 128-bit registers `(hi, lo)`: the carry out of the low words goes
into the sum of the high words. -/
def add128 (x y : Int × Int) : Int × Int :=
  (wrap 64 (x.1 + y.1 + (x.2 + y.2) / 2 ^ 64), (x.2 + y.2) % 2 ^ 64)

theorem add128_words (x y : Int × Int) : Fits 64 (add128 x y).1 ∧ Word (add128 x y).2 := by
  refine ⟨wrap_fits (by norm_num) _, ?_⟩
  unfold add128 Word
  generalize x.2 + y.2 = s
  norm_num
  omega

/-- **Add with carry is the 128-bit add**, wrapped to 128 bits. -/
theorem add128_val (x y : Int × Int) :
    val128 (add128 x y).1 (add128 x y).2 = wrap 128 (val128 x.1 x.2 + val128 y.1 y.2) := by
  obtain ⟨h1, h2⟩ := add128_words x y
  symm
  apply wrap_eq_of_dvd (by norm_num) (val128_fits h1 h2)
  obtain ⟨k, hk⟩ := Int.ModEq.dvd (wrap_modEq 64 (x.1 + y.1 + (x.2 + y.2) / 2 ^ 64))
  have hs : x.2 + y.2 = 2 ^ 64 * ((x.2 + y.2) / 2 ^ 64) + (x.2 + y.2) % 2 ^ 64 := by
    generalize x.2 + y.2 = s; norm_num; omega
  refine ⟨k, ?_⟩
  unfold val128 add128
  simp only
  linear_combination hs + (2 : Int) ^ 64 * hk

/-- The sign rule on the high words of two 128-bit registers. -/
def add128Ovf (x y : Int × Int) : Bool :=
  (decide (x.1 < 0) == decide (y.1 < 0)) && (decide ((add128 x y).1 < 0) != decide (x.1 < 0))

/-- The high-word sign rule is the 128-bit sign rule, so it flags exactly the overflowing adds
(`addOvf_iff`). -/
theorem add128Ovf_eq {x y : Int × Int} (hx : Word x.2) (hy : Word y.2) :
    add128Ovf x y = addOvf 128 (val128 x.1 x.2) (val128 y.1 y.2) := by
  have h := (add128_words x y).2
  simp only [add128Ovf, addOvf, ← add128_val, val128_neg_iff hx, val128_neg_iff hy, val128_neg_iff h]

theorem fits_shr8 {v : Int} (h : Fits 64 v) : Fits 64 (v >>> (8 : Nat)) := by
  rw [Int.shiftRight_eq_div_pow]
  unfold Fits at *
  norm_num at *
  omega

theorem fits_relu {v : Int} (h : Fits 64 v) : Fits 64 (relu v) := by
  unfold relu; split
  · exact h
  · exact fits_zero

/-! ## The checked reduction -/

/-- A checked `w`-bit result: `none` when it overflows. -/
def fitO (w : Nat) (v : Int) : Option Int := if Fits w v then some v else none

/-- A checked `w`-bit add. -/
def addC (w : Nat) (a b : Int) : Option Int := fitO w (a + b)

/-- A checked add of two lane values, either of which may have overflowed already. -/
def addO (w : Nat) (a b : Option Int) : Option Int := a.bind fun x => b.bind fun y => addC w x y

/-- The terms lane `t` of `T` adds, in order: `t, t + T, … < K`. -/
def laneIdx (T K t : Nat) : List Nat := (List.range K).filter fun k => k % T == t

/-- `threadSum` with every add checked. -/
def threadSumC (w T K t : Nat) (f : Nat → Int) : Option Int :=
  (laneIdx T K t).foldl (fun acc k => acc.bind fun a => addC w a (f k)) (some 0)

/-- `warpTree` with every add checked. -/
def warpTreeC (w : Nat) : Nat → List (Option Int) → Option Int
  | 0, l => l.headD (some 0)
  | n + 1, l => warpTreeC w n (List.zipWith (addO w) (l.take (2 ^ n)) (l.drop (2 ^ n)))

/-- `blockReduce` with every add checked: the same terms, the same order, the same tree. -/
def blockReduceC (w : Nat) (g : Geometry) (f : Nat → Int) (K : Nat) : Option Int :=
  warpTreeC w g.logLanes ((List.range g.lanes).map fun t => threadSumC w g.lanes K t f)

/-- The running sums of a left-to-right accumulation from `a`. -/
def prefixSums (f : Nat → Int) : Int → List Nat → List Int
  | _, [] => []
  | a, k :: l => (a + f k) :: prefixSums f (a + f k) l

/-- Every node of the shuffle tree, level by level. -/
def treeNodes : Nat → List Int → List Int
  | 0, _ => []
  | n + 1, l =>
    List.zipWith (· + ·) (l.take (2 ^ n)) (l.drop (2 ^ n)) ++
      treeNodes n (List.zipWith (· + ·) (l.take (2 ^ n)) (l.drop (2 ^ n)))

/-- Every value `blockReduce` forms fits in `w` bits: each lane's running sums and every node of
the tree. -/
def ReduceFits (w : Nat) (g : Geometry) (f : Nat → Int) (K : Nat) : Prop :=
  (∀ t < g.lanes, ∀ x ∈ prefixSums f 0 (laneIdx g.lanes K t), Fits w x) ∧
    ∀ x ∈ treeNodes g.logLanes ((List.range g.lanes).map fun t => threadSum g.lanes K t f), Fits w x

theorem foldlC_none (w : Nat) (f : Nat → Int) (l : List Nat) :
    l.foldl (fun acc k => acc.bind fun a => addC w a (f k)) none = none := by
  induction l with
  | nil => rfl
  | cons k l ih => simpa using ih

theorem foldlC_of_fits (w : Nat) (f : Nat → Int) (l : List Nat) (a : Int)
    (h : ∀ x ∈ prefixSums f a l, Fits w x) :
    l.foldl (fun acc k => acc.bind fun a => addC w a (f k)) (some a) =
      some (l.foldl (fun acc k => acc + f k) a) := by
  induction l generalizing a with
  | nil => rfl
  | cons k l ih =>
    simp only [prefixSums, List.mem_cons, forall_eq_or_imp] at h
    simp only [List.foldl_cons, Option.bind_some, addC, fitO, h.1, ↓reduceIte]
    exact ih _ h.2

theorem foldlC_of_not_fits (w : Nat) (f : Nat → Int) (l : List Nat) (a : Int)
    (h : ¬ ∀ x ∈ prefixSums f a l, Fits w x) :
    l.foldl (fun acc k => acc.bind fun a => addC w a (f k)) (some a) = none := by
  induction l generalizing a with
  | nil => simp [prefixSums] at h
  | cons k l ih =>
    simp only [prefixSums, List.mem_cons, forall_eq_or_imp, not_and_or] at h
    simp only [List.foldl_cons, Option.bind_some, addC, fitO]
    by_cases hk : Fits w (a + f k)
    · simp only [hk, ↓reduceIte]
      exact ih _ (h.resolve_left (not_not.mpr hk))
    · simp only [hk, ↓reduceIte]
      exact foldlC_none w f l

theorem warpTreeC_none (w n : Nat) (l : List (Option Int)) (hl : l.length = 2 ^ n)
    (h : none ∈ l) : warpTreeC w n l = none := by
  induction n generalizing l with
  | zero =>
    match l, hl with
    | [o], _ => simp_all [warpTreeC]
  | succ n ih =>
    simp only [warpTreeC]
    apply ih _ (by simp [List.length_zipWith, hl, pow_succ]; omega)
    obtain ⟨i, hi, hli⟩ := List.mem_iff_getElem.mp h
    have hp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
    rw [List.mem_iff_getElem]
    by_cases hlt : i < 2 ^ n
    · refine ⟨i, by simp [List.length_zipWith, hl]; omega, ?_⟩
      simp only [List.getElem_zipWith, List.getElem_take, hli, addO, Option.bind_none]
    · refine ⟨i - 2 ^ n, by simp [List.length_zipWith, hl]; omega, ?_⟩
      simp only [List.getElem_zipWith, List.getElem_drop]
      have e : 2 ^ n + (i - 2 ^ n) = i := by omega
      simp [e, hli, addO]

theorem zipWith_addO (w : Nat) (a b : List Int) :
    List.zipWith (addO w) (a.map some) (b.map some) = (List.zipWith (· + ·) a b).map (fitO w) := by
  induction a generalizing b with
  | nil => simp
  | cons x a ih => cases b <;> simp_all [addO, addC]

theorem warpTreeC_some (w n : Nat) (l : List Int) (hl : l.length = 2 ^ n) :
    ((∀ x ∈ treeNodes n l, Fits w x) → warpTreeC w n (l.map some) = some (warpTree n l)) ∧
      (¬ (∀ x ∈ treeNodes n l, Fits w x) → warpTreeC w n (l.map some) = none) := by
  induction n generalizing l with
  | zero =>
    match l, hl with
    | [a], _ => simp [warpTreeC, warpTree, treeNodes]
  | succ n ih =>
    simp only [warpTreeC, warpTree, treeNodes, ← List.map_take, ← List.map_drop, zipWith_addO]
    generalize hl' : List.zipWith (· + ·) (l.take (2 ^ n)) (l.drop (2 ^ n)) = l'
    have hlen : l'.length = 2 ^ n := by
      rw [← hl']; simp [List.length_zipWith, hl, pow_succ]; omega
    simp only [List.mem_append]
    by_cases hall : ∀ x ∈ l', Fits w x
    · have e : l'.map (fitO w) = l'.map some :=
        List.map_congr_left fun x hx => by simp [fitO, hall x hx]
      rw [e]
      obtain ⟨i1, i2⟩ := ih l' hlen
      constructor
      · intro h; exact i1 fun x hx => h x (Or.inr hx)
      · intro h; apply i2; intro hn; apply h; intro x hx
        rcases hx with hx | hx
        · exact hall x hx
        · exact hn x hx
    · have hn : none ∈ l'.map (fitO w) := by
        push Not at hall
        obtain ⟨x, hx, hf⟩ := hall
        exact List.mem_map.mpr ⟨x, hx, by simp [fitO, hf]⟩
      refine ⟨fun h => absurd (fun x hx => h x (Or.inl hx)) hall, fun _ => ?_⟩
      exact warpTreeC_none w n _ (by simp [hlen]) hn

theorem threadSumC_spec (w T K t : Nat) (f : Nat → Int) :
    ((∀ x ∈ prefixSums f 0 (laneIdx T K t), Fits w x) →
        threadSumC w T K t f = some (threadSum T K t f)) ∧
      (¬ (∀ x ∈ prefixSums f 0 (laneIdx T K t), Fits w x) → threadSumC w T K t f = none) :=
  ⟨foldlC_of_fits w f _ 0, foldlC_of_not_fits w f _ 0⟩

/-- **The checked reduction succeeds exactly when every value it forms fits**, and then it is
`blockReduce`. -/
theorem blockReduceC_of_fits {w : Nat} {g : Geometry} {f : Nat → Int} {K : Nat}
    (h : ReduceFits w g f K) : blockReduceC w g f K = some (blockReduce g f K) := by
  have e : ((List.range g.lanes).map fun t => threadSumC w g.lanes K t f) =
      ((List.range g.lanes).map fun t => threadSum g.lanes K t f).map some := by
    rw [List.map_map]
    exact List.map_congr_left fun t ht =>
      (threadSumC_spec w _ K t f).1 (h.1 t (List.mem_range.mp ht))
  rw [blockReduceC, e]
  exact (warpTreeC_some w _ _ (by simp [Geometry.lanes])).1 h.2

theorem blockReduceC_of_not_fits {w : Nat} {g : Geometry} {f : Nat → Int} {K : Nat}
    (h : ¬ ReduceFits w g f K) : blockReduceC w g f K = none := by
  rw [blockReduceC]
  by_cases hl : ∀ t < g.lanes, ∀ x ∈ prefixSums f 0 (laneIdx g.lanes K t), Fits w x
  · have e : ((List.range g.lanes).map fun t => threadSumC w g.lanes K t f) =
        ((List.range g.lanes).map fun t => threadSum g.lanes K t f).map some := by
      rw [List.map_map]
      exact List.map_congr_left fun t ht =>
        (threadSumC_spec w _ K t f).1 (hl t (List.mem_range.mp ht))
    rw [e]
    exact (warpTreeC_some w _ _ (by simp [Geometry.lanes])).2 fun h2 => h ⟨hl, h2⟩
  · apply warpTreeC_none w _ _ (by simp [Geometry.lanes])
    push Not at hl
    obtain ⟨t, ht, hx⟩ := hl
    exact List.mem_map.mpr ⟨t, List.mem_range.mpr ht,
      (threadSumC_spec w _ K t f).2 (by push Not; exact hx)⟩

theorem blockReduceC_isSome_iff {w : Nat} {g : Geometry} {f : Nat → Int} {K : Nat} :
    (blockReduceC w g f K).isSome ↔ ReduceFits w g f K := by
  by_cases h : ReduceFits w g f K
  · simp [blockReduceC_of_fits h, h]
  · simp [blockReduceC_of_not_fits h, h]

/-- **A successful checked reduction is the exact sum.** -/
theorem blockReduceC_eq {w : Nat} {g : Geometry} {f : Nat → Int} {K : Nat} {v : Int}
    (h : blockReduceC w g f K = some v) : v = ∑ k ∈ range K, f k := by
  by_cases hf : ReduceFits w g f K
  · rw [blockReduceC_of_fits hf] at h
    rw [← blockReduce_eq g, Option.some_inj.mp h]
  · rw [blockReduceC_of_not_fits hf] at h
    cases h

/-! ## The machine reduction -/

/-- A `w`-bit add on a register with a sticky overflow flag. -/
def addM (w : Nat) (x : Int × Bool) (v : Int) : Int × Bool :=
  (wrap w (x.1 + v), x.2 || addOvf w x.1 v)

/-- A `w`-bit add of two lanes' registers; the flags are or-ed. -/
def addMM (w : Nat) (x y : Int × Bool) : Int × Bool :=
  (wrap w (x.1 + y.1), x.2 || y.2 || addOvf w x.1 y.1)

/-- Lane `t`'s wrapped accumulation and flag. -/
def threadSumM (w T K t : Nat) (f : Nat → Int) : Int × Bool :=
  (laneIdx T K t).foldl (fun acc k => addM w acc (f k)) (0, false)

/-- The shuffle tree on wrapped registers. -/
def warpTreeM (w : Nat) : Nat → List (Int × Bool) → Int × Bool
  | 0, l => l.headD (0, false)
  | n + 1, l => warpTreeM w n (List.zipWith (addMM w) (l.take (2 ^ n)) (l.drop (2 ^ n)))

/-- `blockReduce` as a `w`-bit machine runs it: the wrapped result and the overflow flag. -/
def blockReduceM (w : Nat) (g : Geometry) (f : Nat → Int) (K : Nat) : Int × Bool :=
  warpTreeM w g.logLanes ((List.range g.lanes).map fun t => threadSumM w g.lanes K t f)

/-- A machine register agrees with a checked value: the exact value with a clear flag, or a
raised flag after an overflow. -/
def Agree (w : Nat) : Int × Bool → Option Int → Prop
  | x, some v => x = (v, false) ∧ Fits w v
  | x, none => x.2 = true

theorem agree_addM {w : Nat} (hw : 0 < w) {x : Int × Bool} {c : Option Int} {v : Int}
    (hx : Agree w x c) (hv : Fits w v) : Agree w (addM w x v) (c.bind fun a => addC w a v) := by
  cases c with
  | none => simp_all [Agree, addM]
  | some a =>
    obtain ⟨rfl, ha⟩ := hx
    have ho := addOvf_iff hw ha hv
    by_cases hf : Fits w (a + v)
    · simp [Agree, addM, addC, fitO, hf, wrap_of_fits hw hf]
      simpa [hf] using ho
    · simp [Agree, addM, addC, fitO, hf]
      simpa [hf] using ho

theorem agree_addMM {w : Nat} (hw : 0 < w) {x y : Int × Bool} {c d : Option Int}
    (hx : Agree w x c) (hy : Agree w y d) : Agree w (addMM w x y) (addO w c d) := by
  cases c with
  | none => simp_all [Agree, addMM, addO]
  | some a =>
    cases d with
    | none => simp_all [Agree, addMM, addO]
    | some b =>
      obtain ⟨rfl, ha⟩ := hx
      obtain ⟨rfl, hb⟩ := hy
      have ho := addOvf_iff hw ha hb
      by_cases hf : Fits w (a + b)
      · simp [Agree, addMM, addO, addC, fitO, hf, wrap_of_fits hw hf]
        simpa [hf] using ho
      · simp [Agree, addMM, addO, addC, fitO, hf]
        simpa [hf] using ho

theorem agree_foldl {w : Nat} (hw : 0 < w) (f : Nat → Int) (l : List Nat) (hf : ∀ k ∈ l, Fits w (f k))
    (x : Int × Bool) (c : Option Int) (h : Agree w x c) :
    Agree w (l.foldl (fun acc k => addM w acc (f k)) x)
      (l.foldl (fun acc k => acc.bind fun a => addC w a (f k)) c) := by
  induction l generalizing x c with
  | nil => exact h
  | cons k l ih =>
    simp only [List.foldl_cons]
    exact ih (fun k hk => hf k (List.mem_cons_of_mem _ hk)) _ _
      (agree_addM hw h (hf k List.mem_cons_self))

theorem forall₂_zipWith {α β : Type} {R : α → β → Prop} {F : α → α → α} {G : β → β → β}
    (hR : ∀ a b c d, R a c → R b d → R (F a b) (G c d)) :
    ∀ {a b : List α} {c d : List β}, List.Forall₂ R a c → List.Forall₂ R b d →
      List.Forall₂ R (List.zipWith F a b) (List.zipWith G c d)
  | [], _, [], _, .nil, _ => by simp
  | _ :: _, [], _ :: _, [], .cons _ _, .nil => by simp
  | _ :: _, _ :: _, _ :: _, _ :: _, .cons h1 t1, .cons h2 t2 =>
    List.Forall₂.cons (hR _ _ _ _ h1 h2) (forall₂_zipWith hR t1 t2)

theorem agree_warpTree {w : Nat} (hw : 0 < w) (n : Nat) :
    ∀ {l : List (Int × Bool)} {c : List (Option Int)}, List.Forall₂ (Agree w) l c →
      Agree w (warpTreeM w n l) (warpTreeC w n c) := by
  induction n with
  | zero =>
    intro l c h
    cases h with
    | nil => exact ⟨rfl, fits_zero⟩
    | cons h _ => exact h
  | succ n ih =>
    intro l c h
    exact ih (forall₂_zipWith (fun _ _ _ _ => agree_addMM hw)
      (List.forall₂_take _ h) (List.forall₂_drop _ h))

theorem forall₂_map {α β γ : Type} {R : β → γ → Prop} (F : α → β) (G : α → γ) :
    ∀ (l : List α), (∀ t ∈ l, R (F t) (G t)) → List.Forall₂ R (l.map F) (l.map G)
  | [], _ => .nil
  | t :: l, h => .cons (h t List.mem_cons_self)
      (forall₂_map F G l fun t ht => h t (List.mem_cons_of_mem _ ht))

/-- The machine reduction agrees with the checked one when every term fits. -/
theorem agree_blockReduce {w : Nat} (hw : 0 < w) (g : Geometry) {f : Nat → Int} {K : Nat}
    (hf : ∀ k < K, Fits w (f k)) : Agree w (blockReduceM w g f K) (blockReduceC w g f K) := by
  apply agree_warpTree hw
  apply forall₂_map
  intro t _
  apply agree_foldl hw
  · intro k hk
    simp only [laneIdx, List.mem_filter, List.mem_range] at hk
    exact hf k hk.1
  · exact ⟨rfl, fits_zero⟩

/-- **The machine flag is clear exactly when the checked reduction succeeds.** -/
theorem blockReduceM_flag {w : Nat} (hw : 0 < w) (g : Geometry) {f : Nat → Int} {K : Nat}
    (hf : ∀ k < K, Fits w (f k)) :
    (blockReduceM w g f K).2 = false ↔ (blockReduceC w g f K).isSome := by
  have h := agree_blockReduce hw g hf
  revert h
  cases blockReduceC w g f K with
  | none => intro h; simp_all [Agree]
  | some v => intro h; simp_all [Agree]

/-- **With the flag clear, the machine's wrapped arithmetic is exact.** -/
theorem blockReduceM_val {w : Nat} (hw : 0 < w) (g : Geometry) {f : Nat → Int} {K : Nat}
    (hf : ∀ k < K, Fits w (f k)) {v : Int} (h : blockReduceC w g f K = some v) :
    (blockReduceM w g f K).1 = v := by
  have ha := agree_blockReduce hw g hf
  rw [h] at ha
  rw [ha.1]

theorem blockReduceM_congr (w : Nat) (g : Geometry) {f f' : Nat → Int} {K : Nat}
    (h : ∀ k < K, f k = f' k) : blockReduceM w g f K = blockReduceM w g f' K := by
  unfold blockReduceM threadSumM
  congr 1
  apply List.map_congr_left
  intro t _
  have hl : ∀ k ∈ laneIdx g.lanes K t, f k = f' k := by
    intro k hk
    simp only [laneIdx, List.mem_filter, List.mem_range] at hk
    exact h k hk.1
  generalize laneIdx g.lanes K t = l at hl ⊢
  generalize ((0 : Int), false) = x
  induction l generalizing x with
  | nil => rfl
  | cons k l ih =>
    simp only [List.foldl_cons]
    rw [hl k List.mem_cons_self]
    exact ih (fun k hk => hl k (List.mem_cons_of_mem _ hk)) _

/-! ## The step on the machine -/

theorem fits_128_of_64 {v : Int} (h : Fits 64 v) : Fits 128 v := by
  unfold Fits at *; norm_num at *; omega

theorem wrap64 {v : Int} (h : Fits 64 v) : wrap 64 v = v := wrap_of_fits (by norm_num) h

theorem wrap64_fits (v : Int) : Fits 64 (wrap 64 v) := wrap_fits (by norm_num) v

/-- A reduction as a kernel stores it: the 128-bit machine reduction narrowed to int64. -/
def redM (g : Geometry) (f : Nat → Int) (K : Nat) : Int := wrap 64 (blockReduceM 128 g f K).1

/-- The guard of one reduction: every 128-bit add is exact and the narrowed result is an int64. -/
def RedGuard (g : Geometry) (f : Nat → Int) (K : Nat) : Prop :=
  ∃ S, blockReduceC 128 g f K = some S ∧ Fits 64 S

/-- Under its guard, a machine reduction over terms that agree with the exact ones on `[0, K)` is
`blockReduce`. -/
theorem redM_eq {g : Geometry} {f f' : Nat → Int} {K : Nat} (h : ∀ k < K, f k = f' k)
    (hf : ∀ k, Fits 128 (f k)) (hg : RedGuard g f' K) : redM g f K = blockReduce g f' K := by
  obtain ⟨S, hS, h64⟩ := hg
  rw [redM, blockReduceM_congr 128 g h,
    blockReduceM_val (by norm_num) g (fun k hk => h k hk ▸ hf k) hS, wrap64 h64, blockReduce_eq,
    ← blockReduceC_eq hS]

theorem redM_fits (g : Geometry) (f : Nat → Int) (K : Nat) : Fits 64 (redM g f K) := wrap64_fits _

/-- `hidden_kernel` on the machine: `z = (S >>> 8) + b1[j]`, a checked add. -/
def hiddenZM (g : Geometry) (nI : Nat) (W1 : Mat) (B1 : Vec) (X : Mat) : Mat :=
  fun b j => wrap 64 ((redM g (fun i => W1 j i * X b i) nI >>> (8 : Nat)) + B1 j)

/-- `output_kernel` on the machine: `o = (S >>> 8) + b2[k]` and `dout = o − t[b][k]`, both
checked. -/
def outputDeltaM (g : Geometry) (nH : Nat) (W2 : Mat) (B2 : Vec) (Hm T : Mat) : Mat :=
  fun b k => wrap 64 (wrap 64 ((redM g (fun j => W2 k j * Hm b j) nH >>> (8 : Nat)) + B2 k) - T b k)

/-- `dz_kernel` on the machine. -/
def dzKM (g : Geometry) (nO : Nat) (W2T Z Dout : Mat) : Mat :=
  fun b j => if Z b j > 0 then redM g (fun k => W2T j k * Dout b k) nO >>> (8 : Nat) else 0

/-- `update_w_kernel` on the machine: `p = lr · (S >>> 8)` and `w − (p >>> 8)`, both checked. -/
def updateWM (g : Geometry) (lr : Int) (nB : Nat) (W GT AT : Mat) : Mat :=
  fun r c => wrap 64 (W r c -
    (wrap 64 (lr * (redM g (fun b => GT r b * AT c b) nB >>> (8 : Nat))) >>> (8 : Nat)))

/-- `update_b_kernel` on the machine: `p = lr · S` and `b − (p >>> 8)`, both checked. -/
def updateBM (g : Geometry) (lr : Int) (nB : Nat) (Bv : Vec) (GT : Mat) : Vec :=
  fun r => wrap 64 (Bv r - (wrap 64 (lr * redM g (fun b => GT r b) nB) >>> (8 : Nat)))

/-- The kernels of `gpuStep` on index functions. -/
def kernelStep (g : Geometry) (lr : Int) (nB nI nH nO : Nat) (W1 : Mat) (B1 : Vec) (W2 : Mat)
    (B2 : Vec) (X T : Mat) : Model :=
  let Z := hiddenZ g nI W1 B1 X
  let Hm : Mat := fun b j => relu (Z b j)
  let Dout := outputDelta g nH W2 B2 Hm T
  let Dz := dzK g nO (transposeK W2) Z Dout
  { w1 := Mat.toRows nH nI (updateW g lr nB W1 (transposeK Dz) (transposeK X))
    b1 := Vec.toList nH (updateB g lr nB B1 (transposeK Dz))
    w2 := Mat.toRows nO nH (updateW g lr nB W2 (transposeK Dout) (transposeK Hm))
    b2 := Vec.toList nO (updateB g lr nB B2 (transposeK Dout)) }

/-- The same kernels on the machine. -/
def machineStep (g : Geometry) (lr : Int) (nB nI nH nO : Nat) (W1 : Mat) (B1 : Vec) (W2 : Mat)
    (B2 : Vec) (X T : Mat) : Model :=
  let Z := hiddenZM g nI W1 B1 X
  let Hm : Mat := fun b j => relu (Z b j)
  let Dout := outputDeltaM g nH W2 B2 Hm T
  let Dz := dzKM g nO (transposeK W2) Z Dout
  { w1 := Mat.toRows nH nI (updateWM g lr nB W1 (transposeK Dz) (transposeK X))
    b1 := Vec.toList nH (updateBM g lr nB B1 (transposeK Dz))
    w2 := Mat.toRows nO nH (updateWM g lr nB W2 (transposeK Dout) (transposeK Hm))
    b2 := Vec.toList nO (updateBM g lr nB B2 (transposeK Dout)) }

/-- `gpuStep` on the machine: inputs uploaded as int64, every reduction run on 128-bit registers
and narrowed, every add, subtract and multiply wrapped to 64 bits. -/
def gpuStepM (g : Geometry) (lr : Fx) (m : Model) (batch : List (List Fx × List Fx)) : Model :=
  if batch.isEmpty then m else
  machineStep g (wrap 64 lr.raw) batch.length (getD m.w1 0 []).length m.b1.length m.b2.length
    (fun r c => wrap 64 (Mat.ofRows m.w1 r c)) (fun r => wrap 64 (Vec.ofList m.b1 r))
    (fun r c => wrap 64 (Mat.ofRows m.w2 r c)) (fun r => wrap 64 (Vec.ofList m.b2 r))
    (fun r c => wrap 64 (Mat.ofRows (batch.map (·.1)) r c))
    (fun r c => wrap 64 (Mat.ofRows (batch.map (·.2)) r c))

/-- The guard on index functions: inputs are int64, and on every in-range index each reduction's
guard holds and each checked result is an int64, all on the exact values of `kernelStep`. -/
def StepGuardAt (g : Geometry) (lr : Int) (nB nI nH nO : Nat) (W1 : Mat) (B1 : Vec) (W2 : Mat)
    (B2 : Vec) (X T : Mat) : Prop :=
  let Z := hiddenZ g nI W1 B1 X
  let Hm : Mat := fun b j => relu (Z b j)
  let Dout := outputDelta g nH W2 B2 Hm T
  let Dz := dzK g nO (transposeK W2) Z Dout
  (Fits 64 lr ∧ (∀ r c, Fits 64 (W1 r c)) ∧ (∀ r, Fits 64 (B1 r)) ∧ (∀ r c, Fits 64 (W2 r c)) ∧
    (∀ r, Fits 64 (B2 r)) ∧ (∀ b i, Fits 64 (X b i)) ∧ ∀ b k, Fits 64 (T b k)) ∧
  (∀ b < nB, ∀ j < nH, RedGuard g (fun i => W1 j i * X b i) nI ∧ Fits 64 (Z b j)) ∧
  (∀ b < nB, ∀ k < nO, RedGuard g (fun j => W2 k j * Hm b j) nH ∧
    Fits 64 ((outputKey g nH W2 Hm b k >>> (8 : Nat)) + B2 k) ∧ Fits 64 (Dout b k)) ∧
  (∀ b < nB, ∀ j < nH, RedGuard g (fun k => W2 k j * Dout b k) nO) ∧
  (∀ r < nH, ∀ c < nI, RedGuard g (fun b => Dz b r * X b c) nB ∧
    Fits 64 (lr * (gradKey g nB (transposeK Dz) (transposeK X) r c >>> (8 : Nat))) ∧
    Fits 64 (updateW g lr nB W1 (transposeK Dz) (transposeK X) r c)) ∧
  (∀ r < nH, RedGuard g (fun b => Dz b r) nB ∧
    Fits 64 (lr * blockReduce g (fun b => Dz b r) nB) ∧
    Fits 64 (updateB g lr nB B1 (transposeK Dz) r)) ∧
  (∀ r < nO, ∀ c < nH, RedGuard g (fun b => Dout b r * Hm b c) nB ∧
    Fits 64 (lr * (gradKey g nB (transposeK Dout) (transposeK Hm) r c >>> (8 : Nat))) ∧
    Fits 64 (updateW g lr nB W2 (transposeK Dout) (transposeK Hm) r c)) ∧
  (∀ r < nO, RedGuard g (fun b => Dout b r) nB ∧
    Fits 64 (lr * blockReduce g (fun b => Dout b r) nB) ∧
    Fits 64 (updateB g lr nB B2 (transposeK Dout) r))

/-- **The step guard**: the flags of every kernel of `gpuStep` stay clear on this model and
batch. -/
def StepGuard (g : Geometry) (lr : Fx) (m : Model) (batch : List (List Fx × List Fx)) : Prop :=
  StepGuardAt g lr.raw batch.length (getD m.w1 0 []).length m.b1.length m.b2.length
    (Mat.ofRows m.w1) (Vec.ofList m.b1) (Mat.ofRows m.w2) (Vec.ofList m.b2)
    (Mat.ofRows (batch.map (·.1))) (Mat.ofRows (batch.map (·.2)))

theorem toRows_congr {R C : Nat} {F G : Mat} (h : ∀ r < R, ∀ c < C, F r c = G r c) :
    Mat.toRows R C F = Mat.toRows R C G := by
  unfold Mat.toRows Vec.toList
  refine List.map_congr_left fun r hr => List.map_congr_left fun c hc => ?_
  rw [h r (List.mem_range.mp hr) c (List.mem_range.mp hc)]

theorem toList_congr {n : Nat} {F G : Vec} (h : ∀ r < n, F r = G r) :
    Vec.toList n F = Vec.toList n G := by
  unfold Vec.toList
  refine List.map_congr_left fun r hr => ?_
  rw [h r (List.mem_range.mp hr)]

theorem hiddenZM_eq {g : Geometry} {nI b j : Nat} {W1 : Mat} {B1 : Vec} {X : Mat}
    (hW : ∀ r c, Fits 64 (W1 r c)) (hX : ∀ b i, Fits 64 (X b i))
    (hg : RedGuard g (fun i => W1 j i * X b i) nI) (hz : Fits 64 (hiddenZ g nI W1 B1 X b j)) :
    hiddenZM g nI W1 B1 X b j = hiddenZ g nI W1 B1 X b j := by
  unfold hiddenZM
  rw [redM_eq (fun _ _ => rfl) (fun i => fits_mul (hW _ _) (hX _ _)) hg]
  exact wrap64 hz

theorem outputDeltaM_eq {g : Geometry} {nH b k : Nat} {W2 : Mat} {B2 : Vec} {Hm Hm' T : Mat}
    (hH : ∀ j < nH, Hm b j = Hm' b j) (hHf : ∀ j, Fits 64 (Hm b j)) (hW : ∀ r c, Fits 64 (W2 r c))
    (hg : RedGuard g (fun j => W2 k j * Hm' b j) nH)
    (ho : Fits 64 ((outputKey g nH W2 Hm' b k >>> (8 : Nat)) + B2 k))
    (hd : Fits 64 (outputDelta g nH W2 B2 Hm' T b k)) :
    outputDeltaM g nH W2 B2 Hm T b k = outputDelta g nH W2 B2 Hm' T b k := by
  unfold outputDeltaM
  rw [redM_eq (fun j hj => by rw [hH j hj]) (fun j => fits_mul (hW _ _) (hHf _)) hg]
  have ho' : Fits 64 ((blockReduce g (fun j => W2 k j * Hm' b j) nH >>> (8 : Nat)) + B2 k) := ho
  rw [wrap64 ho']
  exact wrap64 hd

theorem dzKM_eq {g : Geometry} {nO b j : Nat} {W2T Z Z' D D' : Mat} (hz : Z b j = Z' b j)
    (hD : ∀ k < nO, D b k = D' b k) (hDf : ∀ k, Fits 64 (D b k)) (hW : ∀ r c, Fits 64 (W2T r c))
    (hg : RedGuard g (fun k => W2T j k * D' b k) nO) :
    dzKM g nO W2T Z D b j = dzK g nO W2T Z' D' b j := by
  unfold dzKM dzK dzKey
  rw [hz, redM_eq (fun k hk => by rw [hD k hk]) (fun k => fits_mul (hW _ _) (hDf _)) hg]

theorem dzKM_fits (g : Geometry) (nO : Nat) (W2T Z D : Mat) (b j : Nat) :
    Fits 64 (dzKM g nO W2T Z D b j) := by
  unfold dzKM; split
  · exact fits_shr8 (redM_fits _ _ _)
  · exact fits_zero

theorem updateWM_eq {g : Geometry} {lr : Int} {nB r c : Nat} {W GT GT' AT AT' : Mat}
    (hG : ∀ b < nB, GT r b = GT' r b) (hA : ∀ b < nB, AT c b = AT' c b)
    (hGf : ∀ b, Fits 64 (GT r b)) (hAf : ∀ b, Fits 64 (AT c b))
    (hg : RedGuard g (fun b => GT' r b * AT' c b) nB)
    (hp : Fits 64 (lr * (gradKey g nB GT' AT' r c >>> (8 : Nat))))
    (hw : Fits 64 (updateW g lr nB W GT' AT' r c)) :
    updateWM g lr nB W GT AT r c = updateW g lr nB W GT' AT' r c := by
  unfold updateWM
  rw [redM_eq (fun b hb => by rw [hG b hb, hA b hb]) (fun b => fits_mul (hGf _) (hAf _)) hg]
  have hp' : Fits 64 (lr * (blockReduce g (fun b => GT' r b * AT' c b) nB >>> (8 : Nat))) := hp
  rw [wrap64 hp']
  exact wrap64 hw

theorem updateBM_eq {g : Geometry} {lr : Int} {nB r : Nat} {Bv : Vec} {GT GT' : Mat}
    (hG : ∀ b < nB, GT r b = GT' r b) (hGf : ∀ b, Fits 64 (GT r b))
    (hg : RedGuard g (fun b => GT' r b) nB) (hp : Fits 64 (lr * blockReduce g (fun b => GT' r b) nB))
    (hw : Fits 64 (updateB g lr nB Bv GT' r)) :
    updateBM g lr nB Bv GT r = updateB g lr nB Bv GT' r := by
  unfold updateBM
  rw [redM_eq hG (fun b => fits_128_of_64 (hGf _)) hg]
  rw [wrap64 hp]
  exact wrap64 hw

/-- Under the guard, the machine's kernels compute `kernelStep`. -/
theorem machineStep_eq {g : Geometry} {lr : Int} {nB nI nH nO : Nat} {W1 : Mat} {B1 : Vec}
    {W2 : Mat} {B2 : Vec} {X T : Mat} (h : StepGuardAt g lr nB nI nH nO W1 B1 W2 B2 X T) :
    machineStep g lr nB nI nH nO W1 B1 W2 B2 X T = kernelStep g lr nB nI nH nO W1 B1 W2 B2 X T := by
  obtain ⟨⟨_hlr, hW1, _hB1, hW2, _hB2, hX, _hT⟩, gZ, gO, gD, gW1, gB1, gW2, gB2⟩ := h
  have hZ : ∀ b < nB, ∀ j < nH, hiddenZM g nI W1 B1 X b j = hiddenZ g nI W1 B1 X b j :=
    fun b hb j hj => hiddenZM_eq hW1 hX (gZ b hb j hj).1 (gZ b hb j hj).2
  have hHf : ∀ b j, Fits 64 (relu (hiddenZM g nI W1 B1 X b j)) :=
    fun b j => fits_relu (wrap64_fits _)
  have hD : ∀ b < nB, ∀ k < nO,
      outputDeltaM g nH W2 B2 (fun b j => relu (hiddenZM g nI W1 B1 X b j)) T b k =
        outputDelta g nH W2 B2 (fun b j => relu (hiddenZ g nI W1 B1 X b j)) T b k :=
    fun b hb k hk => outputDeltaM_eq (fun j hj => by simp only [hZ b hb j hj]) (hHf b) hW2
      (gO b hb k hk).1 (gO b hb k hk).2.1 (gO b hb k hk).2.2
  have hDf : ∀ b k,
      Fits 64 (outputDeltaM g nH W2 B2 (fun b j => relu (hiddenZM g nI W1 B1 X b j)) T b k) :=
    fun b k => wrap64_fits _
  have hDz : ∀ b < nB, ∀ j < nH,
      dzKM g nO (transposeK W2) (hiddenZM g nI W1 B1 X)
          (outputDeltaM g nH W2 B2 (fun b j => relu (hiddenZM g nI W1 B1 X b j)) T) b j =
        dzK g nO (transposeK W2) (hiddenZ g nI W1 B1 X)
          (outputDelta g nH W2 B2 (fun b j => relu (hiddenZ g nI W1 B1 X b j)) T) b j :=
    fun b hb j hj => dzKM_eq (hZ b hb j hj) (fun k hk => hD b hb k hk) (hDf b)
      (fun r c => hW2 c r) (gD b hb j hj)
  simp only [machineStep, kernelStep, Model.mk.injEq]
  refine ⟨toRows_congr fun r hr c _ => ?_, toList_congr fun r hr => ?_,
    toRows_congr fun r hr c hc => ?_, toList_congr fun r hr => ?_⟩
  · exact updateWM_eq (fun b hb => hDz b hb r hr) (fun _ _ => rfl) (fun b => dzKM_fits _ _ _ _ _ b r)
      (fun b => hX b c) (gW1 r hr c ‹_›).1 (gW1 r hr c ‹_›).2.1 (gW1 r hr c ‹_›).2.2
  · exact updateBM_eq (fun b hb => hDz b hb r hr) (fun b => dzKM_fits _ _ _ _ _ b r)
      (gB1 r hr).1 (gB1 r hr).2.1 (gB1 r hr).2.2
  · exact updateWM_eq (fun b hb => hD b hb r hr)
      (fun b hb => by simp only [transposeK, hZ b hb c hc]) (fun b => hDf b r) (fun b => hHf b c)
      (gW2 r hr c hc).1 (gW2 r hr c hc).2.1 (gW2 r hr c hc).2.2
  · exact updateBM_eq (fun b hb => hD b hb r hr) (fun b => hDf b r)
      (gB2 r hr).1 (gB2 r hr).2.1 (gB2 r hr).2.2

theorem gpuStep_kernelStep (g : Geometry) (lr : Fx) (m : Model) (batch : List (List Fx × List Fx)) :
    gpuStep g lr m batch = if batch.isEmpty then m else
      kernelStep g lr.raw batch.length (getD m.w1 0 []).length m.b1.length m.b2.length
        (Mat.ofRows m.w1) (Vec.ofList m.b1) (Mat.ofRows m.w2) (Vec.ofList m.b2)
        (Mat.ofRows (batch.map (·.1))) (Mat.ofRows (batch.map (·.2))) := rfl

/-- **Under the step guard, the machine step is `gpuStep`.** -/
theorem gpuStepM_eq_gpuStep (g : Geometry) (lr : Fx) (m : Model) (batch : List (List Fx × List Fx))
    (h : StepGuard g lr m batch) : gpuStepM g lr m batch = gpuStep g lr m batch := by
  rw [gpuStep_kernelStep, gpuStepM]
  split
  · rfl
  have h' := h
  obtain ⟨⟨hlr, hW1, hB1, hW2, hB2, hX, hT⟩, _⟩ := h'
  have e1 : (fun r c => wrap 64 (Mat.ofRows m.w1 r c)) = Mat.ofRows m.w1 :=
    funext fun r => funext fun c => wrap64 (hW1 r c)
  have e2 : (fun r => wrap 64 (Vec.ofList m.b1 r)) = Vec.ofList m.b1 :=
    funext fun r => wrap64 (hB1 r)
  have e3 : (fun r c => wrap 64 (Mat.ofRows m.w2 r c)) = Mat.ofRows m.w2 :=
    funext fun r => funext fun c => wrap64 (hW2 r c)
  have e4 : (fun r => wrap 64 (Vec.ofList m.b2 r)) = Vec.ofList m.b2 :=
    funext fun r => wrap64 (hB2 r)
  have e5 : (fun r c => wrap 64 (Mat.ofRows (batch.map (·.1)) r c)) = Mat.ofRows (batch.map (·.1)) :=
    funext fun r => funext fun c => wrap64 (hX r c)
  have e6 : (fun r c => wrap 64 (Mat.ofRows (batch.map (·.2)) r c)) = Mat.ofRows (batch.map (·.2)) :=
    funext fun r => funext fun c => wrap64 (hT r c)
  rw [e1, e2, e3, e4, e5, e6, wrap64 hlr]
  exact machineStep_eq h

/-- **The machine step is the spec's step** whenever the step guard holds, i.e. whenever no
kernel raises its overflow flag. -/
theorem gpuStepM_eq (g : Geometry) (lr : Fx) (m : Model) (nI : Nat)
    (batch : List (List Fx × List Fx)) (hm : Shaped m nI) (hb : BatchShaped m nI batch)
    (h : StepGuard g lr m batch) : gpuStepM g lr m batch = m.step lr batch := by
  rw [gpuStepM_eq_gpuStep g lr m batch h, gpuStep_eq g lr m nI batch hm hb]

end IxAIGpu
