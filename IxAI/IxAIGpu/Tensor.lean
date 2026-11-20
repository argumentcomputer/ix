import IxAIGpu.Bounded

/-!
# The int8 tensor-core GEMM

An int8 tensor core forms a dot product of `int32` operands from byte limbs: operand `a` split
into `ka + 1` base-256 limbs and `b` into `kb + 1`, `K` cut into chunks of `C` indices, and per
chunk one `int32` accumulator for each weight `256^s`, gathering every limb product with
`p + q = s` in whatever order the MMAs choose. Each chunk's accumulators are shifted by `8s` bits
into a 128-bit accumulator.

* `limbs_range`: an operand in `[-2^(8k+7), 2^(8k+7))` has `k` unsigned-byte limbs and a
  signed-byte top limb;
* `limbDot2_eq`, `tileReduce_eq`: recombining the limb planes, in the tile loop order, is the
  exact sum, with no bounds;
* `RTree.evalW_eq`: a reduction tree of `w`-bit adds is exact when its leaves are small enough,
  whatever its shape;
* `tileReduceM_eq`: with `ka, kb ≤ 3`, operands in range, chunks of at most 8192 indices and
  `K < 2^31`, every `int32` accumulator and the 128-bit recombination are exact, so the machine
  result is `∑ k ∈ range K, a k * b k` (`tileReduceM_dotRaw`: `Fx.dotRaw`) for every MMA order.
-/

namespace IxAIGpu
open IxAICore Finset

/-! ## Limb ranges -/

/-- **Limb ranges.** Below `2^(8k+7)` in magnitude, the `k` low limbs are unsigned bytes and the
top limb is a signed byte. -/
theorem limbs_range (k : Nat) (x : Int) (h : -2 ^ (8 * k + 7) ≤ x ∧ x < 2 ^ (8 * k + 7)) :
    (∀ p < k, 0 ≤ limb k p x ∧ limb k p x < 256) ∧ -128 ≤ limb k k x ∧ limb k k x < 128 := by
  induction k generalizing x with
  | zero =>
    simp only [limb, limbs]
    norm_num at h ⊢
    omega
  | succ k ih =>
    have e : (2 : Int) ^ (8 * (k + 1) + 7) = 256 * 2 ^ (8 * k + 7) := by
      rw [show 8 * (k + 1) + 7 = (8 * k + 7) + 8 by ring, pow_add]; norm_num; ring
    have hl : ∀ p, limb (k + 1) (p + 1) x = limb k p (x / 256) := fun p => by simp [limb, limbs]
    have h0 : limb (k + 1) 0 x = x % 256 := by simp [limb, limbs]
    rw [e] at h
    obtain ⟨ih1, ih2⟩ := ih (x / 256) (by generalize (2 : Int) ^ (8 * k + 7) = M at *; omega)
    refine ⟨fun p hp => ?_, by rw [hl]; exact ih2⟩
    cases p with
    | zero => rw [h0]; omega
    | succ p => rw [hl]; exact ih1 p (by omega)

theorem abs_limb_le {k p : Nat} {x : Int} (hp : p ≤ k)
    (hx : -2 ^ (8 * k + 7) ≤ x ∧ x < 2 ^ (8 * k + 7)) : |limb k p x| ≤ 255 := by
  obtain ⟨h1, h2⟩ := limbs_range k x hx
  rw [abs_le]
  rcases Nat.lt_or_ge p k with h | h
  · have := h1 p h; constructor <;> linarith
  · obtain rfl : p = k := by omega
    constructor <;> linarith

/-! ## Limb planes with two limb counts -/

theorem limb_mul_expand (ka kb : Nat) (x y : Int) :
    x * y = ∑ p ∈ range (ka + 1), ∑ q ∈ range (kb + 1), 256 ^ (p + q) * (limb ka p x * limb kb q y) := by
  have e : x * y = (∑ p ∈ range (ka + 1), 256 ^ p * limb ka p x) *
      (∑ q ∈ range (kb + 1), 256 ^ q * limb kb q y) := by
    rw [← limb_expand, ← limb_expand]
  rw [e, Finset.sum_mul_sum]
  apply sum_congr rfl; intros; apply sum_congr rfl; intros
  rw [pow_add]; ring

/-- One limb plane: limb `p` of `a` against limb `q` of `b`. -/
def planeSum (ka kb p q : Nat) (a b : Nat → Int) (K : Nat) : Int :=
  ∑ k ∈ range K, limb ka p (a k) * limb kb q (b k)

/-- Every limb plane, recombined with weight `256^(p+q)`. -/
def limbDot2 (ka kb : Nat) (a b : Nat → Int) (K : Nat) : Int :=
  ∑ p ∈ range (ka + 1), ∑ q ∈ range (kb + 1), 256 ^ (p + q) * planeSum ka kb p q a b K

/-- **Limbs**, for any limb counts of the two operands. -/
theorem limbDot2_eq (ka kb : Nat) (a b : Nat → Int) (K : Nat) :
    limbDot2 ka kb a b K = ∑ k ∈ range K, a k * b k := by
  unfold limbDot2 planeSum
  rw [sum_congr rfl fun k _ => limb_mul_expand ka kb (a k) (b k)]
  symm
  rw [Finset.sum_comm]
  apply sum_congr rfl; intro p _
  rw [Finset.sum_comm]
  apply sum_congr rfl; intro q _
  rw [Finset.mul_sum]

/-! ## The tile loop order -/

/-- The number of chunks of `C` indices covering `K`. -/
def nChunks (C K : Nat) : Nat := (K + C - 1) / C

/-- The indices of chunk `c`: `c·C, …, c·C + C − 1`, below `K`. -/
def chunkIdx (C K c : Nat) : List Nat := ((List.range C).map (c * C + ·)).filter (· < K)

/-- The limbs `p` of `a` meeting a limb `s − p` of `b`. -/
def groupLimbs (ka kb s : Nat) : List Nat := (List.range (ka + 1)).filter fun p => p ≤ s ∧ s - p ≤ kb

/-- The terms of the `int32` accumulator of weight `256^s` in chunk `c`. -/
def groupTerms (ka kb C : Nat) (a b : Nat → Int) (K c s : Nat) : List Int :=
  ((chunkIdx C K c).map fun k =>
    (groupLimbs ka kb s).map fun p => limb ka p (a k) * limb kb (s - p) (b k)).flatten

/-- The tile-order reduction in exact arithmetic: per chunk, per weight, the accumulator's sum. -/
def tileReduce (ka kb C : Nat) (a b : Nat → Int) (K : Nat) : Int :=
  ∑ c ∈ range (nChunks C K), ∑ s ∈ range (ka + kb + 1), 256 ^ s * (groupTerms ka kb C a b K c s).sum

theorem sum_chunkIdx (C K c : Nat) (h : Nat → Int) :
    ((chunkIdx C K c).map h).sum = ∑ i ∈ range C, if c * C + i < K then h (c * C + i) else 0 := by
  rw [chunkIdx, sum_filter_map, List.map_map, sum_map_range]
  simp only [Function.comp, decide_eq_true_eq]

theorem sum_groupLimbs (ka kb s : Nat) (F : Nat → Int) :
    ((groupLimbs ka kb s).map F).sum = ∑ p ∈ range (ka + 1), if p ≤ s ∧ s - p ≤ kb then F p else 0 := by
  rw [groupLimbs, sum_filter_map, sum_map_range]
  simp only [decide_eq_true_eq]

theorem le_nChunks_mul {C : Nat} (hC : 0 < C) (K : Nat) : K ≤ nChunks C K * C := by
  have h1 := Nat.div_add_mod (K + C - 1) C
  have h2 := Nat.mod_lt (K + C - 1) hC
  unfold nChunks
  rw [Nat.mul_comm]
  generalize C * ((K + C - 1) / C) = P at *
  omega

theorem sum_chunks {C : Nat} (hC : 0 < C) (K : Nat) (h : Nat → Int) :
    ∑ c ∈ range (nChunks C K), ∑ i ∈ range C, (if c * C + i < K then h (c * C + i) else 0) =
      ∑ k ∈ range K, h k := by
  have hn : ∀ n, ∑ c ∈ range n, ∑ i ∈ range C, (if c * C + i < K then h (c * C + i) else 0) =
      ∑ k ∈ range (n * C), if k < K then h k else 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]
  rw [hn, ← Finset.sum_filter]
  congr 1
  ext k
  have := le_nChunks_mul hC K
  simp only [mem_filter, mem_range]
  omega

theorem shift_reindex {ka kb p : Nat} (hp : p ≤ ka) (G : Nat → Int) :
    ∑ s ∈ range (ka + kb + 1), (if p ≤ s ∧ s - p ≤ kb then G s else 0) =
      ∑ q ∈ range (kb + 1), G (p + q) := by
  rw [← Finset.sum_filter]
  have e : (range (ka + kb + 1)).filter (fun s => p ≤ s ∧ s - p ≤ kb) = Ico p (p + kb + 1) := by
    ext s; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [e, Finset.sum_Ico_eq_sum_range, show p + kb + 1 - p = kb + 1 by omega]

/-- One index's limb products, gathered by weight and recombined, are its product. -/
theorem group_recombine (ka kb : Nat) (x y : Int) :
    ∑ s ∈ range (ka + kb + 1),
        256 ^ s * ((groupLimbs ka kb s).map fun p => limb ka p x * limb kb (s - p) y).sum = x * y := by
  simp only [sum_groupLimbs, Finset.mul_sum]
  rw [Finset.sum_comm, limb_mul_expand ka kb x y]
  apply sum_congr rfl; intro p hp
  have hp' : p ≤ ka := by simp only [mem_range] at hp; omega
  have e : ∑ s ∈ range (ka + kb + 1),
      256 ^ s * (if p ≤ s ∧ s - p ≤ kb then limb ka p x * limb kb (s - p) y else 0) =
      ∑ s ∈ range (ka + kb + 1),
        (if p ≤ s ∧ s - p ≤ kb then 256 ^ s * (limb ka p x * limb kb (s - p) y) else 0) :=
    sum_congr rfl fun s _ => by split_ifs <;> simp
  rw [e, shift_reindex hp']
  apply sum_congr rfl; intro q _
  simp

/-- **The tile loop order is the exact sum**, for every chunk size. -/
theorem tileReduce_eq (ka kb : Nat) {C : Nat} (hC : 0 < C) (a b : Nat → Int) (K : Nat) :
    tileReduce ka kb C a b K = ∑ k ∈ range K, a k * b k := by
  have hg : ∀ c s, (groupTerms ka kb C a b K c s).sum = ∑ i ∈ range C,
      if c * C + i < K then ((groupLimbs ka kb s).map fun p =>
        limb ka p (a (c * C + i)) * limb kb (s - p) (b (c * C + i))).sum else 0 := by
    intro c s
    rw [groupTerms, List.sum_flatten, List.map_map]
    exact sum_chunkIdx C K c _
  unfold tileReduce
  simp only [hg, Finset.mul_sum]
  rw [← sum_chunks hC K fun k => a k * b k]
  apply sum_congr rfl; intro c _
  rw [Finset.sum_comm]
  apply sum_congr rfl; intro i _
  split_ifs
  · exact group_recombine ka kb _ _
  · simp

/-- The tile-order reduction of two downloaded vectors is `Fx.dotRaw`. -/
theorem tileReduce_dotRaw (ka kb : Nat) {C : Nat} (hC : 0 < C) (n : Nat) (a b : Vec) :
    tileReduce ka kb C a b n =
      Fx.dotRaw ((List.range n).map fun i => (⟨a i⟩ : Fx)) ((List.range n).map fun i => ⟨b i⟩) := by
  rw [tileReduce_eq ka kb hC, dotRaw_range]

/-! ## Bounded reduction trees -/

/-- A reduction tree on a `w`-bit machine: every add wrapped. -/
def RTree.evalW (w : Nat) : RTree → Int
  | .leaf v => wrap w v
  | .node l r => wrap w (l.evalW w + r.evalW w)

theorem fits_of_abs {w : Nat} {v : Int} (h : |v| < 2 ^ (w - 1)) : Fits w v := by
  rw [abs_lt] at h
  exact ⟨h.1.le, h.2⟩

theorem RTree.abs_eval_le (t : RTree) {B : Int} (h : ∀ v ∈ t.leaves, |v| ≤ B) :
    |t.eval| ≤ t.leaves.length * B := by
  induction t with
  | leaf v => simpa [eval, leaves] using h v (by simp [leaves])
  | node l r ihl ihr =>
    simp only [leaves, List.mem_append] at h
    have h1 := ihl fun v hv => h v (Or.inl hv)
    have h2 := ihr fun v hv => h v (Or.inr hv)
    simp only [eval, leaves, List.length_append, Nat.cast_add, add_mul]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- **A bounded reduction tree is exact in `w` bits, whatever its shape**: every node is at most
`(#leaves) · B` in magnitude. -/
theorem RTree.evalW_eq {w : Nat} (hw : 0 < w) (t : RTree) {B : Int} (hB : 0 ≤ B)
    (h : ∀ v ∈ t.leaves, |v| ≤ B) (hl : t.leaves.length * B < 2 ^ (w - 1)) :
    t.evalW w = t.eval := by
  induction t with
  | leaf v =>
    have := h v (by simp [leaves])
    simp only [leaves, List.length_singleton, Nat.cast_one, one_mul] at hl
    exact wrap_of_fits hw (fits_of_abs (by linarith))
  | node l r ihl ihr =>
    simp only [leaves, List.mem_append, List.length_append, Nat.cast_add, add_mul] at h hl
    have hl0 : (0 : Int) ≤ l.leaves.length * B := mul_nonneg (by positivity) hB
    have hr0 : (0 : Int) ≤ r.leaves.length * B := mul_nonneg (by positivity) hB
    have h1 := ihl (fun v hv => h v (Or.inl hv)) (by linarith)
    have h2 := ihr (fun v hv => h v (Or.inr hv)) (by linarith)
    have := (node l r).abs_eval_le (B := B) (by simpa [leaves] using h)
    simp only [leaves, List.length_append, Nat.cast_add, add_mul] at this
    rw [evalW, h1, h2]
    exact wrap_of_fits hw (fits_of_abs (by simp only [eval] at this; linarith))

theorem RTree.fits_eval {w : Nat} (t : RTree) {B : Int} (h : ∀ v ∈ t.leaves, |v| ≤ B)
    (hl : t.leaves.length * B < 2 ^ (w - 1)) : Fits w t.eval :=
  fits_of_abs (lt_of_le_of_lt (t.abs_eval_le h) hl)

/-- A left-to-right accumulation of `w`-bit adds is exact when the start and the addends are
small enough. -/
theorem foldl_wrap {w : Nat} (hw : 0 < w) {B : Int} (l : List Int) (a : Int)
    (hl : ∀ x ∈ l, |x| ≤ B) (h : |a| + l.length * B < 2 ^ (w - 1)) :
    l.foldl (fun acc x => wrap w (acc + x)) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
      add_mul, one_mul] at h ⊢
    have hx := hl x List.mem_cons_self
    have hB : 0 ≤ B := le_trans (abs_nonneg _) hx
    have hlB : (0 : Int) ≤ l.length * B := mul_nonneg (by positivity) hB
    have h1 := abs_add_le a x
    rw [wrap_of_fits hw (fits_of_abs (by linarith)),
      ih (a + x) (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (by linarith)]
    ring

/-! ## The machine -/

/-- An MMA schedule: for chunk `c` and weight `s`, the reduction tree the tensor cores run on the
`int32` accumulator. -/
abbrev Schedule := Nat → Nat → RTree

/-- A schedule is valid when each accumulator's tree adds exactly its group's terms to the zeroed
accumulator, in any order and grouping. -/
def ValidSchedule (ka kb C : Nat) (a b : Nat → Int) (K : Nat) (mma : Schedule) : Prop :=
  ∀ c < nChunks C K, ∀ s < ka + kb + 1, (mma c s).leaves.Perm (0 :: groupTerms ka kb C a b K c s)

/-- What the 128-bit accumulator receives, in loop order: each `int32` accumulator shifted by
`8s` bits. -/
def tileAddends (ka kb C K : Nat) (mma : Schedule) : List Int :=
  ((List.range (nChunks C K)).map fun c =>
    (List.range (ka + kb + 1)).map fun s => wrap 128 (256 ^ s * (mma c s).evalW 32)).flatten

/-- The tensor-core dot product on the machine: `int32` trees, recombined in 128 bits. -/
def tileReduceM (ka kb C K : Nat) (mma : Schedule) : Int :=
  (tileAddends ka kb C K mma).foldl (fun acc x => wrap 128 (acc + x)) 0

/-- Operands within the `k + 1`-limb range. -/
def LimbRange (k : Nat) (a : Nat → Int) (K : Nat) : Prop :=
  ∀ i < K, -2 ^ (8 * k + 7) ≤ a i ∧ a i < 2 ^ (8 * k + 7)

theorem groupTerms_abs {ka kb C : Nat} {a b : Nat → Int} {K : Nat} (ha : LimbRange ka a K)
    (hb : LimbRange kb b K) (c s : Nat) : ∀ v ∈ groupTerms ka kb C a b K c s, |v| ≤ 65025 := by
  intro v hv
  simp only [groupTerms, List.mem_flatten, List.mem_map] at hv
  obtain ⟨_, ⟨k, hk, rfl⟩, hv⟩ := hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
  simp only [chunkIdx, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq] at hk
  simp only [groupLimbs, List.mem_filter, List.mem_range, decide_eq_true_eq] at hp
  have h1 := abs_limb_le (by omega : p ≤ ka) (ha k hk.2)
  have h2 := abs_limb_le hp.2.2 (hb k hk.2)
  rw [abs_mul]
  exact (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)).trans (by norm_num)

theorem length_flatten_le {α : Type} (L : List (List α)) (B : Nat) (h : ∀ l ∈ L, l.length ≤ B) :
    L.flatten.length ≤ L.length * B := by
  induction L with
  | nil => simp
  | cons l L ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := h l List.mem_cons_self
    have := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    omega

theorem groupTerms_length (ka kb C : Nat) (a b : Nat → Int) (K c s : Nat) (hka : ka ≤ 3) :
    (groupTerms ka kb C a b K c s).length ≤ C * 4 := by
  unfold groupTerms
  refine (length_flatten_le _ 4 ?_).trans ?_
  · intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨k, _, rfl⟩ := hl
    simp only [List.length_map, groupLimbs]
    exact (List.length_filter_le _ _).trans (by simp; omega)
  · simp only [List.length_map, chunkIdx]
    exact Nat.mul_le_mul_right _ ((List.length_filter_le _ _).trans (by simp))

/-- **Every `int32` accumulator is exact**, for every MMA order and grouping: each node of any
tree over a sub-multiset of the group's terms fits in 32 bits. -/
theorem group_tree_exact {ka kb C : Nat} {a b : Nat → Int} {K : Nat} (hka : ka ≤ 3)
    (hC : C ≤ 8192) (ha : LimbRange ka a K) (hb : LimbRange kb b K) {c s : Nat} (t : RTree)
    (ht : t.leaves.Subperm (0 :: groupTerms ka kb C a b K c s)) :
    Fits 32 t.eval ∧ t.evalW 32 = t.eval := by
  have hv : ∀ v ∈ t.leaves, |v| ≤ 65025 := by
    intro v hv
    rcases List.mem_cons.mp (ht.subset hv) with rfl | hv
    · norm_num
    · exact groupTerms_abs ha hb c s v hv
  have hlen := ht.length_le
  have hg := groupTerms_length ka kb C a b K c s hka
  simp only [List.length_cons] at hlen
  have hl : (t.leaves.length : Int) * 65025 < 2 ^ (32 - 1) := by
    have : t.leaves.length ≤ 32769 := by omega
    have : (t.leaves.length : Int) ≤ 32769 := by exact_mod_cast this
    norm_num; linarith
  exact ⟨t.fits_eval hv hl, t.evalW_eq (by norm_num) (by norm_num) hv hl⟩

theorem nChunks_le (C K : Nat) : nChunks C K ≤ K + C := by
  unfold nChunks
  exact (Nat.div_le_self _ _).trans (by omega)

/-- **The tensor-core dot product is exact.** With at most four limbs per operand, operands in
range, chunks of at most 8192 indices and `K < 2^31`, every `int32` accumulator and the 128-bit
recombination are exact for every valid MMA schedule. -/
theorem tileReduceM_eq {ka kb C K : Nat} {a b : Nat → Int} {mma : Schedule} (hka : ka ≤ 3)
    (hkb : kb ≤ 3) (hC : 0 < C ∧ C ≤ 8192) (hK : K < 2 ^ 31) (ha : LimbRange ka a K)
    (hb : LimbRange kb b K) (hmma : ValidSchedule ka kb C a b K mma) :
    tileReduceM ka kb C K mma = ∑ k ∈ range K, a k * b k := by
  have hacc : ∀ c < nChunks C K, ∀ s < ka + kb + 1,
      wrap 128 (256 ^ s * (mma c s).evalW 32) = 256 ^ s * (groupTerms ka kb C a b K c s).sum ∧
        |256 ^ s * (groupTerms ka kb C a b K c s).sum| ≤ 2 ^ 79 := by
    intro c hc s hs
    have hp := hmma c hc s hs
    obtain ⟨hfit, hex⟩ := group_tree_exact hka hC.2 ha hb (mma c s) hp.subperm
    have hsum : (mma c s).eval = (groupTerms ka kb C a b K c s).sum := by
      rw [RTree.eval_eq_sum, hp.sum_eq, List.sum_cons, zero_add]
    rw [hex, hsum]
    rw [hsum] at hfit
    have hb' : |256 ^ s * (groupTerms ka kb C a b K c s).sum| ≤ 2 ^ 79 := by
      rw [abs_mul, abs_pow]
      unfold Fits at hfit
      have h1 : |(groupTerms ka kb C a b K c s).sum| ≤ 2 ^ 31 := abs_le.2 ⟨by norm_num at hfit ⊢; linarith, by norm_num at hfit ⊢; linarith⟩
      have h2 : |(256 : Int)| ^ s ≤ 256 ^ 6 := by
        rw [abs_of_pos (by norm_num)]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      calc |(256 : Int)| ^ s * |(groupTerms ka kb C a b K c s).sum| ≤ 256 ^ 6 * 2 ^ 31 :=
            mul_le_mul h2 h1 (abs_nonneg _) (by norm_num)
        _ = 2 ^ 79 := by norm_num
    exact ⟨wrap_of_fits (by norm_num) (fits_of_abs (lt_of_le_of_lt hb' (by norm_num))), hb'⟩
  have hadd : tileAddends ka kb C K mma = ((List.range (nChunks C K)).map fun c =>
      (List.range (ka + kb + 1)).map fun s => 256 ^ s * (groupTerms ka kb C a b K c s).sum).flatten := by
    unfold tileAddends
    congr 1
    refine List.map_congr_left fun c hc => List.map_congr_left fun s hs => ?_
    exact (hacc c (List.mem_range.mp hc) s (List.mem_range.mp hs)).1
  have hlen : (tileAddends ka kb C K mma).length ≤ nChunks C K * (ka + kb + 1) := by
    unfold tileAddends
    refine (length_flatten_le _ (ka + kb + 1) ?_).trans (by simp)
    intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨c, _, rfl⟩ := hl
    simp
  have hn := nChunks_le C K
  unfold tileReduceM
  rw [foldl_wrap (B := 2 ^ 79) (by norm_num) _ 0]
  · rw [zero_add, hadd, List.sum_flatten, List.map_map, ← tileReduce_eq ka kb hC.1, tileReduce,
      sum_map_range]
    apply sum_congr rfl; intro c _
    simp only [Function.comp, sum_map_range]
  · intro x hx
    rw [hadd] at hx
    simp only [List.mem_flatten, List.mem_map, List.mem_range] at hx
    obtain ⟨_, ⟨c, hc, rfl⟩, hx⟩ := hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    simp only [List.mem_range] at hs
    exact (hacc c hc s hs).2
  · have h7 : (tileAddends ka kb C K mma).length ≤ (2 ^ 31 + 8192) * 7 :=
      hlen.trans (Nat.mul_le_mul (by omega) (by omega))
    have h7' : ((tileAddends ka kb C K mma).length : Int) ≤ (2 ^ 31 + 8192) * 7 := by
      exact_mod_cast h7
    rw [abs_zero, zero_add]
    norm_num
    nlinarith

/-- **The tensor-core GEMM entry is `Fx.dotRaw`** of the downloaded row and column. -/
theorem tileReduceM_dotRaw {ka kb C n : Nat} {a b : Vec} {mma : Schedule} (hka : ka ≤ 3)
    (hkb : kb ≤ 3) (hC : 0 < C ∧ C ≤ 8192) (hn : n < 2 ^ 31) (ha : LimbRange ka a n)
    (hb : LimbRange kb b n) (hmma : ValidSchedule ka kb C a b n mma) :
    tileReduceM ka kb C n mma =
      Fx.dotRaw ((List.range n).map fun i => (⟨a i⟩ : Fx)) ((List.range n).map fun i => ⟨b i⟩) := by
  rw [tileReduceM_eq hka hkb hC hn ha hb hmma, dotRaw_range]

/-- Narrowed to int64, the machine result is the exact sum whenever that sum is an int64. -/
theorem tileReduceM_narrow {ka kb C K : Nat} {a b : Nat → Int} {mma : Schedule} (hka : ka ≤ 3)
    (hkb : kb ≤ 3) (hC : 0 < C ∧ C ≤ 8192) (hK : K < 2 ^ 31) (ha : LimbRange ka a K)
    (hb : LimbRange kb b K) (hmma : ValidSchedule ka kb C a b K mma)
    (h64 : Fits 64 (∑ k ∈ range K, a k * b k)) :
    wrap 64 (tileReduceM ka kb C K mma) = ∑ k ∈ range K, a k * b k := by
  rw [tileReduceM_eq hka hkb hC hK ha hb hmma, wrap64 h64]

end IxAIGpu
